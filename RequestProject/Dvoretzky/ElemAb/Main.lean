module

public import RequestProject.Dvoretzky.ElemAb.Source
public import RequestProject.Dvoretzky.ElemAb.Target

/-!
# Borsuk–Ulam for joins of `(ℤ/2)^r`

`elemAb_join`: let `E = (ℤ/2)^r` act on the join of `D + 1` two-point sets, the generator `g_q`
swapping the two points of block `k` iff `ε k q = 1`, where every block is swapped by some
generator. If `D + 1 < N`, there is no continuous map from the `N`-fold join `E * ⋯ * E` to this
join which is equivariant for the generators.

The proof follows `Dold.dold_join`: the family `bfam` of the source join is subdivided until its
simplices are small, mapped to the oriented chains of the target by the simplicial approximation
`vtxSel`, and the resulting family on the target contradicts `no_family` (the product of the linear
forms `∑_q ε_{k q} U_q` does not vanish).
-/

@[expose] public section

open scoped BigOperators

noncomputable section

namespace Dvoretzky.ElemAb

open Dvoretzky Dvoretzky.Dold

variable {r : ℕ}

/-! ### The swap action on vertices and points of the target -/

section TargetAct

variable {D : ℕ}

/-- The swap action on vertices `(j, l)`. -/
def vflip (ε : Fin D → ZMod 2) (v : Fin D × L2) : Fin D × L2 :=
  (v.1, v.2 * Multiplicative.ofAdd (ε v.1))

/-- The swap action on points of the target join. -/
def tflip (ε : Fin D → ZMod 2) (y : Fin D → L2 → ℝ) : Fin D → L2 → ℝ :=
  fun j h => y j (h * Multiplicative.ofAdd (ε j))

lemma ofAdd_mul_self (a : ZMod 2) :
    Multiplicative.ofAdd a * Multiplicative.ofAdd a = (1 : L2) := by
  rw [← ofAdd_add, show a + a = 0 from by
    rw [← two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul]]
  rfl

/-- Pointwise formula for adding a vertex, over `𝔽₂`. -/
lemma wedge_apply (v : Fin D × L2) (c : TChain (ZMod 2) D L2) (t : Smp D L2) :
    wedge v c t = if t v.1 = some v.2 then c (Function.update t v.1 none) else 0 := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c c' hc hc' =>
    rw [map_add, Finsupp.add_apply, hc, hc']
    split_ifs <;> simp
  | single s a =>
    rw [wedge_single, Finsupp.smul_apply, wedgeS]
    split_ifs with h1 h2 h2
    · rw [sgnP_zmod2, one_smul, Finsupp.single_apply, Finsupp.single_apply, smul_eq_mul]
      by_cases e : Function.update s v.1 (some v.2) = t
      · rw [if_pos e, if_pos, mul_one]
        rw [← e, Function.update_idem, Function.update_eq_self_iff.2 h1.symm]
      · rw [if_neg e, if_neg, mul_zero]
        intro e'
        apply e
        rw [e', Function.update_idem, Function.update_eq_self_iff.2 h2.symm]
    · rw [smul_eq_mul, sgnP_zmod2, one_smul, Finsupp.single_apply, if_neg, mul_zero]
      intro e; apply h2; rw [← e, Function.update_self]
    · rw [Finsupp.single_apply, if_neg]
      · simp
      · intro e; apply h1; rw [e, Function.update_self]
    · simp

lemma flipS_update_none (ε : Fin D → ZMod 2) (t : Smp D L2) (j : Fin D) :
    flipS ε (Function.update t j none) = Function.update (flipS ε t) j none := by
  funext i
  by_cases h : i = j
  · subst h; simp [flipS]
  · simp [flipS, Function.update_of_ne h]

lemma wedge_flipL (ε : Fin D → ZMod 2) (v : Fin D × L2) (c : TChain (ZMod 2) D L2) :
    wedge (vflip ε v) (flipL ε c) = flipL ε (wedge v c) := by
  ext t
  rw [wedge_apply, flipL_apply, flipL_apply, wedge_apply, flipS_update_none]
  have : flipS ε t v.1 = some v.2 ↔ t v.1 = some (v.2 * Multiplicative.ofAdd (ε v.1)) := by
    simp only [flipS, vflip]
    constructor
    · intro h
      cases ht : t v.1 with
      | none => rw [ht] at h; simp at h
      | some l =>
        rw [ht] at h
        simp only [Option.map_some, Option.some.injEq] at h
        rw [← h, mul_assoc, ofAdd_mul_self, mul_one]
    · intro h
      rw [h]
      simp [Option.map_some, mul_assoc, ofAdd_mul_self]
  dsimp [vflip] at *
  split_ifs <;> aesop

lemma alpha_map_vflip (ε : Fin D → ZMod 2) (w : List (Fin D × L2)) :
    (alpha (w.map (vflip ε)) : TChain (ZMod 2) D L2) = flipL ε (alpha w) := by
  induction w with
  | nil => simp [alpha, flipL_emptyS]
  | cons v w ih => rw [List.map_cons, alpha, alpha, ih, wedge_flipL]

end TargetAct

/-! ### Equivariance of the vertex selection -/

section Select

variable {N D : ℕ} (Φ : (Fin N → EA r → ℝ) → (Fin (D + 1) → L2 → ℝ))

lemma vtxSel_tflip {x : Fin N → EA r → ℝ} (g : EA r) (ε : Fin (D + 1) → ZMod 2)
    (hx : Φ x ∈ GroupJoin L2 (D + 1)) (heq : Φ (joinAct g x) = tflip ε (Φ x)) :
    vtxSel Φ (joinAct g x) = vflip ε (vtxSel Φ x) := by
  have hS : selSet Φ (joinAct g x) = selSet Φ x := by
    ext j
    simp only [selSet, Finset.mem_filter, Finset.mem_univ, true_and, heq, tflip]
    constructor
    · rintro ⟨h, hh⟩; exact ⟨h * Multiplicative.ofAdd (ε j), hh⟩
    · rintro ⟨h, hh⟩
      exact ⟨h * Multiplicative.ofAdd (ε j), by rwa [mul_assoc, ofAdd_mul_self, mul_one]⟩
  have hne := selSet_nonempty Φ hx
  have hne' : (selSet Φ (joinAct g x)).Nonempty := hS ▸ hne
  have hmin : (selSet Φ (joinAct g x)).min' hne' = (selSet Φ x).min' hne := by
    apply le_antisymm
    · exact Finset.min'_le _ _ (by rw [hS]; exact Finset.min'_mem _ hne)
    · exact Finset.min'_le _ _ (by rw [← hS]; exact Finset.min'_mem _ hne')
  have hmem : ∃ h, (1 : ℝ) / (D + 1) ≤ Φ x ((selSet Φ x).min' hne) h := by
    have := Finset.min'_mem _ hne
    simp only [selSet, Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this
  have hmem' : ∃ h, (1 : ℝ) / (D + 1) ≤
      Φ (joinAct g x) ((selSet Φ (joinAct g x)).min' hne') h := by
    have := Finset.min'_mem _ hne'
    simp only [selSet, Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this
  simp only [vtxSel, dif_pos hne, dif_pos hne', dif_pos hmem, dif_pos hmem', vflip]
  refine Prod.ext hmin ?_
  have key : ∀ c : L2, (1 : ℝ) / (D + 1) ≤
      Φ (joinAct g x) ((selSet Φ (joinAct g x)).min' hne') c →
        c = hmem.choose * Multiplicative.ofAdd (ε ((selSet Φ x).min' hne)) := by
    intro c h1
    have h2 := hmem.choose_spec
    rw [heq, hmin] at h1
    simp only [tflip] at h1
    have hpos : (0 : ℝ) < 1 / (D + 1) := by positivity
    have := hx.2.1 _ _ _ (ne_of_gt (lt_of_lt_of_le hpos h1)) (ne_of_gt (lt_of_lt_of_le hpos h2))
    rw [← this, mul_assoc, ofAdd_mul_self, mul_one]
  exact key _ hmem'.choose_spec

end Select

/-! ### Subdivision -/

section Sd

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

lemma bd_sdPow (k : ℕ) (c : Chain (ZMod 2) E) :
    bd (((sd : Module.End (ZMod 2) (Chain (ZMod 2) E)) ^ k) c) =
      ((sd : Module.End (ZMod 2) (Chain (ZMod 2) E)) ^ k) (bd c) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', Module.End.mul_apply, bd_sd, ih]; rfl

lemma sdPow_nil' (k : ℕ) :
    ((sd : Module.End (ZMod 2) (Chain (ZMod 2) E)) ^ k) (Finsupp.single [] 1) =
      Finsupp.single [] 1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', Module.End.mul_apply, ih, sd_single, sdList_nil, one_smul]

lemma sdPow_actL (k : ℕ) (T : E →ₗ[ℝ] E) (c : Chain (ZMod 2) E) :
    ((sd : Module.End (ZMod 2) (Chain (ZMod 2) E)) ^ k) (actL T c) =
      actL T (((sd : Module.End (ZMod 2) (Chain (ZMod 2) E)) ^ k) c) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', Module.End.mul_apply, ih, sd_actL]; rfl

end Sd

/-! ### The simplicial approximation -/

section Approx

variable {N D : ℕ} (Φ : (Fin N → EA r → ℝ) → (Fin (D + 1) → L2 → ℝ))

/-- The chain map induced by the vertex selection. -/
def PsiE : Chain (ZMod 2) (Fin N → EA r → ℝ) →ₗ[ZMod 2] TChain (ZMod 2) (D + 1) L2 :=
  alphaL ∘ₗ actL (vtxSel Φ)

lemma PsiE_single (m : List (Fin N → EA r → ℝ)) :
    PsiE Φ (Finsupp.single m 1) = alpha (m.map (vtxSel Φ)) := by
  simp [PsiE]

lemma consistent_of_close' (hmaps : ∀ x ∈ GroupJoin (EA r) N, Φ x ∈ GroupJoin L2 (D + 1))
    {δ : ℝ} (hδ : ∀ x ∈ GroupJoin (EA r) N, ∀ y ∈ GroupJoin (EA r) N, dist x y < δ →
      dist (Φ x) (Φ y) < 1 / (2 * (D + 1)))
    {m : List (Fin N → EA r → ℝ)} (hJ : ∀ y ∈ m, y ∈ GroupJoin (EA r) N)
    (hd : ∀ y ∈ m, ∀ z ∈ m, dist y z < δ) : Consistent (m.map (vtxSel Φ)) := by
  intro a ha b hb hab
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hb
  have h1 := vtxSel_spec Φ (hmaps x (hJ x hx))
  have h2 := vtxSel_spec Φ (hmaps y (hJ y hy))
  rw [hab] at h1
  have hc : dist (Φ x (vtxSel Φ y).1 (vtxSel Φ y).2) (Φ y (vtxSel Φ y).1 (vtxSel Φ y).2) <
      1 / (2 * (D + 1)) :=
    lt_of_le_of_lt ((dist_le_pi_dist _ _ _).trans (dist_le_pi_dist _ _ _))
      (hδ x (hJ x hx) y (hJ y hy) (hd x hx y hy))
  rw [Real.dist_eq] at hc
  have hD : (0 : ℝ) < D + 1 := by positivity
  have hpos : 0 < Φ x (vtxSel Φ y).1 (vtxSel Φ y).2 := by
    have e : (1 : ℝ) / (2 * (D + 1)) = (1 / (D + 1)) / 2 := by field_simp
    have := (abs_lt.1 hc).1
    rw [e] at this
    have : (0 : ℝ) < 1 / (D + 1) := by positivity
    linarith
  refine Prod.ext hab ((hmaps x (hJ x hx)).2.1 _ _ _
    (ne_of_gt (lt_of_lt_of_le (by positivity) h1)) (ne_of_gt hpos))

lemma PsiE_bd {c : Chain (ZMod 2) (Fin N → EA r → ℝ)}
    (hc : c ∈ Finsupp.supported (ZMod 2) (ZMod 2) {m | Consistent (m.map (vtxSel Φ))}) :
    PsiE Φ (bd c) = bdT (PsiE Φ c) := by
  refine eq_on_supported (PsiE Φ ∘ₗ bd) (bdT ∘ₗ PsiE Φ) (fun l hl => ?_) hc
  simp only [LinearMap.coe_comp, Function.comp_apply, bd_single, one_smul, PsiE, actL_bdList,
    actL_single, alphaL_single]
  exact (bdT_alpha (R := ZMod 2) hl).symm

lemma PsiE_Tq (q : Fin r) (ε : Fin (D + 1) → ZMod 2)
    (hmaps : ∀ x ∈ GroupJoin (EA r) N, Φ x ∈ GroupJoin L2 (D + 1))
    (heq : ∀ x ∈ GroupJoin (EA r) N, Φ (joinAct (egen q) x) = tflip ε (Φ x))
    {c : Chain (ZMod 2) (Fin N → EA r → ℝ)}
    (hc : c ∈ Finsupp.supported (ZMod 2) (ZMod 2) {m | ∀ y ∈ m, y ∈ GroupJoin (EA r) N}) :
    PsiE Φ (Tq q c) = flipL ε (PsiE Φ c) := by
  refine eq_on_supported (PsiE Φ ∘ₗ Tq q) (flipL ε ∘ₗ PsiE Φ) (fun l hl => ?_) hc
  simp only [LinearMap.coe_comp, Function.comp_apply, Tq, actL_single, PsiE_single]
  rw [← alpha_map_vflip, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun y hy => ?_
  exact vtxSel_tflip Φ (egen q) ε (hmaps y (hl y hy)) (heq y (hl y hy))

end Approx

/-! ### The theorem -/

/-- **Borsuk–Ulam for joins of `(ℤ/2)^r`.** Let `(ℤ/2)^r` act on the join of `D + 1` two-point
sets, the generator `g_q` swapping block `k` iff `ε k q = 1`, every block being swapped by some
generator. If `D + 1 < N`, no continuous map from the `N`-fold join of `(ℤ/2)^r` to this join is
equivariant for the generators. -/
theorem elemAb_join {N D : ℕ} (hND : D + 1 < N) (ε : Fin (D + 1) → Fin r → ZMod 2)
    (hε : ∀ k, ε k ≠ 0) (Φ : (Fin N → EA r → ℝ) → (Fin (D + 1) → L2 → ℝ))
    (hc : ContinuousOn Φ (GroupJoin (EA r) N))
    (hmaps : ∀ x ∈ GroupJoin (EA r) N, Φ x ∈ GroupJoin L2 (D + 1))
    (heq : ∀ q, ∀ x ∈ GroupJoin (EA r) N,
      Φ (joinAct (egen q) x) = tflip (fun k => ε k q) (Φ x)) : False := by
  classical
  have hu : UniformContinuousOn Φ (GroupJoin (EA r) N) :=
    (isCompact_groupJoin N).uniformContinuousOn_of_continuous hc
  have hε' : (0 : ℝ) < 1 / (2 * (D + 1)) := by positivity
  obtain ⟨δ, hδpos, hδ⟩ := Metric.uniformContinuousOn_iff.1 hu _ hε'
  set qq : ℝ := (D + 1) / (D + 2) with hqq
  have hq0 : 0 ≤ qq := by positivity
  have hq1 : qq < 1 := by rw [hqq, div_lt_one (by positivity)]; linarith
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hδpos hq1
  set S := (sd : Module.End (ZMod 2) (Chain (ZMod 2) (Fin N → EA r → ℝ))) ^ k with hS
  have hgood : ∀ I : Fin r →₀ ℕ, Finsupp.degree I ≤ D + 1 →
      S (bfam I) ∈ Finsupp.supported (ZMod 2) (ZMod 2)
        {m | (∀ y ∈ m, y ∈ GroupJoin (EA r) N) ∧ Consistent (m.map (vtxSel Φ))} := by
    intro I hI
    rw [Finsupp.mem_supported]
    intro m hm
    obtain ⟨l, hl, hm'⟩ := mem_support_map hm
    have hV : VList N (Finsupp.degree I) l := bfam_supported I hl
    obtain ⟨hlen, hhull, hdist⟩ := sdIter_support k l 1 hV.dist_le m hm'
    have hlen' := hV.length_eq
    have hJ : ∀ y ∈ m, y ∈ GroupJoin (EA r) N :=
      fun y hy => hV.hull_subset (by omega) (hhull y hy)
    refine ⟨hJ, consistent_of_close' Φ hmaps hδ hJ fun y hy z hz => ?_⟩
    refine lt_of_le_of_lt (hdist y hy z hz) (lt_of_le_of_lt ?_ hk)
    rw [mul_one, hlen']
    refine pow_le_pow_left₀ (ratio_nonneg (Finsupp.degree I + 1)) ?_ k
    rw [hqq, div_le_div_iff₀ (by positivity) (by positivity)]
    have : ((Finsupp.degree I : ℕ) : ℝ) ≤ D + 1 := by exact_mod_cast hI
    push_cast
    nlinarith
  have hcons : ∀ I : Fin r →₀ ℕ, Finsupp.degree I ≤ D + 1 →
      S (bfam I) ∈ Finsupp.supported (ZMod 2) (ZMod 2) {m | Consistent (m.map (vtxSel Φ))} :=
    fun I hI => Finsupp.supported_mono (fun m hm => hm.2) (hgood I hI)
  have hinJ : ∀ I : Fin r →₀ ℕ, Finsupp.degree I ≤ D + 1 →
      S (bfam I) ∈ Finsupp.supported (ZMod 2) (ZMod 2) {m | ∀ y ∈ m, y ∈ GroupJoin (EA r) N} :=
    fun I hI => Finsupp.supported_mono (fun m hm => hm.1) (hgood I hI)
  -- the family on the target
  set β : (Fin r →₀ ℕ) → TChain (ZMod 2) (D + 1) L2 := fun I => PsiE Φ (S (bfam I)) with hβ
  have hSTq : ∀ q c, S (Tq q c) = Tq q (S c) := fun q c => by
    simpa [Tq] using sdPow_actL (E := Fin N → EA r → ℝ) k (joinActL (egen q)) c
  have hfl : ∀ q (J : Fin r →₀ ℕ), Finsupp.degree J ≤ D + 1 →
      flipL (fun j => ε j q) (β J) = PsiE Φ (S (Tq q (bfam J))) := by
    intro q J hJ
    rw [hSTq, PsiE_Tq Φ q _ hmaps (heq q) (hinJ J hJ)]
  have hfam : tgtFam (D + 1) ε (D + 1) (fun J => if J = 0 then 1 else 0) β := by
    intro I hI
    have h1 : bdT (β I) = (PsiE Φ ∘ₗ S) (bd (bfam I)) := by
      rw [LinearMap.comp_apply, hS, ← bd_sdPow, ← hS, PsiE_bd Φ (hcons I hI)]
    have h2 : ∀ q, shift q (fun J => β J + flipL (fun k => ε k q) (β J)) I =
        (PsiE Φ ∘ₗ S) (shift q (fun J => bfam J + Tq q (bfam J)) I) := by
      intro q
      rw [← shift_map]
      refine shift_congr q (fun J hJ => ?_) hI
      rw [hfl q J hJ, LinearMap.comp_apply, map_add, map_add]
    have h3 := isFam_bfam (N := N) (r := r) (D + 1) I hI
    rw [DOp] at h3
    show DOp _ _ β I = _
    rw [DOp, h1, Finset.sum_congr rfl (fun q _ => h2 q), ← map_sum, ← map_add, h3, map_smul]
    congr 1
    rw [LinearMap.comp_apply, sdPow_nil', PsiE_single]
    rfl
  exact no_family ε hε le_rfl β hfam

end Dvoretzky.ElemAb
