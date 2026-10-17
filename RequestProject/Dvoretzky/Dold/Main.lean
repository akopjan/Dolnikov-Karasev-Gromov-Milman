module

public import RequestProject.Dvoretzky.Dold.JoinGeom
public import RequestProject.Dvoretzky.Dold.Algebra

/-!
# Dold's theorem for the joins of `ℤ/p`

For a prime `p` and `G = ℤ/p` there is no continuous `G`-equivariant map from the `N`-fold join
`G * ⋯ * G` to the `M`-fold join if `M < N` (`dold_join`).

The proof is the classical chain-level argument: the standard equivariant cycle-building sequence
`c₀, c₁, …` in the ordered chains of the source join, subdivided barycentrically until all simplices
are small, is mapped by a simplicial approximation of the map (`vtxSel`) to the oriented chains of
the target join, where the algebraic Dold lemma `dold_algebra` gives a contradiction.
-/

@[expose] public section

open scoped BigOperators

noncomputable section

namespace Dvoretzky.Dold

open Dvoretzky

/-! ### Linear maps on supported chains -/

section Supp

variable {R : Type*} [CommRing R] {E : Type*}

lemma map_mem_supported {M : Type*} [AddCommGroup M] [Module R M] (f : Chain R E →ₗ[R] M)
    {s : Set (List E)} (S : Submodule R M) (h : ∀ l ∈ s, f (Finsupp.single l 1) ∈ S)
    {c : Chain R E} (hc : c ∈ Finsupp.supported R R s) : f c ∈ S := by
  rw [Finsupp.supported_eq_span_single] at hc
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hc
  · rintro _ ⟨l, hl, rfl⟩; exact h l hl
  · simp
  · intro x y _ _ hx hy; rw [map_add]; exact S.add_mem hx hy
  · intro a x _ hx; rw [map_smul]; exact S.smul_mem a hx

lemma eq_on_supported {M : Type*} [AddCommGroup M] [Module R M] (f g : Chain R E →ₗ[R] M)
    {s : Set (List E)} (h : ∀ l ∈ s, f (Finsupp.single l 1) = g (Finsupp.single l 1))
    {c : Chain R E} (hc : c ∈ Finsupp.supported R R s) : f c = g c := by
  have := map_mem_supported (f - g) ⊥ (fun l hl => by simp [h l hl]) hc
  simpa [sub_eq_zero] using this

end Supp

/-! ### The cycle-building sequence in the source join -/

section Seq

variable {G : Type} [Group G]

lemma joinAct_mul' {N : ℕ} (a b : G) (x : Fin N → G → ℝ) :
    joinAct a (joinAct b x) = joinAct (a * b) x := by
  funext i h
  simp [joinAct, mul_assoc]

lemma joinAct_one' {N : ℕ} : joinAct (N := N) (1 : G) = id := by
  funext x i h
  simp [joinAct]

/-- The action of `g` on the join as a linear map. -/
def joinActL {N : ℕ} (g : G) : (Fin N → G → ℝ) →ₗ[ℝ] (Fin N → G → ℝ) where
  toFun := joinAct g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma coe_joinActL {N : ℕ} (g : G) : ⇑(joinActL (N := N) g) = joinAct g := rfl

variable (p : ℕ) [Fact p.Prime] {N : ℕ}

/-- The generator of `ℤ/p` acting on the ordered chains of the source join. -/
def Td : Module.End (ZMod p) (Chain (ZMod p) (Fin N → Multiplicative (ZMod p) → ℝ)) :=
  actL (joinAct (gen p))

lemma Td_pow (m : ℕ) (c : Chain (ZMod p) (Fin N → Multiplicative (ZMod p) → ℝ)) :
    ((Td p) ^ m) c = actL (joinAct (gen p ^ m)) c := by
  induction m with
  | zero => simp [joinAct_one', actL_id]
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, ih, Td, actL_comp]
    congr 2
    funext x
    simp [joinAct_mul', pow_succ']

lemma Td_pow_p : (Td p : Module.End (ZMod p) (Chain (ZMod p) (Fin N → _ → ℝ))) ^ p = 1 := by
  refine LinearMap.ext fun c => ?_
  rw [Td_pow, gen_pow_p, joinAct_one', actL_id]
  rfl

/-- The alternating operators `ρ_k = N` (norm) for even `k`, `1 - T` for odd `k`. -/
def rho (k : ℕ) : Module.End (ZMod p) (Chain (ZMod p) (Fin N → Multiplicative (ZMod p) → ℝ)) :=
  altOp (normOp (Td p) p) (1 - Td p) k

lemma commute_bd_Td :
    Commute (bd : Module.End (ZMod p) (Chain (ZMod p) (Fin N → Multiplicative (ZMod p) → ℝ)))
      (Td p) :=
  LinearMap.ext fun c => (actL_bd _ c).symm

lemma commute_bd_rho (k : ℕ) :
    Commute (bd : Module.End (ZMod p) (Chain (ZMod p) (Fin N → Multiplicative (ZMod p) → ℝ)))
      (rho p k) := by
  unfold rho altOp
  split_ifs
  · exact Commute.sum_right _ _ _ fun i _ => (commute_bd_Td p).pow_right i
  · refine LinearMap.ext fun c => ?_
    show bd ((1 - Td p) c) = (1 - Td p) (bd c)
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub]
    congr 1
    exact LinearMap.congr_fun (commute_bd_Td p).eq c

lemma rho_succ_mul (k : ℕ) :
    (rho p (k + 1) : Module.End (ZMod p) (Chain (ZMod p) (Fin N → _ → ℝ))) * rho p k = 0 := by
  unfold rho altOp
  by_cases hk : Even k
  · have : ¬ Even (k + 1) := by rw [Nat.even_add_one]; exact not_not.2 hk
    rw [if_neg this, if_pos hk]
    exact sub_mul_normOp _ p (Td_pow_p p)
  · have : Even (k + 1) := by rw [Nat.even_add_one]; exact hk
    rw [if_pos this, if_neg hk]
    exact normOp_mul_sub _ p (Td_pow_p p)

lemma rho_zero_nil :
    rho p 0 (Finsupp.single ([] : List (Fin N → Multiplicative (ZMod p) → ℝ)) 1) = 0 := by
  rw [rho, altOp, if_pos (by decide), normOp_apply]
  simp only [Td_pow, actL_single, List.map_nil, Finset.sum_const, Finset.card_range]
  rw [← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_self, zero_smul]

/-- The cycle-building sequence: `c₀ = [(0,1)]`, `c_{k+1} = ±(ρ_k c_k) * (k+1, 1)`. -/
def cseq : ℕ → Chain (ZMod p) (Fin N → Multiplicative (ZMod p) → ℝ)
  | 0 => Finsupp.single [vtxPt N 0 1] 1
  | k + 1 => appL (vtxPt N (k + 1) 1) (sgnL (rho p k (cseq k)))

lemma cseq_succ (k : ℕ) : (cseq p (k + 1) : Chain (ZMod p) (Fin N → _ → ℝ)) =
    appL (vtxPt N (k + 1) 1) (sgnL (rho p k (cseq p k))) := rfl

lemma bd_cseq_zero : bd (cseq p 0 : Chain (ZMod p) (Fin N → _ → ℝ)) = Finsupp.single [] 1 := by
  simp [cseq, bdList_cons]

lemma bd_cseq_succ (k : ℕ) :
    bd (cseq p (k + 1) : Chain (ZMod p) (Fin N → _ → ℝ)) = rho p k (cseq p k) := by
  induction k with
  | zero =>
    have h0 : bd (rho p 0 (cseq p 0 : Chain (ZMod p) (Fin N → _ → ℝ))) = 0 := by
      rw [← Module.End.mul_apply, (commute_bd_rho p 0).eq, Module.End.mul_apply, bd_cseq_zero,
        rho_zero_nil]
    rw [cseq_succ, bd_appL, bd_sgnL, h0, map_zero, neg_zero, map_zero, zero_add, sgnL_sgnL]
  | succ k ih =>
    have h0 : bd (rho p (k + 1) (cseq p (k + 1) : Chain (ZMod p) (Fin N → _ → ℝ))) = 0 := by
      rw [← Module.End.mul_apply, (commute_bd_rho p (k + 1)).eq, Module.End.mul_apply, ih,
        ← Module.End.mul_apply, rho_succ_mul, LinearMap.zero_apply]
    rw [cseq_succ, bd_appL, bd_sgnL, h0, map_zero, neg_zero, map_zero, zero_add, sgnL_sgnL]

lemma Td_mem_supported {s : Set (List (Fin N → Multiplicative (ZMod p) → ℝ))}
    (hs : ∀ l ∈ s, l.map (joinAct (gen p)) ∈ s) {c} (hc : c ∈ Finsupp.supported (ZMod p) (ZMod p) s) :
    Td p c ∈ Finsupp.supported (ZMod p) (ZMod p) s :=
  map_mem_supported (Td p) _ (fun l hl => by
    simp only [Td, actL_single]; exact Finsupp.single_mem_supported _ _ (hs l hl)) hc

lemma rho_mem_supported (k : ℕ) {s : Set (List (Fin N → Multiplicative (ZMod p) → ℝ))}
    (hs : ∀ l ∈ s, l.map (joinAct (gen p)) ∈ s) {c} (hc : c ∈ Finsupp.supported (ZMod p) (ZMod p) s) :
    rho p k c ∈ Finsupp.supported (ZMod p) (ZMod p) s := by
  have hpow : ∀ i : ℕ, ((Td p) ^ i) c ∈ Finsupp.supported (ZMod p) (ZMod p) s := by
    intro i
    induction i with
    | zero => simpa using hc
    | succ i ih => rw [pow_succ', Module.End.mul_apply]; exact Td_mem_supported p hs ih
  unfold rho altOp
  split_ifs
  · rw [normOp_apply]
    exact Submodule.sum_mem _ fun i _ => hpow i
  · simp only [LinearMap.sub_apply, Module.End.one_apply]
    exact Submodule.sub_mem _ hc (by simpa using hpow 1)

lemma cseq_supported (k : ℕ) :
    cseq p k ∈ Finsupp.supported (ZMod p) (ZMod p) {l : List (Fin N → _ → ℝ) | VList N k l} := by
  induction k with
  | zero =>
    refine Finsupp.single_mem_supported _ _ ⟨fun _ => 1, ?_⟩
    simp
  | succ k ih =>
    have h1 := rho_mem_supported p k (s := {l | VList N k l}) (fun l hl => VList.map_joinAct hl (gen p)) ih
    refine map_mem_supported (appL (vtxPt N (k + 1) 1) ∘ₗ sgnL) _ (fun l hl => ?_) h1
    simp only [LinearMap.coe_comp, Function.comp_apply, sgnL_single, mul_one, map_smul,
      appL_single]
    exact Submodule.smul_mem _ _ (Finsupp.single_mem_supported _ _ (VList.append hl))

end Seq

/-! ### Subdivision commutes with the action and the boundary -/

section Sd

variable (p : ℕ) [Fact p.Prime] {N : ℕ}

lemma commute_sd_Td :
    Commute (sd : Module.End (ZMod p) (Chain (ZMod p) (Fin N → Multiplicative (ZMod p) → ℝ)))
      (Td p) :=
  LinearMap.ext fun c => by
    simpa [Td] using (sd_actL (R := ZMod p) (joinActL (N := N) (gen p)) c)

lemma commute_sd_rho (k r : ℕ) :
    Commute ((sd : Module.End (ZMod p) (Chain (ZMod p) (Fin N → _ → ℝ))) ^ r) (rho p k) := by
  refine Commute.pow_left ?_ r
  unfold rho altOp
  split_ifs
  · exact Commute.sum_right _ _ _ fun i _ => (commute_sd_Td p).pow_right i
  · refine LinearMap.ext fun c => ?_
    show sd ((1 - Td p) c) = (1 - Td p) (sd c)
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub]
    rw [show Td p (sd c) = sd (Td p c) from (sd_actL (joinActL (gen p)) c).symm]

omit [Fact p.Prime] in
lemma commute_bd_sdPow (r : ℕ) :
    Commute (bd : Module.End (ZMod p) (Chain (ZMod p) (Fin N → Multiplicative (ZMod p) → ℝ)))
      ((sd : Module.End (ZMod p) (Chain (ZMod p) (Fin N → _ → ℝ))) ^ r) :=
  Commute.pow_right (LinearMap.ext fun c => bd_sd c) r

lemma sdPow_nil (r : ℕ) :
    ((sd : Module.End (ZMod p) (Chain (ZMod p) (Fin N → Multiplicative (ZMod p) → ℝ))) ^ r)
      (Finsupp.single [] 1) = Finsupp.single [] 1 := by
  induction r with
  | zero => rfl
  | succ r ih => rw [pow_succ', Module.End.mul_apply, ih, sd_single, sdList_nil, one_smul]

end Sd

/-! ### The simplicial approximation -/

section Approx

variable (p : ℕ) [Fact p.Prime] {N D : ℕ}
  (Φ : (Fin N → Multiplicative (ZMod p) → ℝ) → (Fin (D + 1) → Multiplicative (ZMod p) → ℝ))

/-- The chain map induced by the vertex selection `vtxSel Φ`. -/
def Psi : Chain (ZMod p) (Fin N → Multiplicative (ZMod p) → ℝ) →ₗ[ZMod p]
    TChain (ZMod p) (D + 1) (Multiplicative (ZMod p)) :=
  alphaL ∘ₗ actL (vtxSel Φ)

lemma Psi_single (m : List (Fin N → Multiplicative (ZMod p) → ℝ)) :
    Psi p Φ (Finsupp.single m 1) = alpha (m.map (vtxSel Φ)) := by
  simp [Psi]

lemma consistent_of_close (hmaps : ∀ x ∈ GroupJoin _ N, Φ x ∈ GroupJoin _ (D + 1)) {δ : ℝ}
    (hδ : ∀ x ∈ GroupJoin _ N, ∀ y ∈ GroupJoin _ N, dist x y < δ →
      dist (Φ x) (Φ y) < 1 / (2 * (D + 1)))
    {m : List (Fin N → Multiplicative (ZMod p) → ℝ)} (hJ : ∀ y ∈ m, y ∈ GroupJoin _ N)
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

lemma Psi_bd {c : Chain (ZMod p) (Fin N → Multiplicative (ZMod p) → ℝ)}
    (hc : c ∈ Finsupp.supported (ZMod p) (ZMod p) {m | Consistent (m.map (vtxSel Φ))}) :
    Psi p Φ (bd c) = bdT (Psi p Φ c) := by
  refine eq_on_supported (Psi p Φ ∘ₗ bd) (bdT ∘ₗ Psi p Φ) (fun l hl => ?_) hc
  simp only [LinearMap.coe_comp, Function.comp_apply, bd_single, one_smul, Psi, actL_bdList,
    actL_single, alphaL_single]
  exact (bdT_alpha (R := ZMod p) hl).symm

variable (hmaps : ∀ x ∈ GroupJoin _ N, Φ x ∈ GroupJoin _ (D + 1))
  (heq : ∀ g, ∀ x ∈ GroupJoin _ N, Φ (joinAct g x) = joinAct g (Φ x))
include hmaps heq

lemma Psi_Td {c : Chain (ZMod p) (Fin N → Multiplicative (ZMod p) → ℝ)}
    (hc : c ∈ Finsupp.supported (ZMod p) (ZMod p) {m | ∀ y ∈ m, y ∈ GroupJoin _ N}) :
    Psi p Φ (Td p c) = tact (gen p) (Psi p Φ c) := by
  refine eq_on_supported (Psi p Φ ∘ₗ Td p) (tact (gen p) ∘ₗ Psi p Φ) (fun l hl => ?_) hc
  simp only [LinearMap.coe_comp, Function.comp_apply, Td, actL_single, Psi_single]
  rw [← alpha_map_vact, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun y hy => ?_
  exact vtxSel_joinAct Φ (gen p) (hmaps y (hl y hy)) (heq _ y (hl y hy))

lemma Psi_Td_pow (i : ℕ) {c : Chain (ZMod p) (Fin N → Multiplicative (ZMod p) → ℝ)}
    (hc : c ∈ Finsupp.supported (ZMod p) (ZMod p) {m | ∀ y ∈ m, y ∈ GroupJoin _ N}) :
    Psi p Φ (((Td p) ^ i) c) = ((tact (gen p)) ^ i) (Psi p Φ c) := by
  have hs : ∀ l ∈ {m : List (Fin N → Multiplicative (ZMod p) → ℝ) | ∀ y ∈ m, y ∈ GroupJoin _ N},
      l.map (joinAct (gen p)) ∈ {m | ∀ y ∈ m, y ∈ GroupJoin _ N} := by
    intro l hl y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    exact joinAct_mem _ (hl x hx)
  induction i with
  | zero => simp
  | succ i ih =>
    have hmem : ((Td p) ^ i) c ∈ Finsupp.supported (ZMod p) (ZMod p)
        {m | ∀ y ∈ m, y ∈ GroupJoin _ N} := by
      clear ih
      induction i with
      | zero => simpa using hc
      | succ i ih => rw [pow_succ', Module.End.mul_apply]; exact Td_mem_supported p hs ih
    rw [pow_succ', Module.End.mul_apply, Psi_Td p Φ hmaps heq hmem, ih, pow_succ',
      Module.End.mul_apply]

lemma Psi_rho (k : ℕ) {c : Chain (ZMod p) (Fin N → Multiplicative (ZMod p) → ℝ)}
    (hc : c ∈ Finsupp.supported (ZMod p) (ZMod p) {m | ∀ y ∈ m, y ∈ GroupJoin _ N}) :
    Psi p Φ (rho p k c) = altOp (normOp (tact (gen p)) p) (1 - tact (gen p)) k (Psi p Φ c) := by
  unfold rho altOp
  split_ifs
  · simp only [normOp_apply, map_sum]
    exact Finset.sum_congr rfl fun i _ => Psi_Td_pow p Φ hmaps heq i hc
  · simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub]
    rw [Psi_Td p Φ hmaps heq hc]

end Approx

/-! ### Dold's theorem -/

/-- **Dold's theorem for `ℤ/p`** (`p` prime): there is no continuous `ℤ/p`-equivariant map from
the `N`-fold join `G * ⋯ * G` (`G = ℤ/p`) to the `(D+1)`-fold join when `D + 1 < N`. -/
theorem dold_join (p : ℕ) [Fact p.Prime] {N D : ℕ} (hND : D + 1 < N)
    (Φ : (Fin N → Multiplicative (ZMod p) → ℝ) → (Fin (D + 1) → Multiplicative (ZMod p) → ℝ))
    (hc : ContinuousOn Φ (GroupJoin _ N))
    (hmaps : ∀ x ∈ GroupJoin _ N, Φ x ∈ GroupJoin _ (D + 1))
    (heq : ∀ g, ∀ x ∈ GroupJoin _ N, Φ (joinAct g x) = joinAct g (Φ x)) : False := by
  classical
  have hu : UniformContinuousOn Φ (GroupJoin (Multiplicative (ZMod p)) N) :=
    (isCompact_groupJoin N).uniformContinuousOn_of_continuous hc
  have hε : (0 : ℝ) < 1 / (2 * (D + 1)) := by positivity
  obtain ⟨δ, hδpos, hδ⟩ := Metric.uniformContinuousOn_iff.1 hu _ hε
  set q : ℝ := (D + 1) / (D + 2) with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by rw [hq, div_lt_one (by positivity)]; linarith
  obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one hδpos hq1
  set S := (sd : Module.End (ZMod p) (Chain (ZMod p) (Fin N → Multiplicative (ZMod p) → ℝ))) ^ r
    with hS
  have hgood : ∀ k ≤ D + 1, S (cseq p k) ∈ Finsupp.supported (ZMod p) (ZMod p)
      {m | m.length = k + 1 ∧ (∀ y ∈ m, y ∈ GroupJoin _ N) ∧ Consistent (m.map (vtxSel Φ))} := by
    intro k hk
    rw [Finsupp.mem_supported]
    intro m hm
    obtain ⟨l, hl, hm'⟩ := mem_support_map hm
    have hV : VList N k l := cseq_supported p k hl
    obtain ⟨hlen, hhull, hdist⟩ := sdIter_support r l 1 hV.dist_le m hm'
    have hlen' := hV.length_eq
    have hJ : ∀ y ∈ m, y ∈ GroupJoin _ N := fun y hy => hV.hull_subset (by omega) (hhull y hy)
    refine ⟨by rw [hlen, hlen'], hJ, consistent_of_close p Φ hmaps hδ hJ fun y hy z hz => ?_⟩
    refine lt_of_le_of_lt (hdist y hy z hz) (lt_of_le_of_lt ?_ hr)
    rw [mul_one, hlen']
    refine pow_le_pow_left₀ (ratio_nonneg (k + 1)) ?_ r
    rw [hq, div_le_div_iff₀ (by positivity) (by positivity)]
    have : (k : ℝ) ≤ D + 1 := by exact_mod_cast hk
    push_cast
    nlinarith
  have hcons : ∀ k ≤ D + 1, S (cseq p k) ∈ Finsupp.supported (ZMod p) (ZMod p)
      {m | Consistent (m.map (vtxSel Φ))} := fun k hk =>
    Finsupp.supported_mono (fun m hm => hm.2.2) (hgood k hk)
  have hinJ : ∀ k ≤ D + 1, S (cseq p k) ∈ Finsupp.supported (ZMod p) (ZMod p)
      {m | ∀ y ∈ m, y ∈ GroupJoin _ N} := fun k hk =>
    Finsupp.supported_mono (fun m hm => hm.2.1) (hgood k hk)
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have htp : (tact (gen p) : Module.End (ZMod p) (TChain (ZMod p) (D + 1) _)) ^ p = 1 :=
    LinearMap.ext fun c => by rw [tact_pow, gen_pow_p, tact_one]; rfl
  obtain ⟨hB, hA⟩ := exact_of_proj (tact (gen p) : Module.End (ZMod p) (TChain (ZMod p) (D + 1) _))
    (projQ p) p hp htp (Finsupp.single emptyS 1) (Finsupp.lapply emptyS)
    (fun x => by simpa using projQ_identity p x)
  have hcomm : Commute (bdT : Module.End (ZMod p) (TChain (ZMod p) (D + 1) _)) (tact (gen p)) :=
    LinearMap.ext fun c => (bdT_tact _ c)
  refine dold_algebra (bdT : Module.End (ZMod p) (TChain (ZMod p) (D + 1) _))
    (normOp (tact (gen p)) p) (1 - tact (gen p)) (Finsupp.single emptyS 1) (Finsupp.lapply emptyS)
    (LinearMap.ext fun c => bdT_bdT c)
    (Commute.sum_right _ _ _ fun i _ => hcomm.pow_right i)
    (LinearMap.ext fun c => by
      simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply, map_sub]
      rw [bdT_tact])
    (by simp [faceT, emptyS])
    (fun y => by
      show (y emptyS - (tact (gen p) y) emptyS) = 0
      rw [tact_apply_emptyS, sub_self])
    (by simp)
    hA hB (D + 1) (fun k => Psi p Φ (S (cseq p k))) ?_ ?_ ?_
  · rw [← Psi_bd p Φ (hcons 0 (by omega)), ← Module.End.mul_apply, (commute_bd_sdPow p r).eq,
      Module.End.mul_apply, bd_cseq_zero, sdPow_nil, Psi_single]
    rfl
  · intro k hk
    rw [← Psi_bd p Φ (hcons (k + 1) (by omega)), ← Module.End.mul_apply, (commute_bd_sdPow p r).eq,
      Module.End.mul_apply, bd_cseq_succ, ← Module.End.mul_apply, (commute_sd_rho p k r).eq,
      Module.End.mul_apply]
    exact Psi_rho p Φ hmaps heq k (hinJ k (by omega))
  · refine eq_on_supported (Psi p Φ) 0 (fun l hl => ?_) (hgood (D + 1) le_rfl)
    rw [Psi_single, LinearMap.zero_apply]
    exact alpha_eq_zero_of_length hl.2.2 (by rw [List.length_map, hl.1]; omega)

end Dvoretzky.Dold
