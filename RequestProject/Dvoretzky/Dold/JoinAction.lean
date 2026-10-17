module

public import RequestProject.Dvoretzky.Dold.JoinChains
public import RequestProject.Dvoretzky.Dold.Algebra

/-!
# The action of `G` on the oriented chains of the join, and exactness for `G = ℤ/p`

`G` acts on simplices of the join by right translation of the labels (`sact`), compatibly with
the action `joinAct` on points. The oriented chain module is then a free `𝔽_p[ℤ/p]`-module apart
from the augmentation simplex; we verify the exactness hypotheses of `dold_algebra`.
-/

@[expose] public section

open scoped BigOperators

noncomputable section

namespace Dvoretzky.Dold

variable {R : Type*} [CommRing R] {D : ℕ} {G : Type*} [Group G]

/-- The action on simplices. -/
def sact (g : G) (s : Smp D G) : Smp D G := fun j => (s j).map (· * g⁻¹)

/-- The action on vertices. -/
def vact (g : G) (v : Fin D × G) : Fin D × G := (v.1, v.2 * g⁻¹)

/-- The action on oriented chains. -/
def tact (g : G) : TChain R D G →ₗ[R] TChain R D G := Finsupp.lmapDomain R R (sact g)

@[simp] lemma tact_single (g : G) (s : Smp D G) (c : R) :
    tact g (Finsupp.single s c) = Finsupp.single (sact g s) c := by
  simp [tact]

lemma sact_mul (g g' : G) (s : Smp D G) : sact g (sact g' s) = sact (g * g') s := by
  funext j
  simp only [sact, Option.map_map]
  congr 1
  funext x
  simp [mul_assoc]

@[simp] lemma sact_one (s : Smp D G) : sact (1 : G) s = s := by
  funext j; simp [sact]

lemma sact_injective (g : G) : Function.Injective (sact (D := D) g) := by
  intro s t h
  have := congrArg (sact g⁻¹) h
  rwa [sact_mul, sact_mul, inv_mul_cancel, sact_one, sact_one] at this

@[simp] lemma sact_emptyS (g : G) : sact g (emptyS : Smp D G) = emptyS := by
  funext j; simp [sact, emptyS]

lemma sact_eq_emptyS_iff (g : G) (s : Smp D G) : sact g s = emptyS ↔ s = emptyS := by
  constructor
  · intro h; exact sact_injective g (h.trans (sact_emptyS g).symm)
  · rintro rfl; exact sact_emptyS g

@[simp] lemma isSome_sact (g : G) (s : Smp D G) (j : Fin D) : (sact g s j).isSome = (s j).isSome := by
  simp [sact]

lemma sact_apply_eq_none (g : G) (s : Smp D G) (j : Fin D) : sact g s j = none ↔ s j = none := by
  simp [sact]

@[simp] lemma pos_sact (g : G) (s : Smp D G) (j : Fin D) : pos (sact g s) j = pos s j := by
  simp [pos]

@[simp] lemma sgnP_sact (g : G) (s : Smp D G) (j : Fin D) :
    (sgnP (sact g s) j : R) = sgnP s j := by
  simp [sgnP]

lemma sact_update (g : G) (s : Smp D G) (j : Fin D) (x : Option G) :
    sact g (Function.update s j x) = Function.update (sact g s) j (x.map (· * g⁻¹)) := by
  funext j'
  by_cases h : j' = j
  · subst h; simp [sact]
  · simp [sact, Function.update_of_ne h]

lemma tact_mul (g g' : G) (c : TChain R D G) : tact g (tact g' c) = tact (g * g') c := by
  simp only [tact, Finsupp.lmapDomain_apply, ← Finsupp.mapDomain_comp]
  congr 1
  funext s
  exact sact_mul g g' s

lemma tact_one (c : TChain R D G) : tact (1 : G) c = c := by
  simp only [tact, Finsupp.lmapDomain_apply]
  rw [show (sact (D := D) (1 : G)) = id from funext sact_one, Finsupp.mapDomain_id]

lemma tact_apply_emptyS (g : G) (c : TChain R D G) : tact g c emptyS = c emptyS := by
  simp only [tact, Finsupp.lmapDomain_apply]
  conv_lhs => rw [← sact_emptyS g]
  exact Finsupp.mapDomain_apply_of_injective (sact_injective g) c emptyS

lemma faceT_sact (g : G) (s : Smp D G) :
    (faceT (sact g s) : TChain R D G) = tact g (faceT s) := by
  simp only [faceT, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [isSome_sact]
  split_ifs
  · rw [map_smul, tact_single, sgnP_sact, sact_update]; rfl
  · simp

lemma bdT_tact (g : G) (c : TChain R D G) : bdT (tact g c) = tact g (bdT c) := by
  have : (bdT ∘ₗ tact g : TChain R D G →ₗ[R] TChain R D G) = tact g ∘ₗ bdT :=
    tchain_hom_ext fun s => by simp [faceT_sact]
  exact congrArg (fun F : TChain R D G →ₗ[R] TChain R D G => F c) this

lemma wedgeS_sact (g : G) (v : Fin D × G) (s : Smp D G) :
    (wedgeS (vact g v) (sact g s) : TChain R D G) = tact g (wedgeS v s) := by
  simp only [wedgeS, vact, sact_apply_eq_none]
  split_ifs
  · rw [map_smul, tact_single, sgnP_sact, sact_update]; rfl
  · simp

lemma wedge_tact (g : G) (v : Fin D × G) (c : TChain R D G) :
    wedge (vact g v) (tact g c) = tact g (wedge v c) := by
  have : (wedge (vact g v) ∘ₗ tact g : TChain R D G →ₗ[R] TChain R D G) = tact g ∘ₗ wedge v :=
    tchain_hom_ext fun s => by simp [wedgeS_sact]
  exact congrArg (fun F : TChain R D G →ₗ[R] TChain R D G => F c) this

lemma alpha_map_vact (g : G) (w : List (Fin D × G)) :
    (alpha (w.map (vact g)) : TChain R D G) = tact g (alpha w) := by
  induction w with
  | nil => simp [alpha]
  | cons v w ih => rw [List.map_cons, alpha, alpha, ih, wedge_tact]

lemma consistent_map_vact {w : List (Fin D × G)} (g : G) (hw : Consistent w) :
    Consistent (w.map (vact g)) := by
  intro a ha b hb e
  obtain ⟨a', ha', rfl⟩ := List.mem_map.1 ha
  obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hb
  rw [hw a' ha' b' hb' e]

/-! ### Exactness for `G = ℤ/p` -/

section Exact

variable (p : ℕ) [Fact p.Prime]

/-- The generator of `ℤ/p` (multiplicatively). -/
abbrev gen : Multiplicative (ZMod p) := Multiplicative.ofAdd 1

lemma gen_pow (m : ℕ) : (gen p) ^ m = Multiplicative.ofAdd (m : ZMod p) := by
  rw [← ofAdd_nsmul, nsmul_eq_mul, mul_one]

lemma gen_pow_p : (gen p) ^ p = 1 := by
  rw [gen_pow, ZMod.natCast_self]; rfl

/-- The fundamental domain: simplices whose first vertex has label `1`. -/
def FundDom (s : Smp D (Multiplicative (ZMod p))) : Prop :=
  ∃ j, (∀ j' < j, s j' = none) ∧ s j = some 1

open Classical in
/-- Projection onto the fundamental domain. -/
def projQ : TChain R D (Multiplicative (ZMod p)) →ₗ[R] TChain R D (Multiplicative (ZMod p)) :=
  Finsupp.linearCombination R (fun s => if FundDom p s then Finsupp.single s 1 else 0)

lemma tact_pow (g : G) (m : ℕ) (c : TChain R D G) :
    ((tact g : Module.End R (TChain R D G)) ^ m) c = tact (g ^ m) c := by
  induction m with
  | zero => simp [tact_one]
  | succ m ih => rw [pow_succ', Module.End.mul_apply, ih, tact_mul, ← pow_succ']

lemma fundDom_sact_iff (s : Smp D (Multiplicative (ZMod p))) (j0 : Fin D)
    (h0 : ∀ j' < j0, s j' = none) (g h : Multiplicative (ZMod p)) (hj0 : s j0 = some h) :
    FundDom p (sact g s) ↔ g = h := by
  constructor
  · rintro ⟨j, hj, hjs⟩
    have hjj : j = j0 := by
      rcases lt_trichotomy j j0 with hlt | heq | hgt
      · have := h0 j hlt
        simp [sact, this] at hjs
      · exact heq
      · have := hj j0 hgt
        rw [sact_apply_eq_none] at this
        rw [this] at hj0; simp at hj0
    subst hjj
    simp only [sact, hj0, Option.map_some, Option.some.injEq] at hjs
    have := congrArg (· * g) hjs
    simp only [inv_mul_cancel_right, one_mul] at this
    exact this.symm
  · rintro rfl
    refine ⟨j0, fun j' hj' => by rw [sact_apply_eq_none]; exact h0 j' hj', ?_⟩
    simp [sact, hj0]

lemma projQ_identity (x : TChain R D (Multiplicative (ZMod p))) :
    ∑ i ∈ Finset.range p, ((tact (gen p) : Module.End R (TChain R D (Multiplicative (ZMod p)))) ^ i)
        (projQ p (((tact (gen p) : Module.End R (TChain R D (Multiplicative (ZMod p)))) ^ (p - i)) x)) =
      x - (x emptyS) • Finsupp.single emptyS (1 : R) := by
  classical
  -- reduce to basis elements
  have key : ∀ s : Smp D (Multiplicative (ZMod p)),
      ∑ i ∈ Finset.range p, ((tact (gen p) : Module.End R (TChain R D (Multiplicative (ZMod p)))) ^ i)
        (projQ p (((tact (gen p) : Module.End R (TChain R D (Multiplicative (ZMod p)))) ^ (p - i)) (Finsupp.single s 1))) =
      Finsupp.single s 1 - (if s = emptyS then (1 : R) else 0) • Finsupp.single emptyS 1 := by
    intro s
    have hterm : ∀ i ∈ Finset.range p,
        ((tact (gen p) : Module.End R (TChain R D (Multiplicative (ZMod p)))) ^ i)
          (projQ p (((tact (gen p) : Module.End R (TChain R D (Multiplicative (ZMod p)))) ^ (p - i)) (Finsupp.single s 1))) =
        if FundDom p (sact ((gen p) ^ (p - i)) s) then Finsupp.single s 1 else 0 := by
      intro i hi
      rw [Finset.mem_range] at hi
      rw [tact_pow (gen p) (p - i), tact_single, projQ, Finsupp.linearCombination_single,
        one_smul]
      split_ifs
      · rw [tact_pow, tact_single, sact_mul, ← pow_add, Nat.add_sub_cancel' hi.le, gen_pow_p,
          sact_one]
      · simp
    rw [Finset.sum_congr rfl hterm]
    by_cases hs : s = emptyS
    · subst hs
      have : ∀ i, ¬ FundDom p (sact ((gen p) ^ (p - i)) (emptyS : Smp D _)) := by
        rintro i ⟨j, -, hj⟩
        simp [emptyS, sact] at hj
      rw [Finset.sum_eq_zero (fun i _ => if_neg (this i))]
      simp
    · rw [if_neg hs, zero_smul, sub_zero]
      -- the first vertex
      have hne : (Finset.univ.filter fun j => s j ≠ none).Nonempty := by
        by_contra hcon
        apply hs
        funext j
        by_contra hj
        exact hcon ⟨j, by simpa [emptyS] using hj⟩
      set j0 := (Finset.univ.filter fun j => s j ≠ none).min' hne
      have hj0 : s j0 ≠ none := by
        have := Finset.min'_mem _ hne
        simpa using this
      have h0 : ∀ j' < j0, s j' = none := by
        intro j' hj'
        by_contra hc
        have := Finset.min'_le (Finset.univ.filter fun j => s j ≠ none) j'
          (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hc)
        exact absurd hj' (not_lt.2 this)
      obtain ⟨h, hh⟩ := Option.ne_none_iff_exists'.1 hj0
      have hiff : ∀ i, i ≤ p → (FundDom p (sact ((gen p) ^ (p - i)) s) ↔
          (i : ZMod p) = - Multiplicative.toAdd h) := by
        intro i hi
        rw [fundDom_sact_iff p s j0 h0 _ h hh, gen_pow]
        constructor
        · intro e
          have := congrArg Multiplicative.toAdd e
          simp only [toAdd_ofAdd] at this
          rw [← this, Nat.cast_sub hi, ZMod.natCast_self, zero_sub]
          exact (neg_neg (i : ZMod p)).symm
        · intro e
          apply Multiplicative.toAdd.injective
          simp only [toAdd_ofAdd]
          rw [Nat.cast_sub hi, ZMod.natCast_self, e, zero_sub]
          exact neg_neg (Multiplicative.toAdd h)
      rw [Finset.sum_eq_single (-Multiplicative.toAdd h).val]
      · rw [if_pos ((hiff _ (ZMod.val_lt _).le).2 (ZMod.natCast_zmod_val _))]
      · intro i hi hne'
        rw [Finset.mem_range] at hi
        rw [if_neg]
        rw [hiff i hi.le]
        intro e
        apply hne'
        rw [← e, ZMod.val_cast_of_lt hi]
      · intro hn
        exact absurd (Finset.mem_range.2 (ZMod.val_lt _)) hn
  -- linearity
  have hlin : (∑ i ∈ Finset.range p,
      ((tact (gen p) : Module.End R (TChain R D (Multiplicative (ZMod p)))) ^ i) * projQ p *
        ((tact (gen p) : Module.End R (TChain R D (Multiplicative (ZMod p)))) ^ (p - i))) =
      LinearMap.id - (Finsupp.lapply emptyS).smulRight (Finsupp.single emptyS (1 : R)) := by
    refine tchain_hom_ext fun s => ?_
    rw [LinearMap.coe_sum, Finset.sum_apply]
    simp only [Module.End.mul_apply]
    rw [key s]
    simp [Finsupp.single_apply]
  have := congrArg (fun F : Module.End R (TChain R D (Multiplicative (ZMod p))) => F x) hlin
  simp only [LinearMap.coe_sum, Finset.sum_apply, Module.End.mul_apply] at this
  rw [this]
  simp

end Exact

end Dvoretzky.Dold
