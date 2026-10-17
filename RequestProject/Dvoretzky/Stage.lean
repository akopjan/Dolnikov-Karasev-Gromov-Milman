module

public import RequestProject.Dvoretzky.Averaging
public import RequestProject.Dvoretzky.Wreath

/-!
# The combinatorial part of the proof of Theorem 1

We construct, for given `k ≥ 1` and `δ`, a finite set `X`, a `2`-group `H` of permutations of
`X` and linear forms `l_x` (`x ∈ X`) on `ℝ^k` (not all zero) such that, for every multiset
(exponent vector) `β` on `X` of size `≤ δ`, the `H`-orbit sum
`∑_{h ∈ H} ∏_x l_{h x}(z) ^ (2 β x)` is proportional to `‖z‖ ^ (2 |β|)`.

This is the content of Sections 8–9 of Dol'nikov–Karasev. We replace their description by
`2`-Sylow subgroups of symmetric groups and trees by iterated wreath products
(the group `K₁ ≀ K₂ ≀ ⋯ ≀ K_δ` from the remark at the end of Section 9), and their
pigeonhole argument on forks by an induction on the size of the support of `β`.
-/

@[expose] public section

open scoped BigOperators

noncomputable section

set_option synthInstance.maxHeartbeats 200000

namespace Dvoretzky

open Equiv

/-- A stage of the construction: a finite set `X` with a `2`-group `H` of permutations, a
finite family `π` of elements of `H` (the parametrisation used for orbit sums), and linear
forms `l x` on `ℝ^k`. -/
structure Stage (k : ℕ) where
  X : Type
  [fX : Fintype X]
  [dX : DecidableEq X]
  H : Subgroup (Perm X)
  hH : IsPGroup 2 H
  P : Type
  [fP : Fintype P]
  [nP : Nonempty P]
  π : P → Perm X
  hπ : ∀ p, π p ∈ H
  l : X → (EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ)

attribute [instance] Stage.fX Stage.dX Stage.fP Stage.nP

variable {k : ℕ}

namespace Stage

/-- The orbit sum attached to an exponent vector `β`. -/
def orb (S : Stage k) (β : S.X → ℕ) (z : EuclideanSpace ℝ (Fin k)) : ℝ :=
  ∑ p : S.P, ∏ x : S.X, (S.l (S.π p x) z) ^ (2 * β x)

/-- All orbit sums for `β` with `|β| ≤ δ` and support of size `≤ j` are radial. -/
def GoodUpTo (S : Stage k) (δ j : ℕ) : Prop :=
  ∀ β : S.X → ℕ, ∑ x, β x ≤ δ → (Finset.univ.filter fun x => β x ≠ 0).card ≤ j →
    IsRadial (2 * ∑ x, β x) (S.orb β)

/-- Not all linear forms vanish. -/
def NonDeg (S : Stage k) : Prop := ∃ x, S.l x ≠ 0

lemma orb_isPolyFun (S : Stage k) (β : S.X → ℕ) : IsPolyFun (2 * ∑ x, β x) (S.orb β) := by
  refine isPolyFun_sum _ _ fun p _ => ?_
  have := isPolyFun_prod Finset.univ (fun x => 1 * (2 * β x)) _
    (fun x _ => (isPolyFun_clm (S.l (S.π p x))).pow (2 * β x))
  simpa [Finset.mul_sum] using this

lemma orb_isHomogFun (S : Stage k) (β : S.X → ℕ) : IsHomogFun (2 * ∑ x, β x) (S.orb β) := by
  refine isHomogFun_sum _ _ fun p _ => ?_
  have := isHomogFun_prod Finset.univ (fun x => 1 * (2 * β x)) _
    (fun x _ => (isHomogFun_clm (S.l (S.π p x))).pow (2 * β x))
  simpa [Finset.mul_sum] using this

lemma orb_zero (S : Stage k) (z : EuclideanSpace ℝ (Fin k)) :
    S.orb (fun _ => 0) z = Fintype.card S.P := by
  simp [orb]

/-- The initial stage: one point, trivial group. -/
def init (hk : 0 < k) : Stage k where
  X := Unit
  H := ⊥
  hH := fun g => ⟨0, by
    obtain ⟨g, hg⟩ := g
    rw [Subgroup.mem_bot] at hg
    subst hg
    rfl⟩
  P := Unit
  π := fun _ => 1
  hπ := fun _ => Subgroup.one_mem _
  l := fun _ => EuclideanSpace.proj (⟨0, hk⟩ : Fin k)

lemma init_good (hk : 0 < k) (δ : ℕ) : (init hk).GoodUpTo δ 0 := by
  intro β _ hsupp
  have hβ : ∀ x, β x = 0 := by
    intro x
    by_contra h
    have : x ∈ Finset.univ.filter fun x => β x ≠ 0 := by simp [h]
    rw [Finset.card_eq_zero.1 (Nat.le_zero.1 hsupp)] at this
    simp at this
  have : β = fun _ => 0 := funext hβ
  subst this
  exact ⟨Fintype.card (init hk).P, fun z => by simp [orb_zero]⟩

lemma init_nonDeg (hk : 0 < k) : (init hk).NonDeg := by
  refine ⟨(), fun h => ?_⟩
  have := congrArg (fun f => f (EuclideanSpace.single (⟨0, hk⟩ : Fin k) 1)) h
  simp [init] at this

/-- The wreath-product step of the construction. -/
def step (S : Stage k) (a : ℕ)
    (σ : (Fin a → ZMod 2) → (EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k))) :
    Stage k where
  X := (Fin a → ZMod 2) × S.X
  H := wreath S.H
  hH := wreath_isPGroup S.H S.hH (fun κ => by funext i; exact CharTwo.add_self_eq_zero (κ i))
  P := (Fin a → ZMod 2) × ((Fin a → ZMod 2) → S.P)
  π := fun q => wreathPerm q.1 (fun y => S.π (q.2 y))
  hπ := fun q => wreathPerm_mem_wreath _ _ _ fun y => S.hπ _
  l := fun yx => (S.l yx.2).comp (σ yx.1)

lemma step_orb (S : Stage k) (a : ℕ)
    (σ : (Fin a → ZMod 2) → (EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)))
    (β : (S.step a σ).X → ℕ) (z : EuclideanSpace ℝ (Fin k)) :
    (S.step a σ).orb β z =
      ∑ κ : Fin a → ZMod 2, ∏ y : Fin a → ZMod 2, S.orb (fun x => β (y, x)) (σ (y + κ) z) := by
  classical
  unfold orb
  change ∑ q : (Fin a → ZMod 2) × ((Fin a → ZMod 2) → S.P), ∏ yx : (Fin a → ZMod 2) × S.X,
      ((S.l (S.π (q.2 yx.1) yx.2)) (σ (yx.1 + q.1) z)) ^ (2 * β yx) = _
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun κ _ => ?_
  simp only [Fintype.prod_prod_type]
  rw [Fintype.prod_sum (fun y p => ∏ x, ((S.l (S.π p x)) (σ (y + κ) z)) ^ (2 * β (y, x)))]

/-- Index type for the family of orbit sums to be averaged at a step. -/
abbrev Idx (S : Stage k) (δ : ℕ) := {β : S.X → Fin (δ + 1) // ∑ x, (β x : ℕ) ≤ δ}

lemma card_support_le_sum {X : Type} [Fintype X] (β : X → ℕ) :
    (Finset.univ.filter fun x => β x ≠ 0).card ≤ ∑ x, β x := by
  rw [Finset.card_eq_sum_ones]
  calc ∑ x ∈ Finset.univ.filter (fun x => β x ≠ 0), 1
      ≤ ∑ x ∈ Finset.univ.filter (fun x => β x ≠ 0), β x :=
        Finset.sum_le_sum fun x hx => Nat.one_le_iff_ne_zero.2 (Finset.mem_filter.1 hx).2
    _ ≤ ∑ x, β x := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

lemma step_good (S : Stage k) (δ j : ℕ) (hS : S.GoodUpTo δ j) (a : ℕ)
    (σ : (Fin a → ZMod 2) → (EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)))
    (s : (Fin a → ZMod 2) → ℝ) (hσ : ∀ y, IsSim (σ y) (s y))
    (havg : ∀ β : Idx S δ, IsRadial (2 * ∑ x, (β.1 x : ℕ))
      (fun z => ∑ y, S.orb (fun x => (β.1 x : ℕ)) (σ y z))) :
    (S.step a σ).GoodUpTo δ (j + 1) := by
  classical
  intro β hβδ hsupp
  set βy : (Fin a → ZMod 2) → S.X → ℕ := fun y x => β (y, x) with hβy
  have hsum : ∑ yx, β yx = ∑ y, ∑ x, βy y x := Fintype.sum_prod_type _
  have hcard : (Finset.univ.filter fun yx => β yx ≠ 0).card =
      ∑ y, (Finset.univ.filter fun x => βy y x ≠ 0).card := by
    rw [Finset.card_filter]
    rw [show (∑ i : (S.step a σ).X, if β i ≠ 0 then 1 else 0) =
      ∑ yx : (Fin a → ZMod 2) × S.X, (if β yx ≠ 0 then 1 else 0) from rfl,
      Fintype.sum_prod_type]
    simp [Finset.card_filter, βy]
  have hδy : ∀ y, ∑ x, βy y x ≤ δ := fun y =>
    le_trans (Finset.single_le_sum (f := fun y => ∑ x, βy y x) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ y)) (hsum ▸ hβδ)
  change IsRadial (2 * ∑ yx, β yx) ((S.step a σ).orb β)
  by_cases hA : ∃ y0, ∀ y, y ≠ y0 → ∀ x, βy y x = 0
  · obtain ⟨y0, hy0⟩ := hA
    have hzero : ∀ y, y ≠ y0 → βy y = fun _ => 0 := fun y hy => funext (hy0 y hy)
    have hβ0 : ∑ yx, β yx = ∑ x, βy y0 x := by
      rw [hsum, Finset.sum_eq_single y0 (fun y _ hy => by simp [hzero y hy]) (by simp)]
    let β' : Idx S δ := ⟨fun x => ⟨βy y0 x, Nat.lt_succ_of_le (le_trans
      (Finset.single_le_sum (f := βy y0) (fun _ _ => Nat.zero_le _) (Finset.mem_univ x))
      (hδy y0))⟩, by simpa using hδy y0⟩
    obtain ⟨c, hc⟩ := havg β'
    have hc' : ∀ z, ∑ y, S.orb (βy y0) (σ y z) = c * ‖z‖ ^ (2 * ∑ x, βy y0 x) := hc
    refine ⟨c * (Fintype.card S.P : ℝ) ^ (Fintype.card (Fin a → ZMod 2) - 1), fun z => ?_⟩
    rw [step_orb]
    have hprod : ∀ κ, ∏ y, S.orb (fun x => β (y, x)) (σ (y + κ) z) =
        S.orb (βy y0) (σ (y0 + κ) z) *
          (Fintype.card S.P : ℝ) ^ (Fintype.card (Fin a → ZMod 2) - 1) := by
      intro κ
      rw [Fintype.prod_eq_mul_prod_compl y0]
      congr 1
      rw [Finset.prod_congr rfl (g := fun _ => (Fintype.card S.P : ℝ)), Finset.prod_const,
        Finset.card_compl, Finset.card_singleton]
      intro y hy
      have hy' : y ≠ y0 := by simpa using hy
      have := hzero y hy'
      simp only [βy] at this
      rw [this, orb_zero]
    simp only [hprod]
    rw [← Finset.sum_mul]
    rw [show ∑ κ, S.orb (βy y0) (σ (y0 + κ) z) = ∑ y, S.orb (βy y0) (σ y z) from
      Fintype.sum_equiv (Equiv.addLeft y0) _ _ (fun κ => rfl)]
    rw [hc', hβ0]
    ring
  · push_neg at hA
    have hcy : ∀ y, (Finset.univ.filter fun x => βy y x ≠ 0).card ≤ j := by
      intro y
      obtain ⟨y1, hy1, x1, hx1⟩ := hA y
      have h1 : 1 ≤ (Finset.univ.filter fun x => βy y1 x ≠ 0).card :=
        Finset.card_pos.2 ⟨x1, by simp [hx1]⟩
      have h2 : (Finset.univ.filter fun x => βy y x ≠ 0).card +
          (Finset.univ.filter fun x => βy y1 x ≠ 0).card ≤
          ∑ y, (Finset.univ.filter fun x => βy y x ≠ 0).card := by
        rw [← Finset.sum_pair (f := fun y => (Finset.univ.filter fun x => βy y x ≠ 0).card)
          hy1.symm]
        exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      omega
    choose c hc using fun y => hS (βy y) (hδy y) (hcy y)
    refine ⟨∑ κ, ∏ y, c y * s (y + κ) ^ (2 * ∑ x, βy y x), fun z => ?_⟩
    rw [step_orb, Finset.sum_mul]
    refine Finset.sum_congr rfl fun κ _ => ?_
    have : ∀ y, S.orb (fun x => β (y, x)) (σ (y + κ) z) =
        (c y * s (y + κ) ^ (2 * ∑ x, βy y x)) * ‖z‖ ^ (2 * ∑ x, βy y x) := by
      intro y
      rw [show (fun x => β (y, x)) = βy y from rfl, hc y, (hσ _).2, mul_pow, mul_assoc]
    simp only [this]
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hsum, Finset.mul_sum]

lemma step_nonDeg (S : Stage k) (hS : S.NonDeg) (a : ℕ)
    (σ : (Fin a → ZMod 2) → (EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)))
    (s : (Fin a → ZMod 2) → ℝ) (hσ : ∀ y, IsSim (σ y) (s y)) (y0 : Fin a → ZMod 2)
    (hy0 : 0 < s y0) : (S.step a σ).NonDeg := by
  obtain ⟨x, hx⟩ := hS
  obtain ⟨v, hv⟩ : ∃ v, S.l x v ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (ContinuousLinearMap.ext h)
  have hinj : Function.Injective (σ y0).toLinearMap := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    have := (hσ y0).2 w
    rw [show (σ y0) w = 0 from hw, norm_zero] at this
    exact norm_eq_zero.1 ((mul_eq_zero.1 this.symm).resolve_left hy0.ne')
  obtain ⟨w, hw⟩ := (LinearMap.injective_iff_surjective.1 hinj) v
  refine ⟨(y0, x), fun h => hv ?_⟩
  have := congrArg (fun f => f w) h
  simp only [step, ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply] at this
  rw [← hw]
  exact this

lemma exists_stage (hk : 0 < k) (δ : ℕ) : ∀ j, ∃ S : Stage k, S.GoodUpTo δ j ∧ S.NonDeg := by
  intro j
  induction j with
  | zero => exact ⟨init hk, init_good hk δ, init_nonDeg hk⟩
  | succ j ih =>
    obtain ⟨S, hS, hS'⟩ := ih
    obtain ⟨a, σ, s, hσ, ⟨y0, hy0⟩, havg⟩ := averaging_pow2 hk (J := Idx S δ)
      (fun β => 2 * ∑ x, (β.1 x : ℕ)) (fun β => even_two_mul _)
      (fun β => S.orb (fun x => (β.1 x : ℕ))) (fun β => S.orb_isPolyFun _)
      (fun β => S.orb_isHomogFun _)
    exact ⟨S.step a σ, step_good S δ j hS a σ s hσ havg, step_nonDeg S hS' a σ s hσ y0 hy0⟩

/-- The output of the combinatorial construction. -/
theorem exists_good_stage (hk : 0 < k) (δ : ℕ) :
    ∃ S : Stage k, (∀ β : S.X → ℕ, ∑ x, β x ≤ δ → IsRadial (2 * ∑ x, β x) (S.orb β)) ∧
      S.NonDeg := by
  obtain ⟨S, hS, hS'⟩ := exists_stage hk δ δ
  exact ⟨S, fun β hβ => hS β hβ ((card_support_le_sum β).trans hβ), hS'⟩

end Stage

end Dvoretzky
