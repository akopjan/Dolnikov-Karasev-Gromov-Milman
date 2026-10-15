module

public import Mathlib

/-!
# Euler-class peeling for elementary abelian `2`-groups (algebra)

Let `M` be a `𝔽₂`-module with a "boundary" `d` and commuting operators `act q` (`q : Fin r`),
standing for the generators `g_q` of `(ℤ/2)^r`. A *family* of level `n` with *defect* `R` is a map
`β : (Fin r →₀ ℕ) → M` with

`d (β I) + ∑_{q, I_q ≠ 0} (1 + g_q) β (I - e_q) = R(I) • e`  for all `|I| ≤ n`,

where `e` is a fixed element (the empty simplex). In the language of generating functions this is
`D β = R e` for `D = d + ∑ U_q (1 + g_q)`; a chain map from the standard resolution of `𝔽₂` over
`𝔽₂[(ℤ/2)^r]` is a family with defect `1`.

The main result `IsFam.peel` is the chain-level form of the multiplicativity of the Euler class:
if `M'` is the chains of `X * A` for a two-point `(ℤ/2)^r`-set `A` (on which `g_q` acts by the
swap iff `ε q = 1`), then a family on `M'` with defect `R` produces a family on `M` (the chains of
`X`) with defect `(∑ ε_q U_q) · R`. Iterating, a family with defect `1` on the join of `D`
two-point sets would force the product of the `D` non-zero linear forms `∑ ε_q U_q` to vanish in
degrees `≤ n`, which is impossible when `D ≤ n` because `𝔽₂[U₁, …, U_r]` is a domain
(`exists_coeff_prod_linForm_ne_zero`).
-/

@[expose] public section

open scoped BigOperators

noncomputable section

namespace Dvoretzky.ElemAb

variable {r : ℕ}

/-- Shift of a multi-indexed family in direction `q` (multiplication by `U_q`). -/
def shift {M : Type*} [Zero M] (q : Fin r) (f : (Fin r →₀ ℕ) → M) (I : Fin r →₀ ℕ) : M :=
  if I q ≠ 0 then f (I - Finsupp.single q 1) else 0

lemma degree_sub_single_le (q : Fin r) (I : Fin r →₀ ℕ) :
    Finsupp.degree (I - Finsupp.single q 1) ≤ Finsupp.degree I :=
  Finsupp.degree_mono tsub_le_self

lemma shift_congr {M : Type*} [Zero M] (q : Fin r) {n : ℕ} {f g : (Fin r →₀ ℕ) → M}
    (h : ∀ J : Fin r →₀ ℕ, Finsupp.degree J ≤ n → f J = g J) {I : Fin r →₀ ℕ}
    (hI : Finsupp.degree I ≤ n) : shift q f I = shift q g I := by
  unfold shift
  split_ifs
  · exact h _ ((degree_sub_single_le q I).trans hI)
  · rfl

section Ops

variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]

lemma two_smul_eq_zero (a : M) : a + a = 0 := by
  rw [← two_smul (ZMod 2) a, show (2 : ZMod 2) = 0 from rfl, zero_smul]

lemma neg_eq_self' (a : M) : -a = a := by
  rw [neg_eq_iff_add_eq_zero, two_smul_eq_zero]

lemma eq_add_of_add_eq' {a b c : M} (h : a + b = c) : b = c + a := by
  rw [← h, add_comm a b, add_assoc, two_smul_eq_zero, add_zero]

/-- The total differential `D = d + ∑_q U_q (1 + g_q)`. -/
def DOp (d : M →ₗ[ZMod 2] M) (act : Fin r → M →ₗ[ZMod 2] M) (β : (Fin r →₀ ℕ) → M)
    (I : Fin r →₀ ℕ) : M :=
  d (β I) + ∑ q, shift q (fun J => β J + act q (β J)) I

/-- A family of level `n` with defect `R`. -/
def IsFam (d : M →ₗ[ZMod 2] M) (act : Fin r → M →ₗ[ZMod 2] M) (e : M) (n : ℕ)
    (R : (Fin r →₀ ℕ) → ZMod 2) (β : (Fin r →₀ ℕ) → M) : Prop :=
  ∀ I : Fin r →₀ ℕ, Finsupp.degree I ≤ n → DOp d act β I = R I • e

omit [Module (ZMod 2) M] in
lemma shift_add (q : Fin r) (f g : (Fin r →₀ ℕ) → M) (I : Fin r →₀ ℕ) :
    shift q (fun J => f J + g J) I = shift q f I + shift q g I := by
  unfold shift; split_ifs <;> simp

lemma shift_map {M' : Type*} [AddCommGroup M'] [Module (ZMod 2) M'] (q : Fin r)
    (L : M →ₗ[ZMod 2] M') (f : (Fin r →₀ ℕ) → M) (I : Fin r →₀ ℕ) :
    shift q (fun J => L (f J)) I = L (shift q f I) := by
  unfold shift; split_ifs <;> simp

lemma shift_smul (q : Fin r) (c : ZMod 2) (f : (Fin r →₀ ℕ) → M) (I : Fin r →₀ ℕ) :
    shift q (fun J => c • f J) I = c • shift q f I := by
  unfold shift; split_ifs <;> simp

omit [Module (ZMod 2) M] in
lemma shift_sum {ι : Type*} (s : Finset ι) (q : Fin r) (f : ι → (Fin r →₀ ℕ) → M)
    (I : Fin r →₀ ℕ) : shift q (fun J => ∑ i ∈ s, f i J) I = ∑ i ∈ s, shift q (f i) I := by
  unfold shift; split_ifs <;> simp

omit [Module (ZMod 2) M] in
/-- Shifts in two directions commute. -/
lemma shift_shift (q q' : Fin r) (f : (Fin r →₀ ℕ) → M) (I : Fin r →₀ ℕ) :
    shift q (shift q' f) I = shift q' (shift q f) I := by
  unfold shift
  by_cases hq : q = q'
  · subst hq; rfl
  have h1 : (I - Finsupp.single q 1 : Fin r →₀ ℕ) q' = I q' := by
    simp [hq]
  have h2 : (I - Finsupp.single q' 1 : Fin r →₀ ℕ) q = I q := by
    simp [Ne.symm hq]
  rw [h1, h2, tsub_right_comm]
  by_cases a : I q = 0 <;> by_cases b : I q' = 0 <;> simp [a, b]

variable (d : M →ₗ[ZMod 2] M) (act : Fin r → M →ₗ[ZMod 2] M)

lemma DOp_add (f g : (Fin r →₀ ℕ) → M) (I : Fin r →₀ ℕ) :
    DOp d act (fun J => f J + g J) I = DOp d act f I + DOp d act g I := by
  unfold DOp
  have : ∀ q, shift q (fun J => f J + g J + act q (f J + g J)) I =
      shift q (fun J => f J + act q (f J)) I + shift q (fun J => g J + act q (g J)) I := by
    intro q
    rw [← shift_add]
    congr 1; funext J; rw [map_add]; abel
  beta_reduce
  rw [map_add, Finset.sum_congr rfl (fun q _ => this q), Finset.sum_add_distrib]
  abel

lemma DOp_smul (c : ZMod 2) (f : (Fin r →₀ ℕ) → M) (I : Fin r →₀ ℕ) :
    DOp d act (fun J => c • f J) I = c • DOp d act f I := by
  unfold DOp
  have : ∀ q, shift q (fun J => c • f J + act q (c • f J)) I =
      c • shift q (fun J => f J + act q (f J)) I := by
    intro q
    rw [← shift_smul]
    congr 1; funext J; rw [map_smul, smul_add]
  beta_reduce
  rw [Finset.sum_congr rfl (fun q _ => this q), map_smul, smul_add, Finset.smul_sum]

lemma DOp_sum {ι : Type*} (s : Finset ι) (f : ι → (Fin r →₀ ℕ) → M) (I : Fin r →₀ ℕ) :
    DOp d act (fun J => ∑ i ∈ s, f i J) I = ∑ i ∈ s, DOp d act (f i) I := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [DOp, shift]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [DOp_add, ih]

lemma DOp_shift (q : Fin r) (f : (Fin r →₀ ℕ) → M) (I : Fin r →₀ ℕ) :
    DOp d act (shift q f) I = shift q (DOp d act f) I := by
  unfold DOp
  rw [shift_add, shift_map, shift_sum]
  congr 1
  refine Finset.sum_congr rfl fun q' _ => ?_
  rw [shift_shift q q']
  congr 1
  funext J
  rw [shift_add, shift_map]

lemma DOp_act (hcomm : ∀ q, ∀ x, d (act q x) = act q (d x))
    (hcomm' : ∀ q q', ∀ x, act q (act q' x) = act q' (act q x))
    (q : Fin r) (f : (Fin r →₀ ℕ) → M) (I : Fin r →₀ ℕ) :
    DOp d act (fun J => act q (f J)) I = act q (DOp d act f I) := by
  unfold DOp
  rw [map_add, map_sum, hcomm]
  congr 1
  refine Finset.sum_congr rfl fun q' _ => ?_
  rw [← shift_map]
  congr 1
  funext J
  rw [map_add, hcomm']

end Ops

/-! ### The peeling step -/

section Peel

variable {M M' : Type*} [AddCommGroup M] [Module (ZMod 2) M] [AddCommGroup M'] [Module (ZMod 2) M']
  {d : M →ₗ[ZMod 2] M} {act : Fin r → M →ₗ[ZMod 2] M} {e : M}
  {d' : M' →ₗ[ZMod 2] M'} {act' : Fin r → M' →ₗ[ZMod 2] M'} {e' : M'}

/-- The peeled defect `(∑ ε_q U_q) · R`. -/
def peelDefect (ε : Fin r → ZMod 2) (R : (Fin r →₀ ℕ) → ZMod 2) (I : Fin r →₀ ℕ) : ZMod 2 :=
  ∑ q, shift q (fun J => ε q * R J) I

/-- **Peeling a two-point join factor.** `πx, πa, πb` are the projections of the chains of `X * A`
(`A = {a, b}`) onto the chains of `X` (the part not involving `A`, the cone coefficient at `a`, and
the cone coefficient at `b`), and `g_q` swaps `a, b` iff `ε q = 1`. -/
theorem IsFam.peel (πx πa πb : M' →ₗ[ZMod 2] M) (ε : Fin r → ZMod 2)
    (hcomm : ∀ q, ∀ x, d (act q x) = act q (d x))
    (hcomm' : ∀ q q', ∀ x, act q (act q' x) = act q' (act q x))
    (hacte : ∀ q, act q e = e)
    (hdx : ∀ c, πx (d' c) = d (πx c) + (πa c + πb c))
    (hda : ∀ c, πa (d' c) = d (πa c))
    (hax : ∀ q c, πx (act' q c) = act q (πx c))
    (haa : ∀ q c, πa (act' q c) = act q (πa c + ε q • (πa c + πb c)))
    (hex : πx e' = e) (hea : πa e' = 0)
    {n : ℕ} {R : (Fin r →₀ ℕ) → ZMod 2} {β : (Fin r →₀ ℕ) → M'}
    (hβ : IsFam d' act' e' n R β) :
    IsFam d act e n (peelDefect ε R)
      (fun I => πa (β I) + ∑ q, ε q • shift q (fun J => act q (πx (β J))) I) := by
  intro I hI
  set x : (Fin r →₀ ℕ) → M := fun J => πx (β J) with hx
  set y : (Fin r →₀ ℕ) → M := fun J => πa (β J) with hy
  set p : (Fin r →₀ ℕ) → M := fun J => πa (β J) + πb (β J) with hp
  -- the `a`-component of the family relation at `I`
  have h2 : d (y I) + ∑ q, (shift q (fun J => y J + act q (y J)) I +
      ε q • shift q (fun J => act q (p J)) I) = 0 := by
    have := congrArg πa (hβ I hI)
    rw [map_smul, hea, smul_zero] at this
    rw [← this, DOp, map_add, map_sum, hda]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← shift_map, ← shift_smul, ← shift_add]
    congr 1; funext J; simp only [map_add, haa, map_smul, hy, hp]; abel
  -- the base component at degrees `≤ n`
  have h1 : ∀ J : Fin r →₀ ℕ, Finsupp.degree J ≤ n → p J = R J • e + DOp d act x J := by
    intro J hJ
    have := congrArg πx (hβ J hJ)
    rw [map_smul, hex] at this
    refine eq_add_of_add_eq' ?_
    rw [← this, DOp, DOp, map_add, map_sum, hdx]
    have : ∀ q, πx (shift q (fun K => β K + act' q (β K)) J) =
        shift q (fun K => x K + act q (x K)) J := by
      intro q; rw [← shift_map]; congr 1; funext K; rw [map_add, hax]
    simp only [this, hx, hp]
    abel
  -- `D y = ∑ ε_q U_q g_q p`
  have hDy : DOp d act y I = ∑ q, ε q • shift q (fun J => act q (p J)) I := by
    have h3 := eq_add_of_add_eq' (a := d (y I) + ∑ q, shift q (fun J => y J + act q (y J)) I)
      (b := ∑ q, ε q • shift q (fun J => act q (p J)) I) (c := 0)
      (by rw [← h2, Finset.sum_add_distrib]; abel)
    rw [h3, zero_add]; rfl
  -- substitute `p = R e + D x`
  have hsub : ∀ q, shift q (fun J => act q (p J)) I =
      shift q (fun J => R J • e) I + shift q (fun J => act q (DOp d act x J)) I := by
    intro q
    rw [shift_congr q (g := fun J => act q (R J • e + DOp d act x J))
      (fun J hJ => by rw [h1 J hJ]) hI, ← shift_add]
    congr 1; funext J; rw [map_add, map_smul, hacte]
  -- the result
  have hw : DOp d act (fun I => y I + ∑ q, ε q • shift q (fun J => act q (x J)) I) I =
      DOp d act y I + ∑ q, ε q • shift q (fun J => act q (DOp d act x J)) I := by
    rw [DOp_add, DOp_sum]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [DOp_smul, DOp_shift]
    congr 1
    unfold shift
    split_ifs
    · exact DOp_act d act hcomm hcomm' q x _
    · rfl
  show DOp d act (fun I => y I + ∑ q, ε q • shift q (fun J => act q (x J)) I) I = _
  rw [hw, hDy]
  simp only [hsub, smul_add, Finset.sum_add_distrib, add_assoc, two_smul_eq_zero, add_zero]
  rw [peelDefect, Finset.sum_smul]
  refine Finset.sum_congr rfl fun q _ => ?_
  unfold shift
  split_ifs
  · rw [mul_smul]
  · simp

/-- On the chains of the empty join (`d = 0`, trivial action) a family has zero defect. -/
theorem IsFam.defect_eq_zero_of_trivial {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    {e : M} (he : e ≠ 0) {n : ℕ} {R : (Fin r →₀ ℕ) → ZMod 2} {β : (Fin r →₀ ℕ) → M}
    (hβ : IsFam 0 (fun _ => LinearMap.id) e n R β) {I : Fin r →₀ ℕ}
    (hI : Finsupp.degree I ≤ n) : R I = 0 := by
  have h := hβ I hI
  have h0 : DOp (0 : M →ₗ[ZMod 2] M) (fun _ => LinearMap.id) β I = 0 := by
    simp only [DOp, LinearMap.zero_apply, zero_add, LinearMap.id_apply]
    refine Finset.sum_eq_zero fun q _ => ?_
    unfold shift
    split_ifs
    · exact two_smul_eq_zero _
    · rfl
  rw [h0] at h
  by_contra hR
  have : R I = 1 := by
    have : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
    exact this _ hR
  rw [this, one_smul] at h
  exact he h.symm

/-! ### Products of linear forms over `𝔽₂` -/

open MvPolynomial

/-- The coefficient of a multivariate polynomial at a monomial exponent. -/
def coeff {σ R : Type*} [CommSemiring R] (I : σ →₀ ℕ) (p : MvPolynomial σ R) : R := p.coeff I

@[simp] lemma coeff_def {σ R : Type*} [CommSemiring R] (I : σ →₀ ℕ) (p : MvPolynomial σ R) :
    coeff I p = p.coeff I := rfl

/-- The linear form `∑ ε_q U_q`. -/
def linForm (ε : Fin r → ZMod 2) : MvPolynomial (Fin r) (ZMod 2) := ∑ q, C (ε q) * X q

lemma coeff_linForm_mul (ε : Fin r → ZMod 2) (P : MvPolynomial (Fin r) (ZMod 2))
    (I : Fin r →₀ ℕ) :
    coeff I (linForm ε * P) = peelDefect ε (fun J => coeff J P) I := by
  classical
  rw [coeff_def]
  rw [linForm, Finset.sum_mul, coeff_sum, peelDefect]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [mul_assoc, coeff_C_mul, coeff_X_mul']
  simp only [coeff_def, shift, Finsupp.mem_support_iff]
  split_ifs <;> simp

lemma linForm_ne_zero {ε : Fin r → ZMod 2} (hε : ε ≠ 0) : linForm ε ≠ 0 := by
  classical
  obtain ⟨q, hq⟩ := Function.ne_iff.1 hε
  intro h
  have := congrArg (coeff (Finsupp.single q 1)) h
  rw [coeff_def, linForm, coeff_sum, coeff_def, AddMonoidAlgebra.coeff_zero] at this
  rw [Finset.sum_eq_single q] at this
  · rw [coeff_C_mul, coeff_X] at this
    simp at this
    exact hq this
  · intro q' _ hq'
    rw [coeff_C_mul, coeff_X]
    have : Finsupp.single q' 1 ≠ Finsupp.single q 1 := by
      intro e
      exact hq' (Finsupp.single_left_injective one_ne_zero e)
    simp [this]
  · simp

/-- A product of `D` non-zero linear forms over `𝔽₂` has a non-zero coefficient in degree `D`. -/
theorem exists_coeff_prod_linForm_ne_zero {D : ℕ} (ε : Fin D → Fin r → ZMod 2)
    (hε : ∀ k, ε k ≠ 0) :
    ∃ I : Fin r →₀ ℕ, Finsupp.degree I = D ∧ coeff I (∏ k, linForm (ε k)) ≠ 0 := by
  have hne : (∏ k, linForm (ε k)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => linForm_ne_zero (hε k)
  have hhom : (∏ k, linForm (ε k)).IsHomogeneous D := by
    have := IsHomogeneous.prod Finset.univ (fun k => linForm (ε k)) (fun _ => 1)
      (fun k _ => IsHomogeneous.sum _ _ _ fun q _ => isHomogeneous_C_mul_X _ _)
    simpa using this
  obtain ⟨I, hI⟩ := MvPolynomial.ne_zero_iff.1 hne
  refine ⟨I, ?_, hI⟩
  by_contra h
  exact hI (hhom.coeff_eq_zero h)

end Peel

end Dvoretzky.ElemAb
