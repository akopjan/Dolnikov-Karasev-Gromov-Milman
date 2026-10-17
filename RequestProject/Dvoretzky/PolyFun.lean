module

public import Mathlib

/-!
# Polynomial functions on Euclidean spaces

Basic vocabulary used throughout the formalization of the Dol'nikov–Karasev
Dvoretzky-type theorem for polynomials:

* `IsPolyFun e φ` : `φ` is a polynomial function of total degree `≤ e`;
* `IsHomogFun e φ` : `φ (t • z) = t ^ e * φ z`;
* `IsRadial e φ` : `φ z = c * ‖z‖ ^ e` for some constant `c`
  (i.e. `φ` is proportional to `Q ^ (e / 2)`, where `Q` is the standard quadratic form);
* `IsSim σ s` : `σ` is a similarity transform with ratio `s ≥ 0` (possibly zero).
-/

@[expose] public section

open scoped BigOperators

noncomputable section

namespace Dvoretzky

variable {ι κ : Type} [Fintype ι] [Fintype κ]

/-- `φ` is a polynomial function of total degree at most `e`. -/
def IsPolyFun (e : ℕ) (φ : EuclideanSpace ℝ ι → ℝ) : Prop :=
  ∃ p : MvPolynomial ι ℝ, p.totalDegree ≤ e ∧ ∀ z, φ z = MvPolynomial.eval (fun i => z i) p

/-- `φ` is (positively and negatively) homogeneous of degree `e`. -/
def IsHomogFun (e : ℕ) (φ : EuclideanSpace ℝ ι → ℝ) : Prop :=
  ∀ (t : ℝ) (z : EuclideanSpace ℝ ι), φ (t • z) = t ^ e * φ z

/-- `φ` is proportional to `‖z‖ ^ e`. -/
def IsRadial (e : ℕ) (φ : EuclideanSpace ℝ ι → ℝ) : Prop :=
  ∃ c : ℝ, ∀ z, φ z = c * ‖z‖ ^ e

/-- `σ` is a similarity transform (a rotation composed with a homothety of ratio `s ≥ 0`,
the zero map being allowed). -/
def IsSim (σ : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) (s : ℝ) : Prop :=
  0 ≤ s ∧ ∀ w, ‖σ w‖ = s * ‖w‖

/-! ### Polynomial functions -/

omit [Fintype ι] in
lemma IsPolyFun.mono {e e' : ℕ} {φ : EuclideanSpace ℝ ι → ℝ} (h : IsPolyFun e φ) (he : e ≤ e') :
    IsPolyFun e' φ := by
  obtain ⟨p, hp, hφ⟩ := h
  exact ⟨p, hp.trans he, hφ⟩

omit [Fintype ι] in
lemma isPolyFun_const (c : ℝ) : IsPolyFun (ι := ι) 0 (fun _ => c) :=
  ⟨MvPolynomial.C c, by simp, fun z => by simp⟩

omit [Fintype ι] in
lemma isPolyFun_coord (i : ι) : IsPolyFun (ι := ι) 1 (fun z => z i) :=
  ⟨MvPolynomial.X i, by simp, fun z => by simp⟩

omit [Fintype ι] in
lemma IsPolyFun.add {e : ℕ} {φ ψ : EuclideanSpace ℝ ι → ℝ} (hφ : IsPolyFun e φ)
    (hψ : IsPolyFun e ψ) : IsPolyFun e (fun z => φ z + ψ z) := by
  obtain ⟨p, hp, hφ⟩ := hφ
  obtain ⟨q, hq, hψ⟩ := hψ
  refine ⟨p + q, (MvPolynomial.totalDegree_add p q).trans (max_le hp hq), fun z => ?_⟩
  simp [hφ, hψ]

omit [Fintype ι] in
lemma IsPolyFun.mul {e e' : ℕ} {φ ψ : EuclideanSpace ℝ ι → ℝ} (hφ : IsPolyFun e φ)
    (hψ : IsPolyFun e' ψ) : IsPolyFun (e + e') (fun z => φ z * ψ z) := by
  obtain ⟨p, hp, hφ⟩ := hφ
  obtain ⟨q, hq, hψ⟩ := hψ
  refine ⟨p * q, (MvPolynomial.totalDegree_mul p q).trans (add_le_add hp hq), fun z => ?_⟩
  simp [hφ, hψ]

omit [Fintype ι] in
lemma IsPolyFun.const_mul {e : ℕ} {φ : EuclideanSpace ℝ ι → ℝ} (hφ : IsPolyFun e φ) (c : ℝ) :
    IsPolyFun e (fun z => c * φ z) := by
  simpa using (isPolyFun_const c).mul hφ

omit [Fintype ι] in
lemma IsPolyFun.neg {e : ℕ} {φ : EuclideanSpace ℝ ι → ℝ} (hφ : IsPolyFun e φ) :
    IsPolyFun e (fun z => -φ z) := by
  simpa using hφ.const_mul (-1)

omit [Fintype ι] in
lemma IsPolyFun.sub {e : ℕ} {φ ψ : EuclideanSpace ℝ ι → ℝ} (hφ : IsPolyFun e φ)
    (hψ : IsPolyFun e ψ) : IsPolyFun e (fun z => φ z - ψ z) := by
  simpa [sub_eq_add_neg] using hφ.add hψ.neg

omit [Fintype ι] in
lemma IsPolyFun.pow {e : ℕ} {φ : EuclideanSpace ℝ ι → ℝ} (hφ : IsPolyFun e φ) (n : ℕ) :
    IsPolyFun (e * n) (fun z => φ z ^ n) := by
  induction n with
  | zero => simpa using isPolyFun_const (ι := ι) 1
  | succ n ih =>
    have := ih.mul hφ
    simpa [pow_succ, mul_add] using this

omit [Fintype ι] in
lemma isPolyFun_sum {α : Type*} (s : Finset α) {e : ℕ} (φ : α → EuclideanSpace ℝ ι → ℝ)
    (h : ∀ a ∈ s, IsPolyFun e (φ a)) : IsPolyFun e (fun z => ∑ a ∈ s, φ a z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isPolyFun_const (ι := ι) 0).mono (Nat.zero_le e)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (by simp)).add (ih fun b hb => h b (by simp [hb]))

omit [Fintype ι] in
lemma isPolyFun_prod {α : Type*} (s : Finset α) (e : α → ℕ) (φ : α → EuclideanSpace ℝ ι → ℝ)
    (h : ∀ a ∈ s, IsPolyFun (e a) (φ a)) :
    IsPolyFun (∑ a ∈ s, e a) (fun z => ∏ a ∈ s, φ a z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isPolyFun_const (ι := ι) 1
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (h a (by simp)).mul (ih fun b hb => h b (by simp [hb]))

/-- Every continuous linear functional is a polynomial function of degree `≤ 1`. -/
lemma isPolyFun_clm (l : EuclideanSpace ℝ ι →L[ℝ] ℝ) : IsPolyFun 1 (fun z => l z) := by
  classical
  have key : ∀ z : EuclideanSpace ℝ ι, l z = ∑ i, l (EuclideanSpace.single i 1) * z i := by
    intro z
    conv_lhs => rw [← (EuclideanSpace.basisFun ι ℝ).sum_repr z]
    simp [map_sum, mul_comm]
  have : IsPolyFun 1 (fun z : EuclideanSpace ℝ ι => ∑ i, l (EuclideanSpace.single i 1) * z i) :=
    isPolyFun_sum _ _ fun i _ => (isPolyFun_coord i).const_mul _
  simpa [← key] using this

/-- Monomial expansion of a polynomial function. -/
lemma IsPolyFun.eq_sum_monomials {e : ℕ} {φ : EuclideanSpace ℝ ι → ℝ} (h : IsPolyFun e φ) :
    ∃ p : MvPolynomial ι ℝ, p.totalDegree ≤ e ∧
      ∀ z, φ z = ∑ m ∈ p.support, p.coeff m * ∏ i, (z i) ^ (m i) := by
  obtain ⟨p, hp, hφ⟩ := h
  exact ⟨p, hp, fun z => by rw [hφ, MvPolynomial.eval_eq']⟩

/-- Composition of a polynomial function with a continuous linear map. -/
lemma IsPolyFun.comp_clm {e : ℕ} {φ : EuclideanSpace ℝ ι → ℝ} (h : IsPolyFun e φ)
    (A : EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ ι) : IsPolyFun e (fun w => φ (A w)) := by
  classical
  obtain ⟨p, hp, hφ⟩ := h.eq_sum_monomials
  simp only [hφ]
  refine isPolyFun_sum _ _ fun m hm => ?_
  have hdeg : (∑ i, m i) ≤ e := by
    have := MvPolynomial.le_totalDegree hm
    rw [Finsupp.sum_fintype _ _ (by simp)] at this
    exact this.trans hp
  refine (IsPolyFun.const_mul ?_ _)
  refine (isPolyFun_prod Finset.univ (fun i => 1 * m i) _ fun i _ => ?_).mono (by simpa using hdeg)
  have hl := isPolyFun_clm ((EuclideanSpace.proj i : EuclideanSpace ℝ ι →L[ℝ] ℝ).comp A)
  exact hl.pow (m i)

omit [Fintype ι] in
lemma IsPolyFun.continuous {e : ℕ} {φ : EuclideanSpace ℝ ι → ℝ} (h : IsPolyFun e φ) :
    Continuous φ := by
  obtain ⟨p, -, hφ⟩ := h
  have : φ = fun z => MvPolynomial.eval (fun i => z i) p := funext hφ
  rw [this]
  exact (MvPolynomial.continuous_eval p).comp (PiLp.continuous_ofLp 2 _)

/-- `‖z‖ ^ (2 * r)` is a polynomial function of degree `≤ 2 * r`. -/
lemma isPolyFun_norm_pow (r : ℕ) : IsPolyFun (ι := ι) (2 * r) (fun z => ‖z‖ ^ (2 * r)) := by
  have h2 : IsPolyFun (ι := ι) 2 (fun z => ‖z‖ ^ 2) := by
    have h1 : IsPolyFun (ι := ι) 2 (fun z => ∑ i, (z i) ^ 2) :=
      isPolyFun_sum _ _ fun i _ => by simpa using (isPolyFun_coord (ι := ι) i).pow 2
    have heq : (fun z : EuclideanSpace ℝ ι => ‖z‖ ^ 2) = fun z => ∑ i, (z i) ^ 2 :=
      funext fun z => by rw [EuclideanSpace.norm_sq_eq]; simp
    rw [heq]
    exact h1
  simpa [pow_mul] using h2.pow r

/-! ### Uniqueness on a finite grid -/

/-- A finite grid of points in `EuclideanSpace ℝ ι`, with all coordinates in `{0, …, e}`. -/
def grid (ι : Type) [Fintype ι] [DecidableEq ι] (e : ℕ) : Finset (EuclideanSpace ℝ ι) :=
  (Fintype.piFinset fun _ : ι => (Finset.range (e + 1)).image (fun n : ℕ => (n : ℝ))).image
    (WithLp.toLp 2)

/-- A polynomial function of degree `≤ e` vanishing on `grid ι e` vanishes identically. -/
lemma IsPolyFun.eq_zero_of_grid [DecidableEq ι] {e : ℕ} {φ : EuclideanSpace ℝ ι → ℝ}
    (h : IsPolyFun e φ) (hz : ∀ z ∈ grid ι e, φ z = 0) : ∀ z, φ z = 0 := by
  obtain ⟨p, hp, hφ⟩ := h
  have hp0 : p = 0 := by
    refine MvPolynomial.eq_zero_of_eval_zero_at_prod_finset p
      (fun _ => (Finset.range (e + 1)).image (fun n : ℕ => (n : ℝ))) (fun i => ?_) (fun x hx => ?_)
    · rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
      exact Nat.lt_succ_of_le ((MvPolynomial.degreeOf_le_totalDegree p i).trans hp)
    · have := hz (WithLp.toLp 2 x) (by
        simp only [grid, Finset.mem_image]
        exact ⟨x, Fintype.mem_piFinset.2 hx, rfl⟩)
      rw [hφ] at this
      simpa using this
  intro z
  rw [hφ, hp0]
  simp

/-! ### Homogeneous functions -/

omit [Fintype ι] in
lemma isHomogFun_const (c : ℝ) : IsHomogFun (ι := ι) 0 (fun _ => c) := fun t z => by simp

lemma isHomogFun_clm (l : EuclideanSpace ℝ ι →L[ℝ] ℝ) : IsHomogFun 1 (fun z => l z) :=
  fun t z => by simp

omit [Fintype ι] in
lemma IsHomogFun.mul {e e' : ℕ} {φ ψ : EuclideanSpace ℝ ι → ℝ} (hφ : IsHomogFun e φ)
    (hψ : IsHomogFun e' ψ) : IsHomogFun (e + e') (fun z => φ z * ψ z) := fun t z => by
  simp only [hφ t z, hψ t z, pow_add]; ring

omit [Fintype ι] in
lemma IsHomogFun.pow {e : ℕ} {φ : EuclideanSpace ℝ ι → ℝ} (hφ : IsHomogFun e φ) (n : ℕ) :
    IsHomogFun (e * n) (fun z => φ z ^ n) := fun t z => by
  simp only [hφ t z, mul_pow, pow_mul]

omit [Fintype ι] in
lemma IsHomogFun.const_mul {e : ℕ} {φ : EuclideanSpace ℝ ι → ℝ} (hφ : IsHomogFun e φ) (c : ℝ) :
    IsHomogFun e (fun z => c * φ z) := fun t z => by
  simp only [hφ t z]; ring

omit [Fintype ι] in
lemma isHomogFun_sum {α : Type*} (s : Finset α) {e : ℕ} (φ : α → EuclideanSpace ℝ ι → ℝ)
    (h : ∀ a ∈ s, IsHomogFun e (φ a)) : IsHomogFun e (fun z => ∑ a ∈ s, φ a z) := fun t z => by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun a ha => h a ha t z

omit [Fintype ι] in
lemma isHomogFun_prod {α : Type*} (s : Finset α) (e : α → ℕ) (φ : α → EuclideanSpace ℝ ι → ℝ)
    (h : ∀ a ∈ s, IsHomogFun (e a) (φ a)) :
    IsHomogFun (∑ a ∈ s, e a) (fun z => ∏ a ∈ s, φ a z) := fun t z => by
  show ∏ a ∈ s, φ a (t • z) = t ^ (∑ a ∈ s, e a) * ∏ a ∈ s, φ a z
  rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun a ha => h a ha t z

lemma IsHomogFun.comp_clm {e : ℕ} {φ : EuclideanSpace ℝ ι → ℝ} (h : IsHomogFun e φ)
    (A : EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ ι) : IsHomogFun e (fun w => φ (A w)) :=
  fun t z => by simp [h t]

lemma IsHomogFun.map_zero {e : ℕ} {φ : EuclideanSpace ℝ ι → ℝ} (h : IsHomogFun e φ)
    (he : 0 < e) : φ 0 = 0 := by
  have := h 0 0
  simpa [zero_pow he.ne'] using this

omit [Fintype ι] in
lemma IsHomogFun.eq_const {φ : EuclideanSpace ℝ ι → ℝ} (h : IsHomogFun 0 φ) (z) :
    φ z = φ 0 := by
  have := h 0 z
  simpa using this.symm

end Dvoretzky
