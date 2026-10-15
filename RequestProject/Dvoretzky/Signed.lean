module

public import Mathlib

/-!
# Signed permutation groups

For a group `H` of permutations of a finite set `X`, the group of signed permutations
`y ↦ (x ↦ ε x * y (π x))` (`ε : X → {±1}`, `π ∈ H`) acting on `EuclideanSpace ℝ X` by
linear isometries. If `H` is a `2`-group, so is this group (it is `(ℤ/2)^X ⋊ H`).
-/

@[expose] public section

open scoped BigOperators

noncomputable section

namespace Dvoretzky

open Equiv

variable {X : Type} [Fintype X]

lemma units_int_sq_real (u : ℤˣ) : ((u : ℤ) : ℝ) * ((u : ℤ) : ℝ) = 1 := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> simp

/-- The signed permutation `y ↦ (x ↦ ε x * y (π x))` as a linear equivalence. -/
def signedPermLE (ε : X → ℤˣ) (π : Perm X) :
    EuclideanSpace ℝ X ≃ₗ[ℝ] EuclideanSpace ℝ X where
  toFun y := WithLp.toLp 2 (fun x => ((ε x : ℤ) : ℝ) * y (π x))
  map_add' y y' := by ext x; simp [mul_add]
  map_smul' c y := by ext x; simp; ring
  invFun y := WithLp.toLp 2 (fun x => ((ε (π.symm x) : ℤ) : ℝ) * y (π.symm x))
  left_inv y := by
    ext x
    simp only [Equiv.apply_symm_apply]
    rw [← mul_assoc, units_int_sq_real, one_mul]
  right_inv y := by
    ext x
    simp only [Equiv.symm_apply_apply]
    rw [← mul_assoc, units_int_sq_real, one_mul]

/-- The signed permutation `y ↦ (x ↦ ε x * y (π x))` as a linear isometry equivalence. -/
def signedPerm (ε : X → ℤˣ) (π : Perm X) :
    EuclideanSpace ℝ X ≃ₗᵢ[ℝ] EuclideanSpace ℝ X where
  toLinearEquiv := signedPermLE ε π
  norm_map' y := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    simp only [signedPermLE, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
      PiLp.toLp_apply, Real.norm_eq_abs, sq_abs]
    rw [← Equiv.sum_comp π (fun x => (y x) ^ 2)]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [mul_pow, sq, units_int_sq_real, one_mul]

@[simp] lemma signedPerm_apply (ε : X → ℤˣ) (π : Perm X) (y : EuclideanSpace ℝ X) (x : X) :
    signedPerm ε π y x = ((ε x : ℤ) : ℝ) * y (π x) := rfl

lemma signedPerm_mul (ε ε' : X → ℤˣ) (π π' : Perm X) :
    signedPerm ε π * signedPerm ε' π' = signedPerm (fun x => ε x * ε' (π x)) (π' * π) := by
  ext y x
  simp [mul_assoc]

lemma signedPerm_one : signedPerm (fun _ : X => (1 : ℤˣ)) 1 = 1 := by
  ext y x
  simp

/-- The group of signed permutations with underlying permutation in `H`. -/
def signedGroup (H : Subgroup (Perm X)) :
    Subgroup (EuclideanSpace ℝ X ≃ₗᵢ[ℝ] EuclideanSpace ℝ X) where
  carrier := {g | ∃ ε π, π ∈ H ∧ g = signedPerm ε π}
  mul_mem' := by
    rintro _ _ ⟨ε, π, hπ, rfl⟩ ⟨ε', π', hπ', rfl⟩
    exact ⟨_, _, H.mul_mem hπ' hπ, signedPerm_mul ε ε' π π'⟩
  one_mem' := ⟨fun _ => 1, 1, H.one_mem, signedPerm_one.symm⟩
  inv_mem' := by
    rintro _ ⟨ε, π, hπ, rfl⟩
    refine ⟨fun x => ε (π⁻¹ x), π⁻¹, H.inv_mem hπ, ?_⟩
    rw [eq_comm, ← mul_eq_one_iff_eq_inv, signedPerm_mul, mul_inv_cancel]
    convert signedPerm_one (X := X) using 2
    funext x
    exact Int.units_mul_self _

lemma signedPerm_mem (H : Subgroup (Perm X)) (ε : X → ℤˣ) {π : Perm X} (hπ : π ∈ H) :
    signedPerm ε π ∈ signedGroup H :=
  ⟨ε, π, hπ, rfl⟩

lemma signedGroup_finite [DecidableEq X] (H : Subgroup (Perm X)) : Finite (signedGroup H) := by
  have : ((signedGroup H : Set (EuclideanSpace ℝ X ≃ₗᵢ[ℝ] EuclideanSpace ℝ X))) ⊆
      Set.range (fun p : (X → ℤˣ) × Perm X => signedPerm p.1 p.2) := by
    rintro _ ⟨ε, π, -, rfl⟩
    exact ⟨(ε, π), rfl⟩
  exact ((Set.finite_range _).subset this).to_subtype

lemma signedPerm_pow (ε : X → ℤˣ) (π : Perm X) (n : ℕ) :
    ∃ ε' : X → ℤˣ, signedPerm ε π ^ n = signedPerm ε' (π ^ n) := by
  induction n with
  | zero => exact ⟨fun _ => 1, by rw [pow_zero, pow_zero, signedPerm_one]⟩
  | succ n ih =>
    obtain ⟨ε', h⟩ := ih
    refine ⟨fun x => ε' x * ε ((π ^ n) x), ?_⟩
    rw [pow_succ, h, signedPerm_mul, pow_succ']

lemma signedGroup_isPGroup [DecidableEq X] (H : Subgroup (Perm X)) (hH : IsPGroup 2 H) :
    IsPGroup 2 (signedGroup H) := by
  rintro ⟨g, ε, π, hπ, rfl⟩
  obtain ⟨m, hm⟩ := hH ⟨π, hπ⟩
  have hm' : π ^ (2 ^ m) = 1 := congrArg Subtype.val hm
  refine ⟨m + 1, Subtype.ext ?_⟩
  obtain ⟨ε', h⟩ := signedPerm_pow ε π (2 ^ m)
  simp only [Subgroup.coe_pow, Subgroup.coe_one]
  rw [pow_succ, pow_mul, h, hm', sq, signedPerm_mul]
  convert signedPerm_one (X := X) using 2
  · funext x
    simp only [Perm.one_apply]
    exact Int.units_mul_self _
  · rw [mul_one]

end Dvoretzky
