module

public import Mathlib

/-!
# Wreath products of permutation groups

For an additive group `Y` and a subgroup `H ≤ Perm X`, the wreath product `H ≀ Y` acts on
`Y × X` by `(y, x) ↦ (y + κ, g y x)` with `κ : Y` and `g : Y → H`. If `H` is a `2`-group and
`Y` has exponent `2`, then so is the wreath product.
-/

@[expose] public section

noncomputable section

namespace Dvoretzky

open Equiv

variable {Y X : Type} [AddCommGroup Y]

/-- The permutation `(y, x) ↦ (y + κ, g y x)` of `Y × X`. -/
def wreathPerm (κ : Y) (g : Y → Perm X) : Perm (Y × X) where
  toFun p := (p.1 + κ, g p.1 p.2)
  invFun p := (p.1 - κ, (g (p.1 - κ)).symm p.2)
  left_inv p := by simp
  right_inv p := by simp

@[simp] lemma wreathPerm_apply (κ : Y) (g : Y → Perm X) (p : Y × X) :
    wreathPerm κ g p = (p.1 + κ, g p.1 p.2) := rfl

lemma wreathPerm_mul (κ κ' : Y) (g g' : Y → Perm X) :
    wreathPerm κ g * wreathPerm κ' g' = wreathPerm (κ' + κ) (fun y => g (y + κ') * g' y) := by
  ext p
  · simp [add_assoc]
  · simp

lemma wreathPerm_one : wreathPerm (0 : Y) (fun _ => (1 : Perm X)) = 1 := by
  ext p <;> simp

lemma wreathPerm_inv (κ : Y) (g : Y → Perm X) :
    (wreathPerm κ g)⁻¹ = wreathPerm (-κ) (fun y => (g (y - κ))⁻¹) := by
  rw [eq_comm, ← mul_eq_one_iff_eq_inv, wreathPerm_mul]
  convert wreathPerm_one (Y := Y) (X := X) using 2
  · abel
  · funext y
    simp

/-- The wreath product `H ≀ Y` as a subgroup of `Perm (Y × X)`. -/
def wreath (H : Subgroup (Perm X)) : Subgroup (Perm (Y × X)) where
  carrier := {w | ∃ κ g, (∀ y, g y ∈ H) ∧ w = wreathPerm κ g}
  mul_mem' := by
    rintro _ _ ⟨κ, g, hg, rfl⟩ ⟨κ', g', hg', rfl⟩
    exact ⟨_, _, fun y => H.mul_mem (hg _) (hg' y), wreathPerm_mul κ κ' g g'⟩
  one_mem' := ⟨0, fun _ => 1, fun _ => H.one_mem, wreathPerm_one.symm⟩
  inv_mem' := by
    rintro _ ⟨κ, g, hg, rfl⟩
    exact ⟨_, _, fun y => H.inv_mem (hg _), wreathPerm_inv κ g⟩

lemma wreathPerm_mem_wreath (H : Subgroup (Perm X)) (κ : Y) (g : Y → Perm X)
    (hg : ∀ y, g y ∈ H) : wreathPerm κ g ∈ wreath H :=
  ⟨κ, g, hg, rfl⟩

lemma wreathPerm_pow (H : Subgroup (Perm X)) (κ : Y) (g : Y → Perm X) (hg : ∀ y, g y ∈ H)
    (n : ℕ) : ∃ g' : Y → Perm X, (∀ y, g' y ∈ H) ∧ wreathPerm κ g ^ n = wreathPerm (n • κ) g' := by
  induction n with
  | zero => exact ⟨fun _ => 1, fun _ => H.one_mem, by simp [wreathPerm_one]⟩
  | succ n ih =>
    obtain ⟨g', hg', h⟩ := ih
    refine ⟨fun y => g' (y + κ) * g y, fun y => H.mul_mem (hg' _) (hg y), ?_⟩
    rw [pow_succ, h, wreathPerm_mul, succ_nsmul, add_comm κ]

lemma wreathPerm_zero_pow (g : Y → Perm X) (n : ℕ) :
    wreathPerm (0 : Y) g ^ n = wreathPerm 0 (g ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact wreathPerm_one.symm
  | succ n ih =>
    rw [pow_succ, ih, wreathPerm_mul]
    simp [pow_succ]
    rfl

lemma wreath_isPGroup [Finite X] (H : Subgroup (Perm X)) (hH : IsPGroup 2 H)
    (hY : ∀ κ : Y, κ + κ = 0) : IsPGroup 2 (wreath (Y := Y) H) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 hH
  have hexp : ∀ h ∈ H, h ^ (2 ^ m) = 1 := by
    intro h hh
    have := pow_card_eq_one' (G := H) (x := ⟨h, hh⟩)
    rw [hm] at this
    exact congrArg Subtype.val this
  rintro ⟨w, κ, g, hg, rfl⟩
  refine ⟨m + 1, Subtype.ext ?_⟩
  obtain ⟨g', hg', h2⟩ := wreathPerm_pow H κ g hg 2
  rw [two_nsmul, hY] at h2
  simp only [Subgroup.coe_pow, Subgroup.coe_one]
  rw [pow_succ', pow_mul, h2, wreathPerm_zero_pow]
  convert wreathPerm_one (Y := Y) (X := X) using 2
  funext y
  exact hexp _ (hg' y)

end Dvoretzky
