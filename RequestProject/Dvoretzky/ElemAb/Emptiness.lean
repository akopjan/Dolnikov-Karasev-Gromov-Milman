module

public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import RequestProject.Dvoretzky.JoinEmptiness
public import RequestProject.Dvoretzky.ElemAb.Main

/-!
# Lemma 1 for elementary abelian `2`-groups

`joinEmptiness_elemAb`: the emptiness statement `JoinEmptiness` holds for `(ℤ/2)^r`. Given a
finite `(ℤ/2)^r`-set `S` without fixed points, every orbit `O` admits a non-zero character `χ_O`
vanishing on its stabiliser, hence an equivariant map from `O` to the two-point set on which
`g` acts by the translation `χ_O(g)`. This maps `S^{*J}` equivariantly to a join of two-point sets,
one per pair `(j, O)`, and `elemAb_join` applies.

Consequently `JoinOrbitCollapse` (Lemma 1 in the form used by Theorem 1) holds for every
elementary abelian `2`-group (`joinOrbitCollapse_elemAb`, `joinOrbitCollapse_of_mul_self_eq_one`).
-/

@[expose] public section

open scoped BigOperators

noncomputable section

namespace Dvoretzky.ElemAb

open Dvoretzky Dvoretzky.Dold

instance (r : ℕ) : @Module (ZMod 2) (Fin r → ZMod 2) (ZMod.instField 2).toDivisionRing.toSemiring Pi.addCommGroup.toAddCommMonoid :=
  Pi.Function.module (Fin r) (ZMod 2) (ZMod 2)

variable {r : ℕ}

lemma vtxPt_mem_groupJoin {G : Type} [Fintype G] [DecidableEq G] {N j : ℕ} (hj : j < N) (h : G) :
    vtxPt N j h ∈ GroupJoin G N := by
  classical
  refine ⟨fun i h => by simp only [vtxPt]; split_ifs <;> norm_num, fun i a b ha hb => ?_, ?_⟩
  · simp only [vtxPt] at ha hb
    split_ifs at ha hb with h1 h2
    · rw [h1.2, h2.2]
    all_goals simp_all
  · rw [Finset.sum_eq_single ⟨j, hj⟩]
    · simp [vtxPt]
    · intro i _ hi
      refine Finset.sum_eq_zero fun h' _ => ?_
      simp only [vtxPt]
      rw [if_neg]
      rintro ⟨e, -⟩
      exact hi (Fin.ext e)
    · simp

section Orbits

variable (S : Type) [Fintype S] [MulAction (EA r) S]

/-- The stabiliser of `s`, as a subspace of `𝔽₂^r`. -/
def stabSub (s : S) : Submodule (ZMod 2) (Fin r → ZMod 2) where
  carrier := {v | Multiplicative.ofAdd v • s = s}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [ofAdd_add, mul_smul, hb, ha]
  smul_mem' := by
    intro c v hv
    rcases zmod2_cases c with rfl | rfl
    · simp
    · simpa using hv

variable {S}

/-- A non-zero character vanishing on the stabiliser of a non-fixed point. -/
lemma exists_char (s : S) (hs : ∃ g : EA r, g • s ≠ s) :
    ∃ χ : (Fin r → ZMod 2) →ₗ[ZMod 2] ZMod 2, χ ≠ 0 ∧ stabSub S s ≤ LinearMap.ker χ := by
  have htop : (stabSub S s : Submodule (ZMod 2) (Fin r → ZMod 2)) ≠ ⊤ := by
    intro htop
    obtain ⟨g, hg⟩ := hs
    have : Multiplicative.toAdd g ∈ stabSub S s := htop ▸ Submodule.mem_top
    exact hg this
  exact Submodule.exists_le_ker_of_lt_top (stabSub S s) (lt_top_iff_ne_top.2 htop)

variable (hS : ∀ s : S, ∃ g : EA r, g • s ≠ s)

/-- The chosen character at `s`. -/
def chr (s : S) : (Fin r → ZMod 2) →ₗ[ZMod 2] ZMod 2 := (exists_char s (hS s)).choose

lemma chr_ne_zero (s : S) : chr hS s ≠ 0 := (exists_char s (hS s)).choose_spec.1

lemma chr_stab (s : S) {v : Fin r → ZMod 2} (hv : Multiplicative.ofAdd v • s = s) :
    chr hS s v = 0 :=
  (exists_char s (hS s)).choose_spec.2 hv

variable (r) in
/-- The chosen representative of the orbit of `t`. -/
def orbRep (t : S) : S := (Quotient.mk (MulAction.orbitRel (EA r) S) t).out

lemma exists_smul_eq_rep (t : S) : ∃ g : EA r, g • t = orbRep r t :=
  MulAction.orbitRel_apply.1 (Quotient.mk_out (s := MulAction.orbitRel (EA r) S) t)

lemma rep_smul (g : EA r) (t : S) : orbRep r (g • t) = orbRep r t := by
  unfold orbRep
  congr 1
  exact Quotient.sound (MulAction.orbitRel_apply.2 (MulAction.mem_orbit _ _))

variable (r) in
/-- An element moving `t` to its representative. -/
def orbG (t : S) : EA r := (exists_smul_eq_rep t).choose

lemma gt_spec (t : S) : orbG r t • t = orbRep r t := (exists_smul_eq_rep t).choose_spec

/-- The position of `t` in the two-point set of its orbit. -/
def orbPos (t : S) : ZMod 2 := chr hS (orbRep r t) (Multiplicative.toAdd (orbG r t))

lemma pos_smul (g : EA r) (t : S) :
    orbPos hS (g • t) = orbPos hS t + chr hS (orbRep r t) (Multiplicative.toAdd g) := by
  have hk : Multiplicative.ofAdd (Multiplicative.toAdd (orbG r (g • t) * g * (orbG r t)⁻¹)) • orbRep r t =
      orbRep r t := by
    rw [ofAdd_toAdd]
    calc _ = (orbG r (g • t) * g * (orbG r t)⁻¹) • (orbG r t • t) := by rw [gt_spec]
      _ = (orbG r (g • t) * g) • ((orbG r t)⁻¹ • (orbG r t • t)) := by rw [mul_smul]
      _ = (orbG r (g • t) * g) • t := by
        congr 1
        have : (orbG r t)⁻¹ * orbG r t = 1 := inv_mul_cancel _
        rw [smul_smul, this, one_smul]
      _ = orbG r (g • t) • (g • t) := by rw [mul_smul]
      _ = orbRep r t := by rw [gt_spec, rep_smul]
  have h0 := chr_stab hS (orbRep r t) hk
  simp only [toAdd_mul, toAdd_inv, map_add] at h0
  unfold orbPos
  rw [rep_smul]
  have hneg : -Multiplicative.toAdd (orbG r t) = Multiplicative.toAdd (orbG r t) := by
    ext i; exact ZMod.neg_eq_self_mod_two _
  rw [hneg] at h0
  have e : ∀ a b c : ZMod 2, a + b + c = 0 → a = c + b := by decide
  exact e _ _ _ h0

end Orbits

/-! ### The map to the join of two-point sets -/

section Map

variable {S J : Type} [Fintype S] [Fintype J] [MulAction (EA r) S]
  (hS : ∀ s : S, ∃ g : EA r, g • s ≠ s) {n : ℕ} (e : Fin n ≃ J × S)

open Classical in
/-- The map `S^{*J} → (two-point sets)^{*(J × S)}`; only the blocks `(j, s)` with `s` a
representative of an orbit are used. -/
def Psi (y : J → S → ℝ) : Fin n → L2 → ℝ := fun k l =>
  ∑ t, if orbRep r t = (e k).2 ∧ orbPos hS t = Multiplicative.toAdd l then y (e k).1 t else 0

lemma continuous_Psi : Continuous (Psi hS e) := by
  refine continuous_pi fun k => continuous_pi fun l => continuous_finset_sum _ fun t _ => ?_
  split_ifs
  · exact (continuous_apply t).comp (continuous_apply _)
  · exact continuous_const

lemma Psi_mem {y : J → S → ℝ} (hy : y ∈ SetJoin S J) : Psi hS e y ∈ GroupJoin L2 n := by
  classical
  obtain ⟨hnn, hsupp, hsum⟩ := hy
  have hl : ∀ k t, ∑ l : L2, (if orbRep r t = (e k).2 ∧ orbPos hS t = Multiplicative.toAdd l
      then y (e k).1 t else 0) = if orbRep r t = (e k).2 then y (e k).1 t else 0 := by
    intro k t
    by_cases hA : orbRep r t = (e k).2
    · simp only [hA, true_and, if_true]
      rw [Finset.sum_eq_single (Multiplicative.ofAdd (orbPos hS t))]
      · exact if_pos rfl
      · intro l _ hl
        rw [if_neg]
        intro h
        apply hl
        rw [h]
        rfl
      · simp
    · simp [hA]
  refine ⟨fun k l => Finset.sum_nonneg fun t _ => ?_, fun k l l' hl hl' => ?_, ?_⟩
  · split_ifs
    · exact hnn _ _
    · exact le_rfl
  · obtain ⟨t, -, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero hl
    obtain ⟨t', -, ht'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hl'
    split_ifs at ht ht' with c c'
    · have := hsupp _ _ _ ht ht'
      subst this
      exact Multiplicative.toAdd.injective (c.2.symm.trans c'.2)
    all_goals simp_all
  · calc ∑ k, ∑ l, Psi hS e y k l =
          ∑ k, ∑ t, (if orbRep r t = (e k).2 then y (e k).1 t else 0) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          simp only [Psi]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun t _ => hl k t
      _ = ∑ js : J × S, ∑ t, (if orbRep r t = js.2 then y js.1 t else 0) :=
          Fintype.sum_equiv e _ _ fun k => rfl
      _ = ∑ j, ∑ t, y j t := by
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun t _ => ?_
          simp
      _ = 1 := hsum

lemma Psi_setJoinAct (q : Fin r) (y : J → S → ℝ) :
    Psi hS e (setJoinAct (egen q) y) =
      tflip (fun k => chr hS (e k).2 (Pi.single q 1)) (Psi hS e y) := by
  funext k l
  simp only [Psi, tflip, setJoinAct]
  refine Fintype.sum_equiv (MulAction.toPerm (egen q)⁻¹) _ _ fun t => ?_
  have h1 : orbRep r ((egen q)⁻¹ • t) = orbRep r t := rep_smul _ _
  have h2 : orbPos hS ((egen q)⁻¹ • t) =
      orbPos hS t + chr hS (orbRep r t) (Pi.single q 1) := by
    rw [pos_smul, toAdd_inv]
    have hneg : (-Multiplicative.toAdd (egen q) : Fin r → ZMod 2) = Pi.single q 1 := by
      ext i; exact ZMod.neg_eq_self_mod_two _
    rw [hneg]
  simp only [MulAction.toPerm_apply]
  by_cases h : orbRep r t = (e k).2
  · have hiff : orbPos hS t = Multiplicative.toAdd l ↔ orbPos hS ((egen q)⁻¹ • t) =
        Multiplicative.toAdd (l * Multiplicative.ofAdd (chr hS (e k).2 (Pi.single q 1))) := by
      rw [h2, h, toAdd_mul, toAdd_ofAdd, add_left_inj]
    by_cases hp : orbPos hS t = Multiplicative.toAdd l
    · rw [if_pos ⟨h, hp⟩, if_pos ⟨h1.trans h, hiff.1 hp⟩]; rfl
    · rw [if_neg (fun h' => hp h'.2), if_neg (fun h' => hp (hiff.2 h'.2))]
  · rw [if_neg (fun h' => h h'.1), if_neg (fun h' => h (h1.symm.trans h'.1))]

end Map

lemma chr_single_ne_zero {S : Type} [Fintype S] [MulAction (EA r) S]
    (hS : ∀ s : S, ∃ g : EA r, g • s ≠ s) (s : S) :
    (fun q => chr hS s (Pi.single q 1)) ≠ 0 := by
  intro h
  apply chr_ne_zero hS s
  refine LinearMap.pi_ext fun q c => ?_
  have := congrFun h q
  simp only [Pi.zero_apply] at this
  rw [LinearMap.zero_apply, show (Pi.single q c : Fin r → ZMod 2) = c • Pi.single q 1 by
      rw [← Pi.single_smul, smul_eq_mul, mul_one],
    map_smul, this, smul_zero]

/-- **Lemma 1 (emptiness form) for `(ℤ/2)^r`.** -/
theorem joinEmptiness_elemAb (r : ℕ) : JoinEmptiness (EA r) := by
  classical
  intro S _ _ hS J _
  by_cases hK : Fintype.card (J × S) = 0
  · refine ⟨1, fun Φ _ hmaps => ?_⟩
    exfalso
    obtain ⟨-, -, hsum⟩ := hmaps _ (vtxPt_mem_groupJoin (N := 1) (j := 0) one_pos 1)
    have : IsEmpty (J × S) := Fintype.card_eq_zero_iff.1 hK
    have h0 : ∀ j : J, ∀ s : S, False := fun j s => this.false (j, s)
    rcases isEmpty_or_nonempty J with hJ | ⟨⟨j⟩⟩
    · simp at hsum
    · have : IsEmpty S := ⟨h0 j⟩
      simp at hsum
  obtain ⟨D, hD⟩ := Nat.exists_eq_succ_of_ne_zero hK
  let e : Fin (D + 1) ≃ J × S := (Fintype.equivFinOfCardEq hD).symm
  refine ⟨D + 2, fun Φ hc hmaps => ?_⟩
  by_contra hno
  push_neg at hno
  refine elemAb_join (N := D + 2) (D := D) (by omega) (fun k q => chr hS (e k).2 (Pi.single q 1))
    (fun k => chr_single_ne_zero hS (e k).2) (Psi hS e ∘ Φ)
    ((continuous_Psi hS e).comp_continuousOn hc) (fun x hx => Psi_mem hS e (hmaps x hx))
    (fun q x hx => ?_)
  simp only [Function.comp_apply]
  rw [hno x hx, Psi_setJoinAct]

/-- **Lemma 1 (orbit form) for `(ℤ/2)^r`.** -/
theorem joinOrbitCollapse_elemAb (r : ℕ) : JoinOrbitCollapse (EA r) :=
  (joinOrbitCollapse_iff_joinEmptiness _).2 (joinEmptiness_elemAb r)

/-- **Lemma 1 (orbit form) for every finite elementary abelian `2`-group.** -/
theorem joinOrbitCollapse_of_mul_self_eq_one (G : Type) [CommGroup G] [Fintype G]
    (hG : ∀ g : G, g * g = 1) : JoinOrbitCollapse G := by
  classical
  letI : Module (ZMod 2) (Additive G) := AddCommGroup.zmodModule (fun x => by
    rw [two_nsmul]; exact hG (Additive.toMul x))
  let e := Fintype.equivFin G
  let f : (Fin (Fintype.card G) → ZMod 2) →ₗ[ZMod 2] Additive G :=
    Fintype.linearCombination (ZMod 2) (fun i => Additive.ofMul (e.symm i))
  refine JoinOrbitCollapse.of_surjective (AddMonoidHom.toMultiplicativeLeft f.toAddMonoidHom)
    (fun g => ⟨Multiplicative.ofAdd (Pi.single (e g) 1), ?_⟩) (joinOrbitCollapse_elemAb _)
  simp [f, AddMonoidHom.toMultiplicativeLeft, Fintype.linearCombination_apply_single]

/-- **Lemma 1 (emptiness form) for every finite elementary abelian `2`-group.** -/
theorem joinEmptiness_of_mul_self_eq_one (G : Type) [CommGroup G] [Fintype G]
    (hG : ∀ g : G, g * g = 1) : JoinEmptiness G :=
  (joinOrbitCollapse_of_mul_self_eq_one G hG).joinEmptiness

end Dvoretzky.ElemAb
