module

public import RequestProject.Dvoretzky.Dold.Main
public import RequestProject.Dvoretzky.ElemAb.Algebra

/-!
# The source: a family in the ordered chains of `E * ⋯ * E`, `E = (ℤ/2)^r`

For the elementary abelian group `E = (ℤ/2)^r` with generators `g_q` we build ordered chains
`b_I` (`I : Fin r →₀ ℕ`) in the `N`-fold join of `E`, supported on simplices with vertices in the
factors `0, …, |I|`, with

`∂ b_0 = ∅`,  `∂ b_I = ∑_{q, I_q ≠ 0} (1 + g_q) b_{I - e_q}`  (over `𝔽₂`),

i.e. a family with defect `1` (`isFam_bfam`). It is the cellular chain map from the standard
`𝔽₂[E]`-resolution (the tensor product of the resolutions of the factors `ℤ/2`).
-/

@[expose] public section

open scoped BigOperators

noncomputable section

namespace Dvoretzky.ElemAb

open Dvoretzky Dvoretzky.Dold

variable {r : ℕ}

/-- The elementary abelian group `(ℤ/2)^r`, written multiplicatively. -/
abbrev EA (r : ℕ) := Multiplicative (Fin r → ZMod 2)

/-- The `q`-th standard generator of `(ℤ/2)^r`. -/
def egen (q : Fin r) : EA r := Multiplicative.ofAdd (Pi.single q 1)

lemma egen_mul_self (q : Fin r) : egen q * egen q = 1 := by
  rw [egen, ← ofAdd_add]
  have : (Pi.single q (1 : ZMod 2) : Fin r → ZMod 2) + Pi.single q 1 = 0 := by
    funext i
    simp only [Pi.add_apply, Pi.zero_apply]
    by_cases h : i = q
    · subst h; simp; rfl
    · simp [h]
  rw [this]; rfl

variable {N : ℕ}

/-- The action of the generator `g_q` on the ordered chains of the source join. -/
def Tq (q : Fin r) : Module.End (ZMod 2) (Chain (ZMod 2) (Fin N → EA r → ℝ)) :=
  actL (joinAct (egen q))

lemma Tq_Tq (q : Fin r) (c : Chain (ZMod 2) (Fin N → EA r → ℝ)) : Tq q (Tq q c) = c := by
  rw [Tq, actL_comp]
  have : (joinAct (egen q) ∘ joinAct (egen q) : (Fin N → EA r → ℝ) → _) = id := by
    funext x
    simp only [Function.comp_apply, joinAct_mul', egen_mul_self, joinAct_one', id]
  rw [this, actL_id]

lemma Tq_comm (q q' : Fin r) (c : Chain (ZMod 2) (Fin N → EA r → ℝ)) :
    Tq q (Tq q' c) = Tq q' (Tq q c) := by
  rw [Tq, Tq, actL_comp, actL_comp]
  rw [show (joinAct (egen q) ∘ joinAct (egen q') : (Fin N → EA r → ℝ) → _) =
    joinAct (egen q') ∘ joinAct (egen q) from funext fun x => by
      simp only [Function.comp_apply, joinAct_mul', mul_comm]]

lemma bd_Tq (q : Fin r) (c : Chain (ZMod 2) (Fin N → EA r → ℝ)) : bd (Tq q c) = Tq q (bd c) :=
  (actL_bd _ c).symm

lemma Tq_nil (q : Fin r) :
    Tq q (Finsupp.single ([] : List (Fin N → EA r → ℝ)) (1 : ZMod 2)) = Finsupp.single [] 1 := by
  simp [Tq]

/-- Auxiliary recursion for the family. -/
def baux : ℕ → (Fin r →₀ ℕ) → Chain (ZMod 2) (Fin N → EA r → ℝ)
  | 0, _ => Finsupp.single [vtxPt N 0 1] 1
  | k + 1, I => appL (vtxPt N (k + 1) 1)
      (sgnL (∑ q, shift q (fun J => baux k J + Tq q (baux k J)) I))

/-- The family `b_I`. -/
def bfam (I : Fin r →₀ ℕ) : Chain (ZMod 2) (Fin N → EA r → ℝ) := baux (Finsupp.degree I) I

lemma degree_sub_single {q : Fin r} {I : Fin r →₀ ℕ} (h : I q ≠ 0) :
    Finsupp.degree (I - Finsupp.single q 1) + 1 = Finsupp.degree I := by
  have hle : Finsupp.single q 1 ≤ I := by
    intro i
    by_cases hi : i = q
    · subst hi; simp; omega
    · simp [Ne.symm hi]
  conv_rhs => rw [← tsub_add_cancel_of_le hle]
  rw [map_add, Finsupp.degree_single]

lemma shift_congr_deg {M : Type*} [Zero M] (q : Fin r) {k : ℕ} {f g : (Fin r →₀ ℕ) → M}
    (h : ∀ J : Fin r →₀ ℕ, Finsupp.degree J = k → f J = g J) {I : Fin r →₀ ℕ}
    (hI : Finsupp.degree I = k + 1) : shift q f I = shift q g I := by
  unfold shift
  split_ifs with hq
  · exact h _ (by have := degree_sub_single hq; omega)
  · rfl

lemma bfam_succ {k : ℕ} {I : Fin r →₀ ℕ} (hI : Finsupp.degree I = k + 1) :
    (bfam I : Chain (ZMod 2) (Fin N → EA r → ℝ)) = appL (vtxPt N (k + 1) 1)
      (sgnL (∑ q, shift q (fun J => bfam J + Tq q (bfam J)) I)) := by
  rw [bfam, hI, baux]
  congr 2
  refine Finset.sum_congr rfl fun q _ => ?_
  exact shift_congr_deg q (fun J hJ => by rw [bfam, hJ]) hI

/-- The boundary formula for the family. -/
theorem bd_bfam : ∀ (k : ℕ) (I : Fin r →₀ ℕ), Finsupp.degree I = k →
    bd (bfam I : Chain (ZMod 2) (Fin N → EA r → ℝ)) =
      (if I = 0 then Finsupp.single [] 1 else 0) +
        ∑ q, shift q (fun J => bfam J + Tq q (bfam J)) I
  | 0, I, hI => by
    have h0 : I = 0 := (Finsupp.degree_eq_zero_iff I).1 hI
    subst h0
    rw [bfam, hI, baux, if_pos rfl]
    simp [shift, bdList_cons]
  | k + 1, I, hI => by
    have hne : I ≠ 0 := by
      rintro rfl; simp at hI
    rw [if_neg hne, zero_add, bfam_succ hI, bd_appL, bd_sgnL, sgnL_sgnL]
    set X := ∑ q, shift q (fun J => (bfam J : Chain (ZMod 2) (Fin N → EA r → ℝ)) + Tq q (bfam J)) I
    suffices hX : bd X = 0 by rw [hX, map_zero, neg_zero, map_zero, zero_add]
    have ih := bd_bfam k
    -- expand `∂ X` with the induction hypothesis
    have h1 : ∀ q, bd (shift q (fun J => (bfam J : Chain (ZMod 2) (Fin N → EA r → ℝ)) +
        Tq q (bfam J)) I) =
        shift q (fun J => ∑ q', shift q' (fun K => (bfam K + Tq q' (bfam K)) +
          Tq q (bfam K + Tq q' (bfam K))) J) I := by
      intro q
      rw [← shift_map]
      refine shift_congr_deg q (fun J hJ => ?_) hI
      rw [map_add, bd_Tq, ih J hJ]
      simp only [map_add]
      split_ifs
      · rw [Tq_nil, map_sum, add_add_add_comm, two_smul_eq_zero, zero_add,
          ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun q' _ => ?_
        rw [← shift_map, ← shift_add]
        congr 1; funext K; rw [map_add]
      · rw [zero_add, map_zero, zero_add, map_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun q' _ => ?_
        rw [← shift_map, ← shift_add]
        congr 1; funext K; rw [map_add]
    rw [map_sum, Finset.sum_congr rfl fun q _ => h1 q]
    simp only [shift_sum]
    refine Dold.sum_antisymm _ (fun q q' => ?_) (fun q => ?_)
    · rw [neg_eq_self', shift_shift]
      congr 1; funext K; congr 1; funext K'
      simp only [map_add]
      rw [Tq_comm q q']
      abel
    · have : ∀ K, (bfam K : Chain (ZMod 2) (Fin N → EA r → ℝ)) + Tq q (bfam K) +
          Tq q (bfam K + Tq q (bfam K)) = 0 := by
        intro K
        rw [map_add, Tq_Tq, add_comm (Tq q (bfam K)) (bfam K), two_smul_eq_zero]
      simp only [this]
      unfold shift
      split_ifs <;> simp

/-- The family has defect `1`. -/
theorem isFam_bfam (n : ℕ) :
    IsFam (bd : Module.End (ZMod 2) (Chain (ZMod 2) (Fin N → EA r → ℝ))) Tq
      (Finsupp.single [] 1) n (fun J => if J = 0 then 1 else 0) bfam := by
  intro I _
  rw [DOp, bd_bfam _ I rfl, add_assoc, two_smul_eq_zero, add_zero]
  by_cases h : I = 0 <;> simp [h]

/-- Supports: `b_I` lives on the simplices with one vertex in each of the factors `0, …, |I|`. -/
theorem baux_supported : ∀ (k : ℕ) (I : Fin r →₀ ℕ),
    (baux k I : Chain (ZMod 2) (Fin N → EA r → ℝ)) ∈
      Finsupp.supported (ZMod 2) (ZMod 2) {l : List (Fin N → EA r → ℝ) | VList N k l}
  | 0, I => Finsupp.single_mem_supported _ _ ⟨fun _ => 1, by simp⟩
  | k + 1, I => by
    have hT : ∀ q J, Tq q (baux k J : Chain (ZMod 2) (Fin N → EA r → ℝ)) ∈
        Finsupp.supported (ZMod 2) (ZMod 2) {l : List (Fin N → EA r → ℝ) | VList N k l} := by
      intro q J
      refine map_mem_supported (Tq q) _ (fun l hl => ?_) (baux_supported k J)
      simp only [Tq, actL_single]
      exact Finsupp.single_mem_supported _ _ (VList.map_joinAct hl _)
    have hsum : (∑ q, shift q (fun J => (baux k J : Chain (ZMod 2) (Fin N → EA r → ℝ)) +
        Tq q (baux k J)) I) ∈
        Finsupp.supported (ZMod 2) (ZMod 2) {l : List (Fin N → EA r → ℝ) | VList N k l} := by
      refine Submodule.sum_mem _ fun q _ => ?_
      unfold shift
      split_ifs
      · exact Submodule.add_mem _ (baux_supported k _) (hT q _)
      · exact Submodule.zero_mem _
    refine map_mem_supported (appL (vtxPt N (k + 1) 1) ∘ₗ sgnL) _ (fun l hl => ?_) hsum
    simp only [LinearMap.coe_comp, Function.comp_apply, sgnL_single, mul_one, map_smul,
      appL_single]
    exact Submodule.smul_mem _ _ (Finsupp.single_mem_supported _ _ (VList.append hl))

lemma bfam_supported (I : Fin r →₀ ℕ) :
    (bfam I : Chain (ZMod 2) (Fin N → EA r → ℝ)) ∈ Finsupp.supported (ZMod 2) (ZMod 2)
      {l : List (Fin N → EA r → ℝ) | VList N (Finsupp.degree I) l} :=
  baux_supported _ I

end Dvoretzky.ElemAb
