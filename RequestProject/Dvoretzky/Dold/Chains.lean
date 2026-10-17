module

public import Mathlib

/-!
# Ordered (affine) chains

Chains are finitely supported functions on lists of points, `List E →₀ R`; the empty list plays
the role of the augmentation simplex. The boundary is `∂ [x₀, …, x_k] = ∑ (-1)ⁱ [x₀, …, x̂ᵢ, …, x_k]`
(so `∂ [x] = []`), defined recursively by `∂ (x :: l) = l - x :: ∂ l`.

We define cones (`consL`, `appL`), the action of maps `E → E` (`actL`), and the barycentric
subdivision `sd`, and prove the basic chain identities.
-/

@[expose] public section

open scoped BigOperators

noncomputable section

namespace Dvoretzky.Dold

variable {R : Type*} [CommRing R] {E : Type*}

/-- Ordered chains with coefficients in `R` on points of `E`. -/
abbrev Chain (R E : Type*) [CommRing R] := List E →₀ R

/-- Cone with apex `x` in front: `l ↦ x :: l`. -/
def consL (x : E) : Chain R E →ₗ[R] Chain R E := Finsupp.lmapDomain R R (List.cons x)

/-- Cone with apex `v` at the end: `l ↦ l ++ [v]`. -/
def appL (v : E) : Chain R E →ₗ[R] Chain R E := Finsupp.lmapDomain R R (· ++ [v])

/-- The action of a map `T : E → F` on chains. -/
def actL {F : Type*} (T : E → F) : Chain R E →ₗ[R] Chain R F := Finsupp.lmapDomain R R (List.map T)

/-- The sign operator `l ↦ (-1)^(length l) l`. -/
def sgnL : Chain R E →ₗ[R] Chain R E :=
  Finsupp.linearCombination R (fun l : List E => ((-1 : R) ^ l.length) • Finsupp.single l 1)

/-- Boundary of a single list. -/
def bdList : List E → Chain R E
  | [] => 0
  | x :: l => Finsupp.single l 1 - consL x (bdList l)

/-- The boundary operator. -/
def bd : Chain R E →ₗ[R] Chain R E := Finsupp.linearCombination R bdList

@[simp] lemma consL_single (x : E) (l : List E) (c : R) :
    consL x (Finsupp.single l c) = Finsupp.single (x :: l) c := by
  simp [consL]

@[simp] lemma appL_single (v : E) (l : List E) (c : R) :
    appL v (Finsupp.single l c) = Finsupp.single (l ++ [v]) c := by
  simp [appL]

@[simp] lemma actL_single {F : Type*} (T : E → F) (l : List E) (c : R) :
    actL T (Finsupp.single l c) = Finsupp.single (l.map T) c := by
  simp [actL]

@[simp] lemma sgnL_single (l : List E) (c : R) :
    sgnL (Finsupp.single l c) = ((-1 : R) ^ l.length * c) • Finsupp.single l 1 := by
  simp [sgnL, mul_comm, mul_smul]

@[simp] lemma bd_single (l : List E) (c : R) :
    bd (Finsupp.single l c) = c • (bdList l : Chain R E) := by
  simp [bd]

@[simp] lemma bdList_nil : (bdList [] : Chain R E) = 0 := rfl

lemma bdList_cons (x : E) (l : List E) :
    (bdList (x :: l) : Chain R E) = Finsupp.single l 1 - consL x (bdList l) := rfl

/-- Two linear maps out of chains agreeing on basis lists are equal. -/
lemma chain_hom_ext {M : Type*} [AddCommGroup M] [Module R M] {f g : Chain R E →ₗ[R] M}
    (h : ∀ l : List E, f (Finsupp.single l 1) = g (Finsupp.single l 1)) : f = g :=
  Finsupp.lhom_ext' fun l => LinearMap.ext_ring (h l)

lemma bd_consL (x : E) (c : Chain R E) : bd (consL x c) = c - consL x (bd c) := by
  have : (bd ∘ₗ consL x : Chain R E →ₗ[R] Chain R E) = LinearMap.id - consL x ∘ₗ bd := by
    refine chain_hom_ext fun l => ?_
    simp [bdList_cons]
  exact congrArg (fun F : Chain R E →ₗ[R] Chain R E => F c) this

lemma bd_bdList (l : List E) : bd (bdList l : Chain R E) = 0 := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [bdList_cons, map_sub, bd_single, one_smul, bd_consL, ih, map_zero, sub_zero, sub_self]

lemma bd_bd (c : Chain R E) : bd (bd c) = 0 := by
  have : (bd ∘ₗ bd : Chain R E →ₗ[R] Chain R E) = 0 := by
    refine chain_hom_ext fun l => ?_
    simp [bd_bdList]
  exact congrArg (fun F : Chain R E →ₗ[R] Chain R E => F c) this

lemma bd_mul_bd : (bd * bd : Module.End R (Chain R E)) = 0 :=
  LinearMap.ext fun c => bd_bd c

lemma consL_appL (x v : E) (c : Chain R E) : consL x (appL v c) = appL v (consL x c) := by
  have : (consL x ∘ₗ appL v : Chain R E →ₗ[R] Chain R E) = appL v ∘ₗ consL x := by
    refine chain_hom_ext fun l => ?_
    simp
  exact congrArg (fun F : Chain R E →ₗ[R] Chain R E => F c) this

lemma bdList_append (v : E) (l : List E) :
    (bdList (l ++ [v]) : Chain R E) = appL v (bdList l) + sgnL (Finsupp.single l 1) := by
  induction l with
  | nil => simp [bdList_cons]
  | cons x l ih =>
    rw [List.cons_append, bdList_cons, ih, bdList_cons, map_sub, map_add, consL_appL]
    simp only [appL_single, sgnL_single, mul_one, List.length_cons, pow_succ, consL_single,
      map_smul]
    rw [mul_neg_one, neg_smul]
    abel

lemma bd_appL (v : E) (c : Chain R E) : bd (appL v c) = appL v (bd c) + sgnL c := by
  have : (bd ∘ₗ appL v : Chain R E →ₗ[R] Chain R E) = appL v ∘ₗ bd + sgnL := by
    refine chain_hom_ext fun l => ?_
    simp [bdList_append]
  exact congrArg (fun F : Chain R E →ₗ[R] Chain R E => F c) this

lemma sgnL_consL (x : E) (c : Chain R E) : sgnL (consL x c) = - consL x (sgnL c) := by
  have : (sgnL ∘ₗ consL x : Chain R E →ₗ[R] Chain R E) = -(consL x ∘ₗ sgnL : Chain R E →ₗ[R] Chain R E) := by
    refine chain_hom_ext fun l => ?_
    simp [pow_succ]
  exact congrArg (fun F : Chain R E →ₗ[R] Chain R E => F c) this

lemma sgnL_bdList (l : List E) :
    sgnL (bdList l : Chain R E) = -((-1 : R) ^ l.length • (bdList l : Chain R E)) := by
  induction l with
  | nil => simp
  | cons x m ih =>
    rw [bdList_cons, map_sub, sgnL_consL, ih, sgnL_single]
    simp only [mul_one, map_neg, map_smul, List.length_cons, pow_succ, neg_smul, smul_sub,
      mul_neg, neg_neg, sub_neg_eq_add]
    abel

lemma bd_sgnL (c : Chain R E) : bd (sgnL c) = - sgnL (bd c) := by
  have : (bd ∘ₗ sgnL : Chain R E →ₗ[R] Chain R E) = -(sgnL ∘ₗ bd : Chain R E →ₗ[R] Chain R E) := by
    refine chain_hom_ext fun l => ?_
    simp [sgnL_bdList]
  exact congrArg (fun F : Chain R E →ₗ[R] Chain R E => F c) this

lemma sgnL_sgnL (c : Chain R E) : sgnL (sgnL c) = c := by
  have : (sgnL ∘ₗ sgnL : Chain R E →ₗ[R] Chain R E) = LinearMap.id := by
    refine chain_hom_ext fun l => ?_
    simp [← pow_add, ← two_mul, pow_mul]
  exact congrArg (fun F : Chain R E →ₗ[R] Chain R E => F c) this

lemma actL_consL {F : Type*} (T : E → F) (x : E) (c : Chain R E) :
    actL T (consL x c) = consL (T x) (actL T c) := by
  have : (actL T ∘ₗ consL x : Chain R E →ₗ[R] Chain R F) = consL (T x) ∘ₗ actL T := by
    refine chain_hom_ext fun l => ?_
    simp
  exact congrArg (fun Φ : Chain R E →ₗ[R] Chain R F => Φ c) this

lemma actL_appL (T : E → E) (v : E) (c : Chain R E) :
    actL T (appL v c) = appL (T v) (actL T c) := by
  have : (actL T ∘ₗ appL v : Chain R E →ₗ[R] Chain R E) = appL (T v) ∘ₗ actL T := by
    refine chain_hom_ext fun l => ?_
    simp
  exact congrArg (fun F : Chain R E →ₗ[R] Chain R E => F c) this

lemma actL_sgnL (T : E → E) (c : Chain R E) : actL T (sgnL c) = sgnL (actL T c) := by
  have : (actL T ∘ₗ sgnL : Chain R E →ₗ[R] Chain R E) = sgnL ∘ₗ actL T := by
    refine chain_hom_ext fun l => ?_
    simp
  exact congrArg (fun F : Chain R E →ₗ[R] Chain R E => F c) this

lemma actL_bdList {F : Type*} (T : E → F) (l : List E) :
    actL T (bdList l : Chain R E) = bdList (l.map T) := by
  induction l with
  | nil => simp
  | cons x l ih => simp [bdList_cons, actL_consL, ih]

lemma actL_bd {F : Type*} (T : E → F) (c : Chain R E) : actL T (bd c) = bd (actL T c) := by
  have : (actL T ∘ₗ bd : Chain R E →ₗ[R] Chain R F) = bd ∘ₗ actL T := by
    refine chain_hom_ext fun l => ?_
    simp [actL_bdList]
  exact congrArg (fun Φ : Chain R E →ₗ[R] Chain R F => Φ c) this

lemma actL_comp (S T : E → E) (c : Chain R E) : actL S (actL T c) = actL (S ∘ T) c := by
  have : (actL S ∘ₗ actL T : Chain R E →ₗ[R] Chain R E) = actL (S ∘ T) := by
    refine chain_hom_ext fun l => ?_
    simp
  exact congrArg (fun F : Chain R E →ₗ[R] Chain R E => F c) this

lemma actL_id (c : Chain R E) : actL (id : E → E) c = c := by
  have : (actL id : Chain R E →ₗ[R] Chain R E) = LinearMap.id := by
    refine chain_hom_ext fun l => ?_
    simp
  exact congrArg (fun F : Chain R E →ₗ[R] Chain R E => F c) this

end Dvoretzky.Dold
