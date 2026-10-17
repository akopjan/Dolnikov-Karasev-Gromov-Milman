module

public import Mathlib

/-!
# Convex hulls of compact sets in finite-dimensional spaces are compact

A consequence of Carathéodory's theorem, used in the averaging lemma.
-/

@[expose] public section

open scoped BigOperators

noncomputable section

namespace Dvoretzky

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The set of convex combinations of `m` points of `S`. -/
def convComb (S : Set V) (m : ℕ) : Set V :=
  (fun p : (Fin m → ℝ) × (Fin m → V) => ∑ i, p.1 i • p.2 i) ''
    (stdSimplex ℝ (Fin m) ×ˢ Set.pi Set.univ fun _ => S)

omit [FiniteDimensional ℝ V] in
lemma isCompact_convComb {S : Set V} (hS : IsCompact S) (m : ℕ) : IsCompact (convComb S m) := by
  refine (IsCompact.prod (isCompact_stdSimplex (𝕜 := ℝ) (ι := Fin m)) (isCompact_univ_pi fun _ => hS)).image ?_
  fun_prop

omit [FiniteDimensional ℝ V] in
lemma convComb_subset_convexHull (S : Set V) (m : ℕ) : convComb S m ⊆ convexHull ℝ S := by
  rintro _ ⟨⟨w, v⟩, ⟨hw, hv⟩, rfl⟩
  refine (convex_convexHull ℝ S).sum_mem (fun i _ => hw.1 i) hw.2 fun i _ => ?_
  exact subset_convexHull ℝ S (hv i (Set.mem_univ i))

lemma convexHull_subset_iUnion_convComb (S : Set V) :
    convexHull ℝ S ⊆ ⋃ m ∈ Finset.range (Module.finrank ℝ V + 2), convComb S m := by
  intro x hx
  obtain ⟨ι, _, z, w, hzS, hind, hw0, hw1, hx⟩ := eq_pos_convex_span_of_mem_convexHull hx
  have hcard : Fintype.card ι ≤ Module.finrank ℝ V + 1 :=
    hind.card_le_finrank_succ.trans (Nat.succ_le_succ (Submodule.finrank_le _))
  simp only [Set.mem_iUnion, Finset.mem_range]
  refine ⟨Fintype.card ι, by omega, ?_⟩
  let e := Fintype.equivFin ι
  refine ⟨(fun i => w (e.symm i), fun i => z (e.symm i)), ⟨⟨fun i => (hw0 _).le, ?_⟩, ?_⟩, ?_⟩
  · rw [← hw1]
    exact e.symm.sum_comp w
  · intro i _
    exact hzS ⟨_, rfl⟩
  · rw [← hx]
    exact e.symm.sum_comp (fun i => w i • z i)

/-- In a finite-dimensional real normed space, the convex hull of a compact set is compact. -/
theorem isCompact_convexHull_of_isCompact {S : Set V} (hS : IsCompact S) :
    IsCompact (convexHull ℝ S) := by
  have : convexHull ℝ S = ⋃ m ∈ Finset.range (Module.finrank ℝ V + 2), convComb S m :=
    Set.Subset.antisymm (convexHull_subset_iUnion_convComb S)
      (Set.iUnion₂_subset fun m _ => convComb_subset_convexHull S m)
  rw [this]
  exact (Finset.range _).isCompact_biUnion fun m _ => isCompact_convComb hS m

end Dvoretzky
