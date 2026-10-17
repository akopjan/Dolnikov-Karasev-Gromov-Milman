module

public import RequestProject.Dvoretzky.Dold.Subdivision
public import RequestProject.Dvoretzky.Dold.JoinAction
public import RequestProject.Dvoretzky.Lemma1Partial

/-!
# Geometry of the join `G * ⋯ * G` for Dold's theorem

* `isCompact_groupJoin`: the realisation `GroupJoin G N` is compact;
* `vtxPt N j h`: the vertex `h` of the `j`-th factor; `VList N k l`: `l` is the list of vertices
  of a `k`-simplex of the join using the factors `0, …, k`; its convex hull lies in the join;
* `vtxSel Φ x`: for a map `Φ` into the join `G^{*(D+1)}`, a canonical vertex `(j, h)` of the target
  with `Φ x j h ≥ 1/(D+1)` (the least such `j`); it is equivariant.
-/

@[expose] public section

open scoped BigOperators

noncomputable section

namespace Dvoretzky.Dold

open Dvoretzky

variable {G : Type} [Group G] [Fintype G] [DecidableEq G]

omit [Group G] [DecidableEq G] in
lemma groupJoin_le_one {N : ℕ} {x : Fin N → G → ℝ} (hx : x ∈ GroupJoin G N) (i : Fin N) (h : G) :
    x i h ≤ 1 := by
  obtain ⟨h0, -, h2⟩ := hx
  calc x i h ≤ ∑ h', x i h' := Finset.single_le_sum (fun h' _ => h0 i h') (Finset.mem_univ h)
    _ ≤ ∑ i', ∑ h', x i' h' :=
        Finset.single_le_sum (f := fun i' => ∑ h', x i' h')
          (fun i' _ => Finset.sum_nonneg fun h' _ => h0 i' h') (Finset.mem_univ i)
    _ = 1 := h2

omit [Group G] [DecidableEq G] in
lemma isCompact_groupJoin (N : ℕ) : IsCompact (GroupJoin G N) := by
  have hset : GroupJoin G N = {x | ∀ i h, 0 ≤ x i h} ∩
      ({x | ∀ i h h', h ≠ h' → x i h * x i h' = 0} ∩ {x | ∑ i, ∑ h, x i h = 1}) := by
    ext x
    simp only [GroupJoin, Set.mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨h0, h1, h2⟩
      refine ⟨h0, fun i h h' hne => ?_, h2⟩
      by_contra hc
      exact hne (h1 i h h' (left_ne_zero_of_mul hc) (right_ne_zero_of_mul hc))
    · rintro ⟨h0, h1, h2⟩
      refine ⟨h0, fun i h h' a b => ?_, h2⟩
      by_contra hne
      exact mul_ne_zero a b (h1 i h h' hne)
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · rw [hset]
    refine IsClosed.inter ?_ (IsClosed.inter ?_ ?_)
    · simp only [Set.setOf_forall]
      exact isClosed_iInter fun i => isClosed_iInter fun h =>
        isClosed_le continuous_const ((continuous_apply h).comp (continuous_apply i))
    · simp only [Set.setOf_forall]
      refine isClosed_iInter fun i => isClosed_iInter fun h => isClosed_iInter fun h' =>
        isClosed_iInter fun _ => isClosed_eq ?_ continuous_const
      exact (continuous_apply_apply i h).mul (continuous_apply_apply i h')
    · exact isClosed_eq (continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun h _ =>
        (continuous_apply h).comp (continuous_apply i)) continuous_const
  · refine (Metric.isBounded_closedBall (x := (0 : Fin N → G → ℝ)) (r := 1)).subset ?_
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun h => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hx.1 i h)]
    exact groupJoin_le_one hx i h

/-- The vertex `h` of the `j`-th factor of the join. -/
def vtxPt (N j : ℕ) (h : G) : Fin N → G → ℝ := fun i h' => if (i : ℕ) = j ∧ h' = h then 1 else 0

omit [Fintype G] in
lemma joinAct_vtxPt {N : ℕ} (g : G) (j : ℕ) (h : G) :
    joinAct g (vtxPt N j h) = vtxPt N j (h * g⁻¹) := by
  funext i h'
  simp only [joinAct, vtxPt]
  congr 1
  apply propext
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [← h2]; group⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [h2]; group⟩

/-- `l` is the list of vertices `(0, f 0), …, (k, f k)` of the join. -/
def VList (N k : ℕ) (l : List (Fin N → G → ℝ)) : Prop :=
  ∃ f : ℕ → G, l = (List.range (k + 1)).map (fun i => vtxPt N i (f i))

omit [Group G] [Fintype G] in
lemma VList.length_eq {N k : ℕ} {l : List (Fin N → G → ℝ)} (h : VList N k l) :
    l.length = k + 1 := by
  obtain ⟨f, rfl⟩ := h; simp

omit [Fintype G] in
lemma VList.map_joinAct {N k : ℕ} {l : List (Fin N → G → ℝ)} (h : VList N k l) (g : G) :
    VList N k (l.map (joinAct g)) := by
  obtain ⟨f, rfl⟩ := h
  refine ⟨fun i => f i * g⁻¹, ?_⟩
  simp [List.map_map, Function.comp_def, joinAct_vtxPt]

omit [Fintype G] in
lemma VList.append {N k : ℕ} {l : List (Fin N → G → ℝ)} (h : VList N k l) :
    VList N (k + 1) (l ++ [vtxPt N (k + 1) 1]) := by
  obtain ⟨f, rfl⟩ := h
  refine ⟨Function.update f (k + 1) 1, ?_⟩
  rw [List.range_succ (n := k + 1), List.map_append]
  congr 1
  · refine List.map_congr_left fun i hi => ?_
    rw [Function.update_of_ne]
    have := List.mem_range.1 hi
    omega
  · simp

omit [Group G] in
lemma VList.dist_le {N k : ℕ} {l : List (Fin N → G → ℝ)} (h : VList N k l) :
    ∀ a ∈ l, ∀ b ∈ l, dist a b ≤ 1 := by
  obtain ⟨f, rfl⟩ := h
  intro a ha b hb
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 ha
  obtain ⟨i', -, rfl⟩ := List.mem_map.1 hb
  refine (dist_pi_le_iff zero_le_one).2 fun j => (dist_pi_le_iff zero_le_one).2 fun h' => ?_
  simp only [vtxPt, Real.dist_eq]
  split_ifs <;> norm_num

omit [Group G] in
lemma VList.hull_subset {N k : ℕ} {l : List (Fin N → G → ℝ)} (h : VList N k l) (hk : k < N) :
    hull l ⊆ GroupJoin G N := by
  obtain ⟨f, rfl⟩ := h
  let C : Set (Fin N → G → ℝ) := {x | (∀ i h, 0 ≤ x i h) ∧ (∀ (i : Fin N) h, h ≠ f i → x i h = 0) ∧
    ∑ i, ∑ h, x i h = 1}
  have hC : Convex ℝ C := by
    rintro x ⟨hx0, hx1, hx2⟩ y ⟨hy0, hy1, hy2⟩ a b ha hb hab
    refine ⟨fun i h => ?_, fun i h hne => ?_, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have := hx0 i h; have := hy0 i h; positivity
    · simp [hx1 i h hne, hy1 i h hne]
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum, hx2, hy2, mul_one, hab]
  have hCJ : C ⊆ GroupJoin G N := by
    rintro x ⟨hx0, hx1, hx2⟩
    refine ⟨hx0, fun i h h' a b => ?_, hx2⟩
    by_contra hne
    by_cases e : h = f i
    · subst e; exact b (hx1 i h' (Ne.symm hne))
    · exact a (hx1 i h e)
  refine subset_trans (convexHull_min ?_ hC) hCJ
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
  have hj' : j < N := by have := List.mem_range.1 hj; omega
  refine ⟨fun i h => by simp only [vtxPt]; split_ifs <;> norm_num, fun i h hne => ?_, ?_⟩
  · simp only [vtxPt]
    rw [if_neg]
    rintro ⟨rfl, rfl⟩
    exact hne rfl
  · rw [Finset.sum_eq_single ⟨j, hj'⟩]
    · simp [vtxPt]
    · intro i _ hi
      refine Finset.sum_eq_zero fun h _ => ?_
      simp only [vtxPt]
      rw [if_neg]
      rintro ⟨e, -⟩
      exact hi (Fin.ext e)
    · simp

/-! ### Canonical vertex selection -/

section Select

variable {N D : ℕ} {X : Type} (Φ : X → (Fin (D + 1) → G → ℝ))

/-- The set of target coordinates `j` with some `Φ x j h ≥ 1/(D+1)`. -/
def selSet (x : X) : Finset (Fin (D + 1)) :=
  Finset.univ.filter fun j => ∃ h, (1 : ℝ) / (D + 1) ≤ Φ x j h

/-- A canonical vertex of the target carrying weight at least `1/(D+1)`. -/
def vtxSel (x : X) : Fin (D + 1) × G :=
  if hS : (selSet Φ x).Nonempty then
    ((selSet Φ x).min' hS,
      if hh : ∃ h, (1 : ℝ) / (D + 1) ≤ Φ x ((selSet Φ x).min' hS) h then hh.choose else 1)
  else (0, 1)

omit [Group G] [DecidableEq G] in
lemma selSet_nonempty {x : X} (hx : Φ x ∈ GroupJoin G (D + 1)) :
    (selSet Φ x).Nonempty := by
  obtain ⟨h0, h1, h2⟩ := hx
  by_contra hne
  simp only [selSet, Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hne
  have hlt : ∀ j, ∑ h, Φ x j h < (1 : ℝ) / (D + 1) := by
    intro j
    have hj := hne (Finset.mem_univ j)
    push_neg at hj
    by_cases hz : ∃ h, Φ x j h ≠ 0
    · obtain ⟨h, hh⟩ := hz
      rw [Finset.sum_eq_single h]
      · exact hj h
      · intro h' _ hne'
        by_contra hc
        exact hne' (h1 j h' h hc hh)
      · simp
    · push_neg at hz
      simp only [hz, Finset.sum_const_zero]
      positivity
  have := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun j _ => hlt j)
  rw [h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  push_cast at this
  rw [mul_one_div_cancel (by positivity)] at this
  exact lt_irrefl _ this

omit [DecidableEq G] in
lemma vtxSel_spec {x : X} (hx : Φ x ∈ GroupJoin G (D + 1)) :
    (1 : ℝ) / (D + 1) ≤ Φ x (vtxSel Φ x).1 (vtxSel Φ x).2 := by
  have hS := selSet_nonempty Φ hx
  have hmem : ∃ h, (1 : ℝ) / (D + 1) ≤ Φ x ((selSet Φ x).min' hS) h := by
    have := Finset.min'_mem _ hS
    simp only [selSet, Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this
  simp only [vtxSel, dif_pos hS, dif_pos hmem]
  exact hmem.choose_spec

end Select

section SelectAct

variable {N D : ℕ} (Φ : (Fin N → G → ℝ) → (Fin (D + 1) → G → ℝ))

omit [DecidableEq G] in
lemma vtxSel_joinAct {x : Fin N → G → ℝ} (g : G) (hx : Φ x ∈ GroupJoin G (D + 1))
    (heq : Φ (joinAct g x) = joinAct g (Φ x)) :
    vtxSel Φ (joinAct g x) = vact g (vtxSel Φ x) := by
  have hS : selSet Φ (joinAct g x) = selSet Φ x := by
    ext j
    simp only [selSet, Finset.mem_filter, Finset.mem_univ, true_and, heq, joinAct]
    constructor
    · rintro ⟨h, hh⟩; exact ⟨h * g, hh⟩
    · rintro ⟨h, hh⟩; exact ⟨h * g⁻¹, by simpa using hh⟩
  have hne := selSet_nonempty Φ hx
  have hne' : (selSet Φ (joinAct g x)).Nonempty := hS ▸ hne
  have hmin : (selSet Φ (joinAct g x)).min' hne' = (selSet Φ x).min' hne := by
    apply le_antisymm
    · exact Finset.min'_le _ _ (by rw [hS]; exact Finset.min'_mem _ hne)
    · exact Finset.min'_le _ _ (by rw [← hS]; exact Finset.min'_mem _ hne')
  have hmem : ∃ h, (1 : ℝ) / (D + 1) ≤ Φ x ((selSet Φ x).min' hne) h := by
    have := Finset.min'_mem _ hne
    simp only [selSet, Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this
  have hmem' : ∃ h, (1 : ℝ) / (D + 1) ≤
      Φ (joinAct g x) ((selSet Φ (joinAct g x)).min' hne') h := by
    have := Finset.min'_mem _ hne'
    simp only [selSet, Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this
  simp only [vtxSel, dif_pos hne, dif_pos hne', dif_pos hmem, dif_pos hmem', vact]
  refine Prod.ext hmin ?_
  have key : ∀ c : G, (1 : ℝ) / (D + 1) ≤
      Φ (joinAct g x) ((selSet Φ (joinAct g x)).min' hne') c → c = hmem.choose * g⁻¹ := by
    intro c h1
    have h2 := hmem.choose_spec
    rw [heq, hmin] at h1
    simp only [joinAct] at h1
    have hpos : (0 : ℝ) < 1 / (D + 1) := by positivity
    have := hx.2.1 _ _ _ (ne_of_gt (lt_of_lt_of_le hpos h1)) (ne_of_gt (lt_of_lt_of_le hpos h2))
    rw [← this]; group
  exact key _ hmem'.choose_spec

end SelectAct

end Dvoretzky.Dold
