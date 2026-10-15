module

public import RequestProject.Dvoretzky.Dold.Chains

/-!
# Barycentric subdivision of ordered affine chains

`sd [x₀, …, x_k] = b · sd (∂ [x₀, …, x_k])` (cone from the barycenter `b`), extended linearly.
We prove that `sd` is a chain map, commutes with linear maps, and that every simplex of
`sd [x₀, …, x_k]` lies in the convex hull of the `xᵢ` and has diameter at most `k/(k+1)` times
the diameter of `[x₀, …, x_k]`.
-/

@[expose] public section

open scoped BigOperators

noncomputable section

namespace Dvoretzky.Dold

variable {R : Type*} [CommRing R] {E : Type*}

lemma bdList_eq_sum (l : List E) :
    (bdList l : Chain R E) =
      ∑ i ∈ Finset.range l.length, ((-1 : R) ^ i) • Finsupp.single (l.eraseIdx i) (1 : R) := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [bdList_cons, ih, List.length_cons, Finset.sum_range_succ', map_sum]
    simp only [pow_zero, one_smul, List.eraseIdx_cons_zero,
      List.eraseIdx_cons_succ, map_smul, consL_single, pow_succ, mul_neg, mul_one, neg_smul,
      Finset.sum_neg_distrib, sub_eq_add_neg]
    abel

section Bary

variable [AddCommGroup E] [Module ℝ E]

/-- Barycenter of a list of points. -/
def bary (l : List E) : E := ((l.length : ℝ)⁻¹) • l.sum

lemma bary_map (T : E →ₗ[ℝ] E) (l : List E) : bary (l.map T) = T (bary l) := by
  simp only [bary, List.length_map, map_smul, map_list_sum]

/-- Barycentric subdivision of a single list. -/
def sdList : List E → Chain R E
  | [] => Finsupp.single [] 1
  | x :: l => consL (bary (x :: l))
      (∑ i : Fin (l.length + 1), ((-1 : R) ^ (i : ℕ)) • sdList ((x :: l).eraseIdx i))
termination_by l => l.length
decreasing_by
  rw [List.length_eraseIdx_of_lt (by simpa using i.isLt)]
  simp

/-- Barycentric subdivision. -/
def sd : Chain R E →ₗ[R] Chain R E := Finsupp.linearCombination R sdList

@[simp] lemma sd_single (l : List E) (c : R) :
    sd (Finsupp.single l c) = c • (sdList l : Chain R E) := by
  simp [sd]

lemma sdList_nil : (sdList [] : Chain R E) = Finsupp.single [] 1 := by
  rw [sdList]

lemma sdList_cons (x : E) (l : List E) :
    (sdList (x :: l) : Chain R E) = consL (bary (x :: l)) (sd (bdList (x :: l))) := by
  rw [sdList, bdList_eq_sum (x :: l), List.length_cons,
    ← Fin.sum_univ_eq_sum_range (fun i => ((-1 : R) ^ i) •
      Finsupp.single ((x :: l).eraseIdx i) (1 : R))]
  simp only [map_sum, map_smul, sd_single, one_smul]

lemma bd_sdList (l : List E) : bd (sdList l : Chain R E) = sd (bdList l) := by
  induction h : l.length using Nat.strong_induction_on generalizing l with
  | _ n ih =>
    cases l with
    | nil => simp [sdList_nil]
    | cons x m =>
      rw [sdList_cons, bd_consL]
      have : bd (sd (bdList (x :: m) : Chain R E)) = 0 := by
        rw [bdList_eq_sum, map_sum, map_sum]
        have h2 : ∀ i ∈ Finset.range (x :: m).length, bd (sd (((-1 : R) ^ i) •
            Finsupp.single ((x :: m).eraseIdx i) (1 : R))) = sd (bd (((-1 : R) ^ i) •
            Finsupp.single ((x :: m).eraseIdx i) (1 : R))) := by
          intro i hi
          rw [Finset.mem_range] at hi
          simp only [map_smul, sd_single, bd_single, one_smul]
          rw [ih _ (by rw [← h, List.length_eraseIdx_of_lt hi]; simp) _ rfl]
        rw [Finset.sum_congr rfl h2, ← map_sum, ← map_sum, ← bdList_eq_sum,
          bd_bdList, map_zero]
      rw [this, map_zero, sub_zero]

lemma bd_sd (c : Chain R E) : bd (sd c) = sd (bd c) := by
  have : (bd ∘ₗ sd : Chain R E →ₗ[R] Chain R E) = sd ∘ₗ bd := by
    refine chain_hom_ext fun l => ?_
    simp [bd_sdList]
  exact congrArg (fun F : Chain R E →ₗ[R] Chain R E => F c) this

lemma sdList_map (T : E →ₗ[ℝ] E) (l : List E) :
    (sdList (l.map T) : Chain R E) = actL (⇑T) (sdList l) := by
  induction h : l.length using Nat.strong_induction_on generalizing l with
  | _ n ih =>
    cases l with
    | nil => simp [sdList_nil]
    | cons x m =>
      rw [List.map_cons, sdList_cons, sdList_cons, actL_consL, ← List.map_cons, bary_map,
        ← actL_bdList]
      congr 1
      rw [bdList_eq_sum]
      simp only [map_sum, map_smul, actL_single, sd_single, one_smul]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      rw [ih _ ?_ _ rfl]
      rw [← h, List.length_eraseIdx_of_lt hi]
      simp

lemma sd_actL (T : E →ₗ[ℝ] E) (c : Chain R E) : sd (actL (⇑T) c) = actL (⇑T) (sd c) := by
  have : (sd ∘ₗ actL (⇑T) : Chain R E →ₗ[R] Chain R E) = actL (⇑T) ∘ₗ sd := by
    refine chain_hom_ext fun l => ?_
    simp [sdList_map]
  exact congrArg (fun F : Chain R E →ₗ[R] Chain R E => F c) this

end Bary

section Geometry

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The convex hull of the points of a list. -/
def hull (l : List E) : Set E := convexHull ℝ {a | a ∈ l}

lemma mem_hull_of_mem {l : List E} {a : E} (h : a ∈ l) : a ∈ hull l :=
  subset_convexHull ℝ _ h

lemma hull_mono {l m : List E} (h : ∀ a ∈ m, a ∈ hull l) : hull m ⊆ hull l :=
  convexHull_min h (convex_convexHull ℝ _)

omit [NormedSpace ℝ E] in
lemma norm_sum_sub_le (a : E) (D : ℝ) :
    ∀ l : List E, (∀ b ∈ l, ‖b - a‖ ≤ D) → ‖l.sum - l.length • a‖ ≤ l.length * D
  | [], _ => by simp
  | x :: l, h => by
    have ih := norm_sum_sub_le a D l fun b hb => h b (List.mem_cons_of_mem _ hb)
    have hx := h x (List.mem_cons_self ..)
    rw [List.sum_cons, List.length_cons, succ_nsmul',
      show x + l.sum - (a + l.length • a) = (x - a) + (l.sum - l.length • a) by abel]
    push_cast
    linarith [norm_add_le (x - a) (l.sum - l.length • a)]

omit [NormedSpace ℝ E] in
lemma norm_sum_sub_le' (a : E) (D : ℝ) :
    ∀ l : List E, a ∈ l → (∀ b ∈ l, ‖b - a‖ ≤ D) →
      ‖l.sum - l.length • a‖ ≤ (l.length - 1) * D
  | [], h, _ => by simp at h
  | x :: l, hmem, h => by
    have hD : 0 ≤ D := le_trans (norm_nonneg _) (h a hmem)
    rw [List.sum_cons, List.length_cons, succ_nsmul',
      show x + l.sum - (a + l.length • a) = (x - a) + (l.sum - l.length • a) by abel]
    push_cast
    rcases List.mem_cons.1 hmem with rfl | hl
    · rw [sub_self, zero_add]
      have := norm_sum_sub_le a D l fun b hb => h b (List.mem_cons_of_mem _ hb)
      linarith
    · have ih := norm_sum_sub_le' a D l hl fun b hb => h b (List.mem_cons_of_mem _ hb)
      have hx := h x (List.mem_cons_self ..)
      linarith [norm_add_le (x - a) (l.sum - l.length • a)]

lemma bary_mem_hull {l : List E} (hl : l ≠ []) : bary l ∈ hull l := by
  have hn : (0 : ℝ) < l.length := by
    have := List.length_pos_of_ne_nil hl
    exact_mod_cast this
  have hsum : l.sum = ∑ i : Fin l.length, l.get i := by
    conv_lhs => rw [← List.ofFn_get l]
    rw [List.sum_ofFn]
  rw [bary, hsum, Finset.smul_sum]
  refine (convex_convexHull ℝ _).sum_mem (fun i _ => by positivity) ?_
    (fun i _ => mem_hull_of_mem (List.get_mem l i))
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

lemma dist_bary_le {l : List E} (hl : l ≠ []) (D : ℝ)
    (hD : ∀ a ∈ l, ∀ b ∈ l, dist a b ≤ D) {y : E} (hy : y ∈ hull l) :
    dist (bary l) y ≤ ((l.length - 1 : ℝ) / l.length) * D := by
  have hn : (0 : ℝ) < l.length := by
    have := List.length_pos_of_ne_nil hl
    exact_mod_cast this
  suffices h : hull l ⊆ Metric.closedBall (bary l) (((l.length - 1 : ℝ) / l.length) * D) by
    have := h hy
    rw [Metric.mem_closedBall, dist_comm] at this
    exact this
  refine convexHull_min (fun a ha => ?_) (convex_closedBall _ _)
  rw [Set.mem_setOf_eq] at ha
  rw [Metric.mem_closedBall, dist_comm, dist_eq_norm, bary]
  have h1 : ((l.length : ℝ)⁻¹ • l.sum - a) = (l.length : ℝ)⁻¹ • (l.sum - l.length • a) := by
    rw [smul_sub, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hn.ne', one_smul]
  rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hn)]
  have h2 := norm_sum_sub_le' a D l ha fun b hb => by rw [← dist_eq_norm]; exact hD b hb a ha
  rw [div_mul_eq_mul_div, inv_mul_eq_div]
  exact div_le_div_of_nonneg_right h2 hn.le

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The support of the image of a chain under a linear map. -/
lemma mem_support_map {F : Chain R E →ₗ[R] Chain R E} {c : Chain R E} {m : List E}
    (hm : m ∈ (F c).support) : ∃ l ∈ c.support, m ∈ (F (Finsupp.single l 1)).support := by
  classical
  have hc : F c = ∑ l ∈ c.support, c l • F (Finsupp.single l 1) := by
    conv_lhs => rw [← Finsupp.sum_single c]
    rw [Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← map_smul, Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [hc] at hm
  obtain ⟨l, hl, hm⟩ := Finset.mem_biUnion.1 (Finsupp.support_finset_sum hm)
  exact ⟨l, hl, Finsupp.support_smul hm⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma mem_support_consL {x : E} {c : Chain R E} {m : List E}
    (hm : m ∈ (consL x c).support) : ∃ m', m = x :: m' ∧ m' ∈ c.support := by
  classical
  have := Finsupp.mapDomain_support hm
  obtain ⟨m', hm', rfl⟩ := Finset.mem_image.1 this
  exact ⟨m', rfl, hm'⟩

lemma ratio_mono (k : ℕ) : ((k : ℝ) - 1) / k ≤ ((k + 1 : ℕ) - 1 : ℝ) / (k + 1 : ℕ) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    push_cast
    rw [div_le_div_iff₀ hk' (by positivity)]
    nlinarith

lemma ratio_nonneg (k : ℕ) : 0 ≤ ((k : ℝ) - 1) / k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    exact div_nonneg (by linarith) (by linarith)

/-- Every simplex of `sd l` has the same length as `l`, lies in the convex hull of `l`, and has
diameter at most `(k/(k+1)) D` where `D` bounds the diameter of `l` and `k + 1` is its length. -/
lemma sdList_support (l : List E) (D : ℝ) (hD : ∀ a ∈ l, ∀ b ∈ l, dist a b ≤ D) :
    ∀ m ∈ (sdList l : Chain R E).support, m.length = l.length ∧ (∀ y ∈ m, y ∈ hull l) ∧
      ∀ y ∈ m, ∀ z ∈ m, dist y z ≤ ((l.length - 1 : ℝ) / l.length) * D := by
  classical
  induction h : l.length using Nat.strong_induction_on generalizing l D with
  | _ n ih =>
    intro m hm
    cases l with
    | nil =>
      rw [sdList_nil] at hm
      have : m = [] := Finset.mem_singleton.1 (Finsupp.support_single_subset hm)
      subst this
      simp [← h]
    | cons x l' =>
      subst h
      rw [sdList] at hm
      obtain ⟨m', rfl, hm'⟩ := mem_support_consL hm
      obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 (Finsupp.support_finset_sum hm')
      have hi' := Finsupp.support_smul hi
      set L := x :: l' with hL
      have hlen : (L.eraseIdx i).length = l'.length := by
        rw [List.length_eraseIdx_of_lt (by simpa [hL] using i.isLt)]; simp [hL]
      have hD0 : 0 ≤ D := le_trans dist_nonneg (hD x (by simp [hL]) x (by simp [hL]))
      obtain ⟨h1, h2, h3⟩ := ih l'.length (by simp [hL]) (L.eraseIdx i) D
        (fun a ha b hb => hD a (List.mem_of_mem_eraseIdx ha) b (List.mem_of_mem_eraseIdx hb))
        hlen m' hi'
      have hsub : hull (L.eraseIdx i) ⊆ hull L :=
        hull_mono fun a ha => mem_hull_of_mem (List.mem_of_mem_eraseIdx ha)
      have hLne : L ≠ [] := by simp [hL]
      have hLlen : L.length = l'.length + 1 := by simp [hL]
      have hq := ratio_mono l'.length
      have hq0 := ratio_nonneg (l'.length + 1)
      rw [← hLlen] at hq hq0
      refine ⟨by simp [h1, hLlen], ?_, ?_⟩
      · intro y hy
        rcases List.mem_cons.1 hy with rfl | hy
        · exact bary_mem_hull hLne
        · exact hsub (h2 y hy)
      · have hb : ∀ z ∈ m', dist (bary L) z ≤ ((L.length - 1 : ℝ) / L.length) * D :=
          fun z hz => dist_bary_le hLne D hD (hsub (h2 z hz))
        have hm'' : ∀ y ∈ m', ∀ z ∈ m', dist y z ≤ ((L.length - 1 : ℝ) / L.length) * D :=
          fun y hy z hz => (h3 y hy z hz).trans (mul_le_mul_of_nonneg_right hq hD0)
        intro y hy z hz
        rcases List.mem_cons.1 hy with rfl | hy <;> rcases List.mem_cons.1 hz with rfl | hz
        · simp only [dist_self]; positivity
        · exact hb z hz
        · rw [dist_comm]; exact hb y hy
        · exact hm'' y hy z hz

/-- Iterated subdivision. -/
lemma sdIter_support (r : ℕ) (l : List E) (D : ℝ) (hD : ∀ a ∈ l, ∀ b ∈ l, dist a b ≤ D) :
    ∀ m ∈ (((sd : Module.End R (Chain R E)) ^ r) (Finsupp.single l 1)).support,
      m.length = l.length ∧ (∀ y ∈ m, y ∈ hull l) ∧
      ∀ y ∈ m, ∀ z ∈ m, dist y z ≤ (((l.length - 1 : ℝ) / l.length) ^ r) * D := by
  classical
  induction r with
  | zero =>
    intro m hm
    simp only [pow_zero, Module.End.one_apply] at hm
    have : m = l := Finset.mem_singleton.1 (Finsupp.support_single_subset hm)
    subst this
    exact ⟨rfl, fun y hy => mem_hull_of_mem hy, by simpa using hD⟩
  | succ r ih =>
    intro m hm
    rw [pow_succ', Module.End.mul_apply] at hm
    obtain ⟨m', hm', hm⟩ := mem_support_map (F := sd) hm
    obtain ⟨h1, h2, h3⟩ := ih m' hm'
    rw [sd_single, one_smul] at hm
    obtain ⟨g1, g2, g3⟩ := sdList_support m' _ h3 m hm
    refine ⟨g1.trans h1, fun y hy => hull_mono h2 (g2 y hy), fun y hy z hz => ?_⟩
    have := g3 y hy z hz
    rw [h1] at this
    calc dist y z ≤ _ := this
      _ = _ := by rw [pow_succ']; ring

end Geometry

end Dvoretzky.Dold
