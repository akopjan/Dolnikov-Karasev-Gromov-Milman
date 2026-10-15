module

public import RequestProject.Dvoretzky.Dold.Chains

/-!
# Oriented chains of the join `G * ⋯ * G` (`D` factors)

A simplex of the join of `D` copies of a set `G` is a partial function `s : Fin D → Option G`
(the empty partial function is the augmentation simplex). Simplices are oriented by the order
of the join coordinates, which is invariant under the action of `G` on the labels.

* `bdT` is the boundary operator, `bdT_bdT : ∂∂ = 0`;
* `wedge v` adds the vertex `v = (j, h)` in front (with the sign of the position of `j`);
* `alpha w = v₀ ∧ v₁ ∧ ⋯ ∧ v_k` for a list `w` of vertices, so that
  `bdT (alpha w) = alpha (∂ w)` when `w` is *consistent* (two vertices with the same coordinate are
  equal), and `alpha w = 0` if `w` has a repeated vertex.
-/

@[expose] public section

open scoped BigOperators

noncomputable section

namespace Dvoretzky.Dold

variable {R : Type*} [CommRing R] {D : ℕ} {G : Type*}

/-- Simplices of the `D`-fold join of `G` (partial functions). -/
abbrev Smp (D : ℕ) (G : Type*) := Fin D → Option G

/-- Oriented chains of the `D`-fold join of `G`. -/
abbrev TChain (R : Type*) [CommRing R] (D : ℕ) (G : Type*) := Smp D G →₀ R

/-- The empty simplex. -/
def emptyS : Smp D G := fun _ => none

/-- Number of vertices of `s` with coordinate `< j`. -/
def pos (s : Smp D G) (j : Fin D) : ℕ :=
  (Finset.univ.filter (fun j' => j' < j ∧ (s j').isSome)).card

/-- The sign `(-1)^(pos s j)`. -/
def sgnP (s : Smp D G) (j : Fin D) : R := (-1) ^ pos s j

section Pos

lemma sgnP_mul_self (s : Smp D G) (j : Fin D) : (sgnP s j : R) * sgnP s j = 1 := by
  rw [sgnP, ← pow_add, ← two_mul, pow_mul]; simp

lemma pos_update_of_le (s : Smp D G) {a j : Fin D} (h : j ≤ a) (x : Option G) :
    pos (Function.update s a x) j = pos s j := by
  unfold pos
  congr 1
  ext j'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩
    rw [Function.update_of_ne (by intro e; subst e; exact absurd h1 (not_lt.2 h))] at h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    rw [Function.update_of_ne (by intro e; subst e; exact absurd h1 (not_lt.2 h))]
    exact ⟨h1, h2⟩

lemma sgnP_update_of_le (s : Smp D G) {a j : Fin D} (h : j ≤ a) (x : Option G) :
    (sgnP (Function.update s a x) j : R) = sgnP s j := by
  rw [sgnP, sgnP, pos_update_of_le s h]

lemma pos_update_some (s : Smp D G) {a j : Fin D} (h : a < j) (ha : s a = none) (g : G) :
    pos (Function.update s a (some g)) j = pos s j + 1 := by
  unfold pos
  rw [← Finset.card_insert_of_notMem (a := a) (by simp [ha])]
  congr 1
  ext j'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  by_cases e : j' = a
  · subst e; simp [h]
  · rw [Function.update_of_ne e]; simp [e]

lemma pos_update_none (s : Smp D G) {a j : Fin D} (h : a < j) (ha : (s a).isSome) :
    pos (Function.update s a none) j + 1 = pos s j := by
  unfold pos
  rw [← Finset.card_insert_of_notMem (a := a) (by simp)]
  congr 1
  ext j'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  by_cases e : j' = a
  · subst e; simp [h, ha]
  · rw [Function.update_of_ne e]; simp [e]

lemma sgnP_update_some (s : Smp D G) {a j : Fin D} (h : a < j) (ha : s a = none) (g : G) :
    (sgnP (Function.update s a (some g)) j : R) = - sgnP s j := by
  rw [sgnP, sgnP, pos_update_some s h ha, pow_succ]; ring

lemma sgnP_update_none (s : Smp D G) {a j : Fin D} (h : a < j) (ha : (s a).isSome) :
    (sgnP (Function.update s a none) j : R) = - sgnP s j := by
  rw [sgnP, sgnP, ← pos_update_none s h ha, pow_succ]; ring

end Pos

/-- Boundary of a single simplex. -/
def faceT (s : Smp D G) : TChain R D G :=
  ∑ j, if (s j).isSome then (sgnP s j : R) • Finsupp.single (Function.update s j none) 1 else 0

/-- The boundary operator. -/
def bdT : TChain R D G →ₗ[R] TChain R D G := Finsupp.linearCombination R faceT

@[simp] lemma bdT_single (s : Smp D G) (c : R) :
    bdT (Finsupp.single s c) = c • (faceT s : TChain R D G) := by
  simp [bdT]

/-- Adding the vertex `v` in front of a single simplex. -/
def wedgeS (v : Fin D × G) (s : Smp D G) : TChain R D G :=
  if s v.1 = none then (sgnP s v.1 : R) • Finsupp.single (Function.update s v.1 (some v.2)) 1
  else 0

/-- Adding the vertex `v` in front. -/
def wedge (v : Fin D × G) : TChain R D G →ₗ[R] TChain R D G :=
  Finsupp.linearCombination R (wedgeS v)

@[simp] lemma wedge_single (v : Fin D × G) (s : Smp D G) (c : R) :
    wedge v (Finsupp.single s c) = c • (wedgeS v s : TChain R D G) := by
  simp [wedge]

lemma tchain_hom_ext {f g : TChain R D G →ₗ[R] TChain R D G}
    (h : ∀ s : Smp D G, f (Finsupp.single s 1) = g (Finsupp.single s 1)) : f = g :=
  Finsupp.lhom_ext' fun s => LinearMap.ext_ring (h s)

/-- Expansion of a chain in the basis. -/
lemma tchain_eq_sum (c : TChain R D G) :
    c = ∑ s ∈ c.support, c s • Finsupp.single s (1 : R) := by
  conv_lhs => rw [← Finsupp.sum_single c]
  rw [Finsupp.sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finsupp.smul_single, smul_eq_mul, mul_one]

/-- The key identity `∂ (v ∧ s) = s - v ∧ ∂ s` for a simplex `s` consistent with `v`. -/
lemma bdT_wedgeS (v : Fin D × G) (s : Smp D G) (hs : s v.1 = none ∨ s v.1 = some v.2) :
    bdT (wedgeS v s : TChain R D G) = Finsupp.single s 1 - wedge v (faceT s) := by
  obtain ⟨a, g⟩ := v
  simp only at hs ⊢
  rcases hs with ha | ha
  · -- `s a = none`
    simp only [wedgeS, ha, if_true, map_smul, bdT_single, one_smul]
    set s' := Function.update s a (some g) with hs'
    rw [faceT, faceT, map_sum, Fintype.sum_eq_add_sum_compl a, Fintype.sum_eq_add_sum_compl a]
    have hs'a : (s' a).isSome := by simp [hs']
    simp only [hs'a, if_true, ha, Option.isSome_none, Bool.false_eq_true, if_false, map_zero,
      zero_add]
    have h1 : Function.update s' a none = s := by
      rw [hs', Function.update_idem, Function.update_eq_self_iff.2 ha.symm]
    rw [h1, sgnP_update_of_le s le_rfl, smul_add, smul_smul, sgnP_mul_self, one_smul,
      Finset.smul_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    have hja : j ≠ a := by simpa using hj
    have hsj : (s' j).isSome = (s j).isSome := by rw [hs', Function.update_of_ne hja]
    rw [hsj]
    split_ifs with hj'
    · rw [map_smul, wedge_single, one_smul, wedgeS]
      simp only
      rw [if_pos (by rw [Function.update_of_ne (Ne.symm hja)]; exact ha)]
      rw [hs', Function.update_comm (Ne.symm hja), smul_smul, smul_smul, ← neg_smul]
      congr 1
      rcases lt_or_gt_of_ne hja with hlt | hlt
      · rw [sgnP_update_of_le s hlt.le, sgnP_update_none s hlt hj']; ring
      · rw [sgnP_update_some s hlt ha, sgnP_update_of_le s hlt.le]; ring
    · simp
  · -- `s a = some g`
    simp only [wedgeS, ha, reduceCtorEq, if_false, map_zero]
    rw [faceT, map_sum, Fintype.sum_eq_add_sum_compl a]
    have hsa : (s a).isSome := by simp [ha]
    simp only [hsa, if_true, map_smul, wedge_single, one_smul]
    rw [Finset.sum_eq_zero]
    · have hup : Function.update s a (some g) = s := Function.update_eq_self_iff.2 ha.symm
      simp only [wedgeS, Function.update_self, if_true, add_zero]
      rw [Function.update_idem, hup, smul_smul,
        sgnP_update_of_le s le_rfl, sgnP_mul_self, one_smul, sub_self]
    · intro j hj
      have hja : j ≠ a := by simpa using hj
      have hne : Function.update s j none a ≠ none := by
        rw [Function.update_of_ne (Ne.symm hja), ha]; simp
      split_ifs
      · rw [map_smul, wedge_single, wedgeS, if_neg hne]
        simp
      · simp

lemma bdT_wedge (v : Fin D × G) (c : TChain R D G)
    (hc : ∀ s ∈ c.support, s v.1 = none ∨ s v.1 = some v.2) :
    bdT (wedge v c) = c - wedge v (bdT c) := by
  conv_lhs => rw [tchain_eq_sum c]
  conv_rhs => rw [tchain_eq_sum c]
  simp only [map_sum, map_smul, wedge_single, bdT_single, one_smul]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [bdT_wedgeS v s (hc s hs), smul_sub]

/-- Sum of an antisymmetric family vanishes. -/
lemma sum_antisymm {M : Type*} [AddCommGroup M] {ι : Type*} [Fintype ι] (f : ι → ι → M)
    (hf : ∀ i j, f j i = - f i j) (hd : ∀ i, f i i = 0) : ∑ i, ∑ j, f i j = 0 := by
  rw [← Finset.sum_product']
  refine Finset.sum_involution (fun x _ => (x.2, x.1)) (fun x _ => ?_) (fun x _ hx => ?_)
    (fun x _ => by simp) (fun x _ => by simp)
  · simp [hf x.1 x.2]
  · intro e
    apply hx
    have : x.1 = x.2 := by simpa [Prod.ext_iff, eq_comm] using e
    rw [show x = (x.1, x.2) from rfl, this, hd]

lemma bdT_faceT (s : Smp D G) : bdT (faceT s : TChain R D G) = 0 := by
  let f : Fin D → Fin D → TChain R D G := fun j j' =>
    if (s j).isSome ∧ (Function.update s j none j').isSome then
      ((sgnP s j : R) * sgnP (Function.update s j none) j') •
        Finsupp.single (Function.update (Function.update s j none) j' none) 1 else 0
  have h1 : bdT (faceT s : TChain R D G) = ∑ j, ∑ j', f j j' := by
    rw [faceT, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : (s j).isSome
    · simp only [hj, if_true, map_smul, bdT_single, one_smul, faceT, Finset.smul_sum, f,
        true_and]
      refine Finset.sum_congr rfl fun j' _ => ?_
      split_ifs <;> simp
    · simp [hj, f]
  rw [h1]
  refine sum_antisymm f (fun i j => ?_) (fun i => by simp [f])
  by_cases hij : i = j
  · subst hij; simp [f]
  have hu : Function.update (Function.update s j none) i none =
      Function.update (Function.update s i none) j none := Function.update_comm (Ne.symm hij) _ _ _
  simp only [f, Function.update_of_ne hij, Function.update_of_ne (Ne.symm hij), hu]
  by_cases hi : (s i).isSome
  · by_cases hj : (s j).isSome
    · simp only [hi, hj, and_self, if_true, ← neg_smul]
      congr 1
      rcases lt_or_gt_of_ne hij with hlt | hlt
      · rw [sgnP_update_of_le s hlt.le, sgnP_update_none s hlt hi]; ring
      · rw [sgnP_update_none s hlt hj, sgnP_update_of_le s hlt.le]; ring
    · simp [hj]
  · simp [hi]

lemma bdT_bdT (c : TChain R D G) : bdT (bdT c) = 0 := by
  have : (bdT ∘ₗ bdT : TChain R D G →ₗ[R] TChain R D G) = 0 :=
    tchain_hom_ext fun s => by simp [bdT_faceT]
  exact congrArg (fun F : TChain R D G →ₗ[R] TChain R D G => F c) this

/-! ### Wedges of lists of vertices -/

/-- `alpha [v₀, …, v_k] = v₀ ∧ ⋯ ∧ v_k`. -/
def alpha : List (Fin D × G) → TChain R D G
  | [] => Finsupp.single emptyS 1
  | v :: w => wedge v (alpha w)

/-- The linear extension of `alpha` to ordered chains of vertices. -/
def alphaL : Chain R (Fin D × G) →ₗ[R] TChain R D G := Finsupp.linearCombination R alpha

@[simp] lemma alphaL_single (w : List (Fin D × G)) (c : R) :
    alphaL (Finsupp.single w c) = c • (alpha w : TChain R D G) := by
  simp [alphaL]

lemma alphaL_consL (v : Fin D × G) (c : Chain R (Fin D × G)) :
    alphaL (consL v c) = wedge v (alphaL c) := by
  have : (alphaL ∘ₗ consL v : Chain R (Fin D × G) →ₗ[R] TChain R D G) = wedge v ∘ₗ alphaL := by
    refine chain_hom_ext fun l => ?_
    simp [alpha]
  exact congrArg (fun F : Chain R (Fin D × G) →ₗ[R] TChain R D G => F c) this

lemma mem_support_wedge {v : Fin D × G} {c : TChain R D G} {s : Smp D G}
    (hs : s ∈ (wedge v c).support) :
    ∃ t ∈ c.support, t v.1 = none ∧ s = Function.update t v.1 (some v.2) := by
  classical
  rw [tchain_eq_sum c, map_sum] at hs
  obtain ⟨t, ht, hs⟩ := Finset.mem_biUnion.1 (Finsupp.support_finset_sum hs)
  rw [map_smul, wedge_single, one_smul] at hs
  have hs := Finsupp.support_smul hs
  unfold wedgeS at hs
  split_ifs at hs with h
  · have := Finset.mem_singleton.1 (Finsupp.support_single_subset (Finsupp.support_smul hs))
    exact ⟨t, ht, h, this⟩
  · simp at hs

/-- The simplices in the support of `alpha w` have exactly the vertices of `w`. -/
lemma mem_support_alpha {w : List (Fin D × G)} {s : Smp D G}
    (hs : s ∈ (alpha w : TChain R D G).support) : ∀ j g, s j = some g ↔ (j, g) ∈ w := by
  induction w generalizing s with
  | nil =>
    have : s = emptyS := Finset.mem_singleton.1 (Finsupp.support_single_subset hs)
    subst this
    simp [emptyS]
  | cons v w ih =>
    obtain ⟨t, ht, htv, rfl⟩ := mem_support_wedge hs
    have iht := ih ht
    intro j g
    by_cases hj : j = v.1
    · subst hj
      simp only [Function.update_self, Option.some.injEq, List.mem_cons]
      constructor
      · rintro rfl; left; rfl
      · rintro (h | h)
        · exact (congrArg Prod.snd h).symm
        · rw [← iht] at h; rw [htv] at h; simp at h
    · rw [Function.update_of_ne hj, iht, List.mem_cons]
      constructor
      · exact Or.inr
      · rintro (h | h)
        · exact absurd (congrArg Prod.fst h) hj
        · exact h

/-- A list of vertices is *consistent* if two vertices with the same coordinate coincide. -/
def Consistent (w : List (Fin D × G)) : Prop := ∀ a ∈ w, ∀ b ∈ w, a.1 = b.1 → a = b

lemma Consistent.of_subset {w w' : List (Fin D × G)} (h : Consistent w) (hs : ∀ a ∈ w', a ∈ w) :
    Consistent w' := fun a ha b hb => h a (hs a ha) b (hs b hb)

lemma alpha_eq_zero_of_not_nodup {w : List (Fin D × G)} (hw : ¬ w.Nodup) :
    (alpha w : TChain R D G) = 0 := by
  induction w with
  | nil => simp at hw
  | cons v w ih =>
    rw [alpha]
    by_cases hv : v ∈ w
    · have : (alpha w : TChain R D G) = (alpha w : TChain R D G) := rfl
      rw [tchain_eq_sum (alpha w), map_sum]
      refine Finset.sum_eq_zero fun s hs => ?_
      have := (mem_support_alpha hs v.1 v.2).2 hv
      rw [map_smul, wedge_single, wedgeS, if_neg (by rw [this]; simp)]
      simp
    · rw [List.nodup_cons, not_and] at hw
      rw [ih (hw hv), map_zero]

lemma not_nodup_of_consistent {w : List (Fin D × G)} (hw : Consistent w) (hlen : D < w.length) :
    ¬ w.Nodup := by
  intro hnd
  have h2 : (w.map Prod.fst).Nodup := hnd.map_on fun a ha b hb e => hw a ha b hb e
  have := h2.length_le_card
  simp at this
  omega

lemma alpha_eq_zero_of_length {w : List (Fin D × G)} (hw : Consistent w) (hlen : D < w.length) :
    (alpha w : TChain R D G) = 0 :=
  alpha_eq_zero_of_not_nodup (not_nodup_of_consistent hw hlen)

/-- `alpha` is a chain map on consistent lists. -/
lemma bdT_alpha {w : List (Fin D × G)} (hw : Consistent w) :
    bdT (alpha w : TChain R D G) = alphaL (bdList w) := by
  induction w with
  | nil =>
    simp [alpha, faceT, emptyS]
  | cons v w ih =>
    have hw' : Consistent w := hw.of_subset fun a ha => List.mem_cons_of_mem _ ha
    rw [alpha, bdT_wedge, ih hw', bdList_cons, map_sub, alphaL_single, one_smul, alphaL_consL]
    intro s hs
    by_cases h : s v.1 = none
    · exact Or.inl h
    · obtain ⟨g, hg⟩ := Option.ne_none_iff_exists'.1 h
      right
      have hmem := (mem_support_alpha hs v.1 g).1 hg
      have := hw v (List.mem_cons_self ..) (v.1, g) (List.mem_cons_of_mem _ hmem) rfl
      rw [hg, this]

end Dvoretzky.Dold
