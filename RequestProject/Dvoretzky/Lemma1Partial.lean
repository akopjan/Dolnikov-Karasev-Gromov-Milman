module

public import RequestProject.Dvoretzky.JoinBU

/-!
# Partial results towards Lemma 1 (`JoinBorsukUlam`)

* `joinBorsukUlam_iff`: Lemma 1 is equivalent to its "zero" form, i.e. to the statement for
  representations without nonzero fixed vectors, where the conclusion is that the map vanishes
  somewhere (pass to the orthogonal complement of the fixed subspace).
* `JoinZeroProperty.mono`: the property is monotone in the number `N` of join factors.
* `isPreconnected_groupJoin`: the `N`-fold join is connected for `N ≥ 2`.
* `joinZeroProperty_of_finrank_le_one`, `joinFixedProperty_of_finrank_compl_le_one`: Lemma 1
  holds (with `N = 2`, for any finite group) when the complement of the fixed subspace has
  dimension at most one; this is the intermediate value theorem.

The general case is not proved here: it is the Borsuk–Ulam property of finite `2`-groups, whose
known proofs use Carlsson's theorem (the Segal conjecture); already the case of the group of
order `2` is the classical Borsuk–Ulam theorem; that case (and more generally the case of a group
containing an involution whose fixed vectors are fixed by the whole group) is proved in
`RequestProject/Dvoretzky/Lemma1Involution.lean` from the Borsuk–Ulam theorem of the
`HamSandwich` library.
-/

@[expose] public section

open scoped BigOperators InnerProductSpace

noncomputable section

namespace Dvoretzky

variable {G : Type} [Group G]
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The `G`-fixed subspace `V^G` of an orthogonal representation. -/
def fixedSubspace (ρ : G →* (V ≃ₗᵢ[ℝ] V)) : Submodule ℝ V where
  carrier := {v | ∀ g, ρ g v = v}
  add_mem' ha hb g := by simp_all
  zero_mem' g := by simp
  smul_mem' c v hv g := by simp_all

/-- Lemma 1 for a fixed group, representation and join size, in the "zero" form: every continuous
equivariant map from the `N`-fold join of `G` to `V` vanishes somewhere. -/
def JoinZeroProperty (G : Type) [Group G] [Fintype G] (V : Type) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (ρ : G →* (V ≃ₗᵢ[ℝ] V)) (N : ℕ) : Prop :=
  ∀ f : (Fin N → G → ℝ) → V, ContinuousOn f (GroupJoin G N) →
    (∀ g, ∀ x ∈ GroupJoin G N, f (joinAct g x) = ρ g (f x)) → ∃ x ∈ GroupJoin G N, f x = 0

/-- Lemma 1 for a fixed group, representation and join size, in the "fixed value" form. -/
def JoinFixedProperty (G : Type) [Group G] [Fintype G] (V : Type) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (ρ : G →* (V ≃ₗᵢ[ℝ] V)) (N : ℕ) : Prop :=
  ∀ f : (Fin N → G → ℝ) → V, ContinuousOn f (GroupJoin G N) →
    (∀ g, ∀ x ∈ GroupJoin G N, f (joinAct g x) = ρ g (f x)) →
      ∃ x ∈ GroupJoin G N, ∀ g, ρ g (f x) = f x

section Complement

variable (ρ : G →* (V ≃ₗᵢ[ℝ] V))

lemma mem_fixedSubspace_iff {v : V} : v ∈ fixedSubspace ρ ↔ ∀ g, ρ g v = v := Iff.rfl

/-- The orthogonal complement of the fixed subspace is invariant. -/
lemma map_mem_fixedCompl (g : G) {v : V} (hv : v ∈ (fixedSubspace ρ)ᗮ) :
    ρ g v ∈ (fixedSubspace ρ)ᗮ := by
  intro u hu
  have := hv u hu
  rw [← this, ← (ρ g).inner_map_map u v, hu g]

/-- The restriction of `ρ g` to the orthogonal complement of the fixed subspace. -/
def complRepFun (g : G) : (fixedSubspace ρ)ᗮ ≃ₗᵢ[ℝ] (fixedSubspace ρ)ᗮ where
  toLinearEquiv := LinearEquiv.ofLinear
    ((ρ g).toLinearEquiv.toLinearMap.restrict (fun v hv => map_mem_fixedCompl ρ g hv))
    ((ρ g⁻¹).toLinearEquiv.toLinearMap.restrict (fun v hv => map_mem_fixedCompl ρ g⁻¹ hv))
    (by
      ext v
      simp [LinearMap.restrict_apply])
    (by
      ext v
      simp [LinearMap.restrict_apply])
  norm_map' v := by
    change ‖ρ g (v : V)‖ = ‖(v : V)‖
    exact (ρ g).norm_map v

@[simp] lemma coe_complRepFun (g : G) (v : (fixedSubspace ρ)ᗮ) :
    ((complRepFun ρ g v : (fixedSubspace ρ)ᗮ) : V) = ρ g v := rfl

/-- The subrepresentation on the orthogonal complement of the fixed subspace. -/
def complRep : G →* ((fixedSubspace ρ)ᗮ ≃ₗᵢ[ℝ] (fixedSubspace ρ)ᗮ) where
  toFun := complRepFun ρ
  map_one' := by ext v; simp
  map_mul' g h := by ext v; simp [LinearIsometryEquiv.coe_mul]

@[simp] lemma coe_complRep (g : G) (v : (fixedSubspace ρ)ᗮ) :
    ((complRep ρ g v : (fixedSubspace ρ)ᗮ) : V) = ρ g v := rfl

/-- The complementary subrepresentation has no nonzero fixed vectors. -/
lemma complRep_fixed_eq_zero (v : (fixedSubspace ρ)ᗮ) (hv : ∀ g, complRep ρ g v = v) : v = 0 := by
  have h1 : (v : V) ∈ fixedSubspace ρ := fun g => by
    simpa using congrArg Subtype.val (hv g)
  have h2 := v.2
  have := Submodule.inner_right_of_mem_orthogonal h1 h2
  ext
  simpa using this

variable [FiniteDimensional ℝ V]

/-- The orthogonal projection onto the complement of the fixed subspace is equivariant. -/
lemma orthogonalProjection_fixedCompl_equivariant (g : G) (v : V) :
    (fixedSubspace ρ)ᗮ.orthogonalProjection (ρ g v) =
      complRep ρ g ((fixedSubspace ρ)ᗮ.orthogonalProjection v) := by
  set W := (fixedSubspace ρ)ᗮ
  ext
  rw [coe_complRep, ← Submodule.starProjection_apply]
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · exact map_mem_fixedCompl ρ g (W.orthogonalProjection v).2
  · have hw : v - (W.orthogonalProjection v : V) ∈ fixedSubspace ρ := by
      have := W.sub_starProjection_mem_orthogonal v
      rwa [Submodule.orthogonal_orthogonal] at this
    rw [Submodule.orthogonal_orthogonal, ← map_sub]
    rw [hw g]
    exact hw

/-- If the complementary subrepresentation satisfies the zero form of Lemma 1, then `ρ`
satisfies the fixed-value form. -/
theorem joinFixedProperty_of_complRep [Fintype G] {N : ℕ}
    (h : JoinZeroProperty G (fixedSubspace ρ)ᗮ (complRep ρ) N) :
    JoinFixedProperty G V ρ N := by
  intro f hf hequiv
  set W := (fixedSubspace ρ)ᗮ
  obtain ⟨x, hx, hx0⟩ := h (fun x => W.orthogonalProjection (f x))
    ((W.orthogonalProjection).continuous.comp_continuousOn hf)
    (fun g x hx => by
      rw [hequiv g x hx, orthogonalProjection_fixedCompl_equivariant])
  refine ⟨x, hx, ?_⟩
  rw [Submodule.orthogonalProjection_eq_zero_iff, Submodule.orthogonal_orthogonal] at hx0
  exact hx0

end Complement

section Join

variable [Fintype G]

lemma joinAct_mem {N : ℕ} (g : G) {x : Fin N → G → ℝ} (hx : x ∈ GroupJoin G N) :
    joinAct g x ∈ GroupJoin G N := by
  obtain ⟨h0, h1, h2⟩ := hx
  refine ⟨fun i h => h0 i (h * g), fun i h h' a b => mul_right_cancel (h1 i _ _ a b), ?_⟩
  rw [← h2]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Fintype.sum_equiv (Equiv.mulRight g) _ _ (fun h => rfl)

/-- Extension by zero from the `N`-fold join to the `N'`-fold join. -/
def joinIncl {N N' : ℕ} (x : Fin N → G → ℝ) : Fin N' → G → ℝ :=
  fun i h => if hi : (i : ℕ) < N then x ⟨i, hi⟩ h else 0

omit [Group G] in
lemma joinIncl_mem {N N' : ℕ} (hN : N ≤ N') {x : Fin N → G → ℝ} (hx : x ∈ GroupJoin G N) :
    (joinIncl x : Fin N' → G → ℝ) ∈ GroupJoin G N' := by
  obtain ⟨h0, h1, h2⟩ := hx
  refine ⟨fun i h => ?_, fun i h h' a b => ?_, ?_⟩
  · unfold joinIncl; split_ifs <;> simp [h0]
  · unfold joinIncl at a b; split_ifs at a b with hi
    · exact h1 _ _ _ a b
    · exact absurd rfl a
  · rw [← h2]
    symm
    refine Fintype.sum_of_injective (Fin.castLE hN) (Fin.castLE_injective hN) _ _ ?_ ?_
    · intro i hi
      refine Finset.sum_eq_zero fun h _ => ?_
      unfold joinIncl
      rw [dif_neg]
      intro hlt
      exact hi ⟨⟨i, hlt⟩, rfl⟩
    · intro i
      refine Finset.sum_congr rfl fun h _ => ?_
      simp [joinIncl]

omit [Group G] [Fintype G] in
lemma continuous_joinIncl {N N' : ℕ} :
    Continuous (joinIncl : (Fin N → G → ℝ) → Fin N' → G → ℝ) := by
  refine continuous_pi fun i => continuous_pi fun h => ?_
  unfold joinIncl
  split_ifs
  · exact (continuous_apply h).comp (continuous_apply _)
  · exact continuous_const

omit [Fintype G] in
lemma joinIncl_joinAct {N N' : ℕ} (g : G) (x : Fin N → G → ℝ) :
    (joinIncl (joinAct g x) : Fin N' → G → ℝ) = joinAct g (joinIncl x) := by
  ext i h
  simp only [joinIncl, joinAct]

/-- The zero form of Lemma 1 is monotone in the size of the join. -/
theorem JoinZeroProperty.mono {ρ : G →* (V ≃ₗᵢ[ℝ] V)} {N N' : ℕ} (hN : N ≤ N')
    (h : JoinZeroProperty G V ρ N) : JoinZeroProperty G V ρ N' := by
  intro f hf hequiv
  obtain ⟨x, hx, hfx⟩ := h (fun x => f (joinIncl x))
    (hf.comp continuous_joinIncl.continuousOn (fun x hx => joinIncl_mem hN hx))
    (fun g x hx => by
      rw [joinIncl_joinAct, hequiv g _ (joinIncl_mem hN hx)])
  exact ⟨_, joinIncl_mem hN hx, hfx⟩

open Classical in
/-- The vertex `(i, h)` of the join. -/
def joinVertex {N : ℕ} (i : Fin N) (h : G) : Fin N → G → ℝ :=
  fun j k => if j = i ∧ k = h then 1 else 0

omit [Group G] in
lemma joinVertex_mem {N : ℕ} (i : Fin N) (h : G) : joinVertex i h ∈ GroupJoin G N := by
  refine ⟨fun j k => ?_, fun j k k' a b => ?_, ?_⟩
  · unfold joinVertex; split_ifs <;> norm_num
  · unfold joinVertex at a b
    split_ifs at a b with h1 h2 <;> simp_all
  · simp only [joinVertex]
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single h]
      · simp
      · intro b _ hb; simp [hb]
      · simp
    · intro j _ hj; simp [hj]
    · simp

omit [Group G] in
/-- The segment between two points of the join whose labels agree blockwise lies in the join. -/
lemma segment_subset_groupJoin {N : ℕ} {x z : Fin N → G → ℝ} (hx : x ∈ GroupJoin G N)
    (hz : z ∈ GroupJoin G N) (hcompat : ∀ i h h', x i h ≠ 0 → z i h' ≠ 0 → h = h') :
    segment ℝ x z ⊆ GroupJoin G N := by
  obtain ⟨x0, x1, x2⟩ := hx
  obtain ⟨z0, z1, z2⟩ := hz
  rintro _ ⟨a, b, ha, hb, hab, rfl⟩
  have key : ∀ i h, (a • x + b • z) i h ≠ 0 → x i h ≠ 0 ∨ z i h ≠ 0 := by
    intro i h hne
    by_contra hc
    push_neg at hc
    apply hne
    simp [hc.1, hc.2]
  refine ⟨fun i h => ?_, fun i h h' p q => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := x0 i h; have := z0 i h; positivity
  · rcases key i h p with p | p <;> rcases key i h' q with q | q
    · exact x1 i h h' p q
    · exact hcompat i h h' p q
    · exact (hcompat i h' h q p).symm
    · exact z1 i h h' p q
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, x2, z2]
    linarith

omit [Group G] in
/-- For `N ≥ 2` the join is connected. -/
lemma isPreconnected_groupJoin {N : ℕ} (hN : 2 ≤ N) [Nonempty G] :
    IsPreconnected (GroupJoin G N) := by
  let i0 : Fin N := ⟨0, by omega⟩
  let i1 : Fin N := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  obtain ⟨g1⟩ := ‹Nonempty G›
  refine isPreconnected_of_forall (joinVertex i1 g1) fun y hy => ?_
  have : ∃ h0 : G, ∀ h, y i0 h ≠ 0 → h = h0 := by
    by_cases hex : ∃ h, y i0 h ≠ 0
    · obtain ⟨h0, hh0⟩ := hex
      exact ⟨h0, fun h hh => hy.2.1 i0 h h0 hh hh0⟩
    · push_neg at hex
      exact ⟨g1, fun h hh => absurd (hex h) hh⟩
  obtain ⟨h0, hh0⟩ := this
  refine ⟨segment ℝ y (joinVertex i0 h0) ∪ segment ℝ (joinVertex i0 h0) (joinVertex i1 g1),
    Set.union_subset ?_ ?_, Or.inr (right_mem_segment _ _ _), Or.inl (left_mem_segment _ _ _), ?_⟩
  · refine segment_subset_groupJoin hy (joinVertex_mem _ _) fun i h h' p q => ?_
    unfold joinVertex at q
    split_ifs at q with hq
    · obtain ⟨rfl, rfl⟩ := hq
      exact hh0 h p
    · exact absurd rfl q
  · refine segment_subset_groupJoin (joinVertex_mem _ _) (joinVertex_mem _ _) fun i h h' p q => ?_
    unfold joinVertex at p q
    split_ifs at p q with hp hq <;> simp_all
  · refine (convex_segment _ _).isPreconnected.union (joinVertex i0 h0) (right_mem_segment _ _ _)
      (left_mem_segment _ _ _) (convex_segment _ _).isPreconnected

/-- **Lemma 1 when the representation has dimension at most one** (intermediate value theorem):
if `V` has no nonzero fixed vectors and `dim V ≤ 1`, then for every `N ≥ 2` every continuous
equivariant map from the `N`-fold join of `G` to `V` has a zero. -/
theorem joinZeroProperty_of_finrank_le_one [FiniteDimensional ℝ V] (ρ : G →* (V ≃ₗᵢ[ℝ] V))
    (hV : Module.finrank ℝ V ≤ 1) (hfix : ∀ v, (∀ g, ρ g v = v) → v = 0) {N : ℕ} (hN : 2 ≤ N) :
    JoinZeroProperty G V ρ N := by
  intro f hf hequiv
  let i0 : Fin N := ⟨0, by omega⟩
  have hx0 : joinVertex i0 (1 : G) ∈ GroupJoin G N := joinVertex_mem _ _
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hV with h0 | h1
  · haveI : Subsingleton V := Module.finrank_zero_iff.mp h0
    exact ⟨_, hx0, Subsingleton.elim _ _⟩
  obtain ⟨b, hb, hspan⟩ := finrank_eq_one_iff'.mp h1
  obtain ⟨g, hg⟩ : ∃ g, ρ g b ≠ b := by
    by_contra hc
    push_neg at hc
    exact hb (hfix b hc)
  have hneg : ∀ v, ρ g v = -v := by
    obtain ⟨c, hc⟩ := hspan (ρ g b)
    have hnorm : |c| = 1 := by
      have := (ρ g).norm_map b
      rw [← hc, norm_smul, Real.norm_eq_abs] at this
      have hbpos : 0 < ‖b‖ := norm_pos_iff.mpr hb
      nlinarith
    have hc1 : c = -1 := by
      rcases abs_eq (zero_le_one' ℝ) |>.mp hnorm with h | h
      · exact absurd (by rw [← hc, h, one_smul]) hg
      · exact h
    intro v
    obtain ⟨t, rfl⟩ := hspan v
    rw [map_smul, ← hc, hc1]
    simp
  let φ : V → ℝ := fun v => ⟪b, v⟫_ℝ
  have hφ : ContinuousOn (fun x => φ (f x)) (GroupJoin G N) :=
    (continuous_const.inner continuous_id).comp_continuousOn hf
  have hx1 : joinAct g (joinVertex i0 (1 : G)) ∈ GroupJoin G N := joinAct_mem g hx0
  have hφ1 : φ (f (joinAct g (joinVertex i0 (1 : G)))) = -φ (f (joinVertex i0 (1 : G))) := by
    simp only [φ, hequiv g _ hx0, hneg, inner_neg_right]
  have hconn := isPreconnected_groupJoin (G := G) hN
  obtain ⟨y, hy, hφy⟩ : ∃ y ∈ GroupJoin G N, φ (f y) = (fun _ => (0 : ℝ)) y := by
    by_cases hs : φ (f (joinVertex i0 (1 : G))) ≤ 0
    · exact hconn.intermediate_value₂ hx0 hx1 hφ continuousOn_const hs (by rw [hφ1]; linarith)
    · exact hconn.intermediate_value₂ hx1 hx0 hφ continuousOn_const (by rw [hφ1]; linarith)
        (by linarith)
  refine ⟨y, hy, ?_⟩
  obtain ⟨t, ht⟩ := hspan (f y)
  simp only [φ, ← ht, real_inner_smul_right, real_inner_self_eq_norm_sq] at hφy
  have hbpos : 0 < ‖b‖ := norm_pos_iff.mpr hb
  have ht0 : t = 0 := by
    rcases mul_eq_zero.mp hφy with h | h
    · exact h
    · exfalso; have : 0 < ‖b‖ ^ 2 := by positivity
      linarith
  rw [← ht, ht0, zero_smul]

/-- **Lemma 1 when the non-fixed part has dimension at most one**, in the fixed-value form of
`JoinBorsukUlam`, for any finite group and `N = 2` join factors (or more). -/
theorem joinFixedProperty_of_finrank_compl_le_one [FiniteDimensional ℝ V]
    (ρ : G →* (V ≃ₗᵢ[ℝ] V)) (h : Module.finrank ℝ (fixedSubspace ρ)ᗮ ≤ 1) {N : ℕ}
    (hN : 2 ≤ N) : JoinFixedProperty G V ρ N :=
  joinFixedProperty_of_complRep ρ
    (joinZeroProperty_of_finrank_le_one (complRep ρ) h (complRep_fixed_eq_zero ρ) hN)

end Join

/-- **Reduction of Lemma 1 to its "zero" form.** `JoinBorsukUlam` is equivalent to: for every
finite `2`-group `G` and every orthogonal representation `V` of `G` without nonzero fixed vectors,
for `N` large every continuous equivariant map from the `N`-fold join of `G` to `V` has a zero. -/
theorem joinBorsukUlam_iff : JoinBorsukUlam ↔
    ∀ (G : Type) [Group G] [Fintype G], IsPGroup 2 G →
      ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
        (ρ : G →* (V ≃ₗᵢ[ℝ] V)), (∀ v, (∀ g, ρ g v = v) → v = 0) →
          ∃ N, JoinZeroProperty G V ρ N := by
  constructor
  · intro h G _ _ hG V _ _ _ ρ hfix
    let e : V ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) := (stdOrthonormalBasis ℝ V).repr
    let ρ' : G →* (EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) ≃ₗᵢ[ℝ]
        EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) :=
      { toFun := fun g => e.symm.trans ((ρ g).trans e)
        map_one' := by ext v; simp
        map_mul' := fun g g' => by ext v; simp [LinearIsometryEquiv.coe_mul] }
    obtain ⟨N, hN⟩ := h G hG _ ρ'
    refine ⟨N, fun f hf hequiv => ?_⟩
    obtain ⟨x, hx, hfx⟩ := hN (fun x => e (f x)) (e.continuous.comp_continuousOn hf)
      (fun g x hx => by simp [ρ', hequiv g x hx])
    refine ⟨x, hx, hfix _ fun g => ?_⟩
    have := hfx g
    simpa [ρ'] using this
  · intro h G _ _ hG ι _ ρ
    obtain ⟨N, hN⟩ := h G hG _ (complRep ρ) (complRep_fixed_eq_zero ρ)
    exact ⟨N, joinFixedProperty_of_complRep ρ hN⟩

end Dvoretzky
