module

public import RequestProject.Dvoretzky.Statement

/-!
# Reduction of `TwoGroupBorsukUlam` to the Borsuk–Ulam property of `2`-groups on joins

Lemma 1 of Dol'nikov–Karasev (Bartsch, Clapp–Marzantowicz) states: for a finite `p`-group `G`
and an orthogonal representation `V` of `G` there is `N` such that for every free
`(N - 1)`-connected `G`-space `X`, the image of every continuous equivariant map `X → V`
meets the fixed subspace `V^G`. The `N`-fold join `G * ⋯ * G` is a free `(N - 2)`-connected
`G`-space, so Lemma 1 contains the statement `JoinBorsukUlam` below (for `p = 2`).

We prove that `JoinBorsukUlam` implies `TwoGroupBorsukUlam`, by mapping the join equivariantly
into the space of linear isometric embeddings `ℝ^ι → ℝⁿ`
(`x ↦ ∑ᵢ ∑_h √(xᵢ(h)) • (blockᵢ ∘ h)`).
-/

@[expose] public section

open scoped BigOperators InnerProductSpace

noncomputable section

namespace Dvoretzky

/-- The `N`-fold join `G * ⋯ * G` of a finite group `G`, realised as a subset of
`Fin N → G → ℝ`: a point is a family of nonnegative weights `x i h` with total sum `1` such that
for each `i` at most one `h` carries a nonzero weight. -/
def GroupJoin (G : Type) [Fintype G] (N : ℕ) : Set (Fin N → G → ℝ) :=
  {x | (∀ i h, 0 ≤ x i h) ∧ (∀ i h h', x i h ≠ 0 → x i h' ≠ 0 → h = h') ∧
    ∑ i, ∑ h, x i h = 1}

/-- The (free) action of `G` on its join, by right translation of the labels. -/
def joinAct {G : Type} [Group G] {N : ℕ} (g : G) (x : Fin N → G → ℝ) : Fin N → G → ℝ :=
  fun i h => x i (h * g)

/-- **Lemma 1** of Dol'nikov–Karasev (Borsuk–Ulam property of finite `2`-groups, due to Bartsch
and Clapp–Marzantowicz, resting on Carlsson's solution of the Segal conjecture), for the
`N`-fold join `G * ⋯ * G` as the free highly connected `G`-space:
for every finite `2`-group `G` and every orthogonal representation `ρ` of `G` on `ℝ^ι` there is
`N` such that every continuous `G`-equivariant map from the `N`-fold join of `G` to `ℝ^ι` takes
some value fixed by `G`. -/
def JoinBorsukUlam : Prop :=
  ∀ (G : Type) [Group G] [Fintype G], IsPGroup 2 G →
    ∀ (ι : Type) [Fintype ι] (ρ : G →* (EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι)),
      ∃ N : ℕ, ∀ f : (Fin N → G → ℝ) → EuclideanSpace ℝ ι,
        ContinuousOn f (GroupJoin G N) →
        (∀ g, ∀ x ∈ GroupJoin G N, f (joinAct g x) = ρ g (f x)) →
        ∃ x ∈ GroupJoin G N, ∀ g, ρ g (f x) = f x

section Embedding

variable {ι : Type} [Fintype ι] {N n : ℕ} (e : Fin N × ι ↪ Fin n)

/-- The `i`-th block embedding `ℝ^ι → ℝⁿ`, `w ↦ ∑ₐ w a • e_{e(i,a)}`. -/
def blockMap (i : Fin N) : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  ∑ a, (EuclideanSpace.proj a : EuclideanSpace ℝ ι →L[ℝ] ℝ).toLinearMap.smulRight
    (EuclideanSpace.single (e (i, a)) (1 : ℝ))

lemma blockMap_apply (i : Fin N) (w : EuclideanSpace ℝ ι) :
    blockMap e i w = ∑ a, w a • EuclideanSpace.single (e (i, a)) (1 : ℝ) := by
  simp [blockMap]

lemma inner_blockMap (i i' : Fin N) (w w' : EuclideanSpace ℝ ι) :
    ⟪blockMap e i w, blockMap e i' w'⟫_ℝ = if i = i' then ⟪w, w'⟫_ℝ else 0 := by
  classical
  rw [blockMap_apply, blockMap_apply, sum_inner]
  simp only [inner_sum, inner_smul_left, inner_smul_right, EuclideanSpace.inner_single_left,
    PiLp.single_apply, e.injective.eq_iff, Prod.mk.injEq]
  split_ifs with h
  · subst h
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [dotProduct, conj_trivial, star_trivial]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  · simp [h]

end Embedding

section JoinMap

variable {ι : Type} [Fintype ι] {Γ : Type} [Group Γ] [Fintype Γ]
  (σ : Γ →* (EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι)) {N n : ℕ} (e : Fin N × ι ↪ Fin n)

/-- The `i`-th component `v ↦ ∑_h √(x i h) • σ h v`. -/
def joinComp (x : Fin N → Γ → ℝ) (i : Fin N) :
    EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι :=
  ∑ h, Real.sqrt (x i h) • (σ h).toLinearEquiv.toLinearMap

lemma joinComp_apply (x : Fin N → Γ → ℝ) (i : Fin N) (v : EuclideanSpace ℝ ι) :
    joinComp σ x i v = ∑ h, Real.sqrt (x i h) • σ h v := by
  simp [joinComp]

/-- The linear map `ℝ^ι → ℝⁿ` attached to a point of the join. -/
def joinMap (x : Fin N → Γ → ℝ) : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  ∑ i, blockMap e i ∘ₗ joinComp σ x i

lemma joinMap_apply (x : Fin N → Γ → ℝ) (v : EuclideanSpace ℝ ι) :
    joinMap σ e x v = ∑ i, ∑ h, Real.sqrt (x i h) • blockMap e i (σ h v) := by
  simp [joinMap, joinComp_apply, map_sum, map_smul]

lemma inner_joinComp {x : Fin N → Γ → ℝ} (hx : x ∈ GroupJoin Γ N) (i : Fin N)
    (v w : EuclideanSpace ℝ ι) :
    ⟪joinComp σ x i v, joinComp σ x i w⟫_ℝ = (∑ h, x i h) * ⟪v, w⟫_ℝ := by
  obtain ⟨hpos, hsupp, -⟩ := hx
  rw [joinComp_apply, joinComp_apply, sum_inner, Finset.sum_mul]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [inner_sum, Finset.sum_eq_single h]
  · rw [inner_smul_left, inner_smul_right, LinearIsometryEquiv.inner_map_map]
    simp only [conj_trivial]
    rw [← mul_assoc, Real.mul_self_sqrt (hpos i h)]
  · intro h' _ hh'
    by_cases h1 : x i h = 0
    · simp [h1]
    by_cases h2 : x i h' = 0
    · simp [h2]
    exact absurd (hsupp i h h' h1 h2) (Ne.symm hh')
  · simp

lemma inner_joinMap {x : Fin N → Γ → ℝ} (hx : x ∈ GroupJoin Γ N) (v w : EuclideanSpace ℝ ι) :
    ⟪joinMap σ e x v, joinMap σ e x w⟫_ℝ = ⟪v, w⟫_ℝ := by
  have hsum := hx.2.2
  simp only [joinMap, LinearMap.coe_sum, Finset.sum_apply, LinearMap.coe_comp,
    Function.comp_apply, sum_inner, inner_sum, inner_blockMap]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [inner_joinComp σ hx, ← Finset.sum_mul, hsum, one_mul]

lemma joinMap_joinAct (g : Γ) (x : Fin N → Γ → ℝ) (v : EuclideanSpace ℝ ι) :
    joinMap σ e (joinAct g x) v = joinMap σ e x (σ g⁻¹ v) := by
  rw [joinMap_apply, joinMap_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [joinAct]
  refine Fintype.sum_equiv (Equiv.mulRight g) _ _ fun h => ?_
  simp [map_mul, LinearIsometryEquiv.coe_mul]

lemma continuous_joinMap_apply (v : EuclideanSpace ℝ ι) :
    Continuous fun x : Fin N → Γ → ℝ => joinMap σ e x v := by
  simp only [joinMap_apply]
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun h _ => ?_
  exact ((continuous_apply h).comp (continuous_apply i)).sqrt.smul continuous_const

end JoinMap

/-- The permutation representation of `Γ` on `ℝ^(Γ × P)`: `(ρ g u) (h, p) = u (g⁻¹ h, p)`. -/
def permRep (Γ : Type) [Group Γ] [Fintype Γ] (P : Type) [Fintype P] :
    Γ →* (EuclideanSpace ℝ (Γ × P) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Γ × P)) where
  toFun g := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ ((Equiv.mulLeft g).prodCongr (Equiv.refl P))
  map_one' := by
    ext u ⟨h, p⟩
    simp [LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']
    rfl
  map_mul' g g' := by
    ext u ⟨h, p⟩
    simp [LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft', mul_assoc,
      Equiv.Perm.mul_def]

lemma permRep_apply (Γ : Type) [Group Γ] [Fintype Γ] (P : Type) [Fintype P] (g : Γ)
    (u : EuclideanSpace ℝ (Γ × P)) (h : Γ) (p : P) :
    permRep Γ P g u (h, p) = u (g⁻¹ * h, p) := by
  simp [permRep, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']

/-- `JoinBorsukUlam` (Lemma 1 for joins) implies the form `TwoGroupBorsukUlam` used in the
proof of Theorem 1. -/
theorem twoGroupBorsukUlam_of_join (h : JoinBorsukUlam) : TwoGroupBorsukUlam := by
  classical
  intro ι _ G hGfin hG2 P
  letI : Fintype G := Fintype.ofFinite G
  obtain ⟨N, hN⟩ := h G hG2 (G × P) (permRep G P)
  refine ⟨N * Fintype.card ι, fun n hn φ hφ => ?_⟩
  have hcard : Fintype.card (Fin N × ι) ≤ Fintype.card (Fin n) := by
    simpa using hn
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  let σ : G →* (EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) := G.subtype
  let f : (Fin N → G → ℝ) → EuclideanSpace ℝ (G × P) :=
    fun x => WithLp.toLp 2 (fun hp : G × P => φ (joinMap σ e x (σ hp.1 (hp.2 : EuclideanSpace ℝ ι))))
  have hfc : Continuous f := by
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun hp => ?_)
    exact hφ.comp (continuous_joinMap_apply σ e _)
  have hfeq : ∀ g, ∀ x ∈ GroupJoin G N, f (joinAct g x) = permRep G P g (f x) := by
    intro g x _
    ext ⟨h, p⟩
    rw [permRep_apply]
    simp only [f]
    rw [joinMap_joinAct]
    congr 2
  obtain ⟨x, hx, hfix⟩ := hN f hfc.continuousOn hfeq
  refine ⟨(joinMap σ e x).isometryOfInner (inner_joinMap σ e hx), fun g hg p hp => ?_⟩
  have h1 := congrArg (fun u : EuclideanSpace ℝ (G × P) => u (1, ⟨p, hp⟩)) (hfix ⟨g, hg⟩⁻¹)
  simp only [permRep_apply, inv_inv, mul_one] at h1
  simp only [f] at h1
  simpa [σ, LinearMap.coe_isometryOfInner] using h1

end Dvoretzky
