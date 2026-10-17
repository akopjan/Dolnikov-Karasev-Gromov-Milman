module

public import RequestProject.Dvoretzky.PolyFun
public import RequestProject.Dvoretzky.ConvexCompact

/-!
# The averaging lemma (Lemma 2 of Dol'nikov–Karasev)

For a finite family of even-degree homogeneous polynomial functions on `ℝ^k` there are finitely
many similarity transforms `σ_i` (not all zero) such that every `∑ i, φ_j (σ_i x)` is
proportional to `‖x‖ ^ deg φ_j`.

The proof averages over the orthogonal group (with its Haar measure), and then uses
Carathéodory's theorem to replace the average by a finite convex combination.
-/

@[expose] public section

open scoped BigOperators
open MeasureTheory

noncomputable section

set_option synthInstance.maxHeartbeats 200000

namespace Dvoretzky

variable {k : ℕ}

instance instContinuousStarEnd (k : ℕ) :
    ContinuousStar (EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)) :=
  ⟨(ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin k))
    (F := EuclideanSpace ℝ (Fin k))).continuous⟩

/-- The orthogonal group of `ℝ^k`, realised as the unitary elements of `End(ℝ^k)`. -/
abbrev OG (k : ℕ) := unitary (EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k))

instance : CompactSpace (OG k) := by
  have : IsCompact (OG k : Set (EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k))) := by
    refine Metric.isCompact_of_isClosed_isBounded isClosed_unitary ?_
    refine (Metric.isBounded_closedBall (x := 0) (r := 1)).subset ?_
    intro u hu
    rw [Metric.mem_closedBall, dist_zero_right]
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    rw [Unitary.norm_map ⟨u, hu⟩ x, one_mul]
  exact isCompact_iff_compactSpace.mp this

instance : MeasurableSpace (OG k) := borel _
instance : BorelSpace (OG k) := ⟨rfl⟩

/-- The normalized Haar measure on the orthogonal group. -/
def haarOG (k : ℕ) : Measure (OG k) := Measure.haarMeasure ⊤

instance : IsProbabilityMeasure (haarOG k) := by
  constructor
  have := Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (OG k)))
  rw [TopologicalSpace.PositiveCompacts.coe_top] at this
  exact this

instance : (haarOG k).IsMulLeftInvariant := by
  unfold haarOG; infer_instance

lemma OG.norm_apply (u : OG k) (z : EuclideanSpace ℝ (Fin k)) : ‖u.1 z‖ = ‖z‖ :=
  Unitary.norm_map u z

/-- The orthogonal group acts transitively on spheres. -/
lemma OG.exists_apply_eq {v w : EuclideanSpace ℝ (Fin k)} (h : ‖v‖ = ‖w‖) :
    ∃ u : OG k, u.1 v = w := by
  refine ⟨Unitary.linearIsometryEquiv.symm (Submodule.reflection (ℝ ∙ (v - w))ᗮ), ?_⟩
  have := Unitary.coe_linearIsometryEquiv_apply
    (Unitary.linearIsometryEquiv.symm (Submodule.reflection (ℝ ∙ (v - w))ᗮ) : OG k)
  rw [MulEquiv.apply_symm_apply] at this
  rw [← this]
  exact Submodule.reflection_sub h

/-- The Haar average of `φ (u⁻¹ z)`. -/
def haarAvg (φ : EuclideanSpace ℝ (Fin k) → ℝ) (z : EuclideanSpace ℝ (Fin k)) : ℝ :=
  ∫ u, φ ((u⁻¹ : OG k).1 z) ∂(haarOG k)

lemma haarAvg_apply_unitary (φ : EuclideanSpace ℝ (Fin k) → ℝ) (g : OG k)
    (z : EuclideanSpace ℝ (Fin k)) : haarAvg φ (g.1 z) = haarAvg φ z := by
  unfold haarAvg
  rw [← integral_mul_left_eq_self (μ := haarOG k)
    (fun u : OG k => φ ((u⁻¹ : OG k).1 (g.1 z))) g]
  congr 1
  funext u
  congr 1
  rw [mul_inv_rev]
  show (u⁻¹ : OG k).1 (((g⁻¹ * g : OG k)).1 z) = (u⁻¹ : OG k).1 z
  rw [inv_mul_cancel]
  rfl

lemma haarAvg_radial (hk : 0 < k) {e : ℕ} {φ : EuclideanSpace ℝ (Fin k) → ℝ}
    (hhom : IsHomogFun e φ) : IsRadial e (haarAvg φ) := by
  set e0 : EuclideanSpace ℝ (Fin k) := EuclideanSpace.single ⟨0, hk⟩ 1
  have he0 : ‖e0‖ = 1 := by simp [e0]
  refine ⟨haarAvg φ e0, fun z => ?_⟩
  have hz : ‖‖z‖ • e0‖ = ‖z‖ := by rw [norm_smul, he0, mul_one, norm_norm]
  obtain ⟨g, hg⟩ := OG.exists_apply_eq hz
  calc haarAvg φ z = haarAvg φ (g.1 (‖z‖ • e0)) := by rw [hg]
    _ = _ := by
      rw [haarAvg_apply_unitary]
      unfold haarAvg
      simp only [map_smul, hhom _ _]
      rw [integral_const_mul, mul_comm]

/-- Measurability/integrability facts for the averaging. -/
lemma integrable_of_continuous {V : Type*} [NormedAddCommGroup V] {f : OG k → V}
    (hf : Continuous f) : Integrable f (haarOG k) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

lemma continuous_inv_apply (z : EuclideanSpace ℝ (Fin k)) :
    Continuous fun u : OG k => (u⁻¹ : OG k).1 z := by
  have h1 : Continuous fun u : OG k => (u⁻¹ : OG k).1 :=
    continuous_subtype_val.comp continuous_inv
  exact (ContinuousLinearMap.apply ℝ _ z).continuous.comp h1

/-- **Lemma 2** (single degree). -/
theorem averaging_single (hk : 0 < k) {J : Type} [Fintype J] (e : ℕ) (he : Even e)
    (φ : J → EuclideanSpace ℝ (Fin k) → ℝ) (hpoly : ∀ j, IsPolyFun e (φ j))
    (hhom : ∀ j, IsHomogFun e (φ j)) :
    ∃ (I : Type) (_ : Fintype I) (σ : I → (EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)))
      (s : I → ℝ), (∀ i, IsSim (σ i) (s i)) ∧ (∃ i, 0 < s i) ∧
        ∀ j, IsRadial e (fun z => ∑ i, φ j (σ i z)) := by
  classical
  rcases Nat.eq_zero_or_pos e with rfl | he0
  · refine ⟨Unit, inferInstance, fun _ => ContinuousLinearMap.id ℝ _, fun _ => 1,
      fun _ => ⟨zero_le_one, fun w => by simp⟩, ⟨(), one_pos⟩, fun j => ⟨φ j 0, fun z => ?_⟩⟩
    simp [(hhom j).eq_const z]
  obtain ⟨r, hr⟩ := he
  -- the finite grid of test points
  let Z := {z // z ∈ grid (Fin k) e}
  let F : OG k → (J × Z → ℝ) := fun u p => φ p.1 ((u⁻¹ : OG k).1 p.2.1)
  have hFc : Continuous F := continuous_pi fun p =>
    (hpoly p.1).continuous.comp (continuous_inv_apply _)
  set x : J × Z → ℝ := ∫ u, F u ∂(haarOG k) with hx_def
  have hx_mem : x ∈ convexHull ℝ (Set.range F) := by
    refine Convex.integral_mem (convex_convexHull ℝ _)
      (isCompact_convexHull_of_isCompact (isCompact_range hFc)).isClosed
      (Filter.Eventually.of_forall fun u => subset_convexHull ℝ _ ⟨u, rfl⟩)
      (integrable_of_continuous hFc)
  have hx_apply : ∀ p : J × Z, x p = haarAvg (φ p.1) p.2.1 := by
    intro p
    rw [hx_def]
    have := ContinuousLinearMap.integral_comp_comm
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : J × Z => ℝ) p)
      (integrable_of_continuous hFc) (μ := haarOG k)
    simp only [ContinuousLinearMap.proj_apply] at this
    rw [← this]
    rfl
  obtain ⟨ι, _, zz, w, hzz, -, hw0, hw1, hxw⟩ := eq_pos_convex_span_of_mem_convexHull hx_mem
  choose u hu using fun i => hzz ⟨i, rfl⟩
  refine ⟨ι, inferInstance, fun i => (w i ^ ((e : ℝ)⁻¹)) • ((u i)⁻¹ : OG k).1,
    fun i => w i ^ ((e : ℝ)⁻¹), fun i => ⟨Real.rpow_nonneg (hw0 i).le _, fun v => ?_⟩, ?_, ?_⟩
  · rw [ContinuousLinearMap.smul_apply, norm_smul, OG.norm_apply, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (hw0 i).le _)]
  · have : Nonempty ι := by
      by_contra h
      rw [not_nonempty_iff] at h
      simp at hw1
    obtain ⟨i⟩ := this
    exact ⟨i, Real.rpow_pos_of_pos (hw0 i) _⟩
  · intro j
    obtain ⟨c, hc⟩ := haarAvg_radial hk (hhom j)
    refine ⟨c, fun z => ?_⟩
    -- both sides are polynomial functions of degree `≤ e` agreeing on the grid
    have hsum : ∀ z, ∑ i, φ j (((w i ^ ((e : ℝ)⁻¹)) • ((u i)⁻¹ : OG k).1) z) =
        ∑ i, w i * φ j (((u i)⁻¹ : OG k).1 z) := by
      intro z
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ContinuousLinearMap.smul_apply, hhom j, Real.rpow_inv_natCast_pow (hw0 i).le he0.ne']
    have hpolyL : IsPolyFun e (fun z => ∑ i, w i * φ j (((u i)⁻¹ : OG k).1 z)) :=
      isPolyFun_sum _ _ fun i _ => ((hpoly j).comp_clm _).const_mul _
    have hpolyR : IsPolyFun e (fun z : EuclideanSpace ℝ (Fin k) => c * ‖z‖ ^ e) := by
      have := (isPolyFun_norm_pow (ι := Fin k) r).const_mul c
      rw [show e = 2 * r by omega]
      exact this
    have hgrid := (hpolyL.sub hpolyR).eq_zero_of_grid (fun z hz => by
      have h1 := congrFun hxw (j, ⟨z, hz⟩)
      rw [hx_apply, hc] at h1
      rw [← h1]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [sub_eq_zero]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hu i])
    show ∑ i, φ j (((w i ^ ((e : ℝ)⁻¹)) • ((u i)⁻¹ : OG k).1) z) = c * ‖z‖ ^ e
    rw [hsum, ← sub_eq_zero]
    exact hgrid z

end Dvoretzky

namespace Dvoretzky

variable {k : ℕ}

/-- **Lemma 2** (Dol'nikov–Karasev), for a finite family of even-degree homogeneous polynomial
functions of possibly different degrees. -/
theorem averaging_lemma (hk : 0 < k) {J : Type} [Fintype J] (e : J → ℕ) (he : ∀ j, Even (e j))
    (φ : J → EuclideanSpace ℝ (Fin k) → ℝ) (hpoly : ∀ j, IsPolyFun (e j) (φ j))
    (hhom : ∀ j, IsHomogFun (e j) (φ j)) :
    ∃ (I : Type) (_ : Fintype I) (σ : I → (EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)))
      (s : I → ℝ), (∀ i, IsSim (σ i) (s i)) ∧ (∃ i, 0 < s i) ∧
        ∀ j, IsRadial (e j) (fun z => ∑ i, φ j (σ i z)) := by
  classical
  suffices H : ∀ D : Finset ℕ, ∀ (J : Type) [Fintype J] (e : J → ℕ), (∀ j, Even (e j)) →
      ∀ φ : J → EuclideanSpace ℝ (Fin k) → ℝ, (∀ j, IsPolyFun (e j) (φ j)) →
      (∀ j, IsHomogFun (e j) (φ j)) → (∀ j, e j ∈ D) →
      ∃ (I : Type) (_ : Fintype I)
        (σ : I → (EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)))
        (s : I → ℝ), (∀ i, IsSim (σ i) (s i)) ∧ (∃ i, 0 < s i) ∧
          ∀ j, IsRadial (e j) (fun z => ∑ i, φ j (σ i z)) from
    H (Finset.univ.image e) J e he φ hpoly hhom (fun j => Finset.mem_image_of_mem e (by simp))
  intro D
  induction D using Finset.induction_on with
  | empty =>
    intro J _ e _ φ _ _ hD
    exact ⟨Unit, inferInstance, fun _ => ContinuousLinearMap.id ℝ _, fun _ => 1,
      fun _ => ⟨zero_le_one, fun w => by simp⟩, ⟨(), one_pos⟩, fun j => absurd (hD j) (by simp)⟩
  | insert d D hdD ih =>
    intro J _ e he φ hpoly hhom hD
    -- Step 1: average the functions of degree `d`.
    obtain ⟨I1, _, σ1, s1, hσ1, ⟨i1, hi1⟩, h1⟩ : ∃ (I : Type) (_ : Fintype I)
        (σ : I → (EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)))
        (s : I → ℝ), (∀ i, IsSim (σ i) (s i)) ∧ (∃ i, 0 < s i) ∧
          ∀ j : {j // e j = d}, IsRadial d (fun z => ∑ i, φ j.1 (σ i z)) := by
      by_cases hd : Even d
      · exact averaging_single hk d hd (fun j : {j // e j = d} => φ j.1)
          (fun j => by have := hpoly j.1; rwa [j.2] at this)
          (fun j => by have := hhom j.1; rwa [j.2] at this)
      · exact ⟨Unit, inferInstance, fun _ => ContinuousLinearMap.id ℝ _, fun _ => 1,
          fun _ => ⟨zero_le_one, fun w => by simp⟩, ⟨(), one_pos⟩,
          fun j => absurd (j.2 ▸ he j.1) hd⟩
    -- Step 2: average the remaining functions, precomposed with the first family.
    obtain ⟨I2, _, σ2, s2, hσ2, ⟨i2, hi2⟩, h2⟩ := ih ({j // e j ≠ d} × I1)
      (fun p => e p.1.1) (fun p => he p.1.1) (fun p z => φ p.1.1 (σ1 p.2 z))
      (fun p => (hpoly p.1.1).comp_clm _) (fun p => (hhom p.1.1).comp_clm _)
      (fun p => by
        have := hD p.1.1
        rw [Finset.mem_insert] at this
        exact this.resolve_left p.1.2)
    refine ⟨I1 × I2, inferInstance, fun p => (σ1 p.1).comp (σ2 p.2), fun p => s1 p.1 * s2 p.2,
      fun p => ⟨mul_nonneg (hσ1 p.1).1 (hσ2 p.2).1, fun w => ?_⟩, ⟨(i1, i2), mul_pos hi1 hi2⟩,
      fun j => ?_⟩
    · rw [ContinuousLinearMap.comp_apply, (hσ1 p.1).2, (hσ2 p.2).2, mul_assoc]
    · by_cases hj : e j = d
      · obtain ⟨c, hc⟩ := h1 ⟨j, hj⟩
        have hc' : ∀ z, ∑ i, φ j (σ1 i z) = c * ‖z‖ ^ d := hc
        refine ⟨∑ i, c * s2 i ^ e j, fun z => ?_⟩
        simp only [ContinuousLinearMap.comp_apply]
        rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        dsimp only
        rw [hc' ((σ2 i) z), (hσ2 i).2, hj, mul_pow, mul_assoc]
      · choose c hc using fun i => h2 (⟨j, hj⟩, i)
        refine ⟨∑ i, c i, fun z => ?_⟩
        simp only [ContinuousLinearMap.comp_apply]
        rw [Fintype.sum_prod_type, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => hc i z

/-- Version of the averaging lemma where the similarities are indexed by an elementary abelian
`2`-group `(ZMod 2)^a` (pad with zero maps). -/
theorem averaging_pow2 (hk : 0 < k) {J : Type} [Fintype J] (e : J → ℕ) (he : ∀ j, Even (e j))
    (φ : J → EuclideanSpace ℝ (Fin k) → ℝ) (hpoly : ∀ j, IsPolyFun (e j) (φ j))
    (hhom : ∀ j, IsHomogFun (e j) (φ j)) :
    ∃ (a : ℕ) (σ : (Fin a → ZMod 2) → (EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)))
      (s : (Fin a → ZMod 2) → ℝ), (∀ y, IsSim (σ y) (s y)) ∧ (∃ y, 0 < s y) ∧
        ∀ j, IsRadial (e j) (fun z => ∑ y, φ j (σ y z)) := by
  classical
  obtain ⟨I, _, σ, s, hσ, ⟨i0, hi0⟩, h⟩ := averaging_lemma hk e he φ hpoly hhom
  let eqv := Fintype.equivFin I
  let emb : I → (Fin (Fintype.card I) → ZMod 2) := fun i => Pi.single (eqv i) 1
  have hemb : Function.Injective emb := by
    intro i i' hii'
    by_contra hne
    have hne' : eqv i ≠ eqv i' := fun h => hne (eqv.injective h)
    have := congrFun hii' (eqv i)
    simp [emb, hne'] at this
  let embE : I ↪ (Fin (Fintype.card I) → ZMod 2) := ⟨emb, hemb⟩
  refine ⟨Fintype.card I, Function.extend emb σ 0, Function.extend emb s 0, fun y => ?_,
    ⟨emb i0, by rw [hemb.extend_apply]; exact hi0⟩, fun j => ?_⟩
  · by_cases hy : ∃ i, emb i = y
    · obtain ⟨i, rfl⟩ := hy
      rw [hemb.extend_apply, hemb.extend_apply]
      exact hσ i
    · rw [Function.extend_apply' _ _ _ hy, Function.extend_apply' _ _ _ hy]
      exact ⟨le_rfl, fun w => by simp⟩
  · rcases Nat.eq_zero_or_pos (e j) with h0 | hpos
    · refine ⟨∑ _y : Fin (Fintype.card I) → ZMod 2, φ j 0, fun z => ?_⟩
      have hc := (hhom j)
      rw [h0] at hc
      simp [hc.eq_const, h0]
    · obtain ⟨c, hc⟩ := h j
      refine ⟨c, fun z => ?_⟩
      show ∑ y, φ j (Function.extend emb σ 0 y z) = c * ‖z‖ ^ e j
      rw [← Finset.sum_add_sum_compl (Finset.univ.map embE), Finset.sum_map]
      have hrest : ∑ y ∈ (Finset.univ.map embE)ᶜ, φ j (Function.extend emb σ 0 y z) = 0 := by
        refine Finset.sum_eq_zero fun y hy => ?_
        have hy' : ¬∃ i, emb i = y := by
          rintro ⟨i, rfl⟩
          simp [embE] at hy
        rw [Function.extend_apply' _ _ _ hy']
        simpa using (hhom j).map_zero hpos
      rw [hrest, add_zero, ← hc z]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [embE, Function.Embedding.coeFn_mk, hemb.extend_apply]

end Dvoretzky
