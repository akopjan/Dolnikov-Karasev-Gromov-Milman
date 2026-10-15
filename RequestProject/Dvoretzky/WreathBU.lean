module

public import RequestProject.Dvoretzky.ElemAb.Emptiness
public import RequestProject.Dvoretzky.Theorem1

/-!
# Invariance under signed iterated wreath products from Lemma 1 for elementary abelian groups

The proof of Theorem 1 needs, for the `2`-group `H ≤ Perm X` of the combinatorial construction
(an iterated wreath product `K₁ ≀ ⋯ ≀ K_δ` of elementary abelian `2`-groups), an isometric
embedding `L : ℝ^X → ℝⁿ` such that `φ ∘ L` is invariant under all signed permutations with
underlying permutation in `H`.

The paper obtains this from Lemma 1 for the (non-abelian) group `(ℤ/2)^X ⋊ H`. Here we obtain it
from Lemma 1 for **elementary abelian** `2`-groups only (proved in `ElemAb/`), applied once per
level of the wreath product. The point is that the embeddings produced by the join construction
`v ↦ (i, c) ↦ ∑_h √(x i h) v (h • c)` are *block-structured*: if `ψ` on `ℝ^(Fin M × ι)` is
invariant under independent copies (one per block `i`) of a group `K` normalised by the
translations used, then `ψ ∘ L_x` is `K`-invariant. Invariance under the previous levels is thus
inherited, and only the new top-level translations require a Borsuk–Ulam type argument.

Main results:

* `Achievable e X H`: for every number `Z` of blocks one can make every polynomial function of
  degree `≤ e` invariant, after a suitable isometric embedding of `ℝ^(Z × X)`, under all sign
  changes and all blockwise permutations `(z, x) ↦ (z, g z x)` with `g z ∈ H`;
* `achievable_base`, `achievable_step`: this holds for the trivial group on a point and passes to
  the wreath product with an elementary abelian `2`-group;
* `exists_good_stage_achievable`: the output of the combinatorial construction satisfies it.

See `README.md` and `COMPARISON_WITH_PAPER.md` for extended discussion of the comparison with
the paper's proof.
-/

@[expose] public section

open scoped BigOperators InnerProductSpace

noncomputable section

namespace Dvoretzky

namespace WreathBU

open Equiv

/-- The blockwise permutation `(z, x) ↦ (z, g z x)` of `Z × X`. -/
def blockPerm {Z X : Type} (g : Z → Perm X) : Perm (Z × X) :=
  Equiv.prodShear (Equiv.refl Z) g

@[simp] lemma blockPerm_apply {Z X : Type} (g : Z → Perm X) (p : Z × X) :
    blockPerm g p = (p.1, g p.1 p.2) := rfl

/-- The invariance property obtained by iterating Lemma 1 for elementary abelian groups. -/
def Achievable (e : ℕ) (X : Type) [Fintype X] (H : Subgroup (Perm X)) : Prop :=
  ∀ (Z : Type) [Fintype Z] [DecidableEq Z], ∃ N : ℕ, ∀ n ≥ N,
    ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ, IsPolyFun e φ →
      ∃ L : EuclideanSpace ℝ (Z × X) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
        (∀ ε : Z × X → ℤˣ, ∀ y, φ (L (signedPerm ε 1 y)) = φ (L y)) ∧
        (∀ g : Z → Perm X, (∀ z, g z ∈ H) → ∀ y, φ (L (signedPerm 1 (blockPerm g) y)) = φ (L y))

/-! ### Selecting the occupied label in each block of a join point -/

section Sel

variable {Γ : Type} [Fintype Γ] [One Γ] {M : ℕ}

open Classical in
/-- The label carrying the weight of block `i` (or `1` if the block is empty). -/
def sel (x : Fin M → Γ → ℝ) (i : Fin M) : Γ :=
  if h : ∃ h, x i h ≠ 0 then h.choose else 1

lemma eq_zero_of_ne_sel {x : Fin M → Γ → ℝ} (hx : x ∈ GroupJoin Γ M) {i : Fin M} {h : Γ}
    (hh : h ≠ sel x i) : x i h = 0 := by
  classical
  by_contra hne
  have hex : ∃ h, x i h ≠ 0 := ⟨h, hne⟩
  have hsel : sel x i = hex.choose := by simp [sel, hex]
  exact hh (hsel ▸ hx.2.1 i h hex.choose hne hex.choose_spec)

lemma sum_eq_sel {x : Fin M → Γ → ℝ} (hx : x ∈ GroupJoin Γ M) (i : Fin M) (f : Γ → ℝ) :
    ∑ h, Real.sqrt (x i h) * f h = Real.sqrt (x i (sel x i)) * f (sel x i) := by
  rw [Finset.sum_eq_single (sel x i)]
  · intro h _ hh
    rw [eq_zero_of_ne_sel hx hh]
    simp
  · simp

lemma sum_weights_eq_sel {x : Fin M → Γ → ℝ} (hx : x ∈ GroupJoin Γ M) (i : Fin M) :
    ∑ h, x i h = x i (sel x i) := by
  rw [Finset.sum_eq_single (sel x i)]
  · intro h _ hh
    exact eq_zero_of_ne_sel hx hh
  · simp

end Sel

/-! ### The block-structured join embedding -/

section BJoin

variable {ι Γ : Type} [Fintype ι] [Fintype Γ] {M : ℕ} (tr : Γ → Perm ι)

/-- The linear map `ℝ^ι → ℝ^(Fin M × ι)`, `v ↦ (i, c) ↦ ∑_h √(x i h) v (tr h c)`. -/
def bjoin (x : Fin M → Γ → ℝ) : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ (Fin M × ι) where
  toFun v := WithLp.toLp 2 (fun ic => ∑ h, Real.sqrt (x ic.1 h) * v (tr h ic.2))
  map_add' v w := by
    ext ic
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c v := by
    ext ic
    simp [Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => by ring

lemma bjoin_apply (x : Fin M → Γ → ℝ) (v : EuclideanSpace ℝ ι) (ic : Fin M × ι) :
    bjoin tr x v ic = ∑ h, Real.sqrt (x ic.1 h) * v (tr h ic.2) := rfl

lemma bjoin_apply_sel [One Γ] {x : Fin M → Γ → ℝ} (hx : x ∈ GroupJoin Γ M) (v : EuclideanSpace ℝ ι)
    (i : Fin M) (c : ι) :
    bjoin tr x v (i, c) = Real.sqrt (x i (sel x i)) * v (tr (sel x i) c) := by
  rw [bjoin_apply]
  exact sum_eq_sel hx i (fun h => v (tr h c))

lemma inner_bjoin [One Γ] {x : Fin M → Γ → ℝ} (hx : x ∈ GroupJoin Γ M) (v w : EuclideanSpace ℝ ι) :
    ⟪bjoin tr x v, bjoin tr x w⟫_ℝ = ⟪v, w⟫_ℝ := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial]
  rw [Fintype.sum_prod_type]
  have h1 : ∀ i : Fin M, ∑ c : ι, (bjoin tr x w) (i, c) * (bjoin tr x v) (i, c) =
      x i (sel x i) * ∑ c : ι, w c * v c := by
    intro i
    simp only [bjoin_apply_sel tr hx]
    rw [Finset.mul_sum]
    rw [← Equiv.sum_comp (tr (sel x i)) (fun c => x i (sel x i) * (w c * v c))]
    refine Finset.sum_congr rfl fun c _ => ?_
    have := Real.mul_self_sqrt (hx.1 i (sel x i))
    calc Real.sqrt (x i (sel x i)) * w (tr (sel x i) c) *
          (Real.sqrt (x i (sel x i)) * v (tr (sel x i) c))
        = (Real.sqrt (x i (sel x i)) * Real.sqrt (x i (sel x i))) *
          (w (tr (sel x i) c) * v (tr (sel x i) c)) := by ring
      _ = _ := by rw [this]
  rw [Finset.sum_congr rfl fun i _ => h1 i, ← Finset.sum_mul]
  rw [Finset.sum_congr rfl fun i _ => (sum_weights_eq_sel hx i).symm, hx.2.2, one_mul]

lemma bjoin_joinAct [Group Γ] (htr : ∀ a b : Γ, tr (a * b) = tr b * tr a) (g : Γ)
    (x : Fin M → Γ → ℝ) (v : EuclideanSpace ℝ ι) :
    bjoin tr (joinAct g x) v = bjoin tr x (signedPerm 1 (tr g⁻¹) v) := by
  ext ic
  simp only [bjoin_apply, joinAct, signedPerm_apply, Pi.one_apply, Units.val_one,
    Int.cast_one, one_mul]
  refine Fintype.sum_equiv (Equiv.mulRight g) _ _ fun h => ?_
  simp only [Equiv.coe_mulRight]
  rw [← Perm.mul_apply, ← htr, mul_inv_cancel_right]

lemma continuous_bjoin_apply (v : EuclideanSpace ℝ ι) :
    Continuous fun x : Fin M → Γ → ℝ => bjoin tr x v := by
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun ic => ?_)
  refine continuous_finsetSum _ fun h _ => ?_
  exact (((continuous_apply h).comp (continuous_apply ic.1)).sqrt).mul continuous_const

end BJoin

/-! ### Reindexing -/

lemma piLpCongrLeft_apply' {α β : Type} [Fintype α] [Fintype β] (eqv : α ≃ β)
    (w : EuclideanSpace ℝ α) (j : β) :
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ eqv w j = w (eqv.symm j) := by
  simp [LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']

/-- A polynomial function of degree `≤ e` invariant under an isometry `A` on the grid is
invariant everywhere. -/
lemma invariant_of_grid {ι : Type} [Fintype ι] [DecidableEq ι] {e : ℕ}
    {q : EuclideanSpace ℝ ι → ℝ} (hq : IsPolyFun e q) (A : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (hA : ∀ p ∈ grid ι e, q (A p) = q p) : ∀ y, q (A y) = q y := by
  have h1 : IsPolyFun e (fun y => q (A y) - q y) :=
    (hq.comp_clm A.toContinuousLinearEquiv.toContinuousLinearMap).sub hq
  exact fun y => sub_eq_zero.1 (h1.eq_zero_of_grid (fun z hz => sub_eq_zero.2 (hA z hz)) y)

lemma signedPerm_one_one {X : Type} [Fintype X] (y : EuclideanSpace ℝ X) :
    signedPerm 1 1 y = y := by
  ext x
  simp

/-! ### The base case: sign changes on `ℝ^(Z × Unit)` -/

/-- The base of the induction: sign changes, from Lemma 1 for `(ℤ/2)^(Z × Unit)`. -/
theorem achievable_base (e : ℕ) : Achievable e Unit (⊥ : Subgroup (Perm Unit)) := by
  classical
  intro Z _ _
  let Γ := Z × Unit → ℤˣ
  have hΓ : ∀ g : Γ, g * g = 1 := fun g => funext fun c => Int.units_mul_self (g c)
  let σ : Γ →* (EuclideanSpace ℝ (Z × Unit) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Z × Unit)) :=
    { toFun := fun ε => signedPerm ε 1
      map_one' := signedPerm_one
      map_mul' := fun ε ε' => by
        rw [signedPerm_mul]
        ext y c
        simp only [signedPerm_apply, Perm.one_apply, Perm.mul_apply]
        rw [show (ε * ε') c = ε c * ε' c from rfl] }
  obtain ⟨N, hN⟩ := ElemAb.joinOrbitCollapse_of_mul_self_eq_one Γ hΓ (grid (Z × Unit) e)
  refine ⟨N * Fintype.card (Z × Unit), fun n hn φ hφ => ?_⟩
  have hcard : Fintype.card (Fin N × (Z × Unit)) ≤ Fintype.card (Fin n) := by
    simpa using hn
  obtain ⟨emb⟩ := Function.Embedding.nonempty_of_card_le hcard
  let F : (Fin N → Γ → ℝ) → (grid (Z × Unit) e → ℝ) :=
    fun x p => φ (joinMap σ emb x (p : EuclideanSpace ℝ (Z × Unit)))
  have hFc : Continuous F :=
    continuous_pi fun p => hφ.continuous.comp (continuous_joinMap_apply σ emb _)
  obtain ⟨x, hx, hfix⟩ := hN F hFc.continuousOn
  let L := (joinMap σ emb x).isometryOfInner (inner_joinMap σ emb hx)
  have hLpoly : IsPolyFun e (fun y => φ (L y)) := hφ.comp_clm L.toContinuousLinearMap
  refine ⟨L, fun ε => ?_, fun g _ y => ?_⟩
  · refine invariant_of_grid hLpoly (signedPerm ε 1) fun p hp => ?_
    have h1 := congrFun (hfix ε⁻¹) ⟨p, hp⟩
    simp only [F, joinMap_joinAct] at h1
    rw [inv_inv] at h1
    simpa [L, LinearMap.coe_isometryOfInner, σ] using h1
  · have hb : blockPerm g = 1 := by
      ext p
      rfl
    rw [hb, signedPerm_one_one]

/-! ### The induction step: wreath product with an elementary abelian group -/

section Step

variable {Z Y X : Type} [AddCommGroup Y]

/-- The translation `(z, (y, x)) ↦ (z, (y + κ z, x))`. -/
def transl (κ : Z → Y) : Perm (Z × (Y × X)) :=
  blockPerm fun z => wreathPerm (κ z) (fun _ => 1)

@[simp] lemma transl_apply (κ : Z → Y) (p : Z × (Y × X)) :
    transl κ p = (p.1, (p.2.1 + κ p.1, p.2.2)) := rfl

end Step

section Inner

variable {Z Y X : Type}

/-- The inner permutation `(z, (y, x)) ↦ (z, (y, G z y x))`. -/
def inner (G : Z → Y → Perm X) : Perm (Z × (Y × X)) :=
  blockPerm fun z => blockPerm (G z)

@[simp] lemma inner_apply (G : Z → Y → Perm X) (p : Z × (Y × X)) :
    inner G p = (p.1, (p.2.1, G p.1 p.2.1 p.2.2)) := rfl

/-- Regrouping the indices. -/
def reidx (M : ℕ) (Z Y X : Type) : Fin M × (Z × (Y × X)) ≃ (Fin M × (Z × Y)) × X where
  toFun p := ((p.1, p.2.1, p.2.2.1), p.2.2.2)
  invFun q := (q.1.1, q.1.2.1, q.1.2.2, q.2)
  left_inv _ := rfl
  right_inv _ := rfl

end Inner

/-- **The induction step.** If invariance under (blockwise copies of) the signed group of `H` is
achievable, then so is invariance under the signed group of the wreath product `H ≀ Y` with an
elementary abelian `2`-group `Y`. Only Lemma 1 for the elementary abelian group `Y^Z` is used;
invariance under the inner levels is inherited from the block structure of the join embedding. -/
theorem achievable_step {e : ℕ} {X : Type} [Fintype X] {H : Subgroup (Perm X)}
    {Y : Type} [AddCommGroup Y] [Fintype Y] (hY : ∀ κ : Y, κ + κ = 0)
    (hA : Achievable e X H) : Achievable e (Y × X) (wreath H) := by
  classical
  intro Z _ _
  let Γ := Multiplicative (Z → Y)
  let tr : Γ → Perm (Z × (Y × X)) := fun γ => transl (Multiplicative.toAdd γ)
  have htr : ∀ a b : Γ, tr (a * b) = tr b * tr a := by
    intro a b
    ext p
    · rfl
    · simp only [tr, transl_apply, Perm.mul_apply, add_assoc]
      rfl
    · rfl
  have hΓ : ∀ g : Γ, g * g = 1 := fun g => by
    apply Multiplicative.toAdd.injective
    funext z
    exact hY _
  obtain ⟨M, hM⟩ := ElemAb.joinOrbitCollapse_of_mul_self_eq_one Γ hΓ (grid (Z × (Y × X)) e)
  obtain ⟨N, hN⟩ := hA (Fin M × (Z × Y))
  refine ⟨N, fun n hn φ hφ => ?_⟩
  obtain ⟨L1, hL1s, hL1p⟩ := hN n hn φ hφ
  let R := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (reidx M Z Y X)
  let ψ : EuclideanSpace ℝ (Fin M × (Z × (Y × X))) → ℝ := fun w => φ (L1 (R w))
  have hψ : IsPolyFun e ψ :=
    hφ.comp_clm (L1.toContinuousLinearMap.comp R.toContinuousLinearEquiv.toContinuousLinearMap)
  let F : (Fin M → Γ → ℝ) → (grid (Z × (Y × X)) e → ℝ) :=
    fun x p => ψ (bjoin tr x (p : EuclideanSpace ℝ (Z × (Y × X))))
  have hFc : Continuous F :=
    continuous_pi fun p => hψ.continuous.comp (continuous_bjoin_apply tr _)
  obtain ⟨x, hx, hfix⟩ := hM F hFc.continuousOn
  let q : EuclideanSpace ℝ (Z × (Y × X)) → ℝ := fun v => ψ (bjoin tr x v)
  have hq : IsPolyFun e q := hψ.comp_clm (LinearMap.toContinuousLinearMap (bjoin tr x))
  -- invariance under the translations, from Lemma 1
  have hC : ∀ γ : Γ, ∀ v, q (signedPerm 1 (tr γ) v) = q v := by
    intro γ
    refine invariant_of_grid hq (signedPerm 1 (tr γ)) fun p hp => ?_
    have h1 := congrFun (hfix γ⁻¹) ⟨p, hp⟩
    simp only [F, bjoin_joinAct tr htr] at h1
    rwa [show γ⁻¹⁻¹ = γ from inv_inv γ] at h1
  -- inherited invariance under sign changes
  have hA' : ∀ ε : Z × (Y × X) → ℤˣ, ∀ v, q (signedPerm ε 1 v) = q v := by
    intro ε v
    have hR : R (bjoin tr x (signedPerm ε 1 v)) =
        signedPerm (fun j => ε (tr (sel x ((reidx M Z Y X).symm j).1)
          ((reidx M Z Y X).symm j).2)) 1 (R (bjoin tr x v)) := by
      ext j
      rcases j with ⟨⟨i, z, y0⟩, x0⟩
      simp only [R, piLpCongrLeft_apply', signedPerm_apply, Perm.one_apply]
      change bjoin tr x (signedPerm ε 1 v) (i, z, y0, x0) = _ * bjoin tr x v (i, z, y0, x0)
      rw [bjoin_apply_sel tr hx, bjoin_apply_sel tr hx, signedPerm_apply]
      simp only [Perm.one_apply]
      change _ = ((ε (tr (sel x i) (z, y0, x0)) : ℤ) : ℝ) * _
      ring
    change φ (L1 (R _)) = φ (L1 (R _))
    rw [hR, hL1s]
  -- inherited invariance under the inner permutations
  have hB' : ∀ G : Z → Y → Perm X, (∀ z y, G z y ∈ H) → ∀ v,
      q (signedPerm 1 (inner G) v) = q v := by
    intro G hG v
    let G' : Fin M × (Z × Y) → Perm X :=
      fun j => G j.2.1 (j.2.2 + Multiplicative.toAdd (sel x j.1) j.2.1)
    have hR : R (bjoin tr x (signedPerm 1 (inner G) v)) =
        signedPerm 1 (blockPerm G') (R (bjoin tr x v)) := by
      ext j
      rcases j with ⟨⟨i, z, y0⟩, x0⟩
      simp only [R, piLpCongrLeft_apply', signedPerm_apply, Pi.one_apply, Units.val_one,
        Int.cast_one, one_mul]
      change bjoin tr x (signedPerm 1 (inner G) v) (i, z, y0, x0) =
        bjoin tr x v (i, z, y0, G' (i, z, y0) x0)
      rw [bjoin_apply_sel tr hx, bjoin_apply_sel tr hx, signedPerm_apply]
      simp [tr, G']
    change φ (L1 (R _)) = φ (L1 (R _))
    rw [hR, hL1p G' fun j => hG _ _]
  refine ⟨L1.comp (R.toLinearIsometry.comp
    ((bjoin tr x).isometryOfInner (inner_bjoin tr hx))), fun ε y => ?_, fun g hg y => ?_⟩
  · exact hA' ε y
  · choose κ G hG heq using hg
    have hb : blockPerm g = transl κ * inner G := by
      ext p
      · rfl
      · simp [heq]
      · simp [heq]
    have hs : signedPerm 1 (blockPerm g) y = signedPerm 1 (inner G) (signedPerm 1 (tr (Multiplicative.ofAdd κ)) y) := by
      have hs' : signedPerm 1 (transl κ * inner G) =
          signedPerm 1 (inner G) * signedPerm 1 (tr (Multiplicative.ofAdd κ)) := by
        rw [signedPerm_mul]
        ext w c
        simp [tr]
      rw [hb, hs', LinearIsometryEquiv.coe_mul, Function.comp_apply]
    change q _ = q _
    rw [hs, hB' G hG, hC]

/-! ### Iterating along the combinatorial construction -/

/-- From `Achievable` to the form used in the proof of Theorem 1. -/
theorem Achievable.signedGroup_invariant {e : ℕ} {X : Type} [Fintype X] {H : Subgroup (Perm X)}
    (h : Achievable e X H) : ∃ N : ℕ, ∀ n ≥ N, ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ,
      IsPolyFun e φ → ∃ L : EuclideanSpace ℝ X →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
        ∀ g ∈ signedGroup H, ∀ y, φ (L (g y)) = φ (L y) := by
  classical
  obtain ⟨N, hN⟩ := h Unit
  refine ⟨N, fun n hn φ hφ => ?_⟩
  obtain ⟨L', hs, hp⟩ := hN n hn φ hφ
  let eqv : X ≃ Unit × X :=
    { toFun := fun x => ((), x), invFun := fun p => p.2, left_inv := fun _ => rfl,
      right_inv := fun _ => rfl }
  let U := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ eqv
  refine ⟨L'.comp U.toLinearIsometry, ?_⟩
  rintro _ ⟨ε, π, hπ, rfl⟩ y
  have hU : U (signedPerm ε π y) =
      signedPerm (fun p => ε p.2) 1 (signedPerm 1 (blockPerm fun _ => π) (U y)) := by
    ext ⟨u, x⟩
    simp [U, piLpCongrLeft_apply', eqv]
  change φ (L' (U _)) = φ (L' (U _))
  rw [hU, hs, hp _ fun _ => hπ]

/-- The combinatorial construction of `Stage.lean`, together with the achievability of the
invariance under its signed group. -/
lemma exists_stage_achievable {k : ℕ} (hk : 0 < k) (δ e : ℕ) :
    ∀ j, ∃ S : Stage k, S.GoodUpTo δ j ∧ S.NonDeg ∧ Achievable e S.X S.H := by
  intro j
  induction j with
  | zero => exact ⟨Stage.init hk, Stage.init_good hk δ, Stage.init_nonDeg hk, achievable_base e⟩
  | succ j ih =>
    obtain ⟨S, hS, hS', hA⟩ := ih
    obtain ⟨a, σ, s, hσ, ⟨y0, hy0⟩, havg⟩ := averaging_pow2 hk (J := Stage.Idx S δ)
      (fun β => 2 * ∑ x, (β.1 x : ℕ)) (fun β => even_two_mul _)
      (fun β => S.orb (fun x => (β.1 x : ℕ))) (fun β => S.orb_isPolyFun _)
      (fun β => S.orb_isHomogFun _)
    refine ⟨S.step a σ, Stage.step_good S δ j hS a σ s hσ havg,
      Stage.step_nonDeg S hS' a σ s hσ y0 hy0, ?_⟩
    exact achievable_step (Y := Fin a → ZMod 2)
      (fun κ => by funext i; exact CharTwo.add_self_eq_zero (κ i)) hA

end WreathBU

/-- **Theorem 1 of Dol'nikov–Karasev (the Gromov–Milman conjecture), unconditionally.**
For every even `d > 0` and every `k` there is `N` such that every homogeneous polynomial of degree
`d` in `n ≥ N` real variables is, on some `k`-dimensional linear subspace, equal to `c · ‖v‖ ^ d`.

The topological input is only Lemma 1 for elementary abelian `2`-groups (proved in `ElemAb/`),
applied once per level of the iterated wreath product (`WreathBU.achievable_step`). -/
theorem gromovMilman_unconditional (d k : ℕ) (hd : Even d) (hd0 : 0 < d) :
    GromovMilmanProperty d k := by
  classical
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ⟨0, fun n _ f hf => ⟨⊥, by simp, 0, fun v hv => ?_⟩⟩
    rw [Submodule.mem_bot] at hv
    subst hv
    have h0 : (fun i => (0 : EuclideanSpace ℝ (Fin n)) i) = 0 := rfl
    rw [h0, MvPolynomial.eval_zero]
    change f.coeff 0 = _
    rw [hf.coeff_eq_zero (by simpa using hd0.ne)]
    ring
  obtain ⟨δ, hδ⟩ := hd
  have hd2 : d = 2 * δ := by omega
  subst hd2
  have hδ0 : 1 ≤ δ := by omega
  obtain ⟨S, hS, ⟨x0, hx0⟩, hA⟩ := WreathBU.exists_stage_achievable hk δ (2 * δ) δ
  have hgood : ∀ β : S.X → ℕ, ∑ x, β x ≤ δ → IsRadial (2 * ∑ x, β x) (S.orb β) :=
    fun β hβ => hS β hβ ((Stage.card_support_le_sum β).trans hβ)
  obtain ⟨N, hN⟩ := hA.signedGroup_invariant
  exact ⟨N, gromovMilman_of_stage hδ0 S hgood x0 hx0 hN⟩


end Dvoretzky
