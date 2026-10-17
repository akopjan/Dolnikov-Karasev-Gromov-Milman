module

public import RequestProject.Dvoretzky.Lemma1Partial
public import RequestProject.Dvoretzky.MainTheorem

/-!
# Lemma 1 from Carlsson's theorem

Lemma 1 of Dol'nikov–Karasev, the Borsuk–Ulam property of finite `2`-groups due to Bartsch and
Clapp–Marzantowicz, rests on Carlsson's theorem. Carlsson proved the Segal conjecture and the
Sullivan conjecture for finite `p`-group actions on finite complexes. The consequence used in the
literature is the following fixed point statement:

> **Carlsson's theorem (fixed point form).** Let `G` be a finite `p`-group and `Y` a finite
> `G`-complex without `G`-fixed points. Then for `N` large there is no `G`-equivariant map from
> the `N`-skeleton of `EG` to `Y`. Equivalently, `Y` has no homotopy fixed points.

The proof of this statement (equivariant stable homotopy theory, the Adams spectral sequence,
the Burnside ring) cannot be formalized with the current Mathlib. We take it as a hypothesis,
`CarlssonTheorem`, formulated as follows.

* The finite `G`-complex `Y` is a compact `G`-invariant subset of a finite-dimensional orthogonal
  representation of `G`. By the Mostow–Palais theorem every finite `G`-complex embeds this way.
* The finite skeleta of `EG` are replaced by the finite joins `G * ⋯ * G` (`GroupJoin G N`). The
  `N`-fold join is a free `(N - 2)`-connected `N - 1`-dimensional `G`-complex, a model of the
  skeleta of `EG`.

The main results of this file are:

* `joinBorsukUlam_of_carlsson`: Carlsson's theorem implies Lemma 1 (`JoinBorsukUlam`). Only the
  case of unit spheres `S(V)` of representations with `V^G = 0` is used
  (`CarlssonSphereProperty`). By `joinBorsukUlam_iff`, Lemma 1 is equivalent to its zero form, and
  a nowhere vanishing equivariant map `f` into `V` gives the equivariant map `x ↦ f x / ‖f x‖`
  into `S(V)`.
* `carlssonProperty_two_iff`, `carlssonSphereProperty_two_iff`: for `p = 2`, both forms of the
  hypothesis are equivalent to Lemma 1, so the hypothesis is exactly as strong as Lemma 1 needs.
* `gromovMilman_of_carlsson`: Theorem 1 of Dol'nikov–Karasev (the Gromov–Milman conjecture)
  follows from Carlsson's theorem.
-/

@[expose] public section

open scoped BigOperators InnerProductSpace

noncomputable section

namespace Dvoretzky

/-- **Carlsson's theorem (fixed point form) for the prime `p`.** Let `G` be a finite `p`-group
acting orthogonally on a finite-dimensional real inner product space `V` via `ρ`, and let
`Y ⊆ V` be a compact `G`-invariant set that contains no `G`-fixed point. Then there is `N` such
that no continuous `G`-equivariant map from the `N`-fold join `G * ⋯ * G` maps into `Y`. -/
def CarlssonProperty (p : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Fintype G], IsPGroup p G →
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
      (ρ : G →* (V ≃ₗᵢ[ℝ] V)) (Y : Set V), IsCompact Y → (∀ g, ∀ y ∈ Y, ρ g y ∈ Y) →
        (∀ y ∈ Y, ∃ g, ρ g y ≠ y) →
        ∃ N : ℕ, ∀ f : (Fin N → G → ℝ) → V, ContinuousOn f (GroupJoin G N) →
          (∀ g, ∀ x ∈ GroupJoin G N, f (joinAct g x) = ρ g (f x)) →
          ∃ x ∈ GroupJoin G N, f x ∉ Y

/-- **Carlsson's theorem (fixed point form)** for all primes: a compact fixed-point-free
`G`-space in a representation of a finite `p`-group `G` receives no equivariant map from
a sufficiently large finite join `G * ⋯ * G`. -/
def CarlssonTheorem : Prop := ∀ p : ℕ, p.Prime → CarlssonProperty p

/-- The special case of `CarlssonProperty p` for unit spheres of representations without
nonzero fixed vectors: if `V^G = 0`, then for `N` large no continuous `G`-equivariant map from
the `N`-fold join `G * ⋯ * G` takes all its values in the unit sphere `S(V)`. -/
def CarlssonSphereProperty (p : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Fintype G], IsPGroup p G →
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
      (ρ : G →* (V ≃ₗᵢ[ℝ] V)), (∀ v, (∀ g, ρ g v = v) → v = 0) →
        ∃ N : ℕ, ∀ f : (Fin N → G → ℝ) → V, ContinuousOn f (GroupJoin G N) →
          (∀ g, ∀ x ∈ GroupJoin G N, f (joinAct g x) = ρ g (f x)) →
          ∃ x ∈ GroupJoin G N, ‖f x‖ ≠ 1

/-- Carlsson's theorem contains its special case for representation spheres. -/
theorem carlssonSphereProperty_of_carlssonProperty {p : ℕ} (h : CarlssonProperty p) :
    CarlssonSphereProperty p := by
  intro G _ _ hG V _ _ _ ρ hfix
  obtain ⟨N, hN⟩ := h G hG V ρ (Metric.sphere 0 1) (isCompact_sphere 0 1)
    (fun g y hy => by simpa using hy)
    (fun y hy => by
      by_contra hno
      push_neg at hno
      have h0 := hfix y hno
      rw [h0] at hy
      simp at hy)
  refine ⟨N, fun f hf he => ?_⟩
  obtain ⟨x, hx, hfx⟩ := hN f hf he
  exact ⟨x, hx, by simpa using hfx⟩

/-- **Lemma 1 from Carlsson's theorem for representation spheres.** If no large join maps
equivariantly into the unit sphere of a representation of a `2`-group without fixed vectors,
then Lemma 1 (`JoinBorsukUlam`) holds. In the zero form of Lemma 1 (`joinBorsukUlam_iff`), a
nowhere vanishing equivariant map `f` gives the equivariant map `x ↦ f x / ‖f x‖` into the unit
sphere. -/
theorem joinBorsukUlam_of_carlssonSphereProperty_two (h : CarlssonSphereProperty 2) :
    JoinBorsukUlam := by
  refine joinBorsukUlam_iff.2 fun G _ _ hG V _ _ _ ρ hfix => ?_
  obtain ⟨N, hN⟩ := h G hG V ρ hfix
  refine ⟨N, fun f hf hequiv => ?_⟩
  by_contra hno
  push_neg at hno
  let F : (Fin N → G → ℝ) → V := fun x => ‖f x‖⁻¹ • f x
  have hFc : ContinuousOn F (GroupJoin G N) :=
    (hf.norm.inv₀ fun x hx => norm_ne_zero_iff.2 (hno x hx)).smul hf
  have hFe : ∀ g, ∀ x ∈ GroupJoin G N, F (joinAct g x) = ρ g (F x) := by
    intro g x hx
    simp only [F, hequiv g x hx, LinearIsometryEquiv.norm_map, map_smul]
  obtain ⟨x, hx, hFx⟩ := hN F hFc hFe
  apply hFx
  simp only [F]
  rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 (hno x hx))]

/-- **Lemma 1 from Carlsson's theorem.** Carlsson's theorem for the prime `2` implies Lemma 1
of Dol'nikov–Karasev in its join form `JoinBorsukUlam`. -/
theorem joinBorsukUlam_of_carlssonProperty_two (h : CarlssonProperty 2) : JoinBorsukUlam :=
  joinBorsukUlam_of_carlssonSphereProperty_two (carlssonSphereProperty_of_carlssonProperty h)

/-- Lemma 1 in its fixed value form, for an arbitrary finite-dimensional orthogonal
representation (not only for `ℝ^ι`). -/
theorem JoinBorsukUlam.exists_joinFixedProperty (h : JoinBorsukUlam) (G : Type) [Group G]
    [Fintype G] (hG : IsPGroup 2 G) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (ρ : G →* (V ≃ₗᵢ[ℝ] V)) : ∃ N, JoinFixedProperty G V ρ N := by
  obtain ⟨N, hN⟩ := joinBorsukUlam_iff.1 h G hG _ (complRep ρ) (complRep_fixed_eq_zero ρ)
  exact ⟨N, joinFixedProperty_of_complRep ρ hN⟩

/-- Conversely, Lemma 1 (`JoinBorsukUlam`) implies Carlsson's theorem for the prime `2`. -/
theorem carlssonProperty_two_of_joinBorsukUlam (h : JoinBorsukUlam) : CarlssonProperty 2 := by
  intro G _ _ hG V _ _ _ ρ Y _ _ hfix
  obtain ⟨N, hN⟩ := h.exists_joinFixedProperty G hG V ρ
  refine ⟨N, fun f hf hequiv => ?_⟩
  obtain ⟨x, hx, hfx⟩ := hN f hf hequiv
  refine ⟨x, hx, fun hY => ?_⟩
  obtain ⟨g, hg⟩ := hfix _ hY
  exact hg (hfx g)

/-- For the prime `2`, the fixed point form of Carlsson's theorem is equivalent to Lemma 1 of
Dol'nikov–Karasev in its join form. -/
theorem carlssonProperty_two_iff : CarlssonProperty 2 ↔ JoinBorsukUlam :=
  ⟨joinBorsukUlam_of_carlssonProperty_two, carlssonProperty_two_of_joinBorsukUlam⟩

/-- For the prime `2`, the special case of Carlsson's theorem for representation spheres is
already equivalent to Lemma 1, hence to the general fixed point form. -/
theorem carlssonSphereProperty_two_iff : CarlssonSphereProperty 2 ↔ JoinBorsukUlam :=
  ⟨joinBorsukUlam_of_carlssonSphereProperty_two, fun h =>
    carlssonSphereProperty_of_carlssonProperty (carlssonProperty_two_of_joinBorsukUlam h)⟩

/-- **Lemma 1 from Carlsson's theorem.** -/
theorem joinBorsukUlam_of_carlsson (h : CarlssonTheorem) : JoinBorsukUlam :=
  joinBorsukUlam_of_carlssonProperty_two (h 2 Nat.prime_two)

/-- **Theorem 1** of Dol'nikov–Karasev (the Gromov–Milman conjecture), assuming Carlsson's
theorem in its fixed point form: for even `d > 0` and every `k`, for `n` large every homogeneous
polynomial of degree `d` on `ℝⁿ` is a multiple of `‖v‖ ^ d` on some `k`-dimensional subspace. -/
theorem gromovMilman_of_carlsson (h : CarlssonTheorem) (d k : ℕ) (hd : Even d) (hd0 : 0 < d) :
    GromovMilmanProperty d k :=
  gromovMilman_of_joinBorsukUlam (joinBorsukUlam_of_carlsson h) d k hd hd0

end Dvoretzky
