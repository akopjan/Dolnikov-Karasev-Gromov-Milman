module

public import Mathlib

/-!
# Statements: the Gromov–Milman conjecture (Theorem 1 of Dol'nikov–Karasev)

V. L. Dol'nikov, R. N. Karasev, *Dvoretzky type theorems for multivariate polynomials and
sections of convex bodies*, arXiv:1009.0392.

**Theorem 1.** For an even positive integer `d` and a positive integer `k` there exists
`n(d, k)` such that for any homogeneous polynomial `f` of degree `d` on `ℝⁿ`, `n ≥ n(d, k)`,
there exists a linear `k`-subspace `V ⊆ ℝⁿ` such that `f|_V` is proportional to the
`d/2`-th power of the standard quadratic form `Q = x₁² + ⋯ + xₙ²`.

The proof in the paper uses, as a black box, a Borsuk–Ulam type theorem for `p`-groups
(Lemma 1 of the paper, due to Bartsch, Clapp–Marzantowicz, and resting on Carlsson's
solution of the Segal conjecture). We isolate exactly the consequence of Lemma 1 that is used
as the proposition `TwoGroupBorsukUlam` below.
-/

@[expose] public section

namespace Dvoretzky

/-- The conclusion of **Theorem 1** (Gromov–Milman conjecture) for given `d` and `k`:
there is `N` such that every homogeneous polynomial `f` of degree `d` in `n ≥ N` real variables
restricts to some `k`-dimensional linear subspace `V` as `c · ‖v‖ ^ d = c · Q(v) ^ (d / 2)`. -/
def GromovMilmanProperty (d k : ℕ) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, ∀ f : MvPolynomial (Fin n) ℝ, f.IsHomogeneous d →
    ∃ V : Submodule ℝ (EuclideanSpace ℝ (Fin n)), Module.finrank ℝ V = k ∧
      ∃ c : ℝ, ∀ v ∈ V, MvPolynomial.eval (fun i => v i) f = c * ‖v‖ ^ d

/-- The consequence of **Lemma 1** of Dol'nikov–Karasev (the Borsuk–Ulam property of finite
`2`-groups, due to Bartsch and Clapp–Marzantowicz via Carlsson's theorem) that is used in the
proof of Theorem 1.

Let `G` be a finite `2`-subgroup of the orthogonal group of `ℝ^ι` and `P ⊆ ℝ^ι` a finite set.
Then for `n` large enough, for every continuous `φ : ℝⁿ → ℝ` there is a linear isometric
embedding `L : ℝ^ι → ℝⁿ` such that `φ ∘ L` is `G`-invariant on `P`.

This follows from Lemma 1 applied to the free `G`-space `X = V_ι(ℝⁿ)` of linear isometric
embeddings (the Stiefel manifold, which is `(n - |ι| - 1)`-connected), the `G`-representation
`V = ℝ^(G • P)` (permutation representation) and the equivariant map
`L ↦ (φ (L p))_{p ∈ G • P}`. -/
def TwoGroupBorsukUlam : Prop :=
  ∀ (ι : Type) [Fintype ι] (G : Subgroup (EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι)),
    Finite G → IsPGroup 2 G → ∀ P : Finset (EuclideanSpace ℝ ι),
      ∃ N : ℕ, ∀ n ≥ N, ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ, Continuous φ →
        ∃ L : EuclideanSpace ℝ ι →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
          ∀ g ∈ G, ∀ p ∈ P, φ (L (g p)) = φ (L p)

end Dvoretzky
