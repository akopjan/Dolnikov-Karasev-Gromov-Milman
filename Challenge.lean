module
 
public import Mathlib

/-!
# Challenge: Theorem 1 of Dol'nikov–Karasev (the Gromov–Milman conjecture)

V. L. Dol'nikov, R. N. Karasev, *Dvoretzky type theorems for multivariate polynomials and
sections of convex bodies*, arXiv:1009.0392, Theorem 1:

> For an even positive integer `d` and a positive integer `k` there exists `n(d, k)` such that
> for any homogeneous polynomial `f` of degree `d` on `ℝⁿ`, `n ≥ n(d, k)`, there exists a linear
> `k`-subspace `V ⊆ ℝⁿ` such that `f|_V` is proportional to the `d/2`-th power of the standard
> quadratic form `Q = x₁² + ⋯ + xₙ²`.

The statement follows the paper literally: subspaces of `ℝⁿ = Fin n → ℝ`, the hypotheses
`0 < d`, `Even d`, `0 < k`, and the restriction written as `c * (x₁² + ⋯ + xₙ²)^(d/2)`.
-/

@[expose] public section

/-- Theorem 1 of Dol'nikov–Karasev.  The hypothesis `hk : 0 < k` is kept as in the paper,
although the proof does not need it (for `k = 0` take `V = ⊥`). -/
theorem theorem1
    (d k : ℕ)
    (hd : 0 < d)
    (hd_even : Even d)
    (hk : 0 < k) :
    ∃ N : ℕ,
      ∀ n : ℕ,
        N ≤ n →
        ∀ f : MvPolynomial (Fin n) ℝ,
          f.IsHomogeneous d →
          ∃ V : Submodule ℝ (Fin n → ℝ),
            Module.finrank ℝ V = k ∧
            ∃ c : ℝ,
              ∀ x : V,
                MvPolynomial.eval (x : Fin n → ℝ) f =
                  c * (∑ i : Fin n, ((x : Fin n → ℝ) i) ^ 2) ^ (d / 2) := by
  sorry
