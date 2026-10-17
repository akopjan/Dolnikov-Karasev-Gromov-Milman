# How the formalization differs from the proof in the paper

Paper: V. L. Dol'nikov, R. N. Karasev, *Dvoretzky type theorems for multivariate polynomials and
sections of convex bodies* (arXiv:1009.0392). Main result: **Theorem 1** (the Gromov–Milman
conjecture).

Lean result (`RequestProject/Dvoretzky/WreathBU.lean`):

```lean
theorem gromovMilman_unconditional (d k : ℕ) (hd : Even d) (hd0 : 0 < d) :
    GromovMilmanProperty d k
```

The proof has no `sorry` and no extra hypotheses. `#print axioms` lists only `propext`,
`Classical.choice` and `Quot.sound`.

The comparison below follows the structure of the paper's proof (Dol'nikov–Karasev, arXiv:1009.0392).

---

## 0. Summary

| Step | Paper | Formalization |
|---|---|---|
| Statement | `f|_V` is proportional to `Q^{d/2}` on some `k`-subspace `V`, for `n ≥ n(d,k)` | The same statement (`GromovMilmanProperty`); `k = 0` is included |
| Topological input | Lemma 1 (Borsuk–Ulam for `p`-groups) taken from the literature and applied **once**, to a **non-abelian** 2-group | Lemma 1 **proved from scratch**, but only for **elementary abelian** 2-groups `(ℤ/2)^r`, and applied **once per level** of a wreath product |
| Free, highly connected `G`-space | Stiefel manifold of isometric embeddings `ℝ^m → ℝⁿ` | The `N`-fold join `G * ⋯ * G`, with an explicit map to isometric embeddings |
| Lemma 2 (averaging) | Mixed degrees are reduced to one degree by multiplying by powers of `Q` | Each degree is handled separately and the resulting families of similarities are composed |
| Combinatorics (Sections 6–9) | 2-Sylow subgroups of symmetric groups, binary trees, a pigeonhole argument on forks | Iterated wreath products `K₁ ≀ ⋯ ≀ K_δ` of elementary abelian 2-groups (from the remark at the end of Section 9), and an induction on the size of the support |

The main difference is the first row of the topology: **the formalized proof of Theorem 1 does not
use Carlsson's theorem or equivariant stable cohomotopy**. The paper needs them, through Lemma 1 for
non-abelian 2-groups.

---

## 1. The statement

Paper: for even `d > 0` and every `k` there is `n(d,k)` such that every homogeneous polynomial `f`
of degree `d` on `ℝⁿ`, `n ≥ n(d,k)`, restricted to some linear `k`-subspace, is proportional to
`Q^{d/2}`, where `Q = x₁² + ⋯ + xₙ²`.

Lean (`RequestProject/Dvoretzky/Statement.lean`):

```lean
def GromovMilmanProperty (d k : ℕ) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, ∀ f : MvPolynomial (Fin n) ℝ, f.IsHomogeneous d →
    ∃ V : Submodule ℝ (EuclideanSpace ℝ (Fin n)), Module.finrank ℝ V = k ∧
      ∃ c : ℝ, ∀ v ∈ V, MvPolynomial.eval (fun i => v i) f = c * ‖v‖ ^ d
```

Since `‖v‖^d = Q(v)^{d/2}`, this is the paper's statement. The only additions are minor: `k = 0` is
covered (trivially), and `d` must be even and positive, as in the paper. As in the paper, the
bound `n(d,k)` exists but is not computed.

## 2. The topological input (main difference)

### In the paper

The paper takes **Lemma 1** from the literature (Bartsch; Clapp–Marzantowicz). Let `G` be a
`p`-group acting freely on a sufficiently highly connected space `X`, and `V` a representation
with `V^G = 0`. Then every continuous equivariant map `X → V` has a zero. For general (non-abelian)
`p`-groups, the known proofs use equivariant stable cohomotopy and Carlsson's solution of the Segal
conjecture.

The paper applies Lemma 1 **once**. The group is the signed-permutation group `(ℤ/2)^X ⋊ H`, where
`H` is a 2-subgroup of a symmetric group. The space is the Stiefel manifold, and the map is
`L ↦ (f(L p))_p`. The result is an isometric embedding `L : ℝ^X → ℝⁿ` such that `f ∘ L` is
invariant under the whole group. This group is non-abelian, so this step needs the full strength
of Lemma 1.

### In the formalization

1. **Lemma 1 is proved, but only for elementary abelian 2-groups `(ℤ/2)^r`**
   (`RequestProject/Dvoretzky/ElemAb/`). It extends Dold's theorem for `ℤ/2`. The proof works at the
   chain level, built from scratch:
   * a family of chains on the join of `(ℤ/2)^r`, from the standard resolution;
   * the fact that `𝔽₂[U₁,…,U_r]` is an integral domain;
   * barycentric subdivision and simplicial approximation.

   It does not use Carlsson's theorem, stable cohomotopy, or K-theory.

2. **Lemma 1 is applied level by level instead of once.** This argument is not in the paper. The
   group `H = K₁ ≀ ⋯ ≀ K_δ` is an iterated wreath product of elementary abelian 2-groups. The
   invariance is built by induction on the levels.
   * The induction property is `Achievable e X H`.
   * The base case `achievable_base` handles the sign changes, using Lemma 1 for `(ℤ/2)^Z`.
   * The step `achievable_step` passes from `H` to `H ≀ (ℤ/2)^a`. It uses Lemma 1 only for the
     elementary abelian group `((ℤ/2)^a)^Z` of new top-level translations.

   The symmetry gained at earlier levels is kept for a structural reason. The join embedding
   `L_x(v)(i, c) = ∑_h √(x_i(h)) · v(h·c)` is block-structured: in each join block `i` only one
   label `h` carries weight. Suppose the function is invariant under independent copies, one per
   block, of the inner group. Then it stays invariant after composing with `L_x`. Lemma 1 is
   therefore never needed for a non-abelian group.

3. Consequently the paper's single use of Lemma 1 for the non-abelian group `(ℤ/2)^X ⋊ H` is
   replaced by `δ + 1` uses of the elementary abelian case.

   Lemma 1 applied to a single abelian subgroup of the group that the paper uses cannot give the
   required invariance. There is no conflict with the level-by-level argument. That argument never
   asks for invariance under an abelian subgroup of a fixed embedding. Instead it builds a new
   embedding at each level, composed with the previous one.

The general form of Lemma 1, used in the paper, is still **not** formalized for non-abelian
2-groups, and neither is Carlsson's theorem. It remains available as an explicit hypothesis in
the older conditional versions (`gromovMilman`, `gromovMilman_of_joinBorsukUlam`,
`gromovMilman_of_carlsson`), but Theorem 1 itself does not need it.

## 3. The free `G`-space: join instead of Stiefel manifold

* **Paper:** Lemma 1 is applied to the Stiefel manifold of linear isometric embeddings
  `ℝ^m → ℝⁿ`, which is `(n - m - 1)`-connected. This uses the homotopy groups of Stiefel
  manifolds, which Mathlib does not have.
* **Formalization:** the free space is the `N`-fold join `G * ⋯ * G`. It is modelled concretely as
  the weight families `x : Fin N → G → ℝ` that are nonnegative, sum to `1`, and use at most one
  label per block. Each point of the join is sent to an explicit isometric embedding into
  orthogonal blocks of `ℝⁿ`: `v ↦ ∑_i ∑_h √(x_i(h)) · block_i(h·v)`. Connectivity of the join is
  never used directly. It is built into the Borsuk–Ulam statement for joins.

## 4. Finite-dimensional target: a grid instead of all of `f`

Lemma 1 needs a finite-dimensional representation as target. The formalization uses the values of
`f ∘ L` on a finite **grid** of points. A polynomial of degree `≤ e` is determined by its values on
the grid (`invariant_of_grid`). So equality on the grid, for the translated points, gives
invariance of the whole polynomial. The paper uses an equivalent reduction (invariance of a
polynomial is a finite-dimensional condition); the grid is just a concrete way to write it.

## 5. Lemma 2 (averaging)

* **Paper:** for finitely many even-degree homogeneous polynomials on `ℝ^k`, average over `O(k)`
  and use Carathéodory to obtain finitely many similarities `σ_i` with `∑_i φ_j ∘ σ_i` proportional
  to `‖·‖^{deg φ_j}`. Different degrees are reduced to one degree `d` by multiplying by powers of
  `Q`.
* **Formalization** (`Averaging.lean`, `averaging_lemma`): the same averaging, with Haar measure on
  `O(k)`, Carathéodory, and uniqueness of polynomials on a finite grid. The mixed-degree reduction
  is **not** used. If the similarities are rescaled as `w_i^{1/d} ρ_i`, then a term of lower degree
  `d'` picks up the extra factor `w_i^{(d-d')/d}` instead of `w_i`, and the convex weights no longer
  match. The formalization handles one degree at a time and composes the resulting families of
  similarities. There is also a variant `averaging_pow2`, where the similarities are indexed by
  `(ℤ/2)^a`, padded with zero maps. This variant is what makes each level of the construction an
  elementary abelian group.

## 6. The combinatorial part (Sections 6–9)

* **Paper:** uses 2-Sylow subgroups of symmetric groups, described through binary trees, together
  with a pigeonhole argument on "forks" of the trees. This shows that all orbit sums
  `∑_{h∈H} ∏_x l_{h x}(z)^{2β_x}` with `|β| ≤ δ` are proportional to `‖z‖^{2|β|}`.
* **Formalization** (`Wreath.lean`, `Stage.lean`): uses iterated wreath products
  `K₁ ≀ ⋯ ≀ K_δ` of elementary abelian 2-groups, which the paper itself suggests in the remark at
  the end of Section 9. The pigeonhole argument is replaced by an induction on the size of the
  support of the exponent vector `β` (`Stage.step_good`). The final averaging step, which derives
  Theorem 1 from the invariance and the radial orbit sums, follows the paper
  (`gromovMilman_of_stage` in `Theorem1.lean`).

## 7. Scope of the formalization

* **Lemma 1**: Proved from scratch for groups of prime order (`Dold/`) and elementary abelian 2-groups (`ElemAb/`).
  General non-abelian 2-groups are not formalized and are not needed for Theorem 1.
* **Carlsson's theorem**: Not formalized and eliminated from the proof of Theorem 1.
* **Focus on Theorem 1**: The formalization focuses strictly on establishing Theorem 1 (the Gromov–Milman conjecture) unconditionally with zero `sorry` and standard Lean foundations.

