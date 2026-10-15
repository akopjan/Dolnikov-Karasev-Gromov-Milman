# Gromov–Milman Conjecture: Dvoretzky-Type Theorem for Multivariate Polynomials

This repository contains the unconditional Lean 4 formalization of **Theorem 1** from:

> V. L. Dol'nikov, R. N. Karasev, *Dvoretzky type theorems for multivariate polynomials and sections of convex bodies*, [arXiv:1009.0392](https://arxiv.org/abs/1009.0392).

This theorem confirms the **Gromov–Milman conjecture** on polynomials restricted to subspaces: for any even degree $d > 0$ and any dimension $k \ge 1$, every homogeneous real polynomial $f$ of degree $d$ in sufficiently many variables ($n \ge n(d, k)$) restricts on some $k$-dimensional linear subspace $V \subseteq \mathbb{R}^n$ to a scalar multiple of $(x_1^2 + \dots + x_n^2)^{d/2}$.

---

## Status and Verification

- **Lean Version**: `leanprover/lean4:v4.35.0` (with Mathlib `v4.35.0`).
- **Axioms**: Standard Lean foundations only (`propext`, `Quot.sound`, `Classical.choice`). Zero custom axioms.
- **`sorry` Count**: `0` in `Solution.lean` and all dependencies of Theorem 1.
- **Palomar Audit**: Verified with [`leanprover/comparator`](https://github.com/leanprover/comparator) against `Challenge.lean`. Result: `Your solution is okay!`.

### Verification Steps

1. **Build targets**:
   ```bash
   lake build Challenge Solution
   ```
2. **Run comparator audit**:
   ```bash
   lake env comparator comparator.json
   ```
   The comparator verifies that `Solution.theorem1` matches `Challenge.theorem1` verbatim and uses no unpermitted axioms or `sorry`.

---

## Statement

The statement formalized in `Challenge.lean` and proven in `Solution.lean` matches the paper verbatim:

```lean
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
                  c * (∑ i : Fin n, ((x : Fin n → ℝ) i) ^ 2) ^ (d / 2)
```

---

## Comparison with the Original Proof in the Paper

While the theorem statement and the broad topological-combinatorial architecture originate in Dol'nikov–Karasev (arXiv:1009.0392), the **formalized proof contains major structural differences and innovations**. Most notably, **it completely eliminates Gunnar Carlsson's theorem and equivariant stable cohomotopy**, replacing external topological black boxes with an elementary abelian Dold-type Borsuk–Ulam theorem proved from first principles on chain complexes and applied inductively level-by-level.

### Overview of Differences

| Aspect | Paper (Dol'nikov–Karasev) | Formalization (`Solution.lean` / `WreathBU.lean`) |
| :--- | :--- | :--- |
| **Topological Input** | **Lemma 1** (Borsuk–Ulam for $p$-groups) taken from literature; applied **once** to a **non-abelian** 2-group $(\mathbb{Z}/2)^X \rtimes H$. | **Lemma 1 proved from scratch**, but strictly for **elementary abelian** 2-groups $(\mathbb{Z}/2)^r$; applied **level-by-level** to wreath products. |
| **Carlsson's Theorem** | **Required** (known proofs of Lemma 1 for general non-abelian 2-groups rely on Carlsson's proof of the Segal conjecture and stable cohomotopy). | **Completely eliminated**. No Carlsson theorem, no stable cohomotopy, no equivariant spectra. |
| **Free $G$-Space** | Stiefel manifold of isometric linear embeddings $V_m(\mathbb{R}^n)$, using its $(n-m-1)$-connectivity. | Concrete $N$-fold join $G * \dots * G$ with an explicit block-structured isometric embedding into orthogonal blocks of $\mathbb{R}^n$. |
| **Combinatorics** | 2-Sylow subgroups of symmetric groups via binary trees and pigeonhole on tree "forks". | Iterated wreath products $K_1 \wr \dots \wr K_\delta$ of elementary abelian 2-groups (Section 9 remark), with induction on exponent support. |
| **Lemma 2 (Averaging)** | Mixed-degree polynomials reduced to degree $d$ by multiplying by powers of $Q = \sum x_i^2$. | Each degree is averaged separately over $O(k)$ and the resulting families of similarities are composed sequentially. |
| **Target Representation** | Infinite-dimensional polynomial functions. | Values of polynomials evaluated on a finite grid (`invariant_of_grid`). |

---

### Detailed Mathematical Differences

#### 1. Elimination of Carlsson's Theorem and Non-Abelian Borsuk–Ulam

- **In the Paper**: The paper applies Lemma 1 (the Borsuk–Ulam theorem for $p$-groups, originally due to Bartsch and Clapp–Marzantowicz) to the signed permutation group $(\mathbb{Z}/2)^X \rtimes H$. Because $H$ is a 2-Sylow subgroup of a symmetric group, this group is **non-abelian**. Proving Lemma 1 for arbitrary non-abelian $p$-groups is one of the deepest results in equivariant topology: all known proofs depend on Gunnar Carlsson's theorem (the Segal conjecture for elementary abelian 2-groups and its extension to 2-groups) and equivariant stable cohomotopy.
- **In the Formalization**: Carlsson's theorem is **not** used. Instead:
  1. Lemma 1 is proven from first principles in `RequestProject/Dvoretzky/ElemAb/` exclusively for **elementary abelian** 2-groups $(\mathbb{Z}/2)^r$. The proof works directly at the chain level:
     - constructing canonical equivariant chain complexes on iterated joins of $(\mathbb{Z}/2)^r$;
     - using the algebraic fact that the polynomial ring $\mathbb{F}_2[U_1, \dots, U_r]$ is an integral domain to carry out algebraic Dold peeling;
     - employing barycentric subdivision and simplicial approximation to transfer continuous maps to chain maps.
  2. This constructive chain-level proof requires only elementary linear algebra and combinatorial topology.

#### 2. Level-by-Level Induction on Iterated Wreath Products

Because Lemma 1 is only available for elementary abelian 2-groups, the paper's single non-abelian application cannot be executed directly:
- **Paper**: One single application to $(\mathbb{Z}/2)^X \rtimes H$.
- **Formalization**: The group $H = K_1 \wr \dots \wr K_\delta$ is an iterated wreath product of elementary abelian 2-groups $(\mathbb{Z}/2)^{a_j}$. The formalization establishes polynomial invariance by **induction on the levels of the wreath product** (`Achievable e X H` in `RequestProject/Dvoretzky/WreathBU.lean`):
  - **Base step** (`achievable_base`): Lemma 1 for $(\mathbb{Z}/2)^Z$ handles sign changes.
  - **Inductive step** (`achievable_step`): Passes from $H$ to $H \wr (\mathbb{Z}/2)^a$ using Lemma 1 *only* for the abelian group of top-level translations $((\mathbb{Z}/2)^a)^Z$.
- **Why this works without non-abelian Lemma 1**: The join embedding:
  $$L_x(v)(i, c) = \sum_{h \in G} \sqrt{x_i(h)} \cdot v(h \cdot c)$$
  is **block-structured**: inside block $i$, only one label $h$ carries positive weight. If a polynomial function is invariant under independent copies of the inner group acting on each block, composing with $L_x$ preserves this inner invariance automatically. Hence, symmetries gained at earlier levels are never destroyed by subsequent steps!

#### 3. Free $G$-Spaces: Joins Instead of Stiefel Manifolds

- **In the Paper**: Lemma 1 is applied to the Stiefel manifold of orthonormal $m$-frames in $\mathbb{R}^n$, utilizing the fact that $\pi_i(V_m(\mathbb{R}^n)) = 0$ for $i < n - m$. Mathlib does not currently contain homotopy groups of Stiefel manifolds.
- **In the Formalization**: The free $G$-space is the concrete $N$-fold topological join $G * \dots * G$, parametrized as families of weights $x : \text{Fin } N \to G \to \mathbb{R}_{\ge 0}$ with $\sum_h x_i(h) \le 1$ and at most one active label per block. Each join element defines an explicit linear isometric embedding into orthogonal blocks of $\mathbb{R}^n$. Topological connectivity of Stiefel manifolds is completely bypassed.

#### 4. Averaging Lemma (Lemma 2)

- **In the Paper**: For a polynomial with mixed degrees, terms of degree $d' < d$ are multiplied by $(\sum x_i^2)^{(d-d')/2}$ to reduce everything to a single homogeneous degree $d$.
- **In the Formalization**: Rescaling similarities by $w_i^{1/d}$ causes a degree $d'$ term to acquire a weight factor $w_i^{d'/d} \ne w_i$, disrupting the convex combination. The formalization avoids this issue by:
  - Applying Carathéodory's theorem and Haar averaging over $O(k)$ to **one degree at a time** (`Averaging.lean`);
  - Composing the resulting families of similarities sequentially across degrees;
  - Padding similarities to powers of two (`averaging_pow2`), which supplies the elementary abelian top-level groups $(\mathbb{Z}/2)^a$.

For further mathematical details and file-by-file comparisons, see [`COMPARISON_WITH_PAPER.md`](file:///Users/akopyan/Documents/antigravity/Lean/Gromov-Milman/COMPARISON_WITH_PAPER.md).

---

## Repository Layout

```
.
├── Challenge.lean                  # Formal theorem formulation (sorry)
├── Solution.lean                   # Verified proof of theorem1
├── comparator.json                 # Palomar comparator configuration
├── formalization.yaml              # Palomar v0.4 metadata specification
├── LICENSE                         # Apache License 2.0
├── lakefile.toml                   # Lake project configuration (Lean 4.35)
├── lean-toolchain                  # leanprover/lean4:v4.35.0
├── COMPARISON_WITH_PAPER.md        # Extended mathematical comparison with the paper
├── RequestProject/
│   └── Dvoretzky/
│       ├── WreathBU.lean           # Level-by-level wreath Borsuk–Ulam induction
│       ├── Theorem1.lean           # Gromov–Milman derivation from stage invariance
│       ├── Stage.lean              # Wreath product stage construction
│       ├── Wreath.lean             # Iterated wreath products of elementary abelian groups
│       ├── Averaging.lean          # Lemma 2: Haar averaging and Carathéodory
│       ├── ElemAb/                 # Lemma 1 for (Z/2)^r (elementary abelian groups)
│       │   ├── Source.lean         # Chain complex on join of (Z/2)^r
│       │   ├── Target.lean         # Target peeling over F_2[U_1, ..., U_r]
│       │   ├── Main.lean           # Topological Dold theorem for (Z/2)^r
│       │   └── Emptiness.lean      # Non-existence of equivariant maps to sphere
│       ├── Dold/                   # Dold's theorem for Z/p
│       │   ├── Chains.lean         # Standard Z/p resolution
│       │   ├── Subdivision.lean    # Simplicial subdivision
│       │   └── Main.lean           # Borsuk–Ulam for prime cyclic groups
│       ├── ConvexCompact.lean      # Simplex compactness and convexity
│       ├── PolyFun.lean            # Polynomial representation on finite grids
│       └── Signed.lean             # Signed permutation group actions
```

---

## Attribution and Citation

This formalization was developed by **Arseniy Akopyan** with assistance from [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

---

## License

This project is licensed under the Apache License, Version 2.0. See [LICENSE](LICENSE) for the full license text.