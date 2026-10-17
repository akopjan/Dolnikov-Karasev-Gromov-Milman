module

public import Mathlib
public import RequestProject.Dvoretzky.WreathBU

/-!
# Solution: Theorem 1 of Dol'nikov–Karasev (the Gromov–Milman conjecture)

The untrusted side of the comparator check.  It restates the theorem of
`Challenge.lean` verbatim and proves it from the project's main result
`Dvoretzky.gromovMilman_unconditional` (in `RequestProject/Dvoretzky/WreathBU.lean`).

## Differences from the Paper's Original Proof

While following the overarching combinatorial and topological strategy of Dol'nikov–Karasev
(arXiv:1009.0392), the formalized proof introduces key mathematical modifications:

1. **Elimination of Carlsson's theorem and stable cohomotopy**: The paper relies on Lemma 1
   (Borsuk–Ulam for $p$-groups) for general non-abelian 2-groups, requiring Gunnar Carlsson's
   deep theorem on the Segal conjecture. The formalization proves Lemma 1 from scratch exclusively
   for elementary abelian 2-groups `(ℤ/2)^r` (`ElemAb/`) using explicit chain complexes and
   algebraic Dold peeling over `𝔽₂[U₁,...,U_r]`.
2. **Level-by-level wreath induction**: The paper applies Lemma 1 once to the non-abelian signed
   permutation group `(ℤ/2)^X ⋊ H`. The formalization decomposes `H` into an iterated wreath
   product `K₁ ≀ ⋯ ≀ K_δ` of elementary abelian 2-groups and applies Lemma 1 level-by-level.
   Because the join embedding is block-structured, symmetries established at earlier levels are
   inherited and preserved.
3. **Free spaces**: The paper uses Stiefel manifolds and their connectivity; the formalization
   uses concrete $N$-fold joins `G * ⋯ * G` with explicit isometric block embeddings.
4. **Averaging**: Each degree is averaged separately over `O(k)` and composed sequentially,
   avoiding convex weight discrepancies from scaling lower degrees by powers of `Q`.

For full details, see `README.md` and `COMPARISON_WITH_PAPER.md`.
-/

@[expose] public section

noncomputable section

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
  obtain ⟨N, hN⟩ := Dvoretzky.gromovMilman_unconditional d k hd_even hd
  refine ⟨N, fun n hn f hf => ?_⟩
  obtain ⟨V, hV, c, hc⟩ := hN n hn f hf
  let e := WithLp.linearEquiv 2 ℝ (Fin n → ℝ)
  refine ⟨V.map (e : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] (Fin n → ℝ)), ?_, c, ?_⟩
  · rw [LinearEquiv.finrank_map_eq, hV]
  · rintro ⟨x, hx⟩
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hx
    have h1 := hc v hv
    have hfun : (fun i => v i) = (e v : Fin n → ℝ) := rfl
    rw [hfun] at h1
    refine h1.trans ?_
    obtain ⟨m, rfl⟩ := hd_even
    have hsq : ‖v‖ ^ 2 = ∑ i, (e v : Fin n → ℝ) i ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp [e]
    rw [show m + m = 2 * m by ring, pow_mul, hsq, Nat.mul_div_cancel_left _ two_pos]
    rfl

end

end
