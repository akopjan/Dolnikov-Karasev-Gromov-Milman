module

public import Mathlib

/-!
# The algebraic core of Dold's theorem for `ℤ/p`

Let `g` be an endomorphism of order `p` of a module `M`, `σ = 1 - g` and `τ = 1 + g + ⋯ + g^(p-1)`.

* `dold_algebra`: an abstract chain-level argument (the Smith-theory proof of the Borsuk–Ulam
  theorem for `ℤ/p`). If `∂` is a differential commuting with `g`, the module is "free" in the
  sense that `ker τ ⊆ im σ` and `ker σ ⊆ im τ` (up to multiples of a fixed augmentation cycle `u`),
  then there is no sequence `b₀, …, bₙ` with `∂ b₀ = u`, `∂ b_{k+1} = ρ_k b_k` (`ρ` alternating
  between `τ` and `σ`) and `bₙ = 0`.
* `exact_of_proj`: the exactness hypotheses hold as soon as there is a "fundamental domain
  projection" `Q` with `∑ᵢ gⁱ Q g^(p-i) = 1 - u ⊗ ε`.
-/

@[expose] public section

open scoped BigOperators

noncomputable section

namespace Dvoretzky.Dold

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Alternating operator: `ρ k = A` for even `k`, `B` for odd `k`. -/
def altOp (A B : Module.End R M) (k : ℕ) : Module.End R M := if Even k then A else B

lemma altOp_add_two (A B : Module.End R M) (k : ℕ) : altOp A B (k + 2) = altOp A B k := by
  simp [altOp, Nat.even_add]

/-- **Algebraic Dold lemma.** -/
theorem dold_algebra (d A B : Module.End R M) (u : M) (ε : M →ₗ[R] R)
    (hdd : d * d = 0) (hdA : d * A = A * d) (hdB : d * B = B * d) (hdu : d u = 0)
    (hεB : ∀ y, ε (B y) = 0) (hεu : ε u ≠ 0)
    (hA : ∀ z, A z = 0 → ∃ e : M, ∃ c : R, z = B e + c • u)
    (hB : ∀ z, B z = 0 → ∃ e : M, ∃ c : R, z = A e + c • u)
    (n : ℕ) (b : ℕ → M) (hb0 : d (b 0) = u)
    (hb : ∀ k < n, d (b (k + 1)) = altOp A B k (b k)) (hbn : b n = 0) : False := by
  have hdρ : ∀ k, d * altOp A B k = altOp A B k * d := by
    intro k; unfold altOp; split_ifs <;> assumption
  have hd2 : ∀ x, d (d x) = 0 := fun x => by rw [← Module.End.mul_apply, hdd]; rfl
  have hex : ∀ k z, altOp A B k z = 0 → ∃ e : M, ∃ c : R, z = altOp A B (k + 1) e + c • u := by
    intro k z hz
    unfold altOp at hz ⊢
    by_cases hk : Even k
    · rw [if_pos hk] at hz
      rw [if_neg (by simpa [Nat.even_add_one] using hk)]
      exact hA z hz
    · rw [if_neg hk] at hz
      rw [if_pos (by simpa [Nat.even_add_one] using hk)]
      exact hB z hz
  have key : ∀ j ≤ n, ∃ e e' : M, ∃ c : R,
      b (n - j) = d e + altOp A B (n - j + 1) e' + c • u := by
    intro j hj
    induction j with
    | zero => exact ⟨0, 0, 0, by simp [hbn]⟩
    | succ j ih =>
      obtain ⟨E, E', c, hE⟩ := ih (by omega)
      have hk1 : n - j = (n - (j + 1)) + 1 := by omega
      rw [hk1] at hE
      set k := n - (j + 1)
      have h1 : altOp A B k (b k - d E') = 0 := by
        have h2 := hb k (by omega)
        rw [hE] at h2
        have h4 : d (altOp A B (k + 1 + 1) E') = altOp A B k (d E') := by
          rw [show k + 1 + 1 = k + 2 by ring, altOp_add_two, ← Module.End.mul_apply, hdρ,
            Module.End.mul_apply]
        simp only [map_add, map_smul, hd2, h4, hdu, smul_zero, add_zero, zero_add] at h2
        rw [map_sub, ← h2, sub_self]
      obtain ⟨e, c', he⟩ := hex k _ h1
      exact ⟨E', e, c', by rw [add_assoc, ← he]; abel⟩
  obtain ⟨e, e', c, he⟩ := key n le_rfl
  simp only [Nat.sub_self, zero_add] at he
  have h1 : d (b 0) = B (d e') := by
    rw [he]
    have hB1 : altOp A B 1 = B := by simp [altOp]
    simp only [map_add, map_smul, hd2, hdu, smul_zero, add_zero, zero_add, hB1]
    rw [← Module.End.mul_apply, hdB, Module.End.mul_apply]
  rw [hb0] at h1
  exact hεu (by rw [h1, hεB])

/-- The norm element `τ = ∑_{i<p} gⁱ`. -/
def normOp (g : Module.End R M) (p : ℕ) : Module.End R M := ∑ i ∈ Finset.range p, g ^ i

lemma normOp_apply (g : Module.End R M) (p : ℕ) (x : M) :
    normOp g p x = ∑ i ∈ Finset.range p, (g ^ i) x := by
  simp [normOp]

lemma normOp_mul_sub (g : Module.End R M) (p : ℕ) (hg : g ^ p = 1) :
    normOp g p * (1 - g) = 0 := by
  unfold normOp
  rw [Finset.sum_mul]
  have : ∀ i ∈ Finset.range p, g ^ i * (1 - g) = g ^ i - g ^ (i + 1) := by
    intro i _; rw [mul_sub, mul_one, pow_succ]
  rw [Finset.sum_congr rfl this, Finset.sum_range_sub', pow_zero, hg, sub_self]

lemma commute_normOp (g : Module.End R M) (p : ℕ) : Commute g (normOp g p) := by
  unfold normOp
  exact Commute.sum_right _ _ _ fun i _ => Commute.pow_right (Commute.refl g) i

lemma sub_mul_normOp (g : Module.End R M) (p : ℕ) (hg : g ^ p = 1) :
    (1 - g) * normOp g p = 0 := by
  have hc : Commute (1 - g) (normOp g p) :=
    (Commute.one_left _).sub_left (commute_normOp g p)
  rw [hc.eq, normOp_mul_sub g p hg]

/-- **Exactness from a fundamental domain projection.** -/
theorem exact_of_proj (g Q : Module.End R M) (p : ℕ) (hp : 0 < p) (hg : g ^ p = 1) (u : M)
    (ε : M →ₗ[R] R)
    (hQ : ∀ x, ∑ i ∈ Finset.range p, (g ^ i) (Q ((g ^ (p - i)) x)) = x - ε x • u) :
    (∀ z, (1 - g) z = 0 → ∃ e : M, ∃ c : R, z = normOp g p e + c • u) ∧
    (∀ z, normOp g p z = 0 → ∃ e : M, ∃ c : R, z = (1 - g) e + c • u) := by
  constructor
  · intro z hz
    have hgz : g z = z := by
      have h := hz
      simp only [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h
      exact h.symm
    have hpow : ∀ m, (g ^ m) z = z := by
      intro m; induction m with
      | zero => simp
      | succ m ih => rw [pow_succ, Module.End.mul_apply, hgz, ih]
    refine ⟨Q z, ε z, ?_⟩
    have h := hQ z
    simp only [hpow] at h
    rw [normOp_apply, h]
    abel
  · intro z hz
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    let Qi : ℕ → Module.End R M := fun i => g ^ i * Q * g ^ (q + 1 - i)
    have hQi : ∀ i w, Qi i w = (g ^ i) (Q ((g ^ (q + 1 - i)) w)) := fun i w => rfl
    have hgQ : ∀ i ≤ q, ∀ w, g (Qi i w) = Qi (i + 1) (g w) := by
      intro i hi w
      simp only [hQi]
      rw [← Module.End.mul_apply g, ← pow_succ', ← Module.End.mul_apply _ g, ← pow_succ,
        show q + 1 - (i + 1) + 1 = q + 1 - i by omega]
    let S : ℕ → M := fun i => ∑ m ∈ Finset.range (i + 1), (g ^ m) z
    have hτ : ∑ m ∈ Finset.range (q + 1), (g ^ m) z = 0 := by
      rw [← normOp_apply]; exact hz
    have hgS : ∀ i, g (S i) = S (i + 1) - z := by
      intro i
      simp only [S, map_sum]
      rw [Finset.sum_range_succ' (fun m => (g ^ m) z) (i + 1)]
      simp only [pow_zero, Module.End.one_apply, add_sub_cancel_right]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [pow_succ', Module.End.mul_apply]
    have hSq : S q = 0 := hτ
    let y : M := ∑ i ∈ Finset.range (q + 1), Qi i (S i)
    refine ⟨y, ε z, ?_⟩
    have hgy : g y = ∑ i ∈ Finset.range (q + 1), Qi (i + 1) (g (S i)) := by
      simp only [y, map_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      exact hgQ i (by omega) _
    have hsum : ∑ i ∈ Finset.range (q + 1), Qi i z = z - ε z • u := hQ z
    have hy : y - g y = z - ε z • u := by
      rw [hgy, ← hsum]
      simp only [y]
      rw [Finset.sum_range_succ' (fun i => Qi i (S i)), Finset.sum_range_succ,
        Finset.sum_range_succ' (fun i => Qi i z)]
      rw [hSq, map_zero, map_zero, add_zero]
      have : ∀ i ∈ Finset.range q, Qi (i + 1) (S (i + 1)) - Qi (i + 1) (g (S i)) =
          Qi (i + 1) z := by
        intro i _
        rw [hgS, ← map_sub, sub_sub_cancel]
      rw [show ∀ a b c : M, a + b - c = (a - c) + b from fun a b c => by abel,
        ← Finset.sum_sub_distrib, Finset.sum_congr rfl this]
      simp [S]
    simp only [LinearMap.sub_apply, Module.End.one_apply]
    rw [hy]; abel

end Dvoretzky.Dold
