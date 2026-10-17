module

public import RequestProject.Dvoretzky.Statement
public import RequestProject.Dvoretzky.Stage
public import RequestProject.Dvoretzky.Signed

/-!
# Proof of Theorem 1 (Gromov–Milman conjecture), assuming the Borsuk–Ulam property

We combine the topological input `TwoGroupBorsukUlam` (applied to the group of signed
permutations attached to the wreath-product `2`-group of `Stage.exists_good_stage`) with the
averaging/combinatorial construction of `Stage.lean`.
-/

@[expose] public section

open scoped BigOperators
open MvPolynomial

noncomputable section

set_option synthInstance.maxHeartbeats 200000

namespace Dvoretzky

lemma sum_units_pow (n : ℕ) : ∑ u : ℤˣ, ((u : ℤ) : ℝ) ^ n = 1 + (-1) ^ n := by
  rw [UnitsInt.univ, Finset.sum_pair (by decide)]
  simp

lemma sum_units_prod_pow {X : Type} [Fintype X] [DecidableEq X] (α : X → ℕ) :
    ∑ ε : X → ℤˣ, ∏ x, ((ε x : ℤ) : ℝ) ^ α x = ∏ x, ((1 : ℝ) + (-1) ^ α x) := by
  rw [← Fintype.prod_sum (fun x (u : ℤˣ) => ((u : ℤ) : ℝ) ^ α x)]
  exact Finset.prod_congr rfl fun x _ => sum_units_pow _

lemma eval_aeval_eq {σ τ : Type} (f : MvPolynomial σ ℝ) (g : σ → MvPolynomial τ ℝ) (y : τ → ℝ) :
    eval y (aeval g f) = eval (fun i => eval y (g i)) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
  | mul_X p i hp => rw [map_mul, map_mul, hp, aeval_X, map_mul, eval_X]

variable {k : ℕ}

/-- The averaged contribution of one monomial is radial. -/
lemma avg_monomial (S : Stage k) (δ : ℕ)
    (hgood : ∀ β : S.X → ℕ, ∑ x, β x ≤ δ → IsRadial (2 * ∑ x, β x) (S.orb β))
    (α : S.X → ℕ) (hα : ∑ x, α x = 2 * δ) :
    ∃ C : ℝ, ∀ z, ∑ ε : S.X → ℤˣ, ∑ p : S.P,
      ∏ x, (((ε x : ℤ) : ℝ) * S.l (S.π p x) z) ^ (α x) = C * ‖z‖ ^ (2 * δ) := by
  classical
  have key : ∀ z, ∑ ε : S.X → ℤˣ, ∑ p : S.P, ∏ x, (((ε x : ℤ) : ℝ) * S.l (S.π p x) z) ^ (α x) =
      (∏ x, ((1 : ℝ) + (-1) ^ α x)) * ∑ p : S.P, ∏ x, (S.l (S.π p x) z) ^ (α x) := by
    intro z
    simp only [mul_pow, Finset.prod_mul_distrib]
    rw [← sum_units_prod_pow, Finset.sum_mul_sum]
  by_cases hev : ∀ x, Even (α x)
  · let β : S.X → ℕ := fun x => α x / 2
    have hαβ : ∀ x, α x = 2 * β x := fun x => (Nat.two_mul_div_two_of_even (hev x)).symm
    have hβ : ∑ x, β x = δ := by
      have : 2 * ∑ x, β x = 2 * δ := by rw [Finset.mul_sum, ← hα]; simp [hαβ]
      omega
    obtain ⟨c, hc⟩ := hgood β hβ.le
    refine ⟨(∏ x, ((1 : ℝ) + (-1) ^ α x)) * c, fun z => ?_⟩
    rw [key, mul_assoc]
    congr 1
    have := hc z
    rw [hβ] at this
    rw [← this]
    simp only [Stage.orb, hαβ]
  · push_neg at hev
    obtain ⟨x0, hx0⟩ := hev
    refine ⟨0, fun z => ?_⟩
    rw [key, zero_mul]
    rw [Finset.prod_eq_zero (Finset.mem_univ x0)]
    · ring
    · rw [Nat.not_even_iff_odd] at hx0
      rw [hx0.neg_one_pow]
      ring

/-- The core of the proof of **Theorem 1**: given a good stage `S` of the combinatorial
construction and, for large `n`, isometric embeddings `L : ℝ^X → ℝⁿ` making every polynomial
function of degree `≤ 2δ` invariant under the signed permutation group of `S.H`, every
homogeneous polynomial of degree `2δ` in `n` variables is radial on some `k`-subspace. -/
theorem gromovMilman_of_stage {δ : ℕ} (hδ0 : 1 ≤ δ) (S : Stage k)
    (hgood : ∀ β : S.X → ℕ, ∑ x, β x ≤ δ → IsRadial (2 * ∑ x, β x) (S.orb β))
    (x0 : S.X) (hx0 : S.l x0 ≠ 0) {N : ℕ}
    (hN : ∀ n ≥ N, ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ, IsPolyFun (2 * δ) φ →
      ∃ L : EuclideanSpace ℝ S.X →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
        ∀ g ∈ signedGroup S.H, ∀ y, φ (L (g y)) = φ (L y)) :
    ∀ n ≥ N, ∀ f : MvPolynomial (Fin n) ℝ, f.IsHomogeneous (2 * δ) →
      ∃ V : Submodule ℝ (EuclideanSpace ℝ (Fin n)), Module.finrank ℝ V = k ∧
        ∃ c : ℝ, ∀ v ∈ V, MvPolynomial.eval (fun i => v i) f = c * ‖v‖ ^ (2 * δ) := by
  classical
  intro n hn f hf
  set φ : EuclideanSpace ℝ (Fin n) → ℝ := fun v => eval (fun i => v i) f with hφ_def
  have hφpoly : IsPolyFun (2 * δ) φ := ⟨f, hf.totalDegree_le, fun z => rfl⟩
  obtain ⟨L, hinv0⟩ := hN n hn φ hφpoly
  set q : EuclideanSpace ℝ S.X → ℝ := fun y => φ (L y) with hq_def
  have hinv : ∀ g ∈ signedGroup S.H, ∀ y, q (g y) = q y := hinv0
  -- a homogeneous polynomial representing `q`
  let lin : Fin n → MvPolynomial S.X ℝ :=
    fun i => ∑ x, C ((L (EuclideanSpace.single x 1)) i) * X x
  let Q : MvPolynomial S.X ℝ := aeval lin f
  have hQhom : Q.IsHomogeneous (2 * δ) := by
    have := hf.aeval lin (fun i => IsHomogeneous.sum _ _ _ fun x _ => isHomogeneous_C_mul_X _ _)
    simpa [Q] using this
  have hQeval : ∀ y, q y = eval (fun x => y x) Q := by
    intro y
    have hfun : (fun i => (L y) i) = (fun i => eval (fun x => y x) (lin i)) := by
      funext i
      simp only [lin, map_sum, map_mul, eval_C, eval_X]
      conv_lhs => rw [← (EuclideanSpace.basisFun S.X ℝ).sum_repr y]
      simp [map_sum, mul_comm]
    simp only [hq_def, hφ_def, Q, eval_aeval_eq]
    rw [hfun]
  -- the linear map `Λ : ℝ^k → ℝ^X`, `z ↦ (l_x z)_x`
  let Λ : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ S.X :=
    (EuclideanSpace.equiv S.X ℝ).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun x => S.l x)
  have hΛ : ∀ z x, Λ z x = S.l x z := fun z x => rfl
  -- Claim A: `q ∘ Λ` is radial
  obtain ⟨C0, hC0⟩ : ∃ C0 : ℝ, ∀ z, q (Λ z) = C0 * ‖z‖ ^ (2 * δ) := by
    have hdeg : ∀ α ∈ Q.support, ∑ x, α x = 2 * δ := by
      intro α hα
      have := hQhom (mem_support_iff.1 hα)
      rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at this
      simpa using this
    choose Cα hCα using fun α : Q.support => avg_monomial S δ hgood α (hdeg α α.2)
    set M := Fintype.card ((S.X → ℤˣ) × S.P) with hM
    have hMpos : (0 : ℝ) < M := by exact_mod_cast Fintype.card_pos
    refine ⟨(∑ α : Q.support, Q.coeff α.1 * Cα α) / M, fun z => ?_⟩
    have havg : (M : ℝ) * q (Λ z) =
        ∑ ε : S.X → ℤˣ, ∑ p : S.P, q (signedPerm ε (S.π p) (Λ z)) := by
      simp only [hinv _ (signedPerm_mem S.H _ (S.hπ _)), Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, hM, Fintype.card_prod]
      push_cast
      ring
    have hexp : ∀ ε p, q (signedPerm ε (S.π p) (Λ z)) =
        ∑ α : Q.support, Q.coeff α.1 *
          ∏ x, (((ε x : ℤ) : ℝ) * S.l (S.π p x) z) ^ (α.1 x) := by
      intro ε p
      rw [hQeval, eval_eq', ← Finset.sum_coe_sort]
      rfl
    rw [div_mul_eq_mul_div, eq_div_iff hMpos.ne', mul_comm, havg]
    simp only [hexp]
    have hswap : ∀ F : (S.X → ℤˣ) → S.P → Q.support → ℝ,
        ∑ ε, ∑ p, ∑ α, F ε p α = ∑ α, ∑ ε, ∑ p, F ε p α := by
      intro F
      calc ∑ ε, ∑ p, ∑ α, F ε p α = ∑ ε, ∑ α, ∑ p, F ε p α :=
            Finset.sum_congr rfl fun ε _ => Finset.sum_comm
        _ = ∑ α, ∑ ε, ∑ p, F ε p α := Finset.sum_comm
    rw [hswap, Finset.sum_mul]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [mul_assoc, ← hCα α z, Finset.mul_sum]
    simp only [Finset.mul_sum]
  -- Claim B: `‖Λ z‖² = c0 ‖z‖²` with `c0 > 0`
  obtain ⟨c0, hc0pos, hc0⟩ : ∃ c0 : ℝ, 0 < c0 ∧ ∀ z, ‖Λ z‖ ^ 2 = c0 * ‖z‖ ^ 2 := by
    have hsingle : ∀ x, IsRadial 2 (fun z => ∑ p : S.P, (S.l (S.π p x) z) ^ 2) := by
      intro x
      have hβ : ∑ y, (Pi.single x 1 : S.X → ℕ) y = 1 := by simp
      obtain ⟨c, hc⟩ := hgood (Pi.single x 1) (by rw [hβ]; exact hδ0)
      refine ⟨c, fun z => ?_⟩
      have := hc z
      rw [hβ] at this
      rw [← this]
      simp only [Stage.orb]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.prod_eq_single x]
      · simp
      · intro y _ hy
        simp [hy]
      · simp
    choose c hc using hsingle
    have hsq : ∀ z, ‖Λ z‖ ^ 2 = ∑ x, (S.l x z) ^ 2 := by
      intro z
      rw [EuclideanSpace.norm_sq_eq]
      simp [hΛ]
    have hP : (0 : ℝ) < Fintype.card S.P := by exact_mod_cast Fintype.card_pos
    have hkey : ∀ z, (Fintype.card S.P : ℝ) * ∑ x, (S.l x z) ^ 2 = (∑ x, c x) * ‖z‖ ^ 2 := by
      intro z
      rw [Finset.sum_mul]
      simp only [← hc]
      rw [Finset.sum_comm]
      rw [← nsmul_eq_mul, ← Finset.card_univ, ← Finset.sum_const]
      refine Finset.sum_congr rfl fun p _ => ?_
      exact (Equiv.sum_comp (S.π p) (fun x => (S.l x z) ^ 2)).symm
    refine ⟨(∑ x, c x) / Fintype.card S.P, ?_, fun z => ?_⟩
    · obtain ⟨v, hv⟩ : ∃ v, S.l x0 v ≠ 0 := by
        by_contra h
        push_neg at h
        exact hx0 (ContinuousLinearMap.ext h)
      have h1 : 0 < ∑ x, (S.l x v) ^ 2 :=
        lt_of_lt_of_le (by positivity)
          (Finset.single_le_sum (f := fun x => (S.l x v) ^ 2) (fun _ _ => sq_nonneg _)
            (Finset.mem_univ x0))
      have h2 := hkey v
      have h3 : 0 < (∑ x, c x) * ‖v‖ ^ 2 := by rw [← h2]; positivity
      have h4 : 0 < ∑ x, c x := pos_of_mul_pos_left h3 (by positivity)
      positivity
    · rw [hsq, div_mul_eq_mul_div, eq_div_iff hP.ne', mul_comm, hkey]
  -- the subspace
  let T : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    L.toLinearMap ∘ₗ Λ.toLinearMap
  have hTnorm : ∀ z, ‖T z‖ ^ 2 = c0 * ‖z‖ ^ 2 := by
    intro z
    show ‖L (Λ z)‖ ^ 2 = _
    rw [LinearIsometry.norm_map, hc0]
  have hTinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    have h1 := hTnorm z
    rw [hz, norm_zero, zero_pow two_ne_zero] at h1
    have h2 : ‖z‖ ^ 2 = 0 := (mul_eq_zero.1 h1.symm).resolve_left hc0pos.ne'
    exact norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h2)
  refine ⟨LinearMap.range T, ?_, C0 / c0 ^ δ, ?_⟩
  · rw [LinearMap.finrank_range_of_inj hTinj, finrank_euclideanSpace_fin]
  · rintro v ⟨z, rfl⟩
    have hv : eval (fun i => (T z) i) f = q (Λ z) := rfl
    rw [hv, hC0, pow_mul, pow_mul, hTnorm, mul_pow]
    field_simp

/-- **Theorem 1** (Gromov–Milman conjecture, Dol'nikov–Karasev), assuming the Borsuk–Ulam
property of finite `2`-groups (Lemma 1 of the paper). -/
theorem gromovMilman (hBU : TwoGroupBorsukUlam) (d k : ℕ) (hd : Even d) (hd0 : 0 < d) :
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
  obtain ⟨S, hgood, ⟨x0, hx0⟩⟩ := Stage.exists_good_stage hk δ
  obtain ⟨N, hN⟩ := hBU S.X (signedGroup S.H) (signedGroup_finite _)
    (signedGroup_isPGroup _ S.hH) (grid S.X (2 * δ))
  refine ⟨N, gromovMilman_of_stage hδ0 S hgood x0 hx0 fun n hn φ hφpoly => ?_⟩
  obtain ⟨L, hL⟩ := hN n hn φ hφpoly.continuous
  refine ⟨L, fun g hg => ?_⟩
  have hqpoly : IsPolyFun (2 * δ) (fun y => φ (L y)) := hφpoly.comp_clm L.toContinuousLinearMap
  have h1 : IsPolyFun (2 * δ) (fun y => φ (L (g y)) - φ (L y)) :=
    (hqpoly.comp_clm g.toContinuousLinearEquiv.toContinuousLinearMap).sub hqpoly
  exact fun y => sub_eq_zero.1
    (h1.eq_zero_of_grid (fun z hz => sub_eq_zero.2 (hL g hg z hz)) y)

end Dvoretzky
