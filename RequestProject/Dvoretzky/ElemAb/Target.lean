module

public import RequestProject.Dvoretzky.Dold.JoinChains
public import RequestProject.Dvoretzky.ElemAb.Algebra

/-!
# The target: joins of two-point sets with `(ℤ/2)^r` acting by swaps

The `D`-fold join of the two-point set `L = ℤ/2` (written multiplicatively) is a `(D-1)`-sphere.
The group `(ℤ/2)^r` acts on it block by block: the generator `g_q` swaps the two points of block
`k` iff `ε k q = 1`. Over `𝔽₂` its oriented chains are `TChain (ZMod 2) D L`.

* `flipL`: the action of a generator on chains; `bdT_flipL`: it commutes with the boundary;
* `proj v`: the projection of the chains of the `(D+1)`-fold join onto the chains of the `D`-fold
  join, recording the value `v` of the last coordinate; it satisfies the identities required by
  `IsFam.peel`;
* `coeff_mul_prod_eq_zero`, `no_family`: on the `D`-fold join there is no family of level `n ≥ D`
  with defect `1` as soon as every block is moved by some generator (`ε k ≠ 0`).
-/

@[expose] public section

open scoped BigOperators

noncomputable section

namespace Dvoretzky.ElemAb

open Dvoretzky.Dold

/-- The two-point set `ℤ/2`, written multiplicatively. -/
abbrev L2 := Multiplicative (ZMod 2)

variable {D : ℕ}

/-- Signs are trivial over `𝔽₂`. -/
lemma sgnP_zmod2 (s : Smp D L2) (j : Fin D) : (sgnP s j : ZMod 2) = 1 := by
  have h : ∀ n : ℕ, ((-1 : ZMod 2) ^ n) = 1 := by
    intro n
    have : (-1 : ZMod 2) = 1 := by decide
    rw [this, one_pow]
  exact h (pos s j)

/-- Pointwise formula for the boundary over `𝔽₂`. -/
lemma bdT_apply (c : TChain (ZMod 2) D L2) (t : Smp D L2) :
    bdT c t = ∑ j, if t j = none then ∑ l, c (Function.update t j (some l)) else 0 := by
  classical
  have key : ∀ s : Smp D L2, (faceT s : TChain (ZMod 2) D L2) t =
      ∑ j, if t j = none then ∑ l, (Finsupp.single s (1 : ZMod 2)) (Function.update t j (some l))
        else 0 := by
    intro s
    rw [faceT, Finsupp.finset_sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hs : (s j).isSome
    · obtain ⟨l0, hl0⟩ := Option.isSome_iff_exists.1 hs
      rw [if_pos hs, sgnP_zmod2, one_smul, Finsupp.single_apply]
      by_cases ht : Function.update s j none = t
      · subst ht
        rw [if_pos rfl, if_pos (by simp)]
        rw [Finset.sum_eq_single l0]
        · rw [Finsupp.single_apply, if_pos]
          rw [Function.update_idem, ← hl0, Function.update_eq_self]
        · intro l _ hl
          rw [Finsupp.single_apply, if_neg]
          intro e
          have := congrFun e j
          rw [Function.update_idem, Function.update_self, hl0] at this
          exact hl (Option.some_injective _ this).symm
        · simp
      · rw [if_neg ht]
        split_ifs with htj
        · refine (Finset.sum_eq_zero fun l _ => ?_).symm
          rw [Finsupp.single_apply, if_neg]
          intro e
          apply ht
          rw [e, Function.update_idem, Function.update_eq_self_iff.2 htj.symm]
        · rfl
    · rw [if_neg hs]
      split_ifs with htj
      · refine (Finset.sum_eq_zero fun l _ => ?_).symm
        rw [Finsupp.single_apply, if_neg]
        intro e
        apply hs
        rw [e, Function.update_self]; rfl
      · rfl
  have hlin : bdT c = ∑ s ∈ c.support, c s • (faceT s : TChain (ZMod 2) D L2) := by
    conv_lhs => rw [tchain_eq_sum c]
    simp only [map_sum, map_smul, bdT_single, one_smul]
  rw [hlin, Finsupp.finset_sum_apply]
  simp only [Finsupp.smul_apply, smul_eq_mul, key]
  conv_rhs => rw [tchain_eq_sum c]
  simp only [Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs
  · simp only [Finset.mul_sum]
    exact Finset.sum_comm
  · simp

/-! ### The swap action -/

/-- The swap of the blocks `k` with `ε k = 1`, on simplices. -/
def flipS (ε : Fin D → ZMod 2) (s : Smp D L2) : Smp D L2 :=
  fun j => (s j).map (· * Multiplicative.ofAdd (ε j))

lemma flipS_flipS (ε : Fin D → ZMod 2) (s : Smp D L2) : flipS ε (flipS ε s) = s := by
  funext j
  simp only [flipS, Option.map_map]
  cases s j with
  | none => rfl
  | some l =>
    simp only [Option.map_some, Function.comp_apply, mul_assoc, ← ofAdd_add]
    rw [show ε j + ε j = 0 from by rw [← two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul]]
    simp

lemma flipS_injective (ε : Fin D → ZMod 2) : Function.Injective (flipS ε) :=
  Function.LeftInverse.injective (flipS_flipS ε)

/-- The swap action on chains. -/
def flipL (ε : Fin D → ZMod 2) : TChain (ZMod 2) D L2 →ₗ[ZMod 2] TChain (ZMod 2) D L2 :=
  Finsupp.lmapDomain (ZMod 2) (ZMod 2) (flipS ε)

lemma flipL_apply (ε : Fin D → ZMod 2) (c : TChain (ZMod 2) D L2) (t : Smp D L2) :
    flipL ε c t = c (flipS ε t) := by
  conv_lhs => rw [← flipS_flipS ε t]
  exact Finsupp.mapDomain_apply_of_injective (flipS_injective ε) c _

lemma flipS_update (ε : Fin D → ZMod 2) (t : Smp D L2) (j : Fin D) (l : L2) :
    flipS ε (Function.update t j (some l)) =
      Function.update (flipS ε t) j (some (l * Multiplicative.ofAdd (ε j))) := by
  funext i
  by_cases h : i = j
  · subst h; simp [flipS]
  · simp [flipS, Function.update_of_ne h]

lemma bdT_flipL (ε : Fin D → ZMod 2) (c : TChain (ZMod 2) D L2) :
    bdT (flipL ε c) = flipL ε (bdT c) := by
  ext t
  rw [bdT_apply, flipL_apply, bdT_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hn : flipS ε t j = none ↔ t j = none := by simp [flipS]
  by_cases h : t j = none
  · rw [if_pos h, if_pos (hn.2 h)]
    simp only [flipL_apply, flipS_update]
    exact Fintype.sum_equiv (Equiv.mulRight (Multiplicative.ofAdd (ε j))) _ _ (fun l => rfl)
  · rw [if_neg h, if_neg (fun h' => h (hn.1 h'))]

lemma flipL_comm (ε ε' : Fin D → ZMod 2) (c : TChain (ZMod 2) D L2) :
    flipL ε (flipL ε' c) = flipL ε' (flipL ε c) := by
  ext t
  rw [flipL_apply, flipL_apply, flipL_apply, flipL_apply]
  congr 1
  funext j
  simp only [flipS, Option.map_map]
  congr 1
  funext l
  simp [mul_assoc, mul_comm (Multiplicative.ofAdd (ε j))]

lemma flipL_emptyS (ε : Fin D → ZMod 2) :
    flipL ε (Finsupp.single emptyS 1) = Finsupp.single emptyS 1 := by
  ext t
  rw [flipL_apply, Finsupp.single_apply, Finsupp.single_apply]
  congr 1
  apply propext
  constructor
  · intro h; rw [← flipS_flipS ε t, ← h]; rfl
  · intro h; subst h; rfl

/-! ### Projections onto the last coordinate -/

/-- Projection of the chains of the `(D+1)`-fold join onto the chains of the `D`-fold join, at the
value `v` of the last coordinate. -/
def proj (v : Option L2) : TChain (ZMod 2) (D + 1) L2 →ₗ[ZMod 2] TChain (ZMod 2) D L2 :=
  Finsupp.lcomapDomain (fun s : Smp D L2 => (Fin.snoc s v : Smp (D + 1) L2))
    (fun _ _ h => (Fin.snoc_injective2 h).1)

lemma proj_apply (v : Option L2) (c : TChain (ZMod 2) (D + 1) L2) (s : Smp D L2) :
    proj v c s = c (Fin.snoc s v) := rfl

lemma proj_none_bdT (c : TChain (ZMod 2) (D + 1) L2) :
    proj none (bdT c) = bdT (proj none c) +
      (proj (some 1) c + proj (some (Multiplicative.ofAdd 1)) c) := by
  ext s
  rw [Finsupp.add_apply, Finsupp.add_apply, proj_apply, bdT_apply, bdT_apply,
    Fin.sum_univ_castSucc]
  have hl : ∀ l : L2, Function.update (Fin.snoc s none : Smp (D + 1) L2) (Fin.last D) (some l) =
      Fin.snoc s (some l) := fun l => Fin.update_snoc_last _ _ _
  have hc : ∀ (j : Fin D) (l : L2), Function.update (Fin.snoc s none : Smp (D + 1) L2) j.castSucc
      (some l) = Fin.snoc (Function.update s j (some l)) none := fun j l =>
    (Fin.snoc_update _ _ _ _).symm
  simp only [Fin.snoc_last, if_true, Fin.snoc_castSucc, proj_apply, hl, hc]
  congr 1
  have : (Finset.univ : Finset L2) = {1, Multiplicative.ofAdd 1} := by decide
  rw [this, Finset.sum_pair (by decide)]

lemma proj_some_bdT (l : L2) (c : TChain (ZMod 2) (D + 1) L2) :
    proj (some l) (bdT c) = bdT (proj (some l) c) := by
  ext s
  rw [proj_apply, bdT_apply, bdT_apply, Fin.sum_univ_castSucc]
  have hc : ∀ (j : Fin D) (l' : L2), Function.update (Fin.snoc s (some l) : Smp (D + 1) L2)
      j.castSucc (some l') = Fin.snoc (Function.update s j (some l')) (some l) := fun j l' =>
    (Fin.snoc_update _ _ _ _).symm
  simp only [Fin.snoc_last, reduceCtorEq, if_false, add_zero, Fin.snoc_castSucc, proj_apply, hc]

lemma flipS_snoc (ε : Fin (D + 1) → ZMod 2) (s : Smp D L2) (v : Option L2) :
    flipS ε (Fin.snoc s v : Smp (D + 1) L2) =
      Fin.snoc (flipS (Fin.init ε) s) (v.map (· * Multiplicative.ofAdd (ε (Fin.last D)))) := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [flipS]
  · simp [flipS, Fin.init]

lemma proj_flipL (ε : Fin (D + 1) → ZMod 2) (v : Option L2) (c : TChain (ZMod 2) (D + 1) L2) :
    proj v (flipL ε c) =
      flipL (Fin.init ε) (proj (v.map (· * Multiplicative.ofAdd (ε (Fin.last D)))) c) := by
  ext s
  rw [proj_apply, flipL_apply, flipL_apply, proj_apply, flipS_snoc]

lemma proj_emptyS_none :
    proj none (Finsupp.single (emptyS : Smp (D + 1) L2) (1 : ZMod 2)) = Finsupp.single emptyS 1 := by
  ext s
  rw [proj_apply, Finsupp.single_apply, Finsupp.single_apply]
  congr 1
  apply propext
  constructor
  · intro h; funext j; have := congrFun h j.castSucc; simpa [emptyS] using this
  · intro h; subst h; funext j; refine Fin.lastCases ?_ (fun i => ?_) j <;> simp [emptyS]

lemma proj_emptyS_some (l : L2) :
    proj (some l) (Finsupp.single (emptyS : Smp (D + 1) L2) (1 : ZMod 2)) = 0 := by
  ext s
  rw [proj_apply, Finsupp.single_apply, if_neg]
  · rfl
  · intro h; have := congrFun h (Fin.last D); simp [emptyS] at this

/-! ### No family on a join of two-point sets -/

variable {r : ℕ}

/-- The target data: `d = ∂`, `act q = ` swap by generator `q`, `e = ∅`. -/
abbrev tgtFam (D : ℕ) (ε : Fin D → Fin r → ZMod 2) (n : ℕ) (R : (Fin r →₀ ℕ) → ZMod 2)
    (β : (Fin r →₀ ℕ) → TChain (ZMod 2) D L2) : Prop :=
  IsFam bdT (fun q => flipL (fun k => ε k q)) (Finsupp.single emptyS 1) n R β

lemma zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · left; rfl
  · right; rfl

open MvPolynomial in
/-- A family on the `D`-fold join with defect `P` forces `P · ∏ₖ (∑_q ε_{k q} U_q)` to vanish in
degrees `≤ n`. -/
theorem coeff_mul_prod_eq_zero : ∀ (D : ℕ) (ε : Fin D → Fin r → ZMod 2) (n : ℕ)
    (P : MvPolynomial (Fin r) (ZMod 2)) (β : (Fin r →₀ ℕ) → TChain (ZMod 2) D L2),
    tgtFam D ε n (fun J => coeff J P) β →
      ∀ I : Fin r →₀ ℕ, Finsupp.degree I ≤ n → coeff I (P * ∏ k, linForm (ε k)) = 0
  | 0, ε, n, P, β, hβ, I, hI => by
    have hbd : (bdT : TChain (ZMod 2) 0 L2 →ₗ[ZMod 2] TChain (ZMod 2) 0 L2) = 0 := by
      refine LinearMap.ext fun c => Finsupp.ext fun t => ?_
      rw [bdT_apply]; simp
    have hfl : ∀ ε' : Fin 0 → ZMod 2,
        (flipL ε' : TChain (ZMod 2) 0 L2 →ₗ[ZMod 2] TChain (ZMod 2) 0 L2) = LinearMap.id := by
      intro ε'
      refine LinearMap.ext fun c => Finsupp.ext fun t => ?_
      rw [flipL_apply]
      congr 1
      funext j; exact j.elim0
    have hβ' : IsFam (0 : TChain (ZMod 2) 0 L2 →ₗ[ZMod 2] TChain (ZMod 2) 0 L2)
        (fun _ => LinearMap.id) (Finsupp.single emptyS 1) n (fun J => coeff J P) β := by
      have := hβ
      simp only [tgtFam, hbd, hfl] at this
      exact this
    rw [Finset.univ_eq_empty, Finset.prod_empty, mul_one]
    exact IsFam.defect_eq_zero_of_trivial (Finsupp.single_ne_zero.2 one_ne_zero) hβ' hI
  | D + 1, ε, n, P, β, hβ, I, hI => by
    have hpeel := IsFam.peel (d := bdT) (act := fun q => flipL (fun k => Fin.init ε k q))
      (e := Finsupp.single emptyS 1)
      (proj none) (proj (some 1)) (proj (some (Multiplicative.ofAdd 1))) (ε (Fin.last D))
      (fun q x => bdT_flipL _ x) (fun q q' x => flipL_comm _ _ x) (fun q => flipL_emptyS _)
      proj_none_bdT (proj_some_bdT 1)
      (fun q c => by rw [proj_flipL]; rfl)
      (fun q c => by
        rw [proj_flipL]
        rcases zmod2_cases (ε (Fin.last D) q) with h | h
        · simp only [h, Option.map_some, ofAdd_zero, mul_one, zero_smul, add_zero]; rfl
        · simp only [h, Option.map_some, one_mul, one_smul]
          rw [← add_assoc, two_smul_eq_zero, zero_add]; rfl)
      proj_emptyS_none (proj_emptyS_some 1) hβ
    have hdef : peelDefect (ε (Fin.last D)) (fun J => coeff J P) =
        fun J => coeff J (linForm (ε (Fin.last D)) * P) := by
      funext J; rw [coeff_linForm_mul]
    rw [hdef] at hpeel
    have := coeff_mul_prod_eq_zero D (Fin.init ε) n _ _ hpeel I hI
    rw [Fin.prod_univ_castSucc]
    rw [show P * ((∏ k : Fin D, linForm (ε k.castSucc)) * linForm (ε (Fin.last D))) =
      linForm (ε (Fin.last D)) * P * ∏ k : Fin D, linForm (Fin.init ε k) from by
        simp only [Fin.init]; ring]
    exact this

open MvPolynomial in
/-- **No family on a join of two-point sets.** If every block of the `D`-fold join of two-point
sets is swapped by some generator, there is no family of level `n ≥ D` with defect `1`. -/
theorem no_family (ε : Fin D → Fin r → ZMod 2) (hε : ∀ k, ε k ≠ 0) {n : ℕ} (hn : D ≤ n)
    (β : (Fin r →₀ ℕ) → TChain (ZMod 2) D L2)
    (hβ : tgtFam D ε n (fun J => if J = 0 then 1 else 0) β) : False := by
  classical
  have h1 : (fun J : Fin r →₀ ℕ => if J = 0 then (1 : ZMod 2) else 0) =
      fun J => coeff J (1 : MvPolynomial (Fin r) (ZMod 2)) := by
    funext J
    rw [coeff_def, MvPolynomial.coeff_one]
    split_ifs <;> aesop
  rw [h1] at hβ
  obtain ⟨I, hIdeg, hI⟩ := exists_coeff_prod_linForm_ne_zero ε hε
  have := coeff_mul_prod_eq_zero D ε n 1 β hβ I (hIdeg ▸ hn)
  rw [one_mul] at this
  exact hI this

end Dvoretzky.ElemAb
