module

public import RequestProject.Dvoretzky.OrbitCollapse
public import RequestProject.Dvoretzky.Dold.Main

/-!
# The orbit collapse property for groups of prime order

Using Dold's theorem `Dold.dold_join` we prove `JoinOrbitCollapse G` for every group of prime
order `p` (`joinOrbitCollapse_of_card_prime`), unconditionally.

Given a continuous `F` from the join of `ℤ/p` to `ℝ^ι` which is not constant on any orbit, put
`y_h(x) = F(h·x)` and, for `i ∈ ι` and a proper nonempty `A ⊆ G`,
`w_{i,A}(x) = ∏_{a ∈ A} ∏_{b ∉ A} max(0, y_a(x)_i - y_b(x)_i)`
(positive iff `A` is a strict "upper set" of the values `y_·(x)_i`). The weights
`w_{i, A·h}(x)` at the labels `h` define, after normalisation, an equivariant map to the join with
`|ι| · 2^p + 1` coordinates, contradicting Dold's theorem.
-/

@[expose] public section

open scoped BigOperators

noncomputable section

namespace Dvoretzky

namespace PrimeOrbit

variable {G : Type} [Group G] [Fintype G] [DecidableEq G] {ι : Type} [Fintype ι] {N : ℕ}
  (F : (Fin N → G → ℝ) → (ι → ℝ))

/-- Right translation of a finite subset of `G`. -/
def tr (A : Finset G) (h : G) : Finset G := A.map (Equiv.mulRight h).toEmbedding

omit [Fintype G] [DecidableEq G] in
lemma tr_tr (A : Finset G) (h g : G) : tr (tr A h) g = tr A (h * g) := by
  ext a
  simp only [tr, Finset.map_map, Finset.mem_map, Function.Embedding.trans_apply,
    Equiv.coe_toEmbedding, Equiv.coe_mulRight]
  constructor
  · rintro ⟨b, hb, rfl⟩; exact ⟨b, hb, by group⟩
  · rintro ⟨b, hb, rfl⟩; exact ⟨b, hb, by group⟩

omit [Fintype G] [DecidableEq G] in
@[simp] lemma tr_one (A : Finset G) : tr A 1 = A := by
  ext a; simp [tr]; rfl

omit [Fintype G] [DecidableEq G] in
lemma card_tr (A : Finset G) (h : G) : (tr A h).card = A.card := by simp [tr]

omit [Fintype G] [DecidableEq G] in
lemma tr_nonempty_iff (A : Finset G) (h : G) : (tr A h).Nonempty ↔ A.Nonempty := by
  simp [tr]

omit [DecidableEq G] in
lemma tr_eq_univ_iff (A : Finset G) (h : G) : tr A h = Finset.univ ↔ A = Finset.univ := by
  rw [← Finset.card_eq_iff_eq_univ, ← Finset.card_eq_iff_eq_univ, card_tr]

/-- The values `y_h(x) = F(h · x)`. -/
def yv (x : Fin N → G → ℝ) (h : G) (i : ι) : ℝ := F (joinAct h x) i

/-- The weight of the subset `A` in the coordinate `i`. -/
def wt (x : Fin N → G → ℝ) (i : ι) (A : Finset G) : ℝ :=
  if A.Nonempty ∧ A ≠ Finset.univ then
    ∏ a ∈ A, ∏ b ∈ Finset.univ \ A, max 0 (yv F x a i - yv F x b i)
  else 0

omit [Fintype ι] in
lemma wt_nonneg (x : Fin N → G → ℝ) (i : ι) (A : Finset G) : 0 ≤ wt F x i A := by
  unfold wt
  split_ifs
  · exact Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => le_max_left _ _
  · exact le_rfl

omit [Fintype G] [DecidableEq G] [Fintype ι] in
lemma yv_joinAct (x : Fin N → G → ℝ) (g a : G) (i : ι) :
    yv F (joinAct g x) a i = yv F x (a * g) i := by
  simp [yv, joinAct_joinAct]

lemma sdiff_tr (A : Finset G) (g : G) : Finset.univ \ tr A g = tr (Finset.univ \ A) g := by
  simp [tr, Finset.map_sdiff]

omit [Fintype ι] in
lemma wt_joinAct (x : Fin N → G → ℝ) (g : G) (i : ι) (A : Finset G) :
    wt F (joinAct g x) i A = wt F x i (tr A g) := by
  unfold wt
  by_cases hc : A.Nonempty ∧ A ≠ Finset.univ
  · rw [if_pos hc, if_pos ⟨(tr_nonempty_iff A g).2 hc.1, fun h => hc.2 ((tr_eq_univ_iff A g).1 h)⟩]
    rw [sdiff_tr, tr, Finset.prod_map]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [tr, Finset.prod_map]
    refine Finset.prod_congr rfl fun b _ => ?_
    simp [yv_joinAct]
  · rw [if_neg hc, if_neg fun h => hc ⟨(tr_nonempty_iff A g).1 h.1,
      fun h' => h.2 ((tr_eq_univ_iff A g).2 h')⟩]

omit [Fintype ι] in
lemma upper_of_wt_pos {x : Fin N → G → ℝ} {i : ι} {A : Finset G} (hA : 0 < wt F x i A) :
    A.Nonempty ∧ A ≠ Finset.univ ∧ ∀ a ∈ A, ∀ b ∉ A, yv F x b i < yv F x a i := by
  unfold wt at hA
  split_ifs at hA with hc
  · refine ⟨hc.1, hc.2, fun a ha b hb => ?_⟩
    by_contra hle
    push_neg at hle
    have h0 : max 0 (yv F x a i - yv F x b i) = 0 := max_eq_left (by linarith)
    have : ∏ a ∈ A, ∏ b ∈ Finset.univ \ A, max 0 (yv F x a i - yv F x b i) = 0 :=
      Finset.prod_eq_zero ha (Finset.prod_eq_zero (by simpa using hb) h0)
    linarith
  · exact absurd hA (lt_irrefl 0)

omit [Fintype ι] in
lemma eq_of_wt_pos {x : Fin N → G → ℝ} {i : ι} {A B : Finset G} (hA : 0 < wt F x i A)
    (hB : 0 < wt F x i B) (hc : A.card = B.card) : A = B := by
  obtain ⟨-, -, hA'⟩ := upper_of_wt_pos F hA
  obtain ⟨-, -, hB'⟩ := upper_of_wt_pos F hB
  refine Finset.eq_of_subset_of_card_le (fun a ha => ?_) hc.ge
  by_contra haB
  have hBA : ¬ B ⊆ A := fun hsub => haB ((Finset.eq_of_subset_of_card_le hsub hc.le) ▸ ha)
  obtain ⟨b, hb, hbA⟩ := Finset.not_subset.1 hBA
  have h1 := hA' a ha b hbA
  have h2 := hB' b hb a haB
  linarith

omit [Fintype G] in
/-- In a group of prime order a proper nonempty subset has trivial stabiliser. -/
lemma eq_one_of_tr_eq [Fintype G] {q : ℕ} [Fact q.Prime] (hq : Nat.card G = q) {A : Finset G}
    (hne : A.Nonempty) (hnu : A ≠ Finset.univ) {h : G} (hA : tr A h = A) : h = 1 := by
  by_contra h1
  have htop := zpowers_eq_top_of_prime_card hq h1
  have hstep : ∀ a ∈ A, a * h ∈ A := fun a ha => by
    rw [← hA]; exact Finset.mem_map.2 ⟨a, ha, rfl⟩
  have hpow : ∀ n : ℕ, ∀ a ∈ A, a * h ^ n ∈ A := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => intro a ha; rw [pow_succ, ← mul_assoc]; exact hstep _ (ih a ha)
  obtain ⟨a0, ha0⟩ := hne
  apply hnu
  refine Finset.eq_univ_of_forall fun b => ?_
  have hmem : a0⁻¹ * b ∈ Submonoid.powers h := by
    rw [mem_powers_iff_mem_zpowers, htop]; exact Subgroup.mem_top _
  obtain ⟨n, hn⟩ := hmem
  have := hpow n a0 ha0
  simp only at hn
  rwa [hn, mul_inv_cancel_left] at this

/-- The index set of the coordinates of the target join. -/
abbrev Idx (G ι : Type) := ι × Finset G

/-- Raw weights on the target join with `|ι × 2^G| + 1` coordinates (the last one is unused). -/
def W (x : Fin N → G → ℝ) (j : Fin (Fintype.card (Idx G ι) + 1)) (h : G) : ℝ :=
  if hj : (j : ℕ) < Fintype.card (Idx G ι) then
    wt F x ((Fintype.equivFin (Idx G ι)).symm ⟨j, hj⟩).1
      (tr ((Fintype.equivFin (Idx G ι)).symm ⟨j, hj⟩).2 h)
  else 0

/-- Total weight. -/
def T (x : Fin N → G → ℝ) : ℝ := ∑ j, ∑ h, W F x j h

/-- The normalised map to the target join. -/
def Phi (x : Fin N → G → ℝ) : Fin (Fintype.card (Idx G ι) + 1) → G → ℝ :=
  fun j h => W F x j h / T F x

lemma W_nonneg (x : Fin N → G → ℝ) (j) (h : G) : 0 ≤ W F x j h := by
  unfold W
  split_ifs
  · exact wt_nonneg F x _ _
  · exact le_rfl

lemma W_joinAct (x : Fin N → G → ℝ) (g : G) (j) (h : G) :
    W F (joinAct g x) j h = W F x j (h * g) := by
  unfold W
  split_ifs
  · rw [wt_joinAct, tr_tr]
  · rfl

lemma T_joinAct (x : Fin N → G → ℝ) (g : G) : T F (joinAct g x) = T F x := by
  unfold T
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [W_joinAct]
  exact Fintype.sum_equiv (Equiv.mulRight g) _ _ fun h => rfl

lemma Phi_joinAct (x : Fin N → G → ℝ) (g : G) : Phi F (joinAct g x) = joinAct g (Phi F x) := by
  funext j h
  simp [Phi, joinAct, W_joinAct, T_joinAct]

lemma T_pos {x : Fin N → G → ℝ} {g : G} (hg : F (joinAct g x) ≠ F x) : 0 < T F x := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, F (joinAct g x) i ≠ F x i := by
    by_contra hc; push_neg at hc; exact hg (funext hc)
  obtain ⟨hm, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun h => yv F x h i)
    Finset.univ_nonempty
  set A : Finset G := Finset.univ.filter fun h => yv F x h i = yv F x hm i with hA
  have hAne : A.Nonempty := ⟨hm, by simp [hA]⟩
  have hAu : A ≠ Finset.univ := by
    intro hu
    have h1 : yv F x 1 i = yv F x hm i :=
      (Finset.mem_filter.1 (show (1 : G) ∈ A from hu.symm ▸ Finset.mem_univ _)).2
    have hg' : yv F x g i = yv F x hm i :=
      (Finset.mem_filter.1 (show g ∈ A from hu.symm ▸ Finset.mem_univ _)).2
    unfold yv at h1 hg'
    rw [joinAct_one] at h1
    exact hi (hg'.trans h1.symm)
  have hwt : 0 < wt F x i A := by
    unfold wt
    rw [if_pos ⟨hAne, hAu⟩]
    refine Finset.prod_pos fun a ha => Finset.prod_pos fun b hb => ?_
    simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff] at ha hb
    have := hmax b (Finset.mem_univ _)
    have hlt : yv F x b i < yv F x a i := by rw [ha]; exact lt_of_le_of_ne this hb
    exact lt_max_of_lt_right (by linarith)
  set k := Fintype.equivFin (Idx G ι) (i, A) with hk
  have hj : ((Fin.castSucc k : Fin (Fintype.card (Idx G ι) + 1)) : ℕ) < Fintype.card (Idx G ι) :=
    k.isLt
  have hW : W F x (Fin.castSucc k) 1 = wt F x i A := by
    unfold W
    rw [dif_pos hj]
    have : (⟨(Fin.castSucc k : ℕ), hj⟩ : Fin (Fintype.card (Idx G ι))) = k := Fin.ext rfl
    rw [this, hk, Equiv.symm_apply_apply, tr_one]
  calc 0 < W F x (Fin.castSucc k) 1 := hW ▸ hwt
    _ ≤ ∑ h, W F x (Fin.castSucc k) h :=
        Finset.single_le_sum (fun h _ => W_nonneg F x _ h) (Finset.mem_univ _)
    _ ≤ T F x := Finset.single_le_sum (f := fun j => ∑ h, W F x j h)
        (fun j _ => Finset.sum_nonneg fun h _ => W_nonneg F x j h) (Finset.mem_univ _)

lemma Phi_mem {q : ℕ} [Fact q.Prime] (hq : Nat.card G = q) {x : Fin N → G → ℝ} (hT : 0 < T F x) :
    Phi F x ∈ GroupJoin G (Fintype.card (Idx G ι) + 1) := by
  refine ⟨fun j h => div_nonneg (W_nonneg F x j h) hT.le, fun j h h' a b => ?_, ?_⟩
  · simp only [Phi, ne_eq, div_eq_zero_iff, not_or] at a b
    unfold W at a b
    split_ifs at a b with hj
    · set c := (Fintype.equivFin (Idx G ι)).symm ⟨j, hj⟩
      have ha := lt_of_le_of_ne (wt_nonneg F x _ _) (Ne.symm a.1)
      have hb := lt_of_le_of_ne (wt_nonneg F x _ _) (Ne.symm b.1)
      have heq := eq_of_wt_pos F ha hb (by rw [card_tr, card_tr])
      obtain ⟨hne, hnu, -⟩ := upper_of_wt_pos F ha
      have : tr (tr c.2 h) (h⁻¹ * h') = tr c.2 h := by rw [tr_tr, mul_inv_cancel_left, heq]
      have h1 := eq_one_of_tr_eq hq hne hnu this
      rw [inv_mul_eq_one] at h1
      exact h1
    · exact absurd rfl a.1
  · simp only [Phi, ← Finset.sum_div]
    exact div_self hT.ne'

omit [DecidableEq G] [Fintype ι] in
lemma continuousOn_yv (hF : ContinuousOn F (GroupJoin G N)) (a : G) (i : ι) :
    ContinuousOn (fun x => yv F x a i) (GroupJoin G N) :=
  (continuous_apply i).comp_continuousOn
    (hF.comp (continuous_joinAct a).continuousOn fun _ hx => joinAct_mem a hx)

lemma continuousOn_W (hF : ContinuousOn F (GroupJoin G N)) (j) (h : G) :
    ContinuousOn (fun x => W F x j h) (GroupJoin G N) := by
  by_cases hj : (j : ℕ) < Fintype.card (Idx G ι)
  · simp only [W, dif_pos hj]
    unfold wt
    split_ifs
    · refine continuousOn_finset_prod _ fun a _ => continuousOn_finset_prod _ fun b _ => ?_
      exact (continuous_const.max continuous_id).comp_continuousOn ((continuousOn_yv F hF a _).sub (continuousOn_yv F hF b _))
    · exact continuousOn_const
  · simp only [W, dif_neg hj]
    exact continuousOn_const

end PrimeOrbit

open PrimeOrbit in
/-- **The orbit collapse property for `ℤ/p`** (`p` prime), proved via Dold's theorem. -/
theorem joinOrbitCollapse_zmod (p : ℕ) [Fact p.Prime] :
    JoinOrbitCollapse (Multiplicative (ZMod p)) := by
  classical
  intro ι _
  refine ⟨Fintype.card (Idx (Multiplicative (ZMod p)) ι) + 2, fun F hF => ?_⟩
  by_contra hno
  push_neg at hno
  have hT : ∀ x ∈ GroupJoin _ _, 0 < T F x := fun x hx => by
    obtain ⟨g, hg⟩ := hno x hx
    exact T_pos F hg
  have hq : Nat.card (Multiplicative (ZMod p)) = p := by simp
  refine Dold.dold_join p (D := Fintype.card (Idx (Multiplicative (ZMod p)) ι)) (by omega)
    (Phi F) ?_ (fun x hx => Phi_mem F hq (hT x hx)) (fun g x _ => Phi_joinAct F x g)
  refine continuousOn_pi.2 fun j => continuousOn_pi.2 fun h => ?_
  have hTc : ContinuousOn (fun x => T F x) (GroupJoin _ _) :=
    continuousOn_finset_sum _ fun j _ => continuousOn_finset_sum _ fun h _ => continuousOn_W F hF j h
  exact (continuousOn_W F hF j h).div hTc fun x hx => (hT x hx).ne'

/-- **The orbit collapse property for every group of prime order** (unconditional). -/
theorem joinOrbitCollapse_of_card_prime (G : Type) [Group G] [Fintype G] {p : ℕ} [Fact p.Prime]
    (hG : Nat.card G = p) : JoinOrbitCollapse G := by
  have e : G ≃* Multiplicative (ZMod p) := mulEquivOfPrimeCardEq hG (by simp)
  exact JoinOrbitCollapse.of_injective e.toMonoidHom e.injective (joinOrbitCollapse_zmod p)

end Dvoretzky
