module

public import RequestProject.Dvoretzky.PrimeOrbitCollapse

/-!
# Lemma 1 as an "emptiness" statement

The emptiness part of the generalised Sullivan conjecture (Miller, Lannes, Carlsson) says that for
a finite `p`-group `G` and a finite-dimensional `G`-complex `Y` without `G`-fixed points there is
no `G`-map `EG → Y`. Its finite, join-model form is `JoinEmptiness G`: for every finite `G`-set
`S` without fixed points and every finite index set `J` there is `N` such that there is no
continuous equivariant map from the `N`-fold join `G * ⋯ * G` to the join `S^{*J}` of `|J|` copies
of `S` (a finite simplicial `G`-complex without fixed points).

Main results:

* `joinOrbitCollapse_iff_joinEmptiness`: for every finite group this is equivalent to the orbit
  collapse property `JoinOrbitCollapse G` (Lemma 1 in the form used by Theorem 1). The direction
  `←` maps a point `x` to the strict "upper sets" of the values `F(h·x)`, a finite `G`-set without
  fixed points; the direction `→` is immediate.
* `joinEmptiness_of_card_prime`: unconditional for groups of prime order (from Dold's theorem).
* `twoGroupOrbitCollapse_iff_joinEmptiness`, `gromovMilman_of_joinEmptiness`: Theorem 1 follows
  from the emptiness statement for finite `2`-groups, and needs exactly it.
-/

@[expose] public section

open scoped BigOperators

noncomputable section

namespace Dvoretzky

/-- The join `S * ⋯ * S` of `|J|` copies of a finite set `S`: weights `y j s ≥ 0` of total
mass `1`, each block `j` supported at a single point. -/
def SetJoin (S J : Type) [Fintype S] [Fintype J] : Set (J → S → ℝ) :=
  {y | (∀ j s, 0 ≤ y j s) ∧ (∀ j s s', y j s ≠ 0 → y j s' ≠ 0 → s = s') ∧ ∑ j, ∑ s, y j s = 1}

/-- The action of `G` on `S^{*J}` induced by an action on `S`. -/
def setJoinAct {G S J : Type} [Group G] [MulAction G S] (g : G) (y : J → S → ℝ) : J → S → ℝ :=
  fun j s => y j (g⁻¹ • s)

/-- **Emptiness statement** (join model of the emptiness part of the generalised Sullivan
conjecture): for every finite `G`-set `S` without fixed points and every finite `J` there is `N`
such that no continuous map from the `N`-fold join of `G` to `S^{*J}` is equivariant. -/
def JoinEmptiness (G : Type) [Group G] [Fintype G] : Prop :=
  ∀ (S : Type) [Fintype S] [MulAction G S], (∀ s : S, ∃ g : G, g • s ≠ s) →
    ∀ (J : Type) [Fintype J], ∃ N : ℕ, ∀ Φ : (Fin N → G → ℝ) → (J → S → ℝ),
      ContinuousOn Φ (GroupJoin G N) → (∀ x ∈ GroupJoin G N, Φ x ∈ SetJoin S J) →
        ∃ x ∈ GroupJoin G N, ∃ g : G, Φ (joinAct g x) ≠ setJoinAct g (Φ x)

/-! ### Orbit collapse implies emptiness -/

theorem JoinOrbitCollapse.joinEmptiness {G : Type} [Group G] [Fintype G]
    (h : JoinOrbitCollapse G) : JoinEmptiness G := by
  intro S _ _ hS J _
  obtain ⟨N, hN⟩ := h (J × S)
  refine ⟨N, fun Φ hΦ hmem => ?_⟩
  by_contra hno
  push_neg at hno
  let F : (Fin N → G → ℝ) → (J × S → ℝ) := fun x js => Φ x js.1 js.2
  have hF : ContinuousOn F (GroupJoin G N) :=
    continuousOn_pi.2 fun js => (continuous_apply js.2).comp_continuousOn
      ((continuous_apply js.1).comp_continuousOn hΦ)
  obtain ⟨x, hx, hfix⟩ := hN F hF
  obtain ⟨hnn, hsupp, hsum⟩ := hmem x hx
  obtain ⟨j, s, hjs⟩ : ∃ j s, Φ x j s ≠ 0 := by
    by_contra hc
    push_neg at hc
    simp [hc] at hsum
  obtain ⟨g, hg⟩ := hS s
  have h1 : Φ x j (g • s) = Φ x j s := by
    have e1 := congrFun (hfix g⁻¹) (j, s)
    simp only [F] at e1
    rw [hno x hx g⁻¹] at e1
    simpa [setJoinAct] using e1
  exact hg (hsupp j _ _ (h1 ▸ hjs) hjs)

/-! ### Emptiness implies orbit collapse -/

namespace Empt

open PrimeOrbit

variable {G : Type} [Group G] [Fintype G] [DecidableEq G]

/-- Proper nonempty subsets of `G`. -/
def PSub (G : Type) [Fintype G] : Type := {A : Finset G // A.Nonempty ∧ A ≠ Finset.univ}

instance : Finite (PSub G) := Subtype.finite

instance : Fintype (PSub G) := Fintype.ofFinite _

/-- `G` acts on proper nonempty subsets by `g • A = A g⁻¹`. -/
instance : MulAction G (PSub G) where
  smul g A := ⟨tr A.1 g⁻¹, (tr_nonempty_iff _ _).2 A.2.1,
    fun h => A.2.2 ((tr_eq_univ_iff _ _).1 h)⟩
  one_smul A := Subtype.ext (by show tr A.1 1⁻¹ = A.1; simp)
  mul_smul a b A := Subtype.ext (by
    show tr A.1 (a * b)⁻¹ = tr (tr A.1 b⁻¹) a⁻¹
    rw [tr_tr, mul_inv_rev])

omit [DecidableEq G] in
lemma psub_smul_val (g : G) (A : PSub G) : (g • A).1 = tr A.1 g⁻¹ := rfl

omit [DecidableEq G] in
/-- No proper nonempty subset is fixed by all of `G`. -/
lemma psub_not_fixed (A : PSub G) : ∃ g : G, g • A ≠ A := by
  obtain ⟨a, ha⟩ := A.2.1
  obtain ⟨b, hb⟩ : ∃ b, b ∉ A.1 := by
    by_contra hc
    push_neg at hc
    exact A.2.2 (Finset.eq_univ_of_forall hc)
  refine ⟨b⁻¹ * a, fun h => hb ?_⟩
  have : b ∈ ((b⁻¹ * a) • A).1 := by
    rw [psub_smul_val]
    exact Finset.mem_map.2 ⟨a, ha, by simp⟩
  rwa [h] at this

variable {ι : Type} [Fintype ι] {N : ℕ} (F : (Fin N → G → ℝ) → (ι → ℝ))

/-- Blocks of the target join: a coordinate `i` and a size `c` of the upper set. -/
abbrev Blk (G ι : Type) [Fintype G] := ι × Fin (Fintype.card G + 1)

/-- Raw weights. -/
def W (x : Fin N → G → ℝ) (j : Blk G ι) (A : PSub G) : ℝ :=
  if A.1.card = (j.2 : ℕ) then wt F x j.1 A.1 else 0

/-- Total weight. -/
def T (x : Fin N → G → ℝ) : ℝ := ∑ j : Blk G ι, ∑ A : PSub G, W F x j A

/-- The normalised map to the join `(PSub G)^{*(ι × Fin (|G|+1))}`. -/
def Phi (x : Fin N → G → ℝ) : Blk G ι → PSub G → ℝ := fun j A => W F x j A / T F x

omit [Fintype ι] in
lemma W_nonneg (x : Fin N → G → ℝ) (j : Blk G ι) (A : PSub G) : 0 ≤ W F x j A := by
  unfold W
  split_ifs
  · exact wt_nonneg F x _ _
  · exact le_rfl

omit [Fintype ι] in
lemma W_joinAct (x : Fin N → G → ℝ) (g : G) (j : Blk G ι) (A : PSub G) :
    W F (joinAct g x) j A = W F x j (g⁻¹ • A) := by
  unfold W
  rw [psub_smul_val, inv_inv, card_tr, wt_joinAct]

lemma T_joinAct (x : Fin N → G → ℝ) (g : G) : T F (joinAct g x) = T F x := by
  unfold T
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [W_joinAct]
  exact Fintype.sum_equiv (MulAction.toPerm g⁻¹) _ _ fun A => rfl

lemma Phi_joinAct (x : Fin N → G → ℝ) (g : G) :
    Phi F (joinAct g x) = setJoinAct g (Phi F x) := by
  funext j A
  simp [Phi, setJoinAct, W_joinAct, T_joinAct]

omit [Fintype ι] in
/-- If `F` is not constant on the orbit of `x`, some strict upper set has positive weight. -/
lemma exists_wt_pos {x : Fin N → G → ℝ} {g : G} (hg : F (joinAct g x) ≠ F x) :
    ∃ i : ι, ∃ A : PSub G, 0 < wt F x i A.1 := by
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
  refine ⟨i, ⟨A, hAne, hAu⟩, ?_⟩
  unfold wt
  rw [if_pos ⟨hAne, hAu⟩]
  refine Finset.prod_pos fun a ha => Finset.prod_pos fun b hb => ?_
  simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff] at ha hb
  have := hmax b (Finset.mem_univ _)
  have hlt : yv F x b i < yv F x a i := by rw [ha]; exact lt_of_le_of_ne this hb
  exact lt_max_of_lt_right (by linarith)

lemma T_pos {x : Fin N → G → ℝ} {g : G} (hg : F (joinAct g x) ≠ F x) : 0 < T F x := by
  obtain ⟨i, A, hA⟩ := exists_wt_pos F hg
  let j : Blk G ι := (i, ⟨A.1.card, Nat.lt_succ_of_le (Finset.card_le_univ _)⟩)
  have hW : W F x j A = wt F x i A.1 := by simp [W, j]
  calc 0 < W F x j A := hW ▸ hA
    _ ≤ ∑ B, W F x j B := Finset.single_le_sum (fun B _ => W_nonneg F x j B) (Finset.mem_univ _)
    _ ≤ T F x := Finset.single_le_sum (f := fun j => ∑ B, W F x j B)
        (fun j _ => Finset.sum_nonneg fun B _ => W_nonneg F x j B) (Finset.mem_univ _)

lemma Phi_mem {x : Fin N → G → ℝ} (hT : 0 < T F x) : Phi F x ∈ SetJoin (PSub G) (Blk G ι) := by
  refine ⟨fun j A => div_nonneg (W_nonneg F x j A) hT.le, fun j A B a b => ?_, ?_⟩
  · simp only [Phi, ne_eq, div_eq_zero_iff, not_or] at a b
    unfold W at a b
    split_ifs at a b with hA hB
    · have ha := lt_of_le_of_ne (wt_nonneg F x _ _) (Ne.symm a.1)
      have hb := lt_of_le_of_ne (wt_nonneg F x _ _) (Ne.symm b.1)
      exact Subtype.ext (eq_of_wt_pos F ha hb (by rw [hA, hB]))
    all_goals simp_all
  · simp only [Phi, ← Finset.sum_div]
    exact div_self hT.ne'

omit [Fintype ι] in
lemma continuousOn_W (hF : ContinuousOn F (GroupJoin G N)) (j : Blk G ι) (A : PSub G) :
    ContinuousOn (fun x => W F x j A) (GroupJoin G N) := by
  unfold W
  split_ifs
  · unfold wt
    split_ifs
    · refine continuousOn_finset_prod _ fun a _ => continuousOn_finset_prod _ fun b _ => ?_
      exact (continuous_const.max continuous_id).comp_continuousOn
        ((continuousOn_yv F hF a _).sub (continuousOn_yv F hF b _))
    · exact continuousOn_const
  · exact continuousOn_const

end Empt

open Empt in
theorem JoinEmptiness.joinOrbitCollapse {G : Type} [Group G] [Fintype G]
    (h : JoinEmptiness G) : JoinOrbitCollapse G := by
  classical
  intro ι _
  obtain ⟨N, hN⟩ := h (PSub G) psub_not_fixed (Blk G ι)
  refine ⟨N, fun F hF => ?_⟩
  by_contra hno
  push_neg at hno
  have hT : ∀ x ∈ GroupJoin G N, 0 < Empt.T F x := fun x hx => by
    obtain ⟨g, hg⟩ := hno x hx
    exact Empt.T_pos F hg
  have hTc : ContinuousOn (fun x => Empt.T F x) (GroupJoin G N) :=
    continuousOn_finset_sum _ fun j _ => continuousOn_finset_sum _ fun A _ =>
      Empt.continuousOn_W F hF j A
  have hΦc : ContinuousOn (Empt.Phi F) (GroupJoin G N) :=
    continuousOn_pi.2 fun j => continuousOn_pi.2 fun A =>
      (Empt.continuousOn_W F hF j A).div hTc fun x hx => (hT x hx).ne'
  obtain ⟨x, -, g, hg⟩ := hN (Empt.Phi F) hΦc fun x hx => Empt.Phi_mem F (hT x hx)
  exact hg (Empt.Phi_joinAct F x g)

/-- **Lemma 1 (orbit form) is the emptiness statement.** For every finite group, the orbit
collapse property is equivalent to the join-model emptiness statement. -/
theorem joinOrbitCollapse_iff_joinEmptiness (G : Type) [Group G] [Fintype G] :
    JoinOrbitCollapse G ↔ JoinEmptiness G :=
  ⟨JoinOrbitCollapse.joinEmptiness, JoinEmptiness.joinOrbitCollapse⟩

/-- **Emptiness for groups of prime order** (unconditional, from Dold's theorem): no continuous
equivariant map from a high join of `G` to a join of copies of a fixed-point-free finite `G`-set. -/
theorem joinEmptiness_of_card_prime (G : Type) [Group G] [Fintype G] {p : ℕ} [Fact p.Prime]
    (hG : Nat.card G = p) : JoinEmptiness G :=
  (joinOrbitCollapse_of_card_prime G hG).joinEmptiness

/-- The part of Carlsson's theorem used by Theorem 1 is exactly the emptiness statement for
finite `2`-groups. -/
theorem twoGroupOrbitCollapse_iff_joinEmptiness :
    TwoGroupOrbitCollapse ↔
      ∀ (G : Type) [Group G] [Fintype G], IsPGroup 2 G → JoinEmptiness G :=
  ⟨fun h G _ _ hG => (h G hG).joinEmptiness, fun h G _ _ hG => (h G hG).joinOrbitCollapse⟩

/-- **Theorem 1** of Dol'nikov–Karasev, assuming the emptiness statement for finite `2`-groups. -/
theorem gromovMilman_of_joinEmptiness
    (h : ∀ (G : Type) [Group G] [Fintype G], IsPGroup 2 G → JoinEmptiness G)
    (d k : ℕ) (hd : Even d) (hd0 : 0 < d) : GromovMilmanProperty d k :=
  gromovMilman_of_orbitCollapse (twoGroupOrbitCollapse_iff_joinEmptiness.2 h) d k hd hd0

end Dvoretzky
