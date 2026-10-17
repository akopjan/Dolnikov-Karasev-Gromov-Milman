module

public import RequestProject.Dvoretzky.Carlsson

/-!
# The part of Carlsson's theorem used by Dol'nikov–Karasev: collapsing an orbit

The proof of Theorem 1 of Dol'nikov–Karasev applies Lemma 1 only to *permutation*
representations `ℝ^(G × P)` (copies of the regular representation). For these the fixed value
statement of Lemma 1 says that a map is constant on a whole orbit. We isolate this as

* `JoinOrbitCollapse G`: for every finite index type `ι` there is `N` such that every continuous
  map `F` from the `N`-fold join `G * ⋯ * G` to `ℝ^ι` (no equivariance is required) is constant on
  some `G`-orbit;
* `TwoGroupOrbitCollapse`: `JoinOrbitCollapse G` for every finite `2`-group `G`.

Main results:

* `twoGroupBorsukUlam_of_orbitCollapse`, `gromovMilman_of_orbitCollapse`: this orbit form is all
  that the proof of Theorem 1 needs.
* `JoinBorsukUlam.twoGroupOrbitCollapse`, `twoGroupOrbitCollapse_of_carlsson`: it follows from
  Lemma 1, hence from Carlsson's theorem.
* `twoGroupOrbitCollapse_iff`, `twoGroupOrbitCollapse_iff_carlssonProperty_two`: conversely, it
  implies Lemma 1 for all representations, so the part of Carlsson's theorem needed by
  Dol'nikov–Karasev is exactly Lemma 1 for finite `2`-groups.
* `JoinOrbitCollapse.of_surjective`, `JoinOrbitCollapse.of_injective`: the orbit property passes
  to quotient groups and to subgroups.
* `joinOrbitCollapse_of_card_le_two`: it holds for groups of order at most `2` (classical
  Borsuk–Ulam theorem).
-/

@[expose] public section

open scoped BigOperators InnerProductSpace

noncomputable section

namespace Dvoretzky

/-- **Orbit collapse property** of a finite group `G`. For every finite index type `ι` there is
`N` such that every continuous map `F` from the `N`-fold join `G * ⋯ * G` to `ℝ^ι` is constant on
some `G`-orbit. No equivariance of `F` is assumed. This is the fixed value form of Lemma 1 for the
permutation representation `ℝ^(G × ι)` (copies of the regular representation). -/
def JoinOrbitCollapse (G : Type) [Group G] [Fintype G] : Prop :=
  ∀ (ι : Type) [Fintype ι], ∃ N : ℕ, ∀ F : (Fin N → G → ℝ) → (ι → ℝ),
    ContinuousOn F (GroupJoin G N) → ∃ x ∈ GroupJoin G N, ∀ g, F (joinAct g x) = F x

/-- **The part of Carlsson's theorem used by Dol'nikov–Karasev**: every finite `2`-group has the
orbit collapse property `JoinOrbitCollapse`. -/
def TwoGroupOrbitCollapse : Prop :=
  ∀ (G : Type) [Group G] [Fintype G], IsPGroup 2 G → JoinOrbitCollapse G

section Basic

variable {G : Type} [Group G]

lemma joinAct_joinAct {N : ℕ} (a b : G) (x : Fin N → G → ℝ) :
    joinAct a (joinAct b x) = joinAct (a * b) x := by
  funext i h
  simp [joinAct, mul_assoc]

@[simp] lemma joinAct_one {N : ℕ} (x : Fin N → G → ℝ) : joinAct (1 : G) x = x := by
  funext i _
  simp [joinAct]

lemma continuous_joinAct {N : ℕ} (g : G) : Continuous (joinAct (N := N) g) :=
  continuous_pi fun i => continuous_pi fun _ => (continuous_apply _).comp (continuous_apply i)

end Basic

/-! ### The orbit form suffices for Theorem 1 -/

/-- The orbit collapse property of finite `2`-groups implies the form `TwoGroupBorsukUlam` of
Lemma 1 used in the proof of Theorem 1. -/
theorem twoGroupBorsukUlam_of_orbitCollapse (h : TwoGroupOrbitCollapse) : TwoGroupBorsukUlam := by
  classical
  intro ι _ G hGfin hG2 P
  letI : Fintype G := Fintype.ofFinite G
  obtain ⟨N, hN⟩ := h G hG2 P
  refine ⟨N * Fintype.card ι, fun n hn φ hφ => ?_⟩
  have hcard : Fintype.card (Fin N × ι) ≤ Fintype.card (Fin n) := by
    simpa using hn
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  let σ : G →* (EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) := G.subtype
  let F : (Fin N → G → ℝ) → (P → ℝ) := fun x p => φ (joinMap σ e x (p : EuclideanSpace ℝ ι))
  have hFc : Continuous F :=
    continuous_pi fun p => hφ.comp (continuous_joinMap_apply σ e _)
  obtain ⟨x, hx, hfix⟩ := hN F hFc.continuousOn
  refine ⟨(joinMap σ e x).isometryOfInner (inner_joinMap σ e hx), fun g hg p hp => ?_⟩
  have h1 := congrFun (hfix ⟨g, hg⟩⁻¹) ⟨p, hp⟩
  simp only [F, joinMap_joinAct, inv_inv] at h1
  simpa [σ, LinearMap.coe_isometryOfInner] using h1

/-- **Theorem 1** of Dol'nikov–Karasev (the Gromov–Milman conjecture), assuming only the orbit
collapse property of finite `2`-groups (`TwoGroupOrbitCollapse`), the part of Carlsson's theorem
that the proof uses. -/
theorem gromovMilman_of_orbitCollapse (h : TwoGroupOrbitCollapse) (d k : ℕ) (hd : Even d)
    (hd0 : 0 < d) : GromovMilmanProperty d k :=
  gromovMilman (twoGroupBorsukUlam_of_orbitCollapse h) d k hd hd0

/-! ### The orbit form follows from Lemma 1 and from Carlsson's theorem -/

/-- Lemma 1 (`JoinBorsukUlam`) implies the orbit collapse property of finite `2`-groups: apply it
to the permutation representation `ℝ^(G × ι)` and the equivariant map
`x ↦ (F (h⁻¹ • x) i)_{(h, i)}`. -/
theorem JoinBorsukUlam.twoGroupOrbitCollapse (h : JoinBorsukUlam) : TwoGroupOrbitCollapse := by
  intro G _ _ hG ι _
  obtain ⟨N, hN⟩ := h G hG (G × ι) (permRep G ι)
  refine ⟨N, fun F hF => ?_⟩
  let f : (Fin N → G → ℝ) → EuclideanSpace ℝ (G × ι) :=
    fun x => WithLp.toLp 2 (fun hi : G × ι => F (joinAct hi.1⁻¹ x) hi.2)
  have hfc : ContinuousOn f (GroupJoin G N) := by
    refine (PiLp.continuous_toLp 2 _).comp_continuousOn (continuousOn_pi.2 fun hi => ?_)
    exact (continuous_apply hi.2).comp_continuousOn
      (hF.comp (continuous_joinAct _).continuousOn fun x hx => joinAct_mem _ hx)
  have hfe : ∀ g, ∀ x ∈ GroupJoin G N, f (joinAct g x) = permRep G ι g (f x) := by
    intro g x _
    ext ⟨h, i⟩
    rw [permRep_apply]
    simp only [f, joinAct_joinAct, mul_inv_rev, inv_inv]
  obtain ⟨x, hx, hfix⟩ := hN f hfc hfe
  refine ⟨x, hx, fun g => funext fun i => ?_⟩
  have h1 := congrArg (fun u : EuclideanSpace ℝ (G × ι) => u (1, i)) (hfix g)
  simp only [permRep_apply, mul_one, f, inv_one, joinAct_one, inv_inv] at h1
  exact h1

/-- **The part of Carlsson's theorem used by Dol'nikov–Karasev follows from Carlsson's theorem.**
-/
theorem twoGroupOrbitCollapse_of_carlsson (h : CarlssonTheorem) : TwoGroupOrbitCollapse :=
  (joinBorsukUlam_of_carlsson h).twoGroupOrbitCollapse


/-! ### The orbit form is equivalent to Lemma 1 -/

/-- Conversely, the orbit collapse property of finite `2`-groups implies Lemma 1
(`JoinBorsukUlam`): apply it to the coordinates of an equivariant map. -/
theorem TwoGroupOrbitCollapse.joinBorsukUlam (h : TwoGroupOrbitCollapse) : JoinBorsukUlam := by
  intro G _ _ hG ι _ ρ
  obtain ⟨N, hN⟩ := h G hG ι
  refine ⟨N, fun f hf he => ?_⟩
  obtain ⟨x, hx, hfix⟩ := hN (fun x i => f x i)
    (continuousOn_pi.2 fun i => (PiLp.continuous_apply 2 _ i).comp_continuousOn hf)
  refine ⟨x, hx, fun g => ?_⟩
  rw [← he g x hx]
  ext i
  exact congrFun (hfix g) i

/-- **The part of Carlsson's theorem needed by Dol'nikov–Karasev is all of Lemma 1.** The orbit
collapse property of finite `2`-groups (Lemma 1 for permutation representations, which is what the
proof of Theorem 1 uses) is equivalent to Lemma 1 for all orthogonal representations. -/
theorem twoGroupOrbitCollapse_iff : TwoGroupOrbitCollapse ↔ JoinBorsukUlam :=
  ⟨TwoGroupOrbitCollapse.joinBorsukUlam, JoinBorsukUlam.twoGroupOrbitCollapse⟩

/-- Equivalently, the orbit collapse property of finite `2`-groups is the fixed point form of
Carlsson's theorem for the prime `2`. -/
theorem twoGroupOrbitCollapse_iff_carlssonProperty_two :
    TwoGroupOrbitCollapse ↔ CarlssonProperty 2 :=
  twoGroupOrbitCollapse_iff.trans carlssonProperty_two_iff.symm

/-! ### Passing to quotients and subgroups -/

section Push

variable {G Q : Type} [Fintype G] [DecidableEq Q]

/-- The map of joins `G * ⋯ * G → Q * ⋯ * Q` induced by a map of vertices `r : G → Q`. -/
def joinPush (r : G → Q) {N : ℕ} (x : Fin N → G → ℝ) : Fin N → Q → ℝ :=
  fun i q => ∑ a ∈ Finset.univ.filter (fun a => r a = q), x i a

lemma continuous_joinPush (r : G → Q) {N : ℕ} : Continuous (joinPush r (N := N)) :=
  continuous_pi fun i => continuous_pi fun _ =>
    continuous_finset_sum _ fun a _ => (continuous_apply a).comp (continuous_apply i)

lemma joinPush_mem [Fintype Q] (r : G → Q) {N : ℕ} {x : Fin N → G → ℝ} (hx : x ∈ GroupJoin G N) :
    joinPush r x ∈ GroupJoin Q N := by
  obtain ⟨h0, h1, h2⟩ := hx
  have hsingle : ∀ i, ∀ q, joinPush r x i q ≠ 0 → ∃ a, r a = q ∧ x i a ≠ 0 := by
    intro i q hq
    by_contra hno
    push_neg at hno
    exact hq (Finset.sum_eq_zero fun a ha => hno a (Finset.mem_filter.1 ha).2)
  refine ⟨fun i q => Finset.sum_nonneg fun a _ => h0 i a, fun i q q' hq hq' => ?_, ?_⟩
  · obtain ⟨a, rfl, ha⟩ := hsingle i q hq
    obtain ⟨b, rfl, hb⟩ := hsingle i q' hq'
    rw [h1 i a b ha hb]
  · rw [← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [joinPush]
    exact Finset.sum_fiberwise Finset.univ r (x i)

lemma joinPush_joinAct [Group G] [Group Q] (r : G → Q) {g : G} {q : Q} (hr : ∀ a, r (a * g) = r a * q) {N : ℕ}
    (x : Fin N → G → ℝ) : joinPush r (joinAct g x) = joinAct q (joinPush r x) := by
  funext i c
  simp only [joinPush, joinAct]
  refine Finset.sum_nbij' (fun a => a * g) (fun b => b * g⁻¹) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    rw [hr, ha]
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    have := hr (b * g⁻¹)
    rw [inv_mul_cancel_right, hb] at this
    exact mul_right_cancel this.symm
  · intro a _; simp
  · intro b _; simp
  · intro a _; rfl

end Push

/-- **The orbit collapse property passes to quotient groups.** -/
theorem JoinOrbitCollapse.of_surjective {G Q : Type} [Group G] [Group Q] [Fintype G] [Fintype Q]
    (π : G →* Q) (hπ : Function.Surjective π) (h : JoinOrbitCollapse G) : JoinOrbitCollapse Q := by
  classical
  intro ι _
  obtain ⟨N, hN⟩ := h ι
  refine ⟨N, fun F hF => ?_⟩
  obtain ⟨x, hx, hfix⟩ := hN (F ∘ joinPush π)
    (hF.comp (continuous_joinPush π).continuousOn fun x hx => joinPush_mem _ hx)
  refine ⟨joinPush π x, joinPush_mem _ hx, fun q => ?_⟩
  obtain ⟨g, rfl⟩ := hπ q
  have := hfix g
  simp only [Function.comp_apply] at this
  rwa [joinPush_joinAct π (fun a => map_mul π a g)] at this

/-- **The orbit collapse property passes to subgroups** (more generally, along injective
homomorphisms). -/
theorem JoinOrbitCollapse.of_injective {H G : Type} [Group H] [Group G] [Fintype H] [Fintype G]
    (φ : H →* G) (hφ : Function.Injective φ) (h : JoinOrbitCollapse G) : JoinOrbitCollapse H := by
  classical
  -- a vertex map `r : G → H` with `r (a * φ k) = r a * k`, from representatives of `G ⧸ φ(H)`
  let K : Subgroup G := φ.range
  have hmem : ∀ a : G, ((QuotientGroup.mk (s := K) a).out)⁻¹ * a ∈ K := fun a => by
    have := QuotientGroup.mk_out_eq_mul K a
    obtain ⟨k, hk⟩ := this
    rw [hk, mul_inv_rev, inv_mul_cancel_right]
    exact K.inv_mem k.2
  let r : G → H := fun a => (hmem a).choose
  have hr_spec : ∀ a, φ (r a) = ((QuotientGroup.mk (s := K) a).out)⁻¹ * a :=
    fun a => (hmem a).choose_spec
  have hr : ∀ a k, r (a * φ k) = r a * k := by
    intro a k
    apply hφ
    have hq : (QuotientGroup.mk (s := K) (a * φ k)) = QuotientGroup.mk a := by
      rw [QuotientGroup.eq]
      simp only [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
      exact K.inv_mem ⟨k, rfl⟩
    rw [hr_spec, map_mul, hr_spec, hq, mul_assoc]
  intro ι _
  obtain ⟨N, hN⟩ := h ι
  refine ⟨N, fun F hF => ?_⟩
  obtain ⟨x, hx, hfix⟩ := hN (F ∘ joinPush r)
    (hF.comp (continuous_joinPush r).continuousOn fun x hx => joinPush_mem _ hx)
  refine ⟨joinPush r x, joinPush_mem _ hx, fun k => ?_⟩
  have := hfix (φ k)
  simp only [Function.comp_apply] at this
  rwa [joinPush_joinAct r (fun a => hr a k)] at this

/-! ### Groups of order at most two -/

/-- **The orbit collapse property for groups of order at most `2`** (classical Borsuk–Ulam
theorem for order `2`; trivial for the trivial group). -/
theorem joinOrbitCollapse_of_card_le_two (G : Type) [Group G] [Fintype G]
    (hG : Fintype.card G ≤ 2) : JoinOrbitCollapse G := by
  sorry

end Dvoretzky
