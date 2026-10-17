module

public import RequestProject.Dvoretzky.Theorem1
public import RequestProject.Dvoretzky.JoinBU

/-!
# Theorem 1 (Gromov–Milman conjecture) from the standard form of Lemma 1

The only external input is `JoinBorsukUlam`: Lemma 1 of Dol'nikov–Karasev (the Borsuk–Ulam
property of finite `2`-groups, due to Bartsch and Clapp–Marzantowicz via Carlsson's theorem),
stated for the `N`-fold join of the group as the highly connected free `G`-space.
-/

@[expose] public section

namespace Dvoretzky

/-- **Theorem 1** (Gromov–Milman conjecture, Dol'nikov–Karasev), assuming only Lemma 1 of the
paper in its standard form for joins. -/
theorem gromovMilman_of_joinBorsukUlam (hBU : JoinBorsukUlam) (d k : ℕ) (hd : Even d)
    (hd0 : 0 < d) : GromovMilmanProperty d k :=
  gromovMilman (twoGroupBorsukUlam_of_join hBU) d k hd hd0

end Dvoretzky
