import JSPProblem.Slack
import JSPProblem.Criterion

/-!
# JSP-000140 — the headline statement, reduced to a *checkable* construction hypothesis

`Criterion.lean` proved that the catalog condition `Admissible c` ("every four-vertex clique spans at
least five colours") is **equivalent** to four purely local conditions on the colour classes
(`Criterion.design_iff_admissible`).  This file closes the loop with the reduction of round 15:

* `SlackFamily.of_design` — a family of designs gives a family of *admissible* colourings with the
  same number of colours: this is the point of the criterion, because it lets the remaining
  hypothesis be stated for constructions that are *not yet known* to be admissible;
* `jsp_000140_main_of_design_family` — **the required theorem `jsp_000140_main`, i.e. the catalog
  statement `f(n, 4, 5) = 5n/6 + o(n)`, reduced to `Criterion.DesignFamily`**: for every
  `δ > 0` and all large `m ≡ 1 (mod 6)` there is a colouring of `K_m` whose colour classes tile the
  vertex set, whose two-edge paths form a linear hypergraph and which has neither a bad nor a
  crossing four-set, and which uses at most `5(m-1)/6 + δ m / 6` colours.

Together with the lower half (`Main.fiveSixthLower_eg`, proved in round 10) this identifies the
whole remaining content of the prize as *only* the probabilistic construction of
arXiv:2207.02920 — and states it in a form in which **no four-vertex clique has to be checked**.
-/

namespace JSP140

variable {n k : ℕ}

/-- A family of designs gives a family of admissible colourings: `DesignFamily → SlackFamily`. -/
theorem SlackFamily.of_design (hfam : DesignFamily) : SlackFamily := by
  intro δ hδ
  obtain ⟨M, hM4, hM⟩ := hfam δ hδ
  refine ⟨max M 4, fun m hMm hm => ?_⟩
  obtain ⟨k, c, hc, hk⟩ := hM m (by omega) hm
  exact ⟨k, c, (design_iff_admissible (by omega)).mpr hc, hk⟩

/-- **THE REQUIRED THEOREM, REDUCED TO A CHECKABLE CONSTRUCTION HYPOTHESIS.**  If for every
`δ > 0` and all large `m ≡ 1 (mod 6)` there is a `k`-edge-colouring of `K_m` satisfying the four
local conditions of `Criterion` and using at most `5(m-1)/6 + δm/6` colours, then

    `jsp_000140_target` — the statement of the required theorem `jsp_000140_main`, i.e. the
    catalog answer `f(n, 4, 5) = 5n/6 + o(n)` — holds.

Together with the lower half proved in `Cherry.lean`, this identifies the remaining content of
the prize as *only* the construction of arXiv:2207.02920: a colouring whose colour classes tile
the vertex set, whose two-edge paths form a linear hypergraph, and which has neither a bad nor a
crossing four-set. -/
theorem jsp_000140_main_of_design_family (hfam : DesignFamily) : jsp_000140_target :=
  jsp_000140_main_of_slack_family (SlackFamily.of_design hfam)

end JSP140
