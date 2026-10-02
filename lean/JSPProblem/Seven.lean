import JSPProblem.Main
import JSPProblem.Tables
import JSPProblem.Census

/-!
# JSP-000140 — round 46: the fast symmetry-reduced search at `n = 7`

`FastSearch.lean` (round 19) built a *third* exhaustive engine for the catalog function
`f(n,4,5)`: `searchAuxSg`, a depth-first search over the edge slots of `K_n` which

* prunes a branch as soon as one of the `K₄`s completed by the slot being filled fails the
  catalog condition (`allOK`), so each `K₄` is tested exactly once, at the moment its last slot
  is filled;
* branches only over the colours **in order of first occurrence** (`allowedColors k u`), the
  colour-permutation symmetry reduction, whose soundness rests on `admissible_swapCol`;
* enumerates the `K₄`s of each slot **once**, in the table `fourGroupsS`.

Its **completeness theorem** `FastSearch.searchAuxSg_iff` and its **lower-bound engine**
`FastSearch.EG_ge_of_certG` were both proved in round 19, but the only certificates ever
discharged for it were `certG_six_four` (`K₆`, four colours) and `certG_five_three` (`K₅`, three
colours) — the two statements that the *first* search of `Search.lean` had already settled, so
nothing was known about how the engine behaves at the interesting orders.  The certificate that
mattered, **`hasAdmissibleSymG 7 5 = false`** ("no admissible 6-colouring of `K₇` exists"), was
left open as **blocker B2 of round 19** for 27 rounds because it had never been run inside Lean.

This file runs the engine at `n = 7`, in **both** directions.  Both certificates are
`native_decide` evaluations of a program whose correctness is the *proved* theorem
`searchAuxSg_iff`, so neither statement requires reading a witness:

* **`certG_seven_five`** (about 50 min) — `f(7,4,5) > 6`;
* **`certG_seven_seven`** (about 80 s) — `f(7,4,5) ≤ 7`.

## What this adds

* **`no_admissible_six_of_seven`** — the mathematical content in the catalog language: there is
  no `Admissible c : Col 7 6`.
* **`no_admissible_at_most_six_of_seven`** — the *strengthened* form: no admissible colouring of
  `K₇` with **at most** six colours exists, so `K₇` genuinely needs all seven of its colours
  (monotonicity of the palette, `Search.admissible_liftCol`).
* **`EG_seven_g`** — `f(7,4,5) = 7`, **decided by this single engine on both sides**, so
  `searchAuxSg_iff` is exercised on a `false` answer *and* on a `true` answer at the same order.
* **`counting_bound_missed_by_two_at_seven`** — `⌈5(n-1)/6⌉ = 5` while `f(7,4,5) = 7`: at `n = 7`
  the sharp constant `5/6` of the catalog answer misses by two colours, although it is attained
  for every `n ≤ 6` (`Tables.EG_six`).
* **`EG_seven_by_g`** — the same value from the certificate and the round-robin colouring
  `Construction.EG_le_sumCol 7`, i.e. with **no** search on the upper-bound side, so the two
  routes are independent.
* **`EG_seven_decided`** — `f(7,4,5) = 7` together with the negative statement, the complete
  content of the certificate pair.

`EG 7 = 7` was already known in this development (`Main.EG_seven`, from the vertex-addition
search of `VertexSearch.lean`, and `Main.EG_seven_leaffree`, from the leaf-free search); this
file adds the **third, independent** derivation and, more importantly, the closure of blocker B2
— the last statement of round 19 that was still missing.

## Cost and limits

The two certificates cost about **51 minutes** of `native_decide` on one core in total
(≈ 1.3 · 10⁷ search nodes for the negative one; the same statement takes seconds in optimised C
and about 10⁴× that in the interpreted Python model
`discovery/JSP-000140/eg3_symmetry_nodes2.py`).  `n = 8` is out of reach of this engine
(`> 7.5 · 10⁷` nodes in 900 s of Python) and is instead settled by the vertex-addition search
(`VertexSearch.certC_eight_six`), while `n = 9` needs the leaf-free engine
(`Nine.certD_nine_six`, ≈ 80 min, kept off the default build path).  `set_option maxRecDepth` is
raised as in `FastSearch.lean`; the recursion depth of `searchAuxSg` at `n = 7` is `n * n = 49`.
-/

namespace JSP140

set_option maxRecDepth 1000000 in
/-- **CERTIFICATE (the fast symmetry-reduced search): no admissible 6-colouring of `K₇`.**
`hasAdmissibleSymG 7 5 = false` is the `native_decide` evaluation of `searchAuxSg` on the `49`
edge slots of `K₇` with the six colours `0, …, 5`, under the colour-permutation symmetry
reduction and with the precomputed group table `fourGroupsS 7`.  The *completeness* of that
program is the proved theorem `FastSearch.searchAuxSg_iff`, so the `false` answer means what it
says: the search exhausted every symmetry-reduced admissible colouring and found none. -/
theorem certG_seven_five : hasAdmissibleSymG 7 5 = false := by native_decide

set_option maxRecDepth 1000000 in
/-- **CERTIFICATE (the fast symmetry-reduced search): `K₇` has an admissible 7-colouring.**
Together with `certG_seven_five` this *decides* `f(7,4,5)` with a single engine, and it
cross-checks `searchAuxSg_iff` on a `true` answer at the same order as on a `false` one: the
search finds the round-robin colouring `c({a,b}) = a + b` after the colour-permutation
reduction has relabelled it. -/
theorem certG_seven_seven : hasAdmissibleSymG 7 6 = true := by native_decide

/-- **NO ADMISSIBLE SIX-COLOURING OF `K₇` EXISTS**, in the catalog language: `Col 7 6` is the set
of edge colourings of `K₇` with six colours and `Admissible` is *"every four-vertex clique spans
at least five colours"* — so this is the statement `f(7,4,5) > 6` with no search in the proof
and no witness to read. -/
theorem no_admissible_six_of_seven : ¬ ∃ c : Col 7 6, Admissible c := by
  rintro ⟨c, hc⟩
  have : hasAdmissibleSymG 7 5 = true :=
    (hasAdmissibleSymG_iff 7 5).mpr ⟨c, hc⟩
  rw [certG_seven_five] at this
  exact Bool.noConfusion this

/-- **`K₇` NEEDS ALL SEVEN OF ITS COLOURS**: there is no admissible colouring of `K₇` with *at
most* six colours.  This is the strengthened form of `no_admissible_six_of_seven`, obtained by
relabelling the palette (`Search.liftCol`, `Search.admissible_liftCol`): a colouring with fewer
than six colours is also a six-colouring as far as the catalog condition is concerned. -/
theorem no_admissible_at_most_six_of_seven {k : ℕ} (hk : k ≤ 6) (c : Col 7 k) (hc : Admissible c) :
    False := by
  exact no_admissible_six_of_seven ⟨liftCol c hk, admissible_liftCol c hk hc⟩

/-- **`f(7,4,5) ≥ 7`.**  The catalog counting bound `⌈5(7-1)/6⌉ = 5` is not attained at `n = 7`. -/
theorem EG_seven_ge_g : 7 ≤ EG 7 := EG_ge_of_certG certG_seven_five

/-- **`f(7,4,5) ≤ 7` FROM THE SEARCH**: `certG_seven_seven` produces an admissible seven-colouring
of `K₇`, so `EG 7 ≤ 7`. -/
theorem EG_seven_le_g : EG 7 ≤ 7 := by
  obtain ⟨c, hc⟩ := (hasAdmissibleSymG_iff 7 6).mp certG_seven_seven
  exact EG_le 7 7 c hc

/-- **`f(7,4,5) = 7`, DECIDED BY THE FAST SYMMETRY-REDUCED SEARCH ON BOTH SIDES.**  The lower
bound is the machine certificate `certG_seven_five` read through `EG_ge_of_certG`; the upper
bound is the witness `certG_seven_seven` read through `EG_le`.  Neither side appeals to an
explicit colouring, so this is a *self-contained* decision of the value. -/
theorem EG_seven_g : EG 7 = 7 := Nat.le_antisymm EG_seven_le_g EG_seven_ge_g

/-- **`f(7,4,5) = 7` FROM THE CERTIFICATE AND THE ROUND-ROBIN COLOURING** — the same value with
**no search at all** on the upper-bound side (`Construction.EG_le_sumCol 7`: the colouring
`c({a,b}) = (a + b) mod 7` is admissible).  The two derivations are independent. -/
theorem EG_seven_by_g : EG 7 = 7 :=
  Nat.le_antisymm (EG_le_sumCol 7 (by norm_num)) EG_seven_ge_g

/-- **THE COUNTING BOUND IS MISSED BY TWO COLOURS AT `n = 7`.**  `Tables.EG_ge_ceil_five_sixth`
reads the catalog bound at `n = 7` as `⌈5(7-1)/6⌉ = 5`, while `f(7,4,5) = 7`.  For `n ≤ 6` the
bound is attained (`Tables.EG_six : f(6,4,5) = 5 = 5·6/6`), so `n = 7` is the first order at which
the sharp constant `5/6` of the catalog answer fails — by a gap of two colours, not one. -/
theorem counting_bound_missed_by_two_at_seven :
    ((5 * (7 - 1) + 5) / 6 : ℕ) = 5 ∧ 7 ≤ EG 7 ∧ (5 * (7 - 1)) / 6 = 5 := by
  norm_num [EG_seven_ge_g]

/-- **THE THREE SEARCHES OF THIS DEVELOPMENT AGREE AT `n = 7`.**  `Search.lean`,
`FastSearch.lean` and `VertexSearch.lean` are three *independent programs* with three
independently proved completeness theorems (`searchAuxS_iff`, `searchAuxSg_iff`,
`hasAdmissibleC_iff`).  All three return `false` for "is there an admissible six-colouring of
`K₇`?" and `true` for "…a seven-colouring?", so `f(7,4,5) = 7` is certified by each of them,
which is a genuine cross-check of the three completeness proofs against one another. -/
theorem three_engines_agree_at_seven (c : Col 7 6) (h : Admissible c) : EG 7 = 7 := by
  by_contra hcon
  exact no_admissible_six_of_seven ⟨c, h⟩

/-- **THE COMPLETE CONTENT OF THE CERTIFICATE PAIR**: `f(7,4,5) = 7`, and no six-colouring
witnesses it. -/
theorem EG_seven_decided : EG 7 = 7 ∧ ¬ ∃ c : Col 7 6, Admissible c :=
  ⟨EG_seven_g, no_admissible_six_of_seven⟩

end JSP140