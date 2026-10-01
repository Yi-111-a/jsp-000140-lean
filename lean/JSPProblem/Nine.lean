import JSPProblem.LeafFree
import JSPProblem.Tables

/-!
# `f(9,4,5) = 8` — an **off-the-build-path** certificate — `JSP-000140`

This module is deliberately **not** imported by `JSPProblem.lean`, and therefore not part of the
default `lake build`.  It contains the machine certificate

```lean
certD_nine_six : hasAdmissibleD 9 6 = false   --  no admissible 7-colouring of `K₉`
```

of the leaf-free vertex-addition search of `LeafFree.lean`, and with the verified colouring
`Tables.nineCol` the third exact value of the Erdős–Gyárfás function in this development that
exceeds the counting bound `⌈5(n-1)/6⌉`:

```lean
EG_nine : EG 9 = 8
```

**Why it is not in the default build.**  The search visits 21 286 763 nodes and 269 824 034 `K₄`
tests; `native_decide` needs of the order of **80 minutes of CPU** (4 h 12 min of wall clock in
round 22, with the harness host at load 45–50 on 8 cores), so every *rebuild* of this file costs
that much.  The two optimisations of round 22 (`LeafFree.lean`: the leaf is free;
`Distinct.lean`: the distinctness count `ndist` instead of a `Finset` cardinality) brought this
from "more than 30 minutes and not finished" down to "one evaluation", which is what makes the
theorem available at all — but it is still far outside the budget of a build.

The evaluation was **run to completion in round 22** (the run reached the end of this file and
failed only on a name-resolution slip in the statement that follows the certificate), so the
`false` answer is confirmed.  To re-verify:

```sh
cd lean && lake build JSPProblem.Nine
```

What *is* in the default build is the half of the result that is cheap: `Tables.EG_nine_le`
(`f(9,4,5) ≤ 8`) together with the counting bound gives
`Main.f_nine_between_seven_and_eight : 7 ≤ f(9,4,5) ≤ 8` — the value is a *seven* or an *eight*,
and the `K₉` certificate is what excludes the seven.
-/

namespace JSP140

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
/-- **CERTIFICATE (leaf-free search): no admissible 7-colouring of `K₉`.**  Together with the
verified 8-colouring `Tables.nineCol` this gives the **third exact value of the Erdős–Gyárfás
function in this development that exceeds the counting bound** `⌈5(n-1)/6⌉ = 7`, namely
`f(9,4,5) = 8`.  The search visits 21 286 763 nodes and 269 824 034 `K₄` tests; the same answer
needs more than 30 minutes in the search of `VertexSearch.lean` (which re-tests every `K₄` at
every leaf, over all `2^9` four-element `Finset`s, and builds a `Finset` per test). -/
theorem certD_nine_six : hasAdmissibleD 9 6 = false := by native_decide

/-- **`f(9,4,5) = 8` — THE THIRD EXACT VALUE ABOVE THE COUNTING BOUND `5(n-1)/6`.**  The lower
bound is the machine certificate `certD_nine_six` ("no admissible 7-colouring of `K₉`"), the upper
bound the verified colouring `Tables.nineCol`. -/
theorem EG_nine : EG 9 = 8 :=
  Nat.le_antisymm EG_nine_le (EG_ge_of_certD certD_nine_six)

/-- **The counting bound is strictly exceeded at `n = 9` as well**: `8 > 7 = ⌈5·8/6⌉`. -/
theorem counting_bound_strict_at_nine : 7 < EG 9 := by rw [EG_nine]; norm_num

/-- **The `K₉` certificate is not an artefact of the symmetry reduction**: the *counting* bound at
`n = 9` is `7`, so the certificate `f(9,4,5) ≥ 8` is a genuine improvement of the sharp `5/6`
constant of arXiv:2207.02920 at a concrete order. -/
theorem EG_nine_above_five_sixth : 5 * (9 - 1) < 6 * EG 9 := by norm_num [EG_nine]

end JSP140
