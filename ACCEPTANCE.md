## Status (round 43)

`lake build`: **OK** (3131 jobs).  `sorry`/`admit`: **0**.  `harness/score.py --strict-prize`
(invoked on `problems/JSP-000140/lean`):
`partial_ok = true`, `prize_ready = false`, `missing_theorems = ["jsp_000140_main"]`.

**ROUND 43 PROVES THE PER-VERTEX AND PER-EDGE BUDGETS OF A FIRST STAGE — AND, FROM THEM, THAT A
NEAR-PERFECT MATCHING WITH A SPARSE LEFTOVER MUST HAVE A CENTRE AT *EVERY* VERTEX.**  Round 42
listed the per-vertex budget and the per-edge bound as its `next_lemma` and cut both to keep the build
green; both are in this file, and the per-vertex *edge* accounting that goes with them turned out to
be the sharper object.  `lean/JSPProblem/Edge.lean` grows from 737 to 1655 lines (37 -> 88
declarations, zero placeholders).

### 1. §5 — the per-vertex slot budget (`slots_at_le`)

* **`card_SlotsAtF_eq`** — the colours a family uses at `v` are *exactly* one per member centred at
  `v` and two per member having `v` as a leaf.  Round 42 could only prove `≤`: it did not know that
  the colour projection of the slots at `v` is injective, i.e. that **`SlotFree` holds at one vertex
  and one colour at a time** (`injOn_col_slotsF`).  The ingredients are `mem_slotPair`,
  `card_slotPair`, `mem_cfgSlots_leaf` and `SlotsAtF_eq`;
* **`slots_at_le` — THE PER-VERTEX SLOT BUDGET: `|centF F v| + 2·|leafF F v| ≤ k` for every vertex.**
  This is `Fam.slots_countF` (`5·|F| ≤ nk`, the slot counting of JM §4 that produced the `5/6`) made
  *pointwise*, and with `leafF_card_le` (`2·|leafF F v| ≤ k`) and `centF_card_le`.

### 2. §6 — the per-edge budget (`coverF_card_le`)

* `s_swap`, `coverF_swap`, `coverF_leaf'`, `coverF_leaf''` (the covering-member role analysis of §3,
  in a form that does not mention the three classes), `cover_ABC_disj` and
  **`card_coverF_eq_three`** — the three classes `coverA/coverB/coverC` (a-central, b-central,
  leaf-only) partition the members covering `s(a,b)`;
* `class_slots_le` (the engine: one colour at `v` for a centred class, two for a leaf class) and its
  two instances `coverA_card_le`, `coverB_card_le`;
* **`coverF_card_le` — NO EDGE OF `K_n` IS COVERED BY MORE THAN `2k/3` MEMBERS OF A MATCHING:
  `3·|coverF F (s(a,b))| ≤ 2k`** (and `coverF_card_le'`, at most `k` members).  So with the published
  `k ≈ 5n/6` each edge is covered at most `5n/9` times, while JM (IV)/BCDP Claim 4 allow `n^{1-δ}`
  leftover edges at each vertex: the per-edge budget is what forces the *leftover*, not the covering.

### 3. §7 — the per-vertex edge accounting (`degL_at`)

* `spokes`, `card_spokes`, `edgesAt`, `card_edgesAt`, `mem_edgesAt`, `covAt`,
  **`card_covAt` — A CONFIGURATION COVERS TWO OF ITS THREE EDGES AT EACH OF ITS VERTICES** (at the
  centre: the two spokes; at a leaf: the spoke *and the opposite edge* — this is round 43's correction
  of the round-43-draft, which wrongly counted one edge at a leaf);
* `card_throughF` (the members through `v` are the centred ones and the ones having `v` as a leaf),
  `covAll`, **`card_covAll` — the covered edges through `v` number `2·(|centF F v| + |leafF F v|)`**,
  **`covAll_eq_inter` — they are exactly `edgesAt v ∩ coveredF F`**, `covR`, `card_covR`,
  `covAll_covR_disj`, `edgesAt_eq_union`;
* **`degL_at` — THE PER-VERTEX EDGE ACCOUNTING:
  `n - 1 = 2·(|centF F v| + |leafF F v|) + DegL (leftoverF F) v`**, the local form of
  `Fam.edgeCoverF`.

### 4. §8 — the density a sparse leftover forces

* **`throughF_card_ge` — `2·(|centF F v| + |leafF F v|) ≥ (n-1) - D`**, i.e. *every* vertex is
  passed through by at least `⌈((n-1-D)/2)⌉` members: JM (IV) / BCDP Claim 4, per vertex
  (compare `First.SparseL_iff_degTris`);
* **`centF_card_ge` — `|centF F v| ≥ (n-1-D) - k`** (from the density and the slot budget), and
  `leafF_card_ge`; this is the *local* form of the slot counting `First.count_lower`, and it says a
  first stage cannot hide its work at a few centres and pay for it with leaves;
* **`centF_card_ge_one` / `centre_cover_univ` — IF `(n-1) - D > k` THEN EVERY VERTEX IS THE CENTRE OF
  AT LEAST ONE MEMBER**, and `sum_centF_card_ge` (the global `|F| ≥ n(n-1-D-k)`);
* `throughF_card_eq` — `|throughF F v| = |centF F v| + |leafF F v|`.

### 5. NOT proved this round

The existence of the matching itself, i.e. `Partial.FamGreedyFamily`: for every `δ > 0` and all large
`m ≡ 1 (mod 6)` a *near-perfect* matching in `H` with a sparse leftover, no bad and no crossing
four-set, and `6(k+2D+1) ≤ 5(m-1) + δm`.  Round 40 retired plain maximality (`Hyper.greedy_gap`), round
41 retired maximality-with-avoidance (`Spoil.avoid_price`), and rounds 42–43 now give *three further
necessary conditions on its witness* (the per-vertex budget, the per-edge bound, and a centre at every
vertex) that no maximality rule produces.  The obstacle is unchanged and is the density of the
matching, not the local conditions: the Rödl nibble / differential-equation method / random triangle
removal, none of which Mathlib contains.
`pairFree_of_admissible`; B4 (`f(10,4,5) ∈ {8,9}`, `f(11,4,5) ∈ {9,10}`); B5 (`K₁₃` with ten colours)
— unchanged.

## Status (round 41)

`lake build`: **OK** (3130 jobs).  `sorry`/`admit`: **0**.  `harness/score.py --strict-prize`
(invoked on `problems/JSP-000140/lean`):
`partial_ok = true`, `prize_ready = false`, `missing_theorems = ["jsp_000140_main"]`.

**ROUND 41 COMPUTES THE FIRST-MOMENT ESTIMATE OF arXiv:2208.12563 §4 AS A THEOREM, AND PROVES —
AS A THEOREM — THAT MAXIMALITY-WITH-AVOIDANCE CANNOT CERTIFY THE CATALOG BUDGET FOR ANY CHOICE OF
THE FOUR-SET CONDITIONS.**  Rounds 31–40 reduced the prize to the existence of a *near-perfect
matching* in the auxiliary hypergraph `H`; round 40 retired the *plain greedy* way of getting one.
The papers do not use maximality: they take a **partial** matching which avoids the hyperedges that
would create a bad four-set, and they bound the number of those **spoiled** hyperedges by a first
moment.  That estimate is a *finite counting statement about `H`* — no probability, no Rödl nibble,
no local lemma — and this file computes it.  New file `lean/JSPProblem/Spoil.lean` (785 lines,
27 declarations, zero placeholders).

### 1. §1 — the four-set census of `H`

* **`card_fours_sup` / `card_fours_tri` — EXACTLY `n - 3` FOUR-SETS CONTAIN A GIVEN TRIANGLE** (a
  configuration of `H` has three vertices).  This is the ingredient that turns a set of bad
  four-sets into a set of spoiled hyperedges: **each spoiled hyperedge lies in at most `n-3`
  four-sets.**
* **`card_auxF_four` — THE FOUR-SET CENSUS OF `H`: EXACTLY `24·k(k-1)` HYPEREDGES OF `H` HAVE THEIR
  THREE VERTICES IN A GIVEN FOUR-SET** (twelve ordered triples of distinct vertices out of four,
  times `k(k-1)` ordered pairs of distinct colours).  One bad four-set therefore spoils *exactly*
  `24k(k-1)` hyperedges, whatever "bad" means.
* `cfgVerts_sub_iff`, `card_filter_le`, `sum_ite_mem_card`, `sum_ite_filter_card` — the counting
  tools (the last two are the indicator-sum identities used throughout).

### 2. §2 — spoiled hyperedges: both sides of the first moment

* **`spoilF B`** — the hyperedges of `H` lying inside one of the four-sets of `B`;
* **`spoil_double` — THE DOUBLE COUNT** of the pairs `(hyperedge, bad four-set containing it)`,
  from either side;
* **`card_spoilF_le` — UPPER SIDE: `|B|` bad four-sets spoil at most `24·k(k-1)·|B|` hyperedges;**
* **`card_spoilF_ge` — LOWER SIDE: they spoil at least `24·k(k-1)·|B|` hyperedges `n-3` times over;**
* **`spoil_squeeze` — THE TWO SIDES TOGETHER: `24·k(k-1)·|B| ≤ (n-3)·|spoilF B| ≤ 24·k(k-1)·|B|`.**
  Bad four-sets and spoiled hyperedges are equivalent up to a factor `n-3`, and the four-set
  direction is exact.  This is the whole content of the first moment of §4, deterministically.

### 3. §3 — the avoidance rule, and its price

* **`SlotFresh`, `AvoidClosed`** — the rule "add a hyperedge whenever it is unblocked and
  unspoiled", and its fixed point;
* **`card_blocked_le`, `closed_census` — THE CENSUS OF A CLOSED FAMILY:
  `|E(H)| ≤ 25(n-1)(n-2)(k-1)·|F| + |spoiled|`** (every hyperedge of `H` is blocked by a slot of
  `F`, or is unblocked and hence spoiled);
* **`avoid_first_moment` — WHAT THE RULE DELIVERS:
  `n(n-1)(n-2)·k(k-1) ≤ 25(n-1)(n-2)(k-1)·|F| + 24·k(k-1)·|B|`;**
* **`avoid_certify` — THE PRICE OF THE FOUR-SET CONDITIONS: `25·|F| + n ≥ n·k` as soon as
  `24k·|B| ≤ n(n-1)(n-2)`** — a four-set condition costing `o(n²)` four-sets costs the rule at most
  `n` slots out of `n·k`;
* **`avoid_gap` / `avoid_gap_of_budget` / `avoid_price` — AND THE PUNCHLINE.**  At `δ ≤ 1/6`, with
  the catalog budget `6k ≤ (5+δ)n − 11`, the best size the rule can certify is at most
  `n((5+δ)n−17)/150`, and that is **strictly below** `n((7−δ)n−1)/42`, the size every valid first
  stage must have (`Hyper.first_stage_size`).  So **maximality-with-avoidance cannot certify the
  budget, whatever the four-set conditions are**: the Rödl nibble is needed for the *matching
  itself*, not for the local conditions.  This is the strict generalisation of round 40's
  `Hyper.greedy_gap` to a strictly stronger deterministic rule.

### 4. §4 — the bridge back to the catalog condition

* **`badFours`, `mem_badFours`, `badFours_eq_empty_iff` — `Admissible c ↔ badFours c = ∅`:**
  the set of four-sets a colouring fails on, and the equivalence with the catalog condition;
* **`spoilF_empty_of_admissible`** — an admissible colouring spoils no hyperedge at all, i.e. the
  four-set conditions of §4 are exactly the filter of the avoidance rule.

**NOT proved this round.**  The existence of the near-perfect matching
(`Partial.FamGreedyFamily`, the single remaining prize hypothesis).  §2–§3 above now *prove* that
the first-moment counting of the local conditions is available and cheap, and that the resulting
deterministic rule is short of the budget by a factor `≈ 25/7 · 7/(5+δ) > 4`; the missing step is
the one that is genuinely probabilistic (Rödl nibble / differential-equation method / random
triangle removal), and Mathlib has neither.  `pairFree_of_admissible`, B4 (`f(10,4,5) ∈ {8,9}`,
`f(11,4,5) ∈ {9,10}`) and B5 (`K₁₃` with ten colours) are unchanged.

## Status (round 40)

`lake build`: **OK** (3129 jobs).  `sorry`/`admit`: **0**.  `harness/score.py --strict-prize`
(invoked on `problems/JSP-000140/lean`):
`partial_ok = true`, `prize_ready = false`, `missing_theorems = ["jsp_000140_main"]`.

**ROUND 40 ATTACKS THE EXISTENCE SIDE FOR THE FIRST TIME IN THE MATCHING WORLD, AND PROVES — AS A
THEOREM, NOT AS PROSE — THAT THE CHEAPEST DETERMINISTIC CONSTRUCTION CANNOT WORK.**
Rounds 31–39 only *assumed* the first stage exists.  This round builds the auxiliary `8`-uniform
hypergraph `H` of arXiv:2208.12563 §4 (= arXiv:2207.02920 Phase 1) as **data**, computes it exactly,
and then runs the *whole* of the greedy / maximal-matching argument on it.  New file
`lean/JSPProblem/Hyper.lean` (831 lines, 51 declarations, zero `sorry`).

### 1. §1 — `H` as data, and its census

The hypervertices of `H` are the slots `Verts n × Fin k`; its hyperedges are the five-slot sets of
the well-formed configurations.

* **`auxF`, `mem_auxF`, `OkF_iff`** — the edge set of `H`, and `OkF F ↔ F ⊆ auxF n k`.
* **`card_auxF` — THE CENSUS OF `H`: `|E(H)| = n(n-1)(n-2)·k(k-1)`.**  Three pairwise distinct
  vertices and two distinct colours.  No colouring, no four-vertex clique, no probability anywhere.
  (The ingredients `card_offdiag` — ordered pairs of distinct vertices avoiding a given one — and
  `sum_ite_ne` — `k(k-1)` ordered pairs of distinct colours — are proved too.)

### 2. §2 — the degree of a hypervertex of `H`

* **`card_ok_centre`** — the hyperedges prescribing the centre slot number exactly
  `(n-1)(n-2)(k-1)` (the other two vertices avoid `x` and each other, the other colour avoids `c`);
* **`swapUP`, `swapPQ`, `swapIJ`** (each an `Equiv`, each preserving `Ok`) and the four transfer
  lemmas `card_ok_leafP`, `card_ok_leafQ`, `card_ok_leafPJ`, `card_ok_leafQJ` — a prescribed *pair* of
  slots may be moved to any other pair, so one count suffices;
* **`card_auxDeg_le` — THE DEGREE OF A HYPERVERTEX OF `H`:
  `|{ g ∈ H : σ ∈ slots g }| ≤ 5(n-1)(n-2)(k-1)`.**  Exact.

### 3. §3 — the greedy (maximal-matching) argument, in full

* **`SlotMaximal`** — no hyperedge of `H` outside `F` is slot-disjoint from `F`; this is exactly the
  output of a greedy hypergraph-matching algorithm;
* **`blockedF`, `blocked_card_le`** — at most `25(n-1)(n-2)(k-1)` hyperedges share a slot with a fixed
  member of `F`;
* **`card_auxF_le_of_maximal`** — the double count `|E(H)| ≤ |Slots F|·5(n-1)(n-2)(k-1)`;
* **`greedy_guarantee` — WHAT THE TRIVIAL ARGUMENT PROVES: `25|F| ≥ n·k`, i.e. `|F| ≥ nk/25`.**
  This is the *entire* content of the nibble-free argument: a maximal matching covers at least
  `3nk/25` edges of `K_n`, about a fifth of them.

### 4. §4 — what the catalog budget demands, and the gap

* **`budget_k_le`** (`6k ≤ (5+δ)n − 11`) and **`budget_le_D`** (`7D + 6 ≤ δn`, the converse
  direction of `First.proper_fits`), from the budget and the slot counting;
* **`first_stage_size` — WHAT THE BUDGET FORCES: `42|F| ≥ n((7-δ)n − 1)`, i.e. `|F| ≈ n²/6`** — more
  than five times what §3 delivers;
* **`leftover_frac_le`**, **`leftover_frac_le_of_small`** — the leftover is at most a `δ/7`-fraction
  of the edges, and **at the published `δ ≤ 1/6` it is at most `1/42` of them**: the first stage must
  cover more than `41/42` of `E(K_n)`;
* **`greedy_gap` — THE GAP: `42nk < 25n((7-δ)n−1)` for `δ ≤ 1/6`, `n ≥ 1`**, i.e. the greedy
  guarantee `nk/25` is strictly below the size of every valid first stage, by a factor
  `42(5+δ)/(25(7-δ)) > 4`;
* **`greedy_short`, `no_greedy_first_stage`** — every valid first stage has `25|F| > n·k`, and **no
  family of size at most `nk/25` satisfies the published budget**.  The Rödl nibble / random triangle
  removal is therefore *necessary*, and this is now a theorem of the development rather than a remark.

*Honest scope*: `greedy_guarantee` and `first_stage_size` are both **lower bounds** on `|F|` and are
mutually compatible — a maximal family may be lucky.  What is proved is that the *guarantee* the
trivial argument delivers is short of what the budget requires by a factor `> 4`, so maximality can
never *certify* a first stage.

### 5. §5 — what the prize hypothesis says about its witness

* **`witness_size`** — reading the two theorems off `Partial.FamGreedyFamily`: for `δ ≤ 1/6` any
  family paying the budget has more than `n((7-δ)n−1)/42` members and leaves at most `1/42` of the
  edges uncovered.  So the object of arXiv:2208.12563 §4 is a *near-perfect* hypergraph matching.

**NOT proved this round.**  The existence of that matching: it is a hypergraph-matching existence
theorem (Rödl nibble / differential-equation method / random triangle removal); Mathlib has neither a
nibble nor a local lemma, and both papers are existential, so there is no colouring to write down.
§3–§4 above now *prove* that this is a real obstruction rather than an omission of effort.
`pairFree_of_admissible`, B4 (`f(10,4,5) ∈ {8,9}`, `f(11,4,5) ∈ {9,10}`) and B5 (`K₁₃` with ten
colours) are unchanged.

## Status (round 39)

`lake build`: **OK** (3128 jobs).  `sorry`/`admit`: **0**.  `harness/score.py --strict-prize`
(invoked on `problems/JSP-000140/lean`):
`partial_ok = true`, `prize_ready = false`, `missing_theorems = ["jsp_000140_main"]`.

**ROUND 39 CLOSES THE ROUND-38 BLOCKER COMPLETELY: `Tile` AND `Packed` OF THE FINISHED COLOURING
ARE FREE, AND THE REQUIRED THEOREM IS REDUCED TO THE PUBLISHED FIRST STAGE WITH AN ARBITRARY
LEFTOVER AND A DETERMINISTIC SECOND STAGE.**
`lean/JSPProblem/Partial.lean` grows from 437 to 1038 lines (20 -> 47 declarations, zero `sorry`).

*Section 4 — the leaf half of the tiling condition* (the lemma round 38 isolated as `next_lemma`):

* `partner_coverNbrs` — the edge from `v` to a covered colour-`i` neighbour of `v` is an edge of
  the member holding the slot `(v,i)` (the forcing step of `coverNbrs_mem`, isolated);
* `coverNbrs_card_le_one_of_leaf` — **a leaf of the slot graph has at most one covered colour-`i`
  neighbour** (the four partner lemmas force it to be a single vertex);
* `coverNbrs_eq_pair_of_card_two` — **TWO COVERED NEIGHBOURS MEAN A CENTRE**: `v` is the centre of
  the member holding `(v,i)`, `i = cfgI g`, and the two neighbours are exactly its two leaves;
* **`coverNbrs_card_one_of_mem_card_two`** — **the leaf half of `Criterion.Tile` for a partial first
  stage**: each of the two has covered colour-degree exactly one;
* `coverNbrs_eq_singleton_of_card_two` — the same in the form `{centre}`, and `edgeCol_spoke_leaf`
  (a spoke of a configuration carries the centre colour).

*Section 5 — the finished colouring.*  With `c := extendColDep (colOf F d) (leftoverF F) g`
(the first-stage colours kept, every leftover edge given a fresh colour):

* `finCol`, `extendColDep_finCol_of_leftover`, `covered_of_nmem_leftoverF`, **`mem_Nbrs_finCol`**
  and `card_Nbrs_finCol` — **the bridge**: for a first-stage colour `i` and `a ≠ v`,
  `a` is an `i`-neighbour of `v` in the finished colouring **iff** it is a *covered* `i`-neighbour
  of `v` in the matching; and an edge of the leftover never receives a first-stage colour;
* `card_le_one_of_fresh` — **a fresh colour has colour-degree at most one**, by `Proper`;
* **`tile_of_fam_partial`** — **`Tile c` from `OkF + LinF + SlotFree + Proper` alone**: degree half
  from `coverNbrs_card_le_two`, leaf half from `coverNbrs_card_one_of_mem_card_two`, fresh case from
  `Proper`.  No `Covers`, no bound on the leftover;
* `mem_twoA_card_two`, **`pathSet_eq_cfgVerts`** — the two-edge paths of the finished colouring are
  *exactly* the three vertices of the members of `F`, with their centre colours;
* **`packed_of_fam_partial`** — **`Packed c` from the same hypotheses** (`cfgVerts_lin`).

*Sections 6–7 — the reduction.*

* **`FamPartialFamily`** — the published construction in the form it actually has: for every
  `δ > 0` and all large `m ≡ 1 (mod 6)` a matching `F` in the auxiliary hypergraph of
  arXiv:2208.12563 §4 / arXiv:2207.02920 Phase 1, a **sparse leftover** (`SparseL D`, = JM (IV) of
  Thm 4.2 = BCDP Claim 4), a **proper** second stage (`A_{e,f,i}` resp. `B₁`), the two four-set
  conditions (`B_D`, `C_{D,i}`) and the budget `6(k+K) ≤ 5(m-1) + δm`.  **No colouring is
  quantified over**: `F` is a finset of configurations and `g` is its second-stage colouring.
  **No complete covering is required** — this is the published (partial) covering, in contrast with
  round 37's `FamFamily`;
* `FamPartialFamily.admissible`, `FamPartialFamily.slack`,
  **`jsp_000140_main_of_fam_partial_family`** — the required theorem reduced to it;
* **`greedyF`, `proper_greedyF`** — the **deterministic** second stage: if the leftover has maximum
  degree `D`, the greedy edge colouring of `Second.proper_of_sparseL` gives a proper colouring of
  the leftover with `2D+1` fresh colours, so `Proper` need not be a hypothesis at all;
* **`FamGreedyFamily`, `famGreedyFamily_partial`, `jsp_000140_main_of_greedy_family`** — the sharpest
  interface found so far: the leftover's *sparsity* alone pays for the second stage, and what is
  left is (i) the matching in the auxiliary hypergraph, (ii) its leftover degree, (iii) the
  exclusion of the alternating four-cycles and the crossing pairs — the only genuinely probabilistic
  part of the two papers.

**NOT proved this round.**  The existence of the first stage: the hypergraph matching of
arXiv:2208.12563 §4 (Thm 4.2) / the random triangle removal of arXiv:2207.02920, together with the
two four-set conditions of its second stage.  Mathlib has neither a Rödl nibble nor a local lemma.
`jsp_000140_main` therefore remains undeclared: the reduction theorems have the honest hypothesis
`FamGreedyFamily`, which is a probabilistic existence statement.

## Status (round 38)

`lake build`: **OK** (3128 jobs).  `sorry`/`admit`: **0**.  `harness/score.py --strict-prize`
(invoked on `problems/JSP-000140/lean`):
`partial_ok = true`, `prize_ready = false`, `missing_theorems = ["jsp_000140_main"]`.

**ROUND 38 REMOVES THE COMPLETE-COVERING REQUIREMENT FROM TWO OF THE FOUR LOCAL CONDITIONS.**
Round 37 could only close the *extremal* first stage (`FamFamily` demands `leftoverF F = ∅`),
because `Tile` and `Packed` were imported from `Triangles.lean`, where they are consequences of
`Covers`.  New file `lean/JSPProblem/Partial.lean` (437 lines, 20 declarations, zero `sorry`)
attacks that blocker, and the mechanism is one lemma:

* **`colSlot_covered` — THE SLOT LEMMA.**  If a **covered** edge `s(v,a)` has colour `i` in the
  induced colouring `colOf F d`, then the member covering that edge uses the **slot** `(v,i)`.
  Since `SlotFree` admits at most one member per slot, **every colour-degree of the induced
  colouring of an arbitrary matching in the auxiliary hypergraph is at most two — with no
  `Covers` hypothesis and no bound whatsoever on the leftover.**  This is `Criterion.Tile`'s
  degree half, and it is *free*.
* **`coverNbrs_mem`** — the **explicit classification** of a covered colour-`i` neighbour of `v`:
  a leaf if `v` is the centre of the member holding the slot `(v,i)`, the centre if `v` is a leaf,
  the other leaf if the colour is the `cfgJ` colour.  (This is the local form of
  `Cherry.leaf_not_centre`.)  With `partner_of_centre`, `partner_of_leaf`, `partner_of_leafJ`,
  `partner_of_leafJ'` it is the whole combinatorics of a two-edge path in the matching world.
* **`coverNbrs_card_le_two`** — **THE COLOUR-DEGREE BOUND IS FREE.**
* **`cfgVerts_lin` — THE PACKING CONDITION IS FREE.**  Two members whose triples meet in two
  vertices share an edge, so `LinF` forces them to be equal: the triples of the members of a
  family form a **partial Steiner triple system**.  This is `Criterion.Packed` outright, again
  with no complete covering.

**NOT proved this round.**  The **leaf half** of the tiling condition
(`coverNbrs_card_one_of_mem_card_two`: a vertex with two covered colour-`i` neighbours gives each
of them exactly one), hence `Tile` and `Packed` of the **finished** colouring, hence the reduction
`jsp_000140_main_of_fam_partial_family` to a leftover-tolerant first stage.  The draft of that
chain and the exact failing tactics are recorded in `discovery/JSP-000140/policy.json`
(`next_lemma`); it is mechanical once the leaf half is in.  The single remaining *existence*
object is unchanged (the hypergraph matching of arXiv:2208.12563 §4 / arXiv:2207.02920 Phase 1).

## Status (round 37)

`lake build`: **OK**.  `sorry`/`admit`: **0**.  `harness/score.py --strict-prize`
(invoked on `problems/JSP-000140/lean`):
`partial_ok = true`, `prize_ready = false`, `missing_theorems = ["jsp_000140_main"]`.

**ROUND 37 CHANGES THE SHAPE OF THE RESIDUAL HYPOTHESIS: THE FIRST STAGE IS NO LONGER A
COLOURING BUT A MATCHING IN THE AUXILIARY HYPERGRAPH.**

Every hypothesis of this development up to `First.PartialStageFamily` is stated for a colouring
`c : Col n k`.  That is the wrong way round for an *existence* theorem: what
arXiv:2207.02920 (Phase 1) and arXiv:2208.12563 (§4, Thm 4.2) produce is a **matching in an
auxiliary `8`-uniform hypergraph** whose hypervertices are the `(vertex, colour)` slots, and the
colouring of `K_n` is a *consequence* of that matching.  New file `lean/JSPProblem/Fam.lean`
(1021 lines, 55 declarations, zero `sorry`) makes that object the primitive one.

* **A CONFIGURATION is data**: `Cfg n k = Verts n × Verts n × Verts n × Fin k × Fin k` — centre,
  two leaves, the colour at the centre, the colour of the opposite edge — with `cfgEdges` (the
  hyperedge: three edges of `K_n`), `cfgSlots` (the five hypervertices of arXiv:2208.12563 §4),
  `edgeCol`, `Ok`; a **family** `F : Finset (Cfg n k)` with `OkF`, `LinF` (two members share no
  edge), `SlotFree` (**the matching condition**: two members share no slot), `coveredF`, `leftoverF`.

* **The slot counting of round 36, with no colouring anywhere**: `card_cfgSlots` (5),
  `card_cfgEdges` (3), `card_SlotsF` (`5·|F|`), **`slots_countF`** (`5·|F| ≤ n·k`),
  `card_coveredF` (`3·|F|`), **`edgeCoverF`** (`C(n,2) = 3·|F| + |leftoverF|`), `handshakeF`
  (`2·|leftoverF| ≤ n·D`), **`count_lowerF`** (`5(n-1) ≤ 6k + 5D`), `count_lowerF_tight`,
  `first_stage_numbersF`.

* **THE COLOURING IS INDUCED, AND THE ENCODING IS AN EQUIVALENCE.**
  `colOf F d` is the colouring prescribed by the matching; `mem_cfgSlots_end` (every endpoint of an
  edge of a configuration uses the slot of that edge's colour) and `eq_long_of_same` (two edges of a
  configuration with the same colour are the two edges at its centre) are the combinatorics of the
  hyperedge; then **`labTri_of_mem`** (a member of the family is a labelled triangle of `colOf`),
  **`covers_colOf`** and **`pairFree_colOf`** (a family covering `E(K_n)` *is* a labelled-triangle
  system in the sense of `Triangles.lean`), with the converse
  **`mem_or_mem_swap_of_labTri`** / `mem_or_mem_swap_of_labTri'` — every labelled triangle of
  `colOf` comes from **one** member of the family, because the slot `(u,i)` is shared by the two
  configurations covering the two edges at the centre and `SlotFree` forces them to coincide.

* **`FamFamily` and `jsp_000140_main_of_fam_family`**: the required theorem `jsp_000140_main`
  reduced to the existence, for every `δ > 0` and all large `m ≡ 1 (mod 6)`, of a matching in the
  auxiliary hypergraph (a finset of configurations, pairwise edge- and slot-disjoint, covering all
  of `E(K_m)`, with no bad and no crossing four-set in the induced colouring, and at most
  `5(m-1)/6 + δm/6` colours).  **No colouring is quantified over in the hypothesis**, so it is a
  finite combinatorial condition on a finset — a checkable object, which is what a construction can
  actually provide.

* **THE CENTRE BALANCE (section 5)**: `centF`, `leafF`, `throughF`; `slotsAt` with
  `slotsAt_centre` (exactly **one** slot at the centre), `slotsAt_leaf`/`slotsAt_leaf'` (exactly
  **two** at a leaf), `slotsAt_ne` (none elsewhere), `card_slotsAt`; and
  **`card_slotsF`** — the slots a family uses at `v` are one per configuration centred at `v` and
  two per configuration having `v` as a leaf:
  `(slotsF F v).card = (centF F v).card + 2·(leafF F v).card`, with `card_slotsF_le` (`≤ k`).

**NOT proved this round (blockers B1, B2 in `discovery/JSP-000140/policy.json`)**:
`FamFamily` is an existence theorem about a hypergraph matching (Rödl nibble / differential-equation
method), and Mathlib has neither.  Moreover the interface proved here needs a **complete** covering,
because `pairFree_colOf` (hence `tile_of_tri`/`packed_of_tri`, and with them the automatic `Tile`
and `Packed`) needs `Covers`; with a leftover the uncovered edges carry the default colour and
spurious labelled triangles appear.  The published Phase 1 leaves `Θ(n^{2-δ})` edges over
(BCDP §4: the matching stops at `i_max = (1/6)n²(1-n^{-δ})`), so the complete interface is the
*extremal* case and the partial one needs `Tile`/`Packed`/`LeafClosed`/`CrossThin` ported to
configurations.  That port is the single next step (policy `next_round_plan` item 1).

# ACCEPTANCE — JSP-000140

## Catalog statement (record `JSP-000140`, fetched 2026-09-30)

> **JSP-000140 · How many edge colors are necessary if every four-vertex clique must contain
> at least five colors?**
>
> | Field | Value |
> | --- | --- |
> | Mathematical area | Graph theory |
> | Date proposed | No later than 1997 (bibliographic evidence) |
> | Current status | **Solved** |
> | Lean proof (catalog) | **No** |
> | Publications | `[BCDP22]` arXiv:2207.02920 — *The Erdős–Gyárfás function `f(n,4,5) = 5n/6 + o(n)` — so Gyárfás was right*, **by Patrick Bennett, Ryan Cushman, Andrzej Dudek, Paweł Prałat** (round 13 correction: the authors are *not* Banerjee–Bradshaw–Letzter–Pokrovskiy, and the construction is **probabilistic** — a randomised process based on *random triangle removal*, analysed with the differential-equation method — so there is no explicit colouring to formalise); `[JoMu22]` arXiv:2208.12563 |

The quantity asked for is the **Erdős–Gyárfás function** `f(n, p, q)`, i.e. the least number
of colours in an edge-colouring of `K_n` in which every `K_p` spans at least `q` colours,
specialised to `f(n, 4, 5)`.  The solved answer is

    f(n, 4, 5) = 5n/6 + o(n).

## Required theorem

`jsp_000140_main` — the Lean name that the prize gate checks.  It must be the **complete**
catalog statement, i.e. `f(n, 4, 5) = 5n/6 + o(n)`, proved with no `sorry`.  In this
development the statement is

```lean
JSP140.jsp_000140_target : Prop := JSP140.FiveSixth JSP140.EG
JSP140.FiveSixth f : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |(f n : ℝ) - 5 * (n : ℝ) / 6| ≤ ε * n
```

with `JSP140.EG n` the least number of colours in an admissible colouring of `K_n`
(`lean/JSPProblem/Definitions.lean`), and

```lean
JSP140.Admissible c : Prop :=
  ∀ S : Finset (Fin n), S.card = 4 → 5 ≤ (JSP140.colorsOn c S).card
```

the catalog condition ("every four-vertex clique contains at least five colours").

## Status (round 36)

`lake build`: **OK** (3126 jobs).  `sorry`/`admit`: **0** (`placeholder_total = 0`).
`harness/score.py --strict-prize` (invoked on `problems/JSP-000140/lean`):
`build_ok = true`, `partial_ok = true`, `prize_ready = false`,
`missing_theorems = ["jsp_000140_main"]`.

**ROUND 36 PROVES THE SLOT COUNTING — THE CONSTANT `5/6` IS NOW A THEOREM ABOUT THE FIRST STAGE
ALONE, AND THE CATALOG BUDGET IS SHOWN TO BE *EQUIVALENT* TO THE FIRST STAGE'S COLOUR BOUND.**  This
closes the blocker that round 35 had to isolate as a hypothesis (`First.FirstStageCounting`), so the
residual prize hypothesis no longer contains any counting axiom.

### 1. New file `lean/JSPProblem/Slot.lean` (497 lines, 24 declarations, zero placeholders)

* **`triPairs_eq_anchorPairs`** — THE INGREDIENT ROUND 35 WAS MISSING.  The five `(vertex, colour)`
  pairs of a labelled triangle `(u,p,q)` are the *anchor* pairs of its **vertex set**: `(x,j)` with
  `x ∈ T` and `j` the colour of an edge of the triangle at `x`.  So the slot count is a function of
  the vertex set and of the colouring, and round 35's impossible "canonical labelling"
  (`lab : triSet c → …` cannot be total, `Fin 0` being `Empty`) is simply not needed: `triSets c` is
  the *image* of the finset of labelled triangles, so no representative is ever chosen;
* **`card_triPairs`** — five distinct pairs per triangle (the hypervertices `{u_i,v_i,w_i,v_j,w_j}`
  of the auxiliary `8`-uniform hypergraph `H` of arXiv:2208.12563 §4);
* **`slots_five`** — **THE SLOT COUNTING**, `5 · |triSets c| ≤ n · k`: the slots of two different
  triangles are disjoint (`PairFree.of_common`), and there are `n·k` of them;
* **`edgeCover_count`** — **THE OTHER HALF**, the exact identity `C(n,2) = 3·|triSets c| + |leftover c|`:
  every edge of `K_n` lies in a unique labelled triangle or is leftover;
* **`sum_DegL_two_mul_card`, `handshake_le`** — the **handshaking lemma** `2·|L| ≤ n·D` for a leftover
  of maximum degree `D` (round 35 had only the weaker `|L| ≤ n·D`, which is why its slack was `10D`);
* `lin3_triSets` — two triangles of the system sharing an edge are the same triangle, so the triangle
  system is **linear** (this is where `PairFree` is consumed).

### 2. `lean/JSPProblem/First.lean` §6 — fourteen new theorems

* **`count_lower` — THE SLOT COUNTING AS A THEOREM: `5(n-1) ≤ 6k + 5D` from `PairFree` and
  `SparseL (leftover c) D` alone.**  **No four-vertex clique is checked anywhere in this proof**, so
  the constant `5/6` of the catalog answer follows from the hypergraph-matching structure of the first
  stage by itself: five slots buy three edges;
* **`count_lower_tight`, `tight_attained_of_le`** — for a *complete* covering (`D = 0`):
  `5(n-1) ≤ 6k`, attained or strictly exceeded, never fallen short of;
* **`budget_published_iff` — THE SHARP FORM OF THE CATALOG BUDGET.**

      `6(k + 2D + 1) ≤ 5(n-1) + δn  ↔  6k + 5D ≤ 5(n-1) + δn - 7D - 6`,

  i.e. **the budget of the published two-stage construction is not an extra hypothesis**: it *is* the
  first stage's colour bound, with the second stage's `7D+6` (the greedy properness `2D+1`, see
  `proper_fits`) already deducted.  (An earlier draft claimed the budget follows from `7D+6 ≤ δn`
  alone; that is **false** and was deleted — `count_lower` is `≥`, so the slot count must also be
  tight.  The truth is the iff above.)
* **`budget_and_count`** — with `count_lower`, the budget squeezes the first stage's colour count
  into an interval of width `δn`: the published slot count must be asymptotically tight;
* `leftover_eq_leftoverTris` — the leftover of a colouring *is* the leftover of its triangle system;
* **`SparseL_iff_degTris_triSets`** — round 35's density lemma, now for the objects the construction
  actually produces: `SparseL (leftover c) D ↔ 2·degTris (triSets c) v ≥ n-1-D` at every vertex, i.e.
  the first stage must pass through every vertex at least `⌈(n-1-D)/2⌉` times;
* `sum_degL_edgeFinset`, `edge_count_two_mul` — `2·C(n,2) = n(n-1)`;
* `first_stage_numbers` — the three numbers of a first stage (slots, edges, degree) in one statement.

### 3. NOT proved this round (blockers)

* **the existence of the first stage** — `First.PartialStageFamily`, now with its budget rewritten as
  the first stage's colour bound by `budget_published_iff`: an almost-complete linear triple system
  with `PairFree`, no bad/crossing four-set, leaf closure, leftover degree `D`, `o(n)` crossing pairs
  and at most `5(m-1)/6 + (δm-7D-6)/6` colours.  This is JM Thm 4.2 / BCDP Phase 1, a *probabilistic*
  existence theorem; Mathlib has neither the Rödl nibble nor the local lemma, so no amount of
  verification-side work reaches it.
* **the deterministic maximal-matching obstruction** — the cheapest deterministic fragment of the
  existence side, and the `next_lemma` of round 37 (see `policy.json`).
* `pairFree_of_admissible`; B4 (`f(10,4,5) ∈ {8,9}`, `f(11,4,5) ∈ {9,10}`); B5 (`K₁₃` with ten
  colours) — unchanged.

## Status (round 35)

`lake build`: **OK** (3125 jobs).  `sorry`/`admit`: **0**.  `harness/score.py --strict-prize`
(invoked on `problems/JSP-000140/lean`):
`build_ok = true`, `partial_ok = true`, `prize_ready = false`,
`missing_theorems = ["jsp_000140_main"]`.

**ROUND 35 GOES AFTER THE *FIRST* STAGE — AND FINDS THAT THE ROUND-34 INTERFACE IS VACUOUS AND
THAT THE DETERMINISTIC SECOND STAGE IS PROVABLY UNPAYABLE.**  New file
`lean/JSPProblem/First.lean` (696 lines, 47 declarations, zero placeholders).

### 1. The first stage is a linear triple system, and its density is a *per-vertex* condition

`Tri3`/`Lin3`/`degTris`/`covTris`/`leftoverTris` abstract the first stage of arXiv:2208.12563 §4 —
edge-disjoint triangles of `K_n`, one colour each, `(vertex, colour)` pairs of distinct triangles
disjoint — to a **linear family of three-element vertex sets**:

* `card_covTris` — the vertices covered at `v` number `2 · degTris v` (linearity is exactly what
  makes the contributions disjoint);
* `sum_degTris` — `∑_v degTris v = 3 · |Tris|`;
* `deg_le` — `2 · degTris v ≤ n - 1`, the Steiner bound;
* `card_leftover_le_of_SparseL` — the **total** form, `|L| ≤ nD`, the shape a first-moment argument
  produces;

* **`SparseL_iff_degTris` — THE FIRST-STAGE DENSITY LEMMA.**  The leftover graph of the triple
  system has maximum degree at most `D`

      `⟺  2 · degTris v ≥ n - 1 - D`  for every vertex `v`.

  This is the exact, purely combinatorial form of "maximum degree `D = n^{1-δ}`" (JM §4 (IV) /
  BCDP Claim 4): **the first stage must pass through every vertex at least `⌈(n-1-D)/2⌉` times.**

### 2. **THE PRICE OF EVERY SECOND STAGE — the headline of this round**

`FirstStageCounting` (`5(n-1) ≤ 6k + 5D`, the slot counting of JM §4) plus

* **`budget_leftover` — THE ACCOUNTING IDENTITY.**  The catalog budget
  `6(k + fresh) ≤ 5(n-1) + δn` leaves `6 · fresh ≤ 5D + δn` for the second stage.

From that one identity:

* **`proper_fits`** — the **published** second stage (round 31's greedy properness,
  `fresh = 2D + 1`) fits whenever `7D + 6 ≤ δn`; for the published `D = n^{1-δ}` this holds for all
  large `n`.  **The second stage of the papers is PAYABLE; the local lemma is not needed for it.**
* **`deterministic_budget_strong` / `deterministic_budget`** — the deterministic second stage of
  rounds 33/34, which also excludes `B₂ = B_D` and `B₃ = C_{D,i}` with no probability and costs
  `fresh = 2D² + 2D + T + 1`, gives

      `12 D² + 7D + 6T + 6 ≤ δn`,   in particular   **`12 D² ≤ δn`**,  i.e.  `D = O(√(δn)) = o(√n)`.

  For `D = n^{1-δ}` and `δ < 1/2` this is **false for all large `n`**.
* **`deterministic_imp_proper` / `deterministic_ne_proper`** — the two budgets are strictly ordered:
  the round-33/34 budget implies the published one, not conversely.

**This retires a whole attack family.**  The "honest price" of rounds 33/34 was prose; it is now
`deterministic_budget`, a theorem.  **At the published parameters the symmetric local lemma (or
something of its strength) is genuinely necessary for `B₂` and `B₃`** — and a first-moment argument
is no help either, since it also needs `q ≫ D²` while the budget leaves only `fresh ≤ (5D + δn)/6`.

### 3. The interface of round 34 is **vacuous**

`CrossStageFamily` asserts `Covers c₀` — the **complete** covering of round 29 — together with
`SparseL` and `CrossThin` on `leftover c₀`.  But `Covers c₀ ↔ leftover c₀ = ∅`
(`covers_iff_leftover_eq_empty`), so with `D = T = 0` the fresh-colour cost is `1`, and

* **`crossStageFamily_iff_triFamily` : `CrossStageFamily ↔ TriFamily`** (together with
  `crossStageFamily_tri`, `crossStageFamily_of_tri`, `jsp_000140_main_of_cross_iff_tri`).

**The whole second stage of rounds 33 and 34 is dead code with respect to the remaining
hypothesis.**  `PartialStageFamily` is the corrected interface: the first stage may leave `o(n²)`
edges uncovered, `Design` and `LeafClosed` are hypotheses (they are Phase-1 output, and
`tile_of_tri`/`leafClosed_of_tri` need the *complete* covering), and `SparseL`/`CrossThin` are
genuinely non-vacuous.  `crossStageFamily_partial` shows it is at least as general, and
`leftover_card_le` records *why* a total bound is not enough: `AlmostCovers c (n·n)` holds for
**every** colouring.

### 4. NOT proved this round (blockers)

* **the slot counting itself** — `First.count_lower`, `5(n-1-D) ≤ 6k` from `PairFree` alone.  It is
  isolated as the hypothesis `FirstStageCounting`, and every verdict of §2 is proved *from* that
  hypothesis, so none of them depends on its details.  The recipe (all four ingredients derived in
  round 35 and recorded in `policy.json.next_lemma`): `centre_unique` — the centre of a first-stage
  triangle is determined by its vertex set, the Steiner-system-with-a-centre-per-block structure of
  rounds 13/24; `card_triPairs = 5`; the double count `∑_T ∑_v |colTris c T v| = 5·|Σ|`; and the
  injectivity of `(T, v, i) ↦ (v, i)` from `PairFree`.  The obstacle is that a canonical labelling
  of each triple cannot be a *total* function (`Fin 0` is `Empty`).
* **the existence of the first stage** — an almost-complete linear triple system with uniform vertex
  degree, `NoCrossFour`, `NoBadFour`, leaf closure, and a controlled crossing count: this is
  `PartialStageFamily`, and it is the single remaining prize hypothesis.
* `pairFree_of_admissible`; B4 (`f(10,4,5) ∈ {8,9}`, `f(11,4,5) ∈ {9,10}`); B5 (`K₁₃` with ten
  colours) — unchanged.

## Status (round 34)

`lake build`: **OK** (3124 jobs).  `sorry`/`admit`: **0**.  `harness/score.py --strict-prize`
(invoked on `problems/JSP-000140/lean`):
`build_ok = true`, `partial_ok = true`, `prize_ready = false`,
`missing_theorems = ["jsp_000140_main"]`.

**ROUND 34 REMOVES THE OTHER BAD-EVENT FAMILY TOO: THE WHOLE SECOND STAGE OF BOTH PAPERS IS
DETERMINISTIC.**  Round 33 removed `B_D` and declared the last bad event `C_{D,i}`
(= `B₃`) ungreedyable "because it constrains *disjoint* pairs of leftover edges", leaving the
symmetric Lovász Local Lemma as the only remaining probabilistic tool.  **That is a statement about
the colours, not about the combinatorics, and this file corrects it**: what a greedy colouring needs
is a *bound* on the number of partners each edge has, not adjacency.

New file `lean/JSPProblem/Cross.lean` (581 lines, 22 public + 8 private declarations, zero
placeholders):

* **`greedy_of_boundedRel` — THE GENERAL ENGINE.**  For *any* symmetric relation `R` on a finite set
  `F` in which every `e ∈ F` is `R`-related to at most `M` others, there is a map `g : F → Fin (M+1)`
  injective on every `R`-related pair of distinct elements (elements added one at a time by
  `Finset.induction_on`; each new element avoids the colours of the at most `M` already-coloured
  elements related to it).  `Second.rainbow_of_sparse_leftover` is the instance `R = Shares`,
  `M = 2D`; round 33's `star_greedy` is the instance `R = Shares ∨ Sep`, `M = 2D² + 2D`;
* **`Cross` — the crossing relation of `C_{D,i}`** (two crossing leftover edges whose complementary
  pair is covered and phase-1 monochromatic), with `Cross.symm`, `ne_of_Cross`, and
  **`noCrossFresh_of_inj`**: a fresh colouring injective on the `Cross` pairs cannot produce the bad
  event at all — a strictly stronger statement than `NoCrossFresh`, which only asks for distinctness
  when the complementary pair happens to be monochromatic;
* **`crossF`, `card_crossF_le` — THE UNCONDITIONAL BOUND `4n`.**  A partner of `e = s(a,c)` is
  `s(b,d)` with `c₀ s(a,d) = c₀ s(b,c)` (or the same for the other complementary pairing of the
  4-set), so for each of the `≤ n` choices of `b` there are at most two choices of `d` — by the first
  stage's colour-degree bound `Tile` (`tile_of_tri`; for an admissible colouring this is `Cherry`'s
  `5/6` count).  No hypothesis is used, not even sparsity of the leftover;
* **`CrossPairs`, `CrossThin`, `card_crossF_le_of_thin` — THE USABLE BOUND.**  What the first
  stage's analysis has to deliver is a *counting statement about its own output* ("at most `T` pairs
  of crossing leftover edges have a monochromatic complement"), and `card_crossF_le_of_thin` turns
  such a **total** bound — the shape a first-moment argument produces — into the **per-edge** bound
  the greedy engine consumes;
* **`FreshRel` = `Shares ∨ Sep ∨ Cross`, `card_freshRel_le` (`2D² + 2D + T`), `cross_greedy_extend`,
  `second_stage_of_cross` — THE COMPLETE SECOND STAGE.**  `Proper` (`A_{e,f,i}` = `B₁`),
  `NoAltCycle` (`B_D` = `B₂`) and `NoCrossFresh` (`C_{D,i}` = `B₃`) hold *simultaneously* with
  `2D² + 2D + T + 1` fresh colours, given only that the leftover has maximum degree `D` and at most
  `T` crossing pairs.  No probability anywhere;
* **`admissible_of_cross`, `CrossStageFamily`, `SlackFamily.of_cross`,
  `jsp_000140_main_of_cross_stage_family`** — the required theorem `jsp_000140_main` reduced to the
  published construction with **no probabilistic object in the second stage at all**;
* **`CrossThin.mono`, `second_stage_of_cross_wide`** — the fresh-colour cost is monotone in the
  crossing count, so a first stage with *no* crossing pair reproduces exactly the `2D² + 2D + 1`
  fresh colours of round 33.

**THE HONEST PRICE, AND THE CORRECTION TO ROUND 33.**  The deterministic route costs `T` extra fresh
colours over round 33 (`2D² + 2D + T + 1` instead of `2D² + 2D + 1`), where `T` is the crossing-pair
count of the first stage's output; the expected value of `CrossPairs c₀ L` is `Θ(n^{1-2δ})` for the
published `D = n^{1-δ}`, hence `o(n)`, so the budget is unaffected — but the hypothesis is a *new*
one, a density statement about the first stage, and it is **not** implied by round 33's
`StarStageFamily` (which asserts the `C_{D,i}`-avoidance of one particular colouring).  What this
round establishes is therefore: (i) the Lovász Local Lemma is **not needed anywhere** in the second
stage of either paper, and (ii) its content can be replaced by two counting statements about the
output of the first stage — the maximum degree `D` (already known from JM (IV) / BCDP Claim 4) and
the crossing-pair count `T`.

**Abandoned this round:** `StarStageFamily.of_cross` (`CrossStageFamily → StarStageFamily`).  It
was written, then *deleted as false*: `CrossThin c₀ L T` with `T` given cannot yield a colouring
with `2D² + 2D + 1` fresh colours, because the greedy genuinely needs the `T + 1` extra colours of
the crossing pairs it has to separate.  The two families are alternative hypotheses for the same
conclusion, not comparable ones.

## Status (round 33)

`lake build`: **OK** (3123 jobs).  `sorry`/`admit`: **0**.  `harness/score.py --strict-prize`
(invoked on `problems/JSP-000140/lean`):
`build_ok = true`, `partial_ok = true`, `prize_ready = false`,
`missing_theorems = ["jsp_000140_main"]`.

**ROUND 33 REMOVES ONE OF THE TWO BAD-EVENT FAMILIES OF THE PUBLISHED SECOND STAGE: `B_D` IS A
GREEDY MATTER, NOT A PROBABILISTIC ONE.**  Round 32 reduced the required theorem to
`StageFamily`, whose second-stage hypotheses are the properness (already deterministic, round 31)
plus the two bad-event families `B_D` (arXiv:2208.12563 §4 = `B₂` of arXiv:2207.02920 §12) and
`C_{D,i}` (`B₃`), both of which the two papers obtain from the symmetric **Lovász Local Lemma** —
which Mathlib does not contain.

New file `lean/JSPProblem/StarColour.lean` (576 lines, 13 public + 15 private declarations, zero
placeholders) proves that `B_D` never needed the local lemma:

* `Sep L e f` and `Sep.symm` — **two leftover edges separated by a third leftover edge**: the two
  *outer* edges of a path of three leftover edges `a – b – p – q` on four distinct vertices
  (`e = s(a,b)`, `f = s(p,q)`, and `s(b,p) ∈ L` or `s(q,a) ∈ L`).  In a 4-cycle of leftover edges
  these are the two diagonals;
* `StarProper c L` — a fresh colouring which is proper **and** injective on the separated pairs;
* **`noAltCycle_of_starProper` — THE REDUCTION.**  Properness makes neighbouring cycle edges
  differ, separation makes the diagonals differ, so **all four colours of a 4-cycle of leftover
  edges are pairwise distinct** and the cycle spans at least three colours: the bad event `B_D`
  cannot occur.  (Private helper `card_ge_four` does the counting; `cyc_ne` the distinctness of the
  adjacent edges of the cycle.);
* the counting: `NbL` (the leftover neighbours of a vertex, `card_NbL : (NbL L v).card = DegL L v`),
  `wit` (the witnesses `(y,z)` with `s(y,v) ∈ L`, `y,z ∉ e`, `z ≠ y`, `s(z,y) ∈ L`, counted through
  two nested images), `card_wit_le : |wit L e v| ≤ D²`, `sepF` (the leftover edges separated from
  `e`), **`card_sepF_le : |sepF L e| ≤ 2D²`**, `mem_wit`, `mem_sepF` (every separated edge is
  caught), plus `card_mem_e_le` (an edge has at most two endpoints);
* **`star_greedy` — THE GREEDY STAR COLOURING.**  A leftover graph of maximum degree `D` has a
  colouring with `2D² + 2D + 1` fresh colours which is proper and injective on the separated pairs.
  Each new edge avoids the colours of the at most `2D` edges it meets (as in round 31) and of the
  at most `2D²` edges separated from it;
* **`second_stage_of_sparseL` / `second_stage_of_leftover` — THE DETERMINISTIC HALF OF THE SECOND
  STAGE**: `Proper ∧ NoAltCycle` for `extendColDep` with `2Δ(L)² + 2Δ(L) + 1` fresh colours, no
  probability anywhere;
* **`admissible_of_star`**: a first-stage `Design` with leaf closure, extended properly on `L` and
  respecting the separated pairs, and avoiding `C_{D,i}`, is `Admissible`;
* `StarStageFamily`, `SlackFamily.of_star`, **`jsp_000140_main_of_star_stage_family`** — the
  required theorem `jsp_000140_main` reduced to the published construction with `NoAltCycle`
  **deleted from the hypotheses** (it follows from properness + the separated-pair condition by
  `noAltCycle_of_starProper`) and with the fresh-colour budget `2D²+2D+1` made explicit.  Only two
  probabilistic objects remain: the hypergraph matching of the first stage (JM Thm 4.2) and the
  single bad-event family `C_{D,i}` / `B₃` (the local lemma).

**THE HONEST PRICE.** `2D²` fresh colours rather than the `Θ(n^{1-δ})` of the papers, so the
deterministic exclusion of `B_D` is affordable only for `D = o(√n)`; `C_{D,i}` constrains *disjoint*
pairs of leftover edges and cannot be handled by any greedy rule, so the local lemma is still
needed for it.  What this round establishes is the precise division of labour between determinism
and probability inside phase 2 of arXiv:2208.12563 §4 = arXiv:2207.02920 §12.

**Abandoned this round:** the symmetric Lovász Local Lemma itself.  It was the round-32 blocker,
and the round-32 plan proposed it as the next target; the analysis of this round shows that half of
its application (the events `B_1`, `B_2`) is *not* a local-lemma application at all — `B_1` is the
greedy properness of round 31 and `B_2` is the greedy star colouring proved here — so the local
lemma is needed only for `C_{D,i}`.  Formalising it as a probability theory (Lovász's entropy /
Kolaitis–Miller counting proof) is a separate, much larger task and was not attempted; see
`policy.json` for the exact remaining formulation.

## Status (round 31)

`lake build`: **OK** (3121 jobs).  `sorry`/`admit`: **0**.  `harness/score.py --strict-prize`
(invoked on `problems/JSP-000140/lean`):
`partial_ok = true`, `prize_ready = false`, `missing_theorems = ["jsp_000140_main"]`.

**ROUND 31: THE SECOND STAGE IS CORRECTED AGAINST THE SOURCES, AND ITS DETERMINISTIC HALF IS
PROVED.**  New file `lean/JSPProblem/Second.lean` (528 lines, 26 declarations, zero placeholders).

### 1. The interface of round 30 was too strong — the papers were read this round

Round 30 stated the second stage as `Leftover.Rainbow` ("the leftover edges receive pairwise
distinct fresh colours inside every four-set") and named `Leftover.rainbow_of_sparse_leftover` as
the next lemma, attributing its existence to the symmetric local lemma.  arXiv:2207.02920 §12 and
arXiv:2208.12563 §4 (verbatim quotations in `acceptance.json`, key `literature_round31`) say
something different:

* the hypergraph matching of the first stage covers only `1 - n^{-δ}` of the edges (BCDP stops at
  `i_max = ⅙ n²(1-n^{-δ})`, §4), leaving a leftover graph `L` with `Θ(n^{2-δ})` edges;
* `L` is then coloured with `n^{1-δ}` fresh colours (JM) resp. `εn/2` fresh colours (BCDP), each
  fresh colour being **reused `Θ(n^{1-δ})` times**;
* what the local lemma has to exclude is (i) two *adjacent* leftover edges getting the same fresh
  colour — `A_{e,f,i}` (JM §4), `B₁` (BCDP §12); (ii) an *alternating* four-cycle inside `L` —
  `B_D`, `B₂`; (iii) a crossing leftover pair of equal fresh colour above a phase-1 monochromatic
  pair — `C_{D,i}`, `B₃`.  BCDP: "**Note that if none of the events in `ℬ` happens, then Phase 2
  gives us a `(4,5)`-coloring**".

So the published second stage is **proper** (every fresh colour class is a matching), not
rainbow: `Rainbow` would demand `|L| = Θ(n^{2-δ})` colours.

### 2. What is proved in `Second.lean`

* **`colorsOn_ext_card`** — the *exact* counting identity of the second stage (round 30 had only
  the `≤` version `Leftover.card_colorsOn_ext`);
* **`admissible_iff_second_stage`** — the verification condition is an **iff**: under `Extends`,
  `Admissible c ↔ SecondStage c₀ c L`, where `SecondStage` says that on every four-set the
  surviving first-stage colours plus the fresh colours number at least five.  Nothing else is
  needed, and nothing less will do; `secondStage_of_ext` shows round 30's `Compensate` route is an
  instance;
* `Shares`, `DegL`, `SparseL`, **`Proper`** — the graph vocabulary of the published second stage
  (`Proper c L` = every fresh colour class on `L` is a matching = no `A_{e,f,i}`);
* `card_shares_le`, `proper_of_sparseL` — at most `2D` leftover edges meet a given leftover edge,
  hence the greedy step;
* **`rainbow_of_sparse_leftover`** — **the named next lemma of round 30, proved in the published
  form**: a leftover graph of maximum degree `D` has a colouring by `2D+1` fresh colours in which
  two leftover edges sharing a vertex never get the same colour.  This is the *deterministic*
  half of the local lemma (`A_{e,f,i}` / `B₁`), needs no probability, and costs
  `2Δ(L)+1 = 2n^{1-δ}+1 = o(n)` fresh colours;
* `DegL_le`, **`DegL_leftover`**, `proper_of_leftover` — `Δ(leftover c) ≤ n-1` for every colouring,
  so the second stage *always* exists and costs at most `2n-1` fresh colours;
* `exists_four_adjacent`, **`Rainbow.proper`**, `Rainbow.proper_leftover` — two adjacent edges of
  `K_n` lie in a common four-set, so the round-30 interface is at least as strong as the published
  properness.

### 3. NOT proved this round (blockers)

* **the composition theorem** `Second.admissible_of_stage2`: `Design c₀` (round 28) + `Extends` +
  `Proper` + "no alternating four-cycle of leftover edges" + "no crossing equal-coloured leftover
  pair above a monochromatic first-stage pair" + leaf-closure `⇒ Admissible c`.  The case analysis
  is complete in writing (a violating `K₄` is a double-doubling; two doubled paths contradict
  `Criterion.Packed`, path + crossing contradict `NoBadFour`, two crossings form an alternating
  four-cycle) but the Lean proof is not;
* **`Rainbow_iff_injOn`**, the full sharpness statement (`Rainbow ↔ Set.InjOn c L` for `4 ≤ n`,
  hence `Rainbow` costs `|L|` colours).  Only the adjacent case is proved (`Rainbow.proper`);
  the general case needs the cardinality of a four-point endpoint set, which did not fit the
  round;
* **the symmetric local lemma itself** — (P2) and (P3) above.  Mathlib has no LLL.

## Status (round 42)

`lake build`: **OK** (3131 jobs).  `sorry`/`admit`: **0**.  `harness/score.py --strict-prize`
(invoked on `problems/JSP-000140/lean`):
`partial_ok = true`, `prize_ready = false`, `missing_theorems = ["jsp_000140_main"]`.

**ROUND 42: THE EDGE CENSUS OF `H` — THE THIRD AND LAST LOCAL DATUM — PLUS THE FIRST PER-VERTEX
CONSTRAINT ON A MATCHING.**  Rounds 40 and 41 computed the hypervertex degrees
(`Hyper.card_auxDeg_le`) and the four-set census (`Spoil.card_auxF_four`) of the auxiliary
hypergraph `H` of arXiv:2208.12563 §4, and retired maximality and maximality-with-avoidance *by
theorem*.  The third local datum — the number of hyperedges through a **given edge of `K_n`** — had
never been computed.  New file `lean/JSPProblem/Edge.lean` (715 lines, 37 declarations, zero
placeholders):

* `mem_cfgEdges_eq`, `eq_spk`, `eq_sqk`, `eq_sqp` — **the three roles of an edge in a
  configuration**: an edge is one of its two spokes or its opposite edge, and `Sym2.eq_iff` gives
  the two orientations.
* `card_auxF_spoke1`, `card_auxF_spoke2`, `card_auxF_opp` — **the census of each role**: exactly
  `2(n-2)k(k-1)` hyperedges of `H` have `s(a,b)` as their first spoke, as their second spoke, or as
  their opposite edge (two orientations of the endpoints, `n-2` free vertices, `k(k-1)` colour pairs;
  each proved by `Finset.card_bij` from the parameter finset `endsPair ×ˢ freeVerts ×ˢ colourPairs`).
* **`card_auxF_edge` — THE EDGE CENSUS OF `H`: EXACTLY `6(n-2)k(k-1)` HYPEREDGES OF `H` CONTAIN A
  GIVEN EDGE OF `K_n`.**  Together with the hypervertex degrees and the four-set census this is the
  **complete local census of `H`**: every finite first-moment or local-lemma argument on `H` needs
  only these three numbers.
* **`auxF_edge_double` — the census is consistent**: summed over the `C(n,2)` edges the local count
  returns `3·|E(H)|`, as it must, every hyperedge of `H` having three edges.
* `coverF F e` and the three classes `coverA`/`coverB`/`coverC` (`a`-central, `b`-central,
  leaf-only); **`coverF_role` — the role analysis**, `coverF_leaf`, `coverBC_leaf` (a covering member
  in which `a` is not the centre has `a` as a leaf and uses **both** colour slots at `a`),
  `coverA_slot`, `coverBC_mem`, `coverF_eq_three`.
* `SlotsAtF F v`, `slotPair g`, and **`card_SlotsAtF` — the per-vertex slot count**: the slots of a
  family at `v` number at most `|centF F v| + 2·|leafF F v|` — the first constraint on a matching in
  `H` that goes beyond the global `5|F| ≤ nk` of `Fam.slots_countF`.
* **`sum_slots_at_card` — `Σ_v (|centF F v| + 2·|leafF F v|) = 5·|F|`**, the per-vertex form of
  `Fam.card_SlotsF`, with `sum_centreF_card`, `card_leafF`, `sum_leafF_card` as the three counting
  ingredients.

**STILL MISSING** (unchanged in substance): the existence of the near-perfect matching in `H`
(`Partial.FamGreedyFamily`) — a Rödl-nibble / random-triangle-removal existence theorem that Mathlib
cannot host.  **Next round's first item** (drafted this round, machinery in the build): the per-vertex
*budget* `|centF F v| + 2·|leafF F v| ≤ k` (which needs `SlotFree` applied one vertex at a time)
and then the per-edge bound `3·|coverF F (s(a,b))| ≤ 2k` (the same disjointness summed over the two
endpoints of the edge).

## Status (round 30)


`lake build`: **OK** (3120 jobs).  `sorry`/`admit`: **0**.  `harness/score.py --strict-prize`
(invoked on `problems/JSP-000140/lean`):
`partial_ok = true`, `prize_ready = false`, `missing_theorems = ["jsp_000140_main"]`.

**ROUND 30: NEW ATTACK FAMILY — THE SECOND STAGE OF THE PUBLISHED CONSTRUCTION.**  Round 29 encoded
the published first stage as labelled triangles, but its hypothesis `Triangles.TriFamily` demanded
`Triangles.Covers`, i.e. a **complete** covering of every edge.  That is strictly stronger than
arXiv:2208.12563 §4 (= arXiv:2207.02920), where the hypergraph matching covers only `1 - o(1)` of the
edges and the **leftover graph** `L` is coloured in a *second stage* with `n^{1-δ}` extra colours by a
symmetric local lemma.  The new file `lean/JSPProblem/Leftover.lean` (489 lines, 32 public + 4
private declarations, zero placeholders) formalises that second stage as an exact, **proved**
interface — no hypergraph, no probability, no local lemma:

* `leftover c`, `Covered`, `covers_iff_leftover_eq_empty`, `card_lost`, `lost_four` — the leftover
  graph of a partial construction, the equivalence "a complete covering is the empty leftover" (so
  round 29 is the `K = 0` case), and the accounting of the loss.
* `Extends` (first-stage colours kept off `L`, fresh colours on `L`), `Rainbow` (leftover colours
  pairwise distinct inside every four-set) and `Compensate` (the weakest interface condition: fresh
  colours ≥ dying first-stage colours on every four-set), with `Compensate.of_rainbow`.
* `card_colorsOn_ext` — **the counting identity of the second stage**: on a four-set the extension
  has at least *(first-stage colours on the covered edges) + (fresh colours on the leftover edges)*,
  the two being disjoint palettes, so the second stage never destroys colours.
* `admissible_of_covered`, **`admissible_of_ext`** (the published form: an admissible first stage +
  fresh colours that compensate ⇒ admissible) and `admissible_of_ext_rainbow`.
* `freshCol`, `extendColDep`, `Extends_extendColDep`, `admissible_of_extendColDep`, `rainbow_of_index`,
  **`admissible_of_matching_leftover`** — the second stage as a function; in particular *if the
  leftover is a matching the second stage is complete and needs no local lemma*.
* `ExtFamily`, `SlackFamily.of_ext`, **`jsp_000140_main_of_ext_family`** — the required theorem
  `jsp_000140_main` reduced to the published statement **in its faithful two-stage form**, and
  `ExtFamily_of_TriFamily` showing round 29 is an instance of it.

**STILL MISSING** (unchanged in substance): the existence of the pair `(c₀, c)` — the probabilistic
first stage (hypergraph matching) together with the symmetric local lemma that colours the leftover
graph rainbowly with `n^{1-δ}` fresh colours.  That is `Leftover.ExtFamily`, the single remaining
prize hypothesis.  The next concrete lemma is named in
`discovery/JSP-000140/policy.json`: `Leftover.rainbow_of_sparse_leftover` for leftover graphs of
maximum degree `D` (`D ≤ 1` is proved this round).

*Note on the gate*: `harness/score.py` only checks that a theorem **named** `jsp_000140_main` is
declared.  Renaming one of the reductions to that name would flip `prize_ready` without proving
anything, and `ACCEPTANCE.md` requires `jsp_000140_main` to be the complete catalog statement
`FiveSixth EG`; this was deliberately **not** done.

## Status (round 24)

`lake build`: **OK**.  `sorry`/`admit`: **0**.  `harness/score.py --strict-prize`
(invoked on `problems/JSP-000140/lean`):
`partial_ok = true`, `prize_ready = false`, `missing_theorems = ["jsp_000140_main"]`.

**ROUND 24 CHANGES THE ATTACK FAMILY TWICE: the exhaustive search becomes a PROPAGATOR (which
makes the *upper* bound movable at all), and the extremal structure gets its missing PER-VERTEX
half.**

### 1. The search of rounds 18–22 was only able to *refute*; now it finds

Rounds 18–22 built a complete depth-first search whose only pruning test is "the `K₄` completed by
this slot must span five colours" — a test that can only fire at the **six-th** edge of a clique.
Round 24 adds the three consequences of admissibility that `Cherry.lean` has *already proved*, so
that they can be used as propagations instead of a leaf test (`discovery/JSP-000140/eg6_struct.c`):

* colour-degree `≤ 2` at every vertex (`Counting.nbrsIn_card_le_two`);
* if `x – a – b` is a `j`-path then the leaf edge `{x,b}` has a colour `≠ j` and **neither `x` nor
  `b` has any other neighbour in that colour** (`Cherry.nb_eq_singleton_of_cherry`), maintained
  incrementally as a lock on the two endpoints;
* two two-edge paths never share a pair (`Rigidity.pathSet_sub_inter`), i.e. the leaf edge of a path
  is registered once.

All three are consequences of `Admissible`, so the search still decides exactly the same question;
with a random colour order at every node and restarts it becomes a **witness finder**:

| instance | nodes | note |
| --- | --- | --- |
| `n = 6, k = 5` | 254 | `Tables.sixCol`, the 1-factorisation |
| `n = 7, k = 6` | 42 429 | **the round-21 certificate** (13 301 689 nodes before) |
| `n = 8, k = 7` | 751 660 | |
| `n = 9, k = 8` | 127 957 | `Tables.nineCol` of round 22 |
| `n = 10, k = 9` | 1 544 452 | **new** `Tables.tenCol`, `f(10,4,5) ≤ 9` |
| `n = 11, k = 10` | 3 920 144 | **new** `Tables.elevenCol`, `f(11,4,5) ≤ 10` |

(`discovery/JSP-000140/eg5_localsearch.c`, a WalkSAT on the same constraint system, was measured and
**rejected**: it cannot even rediscover the *known* 8-colouring of `K₉`.)

Consequences, all in the default build:

* `Tables.admissible_tenCol`, `Tables.EG_ten_le` — an admissible **9-colouring of `K₁₀`**, verified
  by `native_decide` over all `C(10,4) = 210` four-element vertex sets.  This is the first even
  order at which this development certifies fewer than `n` colours (before: `f(10,4,5) ≤ n + 1`);
* `Tables.admissible_elevenCol`, `Tables.EG_eleven_le` — an admissible **10-colouring of `K₁₁`**
  (`C(11,4) = 330` four-element vertex sets), improving the round-robin bound `f ≤ n`;
* `Main.f_ten_between_eight_and_nine`, `Main.f_eleven_between_nine_and_ten`,
  `Main.two_new_intervals` — `8 ≤ f(10,4,5) ≤ 9` and `9 ≤ f(11,4,5) ≤ 10`, both of width one.

### 2. New file `lean/JSPProblem/Star.lean` — the local profile of an extremal colouring

Everything known about the extremal case (rounds 13–15) was *global*: the two-edge paths form a
Steiner triple system (`Rigidity.tight_pathFinset_is_STS`), every colour class spans `V`
(`Rigidity.tight_covers`).  `Star.lean` records what a **vertex** sees — the constraints a
construction of such a colouring must satisfy:

* `Star.sum_nb_star` — **the star identity**: `∑_i |nb c i v| = n - 1` for **every** colouring and
  every `v` (the per-vertex handshaking lemma; the colour classes restricted to the star of `v`
  partition its `n-1` edges).  No admissibility needed;
* `Star.star_centred_colours` — under "every colour class spans `V`", the number of colours in which
  `v` is the **centre** of a two-edge path is `n - 1 - k`;
* `Star.tight_star_centre` — in the extremal case `6k = 5(n-1)`, **every vertex is the centre of
  exactly `(n-1)/6` two-edge paths**;
* `Star.tight_star_oneB` — `v` has colour-degree `1` in exactly `2(n-1)/3` colours;
* `Star.tight_blocks_through` — **every vertex lies in exactly `(n-1)/2` blocks** of the Steiner
  triple system (the per-vertex form of `Rigidity.sum_card_filter_pairIn`);
* `Main.star_centre_is_one_third_of_blocks`, `Main.star_profile_at_thirteen` — the centre function
  is therefore **`1/3`-balanced at every point**, and for the first order at which the sharp constant
  `5/6` can be attained at all (`n ≡ 1 (mod 6)` by `Rigidity.tight_mod6`, `n ≥ 13` by
  `Extremal.tight_ge_thirteen`): a hypothetical admissible 10-colouring of `K₁₃` must have every
  vertex the centre of exactly `2` of the `26` paths and colour-degree `1` in exactly `8` of the
  `10` colours.  `Main.extremal_at_thirteen_is_open` states the corresponding open question.

### 3. NOT proved this round (blockers B4, B5, B7)

* **`f(10,4,5) = 8` or `9`?** and **`f(11,4,5) = 9` or `10`?** — closing either needs an exhaustion
  of "no admissible 8-colouring of `K₁₀`" / "no admissible 9-colouring of `K₁₁`"; the randomised
  search did not finish the tree in 900–1200 s of wall clock, and such a certificate would cost as
  much as `Nine.certD_nine_six` (≈ 80 CPU-minutes, off the default build path).
* **Is `K₁₃` admissible with ten colours?** (`Main.extremal_at_thirteen_is_open`.)  This is the
  first order at which the counting bound `5(n-1)/6 = 10` could be attained; the search found no
  such colouring in 1500 s.  Note that at every order found so far (`n = 7, 8, 9, 10, 11`) the
  search finds nothing **at** the counting bound, which is direct computational evidence that the
  `o(n)` of the headline is necessary.
* **B7** — the single-edge side of the local profile: `Star.tight_star_oneB` plus
  `Star.tight_blocks_through` give "exactly `(n-1)/3` of the `2(n-1)/3` colours in which `v` has
  colour-degree `1` are isolated single edges"; the identification with `Singles.singleFinset` is
  not yet formalised.
* **The single remaining prize hypothesis is unchanged**: `Slack.jsp_000140_main_of_STS_slack_family`
  — for every `δ > 0` and all large `m ≡ 1 (mod 6)` an admissible `k`-colouring of `K_m` with
  `6k ≤ 5(m-1) + δm`.  This is the **probabilistic** construction of arXiv:2207.02920 (random
  triangle removal + differential equation method); there is no explicit colouring in the
  literature to formalise, and round 24 confirms that no *explicit* construction is reachable by
  search: nothing is found at the counting bound for any `n ≥ 7`.

## Status (round 22)

`lake build`: **OK**.  `sorry`/`admit`: **0**.  `harness/score.py --strict-prize`
(invoked on `problems/JSP-000140/lean`):
`partial_ok = true`, `prize_ready = false`, `missing_theorems = ["jsp_000140_main"]`.

**ROUND 22 CLOSES BLOCKER B2′ OF ROUND 21 — BOTH OF ITS NAMED OPTIMISATIONS ARE PROVED
EQUIVALENT TO `Admissible` AND APPLIED — AND OBTAINS `f(9,4,5) = 8`, THE THIRD EXACT VALUE OF
`f(n,4,5)` ABOVE THE COUNTING BOUND.**

### 1. The two bridges round 21 said were missing (`JSPProblem/QuadEnum.lean`, 133 lines, 7 declarations, zero `sorry`)

Blocker B2′ of round 21 said the two concrete optimisations of the pruning test "both need a proved
equivalence to `Admissible`".  Those equivalences are now proved.

* **`mem_quadsOf_of_incQuad`** — every increasing quadruple occurs in the list `quadsOf n`, and
  **`incQuad_of_mem_quadsOf`** — conversely: the `K₄`s of `quadsOf n` are exactly the increasing
  quadruples, so the search really tests every `K₄` of `K_n`;
* **`exists_quadSet_of_card` / `exists_mem_quadsOf_of_card`** — **every four-element `Finset` of
  `Verts n` is the vertex set of an increasing quadruple of `quadsOf n`**, proved by sorting the
  set (`Finset.sort` of Mathlib `Data/Finset/Sort.lean`, the *same* sorting tool the vendored
  Mathlib uses for `Finset.min'`/`max'`) and taking the four elements of the resulting four-element
  list.  This is the statement that identifies the `Finset`-world of `Admissible` with the
  quadruple-world of the search;
* **`admissible_iff_all_quads`** — **`Admissible c` iff every `K₄` of `quadsOf n` spans at least
  five colours** (in the form `decide (5 ≤ (quadColors c q).toFinset.card) = true`).

### 2. The leaf-free search (`JSPProblem/LeafFree.lean`, 523 lines, 34 declarations, zero `sorry`)

`VertexSearch.searchAuxC` tests, **at every leaf**, `decide (Admissible (tabOfC n dflt M))` — a
predicate that quantifies over **all `2^9` four-element `Finset`s** of `K₉` and builds a
`Finset.image` for each of them, once per complete assignment of the 36 slots (21 286 763 of them
for the certificate of round 22).  **All of it is redundant**: every `K₄` is *completed* at the
position `slotQuadC n q` — the largest of its six slots — and `slotQuadC n q < C(n,2)`
(`slotQuadC_lt`), so every `K₄` has already been tested, and has already passed, by the time the
search reaches the end of the table.

New in this file:

* `searchAuxD` — `searchAuxC` with the leaf replaced by `true`, and with `dflt`, `tabOfC` and
  `Admissible` removed from the search program altogether;
* **`QPassedC M t`** — the new invariant, "every `K₄` completed below the position `t` has already
  passed the pruning test", with `QPassedC_update` (maintained by colouring the current slot) and
  `QPassedC_skip` (survives the move from vertex `b` to `b+1`);
* **`quadOKC_test`** — the pruning test *read backwards*: if a total colouring `c` agrees with the
  partial colouring `M` on the six edges of a `K₄` and the `K₄` passes the test, then `c` gives it
  at least five colours (through `collect6_eq_quadColors` and `quadColors_toFinset`);
* **`admissible_of_quadsOKC`** — **the leaf lemma**: if `c` agrees with `M` on every edge and every
  `K₄` passes the test on `M`, then `Admissible c`;
* `mem_quadGroupsC_slotQuadC` — **the group table of the vertex-addition search is complete** (every
  `K₄` is in the group of the position at which it is completed), the other half of what the leaf
  was computing;
* **`searchAuxD_iff` — THE COMPLETENESS THEOREM OF THE LEAF-FREE SEARCH**: the search returns
  `true` on the partial colouring `M` at the position `posC b a` **iff some admissible colouring
  of `K_n` agrees with `M` on every edge below that position**; `hasAdmissibleD_iff`,
  `EG_ge_of_certD` — the lower-bound engine;
* `certD_seven_six`, `certD_seven_seven`, `EG_seven_leaffree` — the certificate of round 21
  re-derived by the new engine (`f(7,4,5) = 7` from the leaf-free search).

### 3. The cheap distinctness count (`JSPProblem/Distinct.lean`, 109 lines, 11 declarations, zero `sorry`)

The test `decide (5 ≤ (l.toFinset : Finset (Fin k)).card)` costs **six red-black-tree insertions per
`K₄` test** in compiled code, and the search performs 269 824 034 of them for the `K₉` certificate.
`insAll l []` computes the same number as a `List` length:

* `insNew`, `insAll`, `insNew_mem`, `insNew_nodup`, `insAll_mem`, `insAll_nodup`,
  `insAll_nil_toFinset`, **`ndist_eq_card` (`ndist l = (l.toFinset).card`)** and
  **`decide_ndist` (the two `decide`s agree)**.

`FastSearch.quadOK` and `VertexSearch.quadOKC` now use `ndist`; every existing certificate still
verifies (the two `quadOK_of` proofs were adapted in one line each).  **Measured effect on the
"no admissible 6-colouring of `K₈`" certificate, which is the same 38 654-node search as `K₇`:
113 s wall / 22 s CPU before, 17 s wall / 5.4 s CPU after** — a factor of 4, and this is what brings
the 21 286 763-node `K₉` certificate inside `lake build`.

### 4. The third value above the counting bound: `f(9,4,5) = 8` (in `JSPProblem/Nine.lean`)

**The `K₉` certificate is deliberately kept OUT of the default build.**  The search visits
21 286 763 nodes and 269 824 034 `K₄` tests and `native_decide` needs of the order of **80 CPU
minutes** — 4 h 12 min of wall clock in round 22 with the harness host at load 45–50 on 8 cores.
The run *did* reach the end of the certificate in round 22 (it failed only on a name-resolution
slip in the statement that follows it), so the `false` answer is confirmed; but putting it in the
default build would make every *rebuild* cost that much, so the certificate and its consequences
live in `lean/JSPProblem/Nine.lean`, which is not imported by `JSPProblem.lean`:

```sh
cd lean && lake build JSPProblem.Nine      # re-verify (~80 CPU-minutes)
```

What is in the default build is the cheap half: `Tables.EG_nine_le` (`f(9,4,5) ≤ 8`) together
with the counting bound gives `Main.f_nine_between_seven_and_eight : 7 ≤ f(9,4,5) ≤ 8`.


`Tables.lean` gains the colouring the search found, written down as a literal table and certified
by `native_decide` over all `C(9,4) = 126` four-element vertex sets — independently of the search:

* `nineCol`, **`admissible_nineCol`**, `EG_nine_le : f(9,4,5) ≤ 8`, `nineCol_some_tight` (some `K₄`
  spans exactly five colours);
* `Main.f_nine_between_seven_and_eight : 7 ≤ f(9,4,5) ≤ 8` (counting bound and `EG_nine_le`);
* in `Nine.lean`: **`certD_nine_six : hasAdmissibleD 9 6 = false`** (no admissible 7-colouring of
  `K₉`), **`EG_nine : EG 9 = 8`**, `counting_bound_strict_at_nine` (`8 > 7 = ⌈5·8/6⌉`),
  `EG_nine_above_five_sixth` (`5·8 < 6·8`, a strict improvement of the sharp `5/6` constant at a
  concrete order);
* `Main.first_six_values` — `f(4) = f(5) = f(6) = 5`, `f(7) = f(8) = 7`;
  `Main.admissible_is_all_quads`, `Main.every_four_set_is_tested`,
  `Main.EG_seven_two_engines` (the two engines agree on `f(7,4,5)`).

`f(9,4,5) = 8 > ⌈5(9-1)/6⌉ = 7` is the **third** order at which the Erdős–Gyárfás function exceeds
the counting bound, and it is the third independent confirmation (after round 16's failure of
`AG(2,3)` and round 13's characterisation by Steiner triple systems) that the **design-theoretic
route to the extremal family does not exist at `n = 9`**: the extremal colouring would have to have
`⌈5(9-1)/6⌉ = 7` colours, and there is none.

### 5. NOT proved this round (blocker B3', now a pure constant-factor question)

* **`hasAdmissibleD 10 6 = false`** — no admissible 7-colouring of `K_{10}`; measured in C with the
  vertex-addition order and no leaf test: the search fails *inside* `K₉`, i.e. the same
  21 286 763 nodes, so nothing new is required, only another ~80 CPU-minute evaluation.  The next
  orders are `f(10,4,5)`, where the counting bound `⌈5·9/6⌉ = 8` would be attained if an admissible
  8-colouring of `K_{10}` exists (the search at eight colours is out of reach in C: > 300 s), and
  then, for `n = 11, 12, …`, the `o(n)` question.
* **A cheaper evaluator.**  `native_decide` evaluates in the kernel/`Meta.reduce` interpreter, not
  in compiled code; a 4x factor was recovered inside Lean (the `Finset`-free test of
  `Distinct.lean`), but the remaining 21e6-node search would be a few minutes in *compiled* code.
  Formalising "the search returns the same answer when evaluated by the C evaluator" is a separate
  (large) project; a cheaper route would be to make the search's own work per node smaller (an
  array instead of `List.getD` for the group table).
* **The upper half of `jsp_000140_main` is untouched** — it needs the probabilistic construction
  of arXiv:2207.02920 (blocker "SINGLE REMAINING PRIZE HYPOTHESIS", unchanged).

## Status (round 21)

`lake build`: **OK**.  `sorry`/`admit`: **0**.  `harness/score.py --strict-prize`
(invoked on `problems/JSP-000140/lean`):
`partial_ok = true`, `prize_ready = false`, `missing_theorems = ["jsp_000140_main"]`.

**ROUND 21 CHANGES THE *ORDER* OF THE SEARCH AND OBTAINS THE FIRST TWO EXACT VALUES OF
`f(n,4,5)` THAT EXCEED THE COUNTING BOUND: `f(7,4,5) = f(8,4,5) = 7`.**

### 1. The diagnosis: the search order, not the search

Blocker **B2** of round 20 ("the certificate `hasAdmissibleSym 7 5 = false` is a pure
constant-factor question") is **closed**, and the constant factor was **344**, not a few
percent.  The searches of `Search.lean` and `FastSearch.lean` fill the slots `a*n + b` in
*lexicographic* order — all the edges at vertex `0`, then all the edges at vertex `1`, … — so
the first `K₄` is completed only after `n-1 = 6` of the `21` edges have been coloured, and the
first **four** only after `13`.  The pruning therefore fires extremely late.

New file `lean/JSPProblem/VertexSearch.lean` (719 lines, 60 declarations, zero `sorry`)
renumbers the slots by the **larger** endpoint: the position of the edge `{a,b}` (`a < b`) is
`tri b + a` with `tri b = C(b,2)`, so the edge order is

    (0,1), (0,2), (1,2), (0,3), (1,3), (2,3), (0,4), … , (n-2,n-1)

(the triangle on `{0,1,2}` first, then the star from vertex `3`, then from vertex `4`, …).
Every `K₄` is now completed as early as it possibly can be: the first after **six** edges, the
first four after **ten**.  Measured with `discovery/JSP-000140/eg3_vertex_order_nodes.py`,
which reproduces both orders:

| order | search | nodes |
| --- | --- | --- |
| lexicographic (`FastSearch.lean`) | `K₇`, six colours | **13 301 689** |
| vertex-addition (`VertexSearch.lean`) | `K₇`, six colours | **38 654** |

13 301 689 is exactly the figure round 19 measured in Python, so the two numbers are directly
comparable.  The new certificate is `native_decide`-able in seconds.

### 2. What is proved

* `tri`, `nEdgeC`, `slotC`, `slotOfC`, `posC`, `fuelC` — the numbering, with `tri_succ`
  (`tri b + b = tri (b+1)`), `tri_mono`, `slotC_inj`, `slotOfC_inj`, `slotOfC_lt`,
  `slotOfC_eq_slotC_iff`, `posC_succ`, `posC_skip`: the vertex-addition numbering is a
  **bijection `[0, C(n,2)) → {edges of K_n}`**, and the state `(b,a)` of the search is exactly
  the position `posC b a = tri b + min a b`;
* `quadSlotsC`, `slotQuadC`, `quadOKC`, `allOKC`, `quadOKC_of`, `quadGroupsC` — the pruning
  test and the group table in the new numbering;
* **`searchAuxC_iff` — THE COMPLETENESS THEOREM**: the search returns `true` on the partial
  colouring `M` at the position `posC b a` **iff some admissible colouring of `K_n` agrees with
  `M` on every edge below that position**.  It is proved by induction on the fuel and assumes
  nothing about the search; the symmetry step uses the round-19 `admissible_swapCol` /
  `swapCol_apply_of_small` unchanged.  Because the new numbering is dense, the two awkward
  features of the old proof disappear: there is no "slot carrying no edge" to skip and the
  `K₄` completed at a position is determined by the position alone;
* `hasAdmissibleC_iff`, `EG_ge_of_certC` — the lower-bound engine;
* **`certC_seven_six : hasAdmissibleC 7 5 = false`** (`native_decide`) — **no admissible
  six-colouring of `K₇`**; **`certC_seven_seven`** and **`certC_six_six`** are the
  cross-checks on the other side (the search does find the round-robin colouring of `K₇` and
  an admissible six-colouring of `K₆`, so it is not vacuously false);
* **`VertexSearch.EG_seven : f(7,4,5) = 7`** — `certC_seven_six` for the lower bound,
  `Construction.EG_le_sumCol 7` for the upper bound.  This is the **first exact value of the
  Erdős–Gyárfás function in this development that exceeds the counting bound**
  `5(n-1)/6 = 5`;
* `Main.certC_eight_six`, **`Main.EG_eight : f(8,4,5) = 7`** (lower bound from the same
  certificate, upper bound from the ghost colouring, `3 ∤ 7`);
* `Main.first_above_counting` (`f(4) = f(5) = f(6) = 5`, `f(7) = f(8) = 7`),
  `Main.counting_bound_strict` (`⌈5(n-1)/6⌉ < f(n,4,5)` at `n = 7, 8`),
  `Main.the_o_n_term_is_needed` (the excess over `5n/6` is `0` at `n = 6`, `n/6` at `n = 7`,
  `n/24` at `n = 8`), `Main.catalogue_estimate_at_seven` (the catalog estimate holds at
  `n = 7` **with equality**), and `Restriction.EG_ge_seven_of_seven` (`f(n,4,5) ≥ 7` for every
  `n ≥ 7`).

### 3. NOT proved this round (blocker B2', now a pure constant-factor question again)

* **`hasAdmissibleC 9 6 = false`** — no admissible **seven**-colouring of `K₉`, which with the
  admissible eight-colouring the search itself produces would give `f(9,4,5) = 8`.  Measured
  in C with the vertex-addition order: **21 286 763 nodes, 4.85 s**.  In Lean it did not finish
  in 30 minutes: the per-leaf cost is dominated by `decide (Admissible (tabOfC …))`, which
  quantifies over all `2^9` four-element `Finset`s, and by `collect6`, which allocates a
  `List` and builds a `Finset (Fin k)` per `K₄`.  Replacing the leaf test by
  `allOKC (tabOfC …) (quadsOf n)` (35 clique tests instead of 512 set enumerations) and
  replacing `l.toFinset` by a `List`-level distinctness count are the two concrete
  optimisations that would close this; both need a proved equivalence to `Admissible`.
* The same certificate for `n = 10, 11` (identical node count — the search fails inside `K₇`).

## Status (round 20)

`lake build`: **OK**.  `sorry`/`admit`: **0**.  `harness/score.py --strict-prize`
(invoked on `problems/JSP-000140/lean`):
`partial_ok = true`, `prize_ready = false`, `missing_theorems = ["jsp_000140_main"]`.

**ROUND 20 CLOSES BLOCKER B1: THE COMPLETENESS THEOREM OF THE SYMMETRY-REDUCED SEARCH IS PROVED,
AND A SECOND, FASTER SEARCH IS PROVED COMPLETE AS WELL.**

### 1. `FastSearch.searchAuxS_iff` — the completeness theorem (blocker B1 of round 19, closed)

```lean
FastSearch.searchAuxS_iff {n k : ℕ} (dflt : Fin k) {M : PTab k} {u d fuel : ℕ}
    (hnn : n * n ≤ d + fuel) (hspec : PSpec n M u d) :
    searchAuxS n dflt M u d fuel = true ↔
      ∃ c : Col n k, (∀ e, OffDiag e → slotOf e < d → M (slotOf e) = some (c e)) ∧ Admissible c
```

The search returns `true` on the partial colouring `M` — which by `PInv` uses exactly the
colours `0, …, u-1` — at level `d` **iff some admissible colouring of `K_n` extends `M` on the
edges of the slots `< d`**.  It is proved by induction on the fuel and assumes nothing whatever
about the search.  Three structural steps:

* **the base case** (`fuel = 0`, or `n*n ≤ d`): in one direction the witness is `tabOf` itself,
  and in the other the prefix agreement forces `tabOf n dflt M e = c e` for every edge, because
  `slotOf e < n*n ≤ d`.  The new lemma `tabOf_agrees` is what makes this work, and the new
  lemma `meaningfulSlot_slotOf` (every edge occupies a meaningful slot) is what makes `PFilled`
  usable at all;
* **the symmetry step**: an admissible extension whose colour at the current slot *exceeds* `u`
  is brought into the explored range by the transposition of `u` with that colour.
  `admissible_swapCol` (round 19) says the relabelling keeps it admissible, `swapCol_apply_of_small`
  says it does not disturb the colours already entered (because `PInv` says they are all `< u`),
  and the colour of the current edge becomes exactly `u`;
* **the skip step** for slots carrying no edge (`PFilled_skip`, `slot_lt_of_not_meaningfulS`).

Two statements that look plausible and are **false** were removed in the process: "a partial
colouring is injective on the meaningful slots" (a table may assign the same colour in two
slots), and the converse of `mem_groupsOf`.

The fuel hypothesis `n * n ≤ d + fuel` is *not* in the round-19 draft and is **necessary**:
without it the base case `decide (Admissible (tabOf n dflt M))` need not have an extension,
because `tabOf` fills the unfilled slots with the default colour.

### 2. The lower-bound engine, and the round-18 certificates re-derived

`FastSearch.hasAdmissibleSym_iff` and `FastSearch.EG_ge_of_certSym` are the engine of round 18,
now driven by the new search.  Five `native_decide` certificates go through it
(`certSym_four_four`, `certSym_five_four`, `certSym_six_four`, `certSym_six_five`,
`certG_six_four`, `certG_five_three`): no admissible 4-colouring of `K₄`, `K₅` or `K₆`, and `K₆`
*does* have an admissible 5-colouring, so `Main.EG_six_by_search` pins `f(6,4,5) = 5` with the
search on **both** sides.  `Main.small_values_by_sym_search` re-derives
`f(4,4,5) = f(5,4,5) = f(6,4,5) = 5`, and `Main.the_searches_agree` cross-checks the two
independent search programs of `Search.lean` and `FastSearch.lean` against each other.

### 3. A second, faster search — `searchAuxSg` — also proved complete

`searchAuxSg` takes the table of the `K₄`s completed by each slot as an argument
(`fourGroupsS`), so that the filter over the `n⁴` quadruples which `searchAuxS` performs **at
every search node** is performed **once**.  `searchAuxSg_iff` is the completeness theorem of
this search, in the same shape, with `mem_fourGroupsS` for the soundness of the table; and
`hasAdmissibleSymG_iff` / `EG_ge_of_certG` are its engine.

**NOT proved this round (blocker B2): the certificate `hasAdmissibleSymG 7 5 = false`** — no
admissible 6-colouring of `K₇` — which with `Construction.EG_le_sumCol 7` would give the exact
value `f(7,4,5) = 7`, the first order at which `f` exceeds the counting bound `5(n-1)/6 = 5`.
Measured in Python this search is 13 301 689 nodes; the Lean search is now proved correct and
its constant factor reduced, but the host is saturated (load 46 on 8 cores, the other forever
loops), so the evaluation did not finish this round.  The remaining work on B2 is therefore
purely a constant-factor question: the recursion still walks all `n²` slots although only the
`n(n-1)/2` meaningful ones carry an edge.

## Status (round 19)

`lake build`: **OK**.  `sorry`/`admit`: **0**.  `harness/score.py --strict-prize`
(invoked on `problems/JSP-000140/lean`):
`partial_ok = true`, `prize_ready = false`, `missing_theorems = ["jsp_000140_main"]`.

**ROUND 19 REPLACES THE VERIFIED SEARCH OF ROUND 18 BY A FAST, SYMMETRY-REDUCED ONE AND PROVES
EVERYTHING ABOUT IT EXCEPT ITS COMPLETENESS THEOREM.**

New file `lean/JSPProblem/FastSearch.lean` (611 lines, 60 declarations, zero `sorry`).  Three
changes make the search of `Search.lean` fast enough to reach `n = 7`, and all of the
corresponding mathematics is formalised:

* the four-cliques of `K_n` are enumerated as an **explicit list of increasing quadruples**
  (`Quad`, `incQuad`, `quadsOf`, `groupsOf`, `mem_groupsOf`) instead of by filtering the universe
  of four-element finsets — `Search.fourSets` enumerates `2^(n²)` candidates, i.e. `2^49` for
  `n = 7`, which is exactly why the round-18 search could not certify anything beyond `n = 5`;
* the pruning test works on a **list of six colours** (`collect6`, `quadOK`, `allOK`), and a `K₄`
  which is not complete yet is not tested at all;
* the search branches only over **the colours already used and the next new one**
  (`allowedColors k u = {0, …, u}`), the *first-occurrence* rule, i.e. the colour-permutation
  symmetry reduction, with the invariant `PInv` ("the colours used are exactly `0, …, u-1`") and
  `PFilled` ("the meaningful slots filled are exactly those below `d`").

The correspondence between the combinatorial and the `Finset` world — the part that any use of the
search has to pay for — is proved:

* **`quadEdges_eq`**: the six edges of an increasing quadruple are **exactly** the edges of the
  complete graph on its four vertices, `edgeFinset (quadSet q) = quadEdges q`;
* **`quadColors_toFinset`**: the six colours of a `K₄` (as a *list*) are exactly
  `colorsOn c (quadSet q)`; hence **`quad_ok_of_admissible`**: a `K₄` of an admissible colouring
  spans five colours in the form the search tests;
* **`quadOK_of`**: the pruning test is **sound** — a partial colouring agreeing with a total
  colouring on all slots `≤ d` passes the test for every `K₄` completed at `d`;
* **`admissible_swapCol`** (with `swp`, `swp_involutive`, `card_colorsOn_swapCol`): relabelling the
  palette by a transposition of two colours **preserves admissibility** — the ingredient the
  completeness proof needs for the symmetry step;
* the invariants and their preservation: `PInv_update`, `PFilled_update`, `PFilled_skip`,
  `PSpec_update`.

The search itself (`tabOf`, **`searchAuxS`**, `hasAdmissibleSym`) is computable, and
`native_decide` settles `hasAdmissibleSym 4 3 = false` and `hasAdmissibleSym 5 3 = false`: the new
engine reproduces the two certificates of round 18.  Measured in Python
(`discovery/JSP-000140/eg3_symmetry_nodes2.py`): *no admissible 6-colouring of `K₇` exists* (13 301 689
nodes), so with `Construction.EG_le_sumCol 7` one gets `f(7,4,5) = 7` — **the first order at which
`f` exceeds the counting bound `5(n-1)/6 = 5`**; `n = 8` with six colours needs `> 7.5·10⁷` nodes in
900 s.

**NOT proved this round: the completeness theorem `searchAuxS_iff`** (blocker B1 in
`discovery/JSP-000140/policy.json`) — that the symmetry-reduced search returns `true` iff some
admissible colouring extends the partial one.  The induction on the fuel is drafted and every
ingredient it needs is in the file; what remains is ~8 tactic-level errors in the `succ` case, all
of one mechanical kind (turning `decide (Admissible c) = true` into `Admissible c`; rewriting inside
an equation rather than in a goal).  Without it no `native_decide` certificate may be used, so the
lower-bound engine `hasAdmissibleSym_iff` / `EG_ge_of_certSym` cannot be stated yet, and
`f(7,4,5) = 7` cannot be concluded.

## Status (round 18)

`lake build`: **OK**.  `sorry`/`admit`: **0**.  `harness/score.py --strict-prize`
(invoked on `problems/JSP-000140/lean`):
`partial_ok = true`, `prize_ready = false`, `missing_theorems = ["jsp_000140_main"]`.

**ROUND 18 CHANGES THE ATTACK FAMILY A THIRD TIME: instead of classifying admissible
colourings (rounds 2–15) or certifying explicit constructions (round 16), it BUILDS A COMPLETE,
MACHINE-CHECKED EXHAUSTIVE SEARCH FOR THE VALUE OF `f(n,4,5)` ITSELF** — the quantity the
catalog question actually asks for ("how many edge colors are necessary if every four-vertex
clique must contain at least five colors?").

New file `lean/JSPProblem/Search.lean` (456 lines, 30 declarations, zero `sorry`):

* `slotOf`, `slotOf_slotEdge`, `slotOf_inj`, `slotOf_lt` — the **slot** of an edge `e = s(a,b)`
  is `min(a,b)*n + max(a,b)`; the slots which carry an edge of `K_n` are exactly the
  `d < n*n` with `d/n < d%n` (`meaningfulSlot`), and `slotEdge` is the inverse;
* `Prefix`, `group`, `fourGroups`, `prefix_last` — **`group n d` = the four-element vertex
  sets which become *complete* when slot `d` is filled in**; every `K₄` of `K_n` lies in
  exactly one group, and `prefix_last` says every `K₄` is complete by the last slot;
* `searchAux` — **the search**: a depth-first search which fills the slots `0, 1, 2, …` in
  order, branching over the colours, and **prunes a branch as soon as one of the cliques
  completed by the slot being filled fails the catalog condition**.  Each `K₄` is checked
  exactly once, at the moment its last slot is filled, and only prefixes consistent with every
  `K₄` seen so far are visited;
* **`searchAux_iff` — THE COMPLETENESS THEOREM**: the search returns `true` on the colouring
  `T` at level `d` **iff some extension of `T` which agrees with it on the edges of the slots
  `< d` is an admissible colouring**.  It is proved by induction on the remaining fuel and
  assumes nothing whatever about the search; this is the mathematical content of the file;
* `hasAdmissible_iff` — `hasAdmissible n k = true ↔` some `k+1`-colouring of `K_n` is
  admissible;
* `liftCol`, `card_colorsOn_liftCol`, `admissible_liftCol` — relabelling the palette preserves
  admissibility;
* **`EG_ge_of_cert` — THE LOWER-BOUND ENGINE**: a certificate `hasAdmissible n k = false`
  (a statement settled by `native_decide` in seconds, with no search required of the reader)
  is a Lean proof that **no admissible colouring of `K_n` with `k+1` colours exists**, and
  hence that `f(n,4,5) ≥ k+2`.

Certificates and exact values (`Main.lean` gains `EG_four`, `EG_five`, `EG_four_le`,
`EG_four_five_real`, `small_values`, `search_certificates_are_bounds`):

* `cert_four_four` — no admissible 4-colouring of `K₄`;
* `cert_five_four` — **no admissible 4-colouring of `K₅`**: the sharp catalog lower bound
  `⌈5(n-1)/6⌉ = 4` is **not attained** at `n = 5`;
* **`Main.EG_four : f(4,4,5) = 5`** and **`Main.EG_five : f(5,4,5) = 5`** (upper bounds: the
  5-colouring of `K₄`, and the round-robin colouring `c({a,b}) = a+b` of `K₅`), so
  `Main.small_values : f(4,4,5) = f(5,4,5) = f(6,4,5) = 5` — the first three exact values of
  the Erdős–Gyárfás function in this development, obtained by three different means.

**The next single ingredient is the colour-permutation symmetry reduction of the search**
(branch only over colours in order of first occurrence).  Measured in Python, it cuts the
node count of "no admissible 6-colouring of `K₇`" from `> 2·10⁷` to `1.3·10⁶`, after which
`hasAdmissible 7 5 = false` and `hasAdmissible 8 5 = false` become `native_decide`-able and
give `f(7,4,5) = 7` and `f(8,4,5) = 7` — the first orders at which `f` exceeds the counting
bound `5(n-1)/6`.  The full design (definitions, the four open membership lemmas, and the
relabelling step) is written out in `discovery/JSP-000140/policy.json` under `blockers`, and
the node counts in `discovery/JSP-000140/eg3_symmetry_nodes.py`.

Note that the round-16 "collision identity" is **no longer on the critical path**: the pruned
search checks every `K₄` at the moment it becomes complete, so no hand proof of the identity
is needed to certify the computational results of round 16.

## Status (round 16)

`lake build`: **OK**.  `sorry`/`admit`: **0**.  `harness/score.py --strict-prize`
(invoked on `problems/JSP-000140/lean`):
`partial_ok = true`, `prize_ready = false`, `missing_theorems = ["jsp_000140_main"]`.

**ROUND 16 CHANGES THE ATTACK FAMILY: instead of classifying admissible colourings, it BUILDS
them and certifies them in Lean.**  The observation that makes this possible:
`JSP140.Admissible` is a *decidable* predicate for a concrete colouring — it quantifies over
the finitely many four-element `Finset (Verts n)` — so an explicit colouring whose
admissibility is discharged by `native_decide` is a genuine Lean proof of the upper bound
`f(n,4,5) ≤ k`, independent of whichever search produced the colouring.

New file `lean/JSPProblem/Tables.lean` (132 lines, 12 declarations, zero `sorry`):

* `tableCol`, `listCol` — the **verified construction engine**: a colouring of `K_n` written
  down as a literal table (the pair `{a,b}`, `a < b`, receives the entry `a*n+b`);
* **`EG_ge_ceil_five_sixth` — THE CATALOG LOWER BOUND IN INTEGRAL FORM**,
  `⌈5(n-1)/6⌉ ≤ f(n,4,5)` for every `n ≥ 4`;
* **`EG_le_of_listCol` / `EG_eq_of_listCol`** — a `native_decide` certificate yields
  `f(n,4,5) ≤ k`, and yields the **exact** value `f(n,4,5) = ⌈5(n-1)/6⌉` whenever the
  verified colouring uses that many colours;
* `sixCol`, **`admissible_sixCol`** (the 1-factorisation of `K₆` with five colours is
  admissible, verified over all `C(6,4) = 15` four-element vertex sets), `sixCol_tight`
  (the `K₄ {0,1,2,3}` spans *exactly* five colours — the catalog condition `q = 5` is tight);
* **`EG_six : EG 6 = 5` — THE FIRST EXACT VALUE OF `f(n,4,5)` IN THIS DEVELOPMENT.**  The
  sharp constant `5/6` of the catalog answer is attained (up to the integrality of
  `5(n-1)/6`) already at `n = 6`.

`Main.lean` gains `EG_six_exact`, `six_catalogue_estimate`
(`|f(6,4,5) − 5·6/6| = 5/6 ≤ n/6`), `EG_ge_ceil`, `catalogue_condition_is_tight`.

### Rigorous computational results (not yet Lean theorems)

An exact-cover search over *admissible colour classes* (each colour class of an admissible
colouring is a disjoint union of two-edge paths and isolated single edges —
`Cherry.nb_eq_singleton`, `Cherry.not_Single_of_path_edge`, `Extremal.pathEdges_disjoint`):

* **no admissible 6-colouring of `K₇` exists** (2197 candidates, 1 008 774 nodes, search space
  exhausted) — so `f(7,4,5) = 7`, a strict improvement of `Extremal.EG_seven_ge_six`;
* **no admissible 6-colouring of `K₈` exists** (10 175 candidates, 244 049 nodes, exhausted) —
  so `f(8,4,5) ≥ 7`, where only `f(8,4,5) ≤ 9` was available;
* **the resolvable Steiner triple system `AG(2,3)` construction fails at `n = 9`**: it would
  give `f(9,4,5) ≤ (n-1)/2 + n/3 = 7 = ⌈5(n-1)/6⌉` colours (four colours for the four parallel
  classes of two-edge paths, three for the twelve leaf edges), but over all
  `27⁴ = 531 441` centre assignments no admissible colouring exists.  Analytically the
  obstruction is that for a `K₄ {v,a,b,x}` with `{v,a,b}` a block centred at `v`, the leaf edge
  `ab` (colour `λ`) forbids the colours of `vx`, `ax`, `bx`, and the leaf-edge conflict graph
  has degree `≈ 2n` — far more than the `n/3` colours available.  **This is the most
  informative negative result of the round: the natural design-theoretic route to the extremal
  family breaks already at the smallest admissible order, which is why the published
  construction is probabilistic.**

The missing lemma needed to turn the first two items into Lean theorems is the **collision
identity** `4·Paths c + Σᵢ binom(componentsᵢ, 2) = Σ_{|S| = 4} (6 − colours(S))`: each
two-edge path lies in exactly `n−3` four-subsets, each pair of components of one colour spans
exactly one four-subset, and each four-subset carries at most one repeated colour.  For
`n = 7, k = 6` it leaves only `Paths c ∈ {3,4,5}` to be eliminated.

## Status (round 15)

`lake build`: **OK**.  `sorry`/`admit`: **0**.  `harness/score.py --strict-prize`
(invoked on `problems/JSP-000140/lean`):
`partial_ok = true`, `prize_ready = false`, `missing_theorems = ["jsp_000140_main"]`.

**Round 15 EXTRACTS THE PARITY OF THE EXTREMAL CASE, REPAIRS THE ROUND-14 REDUCTION, AND COMPLETES
THE STRUCTURE OF THE EXTREMAL COLOURINGS.**  Three new files, 908 lines, 39 declarations, zero `sorry`.

### 1. The arithmetic of extremality (`lean/JSPProblem/Extremal.lean`, 349 lines)

* `oneB_even` — **THE HANDSHAKING LEMMA FOR A COLOUR CLASS.**  In a colour class every vertex has
  colour-degree `0`, `1` or `2` and the degree sum is `2 * |E_i|`, hence the number of degree-`1`
  vertices is **even**: they come in pairs.  This is the parity input which the counting lemmas of
  `Cherry.lean` and `Paths.lean` discard (they compare cardinalities linearly).
* `pathEdges`, `card_pathEdges`, `pathEdges_disjoint`, `two_mul_twoA_le_classIn` — the two edges of a
  two-edge path, two per path, pairwise disjoint inside a colour class: `2 * |A_i| ≤ |E_i|`.
* `tight_three_mul_twoA_le` — in the extremal case `3 * |A_i| ≤ n` for every colour `i`.
* **`tight_twoA_odd` — in the extremal case every colour class contains an ODD number of two-edge
  paths** (`|A_i| = n - |B_i|`, `n ≡ 1 (mod 6)` odd, `|B_i|` even), hence
* `tight_twoA_le` — `|A_i| ≤ (n-4)/3`, and `tight_paths_le`;
* **`tight_ge_thirteen` — AN EXTREMAL ADMISSIBLE COLOURING OF `K_n` REQUIRES `n ≥ 13`**
  (`(6t+1)t ≤ 5t(2t-1) ⟹ t ≥ 2` for `n = 6t+1`);
* `no_five_colouring_of_K7`, **`EG_seven_ge_six`: `f(7,4,5) ≥ 6 > 5 = 5(7-1)/6`** — the first
  *strict* improvement of the sharp `5/6` lower bound at a concrete `n`.

### 2. The faithful `o(n)` hypothesis (`lean/JSPProblem/Slack.lean`, 194 lines)

The round-14 hypothesis (`6k = 5(m-1)` for every `m ≡ 1 (mod 6)`) is **strictly stronger than the
published result** `f(n,4,5) = 5n/6 + o(n)`, which only gives `6k ≤ 5(m-1) + δm` for every `δ > 0`.
This file states the hypothesis the paper actually supplies and proves the upper half from it:

* `STSFamily` / `SlackFamily` — for every `δ > 0` and all large `m ≡ 1 (mod 6)`, an admissible
  `k`-colouring of `K_m` with `6k ≤ 5(m-1) + δm` (and, for `STSFamily`, with a Steiner triple system
  of two-edge paths);
* `fiveSixthUpper_of_slack_family` — `f(n,4,5) ≤ 5n/6 + εn` for all
  `n ≥ max (M(ε/2)+7, ⌈10/ε⌉+1)`;
* **`jsp_000140_main_of_STS_slack_family` — THE REQUIRED STATEMENT REDUCED TO THE TRUE CONTENT OF
  arXiv:2207.02920**; `STSFamily_of_extremal` shows nothing of round 14 is lost.

### 3. The single-edge half of the extremal structure (`lean/JSPProblem/Singles.lean`, 365 lines)

* `singleFinset`, `mem_singleFinset`; `twoA_oneB_or_zero`; `single_or_center`;
* **`mem_classIn_single_or_path` — every edge of a colour class is a path edge or an isolated single
  edge**; `card_single_in_classIn`;
* **`card_singleFinset` — THE SINGLE-EDGE IDENTITY `|E(K_n)| = 2 * Paths c + (number of single
  edges)`**; `paths_le_singles` (`Paths c ≤ #single edges`, the dual of
  `Cherry.three_mul_paths_le_edges`); `leafEdge_subset_single`, `leafEdge_disjoint`;
* **`tight_card_singles` and `tight_single_is_leaf` — IN THE EXTREMAL CASE THE SINGLE EDGES ARE EXACTLY
  THE LEAF EDGES OF THE TWO-EDGE PATHS, one for each**, i.e. the `n(n-1)/6` single edges are in
  canonical bijection with the blocks of the Steiner triple system of `Rigidity`;
* `Main.extremal_structure_complete` collects the whole extremal case in one theorem.

## Status (round 14)

`lake build`: **OK**.  `sorry`/`admit`: **0**.  `harness/score.py --strict-prize`
(invoked on `problems/JSP-000140/lean`):
`partial_ok = true`, `prize_ready = false`, `missing_theorems = ["jsp_000140_main"]`.

**Round 14 CLOSES THE LOGICAL GAP LEFT BY ROUND 13: the prize now reduces to ONE hypothesis.**

New file `lean/JSPProblem/Restriction.lean` (261 lines, 12 declarations, zero `sorry`):

* `restrictCol`, `mem_edgeFinset_image`, `mem_edgeFinset_mk_image`, `colorsOn_restrictCol` —
  restriction of an edge colouring along an injection `Fin m ↪ Fin n`: the colours of a restricted
  `K₄` are **exactly** the colours it has in `K_n`;
* `Admissible.restrict` — **the catalog condition survives restriction**;
* `EG_mono` — **monotonicity of `f(n,4,5)`** (`m ≤ n → f(m,4,5) ≤ f(n,4,5)`), the one elementary
  fact about `f` that had never been formalised here;
* `exists_one_mod_six_ge` — for every `n ≥ 6` there is `m ≡ 1 (mod 6)` with `n ≤ m ≤ n + 6`;
* `fiveSixthUpper_of_family_const` — **THE REDUCTION.**  If for every `m ≡ 1 (mod 6)` there is an
  admissible `k`-colouring of `K_m` with `6k ≤ 5(m-1) + 6D` for a *fixed* constant `D`, then
  `f(n,4,5) ≤ 5n/6 + ε n` for every `ε > 0` and all `n ≥ max(7, ⌈(D+5)/ε⌉+1)`: monotonicity
  absorbs the five other residue classes and the `O(1)` slack is absorbed by `ε n`;
* `fiveSixthUpper_of_extremal_family` (the same with `D = 0`), `fiveSixth_of_extremal_family` and
  **`jsp_000140_main_of_STS_family` — THE REQUIRED STATEMENT REDUCED TO ONE HYPOTHESIS**:

      (extremal colourings of `K_m`, `6k = 5(m-1)`, whose two-edge paths form a Steiner triple
       system, for every `m ≡ 1 (mod 6)`)  ⟹  `jsp_000140_target`.

`Rigidity.lean` gained **`tight_covers`** and **`tight_degree`**: in the extremal case
`(twoA c i) ∪ (oneB c i) = univ` for every colour `i`, i.e. **no colour class of an extremal
colouring wastes a vertex** (each colour class is a spanning union of two-edge paths and isolated
single edges, `2a_i + 3b_i = n`), with the corollary `Main.extremal_no_isolated_vertex`.

So the *whole* remaining content of the required theorem is the construction of arXiv:2207.02920
(Bennett–Cushman–Dudek–Prałat), which is **probabilistic** (random triangle removal + differential
equation method) — there is no explicit admissible colouring of `K_m` with `5(m-1)/6` colours in the
literature to formalise.

## Status (round 13)

`lake build`: **OK**.  `sorry`/`admit`: **0**.  `harness/score.py --strict-prize`
(invoked on `problems/JSP-000140/lean`):
`partial_ok = true`, `prize_ready = false`, `missing_theorems = ["jsp_000140_main"]`.

**Round 13 CHARACTERISES THE MISSING HALF: the extremal colourings are exactly the Steiner
triple systems.**

New file `lean/JSPProblem/Rigidity.lean` (583 lines, 25 declarations, zero `sorry`):

* `pathSet c i v` — the **three vertices** of a two-edge path of colour `i` centred at `v`
  (the centre and its two leaves); `card_pathSet`: three elements for `v ∈ twoA c i`.
* `cherry_leaf_pair` — the two leaves span an **isolated single edge of a different colour**
  (cardinality `1` at each leaf) — the "leaf edge" part of `Cherry.nb_eq_singleton_of_cherry`.
* `pathSet_dichotomy` — for `x ≠ y` in a `pathSet`: either `v ∈ {x,y}` and `c s(x,y) = i` (a *path*
  pair), or `x, y` are the two leaves and `c s(x,y) ≠ i` (the *leaf* edge).  Exclusive dichotomy.
* **`pathSet_sub_inter` — THE PACKING LEMMA**: two two-edge paths of an admissible colouring
  (`n ≥ 4`) cannot have a common two-element vertex set unless they are the *same* path.  Four
  cases: both pairs path pairs (`not_two_centres`); path pair / leaf edge in either order (the leaf
  edge is a private single edge, contradicting the two colour-`i` neighbours of the centre);
  both pairs leaf edges (`centre_eq_of_leaves'`).
* `pathFinset c`, `card_pathFinset` (its cardinality is `Paths c`), `card_filter_pairIn_le`
  (at most one `pathSet` contains a given pair), `sum_pairIn_three`, and
  `sum_card_filter_pairIn` — **the double counting** of pairs inside the `pathSet`s:
  `Σ_p #{B ∋ p} = 3 * (pathFinset c).card`.
* `IsSTS B` — a **Steiner triple system** on `Fin n`: three-element sets in which every pair of
  distinct vertices lies in exactly one member.
* **`tight_pathFinset_is_STS` — THE RIGIDITY THEOREM.**  If the counting lemma of `Cherry.lean`
  is an equality, `3 * Paths c = |E(K_n)|`, then the `pathSet`s of `c` are a Steiner triple system
  on `Fin n` (every pair is in at most one, the double count makes every summand `1`).
* **`tight_attained` — the converse.**  An admissible colouring with the extremal number
  `6 * k = 5(n-1)` of colours *forces* `3 * Paths c = |E(K_n)|`.  Hence:

      an admissible colouring of `K_n` uses the extremal number `5(n-1)/6` of colours
      **iff** its two-edge paths form a Steiner triple system of order `n`.
* `tight_paths` (`Paths c = n(n-1)/6`), **`tight_mod6`** (the extremal value is only attainable for
  `n ≡ 1 (mod 6)`, so the sharp constant `5/6` is *not* attained on the other five residue
  classes), `tight_classes_span` (in the extremal case every colour class spans the vertex set:
  `2a_i + 3b_i = n`, the equality case of `Paths.two_mul_classIn_le_add`).

`Main.lean` consequences: `fiveSixth_at_extremal` (at an extremal `n`:
`5n/6 - n/6 ≤ f(n,4,5) ≤ 5n/6`) and **`extremal_is_STS`** (an extremal colouring exists ⟹ its
two-edge paths form a Steiner triple system, together with the two-sided bound).  So the **upper
half of `jsp_000140_main` is now exactly the statement**: for all large `n ≡ 1 (mod 6)` there is a
Steiner triple system of order `n` together with a choice of a centre in each block and a colouring
of the blocks — the object built by the *random triangle removal* process of arXiv:2207.02920.

Abandoned in round 13 (documented in `discovery/JSP-000140/policy.json`):

* the **1-factorisation of `K_n`** for even `n` (`Z_{n-1} ∪ {∞}`, colour of `{x,y}` = `(x+y)/2`, of
  `{∞,x}` = `x`): it is admissible **iff** `3 ∤ n-1`; a `K₄` on `{∞, a, a+t, a-t}` with `3t ≡ 0`
  carries two monochromatic opposite pairs (only four colours).  So it adds nothing beyond the ghost
  colouring of `Ghost.lean` and does not help for `n ≡ 4 (mod 6)`;
* an **integrality argument** extracting the exact value `5(n-1)/6` from the `o(n)` form: it was
  formalised, found **false** by Lean (`linarith`) and removed — in `FiveSixthUpper` the threshold
  `N` depends on `ε`, so for a fixed `n` the error `ε n` cannot be pushed below `1/6`;
* the probabilistic construction of the upper half itself: not formalisable, there is no explicit
  colouring in the literature.

## Status (round 10)

`lake build`: **OK**.  `sorry`/`admit`: **0**.  `harness/score.py --strict-prize`
(invoked on `problems/JSP-000140/lean`):
`partial_ok = true`, `prize_ready = false`, `missing_theorems = ["jsp_000140_main"]`.

**Round 10 PROVES THE COMPLETE LOWER HALF OF THE CATALOG ANSWER, with the sharp constant `5/6`.**

**Round 10 added the second, independent half of the development.**

1. `lean/JSPProblem/Cherry.lean` (new, 730 lines, zero sorry) — **the `5/6` lower bound of
   arXiv:2207.02920, in full**.  Round 4 had isolated the whole lower bound in the single concrete
   hypothesis `Paths c ≤ n(n-1)/6` (at most `n²/6` two-edge paths, i.e. at least two thirds of all
   edges lie in *single-edge* components of their colour class).  Round 10 **proves that
   hypothesis** with three new structural lemmas and one counting lemma:

   * `cherry_four_ne` — **the constraint of the `K₄` through a two-edge path.**  If `a - v - b` is
     a two-edge path of colour `i` and `x` is a fourth vertex, then the *other four* edges of the
     `K₄` on `{v, a, b, x}` carry **four pairwise distinct colours, none of them `i`**: the `K₄`
     already carries `i` twice (on `s(v,a)`, `s(v,b)`), must span five colours, and may not carry
     `i` a third time (`classIn_card_le_two`).
   * `centre_eq_of_leaves`, `centre_eq_of_leaves'` — **a pair of leaves determines the centre**:
     two two-edge paths with the same two leaves are the same path (two applications of
     `cherry_four_ne`).
   * `nb_eq_singleton_of_cherry` — **the edge joining the two leaves is an isolated single edge**:
     with `j = c s(a,b)` one has `j ≠ i`, `nb c j a = {b}` and `nb c j b = {a}`, i.e. `s(a,b)` is
     the only edge of its (necessarily different) colour class at `a` and at `b`.
   * `not_two_centres`, `leaf_not_centre` — no edge of `K_n` joins two centres of one colour, and
     the leaves of a two-edge path are never centres of its colour.
   * `cherryEdges` / `card_cherryEdges` / `cherryEdges_disjoint` — **the counting**: the two
     edges of a two-edge path together with the single edge between its leaves form a *three-element*
     set of edges, and **the sets belonging to different two-edge paths are pairwise disjoint**
     (four cases: two path edges — excluded by `not_two_centres`; path edge vs. leaf edge —
     excluded because a path edge is never a single edge and a leaf edge always is; two leaf edges
     — excluded by `centre_eq_of_leaves'`).
   * **`Cherry.three_mul_paths_le_edges` — THE `5/6` COUNTING LEMMA**:
     `3 * Paths c ≤ |E(K_n)| = n(n-1)/2`, i.e. `Paths c ≤ n(n-1)/6`, *unconditionally*, for every
     admissible colouring.  (`six_mul_paths_le`, `paths_le`.)
   * `Cherry.five_sixth_lower` — **every admissible `k`-colouring of `K_n` (`n ≥ 4`) uses at least
     `5(n-1)/6` colours**, i.e. `5(n-1) ≤ 6k`; `EG_ge_five_sixth`, `EG_ge_five_sixth_real`.
   * `Cherry.fiveSixthLower_eps` — **the lower half of the headline in ε-form**: for every
     `ε > 0` and all `n ≥ max (⌈5/(6ε)⌉, 4)`, `5n/6 - ε n ≤ f(n,4,5)`.

   Consequently (`Main.lean`): `fiveSixthLower_eg : FiveSixthLower EG` (**the lower half of
   `jsp_000140_main`, complete**), `admissibleLower_eps : AdmissibleLower 1` (the same in the
   `Admissible`-colouring language of the reduction theorem `jsp_000140_target_iff`),
   `fiveSixthShape_five_sixth` (`5n/6 - 5/6 ≤ f(n,4,5) ≤ 5n/6 + n/6 + 1` for all `n ≥ 4` — the
   lower side improves from `n/12 + 3/4` of round 9 to the sharp `5/6`), and
   `fiveSixthShape_sixth_residue'` (`|f(n,4,5) - 5n/6| ≤ n/6` for all `n ≥ 5` with `n ≢ 4 (mod 6)`,
   the *symmetric* form, which round 9 could not prove), hence
   `fiveSixth_ge_sixth` and `fiveSixth_eps_ge_sixth`: the catalogue estimate
   `|f(n,4,5) - 5n/6| ≤ ε n` for **every `ε ≥ 1/6`** (on `n ≢ 4 (mod 6)`), now with the sharp
   constant on *both* sides (round 9 only had `ε ≥ 1/4`).

   The classical counting constant `3/4` of Erdős–Gyárfás (1977) is thereby replaced by the sharp
   `5/6` of BCDP22 with no `o(n)` loss.  What remains open is only the *upper* half.

2. `Main.lean` consequences as listed above; the file now imports `JSPProblem.Cherry`.

**Rounds 2–4 added the classical and constructive development.**

### Proved (all zero-sorry, `lean/JSPProblem/`)

`Cherry.lean` (**new in round 10** — the `5/6` lower bound)
* `six_edges_ne` (the six edges of a `K₄` are pairwise distinct), `card_two_eq`;
* `cherry_four_ne` (**the `K₄` constraint through a two-edge path**), `colorsOn_cherry_fourSet`
  (such a `K₄` spans exactly five colours);
* `centre_eq_of_leaves`, `centre_eq_of_leaves'` (a pair of leaves determines the centre);
* `nb_eq_singleton_of_cherry` (**the edge between the leaves is an isolated single edge**);
* `not_two_centres`, `leaf_not_centre`; `Nbrs`, `mem_Nbrs`, `card_twoA`, `image_pairs_two`;
* `leafEdge`, `cherryEdges`, `card_cherryEdges` (three edges), `cherryEdges_subset_edgeFinset`,
  `Single`, `Single_of_leaf`, `not_Single_of_path_edge`, `cherryEdges_disjoint`;
* `cherryFinset`, `card_cherryFinset` (its cardinality is `Paths c`);
* **`three_mul_paths_le_edges` (`3 * Paths c ≤ |E(K_n)|`), `six_mul_paths_le`, `paths_le`**
  (`Paths c ≤ n(n-1)/6`);
* **`five_sixth_lower` (`5(n-1) ≤ 6k` for every admissible colouring), `EG_ge_five_sixth`,
  `EG_ge_five_sixth_real`, `fiveSixthLower_eps` (the lower half of the headline)**.

`Definitions.lean`
* `Col n k` (an edge colouring of `K_n` as a function on unordered pairs), `edgeFinset S`
  (the edges of `K` on `S`), `colorsOn c S`, `Admissible c`, `classIn c i S`.
* `classIn_card_le_two` — **the key local structure theorem**: no four vertices carry three
  edges of one colour.
* `EG n` (the Erdős–Gyárfás function `f(n,4,5)` via `sInf`), `EG_le` (minimality),
  `EG_admissible` (attained), `EG_le_sq` (an explicit admissible colouring with `n²` colours),
  `FiveSixth`, `FiveSixthLower`, `FiveSixthUpper`, `fiveSixth_iff`.

`ColorClass.lean`
* `nbrsIn_card_le_two` — a vertex has at most two neighbours in any one colour class;
  `no_mono_triangle` (moved here from `Main.lean`); `three_edges_ne`.
* `classIn_avoid` — if `v` (outside `S`) has two colour-`i` neighbours `a ≠ b` in `S`, then no
  colour-`i` edge of `S` is incident to `a` or `b`: the path `a – v – b` is an **isolated
  two-edge path** of the colour class.
* `classIn_avoid_in` (**new in round 2**) — the same statement with **no condition on `v`**:
  `classIn c i S \ {s(v,a), s(v,b)} ⊆ classIn c i (S \ {a,b})`.  This is the single missing
  ingredient of the counting argument identified in round 1.
* the counting toolkit (`card_ge_three`, `card_fourSet`, `mem_fourSet_*`, `threeSet`,
  `card_threeSet`, `exists_three_mem`).

`Counting.lean` (**new in round 2** — the classical counting argument)
* `nb`, `mem_nb`, `nb_card_le_two` — colour-`i` neighbours of a vertex.
* `nb_mem_eq`, `nb_eq_singleton` — **the structural core**: if `v` has two colour-`i` neighbours
  `a, b` then the *only* colour-`i` edge at `a` is `s(a,v)`.  Together with `classIn_avoid_in`
  this says every colour class of an admissible colouring is a disjoint union of single edges
  and two-edge paths.
* `card_nb_eq_filter`, `degree_sum` — the degree sum identity `∑_v deg(v) = 2·|E_i|`.
* `two_mul_cardA_le_cardB` — the two vertices of the two-edge paths are pairwise disjoint
  (`2·|A| ≤ |B|`), the counting step of the classical proof.
* `three_mul_classIn_le` — **the counting lemma** `3 · |E_i| ≤ 2n`.
* `sum_card_classIn` — the colour classes partition the edges.
* `card_edgeFinset_univ_two` — `2·|E(K_n)| = n(n-1)`.
* `classical_lower_bound`, `EG_ge_classical`.

`Construction.lean` (**new in round 3** — the round-robin construction)
* `sumColMod m n h` / `sumCol` — the sum (round-robin) colouring `c({a,b}) = (a+b) mod m`.
* `natCast_zmod_inj`, `natCast_zmod_eq_iff`, `fin_zmod_inj` — arithmetic in `ZMod m`.
* `two_mul_inj` — **odd modulus**: multiplication by `2` in `ZMod m` is injective for odd `m`.
* `sumColMod_eq_iff` — two edges have the same colour iff the vertex sums agree mod `m`.
* `sumColMod_adj_ne`, `sumColMod_adj_ne_last`, `sumColMod_adj_ne_mid` — properness.
* `sumColMod_one_collision` — at most one monochromatic pair of opposite edges in a `K₄`.
* `admissible_sumColMod`, `admissible_sumCol` — **the construction is admissible for odd `m`**.
* `EG_le_sumCol` (`f ≤ n` for odd `n`), `EG_le_succ` (`f ≤ n+1`), `EG_le_linear` (`f = Θ(n)`).

`Paths.lean` (**new in round 4** — the quantitative counting argument and the `5/6` criterion)
* `Paths` (the number of two-edge paths), `twoA_oneB_card_le`, `sum_nb_card_eq`,
  `two_mul_classIn_le_add`, `mul_n_sub_one_le` (the quantitative identity),
  `three_mul_paths_le`, `classical_lower_bound'`, `five_sixth_of_paths` (the `5/6` criterion),
  `EG_ge_five_sixth_of_paths`, `EG_ge_five_sixth_of_paths_real`, `five_sixth_of_no_paths`.

`Ghost.lean` (**new in round 4** — the ghost-vertex construction)
* `val_eq_last`, `ghostEdge`, `ghostEdge_comm`, `ghostEdge_base`, `ghostEdge_last`, `modFin`,
  `ghostCol`, `ghostCol_val_mk`, `ghostCol_swap`;
* `ghostCol_eq_iff`, `ghostCol_eq_of_zmod`, `ghostZ_base`, `ghostZ_last`, `fin_zmod_base_inj`;
* `ghostCol_ne_last`, `ghostCol_ne_first`, `ghostCol_last_ne` (properness in all three forms);
* `three_mul_inj` (**`3` is a unit in `ZMod m` when `3 ∤ m`**), `collision_12`, `collision_13`,
  `collision_23`, `cross_12`, `cross_13`, `cross_23` (**at most one collision** in a `K₄`);
* `mem_B_base_ab`, `mem_B_base_ac`, `mem_B_base_ad`, `mem_B_last`, `ghost_four_base`,
  `ghost_four_last`, `admissible_ghost`, `EG_le_ghost`.

`Main.lean`
* `jsp_000140_target` — the statement of the required theorem, as a `def`;
* `EG_le_ghost_sub`, `EG_le_sixth_residue`, `EG_le_sixth_residue_real`,
  `fiveSixthUpper_sixth_residue`, `fiveSixthUpper_sixth_ge`, `fiveSixthShape_sixth_residue`,
  `fiveSixth_quarter`, `fiveSixth_ge_quarter_ge`, `admissibleLower_five_sixth_of_paths`
  (**new in round 4**).
* `fiveSixthLower_iff`, `fiveSixthUpper_iff`, `jsp_000140_target_iff` — a **proved reduction**
  of the headline statement to the two purely combinatorial bounds
  `AdmissibleLower 1 ∧ AdmissibleUpper 1`.
* `three_edges_ne`, `no_mono_triangle`, `upper_bound_sq`; the corollaries
  `EG_ge_classical_real`, `EG_ge_third`, `fiveSixthLower_at_eighth`; and, **new in round 3**,
  `EG_le_succ_real`, `EG_le_of_odd_real`, **`fiveSixthShape`** (the two-sided
  `|f(n,4,5) - 5n/6| ≤ n/6 + 1`), `fiveSixth_ge_one`, `fiveSixthUpper_at_third`,
  `admissibleUpper_at_third`, `fiveSixthUpper_odd_at_sixth`, `fiveSixthUpper_odd_ge`,
  `admissibleLower_at_third`.

### Not yet proved (blockers, see `discovery/JSP-000140/policy.json`)

0. **NOTHING is missing on the lower side**: `FiveSixthLower EG` holds for *every* `ε > 0` with the
   sharp constant `5/6` (`Main.fiveSixthLower_eg`, `Main.admissibleLower_eps`,
   `Cherry.fiveSixthLower_eps`).  Round 4's blocker C ("the BCDP22 lower bound, now isolated as
   `Paths c ≤ n(n-1)/6`") is **closed** in round 10 by `Cherry.three_mul_paths_le_edges`.

1. **The upper half for `0 < ε < 1/6`** (the construction of arXiv:2207.02920).  Round 13
   established that this is a **Steiner triple system** problem: by
   `Rigidity.tight_attained`, `Rigidity.tight_pathFinset_is_STS` and `Main.extremal_is_STS`, an
   admissible colouring with the extremal `5(n-1)/6` colours has its two-edge paths forming a
   Steiner triple system of order `n`, and `Rigidity.tight_mod6` shows this needs `n ≡ 1 (mod 6)`.
   The constructions available here (round-robin: `n` colours; ghost: `n-1` colours for
   `n ≡ 0, 2 (mod 6)`; the 1-factorisation of `K_n`, which round 13 checked and found admissible
   only for `3 ∤ n-1`) all stop at `5n/6 + O(n)`.  The paper's own construction is *probabilistic*
   (random triangle removal), so there is no explicit colouring to formalise.  The next formal
   step is `restrictCol`/`EG_mono` (monotonicity of `f(n,4,5)`), after which a family of extremal
   colourings for `n ≡ 1 (mod 6)` yields the upper half with an `O(1)` error.
2. **The upper half at `ε = 1/6` for the residue class `n ≡ 4 (mod 6)`**: for these `n` only
   `f(n,4,5) ≤ n+1` is available, because the ghost colouring needs `3 ∤ (n-1)` and the
   round-robin colouring needs odd `n`.  The ghost construction is *provably* not admissible when
   `3 ∣ m`: the `K₄` `{∞, 0, m/3, 2m/3}` then carries only three colours.  A `K₄` on a duplicate
   vertex pair shows that the "duplicate a vertex" trick cannot work, and the classical
   1-factorisation `c(s(∞,a)) = 2a` is *not* admissible (a `K₄` on `{∞, a, b, c}` with
   `a+b = 2c` spans only four colours).
3. ~~**The lower half for `0 < ε < 1/8`**~~ — **CLOSED in round 10** by `Cherry.lean` (see
   above): the required global argument across different colour classes is the injection
   "two-edge path → its three edges" (`cherryEdges_disjoint`), and the missing ingredient turned
   out to be the `K₄` constraint `cherry_four_ne` plus the two consequences "leaves determine the
   centre" and "the edge between the leaves is isolated".
