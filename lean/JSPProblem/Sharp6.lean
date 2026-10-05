import JSPProblem.Rate
import JSPProblem.One

/-!
# JSP-000140 — round 93: **`Grow6` IS FALSE** — the universal growth lemma is refuted, no growth
lemma at rate `5/6` exists at *any* step length, and the sharp palette at `n ≡ 0 (mod 6)` is
`5n/6 + 1`

Ninety-two rounds of this development attacked the missing half of the catalog answer
`f(n,4,5) = 5n/6 + o(n)` from the *necessity* side: the counting bound (`Cherry.lean`), its exact
surplus form (`Surplus.lean`), the rigidity of the extremal case (`Rigidity.lean`), the structural
theory of the colour classes (`Singles.lean`, `Cell.lean`, `PathFac.lean`), the impossibility of
every deterministic move (`Fusion.lean`, `LocalFuse.lean`, `Product.lean`), the union-bound barrier
(`Barrier.lean`) and the per-vertex budget of the published first stage (`VertexBudget.lean`).

The only *sufficiency* route ever formalised is the **growth route** of round 68, and round 75
(`Rate.lean`) pinned down its shape: a growth hypothesis of step `(a,b)` must have rate exactly
`5/6`, so the six-step `(6,5)` is the finest possible one, and `Grow6.main` then reads

> *one finite witness plus one local extension lemma is the whole prize.*

**This round shows that the hypothesis of that sentence is FALSE.**

## §1 — `Grow6` IS FALSE

`Grow6` (`Grow.lean`) is the *universal* statement

> for **every** `m`, **every** `j` and **every** admissible colouring `c : Col m j` there is an
> admissible extension `d : Col (m+6) (j+5)`,

and `K₆` is the counterexample: `Tables.sixCol` is an admissible **five**-colouring of `K₆`
(`Tables.admissible_sixCol`, `Tables.EG_six : EG 6 = 5`), so `Grow6` applied at `(m,j) = (6,5)`
demands an admissible **ten**-colouring of `K₁₂` — and there is none:

* **`Sharp6.not_Grow6 : ¬ Grow6`**, from `Tables.sixCol` and `Grow6.not_from_six`
  (= `Vacant.no_ten_of_twelve`);
* **`Sharp6.not_GrowRate_six_five : ¬ GrowRate 6 5`** — the same in the language of `Rate.lean`,
  so the candidate growth steps of `Rate.lean` are empty in their universal form;
* **`Sharp6.no_growth_five_sixth : ¬ GrowRate (6s) (5s)` for every `s ≥ 1`** — **NO growth
  hypothesis of rate `5/6` EXISTS, AT ANY STEP LENGTH.**  Iterating `GrowRate (6s) (5s)` exactly
  `s` times from the `K₆` witness would produce an admissible `(6 + 6s²)`-vertex colouring with
  `5+5s²` colours, while the refined counting bound `Vacant.five_n_add_one_le_six_k_of_seven`
  demands `5(6+6s²)+1 ≤ 6(5+5s²)`, i.e. `31 + 30s² ≤ 30 + 30s²`.  The obstruction is pure counting;
  no search and no structural theory is involved.

Consequently **`Grow6.main` and `Grow6.jsp_000140_main` are vacuously true**
(`Sharp6.main_is_vacuous`), and any future round that tries to prove `Grow6` is chasing a false
statement.  What survives is §2.

## §2 — THE CORRECTLY SCOPED HYPOTHESIS, AND THE PRIZE FROM IT

`Grow6At` restricts the universal quantifier to the **boundary anchors** `6j = 5m+6` — the shape on
which the growth step is numerically consistent (`Grow6.anchor_counting`) and the shape of the
verified witness `EG 12 = 11` (`anchor_twelve`).  The `K₆` counterexample is *not* a boundary anchor
(`6·5 = 30 ≠ 36 = 5·6+6`, `Sharp6.sixCol_not_anchor`), so `Grow6At` is not refuted by §1.

* **`Sharp6.Grow6At.family`** — iteration: `Grow6At` turns the verified anchor `EG 12 = 11` into an
  admissible `(12+6t, 11+5t)`-colouring for every `t`, i.e. round 83's `Solo6 12 11`
  (`Sharp6.Grow6At.solo`);
* **`Sharp6.Grow6At.count_bound`** — hence `6·f(n) ≤ 5n + 31` for every `n ≥ 12`, the same constant
  as `Grow6.count_bound` but reached **without** any extension statement beyond the family;
* **`Sharp6.Grow6At.target : Grow6At → jsp_000140_target`** — the honest form of `Grow6.main`: the
  prize, from one finite witness plus one *boundary* extension lemma.

## §3 — THE SHARP PALETTE AT `n ≡ 0 (mod 6)`

Along the residue class `0 (mod 6)` the counting bound `5n/6` is **never** attained (from `t = 2`
onwards), so the growth family's value is *optimal*, not an artefact:

* **`Sharp6.ge : 5·t + 1 ≤ EG (6t)`** for every `t ≥ 2` — the sharp lower bound there, i.e.
  `Sharp6.Grow6At.minimum_palette`;
* **`Sharp6.not_five_t : ¬ ∃ c : Col (6t) (5t), Admissible c`** for every `t ≥ 2` — the counting
  bound `5n/6` is unattainable at every order `n ≡ 0 (mod 6)`, `n ≥ 12`.  In particular the
  conditional family of round 83 (`Solo6.sharp_eighteen`, `f(18+6t,4,5) = 16+5t`) cannot be
  improved by one colour at any of its orders, and `One.Solo6.sharp_eighteen` is the strongest
  possible statement of its shape;
* **`Sharp6.boundary : 6(5t+1) = 5(6t)+6`** — the palette `5t+1` sits exactly on the growth boundary;
* **`Sharp6.anchor_two : EG 12 = 11`** — attained (`t = 2`), so the target is not vacuous;
* **`Sharp6.eighteen : 16 ≤ EG 18 ∧ EG 18 ≤ 17`** and **`Sharp6.eighteen_cases`** — the first order
  at which the optimal palette `16` is not yet known to be attained: `EG 18 = 16 ∨ EG 18 = 17` is
  decided by the single finite question `∃ c : Col 18 16, Admissible c`, which is exactly
  `Grow6At` at `m = 12` (`Sharp6.Grow6At.eighteen`, `Sharp6.eighteen_eq_sixteen`).  **This one
  finite question is the first missing link of the growth route.**

## What is still missing

Unchanged: `Main.AdmissibleUpper ε` for `0 < ε < 1/6`, i.e. the probabilistic existence theorem of
arXiv:2207.02920 §4/§12.  But the *form* of the remaining work is now sharp and non-vacuous: it is
enough to attain the optimal palette `5t+1` at all sufficiently large orders `6t` (round 83's
`Solo6`, or `Sharp6.Grow6At.target` together with the verified anchor `EG 12 = 11`), whereas the
universal growth lemma that was advertised as a single finite target **does not exist**.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace JSP140

namespace Sharp6

variable {n k : ℕ}

/-! ### §1  `Grow6` IS FALSE -/

/-- **`Grow6` IS FALSE.**  The universal six-step of round 68 is refuted by the development's own
verified `K₆` witness: `Tables.sixCol` is an admissible five-colouring of `K₆`, so `Grow6` would
produce an admissible ten-colouring of `K₁₂`, and `Grow6.not_from_six` says there is none.

Hence **`Grow6.main` and `Grow6.jsp_000140_main` are vacuously true**, and the round-68 slogan
"one finite witness plus one local extension lemma is the whole prize" does not rest on a
proposition anybody can prove. -/
theorem not_Grow6 : ¬ Grow6 := by
  intro h
  obtain ⟨d, hd⟩ := h 6 5 sixCol admissible_sixCol
  exact Grow6.not_from_six ⟨d, hd⟩

/-- **The same refutation in the rate language of `Rate.lean`**: the growth hypothesis of step
`(6,5)` does not hold. -/
theorem not_GrowRate_six_five : ¬ Rate.GrowRate 6 5 :=
  fun h => not_Grow6 ((Rate.growRate_six).mp h)

/-- **NO UNIVERSAL GROWTH HYPOTHESIS OF RATE `5/6` EXISTS, AT ANY STEP LENGTH `6s` (`s ≥ 1`).**

Suppose `GrowRate (6s) (5s)`.  Iterating it `s` times from the verified admissible five-colouring
`sixCol` of `K₆` (`Rate.GrowRate.family` with `t = s`) gives an admissible colouring of `K_{6+6s²}`
with `5+5s²` colours.  The refined counting bound `Vacant.five_n_add_one_le_six_k_of_seven` then
demands `5(6+6s²)+1 ≤ 6(5+5s²)`, i.e. `31 + 30s² ≤ 30 + 30s²`, which is false.  **The obstruction is
counting alone.**

So the growth route is not merely blocked at the step `(6,5)`: it is blocked at *every* step of rate
`5/6`, and the whole "universal growth lemma" family of `Grow.lean`/`Rate.lean` is dead. -/
theorem no_growth_five_sixth {s : ℕ} (hs : 1 ≤ s) : ¬ Rate.GrowRate (6 * s) (5 * s) := by
  intro h
  obtain ⟨d, hd⟩ := h.family (m := 6) (j := 5) (c := sixCol) admissible_sixCol s
  have h7 : 7 ≤ 6 + 6 * s * s := by nlinarith
  have h1 := five_n_add_one_le_six_k_of_seven hd h7
  have hA : 5 * (6 + 6 * s * s) + 1 = 31 + 30 * s * s := by ring
  have hB : 6 * (5 + 5 * s * s) = 30 + 30 * s * s := by ring
  nlinarith

/-- **The `K₆` witness is not a boundary anchor**, which is exactly why the restriction of §2 escapes
the refutation of §1: `6·5 = 30` while `5·6 + 6 = 36`. -/
theorem sixCol_not_anchor : ¬ (6 * 5 = 5 * 6 + 6) := by norm_num

/-! ### §2  THE BOUNDARY-ANCHOR GROWTH LEMMA, AND THE PRIZE FROM IT -/

/-- **THE SIX-STEP, RESTRICTED TO THE BOUNDARY ANCHORS `6j = 5m+6`.**  This is the only form of the
round-68 growth lemma that survives `Sharp6.not_Grow6`: the extension is demanded only from those
colourings which already sit on the growth boundary, i.e. from the shape `6j = 5m+6` in which the
step `(+6,+5)` is numerically consistent (`Grow6.anchor_counting`) and in which the verified witness
`EG 12 = 11` lives. -/
def Grow6At : Prop :=
  ∀ (m j : ℕ) (c : Col m j), Admissible c → 6 * j = 5 * m + 6 →
    ∃ (d : Col (m + 6) (j + 5)), Admissible d

theorem Grow6At.step {h : Grow6At} {m j : ℕ} {c : Col m j} (hc : Admissible c)
    (hk : 6 * j = 5 * m + 6) : ∃ (d : Col (m + 6) (j + 5)), Admissible d :=
  h m j c hc hk

/-- **A SIX-STEP FROM A BOUNDARY ANCHOR IS A BOUNDARY ANCHOR**: the shape `6k = 5n+6` is preserved
exactly, so the hypothesis of `Grow6At` is re-established at every step of the iteration. -/
theorem Grow6At.shape {h : Grow6At} {m j : ℕ} {c : Col m j} (hc : Admissible c)
    (hk : 6 * j = 5 * m + 6) : 6 * (j + 5) = 5 * (m + 6) + 6 := by
  calc 6 * (j + 5) = 6 * j + 30 := by ring
    _ = 5 * m + 6 + 30 := by rw [hk]
    _ = 5 * (m + 6) + 6 := by ring

/-- **THE VERIFIED ANCHOR AS AN ACTUAL COLOURING.**  This is `Window.r66Col`, the eleven-colouring of
`K₁₂` found by the search of `discovery/JSP-000140/r66_walk` and certified by `native_decide` over
all `C(12,4) = 495` four-sets; `Window.EG_twelve` derives `f(12,4,5) = 11` from it. -/
theorem anchor_col : ∃ (c : Col 12 11), Admissible c :=
  ⟨listCol 12 11 (by norm_num) r66Col, admissible_r66Col⟩

/-- **`Grow6At` PROPAGATES THE VERIFIED ANCHOR `EG 12 = 11` TO EVERY ORDER `12 + 6t`.**  One finite
witness — the `K₁₂` colouring, on the boundary `6·11 = 5·12+6` — plus the boundary extension lemma
yields an admissible `(12+6t, 11+5t)`-colouring for every `t`, i.e.
`f(12+6t,4,5) ≤ 5(12+6t)/6 + 1`. -/
theorem Grow6At.family {h : Grow6At} :
    ∀ t : ℕ, ∃ (d : Col (12 + 6 * t) (11 + 5 * t)), Admissible d := by
  intro t
  induction t with
  | zero => obtain ⟨c, hc⟩ := anchor_col; exact ⟨c, hc⟩
  | succ t ih =>
    obtain ⟨d, hd⟩ := ih
    have hshape : 6 * (11 + 5 * t) = 5 * (12 + 6 * t) + 6 := by ring
    obtain ⟨d', hd'⟩ := h.step (m := 12 + 6 * t) (j := 11 + 5 * t) (c := d) hd hshape
    rw [show 12 + 6 * (t + 1) = 12 + 6 * t + 6 from by ring,
      show 11 + 5 * (t + 1) = 11 + 5 * t + 5 from by ring]
    exact ⟨d', hd'⟩

/-- **`Grow6At` IS ROUND 83's `Solo6` FAMILY AT THE VERIFIED ANCHOR.**  Round 83 weakened the growth
hypothesis to a *non-uniform* family — one witness per order, no extension statement at all — and
showed it wins the prize; `Grow6At.family` lands exactly on `Solo6 12 11`. -/
theorem Grow6At.solo {h : Grow6At} : Solo6 12 11 := h.family

/-- **The propagated upper bounds**: `f(12+6t,4,5) ≤ 11+5t = 5(12+6t)/6 + 1`. -/
theorem Grow6At.eg_le {h : Grow6At} (t : ℕ) : EG (12 + 6 * t) ≤ 11 + 5 * t := by
  obtain ⟨d, hd⟩ := h.family t
  exact EG_le _ _ d hd

/-- **THE COUNTING FORM, WITHOUT ANY EXTENSION STATEMENT BEYOND THE FAMILY.**  `Grow6.count_bound`
derives `6·f(n) ≤ 5n+31` from `Grow6` by iteration; here it is `Solo6.count_bound` applied to the
family, so the constant `31 = 25+6` — monotonicity costs at most five extra vertices, the anchor's
own slack costs `6` — is the entire content of the growth route: **one finite witness plus one
family suffices for an `O(1)` error at every `n`.** -/
theorem Grow6At.count_bound {h : Grow6At} {n' : ℕ} (hn' : 12 ≤ n') :
    6 * EG n' ≤ 5 * n' + 31 := by
  exact Solo6.count_bound h.solo (C := 6) (by omega) hn'

/-- **THE UPPER HALF, FROM THE BOUNDARY SIX-STEP AND THE VERIFIED ANCHOR.** -/
theorem Grow6At.fiveSixthUpper {h : Grow6At} : FiveSixthUpper EG :=
  Solo6.fiveSixthUpper h.solo (C := 6) (by omega)

/-- **THE HONEST FORM OF `Grow6.main`.**  Unlike `Grow6.main`, whose hypothesis `Sharp6.not_Grow6`
refutes, this reads off the required theorem `jsp_000140_target` from a hypothesis that is not
refuted: the boundary six-step, applied to the verified anchor `EG 12 = 11`. -/
theorem Grow6At.target {h : Grow6At} : jsp_000140_target :=
  fiveSixth_iff.mpr ⟨fiveSixthLower_eg, h.fiveSixthUpper⟩

/-- **`Grow6.main` is vacuous**: its statement survives, but only because its hypothesis
`Sharp6.not_Grow6` refutes.  Recorded so that the difference with `Sharp6.Grow6At.target` is
explicit. -/
theorem main_is_vacuous (h : Grow6) : jsp_000140_target := h.main

/-! ### §3  THE SHARP PALETTE AT THE ORDERS `n ≡ 0 (mod 6)` -/

/-- **THE SHARP LOWER BOUND AT `n ≡ 0 (mod 6)`: `f(6t, 4, 5) ≥ 5t+1` for every `t ≥ 2`.**

This is `Vacant.EG_ge_ceil_five_sixth_plus_one` read at `n = 6t`, where `⌈(5n+6)/6⌉ = 5t+1`.  It
says that along the whole residue class `0 (mod 6)` the catalog value `5n/6 + 1` is the *smallest
possible* palette of an admissible colouring, so the value used by the growth family
(`Sharp6.boundary`, `Grow6At.eg_le`) is optimal and cannot be improved by one colour. -/
theorem ge (t : ℕ) (ht : 2 ≤ t) : 5 * t + 1 ≤ EG (6 * t) := by
  have h := EG_ge_ceil_five_sixth_plus_one (6 * t) (by omega : 7 ≤ 6 * t)
  have hnum : 5 * (6 * t) + 1 + 5 = 6 * (5 * t + 1) := by ring
  omega

/-- **THE COUNTING BOUND `5n/6` IS NEVER ATTAINED AT AN ORDER `n ≡ 0 (mod 6)`, `n ≥ 12`.**

Suppose `c : Col (6t) (5t)` were admissible.  The refined counting bound
`Vacant.five_n_add_one_le_six_k_of_seven` gives `5·6t+1 ≤ 6·5t`, i.e. `30t+1 ≤ 30t`.  So the palette
`5n/6` is impossible at every such order, while `5n/6 + 1` is attained at `n = 12`
(`Sharp6.anchor_two`).

In particular the conditional family of round 83 (`Solo6.sharp_eighteen`,
`f(18+6t,4,5) = 16+5t`) is **exactly** at the optimum: it cannot be lowered by one colour at any of
its orders. -/
theorem not_five_t (t : ℕ) (ht : 2 ≤ t) : ¬ ∃ c : Col (6 * t) (5 * t), Admissible c := by
  rintro ⟨c, hc⟩
  have h := five_n_add_one_le_six_k_of_seven hc (by omega : 7 ≤ 6 * t)
  omega

/-- **THE PALETTE `5t+1` SITS EXACTLY ON THE GROWTH BOUNDARY `6k = 5n+6`**, for every `t`: this is
the arithmetic reason the residue class `0 (mod 6)` is the natural one for the growth route, and
why `EG 12 = 11` (`6·11 = 66 = 5·12+6`) is a *boundary* anchor. -/
theorem boundary (t : ℕ) : 6 * (5 * t + 1) = 5 * (6 * t) + 6 := by ring

/-- **THE OPTIMAL PALETTE IS ATTAINED AT `t = 2`**: `f(12,4,5) = 11 = 5·2+1`, so the growth route has
a verified seed on its own boundary. -/
theorem anchor_two : EG 12 = 11 := anchor_twelve.1

/-- **THE MINIMUM PALETTE AT THE ORDERS `6t`.**  For every `t ≥ 2` the least possible palette of an
admissible colouring of `K_{6t}` is `5t+1`, and `6(5t+1) = 5(6t)+6`. -/
theorem Grow6At.minimum_palette (t : ℕ) (ht : 2 ≤ t) :
    5 * t + 1 ≤ EG (6 * t) ∧ 6 * (5 * t + 1) = 5 * (6 * t) + 6 :=
  ⟨ge t ht, boundary t⟩

/-- **`f(18, 4, 5)` IS PINNED TO TWO VALUES.**  The sharp bound gives `16`, the ghost colouring
(`Ghost.EG_le_ghost 17`) gives `17`.  **The first order at which the optimal palette is not known to
be attained.** -/
theorem eighteen : 16 ≤ EG 18 ∧ EG 18 ≤ 17 := by
  constructor
  · exact ge 3 (by norm_num)
  · exact EG_le_ghost 17 (by norm_num) (by norm_num) (by decide)

theorem eighteen_cases : EG 18 = 16 ∨ EG 18 = 17 := by
  obtain ⟨h1, h2⟩ := eighteen
  omega

/-- Admissivity is transported along an equality of palettes: re-labelling every edge by a bijection
of the palette preserves the number of colours on every four-set. -/
theorem Admissible.palette {n k k' : ℕ} (c : Col n k) (h : k = k') (hc : Admissible c) :
    Admissible (fun e => h ▸ c e) := by
  subst h
  show Admissible c
  exact hc

/-- **THE FIRST MISSING LINK OF THE GROWTH ROUTE, AS ONE FINITE QUESTION.**  `EG 18 = 16` holds if
and only if there is an admissible sixteen-colouring of `K₁₈`; equivalently
`Sharp6.eighteen_cases` is settled by deciding this single existence statement. -/
theorem eighteen_eq_sixteen : EG 18 = 16 ↔ ∃ (c : Col 18 16), Admissible c := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := EG_admissible 18
    exact ⟨fun e => h ▸ c e, Admissible.palette c h hc⟩
  · rintro ⟨c, hc⟩
    have h1 := EG_le 18 16 c hc
    have h2 := ge 3 (by norm_num)
    exact Nat.le_antisymm h1 h2

/-- **AND THAT ONE FINITE QUESTION IS EXACTLY THE FIRST STEP OF `Grow6At`.**  From the verified anchor
`EG 12 = 11` (on the boundary `6·11 = 5·12+6`) the boundary extension lemma asks for an admissible
`Col 18 16`; so `Grow6At` settles `EG 18 = 16`. -/
theorem Grow6At.eighteen {h : Grow6At} : EG 18 = 16 := by
  obtain ⟨c, hc⟩ := anchor_col
  obtain ⟨d, hd⟩ := h.step (m := 12) (j := 11) (c := c) hc (by norm_num)
  have h1 := EG_le 18 16 d hd
  have h2 := ge 3 (by norm_num)
  exact Nat.le_antisymm h1 h2

end Sharp6

end JSP140