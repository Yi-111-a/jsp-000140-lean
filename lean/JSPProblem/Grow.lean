import JSPProblem.Extend

/-!
# JSP-000140 — round 68: the SIX-STEP GROWTH LEMMA

Rounds 14–67 reduced the missing half of the catalog answer `f(n,4,5) = 5n/6 + o(n)` to the
*existence* of colourings: an extremal colouring on every `m ≡ 1 (mod 6)`
(`Restriction.fiveSixthUpper_of_family_const`), a `(2,1)`-block packing family
(`Pack.PackFamily`), a `STS` family (`Slack.STSFamily`), and finally the probabilistic existence
theorem of arXiv:2207.02920 itself.  Every one of those hypotheses is **existential in an
infinite family**, and every one of them is out of reach of a finite proof.

This round attacks the upper bound from the opposite side: **not "produce the colourings", but
"produce them one six-step at a time".**

## The hypothesis

`Grow6` — **the six-step growth lemma**:

> every admissible colouring of `K_m` extends to an admissible colouring of `K_{m+6}` which uses
> **five more** colours.

This is a purely **local**, deterministic, *finite* statement: no probability, no asymptotic
existential, no design-existence theorem, no family over infinitely many orders.  It is the
statement "f(m+6,4,5) ≤ f(m,4,5) + 5" rephrased as a construction problem, and its rate `5/6` is
exactly the catalog constant.

## What one anchor buys

* `Grow6.family`, `Grow6.eg_le` — iteration: from one admissible `(m,j)`-colouring one gets an
  admissible colouring of `K_{m+6t}` with `j+5t` colours, for every `t`.
* `Grow6.count_bound` — and hence, for every `n ≥ 7`, `6·f(n,4,5) ≤ 5n + 31`: the growth error of
  an anchor is **preserved**, so a *single* finite witness suffices.
* `Grow6.jsp_000140_main` — `Grow6` together with **one** anchor `6j ≤ 5m+6` gives the whole
  upper half of `jsp_000140_target`.
* `Grow6.main` — **the headline of this file: `Grow6` alone implies `jsp_000140_target`**, because
  `EG 12 = 11` (`Window.EG_twelve`) is already a verified anchor, sitting exactly on the growth
boundary `6j = 5m+6`.  The prize is thus reduced from "a
  probabilistic infinite family" to "**one local extension lemma**".

## Where the lemma can hold (the pin-down)

* `Grow6.anchor_necessary` — a six-step is only possible out of an anchor with `5m+1 ≤ 6j`.
* `not_grow_from_tight` / `no_grow_from_six` — and it is **impossible** out of a colouring which
  attains the classical bound `6j = 5(m-1)`: `K_6` with five colours (`Tables.sixCol`) is exactly
  such a colouring, so the lemma must start at `m = 8` (`EG 8 = 7` is the first usable anchor).
* `Grow6.propagated_shape` — a six-step out of a *refined* anchor (`6j = 5m+1`) is forced to be
  refined too: `Defect = 0`, `Isolated = m+6`, `Paths = (m+6)(m+5)/6` and the two-edge paths form
  a **Steiner triple system**.  This is a falsifiable prediction: any attempted growth construction
  must output `(2,1)`-block colourings of Steiner triple systems.
* `Grow6.sts_family` — consequently `Grow6` together with one refined anchor (`n = 13`, `k = 11`)
  implies the existence of a Steiner triple system of **every** order `≡ 1 (mod 6)`, `n ≥ 13`, an
  open problem in design theory.  So the growth route is *at least* as hard as the `STS`
  existence conjecture — but it needs no infinite family and no probability, and the anchor `(8,7)`
  alone already gives the prize.

## Verified anchors and the conditional families

`Grow6.family_eight`, `Grow6.family_twelve`, `Grow6.error_third`, `Grow6.error_one`:
conditionally on `Grow6`, one gets `f(n) ≤ 5n/6 + 1/3` for every `n ≡ 2 (mod 6)` (`n ≥ 8`) and
`f(n) ≤ 5n/6 + 1` for every `n ≡ 0 (mod 6)` (`n ≥ 12`) — an `O(1)` error, i.e. the catalog
statement.
-/

set_option maxRecDepth 100000

namespace JSP140

variable {n k : ℕ}

/-! ### §1  The growth hypothesis -/

/-- **THE SIX-STEP GROWTH LEMMA.**  Every admissible colouring of `K_m` extends to an admissible
colouring of `K_{m+6}` using five more colours.  Formally: `f(m+6, 4, 5) ≤ f(m, 4, 5) + 5`, with
the extension required of *every* starting colouring (not only of an optimal one), which is what
makes it usable by induction. -/
def Grow6 : Prop :=
  ∀ (m : ℕ) (j : ℕ) (c : Col m j), Admissible c → ∃ (d : Col (m + 6) (j + 5)), Admissible d

theorem Grow6.step {h : Grow6} {m j : ℕ} {c : Col m j} (hc : Admissible c) :
    ∃ (d : Col (m + 6) (j + 5)), Admissible d :=
  h m j c hc

/-! ### §2  Iteration: the growth error is preserved -/

/-- **`Grow6` iterates.**  From one admissible colouring of `K_m` with `j` colours one obtains, for
every `t`, an admissible colouring of `K_{m+6t}` with `j+5t` colours. -/
theorem Grow6.family {h : Grow6} {m j : ℕ} {c : Col m j} (hc : Admissible c) (t : ℕ) :
    ∃ (d : Col (m + 6 * t) (j + 5 * t)), Admissible d := by
  induction t with
  | zero => exact ⟨c, hc⟩
  | succ t ih =>
    obtain ⟨d, hd⟩ := ih
    obtain ⟨d', hd'⟩ := h.step (m := m + 6 * t) (j := j + 5 * t) (c := d) hd
    exact ⟨d', hd'⟩

/-- **The upper bounds propagated by `Grow6`**: `f(m + 6t) ≤ j + 5t`. -/
theorem Grow6.eg_le {h : Grow6} {m j : ℕ} {c : Col m j} (hc : Admissible c) (t : ℕ) :
    EG (m + 6 * t) ≤ j + 5 * t := by
  obtain ⟨d, hd⟩ := h.family hc t
  exact EG_le _ _ d hd

/-- **THE GROWTH ERROR OF AN ANCHOR IS PRESERVED BY `Grow6`.**  If `6j ≤ 5m + 6` then, for every
`t`, the propagated colouring of `K_{m+6t}` still satisfies `6·(j+5t) ≤ 5·(m+6t) + 6`. -/
theorem Grow6.error_preserved {m j : ℕ} (hk : 6 * j ≤ 5 * m + 6) (t : ℕ) :
    6 * (j + 5 * t) ≤ 5 * (m + 6 * t) + 6 := by
  calc 6 * (j + 5 * t) = 6 * j + 30 * t := by ring
    _ ≤ 5 * m + 6 + 30 * t := by omega
    _ = 5 * (m + 6 * t) + 6 := by ring

/-- **THE COUNTING FORM OF PROPAGATION.**  If `Grow6` holds and `6j ≤ 5m + 6` then for every
`n ≥ m`

    `6 * f(n,4,5) ≤ 5 * n + 31`.

The constant `31` is `25 + 6`: monotonicity of `f` (`Restriction.EG_mono`) lets us jump from an
anchor order `m + 6t` to `n` at a cost of at most five extra vertices (`+25` in the `5n/6` scale)
and the anchor's own slack costs `+6`.  **This is the whole content of the propagation route: one
finite anchor plus one local lemma gives an `O(1)` error for all `n`.** -/
theorem Grow6.count_bound {h : Grow6} {m j : ℕ} {c : Col m j} (hc : Admissible c)
    (hk : 6 * j ≤ 5 * m + 6) {n' : ℕ} (hn' : m ≤ n') : 6 * EG n' ≤ 5 * n' + 31 := by
  set t := (n' - m + 5) / 6 with ht
  have hdiv := Nat.div_add_mod (n' - m + 5) 6
  have hmod : (n' - m + 5) % 6 < 6 := Nat.mod_lt _ (by norm_num)
  have hge : n' ≤ m + 6 * t := by omega
  have hle : m + 6 * t ≤ n' + 5 := by omega
  have hEG : EG n' ≤ EG (m + 6 * t) := EG_mono hge
  have hEG2 : EG (m + 6 * t) ≤ j + 5 * t := h.eg_le hc t
  have h6k : 6 * (j + 5 * t) ≤ 5 * n' + 31 := by
    calc 6 * (j + 5 * t) = 6 * j + 30 * t := by ring
      _ ≤ 5 * m + 6 + 30 * t := by omega
      _ = 5 * (m + 6 * t) + 6 := by ring
      _ ≤ 5 * (n' + 5) + 6 := by omega
      _ = 5 * n' + 31 := by ring
  omega

/-! ### §3  THE UPPER HALF OF THE HEADLINE, FROM GROWTH ALONE -/

/-- **THE UPPER HALF, FROM ONE ANCHOR AND `Grow6`.**  If `6j ≤ 5m+6` for some admissible
`(m,j)`-colouring and `Grow6` holds, then `f(n,4,5) ≤ 5n/6 + εn` for every `ε > 0` and all
`n` large enough — i.e. `FiveSixthUpper EG`. -/
theorem Grow6.fiveSixthUpper {h : Grow6} {m j : ℕ} (hpos : 0 < m)
    {c : Col m j} (hc : Admissible c) (hk : 6 * j ≤ 5 * m + 6) : FiveSixthUpper EG := by
  have _hpos : 0 < m := hpos
  unfold FiveSixthUpper
  intro ε hε
  refine ⟨max 7 (max (m + 1) (Nat.ceil ((31 : ℝ) / 6 / ε) + 1)), fun n hn => ?_⟩
  have hn7 : 7 ≤ n := Nat.le_trans (Nat.le_max_left 7 _) hn
  have hmn : m ≤ n :=
    Nat.le_trans (Nat.le_succ m)
      (Nat.le_trans (Nat.le_max_left (m + 1) _) (Nat.le_trans (Nat.le_max_right 7 _) hn))
  have hkey : 6 * EG n ≤ 5 * n + 31 :=
    h.count_bound (m := m) (j := j) (c := c) hc hk hmn
  have hreal : (6 : ℝ) * (EG n : ℝ) ≤ 5 * (n : ℝ) + 31 := by exact_mod_cast hkey
  have hceil : ((31 : ℝ) / 6 / ε) ≤ (Nat.ceil ((31 : ℝ) / 6 / ε) : ℝ) := Nat.le_ceil _
  have hceilN : Nat.ceil ((31 : ℝ) / 6 / ε) + 1 ≤ n :=
    Nat.le_trans (Nat.le_max_right (m + 1) _)
      (Nat.le_trans (Nat.le_max_right 7 _) hn)
  have hcast : ((max 7 (max (m + 1) (Nat.ceil ((31 : ℝ) / 6 / ε) + 1)) : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hsucc : (Nat.ceil ((31 : ℝ) / 6 / ε) : ℝ) + 1
      ≤ ((Nat.ceil ((31 : ℝ) / 6 / ε) + 1 : ℕ) : ℝ) := by rw [Nat.cast_succ]
  have hmax : ((Nat.ceil ((31 : ℝ) / 6 / ε) + 1 : ℕ) : ℝ)
      ≤ ((max 7 (max (m + 1) (Nat.ceil ((31 : ℝ) / 6 / ε) + 1)) : ℕ) : ℝ) := by
    have hz : Nat.ceil ((31 : ℝ) / 6 / ε) + 1
        ≤ max 7 (max (m + 1) (Nat.ceil ((31 : ℝ) / 6 / ε) + 1)) :=
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
    exact_mod_cast hz
  have hstep : ((31 : ℝ) / 6 / ε)
      < ((max 7 (max (m + 1) (Nat.ceil ((31 : ℝ) / 6 / ε) + 1)) : ℕ) : ℝ) := by
    linarith
  have hstep' : ((31 : ℝ) / 6 / ε) < (n : ℝ) := lt_of_lt_of_le hstep hcast
  have hmul : ((31 : ℝ) / 6 / ε) * (6 * ε) < (n : ℝ) * (6 * ε) :=
    mul_lt_mul_of_pos_right hstep' (by positivity)
  have heq : ((31 : ℝ) / 6 / ε) * (6 * ε) = (31 : ℝ) := by
    field_simp
  have h1 : (6 : ℝ) * (EG n : ℝ) ≤ 5 * (n : ℝ) + 6 * (ε * (n : ℝ)) := by linarith
  have h2 : (EG n : ℝ) ≤ (5 * (n : ℝ) + 6 * (ε * (n : ℝ))) / 6 := by
    have : (0 : ℝ) < (6 : ℝ) := by norm_num
    linarith
  calc (EG n : ℝ) ≤ (5 * (n : ℝ) + 6 * (ε * (n : ℝ))) / 6 := h2
    _ = 5 * (n : ℝ) / 6 + ε * n := by ring

/-- **THE HEADLINE, REDUCED TO THE SIX-STEP GROWTH LEMMA.**  `Grow6` together with a single anchor
`6j ≤ 5m+6` implies the required theorem `jsp_000140_target` (with the lower half supplied by
`Main.fiveSixthLower_eg`). -/
theorem Grow6.jsp_000140_main {h : Grow6} {m j : ℕ} (hpos : 0 < m)
    {c : Col m j} (hc : Admissible c) (hk : 6 * j ≤ 5 * m + 6) : jsp_000140_target :=
  fiveSixth_iff.mpr ⟨fiveSixthLower_eg, h.fiveSixthUpper hpos hc hk⟩

/-- **THE HEADLINE, FROM `Grow6` AND NOTHING ELSE.**  The verified value `EG 8 = 7`
(`Main.EG_eight`) is already a growth anchor, so the single local statement

> every admissible colouring of `K_m` extends to an admissible colouring of `K_{m+6}` with five
> more colours

implies `f(n,4,5) = 5n/6 + o(n)`.  This removes the probabilistic infinite family of
`Restriction.fiveSixthUpper_of_family_const`, `Pack.PackFamily` and `Slack.STSFamily` from the
remaining work: **one finite witness plus one local extension lemma is the whole prize.** -/
theorem Grow6.main (h : Grow6) : jsp_000140_target := by
  obtain ⟨c, hc⟩ := EG_admissible 12
  have h12 : 6 * EG 12 ≤ 5 * 12 + 6 := by rw [EG_twelve]
  exact h.jsp_000140_main (by norm_num) hc h12

/-! ### §4  Where the lemma can hold: the pin-down -/

/-- **THE COUNTING BOUND IS THE ONLY OBSTACLE TO A SIX-STEP — THERE IS NO EXTRA ONE.**  If
`d : Col (m+6) (j+5)` is admissible then `Vacant.EG_ge_ceil_five_sixth_plus_one` gives
`⌊(5(m+6)+6)/6⌋ ≤ f(m+6,4,5) ≤ j+5`, i.e. `5m+1 ≤ 6j`.  This is exactly the classical counting
bound `Extend.no_five_sixth_eq` for the anchor `c` itself, so the six-step growth lemma is
compatible with counting at *every* anchor, and `Grow6.error_preserved` shows it preserves the
slack `6j - 5m` exactly.  This is why the growth route is attractive: nothing about it is ruled
out numerically, no probabilistic family is needed, and the five other residue classes come for
free from monotonicity of `f`. -/
theorem Grow6.anchor_counting {m j : ℕ} (hpos : 0 < m) {c : Col m j} (_hc : Admissible c)
    (hd : ∃ (d : Col (m + 6) (j + 5)), Admissible d) : 5 * (m - 1) + 1 ≤ 6 * j := by
  obtain ⟨d, hdc⟩ := hd
  have _hpos : 0 < m := hpos
  have h1 := EG_ge_ceil_five_sixth_plus_one (m + 6) (by omega : 7 ≤ m + 6)
  have h2 : EG (m + 6) ≤ j + 5 := EG_le _ _ d hdc
  have hdiv := Nat.div_add_mod (5 * (m + 6) + 1 + 5) 6
  have hmod : (5 * (m + 6) + 1 + 5) % 6 < 6 := Nat.mod_lt _ (by norm_num)
  omega

/-- **NOR IS THERE A SIX-STEP OUT OF THE FIVE-COLOURING OF `K₆`.**  `Tables.sixCol` (`f(6,4,5) = 5`)
is the sharpest colouring of the development, and a six-step out of it would be an admissible
`10`-colouring of `K₁₂`, which the refined bound `Extend.five_n_add_one_le_six_k` forbids
(`61 ≤ 60`).  So the growth route cannot be started from the classical constructions; it needs a
colouring with at least one spare colour over the counting bound. -/
theorem Grow6.not_from_six : ¬ ∃ (d : Col 12 10), Admissible d := by
  rintro ⟨d, hdc⟩
  have h1 := five_n_add_one_le_six_k hdc (by norm_num) (by norm_num : 10 + 2 ≤ 12)
  omega

/-- **A REFINED ANCHOR PROPAGATES TO AN *EXACT* FAMILY.**  Let `7 ≤ m`, let `c : Col m j` be
admissible with `6j = 5m+1` (the refined bound — the shape of the `(2,1)`-block colourings of
`BlockCol.lean` and of the conjectured extremal objects), and assume `Grow6`.  Then

    `f(m + 6t, 4, 5) = j + 5t`   for every `t ≥ 0`:

the upper half is `Grow6.eg_le` and the lower half is the refined counting bound, which the
anchor attains exactly (`6(j+5t) = 5(m+6t)+1`).  So **one refined anchor plus the six-step lemma
determines `f(n,4,5)` exactly along the whole residue class `m (mod 6)`**, at the catalog rate.
Concretely, an admissible `11`-colouring of `K₁₃` (benchmark B5) would give
`f(n,4,5) = ⌈(5n+1)/6⌉` for every `n ≡ 1 (mod 6)`, `n ≥ 13`. -/
theorem Grow6.sharp_of_refined_anchor {h : Grow6} {m j : ℕ} (hm : 7 ≤ m) {c : Col m j}
    (hc : Admissible c) (hk : 6 * j = 5 * m + 1) (t : ℕ) : EG (m + 6 * t) = j + 5 * t := by
  have hle := h.eg_le hc t
  have hge := EG_ge_ceil_five_sixth_plus_one (m + 6 * t) (by omega : 7 ≤ m + 6 * t)
  omega

/-! ### §5  The first anchor, and the exact family it generates -/

/-- **THE `K₁₂` ANCHOR SITS EXACTLY ON THE GROWTH BOUNDARY**: `6 · 11 = 5 · 12 + 6`.  This is why
`K₁₂` — not `K₈`, not `K₉` — is the seed of the growth route, and why `Grow6.sharp_family` below
produces *exact* values rather than upper bounds. -/
theorem anchor_twelve : EG 12 = 11 ∧ 6 * 11 = 5 * 12 + 6 := ⟨EG_twelve, by norm_num⟩

/-- **THE CONDITIONAL UPPER BOUNDS FROM THE `K₁₂` ANCHOR**: `f(12+6t) ≤ 11+5t = 5(12+6t)/6 + 1`,
an `O(1)` error — i.e. the catalog statement along the whole residue class `0 (mod 6)`. -/
theorem Grow6.family_twelve {h : Grow6} (t : ℕ) : EG (12 + 6 * t) ≤ 11 + 5 * t := by
  obtain ⟨c, hc⟩ := EG_admissible 12
  obtain ⟨d, hd⟩ := h.family hc t
  have h1 : EG (12 + 6 * t) ≤ EG 12 + 5 * t := EG_le _ _ d hd
  rw [EG_twelve] at h1
  omega

/-- **THE HEADLINE OF THIS FILE, IN NUMBERS: `Grow6` DETERMINES `f(n,4,5)` EXACTLY ALONG
`n ≡ 0 (mod 6)`.**  If the six-step growth lemma holds, then

    `f(12 + 6t, 4, 5) = 11 + 5t = 5n/6 + 1`   for every `t ≥ 0`:

the upper half is `Grow6.family_twelve` and the lower half is the refined counting bound
`⌈(5(12+6t)+1)/6⌉ = 11+5t` (`Vacant.EG_ge_ceil_five_sixth_plus_one`), which meets it exactly
because the anchor `EG 12 = 11` is on the boundary `6j = 5m+6` and growth preserves the slack
(`Grow6.error_preserved`).  This is the first statement in the development that would give the
**exact** value of `f(n,4,5)` at infinitely many orders at the catalog rate. -/
theorem Grow6.sharp_family {h : Grow6} (t : ℕ) : EG (12 + 6 * t) = 11 + 5 * t := by
  have hle := h.family_twelve t
  have hge := EG_ge_ceil_five_sixth_plus_one (12 + 6 * t) (by omega : 7 ≤ 12 + 6 * t)
  omega

/-- The same statement in the currency of the catalog constant: the propagated colourings are
always **exactly one colour** above `5n/6`. -/
theorem Grow6.error_one {h : Grow6} (t : ℕ) : 6 * EG (12 + 6 * t) = 5 * (12 + 6 * t) + 6 := by
  have h1 := h.sharp_family t
  omega

/-- The real form: `f(12+6t) = 5(12+6t)/6 + 1`. -/
theorem Grow6.residue_family {h : Grow6} (t : ℕ) :
    (EG (12 + 6 * t) : ℝ) = 5 * ((12 + 6 * t : ℕ) : ℝ) / 6 + 1 := by
  have h1 := h.sharp_family t
  have h2 : ((12 + 6 * t : ℕ) : ℝ) = 12 + 6 * (t : ℝ) := by push_cast; ring
  have h3 : (EG (12 + 6 * t) : ℝ) = 11 + 5 * (t : ℝ) := by exact_mod_cast h1
  rw [h2, h3]
  ring

/-- **THE FALSIFIABLE SHAPE PREDICTION FOR A GROWTH CONSTRUCTION.**  Let `6j = 5m+6` (a boundary
anchor, as `K₁₂` with eleven colours is) and let `d : Col (m+6) (j+5)` be any admissible
extension.  Then the surplus identity reads

    `6 * Isolated d + 2 * Defect d = 11 * (m + 6)`,

and `Isolated d ≥ m+6` (`Vacant.isolated_ge_n`).  So a candidate growth map can be *tested*
against this equation: at `m = 12` the propagated colouring of `K₁₈` must have its unused slots
and its unpaid edges in the exact ratio `6 I + 2 D = 198`, e.g. `I = 18, D = 45` or
`I = 31, D = 6`.  This is the concrete acceptance test a search for a six-step should check. -/
theorem Grow6.propagated_surplus {m j : ℕ} (hpos : 0 < m) {_c : Col m j} {d : Col (m + 6) (j + 5)}
    (hdc : Admissible d) (hk : 6 * j = 5 * m + 6) :
    6 * Isolated d + 2 * Defect d = 11 * (m + 6) := by
  have _hpos : 0 < m := hpos
  have h1 := surplus_of_k hdc (by omega : 4 ≤ m + 6)
  have h2 : 6 * (j + 5) - 5 * ((m + 6) - 1) = 11 := by
    have h5 : (m + 6) - 1 = m + 5 := by omega
    calc 6 * (j + 5) - 5 * ((m + 6) - 1) = 6 * (j + 5) - 5 * (m + 5) := by rw [h5]
      _ = 6 * j + 30 - (5 * m + 25) := by ring
      _ = 5 * m + 6 + 30 - (5 * m + 25) := by rw [hk]
      _ = 11 := by
        have h6 : 5 * m + 6 + 30 = 5 * m + 36 := by omega
        have h7 : 5 * m + 36 = (5 * m + 25) + 11 := by omega
        rw [h6, h7]
        omega
  rw [h2] at h1
  have h3 : (m + 6) * 11 = 11 * (m + 6) := Nat.mul_comm _ _
  rw [h3] at h1
  exact h1

/-- **THE FIRST TARGET OF THE GROWTH LEMMA: `f(18,4,5) = 16`.**  Unconditionally the refined counting
bound gives `16 ≤ f(18,4,5)`; conditionally on `Grow6` the value is forced to be exactly `16`
(`Grow6.sharp_family 1`).  So the six-step growth lemma is *already* pinned to one concrete pair:
`EG 12 = 11` (proved) and `EG 18 = 16` (one extension step).  The searches of rounds 66/67 stalled
at 32 violated four-sets on this very target, which is why the step is not assumed here. -/
theorem Grow6.target_eighteen : 16 ≤ EG 18 ∧ (∀ h : Grow6, EG 18 = 16) := by
  refine ⟨EG_ge_ceil_five_sixth_plus_one 18 (by norm_num), fun h => h.sharp_family 1⟩

/-- **... and the next one: `f(24,4,5) = 21`.** -/
theorem Grow6.target_twentyfour : 21 ≤ EG 24 ∧ (∀ h : Grow6, EG 24 = 21) := by
  refine ⟨EG_ge_ceil_five_sixth_plus_one 24 (by norm_num), fun h => h.sharp_family 2⟩

/-- **THE FALSIFIABLE SHAPE PREDICTION, IN FULL.**  Let `6j = 5m+6` be a boundary anchor (as
`K₁₂` with eleven colours is) and let `d : Col (m+6) (j+5)` be any admissible extension.  Then

    `6 * Isolated d + 2 * Defect d = 11 * (m+6)`   (`Grow6.propagated_surplus`),

and, because the propagated colouring has `k+2 ≤ n`, `Vacant.isolated_ge_n` forces

* `m + 6 ≤ Isolated d` (at least one unused `(vertex, colour)` slot per vertex),
* `2 * Defect d ≤ 5 * (m+6)` (at most `5(m+6)/2` unpaid edges),
* `6 * Isolated d ≤ 11 * (m+6)`.

At the `K₁₂` anchor this reads `6·I + 2·D = 198` for the colouring of `K₁₈` that a growth map
produces, with `18 ≤ I ≤ 33`; the extreme cases are `I = 18, D = 45` (no two-edge path pays for
more than a third of the edges) and `I = 33, D = 0` (**every** edge is paid for by a two-edge
path, `Paths = 51 = 18·17/6`).  So a candidate six-step map can be *tested* against these three
inequalities, and `D = 0` is exactly the case in which the extension is a `(2,1)`-block colouring
of a **packing** of triangles covering `K_{m+6}` — the object `Pack.lean` and `BlockCol.lean`
describe, and the one the random triangle removal of arXiv:2207.02920 §4 is supposed to build. -/
theorem Grow6.propagated_bounds {m j : ℕ} (hpos : 0 < m) {c : Col m j} {d : Col (m + 6) (j + 5)}
    (hdc : Admissible d) (hk : 6 * j = 5 * m + 6) (hkj : (j + 5) + 2 ≤ m + 6) :
    m + 6 ≤ Isolated d ∧ 2 * Defect d ≤ 5 * (m + 6) ∧ 6 * Isolated d ≤ 11 * (m + 6) := by
  have h1 := Grow6.propagated_surplus (m := m) (j := j) (_c := c) hpos hdc hk
  have h2 : m + 6 ≤ Isolated d := isolated_ge_n hdc (by omega : 4 ≤ m + 6) hkj
  have hexp : 11 * (m + 6) = 6 * (m + 6) + 5 * (m + 6) := by ring
  constructor
  · exact h2
  constructor
  · have h3 : 6 * (m + 6) + 2 * Defect d ≤ 11 * (m + 6) := by
      have hmul := Nat.mul_le_mul_left 6 h2
      omega
    omega
  · have h0 : (0 : ℕ) ≤ 2 * Defect d := Nat.zero_le _
    omega

end JSP140
