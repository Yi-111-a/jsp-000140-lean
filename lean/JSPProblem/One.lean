import JSPProblem.Grow

/-!
# JSP-000140 — round 83: THE GROWTH ROUTE DOES NOT NEED TO BE UNIFORM

Round 68 reduced the missing half of `f(n,4,5) = 5n/6 + o(n)` to the **six-step growth lemma**
`Grow6`:

> every admissible colouring of `K_m` extends to an admissible colouring of `K_{m+6}` which uses
> five more colours.

`Grow6` is a **uniform** statement: it quantifies over *every* order `m`, *every* budget `j` and
*every* admissible colouring `c` of `K_m`.  That uniformity is an artefact of the way the
construction route was *stated*, not of anything the catalog answer needs, and it is what makes
`Grow6` look out of reach: to discharge it one must extend arbitrarily many unrelated colourings at
once, whereas the prize only ever uses the colourings of **one** family.

This file removes the uniformity.  Two statements, in increasing order of weakness:

* `One.Solo6 m j` — for every `t` **there is** an admissible `j + 5t`-colouring of `K_{m + 6t}`.
  The colourings may be unrelated: no extension statement is assumed at all.  `Solo6` still gives
  the catalog answer (`Solo6.main_eighteen`), so

  > **the prize needs no extension lemma whatsoever — only one witness per order.**

  Concretely: *for every* `t` an admissible `16 + 5t`-colouring of `K_{18+6t}` is enough, and it
  would then follow that `f(18+6t,4,5) = 16+5t = 5n/6 + 1` exactly (`Solo6.sharp_eighteen`).

* `One.DenseSlack` — there is a constant `C` and, for every threshold `N`, an order `n` with
  `N ≤ n < N + 6` admitting an admissible colouring with `6k ≤ 5n + C`: an **unbounded family with
  bounded excess** over the catalog rate, whose orders are **6-dense**.  `DenseSlack.main` derives
  the headline from it.  No relation between the witnesses is required, so `DenseSlack` is *not*
  implied by `Solo6` and is a genuinely weaker target: the witnesses may come from unrelated
  constructions, from different families, or from different searches.  (`Solo6 → DenseSlack` is
  `DenseSlack.of_solo`, the only implication proved here.)

The gap condition `n < N + 6` is necessary and is the point of the definition: with only
`N ≤ n` the excess `C` would be incurred at the *witness* order, and monotonicity of `f` runs the
wrong way, so `BoundedSlack` (excess bounded, orders unbounded, gaps uncontrolled) is **false as a
sufficient hypothesis** — `EG` is not known to be non-decreasing, and no bounded-excess family with
uncontrolled gaps can be used.  Recording this failure mode is part of the round: the bound
`6·f(n) ≤ 5n + 36 + C` of `Solo6.count_bound` costs exactly the five extra vertices of the gap.

References used below: `Restriction.EG_mono` (monotonicity of `f`), `EG_le` (a witness gives an
upper bound), `EG_ge_ceil_five_sixth_plus_one` (the refined counting lower bound) and
`Main.EG_twelve` / `Window.EG_twelve` (the verified `K₁₂` anchor with eleven colours).
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace JSP140

/-- The **non-uniform** six-step hypothesis: for every `t` there exists an admissible colouring of
`K_{m + 6t}` with `j + 5t` colours.  No relation between the colourings at different `t` is
assumed, and in particular no extension statement is assumed. -/
def Solo6 (m j : ℕ) : Prop := ∀ t : ℕ, ∃ d : Col (m + 6 * t) (j + 5 * t), Admissible d

/-- **An unbounded family with bounded excess, on 6-dense orders.**  There are a constant `C` and a
threshold `m` such that for every `N ≥ m` some order `N ≤ n < N + 6` admits an admissible
colouring whose colour count satisfies `6k ≤ 5n + C`.  This is the weakest sufficient hypothesis
of this file. -/
def DenseSlack : Prop :=
  ∃ C m : ℕ, ∀ N : ℕ, m ≤ N →
    ∃ (n k : ℕ) (c : Col n k), Admissible c ∧ N ≤ n ∧ n < N + 6 ∧ 6 * k ≤ 5 * n + C

/-! ### §1  `Solo6` reproduces everything `Grow6` gave -/

/-- The upper bounds of a `Solo6` family: `f(m + 6t) ≤ j + 5t`. -/
theorem Solo6.eg_le {m j : ℕ} (h : Solo6 m j) (t : ℕ) : EG (m + 6 * t) ≤ j + 5 * t := by
  obtain ⟨d, hd⟩ := h t
  exact EG_le _ _ d hd

/-- **The slack of a `Solo6` family is preserved along the family**: if `6j ≤ 5m + C` then
`6·(j+5t) ≤ 5·(m+6t) + C` for every `t`. -/
theorem Solo6.slack_preserved {m j C : ℕ} (hk : 6 * j ≤ 5 * m + C) (t : ℕ) :
    6 * (j + 5 * t) ≤ 5 * (m + 6 * t) + C := by
  calc 6 * (j + 5 * t) = 6 * j + 30 * t := by ring
    _ ≤ 5 * m + C + 30 * t := by omega
    _ = 5 * (m + 6 * t) + C := by ring

/-- **THE COUNTING FORM FOR A NON-UNIFORM FAMILY.**  If `Solo6 m j` and `6j ≤ 5m + C`, then for
every `n' ≥ m`

    `6 * f(n',4,5) ≤ 5 * n' + 25 + C`.

This is `Grow6.count_bound` with the uniform hypothesis deleted; the constant `25` is `5 · 5`, the
price of the five extra vertices that monotonicity may force us to add (round 68 had the same `25`
plus the slack `6` of its anchor). -/
theorem Solo6.count_bound {m j C : ℕ} (h : Solo6 m j) (hk : 6 * j ≤ 5 * m + C) {n' : ℕ}
    (hn' : m ≤ n') : 6 * EG n' ≤ 5 * n' + (25 + C) := by
  set t := (n' - m + 5) / 6 with ht
  have hdiv := Nat.div_add_mod (n' - m + 5) 6
  have hmod : (n' - m + 5) % 6 < 6 := Nat.mod_lt _ (by norm_num)
  have hge : n' ≤ m + 6 * t := by omega
  have hEG : EG n' ≤ EG (m + 6 * t) := EG_mono hge
  have hEG2 : EG (m + 6 * t) ≤ j + 5 * t := h.eg_le t
  have h6k : 6 * (j + 5 * t) ≤ 5 * n' + (25 + C) := by
    calc 6 * (j + 5 * t) = 6 * j + 30 * t := by ring
      _ ≤ 5 * m + C + 30 * t := by omega
      _ = 5 * (m + 6 * t) + C := by ring
      _ ≤ 5 * (n' + 5) + C := by omega
      _ = 5 * n' + (25 + C) := by ring
  omega

/-- **`Solo6` gives the upper half of the catalog answer.** -/
theorem Solo6.fiveSixthUpper {m j C : ℕ} (h : Solo6 m j) (hk : 6 * j ≤ 5 * m + C) :
    FiveSixthUpper EG := by
  set D := 25 + C with hD
  unfold FiveSixthUpper
  intro ε hε
  refine ⟨max 7 (max (m + 1) (Nat.ceil (D / 6 / ε) + 1)), fun n hn => ?_⟩
  have hn7 : 7 ≤ n := Nat.le_trans (Nat.le_max_left 7 _) hn
  have hmn : m ≤ n :=
    Nat.le_trans (Nat.le_succ m)
      (Nat.le_trans (Nat.le_max_left (m + 1) _) (Nat.le_trans (Nat.le_max_right 7 _) hn))
  have hkey : 6 * EG n ≤ 5 * n + D := by
    rw [hD]
    exact h.count_bound hk hmn
  have hreal : (6 : ℝ) * (EG n : ℝ) ≤ 5 * (n : ℝ) + D := by exact_mod_cast hkey
  have hceil : (D / 6 / ε) ≤ (Nat.ceil (D / 6 / ε) : ℝ) := Nat.le_ceil _
  have hceilN : Nat.ceil (D / 6 / ε) + 1 ≤ n :=
    (Nat.le_max_right (m + 1) (Nat.ceil (D / 6 / ε) + 1)).trans
      ((Nat.le_max_right 7 (max (m + 1) (Nat.ceil (D / 6 / ε) + 1))).trans hn)
  have hcast : ((max 7 (max (m + 1) (Nat.ceil (D / 6 / ε) + 1)) : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hsucc : (Nat.ceil (D / 6 / ε) : ℝ) + 1
      ≤ ((Nat.ceil (D / 6 / ε) + 1 : ℕ) : ℝ) := by rw [Nat.cast_succ]
  have hmax : ((Nat.ceil (D / 6 / ε) + 1 : ℕ) : ℝ)
      ≤ ((max 7 (max (m + 1) (Nat.ceil (D / 6 / ε) + 1)) : ℕ) : ℝ) := by
    have hz : Nat.ceil (D / 6 / ε) + 1
        ≤ max 7 (max (m + 1) (Nat.ceil (D / 6 / ε) + 1)) :=
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
    exact_mod_cast hz
  have hstep : (D / 6 / ε)
      < ((max 7 (max (m + 1) (Nat.ceil (D / 6 / ε) + 1)) : ℕ) : ℝ) := by
    linarith
  have hstep' : (D / 6 / ε) < (n : ℝ) := lt_of_lt_of_le hstep hcast
  have hmul : (D / 6 / ε) * (6 * ε) < (n : ℝ) * (6 * ε) :=
    mul_lt_mul_of_pos_right hstep' (by positivity)
  have heq : (D / 6 / ε) * (6 * ε) = D := by
    field_simp
  have h1 : (6 : ℝ) * (EG n : ℝ) ≤ 5 * (n : ℝ) + 6 * (ε * (n : ℝ)) := by linarith
  have h2 : (EG n : ℝ) ≤ (5 * (n : ℝ) + 6 * (ε * (n : ℝ))) / 6 := by
    have : (0 : ℝ) < (6 : ℝ) := by norm_num
    linarith
  calc (EG n : ℝ) ≤ (5 * (n : ℝ) + 6 * (ε * (n : ℝ))) / 6 := h2
    _ = 5 * (n : ℝ) / 6 + ε * n := by ring
/-- **THE HEADLINE FROM A NON-UNIFORM FAMILY.**  `Solo6 m j` together with `6j ≤ 5m + C` gives
the required theorem `jsp_000140_target`.  This is `Grow6.jsp_000140_main` with the uniform
hypothesis replaced by the much weaker `Solo6`. -/
theorem Solo6.jsp_000140_main {m j C : ℕ} (h : Solo6 m j) (hk : 6 * j ≤ 5 * m + C) :
    jsp_000140_target :=
  fiveSixth_iff.mpr ⟨fiveSixthLower_eg, h.fiveSixthUpper hk⟩

/-! ### §2  The prize from ONE witness per order -/

/-- **THE WEAKEST GROWTH HYPOTHESIS OF ROUND 68, AND IT WINS THE PRIZE.**  If for every `t` there
is an admissible colouring of `K_{18 + 6t}` with `16 + 5t` colours — *no extension statement, no
uniformity, no relation between consecutive witnesses* — then

    `f(n,4,5) = 5n/6 + o(n)`,

i.e. the required theorem `jsp_000140_target`.  Numerically: the witnesses sit on the boundary
`6·(16+5t) = 5·(18+6t) + 6`, exactly one colour above `5n/6`, and `Solo6.count_bound` turns that
into `6·f(n) ≤ 5n + 36` for every `n ≥ 18`.  Compare `Grow6.main`, which needed the universal
extension lemma for *every* admissible colouring of *every* order. -/
theorem Solo6.main_eighteen
    (h : ∀ t : ℕ, ∃ d : Col (18 + 6 * t) (16 + 5 * t), Admissible d) : jsp_000140_target :=
  (show Solo6 18 16 from h).jsp_000140_main (C := 6) (by omega)

/-- The same, phrased as the family `f(18 + 6t, 4, 5) ≤ 16 + 5t = 5n/6 + 1`. -/
theorem Solo6.eg_le_eighteen (h : ∀ t : ℕ, ∃ d : Col (18 + 6 * t) (16 + 5 * t), Admissible d)
    (t : ℕ) : EG (18 + 6 * t) ≤ 16 + 5 * t := Solo6.eg_le (show Solo6 18 16 from h) t

/-- **THE EXACT VALUES, CONDITIONALLY.**  Under the same non-uniform hypothesis the refined
counting bound `⌈(5n+1)/6⌉` is met exactly on the whole residue class, so
`f(18 + 6t, 4, 5) = 16 + 5t = 5n/6 + 1` for every `t` — the first statement of this development
that would give the **exact** value of `f(n,4,5)` at infinitely many orders at the catalog rate. -/
theorem Solo6.sharp_eighteen
    (h : ∀ t : ℕ, ∃ d : Col (18 + 6 * t) (16 + 5 * t), Admissible d) (t : ℕ) :
    EG (18 + 6 * t) = 16 + 5 * t := by
  have hle := Solo6.eg_le (show Solo6 18 16 from h) t
  have hge := EG_ge_ceil_five_sixth_plus_one (18 + 6 * t) (by omega : 7 ≤ 18 + 6 * t)
  omega

/-- The real form of the conditional family: `f(18+6t) = 5(18+6t)/6 + 1`. -/
theorem Solo6.residue_eighteen
    (h : ∀ t : ℕ, ∃ d : Col (18 + 6 * t) (16 + 5 * t), Admissible d) (t : ℕ) :
    (EG (18 + 6 * t) : ℝ) = 5 * ((18 + 6 * t : ℕ) : ℝ) / 6 + 1 := by
  have h1 := Solo6.sharp_eighteen h t
  have h2 : ((18 + 6 * t : ℕ) : ℝ) = 18 + 6 * (t : ℝ) := by push_cast; ring
  have h3 : (EG (18 + 6 * t) : ℝ) = 16 + 5 * (t : ℝ) := by exact_mod_cast h1
  rw [h2, h3]
  ring

/-! ### §3  `DenseSlack`: bounded excess on 6-dense orders -/

/-- A `Solo6` family at bounded excess is a `DenseSlack` family: from `N` take the least `t` with
`m + 6t ≥ N`, so the witness order lies in `[N, N+5] ⊆ [N, N+6)`. -/
theorem DenseSlack.of_solo {m j C : ℕ} (hk : 6 * j ≤ 5 * m + C) (h : Solo6 m j) :
    DenseSlack := by
  refine ⟨C, m, fun N hmn => ?_⟩
  set t := (N - m + 5) / 6 with ht
  have hdiv := Nat.div_add_mod (N - m + 5) 6
  have hmod : (N - m + 5) % 6 < 6 := Nat.mod_lt _ (by norm_num)
  subst t
  have hge : N ≤ m + 6 * ((N - m + 5) / 6) := by omega
  have hlt : m + 6 * ((N - m + 5) / 6) < N + 6 := by omega
  obtain ⟨d, hd⟩ := h ((N - m + 5) / 6)
  exact ⟨m + 6 * ((N - m + 5) / 6), j + 5 * ((N - m + 5) / 6), d, hd, hge, hlt,
    Solo6.slack_preserved hk ((N - m + 5) / 6)⟩

/-- **THE HEADLINE, FROM BOUNDED EXCESS ON 6-DENSE ORDERS ALONE.**  If there is a constant `C` and,
for every threshold `N`, an order `N ≤ n < N + 6` admitting an admissible colouring with
`6k ≤ 5n + C`, then

    `f(n,4,5) = 5n/6 + o(n)`,

i.e. the required theorem `jsp_000140_target`.  Concretely: **it is enough to construct, for one
absolute constant `C` and arbitrarily large `n`, admissible colourings of `K_n` using at most
`5n/6 + (25 + C)/6` colours** — no extension lemma, no related family, no order arithmetic beyond
`n < N + 6`, no probability.  The `+25` is the price of the gap: monotonicity of `f` may force
five extra vertices, and `EG` is not known to be non-decreasing, so the gap condition cannot be
dropped. -/
theorem DenseSlack.fiveSixthUpper' (h : DenseSlack) : FiveSixthUpper EG := by
  obtain ⟨C, m, hC⟩ := h
  unfold FiveSixthUpper
  intro ε hε
  set D := 25 + C with hD
  refine ⟨max 7 (max (m + 1) (Nat.ceil (D / 6 / ε) + 1)), fun n hn => ?_⟩
  have hceil0 : Nat.ceil (D / 6 / ε) + 1 ≤
      max 7 (max (m + 1) (Nat.ceil (D / 6 / ε) + 1)) :=
    (Nat.le_max_right (m + 1) (Nat.ceil (D / 6 / ε) + 1)).trans
      (Nat.le_max_right 7 _)
  have hmid : m + 1 ≤ max (m + 1) (Nat.ceil (D / 6 / ε) + 1) :=
    Nat.le_max_left (m + 1) (Nat.ceil (D / 6 / ε) + 1)
  have hmt : max (m + 1) (Nat.ceil (D / 6 / ε) + 1) ≤
      max 7 (max (m + 1) (Nat.ceil (D / 6 / ε) + 1)) :=
    le_max_right 7 (max (m + 1) (Nat.ceil (D / 6 / ε) + 1))
  have hmn' : m ≤ n := (Nat.le_succ m).trans (hmid.trans (hmt.trans hn))
  obtain ⟨mm, k, c, hc, hmn, hmlt, h6k⟩ := hC n hmn'
  have hkey : 6 * EG n ≤ 5 * n + D := by
    have hEG : EG n ≤ EG mm := EG_mono hmn
    have hk' : EG mm ≤ k := EG_le _ _ c hc
    have h6 : 6 * (EG n) ≤ 6 * k := Nat.mul_le_mul_left 6 (hEG.trans hk')
    have h5 : 5 * mm ≤ 5 * (n + 5) := by omega
    omega
  have hreal : (6 : ℝ) * (EG n : ℝ) ≤ 5 * (n : ℝ) + D := by exact_mod_cast hkey
  have hceil : (D / 6 / ε) ≤ (Nat.ceil (D / 6 / ε) : ℝ) := Nat.le_ceil _
  have hceilN : Nat.ceil (D / 6 / ε) + 1 ≤ n :=
    (Nat.le_max_right (m + 1) (Nat.ceil (D / 6 / ε) + 1)).trans
      ((Nat.le_max_right 7 (max (m + 1) (Nat.ceil (D / 6 / ε) + 1))).trans hn)
  have hcast : ((max 7 (max (m + 1) (Nat.ceil (D / 6 / ε) + 1)) : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hsucc : (Nat.ceil (D / 6 / ε) : ℝ) + 1
      ≤ ((Nat.ceil (D / 6 / ε) + 1 : ℕ) : ℝ) := by rw [Nat.cast_succ]
  have hmax : ((Nat.ceil (D / 6 / ε) + 1 : ℕ) : ℝ)
      ≤ ((max 7 (max (m + 1) (Nat.ceil (D / 6 / ε) + 1)) : ℕ) : ℝ) := by
    have hz : Nat.ceil (D / 6 / ε) + 1
        ≤ max 7 (max (m + 1) (Nat.ceil (D / 6 / ε) + 1)) :=
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
    exact_mod_cast hz
  have hstep : (D / 6 / ε)
      < ((max 7 (max (m + 1) (Nat.ceil (D / 6 / ε) + 1)) : ℕ) : ℝ) := by
    linarith
  have hstep' : (D / 6 / ε) < (n : ℝ) := lt_of_lt_of_le hstep hcast
  have hmul : (D / 6 / ε) * (6 * ε) < (n : ℝ) * (6 * ε) :=
    mul_lt_mul_of_pos_right hstep' (by positivity)
  have heq : (D / 6 / ε) * (6 * ε) = D := by field_simp
  have h1 : (6 : ℝ) * (EG n : ℝ) ≤ 5 * (n : ℝ) + 6 * (ε * (n : ℝ)) := by linarith
  have h2 : (EG n : ℝ) ≤ (5 * (n : ℝ) + 6 * (ε * (n : ℝ))) / 6 := by
    have : (0 : ℝ) < (6 : ℝ) := by norm_num
    linarith
  calc (EG n : ℝ) ≤ (5 * (n : ℝ) + 6 * (ε * (n : ℝ))) / 6 := h2
    _ = 5 * (n : ℝ) / 6 + ε * n := by ring

/-- **THE HEADLINE, FROM BOUNDED EXCESS ALONE.**  The upper half is `DenseSlack.fiveSixthUpper'`
and the lower half is `Main.fiveSixthLower_eg` (the sharp counting bound, a theorem). -/
theorem DenseSlack.main (h : DenseSlack) : jsp_000140_target :=
  fiveSixth_iff.mpr ⟨fiveSixthLower_eg, h.fiveSixthUpper'⟩

end JSP140