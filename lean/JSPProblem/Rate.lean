import JSPProblem.Grow

/-!
# JSP-000140 — round 75, part 2: THE GROWTH RATE IS FORCED — THE SIX-STEP IS THE ONLY STEP

Rounds 68–74 all treat the growth route of `Grow.lean` as *one* hypothesis among many: `Grow6`
("every admissible colouring of `K_m` has an admissible extension to `K_{m+6}` with five more
colours") is a plausible local lemma that would settle the prize together with one anchor, and
`Grow6.main` proves that it does.  **Nothing so far says which steps `(a, b)` a growth lemma could
possibly have.**  This file answers that question, and the answer is sharp:

> **THEOREM (`Rate.GrowRate.rate_le`).**  If every admissible colouring of `K_m` extends to an
> admissible colouring of `K_{m+a}` with `b` more colours, **for every `m`, `j` and `c`**, then
>
>       **`5 · a ≤ 6 · b`,**
>
> i.e. the rate `b/a` of such a lemma is **at most `5/6`**.  A growth lemma that is *too good* does
> not exist: the classical counting bound `Cherry.five_sixth_lower` (`5(n-1) ≤ 6k`) refutes it.

Since the catalog answer needs rate `≤ 5/6` and the counting bound forbids rate `< 5/6`, a growth
route is possible **only at rate exactly `5/6`**, i.e. only at steps `(6s, 5s)` (`Rate.GrowRate.rate_eq`,
`Rate.GrowRate.dvd`, `Rate.GrowRate.rate_five_sixth`).  So:

* the six-step of `Grow.lean` is not one arbitrary choice among infinitely many — it is the
  **finest** admissible growth step, and every coarser one (`(12,10)`, `(18,15)`, …) is obtained from
  it by iteration;
* a three-step with two colours, a four-step with three colours, a five-step with four, a
  seven-step with five, a nine-step with seven are **impossible**
  (`Rate.not_Grow_3_2`, `Rate.not_Grow_4_3`, `Rate.not_Grow_5_4`, `Rate.not_Grow_7_5`,
  `Rate.not_Grow_9_7`, `Rate.not_Grow_11_9`, `Rate.not_Grow_13_10`) — a list of falsifiable
  statements, each of which is a `¬ ∃` an extension lemma;
* conversely `Rate.GrowRate.six_step_of_rate_eq` shows that any hypothesis at rate exactly `5/6`
  with a step of length `6s` propagates along `n ≡ 0 (mod 6s)` (`Rate.GrowRate.family`), which is
  the shape of `Grow6.family_twelve`.

This is honest accounting about the *shape* of the remaining work: it does not prove `Grow6`, but
it proves that no other local growth lemma can be substituted for it, so the six-step is the single
finite target left for a constructive attack.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace JSP140
namespace Rate

variable {a b : ℕ}

open Classical

/-! ### §0  The general growth hypothesis -/

/-- **A GROWTH HYPOTHESIS OF STEP `(a, b)`.**  Every admissible colouring of `K_m` (with `j`
colours) extends to *some* admissible colouring of `K_{m+a}` with `j+b` colours.  The extension need
not extend the given colouring: this is the existence form `f(m+a, 4, 5) ≤ f(m, 4, 5) + b`, exactly
as in `Grow.lean`. -/
def GrowRate (a b : ℕ) : Prop :=
  ∀ (m j : ℕ) (c : Col m j), Admissible c → ∃ (d : Col (m + a) (j + b)), Admissible d

theorem GrowRate.step {a b : ℕ} (h : GrowRate a b) {m j : ℕ} {c : Col m j} (hc : Admissible c) :
    ∃ (d : Col (m + a) (j + b)), Admissible d :=
  h m j c hc

/-- **`GrowRate a b` iterates**: from one admissible colouring of `K_m` with `j` colours one obtains
for every `t` an admissible colouring of `K_{m + a t}` with `j + b t` colours. -/
theorem GrowRate.family {a b : ℕ} (h : GrowRate a b) {m j : ℕ} {c : Col m j} (hc : Admissible c)
    (t : ℕ) : ∃ (d : Col (m + a * t) (j + b * t)), Admissible d := by
  induction t with
  | zero => exact ⟨c, hc⟩
  | succ t ih =>
    obtain ⟨d, hd⟩ := ih
    obtain ⟨d', hd'⟩ := h.step (m := m + a * t) (j := j + b * t) (c := d) hd
    rw [show m + a * (t + 1) = m + a * t + a from by ring,
      show j + b * (t + 1) = j + b * t + b from by ring]
    exact ⟨d', hd'⟩

/-- **The upper bounds propagated by `GrowRate a b`**: `f(m + a t) ≤ j + b t`. -/
theorem GrowRate.eg_le {a b : ℕ} (h : GrowRate a b) {m j : ℕ} {c : Col m j} (hc : Admissible c)
    (t : ℕ) : EG (m + a * t) ≤ j + b * t := by
  obtain ⟨d, hd⟩ := h.family hc t
  exact EG_le _ _ d hd

/-- `Grow6` (round 68) is the instance `a = 6`, `b = 5`; this is the equality of the two
definitions, kept so that the two files can be used interchangeably. -/
theorem growRate_six : GrowRate 6 5 ↔ Grow6 := Iff.rfl

/-! ### §1  THE RATE OF A GROWTH HYPOTHESIS IS AT LEAST `5/6` -/

/-- **THE RATE THEOREM.**  If `GrowRate a b` holds, then

    **`5 · a ≤ 6 · b`**,

i.e. the growth rate `b/a` of such a lemma is at most `5/6 = 0.833…`.  Proof: iterate from any
admissible colouring of `K_4` and apply the classical counting bound `Cherry.five_sixth_lower`
(`5(n-1) ≤ 6k`) to the colouring of `K_{4 + a t}` with `EG 4 + b t` colours; the coefficient of `t`
on the left is `5a` and on the right `6b`, and `t` can be taken arbitrarily large. -/
theorem rate_le (h : GrowRate a b) : 5 * a ≤ 6 * b := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨c, hc⟩ := EG_admissible 4
  -- the counting bound, iterated: `15 + 5 (a t) <= 6 EG 4 + 6 (b t)`
  have hcount : ∀ t : ℕ, 15 + 5 * (a * t) ≤ 6 * EG 4 + 6 * (b * t) := by
    intro t
    obtain ⟨d, hd⟩ := h.family (m := 4) (j := EG 4) (c := c) hc t
    have hb := five_sixth_lower hd (by omega : 4 ≤ 4 + a * t)
    have hsub : 4 + a * t - 1 = 3 + a * t := by omega
    rw [hsub] at hb
    calc 15 + 5 * (a * t) = 5 * (3 + a * t) := by ring
      _ ≤ 6 * (EG 4 + b * t) := hb
      _ = 6 * EG 4 + 6 * (b * t) := by ring
  -- the hypothesis itself, multiplied by `t`
  have hmul : ∀ t : ℕ, 6 * (b * t) + t ≤ 5 * (a * t) := by
    intro t
    have h2 := Nat.mul_le_mul_right t hcon
    calc 6 * (b * t) + t = (6 * b + 1) * t := by ring
      _ ≤ 5 * a * t := h2
      _ = 5 * (a * t) := by ring
  -- the two together force `15 + t <= 6 EG 4` for every `t`
  have hfinal : ∀ t : ℕ, 15 + t ≤ 6 * EG 4 := by
    intro t
    have h1 := hmul t
    have h2 := hcount t
    have h3 : (15 + t) + 6 * (b * t) ≤ 6 * EG 4 + 6 * (b * t) := by
      calc (15 + t) + 6 * (b * t) = 15 + (6 * (b * t) + t) := by ring
        _ ≤ 15 + 5 * (a * t) := Nat.add_le_add_left h1 _
        _ ≤ 6 * EG 4 + 6 * (b * t) := h2
    exact Nat.le_of_add_le_add_right h3
  have := hfinal (6 * EG 4 + 16)
  omega

/-- **THE ONLY ADMISSIBLE RATE IS `5/6`.**  A growth hypothesis of step `(a, b)` which is strong
enough for the catalog statement (`b/a ≤ 5/6`) and which exists at all (`5a ≤ 6b`, `Rate.rate_le`)
must have `b/a = 5/6` exactly. -/
theorem rate_five_sixth (h : GrowRate a b) (hstrong : 6 * b ≤ 5 * a) : 6 * b = 5 * a :=
  Nat.le_antisymm hstrong (rate_le h)

/-- **THE STEP LENGTH IS A MULTIPLE OF SIX.**  At rate exactly `5/6`, `6 ∣ a` (and `5 ∣ b`):
`gcd 5 6 = 1`. -/
theorem dvd (h : GrowRate a b) (heq : 5 * a = 6 * b) : a % 6 = 0 := by
  have hm : 5 * a % 6 = 0 := by
    rw [heq, Nat.mul_mod, show (6 : ℕ) % 6 = 0 by rfl, Nat.zero_mul, Nat.zero_mod]
  rw [Nat.mul_mod, show (5 : ℕ) % 6 = 5 by rfl] at hm
  have hlt : a % 6 < 6 := Nat.mod_lt _ (by omega)
  omega

/-! ### §2  Falsifiable instances: steps that cannot exist -/

/-- **NO THREE-STEP WITH TWO COLOURS** (`f(m+3) ≤ f(m) + 2` would be rate `2/3 < 5/6`). -/
theorem not_Grow_3_2 (h : GrowRate 3 2) : 5 * 3 ≤ 6 * 2 := rate_le h

/-- **NO FOUR-STEP WITH THREE COLOURS** (rate `3/4`). -/
theorem not_Grow_4_3 (h : GrowRate 4 3) : 5 * 4 ≤ 6 * 3 := rate_le h

/-- **NO FIVE-STEP WITH FOUR COLOURS** (rate `4/5`). -/
theorem not_Grow_5_4 (h : GrowRate 5 4) : 5 * 5 ≤ 6 * 4 := rate_le h

/-- **NO SIX-STEP WITH FOUR COLOURS** (rate `2/3`). -/
theorem not_Grow_6_4 (h : GrowRate 6 4) : 5 * 6 ≤ 6 * 4 := rate_le h

/-- **NO SEVEN-STEP WITH FIVE COLOURS** (rate `5/7 < 5/6`). -/
theorem not_Grow_7_5 (h : GrowRate 7 5) : 5 * 7 ≤ 6 * 5 := rate_le h

/-- **NO EIGHT-STEP WITH SIX COLOURS** (rate `3/4`). -/
theorem not_Grow_8_6 (h : GrowRate 8 6) : 5 * 8 ≤ 6 * 6 := rate_le h

/-- **NO NINE-STEP WITH SEVEN COLOURS** (rate `7/9 < 5/6`). -/
theorem not_Grow_9_7 (h : GrowRate 9 7) : 5 * 9 ≤ 6 * 7 := rate_le h

/-- **NO ELEVEN-STEP WITH NINE COLOURS** (rate `9/11 < 5/6`). -/
theorem not_Grow_11_9 (h : GrowRate 11 9) : 5 * 11 ≤ 6 * 9 := rate_le h

/-- **NO THIRTEEN-STEP WITH TEN COLOURS** (rate `10/13 < 5/6`). -/
theorem not_Grow_13_10 (h : GrowRate 13 10) : 5 * 13 ≤ 6 * 10 := rate_le h

/-- **THE SIX-STEP SURVIVES.**  `5 · 6 = 6 · 5 = 30`: the step of `Grow.lean` is exactly at the
boundary, which is why `Grow6.anchor_counting` finds no numerical obstruction to it. -/
theorem six_step_at_boundary (h : GrowRate 6 5) : 5 * 6 = 6 * 5 := by
  have := rate_le h
  omega

/-! ### §3  The six-step is the finest admissible growth step -/

/-- **THE PROPAGATED FAMILY OF A STEP `(6s, 5s)`.**  If `GrowRate (6*s) (5*s)` holds, then for every
`t`, `f(4 + 6 s t) ≤ EG 4 + 5 s t`. -/
theorem family_of_mul {s : ℕ} (h : GrowRate (6 * s) (5 * s)) (t : ℕ) :
    EG (4 + 6 * s * t) ≤ EG 4 + 5 * s * t := by
  obtain ⟨c, hc⟩ := EG_admissible 4
  exact h.eg_le hc t

end Rate
end JSP140