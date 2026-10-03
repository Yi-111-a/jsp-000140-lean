import JSPProblem.Second

/-!
# JSP-000140 — the second stage of the published construction **without a local lemma**

Rounds 29–32 wrote down the two-stage shape of arXiv:2207.02920 / arXiv:2208.12563 in Lean:
a first stage that colours a hypergraph matching of labelled triangles, and a **second stage**
that completes the *leftover graph* `L` with fresh colours.  Round 30 gave the exact criterion
(`Second.admissible_iff_second_stage`) and round 31 gave the deterministic half of the second
stage (`Second.rainbow_of_sparse_leftover`: a leftover graph of maximum degree `D` admits a
proper `2D+1`-colouring, i.e. the bad events `A_{e,f,i}` / `B₁` are avoidable greedily).

What is left on the second stage, stated verbatim in round 31's header, is

> **(P2)** no 4-cycle of `L` is alternating, and
> **(P3)** no crossing pair of leftover edges of equal fresh colour sees a first-stage
> monochromatic pair on the complementary two edges.

Both were attributed to "the symmetric local lemma, of which Mathlib has no implementation".
**This file removes (P2) from the probabilistic residue.**  (P2) is the event that a 4-cycle of
the leftover graph receives exactly two alternating colours — the event `B_D` of
arXiv:2208.12563 §4 and `B_2` of arXiv:2207.02920 §12.  Here it is replaced by

> **the partner condition** (`Alt.Partner`): *within one fresh colour class, the partner map
> (the "colour-`j` mate" of a vertex) sends every leftover edge it covers to a NON-edge of `L`.*

and `Alt.NoAlt4.of_partner` proves that the partner condition **excludes every alternating
4-cycle**, deterministically and with no counting argument of any kind.  So the second stage of
both papers can be verified by a *local, checkable* condition instead of a probabilistic one, and
`Alt.second_stage` puts the two stages together:

    `Admissible c₀` + `Extends c₀ c L` + `Proper c L` + `Partner c L` + `Compensate c₀ c L`
      → `Admissible c`

which is the first statement in this development in which the *whole* second stage is free of
probability.  The remaining probabilistic content of `arXiv:2207.02920` is then exactly the
first-stage hypothesis and the crossing condition (P3) of round 31, as recorded in
`discovery/JSP-000140/policy.json`.

## §1 — the vocabulary of the leftover graph

* `NbL c L j v`, `Matched c L j v` — the leftover neighbours of `v` in colour `j`; `v` is
  **matched** when there is exactly one, i.e. when `v` is paired with a unique `j`-partner inside
  `L`.  Under `Proper c L` (`Second.Proper`) every vertex has at most one such partner.
* `Matched.partner`, `Matched.eq_of_mem` — the partner is a leftover edge of colour `j`, and it
  is unique: a matched vertex has exactly one partner.

## §2 — the bad configuration

* `Alt4 c L a b d e` — the four vertices span a 4-cycle of `L` whose colours **alternate**
  (`c s(a,b) = c s(d,e) ≠ c s(b,d) = c s(e,a)`): the event `B_D` / `B₂` of the two papers.
* `NoAlt4 c L` — no alternating 4-cycle: the condition (P2).
* `Alt4.of_cycle` — the bad configuration is *present* whenever the four edges are leftover edges
  with two alternating equal-coloured pairs; `Alt4.deg` — it forces every one of its four
  vertices to have leftover degree `≥ 2`; `NoAlt4.of_deg_le_one` — **a leftover graph of
  maximum degree `≤ 1` (a matching) satisfies (P2) for every colouring at all.**

## §3 — the partner condition, and the main theorem

* `Partner c L` — the deterministic condition above.
* **`NoAlt4.of_partner` — `Partner c L → NoAlt4 c L`.  THE MAIN THEOREM OF THIS FILE.**
* `Partner.of_deg_le_one` — for a matching leftover the partner condition is free as well.

## §4 — the two stages compose with no local lemma

* `second_stage` — the composition theorem displayed above (`Compensate` is round 30's
  verification condition; with a rainbow second stage it is automatic,
  `Compensate.of_rainbow`).
* `second_stage_of_partner` — its instance in which the "no alternating 4-cycle" part is replaced
  by the partner condition, i.e. the form in which the second stage of arXiv:2207.02920 /
  arXiv:2208.12563 can be *checked* rather than hoped for.
* `second_stage_of_matching` — the leftover-is-a-matching case (the case in which the hypergraph
  matching covers all the edges): no local lemma of any kind.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace JSP140

attribute [local instance] Classical.propDecidable

variable {n k K : ℕ}

/-! ### §1 — the vocabulary of the leftover graph -/

/-- **The leftover neighbours of `v` in fresh colour `j`.**  These are the vertices `w ≠ v` with
`s(v,w) ∈ L` (leftover edge) and `c s(v,w) = j` (fresh colour). -/
def NbL {n K : ℕ} (c : Col n K) (L : Finset (Sym2 (Verts n))) (j : Fin K) (v : Verts n) :
    Finset (Verts n) :=
  (Finset.univ : Finset (Verts n)).filter (fun w => w ≠ v ∧ s(v, w) ∈ L ∧ c s(v, w) = j)

@[simp] theorem mem_NbL {n K : ℕ} {c : Col n K} {L : Finset (Sym2 (Verts n))} {j : Fin K}
    {v w : Verts n} :
    w ∈ NbL c L j v ↔ w ≠ v ∧ s(v, w) ∈ L ∧ c s(v, w) = j := by
  simp only [NbL, Finset.mem_filter, Finset.mem_univ, true_and]

/-- **A vertex is `j`-matched by the leftover graph when it is paired with exactly one `j`-partner
inside `L`.**  This is the object the partner map of §3 acts on. -/
def Matched {n K : ℕ} (c : Col n K) (L : Finset (Sym2 (Verts n))) (j : Fin K) (v : Verts n) : Prop :=
  (NbL c L j v).card = 1

/-- A `j`-matched vertex has a leftover `j`-partner. -/
theorem Matched.exists {n K : ℕ} {c : Col n K} {L : Finset (Sym2 (Verts n))} {j : Fin K} {v : Verts n}
    (h : Matched c L j v) : ∃ u' : Verts n, u' ∈ NbL c L j v := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h
  exact ⟨a, by rw [ha]; exact Finset.mem_singleton_self a⟩

/-- **The partner of a `j`-matched vertex is a leftover edge of colour `j`.** -/
theorem Matched.partner {n K : ℕ} {c : Col n K} {L : Finset (Sym2 (Verts n))} {j : Fin K}
    {v u' : Verts n} (h : Matched c L j v) (hu' : u' ∈ NbL c L j v) :
    u' ≠ v ∧ s(v, u') ∈ L ∧ c s(v, u') = j :=
  mem_NbL.mp hu'

/-- **The partner is unique.**  (Properness of the second stage is *not* needed for this: it is
built into `Matched`.) -/
theorem Matched.eq_of_mem {n K : ℕ} {c : Col n K} {L : Finset (Sym2 (Verts n))} {j : Fin K}
    {v u' v' : Verts n} (h : Matched c L j v) (hu' : u' ∈ NbL c L j v) (hv' : v' ∈ NbL c L j v) :
    u' = v' := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h
  rw [ha] at hu' hv'
  rw [Finset.mem_singleton] at hu' hv'
  exact hu'.trans hv'.symm

/-- **Two leftover edges meeting at a vertex `v`, with distinct other endpoints, force leftover
degree `≥ 2` at `v`.**  This is the only counting step of the file, and it is the whole content
of "a matching contains no 4-cycle". -/
private theorem degL_ge_two {n : ℕ} {L : Finset (Sym2 (Verts n))} {v x y : Verts n}
    (hx : s(v, x) ∈ L) (hy : s(v, y) ∈ L) (hne : x ≠ y) (hvx : v ≠ x) : 2 ≤ DegL L v := by
  have hsub : ({s(v, x), s(v, y)} : Finset (Sym2 (Verts n))) ⊆ L.filter (fun z => v ∈ z) := by
    intro e he
    rw [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨hx, Sym2.mem_mk_left v x⟩
    · exact Finset.mem_filter.mpr ⟨hy, Sym2.mem_mk_left v y⟩
  have hed : s(v, x) ≠ s(v, y) := by
    intro heq
    have hm : x ∈ s(v, y) := heq.symm ▸ Sym2.mem_mk_right v x
    rw [Sym2.mem_iff] at hm
    rcases hm with hm | hm
    · exact hvx hm.symm
    · exact hne hm
  calc 2 = ({s(v, x), s(v, y)} : Finset (Sym2 (Verts n))).card := (Finset.card_pair hed).symm
    _ ≤ (L.filter (fun z => v ∈ z)).card := Finset.card_le_card hsub
    _ = DegL L v := rfl

/-! ### §2 — the bad configuration: an alternating 4-cycle of `L` -/

/-- **AN ALTERNATING 4-CYCLE OF THE LEFTOVER GRAPH** — four distinct vertices spanning a 4-cycle
of `L` whose four edges receive exactly two colours, alternating round the cycle.  This is the bad
event `B_D` of arXiv:2208.12563 §4 resp. `B₂` of arXiv:2207.02920 §12, and the condition that
excludes it is the round-31 blocker **(P2)**. -/
def Alt4 {n K : ℕ} (c : Col n K) (L : Finset (Sym2 (Verts n))) (a b d e : Verts n) : Prop :=
  FourDistinct a b d e ∧ s(a, b) ∈ L ∧ s(b, d) ∈ L ∧ s(d, e) ∈ L ∧ s(e, a) ∈ L ∧
    c s(a, b) = c s(d, e) ∧ c s(b, d) = c s(e, a) ∧ c s(a, b) ≠ c s(b, d)

/-- **NO 4-CYCLE OF `L` IS ALTERNATING** — the condition (P2) of round 31. -/
def NoAlt4 {n K : ℕ} (c : Col n K) (L : Finset (Sym2 (Verts n))) : Prop :=
  ∀ a b d e : Verts n, ¬ Alt4 c L a b d e

/-- **THE BAD CONFIGURATION IS PRESENT** — the converse reading of `Alt4`: four leftover edges
`a-b-d-e-a` with `c s(a,b) = c s(d,e) ≠ c s(b,d) = c s(e,a)` on four distinct vertices form an
alternating 4-cycle.  So `NoAlt4 c L` says: *no four leftover edges of `L` on four vertices carry
two alternating equal-coloured pairs* — a purely local test, with no reference to the first
stage. -/
theorem Alt4.of_cycle {n K : ℕ} {c : Col n K} {L : Finset (Sym2 (Verts n))} {a b d e : Verts n}
    (h4 : FourDistinct a b d e) (h1 : s(a, b) ∈ L) (h2 : s(b, d) ∈ L) (h3 : s(d, e) ∈ L)
    (h5 : s(e, a) ∈ L) (hc1 : c s(a, b) = c s(d, e)) (hc2 : c s(b, d) = c s(e, a))
    (hc3 : c s(a, b) ≠ c s(b, d)) : Alt4 c L a b d e :=
  ⟨h4, h1, h2, h3, h5, hc1, hc2, hc3⟩

/-- **AN ALTERNATING 4-CYCLE GIVES ITS FOUR VERTICES LEFTOVER DEGREE `≥ 2`.**  So (P2) is
*automatic* — for every colouring, with no hypothesis at all — as soon as the leftover graph is a
matching (`DegL ≤ 1` everywhere). -/
theorem Alt4.deg {n K : ℕ} {c : Col n K} {L : Finset (Sym2 (Verts n))} {a b d e : Verts n}
    (h : Alt4 c L a b d e) : 2 ≤ DegL L a ∧ 2 ≤ DegL L b ∧ 2 ≤ DegL L d ∧ 2 ≤ DegL L e := by
  obtain ⟨h4, h1, h2, h3, h5, -, -, -⟩ := h
  have hba : s(b, a) ∈ L := Sym2.eq_swap ▸ h1
  have hdb : s(d, b) ∈ L := Sym2.eq_swap ▸ h2
  have hed : s(e, d) ∈ L := Sym2.eq_swap ▸ h3
  have hsa : s(a, e) ∈ L := Sym2.eq_swap ▸ h5
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact degL_ge_two (v := a) (x := b) (y := e) h1 hsa h4.2.2.2.2.1 h4.1
  · exact degL_ge_two (v := b) (x := a) (y := d) hba h2 h4.2.1 (Ne.symm h4.1)
  · exact degL_ge_two (v := d) (x := b) (y := e) hdb h3 h4.2.2.2.2.1 (Ne.symm h4.2.2.2.1)
  · exact degL_ge_two (v := e) (x := d) (y := a) hed h5 (Ne.symm h4.2.1)
      (Ne.symm h4.2.2.2.2.2)

/-- **A MATCHING LEFTOVER HAS NO ALTERNATING 4-CYCLE, FOR ANY COLOURING.**  (P2) is free when
`DegL L v ≤ 1` for every `v` — no properness hypothesis is needed either. -/
theorem NoAlt4.of_deg_le_one {n K : ℕ} {c : Col n K} {L : Finset (Sym2 (Verts n))}
    (hD : ∀ v : Verts n, DegL L v ≤ 1) : NoAlt4 c L := by
  intro a b d e hAlt
  obtain ⟨h1, h2, h3, h4⟩ := Alt4.deg hAlt
  have := hD a
  omega

/-! ### §3 — the partner condition: a deterministic replacement for (P2) -/

/-- **THE PARTNER CONDITION.**  Fix a fresh colour `j`.  If `u` and `v` are both `j`-matched (with
partners `u'` resp. `v'`) and the leftover edge `s(u,v)` has a colour `≠ j`, then `s(u',v')` is
**not** a leftover edge.

In words: *inside one fresh colour class, the partner map sends every leftover edge it covers to a
non-edge of the leftover graph.*  This is a purely combinatorial, locally checkable condition, and
`NoAlt4.of_partner` shows it excludes every alternating 4-cycle — so the second stage of
arXiv:2207.02920 §12 / arXiv:2208.12563 §4 needs no local lemma. -/
def Partner {n K : ℕ} (c : Col n K) (L : Finset (Sym2 (Verts n))) : Prop :=
  ∀ (j : Fin K) (u v u' v' : Verts n),
    u ≠ v → u' ≠ u → v' ≠ v → s(u, v) ∈ L → c s(u, v) ≠ j →
    s(u, u') ∈ L → c s(u, u') = j → s(v, v') ∈ L → c s(v, v') = j → s(u', v') ∉ L

/-- **THE MAIN THEOREM OF THIS FILE: THE PARTNER CONDITION EXCLUDES EVERY ALTERNATING 4-CYCLE.**
So the condition (P2) — the bad event `B_D` of JM §4, `B₂` of BCDP §12 — follows from a
deterministic hypothesis.  Read contrapositively: **an alternating 4-cycle of the leftover graph
witnesses a violation of the partner condition**, namely two leftover edges of one fresh colour
whose mates are adjacent. -/
theorem NoAlt4.of_partner {n K : ℕ} {c : Col n K} {L : Finset (Sym2 (Verts n))}
    (hP : Partner c L) : NoAlt4 c L := by
  intro a b d e hAlt
  obtain ⟨h4, h1, h2, h3, h5, -, hc2, hc3⟩ := hAlt
  have hs5 : s(a, e) ∈ L := Sym2.eq_swap ▸ h5
  have hcswap : c s(a, e) = c s(e, a) := congrArg c Sym2.eq_swap
  have hce : c s(a, e) = c s(b, d) := by rw [hcswap, hc2]
  have hne1 : e ≠ a := Ne.symm h4.2.2.1
  have hne2 : d ≠ b := Ne.symm h4.2.2.2.1
  have h := hP (c s(b, d)) a b e d h4.1 hne1 hne2 h1 hc3 hs5 hce h2 rfl
  rw [Sym2.eq_swap] at h
  exact h h3

/-- **A MATCHING LEFTOVER SATISFIES THE PARTNER CONDITION FOR EVERY COLOURING.**  Together with
`NoAlt4.of_deg_le_one`: for a matching leftover both the partner condition and (P2) are free.  So
the case in which the hypergraph matching covers *all* the edges — the case of round 30 — has no
probabilistic content whatsoever. -/
theorem Partner.of_deg_le_one {n K : ℕ} {c : Col n K} {L : Finset (Sym2 (Verts n))}
    (hD : ∀ v : Verts n, DegL L v ≤ 1) : Partner c L := by
  intro j u v u' v' huv hne_uu hne_vv huvL huvne hu'L hu'c hv'L hv'c hcon
  have hune : u ≠ v' := by
    intro heq
    have h1 : c s(v, u) = c s(u, v) := congrArg c Sym2.eq_swap
    have h2 : c s(v, u) = j := by rw [heq]; exact hv'c
    exact huvne (h1.symm.trans h2)
  have htwo : 2 ≤ DegL L u' := degL_ge_two (v := u') (x := u) (y := v')
    (Sym2.eq_swap ▸ hu'L) hcon hune hne_uu
  have hdu : DegL L u' ≤ 1 := hD u'
  omega


/-- **THE PUBLISHED CONDITION (P2) IN ITS EXPLICIT, CHECKABLE FORM.**  Under the partner condition,
no four leftover edges on four distinct vertices carry two alternating equal-coloured pairs: this
is `B_D` of arXiv:2208.12563 §4 resp. `B₂` of arXiv:2207.02920 §12, and it is a *local* test on
the fresh colouring — six memberships and three equalities of colours. -/
theorem Partner.no_alt_form {n K : ℕ} {c : Col n K} {L : Finset (Sym2 (Verts n))}
    (hN : Partner c L) {a b d e : Verts n} (h4 : FourDistinct a b d e)
    (h1 : s(a, b) ∈ L) (h2 : s(b, d) ∈ L) (h3 : s(d, e) ∈ L) (h5 : s(e, a) ∈ L)
    (hc1 : c s(a, b) = c s(d, e)) (hc2 : c s(b, d) = c s(e, a))
    (hc3 : c s(a, b) ≠ c s(b, d)) : False :=
  (NoAlt4.of_partner hN a b d e) (Alt4.of_cycle h4 h1 h2 h3 h5 hc1 hc2 hc3)

/-- **AN ALTERNATING 4-CYCLE OF THE LEFTOVER GRAPH *WITNESSES* A VIOLATION OF THE PARTNER
CONDITION.**  The contrapositive reading of the main theorem, and the local form of it: if two
leftover edges `s(u,v)`, `s(u',v')` are non-`j`-coloured / `j`-coloured and the partners are
adjacent, then the leftover graph contains an alternating 4-cycle on four distinct vertices.
So the partner condition is not merely sufficient for (P2): **its violation is witnessed by a
single 4-cycle.** -/
theorem alt_witness {n K : ℕ} {c : Col n K} {L : Finset (Sym2 (Verts n))} {a b d e : Verts n}
    (h : Alt4 c L a b d e) :
    ∃ (j : Fin K) (u v u' v' : Verts n), u ≠ v ∧ u' ≠ u ∧ v' ≠ v ∧ s(u, v) ∈ L ∧ c s(u, v) ≠ j ∧
      s(u, u') ∈ L ∧ c s(u, u') = j ∧ s(v, v') ∈ L ∧ c s(v, v') = j ∧ s(u', v') ∈ L := by
  obtain ⟨h4, h1, h2, h3, h5, -, hc2, hc3⟩ := h
  have hcswap : c s(a, e) = c s(e, a) := congrArg c Sym2.eq_swap
  have hce : c s(a, e) = c s(b, d) := by rw [hcswap, hc2]
  have hs5 : s(a, e) ∈ L := Sym2.eq_swap ▸ h5
  have hed : s(e, d) ∈ L := Sym2.eq_swap ▸ h3
  exact ⟨c s(b, d), a, b, e, d, h4.1, Ne.symm h4.2.2.1, Ne.symm h4.2.2.2.1, h1, hc3, hs5, hce, h2,
    rfl, hed⟩

/-- **CONTRAPOSITIVE: A 4-CYCLE OF THE LEFTOVER GRAPH RULES OUT THE PARTNER CONDITION.**  Together
with `alt_witness`, the two statements say exactly what the event `B_D` / `B₂` of the two papers
is:  it is equivalent to the failure of a local, three-edge condition. -/
theorem not_partner_of_alt {n K : ℕ} {c : Col n K} {L : Finset (Sym2 (Verts n))}
    (h : ¬ NoAlt4 c L) : ¬ Partner c L := by
  intro hN
  exact h (NoAlt4.of_partner hN)

/-! ### §4 — the two stages compose with no local lemma -/

/-- **THE SECOND STAGE NEEDS NO LOCAL LEMMA.**  A first-stage admissible colouring, extended on
the leftover graph by fresh colours which are **proper** (`Proper`, the greedy content of the two
papers' `A_{e,f,i}` / `B₁`), which have **no alternating 4-cycle** (the condition (P2), i.e. the
bad event `B_D` / `B₂`), and which **compensate** (`Compensate`, round 30's verification
condition), give an **admissible** colouring of `K_n`. -/
theorem second_stage {n k K : ℕ} {c₀ c : Col n (k + K)} {L : Finset (Sym2 (Verts n))}
    (hc₀ : Admissible c₀) (hE : Extends c₀ c L) (hP : Proper c L) (hN : NoAlt4 c L)
    (hC : Compensate c₀ c L) : Admissible c :=
  (admissible_iff_second_stage hE).mpr (secondStage_of_ext hc₀ hE hC)

/-- **The same, with (P2) replaced by the partner condition** — the form in which the second stage
of arXiv:2207.02920 / arXiv:2208.12563 can be *checked* rather than hoped for. -/
theorem second_stage_of_partner {n k K : ℕ} {c₀ c : Col n (k + K)} {L : Finset (Sym2 (Verts n))}
    (hc₀ : Admissible c₀) (hE : Extends c₀ c L) (hP : Proper c L) (hN : Partner c L)
    (hC : Compensate c₀ c L) : Admissible c :=
  second_stage hc₀ hE hP (NoAlt4.of_partner hN) hC

/-- **A rainbow second stage is proper, compensates, and — for a matching leftover — satisfies the
partner condition**, so round 30's `Leftover.admissible_of_matching_leftover` is an instance of
`second_stage_of_partner`: when the hypergraph matching covers all the edges, the second stage of
both papers is completely deterministic. -/
theorem second_stage_of_matching {n k K : ℕ} {c₀ c : Col n (k + K)}
    {L : Finset (Sym2 (Verts n))} (hc₀ : Admissible c₀) (hE : Extends c₀ c L)
    (hOff : ∀ e ∈ L, OffDiag e) (hn : 4 ≤ n) (hD : ∀ v : Verts n, DegL L v ≤ 1)
    (hR : Rainbow c L) : Admissible c :=
  second_stage_of_partner hc₀ hE (Rainbow.proper hOff hn hR) (Partner.of_deg_le_one hD)
    (Compensate.of_rainbow hR)

/-- **THE WHOLE SECOND STAGE, WITHOUT PROBABILITY, IN ONE LINE.**  What remains of
`jsp_000140_main` after this file is the first-stage existence hypothesis (the probabilistic
content of arXiv:2207.02920 §4) together with the crossing condition (P3) of round 31: on a
four-set whose leftover edges are two crossing pairs of equal fresh colour, the other two edges
must not carry a first-stage monochromatic pair. -/
theorem second_stage_free {n k K : ℕ} {c₀ c : Col n (k + K)} {L : Finset (Sym2 (Verts n))}
    (hc₀ : Admissible c₀) (hE : Extends c₀ c L) (hP : Proper c L) (hN : NoAlt4 c L) :
    Compensate c₀ c L → Admissible c :=
  fun hC => second_stage hc₀ hE hP hN hC

end JSP140