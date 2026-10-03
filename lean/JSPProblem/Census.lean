import JSPProblem.Surplus
import JSPProblem.Search

/-!
# JSP-000140 — the exact four-set census of an admissible colouring

Rounds 37–44 reduced the prize to the *existence* of a first stage and to the *exact* surplus
identity (`Surplus.surplus_identity`).  Both look at a colouring through its **edges**.  This
file looks at it through its **four-vertex cliques**, and produces an obstruction which is
strictly stronger than the counting bound `5(n-1) ≤ 6k` (`Cherry.five_sixth_lower`).

The four-vertex side of the catalog condition has so far been used only through
`Definitions.classIn_card_le_two` (*no four vertices carry three edges of one colour*).  Read
**globally**, that one lemma has strong consequences which no theorem of this development stated.

## §1 — the 5-or-6 dichotomy

No colour class meets a `K₄` in three edges, and the six edges of a `K₄` are partitioned by the
colour classes.  Hence

* **`card_colorsOn_add_doubledIn`** — the exact form, with `doubledIn c S` the set of **doubled
  colours** (those occurring twice on `S`):  `|colorsOn c S| + |doubledIn c S| = 6`;
* **`card_doubledIn_le_one`** — a `K₄` has **at most one doubled colour**, so the multiplicity
  pattern `(2,2,1,1)` (four colours) is excluded;
* **`card_colorsOn_four_five_or_six`** — **EVERY FOUR-SET OF AN ADMISSIBLE COLOURING SPANS EXACTLY
  FIVE OR SIX COLOURS**, the only admissible patterns being `(2,1,1,1,1)` and
  `(1,1,1,1,1,1)`.

## §2 — the counting tools the census needs

* `edgePairs` / `card_edgePairs` — the number of **ordered pairs of distinct** elements of a finset;
* `two_mul_choose_two` — `2 * choose m 2 = m * (m - 1)`, the arithmetic of pairs that the
  per-colour census will use.

## §2* — the census (PROVED in `Quad.lean` and `Pairs.lean`, round 62 — §2* IS NOW CLOSED)

`Quad.lean` proves `sum_twoFourSets` and the inequality half of the per-colour census;
`Pairs.lean` (round 62) proves the **exact** per-colour census `card_twoFourSets_census`, the global
form `fiveFourSets_census`, `census_obstruction`, and the ordered version `card_adjEdgePairs_eq`
(`|adjEdgePairs c i| = 2 * |twoA c i|`, `sum_card_adjEdgePairs : ∑_i |adjEdgePairs c i| =
2 * Paths c`) — together with `card_pathFourSets_eq`, `card_meetingFourSets`, the bijection
`disjPairs c i ≃ nonMeetingFourSets c i`, and the **second moment**
`sum_sq_le : ∑_i |E_i|² ≤ 2 * |fourSets n| + |E(K_n)|`.  Every bullet of §2* below is now a
theorem; the statements are kept as the specification of what `Pairs.lean` proves.

* **`card_adjPairs`** — **THE NUMBER OF ADJACENT ORDERED PAIRS OF EQUALLY COLOURED EDGES IS TWICE
  THE NUMBER OF TWO-EDGE PATHS**:  `|{(e,f) : e ≠ f ∈ E_i, |e ∪ f| = 3}| = 2 * (twoA c i).card`.
  The ingredient is the bijection "ordered pair of equally coloured edges sharing a vertex ↔
  (centre, ordered pair of its two colour neighbours)".
* **`card_twoFourSets`** — **THE EXACT PER-COLOUR FOUR-SET CENSUS**: the four-element vertex sets
  on which colour `i` occurs exactly twice number

      `(choose |E_i| 2) + (n - 4) * (twoA c i).card`,

  i.e. one for every unordered pair of colour-`i` edges (a pair of *disjoint* colour-`i` edges
  determines its `K₄` uniquely, whereas a pair of *adjacent* ones lies in `n-3` of them).
* **`sum_twoFourSets`** — summing over colours, the `K₄`s with a doubled colour are counted once
  each (`card_doubledIn_le_one`), so `∑_i |twoFourSets c i| = |fiveFourSets c|`;
* **`census_obstruction` — THE CENSUS OBSTRUSION**:

      `∑_i ( choose |E_i| 2 )  +  (n - 4) * Paths c  ≤  |fourSets|`,

  a **new necessary condition on the colour-class profile of an admissible colouring**.  It is not
  a consequence of `Surplus.surplus_identity`, which knows only `∑_i |E_i|`, `Paths c` and
  `Isolated c`: it uses the **pair** census of the colour classes.

## §3 — what the census gives for `f(n,4,5)` (CORRECTED in round 63)

**The three bullets this section used to advertise (`profile_cost_seven`, `profile_cost_eight`,
`no_six_of_seven`, `no_six_of_eight`) were never proved** — the names appear nowhere in the
development.  The exact values `EG 7 = 7` and `EG 8 = 7` are theorems of this repository, but they
rest on **search certificates** (`VertexSearch.certC_eight_six`, `EG_ge_of_certC`) and on the
ghost/sum colourings, not on the census.  Round 63 replaces this section with what is actually
proved.

* **`Moment.pairs_lower`** (`Moment.lean` §1) — the *lower* second moment of the profile,
  `2k ∑_i choose |E_i| 2 + k|E| ≥ |E|²`, from Cauchy–Schwarz; the mirror image of `Pairs.sum_sq_le`;
* **`Moment.moment_obstruction`** (`Moment.lean` §4) — combining the census (upper bound on `Paths`)
  with the exact surplus identity (lower bound on `Paths`) gives a **quadratic** necessary
  condition on `(n,k)` alone, where `Cherry.five_sixth_lower` is linear:

      `6n(n-1)k(n-4) + 3 C(n,2)² ≤ 6nk²(n-4) + 6k C(n,4) + 3k C(n,2)`;

* **`Moment.no_six_of_eight` — `f(8,4,5) ≥ 7`, ANALYTICALLY.**  The classical counting bound gives
  only `⌈35/6⌉ = 6` at `n = 8` (`Moment.classical_misses_eight`), and the census obstruction
  excludes the six-colouring **without any search certificate**.  This is the `no_six_of_eight`
  the old version of this section advertised; it is now a theorem;
* `Moment.no_four_of_four`, `Moment.no_four_of_five`, `Moment.no_five_of_seven` — the same argument
  at `n = 4, 5, 7`, where the counting bound gives `3, 4, 5`;
* **`no_six_of_seven` is NOT a consequence of the census** and remains unproved by any
  census argument: `Moment.momentOK 7 6` holds, so the obstruction is silent at `(7,6)`.  The value
  `EG 7 = 7` therefore still rests on the search certificate;
* `Moment.census_at_least_five_sixth_below_eleven` and `Moment.census_weaker_at_eleven`
  (`native_decide`, all `n < 21`, `k < 20`) state exactly where the census is stronger than the
  counting bound (`n ≤ 8`), where it agrees (`n = 9, 10`) and where it is **weaker** (`n ≥ 11`) —
  the census left-hand side is `Θ(n³)` at `k = Θ(n)` against a right-hand side of `Θ(n⁴)`.

So the census **is** the first improvement over the catalog counting bound `f(n,4,5) ≥ 5(n-1)/6`,
but only at the `O(1)` level and only at `n ∈ {4, 5, 7, 8}`.
-/

set_option maxHeartbeats 1000000

namespace JSP140

variable {n k : ℕ}

/-! ### §0  Four-vertex cliques and doubled colours -/

/-- **THE `K₄`s OF `K_n`.**  `Search.fourSets n` is the finset of four-element subsets of `V`; this
is the same object, and `mem_fourSets` records its membership criterion. -/
theorem mem_fourSets {n : ℕ} {S : Finset (Verts n)} :
    S ∈ fourSets n ↔ S.card = 4 := by simp [fourSets]

/-- The **doubled colours** on a vertex set `S`: the colours occurring on exactly two of the
edges of the complete graph on `S`. -/
def doubledIn {n k : ℕ} (c : Col n k) (S : Finset (Verts n)) : Finset (Fin k) :=
  (Finset.univ : Finset (Fin k)).filter fun i => (classIn c i S).card = 2

theorem mem_doubledIn {c : Col n k} {i : Fin k} {S : Finset (Verts n)} :
    i ∈ doubledIn c S ↔ (classIn c i S).card = 2 := by simp [doubledIn]

/-- The colours occurring on **exactly one** edge of the complete graph on `S`. -/
def singleIn {n k : ℕ} (c : Col n k) (S : Finset (Verts n)) : Finset (Fin k) :=
  (Finset.univ : Finset (Fin k)).filter fun i => (classIn c i S).card = 1

theorem mem_singleIn {c : Col n k} {i : Fin k} {S : Finset (Verts n)} :
    i ∈ singleIn c S ↔ (classIn c i S).card = 1 := by simp [singleIn]

/-- The four-element vertex sets on which colour `i` occurs exactly twice. -/
def twoFourSets {n k : ℕ} (c : Col n k) (i : Fin k) : Finset (Finset (Verts n)) :=
  (fourSets n).filter fun S => (classIn c i S).card = 2

theorem mem_twoFourSets {c : Col n k} {i : Fin k} {S : Finset (Verts n)} :
    S ∈ twoFourSets c i ↔ S.card = 4 ∧ (classIn c i S).card = 2 := by
  rw [twoFourSets, Finset.mem_filter, mem_fourSets]

/-- The four-element vertex sets spanning **exactly five** colours. -/
def fiveFourSets {n k : ℕ} (c : Col n k) : Finset (Finset (Verts n)) :=
  (fourSets n).filter fun S => (colorsOn c S).card = 5

theorem mem_fiveFourSets {c : Col n k} {S : Finset (Verts n)} :
    S ∈ fiveFourSets c ↔ S.card = 4 ∧ (colorsOn c S).card = 5 := by
  rw [fiveFourSets, Finset.mem_filter, mem_fourSets]

/-- A nonempty finset has a member. -/
theorem exists_mem_of_card_pos {α : Type*} {s : Finset α} (h : 0 < s.card) : ∃ x, x ∈ s := by
  rw [Finset.card_pos] at h
  exact h

/-! ### §1  The 5-or-6 dichotomy -/

/-- A colour occurring on `S` in an admissible colouring (`S` of size four) occurs on **one or two**
edges, never zero and never three. -/
theorem classIn_card_mem_colorsOn {c : Col n k} (hc : Admissible c) {S : Finset (Verts n)}
    (hS : S.card = 4) {i : Fin k} (hi : i ∈ colorsOn c S) :
    0 < (classIn c i S).card ∧ (classIn c i S).card ≤ 2 := by
  constructor
  · obtain ⟨e, he, hce⟩ := Finset.mem_image.mp hi
    rw [Finset.card_pos]
    exact ⟨e, mem_classIn.mpr ⟨he, hce⟩⟩
  · exact classIn_card_le_two hc i S hS

/-- A colour occurring at all on `S` occurs on `S`. -/
theorem mem_colorsOn_of_card_pos {c : Col n k} {S : Finset (Verts n)} {i : Fin k}
    (h : 0 < (classIn c i S).card) : i ∈ colorsOn c S := by
  obtain ⟨e, he⟩ := exists_mem_of_card_pos h
  rw [colorsOn, Finset.mem_image]
  exact ⟨e, (mem_classIn.mp he).1, (mem_classIn.mp he).2⟩

/-- A constant summed over a finset of colours. -/
theorem sum_const_card_nat (s : Finset (Fin k)) (b : ℕ) : ∑ _i ∈ s, b = s.card * b := by
  simp [Finset.sum_const, Nat.mul_comm]

/-- The edges of the complete graph on `S`, split by colour: the class sizes sum to `|E(S)|`. -/
theorem sum_card_classIn_colors (c : Col n k) (S : Finset (Verts n)) :
    (edgeFinset S).card = ∑ i ∈ colorsOn c S, (classIn c i S).card := by
  rw [Finset.card_eq_sum_card_fiberwise (s := edgeFinset S) (t := colorsOn c S) (f := c)]
  · refine Finset.sum_congr rfl fun i _ => ?_
    show ({e ∈ edgeFinset S | c e = i} : Finset (Sym2 (Verts n))).card = (classIn c i S).card
    rfl
  · intro e he
    show c e ∈ (edgeFinset S).image c
    exact Finset.mem_image.mpr ⟨e, he, rfl⟩

/-- **THE 5-OR-6 DICHOTOMY, exact form.**  For every admissible colouring and every four-element
vertex set `S`,

    `|colorsOn c S| + |doubledIn c S| = 6`.

Indeed no colour class meets a `K₄` in three edges, so the six edges of a `K₄` carry multiplicities
which are all `1` or `2`, and the number of distinct colours is the number of multiplicity-`2`
classes short of six. -/
theorem card_colorsOn_add_doubledIn {c : Col n k} (hc : Admissible c) {S : Finset (Verts n)}
    (hS : S.card = 4) : (colorsOn c S).card + (doubledIn c S).card = 6 := by
  have h6 : (edgeFinset S).card = 6 := card_edgeFinset_four hS
  have hmem (i : Fin k) (hi : i ∈ colorsOn c S) : i ∈ doubledIn c S ∪ singleIn c S := by
    rcases classIn_card_mem_colorsOn hc hS hi with ⟨h1, h2⟩
    by_cases hd : (classIn c i S).card = 2
    · exact Finset.mem_union_left _ (by rw [mem_doubledIn]; exact hd)
    · refine Finset.mem_union_right _ ?_
      rw [mem_singleIn]; omega
  have hunion : colorsOn c S = doubledIn c S ∪ singleIn c S :=
    Finset.Subset.antisymm (fun i hi => hmem i hi) (fun i hi => by
      simp only [Finset.mem_union] at hi
      rcases hi with hi | hi
      · exact mem_colorsOn_of_card_pos (by rw [mem_doubledIn.mp hi]; omega)
      · exact mem_colorsOn_of_card_pos (by rw [mem_singleIn.mp hi]; omega))
  have hdisj : Disjoint (doubledIn c S) (singleIn c S) := by
    refine Finset.disjoint_left.mpr fun i h1 h2 => ?_
    have h2' := mem_doubledIn.mp h1
    have h3 := mem_singleIn.mp h2
    omega
  have hcard : 6 = 2 * (doubledIn c S).card + (singleIn c S).card := by
    calc 6 = (edgeFinset S).card := h6.symm
      _ = ∑ i ∈ colorsOn c S, (classIn c i S).card := sum_card_classIn_colors c S
      _ = ∑ i ∈ (doubledIn c S ∪ singleIn c S), (classIn c i S).card := by rw [hunion]
      _ = (∑ i ∈ doubledIn c S, (classIn c i S).card)
          + ∑ i ∈ singleIn c S, (classIn c i S).card := Finset.sum_union hdisj
      _ = (∑ _i ∈ doubledIn c S, (2 : ℕ)) + ∑ _i ∈ singleIn c S, (1 : ℕ) := by
        have h1 : (∑ i ∈ doubledIn c S, (classIn c i S).card) = ∑ _i ∈ doubledIn c S, (2 : ℕ) :=
          Finset.sum_congr rfl fun i hi => by rw [mem_doubledIn.mp hi]
        have h2 : (∑ i ∈ singleIn c S, (classIn c i S).card) = ∑ _i ∈ singleIn c S, (1 : ℕ) :=
          Finset.sum_congr rfl fun i hi => by rw [mem_singleIn.mp hi]
        rw [h1, h2]
      _ = 2 * (doubledIn c S).card + (singleIn c S).card := by
        rw [sum_const_card_nat, sum_const_card_nat]
        simp [Nat.mul_comm]
  have hcard2 : (colorsOn c S).card = (doubledIn c S).card + (singleIn c S).card := by
    rw [hunion, Finset.card_union_of_disjoint hdisj]
  omega

/-- A `K₄` has **at most one doubled colour**. -/
theorem card_doubledIn_le_one {c : Col n k} (hc : Admissible c) {S : Finset (Verts n)}
    (hS : S.card = 4) : (doubledIn c S).card ≤ 1 := by
  have h := card_colorsOn_add_doubledIn hc hS
  have h5 := hc S hS
  omega

/-- **EVERY FOUR-SET OF AN ADMISSIBLE COLOURING SPANS EXACTLY FIVE OR SIX COLOURS.** -/
theorem card_colorsOn_four_five_or_six {c : Col n k} (hc : Admissible c) {S : Finset (Verts n)}
    (hS : S.card = 4) : (colorsOn c S).card = 5 ∨ (colorsOn c S).card = 6 := by
  have h := card_colorsOn_add_doubledIn hc hS
  have h1 := card_doubledIn_le_one hc hS
  have h5 := hc S hS
  omega

/-- A `K₄` is rainbow (six colours) exactly when it has no doubled colour. -/
theorem card_colorsOn_four_eq_six_iff {c : Col n k} (hc : Admissible c) {S : Finset (Verts n)}
    (hS : S.card = 4) : (colorsOn c S).card = 6 ↔ doubledIn c S = ∅ := by
  have h := card_colorsOn_add_doubledIn hc hS
  constructor
  · intro h6
    have hD : (doubledIn c S).card = 0 := by omega
    exact Finset.card_eq_zero.mp hD
  · intro h0
    have h5 := hc S hS
    have hD : (doubledIn c S).card = 0 := Finset.card_eq_zero.mpr h0
    omega

/-- A `K₄` spans five colours exactly when it has exactly one doubled colour. -/
theorem card_colorsOn_four_eq_five_iff {c : Col n k} (hc : Admissible c) {S : Finset (Verts n)}
    (hS : S.card = 4) : (colorsOn c S).card = 5 ↔ (doubledIn c S).card = 1 := by
  have h := card_colorsOn_add_doubledIn hc hS
  constructor
  · intro h5
    have h5' := hc S hS
    omega
  · intro h1
    have h5' := hc S hS
    omega

/-! ### §2  Ordered pairs of equally coloured edges -/

/-- The ordered pairs of **distinct** elements of `A`. -/
def edgePairs {α : Type*} [DecidableEq α] (A : Finset (Sym2 α)) :
    Finset (Sym2 α × Sym2 α) := (A ×ˢ A).filter fun q => q.1 ≠ q.2

theorem mem_edgePairs {α : Type*} [DecidableEq α] {A : Finset (Sym2 α)} {e f : Sym2 α} :
    (e, f) ∈ edgePairs A ↔ e ∈ A ∧ f ∈ A ∧ e ≠ f := by
  simp [edgePairs, and_assoc]

theorem card_edgePairs {α : Type*} [DecidableEq α] (A : Finset (Sym2 α)) :
    (edgePairs A).card = A.card * (A.card - 1) := by
  have hsub : ((A ×ˢ A).filter (fun q : Sym2 α × Sym2 α => q.1 = q.2)) ⊆ A ×ˢ A :=
    Finset.filter_subset _ _
  have hcard : ((A ×ˢ A).filter (fun q : Sym2 α × Sym2 α => q.1 = q.2)).card = A.card :=
    Finset.card_bij (fun q _ => q.1)
      (fun q hq => (Finset.mem_product.mp (Finset.mem_filter.mp hq).1).1)
      (fun q₁ hq₁ q₂ hq₂ heq => by
        obtain ⟨h1a, h1b⟩ := Finset.mem_filter.mp hq₁
        obtain ⟨h2a, h2b⟩ := Finset.mem_filter.mp hq₂
        refine Prod.ext heq ?_
        rw [← h1b, ← h2b]; exact heq)
      (fun a ha => ⟨(a, a),
        (show (a, a) ∈ (A ×ˢ A).filter (fun q : Sym2 α × Sym2 α => q.1 = q.2) from
          Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, ha⟩, rfl⟩), rfl⟩)
  have hdiff : edgePairs A
      = (A ×ˢ A) \ ((A ×ˢ A).filter (fun q : Sym2 α × Sym2 α => q.1 = q.2)) := by
    ext q
    constructor
    · intro hq
      obtain ⟨hq1, hq2⟩ := Finset.mem_filter.mp hq
      refine Finset.mem_sdiff.mpr ⟨hq1, fun hc => hq2 (Finset.mem_filter.mp hc).2⟩
    · intro hq
      obtain ⟨hq1, hq2⟩ := Finset.mem_sdiff.mp hq
      exact Finset.mem_filter.mpr ⟨hq1, fun he => hq2 (Finset.mem_filter.mpr ⟨hq1, he⟩)⟩
  rw [hdiff, Finset.card_sdiff_of_subset hsub, Finset.card_product, hcard]
  have hk : A.card * (A.card - 1) = A.card * A.card - A.card := Nat.mul_sub_one _ _
  omega

/-- `2 * choose m 2 = m * (m - 1)`, the elementary arithmetic of pairs. -/
theorem two_mul_choose_two : ∀ m : ℕ, 2 * m.choose 2 = m * (m - 1) := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : (m + 1).choose 2 = m + m.choose 2 := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
    calc 2 * (m + 1).choose 2 = 2 * (m + m.choose 2) := by rw [h1]
      _ = 2 * m + 2 * m.choose 2 := by ring
      _ = 2 * m + (m * m - m) := by rw [ih, Nat.mul_sub_one]
      _ = m * m + m := by
        have hmm : m ≤ m * m := by
          induction m with
          | zero => simp
          | succ m ih => rw [Nat.succ_mul]; omega
        have hz : 2 * m - m = m := by omega
        omega
      _ = (m + 1) * m := by rw [Nat.add_mul, Nat.one_mul]
      _ = (m + 1) * ((m + 1) - 1) := by rw [show (m + 1) - 1 = m by omega]

end JSP140
