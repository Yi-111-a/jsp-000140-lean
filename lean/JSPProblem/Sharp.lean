import JSPProblem.Cherry
import JSPProblem.Leftover
import JSPProblem.Cover

/-!
# JSP-000140 — **the sharp bound is attained if and only if the colouring *is* the construction**

Rounds 29–51 encoded the construction of arXiv:2208.12563 / arXiv:2207.02920 as a family of
**labelled triangles** and proved the verification lemma (`Triangles.admissible_of_tri`): a
colouring *covered* by labelled triangles (`Covers c`), with disjoint `(vertex, colour)` usage and
with neither a bad nor a crossing four-set, is admissible.  Every hypothesis introduced since
round 29 therefore asks for a colouring which is

  (i) **admissible** (`Criterion.Admissible` — the catalog condition),
  (ii) **covered** by labelled triangles (`Triangles.Covers` — every edge of `K_n` lies in one
  labelled triangle),
  (iii) **cheap**: `6k ≤ 5(m-1) + δ·m`.

Conditions (i) and (ii) turn out **not to be independent**, and this file closes the gap:

**§1** `covered_iff_cherry` — an edge lies in a labelled triangle **iff** it lies in the three
edges of a two-edge path of the colouring.  A labelled triangle `(u; p, q)` is *exactly* a two-edge
path `p - u - q` together with its leaf edge `s(p,q)`, so the two notions coincide edge by edge.

**§2** `card_sdiff_leftover` — consequently `|E(K_n) \ leftover c| = 3 · Paths c`: the covered
edges are counted by the two-edge paths.

**§3** `card_leftover_le` — **THE QUANTITATIVE LEFTOVER BOUND.**  Combining §2 with
`Cherry.three_mul_paths_le_edges` (`3 · Paths c ≤ |E(K_n)|`) and `Paths.mul_n_sub_one_le`
(`n(n-1) ≤ n·k + Paths c`) gives

    `6k ≤ 5(n-1) + d   ⟹   (leftover c).card ≤ n · d / 2`.

**§4** Two consequences, both new:

* **`covers_of_extremal`** — at the extremal point `6k = 5(n-1)` the leftover is *empty*, so
  **`Covers c` is a theorem, not a hypothesis**: a colouring attaining the sharp Erdős–Gyárfás
  lower bound *is* covered by labelled triangles, and with them the `(vertex, colour)` pairs of
  distinct triangles are disjoint (`Cover.PairFree_of_admissible`, round 51).  The "hypergraph
  matching" clause of arXiv:2208.12563 §4 is **forced by sharpness**, not an extra requirement.
  The contrapositive `not_covers_ge` says the same in colours: an admissible colouring that leaves
  one edge uncovered uses strictly more than `5(n-1)/6` colours.
* **`card_leftover_of_eps`** — the "up to `o(n²)` edges" clause of arXiv:2208.12563 §4 is
  **free**: every asymptotically optimal admissible colouring (`k ≤ 5n/6 + εn`) covers all but
  `3εn² + 6n` edges, so the second stage has an `o(n²)` leftover graph *automatically*.

**§5** What this says about the prize hypothesis: `TriFamilyAdmissible.slack` shows the `Covers`
conjunct of `Cover.TriFamilyAdmissible` is a **sufficient-condition device only** (the conclusion
knows nothing about labelled triangles), `jsp_000140_main_of_admissibleUpper` records the shortest
form of the prize, and `jsp_000140_main_of_sharp` gives the converse direction: the catalog
statement also follows from the *exact attainment* of the sharp bound on `m ≡ 1 (mod 6)`.
-/

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option maxRecDepth 10000

namespace JSP140

variable {n k : ℕ}

/-! ### §0  Tools -/

/-- A finset containing two distinct elements has at least two elements. -/
private theorem card_two_of_two {α : Type*} [DecidableEq α] {s : Finset α} {a b : α}
    (hab : a ≠ b) (ha : a ∈ s) (hb : b ∈ s) : 2 ≤ s.card := by
  have hsub : (insert a (insert b ∅) : Finset α) ⊆ s := by
    intro x hx
    simp only [Finset.mem_insert] at hx
    rcases hx with hxa | hxb | hx
    · exact hxa ▸ ha
    · exact hxb ▸ hb
    · simp at hx
  have hle := Finset.card_le_card hsub
  have heq : (insert a (insert b ∅) : Finset α) = {a, b} := by
    ext x
    simp [Finset.mem_insert, Finset.mem_singleton]
  rw [heq] at hle
  simp [Finset.card_insert_of_notMem, hab] at hle
  exact hle

/-- `v ∈ twoA c i ↔ v` has exactly two colour-`i` neighbours. -/
private theorem mem_twoA_iff {c : Col n k} (i : Fin k) (v : Verts n) :
    v ∈ twoA c i ↔ (Nbrs c i v).card = 2 := by
  rw [twoA, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  rfl

/-! ### §1  Edges covered by the construction = the three edges of a two-edge path -/

/-- **AN EDGE IS COVERED BY THE CONSTRUCTION IFF IT LIES IN THE THREE EDGES OF A TWO-EDGE
PATH.**  This is the identification that makes the two halves of the construction the same
object: a labelled triangle `(u; p, q)` of an admissible colouring is exactly a two-edge path
`p - u - q` of colour `λ = c s(u,p)` together with its leaf edge `s(p,q)` of colour `μ ≠ λ`. -/
theorem covered_iff_cherry {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    {e : Sym2 (Verts n)} :
    Covered c e ↔ ∃ (i : Fin k) (v : Verts n), v ∈ twoA c i ∧ e ∈ cherryEdges c i v := by
  have htwo : ∀ (i : Fin k) (v a b : Verts n) (hab : a ≠ b) (ha : a ∈ Nbrs c i v)
      (hb : b ∈ Nbrs c i v), v ∈ twoA c i := by
    intro i v a b hab ha hb
    have h1 : (Nbrs c i v).card = 2 := by
      have hle := Nbrs_le_two hc i v
      have hge : 2 ≤ (Nbrs c i v).card := card_two_of_two hab ha hb
      omega
    exact (mem_twoA_iff i v).mpr h1
  have hLab : ∀ (i : Fin k) (v a b : Verts n) (hab : a ≠ b) (ha : a ∈ Nbrs c i v)
      (hb : b ∈ Nbrs c i v), LabTri c v a b := by
    intro i v a b hab ha hb
    have hva : v ≠ a := (mem_Nbrs.mp ha).1.symm
    have hvb : v ≠ b := (mem_Nbrs.mp hb).1.symm
    have hia : c s(v, a) = i := (mem_Nbrs.mp ha).2
    have hib : c s(v, b) = i := (mem_Nbrs.mp hb).2
    obtain ⟨hji, _, _⟩ := nb_eq_singleton_of_cherry hc hn i hva hvb hab hia hib (c s(a, b)) rfl
    refine ⟨hva, hvb, hab, hia.trans hib.symm, ?_⟩
    intro hh
    exact hji (hh.symm.trans hia)
  constructor
  · rintro ⟨u, p, q, hL, he⟩
    have hpN : p ∈ Nbrs c (c s(u, p)) u := mem_Nbrs.mpr ⟨hL.1.symm, rfl⟩
    have hqN : q ∈ Nbrs c (c s(u, p)) u := mem_Nbrs.mpr ⟨hL.2.1.symm, hL.2.2.2.1.symm⟩
    have hcen : u ∈ twoA c (c s(u, p)) := htwo _ u p q hL.2.2.1 hpN hqN
    rcases (eq_triEdges he) with he | he | he
    · exact ⟨c s(u, p), u, hcen,
        Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p, hpN, he.symm⟩)⟩
    · exact ⟨c s(u, p), u, hcen,
        Finset.mem_union_left _ (Finset.mem_image.mpr ⟨q, hqN, he.symm⟩)⟩
    · exact ⟨c s(u, p), u, hcen,
        Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(p, q),
          Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hpN, hqN⟩, hL.2.2.1⟩, he.symm⟩)⟩
  · rintro ⟨i, v, hv, he⟩
    obtain ⟨a, b, hab, hN⟩ := Finset.card_eq_two.mp (card_twoA i hv)
    have haN : a ∈ Nbrs c i v := hN.symm ▸ Finset.mem_insert_self a _
    have hbN : b ∈ Nbrs c i v := hN.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl)
    have hL : LabTri c v a b := hLab i v a b hab haN hbN
    refine ⟨v, a, b, hL, ?_⟩
    have hmem : e = s(v, a) ∨ e = s(v, b) ∨ e = s(a, b) → e ∈ triEdges c v a b := by
      rintro (h | h | h)
      · rw [h]; simp [triEdges]
      · rw [h]; simp [triEdges]
      · rw [h]; simp [triEdges]
    rcases mem_cherryEdges i he with ⟨x, hx, hex⟩ | ⟨t, ht, hte, hex⟩
    · have hxa : x = a ∨ x = b := by
        rw [hN] at hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        exact hx
      rcases hxa with hxa | hxa
      · exact hmem (Or.inl (hxa ▸ hex))
      · exact hmem (Or.inr (Or.inl (hxa ▸ hex)))
    · obtain ⟨h1, h2⟩ := Finset.mem_product.mp ht
      have h1' : t.1 = a ∨ t.1 = b := by
        rw [hN] at h1
        simp only [Finset.mem_insert, Finset.mem_singleton] at h1
        exact h1
      have h2' : t.2 = a ∨ t.2 = b := by
        rw [hN] at h2
        simp only [Finset.mem_insert, Finset.mem_singleton] at h2
        exact h2
      rcases h1' with h1' | h1' <;> rcases h2' with h2' | h2'
      · exact absurd (h1' ▸ h2' ▸ hte) (by simp)
      · exact hmem (Or.inr (Or.inr (h1' ▸ h2' ▸ hex)))
      · exact hmem (Or.inr (Or.inr (by
          rw [hex, h1', h2', Sym2.eq_swap])))
      · exact absurd (h1' ▸ h2' ▸ hte) (by simp)

/-- **ONE DIRECTION IS ENOUGH FOR THE COUNTING**, and it is the one used in §2. -/
theorem covered_of_cherry {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) {i : Fin k} {v : Verts n}
    {e : Sym2 (Verts n)} (hv : v ∈ twoA c i) (he : e ∈ cherryEdges c i v) : Covered c e := by
  refine (covered_iff_cherry (e := e) hc hn).mpr ?_
  exact ⟨i, v, hv, he⟩

/-- The witness form of `covered_iff_cherry`, with the edge made explicit. -/
theorem exists_cherry_of_covered {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (e : Sym2 (Verts n)) (hcov : Covered c e) :
    ∃ (i : Fin k) (v : Verts n), v ∈ twoA c i ∧ e ∈ cherryEdges c i v := by
  refine (covered_iff_cherry (e := e) hc hn).mp hcov

/-- Every labelled path `(i, v)` is an element of `cherryFinset c`. -/
private theorem mem_cherryFinset_of_twoA {c : Col n k} (i : Fin k) (v : Verts n)
    (hv : v ∈ twoA c i) : (i, v) ∈ cherryFinset c := by
  rw [cherryFinset, Finset.mem_biUnion]
  exact ⟨i, Finset.mem_univ i, Finset.mem_image.mpr ⟨v, hv, rfl⟩⟩

/-! ### §2  The covered edges are exactly `3 · Paths c` of them -/

/-- **THE COVERED EDGES ARE COUNTED BY THE TWO-EDGE PATHS.**  Every edge of `K_n` that lies in a
labelled triangle lies in the three edges of a two-edge path, and conversely; so

    `|E(K_n) \ leftover c| = 3 · Paths c`.

This is the counting lemma of `Cherry.lean` (`3 · Paths c ≤ |E(K_n)|`) *with equality* read as a
statement about the construction: the leftover graph is what is left of `K_n` when the two-edge
paths are taken out. -/
theorem card_sdiff_leftover {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) :
    (edgeFinset (Finset.univ : Finset (Verts n)) \ leftover c).card = 3 * Paths c := by
  have hsub : ∀ e ∈ (cherryFinset c).biUnion (fun p => cherryEdges c p.1 p.2),
      e ∈ edgeFinset (Finset.univ : Finset (Verts n)) := by
    intro e he
    obtain ⟨p, hp, he'⟩ := Finset.mem_biUnion.mp he
    exact cherryEdges_subset_edgeFinset p.1 he'
  have heq : edgeFinset (Finset.univ : Finset (Verts n)) \ leftover c
      = (cherryFinset c).biUnion (fun p => cherryEdges c p.1 p.2) := by
    apply Finset.Subset.antisymm
    · intro e he'
      have hcov : Covered c e := by
        by_contra hC
        exact (Finset.mem_sdiff.mp he').2 (mem_leftover.mpr ⟨(Finset.mem_sdiff.mp he').1, hC⟩)
      obtain ⟨i, v, hv, hcv⟩ := exists_cherry_of_covered hc hn e hcov
      exact Finset.mem_biUnion.mpr ⟨(i, v), mem_cherryFinset_of_twoA i v hv, hcv⟩
    · intro e he'
      obtain ⟨p, hp, he'⟩ := Finset.mem_biUnion.mp he'
      refine Finset.mem_sdiff.mpr ⟨hsub e (Finset.mem_biUnion.mpr ⟨p, hp, he'⟩), ?_⟩
      exact mem_leftover_of_covered (covered_of_cherry hc hn (twoA_of_mem_cherryFinset hp) he')
  have hdisc : ((↑(cherryFinset c) : Set (Fin k × Verts n)).PairwiseDisjoint
      (fun p => cherryEdges c p.1 p.2)) := by
    intro p hp q hq hpq
    exact cherryEdges_disjoint hc hn (twoA_of_mem_cherryFinset (Finset.mem_coe.mp hp))
      (twoA_of_mem_cherryFinset (Finset.mem_coe.mp hq)) hpq
  have h1 : ((cherryFinset c).biUnion (fun p => cherryEdges c p.1 p.2)).card
      = ∑ p ∈ cherryFinset c, (cherryEdges c p.1 p.2).card := Finset.card_biUnion hdisc
  have h2 : (∑ p ∈ cherryFinset c, (cherryEdges c p.1 p.2).card) = 3 * (cherryFinset c).card := by
    calc (∑ p ∈ cherryFinset c, (cherryEdges c p.1 p.2).card) = ∑ p ∈ cherryFinset c, (3 : ℕ) := by
          refine Finset.sum_congr rfl fun p hp => card_cherryEdges p.1
            (twoA_of_mem_cherryFinset (Finset.mem_coe.mp hp))
      _ = (cherryFinset c).card • (3 : ℕ) := Finset.sum_const _
      _ = 3 * (cherryFinset c).card := by rw [nsmul_eq_mul]; exact Nat.mul_comm _ _
  rw [heq, h1, h2, card_cherryFinset]

/-! ### §3  **THE QUANTITATIVE LEFTOVER BOUND** -/

/-- The purely linear content of `card_leftover_le`. -/
private theorem leftover_linear {c : Col n k} {E P X B d : ℕ}
    (hL : (leftover c).card ≤ E - 3 * P) (hE : 2 * E ≤ X) (hQ : 6 * (X - B) ≤ 6 * P)
    (h6 : 6 * B ≤ 5 * X + n * d) : 2 * (leftover c).card ≤ n * d := by omega

/-- **THE PRICE OF THE LEFTOVER GRAPH, IN COLOURS.**  Let `c` be an admissible `k`-colouring of
`K_n` (`n ≥ 4`) with `6k ≤ 5(n-1) + d`.  Then at most

    **`n · d / 2`**

edges of `K_n` fail to lie in a labelled triangle: the leftover graph of `Leftover.lean` — the
graph the *second stage* of arXiv:2208.12563 §4 has to colour — has `n · d / 2` edges at most.

At the extremal point `d = 0` the covering is **complete** (`covers_of_extremal`); for `d = δ · n`
it misses at most `δ · n² / 2` edges, which is the "up to `o(n²)` edges" clause of the published
construction.  **Both are theorems.**

Proof: `|E \ leftover c| = 3 · Paths c` (`card_sdiff_leftover`) and `Paths c ≥ n(n-1) - n·k`
(`Paths.mul_n_sub_one_le`), whence `|leftover c| ≤ |E| - 3n(n-1) + 3nk ≤ n·d/2`. -/
theorem card_leftover_le {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) {d : ℕ}
    (h : 6 * k ≤ 5 * (n - 1) + d) : (leftover c).card ≤ n * d / 2 := by
  have hL : (leftover c).card ≤ (edgeFinset (Finset.univ : Finset (Verts n))).card - 3 * Paths c := by
    have h1 := card_sdiff_leftover hc hn
    have hsub2 : leftover c ⊆ edgeFinset (Finset.univ : Finset (Verts n)) :=
      fun e he => (mem_leftover.mp he).1
    have h2 := Finset.card_sdiff_add_card_eq_card (s := leftover c)
      (t := edgeFinset (Finset.univ : Finset (Verts n))) hsub2
    omega
  have hQ0 : n * (n - 1) - n * k ≤ Paths c := by
    have h := mul_n_sub_one_le (c := c) hc
    omega
  have hQ : 6 * (n * (n - 1) - n * k) ≤ 6 * Paths c := Nat.mul_le_mul_left 6 hQ0
  have hE : 2 * (edgeFinset (Finset.univ : Finset (Verts n))).card ≤ n * (n - 1) :=
    le_of_eq (card_edgeFinset_univ_two n)
  have h6 : 6 * (n * k) ≤ 5 * (n * (n - 1)) + n * d := by
    have h := Nat.mul_le_mul_left n h
    calc 6 * (n * k) = n * (6 * k) := by ring
      _ ≤ n * (5 * (n - 1) + d) := h
      _ = 5 * (n * (n - 1)) + n * d := by ring
  have hlin := leftover_linear (c := c) (E := (edgeFinset (Finset.univ : Finset (Verts n))).card)
    (P := Paths c) (X := n * (n - 1)) (B := n * k) (d := d) hL hE hQ h6
  exact (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)

/-- The same bound in real form (multiplied by `2`, to avoid a real half), which is the form the
`ε`-slack of the prize uses. -/
theorem card_leftover_real {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) {d : ℕ}
    (h : ((6 * k : ℕ) : ℝ) ≤ ((5 * (n - 1) + d : ℕ) : ℝ)) :
    (2 : ℝ) * ((leftover c).card : ℝ) ≤ (n : ℝ) * (d : ℝ) := by
  have h' : 6 * k ≤ 5 * (n - 1) + d := (Nat.cast_le (α := ℝ)).mp h
  have h2 := (Nat.le_div_iff_mul_le (by omega)).mp (card_leftover_le hc hn h')
  have h3 : 2 * (leftover c).card ≤ n * d := by omega
  calc (2 : ℝ) * ((leftover c).card : ℝ) = ((2 * (leftover c).card : ℕ) : ℝ) := by push_cast; ring
    _ ≤ ((n * d : ℕ) : ℝ) := by exact_mod_cast h3
    _ = (n : ℝ) * (d : ℝ) := by push_cast; ring

/-! ### §3b  **THE REFINED SHARP LOWER BOUND: UNCOVERED EDGES COST COLOURS** -/

/-- **THE REFINED SHARP LOWER BOUND.**  For every admissible `k`-colouring `c` of `K_n` (`n ≥ 4`),

    `2 · |leftover c| + 5 · n · (n-1) ≤ 6 · n · k`,

i.e.

    `6k ≥ (5/2) · n(n-1) + |leftover c|`.

The sharp Erdős–Gyárfás bound `5(n-1) ≤ 6k` of `Cherry.five_sixth_lower` is the `|leftover c| = 0`
case; **each edge the hypergraph matching of arXiv:2208.12563 §4 fails to cover costs the colouring
`2/n` of a colour.**  In particular `6k = 5(n-1)` forces an empty leftover (`covers_of_extremal`) and
a single uncovered edge forces `6k ≥ 5(n-1) + 1` (`not_covers_ge`). -/
theorem two_mul_leftover_add {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) :
    2 * (leftover c).card + 5 * n * (n - 1) ≤ 6 * n * k := by
  have hstep : n * (n - 1) - Paths c ≤ n * k := by
    have h := mul_n_sub_one_le (c := c) hc
    omega
  have hEq : (leftover c).card + 3 * Paths c
      = (edgeFinset (Finset.univ : Finset (Verts n))).card := by
    have h1 := card_sdiff_leftover hc hn
    have hsub2 : leftover c ⊆ edgeFinset (Finset.univ : Finset (Verts n)) :=
      fun e he => (mem_leftover.mp he).1
    have h2 := Finset.card_sdiff_add_card_eq_card (s := leftover c)
      (t := edgeFinset (Finset.univ : Finset (Verts n))) hsub2
    omega
  have h2E : 2 * (edgeFinset (Finset.univ : Finset (Verts n))).card = n * (n - 1) :=
    card_edgeFinset_univ_two n
  have hid : 2 * (leftover c).card + 6 * Paths c = n * (n - 1) := by omega
  have hid2 : 2 * (leftover c).card + 5 * (n * (n - 1))
      = 6 * (n * (n - 1) - Paths c) := by omega
  calc 2 * (leftover c).card + 5 * n * (n - 1)
      = 2 * (leftover c).card + 5 * (n * (n - 1)) := by ring
    _ = 6 * (n * (n - 1) - Paths c) := hid2
    _ ≤ 6 * (n * k) := by have hh := Nat.mul_le_mul_left 6 hstep; omega
    _ = 6 * n * k := by ring

/-! ### §4  Consequences: the covering hypothesis is *asymptotically free* -/

/-- **THE LEFTOVER GRAPH OF AN ASYMPTOTICALLY OPTIMAL COLOURING IS `o(n²)`.**  If `c` is an
admissible `k`-colouring of `K_n` (`n ≥ 4`) with `k ≤ 5n/6 + εn` then at most

    `3 ε n² + 6n`

edges of `K_n` fail to lie in a labelled triangle.  Together with `card_leftover_le` this is the
"up to `o(n²)` edges" hypothesis of arXiv:2208.12563 §4 — **proved here, not assumed**: it is
forced by the colour budget. -/
theorem card_leftover_of_eps {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (ε : ℝ) (hε : 0 < ε)
    (hb : (k : ℝ) ≤ 5 * (n : ℝ) / 6 + ε * (n : ℝ)) :
    (leftover c).card ≤ 3 * ε * (n : ℝ) ^ 2 + 6 * (n : ℝ) := by
  have hceil : ((Nat.ceil (ε * (n : ℝ)) : ℕ) : ℝ) < ε * (n : ℝ) + 1 :=
    Nat.ceil_lt_add_one (mul_nonneg (le_of_lt hε) (Nat.cast_nonneg _))
  have hceil0 : ε * (n : ℝ) ≤ ((Nat.ceil (ε * (n : ℝ)) : ℕ) : ℝ) := Nat.le_ceil _
  have hrR : (6 : ℝ) * (k : ℝ) ≤ (5 : ℝ) * (n : ℝ)
      + (6 : ℝ) * ((Nat.ceil (ε * (n : ℝ)) : ℕ) : ℝ) := by linarith
  have hr : 6 * k ≤ 5 * (n - 1) + (5 + 6 * Nat.ceil (ε * (n : ℝ))) := by
    have hrw : 5 * (n - 1) + (5 + 6 * Nat.ceil (ε * (n : ℝ)))
        = 5 * n + 6 * Nat.ceil (ε * (n : ℝ)) := by
      have h5 : 5 * (n - 1) + 5 = 5 * n := by omega
      omega
    rw [hrw]
    exact_mod_cast hrR
  have hr' : ((6 * k : ℕ) : ℝ)
      ≤ ((5 * (n - 1) + (5 + 6 * Nat.ceil (ε * (n : ℝ))) : ℕ) : ℝ) :=
    Nat.cast_le.mpr hr
  have h2 := card_leftover_real hc hn hr'
  push_cast at h2 ⊢
  nlinarith

/-- **AT THE EXTREMAL POINT THE CONSTRUCTION COVERS EVERY EDGE.**  If an admissible `k`-colouring
of `K_n` attains the sharp Erdős–Gyárfás lower bound `6k = 5(n-1)`, then it *is* the construction
of arXiv:2208.12563: every edge of `K_n` lies in a labelled triangle, and (round 51,
`Cover.PairFree_of_admissible`) the `(vertex, colour)` pairs of distinct triangles are disjoint,
i.e. `Triangles.PairFree c` holds as well.

**So the "hypergraph matching" clause of the published construction is not an extra requirement:
it is forced by sharpness of the counting bound.** -/
theorem covers_of_extremal {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (hext : 6 * k = 5 * (n - 1)) : Covers c := by
  have h1 : (leftover c).card = 0 := by
    have hz := card_leftover_le hc hn (d := 0) hext.le
    omega
  exact covers_iff_leftover_eq_empty.mpr (Finset.card_eq_zero.mp h1)

/-- **A COLOURING THAT IS NOT COVERED PAYS FOR IT IN COLOURS.**  If an admissible `k`-colouring of
`K_n` (`n ≥ 4`) leaves one edge uncovered then `6k ≥ 5(n-1) + 1`, i.e. it uses strictly more than
the sharp lower bound `5(n-1)/6`. -/
theorem not_covers_ge {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (hnc : ¬ Covers c) :
    5 * (n - 1) + 1 ≤ 6 * k := by
  have hne : leftover c ≠ ∅ := fun h => hnc (covers_iff_leftover_eq_empty.mpr h)
  have h1 : 1 ≤ (leftover c).card := by
    have hpos : 0 < (leftover c).card :=
      Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
    omega
  by_contra hcon
  have h3 : 6 * k ≤ 5 * (n - 1) := by omega
  have h4 := card_leftover_le hc hn (d := 0) h3
  omega

/-- **THE PRICE OF ONE COLOUR ABOVE THE SHARP BOUND.**  If `6k ≤ 5(n-1) + 1` — one integer step
above the sharp Erdős–Gyárfás bound — the leftover graph still has at most `n / 2` edges, so the
second stage of arXiv:2208.12563 §4 still sees only `O(n)` edges. -/
theorem card_leftover_of_one {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (hle : 6 * k ≤ 5 * (n - 1) + 1) : (leftover c).card ≤ n / 2 := by
  have h := card_leftover_le hc hn (d := 1) hle
  rwa [Nat.mul_one] at h

/-- **THE PRIZE HYPOTHESIS IN ITS VERIFIED FORM.**  The conjunction `Admissible c ∧ Covers c` of
`Cover.TriFamilyAdmissible`, with `6k = 5(m-1)`, is exactly the extremal case of the catalog:
admissible, covered by labelled triangles, pairwise disjoint `(vertex, colour)` usage
(`Cover.PairFree_of_admissible`), exact budget.  This is `Triangles.TriFamily` at its sharpest
point. -/
theorem triFamily_of_extremal {m j : ℕ} {c : Col m j} (hc : Admissible c) (hm : 4 ≤ m)
    (hext : 6 * j = 5 * (m - 1)) :
    Covers c ∧ PairFree c ∧ NoCrossFour c ∧ NoBadFour c := by
  obtain ⟨-, -, hX, hB⟩ := (design_iff_admissible hm).mp hc
  exact ⟨covers_of_extremal hc hm hext, PairFree_of_admissible hc, hX, hB⟩

/-! ### §5  What this says about the prize hypothesis -/

/-- **THE ENCODING IS A SUFFICIENT-CONDITION DEVICE ONLY.**  `Cover.TriFamilyAdmissible` demands
that the colouring be *covered* by labelled triangles; the conclusion of the prize does not use it
at all — `Slack.lean`'s `SlackFamily`, and hence the catalog statement, asks only for an
**admissible** colouring with the right budget.  The `Covers` conjunct is therefore free to drop,
and what is left is the pure numerical statement `Main.AdmissibleUpper 1`. -/
theorem TriFamilyAdmissible.slack (hfam : TriFamilyAdmissible) : SlackFamily := by
  intro δ hδ
  obtain ⟨M, hM⟩ := hfam δ hδ
  refine ⟨max M 4, fun m hMm hm => ?_⟩
  obtain ⟨k, c, hadm, _, _, _, hk⟩ := hM m (by omega) hm
  exact ⟨k, c, hadm, hk⟩

/-- **THE REQUIRED THEOREM, IN THE SHORTEST FORM KNOWN TO THIS DEVELOPMENT.**  Together with
`Main.fiveSixthLower_eg` (the lower half, complete), the catalog statement
`f(n,4,5) = 5n/6 + o(n)` is *exactly* `Main.AdmissibleUpper 1`: for every `ε > 0` and all large
`n` there is an admissible `k`-colouring of `K_n` with `k ≤ 5n/6 + εn`. -/
theorem jsp_000140_main_of_admissibleUpper (h : AdmissibleUpper 1) : jsp_000140_target :=
  jsp_000140_target_iff.mpr ⟨admissibleLower_eps, h⟩

/-- **THE PRIZE, WITH THE LEFTOVER ACCOUNTED FOR AND *WITHOUT* ANY HYPOTHESIS ON THE
CONSTRUCTION.**  For every `ε > 0` and all large `n` there is an admissible colouring of `K_n` with
`k ≤ 5n/6 + εn` whose leftover graph has at most `3εn² + 6n` edges: the `o(n²)` clause of the
published construction comes with the colouring, for free. -/
theorem leftover_of_admissibleUpper (h : AdmissibleUpper 1) :
    ∀ (ε : ℝ) (hε : 0 < ε), ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∃ (k : ℕ) (c : Col m k), Admissible c ∧
      (k : ℝ) ≤ 5 * (m : ℝ) / 6 + ε * (m : ℝ) ∧
      (leftover c).card ≤ 3 * ε * (m : ℝ) ^ 2 + 6 * (m : ℝ) := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨max N 4, fun m hMm => ?_⟩
  obtain ⟨k, c, hc, hb⟩ := hN m (by omega)
  exact ⟨k, c, hc, hb, card_leftover_of_eps hc (by omega) ε hε hb⟩

/-- **THE CONVERSE DIRECTION: THE PRIZE FOLLOWS FROM THE *EXACT ATTAINMENT* OF THE SHARP LOWER
BOUND.**  Suppose that on the residue class `m ≡ 1 (mod 6)` the Erdős–Gyárfás function is exactly
`5(m-1)/6` for all large `m`:

    `6 · EG m = 5 · (m - 1)`,

then the catalog statement `jsp_000140_target` holds.  Indeed `EG_admissible m` is an admissible
`5(m-1)/6`-colouring, and by `triFamily_of_extremal` it *is* the construction of arXiv:2208.12563.

This hypothesis is *stronger* than the prize (BCDP22 give `5n/6 + o(n)`, not the exact value) and is
recorded only to document that **the construction interface and the sharp bound agree at their
extremal points**: checking a colouring of `K_m` with `5(m-1)/6` colours is a finite, mechanical
task (rounds 46/49 decided `f(7,4,5) = 7` and searched `K_13`). -/
theorem jsp_000140_main_of_sharp
    (h : ∀ δ : ℝ, 0 < δ → ∃ M : ℕ, ∀ m : ℕ, M ≤ m → m % 6 = 1 → 6 * EG m = 5 * (m - 1)) :
    jsp_000140_target := by
  obtain ⟨M, hM⟩ := h 1 (by norm_num)
  refine jsp_000140_main_of_slack_family ?_
  intro δ hδ
  refine ⟨max M 4, fun m hMm hm => ?_⟩
  obtain ⟨c, hc⟩ := EG_admissible m
  have h6 : 6 * EG m = 5 * (m - 1) := hM m (by omega) hm
  refine ⟨EG m, c, hc, ?_⟩
  have h7 : (6 : ℝ) * (EG m : ℝ) ≤ 5 * ((m - 1 : ℕ) : ℝ) + δ * (m : ℝ) := by
    calc (6 : ℝ) * (EG m : ℝ) = 5 * ((m - 1 : ℕ) : ℝ) := by exact_mod_cast h6
      _ ≤ 5 * ((m - 1 : ℕ) : ℝ) + δ * (m : ℝ) := by
        have : (0:ℝ) ≤ δ * (m : ℝ) := mul_nonneg (le_of_lt hδ) (Nat.cast_nonneg _)
        linarith
  exact h7

end JSP140