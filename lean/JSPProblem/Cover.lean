import JSPProblem.Triangles

/-!
# JSP-000140 — the two `(vertex, colour)` roles of a labelled triangle: a **partial** solution of
# the matching-condition blocker

Rounds 29–32 encoded the construction of arXiv:2207.02920 / arXiv:2208.12563 as a family of
**labelled triangles** (`Triangles.lean`): a labelled triangle of the colouring `c` is an ordered
triple `(u, p, q)` whose two edges `s(u,p), s(u,q)` meet at the *labelled vertex* `u`, carry the
same colour, and whose *opposite edge* `s(p,q)` carries a different one.  A covering of `K_n` by
such triangles, in which **no two triangles with different vertex sets use a common
`(vertex, colour)` pair** (`PairFree`), is an admissible colouring — and conversely an admissible
colouring covered by triangles gives a `TriFamily`, the single hypothesis
`jsp_000140_main_of_tri_family` needs.

`PairFree` was carried as an open blocker ("not proved").  **This file attacks it from the only
possible direction: showing that `PairFree` is a *consequence* of admissibility.**  The point is
that a `(vertex, colour)` pair of a labelled triangle carries very little information about the
vertex it belongs to, and all of it can be recovered from the colouring:

Write `λ = c s(u,p) = c s(u,q)` and `μ = c s(p,q) ≠ λ`.  The five `(vertex, colour)` pairs of the
triangle `(u,p,q)` are

  `(u, λ)` — the *labelled* pair (both `λ`-edges meet at `u`);
  `(p, λ), (q, λ)` — the two *path* leaves;
  `(p, μ), (q, μ)` — the two *opposite* leaves.

So a pair `(v, j)` of the triangle says one of only two things about `v`:

* **labelled**: `v = u`, `j = λ`.  Then `v` has exactly **two** `j`-neighbours, the two leaves;
* **leaf**: `v ∈ {p,q}`, `j ∈ {λ, μ}`.  Then `v` has exactly **one** `j`-neighbour.

**This file proves both halves of the second line, which is where all the content is:**

* **`centre_sem`** — the labelled role: `(Nbrs c j u).card = 2`, and `p`, `q` are its two elements;
* **`pathLeaf_sem` — THE PATH-LEAF ROLE.**  If `a - u - b` is a two-edge path of colour `j` then
  the *only* `j`-edge at `a` is `s(a,u)`.  (The `K₄` `{a,u,b,w}` would otherwise carry three
  `j`-edges: `s(a,u)`, `s(a,w)`, `s(u,b)`.)
* **`oppLeaf_sem` — THE OPPOSITE-LEAF ROLE.**  If `s(a,b)` is the opposite edge of a labelled
  triangle, of colour `j`, then the *only* `j`-edge at `a` is `s(a,b)`.  (The `K₄` `{a,u,b,w}`
  would span at most three colours: `j` on `s(a,b), s(a,w)`, `λ` on `s(a,u), s(u,b)`, and the
  colour of `s(u,w)`.)

Three `K₄` configurations are recorded as separate lemmas, each reducing "at most four colours on a
`K₄`" to the four colours explicitly:

* `not_admissible_path_pair` — a two-edge path `y - x - z` of colour `i` and a two-edge path
  `y - w - x` of colour `j`;
* `not_admissible_path_pair2` — two two-edge paths of colours `i` and `j` whose centres are
  adjacent (`y - x - z` of colour `i`, `y - w - x` of colour `j`);
* `not_admissible_path_pair3` — two two-edge paths of colours `i` and `j` on the same leaf pair
  (`y - x - z` of colour `i`, `y - w - z` of colour `j`).

and the two **obstructions** they feed:

* **`obstruction_one`** — a vertex cannot be the *path* leaf of one labelled triangle and the
  *opposite* leaf of another with the same `(vertex, colour)` pair;
* **`obstruction_two`** — a `(vertex, colour)` pair cannot be the *opposite*-leaf pair of two
  labelled triangles with different labelled vertices.

See §2 at the end of the file for the exact remaining case analysis (three lines of bookkeeping
around these six theorems) needed to conclude `PairFree_of_admissible`.
-/

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option maxRecDepth 10000

namespace JSP140

variable {n k : ℕ}

/-! ### §0  Tools -/

/-- `c s(y, x) = c s(x, y)`. -/
private theorem c_swap' {n k : ℕ} {c : Col n k} {x y : Verts n} : c s(y, x) = c s(x, y) := by
  rw [Sym2.eq_swap]

/-- A finset containing two distinct elements has at least two elements. -/
private theorem card_ge_two {α : Type*} [DecidableEq α] {s : Finset α} {a b : α} (hab : a ≠ b)
    (ha : a ∈ s) (hb : b ∈ s) : 2 ≤ s.card := by
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

/-- A four-fold insert has at most four elements. -/
private theorem card_insert4_le {α : Type*} [DecidableEq α] (a b c d : α) :
    ((insert a (insert b (insert c (insert d ∅))) : Finset α)).card ≤ 4 := by
  have h0 : ((insert d ∅ : Finset α)).card ≤ 1 := Finset.card_insert_le _ _
  have h1 : ((insert c (insert d ∅) : Finset α)).card ≤ ((insert d ∅ : Finset α)).card + 1 :=
    Finset.card_insert_le _ _
  have h2 : ((insert b (insert c (insert d ∅)) : Finset α)).card ≤
      ((insert c (insert d ∅) : Finset α)).card + 1 := Finset.card_insert_le _ _
  have h3 : ((insert a (insert b (insert c (insert d ∅))) : Finset α)).card ≤
      ((insert b (insert c (insert d ∅)) : Finset α)).card + 1 := Finset.card_insert_le _ _
  omega

/-- Membership is monotone under `insert`. -/
private theorem mem_in_insert {α : Type*} [DecidableEq α] {a b : α} {s : Finset α} (h : a ∈ s) :
    a ∈ insert b s := Finset.mem_insert_of_mem h

/-- `x` belongs to `insert a (insert b (insert c (insert d (insert e (insert f ∅)))))` when it is
one of `a, …, f`. -/
private theorem mem_insert6 {α : Type*} [DecidableEq α] {a b c d e f : α} {x : α}
    (h : x = a ∨ x = b ∨ x = c ∨ x = d ∨ x = e ∨ x = f) :
    x ∈ insert a (insert b (insert c (insert d (insert e (insert f (∅ : Finset α)))))) := by
  simp only [Finset.mem_insert]
  rcases h with h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))

/-- `a` belongs to `insert a (insert b ∅)`. -/
private theorem mem_insert_top {α : Type*} [DecidableEq α] (a b : α) :
    a ∈ (insert a (insert b (∅ : Finset α))) := Finset.mem_insert_self a (insert b ∅)

/-- A vertex of an admissible colouring has at most two neighbours in a colour class. -/
private theorem nbrs_card_le_two {c : Col n k} (hc : Admissible c) (j : Fin k) (v : Verts n) :
    (Nbrs c j v).card ≤ 2 :=
  card_Nbrs j v ▸ nb_card_le_two hc j v Finset.univ

/-- Two elements of a finset of cardinality `1` are equal. -/
private theorem eq_of_card_one {α : Type*} [DecidableEq α] {s : Finset α} {a b : α}
    (hs : s.card = 1) (ha : a ∈ s) (hb : b ∈ s) : a = b := by
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hs
  rw [hx] at ha hb
  simp only [Finset.mem_singleton] at ha hb
  exact ha.trans hb.symm

/-- A finset of cardinality at most two, containing `a ≠ b`, is contained in `{a, b}`. -/
private theorem sub_insert2_of_card_le_two {α : Type*} [DecidableEq α] {s : Finset α} {a b : α}
    (hab : a ≠ b) (ha : a ∈ s) (hb : b ∈ s) (hcard : s.card ≤ 2) :
    s ⊆ insert a (insert b ∅) := by
  intro x hx
  rw [Finset.mem_insert]
  by_cases hxa : x = a
  · exact Or.inl hxa
  by_cases hxb : x = b
  · rw [Finset.mem_insert]; exact Or.inr (Or.inl hxb)
  exfalso
  have hge := card_ge_three (e₁ := a) (e₂ := b) (e₃ := x) hab (fun hh => hxa hh.symm)
    (fun hh => hxb hh.symm) ⟨ha, hb, hx⟩
  omega

/-- **THREE EDGES OF ONE COLOUR INSIDE A `K₄` ARE IMPOSSIBLE.** -/
private theorem not_admissible_of_three {c : Col n k} {i : Fin k} {a b d e : Verts n}
    (h4 : FourDistinct a b d e) (e₁ e₂ e₃ : Sym2 (Verts n))
    (hm : e₁ ∈ edgeFinset (fourSet a b d e) ∧ e₂ ∈ edgeFinset (fourSet a b d e) ∧
      e₃ ∈ edgeFinset (fourSet a b d e))
    (h1 : c e₁ = i) (h2 : c e₂ = i) (h3 : c e₃ = i)
    (hd : e₁ ≠ e₂ ∧ e₁ ≠ e₃ ∧ e₂ ≠ e₃) : ¬ Admissible c := by
  intro hc
  have hle := classIn_card_le_two hc i (fourSet a b d e) (card_fourSet h4)
  have hge := card_ge_three hd.1 hd.2.1 hd.2.2
    ⟨mem_classIn.mpr ⟨hm.1, h1⟩, mem_classIn.mpr ⟨hm.2.1, h2⟩, mem_classIn.mpr ⟨hm.2.2, h3⟩⟩
  omega

/-- The six edges of a `K₄` have their colours in the given finset. -/
private theorem colorsOn_sub_six {c : Col n k} {a b d e : Verts n} (h4 : FourDistinct a b d e)
    {S : Finset (Fin k)}
    (h1 : c s(a, b) ∈ S) (h2 : c s(a, d) ∈ S) (h3 : c s(a, e) ∈ S)
    (h4' : c s(b, d) ∈ S) (h5 : c s(b, e) ∈ S) (h6 : c s(d, e) ∈ S) :
    colorsOn c (fourSet a b d e) ⊆ S := by
  intro z hz
  rw [colorsOn, Finset.mem_image] at hz
  obtain ⟨e', heS, he⟩ := hz
  rw [← he]
  obtain ⟨x, y, hxy, hne⟩ : ∃ x y : Verts n, e' = s(x, y) ∧ x ≠ y := by
    obtain ⟨p, q, hpq⟩ : ∃ p q : Verts n, e' = s(p, q) :=
      Quot.inductionOn e' (fun t : Verts n × Verts n => ⟨t.1, t.2, rfl⟩)
    obtain ⟨h1', h2'⟩ := mem_edgeFinset.mp (hpq ▸ heS)
    exact ⟨p, q, hpq, h2' p q rfl⟩
  have hmem : ∀ z ∈ e', z ∈ fourSet a b d e := by
    obtain ⟨h1', _⟩ := mem_edgeFinset.mp heS
    intro z hz
    exact (Finset.mem_sym2_iff.mp h1') z hz
  rw [hxy]
  have hxS : x ∈ fourSet a b d e := hmem x (by rw [hxy]; exact Sym2.mem_mk_left x y)
  have hyS : y ∈ fourSet a b d e := hmem y (by rw [hxy]; exact Sym2.mem_mk_right x y)
  rw [mem_fourSet h4] at hxS hyS
  rcases hxS with hxa | hxb | hxd | hxe
  · rcases hyS with hya | hyb | hyd | hye
    · rw [hxa, hya]; exact (hne (hxa.trans hya.symm)).elim
    · rw [hxa, hyb]; exact h1
    · rw [hxa, hyd]; exact h2
    · rw [hxa, hye]; exact h3
  · rcases hyS with hya | hyb | hyd | hye
    · rw [hxb, hya, Sym2.eq_swap]; exact h1
    · rw [hxb, hyb]; exact (hne (hxb.trans hyb.symm)).elim
    · rw [hxb, hyd]; exact h4'
    · rw [hxb, hye]; exact h5
  · rcases hyS with hya | hyb | hyd | hye
    · rw [hxd, hya, Sym2.eq_swap]; exact h2
    · rw [hxd, hyb, Sym2.eq_swap]; exact h4'
    · rw [hxd, hyd]; exact (hne (hxd.trans hyd.symm)).elim
    · rw [hxd, hye]; exact h6
  · rcases hyS with hya | hyb | hyd | hye
    · rw [hxe, hya, Sym2.eq_swap]; exact h3
    · rw [hxe, hyb, Sym2.eq_swap]; exact h5
    · rw [hxe, hyd, Sym2.eq_swap]; exact h6
    · rw [hxe, hye]; exact (hne (hxe.trans hye.symm)).elim

/-- **A `K₄` WITH A TWO-EDGE PATH OF ONE COLOUR AND, AT ONE OF ITS LEAVES, A TWO-EDGE PATH OF
ANOTHER, SPANS AT MOST FOUR COLOURS.**  The six edges of `{x,y,z,w}` are `s(x,y), s(x,z)` of colour
`i`, `s(y,z), s(y,w)` of colour `j`, and `s(x,w), s(z,w)` of arbitrary colours: at most four
colours, so the four-set is not admissible. -/
private theorem not_admissible_path_pair {c : Col n k} (hc : Admissible c)
    {x y z w : Verts n} {i j : Fin k} (h4 : FourDistinct x y z w)
    (h1 : c s(x, y) = i) (h2 : c s(x, z) = i) (h3 : c s(y, z) = j) (h4' : c s(y, w) = j) : False := by
  have hsub := colorsOn_sub_six (c := c) h4
    (S := (insert i (insert j (insert (c s(x, w)) (insert (c s(z, w)) (∅ : Finset (Fin k))))) :
      Finset (Fin k)))
    (by rw [h1]; exact Finset.mem_insert_self _ _)
    (by rw [h2]; exact Finset.mem_insert_self _ _)
    (by exact mem_in_insert (mem_in_insert (Finset.mem_insert_self _ _)))
    (by rw [h3]; exact mem_in_insert (Finset.mem_insert_self _ _))
    (by rw [h4']; exact mem_in_insert (Finset.mem_insert_self _ _))
    (by exact mem_in_insert (mem_in_insert (mem_in_insert (Finset.mem_insert_self _ _))))
  have h5 := hc (fourSet x y z w) (card_fourSet h4)
  have hle := Finset.card_le_card hsub
  have hcard := card_insert4_le i j (c s(x, w)) (c s(z, w))
  omega

/-- **A `K₄` WITH TWO TWO-EDGE PATHS OF DIFFERENT COLOURS, ONE OF WHICH HAS THE OTHER'S
CENTRE AS A LEAF.**  If `y - x - z` is a two-edge path of colour `i` and `y - w - x` one of colour
`j`, then `{x,y,z,w}` spans at most three colours: the six edges are `s(x,y), s(x,z)` of colour
`i`, `s(w,x), s(w,y)` (and `s(x,w) = s(w,x)`) of colour `j`, and `s(y,z)`. -/
private theorem not_admissible_path_pair2 {c : Col n k} (hc : Admissible c)
    {x y z w : Verts n} {i j : Fin k} (h4 : FourDistinct x y z w)
    (h1 : c s(x, y) = i) (h2 : c s(x, z) = i) (h3 : c s(w, x) = j) (h4' : c s(w, y) = j) :
    False := by
  have hxs : c s(x, w) = j := (c_swap' (x := w) (y := x)).trans h3
  have hys : c s(y, w) = j := (c_swap' (x := w) (y := y)).trans h4'
  have hsub := colorsOn_sub_six (c := c) h4
    (S := (insert i (insert j (insert (c s(y, z)) (insert (c s(z, w)) (∅ : Finset (Fin k))))) :
      Finset (Fin k)))
    (by rw [h1]; exact Finset.mem_insert_self _ _)
    (by rw [h2]; exact Finset.mem_insert_self _ _)
    (by rw [hxs]; exact mem_in_insert (Finset.mem_insert_self _ _))
    (by exact mem_in_insert (mem_in_insert (Finset.mem_insert_self _ _)))
    (by rw [hys]; exact mem_in_insert (Finset.mem_insert_self _ _))
    (by exact mem_in_insert (mem_in_insert (mem_in_insert (Finset.mem_insert_self _ _))))
  have h5 := hc (fourSet x y z w) (card_fourSet h4)
  have hle := Finset.card_le_card hsub
  have hcard := card_insert4_le i j (c s(y, z)) (c s(z, w))
  omega

/-- **A `K₄` WITH TWO TWO-EDGE PATHS OF DIFFERENT COLOURS ON THE SAME LEAF PAIR.**  If
`y - x - z` and `y - w - z` are two-edge paths of colours `i` and `j`, then `{x,y,z,w}` spans at
most four colours: `s(x,y), s(x,z)` of colour `i`, `s(w,y), s(w,z)` of colour `j`, and
`s(x,w), s(y,z)`. -/
private theorem not_admissible_path_pair3 {c : Col n k} (hc : Admissible c)
    {x y z w : Verts n} {i j : Fin k} (h4 : FourDistinct x y z w)
    (h1 : c s(x, y) = i) (h2 : c s(x, z) = i) (h3 : c s(w, y) = j) (h4' : c s(w, z) = j) :
    False := by
  have hys : c s(y, w) = j := (c_swap' (x := w) (y := y)).trans h3
  have hzs : c s(z, w) = j := (c_swap' (x := w) (y := z)).trans h4'
  have hsub := colorsOn_sub_six (c := c) h4
    (S := (insert i (insert j (insert (c s(x, w)) (insert (c s(y, z)) (∅ : Finset (Fin k))))) :
      Finset (Fin k)))
    (by rw [h1]; exact Finset.mem_insert_self _ _)
    (by rw [h2]; exact Finset.mem_insert_self _ _)
    (by exact mem_in_insert (mem_in_insert (Finset.mem_insert_self _ _)))
    (by exact mem_in_insert (mem_in_insert (mem_in_insert (Finset.mem_insert_self _ _))))
    (by rw [hys]; exact mem_in_insert (Finset.mem_insert_self _ _))
    (by rw [hzs]; exact mem_in_insert (Finset.mem_insert_self _ _))
  have h5 := hc (fourSet x y z w) (card_fourSet h4)
  have hle := Finset.card_le_card hsub
  have hcard := card_insert4_le i j (c s(x, w)) (c s(y, z))
  omega

/-- The two leaves of a labelled triangle can be exchanged. -/
private theorem labTri_leafSwap {n k : ℕ} {c : Col n k} {u p q : Verts n} (h : LabTri c u p q) :
    LabTri c u q p := by
  have hne : c s(u, q) ≠ c s(q, p) := by
    intro hh
    exact h.2.2.2.2 (h.2.2.2.1.trans (hh.trans c_swap'))
  exact ⟨h.2.1, h.1, Ne.symm h.2.2.1, h.2.2.2.1.symm, hne⟩

/-- Exchanging the two leaves of a labelled triangle does not change its vertex set. -/
private theorem triVerts_swap {n : ℕ} (u p q : Verts n) : triVerts u q p = triVerts u p q := by
  have h1 : (insert q (insert p (∅ : Finset (Verts n))) : Finset (Verts n))
      = insert p (insert q (∅ : Finset (Verts n))) :=
    Finset.insert_comm (a := q) (b := p) (s := (∅ : Finset (Verts n)))
  unfold triVerts
  rw [h1]

/-- Two leaves of the same labelled triangle give the same three-element vertex set. -/
private theorem triVerts_of_leaves {n : ℕ} {u p q v w : Verts n}
    (hv : v = p ∨ v = q) (hw : w = p ∨ w = q) (hwv : w ≠ v) :
    triVerts u v w = triVerts u p q := by
  rcases hv with hv | hv <;> rcases hw with hw | hw
  · exact (hwv (hw.trans hv.symm)).elim
  · rw [hv, hw]
  · rw [hv, hw]; exact triVerts_swap u p q
  · exact (hwv (hw.trans hv.symm)).elim

/-- Membership in `{a, b}` as a disjunction. -/
private theorem mem_insert2_iff {α : Type*} [DecidableEq α] {a b x : α}
    (h : x ∈ (insert a (insert b (∅ : Finset α)))) : x = a ∨ x = b := by
  simp only [Finset.mem_insert] at h
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · simp at h

/-- Two pairs of distinct elements inside the same two-element set are equal. -/
private theorem pair_eq_of_pair {α : Type*} {p q p' q' : α} (hpq : p ≠ q) (hp'q' : p' ≠ q')
    (h1 : p' = p ∨ p' = q) (h2 : q' = p ∨ q' = q) :
    (p' = p ∧ q' = q) ∨ (p' = q ∧ q' = p) := by
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (h1.trans h2.symm) hp'q'
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd (h1.trans h2.symm) hp'q'

/-! ### §1  The two `(vertex, colour)` roles -/

/-- **THE FIVE PAIRS OF A LABELLED TRIANGLE.** -/
private theorem role_of_mem {c : Col n k} {u p q v : Verts n} {j : Fin k}
    (hm : (v, j) ∈ triPairs c u p q) :
    (v, j) = (u, c s(u, p)) ∨ (v, j) = (p, c s(u, p)) ∨ (v, j) = (q, c s(u, p)) ∨
      (v, j) = (p, c s(p, q)) ∨ (v, j) = (q, c s(p, q)) := by
  simp only [triPairs, Finset.mem_insert] at hm
  have hne : (v, j) ∉ (∅ : Finset (Verts n × Fin k)) := by simp
  tauto

/-- **THE LABELLED ROLE: exactly two `j`-neighbours.** -/
theorem centre_sem {c : Col n k} (hc : Admissible c) {u p q : Verts n} {j : Fin k}
    (h : LabTri c u p q) (hj : j = c s(u, p)) :
    (Nbrs c j u).card = 2 ∧ p ∈ Nbrs c j u ∧ q ∈ Nbrs c j u := by
  have hne : u ≠ p ∧ u ≠ q ∧ p ≠ q := LabTri.ne h
  have hup : p ∈ Nbrs c j u := mem_Nbrs.mpr ⟨Ne.symm hne.1, hj.symm⟩
  have huq : q ∈ Nbrs c j u := mem_Nbrs.mpr ⟨Ne.symm hne.2.1, h.2.2.2.1.symm.trans hj.symm⟩
  have hge : 2 ≤ (Nbrs c j u).card := card_ge_two hne.2.2 hup huq
  have hle := nbrs_card_le_two hc j u
  exact ⟨by omega, hup, huq⟩

/-- **THE PATH-LEAF ROLE: exactly one `j`-neighbour, the labelled vertex.** -/
theorem pathLeaf_sem {c : Col n k} (hc : Admissible c) {u a b : Verts n} {j : Fin k}
    (h : LabTri c u a b) (hj : j = c s(u, a)) :
    (Nbrs c j a).card = 1 ∧ u ∈ Nbrs c j a := by
  have hne : u ≠ a ∧ u ≠ b ∧ a ≠ b := LabTri.ne h
  have hau : u ∈ Nbrs c j a :=
    mem_Nbrs.mpr ⟨hne.1, (c_swap' (x := u) (y := a)).trans hj.symm⟩
  refine ⟨?_, hau⟩
  by_contra hnot
  have hcard : (Nbrs c j a).card = 2 := by
    have h1 := Finset.card_pos.2 ⟨u, hau⟩
    have h2 := nbrs_card_le_two hc j a
    omega
  have hlt : ({u} : Finset (Verts n)).card < (Nbrs c j a).card := by
    rw [Finset.card_singleton, hcard]
    norm_num
  obtain ⟨w, hw, hwu⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := ({u} : Finset (Verts n))) hlt
  have hwu' : u ≠ w := Ne.symm (by simpa using hwu)
  have hNbrs : Nbrs c j a = {u, w} := card_two_eq hcard hau hw hwu'
  have hwa : w ≠ a := (mem_Nbrs.mp hw).1
  have hawjw : c s(a, w) = j := (mem_Nbrs.mp hw).2
  have hwq : w ≠ b := by
    intro hh
    rw [hh] at hawjw
    exact h.2.2.2.2 (hawjw.trans hj).symm
  have h4 : FourDistinct a u b w :=
    ⟨Ne.symm hne.1, hne.2.2, Ne.symm hwa, hne.2.1, hwu', Ne.symm hwq⟩
  have hbad : ¬ Admissible c := not_admissible_of_three (i := j) h4 s(a, u) s(a, w) s(u, b)
    ⟨mem_edgeFinset_mk (mem_fourSet_a h4) (mem_fourSet_b h4) (Ne.symm hne.1),
      mem_edgeFinset_mk (mem_fourSet_a h4) (mem_fourSet_e h4) (Ne.symm hwa),
      mem_edgeFinset_mk (mem_fourSet_b h4) (mem_fourSet_d h4) hne.2.1⟩
    ((c_swap' (x := u) (y := a)).trans hj.symm) hawjw (hj.trans h.2.2.2.1).symm
    ⟨fun hh => h4.2.2.2.2.1 (sym2_inj_right hh),
      fun hh => (sym2_inj hh).elim (fun e => h4.1 e.1) (fun e => h4.2.1 e.1),
      fun hh => (sym2_inj hh).elim (fun e => h4.1 e.1) (fun e => h4.2.1 e.1)⟩
  exact hbad hc

/-- **THE OPPOSITE-LEAF ROLE: exactly one `j`-neighbour, the other leaf.** -/
theorem oppLeaf_sem {c : Col n k} (hc : Admissible c) {u a b : Verts n} {j : Fin k}
    (h : LabTri c u a b) (hj : j = c s(a, b)) :
    (Nbrs c j a).card = 1 ∧ b ∈ Nbrs c j a := by
  have hne : u ≠ a ∧ u ≠ b ∧ a ≠ b := LabTri.ne h
  have hab : b ∈ Nbrs c j a := mem_Nbrs.mpr ⟨Ne.symm hne.2.2, hj.symm⟩
  refine ⟨?_, hab⟩
  by_contra hnot
  have hcard : (Nbrs c j a).card = 2 := by
    have h1 := Finset.card_pos.2 ⟨b, hab⟩
    have h2 := nbrs_card_le_two hc j a
    omega
  have hlt : ({b} : Finset (Verts n)).card < (Nbrs c j a).card := by
    rw [Finset.card_singleton, hcard]
    norm_num
  obtain ⟨w, hw, hwb⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := ({b} : Finset (Verts n))) hlt
  have hwb' : b ≠ w := Ne.symm (by simpa using hwb)
  have hNbrs : Nbrs c j a = {b, w} := card_two_eq hcard hab hw hwb'
  have hwa : w ≠ a := (mem_Nbrs.mp hw).1
  have hawjw : c s(a, w) = j := (mem_Nbrs.mp hw).2
  have hwu : w ≠ u := by
    intro hh
    rw [hh] at hawjw
    exact h.2.2.2.2 ((c_swap' (x := u) (y := a)).symm.trans (hawjw.trans hj))
  have h4 : FourDistinct u a b w :=
    ⟨hne.1, hne.2.1, Ne.symm hwu, hne.2.2, Ne.symm hwa, hwb'⟩
  exact not_admissible_path_pair hc h4 (i := c s(u, a)) (j := j) rfl h.2.2.2.1.symm hj.symm
    hawjw

/-- **OBSTRUCTION I.**  `v` is a *path* leaf of `(u; v, w)` with colour `j`, and an *opposite* leaf
of `(u'; v, w')` with colour `j`: impossible. -/
theorem obstruction_one {c : Col n k} (hc : Admissible c) {u v w u' w' : Verts n} {j : Fin k}
    (h1 : LabTri c u v w) (h2 : LabTri c u' v w') (huv : c s(u, v) = j) (hvw' : c s(v, w') = j) :
    False := by
  have hle := pathLeaf_sem hc h1 huv.symm
  have hw'N : w' ∈ Nbrs c j v := mem_Nbrs.mpr ⟨Ne.symm h2.2.2.1, hvw'⟩
  have hw : w' = u := eq_of_card_one hle.1 hw'N hle.2
  rw [hw] at h2
  have hne1 : u ≠ v ∧ u ≠ w ∧ v ≠ w := LabTri.ne h1
  have hne2 : u' ≠ v ∧ u' ≠ u ∧ v ≠ u := LabTri.ne h2
  have hwu : w ≠ u' := by
    intro hh
    have h1' : c s(u, w) = j := h1.2.2.2.1.symm.trans huv
    have h2' : c s(u', u) = c s(u', v) := h2.2.2.2.1.symm
    have e1 : c s(u, u') = j := hh ▸ h1'
    have e2 : c s(u, u') = c s(v, w) := by
      calc c s(u, u') = c s(u', u) := c_swap' (x := u') (y := u)
        _ = c s(u', v) := h2'
        _ = c s(w, v) := by rw [hh]
        _ = c s(v, w) := c_swap' (x := v) (y := w)
    rw [e1] at e2
    exact h1.2.2.2.2 (huv.trans e2)
  have h4 : FourDistinct u v w u' :=
    ⟨hne1.1, hne1.2.1, Ne.symm hne2.2.1, hne1.2.2, Ne.symm hne2.1, hwu⟩
  exact not_admissible_path_pair2 hc h4 (i := j) (j := c s(u', u)) huv
    (h1.2.2.2.1.symm.trans huv) rfl h2.2.2.2.1

/-- **OBSTRUCTION II.**  `v` is an *opposite* leaf of `(u; v, w)` and of `(u'; v, w')` with colour
`j`, and `u ≠ u'`: impossible. -/
theorem obstruction_two {c : Col n k} (hc : Admissible c) {u v w u' w' : Verts n} {j : Fin k}
    (h1 : LabTri c u v w) (h2 : LabTri c u' v w') (hvw : c s(v, w) = j) (hvw' : c s(v, w') = j)
    (huu' : u ≠ u') : False := by
  have hle1 := oppLeaf_sem hc h1 hvw.symm
  have hle2 := oppLeaf_sem hc h2 hvw'.symm
  have hw : w = w' := eq_of_card_one hle1.1 hle1.2 hle2.2
  rw [← hw] at h2
  have hne1 : u ≠ v ∧ u ≠ w ∧ v ≠ w := LabTri.ne h1
  have hne2 : u' ≠ v ∧ u' ≠ w ∧ v ≠ w := LabTri.ne h2
  have h4 : FourDistinct u v w u' :=
    ⟨hne1.1, hne1.2.1, huu', hne1.2.2, Ne.symm hne2.1, Ne.symm hne2.2.1⟩
  exact not_admissible_path_pair3 hc h4 (i := c s(u, v)) (j := c s(u', v)) rfl
    h1.2.2.2.1.symm rfl h2.2.2.2.1.symm


/-! ### §2  The assembly: the matching condition is a consequence of admissibility -/

/-- **THE ROLE OF `v` IN A LABELLED TRIANGLE, IN NORMAL FORM.**  Membership of `(v, j)` in the five
pairs of the labelled triangle `(u; p, q)` means exactly one of

* `v = u` and `j = c s(u, p)` — the **labelled** role, `(v, j) = (u, c s(u,p))`;
* `v` is one of the two leaves and `j = c s(u, p)` — the **path-leaf** role: after naming the
  other leaf `w`, `(v, j) = (v, c s(u, v))` with `LabTri c u v w`;
* `v` is one of the two leaves and `j = c s(p, q)` — the **opposite-leaf** role: after naming the
  other leaf `w`, `(v, j) = (v, c s(v, w))` with `LabTri c u v w`.

In the two leaf roles the named witness also satisfies `triVerts u v w = triVerts u p q`. -/
private theorem role_norm {c : Col n k} {u p q v : Verts n} {j : Fin k} (hL : LabTri c u p q)
    (hm : (v, j) ∈ triPairs c u p q) :
    (v = u ∧ j = c s(u, p)) ∨
      (∃ w, LabTri c u v w ∧ c s(u, v) = j ∧ triVerts u v w = triVerts u p q) ∨
      (∃ w, LabTri c u v w ∧ c s(v, w) = j ∧ triVerts u v w = triVerts u p q) := by
  rcases role_of_mem hm with e | e | e | e | e
  · exact Or.inl ⟨congrArg Prod.fst e, congrArg Prod.snd e⟩
  · have hvp : v = p := congrArg Prod.fst e
    have hpj : j = c s(u, p) := congrArg Prod.snd e
    rw [hvp]
    exact Or.inr (Or.inl ⟨q, hL, hpj.symm, triVerts_of_leaves (Or.inl rfl) (Or.inr rfl) (Ne.symm hL.2.2.1)⟩)
  · have hvp : v = q := congrArg Prod.fst e
    have hpj : j = c s(u, p) := congrArg Prod.snd e
    rw [hvp]
    exact Or.inr (Or.inl ⟨p, labTri_leafSwap hL, hL.2.2.2.1.symm.trans hpj.symm,
      triVerts_of_leaves (Or.inr rfl) (Or.inl rfl) hL.2.2.1⟩)
  · have hvp : v = p := congrArg Prod.fst e
    have hpj : j = c s(p, q) := congrArg Prod.snd e
    rw [hvp]
    exact Or.inr (Or.inr ⟨q, hL, hpj.symm, triVerts_of_leaves (Or.inl rfl) (Or.inr rfl) (Ne.symm hL.2.2.1)⟩)
  · have hvp : v = q := congrArg Prod.fst e
    have hpj : j = c s(p, q) := congrArg Prod.snd e
    rw [hvp]
    exact Or.inr (Or.inr ⟨p, labTri_leafSwap hL, (c_swap' (x := p) (y := q)).trans hpj.symm,
      triVerts_of_leaves (Or.inr rfl) (Or.inl rfl) hL.2.2.1⟩)

/-- **TWO LABELLED TRIANGLES WITH THE SAME LABELLED VERTEX AND THE SAME PATH COLOUR.**  They are the
same triangle: the two `j`-neighbours of the labelled vertex are `{p, q}` and `{p', q'}`
respectively, so `{p, q} = {p', q'}`. -/
private theorem lab_unify {c : Col n k} (hc : Admissible c) {u p q u' p' q' : Verts n} {j : Fin k}
    (h1 : LabTri c u p q) (h2 : LabTri c u' p' q') (hj1 : j = c s(u, p)) (hj2 : j = c s(u', p'))
    (huu' : u = u') : triVerts u p q = triVerts u' p' q' := by
  have hc1 := centre_sem hc h1 hj1
  have hc2 := centre_sem hc h2 hj2
  have hN1 : Nbrs c j u = insert p (insert q ∅) := card_two_eq hc1.1 hc1.2.1 hc1.2.2 h1.2.2.1
  have hp' : p' = p ∨ p' = q := by
    have hmem : p' ∈ Nbrs c j u' := hc2.2.1
    rw [← huu'] at hmem
    rw [hN1] at hmem
    exact mem_insert2_iff hmem
  have hq' : q' = p ∨ q' = q := by
    have hmem : q' ∈ Nbrs c j u' := hc2.2.2
    rw [← huu'] at hmem
    rw [hN1] at hmem
    exact mem_insert2_iff hmem
  rcases pair_eq_of_pair h1.2.2.1 h2.2.2.1 hp' hq' with ⟨hpp, hqq⟩ | ⟨hpq, hqp⟩
  · rw [hpp, hqq, huu']
  · rw [hpq, hqp, huu', triVerts_swap]

/-- **TWO LABELLED TRIANGLES WITH THE SAME PATH-LEAF ROLE.**  The unique `j`-neighbour of `v` is
the labelled vertex of both, so `u = u'`; then the two `j`-neighbours of `u` are `{v, w₁}` and
`{v, w₂}`, so `w₁ = w₂`. -/
private theorem path_unify {c : Col n k} (hc : Admissible c) {u u' v w₁ w₂ : Verts n} {j : Fin k}
    (h1 : LabTri c u v w₁) (h2 : LabTri c u' v w₂) (hj1 : j = c s(u, v)) (hj2 : j = c s(u', v)) :
    triVerts u v w₁ = triVerts u' v w₂ := by
  have hc1 := centre_sem hc h1 hj1
  have hc2 := centre_sem hc h2 hj2
  have hle1 := pathLeaf_sem hc h1 hj1
  have hle2 := pathLeaf_sem hc h2 hj2
  have hu : u = u' := eq_of_card_one hle1.1 hle1.2 hle2.2
  have hN2 : Nbrs c j u' = insert v (insert w₂ ∅) := card_two_eq hc2.1 hc2.2.1 hc2.2.2 h2.2.2.1
  have hw : w₁ = w₂ := by
    have hmem : w₁ ∈ Nbrs c j u := hc1.2.2
    rw [hu] at hmem
    rw [hN2] at hmem
    exact mem_insert2_iff hmem |>.resolve_left (Ne.symm h1.2.2.1)
  rw [hu, hw]

/-- **TWO LABELLED TRIANGLES WITH THE SAME OPPOSITE-LEAF ROLE.**  The unique `j`-neighbour of `v`
is the other leaf of both, so `w₁ = w₂`; if additionally the labelled vertices agree the triangles
coincide, and if they do not, `obstruction_two` rules the configuration out. -/
private theorem opp_unify {c : Col n k} (hc : Admissible c) {u u' v w₁ w₂ : Verts n}
    (h1 : LabTri c u v w₁) (h2 : LabTri c u' v w₂) (hj : c s(v, w₁) = c s(v, w₂)) :
    triVerts u v w₁ = triVerts u' v w₂ := by
  have hle1 := oppLeaf_sem hc h1 rfl
  have hle2 := oppLeaf_sem hc h2 hj
  have hw : w₁ = w₂ := eq_of_card_one hle1.1 hle1.2 hle2.2
  by_cases hu : u = u'
  · rw [hu, hw]
  · exact (obstruction_two hc h1 h2 rfl hj.symm hu).elim

/-- **A LABELLED ROLE AND A LEAF ROLE AT THE SAME `(VERTEX, COLOUR)` PAIR ARE INCOMPATIBLE.**  The
labelled role of `(v, j)` forces `v` to have exactly two `j`-neighbours, either leaf role exactly
one. -/
private theorem lab_leaf_false {c : Col n k} (hc : Admissible c) {u p q v : Verts n} {j : Fin k}
    (h1 : LabTri c u p q) (hj1 : j = c s(u, p)) (hvu : v = u) (hone : (Nbrs c j v).card = 1) :
    False := by
  have hc1 := centre_sem hc h1 hj1
  rw [hvu] at hone
  omega

/-- **TWO LABELLED TRIANGLES OF AN ADMISSIBLE COLOURING THAT SHARE A `(VERTEX, COLOUR)` PAIR ARE THE
SAME TRIANGLE.**  This is the whole content of the matching condition `PairFree` of
arXiv:2208.12563 §4, obtained from the catalog condition alone. -/
theorem triVerts_eq_of_mem_triPairs {n k : ℕ} {c : Col n k} (hc : Admissible c)
    {u p q u' p' q' : Verts n} (h1 : LabTri c u p q) (h2 : LabTri c u' p' q')
    {v : Verts n} {j : Fin k} (hm : (v, j) ∈ triPairs c u p q ∩ triPairs c u' p' q') :
    triVerts u p q = triVerts u' p' q' := by
  obtain ⟨hm1, hm2⟩ := Finset.mem_inter.mp hm
  rcases role_norm h1 hm1 with ⟨hvu1, hj1⟩ | ⟨⟨w₁, h1', hjv1, ht1⟩⟩ | ⟨⟨w₁, h1', hjv1, ht1⟩⟩
  · rcases role_norm h2 hm2 with ⟨hvu2, hj2⟩ | ⟨⟨w₂, h2', hjv2, ht2⟩⟩ | ⟨⟨w₂, h2', hjv2, ht2⟩⟩
    · exact lab_unify hc h1 h2 hj1 hj2 (hvu1.symm.trans hvu2)
    · exact (lab_leaf_false hc h1 hj1 hvu1 (pathLeaf_sem hc h2' hjv2.symm).1).elim
    · exact (lab_leaf_false hc h1 hj1 hvu1 (oppLeaf_sem hc h2' hjv2.symm).1).elim
  · rcases role_norm h2 hm2 with ⟨hvu2, hj2⟩ | ⟨⟨w₂, h2', hjv2, ht2⟩⟩ | ⟨⟨w₂, h2', hjv2, ht2⟩⟩
    · exact (lab_leaf_false hc h2 hj2 hvu2 (pathLeaf_sem hc h1' hjv1.symm).1).elim
    · rw [← ht1, ← ht2]; exact path_unify hc h1' h2' hjv1.symm hjv2.symm
    · rw [← ht1, ← ht2]; exact (obstruction_one hc h1' h2' hjv1 hjv2).elim
  · rcases role_norm h2 hm2 with ⟨hvu2, hj2⟩ | ⟨⟨w₂, h2', hjv2, ht2⟩⟩ | ⟨⟨w₂, h2', hjv2, ht2⟩⟩
    · exact (lab_leaf_false hc h2 hj2 hvu2 (oppLeaf_sem hc h1' hjv1.symm).1).elim
    · rw [← ht1, ← ht2]; exact (obstruction_one hc h2' h1' hjv2 hjv1).elim
    · rw [← ht1, ← ht2]
      refine opp_unify hc h1' h2' ?_
      calc c s(v, w₁) = j := hjv1
        _ = c s(v, w₂) := hjv2.symm

/-- **THE MATCHING CONDITION IS A CONSEQUENCE OF THE CATALOG CONDITION.**  Two labelled triangles of
an admissible colouring which use a common `(vertex, colour)` pair are the same triangle; hence the
five `(vertex, colour)` pairs of distinct labelled triangles of an admissible colouring are
disjoint.  This removes `PairFree` as an extra hypothesis of `Triangles.TriFamily`: for a colouring
*covered* by labelled triangles, `PairFree` now follows from `Admissible` alone. -/
theorem PairFree_of_admissible {n k : ℕ} {c : Col n k} (hc : Admissible c) : PairFree c := by
  intro u p q u' p' q' h1 h2 hcon
  refine Finset.eq_empty_iff_forall_notMem.mpr fun y hy => ?_
  cases y with
  | mk v j => exact hcon (triVerts_eq_of_mem_triPairs hc h1 h2 hy)

/-! ### §3  What the matching condition buys: the price of a triangle family -/

set_option linter.unusedSimpArgs false in
/-- **A LABELLED TRIANGLE USES EXACTLY FIVE `(VERTEX, COLOUR)` PAIRS.**  The five pairs
`(u, λ), (p, λ), (q, λ), (p, μ), (q, μ)` — with `λ = c s(u,p) = c s(u,q)` and `μ = c s(p,q) ≠ λ` —
are pairwise distinct, because `u, p, q` are distinct and `λ ≠ μ`.  This is the "five pairs per
triangle" of arXiv:2208.12563 §4, and it is where the constant `5/6` of the catalog answer
comes from: `|E(K_n)| / 3` triangles, five pairs each, out of `n · k` pairs. -/
theorem card_triPairs_five {n k : ℕ} {c : Col n k} {u p q : Verts n} (h : LabTri c u p q) :
    (triPairs c u p q).card = 5 := by
  have hne : u ≠ p ∧ u ≠ q ∧ p ≠ q := LabTri.ne h
  have hcol : c s(u, p) ≠ c s(p, q) := h.2.2.2.2
  simp only [triPairs]
  rw [Finset.card_insert_of_notMem (by simp [hne.1, hne.2.1]),
    Finset.card_insert_of_notMem (by simp [hne.2.2, hcol]),
    Finset.card_insert_of_notMem (by simp [hne.2.2, hcol]),
    Finset.card_insert_of_notMem (by simp [hne.2.2]),
    Finset.card_insert_of_notMem (by simp [hne.2.2])]
  norm_num

/-- **THE PRICE OF A FAMILY OF LABELLED TRIANGLES.**  Let `T` be a family of labelled triangles of
the admissible colouring `c` — given as the triples themselves, so no choice is needed — whose
vertex sets are pairwise distinct.  Then the `(vertex, colour)` pairs used by the corresponding
triangles are pairwise disjoint — this is `PairFree`, now a theorem — so the family uses
`5 · |T|` distinct pairs out of the `n · k` available, and

    `5 * |T| ≤ n * k`.

This is the packing bound of arXiv:2208.12563 §4, and it is where the constant `5/6` of the
catalog answer comes from: a triangle *decomposition* of `K_n` has `n(n-1)/6` triangles, so
`5 · n(n-1)/6 ≤ n · k`, i.e. `k ≥ 5(n-1)/6` — the sharp lower bound, read off the construction
encoding rather than proved by counting colour classes. -/
theorem five_mul_card_le {n k : ℕ} {c : Col n k} (hc : Admissible c)
    {T : Finset (Verts n × Verts n × Verts n)}
    (htri : ∀ t ∈ T, LabTri c t.1 t.2.1 t.2.2)
    (hdinj : ∀ t t' : Verts n × Verts n × Verts n, t ∈ T → t' ∈ T →
      triVerts t.1 t.2.1 t.2.2 = triVerts t'.1 t'.2.1 t'.2.2 → t = t') :
    5 * T.card ≤ n * k := by
  have hcard : ∀ t : Verts n × Verts n × Verts n, t ∈ T →
      (triPairs c t.1 t.2.1 t.2.2).card = 5 := by
    intro t ht; exact card_triPairs_five (htri t ht)
  have hdisj : ∀ t : Verts n × Verts n × Verts n, t ∈ T →
      ∀ t' : Verts n × Verts n × Verts n, t' ∈ T → t ≠ t' →
      ∀ x : Verts n × Fin k, x ∈ triPairs c t.1 t.2.1 t.2.2 →
        x ∈ triPairs c t'.1 t'.2.1 t'.2.2 → False := by
    intro t ht t' ht' hne x hxt hxt'
    have hmem : x ∈ triPairs c t.1 t.2.1 t.2.2 ∩ triPairs c t'.1 t'.2.1 t'.2.2 :=
      Finset.mem_inter.mpr ⟨hxt, hxt'⟩
    have hEq := triVerts_eq_of_mem_triPairs hc (htri t ht) (htri t' ht') hmem
    exact hne (hdinj t t' ht ht' hEq)
  have hsum : (∑ t ∈ T, (triPairs c t.1 t.2.1 t.2.2).card) = 5 * T.card := by
    rw [Finset.sum_const_nat (fun t ht => hcard t ht)]; omega
  have hdj : ∀ t : Verts n × Verts n × Verts n, t ∈ T →
      ∀ t' : Verts n × Verts n × Verts n, t' ∈ T → t ≠ t' →
        Disjoint (triPairs c t.1 t.2.1 t.2.2) (triPairs c t'.1 t'.2.1 t'.2.2) :=
    fun t ht t' ht' hne => Finset.disjoint_left.mpr
      fun x hx hx' => hdisj t ht t' ht' hne x hx hx'
  have hdju := Finset.card_disjiUnion T (fun t => triPairs c t.1 t.2.1 t.2.2) hdj
  have hle : ((T.disjiUnion (fun t => triPairs c t.1 t.2.1 t.2.2) hdj).card)
      ≤ ((Finset.univ : Finset (Verts n × Fin k)).card : ℕ) := Finset.card_le_card (Finset.subset_univ _)
  have huniv : ((Finset.univ : Finset (Verts n × Fin k)).card : ℕ) = n * k := by
    simp [Finset.card_univ, Fintype.card_prod]
  have h1 : (∑ t ∈ T, (triPairs c t.1 t.2.1 t.2.2).card)
      = ((T.disjiUnion (fun t => triPairs c t.1 t.2.1 t.2.2) hdj).card : ℕ) := hdju.symm
  have h2 : ((T.disjiUnion (fun t => triPairs c t.1 t.2.1 t.2.2) hdj).card) ≤ n * k
      :=
    hle.trans (Nat.le_of_eq huniv)
  have hA : 5 * T.card ≤ (∑ t ∈ T, (triPairs c t.1 t.2.1 t.2.2).card) := le_of_eq hsum.symm
  have hB : (∑ t ∈ T, (triPairs c t.1 t.2.1 t.2.2).card)
      ≤ ((T.disjiUnion (fun t => triPairs c t.1 t.2.1 t.2.2) hdj).card : ℕ) := le_of_eq h1
  exact hA.trans (hB.trans h2)

/-- **THE PRICE OF A TRIANGLE DECOMPOSITION: THE SHARP `5/6` LOWER BOUND FROM THE ENCODING.**  A
family of labelled triangles with pairwise distinct vertex sets whose vertex sets decompose `K_n`
(a *triangle decomposition*, so `6 · |T| = n · (n-1)`) satisfies `5(n-1) ≤ 6k` — the catalog lower
bound with the sharp constant `5/6`, obtained from `fifteen`-style counting of
`triPairs` instead of counting colour classes. -/
theorem five_mul_card_le_decomposition {n k : ℕ} {c : Col n k} (hc : Admissible c)
    {T : Finset (Verts n × Verts n × Verts n)}
    (htri : ∀ t ∈ T, LabTri c t.1 t.2.1 t.2.2)
    (hdinj : ∀ t t' : Verts n × Verts n × Verts n, t ∈ T → t' ∈ T →
      triVerts t.1 t.2.1 t.2.2 = triVerts t'.1 t'.2.1 t'.2.2 → t = t')
    (hn : 0 < n) (h6 : 6 * T.card = n * (n - 1)) : 5 * (n - 1) ≤ 6 * k := by
  have h5 : 5 * T.card ≤ n * k := five_mul_card_le hc htri hdinj
  nlinarith

/-- **TWO LABELLED TRIANGLES OF AN ADMISSIBLE COLOURING NEVER SHARE AN EDGE.**  The matching
condition was carried as an extra hypothesis (`PairFree`, blocker B3) from round 29 on; for an
admissible colouring it is automatic, and the *packing* statement of arXiv:2208.12563 §4 —
"the triangles of the construction form a matching" — comes for free. -/
theorem triVerts_eq_of_mem_triEdges_admissible {n k : ℕ} {c : Col n k} (hc : Admissible c)
    {u p q u' p' q' : Verts n} (h1 : LabTri c u p q) (h2 : LabTri c u' p' q')
    {e : Sym2 (Verts n)} (he : e ∈ triEdges c u p q ∩ triEdges c u' p' q') :
    triVerts u p q = triVerts u' p' q' :=
  triVerts_eq_of_mem_triEdges (PairFree_of_admissible hc) h1 h2 he

/-- **ALL THE COLOUR-`i` EDGES AT A VERTEX LIE IN ONE SINGLE LABELLED TRIANGLE** — again for free,
since the matching condition follows from admissibility. -/
theorem exists_labTri_of_mem_of_admissible {n k : ℕ} {c : Col n k} (hc : Admissible c)
    (hC : Covers c) {i : Fin k} {v : Verts n} (hv : 1 ≤ (Nbrs c i v).card) :
    ∃ u p q : Verts n, LabTri c u p q ∧
      ∀ x : Verts n, x ∈ Nbrs c i v → s(v, x) ∈ triEdges c u p q :=
  exists_labTri_of_mem hC (PairFree_of_admissible hc) hv

/-! ### §4  The prize hypothesis with the matching condition replaced by the catalog condition -/

/-- **THE PUBLISHED CONSTRUCTION, VERIFIABLE BY THE CATALOG CONDITION.**  Exactly
`Triangles.TriFamily`, except that the matching condition is replaced by the catalog condition
`Admissible` — which is legitimate because `PairFree_of_admissible` above makes the matching
condition a *theorem*.  So the second phase of arXiv:2207.02920 §12 does **not** need a separate
"matching" verification: checking the four-vertex cliques of the finished colouring is enough. -/
def TriFamilyAdmissible : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ M : ℕ, ∀ m : ℕ, M ≤ m → m % 6 = 1 →
    ∃ (k : ℕ) (c : Col m k), Admissible c ∧ Covers c ∧ NoCrossFour c ∧ NoBadFour c ∧
      (6 : ℝ) * (k : ℝ) ≤ 5 * ((m - 1 : ℕ) : ℝ) + δ * (m : ℝ)

/-- The two forms of the construction hypothesis agree: verifying admissibility instead of the
matching condition is enough. -/
theorem TriFamily.of_admissible (hfam : TriFamilyAdmissible) : TriFamily := by
  intro δ hδ
  obtain ⟨M, hM⟩ := hfam δ hδ
  refine ⟨M, fun m hMm hm => ?_⟩
  obtain ⟨k, c, hadm, hC, hX, hB, hk⟩ := hM m hMm hm
  exact ⟨k, c, hC, PairFree_of_admissible hadm, hX, hB, hk⟩

/-- **THE REQUIRED THEOREM, REDUCED TO THE CONSTRUCTION VERIFIED BY THE CATALOG CONDITION.** -/
theorem jsp_000140_main_of_tri_family_admissible (hfam : TriFamilyAdmissible) :
    jsp_000140_target :=
  jsp_000140_main_of_tri_family (TriFamily.of_admissible hfam)

end JSP140
