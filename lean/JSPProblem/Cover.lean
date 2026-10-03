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


end JSP140

/- ### §2  WHAT IS STILL MISSING

Everything above is PROVED.  What the file does NOT yet contain is the final assembly
`triVerts_eq_of_mem_triPairs`, i.e. the statement that two labelled triangles of an admissible
colouring which share a `(vertex, colour)` pair coincide.  Its proof reduces, by `centre_sem`,
`pathLeaf_sem` and `oppLeaf_sem`, to the following elementary case analysis on the role of `v` in
the two triangles (all ingredients are in this file):

* `v` labelled in both: both triangles have the same two `j`-neighbours, so
  `triVerts u p q = triVerts u' p' q'` (`sub_insert2_of_card_le_two` plus `pair_eq_of_pair`);
* `v` labelled in one and a leaf in the other: `(Nbrs c j v).card` would be both `2` and `1`;
* `v` a leaf in both, with `j` the path colour of both: the unique `j`-neighbour of `v` is the
  labelled vertex of each, so `u = u'` and then the first case applies;
* `v` a leaf in both, with `j` the path colour of one and the opposite colour of the other:
  `obstruction_one` (which concludes `Not Admissible c`);
* `v` a leaf in both, with `j` the opposite colour of both: the two other leaves agree
  (`Nbrs c j v` has one element), so either `u = u'` and the first case applies again, or
  `obstruction_two` (which concludes `Not Admissible c`).

The three `K₄` configurations needed in that argument are `not_admissible_path_pair`,
`not_admissible_path_pair2` and `not_admissible_path_pair3`, all proved above.  What is missing is
only the bookkeeping: routing the role data through a disjunction `role_bundle` whose statement is
that five-case table (and whose proof is five applications of `role_of_mem`, `centre_sem`,
`pathLeaf_sem`, `oppLeaf_sem`). -/
