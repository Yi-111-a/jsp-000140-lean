import JSPProblem.Cover
import JSPProblem.Rigidity

/-!
# JSP-000140 — round 71: THE GRID DECOMPOSITION OF THE EXTREMAL CASE

Rounds 13–30 (`Rigidity.lean`) proved the **necessity** side of the extremal case: if an
admissible colouring of `K_n` uses exactly `5(n-1)/6` colours — the number forced by the sharp
counting bound `Cherry.five_sixth_lower` — then its two-edge paths form a Steiner triple system
(`Rigidity.tight_pathFinset_is_STS`), so it decomposes `K_n` into `n(n-1)/6` triangles.  Rounds
29–51 (`Triangles.lean`, `Cover.lean`) encoded such a decomposition as a family of **labelled
triangles** and showed that the matching condition `PairFree` of arXiv:2208.12563 §4 follows from
admissibility, together with the **price** `5 · |T| ≤ n · k`: five `(vertex, colour)` cells per
triangle out of the `n · k` available.

**This round puts the five cells of a labelled triangle into a grid and counts them cellwise.**

## The grid

`Grid.cell (n k) = Verts n × Fin k` is the set of `(vertex, colour)` pairs and `Grid.grid n k` its
`n · k` cells (`Grid.card_grid`).  A labelled triangle `(u, p, q)` occupies the **cross**
`Grid.cross c u p q = triPairs c u p q` — the five cells `(u, λ), (p, λ), (q, λ), (p, μ), (q, μ)`
with `λ = c s(u,p) = c s(u,q)` the *cherry* colour and `μ = c s(p,q) ≠ λ` the *leaf* colour
(`Grid.card_cross` = `Cover.card_triPairs_five`).

## The cell equation (the main theorem of this round)

`Grid.Decomposes c T` = the family `T` of labelled triangles covers the whole grid, pairwise
disjointly (the matching condition plus fullness).  Then

> **`Grid.cellCount`: for every colour `j` the `n` cells of colour `j` are covered exactly once,
> a triangle whose cherry colour is `j` covering three of them and a triangle whose leaf colour is
> `j` covering exactly two, so**
>
>     `3 · a_j + 2 · b_j = n`,   `a_j = #`triangles with cherry colour `j`,
>                                  `b_j = #`triangles with leaf colour `j`.

This is a constraint on the *extremal colourings themselves* which rounds 13–30 do not see: it says
that the colour classes of a tight colouring split into those which are mostly cherries and those
which are mostly isolated single edges.

## The obstruction at `n = 7`

At `n = 7` the equation `3 a_j + 2 b_j = 7` forces `a_j = 1` for every colour (an odd `a_j` with
`3 a_j ≤ 7`), so **a decomposition of the `7 × 5` grid has five triangles** (`Grid.card_eq_five`).
A tight admissible colouring of `K_7`, on the other hand, has `n(n-1)/6 = 7` of them
(`Grid.decomposes_of_tight`), which gives

* **`Grid.eg_seven_ge_six : 6 ≤ EG 7`** — the sharp bound `⌈5(n-1)/6⌉ = 5` of
  `Tables.EG_ge_ceil_five_sixth` is *not attained* at `n = 7`, the first order at which the
  tightness theory is refuted.

## What is still missing

`jsp_000140_main = FiveSixth EG` is untouched: its lower half is proved (`Main.fiveSixthLower_eg`)
and its upper half is the existence of labelled-triangle systems (`Triangles.TriFamily`).  What this
round adds is a *no-go* statement at the tight order: the tight colouring would have to be a
decomposition of the `n × k` grid into crosses, and at `n = 7` — the first admissible order of the
Fano plane — this is arithmetically impossible.  A `decide`-free search in
`discovery/JSP-000140/r71_grid_probe.py` (exhaustive over all `20^7` labelings of the seven Fano
blocks) confirms the `n = 7` case, and finds no decomposition of the `13 × 10` grid within a
47·10⁶-node budget, so the obstruction is expected to be special to the smallest order.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace JSP140
namespace Grid

variable {n k : ℕ}

/-- A triple of vertices, to be read as a labelled triangle `(centre, leaf, leaf)`. -/
abbrev Triple (n k : ℕ) : Type := Verts n × Verts n × Verts n

/-! ### §1  The `(vertex, colour)` grid -/

/-- A cell of the grid: a `(vertex, colour)` pair. -/
abbrev Cell (n k : ℕ) : Type := Verts n × Fin k

/-- **The grid**: the `n · k` cells `V(K_n) × Col(K_n)`. -/
def grid (n k : ℕ) : Finset (Cell n k) := (Finset.univ : Finset (Verts n × Fin k))

/-- The grid has `n · k` cells. -/
@[simp] theorem card_grid (n k : ℕ) : (grid n k).card = n * k := by
  show ((Finset.univ : Finset (Verts n × Fin k))).card = n * k
  simp

@[simp] theorem mem_grid {n k : ℕ} {x : Cell n k} : x ∈ grid n k := Finset.mem_univ _

/-- The `n` cells of one colour `j`. -/
def cellsOf (n k : ℕ) (j : Fin k) : Finset (Cell n k) := (grid n k).filter (fun x => x.2 = j)

/-- There are exactly `n` cells of each colour. -/
@[simp] theorem card_cellsOf (n k : ℕ) (j : Fin k) : (cellsOf n k j).card = n := by
  classical
  have e1 : cellsOf n k j ⊆ (Finset.univ : Finset (Verts n)).image (fun v : Verts n => (v, j)) := by
    intro x hx
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hx
    refine Finset.mem_image.mpr ⟨x.1, Finset.mem_univ _, ?_⟩
    exact Prod.ext_iff.mpr ⟨rfl, h2.symm⟩
  have e2 : (Finset.univ : Finset (Verts n)).image (fun v : Verts n => (v, j)) ⊆ cellsOf n k j := by
    intro y hy
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  rw [Finset.Subset.antisymm e1 e2, Finset.card_image_iff.mpr (fun _ _ _ _ hv => congrArg Prod.fst hv)]
  have huniv : ((Finset.univ : Finset (Verts n))).card = n := by
    show (Finset.univ : Finset (Verts n)).card = n
    simp
  rw [huniv]

/-! ### §2  The five cells of a labelled triangle -/

/-- **The cross of a labelled triangle**: the five `(vertex, colour)` cells it occupies
(`triPairs` of `Triangles.lean`). -/
abbrev cross {n k : ℕ} (c : Col n k) (u p q : Verts n) : Finset (Cell n k) := triPairs c u p q

/-- The **cherry colour** of a labelled triangle: the colour of its two centre edges. -/
def cherryCol {n k : ℕ} (c : Col n k) (u p q : Verts n) : Fin k := c s(u, p)

/-- The **leaf colour** of a labelled triangle: the colour of its opposite edge. -/
def leafCol {n k : ℕ} (c : Col n k) (u p q : Verts n) : Fin k := c s(p, q)

/-- A cross has five cells. -/
theorem card_cross {n k : ℕ} {c : Col n k} {u p q : Verts n} (h : LabTri c u p q) :
    (cross c u p q).card = 5 := card_triPairs_five h

/-- **THE FIVE CELLS OF A CROSS, ONE AT A TIME.**  A cell of the cross of `(u, p, q)` is one of the
five `(vertex, colour)` pairs of `Cover.card_triPairs_five`. -/
theorem mem_cross_cases' {n k : ℕ} {c : Col n k} {u p q : Verts n} {y : Cell n k}
    (h : y ∈ cross c u p q) :
    y = (u, cherryCol c u p q) ∨ y = (p, cherryCol c u p q) ∨ y = (q, cherryCol c u p q)
      ∨ y = (p, leafCol c u p q) ∨ y = (q, leafCol c u p q) := by
  simp only [cross, cherryCol, leafCol, triPairs, Finset.mem_insert, Finset.notMem_empty,
    false_or] at h
  rcases h with (h | h | h | h | h | h)
  · exact Or.inl (Prod.ext_iff.mpr ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩)
  · exact Or.inr (Or.inl (Prod.ext_iff.mpr ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩))
  · exact Or.inr (Or.inr (Or.inl (Prod.ext_iff.mpr ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Prod.ext_iff.mpr ⟨congrArg Prod.fst h,
    congrArg Prod.snd h⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Prod.ext_iff.mpr ⟨congrArg Prod.fst h,
    congrArg Prod.snd h⟩))))
  · exact False.elim h

/-- **THE COLOUR OF A CELL OF A CROSS** is the cherry colour or the leaf colour of the triangle. -/
theorem mem_cross_col' {n k : ℕ} {c : Col n k} {u p q : Verts n} {y : Cell n k}
    (h : y ∈ cross c u p q) :
    y.2 = cherryCol c u p q ∨ y.2 = leafCol c u p q := by
  rcases mem_cross_cases' h with h1 | h1 | h1 | h1 | h1
  · exact Or.inl (congrArg Prod.snd h1)
  · exact Or.inl (congrArg Prod.snd h1)
  · exact Or.inl (congrArg Prod.snd h1)
  · exact Or.inr (congrArg Prod.snd h1)
  · exact Or.inr (congrArg Prod.snd h1)

/-- The five cells of the cross of `(u, p, q)`, for a cell `(x, j)`. -/
theorem mem_cross_cases {n k : ℕ} {c : Col n k} {u p q : Verts n} {x : Verts n} {j : Fin k}
    (h : (x, j) ∈ cross c u p q) :
    (x = u ∧ j = cherryCol c u p q) ∨ (x = p ∧ j = cherryCol c u p q)
      ∨ (x = q ∧ j = cherryCol c u p q) ∨ (x = p ∧ j = leafCol c u p q)
      ∨ (x = q ∧ j = leafCol c u p q) := by
  rcases mem_cross_cases' h with h1 | h1 | h1 | h1 | h1
  · exact Or.inl ⟨congrArg Prod.fst h1, congrArg Prod.snd h1⟩
  · exact Or.inr (Or.inl ⟨congrArg Prod.fst h1, congrArg Prod.snd h1⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨congrArg Prod.fst h1, congrArg Prod.snd h1⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨congrArg Prod.fst h1, congrArg Prod.snd h1⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨congrArg Prod.fst h1, congrArg Prod.snd h1⟩)))

/-- **THE COLOUR OF A CELL OF A CROSS** (pointwise form). -/
theorem mem_cross_col {n k : ℕ} {c : Col n k} {u p q : Verts n} {x : Verts n} {j : Fin k}
    (h : (x, j) ∈ cross c u p q) :
    j = cherryCol c u p q ∨ j = leafCol c u p q := mem_cross_col' h

/-- **THE CELL COUNT OF A CROSS.**  A labelled triangle covers three cells of its cherry colour,
two of its leaf colour and none of any other colour: the content of `Cover.card_triPairs_five`,
read colour by colour. -/
theorem card_col_cross {n k : ℕ} {c : Col n k} {u p q : Verts n} {j : Fin k}
    (h : LabTri c u p q) :
    ((cross c u p q).filter (fun x : Cell n k => x.2 = j)).card
      = (if cherryCol c u p q = j then 3 else 0) + (if leafCol c u p q = j then 2 else 0) := by
  classical
  have hne1 : u ≠ p := fun e => (LabTri.ne h).1 e
  have hne2 : u ≠ q := fun e => (LabTri.ne h).2.1 e
  have hne3 : p ≠ q := fun e => (LabTri.ne h).2.2 e
  have hne1' : p ≠ u := Ne.symm hne1
  have hne2' : q ≠ u := Ne.symm hne2
  have hne3' : q ≠ p := Ne.symm hne3
  have hcol : cherryCol c u p q ≠ leafCol c u p q := h.2.2.2.2
  have hA : (u, cherryCol c u p q) ≠ (p, cherryCol c u p q) := by
    simp [Prod.mk.injEq, hne1]
  have hB : (u, cherryCol c u p q) ≠ (q, cherryCol c u p q) := by
    simp [Prod.mk.injEq, hne2]
  have hC : (u, cherryCol c u p q) ≠ (p, leafCol c u p q) := by
    simp [Prod.mk.injEq, hne1, hcol]
  have hD : (u, cherryCol c u p q) ≠ (q, leafCol c u p q) := by
    simp [Prod.mk.injEq, hne2, hcol]
  have hE : (p, cherryCol c u p q) ≠ (q, cherryCol c u p q) := by
    simp [Prod.mk.injEq, hne3]
  have hF : (p, cherryCol c u p q) ≠ (p, leafCol c u p q) := by
    simp [Prod.mk.injEq, hcol]
  have hG : (p, cherryCol c u p q) ≠ (q, leafCol c u p q) := by
    simp [Prod.mk.injEq, hne3, hcol]
  have hH : (q, cherryCol c u p q) ≠ (p, leafCol c u p q) := by
    simp [Prod.mk.injEq, hne3, hcol]
  have hI : (q, cherryCol c u p q) ≠ (q, leafCol c u p q) := by
    simp [Prod.mk.injEq, hcol]
  rw [Finset.card_filter]
  have hexp : cross c u p q = insert (u, cherryCol c u p q)
      (insert (p, cherryCol c u p q) (insert (q, cherryCol c u p q)
        (insert (p, leafCol c u p q) (insert (q, leafCol c u p q)
          (∅ : Finset (Cell n k)))))) := by
    ext y
    simp [cross, cherryCol, leafCol, triPairs]
  rw [hexp]
  rw [Finset.sum_insert (by simp [hA, hB, hC, hD, hE, hF, hG, hH, hI, hne1', hne2', hne3']),
    Finset.sum_insert (by simp [hE, hF, hG, hI, hne3', hne3]),
    Finset.sum_insert (by simp [hE, hI, hne3', hne3]),
    Finset.sum_insert (by simp [hne3', hne3]),
    Finset.sum_insert (by simp)]
  simp only [Prod.snd]
  by_cases hc : cherryCol c u p q = j
  · have hnl : leafCol c u p q ≠ j := fun e => hcol (hc.trans e.symm)
    simp [hc, hnl]
  · by_cases hl : leafCol c u p q = j <;> simp [hc, hl]

/-! ### §3  Grid decompositions -/

/-- The union of the crosses of a family of triples. -/
def crossUnion {n k : ℕ} (c : Col n k) (T : Finset (Triple n k)) : Finset (Cell n k) :=
  T.biUnion (fun t => cross c t.1 t.2.1 t.2.2)

/-- **A FAMILY OF LABELLED TRIANGLES DECOMPOSES THE GRID**: every one of them is a labelled
triangle of `c`, their crosses are pairwise disjoint (the matching condition
`Triangles.PairFree`) and together they cover all `n · k` cells. -/
def Decomposes {n k : ℕ} (c : Col n k) (T : Finset (Triple n k)) : Prop :=
  (∀ t ∈ T, LabTri c t.1 t.2.1 t.2.2)
  ∧ (∀ t ∈ T, ∀ t' ∈ T, t ≠ t' → Disjoint (cross c t.1 t.2.1 t.2.2) (cross c t'.1 t'.2.1 t'.2.2))
  ∧ (crossUnion c T = grid n k)

/-- The cherry colour carried by a triple. -/
def triCherry {n k : ℕ} (c : Col n k) (t : Triple n k) : Fin k := cherryCol c t.1 t.2.1 t.2.2

/-- The leaf colour carried by a triple. -/
def triLeaf {n k : ℕ} (c : Col n k) (t : Triple n k) : Fin k := leafCol c t.1 t.2.1 t.2.2

/-- The triangles of the family whose cherry colour is `j`. -/
def cherryF {n k : ℕ} (c : Col n k) (T : Finset (Triple n k)) (j : Fin k) : Finset (Triple n k) :=
  T.filter (fun t => triCherry c t = j)

/-- The triangles of the family whose leaf colour is `j`. -/
def leafF {n k : ℕ} (c : Col n k) (T : Finset (Triple n k)) (j : Fin k) : Finset (Triple n k) :=
  T.filter (fun t => triLeaf c t = j)

/-- **THE PRICE OF A DECOMPOSITION**, read off the covers: the crosses of a family cover the grid,
so `5 · |T| = n · k`. -/
theorem card_eq_of_decomposes {n k : ℕ} {c : Col n k} {T : Finset (Triple n k)}
    (hD : Decomposes c T) : 5 * T.card = n * k := by
  classical
  have hcard : ∀ t : Triple n k, t ∈ T → (cross c t.1 t.2.1 t.2.2).card = 5 := by
    intro t ht; exact card_cross (hD.1 t ht)
  have hdj : (↑T : Set (Triple n k)).PairwiseDisjoint (fun t => cross c t.1 t.2.1 t.2.2) := by
    intro t ht t' ht' hne; exact hD.2.1 t ht t' ht' hne
  have h1 := Finset.card_biUnion hdj
  have hsum : (∑ t ∈ T, (cross c t.1 t.2.1 t.2.2).card) = 5 * T.card := by
    rw [Finset.sum_const_nat (fun t ht => hcard t ht)]
    omega
  calc 5 * T.card = ∑ t ∈ T, (cross c t.1 t.2.1 t.2.2).card := hsum.symm
    _ = (crossUnion c T).card := h1.symm
    _ = (grid n k).card := congrArg Finset.card hD.2.2
    _ = n * k := card_grid n k

/-- Counting a filter as a sum of indicators. -/
private theorem card_filter_sum {α : Type*} [DecidableEq α] (s : Finset α) (P : α → Prop)
    [DecidablePred P] : (s.filter P).card = ∑ y ∈ s, (if P y then 1 else 0) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => by_cases hP : P a <;> simp [hP, ih]

/-- Summing an indicator over a finset. -/
private lemma sum_ite_card {α : Type*} [DecidableEq α] (s : Finset α) (P : α → Prop)
    [DecidablePred P] (m : ℕ) : (∑ x ∈ s, (if P x then m else 0)) = m * (s.filter P).card := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      by_cases hP : P a
      · simp only [Finset.sum_insert ha, ih, Finset.filter_insert, hP, if_true, add_mul, zero_add]
        rw [Finset.card_insert_of_notMem (by simp [ha])]
        ring
      · simp only [Finset.sum_insert ha, ih, Finset.filter_insert, hP, if_false]
        ring

/-- **THE CELL EQUATION.**  If a family of labelled triangles decomposes the `n × k` grid then,
for every colour `j`, the `n` cells of colour `j` are covered exactly once, three by every triangle
whose cherry colour is `j` and two by every triangle whose leaf colour is `j`; hence

    `3 · |{t : triCherry t = j}| + 2 · |{t : triLeaf t = j}| = n`. -/
theorem cellCount {n k : ℕ} {c : Col n k} {T : Finset (Triple n k)} (hD : Decomposes c T)
    (j : Fin k) : 3 * (cherryF c T j).card + 2 * (leafF c T j).card = n := by
  classical
  have hcov : ∀ y : Cell n k, y ∈ grid n k → y.2 = j → ∃ t ∈ T, y ∈ cross c t.1 t.2.1 t.2.2 := by
    intro y hymem hyj
    have hymem' : y ∈ crossUnion c T := by rw [hD.2.2]; exact hymem
    obtain ⟨t, ht, hmem⟩ := Finset.mem_biUnion.mp hymem'
    exact ⟨t, ht, hmem⟩
  have hdisj : ∀ t ∈ T, ∀ t' ∈ T, t ≠ t' →
      Disjoint ((cross c t.1 t.2.1 t.2.2).filter (fun x : Cell n k => x.2 = j))
        ((cross c t'.1 t'.2.1 t'.2.2).filter (fun x : Cell n k => x.2 = j)) := by
    intro t ht t' ht' hne
    refine Finset.disjoint_left.mpr fun y hy hy' => ?_
    exact Finset.disjoint_left.mp (hD.2.1 t ht t' ht' hne) (Finset.mem_filter.mp hy).1
      (Finset.mem_filter.mp hy').1
  have hunion : T.biUnion (fun t => (cross c t.1 t.2.1 t.2.2).filter (fun x : Cell n k => x.2 = j))
      = cellsOf n k j := by
    ext y
    constructor
    · intro hy
      obtain ⟨t, ht, hmem⟩ := Finset.mem_biUnion.mp hy
      exact Finset.mem_filter.mpr ⟨mem_grid, (Finset.mem_filter.mp hmem).2⟩
    · intro hy
      obtain ⟨hymem, hyj⟩ := Finset.mem_filter.mp hy
      obtain ⟨t, ht, hymem'⟩ := hcov y hymem hyj
      exact Finset.mem_biUnion.mpr ⟨t, ht, Finset.mem_filter.mpr ⟨hymem', hyj⟩⟩
  have hcard1 : ∀ t ∈ T, ((cross c t.1 t.2.1 t.2.2).filter (fun x : Cell n k => x.2 = j)).card
      = (if triCherry c t = j then 3 else 0) + (if triLeaf c t = j then 2 else 0) := by
    intro t ht; exact card_col_cross (hD.1 t ht)
  calc 3 * (cherryF c T j).card + 2 * (leafF c T j).card
      = ∑ t ∈ T, ((if triCherry c t = j then 3 else 0)
          + (if triLeaf c t = j then 2 else 0)) := by
        rw [Finset.sum_add_distrib, sum_ite_card, sum_ite_card]
        rfl
    _ = ∑ t ∈ T, ((cross c t.1 t.2.1 t.2.2).filter (fun x : Cell n k => x.2 = j)).card :=
      Finset.sum_congr rfl fun t ht => (hcard1 t ht).symm
    _ = (T.biUnion (fun t => (cross c t.1 t.2.1 t.2.2).filter
          (fun x : Cell n k => x.2 = j))).card :=
      (Finset.card_biUnion (fun t ht t' ht' hne => hdisj t ht t' ht' hne)).symm
    _ = (cellsOf n k j).card := by rw [hunion]
    _ = n := card_cellsOf n k j

/-! ### §4  The obstruction at `n = 7` -/

/-- **THE CELL EQUATION AT `n = 7`.**  If a family of labelled triangles decomposes the `7 × 5`
grid then every colour is the cherry colour of exactly one triangle and the leaf colour of exactly
two — and, by `Grid.card_eq_five`, there are exactly five triangles. -/
theorem cellCount_seven {c : Col 7 5} {T : Finset (Triple 7 5)} (hD : Decomposes c T) (j : Fin 5) :
    (cherryF c T j).card = 1 ∧ (leafF c T j).card = 2 := by
  have he := cellCount hD j
  omega

/-- **THE TRIANGLES ARE COUNTED BY THEIR CHERRY COLOUR.**  Every triangle has exactly one cherry
colour, so the family is partitioned into the `cherryF c T j`. -/
theorem card_eq_sum_cherry {n k : ℕ} {c : Col n k} (T : Finset (Triple n k)) :
    T.card = ∑ j : Fin k, (cherryF c T j).card := by
  classical
  calc T.card = ∑ t ∈ T, 1 := Finset.card_eq_sum_ones T
    _ = ∑ t ∈ T, (∑ j : Fin k, (if triCherry c t = j then 1 else 0)) := by
      apply Finset.sum_congr rfl; intro t _
      have hone : (∑ j : Fin k, (if triCherry c t = j then 1 else 0)) = 1 := by
        rw [Finset.sum_ite_eq]
        simp
      rw [hone]
    _ = ∑ j : Fin k, (∑ t ∈ T, (if triCherry c t = j then 1 else 0)) := by
      exact Finset.sum_comm
    _ = ∑ j : Fin k, (cherryF c T j).card := by
      apply Finset.sum_congr rfl; intro j _
      exact (card_filter_sum T (fun t => triCherry c t = j)).symm

/-- **NO DECOMPOSITION OF THE `7 × 5` GRID HAS SEVEN TRIANGLES.**  The cell equation
`3 a_j + 2 b_j = 7` forces `a_j = 1` for each of the five colours, hence `|T| = 5`: this is the
arithmetic obstruction which rules out the tight colouring of `K_7`. -/
theorem card_eq_five {c : Col 7 5} {T : Finset (Triple 7 5)} (hD : Decomposes c T) :
    T.card = 5 := by
  rw [card_eq_sum_cherry T, Finset.sum_const_nat (fun j _hj => (cellCount_seven hD j).1)]
  norm_num

/-! ### §5  The tight colouring decomposes the grid -/

/-- The two leaves of the two-edge path centred at `v` of colour `i` — two distinct `i`-neighbours
of `v`, in that order. -/
noncomputable def leaves {n k : ℕ} (c : Col n k) (i : Fin k) (v : Verts n) : Verts n × Verts n :=
  if hv : v ∈ twoA c i then
    ((Finset.card_eq_two.mp (card_twoA i hv)).choose,
      (Finset.card_eq_two.mp (card_twoA i hv)).choose_spec.choose)
  else (v, v)

/-- The two leaves are distinct and they are exactly the colour-`i` neighbours of the centre. -/
theorem leaves_eq {n k : ℕ} {c : Col n k} {i : Fin k} {v : Verts n} (hv : v ∈ twoA c i) :
    (leaves c i v).1 ≠ (leaves c i v).2
      ∧ Nbrs c i v = {(leaves c i v).1, (leaves c i v).2} := by
  have hXne : (Finset.card_eq_two.mp (card_twoA i hv)).choose
      ≠ (Finset.card_eq_two.mp (card_twoA i hv)).choose_spec.choose :=
    (Finset.card_eq_two.mp (card_twoA i hv)).choose_spec.choose_spec.1
  have hXN : Nbrs c i v = {(Finset.card_eq_two.mp (card_twoA i hv)).choose,
      (Finset.card_eq_two.mp (card_twoA i hv)).choose_spec.choose} :=
    (Finset.card_eq_two.mp (card_twoA i hv)).choose_spec.choose_spec.2
  rw [leaves, dif_pos hv]
  exact ⟨hXne, hXN⟩

/-- The labelled triangle of the two-edge path centred at `v` of colour `i`. -/
noncomputable def cherryTri {n k : ℕ} (c : Col n k) (B : Fin k × Verts n) : Triple n k :=
  (B.2, (leaves c B.1 B.2).1, (leaves c B.1 B.2).2)

/-- **THE FAMILY OF LABELLED TRIANGLES OF A COLOURING**: one per two-edge path (`cherryFinset` of
`Cherry.lean` is the set of `(colour, centre)` pairs with two neighbours). -/
noncomputable def TriFamilyOf {n k : ℕ} (c : Col n k) : Finset (Triple n k) :=
  (cherryFinset c).image (cherryTri c)

/-- **EVERY TRIANGLE OF THE FAMILY IS A LABELLED TRIANGLE** — one per two-edge path, with its
cherry colour the colour of the path and its leaf colour the colour of the edge between the leaves
(`Cherry.cherry_leaf_pair`). -/
theorem mem_LabTri {n k : ℕ} {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) {t : Triple n k}
    (ht : t ∈ TriFamilyOf c) : LabTri c t.1 t.2.1 t.2.2 := by
  rw [TriFamilyOf, Finset.mem_image] at ht
  obtain ⟨B, hB, ht⟩ := ht
  subst ht
  obtain ⟨hne, hN⟩ := leaves_eq (twoA_of_mem_cherryFinset hB)
  have hNa : (leaves c B.1 B.2).1 ∈ Nbrs c B.1 B.2 := by rw [hN]; simp
  have hNb : (leaves c B.1 B.2).2 ∈ Nbrs c B.1 B.2 := by rw [hN]; simp
  have hv1 : (leaves c B.1 B.2).1 ≠ B.2 := (mem_Nbrs.mp hNa).1
  have hv2 : (leaves c B.1 B.2).2 ≠ B.2 := (mem_Nbrs.mp hNb).1
  have hcol1 : c s(B.2, (leaves c B.1 B.2).1) = B.1 := (mem_Nbrs.mp hNa).2
  have hcol2 : c s(B.2, (leaves c B.1 B.2).2) = B.1 := (mem_Nbrs.mp hNb).2
  have hleaf : c s(B.2, (leaves c B.1 B.2).1)
      ≠ c s((leaves c B.1 B.2).1, (leaves c B.1 B.2).2) := by
    have := (cherry_leaf_pair hc hn (twoA_of_mem_cherryFinset hB) hNa hNb hne).1
    exact fun h => this (h.symm.trans hcol1)
  refine ⟨hv1.symm, hv2.symm, hne, ?_, hleaf⟩
  calc c s(B.2, (leaves c B.1 B.2).1) = B.1 := hcol1
    _ = c s(B.2, (leaves c B.1 B.2).2) := hcol2.symm

/-- The map from a two-edge path to its labelled triangle is injective. -/
theorem injective_cherryTri {n k : ℕ} {c : Col n k} {B B' : Fin k × Verts n}
    (hB : B ∈ cherryFinset c) (hB' : B' ∈ cherryFinset c) (h : cherryTri c B = cherryTri c B') :
    B = B' := by
  have hcent : B.2 = B'.2 := congrArg (fun z : Triple n k => z.1) h
  have hla : (leaves c B.1 B.2).1 = (leaves c B'.1 B'.2).1 :=
    congrArg (fun z : Triple n k => (z.2).1) h
  have hlb : (leaves c B.1 B.2).2 = (leaves c B'.1 B'.2).2 :=
    congrArg (fun z : Triple n k => (z.2).2) h
  obtain ⟨hneB, hNB⟩ := leaves_eq (twoA_of_mem_cherryFinset hB)
  obtain ⟨hneB', hNB'⟩ := leaves_eq (twoA_of_mem_cherryFinset hB')
  have hmemA : (leaves c B.1 B.2).1 ∈ Nbrs c B.1 B.2 := by rw [hNB]; simp
  have hmemA' : (leaves c B'.1 B'.2).1 ∈ Nbrs c B'.1 B'.2 := by rw [hNB']; simp
  refine Prod.ext ?_ hcent
  calc B.1 = c s(B.2, (leaves c B.1 B.2).1) := (mem_Nbrs.mp hmemA).2.symm
    _ = c s(B'.2, (leaves c B'.1 B'.2).1) := by rw [hla, hcent]
    _ = B'.1 := (mem_Nbrs.mp hmemA').2

/-- **THE FAMILY HAS ONE TRIANGLE PER TWO-EDGE PATH.** -/
theorem card_TriFamilyOf {n k : ℕ} {c : Col n k} : (TriFamilyOf c).card = Paths c := by
  have hinj : Set.InjOn (cherryTri c) ((↑(cherryFinset c) : Set (Fin k × Verts n))) := by
    intro B hB B' hB' h
    exact injective_cherryTri hB hB' h
  rw [TriFamilyOf, Finset.card_image_iff.mpr hinj, card_cherryFinset]

/-- **TWO TRIANGLES OF THE FAMILY WITH THE SAME VERTEX SET ARE THE SAME TRIANGLE.** -/
theorem inj_triVerts {n k : ℕ} {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    {t t' : Triple n k} (ht : t ∈ TriFamilyOf c) (ht' : t' ∈ TriFamilyOf c)
    (h : triVerts t.1 t.2.1 t.2.2 = triVerts t'.1 t'.2.1 t'.2.2) : t = t' := by
  obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp ht
  obtain ⟨B', hB', rfl⟩ := Finset.mem_image.mp ht'
  have hpath : triVerts B.2 (leaves c B.1 B.2).1 (leaves c B.1 B.2).2 = pathSet c B.1 B.2 := by
    obtain ⟨hneB, hN⟩ := leaves_eq (twoA_of_mem_cherryFinset hB)
    ext y
    simp [triVerts, pathSet, hN]
  have hpath' : triVerts B'.2 (leaves c B'.1 B'.2).1 (leaves c B'.1 B'.2).2
      = pathSet c B'.1 B'.2 := by
    obtain ⟨hneB', hN'⟩ := leaves_eq (twoA_of_mem_cherryFinset hB')
    ext y
    simp [triVerts, pathSet, hN']
  have heq : pathSet c B.1 B.2 = pathSet c B'.1 B'.2 := hpath.symm.trans (h.trans hpath')
  have h2 : 2 ≤ (pathSet c B.1 B.2).card := by
    have := card_pathSet (twoA_of_mem_cherryFinset hB)
    omega
  obtain ⟨hi, hv⟩ := pathSet_sub_inter hc hn (twoA_of_mem_cherryFinset hB)
    (twoA_of_mem_cherryFinset hB') (Finset.Subset.rfl) (heq ▸ Finset.Subset.rfl) h2
  have hBB : B = B' := Prod.ext hi hv
  exact hBB ▸ rfl

/-- **IN THE EXTREMAL CASE THE COLOURING DECOMPOSES THE GRID.**  If an admissible colouring of `K_n`
(`n ≥ 4`) attains the counting bound, i.e. `6 k = 5 (n - 1)`, then the family of its labelled
triangles (`Grid.TriFamilyOf`, one per two-edge path) *decomposes* the `n × k` grid: the crosses are
pairwise disjoint because two triangles sharing a `(vertex, colour)` pair are the same triangle
(`Cover.triVerts_eq_of_mem_triPairs`), and they cover the grid because there are `5 · n(n-1)/6 = n k`
cells in them and no more than `n k` cells altogether.

Together with `Grid.card_eq_five` this is the **exact characterisation of the extremal case**: an
admissible colouring of `K_n` attains `5(n-1)/6` colours only if the corresponding grid admits a
decomposition into five-cell crosses — which at `n = 7` is arithmetically impossible. -/
theorem decomposes_of_tight {n k : ℕ} {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (hk : 6 * k = 5 * (n - 1)) : Decomposes c (TriFamilyOf c) := by
  classical
  have h3 := tight_attained hc hn hk
  obtain ⟨hn6, hcard⟩ := tight_mod6 hc hn h3 hk
  refine ⟨fun t ht => mem_LabTri hc hn ht, ?_, ?_⟩
  · intro t ht t' ht' hne
    refine Finset.disjoint_left.mpr fun y hy hy' => ?_
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨B', hB', rfl⟩ := Finset.mem_image.mp ht'
    have hmem : y ∈ cross c B.2 (leaves c B.1 B.2).1 (leaves c B.1 B.2).2
        ∩ cross c B'.2 (leaves c B'.1 B'.2).1 (leaves c B'.1 B'.2).2 :=
      Finset.mem_inter.mpr ⟨hy, hy'⟩
    have heq := triVerts_eq_of_mem_triPairs hc (mem_LabTri hc hn (Finset.mem_image.mpr ⟨B, hB, rfl⟩))
      (mem_LabTri hc hn (Finset.mem_image.mpr ⟨B', hB', rfl⟩)) hmem
    exact hne (inj_triVerts hc hn (Finset.mem_image.mpr ⟨B, hB, rfl⟩)
      (Finset.mem_image.mpr ⟨B', hB', rfl⟩) heq)
  · have hdvd : (6 : ℕ) ∣ (n - 1) := by
      refine ⟨n / 6, ?_⟩
      have hdm := Nat.div_add_mod n 6
      rw [hn6] at hdm
      omega
    have hdvd' : (6 : ℕ) ∣ (n * (n - 1)) := by
      refine ⟨n * ((n - 1) / 6), ?_⟩
      have h := Nat.mul_div_cancel' hdvd
      calc n * (n - 1) = n * (6 * ((n - 1) / 6)) := congrArg (fun t => n * t) h.symm
        _ = 6 * (n * ((n - 1) / 6)) := by ring
    have h6 : 6 * ((n * (n - 1)) / 6) = n * (n - 1) := Nat.mul_div_cancel' hdvd'
    have hpaths : Paths c = n * (n - 1) / 6 := tight_paths hc hn h3
    have h6P : 6 * (TriFamilyOf c).card = n * (n - 1) := by
      calc 6 * (TriFamilyOf c).card = 6 * (n * (n - 1) / 6) := by rw [card_TriFamilyOf, hpaths]
        _ = n * (n - 1) := h6
    have h5 : 5 * (TriFamilyOf c).card = n * k := by
      have hkey : 6 * (5 * (TriFamilyOf c).card) = 6 * (n * k) := by
        calc 6 * (5 * (TriFamilyOf c).card) = 5 * (6 * (TriFamilyOf c).card) := by ring
          _ = 5 * (n * (n - 1)) := by rw [h6P]
          _ = 6 * (n * k) := by
            calc 5 * (n * (n - 1)) = n * (5 * (n - 1)) := by ring
              _ = n * (6 * k) := by rw [hk]
              _ = 6 * (n * k) := by ring
      exact Nat.eq_of_mul_eq_mul_left (by omega) hkey
    have hdj : ((↑(TriFamilyOf c) : Set (Triple n k))).PairwiseDisjoint
        (fun t => cross c t.1 t.2.1 t.2.2) := by
      intro t ht t' ht' hne
      refine Finset.disjoint_left.mpr fun y hy hy' => ?_
      exact hne (inj_triVerts hc hn ht ht' (triVerts_eq_of_mem_triPairs hc (mem_LabTri hc hn ht)
        (mem_LabTri hc hn ht') (Finset.mem_inter.mpr ⟨hy, hy'⟩)))
    have hcard : (crossUnion c (TriFamilyOf c)).card = 5 * (TriFamilyOf c).card := by
      calc (crossUnion c (TriFamilyOf c)).card
          = ∑ t ∈ (TriFamilyOf c), (cross c t.1 t.2.1 t.2.2).card :=
            Finset.card_biUnion hdj
        _ = 5 * (TriFamilyOf c).card := by
          rw [Finset.sum_const_nat (fun t ht => card_cross (mem_LabTri hc hn ht))]
          omega
    have h2 : (grid n k).card = n * k := card_grid n k
    have h3 : (crossUnion c (TriFamilyOf c)).card = n * k := by rw [hcard, h5]
    have hle : (grid n k).card ≤ (crossUnion c (TriFamilyOf c)).card := by
      rw [h2, h3]
    exact Finset.eq_of_subset_of_card_le (by intro y hy; exact mem_grid) hle

/-- **THE TIGHT COLOURING OF `K_n` HAS `n (n - 1) / 6` TRIANGLES** — equivalently, the counting
lemma `Cherry.three_mul_paths_le_edges` is an equality. -/
theorem six_mul_card_TriFamilyOf {n k : ℕ} {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (hk : 6 * k = 5 * (n - 1)) : 6 * (TriFamilyOf c).card = n * (n - 1) := by
  have h3 := tight_attained hc hn hk
  obtain ⟨hn6, hcard⟩ := tight_mod6 hc hn h3 hk
  have hdvd : (6 : ℕ) ∣ (n - 1) := by
    refine ⟨n / 6, ?_⟩
    have hdm := Nat.div_add_mod n 6
    rw [hn6] at hdm
    omega
  have hdvd' : (6 : ℕ) ∣ (n * (n - 1)) := by
    refine ⟨n * ((n - 1) / 6), ?_⟩
    have h := Nat.mul_div_cancel' hdvd
    calc n * (n - 1) = n * (6 * ((n - 1) / 6)) := congrArg (fun t => n * t) h.symm
      _ = 6 * (n * ((n - 1) / 6)) := by ring
  have h6 : 6 * ((n * (n - 1)) / 6) = n * (n - 1) := Nat.mul_div_cancel' hdvd'
  have hpaths : Paths c = n * (n - 1) / 6 := tight_paths hc hn h3
  calc 6 * (TriFamilyOf c).card = 6 * (n * (n - 1) / 6) := by rw [card_TriFamilyOf, hpaths]
    _ = n * (n - 1) := h6

/-! ### §6  `f(7,4,5) ≥ 6` — the sharp bound is not attained at `n = 7` -/

/-- **NO ADMISSIBLE COLOURING OF `K_7` USES FIVE COLOURS** — the sharpness statement of the
catalog lower bound `5(n-1)/6` fails at `n = 7`. -/
theorem no_five_colours {c : Col 7 5} (hc : Admissible c) : False := by
  have hD : Decomposes c (TriFamilyOf c) := decomposes_of_tight hc (by omega) rfl
  have h7 : (TriFamilyOf c).card = 7 := by
    have h6 := six_mul_card_TriFamilyOf hc (by omega) rfl
    omega
  exact absurd (card_eq_five hD) (by omega)

/-- **`EG 7 ≥ 6`.**  The counting bound of `Cherry.five_sixth_lower` forces `EG 7 ≥ 5`; the
tightness theory plus `Grid.card_eq_five` rule out `EG 7 = 5`, so the extremal value of
`f(n,4,5)` at `n = 7` is strictly larger than the lower bound `5(n-1)/6 = 5` of
`Tables.EG_ge_ceil_five_sixth` — the first order at which the tightness theory of round 13 is
refuted, and the first *proved* value bound of this development sharper than `⌈5(n-1)/6⌉`. -/

theorem eg_seven_ge_six : 6 ≤ EG 7 := by
  by_contra hcon
  have hfive := EG_admissible 7
  by_cases hEq : EG 7 = 5
  · rw [hEq] at hfive
    obtain ⟨c, hc⟩ := hfive
    exact no_five_colours hc
  · obtain ⟨c, hc⟩ := hfive
    have := five_sixth_lower hc (by omega)
    omega

end Grid
end JSP140
