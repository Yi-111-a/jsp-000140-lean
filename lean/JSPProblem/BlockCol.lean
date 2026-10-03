import JSPProblem.Block
import JSPProblem.Cover
import JSPProblem.Apex
import JSPProblem.Strict

/-!
# JSP-000140 — the `(2,1)`-block colouring of a Steiner triple system, **as Lean data**

Rounds 49 and 50 built the *family side* of the construction (`Block.lean`: the census of a Steiner
triple system, the first explicit certified `STS(13)`, the exact price `n * k = 5 * Paths + Isolated`
of a decomposition colouring, and the quantisation `k = 5(n-1)/6 + t`).  Round 55 added the *second
order* of the necessity side (`Apex.lean`: the price list at the apexes).  Both rounds recorded the
same gap, and this file closes it:

> **The `(2,1)`-block colouring itself was never written down.**  `Block.decomposition_eq` prices a
> "decomposition colouring" abstractly; `Rigidity.tight_pathFinset_is_STS` extracts a Steiner triple
> system from an extremal colouring; but nowhere in `JSPProblem/` is there a *function* turning a
> triangle decomposition plus a centre and two colours per block into an edge colouring of `K_n`.
> Consequently nothing could be *searched* in the form the papers build, and the design conditions
> that round 55 had to impose by hand in `discovery/JSP-000140/fano_s1s2.py` (apex-avoidance and
> leaf-isolation) were never *proved* to follow from admissibility.

Here it is, `JSP140.TwoOne`, with the following results.

## §1 — the colouring

* `TwoOne` — the data: a triangle decomposition `bl : Fin m → Finset (Verts n)` (`cover`, `uniq`,
  `card_three`), a centre `ctr i` and two **distinct** colours `pc i ≠ qc i` per block.
* `TwoOne.col` — **the colouring**: the edge of a block that touches the centre gets `pc i`, the
  opposite edge gets `qc i`.
* `TwoOne.col_touch` / `TwoOne.col_notouch` — the two cases, *unconditionally*.

## §2 — every block is a labelled triangle of the colouring

* **`TwoOne.labTri` — `LabTri (TwoOne.col C) (ctr i) a b`**: the block is a labelled triangle of the
  colouring, with `pc i` on the two edges at the apex and `qc i` on the opposite edge.  This is the
  bridge between `Block.lean` (the decomposition as data) and `Triangles.lean` / `Cover.lean` (the
  construction interface of arXiv:2208.12563 §4): the `(a, a, b)` pattern of that paper is exactly
  `TwoOne.labTri`.
* `TwoOne.triVerts_eq` — the three vertices of that labelled triangle are the block.

## §3 — the two design conditions are consequences of admissibility

The exhaustive search of round 55 (`fano_s1s2.py`) had to impose *by hand*, on the centre/colour
table of the blocks:

* **apex-avoidance** — the apex has no edge of the leaf colour, and
* **leaf-isolation** — the two leaves have no other edge of the leaf colour.

Both are theorems here, and they hold for **every** `(2,1)`-block colouring, because they hold for
every labelled triangle of an admissible colouring (`apex_zeroA`,
`nb_eq_singleton_of_cherry`):

* **`TwoOne.apex_zero` — `ctr i ∈ zeroA (col C) (qc i)`**: `apex_zeroA` applied to
  `TwoOne.labTri`.  **So the `(2,1)`-block family satisfies the apex-avoidance condition
  automatically** — the constraint the search imposed is not an extra requirement.
* **`TwoOne.leaf_isolated` — `nb (col C) (qc i) a univ = {b}`** for the two leaves: the second
  condition, likewise free, together with `qc i ≠ pc i`.
* **`TwoOne.centre_twoA` — `ctr i ∈ twoA (col C) (pc i)`**: the block really is a two-edge path of
  the colouring, so the decomposition *is* part of the path structure of the colouring.

## §4 — the price: **the construction cannot beat `5/6`**

* **`TwoOne.paths_neq` / `TwoOne.paths_ge` — `Paths (col C) ≥ m`**: the `m` blocks give `m` *distinct*
  two-edge paths.  Two blocks cannot share both their centre and their "twice" colour, for then the
  centre would carry four edges of one colour, against `Counting.nb_card_le_two`.
* **`TwoOne.price` — `5 * m ≤ n * k`**: combining the above with `global_identity` and
  `paths_le`.
* **`TwoOne.paths_eq_of_sts` / `TwoOne.price_exact`** — for a Steiner triple system the two-edge
  paths of the colouring are exactly the blocks, and then `n * k = 5 * m + Isolated (col C)`, i.e.
  `k = 5(n-1)/6 + Isolated / n`.  This is `Block.decomposition_eq` for the explicit colouring.
* **`TwoOne.recipe` — `Isolated (col C) = n → 6 * EG n ≤ 5 * (n-1) + 6`**, i.e. **what a search for
  the sharp constant has to find**: an admissible `(2,1)`-block colouring of some Steiner triple
  system with exactly `n` missed `(vertex, colour)` slots.  At `n = 13` that is `k = 11`, which with
  `Strict.EG_thirteen_ge_eleven` would settle `f(13,4,5) = 11` — the first order at which
  `f(n,4,5) = 5n/6 + 1/6`.
* `TwoOne.decomposition_gap` — the family never attains the counting bound.
-/

set_option linter.unusedVariables false

namespace JSP140

variable {n k : ℕ}

/-! ### §1  `TwoOne`: the `(2,1)`-block colouring as data -/

/-- **THE DATA OF A `(2,1)`-BLOCK COLOURING OF `K_n`.**

`bl : Fin m → Finset (Verts n)` is a triangle decomposition of `K_n` (`cover`: every edge lies in
some block, `uniq`: in exactly one, `card_three`: every block has three vertices), and each block
`bl i` carries a **centre** `ctr i` and two **distinct** colours `pc i ≠ qc i`: the two edges of the
block that meet at the centre get `pc i` and the opposite edge gets `qc i`.  This is the pattern
`(a, a, b)`, `a ≠ b`, of arXiv:2208.12563 §4 — the `(2,1)`-block colouring of `Block.lean`. -/
structure TwoOne (n k m : ℕ) where
  /-- the palette is nonempty, so that `Fin k` can be summed over -/
  hk : NeZero k
  /-- the `m` blocks -/
  bl : Fin m → Finset (Verts n)
  /-- every block is a triangle -/
  card_three : ∀ i, (bl i).card = 3
  /-- the blocks cover every edge -/
  cover : ∀ e : Sym2 (Verts n), OffDiag e → ∃ i, e ∈ edgeFinset (bl i)
  /-- the blocks are edge-disjoint -/
  uniq : ∀ (e : Sym2 (Verts n)) (i j : Fin m), e ∈ edgeFinset (bl i) → e ∈ edgeFinset (bl j) →
    i = j
  /-- the centre of each block -/
  ctr : Fin m → Verts n
  /-- it is one of the three vertices of the block -/
  ctr_mem : ∀ i, ctr i ∈ bl i
  /-- the colour used on the two edges at the centre ("two") -/
  pc : Fin m → Fin k
  /-- the colour used on the opposite edge ("one") -/
  qc : Fin m → Fin k
  /-- the two colours differ -/
  pc_ne : ∀ i, pc i ≠ qc i

/-- The colour of the *ordered* pair `{a, b}`: the (unique) block containing `s(a, b)` gives `pc i`
if `a` or `b` is the centre of that block, and `qc i` otherwise. -/
noncomputable def TwoOne.col' (C : TwoOne n k m) (a b : Verts n) : Fin k := by
  letI := C.hk
  exact ∑ i : Fin m, if s(a, b) ∈ edgeFinset (C.bl i) then
      (if a = C.ctr i ∨ b = C.ctr i then C.pc i else C.qc i) else 0

theorem TwoOne.col'_swap (C : TwoOne n k m) (a b : Verts n) : C.col' a b = C.col' b a := by
  letI := C.hk
  unfold TwoOne.col'
  rw [Sym2.eq_swap]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h1 : s(b, a) ∈ edgeFinset (C.bl i)
  · rw [if_pos h1, if_pos h1]
    by_cases h2 : a = C.ctr i ∨ b = C.ctr i
    · rw [if_pos h2, if_pos (or_comm.mpr h2)]
    · rw [if_neg h2, if_neg (fun hh => h2 (or_comm.mpr hh))]
  · rw [if_neg h1, if_neg h1]

/-- **THE `(2,1)`-BLOCK COLOURING.**  The edge of the block `i` that touches the centre gets `pc i`;
the opposite edge of the block gets `qc i`.  `uniq` says at most one block contains a given edge, so
the sum has a single nonzero term; a loop (which is not an edge of `K_n`) is in no block, so the
value on a loop is `0` and the definition is total. -/
noncomputable def TwoOne.col (C : TwoOne n k m) : Col n k :=
  Sym2.lift ⟨TwoOne.col' C, fun a b => C.col'_swap a b⟩

/-- **The colouring, spelled out on an ordered pair.** -/
theorem TwoOne.col_eq (C : TwoOne n k m) (a b : Verts n) : C.col s(a, b) = C.col' a b := by
  letI := C.hk
  rfl

/-- **The colouring on the edges of a block.** -/
theorem TwoOne.col_of_mem (C : TwoOne n k m) {i : Fin m} {a b : Verts n} (hab : a ≠ b)
    (hi : s(a, b) ∈ edgeFinset (C.bl i)) :
    C.col s(a, b) = if a = C.ctr i ∨ b = C.ctr i then C.pc i else C.qc i := by
  letI := C.hk
  rw [C.col_eq a b]
  unfold TwoOne.col'
  rw [Finset.sum_eq_single i ?_ ?_]
  · rw [if_pos hi]
  · intro j _ hjne
    rw [if_neg (fun h => absurd (C.uniq s(a, b) j i h hi) hjne)]
  · simp

/-- **An edge of the block through the centre gets the "twice" colour `pc i`.** -/
theorem TwoOne.col_touch (C : TwoOne n k m) {i : Fin m} {a b : Verts n} (hab : a ≠ b)
    (hm1 : a ∈ C.bl i) (hm2 : b ∈ C.bl i) (ha : a = C.ctr i) :
    C.col s(a, b) = C.pc i := by
  rw [C.col_of_mem hab (mem_edgeFinset_mk hm1 hm2 hab), if_pos (Or.inl ha)]

/-- **An edge of the block avoiding the centre gets the "once" colour `qc i`.** -/
theorem TwoOne.col_notouch (C : TwoOne n k m) {i : Fin m} {a b : Verts n} (hab : a ≠ b)
    (hm1 : a ∈ C.bl i) (hm2 : b ∈ C.bl i) (ha : a ≠ C.ctr i) (hb : b ≠ C.ctr i) :
    C.col s(a, b) = C.qc i := by
  rw [C.col_of_mem hab (mem_edgeFinset_mk hm1 hm2 hab)]
  rw [if_neg (fun hh => hh.elim ha hb)]

/-- **The colour of an edge from the centre of a block to one of its leaves.** -/
theorem TwoOne.col_ctr_leaf (C : TwoOne n k m) {i : Fin m} {a b : Verts n} (hab : a ≠ b)
    (hctr : C.ctr i ∈ C.bl i) (hain : a ∈ C.bl i) (hane : a ≠ C.ctr i) :
    C.col s(C.ctr i, a) = C.pc i :=
  C.col_touch (i := i) (a := C.ctr i) (b := a) (Ne.symm hane) hctr hain rfl

/-- A two-element finset has two distinct elements in it. -/
private theorem exists_two_mem {α : Type*} [DecidableEq α] (s : Finset α) (h : 2 ≤ s.card) :
    ∃ a b : α, a ∈ s ∧ b ∈ s ∧ a ≠ b := by
  by_contra hn
  have hle : s.card ≤ 1 := by
    refine Finset.card_le_one.mpr (fun a ha b hb => ?_)
    by_contra h
    exact hn (Exists.intro a (Exists.intro b (And.intro ha (And.intro hb h))))
  omega

/-- A two-element finset has two elements and they differ. -/
private theorem card_two {α : Type*} [DecidableEq α] {a b : α} (hab : a ≠ b) :
    (insert a (insert b ∅) : Finset α).card = 2 := by
  rw [Finset.card_insert_of_notMem (by simp [hab])]
  simp

/-- **The two vertices of the block `i` other than its centre.** -/
noncomputable def TwoOne.leaves (C : TwoOne n k m) (i : Fin m) : Finset (Verts n) :=
  (C.bl i).erase (C.ctr i)

theorem TwoOne.card_leaves (C : TwoOne n k m) (i : Fin m) : (C.leaves i).card = 2 := by
  have h3 := C.card_three i
  have hmem := C.ctr_mem i
  rw [TwoOne.leaves, Finset.card_erase_of_mem hmem]
  omega

theorem TwoOne.mem_leaves {C : TwoOne n k m} {i : Fin m} {v : Verts n} (h : v ∈ C.leaves i) :
    v ≠ C.ctr i ∧ v ∈ C.bl i := (Finset.mem_erase.mp h)

theorem TwoOne.leaves_pair (C : TwoOne n k m) (i : Fin m) :
    ∃ a b : Verts n, a ≠ b ∧ C.leaves i = insert a (insert b ∅) := by
  obtain ⟨a, b, hab, hm⟩ := Finset.card_eq_two.mp (C.card_leaves i)
  exact ⟨a, b, hab, hm⟩

theorem TwoOne.leaves_mem {C : TwoOne n k m} {i : Fin m} {a b : Verts n} (hab : a ≠ b)
    (hm : C.leaves i = insert a (insert b ∅)) :
    a ∈ C.bl i ∧ a ≠ C.ctr i ∧ b ∈ C.bl i ∧ b ≠ C.ctr i := by
  have hma : a ∈ C.leaves i := by
    rw [hm]
    exact Finset.mem_insert_self a _
  have hmb : b ∈ C.leaves i := by
    rw [hm]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_self b ∅)
  obtain ⟨hane, hain⟩ := C.mem_leaves hma
  obtain ⟨hbe, hbin⟩ := C.mem_leaves hmb
  exact ⟨hain, hane, hbin, hbe⟩

/-! ### §2  every block is a labelled triangle of the colouring -/

/-- **EVERY BLOCK OF A `(2,1)`-BLOCK COLOURING IS A LABELLED TRIANGLE OF THE COLOURING.**
The two edges at the centre `ctr i` carry `pc i`, the opposite edge `a b` carries `qc i ≠ pc i`:
the `(a, a, b)` pattern with `a ≠ b` of arXiv:2208.12563 §4, and a labelled triangle in the sense
of `Triangles.LabTri`.  No admissibility is needed: this is a statement about the data alone. -/
theorem TwoOne.labTri (C : TwoOne n k m) (i : Fin m) (a b : Verts n) (hab : a ≠ b)
    (hm : C.leaves i = insert a (insert b ∅)) : LabTri (C.col) (C.ctr i) a b := by
  obtain ⟨hain, hane, hbin, hbe⟩ := C.leaves_mem hab hm
  refine ⟨Ne.symm hane, Ne.symm hbe, hab, ?_, ?_⟩
  · rw [C.col_ctr_leaf hab (C.ctr_mem i) hain hane,
      C.col_ctr_leaf (a := b) (b := a) (Ne.symm hab) (C.ctr_mem i) hbin hbe]
  · rw [C.col_ctr_leaf hab (C.ctr_mem i) hain hane,
      C.col_notouch (i := i) hab hain hbin hane hbe]
    exact C.pc_ne i

/-- The three vertices of the labelled triangle of the block `i` are the block. -/
theorem TwoOne.triVerts_eq (C : TwoOne n k m) (i : Fin m) (a b : Verts n) (hab : a ≠ b)
    (hm : C.leaves i = insert a (insert b ∅)) : triVerts (C.ctr i) a b = C.bl i := by
  have hmem := C.ctr_mem i
  have hbl : insert (C.ctr i) (C.leaves i) = C.bl i := Finset.insert_erase hmem
  rw [← hbl]
  have key2 : triVerts (C.ctr i) a b = insert (C.ctr i) (insert a (insert b ∅)) := rfl
  rw [key2]
  exact congrArg (fun t : Finset (Verts n) => insert (C.ctr i) t) hm.symm

/-! ### §3  the two design conditions are consequences of admissibility -/

/-- **The centre of the block `i` is a two-edge-path centre of the colouring**: the block is a
cherry of colour `pc i`.  (`Cherry.cherryFinset` counts one element per such pair, which is what
makes `TwoOne.paths_ge` below a statement about *distinct* cherries.) -/
theorem TwoOne.centre_twoA (C : TwoOne n k m) (hc : Admissible (C.col)) (i : Fin m)
    (a b : Verts n) (hab : a ≠ b) (hm : C.leaves i = insert a (insert b ∅)) :
    C.ctr i ∈ twoA (C.col) (C.pc i) := by
  obtain ⟨hain, hane, hbin, hbe⟩ := C.leaves_mem hab hm
  have hla := C.col_ctr_leaf hab (C.ctr_mem i) hain hane
  have hlb := C.col_ctr_leaf (a := b) (b := a) (Ne.symm hab) (C.ctr_mem i) hbin hbe
  refine mem_twoA.mpr ?_
  have hsub : (insert a (insert b ∅) : Finset (Verts n))
      ⊆ nb (C.col) (C.pc i) (C.ctr i) (Finset.univ : Finset (Verts n)) := by
    intro v hv
    rcases Finset.mem_insert.mp hv with hv1 | hv2
    · rw [hv1]
      exact mem_nb.mpr ⟨hane, Finset.mem_univ _, hla⟩
    · rcases Finset.mem_insert.mp hv2 with hv3 | hv4
      · rw [hv3]
        exact mem_nb.mpr ⟨hbe, Finset.mem_univ _, hlb⟩
      · exact absurd hv4 (by simp)
  have hle := nb_card_le_two hc (C.pc i) (C.ctr i) (Finset.univ : Finset (Verts n))
  have h2 : 2 ≤ (nb (C.col) (C.pc i) (C.ctr i) (Finset.univ : Finset (Verts n))).card := by
    have hh := Finset.card_le_card hsub
    rwa [card_two hab] at hh
  omega

/-- **APEX-AVOIDANCE IS FREE FOR THE `(2,1)`-BLOCK FAMILY.**  The centre of a block has no edge of
colour `qc i` — the condition that round 55 had to impose by hand in the exhaustive search
`discovery/JSP-000140/fano_s1s2.py`.  It is `apex_zeroA`, which holds for every labelled
triangle of an admissible colouring. -/
theorem TwoOne.apex_zero (C : TwoOne n k m) (hc : Admissible (C.col)) (i : Fin m)
    (a b : Verts n) (hab : a ≠ b) (hm : C.leaves i = insert a (insert b ∅)) :
    C.ctr i ∈ zeroA (C.col) (C.qc i) := by
  obtain ⟨hain, hane, hbin, hbe⟩ := C.leaves_mem hab hm
  have h := apex_zeroA hc (C.labTri i a b hab hm)
  have h2 := C.col_notouch (i := i) hab hain hbin hane hbe
  rw [h2] at h
  exact h

/-- **LEAF-ISOLATION IS FREE FOR THE `(2,1)`-BLOCK FAMILY.**  The opposite edge of a block is an
isolated single edge of its colour class: neither leaf has another `qc i`-neighbour
(`nb_eq_singleton_of_cherry`), and `qc i ≠ pc i`. -/
theorem TwoOne.leaf_isolated (C : TwoOne n k m) (hc : Admissible (C.col)) (hn : 4 ≤ n) (i : Fin m)
    (a b : Verts n) (hab : a ≠ b) (hm : C.leaves i = insert a (insert b ∅)) :
    nb (C.col) (C.qc i) a (Finset.univ : Finset (Verts n)) = {b} ∧
      nb (C.col) (C.qc i) b (Finset.univ : Finset (Verts n)) = {a} ∧ C.qc i ≠ C.pc i := by
  obtain ⟨hain, hane, hbin, hbe⟩ := C.leaves_mem hab hm
  obtain ⟨h1, h2, h3⟩ :=
    nb_eq_singleton_of_cherry hc hn (C.pc i) (Ne.symm hane) (Ne.symm hbe) hab
      (C.col_ctr_leaf hab (C.ctr_mem i) hain hane)
      (C.col_ctr_leaf (a := b) (b := a) (Ne.symm hab) (C.ctr_mem i) hbin hbe)
      (C.qc i) (C.col_notouch (i := i) hab hain hbin hane hbe)
  exact ⟨h2, h3, h1⟩

/-! ### §4  the price: the construction cannot beat `5/6` -/

/-- Two distinct blocks cannot have two distinct vertices in common. -/
private theorem TwoOne.two_block_inter (C : TwoOne n k m) {i j : Fin m} {x y : Verts n}
    (hxy : x ≠ y) (hx : x ∈ C.bl i) (hx' : x ∈ C.bl j) (hy : y ∈ C.bl i) (hy' : y ∈ C.bl j) :
    i = j :=
  C.uniq s(x, y) i j (mem_edgeFinset_mk hx hy hxy) (mem_edgeFinset_mk hx' hy' hxy)

/-- Each block gives an element of `cherryFinset (C.col)`. -/
theorem TwoOne.mem_cherryFinset (C : TwoOne n k m) (hc : Admissible (C.col)) (i : Fin m) :
    (C.pc i, C.ctr i) ∈ cherryFinset (C.col) := by
  obtain ⟨a, b, hab, hm⟩ := C.leaves_pair i
  have h1 := C.centre_twoA hc i a b hab hm
  rw [cherryFinset, Finset.mem_biUnion]
  exact ⟨C.pc i, Finset.mem_univ _, Finset.mem_image.mpr ⟨C.ctr i, h1, rfl⟩⟩

/-- **TWO BLOCKS NEVER SHARE BOTH THEIR CENTRE AND THEIR "TWICE" COLOUR.**  Otherwise the centre
would carry four edges of that colour — the two blocks share at most one vertex, and it is their
common centre — against `Counting.nb_card_le_two`. -/
theorem TwoOne.paths_neq (C : TwoOne n k m) (hc : Admissible (C.col)) (i j : Fin m) (hij : i ≠ j) :
    (C.pc i, C.ctr i) ≠ (C.pc j, C.ctr j) := by
  intro h
  obtain ⟨hpc, hctr⟩ := Prod.mk.inj h
  obtain ⟨a, b, hab, hm⟩ := C.leaves_pair i
  obtain ⟨a', b', hab', hm'⟩ := C.leaves_pair j
  obtain ⟨hain, hane, hbin, hbe⟩ := C.leaves_mem hab hm
  obtain ⟨hain', hane', hbin', hbe'⟩ := C.leaves_mem hab' hm'
  have hcjmem : C.ctr i ∈ C.bl j := by
    rw [hctr]
    exact C.ctr_mem j
  have hcommon {x : Verts n} (hx : x ∈ C.bl i) (hx' : x ∈ C.bl j) : C.ctr i = x := by
    by_contra hn
    have hne1 : x ≠ C.ctr i := Ne.symm hn
    have hne2 : x ≠ C.ctr j := fun hh => hn (hh.trans hctr.symm).symm
    exact hij (TwoOne.two_block_inter C hne1 hx hx' (C.ctr_mem i) hcjmem)
  have hne_aa : a ≠ a' := by
    intro hh
    have hz := hcommon hain (by rw [hh]; exact hain')
    exact hane hz.symm
  have hne_ab : a ≠ b' := by
    intro hh
    have hz := hcommon hain (by rw [hh]; exact hbin')
    exact hane hz.symm
  have hne_ba : b ≠ a' := by
    intro hh
    have hz := hcommon hbin (by rw [hh]; exact hain')
    exact hbe hz.symm
  have hne_bb : b ≠ b' := by
    intro hh
    have hz := hcommon hbin (by rw [hh]; exact hbin')
    exact hbe hz.symm
  have hmemA : a ∈ nb (C.col) (C.pc i) (C.ctr i) (Finset.univ : Finset (Verts n)) :=
    mem_nb.mpr ⟨hane, Finset.mem_univ _, C.col_ctr_leaf hab (C.ctr_mem i) hain hane⟩
  have hmemB : b ∈ nb (C.col) (C.pc i) (C.ctr i) (Finset.univ : Finset (Verts n)) :=
    mem_nb.mpr ⟨hbe, Finset.mem_univ _,
      C.col_ctr_leaf (a := b) (b := a) (Ne.symm hab) (C.ctr_mem i) hbin hbe⟩
  have hmemA' : a' ∈ nb (C.col) (C.pc j) (C.ctr j) (Finset.univ : Finset (Verts n)) :=
    mem_nb.mpr ⟨hane', Finset.mem_univ _,
      by simpa only [hpc] using
        C.col_ctr_leaf (i := j) (a := a') (b := a) (Ne.symm hne_aa) (C.ctr_mem j) hain' hane'⟩
  have hmemB' : b' ∈ nb (C.col) (C.pc j) (C.ctr j) (Finset.univ : Finset (Verts n)) :=
    mem_nb.mpr ⟨hbe', Finset.mem_univ _,
      by simpa only [hpc] using
        C.col_ctr_leaf (i := j) (a := b') (b := a') (Ne.symm hab') (C.ctr_mem j) hbin' hbe'⟩
  have hcard : 4 ≤ (insert a (insert b (insert a' (insert b' ∅))) : Finset (Verts n)).card := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hne_aa, hne_ab]),
      Finset.card_insert_of_notMem (by simp [hne_ba, hne_bb]),
      Finset.card_insert_of_notMem (by simp [hab'])]
    simp

  have hsub : (insert a (insert b (insert a' (insert b' ∅))) : Finset (Verts n))
      ⊆ nb (C.col) (C.pc i) (C.ctr i) (Finset.univ : Finset (Verts n)) := by
    intro v hv
    rcases Finset.mem_insert.mp hv with hv1 | hv
    · rw [hv1]
      exact hmemA
    rcases Finset.mem_insert.mp hv with hv2 | hv
    · rw [hv2]
      exact hmemB
    rcases Finset.mem_insert.mp hv with hv3 | hv
    · rw [hv3, hctr, hpc]
      exact hmemA'
    rcases Finset.mem_insert.mp hv with hv4 | hv
    · rw [hv4, hctr, hpc]
      exact hmemB'
    · exact absurd hv (by simp)
  have hle := nb_card_le_two hc (C.pc i) (C.ctr i) (Finset.univ : Finset (Verts n))
  have hle' := Finset.card_le_card hsub
  omega

/-- **THE `m` BLOCKS GIVE `m` DISTINCT TWO-EDGE PATHS OF THE COLOURING.** -/
theorem TwoOne.paths_ge (C : TwoOne n k m) (hc : Admissible (C.col)) : m ≤ Paths (C.col) := by
  have hmem : ∀ i : Fin m, (C.pc i, C.ctr i) ∈ cherryFinset (C.col) := C.mem_cherryFinset hc
  have hinj : Function.Injective (fun i : Fin m => (C.pc i, C.ctr i)) := by
    intro i j heq
    by_contra hne
    exact C.paths_neq hc i j hne heq
  calc m = (Finset.univ : Finset (Fin m)).card := by simp
    _ ≤ ((Finset.univ : Finset (Fin m)).image fun i : Fin m => (C.pc i, C.ctr i)).card :=
        Finset.card_le_card_of_injOn (s := Finset.univ)
          (t := (Finset.univ : Finset (Fin m)).image fun i : Fin m => (C.pc i, C.ctr i))
          (f := fun i : Fin m => (C.pc i, C.ctr i))
          (fun _ hx => Finset.mem_image.mpr ⟨_, hx, rfl⟩)
          (show Set.InjOn (fun i : Fin m => (C.pc i, C.ctr i))
            ((Finset.univ : Finset (Fin m)) : Set (Fin m)) from
            fun _ _ _ _ hab => hinj hab)
    _ ≤ (cherryFinset (C.col)).card := by
        refine Finset.card_le_card ?_
        intro q hq
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
        exact hmem i
    _ = Paths (C.col) := card_cherryFinset _

/-- **THE PRICE OF THE `(2,1)`-BLOCK COLOURING.**  `5 * m ≤ n * k`: the `m` blocks pay five
`(vertex, colour)` slots each, and the palette has `n * k` slots.  Combined with
`6 * m = n * (n-1)` this is `5 * (n-1) ≤ 6 * k` — the sharp constant, which the construction
cannot beat. -/
theorem TwoOne.price (C : TwoOne n k m) (hc : Admissible (C.col)) (hn : 4 ≤ n) : 5 * m ≤ n * k := by
  have hg := global_identity hc
  have hp := C.paths_ge hc
  have hq := paths_le hc hn
  have hq6 : 6 * Paths (C.col) ≤ n * (n - 1) := by
    have h1 := Nat.mul_le_mul_left 6 hq
    exact le_trans h1 (Nat.mul_div_le (n * (n - 1)) 6)
  have hstep : 5 * Paths (C.col) ≤ n * (n - 1) - Paths (C.col) := by omega
  have hstep2 : 5 * Paths (C.col) ≤ n * k := by omega
  have := Nat.mul_le_mul_left 5 hp
  omega

/-- **For a Steiner triple system the two-edge paths of the colouring are exactly the blocks.** -/
theorem TwoOne.paths_eq_of_sts (C : TwoOne n k m) (hc : Admissible (C.col)) (hn : 4 ≤ n)
    (hB : 6 * m = n * (n - 1)) : Paths (C.col) = m := by
  have hp := C.paths_ge hc
  have hq := paths_le hc hn
  have hq' : Paths (C.col) ≤ m := by
    have h1 := hq
    rw [← hB] at h1
    simpa using h1
  omega

/-- **THE EXACT PRICE.**  If the two-edge paths of the colouring are exactly the `m` blocks then
`n * k = 5 * m + Isolated (col C)`, i.e. for a Steiner triple system (`6 * m = n * (n-1)`)

    `k = 5(n-1)/6 + Isolated / n`.

This is `Block.decomposition_eq` for the explicit colouring, and it is what makes the recipe below a
theorem rather than a plan. -/
theorem TwoOne.price_exact (C : TwoOne n k m) (hc : Admissible (C.col)) (hn : 4 ≤ n)
    (hB : 6 * m = n * (n - 1)) : n * k = 5 * m + Isolated (C.col) := by
  have hg := global_identity hc
  have hp := C.paths_eq_of_sts hc hn hB
  omega

/-- An admissible `(2,1)`-block colouring is an admissible colouring, so it gives an upper bound for
`f(n,4,5)`. -/
theorem TwoOne.eg_le (C : TwoOne n k m) (hc : Admissible (C.col)) : EG n ≤ k :=
  EG_le n k (C.col) hc

/-- **WHAT A SEARCH FOR THE SHARP CONSTANT HAS TO FIND.**  An admissible `(2,1)`-block colouring of a
Steiner triple system with exactly `n` missed `(vertex, colour)` slots satisfies

        `6 * k = 5 * (n-1) + 6`,

i.e. `k = 5(n-1)/6 + 1`: the sharp constant of the catalog answer plus one sixth.  At `n = 13` that is
`k = 11`, which with `Strict.EG_thirteen_ge_eleven` would settle `f(13,4,5) = 11`, the first order at
which `f(n,4,5) = 5n/6 + 1/6`. -/
theorem TwoOne.recipe (C : TwoOne n k m) (hc : Admissible (C.col)) (hn : 4 ≤ n)
    (hB : 6 * m = n * (n - 1)) (hiso : Isolated (C.col) = n) :
    6 * k = 5 * (n - 1) + 6 := by
  have hp := C.price_exact hc hn hB
  have key : 6 * (5 * m) = 5 * (n * (n - 1)) := by
    rw [← hB]
    ring
  have h6 : 6 * (n * k) = n * (5 * (n - 1) + 6) := by
    calc 6 * (n * k) = 6 * (5 * m + Isolated (C.col)) := by rw [hp]
      _ = 6 * (5 * m) + 6 * Isolated (C.col) := by ring
      _ = 5 * (n * (n - 1)) + 6 * Isolated (C.col) := by rw [key]
      _ = 5 * (n * (n - 1)) + 6 * n := by rw [hiso]
      _ = n * (5 * (n - 1) + 6) := by ring
  have h7 : n * (6 * k) = n * (5 * (n - 1) + 6) := by
    calc n * (6 * k) = 6 * (n * k) := by ring
      _ = n * (5 * (n - 1) + 6) := h6
  exact Nat.eq_of_mul_eq_mul_left (by omega) h7

/-- **... AND HENCE FOR `EG`:**  `6 * EG n ≤ 5 * (n-1) + 6`. -/
theorem TwoOne.recipe_eg (C : TwoOne n k m) (hc : Admissible (C.col)) (hn : 4 ≤ n)
    (hB : 6 * m = n * (n - 1)) (hiso : Isolated (C.col) = n) :
    6 * EG n ≤ 5 * (n - 1) + 6 := by
  have hr := C.recipe hc hn hB hiso
  have heg := C.eg_le hc
  have h' := Nat.mul_le_mul_left 6 heg
  rw [hr] at h'
  exact h'

/-- **THE REMAINING SEARCH TARGET, AS A THEOREM.**  An admissible `(2,1)`-block colouring of a
Steiner triple system of order `13` with `26` blocks and exactly `13` missed `(vertex, colour)`
slots settles the value of `f(13,4,5)`: `recipe_eg` gives `EG 13 ≤ 11` (the sharp constant
`5(n-1)/6` plus one sixth, rounded) and `EG_thirteen_ge_eleven` gives `EG 13 ≥ 11`.  So the
whole of B5 for `n = 13` reduces to *one* finite question about `26` blocks, each of which must
choose a centre and two of eleven colours — the CSP searched by
`discovery/JSP-000140/sts212b.c`. -/
theorem TwoOne.thirteen (C : TwoOne 13 k 26) (hc : Admissible (C.col))
    (hiso : Isolated (C.col) = 13) : EG 13 = 11 := by
  have hle := C.recipe_eg hc (by norm_num) (by norm_num) hiso
  have hge := EG_thirteen_ge_eleven
  omega

/-- **The `(2,1)`-block family never attains the counting bound**: an admissible `(2,1)`-block
colouring of a Steiner triple system wastes at least one whole colour
(`Strict.isolated_pos`, because its paths are `m = n(n-1)/6 > 0`). -/
theorem TwoOne.decomposition_gap (C : TwoOne n k m) (hc : Admissible (C.col)) (hn : 4 ≤ n)
    (hB : 6 * m = n * (n - 1)) : 6 * k = 5 * (n - 1) ∨ 5 * (n - 1) + 1 ≤ 6 * k := by
  by_cases h : 6 * k = 5 * (n - 1)
  · exact Or.inl h
  · right
    have hm : 0 < m := by
      have h1 : (0 : ℕ) < n * (n - 1) := by
        have h2 : (0 : ℕ) < n - 1 := by omega
        exact Nat.mul_pos (by omega) h2
      rw [← hB] at h1
      exact Nat.pos_of_mul_pos_left h1
    have hpos : 0 < Paths (C.col) := by
      rw [C.paths_eq_of_sts hc hn hB]
      exact hm
    have hi : 0 < Isolated (C.col) := isolated_pos hc hn hpos
    have hs : 6 * Isolated (C.col) + 2 * Defect (C.col) = n * (6 * k - 5 * (n - 1)) :=
      surplus_of_k hc hn
    have hx : 0 < 6 * k - 5 * (n - 1) := by
      by_contra hc0
      have hz : 6 * k - 5 * (n - 1) = 0 := by omega
      have hz2 : 6 * Isolated (C.col) + 2 * Defect (C.col) = 0 := by rw [hs, hz]; simp
      omega
    omega

end JSP140
