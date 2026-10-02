import JSPProblem.Fam

/-!
# JSP-000140 — the first stage **without a complete covering**

`Fam.lean` made the first stage of arXiv:2208.12563 §4 (= arXiv:2207.02920 Phase 1) a primitive
object: a matching `F : Fam n k` in the auxiliary `8`-uniform hypergraph, whose members are
configurations `g = (u, p, q, i, j)` using the three edges `{u,p}, {u,q}, {p,q}` of a triangle and
the five slots `(u,i), (p,i), (q,i), (p,j), (q,j)`.

Round 37 could only close the *complete* covering: `FamFamily` demands `leftoverF F = ∅`, because
`Tile` and `Packed` were imported from `Triangles.lean`, where they are consequences of `Covers`
and `PairFree`.  **The published construction covers only `1 - n^{-δ}` of the edges**
(BCDP §4: the matching stops at `i_max = ⅙ n²(1-n^{-δ})`), so the complete interface is the
*extremal* case and not the theorem.

This file removes the complete covering from the interface — the single blocker of round 37.  The
structural conditions of `Criterion.Design` become **proved** rather than assumed:

* **`colSlot_covered`** — *the key lemma of the file.*  If a **covered** edge `s(v,a)` has colour
  `i` in the induced colouring `colOf F d`, then the configuration covering that edge uses the
  **slot** `(v, i)`.  So the colour-degree of `v` in colour `i` is controlled by a single slot, and
  the matching condition bounds it by two;
* **`coverNbrs_mem`** — the **explicit classification** of a covered colour-`i` neighbour of `v`:
  it is a leaf if `v` is the centre of the member holding the slot `(v,i)`, the centre if `v` is a
  leaf, and the other leaf if the colour is the `cfgJ` colour.  This is the local form of
  `Cherry.leaf_not_centre`;
* **`coverNbrs_sub`** and **`coverNbrs_card_le_two`** — **THE COLOUR-DEGREE BOUND OF THE FIRST
  STAGE IS FREE.**  At most one member of `F` uses the slot `(v,i)`; it contributes two covered
  colour-`i` edges at `v` if `v` is its centre and one otherwise.  So **every colour-degree of the
  induced colouring of an arbitrary matching is at most two, whatever the size of the leftover**,
  and no `Covers` hypothesis appears — the first half of `Criterion.Tile` for a partial first stage;
* **`cfgVerts_lin`** — **THE PACKING CONDITION IS FREE.**  Two members whose triples meet in two
  vertices share an edge, so `LinF` forces them to be equal: the triples of a family form a partial
  Steiner triple system.

**STILL NOT PROVED (the rest of the round-37 blocker).**  The *leaf half* of the tiling condition
(a leaf of a two-edge path has covered colour-degree one), hence `Tile` and `Packed` of the
**finished** colouring, hence the reduction `jsp_000140_main_of_fam_partial_family` to a
leftover-tolerant first stage.  The exact remaining statements are recorded in
`discovery/JSP-000140/policy.json` (`next_lemma`).
-/

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace JSP140

variable {n k : ℕ}

/-! ## 0. Small finset helpers -/

theorem card_insert_two {α : Type*} [DecidableEq α] {a b : α} (h : a ≠ b) :
    (insert a (insert b ∅) : Finset α).card = 2 := by
  rw [Finset.card_insert_of_notMem (by simp [h]), Finset.card_insert_of_notMem (by simp)]
  simp

@[simp] theorem mem_pair {α : Type*} [DecidableEq α] {a b x : α} :
    x ∈ ({a, b} : Finset α) ↔ x = a ∨ x = b := by
  rw [Finset.mem_insert]
  simp

/-- Two distinct elements of a set of cardinality at least two. -/
theorem exists_two_of_card_ge_two {α : Type*} [DecidableEq α] {s : Finset α} (h : 2 ≤ s.card) :
    ∃ x y : α, x ≠ y ∧ x ∈ s ∧ y ∈ s := by
  by_cases h2 : s.card = 2
  · obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp h2
    exact ⟨x, y, hxy, by simp, by simp⟩
  · obtain ⟨x, hx⟩ : ∃ x, x ∈ s := Finset.card_ne_zero.mp (by omega)
    have herase : (s.erase x).card = s.card - 1 := Finset.card_erase_of_mem hx
    obtain ⟨y, hy⟩ : ∃ y, y ∈ s.erase x := Finset.card_ne_zero.mp (by omega)
    refine ⟨x, y, ?_, hx, ?_⟩
    · intro hc
      exact Finset.mem_erase.mp hy |>.1 hc.symm
    · exact Finset.mem_erase.mp hy |>.2

/-- The three vertices of a well-formed configuration are distinct. -/
theorem card_cfgVerts {n k : ℕ} {g : Cfg n k} (h : Ok g) : (cfgVerts g).card = 3 := by
  rw [cfgVerts, triVerts, Finset.card_insert_of_notMem (by simp [h.1, h.2.1]),
    Finset.card_insert_of_notMem (by simp [h.2.2]),
    Finset.card_insert_of_notMem (by simp)]
  simp

/-- **A configuration through `v` uses two of its three vertices besides `v`.** -/
theorem card_cfgVerts_erase {n k : ℕ} {g : Cfg n k} (h : Ok g) {v : Verts n} (hv : v ∈ cfgVerts g) :
    (cfgVerts g \ {v}).card = 2 := by
  have h3 := card_cfgVerts h
  have h1 : ({v} : Finset (Verts n)) ⊆ cfgVerts g := by
    intro x hx
    rw [Finset.mem_singleton.mp hx]
    exact hv
  have h5 : ({v} : Finset (Verts n)).card = 1 := Finset.card_singleton v
  have := Finset.card_sdiff_add_card_eq_card h1
  omega

theorem cfgVerts_erase_of_centre {n k : ℕ} {g : Cfg n k} (h : Ok g) :
    cfgVerts g \ ({cfgU g} : Finset (Verts n)) = ({cfgP g, cfgQ g} : Finset (Verts n)) := by
  apply Finset.Subset.antisymm
  · intro x hx
    rw [Finset.mem_sdiff] at hx
    rcases (mem_cfgVerts g).mp hx.1 with h' | h' | h'
    · exact False.elim (hx.2 (Finset.mem_singleton.mpr h'))
    · rw [mem_pair]; exact Or.inl h'
    · rw [mem_pair]; exact Or.inr h'
  · intro x hx
    rw [mem_pair] at hx
    rcases hx with h' | h'
    · rw [Finset.mem_sdiff]
      refine And.intro ((mem_cfgVerts g).mpr (Or.inr (Or.inl h'))) ?_
      intro hc
      have hc' : x = cfgU g := Finset.mem_singleton.mp hc
      exact h.1 (hc'.symm.trans h')
    · rw [Finset.mem_sdiff]
      refine And.intro ((mem_cfgVerts g).mpr (Or.inr (Or.inr h'))) ?_
      intro hc
      have hc' : x = cfgU g := Finset.mem_singleton.mp hc
      exact h.2.1 (hc'.symm.trans h')

theorem cfgVerts_erase_of_leafP {n k : ℕ} {g : Cfg n k} (h : Ok g) :
    cfgVerts g \ ({cfgP g} : Finset (Verts n)) = ({cfgU g, cfgQ g} : Finset (Verts n)) := by
  apply Finset.Subset.antisymm
  · intro x hx
    rw [Finset.mem_sdiff] at hx
    rcases (mem_cfgVerts g).mp hx.1 with h' | h' | h'
    · rw [mem_pair]; exact Or.inl h'
    · exact False.elim (hx.2 (Finset.mem_singleton.mpr h'))
    · rw [mem_pair]; exact Or.inr h'
  · intro x hx
    rw [mem_pair] at hx
    rcases hx with h' | h'
    · rw [Finset.mem_sdiff]
      refine And.intro ((mem_cfgVerts g).mpr (Or.inl h')) ?_
      intro hc
      have hc' : x = cfgP g := Finset.mem_singleton.mp hc
      exact h.1 (h' ▸ hc')
    · rw [Finset.mem_sdiff]
      refine And.intro ((mem_cfgVerts g).mpr (Or.inr (Or.inr h'))) ?_
      intro hc
      have hc' : x = cfgP g := Finset.mem_singleton.mp hc
      exact h.2.2.1 (hc'.symm.trans h')

theorem cfgVerts_erase_of_leafQ {n k : ℕ} {g : Cfg n k} (h : Ok g) :
    cfgVerts g \ ({cfgQ g} : Finset (Verts n)) = ({cfgU g, cfgP g} : Finset (Verts n)) := by
  apply Finset.Subset.antisymm
  · intro x hx
    rw [Finset.mem_sdiff] at hx
    rcases (mem_cfgVerts g).mp hx.1 with h' | h' | h'
    · rw [mem_pair]; exact Or.inl h'
    · rw [mem_pair]; exact Or.inr h'
    · exact False.elim (hx.2 (Finset.mem_singleton.mpr h'))
  · intro x hx
    rw [mem_pair] at hx
    rcases hx with h' | h'
    · rw [Finset.mem_sdiff]
      refine And.intro ((mem_cfgVerts g).mpr (Or.inl h')) ?_
      intro hc
      have hc' : x = cfgQ g := Finset.mem_singleton.mp hc
      exact h.2.1 (h' ▸ hc')
    · rw [Finset.mem_sdiff]
      refine And.intro ((mem_cfgVerts g).mpr (Or.inr (Or.inl h'))) ?_
      intro hc
      have hc' : x = cfgQ g := Finset.mem_singleton.mp hc
      exact h.2.2.1 (h'.symm.trans hc')

/-- **Two distinct vertices of a configuration span one of its three edges.** -/
theorem edge_of_mem_cfgVerts {n k : ℕ} {g : Cfg n k} {x y : Verts n} (hx : x ∈ cfgVerts g)
    (hy : y ∈ cfgVerts g) (hne : x ≠ y) : s(x, y) ∈ cfgEdges g := by
  refine (mem_cfgEdges g).mpr ?_
  simp only [mem_cfgVerts] at hx hy
  rcases hx with hx | hx | hx <;> rcases hy with hy | hy | hy
  · rw [hx, hy] at hne; exact False.elim (hne rfl)
  · rw [hx, hy]; exact Or.inl rfl
  · rw [hx, hy]; exact Or.inr (Or.inl rfl)
  · rw [hx, hy, Sym2.eq_swap]; exact Or.inl rfl
  · rw [hx, hy] at hne; exact False.elim (hne rfl)
  · rw [hx, hy]; exact Or.inr (Or.inr rfl)
  · rw [hx, hy, Sym2.eq_swap]; exact Or.inr (Or.inl rfl)
  · rw [hx, hy, Sym2.eq_swap]; exact Or.inr (Or.inr rfl)
  · rw [hx, hy] at hne; exact False.elim (hne rfl)

/-- Both endpoints of an edge of a configuration are vertices of that configuration. -/
theorem mem_cfgVerts_of_edge {n k : ℕ} {g : Cfg n k} {e : Sym2 (Verts n)} (he : e ∈ cfgEdges g)
    {x : Verts n} (hx : x ∈ e) : x ∈ cfgVerts g := by
  rcases mem_cfgEdges g |>.mp he with h1 | h1 | h1
  · rw [h1] at hx
    rcases Sym2.mem_iff.mp hx with hx' | hx'
    · rw [hx', mem_cfgVerts]; exact Or.inl rfl
    · rw [hx', mem_cfgVerts]; exact Or.inr (Or.inl rfl)
  · rw [h1] at hx
    rcases Sym2.mem_iff.mp hx with hx' | hx'
    · rw [hx', mem_cfgVerts]; exact Or.inl rfl
    · rw [hx', mem_cfgVerts]; exact Or.inr (Or.inr rfl)
  · rw [h1] at hx
    rcases Sym2.mem_iff.mp hx with hx' | hx'
    · rw [hx', mem_cfgVerts]; exact Or.inr (Or.inl rfl)
    · rw [hx', mem_cfgVerts]; exact Or.inr (Or.inr rfl)

/-- A slot of a configuration is at a vertex of that configuration. -/
theorem mem_cfgVerts_of_slot {n k : ℕ} {g : Cfg n k} {v : Verts n} {i : Fin k}
    (h : (v, i) ∈ cfgSlots g) : v ∈ cfgVerts g := by
  rcases mem_cfgSlots g |>.mp h with h | h
  · rcases h.2 with h' | h' | h'
    · rw [h', mem_cfgVerts]; exact Or.inl rfl
    · rw [h', mem_cfgVerts]; exact Or.inr (Or.inl rfl)
    · rw [h', mem_cfgVerts]; exact Or.inr (Or.inr rfl)
  · rcases h.2 with h' | h'
    · rw [h', mem_cfgVerts]; exact Or.inr (Or.inl rfl)
    · rw [h', mem_cfgVerts]; exact Or.inr (Or.inr rfl)

/-- **A configuration has exactly one pair of edges carrying the centre colour.** -/
theorem edge_is_spoke {n k : ℕ} {g : Cfg n k} (h : Ok g) {e : Sym2 (Verts n)}
    (he : e ∈ cfgEdges g) (hc : edgeCol g e = cfgI g) :
    e = s(cfgU g, cfgP g) ∨ e = s(cfgU g, cfgQ g) := by
  rcases mem_cfgEdges g |>.mp he with h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1
  · rw [h1] at hc; rw [edgeCol_leaf g] at hc
    exact False.elim (h.2.2.2 hc.symm)

/-- **At the centre of a configuration, the partner of a spoke is one of the two leaves.** -/
theorem partner_of_centre {n k : ℕ} {g : Cfg n k} (h : Ok g) {w a : Verts n}
    (hwc : w = cfgU g) (he : s(w, a) ∈ cfgEdges g) (hc : edgeCol g (s(w, a)) = cfgI g) :
    a = cfgP g ∨ a = cfgQ g := by
  subst hwc
  rcases mem_cfgEdges g |>.mp he with h1 | h1 | h1
  · exact Or.inl (sym2_inj_right h1)
  · exact Or.inr (sym2_inj_right h1)
  · rcases sym2_inj h1 with ⟨h4, _⟩ | ⟨h4, _⟩
    · exact False.elim (h.1 (by rw [← h4]))
    · exact False.elim (h.2.1 (by rw [← h4]))

/-- **At a leaf of a configuration, the only edge of the centre colour is the spoke.**  This is the
local form of `Cherry.leaf_not_centre`. -/
theorem partner_of_leaf {n k : ℕ} {g : Cfg n k} (h : Ok g) {w a : Verts n}
    (hw : w = cfgP g ∨ w = cfgQ g) (he : s(w, a) ∈ cfgEdges g) (hc : edgeCol g (s(w, a)) = cfgI g) :
    a = cfgU g := by
  rcases hw with hw | hw <;> subst hw
  · rcases mem_cfgEdges g |>.mp he with h1 | h1 | h1
    · rcases sym2_inj h1 with ⟨h4, _⟩ | ⟨h4, h5⟩
      · exact False.elim (h.1 (by rw [← h4]))
      · exact h5
    · rcases sym2_inj h1 with ⟨h4, _⟩ | ⟨h4, _⟩
      · exact False.elim (h.1 (by rw [← h4]))
      · exact False.elim (h.2.2.1 (by rw [← h4]))
    · rw [h1] at hc; rw [edgeCol_leaf g] at hc
      exact False.elim (h.2.2.2 (by rw [← hc]))
  · rcases mem_cfgEdges g |>.mp he with h1 | h1 | h1
    · rcases sym2_inj h1 with ⟨h4, _⟩ | ⟨h4, _⟩
      · exact False.elim (h.2.1 (by rw [← h4]))
      · exact False.elim (h.2.2.1 (by rw [← h4]))
    · rcases sym2_inj h1 with ⟨h4, _⟩ | ⟨h4, h5⟩
      · exact False.elim (h.2.1 (by rw [← h4]))
      · exact h5
    · rw [h1] at hc; rw [edgeCol_leaf g] at hc
      exact False.elim (h.2.2.2 (by rw [← hc]))

theorem partner_of_leafJ {n k : ℕ} {g : Cfg n k} (h : Ok g) {v a : Verts n} (hw : v = cfgP g)
    (he : s(v, a) ∈ cfgEdges g) (hc : edgeCol g (s(v, a)) = cfgJ g) : a = cfgQ g := by
  subst hw
  rcases mem_cfgEdges g |>.mp he with h1 | h1 | h1
  · rcases sym2_inj h1 with ⟨h4, _⟩ | ⟨h4, h5⟩
    · exact False.elim (h.1 (by rw [← h4]))
    · have hc' : edgeCol g (s(cfgP g, cfgU g)) = cfgJ g := h5 ▸ hc
      have hsp : edgeCol g (s(cfgP g, cfgU g)) = cfgI g := by
        rw [Sym2.eq_swap]; exact edgeCol_long (ne_edges h).2.1
      exact False.elim (h.2.2.2 (hsp.symm.trans hc'))
  · rcases sym2_inj h1 with ⟨h4, h5⟩ | ⟨h4, _⟩
    · exact h5
    · exact False.elim (h.2.2.1 (by rw [← h4]))
  · exact sym2_inj_right h1

theorem partner_of_leafJ' {n k : ℕ} {g : Cfg n k} (h : Ok g) {v a : Verts n} (hw : v = cfgQ g)
    (he : s(v, a) ∈ cfgEdges g) (hc : edgeCol g (s(v, a)) = cfgJ g) : a = cfgP g := by
  subst hw
  rcases mem_cfgEdges g |>.mp he with h1 | h1 | h1
  · rcases sym2_inj h1 with ⟨h4, h5⟩ | ⟨h4, _⟩
    · exact h5
    · exact False.elim (h.2.2.1 (by rw [← h4]))
  · rcases sym2_inj h1 with ⟨h4, _⟩ | ⟨h4, h5⟩
    · exact False.elim (h.2.1 (by rw [← h4]))
    · have hc' : edgeCol g (s(cfgQ g, cfgU g)) = cfgJ g := h5 ▸ hc
      have hsp : edgeCol g (s(cfgQ g, cfgU g)) = cfgI g := by
        rw [Sym2.eq_swap]; exact edgeCol_long (ne_edges h).2.2
      exact False.elim (h.2.2.2 (hsp.symm.trans hc'))
  · rcases sym2_inj h1 with ⟨h4, _⟩ | ⟨h4, h5⟩
    · exact False.elim (h.2.2.1 (by rw [← h4]))
    · exact h5

/-! ## 1. THE KEY LEMMA: a covered colour-`i` edge at `v` uses the slot `(v, i)` -/

/-- **THE SLOT ACCOUNTING OF A SINGLE EDGE.**  If a covered edge `s(v,a)` gets colour `i` in the
induced colouring, then the configuration covering it uses the slot `(v,i)` — the pair
`(vertex, colour)` of that edge at that endpoint.  This is why a matching in the auxiliary
hypergraph *controls a colouring*, and it is what makes the tiling condition automatic. -/
theorem colSlot_covered {n k : ℕ} {F : Fam n k} (hok : OkF F) (hL : LinF F)
    {d i : Fin k} {v a : Verts n} (hcov : s(v, a) ∈ coveredF F)
    (hcol : colOf F d (s(v, a)) = i) :
    ∃ g₀ ∈ F, s(v, a) ∈ cfgEdges g₀ ∧ (v, i) ∈ cfgSlots g₀ := by
  obtain ⟨g₀, hg₀, he₀⟩ := mem_coveredF.mp hcov
  have hok₀ : Ok g₀ := hok g₀ hg₀
  have hce : colOf F d (s(v, a)) = edgeCol g₀ (s(v, a)) := colOf_of_mem hL hg₀ he₀ d
  have hvv : v ∈ s(v, a) := Sym2.mem_mk_left v a
  refine ⟨g₀, hg₀, he₀, ?_⟩
  rcases mem_cfgEdges g₀ |>.mp he₀ with hA | hA | hA
  · rw [hA] at hvv
    rcases Sym2.mem_iff.mp hvv with hv' | hv'
    · have hne : s(v, a) ≠ s(cfgP g₀, cfgQ g₀) := by rw [hA]; exact (ne_edges hok₀).2.1
      have hi : i = cfgI g₀ := hcol.symm.trans (hce.trans (edgeCol_long hne))
      subst hi
      rw [hv']
      exact mem_cfgSlots_1 g₀
    · have hne : s(v, a) ≠ s(cfgP g₀, cfgQ g₀) := by rw [hA]; exact (ne_edges hok₀).2.1
      have hi : i = cfgI g₀ := hcol.symm.trans (hce.trans (edgeCol_long hne))
      subst hi
      rw [hv']
      exact mem_cfgSlots_2 g₀
  · rw [hA] at hvv
    rcases Sym2.mem_iff.mp hvv with hv' | hv'
    · have hne : s(v, a) ≠ s(cfgP g₀, cfgQ g₀) := by rw [hA]; exact (ne_edges hok₀).2.2
      have hi : i = cfgI g₀ := hcol.symm.trans (hce.trans (edgeCol_long hne))
      subst hi
      rw [hv']
      exact mem_cfgSlots_1 g₀
    · have hne : s(v, a) ≠ s(cfgP g₀, cfgQ g₀) := by rw [hA]; exact (ne_edges hok₀).2.2
      have hi : i = cfgI g₀ := hcol.symm.trans (hce.trans (edgeCol_long hne))
      subst hi
      rw [hv']
      exact mem_cfgSlots_3 g₀
  · rw [hA] at hvv
    rcases Sym2.mem_iff.mp hvv with hv' | hv'
    · have hcl : edgeCol g₀ (s(v, a)) = cfgJ g₀ := by rw [hA]; exact edgeCol_leaf g₀
      have hi : i = cfgJ g₀ := hcol.symm.trans (hce.trans hcl)
      subst hi
      rw [hv']
      exact mem_cfgSlots_4 g₀
    · have hcl : edgeCol g₀ (s(v, a)) = cfgJ g₀ := by rw [hA]; exact edgeCol_leaf g₀
      have hi : i = cfgJ g₀ := hcol.symm.trans (hce.trans hcl)
      subst hi
      rw [hv']
      exact mem_cfgSlots_5 g₀

/-! ## 2. The covered colour-degrees -/

/-- **The covered colour-`i` neighbours of `v`**: the colour-`i` neighbours of `v` in the induced
colouring which lie on edges the family covers, so that their colour is prescribed by a member. -/
noncomputable def coverNbrs {n k : ℕ} (F : Fam n k) (d : Fin k) (i : Fin k) (v : Verts n) :
    Finset (Verts n) :=
  (Nbrs (colOf F d) i v).filter (fun x => s(v, x) ∈ coveredF F)

@[simp] theorem mem_coverNbrs {n k : ℕ} {F : Fam n k} {d i : Fin k} {v a : Verts n} :
    a ∈ coverNbrs F d i v ↔ a ≠ v ∧ colOf F d (s(v, a)) = i ∧ s(v, a) ∈ coveredF F := by
  rw [coverNbrs, Finset.mem_filter, mem_Nbrs]
  tauto

/-- **THE COVERED COLOUR-`i` NEIGHBOURS OF `v`, EXPLICITLY.**  With the slot `(v,i)` held by `g`,
the covered colour-`i` neighbour of `v` is a leaf if `v` is the centre of `g`, and the centre if `v`
is a leaf of `g`. -/
theorem coverNbrs_mem {n k : ℕ} {F : Fam n k} (hok : OkF F) (hL : LinF F) (hS : SlotFree F)
    {d i : Fin k} {v a : Verts n} {g : Cfg n k} (hg : g ∈ F) (hslot : (v, i) ∈ cfgSlots g)
    (ha : a ∈ coverNbrs F d i v) :
    (v = cfgU g ∧ i = cfgI g ∧ (a = cfgP g ∨ a = cfgQ g)) ∨
      (v = cfgP g ∧ i = cfgI g ∧ a = cfgU g) ∨
      (v = cfgQ g ∧ i = cfgI g ∧ a = cfgU g) ∨
      (v = cfgP g ∧ i = cfgJ g ∧ a = cfgQ g) ∨
      (v = cfgQ g ∧ i = cfgJ g ∧ a = cfgP g) := by
  obtain ⟨-, hcol, hcov⟩ := mem_coverNbrs.mp ha
  obtain ⟨g₀, hg₀, he₀, hslot₀⟩ := colSlot_covered hok hL hcov hcol
  have heq : g₀ = g := hS g₀ g hg₀ hg (v, i) hslot₀ hslot
  have hce : colOf F d (s(v, a)) = edgeCol g (s(v, a)) := by
    rw [← heq]; exact colOf_of_mem hL hg₀ he₀ d
  have hccol : edgeCol g (s(v, a)) = i := hce.symm.trans hcol
  have hEg : s(v, a) ∈ cfgEdges g := by rw [← heq]; exact he₀
  rcases mem_cfgSlots g |>.mp hslot with h | h
  · rcases h.2 with hv' | hv' | hv'
    · refine Or.inl ⟨hv', h.1, ?_⟩
      exact partner_of_centre (hok g hg) hv' hEg (hccol.trans h.1)
    · refine Or.inr (Or.inl ⟨hv', h.1, ?_⟩)
      exact partner_of_leaf (hok g hg) (Or.inl hv') hEg (hccol.trans h.1)
    · refine Or.inr (Or.inr (Or.inl ⟨hv', h.1, ?_⟩))
      exact partner_of_leaf (hok g hg) (Or.inr hv') hEg (hccol.trans h.1)
  · rcases h.2 with hv' | hv'
    · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨hv', h.1, ?_⟩)))
      exact partner_of_leafJ (hok g hg) hv' hEg (hccol.trans h.1)
    · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨hv', h.1, ?_⟩)))
      exact partner_of_leafJ' (hok g hg) hv' hEg (hccol.trans h.1)

/-- **THE COVERED COLOUR DEGREE IS CONTROLLED BY ONE SLOT.** -/
theorem coverNbrs_sub {n k : ℕ} {F : Fam n k} (hok : OkF F) (hL : LinF F) (hS : SlotFree F)
    {d i : Fin k} {v : Verts n} {g : Cfg n k} (hg : g ∈ F) (hslot : (v, i) ∈ cfgSlots g) :
    coverNbrs F d i v ⊆ cfgVerts g \ {v} := by
  intro a ha
  obtain ⟨-, hcol, hcov⟩ := mem_coverNbrs.mp ha
  obtain ⟨g₀, hg₀, he₀, hslot₀⟩ := colSlot_covered hok hL hcov hcol
  have heq : g₀ = g := hS g₀ g hg₀ hg (v, i) hslot₀ hslot
  subst heq
  rw [Finset.mem_sdiff]
  exact ⟨mem_cfgVerts_of_edge he₀ (Sym2.mem_mk_right v a),
    fun h => (mem_coverNbrs).mp ha |>.1 (Finset.mem_singleton.mp h)⟩

/-- **THE TILING DEGREE BOUND IS FREE.**  The covered colour-degree of a family is at most two,
with **no assumption on the size of the leftover** and no `Covers` hypothesis. -/
theorem coverNbrs_card_le_two {n k : ℕ} {F : Fam n k} (hok : OkF F) (hL : LinF F) (hS : SlotFree F)
    {d i : Fin k} (v : Verts n) : (coverNbrs F d i v).card ≤ 2 := by
  by_cases hex : ∃ g ∈ F, (v, i) ∈ cfgSlots g
  · obtain ⟨g, hg, hslot⟩ := hex
    calc (coverNbrs F d i v).card
        ≤ (cfgVerts g \ {v}).card := Finset.card_le_card (coverNbrs_sub hok hL hS hg hslot)
      _ = 2 := card_cfgVerts_erase (hok g hg) (mem_cfgVerts_of_slot hslot)
  · have hempty : coverNbrs F d i v = ∅ := by
      ext a
      constructor
      · intro ha
        rcases (mem_coverNbrs).mp ha with ⟨-, hcol, hcov⟩
        obtain ⟨g₀, hg₀, -, hslot⟩ := colSlot_covered hok hL hcov hcol
        exact False.elim (hex ⟨g₀, hg₀, hslot⟩)
      · intro ha
        simp at ha
    rw [hempty]
    simp
/-! ## 3. The vertex sets of a family form a packing -/

/-- **THE PACKING CONDITION IS FREE.**  The triples of the members of a family form a partial
Steiner triple system: two of them meet in at most one vertex.  This is `Criterion.Packed` for a
partial (leftover-tolerant) first stage, and it needs no `Covers` hypothesis. -/
theorem cfgVerts_lin {n k : ℕ} {F : Fam n k} (hL : LinF F) {g g' : Cfg n k} (hg : g ∈ F)
    (hg' : g' ∈ F) (hne : g ≠ g') : (cfgVerts g ∩ cfgVerts g').card ≤ 1 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨x, y, hxy, hx, hy⟩ := exists_two_of_card_ge_two hcon
  have hx1 : x ∈ cfgVerts g := (Finset.mem_inter.mp hx).1
  have hx2 : x ∈ cfgVerts g' := (Finset.mem_inter.mp hx).2
  have hy1 : y ∈ cfgVerts g := (Finset.mem_inter.mp hy).1
  have hy2 : y ∈ cfgVerts g' := (Finset.mem_inter.mp hy).2
  exact hne (hL g g' hg hg' _ (edge_of_mem_cfgVerts hx1 hy1 hxy)
    (edge_of_mem_cfgVerts hx2 hy2 hxy))

end JSP140
