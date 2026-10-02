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

/-! ## 4. The leaf half of the tiling condition

Sections 2 and 3 proved the *degree* half of `Criterion.Tile` and the packing condition for a
first stage with an arbitrary leftover.  This section proves the **leaf half**, which was the one
concrete remaining lemma of round 38:

* `partner_coverNbrs` — the edge from `v` to a covered colour-`i` neighbour of `v` is an edge of
  the member holding the slot `(v,i)` (the forcing step of `coverNbrs_mem`, isolated);
* `coverNbrs_card_le_one_of_leaf` — **a leaf of the slot graph has at most one covered colour-`i`
  neighbour**: if `(v,i)` is a slot of `g` and `v` is not the centre of `g`, the covered colour-`i`
  neighbourhood of `v` has at most one element (the partner lemma forces it to be a single
  vertex);
* `coverNbrs_eq_pair_of_card_two` — **TWO COVERED NEIGHBOURS MEAN A CENTRE**: a vertex with two
  covered colour-`i` neighbours is the *centre* of the member holding the slot `(v,i)`, its colour
  is the centre colour, and the two neighbours are exactly the two leaves of that member;
* **`coverNbrs_card_one_of_mem_card_two`** — **THE LEAF HALF OF `Tile` FOR A PARTIAL FIRST STAGE**:
  a covered colour-`i` neighbour of a two-covered-neighbour vertex has covered colour-degree
  exactly one, i.e. it is a leaf of the two-edge path and nothing else.  Together with
  `coverNbrs_card_le_two` (degree half) and `cfgVerts_lin` (packing) this is **all of
  `Criterion.Design` except the two four-set conditions**, for an arbitrary matching with an
  arbitrary leftover;
* `coverNbrs_eq_singleton_of_card_two` — the same statement in the form used downstream: the
  covered colour-`i` neighbourhood of a leaf is the *singleton* `{centre}`. -/

/-- **A SPOKE OF A CONFIGURATION CARRIES THE CENTRE COLOUR.**  The edge from the centre `v` of `g`
to one of its leaves `a` carries `cfgI g`, in the order `(a, v)`. -/
theorem edgeCol_spoke_leaf {n k : ℕ} {g : Cfg n k} (h : Ok g) (a v : Verts n)
    (ha : a = cfgP g ∨ a = cfgQ g) (hv : v = cfgU g) : edgeCol g (s(a, v)) = cfgI g := by
  rcases ha with ha | ha
  · subst ha
    subst hv
    rw [edgeCol_long (by
        intro he
        rcases sym2_inj he with ⟨-, h1⟩ | ⟨h1, -⟩
        · exact h.2.1 h1
        · exact h.2.2.1 h1)]
  · subst ha
    subst hv
    rw [edgeCol_long (by
        intro he
        rcases sym2_inj he with ⟨h1, -⟩ | ⟨-, h1⟩
        · exact h.2.2.1 h1.symm
        · exact h.1 h1)]

/-- **THE MEMBER COVERING A COVERED NEIGHBOUR IS THE ONE HOLDING THE SLOT.**  If `(v,i)` is a slot of
`g`, then for every covered colour-`i` neighbour `a` of `v` the edge `s(v,a)` is an edge of `g` and
receives `g`'s colour.  This is the forcing step of `coverNbrs_mem`, isolated. -/
theorem partner_coverNbrs {n k : ℕ} {F : Fam n k} (hok : OkF F) (hL : LinF F) (hS : SlotFree F)
    {d i : Fin k} {v a : Verts n} {g : Cfg n k} (hg : g ∈ F) (hslot : (v, i) ∈ cfgSlots g)
    (ha : a ∈ coverNbrs F d i v) :
    s(v, a) ∈ cfgEdges g ∧ colOf F d (s(v, a)) = edgeCol g (s(v, a)) := by
  obtain ⟨-, hcol, hcov⟩ := mem_coverNbrs.mp ha
  obtain ⟨g₀, hg₀, he₀, hslot₀⟩ := colSlot_covered hok hL hcov hcol
  have heq : g₀ = g := hS g₀ g hg₀ hg (v, i) hslot₀ hslot
  subst heq
  exact ⟨he₀, colOf_of_mem hL hg he₀ d⟩

/-- **A LEAF OF THE SLOT GRAPH HAS AT MOST ONE COVERED COLOUR-`i` NEIGHBOUR.**  If `(v,i)` is a slot
of `g` and `v` is *not* the centre of `g`, then `v` is joined by a covered colour-`i` edge to at
most one vertex: the partner lemmas force that vertex to be a single one (the centre if the slot
is a centre-colour slot at a leaf, the other leaf otherwise).  **No `Covers` hypothesis and no
bound on the leftover appear.** -/
theorem coverNbrs_card_le_one_of_leaf {n k : ℕ} {F : Fam n k} (hok : OkF F) (hL : LinF F)
    (hS : SlotFree F) {d i : Fin k} {v : Verts n} {g : Cfg n k} (hg : g ∈ F)
    (hslot : (v, i) ∈ cfgSlots g) (hv : v ≠ cfgU g) : (coverNbrs F d i v).card ≤ 1 := by
  rcases mem_cfgSlots g |>.mp hslot with h | h
  · rcases h.2 with hv' | hv' | hv'
    · exact (hv hv').elim
    · have h1 : coverNbrs F d i v ⊆ ({cfgU g} : Finset (Verts n)) := by
        intro b hb
        obtain ⟨he, hce⟩ := partner_coverNbrs hok hL hS hg hslot hb
        have hbc : edgeCol g (s(v, b)) = cfgI g :=
          (hce.symm.trans (mem_coverNbrs.mp hb).2.1).trans h.1
        rw [Finset.mem_singleton]
        exact partner_of_leaf (hok g hg) (Or.inl hv') he hbc
      calc (coverNbrs F d i v).card ≤ (({cfgU g} : Finset (Verts n))).card :=
          Finset.card_le_card h1
        _ = 1 := Finset.card_singleton _
    · have h1 : coverNbrs F d i v ⊆ ({cfgU g} : Finset (Verts n)) := by
        intro b hb
        obtain ⟨he, hce⟩ := partner_coverNbrs hok hL hS hg hslot hb
        have hbc : edgeCol g (s(v, b)) = cfgI g :=
          (hce.symm.trans (mem_coverNbrs.mp hb).2.1).trans h.1
        rw [Finset.mem_singleton]
        exact partner_of_leaf (hok g hg) (Or.inr hv') he hbc
      calc (coverNbrs F d i v).card ≤ (({cfgU g} : Finset (Verts n))).card :=
          Finset.card_le_card h1
        _ = 1 := Finset.card_singleton _
  · rcases h.2 with hv' | hv'
    · have h1 : coverNbrs F d i v ⊆ ({cfgQ g} : Finset (Verts n)) := by
        intro b hb
        obtain ⟨he, hce⟩ := partner_coverNbrs hok hL hS hg hslot hb
        have hbc : edgeCol g (s(v, b)) = cfgJ g :=
          (hce.symm.trans (mem_coverNbrs.mp hb).2.1).trans h.1
        rw [Finset.mem_singleton]
        exact partner_of_leafJ (hok g hg) hv' he hbc
      calc (coverNbrs F d i v).card ≤ (({cfgQ g} : Finset (Verts n))).card :=
          Finset.card_le_card h1
        _ = 1 := Finset.card_singleton _
    · have h1 : coverNbrs F d i v ⊆ ({cfgP g} : Finset (Verts n)) := by
        intro b hb
        obtain ⟨he, hce⟩ := partner_coverNbrs hok hL hS hg hslot hb
        have hbc : edgeCol g (s(v, b)) = cfgJ g :=
          (hce.symm.trans (mem_coverNbrs.mp hb).2.1).trans h.1
        rw [Finset.mem_singleton]
        exact partner_of_leafJ' (hok g hg) hv' he hbc
      calc (coverNbrs F d i v).card ≤ (({cfgP g} : Finset (Verts n))).card :=
          Finset.card_le_card h1
        _ = 1 := Finset.card_singleton _

/-- **TWO COVERED NEIGHBOURS MEAN A CENTRE.**  If `v` has two covered colour-`i` neighbours, then
`(v,i)` is a slot of some member `g` of the family, `v` is its **centre**, `i` is its centre colour
and the two neighbours are exactly its two leaves.  This is the centre half of the tiling condition
for a partial first stage, and it needs no `Covers` hypothesis: the leaf cases are excluded by
`coverNbrs_card_le_one_of_leaf`. -/
theorem coverNbrs_eq_pair_of_card_two {n k : ℕ} {F : Fam n k} (hok : OkF F) (hL : LinF F)
    (hS : SlotFree F) {d i : Fin k} {v : Verts n} (hc : (coverNbrs F d i v).card = 2) :
    ∃ g ∈ F, (v, i) ∈ cfgSlots g ∧ v = cfgU g ∧ i = cfgI g ∧
      coverNbrs F d i v = ({cfgP g, cfgQ g} : Finset (Verts n)) := by
  obtain ⟨a, ha⟩ := Finset.card_ne_zero.mp (by omega : (coverNbrs F d i v).card ≠ 0)
  obtain ⟨-, hcol, hcov⟩ := mem_coverNbrs.mp ha
  obtain ⟨g, hg, -, hslot⟩ := colSlot_covered hok hL hcov hcol
  rcases mem_cfgSlots g |>.mp hslot with h | h
  · rcases h.2 with hv' | hv' | hv'
    · refine ⟨g, hg, hslot, hv', h.1, ?_⟩
      have hsub : coverNbrs F d i v ⊆ ({cfgP g, cfgQ g} : Finset (Verts n)) := by
        intro a ha
        have ha' := coverNbrs_sub hok hL hS hg hslot ha
        rw [hv'] at ha'
        rw [cfgVerts_erase_of_centre (hok g hg)] at ha'
        exact ha'
      refine Finset.eq_of_subset_of_card_le hsub ?_
      have hcard : ({cfgP g, cfgQ g} : Finset (Verts n)).card = 2 :=
        Finset.card_pair (hok g hg).2.2.1
      rw [hcard, hc]
    · exfalso
      have hne : v ≠ cfgU g := (hv'.symm ▸ (hok g hg).1).symm
      have h1 : (coverNbrs F d i v).card ≤ 1 :=
        coverNbrs_card_le_one_of_leaf hok hL hS hg hslot hne
      omega
    · exfalso
      have hne : v ≠ cfgU g := (hv'.symm ▸ (hok g hg).2.1).symm
      have h1 : (coverNbrs F d i v).card ≤ 1 :=
        coverNbrs_card_le_one_of_leaf hok hL hS hg hslot hne
      omega
  · rcases h.2 with hv' | hv'
    · exfalso
      have hne : v ≠ cfgU g := (hv'.symm ▸ (hok g hg).1).symm
      have h1 : (coverNbrs F d i v).card ≤ 1 :=
        coverNbrs_card_le_one_of_leaf hok hL hS hg hslot hne
      omega
    · exfalso
      have hne : v ≠ cfgU g := (hv'.symm ▸ (hok g hg).2.1).symm
      have h1 : (coverNbrs F d i v).card ≤ 1 :=
        coverNbrs_card_le_one_of_leaf hok hL hS hg hslot hne
      omega

/-- **THE LEAF HALF OF `Criterion.Tile` FOR A PARTIAL FIRST STAGE.**  If `v` has two covered
colour-`i` neighbours in the induced colouring of a matching `F`, then each of them has covered
colour-degree exactly one: it is a **leaf** of the two-edge path `a - v - b` and is joined to no
other vertex by a covered colour-`i` edge.

This is the lemma round 38 isolated as `next_lemma`: with `coverNbrs_card_le_two` (degree half) and
`cfgVerts_lin` (packing) it gives all of `Criterion.Design` except `NoCrossFour` and `NoBadFour`,
**for a matching with an arbitrary leftover**. -/
theorem coverNbrs_card_one_of_mem_card_two {n k : ℕ} {F : Fam n k} (hok : OkF F) (hL : LinF F)
    (hS : SlotFree F) {d i : Fin k} {v a : Verts n} (hc : (coverNbrs F d i v).card = 2)
    (ha : a ∈ coverNbrs F d i v) : (coverNbrs F d i a).card = 1 := by
  obtain ⟨g, hg, hslot, hv, hi, hpair⟩ := coverNbrs_eq_pair_of_card_two hok hL hS hc
  have hba : a = cfgP g ∨ a = cfgQ g := by
    have hmem : a ∈ ({cfgP g, cfgQ g} : Finset (Verts n)) := hpair ▸ ha
    exact mem_pair.mp hmem
  have hokg : Ok g := hok g hg
  rcases hba with hpa | hpa
  · subst hpa
    have hsub : coverNbrs F d i (cfgP g) ⊆ ({cfgU g} : Finset (Verts n)) := by
      intro b hb
      obtain ⟨he, hce⟩ : s(cfgP g, b) ∈ cfgEdges g ∧
          colOf F d (s(cfgP g, b)) = edgeCol g (s(cfgP g, b)) :=
        partner_coverNbrs hok hL hS hg (hi ▸ mem_cfgSlots_2 g) hb
      have hbc : edgeCol g (s(cfgP g, b)) = cfgI g :=
        (hce.symm.trans (mem_coverNbrs.mp hb).2.1).trans hi
      rw [Finset.mem_singleton]
      exact partner_of_leaf hokg (Or.inl rfl) he hbc
    have hE : s(cfgP g, cfgU g) ∈ cfgEdges g :=
      (mem_cfgEdges g).mpr
        (Or.inl Sym2.eq_swap.symm)
    have h1 : colOf F d s(cfgP g, cfgU g) = edgeCol g (s(cfgP g, cfgU g)) :=
      colOf_of_mem hL hg hE d
    have hcovU : s(cfgP g, cfgU g) ∈ coveredF F :=
      mem_coveredF.mpr ⟨g, hg, hE⟩
    have hcolU : colOf F d s(cfgP g, cfgU g) = cfgI g := by
      rw [h1]
      exact edgeCol_spoke_leaf hokg (cfgP g) (cfgU g) (Or.inl rfl) rfl
    have hmem : cfgU g ∈ coverNbrs F d i (cfgP g) :=
      (mem_coverNbrs).mpr ⟨hokg.1, hcolU.trans hi.symm, hcovU⟩
    have hcard : coverNbrs F d i (cfgP g) = {cfgU g} :=
      Finset.eq_of_subset_of_card_le hsub (by
        rw [Finset.card_singleton]
        have hpos := Finset.card_pos.mpr ⟨cfgU g, hmem⟩
        omega)
    rw [hcard, Finset.card_singleton]
  · subst hpa
    have hsub : coverNbrs F d i (cfgQ g) ⊆ ({cfgU g} : Finset (Verts n)) := by
      intro b hb
      obtain ⟨he, hce⟩ : s(cfgQ g, b) ∈ cfgEdges g ∧
          colOf F d (s(cfgQ g, b)) = edgeCol g (s(cfgQ g, b)) :=
        partner_coverNbrs hok hL hS hg (hi ▸ mem_cfgSlots_3 g) hb
      have hbc : edgeCol g (s(cfgQ g, b)) = cfgI g :=
        (hce.symm.trans (mem_coverNbrs.mp hb).2.1).trans hi
      rw [Finset.mem_singleton]
      exact partner_of_leaf hokg (Or.inr rfl) he hbc
    have hE : s(cfgQ g, cfgU g) ∈ cfgEdges g :=
      (mem_cfgEdges g).mpr (Or.inr (Or.inl Sym2.eq_swap.symm))
    have h1 : colOf F d s(cfgQ g, cfgU g) = edgeCol g (s(cfgQ g, cfgU g)) :=
      colOf_of_mem hL hg hE d
    have hcovU : s(cfgQ g, cfgU g) ∈ coveredF F :=
      mem_coveredF.mpr ⟨g, hg, hE⟩
    have hcolU : colOf F d s(cfgQ g, cfgU g) = cfgI g := by
      rw [h1]
      exact edgeCol_spoke_leaf hokg (cfgQ g) (cfgU g) (Or.inr rfl) rfl
    have hmem : cfgU g ∈ coverNbrs F d i (cfgQ g) :=
      (mem_coverNbrs).mpr ⟨hokg.2.1, hcolU.trans hi.symm, hcovU⟩
    have hcard : coverNbrs F d i (cfgQ g) = {cfgU g} :=
      Finset.eq_of_subset_of_card_le hsub (by
        rw [Finset.card_singleton]
        have hpos := Finset.card_pos.mpr ⟨cfgU g, hmem⟩
        omega)
    rw [hcard, Finset.card_singleton]

/-- **THE COVERED COLOUR-`i` NEIGHBOURHOOD OF A LEAF IS THE SINGLETON `{centre}`.**  The form of
`coverNbrs_card_one_of_mem_card_two` used downstream: the two edges of a two-edge path of the
induced colouring are exactly the two edges of the member of the family which carries them. -/
theorem coverNbrs_eq_singleton_of_card_two {n k : ℕ} {F : Fam n k} (hok : OkF F) (hL : LinF F)
    (hS : SlotFree F) {d i : Fin k} {v a : Verts n} (hc : (coverNbrs F d i v).card = 2)
    (ha : a ∈ coverNbrs F d i v) : coverNbrs F d i a = {v} := by
  obtain ⟨-, hcol, hcov⟩ := mem_coverNbrs.mp ha
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp
    (coverNbrs_card_one_of_mem_card_two hok hL hS hc ha)
  have hvb : v = b := Finset.mem_singleton.mp (hb ▸ ((mem_coverNbrs).mpr
    ⟨(mem_coverNbrs.mp ha).1.symm, by rw [Sym2.eq_swap]; exact hcol,
      by rw [Sym2.eq_swap]; exact hcov⟩))
  rw [hb, hvb]


/-! ## 5. The finished colouring: `Tile` and `Packed` are free

Let `c := extendColDep (colOf F d) (leftoverF F) g` be the colouring of `K_n` obtained by giving
every **leftover** edge a fresh colour (`g`), keeping the first-stage colours on the covered edges.
This section proves that **`Tile c` and `Packed c` follow from `OkF + LinF + SlotFree + Proper`
alone**, i.e. from the matching conditions of the first stage and the properness of the second:

* `finCol`, `mem_Nbrs_finCol` — the bridge: the colour-`i` neighbourhood of `v` in the *finished*
  colouring, for a first-stage colour `i`, is exactly `coverNbrs F d i v`.  (A leftover edge never
  receives a first-stage colour, so nothing else enters the neighbourhood.);
* `fresh_cover` / `card_le_one_of_fresh` — a **fresh** colour has colour-degree at most one,
  because `Proper` forbids two adjacent leftover edges from sharing a fresh colour;
* **`tile_of_fam_partial`** — `Tile c`: the degree half from `coverNbrs_card_le_two`, the leaf half
  from `coverNbrs_card_one_of_mem_card_two`, and the fresh case from `Proper`;
* `twoA_card_two_mem` — `v ∈ twoA c i ↔ (Nbrs c i v).card = 2`;
* **`packed_of_fam_partial`** — `Packed c`: every two-edge path of the finished colouring is the
  vertex set of the member of `F` which carries it (`pathSet_eq_cfgVerts`), and the triples of a
  family are linear (`cfgVerts_lin`);
* **`FamPartialFamily`** and **`jsp_000140_main_of_fam_partial_family`** — the required theorem
  reduced to the existence of a matching in the auxiliary hypergraph **with an arbitrary
  leftover**: this is the interface the published construction (arXiv:2208.12563 §4: the matching
  stops at `i_max = ⅙n²(1-n^{-δ})`, leaving `Θ(n^{2-δ})` edges for the second stage) actually has. -/

/-- The first-stage colour `i` seen inside the enlarged palette `Fin (k + K)`. -/
def finCol {k K : ℕ} (i : Fin k) : Fin (k + K) :=
  ⟨i.val, lt_of_lt_of_le i.isLt (Nat.le_add_right k K)⟩

@[simp] theorem val_finCol {k K : ℕ} (i : Fin k) : (finCol (k := k) (K := K) i).val = i.val := rfl

/-- **AN EDGE OF THE LEFTOVER NEVER RECEIVES A FIRST-STAGE COLOUR.** -/
theorem extendColDep_finCol_of_leftover {n k K : ℕ} {F : Fam n k} {d : Fin k}
    {g : ∀ e, e ∈ leftoverF F → Fin K} {e : Sym2 (Verts n)} (he : e ∈ leftoverF F) {i : Fin k} :
    extendColDep (colOf F d) (leftoverF F) g e ≠ finCol (k := k) (K := K) i := by
  rw [extendColDep_of_mem he]
  intro hcon
  have := congrArg Fin.val hcon
  rw [freshCol_val, val_finCol] at this
  omega

/-- Two mutually including finsets have the same cardinality. -/
theorem card_eq_of_subset_antisymm {α : Type*} {s t : Finset α} (h1 : s ⊆ t) (h2 : t ⊆ s) :
    s.card = t.card := Nat.le_antisymm (Finset.card_le_card h1) (Finset.card_le_card h2)

/-- **AN EDGE WHICH IS NOT IN THE LEFTOVER IS COVERED.** -/
theorem covered_of_nmem_leftoverF {n k : ℕ} {F : Fam n k}
    {a b : Verts n} (hne : a ≠ b) (hL : s(a, b) ∉ leftoverF F) : s(a, b) ∈ coveredF F := by
  by_contra hc
  have h1 : s(a, b) ∈ leftoverF F := mem_leftoverF.mpr
    ⟨mem_edgeFinset_mk (Finset.mem_univ _) (Finset.mem_univ _) hne, fun hh => hc hh⟩
  exact hL h1

/-- **THE COLOUR-`i` NEIGHBOURHOOD OF THE FINISHED COLOURING IS THE COVERED ONE.**  For a first-stage
colour `i` and two distinct vertices `v a`,

    a is an `i`-neighbour of `v` in the finished colouring  ⟺  a is a covered `i`-neighbour.

This is the bridge between the matching world (`coverNbrs`) and the colouring world (`Nbrs`). -/
theorem mem_Nbrs_finCol {n k K : ℕ} {F : Fam n k} (hok : OkF F) {d : Fin k}
    {g : ∀ e, e ∈ leftoverF F → Fin K} {i : Fin k} {v a : Verts n} (hav : a ≠ v) :
    a ∈ Nbrs (extendColDep (colOf F d) (leftoverF F) g) (finCol (k := k) (K := K) i) v ↔
      a ∈ coverNbrs F d i v := by
  rw [mem_Nbrs, mem_coverNbrs]
  constructor
  · rintro ⟨-, heq⟩
    by_cases hL : s(v, a) ∈ leftoverF F
    · exact absurd heq (extendColDep_finCol_of_leftover hL)
    · have h1 : extendColDep (colOf F d) (leftoverF F) g (s(v, a)) =
          liftCol (colOf F d) (Nat.le_add_right k K) (s(v, a)) := extendColDep_of_nmem hL
      have hval : (colOf F d (s(v, a))).val = i.val := by
        have h2 := congrArg Fin.val (h1.symm.trans heq)
        rw [val_finCol] at h2
        exact h2
      exact ⟨hav, Fin.ext hval, covered_of_nmem_leftoverF hav.symm hL⟩
  · rintro ⟨-, hc, hcov⟩
    have hnotL : s(v, a) ∉ leftoverF F := by
      intro hL
      exact (mem_leftoverF.mp hL).2 hcov
    have h1 : extendColDep (colOf F d) (leftoverF F) g (s(v, a)) =
        liftCol (colOf F d) (Nat.le_add_right k K) (s(v, a)) := extendColDep_of_nmem hnotL
    refine ⟨hav, ?_⟩
    rw [h1]
    apply Fin.ext
    show (colOf F d (s(v, a))).val = i.val
    rw [hc]

/-- **THE CARDINALITY FORM OF THE BRIDGE.** -/
theorem card_Nbrs_finCol {n k K : ℕ} {F : Fam n k} (hok : OkF F) {d : Fin k}
    {g : ∀ e, e ∈ leftoverF F → Fin K} {i : Fin k} {v : Verts n} :
    (Nbrs (extendColDep (colOf F d) (leftoverF F) g) (finCol (k := k) (K := K) i) v).card
      = (coverNbrs F d i v).card := by
  have h1 : Nbrs (extendColDep (colOf F d) (leftoverF F) g) (finCol (k := k) (K := K) i) v
      ⊆ coverNbrs F d i v := by
    intro a ha
    exact (mem_Nbrs_finCol hok (mem_Nbrs.mp ha).1).mp ha
  have h2 : coverNbrs F d i v
      ⊆ Nbrs (extendColDep (colOf F d) (leftoverF F) g) (finCol (k := k) (K := K) i) v := by
    intro a ha
    exact (mem_Nbrs_finCol hok (mem_coverNbrs.mp ha).1).mpr ha
  exact Nat.le_antisymm (Finset.card_le_card h1) (Finset.card_le_card h2)

/-- **A FRESH COLOUR HAS COLOUR-DEGREE AT MOST ONE.**  `Proper` says two leftover edges sharing a
vertex get different fresh colours, so no vertex sees two fresh edges of one colour. -/
theorem card_le_one_of_fresh {n k K : ℕ} {F : Fam n k} {d : Fin k}
    {g : ∀ e, e ∈ leftoverF F → Fin K}
    (hproper : Proper (extendColDep (colOf F d) (leftoverF F) g) (leftoverF F))
    {i : Fin (k + K)} (hi : k ≤ i.val) (v : Verts n) :
    (Nbrs (extendColDep (colOf F d) (leftoverF F) g) i v).card ≤ 1 := by
  by_contra hcon
  obtain ⟨a, b, hab, ha, hb⟩ :=
    exists_two_of_card_ge_two
      (by omega : 2 ≤ (Nbrs (extendColDep (colOf F d) (leftoverF F) g) i v).card)
  obtain ⟨-, hceq⟩ := mem_Nbrs.mp ha
  obtain ⟨-, hceq'⟩ := mem_Nbrs.mp hb
  have hcov : s(v, a) ∈ leftoverF F := by
    by_cases hL : s(v, a) ∈ leftoverF F
    · exact hL
    · exfalso
      have h1 : (colOf F d (s(v, a))).val = i.val :=
        congrArg Fin.val ((extendColDep_of_nmem hL).symm.trans hceq)
      have h2 : (colOf F d (s(v, a))).val < k := (colOf F d (s(v, a))).isLt
      omega
  have hcov' : s(v, b) ∈ leftoverF F := by
    by_cases hL : s(v, b) ∈ leftoverF F
    · exact hL
    · exfalso
      have h1 : (colOf F d (s(v, b))).val = i.val :=
        congrArg Fin.val ((extendColDep_of_nmem hL).symm.trans hceq')
      have h2 : (colOf F d (s(v, b))).val < k := (colOf F d (s(v, b))).isLt
      omega
  have hne : s(v, a) ≠ s(v, b) := by
    intro h
    exact hab (sym2_inj_right h)
  exact hproper (s(v, a)) hcov (s(v, b)) hcov' hne
    ⟨v, Sym2.mem_mk_left v a, Sym2.mem_mk_left v b⟩ (hceq.trans hceq'.symm)

/-- **THE TILING CONDITION OF THE FINISHED COLOURING IS FREE.**  `OkF + LinF + SlotFree + Proper`
give `Tile c` for the colouring `c` obtained by colouring the leftover with fresh colours — **no
`Covers` hypothesis and no bound on the leftover**. -/
theorem tile_of_fam_partial {n k K : ℕ} {F : Fam n k} (hok : OkF F) (hL : LinF F) (hS : SlotFree F)
    {d : Fin k} {g : ∀ e, e ∈ leftoverF F → Fin K}
    (hproper : Proper (extendColDep (colOf F d) (leftoverF F) g) (leftoverF F)) :
    Tile (extendColDep (colOf F d) (leftoverF F) g) := by
  intro i v
  by_cases hi : i.val < k
  · have hNbrs : (Nbrs (extendColDep (colOf F d) (leftoverF F) g) i v).card =
        (coverNbrs F d ⟨i.val, hi⟩ v).card :=
      card_Nbrs_finCol (K := K) (d := d) (g := g) (i := ⟨i.val, hi⟩) (v := v) hok
    refine ⟨?_, ?_⟩
    · rw [hNbrs]
      exact coverNbrs_card_le_two hok hL hS v
    · intro a ha hcard
      have ha' : a ∈ coverNbrs F d ⟨i.val, hi⟩ v :=
        (mem_Nbrs_finCol (K := K) (d := d) (g := g) (v := v) hok (mem_Nbrs.mp ha).1).mp ha
      have hc2 : (coverNbrs F d ⟨i.val, hi⟩ v).card = 2 := by
        rw [← hNbrs]
        exact hcard
      have h1 : (coverNbrs F d ⟨i.val, hi⟩ a).card = 1 :=
        coverNbrs_card_one_of_mem_card_two hok hL hS hc2 ha'
      have hNa : (Nbrs (extendColDep (colOf F d) (leftoverF F) g) i a).card =
          (coverNbrs F d ⟨i.val, hi⟩ a).card :=
        card_Nbrs_finCol (K := K) (d := d) (g := g) (i := ⟨i.val, hi⟩) (v := a) hok
      rw [hNa, h1]
  · have h1 := card_le_one_of_fresh hproper (Nat.le_of_not_gt hi) v
    refine ⟨Nat.le_succ_of_le h1, ?_⟩
    intro a ha hcard
    omega

/-- **A VERTEX HAS TWO NEIGHBOURS OF ONE COLOUR IN THE FINISHED COLOURING.** -/
theorem mem_twoA_card_two {c : Col n k} {i : Fin k} {v : Verts n} :
    v ∈ twoA c i ↔ (Nbrs c i v).card = 2 := by
  rw [twoA, Finset.mem_filter, card_Nbrs]
  constructor
  · rintro ⟨-, h2⟩
    exact h2
  · intro h2
    exact ⟨Finset.mem_univ _, h2⟩

/-- **THE TWO-EDGE PATHS OF THE FINISHED COLOURING ARE THE MEMBERS OF THE FAMILY.**  If `v` has two
neighbours of colour `i` in the finished colouring, then `i` is a first-stage colour, `v` is the
centre of the member `g₀` of `F` holding the slot `(v,i)`, and the two-edge path centred at `v` is
exactly the three vertices of that member.  This is the bridge between the two-edge paths of the
finished colouring and the triangles of the matching. -/
theorem pathSet_eq_cfgVerts {n k K : ℕ} {F : Fam n k} (hok : OkF F) (hL : LinF F) (hS : SlotFree F)
    {d : Fin k} {g : ∀ e, e ∈ leftoverF F → Fin K}
    (hproper : Proper (extendColDep (colOf F d) (leftoverF F) g) (leftoverF F))
    {i : Fin (k + K)} {v : Verts n}
    (hv : (Nbrs (extendColDep (colOf F d) (leftoverF F) g) i v).card = 2) :
    ∃ g₀ : Cfg n k, g₀ ∈ F ∧ i = finCol (k := k) (K := K) (cfgI g₀) ∧ v = cfgU g₀ ∧
      pathSet (extendColDep (colOf F d) (leftoverF F) g) i v = cfgVerts g₀ := by
  have hilt : i.val < k := by
    by_contra hc
    have h1 := card_le_one_of_fresh hproper (Nat.le_of_not_gt hc) v
    omega
  have hi' : i = finCol (k := k) (K := K) ⟨i.val, hilt⟩ := by
    apply Fin.ext
    exact rfl
  have hNbrs : Nbrs (extendColDep (colOf F d) (leftoverF F) g) i v =
      coverNbrs F d ⟨i.val, hilt⟩ v :=
    Finset.Subset.antisymm
      (by
        intro a ha
        exact (mem_Nbrs_finCol (K := K) (d := d) (g := g) (i := ⟨i.val, hilt⟩) (v := v) hok
          (mem_Nbrs.mp ha).1).mp ha)
      (by
        intro a ha
        exact (mem_Nbrs_finCol (K := K) (d := d) (g := g) (i := ⟨i.val, hilt⟩) (v := v) hok
          (mem_coverNbrs.mp ha).1).mpr ha)
  obtain ⟨g₀, hg₀, hslot, hvU, hiI, hpair⟩ :=
    coverNbrs_eq_pair_of_card_two hok hL hS (by
      rw [← hNbrs]
      exact hv)
  refine ⟨g₀, hg₀, ?_, hvU, ?_⟩
  · apply Fin.ext
    show i.val = (cfgI g₀).val
    exact congrArg Fin.val hiI
  rw [pathSet, hNbrs, hpair, hvU, cfgVerts, triVerts]
  rfl

/-- **THE PACKING CONDITION OF THE FINISHED COLOURING IS FREE.**  Two two-edge paths of the finished
colouring are the vertex sets of two members of `F`, and the triples of a family are linear
(`cfgVerts_lin`), so two distinct paths cannot share two vertices. -/
theorem packed_of_fam_partial {n k K : ℕ} {F : Fam n k} (hok : OkF F) (hL : LinF F) (hS : SlotFree F)
    {d : Fin k} {g : ∀ e, e ∈ leftoverF F → Fin K}
    (hproper : Proper (extendColDep (colOf F d) (leftoverF F) g) (leftoverF F)) :
    Packed (extendColDep (colOf F d) (leftoverF F) g) := by
  intro i j v w hv hw hinter
  obtain ⟨g, hg, hi_eq, hvg, hps1⟩ :=
    pathSet_eq_cfgVerts hok hL hS hproper ((mem_twoA_card_two).mp hv)
  obtain ⟨g', hg', hj_eq, hwg, hps2⟩ :=
    pathSet_eq_cfgVerts hok hL hS hproper ((mem_twoA_card_two).mp hw)
  have hinter' : 2 ≤ (cfgVerts g ∩ cfgVerts g').card := by
    rw [← hps1, ← hps2]
    exact hinter
  have heq : g = g' := by
    by_contra hc
    have hcard := cfgVerts_lin hL hg hg' hc
    omega
  have hfin : i = j := by
    rw [hi_eq, hj_eq, heq]
  exact hfin


/-! ## 6. The required theorem, reduced to the first stage with an arbitrary leftover -/

/-- **THE PUBLISHED CONSTRUCTION, IN THE FORM THE CONSTRUCTION PRODUCES IT.**  For every `δ > 0` and
all large `m ≡ 1 (mod 6)` there is a *matching* `F` in the auxiliary hypergraph of arXiv:2208.12563
§4 (= arXiv:2207.02920 Phase 1) — configurations on `k` colours, pairwise edge-disjoint and
slot-disjoint — such that

* the leftover `leftoverF F` has maximum degree `≤ D` (JM (IV) of Thm 4.2 = BCDP Claim 4);
* the second stage is **proper** on the leftover (`Proper`, the family `A_{e,f,i}` resp. `B₁`);
* the **finished** colouring `extendColDep (colOf F d) (leftoverF F) g` has no bad and no crossing
  four-set (the families `B₂, B₃` resp. `B_D, C_{D,i}`, excluded by the local lemma);
* the total number of colours is at most `5(m-1)/6 + δm/6`.

**No colouring is quantified over**: `F` is a finset of configurations, a finite combinatorial
object, and `g` is its second-stage colouring, so the hypothesis is checkable.  Note that the
covering is *partial*, as in the paper: no `(leftoverF F) = ∅` appears. -/
def FamPartialFamily : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ M D K : ℕ, ∀ m : ℕ, M ≤ m → m % 6 = 1 →
    ∃ (k : ℕ) (F : Fam m k) (d : Fin k) (g : ∀ e, e ∈ leftoverF F → Fin K),
      OkF F ∧ LinF F ∧ SlotFree F ∧ SparseL (leftoverF F) D ∧
      Proper (extendColDep (colOf F d) (leftoverF F) g) (leftoverF F) ∧
      NoCrossFour (extendColDep (colOf F d) (leftoverF F) g) ∧
      NoBadFour (extendColDep (colOf F d) (leftoverF F) g) ∧
      (6 : ℝ) * ((k + K : ℕ) : ℝ) ≤ 5 * ((m - 1 : ℕ) : ℝ) + δ * (m : ℝ)

/-- **THE CONSTRUCTION HYPOTHESIS GIVES THE ADMISSIBLE COLOURING.**  The two local conditions which
a matching forces — `Tile` and `Packed` (sections 4 and 5) — are combined with the two
four-set conditions of the hypothesis by `Criterion.admissible_of_design`. -/
theorem FamPartialFamily.admissible {m D k : ℕ} {F : Fam m k} {d : Fin k}
    {g : ∀ e, e ∈ leftoverF F → Fin K}
    (hok : OkF F) (hL : LinF F) (hS : SlotFree F) (hsp : SparseL (leftoverF F) D)
    (hproper : Proper (extendColDep (colOf F d) (leftoverF F) g) (leftoverF F))
    (hX : NoCrossFour (extendColDep (colOf F d) (leftoverF F) g))
    (hB : NoBadFour (extendColDep (colOf F d) (leftoverF F) g)) :
    Admissible (extendColDep (colOf F d) (leftoverF F) g) :=
  admissible_of_design (tile_of_fam_partial hok hL hS hproper)
    (packed_of_fam_partial hok hL hS hproper) hX hB

/-- **`FamPartialFamily` IS A CONSTRUCTION HYPOTHESIS OF THE PUBLISHED SHAPE.** -/
theorem FamPartialFamily.slack (h : FamPartialFamily) : SlackFamily := by
  intro δ hδ
  obtain ⟨M, D, K, hM⟩ := h δ hδ
  refine ⟨M + 7, fun m hMm hm => ?_⟩
  obtain ⟨k, F, d, g, hok, hL, hS, hsp, hproper, hX, hB, hk⟩ := hM m (by omega) hm
  exact ⟨k + K, extendColDep (colOf F d) (leftoverF F) g,
    FamPartialFamily.admissible hok hL hS hsp hproper hX hB, hk⟩

/-- **THE REQUIRED THEOREM `jsp_000140_main`, REDUCED TO THE FIRST STAGE WITH AN ARBITRARY
LEFTOVER.**  What is left of the catalog problem is the existence, for every `δ > 0` and all large
`m ≡ 1 (mod 6)`, of a matching in the auxiliary hypergraph of arXiv:2208.12563 §4 which leaves a
sparse leftover and whose second stage is proper and free of bad and crossing four-sets — i.e. the
first stage plus the two local lemmas of §4 of that paper.  **Everything else is proved here**:
the colouring induced by the matching, the fact that `Tile` and `Packed` hold for the finished
colouring whatever the leftover is, and hence the catalog condition itself. -/
theorem jsp_000140_main_of_fam_partial_family (h : FamPartialFamily) : jsp_000140_target :=
  jsp_000140_main_of_slack_family h.slack


/-! ## 7. The second stage is deterministic: `Proper` is free -/

/-- **THE GREEDY SECOND STAGE.**  If the leftover of a first stage has maximum degree `D`, the
greedy edge colouring of `Second.proper_of_sparseL` gives a function
`leftoverF F → Fin (2D+1)`.  This is the deterministic half of the second stage of arXiv:2208.12563
§4: the bad events `A_{e,f,i}` (resp. `B₁` of arXiv:2207.02920 §12) are excluded **without any
probability**, and the number of extra colours is `2Δ+1 = O(n^{1-δ}) = o(n)`. -/
noncomputable def greedyF {n k D : ℕ} {F : Fam n k} (hD : SparseL (leftoverF F) D) :
    ∀ e, e ∈ leftoverF F → Fin (2 * D + 1) :=
  fun e h => (proper_of_sparseL hD).choose ⟨e, h⟩

/-- **THE GREEDY SECOND STAGE IS PROPER.** -/
theorem proper_greedyF {n k D : ℕ} {F : Fam n k} (hD : SparseL (leftoverF F) D) {d : Fin k} :
    Proper (extendColDep (colOf F d) (leftoverF F) (greedyF hD)) (leftoverF F) := by
  intro e he e' he' hne hsh
  rw [extendColDep_of_mem he, extendColDep_of_mem he']
  intro hcon
  have hval : (greedyF hD e he).val = (greedyF hD e' he').val := by
    have h := congrArg Fin.val hcon
    simpa using h
  exact (proper_of_sparseL hD).choose_spec ⟨e, he⟩ ⟨e', he'⟩
    (fun h => hne (congrArg Subtype.val h))
    (show Shares (⟨e, he⟩ : {e // e ∈ leftoverF F}).1 (⟨e', he'⟩ : {e // e ∈ leftoverF F}).1
      from hsh) (Fin.ext hval)

/-- **THE PUBLISHED CONSTRUCTION WITH THE SECOND STAGE FIXED BY THE GREEDY RULE.**  As
`FamPartialFamily`, but the properness of the second stage is **not** a hypothesis: it is a
consequence of the sparsity of the leftover (`proper_greedyF`), at the cost of `2D+1` fresh
colours, which is exactly what arXiv:2208.12563 §4 uses.  What is left as a hypothesis is the
first stage itself (`OkF + LinF + SlotFree`, leftover of maximum degree `D`) together with the two
four-set conditions `B_D` and `C_{D,i}` of the finished colouring — the only genuinely
probabilistic part of arXiv:2208.12563 §4 / arXiv:2207.02920 §12. -/
def FamGreedyFamily : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ M D : ℕ, ∀ m : ℕ, M ≤ m → m % 6 = 1 →
    ∃ (k : ℕ) (F : Fam m k) (d : Fin k) (hD : SparseL (leftoverF F) D),
      OkF F ∧ LinF F ∧ SlotFree F ∧
      NoCrossFour (extendColDep (colOf F d) (leftoverF F) (greedyF hD)) ∧
      NoBadFour (extendColDep (colOf F d) (leftoverF F) (greedyF hD)) ∧
      (6 : ℝ) * ((k + 2 * D + 1 : ℕ) : ℝ) ≤ 5 * ((m - 1 : ℕ) : ℝ) + δ * (m : ℝ)

/-- **`FamGreedyFamily` IS A `FamPartialFamily`.**  The deterministic second stage is proper by
`proper_greedyF`. -/
theorem famGreedyFamily_partial (h : FamGreedyFamily) : FamPartialFamily := by
  intro δ hδ
  obtain ⟨M, D, hM⟩ := h δ hδ
  refine ⟨M, D, 2 * D + 1, fun m hMm hm => ?_⟩
  obtain ⟨k, F, d, hD, hok, hL, hS, hX, hB, hk⟩ := hM m hMm hm
  exact ⟨k, F, d, greedyF hD, hok, hL, hS, hD, proper_greedyF hD, hX, hB, hk⟩

/-- **THE REQUIRED THEOREM, REDUCED TO THE FIRST STAGE PLUS TWO FOUR-SET CONDITIONS.**  Nothing but
the probabilistic content of arXiv:2208.12563 §4 is left: a matching in the auxiliary hypergraph,
its leftover degree, and the exclusion of the alternating four-cycles (`B_D`) and of the crossing
pairs (`C_{D,i}`) by the second stage. -/
theorem jsp_000140_main_of_greedy_family (h : FamGreedyFamily) : jsp_000140_target :=
  jsp_000140_main_of_fam_partial_family (famGreedyFamily_partial h)

end JSP140
