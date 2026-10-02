import JSPProblem.Spoil

/-!
# JSP-000140 — round 42: the **edge census of the auxiliary hypergraph** `H`, and the first
# **per-vertex** and **per-edge** constraints on a matching in it

Rounds 40 and 41 computed two of the three local data of `H` of arXiv:2208.12563 §4 = arXiv:2207.02920
Phase 1: the hypervertex degrees (`Hyper.card_auxDeg_le`) and the four-set census
(`Spoil.card_auxF_four`); and both retired a deterministic matching rule *by theorem*.  The third
local datum — the number of hyperedges through a **given edge of `K_n`** — had never been computed,
and it is computed here, exactly.

## §1 — the three roles of an edge in a configuration

* `mem_cfgEdges_eq` — an edge of a configuration is one of its two spokes or its opposite edge;
* `eq_spk`, `eq_sqk`, `eq_sqp` — the endpoints of `s(a,b)` are the two named vertices, in one of the
  two orders (`Sym2.eq_iff`).

## §2 — the edge census of `H`

* `card_auxF_spoke1`, `card_auxF_spoke2`, `card_auxF_opp` — **the census of each role**: exactly
  `2(n-2)k(k-1)` hyperedges of `H` have `s(a,b)` as their first spoke, as their second spoke, or as
  their opposite edge (two orientations, `n-2` free vertices, `k(k-1)` colour pairs);
* **`card_auxF_edge` — THE EDGE CENSUS OF `H`: EXACTLY `6(n-2)k(k-1)` HYPEREDGES OF `H` CONTAIN A
  GIVEN EDGE OF `K_n`.**  With `Hyper.card_auxDeg_le` (hypervertex degrees) and
  `Spoil.card_auxF_four` (four-set census) this is the **complete local census of `H`**;
* **`auxF_edge_double` — the census is consistent**: summed over the `C(n,2)` edges it returns
  `3·|E(H)|`, as it must, every hyperedge having three edges.

## §3 — the members of a family covering a given edge

* `coverF F e`, and the three classes `coverA`, `coverB`, `coverC` (`a`-central, `b`-central,
  leaf-only);
* **`coverF_role` — THE ROLE ANALYSIS**, `coverF_leaf` — a covering member in which `a` is not the
  centre has `a` as a leaf, `coverBC_leaf` — and it uses **both** colour slots at `a`;
* `coverA_slot`, `coverBC_mem`, `coverF_eq_three` (the three classes partition the covering members).

## §4 — the slots of a family at one vertex

* `SlotsAtF F v`, `slotPair g` (the pair of slots a leaf-membership uses);
* **`card_SlotsAtF` — THE PER-VERTEX SLOT COUNT**: the slots of a family at `v` are at most the
  members centred at `v` (one slot each) plus twice the members having `v` as a leaf (two slots
  each) — the first constraint on a matching that goes beyond the global `5|F| ≤ nk`;
* `sum_single_fibre`, **`sum_centreF_card`**, **`card_leafF`**, **`sum_leafF_card`** and
  **`sum_slots_at_card`**: `Σ_v (|centF F v| + 2·|leafF F v|) = 5·|F|`, the per-vertex form of
  `Fam.card_SlotsF`, proved vertex by vertex.

## §5 — the per-vertex slot budget (round 43, the round-42 `next_lemma`)

* `injOn_col_slotsF`, `SlotsAtF_eq`, **`card_SlotsAtF_eq`** — the *colours* used at `v` number one
  per member centred at `v` and two per member having `v` as a leaf (round 42 could only prove `≤`,
  not knowing that the colour projection of the slots at `v` is injective);
* **`slots_at_le` — THE PER-VERTEX SLOT BUDGET: `|centF F v| + 2·|leafF F v| ≤ k`**, i.e.
  `Fam.slots_countF` pointwise, with `leafF_card_le`, `centF_card_le`, `mem_slotPair`, `card_slotPair`
  and `mem_cfgSlots_leaf` as the ingredients (slot-freeness applied one vertex and one colour at a
  time).

## §6 — the per-edge budget

* `s_swap`, `coverF_swap`, `coverF_leaf'`, `coverF_leaf''`, `cover_ABC_disj`, `card_coverF_eq_three`
  (the three classes `coverA/coverB/coverC` partition the covering members);
* `class_slots_le` (private engine) and `coverA_card_le` / `coverB_card_le`;
* **`coverF_card_le` — NO EDGE IS COVERED BY MORE THAN `2k/3` MEMBERS: `3·|coverF F (s(a,b))| ≤ 2k`**,
  and `coverF_card_le'` (at most `k`).

## §7 — the per-vertex edge accounting

* `spokes`, `card_spokes`, `edgesAt`, `card_edgesAt`, `mem_edgesAt`, `covAt`, **`card_covAt` — TWO
  EDGES AT EVERY VERTEX OF A CONFIGURATION** (a member covers two of its three edges at each of its
  vertices — the correction of round 43: at a *leaf* the two are the spoke and the opposite edge);
* `card_throughF`, `covAll`, **`card_covAll` — `2·(|centF F v| + |leafF F v|)`**;
* **`covAll_eq_inter` — the covered edges through `v` are exactly `edgesAt v ∩ coveredF F`**;
  `covR`, `card_covR`, `covAll_covR_disj`, `edgesAt_eq_union`;
* **`degL_at` — THE PER-VERTEX EDGE ACCOUNTING: `n - 1 = 2·(|centF F v| + |leafF F v|) + DegL (leftoverF F) v`**,
  the local form of `Fam.edgeCoverF`.

## §8 — the density a sparse leftover forces

* **`throughF_card_ge` — `2·(|centF F v| + |leafF F v|) ≥ (n-1) - D`**: `v` is passed through by at
  least `⌈((n-1-D)/2)⌉` members (JM (IV) / BCDP Claim 4, per vertex);
* **`centF_card_ge` — `|centF F v| ≥ (n-1-D) - k`** and `leafF_card_ge`: the local form of the slot
  counting `First.count_lower`; a first stage cannot hide its work at a few centres;
* **`centF_card_ge_one` / `centre_cover_univ` — THE CENTRES COVER ALL VERTICES as soon as
  `(n-1) - D > k`**, and `sum_centF_card_ge` (the global `|F| ≥ n(n-1-D-k)`).

## what is still missing

The existence of the matching itself (`Partial.FamGreedyFamily`): rounds 40 and 41 retired the greedy
and the greedy-with-avoidance rules by theorem, and rounds 42–43 show that a *near-perfect* matching
with a sparse leftover must satisfy two further local constraints that no maximality argument can
produce (a centre at every vertex; `3·|coverF F e| ≤ 2k`).  The gap is the Rödl nibble, which Mathlib
does not contain.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace JSP140

attribute [local instance] Classical.propDecidable

variable {n k : ℕ}

/-! ### 0. Counting tools -/

/-- **THE TWO ORDERINGS OF THE ENDPOINTS OF AN EDGE.** -/
noncomputable def endsPair {n : ℕ} (a b : Verts n) : Finset (Verts n × Verts n) :=
  insert (a, b) (insert (b, a) ∅)

@[simp] theorem mem_endsPair {n : ℕ} {a b : Verts n} {t : Verts n × Verts n} :
    t ∈ endsPair a b ↔ t = (a, b) ∨ t = (b, a) := by
  simp [endsPair]

/-- **AN EDGE HAS EXACTLY TWO ORDERINGS OF ITS ENDPOINTS.** -/
theorem card_endsPair {n : ℕ} (a b : Verts n) (hab : a ≠ b) : (endsPair a b).card = 2 := by
  have h1 : (a, b) ∉ insert (b, a) (∅ : Finset (Verts n × Verts n)) := by
    intro hmem
    rcases Finset.mem_insert.mp hmem with hmem | hmem
    · exact hab (congrArg Prod.fst hmem)
    · exact absurd hmem (by simp)
  rw [endsPair, Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem (by simp),
    Finset.card_empty]

/-- **THE VERTICES OTHER THAN TWO GIVEN ONES.** -/
noncomputable def freeVerts {n : ℕ} (a b : Verts n) : Finset (Verts n) :=
  (Finset.univ : Finset (Verts n)).filter (fun x => x ≠ a ∧ x ≠ b)

@[simp] theorem mem_freeVerts {n : ℕ} {a b : Verts n} {x : Verts n} :
    x ∈ freeVerts a b ↔ x ≠ a ∧ x ≠ b := by
  rw [freeVerts, Finset.mem_filter]
  exact Iff.intro (fun h => h.2) (fun h => ⟨Finset.mem_univ x, h⟩)

/-- **`n - 2` VERTICES ARE LEFT OVER AFTER FIXING THE ENDPOINTS OF AN EDGE.** -/
theorem card_freeVerts {n : ℕ} (a b : Verts n) (hab : a ≠ b) : (freeVerts a b).card = n - 2 := by
  have h1 : freeVerts a b
      = ((Finset.univ : Finset (Verts n)).filter (fun x => x ≠ a)).filter (fun x => x ≠ b) := by
    ext x
    simp only [mem_freeVerts, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [h1, card_filter_ne (A := (Finset.univ : Finset (Verts n)).filter (fun x => x ≠ a))
      (a := b) (Finset.mem_filter.mpr ⟨Finset.mem_univ b, Ne.symm hab⟩),
    card_filter_ne (A := (Finset.univ : Finset (Verts n))) (a := a) (Finset.mem_univ a),
    Finset.card_univ, Fintype.card_fin]
  omega

/-- **THE ORDERED PAIRS OF DISTINCT COLOURS.** -/
noncomputable def colourPairs (k : ℕ) : Finset (Fin k × Fin k) :=
  (Finset.univ : Finset (Fin k × Fin k)).filter (fun t => t.1 ≠ t.2)

@[simp] theorem mem_colourPairs {k : ℕ} {i j : Fin k} : (i, j) ∈ colourPairs k ↔ i ≠ j := by
  simp [colourPairs]

theorem card_colourPairs (k : ℕ) : (colourPairs k).card = k * (k - 1) := by
  simpa [colourPairs, Finset.card_univ, Fintype.card_fin] using
    (card_offdiag_of (A := (Finset.univ : Finset (Fin k))))

/-- The indicator of `x = b`, summed over `b`, is `1`. -/
private theorem sum_ite_eq_one {β : Type*} [Fintype β] [DecidableEq β] (x : β) :
    ∑ b ∈ (Finset.univ : Finset β), ((if x = b then 1 else 0 : ℕ)) = 1 := by
  have key : ∀ b : β, b ∈ (Finset.univ : Finset β) → b ≠ x → (if x = b then 1 else 0 : ℕ) = 0 := by
    intro b _ hbne
    rw [if_neg (fun h => hbne h.symm)]
  have key2 : x ∉ (Finset.univ : Finset β) → (if x = x then 1 else 0 : ℕ) = 0 := by
    intro h
    exfalso
    exact absurd h (fun hm => hm (Finset.mem_univ x))
  rw [Finset.sum_eq_single (M := ℕ) (s := (Finset.univ : Finset β))
    (f := fun b : β => (if x = b then 1 else 0 : ℕ)) x key key2, if_pos rfl]

/-- The filter of a single value of a function has one element. -/
private theorem card_filter_single {β : Type*} [Fintype β] [DecidableEq β] (x : β) :
    (Finset.filter (fun b : β => x = b) (Finset.univ : Finset β)).card = 1 := by
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact sum_ite_eq_one x

/-- The cardinality of a filter, as a sum of indicators. -/
private theorem card_filter_ite {α β : Type*} [Fintype β] [DecidableEq β] (s : Finset α)
    (f : α → β) (b : β) :
    (s.filter (fun a => f a = b)).card = ∑ a ∈ s, ((if f a = b then 1 else 0 : ℕ)) := by
  rw [Finset.card_eq_sum_ones]
  rw [Finset.sum_filter]

/-- **THE DOUBLE COUNT IN TWO FINITE TYPES.** -/
private theorem sum_swap_ite {α β : Type*} [Fintype β] (s : Finset α) (f : α → β) :
    (∑ b : β, ∑ a ∈ s, ((if f a = b then 1 else 0 : ℕ)))
      = ∑ a ∈ s, ∑ b : β, ((if f a = b then 1 else 0 : ℕ)) :=
  Finset.sum_comm

private theorem disjoint_of_inter_empty {α : Type*} [DecidableEq α] {s t : Finset α}
    (h : s ∩ t = ∅) : Disjoint s t :=
  Finset.disjoint_left.mpr fun ⦃a⦄ ha1 ha2 => by
    have hmem : a ∈ s ∩ t := Finset.mem_inter.mpr ⟨ha1, ha2⟩
    rw [h] at hmem
    simpa using hmem

/-! ### 1. The three roles of an edge inside a configuration -/

/-- **AN EDGE PLAYS ONE OF THE THREE ROLES OF A CONFIGURATION.** -/
@[simp] theorem mem_cfgEdges_eq {n k : ℕ} {g : Cfg n k} {e : Sym2 (Verts n)} :
    e ∈ cfgEdges g ↔ s(cfgU g, cfgP g) = e ∨ s(cfgU g, cfgQ g) = e ∨ s(cfgP g, cfgQ g) = e := by
  rw [mem_cfgEdges]
  constructor
  · rintro (h | h | h)
    · exact Or.inl h.symm
    · exact Or.inr (Or.inl h.symm)
    · exact Or.inr (Or.inr h.symm)
  · rintro (h | h | h)
    · exact Or.inl h.symm
    · exact Or.inr (Or.inl h.symm)
    · exact Or.inr (Or.inr h.symm)

/-- A configuration whose first spoke is `s(a, b)`: its centre and first leaf are `a` and `b`, in one
of the two orders. -/
theorem eq_spk {n : ℕ} {a b : Verts n} {g : Cfg n k} (h : s(cfgU g, cfgP g) = s(a, b)) :
    (cfgU g = a ∧ cfgP g = b) ∨ (cfgU g = b ∧ cfgP g = a) := by
  rcases Sym2.eq_iff.mp h.symm with h1 | h1
  · exact Or.inl ⟨h1.1.symm, h1.2.symm⟩
  · exact Or.inr ⟨h1.2.symm, h1.1.symm⟩

/-- A configuration whose second spoke is `s(a, b)`: its centre and second leaf are `a` and `b`. -/
theorem eq_sqk {n : ℕ} {a b : Verts n} {g : Cfg n k} (h : s(cfgU g, cfgQ g) = s(a, b)) :
    (cfgU g = a ∧ cfgQ g = b) ∨ (cfgU g = b ∧ cfgQ g = a) := by
  rcases Sym2.eq_iff.mp h.symm with h1 | h1
  · exact Or.inl ⟨h1.1.symm, h1.2.symm⟩
  · exact Or.inr ⟨h1.2.symm, h1.1.symm⟩

/-- A configuration whose opposite edge is `s(a, b)`: its two leaves are `a` and `b`. -/
theorem eq_sqp {n : ℕ} {a b : Verts n} {g : Cfg n k} (h : s(cfgP g, cfgQ g) = s(a, b)) :
    (cfgP g = a ∧ cfgQ g = b) ∨ (cfgP g = b ∧ cfgQ g = a) := by
  rcases Sym2.eq_iff.mp h.symm with h1 | h1
  · exact Or.inl ⟨h1.1.symm, h1.2.symm⟩
  · exact Or.inr ⟨h1.2.symm, h1.1.symm⟩

/-! ### 2. The edge census of `H` -/

/-- **THE PARAMETER FINSET OF ONE ROLE:** the two orientations of the edge `s(a,b)`, the third
vertex, and the ordered pair of distinct colours. -/
private noncomputable def roleDomain {n : ℕ} (a b : Verts n) (k : ℕ) :
    Finset (((Verts n × Verts n) × Verts n) × (Fin k × Fin k)) :=
  ((endsPair a b : Finset (Verts n × Verts n)) ×ˢ freeVerts a b) ×ˢ colourPairs k

private theorem card_roleDomain {n : ℕ} (a b : Verts n) (hab : a ≠ b) :
    (roleDomain a b k).card = 2 * ((n - 2) * (k * (k - 1))) := by
  simp only [roleDomain, Finset.card_product]
  rw [card_endsPair a b hab, card_freeVerts a b hab, card_colourPairs k]
  ring

private theorem mem_roleDomain_iff {n k : ℕ} (a b : Verts n)
    (t : ((Verts n × Verts n) × Verts n) × (Fin k × Fin k)) :
    t ∈ roleDomain a b k
      ↔ (t.1.1 ∈ endsPair a b ∧ t.1.2 ∈ freeVerts a b) ∧ t.2 ∈ colourPairs k := by
  rw [roleDomain, Finset.mem_product, Finset.mem_product]

private theorem mem_roleDomain {n k : ℕ} (a b : Verts n)
    (t : ((Verts n × Verts n) × Verts n) × (Fin k × Fin k))
    (h1 : t.1.1 ∈ endsPair a b) (h2 : t.1.2 ∈ freeVerts a b) (h3 : t.2 ∈ colourPairs k) :
    t ∈ roleDomain a b k :=
  (mem_roleDomain_iff a b t).mpr ⟨⟨h1, h2⟩, h3⟩

/-- **THE CENSUS OF ONE ROLE: EXACTLY `2(n-2)k(k-1)` HYPEREDGES OF `H` HAVE `s(a,b)` AS THEIR FIRST
SPOKE.**  Two orientations of the endpoints, `n-2` choices of the third vertex, `k(k-1)` choices of
the ordered colour pair. -/
theorem card_auxF_spoke1 {n k : ℕ} (a b : Verts n) (hab : a ≠ b) :
    ((auxF n k).filter (fun g => s(cfgU g, cfgP g) = s(a, b))).card
      = 2 * ((n - 2) * (k * (k - 1))) := by
  refine (Finset.card_bij (s := roleDomain a b k)
    (t := (auxF n k).filter (fun g => s(cfgU g, cfgP g) = s(a, b)))
    (fun t _ => (t.1.1.1, t.1.1.2, t.1.2, t.2.1, t.2.2)) ?_ ?_ ?_).symm.trans (card_roleDomain a b hab)
  · intro t ht
    obtain ⟨⟨ht1, ht2⟩, ht3⟩ := (mem_roleDomain_iff a b t).mp ht
    obtain ⟨ha, hb⟩ := mem_freeVerts.mp ht2
    have hi : t.2.1 ≠ t.2.2 := mem_colourPairs.mp ht3
    have heq : (t.1.1.1 = a ∧ t.1.1.2 = b) ∨ (t.1.1.1 = b ∧ t.1.1.2 = a) := by
      rcases (mem_endsPair.mp ht1) with h' | h'
      · exact Or.inl ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩
      · exact Or.inr ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩
    rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
      exact Finset.mem_filter.mpr ⟨mem_auxF.mpr (Ok_tuple.mpr
        ⟨hab, ha.symm, hb.symm, hi⟩), rfl⟩
    · rw [h1, h2]
      exact Finset.mem_filter.mpr ⟨mem_auxF.mpr (Ok_tuple.mpr
        ⟨Ne.symm hab, hb.symm, ha.symm, hi⟩), Sym2.eq_swap.symm⟩
  · intro t₁ _ t₂ _ he
    apply Prod.ext
    · apply Prod.ext
      · apply Prod.ext
        · exact congrArg (fun w : Cfg n k => w.1) he
        · exact congrArg (fun w : Cfg n k => w.2.1) he
      · exact congrArg (fun w : Cfg n k => (w.2.2.1 : Verts n)) he
    · apply Prod.ext
      · exact congrArg (fun w : Cfg n k => w.2.2.2.1) he
      · exact congrArg (fun w : Cfg n k => w.2.2.2.2) he
  · intro g hg
    obtain ⟨hg0, hg2⟩ := Finset.mem_filter.mp hg
    have hOk' := Ok_def (mem_auxF.mp hg0)
    rcases eq_spk hg2 with h1 | h1
    · refine ⟨(((cfgU g, cfgP g), cfgQ g), (cfgI g, cfgJ g)), ?_, rfl⟩
      refine (mem_roleDomain_iff a b _).mpr ⟨⟨?_, ?_⟩, ?_⟩
      · exact mem_endsPair.mpr (Or.inl (Prod.ext h1.1 h1.2))
      · exact mem_freeVerts.mpr ⟨fun hc => hOk'.2.1 (h1.1.trans hc.symm),
          fun hc => hOk'.2.2.1 (h1.2.trans hc.symm)⟩
      · exact mem_colourPairs.mpr hOk'.2.2.2
    · refine ⟨(((cfgU g, cfgP g), cfgQ g), (cfgI g, cfgJ g)), ?_, rfl⟩
      refine (mem_roleDomain_iff a b _).mpr ⟨⟨?_, ?_⟩, ?_⟩
      · exact mem_endsPair.mpr (Or.inr (Prod.ext h1.1 h1.2))
      · exact mem_freeVerts.mpr ⟨fun hc => hOk'.2.2.1 (h1.2.trans hc.symm),
          fun hc => hOk'.2.1 (h1.1.trans hc.symm)⟩
      · exact mem_colourPairs.mpr hOk'.2.2.2

/-- **THE CENSUS OF THE SECOND ROLE: EXACTLY `2(n-2)k(k-1)` HYPEREDGES OF `H` HAVE `s(a,b)` AS THEIR
SECOND SPOKE.** -/
theorem card_auxF_spoke2 {n k : ℕ} (a b : Verts n) (hab : a ≠ b) :
    ((auxF n k).filter (fun g => s(cfgU g, cfgQ g) = s(a, b))).card
      = 2 * ((n - 2) * (k * (k - 1))) := by
  refine (Finset.card_bij (s := roleDomain a b k)
    (t := (auxF n k).filter (fun g => s(cfgU g, cfgQ g) = s(a, b)))
    (fun t _ => (t.1.1.1, t.1.2, t.1.1.2, t.2.1, t.2.2)) ?_ ?_ ?_).symm.trans (card_roleDomain a b hab)
  · intro t ht
    obtain ⟨⟨ht1, ht2⟩, ht3⟩ := (mem_roleDomain_iff a b t).mp ht
    obtain ⟨ha, hb⟩ := mem_freeVerts.mp ht2
    have hi : t.2.1 ≠ t.2.2 := mem_colourPairs.mp ht3
    have heq : (t.1.1.1 = a ∧ t.1.1.2 = b) ∨ (t.1.1.1 = b ∧ t.1.1.2 = a) := by
      rcases (mem_endsPair.mp ht1) with h' | h'
      · exact Or.inl ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩
      · exact Or.inr ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩
    rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
      exact Finset.mem_filter.mpr ⟨mem_auxF.mpr (Ok_tuple.mpr
        ⟨ha.symm, hab, hb, hi⟩), rfl⟩
    · rw [h1, h2]
      exact Finset.mem_filter.mpr ⟨mem_auxF.mpr (Ok_tuple.mpr
        ⟨hb.symm, Ne.symm hab, ha, hi⟩), Sym2.eq_swap.symm⟩
  · intro t₁ _ t₂ _ he
    apply Prod.ext
    · apply Prod.ext
      · apply Prod.ext
        · exact congrArg (fun w : Cfg n k => w.1) he
        · exact congrArg (fun w : Cfg n k => (w.2.2.1 : Verts n)) he
      · exact congrArg (fun w : Cfg n k => w.2.1) he
    · apply Prod.ext
      · exact congrArg (fun w : Cfg n k => w.2.2.2.1) he
      · exact congrArg (fun w : Cfg n k => w.2.2.2.2) he
  · intro g hg
    obtain ⟨hg0, hg2⟩ := Finset.mem_filter.mp hg
    have hOk' := Ok_def (mem_auxF.mp hg0)
    rcases eq_sqk hg2 with h1 | h1
    · refine ⟨(((cfgU g, cfgQ g), cfgP g), (cfgI g, cfgJ g)), ?_, rfl⟩
      refine (mem_roleDomain_iff a b _).mpr ⟨⟨?_, ?_⟩, ?_⟩
      · exact mem_endsPair.mpr (Or.inl (Prod.ext h1.1 h1.2))
      · exact mem_freeVerts.mpr ⟨fun hc => hOk'.1 (h1.1.trans hc.symm),
          fun hc => hOk'.2.2.1 (hc.trans h1.2.symm)⟩
      · exact mem_colourPairs.mpr hOk'.2.2.2
    · refine ⟨(((cfgU g, cfgQ g), cfgP g), (cfgI g, cfgJ g)), ?_, rfl⟩
      refine (mem_roleDomain_iff a b _).mpr ⟨⟨?_, ?_⟩, ?_⟩
      · exact mem_endsPair.mpr (Or.inr (Prod.ext h1.1 h1.2))
      · exact mem_freeVerts.mpr ⟨fun hc => hOk'.2.2.1 (hc.trans h1.2.symm),
          fun hc => hOk'.1 (h1.1.trans hc.symm)⟩
      · exact mem_colourPairs.mpr hOk'.2.2.2

/-- **THE CENSUS OF THE OPPOSITE ROLE: EXACTLY `2(n-2)k(k-1)` HYPEREDGES OF `H` HAVE `s(a,b)` AS THEIR
OPPOSITE EDGE.** -/
theorem card_auxF_opp {n k : ℕ} (a b : Verts n) (hab : a ≠ b) :
    ((auxF n k).filter (fun g => s(cfgP g, cfgQ g) = s(a, b))).card
      = 2 * ((n - 2) * (k * (k - 1))) := by
  refine (Finset.card_bij (s := roleDomain a b k)
    (t := (auxF n k).filter (fun g => s(cfgP g, cfgQ g) = s(a, b)))
    (fun t _ => (t.1.2, t.1.1.1, t.1.1.2, t.2.1, t.2.2)) ?_ ?_ ?_).symm.trans (card_roleDomain a b hab)
  · intro t ht
    obtain ⟨⟨ht1, ht2⟩, ht3⟩ := (mem_roleDomain_iff a b t).mp ht
    obtain ⟨ha, hb⟩ := mem_freeVerts.mp ht2
    have hi : t.2.1 ≠ t.2.2 := mem_colourPairs.mp ht3
    have heq : (t.1.1.1 = a ∧ t.1.1.2 = b) ∨ (t.1.1.1 = b ∧ t.1.1.2 = a) := by
      rcases (mem_endsPair.mp ht1) with h' | h'
      · exact Or.inl ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩
      · exact Or.inr ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩
    rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
      exact Finset.mem_filter.mpr ⟨mem_auxF.mpr (Ok_tuple.mpr
        ⟨ha, hb, hab, hi⟩), rfl⟩
    · rw [h1, h2]
      exact Finset.mem_filter.mpr ⟨mem_auxF.mpr (Ok_tuple.mpr
        ⟨hb, ha, Ne.symm hab, hi⟩), Sym2.eq_swap.symm⟩
  · intro t₁ _ t₂ _ he
    apply Prod.ext
    · apply Prod.ext
      · apply Prod.ext
        · exact congrArg (fun w : Cfg n k => w.2.1) he
        · exact congrArg (fun w : Cfg n k => (w.2.2.1 : Verts n)) he
      · exact congrArg (fun w : Cfg n k => w.1) he
    · apply Prod.ext
      · exact congrArg (fun w : Cfg n k => w.2.2.2.1) he
      · exact congrArg (fun w : Cfg n k => w.2.2.2.2) he
  · intro g hg
    obtain ⟨hg0, hg2⟩ := Finset.mem_filter.mp hg
    have hOk' := Ok_def (mem_auxF.mp hg0)
    rcases eq_sqp hg2 with h1 | h1
    · refine ⟨(((cfgP g, cfgQ g), cfgU g), (cfgI g, cfgJ g)), ?_, rfl⟩
      refine (mem_roleDomain_iff a b _).mpr ⟨⟨?_, ?_⟩, ?_⟩
      · exact mem_endsPair.mpr (Or.inl (Prod.ext h1.1 h1.2))
      · exact mem_freeVerts.mpr ⟨fun hc => hOk'.1 (hc.trans h1.1.symm),
          fun hc => hOk'.2.1 (hc.trans h1.2.symm)⟩
      · exact mem_colourPairs.mpr hOk'.2.2.2
    · refine ⟨(((cfgP g, cfgQ g), cfgU g), (cfgI g, cfgJ g)), ?_, rfl⟩
      refine (mem_roleDomain_iff a b _).mpr ⟨⟨?_, ?_⟩, ?_⟩
      · exact mem_endsPair.mpr (Or.inr (Prod.ext h1.1 h1.2))
      · exact mem_freeVerts.mpr ⟨fun hc => hOk'.2.1 (hc.trans h1.2.symm),
          fun hc => hOk'.1 (hc.trans h1.1.symm)⟩
      · exact mem_colourPairs.mpr hOk'.2.2.2

/-- **THE EDGE CENSUS OF `H`: EXACTLY `6(n-2)k(k-1)` HYPEREDGES OF `H` CONTAIN A GIVEN EDGE OF
`K_n`.**  Together with `Hyper.card_auxDeg_le` (the hypervertex degrees) and `Spoil.card_auxF_four`
(the four-set census) this is the **complete local census of `H`**: every finite first-moment or
local-lemma argument on `H` needs only these three numbers. -/
theorem card_auxF_edge {n k : ℕ} (e : Sym2 (Verts n)) (he : OffDiag e) :
    ((auxF n k).filter (fun g => e ∈ cfgEdges g)).card = 6 * ((n - 2) * (k * (k - 1))) := by
  obtain ⟨a, b, rfl⟩ := Sym2.exists.mp ⟨e, rfl⟩
  have hab : a ≠ b := he a b rfl
  set A : Finset (Cfg n k) := (auxF n k).filter (fun g => s(cfgU g, cfgP g) = s(a, b)) with hA
  set B : Finset (Cfg n k) := (auxF n k).filter (fun g => s(cfgU g, cfgQ g) = s(a, b)) with hB
  set C : Finset (Cfg n k) := (auxF n k).filter (fun g => s(cfgP g, cfgQ g) = s(a, b)) with hC
  have hD : (auxF n k).filter (fun g => s(a, b) ∈ cfgEdges g) = A ∪ (B ∪ C) := by
    refine Finset.Subset.antisymm ?_ ?_
    · intro g hg
      obtain ⟨hg0, hg1⟩ := Finset.mem_filter.mp hg
      rcases (mem_cfgEdges_eq).mp hg1 with h1 | h1 | h1
      · exact Finset.mem_union.mpr (Or.inl
          (Finset.mem_filter.mpr ⟨mem_auxF.mpr (mem_auxF.mp hg0), h1⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inl
          (Finset.mem_filter.mpr ⟨mem_auxF.mpr (mem_auxF.mp hg0), h1⟩))))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr
          (Finset.mem_filter.mpr ⟨mem_auxF.mpr (mem_auxF.mp hg0), h1⟩))))
    · intro g hg
      rcases Finset.mem_union.mp hg with hg | hg
      · rw [hA] at hg
        obtain ⟨hg0, hg2⟩ := Finset.mem_filter.mp hg
        exact Finset.mem_filter.mpr ⟨mem_auxF.mpr (mem_auxF.mp hg0),
          (mem_cfgEdges_eq).mpr (Or.inl hg2)⟩
      · rcases Finset.mem_union.mp hg with hg | hg
        · rw [hB] at hg
          obtain ⟨hg0, hg2⟩ := Finset.mem_filter.mp hg
          exact Finset.mem_filter.mpr ⟨mem_auxF.mpr (mem_auxF.mp hg0),
            (mem_cfgEdges_eq).mpr (Or.inr (Or.inl hg2))⟩
        · rw [hC] at hg
          obtain ⟨hg0, hg2⟩ := Finset.mem_filter.mp hg
          exact Finset.mem_filter.mpr ⟨mem_auxF.mpr (mem_auxF.mp hg0),
            (mem_cfgEdges_eq).mpr (Or.inr (Or.inr hg2))⟩
  have hdisj1 : A ∩ (B ∪ C) = ∅ := by
    refine Finset.eq_empty_iff_forall_notMem.mpr fun g hg => ?_
    obtain ⟨hg1, hg2⟩ := Finset.mem_inter.mp hg
    rw [hA] at hg1
    rcases Finset.mem_union.mp hg2 with hg2 | hg2
    · rw [hB] at hg2
      obtain ⟨hg1a, hg1b⟩ := Finset.mem_filter.mp hg1
      obtain ⟨_, hg2a⟩ := Finset.mem_filter.mp hg2
      exact (ne_edges (mem_auxF.mp hg1a)).1 (hg1b.trans hg2a.symm)
    · rw [hC] at hg2
      obtain ⟨hg1a, hg1b⟩ := Finset.mem_filter.mp hg1
      obtain ⟨_, hg2a⟩ := Finset.mem_filter.mp hg2
      exact (ne_edges (mem_auxF.mp hg1a)).2.1 (hg1b.trans hg2a.symm)
  have hdisj2 : B ∩ C = ∅ := by
    refine Finset.eq_empty_iff_forall_notMem.mpr fun g hg => ?_
    obtain ⟨hg1, hg2⟩ := Finset.mem_inter.mp hg
    rw [hB] at hg1
    rw [hC] at hg2
    obtain ⟨hg1a, hg1b⟩ := Finset.mem_filter.mp hg1
    obtain ⟨_, hg2a⟩ := Finset.mem_filter.mp hg2
    exact (ne_edges (mem_auxF.mp hg1a)).2.2 (hg1b.trans hg2a.symm)
  have hcard : (A ∪ (B ∪ C)).card = A.card + B.card + C.card := by
    rw [Finset.card_union_of_disjoint (disjoint_of_inter_empty hdisj1),
      Finset.card_union_of_disjoint (disjoint_of_inter_empty hdisj2)]
    ring
  rw [hD, hcard, hA, hB, hC, card_auxF_spoke1 a b hab, card_auxF_spoke2 a b hab,
    card_auxF_opp a b hab]
  ring

/-- An edge of `K_n` has two distinct endpoints. -/
theorem offDiag_univ {n : ℕ} {e : Sym2 (Verts n)}
    (he : e ∈ edgeFinset (Finset.univ : Finset (Verts n))) : OffDiag e := by
  obtain ⟨a, b, rfl⟩ := Sym2.exists.mp ⟨e, rfl⟩
  exact offDiag_iff.mpr ((mem_edgeFinset.mp he).2 a b rfl)

/-- **THE EDGE CENSUS IS CONSISTENT WITH THE CENSUS OF `H`.**  Summed over the `C(n,2)` edges of `K_n`
the local count returns `3·|E(H)|`, as it must: every hyperedge of `H` has three edges.  So the
census of `Hyper.card_auxF`, the hypervertex degrees, the four-set census and this file's edge census
form a coherent whole. -/
theorem auxF_edge_double {n k : ℕ} :
    (∑ e ∈ edgeFinset (Finset.univ : Finset (Verts n)),
      ((auxF n k).filter (fun g => e ∈ cfgEdges g)).card) = 3 * (auxF n k).card := by
  have h1 : ∀ e ∈ edgeFinset (Finset.univ : Finset (Verts n)),
      ((auxF n k).filter (fun g => e ∈ cfgEdges g)).card
        = 6 * ((n - 2) * (k * (k - 1))) :=
    fun e he => card_auxF_edge e (offDiag_univ he)
  calc (∑ e ∈ edgeFinset (Finset.univ : Finset (Verts n)),
        ((auxF n k).filter (fun g => e ∈ cfgEdges g)).card)
      = ∑ _e ∈ edgeFinset (Finset.univ : Finset (Verts n)),
        (6 * ((n - 2) * (k * (k - 1)))) := by
        refine Finset.sum_congr rfl fun e he => h1 e he
    _ = (edgeFinset (Finset.univ : Finset (Verts n))).card * (6 * ((n - 2) * (k * (k - 1)))) := by
        rw [Finset.sum_const]
        norm_num
    _ = 3 * (n * ((n - 1) * ((n - 2) * (k * (k - 1))))) := by
        have h3 := edge_count_two_mul n
        have h3' : (edgeFinset (Finset.univ : Finset (Verts n))).card * 2 = n * (n - 1) := by
          omega
        calc _ = (edgeFinset (Finset.univ : Finset (Verts n))).card * 2
              * (3 * ((n - 2) * (k * (k - 1)))) := by ring
          _ = (n * (n - 1)) * (3 * ((n - 2) * (k * (k - 1)))) := by rw [h3']
          _ = 3 * (n * ((n - 1) * ((n - 2) * (k * (k - 1))))) := by ring
    _ = 3 * (auxF n k).card := by rw [card_auxF n k]

/-! ### 3. The members of a family covering a given edge -/

/-- **THE MEMBERS OF A FAMILY COVERING A GIVEN EDGE.** -/
noncomputable def coverF {n k : ℕ} (F : Fam n k) (e : Sym2 (Verts n)) : Fam n k :=
  F.filter (fun g => e ∈ cfgEdges g)

@[simp] theorem mem_coverF {n k : ℕ} {F : Fam n k} {e : Sym2 (Verts n)} {g : Cfg n k} :
    g ∈ coverF F e ↔ g ∈ F ∧ e ∈ cfgEdges g :=
  Finset.mem_filter

/-- **THE ROLE ANALYSIS.**  A member of a family covering the edge `s(a,b)` has `a` or `b` as its
centre, or has both of them as leaves. -/
theorem coverF_role {n k : ℕ} {F : Fam n k} {a b : Verts n} {g : Cfg n k} (hab : a ≠ b)
    {h : g ∈ coverF F (s(a, b))} :
    cfgU g = a ∨ cfgU g = b ∨
      ((a = cfgP g ∨ a = cfgQ g) ∧ (b = cfgP g ∨ b = cfgQ g)) := by
  have hE : s(cfgU g, cfgP g) = s(a, b) ∨ s(cfgU g, cfgQ g) = s(a, b) ∨
      s(cfgP g, cfgQ g) = s(a, b) := mem_cfgEdges_eq.mp ((mem_coverF.mp h).2)
  rcases hE with he | he | he
  · rcases eq_spk he with h1 | h1
    · exact Or.inl h1.1
    · exact Or.inr (Or.inl h1.1)
  · rcases eq_sqk he with h1 | h1
    · exact Or.inl h1.1
    · exact Or.inr (Or.inl h1.1)
  · rcases eq_sqp he with h1 | h1
    · exact Or.inr (Or.inr ⟨Or.inl h1.1.symm, Or.inr h1.2.symm⟩)
    · exact Or.inr (Or.inr ⟨Or.inr h1.2.symm, Or.inl h1.1.symm⟩)

/-- **THE THREE CLASSES OF MEMBERS COVERING `s(a,b)`:** those with `a` as centre, those with `b` as
centre, and those with both as leaves. -/
noncomputable def coverA {n k : ℕ} (F : Fam n k) (a b : Verts n) : Fam n k :=
  (coverF F (s(a, b))).filter (fun g => cfgU g = a)

noncomputable def coverB {n k : ℕ} (F : Fam n k) (a b : Verts n) : Fam n k :=
  (coverF F (s(a, b))).filter (fun g => cfgU g = b)

noncomputable def coverC {n k : ℕ} (F : Fam n k) (a b : Verts n) : Fam n k :=
  (coverF F (s(a, b))).filter (fun g => cfgU g ≠ a ∧ cfgU g ≠ b)

@[simp] theorem mem_coverA {n k : ℕ} {F : Fam n k} {a b : Verts n} {g : Cfg n k} :
    g ∈ coverA F a b ↔ g ∈ coverF F (s(a, b)) ∧ cfgU g = a :=
  Finset.mem_filter

@[simp] theorem mem_coverB {n k : ℕ} {F : Fam n k} {a b : Verts n} {g : Cfg n k} :
    g ∈ coverB F a b ↔ g ∈ coverF F (s(a, b)) ∧ cfgU g = b :=
  Finset.mem_filter

@[simp] theorem mem_coverC {n k : ℕ} {F : Fam n k} {a b : Verts n} {g : Cfg n k} :
    g ∈ coverC F a b ↔ g ∈ coverF F (s(a, b)) ∧ (cfgU g ≠ a ∧ cfgU g ≠ b) :=
  Finset.mem_filter

/-- **THE THREE CLASSES PARTITION THE MEMBERS COVERING `s(a,b)`.** -/
theorem coverF_eq_three {n k : ℕ} {F : Fam n k} {a b : Verts n} (hok : OkF F) (hab : a ≠ b) :
    coverF F (s(a, b)) = coverA F a b ∪ (coverB F a b ∪ coverC F a b) := by
  refine Finset.Subset.antisymm ?_ ?_
  · intro g hg
    have hgF : g ∈ F := (mem_coverF.mp hg).1
    have hOk := Ok_def (hok g hgF)
    rcases coverF_role hab (h := hg) with h1 | h1 | h1
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hg, h1⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inl
        (Finset.mem_filter.mpr ⟨hg, h1⟩))))
    · obtain ⟨hpa, hpb⟩ := h1
      refine Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr
        (Finset.mem_filter.mpr ⟨hg, ⟨?_, ?_⟩⟩))))
      · intro hc
        rcases hpa with hpa | hpa
        · exact hOk.1 (hc.trans hpa)
        · exact hOk.2.1 (hc.trans hpa)
      · intro hc
        rcases hpb with hpb | hpb
        · exact hOk.1 (hc.trans hpb)
        · exact hOk.2.1 (hc.trans hpb)
  · intro g hg
    rcases Finset.mem_union.mp hg with hg | hg
    · exact (mem_coverA.mp hg).1
    · rcases Finset.mem_union.mp hg with hg | hg
      · exact (mem_coverB.mp hg).1
      · exact (mem_coverC.mp hg).1

/-- **A MEMBER COVERING `s(a,b)` WITH `a` AS A LEAF IS A MEMBER OF THE FAMILY.** -/
theorem coverBC_mem {n k : ℕ} {F : Fam n k} {a b : Verts n} {g : Cfg n k}
    {h : g ∈ coverB F a b ∨ g ∈ coverC F a b} : g ∈ coverF F (s(a, b)) := by
  rcases h with h | h
  · exact (mem_coverB.mp h).1
  · exact (mem_coverC.mp h).1

/-- **A COVERING MEMBER IN WHICH `a` IS NOT THE CENTRE HAS `a` AS A LEAF.** -/
theorem coverF_leaf {n k : ℕ} {F : Fam n k} {a b : Verts n} {g : Cfg n k} (hab : a ≠ b)
    {h : g ∈ coverB F a b ∨ g ∈ coverC F a b} (hc : cfgU g ≠ a) :
    a = cfgP g ∨ a = cfgQ g := by
  have hg : g ∈ coverF F (s(a, b)) := coverBC_mem (h := h)
  have hE : s(cfgU g, cfgP g) = s(a, b) ∨ s(cfgU g, cfgQ g) = s(a, b) ∨
      s(cfgP g, cfgQ g) = s(a, b) :=
    mem_cfgEdges_eq.mp ((mem_coverF.mp hg).2)
  rcases hE with he | he | he
  · rcases eq_spk he with h1 | h1
    · exact absurd h1.1 hc
    · exact Or.inl h1.2.symm
  · rcases eq_sqk he with h1 | h1
    · exact absurd h1.1 hc
    · exact Or.inr h1.2.symm
  · rcases eq_sqp he with h1 | h1
    · exact Or.inl h1.1.symm
    · exact Or.inr h1.2.symm

/-- **A COVERING MEMBER WITH `a` AS CENTRE USES THE SINGLE SLOT `(a, cfgI g)`.** -/
theorem coverA_slot {n k : ℕ} {F : Fam n k} {a b : Verts n} {g : Cfg n k}
    {h : g ∈ coverA F a b} : (a, cfgI g) ∈ cfgSlots g := by
  rw [← (mem_coverA.mp h).2]
  exact mem_cfgSlots_1 g

/-- **A COVERING MEMBER IN WHICH `a` IS NOT THE CENTRE HAS `a` AS A LEAF, AND USES BOTH SLOTS AT
`a`.** -/
theorem coverBC_leaf {n k : ℕ} {F : Fam n k} {a b : Verts n} {g : Cfg n k} (hab : a ≠ b)
    {h : g ∈ coverB F a b ∨ g ∈ coverC F a b} :
    (a = cfgP g ∨ a = cfgQ g) ∧ (a, cfgI g) ∈ cfgSlots g ∧ (a, cfgJ g) ∈ cfgSlots g := by
  have hg : g ∈ coverF F (s(a, b)) := coverBC_mem (h := h)
  have hnot : cfgU g ≠ a := by
    rcases h with h | h
    · have hb : cfgU g = b := (mem_coverB.mp h).2
      intro hc
      exact hab (hc.symm.trans hb)
    · exact (mem_coverC.mp h).2.1
  have hleaf : a = cfgP g ∨ a = cfgQ g := coverF_leaf hab (h := h) hnot
  refine ⟨hleaf, ?_⟩
  rcases hleaf with hleaf | hleaf
  · rw [hleaf]
    exact ⟨mem_cfgSlots_2 g, mem_cfgSlots_4 g⟩
  · rw [hleaf]
    exact ⟨mem_cfgSlots_3 g, mem_cfgSlots_5 g⟩

/-! ### 4. The slots at one vertex -/

/-- **THE PAIR OF SLOTS A LEAF MEMBERSHIP USES AT ITS VERTEX.** -/
noncomputable def slotPair {n k : ℕ} (g : Cfg n k) : Finset (Fin k) :=
  insert (cfgI g) (insert (cfgJ g) ∅)

/-- **THE SLOTS OF A FAMILY AT ONE VERTEX.** -/
noncomputable def SlotsAtF {n k : ℕ} (F : Fam n k) (v : Verts n) : Finset (Fin k) :=
  (Finset.univ : Finset (Fin k)).filter (fun j => (v, j) ∈ SlotsF F)

@[simp] theorem mem_SlotsAtF {n k : ℕ} {F : Fam n k} {v : Verts n} {j : Fin k} :
    j ∈ SlotsAtF F v ↔ (v, j) ∈ SlotsF F := by
  simp [SlotsAtF]

/-- **THE PER-VERTEX SLOT COUNT.**  Every member in which `v` is the centre occupies one slot at `v`,
every member in which `v` is a leaf occupies two. -/
theorem card_SlotsAtF {n k : ℕ} {F : Fam n k} (hok : OkF F) (hS : SlotFree F) (v : Verts n) :
    (SlotsAtF F v).card ≤ (centF F v).card + 2 * (leafF F v).card := by
  have hsub : SlotsAtF F v ⊆ (centF F v).image (fun g => cfgI g)
      ∪ (leafF F v).biUnion
          (fun g => slotPair g) := by
    intro j hj
    obtain ⟨g, hg, hslot⟩ := Finset.mem_biUnion.mp (mem_SlotsAtF.mp hj)
    rcases (mem_cfgSlots g).mp hslot with ⟨hI, hV⟩ | ⟨hJ, hV⟩
    · rcases hV with hV | hV | hV
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr
          ⟨g, Finset.mem_filter.mpr ⟨hg, hV.symm⟩, hI.symm⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr ⟨g,
          Finset.mem_filter.mpr ⟨hg, Or.inl hV.symm⟩,
          Finset.mem_insert.mpr (Or.inl hI)⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr ⟨g,
          Finset.mem_filter.mpr ⟨hg, Or.inr hV.symm⟩,
          Finset.mem_insert.mpr (Or.inl hI)⟩))
    · rcases hV with hV | hV
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr ⟨g,
          Finset.mem_filter.mpr ⟨hg, Or.inl hV.symm⟩,
          Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl hJ)))⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr ⟨g,
          Finset.mem_filter.mpr ⟨hg, Or.inr hV.symm⟩,
          Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl hJ)))⟩))
  have h3 : ((leafF F v).biUnion
        (fun g => slotPair g)).card
      ≤ ∑ g ∈ leafF F v, (2 : ℕ) := by
    refine le_trans Finset.card_biUnion_le ?_
    refine Finset.sum_le_sum fun g hg => ?_
    have hOk := Ok_def (hok g (Finset.mem_filter.mp hg).1)
    rw [slotPair, Finset.card_insert_of_notMem (by simp [hOk.2.2.2]),
      Finset.card_insert_of_notMem (by simp), Finset.card_empty]
  have h4 : ((centF F v).image (fun g => cfgI g)).card ≤ (centF F v).card :=
    Finset.card_image_le
  calc (SlotsAtF F v).card
      ≤ ((centF F v).image (fun g => cfgI g) ∪ (leafF F v).biUnion
          (fun g => slotPair g)).card :=
        Finset.card_le_card hsub
    _ ≤ ((centF F v).image (fun g => cfgI g)).card + ∑ g ∈ leafF F v, (2 : ℕ) := by
      exact le_trans (Finset.card_union_le _ _) (by omega)
    _ ≤ (centF F v).card + 2 * (leafF F v).card := by
      rw [Finset.sum_const, Nat.nsmul_eq_mul]
      omega

/-- **A SINGLE-VALUE FIBRE SUM: the members with `f g = v`, counted over all `v`, number `|F|`.** -/
private theorem sum_single_fibre {n k : ℕ} (F : Fam n k) (f : Cfg n k → Verts n) :
    (∑ v : Verts n, (F.filter (fun g => f g = v)).card) = F.card := by
  calc (∑ v : Verts n, (F.filter (fun g => f g = v)).card)
      = ∑ v : Verts n, ∑ g ∈ F, ((if f g = v then 1 else 0 : ℕ)) := by
        refine Finset.sum_congr rfl (fun v _ => ?_)
        exact card_filter_ite (F : Finset (Cfg n k)) f v
    _ = ∑ g ∈ F, ∑ v : Verts n, ((if f g = v then 1 else 0 : ℕ)) := Finset.sum_comm
    _ = ∑ _g ∈ F, 1 := by
        refine Finset.sum_congr rfl (fun g _ => ?_)
        exact sum_ite_eq_one (f g)
    _ = F.card := by rw [Finset.sum_const]; norm_num

/-- **EVERY MEMBER IS THE CENTRE OF EXACTLY ONE VERTEX-FILTER.** -/
theorem sum_centreF_card {n k : ℕ} (F : Fam n k) :
    (∑ v : Verts n, (centF F v).card) = F.card :=
  sum_single_fibre F cfgU

/-- **THE LEAF FILTERS SPLIT INTO THE TWO LEAF SLOTS OF EACH MEMBER** (which are disjoint, because
a member has two *different* leaves). -/
theorem card_leafF {n k : ℕ} {F : Fam n k} (hok : OkF F) (v : Verts n) :
    (leafF F v).card
      = (F.filter (fun g => cfgP g = v)).card + (F.filter (fun g => cfgQ g = v)).card := by
  have hU : leafF F v = F.filter (fun g => cfgP g = v)
      ∪ F.filter (fun g => cfgQ g = v) := by
    refine Finset.Subset.antisymm ?_ ?_
    · intro g hg
      obtain ⟨hg1, hg2⟩ := mem_leafF.mp hg
      rcases hg2 with hg2 | hg2
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hg1, hg2⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hg1, hg2⟩))
    · intro g hg
      rcases Finset.mem_union.mp hg with hg | hg
      · obtain ⟨hg1, hg2⟩ := Finset.mem_filter.mp hg
        exact mem_leafF.mpr ⟨hg1, Or.inl hg2⟩
      · obtain ⟨hg1, hg2⟩ := Finset.mem_filter.mp hg
        exact mem_leafF.mpr ⟨hg1, Or.inr hg2⟩
  rw [hU]
  have hdisj : F.filter (fun g => cfgP g = v) ∩ F.filter (fun g => cfgQ g = v) = ∅ := by
    refine Finset.eq_empty_iff_forall_notMem.mpr fun g hg => ?_
    obtain ⟨hg1, hg2⟩ := Finset.mem_inter.mp hg
    obtain ⟨hg1f, hg1v⟩ := Finset.mem_filter.mp hg1
    obtain ⟨_, hg2v⟩ := Finset.mem_filter.mp hg2
    exact (Ok_def (hok g hg1f)).2.2.1 (hg1v.trans hg2v.symm)
  rw [← Finset.card_union_add_card_inter, hdisj, Finset.card_empty, Nat.add_zero]

/-- **EVERY MEMBER IS A LEAF AT EXACTLY TWO VERTICES.** -/
theorem sum_leafF_card {n k : ℕ} {F : Fam n k} (hok : OkF F) :
    (∑ v : Verts n, (leafF F v).card) = 2 * F.card := by
  calc (∑ v : Verts n, (leafF F v).card)
      = ∑ v : Verts n, ((F.filter (fun g => cfgP g = v)).card
        + (F.filter (fun g => cfgQ g = v)).card) := by
        refine Finset.sum_congr rfl (fun v _ => card_leafF hok v)
    _ = (∑ v : Verts n, (F.filter (fun g => cfgP g = v)).card)
        + (∑ v : Verts n, (F.filter (fun g => cfgQ g = v)).card) := Finset.sum_add_distrib
    _ = F.card + F.card := by rw [sum_single_fibre F cfgP, sum_single_fibre F cfgQ]
    _ = 2 * F.card := by ring

/-- **THE PER-VERTEX ACCOUNTING, GLOBALLY: `Σ_v (|centF F v| + 2·|leafF F v|) = 5·|F|`.**  This is
`Fam.card_SlotsF` seen vertex by vertex: each member contributes one slot at its centre and two at
each of its leaves. -/
theorem sum_slots_at_card {n k : ℕ} {F : Fam n k} (hok : OkF F) :
    (∑ v : Verts n, ((centF F v).card + 2 * (leafF F v).card)) = 5 * F.card := by
  have h4 : (∑ v : Verts n, (2 * (leafF F v).card)) = 4 * F.card := by
    rw [← Finset.mul_sum]
    have h2 := sum_leafF_card hok
    calc (2 : ℕ) * (∑ i : Verts n, (leafF F i).card) = 2 * (2 * F.card) := by rw [h2]
      _ = 4 * F.card := by ring
  rw [Finset.sum_add_distrib, sum_centreF_card F, h4]
  ring

/-! ### 5. The per-vertex slot budget -/

/-- **THE TWO COLOURS OF A SLOT PAIR.** -/
@[simp] theorem mem_slotPair {n k : ℕ} (g : Cfg n k) {j : Fin k} :
    j ∈ slotPair g ↔ j = cfgI g ∨ j = cfgJ g := by
  simp only [slotPair, Finset.mem_insert]
  simp

/-- **A SLOT PAIR IS TWO SLOTS.** -/
theorem card_slotPair {n k : ℕ} {g : Cfg n k} (h : Ok g) : (slotPair g).card = 2 := by
  have hij := (Ok_def h).2.2.2
  rw [slotPair, Finset.card_insert_of_notMem (by simp [hij]),
    Finset.card_insert_of_notMem (by simp), Finset.card_empty, Nat.zero_add, Nat.add_zero,
    Nat.one_add]

/-- **A SLOT AT A LEAF.** -/
theorem mem_cfgSlots_leaf {n k : ℕ} {g : Cfg n k} {v : Verts n} {j : Fin k}
    (hleaf : v = cfgP g ∨ v = cfgQ g) (hj : j ∈ slotPair g) :
    (v, j) ∈ cfgSlots g := by
  rcases hleaf with h | h
  · rw [h]
    rcases (mem_slotPair g).mp hj with hj | hj
    · rw [hj]; exact mem_cfgSlots_2 g
    · rw [hj]; exact mem_cfgSlots_4 g
  · rw [h]
    rcases (mem_slotPair g).mp hj with hj | hj
    · rw [hj]; exact mem_cfgSlots_3 g
    · rw [hj]; exact mem_cfgSlots_5 g

/-- **SLOT-FREENESS AT ONE VERTEX.**  Two slots of a family at the *same* vertex with the *same*
colour come from the same member.  This is `SlotFree` applied one vertex and one colour at a time. -/
theorem injOn_col_slotsF {n k : ℕ} {F : Fam n k} (hS : SlotFree F) (v : Verts n) :
    Set.InjOn (fun vp : Verts n × Fin k => vp.2) (slotsF F v) := by
  intro vp hvp vp' hvp' heq
  obtain ⟨hv1, hv2⟩ := Finset.mem_filter.mp hvp
  obtain ⟨hv1', hv2'⟩ := Finset.mem_filter.mp hvp'
  obtain ⟨g, hg, hxg⟩ := Finset.mem_biUnion.mp hv1
  obtain ⟨g', hg', hxg'⟩ := Finset.mem_biUnion.mp hv1'
  have hpa : (v, vp.2) = vp := Prod.ext hv2.symm rfl
  have hpb : (v, vp'.2) = vp' := Prod.ext hv2'.symm rfl
  have hs1 : (v, vp.2) ∈ cfgSlots g := by rw [hpa]; exact hxg
  have hs2 : (v, vp'.2) ∈ cfgSlots g' := by rw [hpb]; exact hxg'
  have hs2' : (v, vp.2) ∈ cfgSlots g' := by
    have hvb : (v, vp.2) = (v, vp'.2) := Prod.ext rfl heq
    rw [hvb]
    exact hs2
  have hg : g = g' := hS g g' hg hg' (v, vp.2) hs1 hs2'
  exact Prod.ext (hv2.trans hv2'.symm) heq

/-- **THE COLOURS USED AT ONE VERTEX** — the image of the slots at `v` under the colour
projection. -/
theorem SlotsAtF_eq {n k : ℕ} (F : Fam n k) (v : Verts n) :
    SlotsAtF F v = (slotsF F v).image (fun vp : Verts n × Fin k => vp.2) := by
  ext j
  constructor
  · intro hj
    rw [mem_SlotsAtF] at hj
    exact Finset.mem_image.mpr ⟨(v, j), Finset.mem_filter.mpr ⟨hj, rfl⟩, rfl⟩
  · intro hj
    obtain ⟨vp, hvp, rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨hv, hv2⟩ := Finset.mem_filter.mp hvp
    have hpa : (v, vp.2) = vp := Prod.ext hv2.symm rfl
    rw [← hpa] at hv
    exact mem_SlotsAtF.mpr hv

/-- **THE PER-VERTEX SLOT COUNT, EXACTLY.**  The colours used at `v` number one per member centred at
`v` and two per member having `v` as a leaf.  (Round 42 could only prove the `≤` direction, because
it did not know that the colour projection of the slots at `v` is injective.) -/
theorem card_SlotsAtF_eq {n k : ℕ} {F : Fam n k} (hok : OkF F) (hS : SlotFree F) (v : Verts n) :
    (SlotsAtF F v).card = (centF F v).card + 2 * (leafF F v).card :=
  (SlotsAtF_eq F v) ▸ (Finset.card_image_iff.mpr (injOn_col_slotsF hS v)) ▸
    card_slotsF hok hS v

/-- **THE PER-VERTEX SLOT BUDGET: `|centF F v| + 2·|leafF F v| ≤ k` for every vertex.**  This is
`Fam.slots_countF` (`5·|F| ≤ nk`) *pointwise*: no vertex can be over budget, and the sum over the
vertices is `5·|F|`.  A first stage of arXiv:2208.12563 §4 must therefore be *uniformly* balanced. -/
theorem slots_at_le {n k : ℕ} {F : Fam n k} (hok : OkF F) (hS : SlotFree F) (v : Verts n) :
    (centF F v).card + 2 * (leafF F v).card ≤ k := by
  have h1 : (SlotsAtF F v).card ≤ k := by
    refine le_trans (Finset.card_le_card fun _ _ => Finset.mem_univ _) ?_
    simp
  rw [← card_SlotsAtF_eq hok hS v]
  exact h1

/-- **A VERTEX IS A LEAF IN AT MOST `⌊k/2⌋` MEMBERS OF A MATCHING.** -/
theorem leafF_card_le {n k : ℕ} {F : Fam n k} (hok : OkF F) (hS : SlotFree F) (v : Verts n) :
    2 * (leafF F v).card ≤ k := by
  have h := slots_at_le hok hS v
  omega

/-- **A VERTEX IS THE CENTRE OF AT MOST `k` MEMBERS OF A MATCHING.** -/
theorem centF_card_le {n k : ℕ} {F : Fam n k} (hok : OkF F) (hS : SlotFree F) (v : Verts n) :
    (centF F v).card ≤ k := by
  have h := slots_at_le hok hS v
  omega


/-! ### 6. The per-edge budget -/

/-- **THE EDGE `s(a,b)` DOES NOT DEPEND ON THE ORDER OF ITS ENDPOINTS.** -/
theorem s_swap {α : Type*} (a b : α) : s(a, b) = s(b, a) := Sym2.eq.mpr (Sym2.Rel.swap a b)

/-- **THE COVERING MEMBERS DO NOT DEPEND ON THE ORDER OF THE ENDPOINTS.** -/
theorem coverF_swap {n k : ℕ} {F : Fam n k} (a b : Verts n) :
    coverF F (s(a, b)) = coverF F (s(b, a)) := by
  rw [s_swap]

/-- **A COVERING MEMBER IN WHICH `a` IS NOT THE CENTRE HAS `a` AS A LEAF** — in the form that does
not mention the three classes of §3. -/
theorem coverF_leaf' {n k : ℕ} {F : Fam n k} {a b : Verts n} {g : Cfg n k} (hab : a ≠ b)
    (hg : g ∈ coverF F (s(a, b))) (hc : cfgU g ≠ a) :
    a = cfgP g ∨ a = cfgQ g := by
  have hE : s(cfgU g, cfgP g) = s(a, b) ∨ s(cfgU g, cfgQ g) = s(a, b) ∨
      s(cfgP g, cfgQ g) = s(a, b) :=
    mem_cfgEdges_eq.mp ((mem_coverF.mp hg).2)
  rcases hE with he | he | he
  · rcases eq_spk he with h1 | h1
    · exact absurd h1.1 hc
    · exact Or.inl h1.2.symm
  · rcases eq_sqk he with h1 | h1
    · exact absurd h1.1 hc
    · exact Or.inr h1.2.symm
  · rcases eq_sqp he with h1 | h1
    · exact Or.inl h1.1.symm
    · exact Or.inr h1.2.symm

/-- **A COVERING MEMBER IN WHICH `b` IS NOT THE CENTRE HAS `b` AS A LEAF.** -/
theorem coverF_leaf'' {n k : ℕ} {F : Fam n k} {a b : Verts n} {g : Cfg n k} (hab : a ≠ b)
    {h : g ∈ coverF F (s(a, b))} (hc : cfgU g ≠ b) :
    b = cfgP g ∨ b = cfgQ g := by
  rw [coverF_swap a b] at h
  exact coverF_leaf' hab.symm h hc

/-- **THE THREE CLASSES OF §3 ARE PAIRWISE DISJOINT.** -/
theorem cover_ABC_disj {n k : ℕ} {F : Fam n k} {a b : Verts n} (hab : a ≠ b) :
    (∀ g : Cfg n k, g ∈ coverA F a b → g ∈ coverB F a b → False) ∧
      (∀ g : Cfg n k, g ∈ coverA F a b → g ∈ coverC F a b → False) ∧
      (∀ g : Cfg n k, g ∈ coverB F a b → g ∈ coverC F a b → False) := by
  refine ⟨fun _ hg1 hg2 => ?_,
    fun _ hg1 hg2 => ?_,
    fun _ hg1 hg2 => ?_⟩
  · obtain ⟨hgA, h1⟩ := mem_coverA.mp hg1
    obtain ⟨hgB, h2⟩ := mem_coverB.mp hg2
    exact hab (h1.symm.trans h2)
  · obtain ⟨hgA, h1⟩ := mem_coverA.mp hg1
    obtain ⟨hgC, h2⟩ := mem_coverC.mp hg2
    exact absurd h1 h2.1
  · obtain ⟨hgB, h2⟩ := mem_coverB.mp hg1
    obtain ⟨hgC, h3⟩ := mem_coverC.mp hg2
    exact absurd h2 h3.2

/-- **THE COVERING MEMBERS NUMBER `|coverA| + |coverB| + |coverC|`.** -/
theorem card_coverF_eq_three {n k : ℕ} {F : Fam n k} (hok : OkF F) {a b : Verts n} (hab : a ≠ b) :
    (coverF F (s(a, b))).card
      = (coverA F a b).card + (coverB F a b).card + (coverC F a b).card := by
  have h1 : Disjoint (coverA F a b ∪ coverB F a b) (coverC F a b) := by
    rw [Finset.disjoint_left]
    intro g hg1 hg2
    obtain ⟨hdAB, hdAC, hdBC⟩ := cover_ABC_disj hab
    rcases Finset.mem_union.mp hg1 with hgAB | hgAB
    · exact hdAC _ hgAB hg2
    · exact hdBC _ hgAB hg2
  calc (coverF F (s(a, b))).card
      = ((coverA F a b ∪ coverB F a b) ∪ coverC F a b).card := by
        rw [coverF_eq_three hok hab, Finset.union_assoc]
    _ = (coverA F a b ∪ coverB F a b).card + (coverC F a b).card :=
        Finset.card_union_of_disjoint h1
    _ = (coverA F a b).card + (coverB F a b).card + (coverC F a b).card := by
        rw [Finset.card_union_of_disjoint (Finset.disjoint_left.2 (cover_ABC_disj hab).1)]

/-- **THE SLOT ACCOUNT OF TWO CLASSES OF MEMBERS AT ONE VERTEX.**  Members of `A` use **one**
colour at `v` (they are centred there), members of `BC` use **two** (they have `v` as a leaf);
then `|A| + 2·|BC| ≤ k`, by slot-freeness. -/
private theorem class_slots_le {n k : ℕ} {F : Fam n k} {v : Verts n} {A BC : Fam n k}
    (hok : OkF F) (hS : SlotFree F)
    (hAF : ∀ (g : Cfg n k), g ∈ A → g ∈ F)
    (hBCF : ∀ (g : Cfg n k), g ∈ BC → g ∈ F)
    (hAc : ∀ (g : Cfg n k), g ∈ A → v = cfgU g)
    (hBC : ∀ (g : Cfg n k), g ∈ BC → v = cfgP g ∨ v = cfgQ g) :
    A.card + 2 * BC.card ≤ k := by
  have hsubA : A.image (fun g => cfgI g) ⊆ SlotsAtF F v := by
    rw [Finset.image_subset_iff]
    intro g hg
    rw [mem_SlotsAtF]
    exact Finset.mem_biUnion.mpr ⟨g, hAF g hg, by rw [hAc g hg]; exact mem_cfgSlots_1 g⟩
  have hsubB : BC.image (fun g => cfgI g) ⊆ SlotsAtF F v := by
    rw [Finset.image_subset_iff]
    intro g hg
    rw [mem_SlotsAtF]
    exact Finset.mem_biUnion.mpr ⟨g, hBCF g hg,
      mem_cfgSlots_leaf (hBC g hg) ((mem_slotPair g).mpr (Or.inl rfl))⟩
  have hsubC : BC.image (fun g => cfgJ g) ⊆ SlotsAtF F v := by
    rw [Finset.image_subset_iff]
    intro g hg
    rw [mem_SlotsAtF]
    exact Finset.mem_biUnion.mpr ⟨g, hBCF g hg,
      mem_cfgSlots_leaf (hBC g hg) ((mem_slotPair g).mpr (Or.inr rfl))⟩
  -- the colour maps are injective on each class: two members using the same colour at `v` would
  -- share the slot `(v, colour)`, which slot-freeness forbids
  have hinjA : Set.InjOn (fun g : Cfg n k => cfgI g) A := by
    intro g1 hg1 g2 hg2 heq
    have heq' : cfgI g1 = cfgI g2 := heq
    have hs1 : (v, cfgI g1) ∈ cfgSlots g1 := by rw [hAc g1 hg1]; exact mem_cfgSlots_1 g1
    have hs2 : (v, cfgI g1) ∈ cfgSlots g2 := by
      rw [heq', hAc g2 hg2]
      exact mem_cfgSlots_1 g2
    exact hS g1 g2 (hAF g1 hg1) (hAF g2 hg2) (v, cfgI g1) hs1 hs2
  have hinjB : Set.InjOn (fun g : Cfg n k => cfgI g) BC := by
    intro g1 hg1 g2 hg2 heq
    have heq' : cfgI g1 = cfgI g2 := heq
    have hs1 : (v, cfgI g1) ∈ cfgSlots g1 :=
      mem_cfgSlots_leaf (hBC g1 hg1) ((mem_slotPair g1).mpr (Or.inl rfl))
    have hs2 : (v, cfgI g1) ∈ cfgSlots g2 := by
      rw [heq']
      exact mem_cfgSlots_leaf (hBC g2 hg2) ((mem_slotPair g2).mpr (Or.inl rfl))
    exact hS g1 g2 (hBCF g1 hg1) (hBCF g2 hg2) (v, cfgI g1) hs1 hs2
  have hinjC : Set.InjOn (fun g : Cfg n k => cfgJ g) BC := by
    intro g1 hg1 g2 hg2 heq
    have heq' : cfgJ g1 = cfgJ g2 := heq
    have hs1 : (v, cfgJ g1) ∈ cfgSlots g1 :=
      mem_cfgSlots_leaf (hBC g1 hg1) ((mem_slotPair g1).mpr (Or.inr rfl))
    have hs2 : (v, cfgJ g1) ∈ cfgSlots g2 := by
      rw [heq']
      exact mem_cfgSlots_leaf (hBC g2 hg2) ((mem_slotPair g2).mpr (Or.inr rfl))
    exact hS g1 g2 (hBCF g1 hg1) (hBCF g2 hg2) (v, cfgJ g1) hs1 hs2
  -- and the three colour sets are pairwise disjoint: a colour cannot be used at `v` by a centred
  -- member and by a leaf member (slot-freeness would make them one configuration, which is never
  -- both centred and a leaf at `v`), and cannot be the `cfgI`- and the `cfgJ`-colour of one member
  have hdisj₁ : ∀ j : Fin k, j ∈ A.image (fun g => cfgI g) → j ∈ BC.image (fun g => cfgI g) →
      False := by
    intro j hj1 hj2
    obtain ⟨g1, hg1, hj1'⟩ := Finset.mem_image.mp hj1
    obtain ⟨g2, hg2, hj2'⟩ := Finset.mem_image.mp hj2
    have hs1 : (v, j) ∈ cfgSlots g1 := by rw [← hj1', hAc g1 hg1]; exact mem_cfgSlots_1 g1
    have hs2 : (v, j) ∈ cfgSlots g2 := by
      rw [← hj2']
      exact mem_cfgSlots_leaf (hBC g2 hg2) ((mem_slotPair g2).mpr (Or.inl rfl))
    have he : g1 = g2 := hS g1 g2 (hAF g1 hg1) (hBCF g2 hg2) (v, j) hs1 hs2
    have hleaf : v = cfgP g1 ∨ v = cfgQ g1 := by simpa [he.symm] using hBC g2 hg2
    rcases hleaf with hleaf | hleaf
    · exact absurd ((hAc g1 hg1).symm.trans hleaf) ((Ok_def (hok g1 (hAF g1 hg1))).1)
    · exact absurd ((hAc g1 hg1).symm.trans hleaf) ((Ok_def (hok g1 (hAF g1 hg1))).2.1)
  have hdisj₂ : ∀ j : Fin k, j ∈ A.image (fun g => cfgI g) → j ∈ BC.image (fun g => cfgJ g) →
      False := by
    intro j hj1 hj2
    obtain ⟨g1, hg1, hj1'⟩ := Finset.mem_image.mp hj1
    obtain ⟨g2, hg2, hj2'⟩ := Finset.mem_image.mp hj2
    have hs1 : (v, j) ∈ cfgSlots g1 := by rw [← hj1', hAc g1 hg1]; exact mem_cfgSlots_1 g1
    have hs2 : (v, j) ∈ cfgSlots g2 := by
      rw [← hj2']
      exact mem_cfgSlots_leaf (hBC g2 hg2) ((mem_slotPair g2).mpr (Or.inr rfl))
    have he : g1 = g2 := hS g1 g2 (hAF g1 hg1) (hBCF g2 hg2) (v, j) hs1 hs2
    have hleaf : v = cfgP g1 ∨ v = cfgQ g1 := by simpa [he.symm] using hBC g2 hg2
    rcases hleaf with hleaf | hleaf
    · exact absurd ((hAc g1 hg1).symm.trans hleaf) ((Ok_def (hok g1 (hAF g1 hg1))).1)
    · exact absurd ((hAc g1 hg1).symm.trans hleaf) ((Ok_def (hok g1 (hAF g1 hg1))).2.1)
  have hdisj₃ : ∀ j : Fin k, j ∈ BC.image (fun g => cfgI g) → j ∈ BC.image (fun g => cfgJ g) →
      False := by
    intro j hj1 hj2
    obtain ⟨g1, hg1, hj1'⟩ := Finset.mem_image.mp hj1
    obtain ⟨g2, hg2, hj2'⟩ := Finset.mem_image.mp hj2
    have hs1 : (v, j) ∈ cfgSlots g1 := by
      rw [← hj1']
      exact mem_cfgSlots_leaf (hBC g1 hg1) ((mem_slotPair g1).mpr (Or.inl rfl))
    have hs2 : (v, j) ∈ cfgSlots g2 := by
      rw [← hj2']
      exact mem_cfgSlots_leaf (hBC g2 hg2) ((mem_slotPair g2).mpr (Or.inr rfl))
    have he : g1 = g2 := hS g1 g2 (hBCF g1 hg1) (hBCF g2 hg2) (v, j) hs1 hs2
    have hj2'' : cfgJ g1 = j := by rw [he.symm] at hj2'; exact hj2'
    exact (Ok_def (hok g1 (hBCF g1 hg1))).2.2.2 (hj1'.trans hj2''.symm)
  have hint₁ : (A.image (fun g => cfgI g)) ∩ (BC.image (fun g => cfgI g)) = ∅ := by
    refine Finset.eq_empty_iff_forall_notMem.mpr fun j hj => ?_
    obtain ⟨hj1, hj2⟩ := Finset.mem_inter.mp hj
    exact hdisj₁ j hj1 hj2
  have hint₂ : ((A.image (fun g => cfgI g) ∪ BC.image (fun g => cfgI g)))
      ∩ (BC.image (fun g => cfgJ g)) = ∅ := by
    refine Finset.eq_empty_iff_forall_notMem.mpr fun j hj => ?_
    obtain ⟨hj1, hj2⟩ := Finset.mem_inter.mp hj
    rcases Finset.mem_union.mp hj1 with hj1 | hj1
    · exact hdisj₂ j hj1 hj2
    · exact hdisj₃ j hj1 hj2
  -- the colours used at `v` by the two classes are therefore exactly `|A| + 2·|BC|` of them, and they
  -- are all colours used by `F` at `v`, of which there are at most `k`
  have hcount : A.card + 2 * BC.card
      = ((A.image (fun g => cfgI g) ∪ BC.image (fun g => cfgI g))
          ∪ BC.image (fun g => cfgJ g)).card := by
    calc A.card + 2 * BC.card
        = (A.image (fun g => cfgI g)).card + (BC.image (fun g => cfgI g)).card
            + (BC.image (fun g => cfgJ g)).card := by
              rw [Finset.card_image_iff.mpr hinjA, Finset.card_image_iff.mpr hinjB,
                Finset.card_image_iff.mpr hinjC]
              ring
      _ = ((A.image (fun g => cfgI g) ∪ BC.image (fun g => cfgI g)).card
            + (BC.image (fun g => cfgJ g)).card) := by
          rw [← Finset.card_union_add_card_inter, hint₁, Finset.card_empty, Nat.add_zero]
      _ = ((A.image (fun g => cfgI g) ∪ BC.image (fun g => cfgI g))
            ∪ BC.image (fun g => cfgJ g)).card := by
          rw [← Finset.card_union_add_card_inter, hint₂, Finset.card_empty, Nat.add_zero]
  have hU : ((A.image (fun g => cfgI g) ∪ BC.image (fun g => cfgI g))
      ∪ BC.image (fun g => cfgJ g)) ⊆ SlotsAtF F v :=
    Finset.union_subset (Finset.union_subset hsubA hsubB) hsubC
  have h1 : (SlotsAtF F v).card ≤ k := by
    refine le_trans (Finset.card_le_card fun _ _ => Finset.mem_univ _) ?_
    simp
  exact hcount.le.trans ((Finset.card_le_card hU).trans h1)

/-- **A MEMBER OF `coverB F a b ∪ coverC F a b` IS A MEMBER OF THE FAMILY.** -/
private theorem memF_coverBC {n k : ℕ} {F : Fam n k} {a b : Verts n} {g : Cfg n k}
    (h : g ∈ coverB F a b ∨ g ∈ coverC F a b) : g ∈ F := by
  rcases h with h | h
  · exact (mem_coverF.mp (mem_coverB.mp h).1).1
  · exact (mem_coverF.mp (mem_coverC.mp h).1).1

/-- **A MEMBER OF `coverA F a b ∪ coverC F a b` IS A MEMBER OF THE FAMILY.** -/
private theorem memF_coverAC {n k : ℕ} {F : Fam n k} {a b : Verts n} {g : Cfg n k}
    (h : g ∈ coverA F a b ∨ g ∈ coverC F a b) : g ∈ F := by
  rcases h with h | h
  · exact (mem_coverF.mp (mem_coverA.mp h).1).1
  · exact (mem_coverF.mp (mem_coverC.mp h).1).1

/-- **A COVERING MEMBER WHICH IS NOT `a`-CENTRAL HAS `a` AS A LEAF.** -/
private theorem leaf_of_coverBC {n k : ℕ} {F : Fam n k} {a b : Verts n} {g : Cfg n k}
    (hab : a ≠ b) (h : g ∈ coverB F a b ∨ g ∈ coverC F a b) :
    a = cfgP g ∨ a = cfgQ g := by
  rcases h with h | h
  · exact coverF_leaf' hab ((mem_coverB.mp h).1)
      (fun hc => hab (hc.symm.trans (mem_coverB.mp h).2))
  · exact coverF_leaf' hab ((mem_coverC.mp h).1) ((mem_coverC.mp h).2.1)

/-- **A COVERING MEMBER WHICH IS NOT `b`-CENTRAL HAS `b` AS A LEAF.** -/
private theorem leaf_of_coverAC {n k : ℕ} {F : Fam n k} {a b : Verts n} {g : Cfg n k}
    (hab : a ≠ b) (h : g ∈ coverA F a b ∨ g ∈ coverC F a b) :
    b = cfgP g ∨ b = cfgQ g := by
  rcases h with h | h
  · exact coverF_leaf'' hab (h := (mem_coverA.mp h).1)
      (fun hc => hab (((mem_coverA.mp h).2).symm.trans hc))
  · exact coverF_leaf'' hab (h := (mem_coverC.mp h).1) ((mem_coverC.mp h).2.2)

/-- **AT THE ENDPOINT `a` OF A COVERED EDGE, THE COVERING MEMBERS COST `|coverA| + 2(|coverB| + |coverC|)`
SLOTS.** -/
theorem coverA_card_le {n k : ℕ} {F : Fam n k} (hok : OkF F) (hS : SlotFree F)
    {a b : Verts n} (hab : a ≠ b) :
    (coverA F a b).card + 2 * ((coverB F a b).card + (coverC F a b).card) ≤ k := by
  have h := class_slots_le hok hS (A := coverA F a b) (BC := coverB F a b ∪ coverC F a b)
    (fun g hg => (mem_coverF.mp (mem_coverA.mp hg).1).1)
    (fun g hg => memF_coverBC (Finset.mem_union.mp hg))
    (fun g hg => (mem_coverA.mp hg).2.symm)
    (fun g hg => leaf_of_coverBC hab (Finset.mem_union.mp hg))
  have hi : (coverB F a b) ∩ (coverC F a b) = ∅ :=
    Finset.eq_empty_iff_forall_notMem.mpr fun g hg =>
      (cover_ABC_disj hab).2.2 g (Finset.mem_inter.mp hg).1 (Finset.mem_inter.mp hg).2
  have hb : (coverB F a b).card + (coverC F a b).card
      = (coverB F a b ∪ coverC F a b).card := by
    rw [← Finset.card_union_add_card_inter, hi, Finset.card_empty, Nat.add_zero]
  omega

/-- **AT THE ENDPOINT `b` OF A COVERED EDGE, THE COVERING MEMBERS COST `|coverB| + 2(|coverA| + |coverC|)`
SLOTS.** -/
theorem coverB_card_le {n k : ℕ} {F : Fam n k} (hok : OkF F) (hS : SlotFree F)
    {a b : Verts n} (hab : a ≠ b) :
    (coverB F a b).card + 2 * ((coverA F a b).card + (coverC F a b).card) ≤ k := by
  have h := class_slots_le hok hS (A := coverB F a b) (BC := coverA F a b ∪ coverC F a b)
    (fun g hg => (mem_coverF.mp (mem_coverB.mp hg).1).1)
    (fun g hg => memF_coverAC (Finset.mem_union.mp hg))
    (fun g hg => (mem_coverB.mp hg).2.symm)
    (fun g hg => leaf_of_coverAC hab (Finset.mem_union.mp hg))
  have hi : (coverA F a b) ∩ (coverC F a b) = ∅ :=
    Finset.eq_empty_iff_forall_notMem.mpr fun g hg =>
      (cover_ABC_disj hab).2.1 g (Finset.mem_inter.mp hg).1 (Finset.mem_inter.mp hg).2
  have hb : (coverA F a b).card + (coverC F a b).card
      = (coverA F a b ∪ coverC F a b).card := by
    rw [← Finset.card_union_add_card_inter, hi, Finset.card_empty, Nat.add_zero]
  omega

/-- **NO EDGE OF `K_n` IS COVERED BY MORE THAN `2k/3` MEMBERS OF A MATCHING: `3·|coverF F (s(a,b))| ≤ 2k`.**
This is the per-edge shadow of the global `Hyper.card_auxDeg_le`, on the side of a *family*: three
members cover `s(a,b)` at most `2k` times over the two endpoints, so the edge can be covered by at
most `2k/3` members.  A first stage of arXiv:2208.12563 §4 with `k ≈ 5n/6` therefore covers each
edge at most `5n/9` times — much more than the `n^{1-δ}` of arXiv:2207.02920 Claim 4 is allowed,
which is exactly why the published construction needs `o(n²)` *left-over* edges. -/
theorem coverF_card_le {n k : ℕ} {F : Fam n k} (hok : OkF F) (hS : SlotFree F)
    {a b : Verts n} (hab : a ≠ b) : 3 * (coverF F (s(a, b))).card ≤ 2 * k := by
  have h1 := coverA_card_le hok hS hab
  have h2 := coverB_card_le hok hS hab
  have h3 := card_coverF_eq_three hok hab
  rw [h3]
  omega

/-- **A COVERED EDGE IS COVERED BY AT MOST `k` MEMBERS** (the two endpoint bounds together). -/
theorem coverF_card_le' {n k : ℕ} {F : Fam n k} (hok : OkF F) (hS : SlotFree F)
    {a b : Verts n} (hab : a ≠ b) : (coverF F (s(a, b))).card ≤ k := by
  have h := coverF_card_le hok hS hab
  omega

/-! ### 7. The per-vertex edge accounting, and the density it forces -/

/-- **THE TWO SPOKES OF A CONFIGURATION** — its two edges at its centre. -/
noncomputable def spokes {n k : ℕ} (g : Cfg n k) : Finset (Sym2 (Verts n)) :=
  insert (s(cfgU g, cfgP g)) (insert (s(cfgU g, cfgQ g)) ∅)

@[simp] theorem mem_spokes {n k : ℕ} (g : Cfg n k) (e : Sym2 (Verts n)) :
    e ∈ spokes g ↔ e = s(cfgU g, cfgP g) ∨ e = s(cfgU g, cfgQ g) := by
  simp [spokes]

theorem card_spokes {n k : ℕ} {g : Cfg n k} (h : Ok g) : (spokes g).card = 2 := by
  have hne1 : cfgU g ≠ cfgQ g := (Ok_def h).2.1
  have hne2 : cfgP g ≠ cfgQ g := (Ok_def h).2.2.1
  simp [spokes, hne1, hne2]

/-- **THE TWO SPOKES ARE EDGES OF THE CONFIGURATION.** -/
theorem spokes_subset {n k : ℕ} (g : Cfg n k) : spokes g ⊆ cfgEdges g := by
  intro e he
  rw [mem_cfgEdges]
  rcases (mem_spokes g e).mp he with he | he
  · exact Or.inl he
  · exact Or.inr (Or.inl he)

/-- **THE EDGES OF `K_n` THROUGH ONE VERTEX.** -/
noncomputable def edgesAt {n : ℕ} (v : Verts n) : Finset (Sym2 (Verts n)) :=
  ((Finset.univ : Finset (Verts n)).filter (fun x => x ≠ v)).image (fun x => s(v, x))

theorem card_edgesAt {n : ℕ} (v : Verts n) :
    (edgesAt v).card = (Finset.univ : Finset (Verts n)).card - 1 := by
  unfold edgesAt
  rw [Finset.card_image_iff.mpr (fun _ _ _ _ heq => sym2_inj_right heq)]
  have h1 : ((Finset.univ : Finset (Verts n)).filter (fun x => x ≠ v))
      = (Finset.univ : Finset (Verts n)).erase v := by
    ext x
    simp
  rw [h1, Finset.card_erase_of_mem (Finset.mem_univ v)]

theorem mem_edgesAt {n : ℕ} {v : Verts n} {e : Sym2 (Verts n)} :
    e ∈ edgesAt v ↔ ∃ x : Verts n, x ≠ v ∧ s(v, x) = e := by
  rw [edgesAt, Finset.mem_image]
  constructor
  · rintro ⟨x, hx, heq⟩
    exact ⟨x, (Finset.mem_filter.mp hx).2, heq⟩
  · rintro ⟨x, hx, heq⟩
    exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩, heq⟩

/-- **THE EDGES OF A CONFIGURATION THROUGH ONE VERTEX**: two at the centre, one at each leaf. -/
noncomputable def cfgEdgesAt {n k : ℕ} (g : Cfg n k) (v : Verts n) :
    Finset (Sym2 (Verts n)) :=
  if v = cfgU g then spokes g
  else if v = cfgP g then insert (s(cfgU g, cfgP g)) ∅
  else if v = cfgQ g then insert (s(cfgU g, cfgQ g)) ∅ else ∅

theorem card_cfgEdgesAt {n k : ℕ} {g : Cfg n k} (h : Ok g) (v : Verts n) :
    (cfgEdgesAt g v).card = if v = cfgU g then 2 else if v = cfgP g ∨ v = cfgQ g then 1 else 0 := by
  by_cases h1 : v = cfgU g
  · have e1 : (cfgEdgesAt g v).card = 2 := by
      rw [cfgEdgesAt, if_pos h1, card_spokes h]
    rw [e1, if_pos h1]
  · by_cases h2 : v = cfgP g
    · have e2 : (cfgEdgesAt g v).card = 1 := by
        rw [cfgEdgesAt, if_neg h1, if_pos h2, Finset.card_insert_of_notMem (by simp),
          Finset.card_empty, Nat.zero_add]
      rw [e2, if_neg h1, if_pos (Or.inl h2)]
    · by_cases h3 : v = cfgQ g
      · have e3 : (cfgEdgesAt g v).card = 1 := by
          rw [cfgEdgesAt, if_neg h1, if_neg h2, if_pos h3,
            Finset.card_insert_of_notMem (by simp), Finset.card_empty, Nat.zero_add]
        rw [e3, if_neg h1, if_pos (Or.inr h3)]
      · have e4 : (cfgEdgesAt g v).card = 0 := by
          rw [cfgEdgesAt, if_neg h1, if_neg h2, if_neg h3, Finset.card_empty]
        have h2' : ¬ (v = cfgP g ∨ v = cfgQ g) := by
          rintro (h2' | h2')
          · exact h2 h2'
          · exact h3 h2'
        rw [e4, if_neg h1, if_neg h2']

/-- **THE EDGES OF A CONFIGURATION THROUGH `v` ARE EDGES OF THE CONFIGURATION.** -/
theorem cfgEdgesAt_subset {n k : ℕ} {g : Cfg n k} {v : Verts n} :
    cfgEdgesAt g v ⊆ cfgEdges g := by
  intro e he
  by_cases h1 : v = cfgU g
  · rw [cfgEdgesAt, if_pos h1] at he
    exact spokes_subset g he
  · by_cases h2 : v = cfgP g
    · rw [cfgEdgesAt, if_neg h1, if_pos h2] at he
      have he' : e = s(cfgU g, cfgP g) := by simpa using he
      rw [mem_cfgEdges]
      exact Or.inl he'
    · by_cases h3 : v = cfgQ g
      · rw [cfgEdgesAt, if_neg h1, if_neg h2, if_pos h3] at he
        have he' : e = s(cfgU g, cfgQ g) := by simpa using he
        rw [mem_cfgEdges]
        exact Or.inr (Or.inl he')
      · rw [cfgEdgesAt, if_neg h1, if_neg h2, if_neg h3] at he
        exact absurd he (by simp)

/-- **AN EDGE OF A CONFIGURATION PASSES THROUGH ITS OWN VERTICES.** -/
theorem v_mem_cfgEdgesAt {n k : ℕ} {g : Cfg n k} {v : Verts n} {e : Sym2 (Verts n)}
    (he : e ∈ cfgEdgesAt g v) : v ∈ e := by
  by_cases h1 : v = cfgU g
  · rw [cfgEdgesAt, if_pos h1] at he
    rcases (mem_spokes g e).mp he with he | he
    · rw [he]; simp [h1]
    · rw [he]; simp [h1]
  · by_cases h2 : v = cfgP g
    · rw [cfgEdgesAt, if_neg h1, if_pos h2] at he
      have he' : e = s(cfgU g, cfgP g) := by simpa using he
      rw [he']; simp [h2]
    · by_cases h3 : v = cfgQ g
      · rw [cfgEdgesAt, if_neg h1, if_neg h2, if_pos h3] at he
        have he' : e = s(cfgU g, cfgQ g) := by simpa using he
        rw [he']; simp [h3]
      · rw [cfgEdgesAt, if_neg h1, if_neg h2, if_neg h3] at he
        exact absurd he (by simp)

/-- **AN EDGE THROUGH `v` WITH NO LOOP AT `v` IS AN EDGE OF `K_n` THROUGH `v`.** -/
theorem mem_edgesAt_of_v_mem {n : ℕ} {v : Verts n} {e : Sym2 (Verts n)} (hd : OffDiag e)
    (hv : v ∈ e) : e ∈ edgesAt v := by
  rw [mem_edgesAt]
  exact ⟨Sym2.Mem.other' hv,
    fun hcon => hd v v ((Sym2.other_spec' hv).symm.trans (by rw [hcon])) rfl,
    Sym2.other_spec' hv⟩

/-- **AN EDGE OF A CONFIGURATION HAS NO LOOP.** -/
theorem offDiag_of_mem_cfgEdges {n k : ℕ} {g : Cfg n k} (h : Ok g) {e : Sym2 (Verts n)}
    (he : e ∈ cfgEdges g) : OffDiag e := by
  have hd := Ok_def h
  rw [mem_cfgEdges] at he
  rcases he with he | he | he
  · rw [he]; exact offDiag_iff.mpr hd.1
  · rw [he]; exact offDiag_iff.mpr hd.2.1
  · rw [he]; exact offDiag_iff.mpr hd.2.2.1

/-- **THE EDGES OF A CONFIGURATION THROUGH `v` ARE EDGES OF `K_n` THROUGH `v`.** -/
theorem cfgEdgesAt_subset_edgesAt {n k : ℕ} {g : Cfg n k} (h : Ok g) {v : Verts n} :
    cfgEdgesAt g v ⊆ edgesAt v := by
  intro e he
  exact mem_edgesAt_of_v_mem (offDiag_of_mem_cfgEdges h (cfgEdgesAt_subset he))
    (v_mem_cfgEdgesAt he)

/-- **AN EDGE OF A CONFIGURATION THROUGH `v` IS AN EDGE OF `K_n` THROUGH `v`.** -/
theorem mem_edgesAt_of_mem_cfgEdgesAt {n k : ℕ} {g : Cfg n k} (h : Ok g) {v : Verts n}
    {e : Sym2 (Verts n)} (he : e ∈ cfgEdgesAt g v) :
    e ∈ edgesAt v :=
  cfgEdgesAt_subset_edgesAt h he

/-- **AN EDGE OF `K_n` THROUGH `v` WHICH IS COVERED IS A SPOKE OF A MEMBER PASSING THROUGH `v`.** -/
theorem mem_coveredF_of_mem_edgesAt {n k : ℕ} {F : Fam n k} (hok : OkF F) {v : Verts n}
    {e : Sym2 (Verts n)} (he : e ∈ edgesAt v) (hc : e ∈ coveredF F) :
    ∃ g : Cfg n k, g ∈ F ∧ v = cfgU g ∨ g ∈ F ∧ (v = cfgP g ∨ v = cfgQ g) := by
  obtain ⟨g, hgF, heE⟩ := mem_coveredF.mp hc
  obtain ⟨x, hx, heq⟩ := mem_edgesAt.mp he
  rw [mem_cfgEdges] at heE
  rcases heE with hE | hE | hE
  · rcases Sym2.eq_iff.mp (hE.symm.trans heq.symm) with h1 | h1
    · exact ⟨g, Or.inl ⟨hgF, h1.1.symm⟩⟩
    · exact ⟨g, Or.inr ⟨hgF, Or.inl h1.2.symm⟩⟩
  · rcases Sym2.eq_iff.mp (hE.symm.trans heq.symm) with h1 | h1
    · exact ⟨g, Or.inl ⟨hgF, h1.1.symm⟩⟩
    · exact ⟨g, Or.inr ⟨hgF, Or.inr h1.2.symm⟩⟩
  · rcases Sym2.eq_iff.mp (hE.symm.trans heq.symm) with h1 | h1
    · exact ⟨g, Or.inr ⟨hgF, Or.inl h1.1.symm⟩⟩
    · exact ⟨g, Or.inr ⟨hgF, Or.inr h1.2.symm⟩⟩

/-- **A MEMBER IS EITHER CENTRED AT `v` OR HAS `v` AS A LEAF, NEVER BOTH.** -/
theorem centF_leafF_disj {n k : ℕ} {F : Fam n k} (hok : OkF F) (v : Verts n) :
    ∀ (g : Cfg n k), g ∈ centF F v → g ∈ leafF F v → False := by
  intro g hg1 hg2
  obtain ⟨_, h1⟩ := mem_centF.mp hg1
  obtain ⟨_, h2⟩ := mem_leafF.mp hg2
  rcases h2 with h2 | h2
  · exact (Ok_def (hok g (mem_centF.mp hg1).1)).1 (h1.trans h2.symm)
  · exact (Ok_def (hok g (mem_centF.mp hg1).1)).2.1 (h1.trans h2.symm)

/-- **A MEMBER CENTRED AT `v` IS NEVER A LEAF AT `v`.** -/
theorem centF_not_leafF {n k : ℕ} {F : Fam n k} (hok : OkF F) (v : Verts n) :
    ∀ (g : Cfg n k), g ∈ centF F v → g ∉ leafF F v := by
  intro g hg hB
  exact centF_leafF_disj hok v g hg hB

/-- **THE EDGES OF A CONFIGURATION THROUGH A VERTEX** — the filter that needs no case analysis: a
member of a family uses **two** of its three edges at each of its three vertices. -/
noncomputable def covAt {n k : ℕ} (g : Cfg n k) (v : Verts n) : Finset (Sym2 (Verts n)) :=
  (cfgEdges g).filter (fun e => v ∈ e)

@[simp] theorem mem_covAt {n k : ℕ} (g : Cfg n k) {v : Verts n} {e : Sym2 (Verts n)} :
    e ∈ covAt g v ↔ e ∈ cfgEdges g ∧ v ∈ e := by
  simp [covAt]

/-- **TWO EDGES AT EVERY VERTEX OF A CONFIGURATION.** -/
theorem card_covAt {n k : ℕ} {g : Cfg n k} (h : Ok g) (v : Verts n) :
    (covAt g v).card = if v ∈ cfgVerts g then 2 else 0 := by
  have hd := Ok_def h
  have hAB : s(cfgU g, cfgP g) ≠ s(cfgU g, cfgQ g) :=
    fun hE => hd.2.2.1 (sym2_inj_right (a := cfgU g) hE)
  have hBC : s(cfgU g, cfgQ g) ≠ s(cfgP g, cfgQ g) := by
    intro hE
    rcases Sym2.eq_iff.mp hE with h1 | h1
    · exact hd.1 h1.1
    · exact hd.2.1 h1.1
  have hAC : s(cfgU g, cfgP g) ≠ s(cfgP g, cfgQ g) := by
    intro hE
    rcases Sym2.eq_iff.mp hE with h1 | h1
    · exact hd.1 h1.1
    · exact hd.2.1 h1.1
  by_cases h1 : v = cfgU g
  · have hnPQ : ¬ (v = cfgP g ∨ v = cfgQ g) := by
      rintro (h | h)
      · exact hd.1 (h1.symm.trans h)
      · exact hd.2.1 (h1.symm.trans h)
    unfold covAt
    simp only [cfgEdges, Finset.filter_insert, Finset.filter_empty, Sym2.mem_iff, mem_cfgVerts,
      if_pos (Or.inl h1), if_pos (Or.inl h1), if_neg hnPQ, if_pos (Or.inr (Or.inl h1))]
    rw [Finset.card_insert_of_notMem (by simp [hAB]),
      Finset.card_insert_of_notMem (by simp), Finset.card_empty]
  · by_cases h2 : v = cfgP g
    · have hnUQ : ¬ (v = cfgU g ∨ v = cfgQ g) := by
        rintro (h | h)
        · exact h1 h
        · exact hd.2.2.1 (h2.symm.trans h)
      unfold covAt
      simp only [cfgEdges, Finset.filter_insert, Finset.filter_empty, Sym2.mem_iff, mem_cfgVerts,
        if_pos (Or.inr h2), if_neg hnUQ, if_pos (Or.inl h2), if_pos (Or.inr (Or.inl h2))]
      rw [Finset.card_insert_of_notMem (by simp [hAC]),
        Finset.card_insert_of_notMem (by simp), Finset.card_empty]
    · by_cases h3 : v = cfgQ g
      · have hnUP : ¬ (v = cfgU g ∨ v = cfgP g) := by
          rintro (h | h)
          · exact h1 h
          · exact h2 h
        unfold covAt
        simp only [cfgEdges, Finset.filter_insert, Finset.filter_empty, Sym2.mem_iff, mem_cfgVerts,
          if_neg hnUP, if_pos (Or.inr h3), if_pos (Or.inr h3), if_pos (Or.inr (Or.inr h3))]
        rw [Finset.card_insert_of_notMem (by simp [hBC]),
          Finset.card_insert_of_notMem (by simp), Finset.card_empty]
      · have hA' : ¬ (v = cfgU g ∨ v = cfgP g) := by
          rintro (h | h)
          · exact h1 h
          · exact h2 h
        have hB' : ¬ (v = cfgU g ∨ v = cfgQ g) := by
          rintro (h | h)
          · exact h1 h
          · exact h3 h
        have hC' : ¬ (v = cfgP g ∨ v = cfgQ g) := by
          rintro (h | h)
          · exact h2 h
          · exact h3 h
        have hV : ¬ (v = cfgU g ∨ v = cfgP g ∨ v = cfgQ g) := by
          rintro (h | h | h)
          · exact h1 h
          · exact h2 h
          · exact h3 h
        unfold covAt
        simp only [cfgEdges, Finset.filter_insert, Finset.filter_empty, Sym2.mem_iff, mem_cfgVerts,
          if_neg hA', if_neg hB', if_neg hC', Finset.card_empty, if_neg hV]

/-- **THE EDGES OF A CONFIGURATION THROUGH `v` ARE EDGES OF `K_n` THROUGH `v`.** -/
theorem covAt_subset_edgesAt {n k : ℕ} {g : Cfg n k} (h : Ok g) {v : Verts n} :
    covAt g v ⊆ edgesAt v := by
  intro e he
  have he' := he
  simp only [mem_covAt] at he'
  exact mem_edgesAt_of_v_mem (offDiag_of_mem_cfgEdges h he'.1) he'.2

/-- **THE MEMBERS THROUGH `v` ARE THE CENTRED ONES AND THE ONES HAVING `v` AS A LEAF.** -/
theorem card_throughF {n k : ℕ} {F : Fam n k} (hok : OkF F) (v : Verts n) :
    (throughF F v).card = (centF F v).card + (leafF F v).card := by
  have hi : (centF F v) ∩ (leafF F v) = ∅ :=
    Finset.eq_empty_iff_forall_notMem.mpr fun g hg =>
      centF_leafF_disj hok v g (Finset.mem_inter.mp hg).1 (Finset.mem_inter.mp hg).2
  have h1 : (centF F v ∪ leafF F v).card = (centF F v).card + (leafF F v).card := by
    rw [← Finset.card_union_add_card_inter, hi, Finset.card_empty, Nat.add_zero]
  have hunion : throughF F v = centF F v ∪ leafF F v := by
    ext g
    rw [mem_throughF]
    constructor
    · intro hg
      rcases (mem_cfgVerts g (v := v)).mp hg.2 with hgv | hgv | hgv
      · exact Finset.mem_union.mpr (Or.inl (mem_centF.mpr ⟨hg.1, hgv.symm⟩))
      · exact Finset.mem_union.mpr (Or.inr (mem_leafF.mpr ⟨hg.1, Or.inl hgv.symm⟩))
      · exact Finset.mem_union.mpr (Or.inr (mem_leafF.mpr ⟨hg.1, Or.inr hgv.symm⟩))
    · intro hg
      rcases Finset.mem_union.mp hg with hgF | hgF
      · obtain ⟨hg1, hg2⟩ := mem_centF.mp hgF
        exact ⟨hg1, (mem_cfgVerts g (v := v)).mpr (Or.inl hg2.symm)⟩
      · obtain ⟨hg1, hg2⟩ := mem_leafF.mp hgF
        rcases hg2 with hgv | hgv
        · exact ⟨hg1, (mem_cfgVerts g (v := v)).mpr (Or.inr (Or.inl hgv.symm))⟩
        · exact ⟨hg1, (mem_cfgVerts g (v := v)).mpr (Or.inr (Or.inr hgv.symm))⟩
  rw [hunion]
  exact h1

/-- **THE COVERED EDGES THROUGH `v`.** -/
noncomputable def covAll {n k : ℕ} (F : Fam n k) (v : Verts n) : Finset (Sym2 (Verts n)) :=
  (throughF F v).biUnion (fun g => covAt g v)

/-- **THE COVERED EDGES THROUGH `v` NUMBER `2·(|centF F v| + |leafF F v|)`.** -/
theorem card_covAll {n k : ℕ} {F : Fam n k} (hok : OkF F) (hL : LinF F) (v : Verts n) :
    (covAll F v).card = 2 * ((centF F v).card + (leafF F v).card) := by
  have hd : ∀ g ∈ throughF F v, ∀ g' ∈ throughF F v, g ≠ g' →
      Disjoint (covAt g v) (covAt g' v) := by
    intro g hg g' hg' hne
    refine Finset.disjoint_left.2 fun e he1 he2 => ?_
    have he1' := he1
    have he2' := he2
    simp only [mem_covAt] at he1' he2'
    obtain ⟨hgF, _⟩ := mem_throughF.mp hg
    obtain ⟨hgF', _⟩ := mem_throughF.mp hg'
    exact hne (hL g g' hgF hgF' e he1'.1 he2'.1)
  have hs : ((throughF F v).biUnion (fun g => covAt g v)).card
      = ∑ g ∈ throughF F v, (covAt g v).card :=
    Finset.card_biUnion (s := throughF F v) (t := fun g => covAt g v) hd
  rw [covAll, hs]
  calc ∑ g ∈ throughF F v, (covAt g v).card = ∑ g ∈ throughF F v, 2 := by
        refine Finset.sum_congr rfl fun g hg => ?_
        obtain ⟨hgF, hv⟩ := mem_throughF.mp hg
        rw [card_covAt (hok g hgF) v, if_pos hv]
      _ = 2 * (throughF F v).card := by
        rw [Finset.sum_const, Nat.nsmul_eq_mul, Nat.mul_comm]
      _ = 2 * ((centF F v).card + (leafF F v).card) := by rw [card_throughF hok v]

/-- **AN EDGE OF A CONFIGURATION CONTAINING `v` MEANS `v` IS ONE OF ITS THREE VERTICES.** -/
theorem v_mem_cfgVerts_of_mem {n k : ℕ} {g : Cfg n k} {v : Verts n} {e : Sym2 (Verts n)}
    (he : e ∈ cfgEdges g) (hv : v ∈ e) : v ∈ cfgVerts g := by
  rw [mem_cfgEdges] at he
  rcases he with he | he | he
  · rw [he] at hv
    rcases Sym2.mem_iff.mp hv with hv | hv
    · exact (mem_cfgVerts g (v := v)).mpr (Or.inl hv)
    · exact (mem_cfgVerts g (v := v)).mpr (Or.inr (Or.inl hv))
  · rw [he] at hv
    rcases Sym2.mem_iff.mp hv with hv | hv
    · exact (mem_cfgVerts g (v := v)).mpr (Or.inl hv)
    · exact (mem_cfgVerts g (v := v)).mpr (Or.inr (Or.inr hv))
  · rw [he] at hv
    rcases Sym2.mem_iff.mp hv with hv | hv
    · exact (mem_cfgVerts g (v := v)).mpr (Or.inr (Or.inl hv))
    · exact (mem_cfgVerts g (v := v)).mpr (Or.inr (Or.inr hv))

/-- **THE COVERED EDGES THROUGH `v` ARE EXACTLY `edgesAt v ∩ coveredF F`.** -/
theorem covAll_eq_inter {n k : ℕ} {F : Fam n k} (hok : OkF F) (v : Verts n) :
    covAll F v = edgesAt v ∩ coveredF F := by
  ext e
  constructor
  · intro he
    obtain ⟨g, hg, he'⟩ := Finset.mem_biUnion.mp he
    obtain ⟨hgF, _⟩ := mem_throughF.mp hg
    have he'' := he'
    simp only [mem_covAt] at he''
    refine Finset.mem_inter.mpr ⟨covAt_subset_edgesAt (hok g hgF) he', ?_⟩
    exact mem_coveredF.mpr ⟨g, hgF, he''.1⟩
  · intro he
    obtain ⟨heE, heC⟩ := Finset.mem_inter.mp he
    obtain ⟨g, hgF, heg⟩ := mem_coveredF.mp heC
    obtain ⟨x, hx, heq⟩ := mem_edgesAt.mp heE
    have hve : v ∈ e := by rw [← heq]; exact Sym2.mem_mk_left v x
    have hvg : v ∈ cfgVerts g := v_mem_cfgVerts_of_mem heg hve
    refine Finset.mem_biUnion.mpr ⟨g, mem_throughF.mpr ⟨hgF, hvg⟩, ?_⟩
    exact (mem_covAt g (v := v) (e := e)).mpr ⟨heg, hve⟩

/-- **THE LEFTOVER EDGES THROUGH `v`.** -/
noncomputable def covR {n : ℕ} {k : ℕ} (F : Fam n k) (v : Verts n) : Finset (Sym2 (Verts n)) :=
  (leftoverF F).filter (fun e => v ∈ e)

/-- **THE LEFTOVER EDGES THROUGH `v` NUMBER `DegL (leftoverF F) v`.** -/
theorem card_covR {n : ℕ} {k : ℕ} (F : Fam n k) (v : Verts n) :
    (covR F v).card = DegL (leftoverF F) v := by
  unfold covR DegL
  rfl

/-- **THE LEFTOVER EDGES THROUGH `v` ARE EDGES OF `K_n` THROUGH `v`.** -/
theorem covR_subset_edgesAt {n : ℕ} {k : ℕ} {F : Fam n k} (hok : OkF F) (v : Verts n) :
    covR F v ⊆ edgesAt v := by
  intro e he
  have hle := mem_leftoverF.mp (Finset.mem_filter.mp he).1
  exact mem_edgesAt_of_v_mem (mem_edgeFinset.mp hle.1).2 (Finset.mem_filter.mp he).2

/-- **A COVERED EDGE THROUGH `v` IS NEVER A LEFTOVER EDGE.** -/
theorem covAll_covR_disj {n : ℕ} {k : ℕ} {F : Fam n k} (hok : OkF F) (v : Verts n) :
    ∀ e, e ∈ covAll F v → e ∈ covR F v → False := by
  intro e he1 he2
  obtain ⟨g, hg, he'⟩ := Finset.mem_biUnion.mp he1
  obtain ⟨hgF, _⟩ := mem_throughF.mp hg
  have he'' := he'
  simp only [mem_covAt] at he''
  exact (mem_leftoverF.mp (Finset.mem_filter.mp he2).1).2
    (mem_coveredF.mpr ⟨g, hgF, he''.1⟩)

/-- **THE EDGES THROUGH `v` SPLIT INTO THE COVERED AND THE LEFTOVER ONES.** -/
theorem edgesAt_eq_union {n : ℕ} {k : ℕ} {F : Fam n k} (hok : OkF F) (hL : LinF F) (v : Verts n) :
    edgesAt v = covAll F v ∪ covR F v := by
  ext e
  constructor
  · intro he
    by_cases hc : e ∈ coveredF F
    · rw [covAll_eq_inter hok v]
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr ⟨he, hc⟩))
    · obtain ⟨x, hx, heq⟩ := mem_edgesAt.mp he
      have hve : v ∈ e := by rw [← heq]; exact Sym2.mem_mk_left v x
      have hed : e ∈ edgeFinset (Finset.univ : Finset (Verts n)) := by
        rw [← heq]
        exact mem_edgeFinset_mk (Finset.mem_univ v) (Finset.mem_univ x) hx.symm
      rw [covAll_eq_inter hok v]
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr
        ⟨mem_leftoverF.mpr ⟨hed, hc⟩, hve⟩))
  · intro he
    rcases Finset.mem_union.mp he with he | he
    · rw [covAll_eq_inter hok v] at he
      exact Finset.mem_inter.mp he |>.1
    · exact covR_subset_edgesAt hok v he

/-- **THE COVERED EDGES THROUGH `v` ARE EDGES OF `K_n` THROUGH `v`.** -/
theorem covAll_subset_edgesAt {n : ℕ} {k : ℕ} {F : Fam n k} (hok : OkF F) (hL : LinF F)
    (v : Verts n) : covAll F v ⊆ edgesAt v := by
  rw [covAll_eq_inter hok v]
  exact Finset.inter_subset_left

/-- **THE PER-VERTEX EDGE ACCOUNTING: `n - 1 = 2·(|centF F v| + |leafF F v|) + DegL (leftoverF F) v`.**
Every edge of `K_n` through `v` is covered by exactly one member passing through `v` — and such a
member covers **two** of its three edges at `v` — or is a leftover edge.  This is the *local* form
of `Fam.edgeCoverF`. -/
theorem degL_at {n : ℕ} {k : ℕ} {F : Fam n k} (hok : OkF F) (hL : LinF F) (v : Verts n) :
    2 * ((centF F v).card + (leafF F v).card) + DegL (leftoverF F) v
      = (Finset.univ : Finset (Verts n)).card - 1 := by
  have hi : covAll F v ∩ covR F v = ∅ :=
    Finset.eq_empty_iff_forall_notMem.mpr fun e he =>
      covAll_covR_disj hok v e (Finset.mem_inter.mp he).1 (Finset.mem_inter.mp he).2
  have hcard : (covAll F v).card + (covR F v).card = (edgesAt v).card := by
    calc (covAll F v).card + (covR F v).card
        = (covAll F v ∪ covR F v).card := by
          rw [← Finset.card_union_add_card_inter, hi, Finset.card_empty, Nat.add_zero]
      _ = (edgesAt v).card := congrArg Finset.card (edgesAt_eq_union hok hL v).symm
  rw [card_covAll hok hL v, card_covR F v] at hcard
  rw [card_edgesAt v] at hcard
  exact hcard

/-! ### 8. The per-vertex density a sparse leftover forces -/

/-- **THE DENSITY OF A FIRST STAGE AT ONE VERTEX: `v` IS PASSED THROUGH BY AT LEAST
`⌈((n-1-D)/2)⌉` MEMBERS.**  This is `First.SparseL_iff_degTris` (the per-vertex form of JM (IV) /
BCDP Claim 4) in the world of matchings. -/
theorem throughF_card_ge {n k D : ℕ} {F : Fam n k} (hok : OkF F) (hL : LinF F)
    (hD : SparseL (leftoverF F) D) (v : Verts n) :
    2 * ((centF F v).card + (leafF F v).card)
      ≥ ((Finset.univ : Finset (Verts n)).card - 1) - D := by
  have h1 := degL_at hok hL v
  have h2 : DegL (leftoverF F) v ≤ D := hD v
  omega

/-- **AND THE MEMBERS THROUGH `v` NUMBER EXACTLY `|centF F v| + |leafF F v|`.** -/
theorem throughF_card_eq {n k : ℕ} {F : Fam n k} (hok : OkF F) (v : Verts n) :
    (throughF F v).card = (centF F v).card + (leafF F v).card :=
  card_throughF hok v

/-- **THE PER-VERTEX CENTRE LOWER BOUND: `|centF F v| ≥ (n-1-D) - k`.**  This is the *local* form of
the slot counting `First.count_lower`: the first stage of arXiv:2208.12563 §4 must make almost every
vertex a centre — it cannot hide the work at a few centres and pay for it with leaves.  Indeed
`2·(|centF| + |leafF|) ≥ (n-1) - D` (the density above) and `|centF| + 2·|leafF| ≤ k` (the slot budget)
give `(n-1) - D ≤ (|centF| + 2·|leafF|) + |centF| ≤ k + |centF|`. -/
theorem centF_card_ge {n k D : ℕ} {F : Fam n k} (hok : OkF F) (hS : SlotFree F) (hL : LinF F)
    (hD : SparseL (leftoverF F) D) (v : Verts n) :
    (centF F v).card + k ≥ ((Finset.univ : Finset (Verts n)).card - 1) - D := by
  have h1 := throughF_card_ge hok hL hD v
  have h2 := slots_at_le hok hS v
  omega

/-- **THE PER-VERTEX LEAF UPPER BOUND IN THE OTHER DIRECTION: `2·|leafF F v| ≥ (n-1-D) - 2k`.** -/
theorem leafF_card_ge {n k D : ℕ} {F : Fam n k} (hok : OkF F) (hS : SlotFree F) (hL : LinF F)
    (hD : SparseL (leftoverF F) D) (v : Verts n) :
    2 * (leafF F v).card + 2 * k ≥ ((Finset.univ : Finset (Verts n)).card - 1) - D := by
  have h1 := throughF_card_ge hok hL hD v
  have h2 := centF_card_le hok hS v
  omega

/-- **A FIRST STAGE WITH A SPARSE LEFTOVER HAS A CENTRE AT EVERY VERTEX, AS SOON AS
`(n-1) - D > k`.**  A vertex with no centred member is a leaf in at most `k/2` members, and then the
whole first stage reaches it in at most `k/2` members, which is not enough to leave at most `D`
leftover edges at it.  So *every* vertex must be a centre, which is the local reason the published
construction has to be a **triangle system with a centre at every vertex** rather than an arbitrary
maximal one. -/
theorem centF_card_ge_one {n k D : ℕ} {F : Fam n k} (hok : OkF F) (hS : SlotFree F) (hL : LinF F)
    (hD : SparseL (leftoverF F) D) {v : Verts n}
    (hv : k < ((Finset.univ : Finset (Verts n)).card - 1) - D) :
    1 ≤ (centF F v).card := by
  have h1 := centF_card_ge hok hS hL hD v
  omega

/-- **THE CENTRES OF A FIRST STAGE COVER ALL VERTICES.** -/
theorem centre_cover_univ {n k D : ℕ} {F : Fam n k} (hok : OkF F) (hS : SlotFree F) (hL : LinF F)
    (hD : SparseL (leftoverF F) D)
    (hv : k < ((Finset.univ : Finset (Verts n)).card - 1) - D) :
    ∀ v : Verts n, 1 ≤ (centF F v).card :=
  fun v => centF_card_ge_one hok hS hL hD (v := v) hv

/-- **THE FIRST STAGE'S CENTRE COUNT IS AT LEAST `n·(n - 1 - D - k)`.**  Summing `centF_card_ge` over
the vertices recovers the global count with the same strength, *pointwise*. -/
theorem sum_centF_card_ge {n k D : ℕ} {F : Fam n k} (hok : OkF F) (hS : SlotFree F) (hL : LinF F)
    (hD : SparseL (leftoverF F) D)
    (hv : ∀ v : Verts n, k < ((Finset.univ : Finset (Verts n)).card - 1) - D) :
    F.card ≥ (Finset.univ : Finset (Verts n)).card *
      (((Finset.univ : Finset (Verts n)).card - 1) - D - k) := by
  have h2 : ∀ v : Verts n, (centF F v).card + k
      ≥ ((Finset.univ : Finset (Verts n)).card - 1) - D :=
    fun v => centF_card_ge hok hS hL hD v
  have h3 : ∑ v : Verts n, (((Finset.univ : Finset (Verts n)).card - 1) - D)
      = (Finset.univ : Finset (Verts n)).card *
        (((Finset.univ : Finset (Verts n)).card - 1) - D) := by
    rw [Finset.sum_const, Nat.nsmul_eq_mul, Nat.mul_comm]
  have h4 : ∑ v : Verts n, (k : ℕ)
      = (Finset.univ : Finset (Verts n)).card * k := by
    rw [Finset.sum_const, Nat.nsmul_eq_mul, Nat.mul_comm]
  have h6 : ∀ v : Verts n,
      (((Finset.univ : Finset (Verts n)).card - 1) - D) - k ≤ (centF F v).card := by
    intro v
    have h := h2 v
    omega
  calc F.card = ∑ v : Verts n, (centF F v).card := (sum_centreF_card F).symm
    _ ≥ ∑ v : Verts n, ((((Finset.univ : Finset (Verts n)).card - 1) - D) - k) :=
          Finset.sum_le_sum fun v _ => h6 v
    _ = (Finset.univ : Finset (Verts n)).card *
        (((Finset.univ : Finset (Verts n)).card - 1) - D - k) := by
      rw [Finset.sum_const, Nat.nsmul_eq_mul, Nat.mul_comm]

end JSP140
