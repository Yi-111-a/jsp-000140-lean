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

## what is still missing

The per-vertex *budget* `|centF F v| + 2·|leafF F v| ≤ k` (which needs the disjointness of the slot
sets used by different members of a matching, i.e. `SlotFree` applied one vertex at a time) and the
per-edge bound `3·|coverF F (s(a,b))| ≤ 2k` (the same disjointness, summed over the two endpoints).
Both were drafted this round and are the next round's first items; the machinery they need
(`slotPair`, `coverA/coverB/coverC`, `coverBC_leaf`, `card_leafF`, `card_SlotsAtF`) is in the build.
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

end JSP140
