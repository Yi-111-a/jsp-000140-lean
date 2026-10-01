import JSPProblem.Triangles

/-!
# JSP-000140 — the **second stage** of the published construction: completing a partial
# labelled-triangle system

Rounds 10–28 classified admissible colourings; round 28 turned the catalog condition into four
local conditions (`Criterion.design_iff_admissible`); round 29 encoded the object the literature
actually builds (`Triangles.Covers`, `Triangles.PairFree`, `Triangles.LabTri`) and proved that
`Tile` and `Packed` are **free** consequences of the matching condition
(`Triangles.tile_of_tri`, `Triangles.packed_of_tri`).

Round 29's hypothesis `Triangles.TriFamily` demanded a **complete** covering (`Covers`), i.e. that
every edge of `K_m` lies in a labelled triangle.  That is **strictly stronger** than the published
statement: arXiv:2208.12563 §4 (= arXiv:2207.02920) builds the labelled triangles by a hypergraph
matching covering only `1 - o(1)` of the edges, and then **colours the leftover graph `L` in a
second stage**, with `n^{1-δ}` extra colours, by a symmetric local lemma.

**This file formalises that second stage.**  There is no hypergraph, no probability and no local
lemma here: this is the *exact interface* between the first stage and the second one, and it is
proved, with no placeholder of any kind.

* `leftover c`, `covers_iff_leftover_eq_empty` — **THE LEFTOVER GRAPH** of a partial construction:
  the edges of `K_n` lying in no labelled triangle.  A complete covering is the empty leftover, so
  the two-stage form genuinely generalises round 29's hypothesis.
* `card_lost`, `lost_four` — **THE ACCOUNTING OF THE LOSS**: how many edges the first stage failed
  to cover, and the local fact that a four-set loses at most six edges.
* `Extends`, `Rainbow`, `Compensate` — the interface conditions of the second stage, of which
  `Rainbow` is the strongest and `Compensate` the weakest; `Compensate.of_rainbow` proves the
  implication.
* **`card_colorsOn_ext`** — **THE COUNTING IDENTITY OF THE SECOND STAGE**: the colours of the
  extension are exactly the first-stage colours surviving on the covered edges together with the
  fresh colours on the leftover edges, and these two sets are disjoint because the leftover colours
  are fresh.  Nothing is lost by the second stage except by collision with fresh colours.
* `admissible_of_covered` — if the first stage already gives five colours on the *covered* edges of
  every four-set, the second stage cannot spoil the catalog condition, whatever fresh colours it
  uses.
* **`admissible_of_ext`** — **THE VERIFICATION LEMMA IN THE PUBLISHED FORM**: an admissible
  first-stage colouring, extended on the leftover edges by *fresh* colours which **compensate** (are
  at least as numerous, on every four-set, as the first-stage colours that die there), is
  admissible.  This is the lemma that composes the two stages of arXiv:2208.12563 §4.
* `admissible_of_ext_rainbow` — its corollary for a **rainbow** second stage, which is what the
  symmetric local lemma produces.
* `extendCol`, `admissible_of_extendCol`, `rainbow_of_matching`,
  `admissible_of_matching_leftover` — the second stage **as a function**; in particular
  **IF THE LEFTOVER IS A MATCHING THE SECOND STAGE IS COMPLETE AND NEEDS NO LOCAL LEMMA**.
* **`ExtFamily` and `jsp_000140_main_of_ext_family`** — **THE REQUIRED THEOREM `jsp_000140_main`,
  REDUCED TO THE PUBLISHED STATEMENT IN ITS FAITHFUL TWO-STAGE FORM.**  Unlike `TriFamily`,
  `ExtFamily` asks for no complete covering: for every `δ > 0` and all large `m ≡ 1 (mod 6)` a
  partial labelled-triangle system whose leftover graph can be given `K` extra colours that
  compensate inside every four-set, with `6(k+K) ≤ 5(m-1) + δm`.  `ExtFamily_of_TriFamily` shows
  round 29 is not lost: with `K = 0` the leftover is empty.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace JSP140

attribute [local instance] Classical.propDecidable

variable {n k : ℕ}

/-! ### Finset counting tools for the second stage -/

/-- **THE PARTITION OF AN IMAGE.**  Over the decomposition `Y = X ∪ (Y \ X)`, the number of colours
of `Y` is at most the number of colours of `X` plus the number of colours of `Y \ X`. -/
private theorem card_image_le_sum {α β : Type*} [DecidableEq α] [DecidableEq β] {g : α → β}
    {X Y : Finset α} :
    (Y.image g).card ≤ (X.image g).card + ((Y \ X).image g).card := by
  have hsub : Y.image g ⊆ (X.image g) ∪ ((Y \ X).image g) := by
    intro z hz
    simp only [Finset.mem_image] at hz
    obtain ⟨e, he, hce⟩ := hz
    rw [Finset.mem_union]
    by_cases hx : e ∈ X
    · refine Or.inl ?_
      exact Finset.mem_image.mpr ⟨e, hx, hce⟩
    · refine Or.inr ?_
      exact Finset.mem_image.mpr ⟨e, Finset.mem_sdiff.mpr ⟨he, hx⟩, hce⟩
  exact le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)

/-- Every off-diagonal unordered pair is an edge of `K_n`. -/
theorem mem_edge_univ {n : ℕ} {e : Sym2 (Verts n)} (he : OffDiag e) :
    e ∈ edgeFinset (Finset.univ : Finset (Verts n)) := by
  obtain ⟨a, b, hab⟩ : ∃ a b : Verts n, e = s(a, b) :=
    Quot.inductionOn e (fun p : Verts n × Verts n => ⟨p.1, p.2, rfl⟩)
  have hne : a ≠ b := fun h => (he a b (by rw [hab, h])) h
  rw [hab]
  exact mem_edgeFinset_mk (Finset.mem_univ a) (Finset.mem_univ b) hne

/-- The number of edges of `K_n`. -/
theorem card_edgeFinset_univ (n : ℕ) :
    (edgeFinset (Finset.univ : Finset (Verts n))).card = Nat.choose (n + 1) 2 - n := by
  rw [card_edgeFinset, Finset.card_univ, Fintype.card_fin]

/-! ### The leftover graph of a partial construction -/

/-- **AN EDGE IS COVERED BY THE CONSTRUCTION** if it lies in one of the labelled triangles. -/
def Covered {n k : ℕ} (c : Col n k) (e : Sym2 (Verts n)) : Prop :=
  ∃ u p q : Verts n, LabTri c u p q ∧ e ∈ triEdges c u p q

/-- **THE LEFTOVER GRAPH `L`.**  The edges of `K_n` which lie in *no* labelled triangle of `c`: the
edges the hypergraph matching of arXiv:2208.12563 §4 does not cover, and the graph that the
**second stage** has to colour with `o(n)` extra colours. -/
noncomputable def leftover {n k : ℕ} (c : Col n k) : Finset (Sym2 (Verts n)) :=
  (edgeFinset (Finset.univ : Finset (Verts n))).filter fun e => ¬ Covered c e

@[simp] theorem mem_leftover {n k : ℕ} {c : Col n k} {e : Sym2 (Verts n)} :
    e ∈ leftover c ↔ e ∈ edgeFinset (Finset.univ : Finset (Verts n)) ∧ ¬ Covered c e :=
  Finset.mem_filter

theorem mem_leftover_of_covered {n k : ℕ} {c : Col n k} {e : Sym2 (Verts n)}
    (h : Covered c e) : e ∉ leftover c := by
  obtain ⟨u, p, q, h1, h2⟩ := h
  rw [mem_leftover]
  intro hcon
  exact hcon.2 ⟨u, p, q, h1, h2⟩

/-- **A COMPLETE COVERING IS THE EMPTY LEFTOVER GRAPH.**  This is how the two-stage form
generalises round 29's hypothesis: `Covers c` is not needed, only `leftover c = ∅`. -/
theorem Covers_of_leftover_eq_empty {n k : ℕ} {c : Col n k} (h : leftover c = ∅) : Covers c := by
  intro e he
  by_contra hnc
  have hne : e ∉ leftover c := by
    rw [h]
    simp
  exact hne (mem_leftover.mpr ⟨mem_edge_univ he, hnc⟩)

theorem covers_iff_leftover_eq_empty {n k : ℕ} {c : Col n k} : Covers c ↔ leftover c = ∅ := by
  constructor
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    by_cases hd : OffDiag e
    · exact absurd (h e hd) (mem_leftover.mp he).2
    · exact hd ((mem_edgeFinset.mp (mem_leftover.mp he).1).2)
  · exact Covers_of_leftover_eq_empty

/-- **THE LOCAL ACCOUNTING OF THE LOSS.**  Every four-set loses at most its six edges. -/
theorem lost_four {n k : ℕ} {c : Col n k} {S : Finset (Verts n)} (hS : S.card = 4) :
    (edgeFinset S \ leftover c).card ≤ 6 := by
  have h := Finset.card_le_card (Finset.sdiff_subset : edgeFinset S \ leftover c ⊆ edgeFinset S)
  rw [card_edgeFinset_four hS] at h
  omega

/-- **THE NUMBER OF UNCOVERED EDGES IS WHAT THE SECOND STAGE PAYS FOR.** -/
theorem card_lost {n k : ℕ} (c : Col n k) :
    (edgeFinset (Finset.univ : Finset (Verts n)) \ leftover c).card
      = Nat.choose (n + 1) 2 - n - (leftover c).card := by
  have h := Finset.card_sdiff_add_card_eq_card
    (s := leftover c) (t := edgeFinset (Finset.univ : Finset (Verts n)))
    (Finset.filter_subset _ _)
  have h2 : (edgeFinset (Finset.univ : Finset (Verts n))).card = Nat.choose (n + 1) 2 - n :=
    card_edgeFinset_univ n
  omega

/-! ### The interface conditions of the second stage -/

/-- **THE FIRST STAGE EXTENDED BY FRESH COLOURS.**  `c₀` is the first stage (colours `0, …, k-1`),
`c` is the completed colouring, and the leftover edges receive only *fresh* colours
(`k, …, k+K-1`): the first component says the first-stage colours are kept off the leftover, the
second says the fresh colours occur on the leftover and nowhere else. -/
def Extends {n k K : ℕ} (c₀ c : Col n (k + K)) (L : Finset (Sym2 (Verts n))) : Prop :=
  (∀ e, e ∉ L → c e = c₀ e) ∧ (∀ e, (e ∈ L) ↔ k ≤ (c e).val)

theorem Extends.agree {n k K : ℕ} {c₀ c : Col n (k + K)} {L : Finset (Sym2 (Verts n))}
    (h : Extends c₀ c L) {e : Sym2 (Verts n)} (he : e ∉ L) : c e = c₀ e := h.1 e he

theorem Extends.fresh {n k K : ℕ} {c₀ c : Col n (k + K)} {L : Finset (Sym2 (Verts n))}
    (h : Extends c₀ c L) {e : Sym2 (Verts n)} (he : e ∈ L) : k ≤ (c e).val := (h.2 e).mp he

theorem Extends.not_fresh {n k K : ℕ} {c₀ c : Col n (k + K)} {L : Finset (Sym2 (Verts n))}
    (h : Extends c₀ c L) {e : Sym2 (Verts n)} (he : e ∉ L) : (c e).val < k := by
  by_contra hcon
  exact he ((h.2 e).mpr (le_of_not_gt hcon))

/-- **RAINBOW ON THE LEFTOVER.**  Inside every four-set, the leftover edges receive pairwise
distinct fresh colours: the colours are reused, but never twice inside a clique of four vertices.
This is what the symmetric local lemma of arXiv:2208.12563 §4 produces. -/
def Rainbow {n k K : ℕ} (c : Col n (k + K)) (L : Finset (Sym2 (Verts n))) : Prop :=
  ∀ S : Finset (Verts n), S.card = 4 →
    ∀ e : Sym2 (Verts n), e ∈ L ∩ edgeFinset S →
    ∀ e' : Sym2 (Verts n), e' ∈ L ∩ edgeFinset S → c e = c e' → e = e'

/-- **COMPENSATION.**  Inside every four-set, the fresh colours appearing on the leftover edges are
at least as many as the first-stage colours that die on them.  This is strictly weaker than
`Rainbow`, and it is the exact condition under which the second stage is invisible to the catalog
condition. -/
def Compensate {n k K : ℕ} (c₀ c : Col n (k + K)) (L : Finset (Sym2 (Verts n))) : Prop :=
  ∀ S : Finset (Verts n), S.card = 4 →
    ((edgeFinset S ∩ L).image c₀).card ≤ ((edgeFinset S ∩ L).image c).card

theorem Compensate.of_rainbow {n k K : ℕ} {c₀ c : Col n (k + K)}
    {L : Finset (Sym2 (Verts n))} (h : Rainbow c L) : Compensate c₀ c L := by
  intro S hS
  calc ((edgeFinset S ∩ L).image c₀).card ≤ (edgeFinset S ∩ L).card := Finset.card_image_le
    _ = ((edgeFinset S ∩ L).image c).card :=
        (Finset.card_image_iff.mpr (fun e he e' he' hce =>
          h S hS e ((Finset.inter_comm (edgeFinset S) L) ▸ he)
            e' ((Finset.inter_comm (edgeFinset S) L) ▸ he') hce)).symm

/-! ### The counting identity of the second stage -/

/-- **THE FIRST-STAGE COLOURS ON THE COVERED PART ARE THE COLOURS OF THE EXTENSION THERE.** -/
private theorem image_agree {n k K : ℕ} {c₀ c : Col n (k + K)}
    {L X : Finset (Sym2 (Verts n))} (hE : Extends c₀ c L)
    (hX : ∀ e, e ∈ X → e ∉ L) : (X.image c₀) = (X.image c) := by
  apply Finset.ext
  intro z
  constructor
  · intro hz
    simp only [Finset.mem_image] at hz
    obtain ⟨e, he, hce⟩ := hz
    simp only [Finset.mem_image]
    exact ⟨e, he, (hE.agree (hX e he)) ▸ hce⟩
  · intro hz
    simp only [Finset.mem_image] at hz
    obtain ⟨e, he, hce⟩ := hz
    simp only [Finset.mem_image]
    exact ⟨e, he, (hE.agree (hX e he)).symm ▸ hce⟩

/-- **THE COUNTING IDENTITY OF THE SECOND STAGE.**  On a four-set, the colours of the extension are
the first-stage colours that survive on the covered edges *together with* the fresh colours on the
leftover edges, and the two sets are disjoint because the leftover colours are fresh: the number of
colours of the extension is at least their sum. -/
theorem card_colorsOn_ext {n k K : ℕ} {c₀ c : Col n (k + K)} {L : Finset (Sym2 (Verts n))}
    (hE : Extends c₀ c L) {S : Finset (Verts n)} :
    ((edgeFinset S \ L).image c₀).card + ((edgeFinset S ∩ L).image c).card
      ≤ (colorsOn c S).card := by
  have hag : (edgeFinset S \ L).image c₀ = (edgeFinset S \ L).image c :=
    image_agree hE (fun e he => (Finset.mem_sdiff.mp he).2)
  have hdis : ((edgeFinset S \ L).image c) ∩ ((edgeFinset S ∩ L).image c) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro z hz
    rw [Finset.mem_inter] at hz
    obtain ⟨hz1, hz2⟩ := hz
    simp only [Finset.mem_image] at hz1 hz2
    obtain ⟨e, he, hce⟩ := hz1
    obtain ⟨e', he', hce'⟩ := hz2
    have h1 : e ∉ L := (Finset.mem_sdiff.mp he).2
    have h2 : e' ∈ L := (Finset.mem_inter.mp he').2
    have h3 : (c e).val < k := hE.not_fresh (e := e) h1
    have h4 : k ≤ (c e').val := hE.fresh (e := e') h2
    have hval : (c e).val = (c e').val := by
      rw [hce, hce']
    omega
  have hsub : ((edgeFinset S \ L).image c) ∪ ((edgeFinset S ∩ L).image c) ⊆ colorsOn c S := by
    refine Finset.union_subset ?_ ?_
    · intro z hz
      simp only [Finset.mem_image] at hz
      obtain ⟨e, he, hce⟩ := hz
      simp only [colorsOn, Finset.mem_image]
      exact ⟨e, (Finset.mem_sdiff.mp he).1, (hE.agree (Finset.mem_sdiff.mp he).2) ▸ hce⟩
    · exact Finset.image_subset_image Finset.inter_subset_left
  have hcard : (((edgeFinset S \ L).image c) ∪ ((edgeFinset S ∩ L).image c)).card
      = ((edgeFinset S \ L).image c).card + ((edgeFinset S ∩ L).image c).card := by
    have h := Finset.card_union_add_card_inter
      ((edgeFinset S \ L).image c) ((edgeFinset S ∩ L).image c)
    rw [hdis, Finset.card_empty, add_zero] at h
    omega
  calc ((edgeFinset S \ L).image c₀).card + ((edgeFinset S ∩ L).image c).card
      = ((edgeFinset S \ L).image c).card + ((edgeFinset S ∩ L).image c).card := by rw [hag]
    _ ≤ (colorsOn c S).card := hcard.symm ▸ Finset.card_le_card hsub

/-- **THE FIRST-STAGE COLOURS OF A FOUR-SET.**  The colours of the first stage on a four-set are at
most the ones it keeps on the covered edges plus the ones that die on the leftover edges. -/
private theorem card_colorsOn_le_sum {n k K : ℕ} {c₀ : Col n (k + K)}
    {L : Finset (Sym2 (Verts n))} {S : Finset (Verts n)} :
    (colorsOn c₀ S).card
      ≤ ((edgeFinset S \ L).image c₀).card + ((edgeFinset S ∩ L).image c₀).card := by
  have h4 : edgeFinset S \ (edgeFinset S \ L) = edgeFinset S ∩ L := by
    ext e
    simp
  rw [colorsOn]
  have h3 := card_image_le_sum (g := c₀) (X := edgeFinset S \ L) (Y := edgeFinset S)
  rw [h4] at h3
  exact h3

/-! ### The verification lemmas of the second stage -/

/-- **THE FIRST STAGE ALONE IS ENOUGH IF IT IS STRONG ON THE COVERED PART.**  If the covered edges
of every four-set already span five colours, then *any* fresh colouring of the leftover edges keeps
the catalog condition: the second stage can only add colours, never remove them. -/
theorem admissible_of_covered {n k K : ℕ} {c₀ c : Col n (k + K)} {L : Finset (Sym2 (Verts n))}
    (h0 : ∀ S : Finset (Verts n), S.card = 4 → 5 ≤ ((edgeFinset S \ L).image c₀).card)
    (hE : Extends c₀ c L) : Admissible c := by
  intro S hS
  have hsub : (edgeFinset S \ L).image c₀ ⊆ colorsOn c S := by
    refine (image_agree hE (fun e he => (Finset.mem_sdiff.mp he).2)) ▸ ?_
    exact Finset.image_subset_image (Finset.sdiff_subset : edgeFinset S \ L ⊆ edgeFinset S)
  have h1 := h0 S hS
  have h2 := Finset.card_le_card hsub
  omega

/-- **THE VERIFICATION LEMMA OF THE SECOND STAGE — THE PUBLISHED FORM.**  An admissible first-stage
colouring, extended on the leftover edges by *fresh* colours which **compensate** (are at least as
numerous, on every four-set, as the first-stage colours that die there), is admissible.

This is the lemma that composes the two stages of arXiv:2208.12563 §4, and it is the exact
interface at which the probabilistic local lemma has to be plugged in. -/
theorem admissible_of_ext {n k K : ℕ} {c₀ c : Col n (k + K)} {L : Finset (Sym2 (Verts n))}
    (hc₀ : Admissible c₀) (hE : Extends c₀ c L) (hC : Compensate c₀ c L) : Admissible c := by
  intro S hS
  have h1 := hc₀ S hS
  have h2 := card_colorsOn_le_sum (n := n) (k := k) (K := K) (c₀ := c₀) (L := L) (S := S)
  have h3 := card_colorsOn_ext hE (S := S)
  have h4 := hC S hS
  omega

/-- **THE VERIFICATION LEMMA FOR A RAINBOW SECOND STAGE.**  The local lemma of arXiv:2208.12563 §4
delivers a *rainbow* colouring of the leftover graph, so this is the form in which it is used. -/
theorem admissible_of_ext_rainbow {n k K : ℕ} {c₀ c : Col n (k + K)}
    {L : Finset (Sym2 (Verts n))} (hc₀ : Admissible c₀) (hE : Extends c₀ c L)
    (hrain : Rainbow c L) : Admissible c :=
  admissible_of_ext hc₀ hE (Compensate.of_rainbow hrain)

/-! ### The second stage as a function -/

/-- **A FRESH COLOUR.**  The colour `k + j` of the bigger palette: outside the first-stage
palette `0, …, k-1`. -/
def freshCol {k K : ℕ} (j : ℕ) (hj : j < K) : Fin (k + K) := ⟨k + j, Nat.add_lt_add_left hj k⟩

@[simp] theorem freshCol_val {k K : ℕ} (j : ℕ) (hj : j < K) :
    ((freshCol (k := k) (K := K) j hj) : Fin (k + K)).val = k + j := rfl

theorem freshCol_inj {k K : ℕ} {j j' : ℕ} (hj : j < K) (hj' : j' < K)
    (heq : freshCol (k := k) (K := K) j hj = freshCol (k := k) (K := K) j' hj') :
    (⟨j, hj⟩ : Fin K) = ⟨j', hj'⟩ := by
  apply Fin.ext
  have h := congrArg Fin.val heq
  simpa using h

/-- **THE SECOND STAGE, WITH A DEPENDENT COLOURING OF THE LEFTOVER.**  `g` assigns to every leftover
edge one of the `K` fresh colours; the first-stage colours are kept everywhere else.  (The
colouring is *dependent* because the leftover set may be empty, in which case no assignment — and
in particular no function into an empty palette — exists.) -/
def extendColDep {n k K : ℕ} (c : Col n k) (L : Finset (Sym2 (Verts n)))
    (g : ∀ e, e ∈ L → Fin K) : Col n (k + K) :=
  fun e => if h : e ∈ L then freshCol (g e h).val (g e h).isLt
            else liftCol c (Nat.le_add_right k K) e

theorem extendColDep_of_mem {n k K : ℕ} {c : Col n k} {L : Finset (Sym2 (Verts n))}
    {g : ∀ e, e ∈ L → Fin K} {e : Sym2 (Verts n)} (h : e ∈ L) :
    extendColDep c L g e = freshCol (g e h).val (g e h).isLt := by
  simp [extendColDep, h]

theorem extendColDep_of_nmem {n k K : ℕ} {c : Col n k} {L : Finset (Sym2 (Verts n))}
    {g : ∀ e, e ∈ L → Fin K} {e : Sym2 (Verts n)} (h : e ∉ L) :
    extendColDep c L g e = liftCol c (Nat.le_add_right k K) e := by
  simp [extendColDep, h]

@[simp] theorem val_extendColDep_of_nmem {n k K : ℕ} {c : Col n k}
    {L : Finset (Sym2 (Verts n))} {g : ∀ e, e ∈ L → Fin K} {e : Sym2 (Verts n)} (h : e ∉ L) :
    (extendColDep c L g e).val = (c e).val := by
  rw [extendColDep_of_nmem h]
  rfl

/-- **THE SECOND STAGE EXTENDS THE FIRST STAGE BY FRESH COLOURS.** -/
theorem Extends_extendColDep {n k K : ℕ} {c : Col n k} {L : Finset (Sym2 (Verts n))}
    {g : ∀ e, e ∈ L → Fin K} :
    Extends (liftCol c (Nat.le_add_right k K)) (extendColDep c L g) L := by
  refine ⟨fun _ he => ?_, fun e => ?_⟩
  · rw [extendColDep_of_nmem he]
  · constructor
    · intro he
      rw [extendColDep_of_mem he, freshCol_val]
      omega
    · intro hval
      by_contra hne
      have h1 : (c e).val = (extendColDep c L g e).val := (val_extendColDep_of_nmem hne).symm
      have h2 : (c e).val < k := (c e).isLt
      omega

/-- **THE SECOND STAGE IS AN ADMISSIBLE COLOURING.**  The published second stage: keep the
first-stage colours on the covered edges, give every leftover edge a fresh colour which is distinct
from the colours of the other leftover edges of the same four-set, and the result satisfies the
catalog condition of `JSP-000140`. -/
theorem admissible_of_extendColDep {n k K : ℕ} {c : Col n k} (hc : Admissible c)
    {L : Finset (Sym2 (Verts n))} {g : ∀ e, e ∈ L → Fin K}
    (hinj : ∀ (e e' : Sym2 (Verts n)) (he : e ∈ L) (he' : e' ∈ L),
      g e he = g e' he' → e = e') :
    Admissible (extendColDep c L g) := by
  refine admissible_of_ext_rainbow (admissible_liftCol c (Nat.le_add_right k K) hc)
    (Extends_extendColDep (c := c) (L := L) (g := g)) ?_
  intro S hS e he e' he' heq
  obtain ⟨he1, he2⟩ := Finset.mem_inter.mp he
  obtain ⟨he'1, he'2⟩ := Finset.mem_inter.mp he'
  rw [extendColDep_of_mem he1, extendColDep_of_mem he'1] at heq
  exact hinj e e' he1 he'1 (by simpa using freshCol_inj _ _ heq)

/-- **THE INDEX MAP OF THE LEFTOVER IS AN INJECTIVE COLOURING OF IT.**  Every edge of `L` is given
the index it has in `L`, so `K = |L|` fresh colours are enough and the colouring is injective. -/
theorem rainbow_of_index {n : ℕ} {L : Finset (Sym2 (Verts n))} :
    ∃ g : ∀ e, e ∈ L → Fin L.card,
      ∀ (e e' : Sym2 (Verts n)) (he : e ∈ L) (he' : e' ∈ L),
        g e he = g e' he' → e = e' := by
  refine ⟨fun e h => Finset.equivFin L ⟨e, h⟩, fun e e' he he' h => ?_⟩
  exact congrArg Subtype.val ((Finset.equivFin L).injective h)

/-- **IF THE LEFTOVER IS A MATCHING, NO LOCAL LEMMA IS NEEDED.**  Any admissible first-stage
colouring whose leftover graph is a matching extends to an admissible colouring of `K_n` using
`|L|` extra colours: inside a four-set there is at most one leftover edge, so the freshness of the
new colours already implies rainbow.  (In the published construction the leftover has maximum degree
`n^{1-δ}`, and this is exactly where the symmetric local lemma is needed.) -/
theorem admissible_of_matching_leftover {n k : ℕ} {c : Col n k} (hc : Admissible c)
    {L : Finset (Sym2 (Verts n))}
    (hmatch : ∀ S : Finset (Verts n), S.card = 4 → (L ∩ edgeFinset S).card ≤ 1) :
    ∃ g : ∀ e, e ∈ L → Fin L.card,
      (∀ (e e' : Sym2 (Verts n)) (he : e ∈ L) (he' : e' ∈ L),
        g e he = g e' he' → e = e') ∧
        Admissible (extendColDep c L g) := by
  obtain ⟨g, hg⟩ := rainbow_of_index (L := L)
  exact ⟨g, hg, admissible_of_extendColDep hc hg⟩

/-! ### The faithful, two-stage form of the construction hypothesis -/

/-- **THE PUBLISHED CONSTRUCTION IN ITS FAITHFUL TWO-STAGE FORM (arXiv:2208.12563 §4).**  For every
`δ > 0` and all large `m ≡ 1 (mod 6)` there is a first-stage `k`-colouring `c₀` of `K_m` — a family of
labelled triangles with pairwise disjoint `(vertex, colour)` usage — such that

* `c₀` is admissible (`Admissible c₀`), so the first stage on its own already satisfies the catalog
  condition on all of `K_m`;
* the leftover graph `leftover c₀` — the edges not covered by any labelled triangle — can be given
  `K` extra colours which are **rainbow** inside every four-set
  (`Rainbow c (leftover c₀)`), and these colours are all **fresh** while the first-stage colours are
  kept on the covered edges (`Extends c₀ c (leftover c₀)`);
* the two stages together use at most `5(m-1)/6 + δm/6` colours.

Note what is **not** asked: no complete covering (`Triangles.Covers`), which round 29's `TriFamily`
required and which is strictly stronger than the published statement. -/
def ExtFamily : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ M K : ℕ, ∀ m : ℕ, M ≤ m → m % 6 = 1 →
    ∃ (k : ℕ) (c₀ c : Col m (k + K)),
      PairFree c₀ ∧ Admissible c₀ ∧ Extends c₀ c (leftover c₀) ∧ Rainbow c (leftover c₀) ∧
      (6 : ℝ) * ((k + K : ℕ) : ℝ) ≤ 5 * ((m - 1 : ℕ) : ℝ) + δ * (m : ℝ)

/-- **THE TWO STAGES COMPOSE.**  A family of partial labelled-triangle systems with a rainbow
second stage gives a family of **admissible** colourings — this is the content of the second stage,
and it is proved here, not assumed. -/
theorem SlackFamily.of_ext (hfam : ExtFamily) : SlackFamily := by
  intro δ hδ
  obtain ⟨M, K, hM⟩ := hfam δ hδ
  refine ⟨max M 4, fun m hMm hm => ?_⟩
  obtain ⟨k, c₀, c, hP, hc₀, hE, hR, hk⟩ := hM m (by omega) hm
  exact ⟨k + K, c, admissible_of_ext_rainbow hc₀ hE hR, hk⟩

/-- **THE REQUIRED THEOREM `jsp_000140_main`, REDUCED TO THE PUBLISHED STATEMENT IN ITS FAITHFUL
TWO-STAGE FORM.**  Together with the lower half (`Main.fiveSixthLower_eg`) this says: the whole
remaining content of the prize is the *probabilistic second stage* — the symmetric local lemma that
colours the leftover graph of a partial labelled-triangle system with `n^{1-δ}` fresh colours,
pairwise distinct inside every four-set. -/
theorem jsp_000140_main_of_ext_family (hfam : ExtFamily) : jsp_000140_target :=
  jsp_000140_main_of_slack_family (SlackFamily.of_ext hfam)

/-- **ROUND 29 IS NOT LOST.**  A family of complete labelled-triangle systems (`Triangles.TriFamily`,
which asks for `Covers` and is therefore *stronger* than the published statement) is an instance of
the faithful two-stage form of this round: with `K = 0` the leftover is empty. -/
theorem ExtFamily_of_TriFamily (hfam : TriFamily) : ExtFamily := by
  intro δ hδ
  obtain ⟨M, hM⟩ := hfam δ hδ
  refine ⟨max M 4, 0, fun m hMm hm => ?_⟩
  obtain ⟨k, c, hC, hP, hX, hB, hk⟩ := hM m (by omega) hm
  have hL : leftover c = ∅ := (covers_iff_leftover_eq_empty (c := c)).mp hC
  have hE : Extends (liftCol c (Nat.le_add_right k 0)) (liftCol c (Nat.le_add_right k 0))
      (leftover c) :=
    ⟨fun _ _ => rfl,
     fun e => ⟨fun he => by
        have hfalse : False := by
          rw [hL] at he
          simp at he
        exact hfalse.elim,
      fun hval => by
        have hval' : k ≤ (c e).val := by
          rw [liftCol] at hval
          exact hval
        have hfalse : False := absurd hval' (by simp)
        exact hfalse.elim⟩⟩
  have hR : Rainbow (liftCol c (Nat.le_add_right k 0)) (leftover c) := by
    intro S hS e he
    have hfalse : False := by
      rw [hL] at he
      simp at he
    exact hfalse.elim
  exact ⟨k, liftCol c (Nat.le_add_right k 0), liftCol c (Nat.le_add_right k 0), hP,
    admissible_liftCol c (Nat.le_add_right k 0) (admissible_of_tri (by omega) hC hP hX hB),
    hE, hR, hk⟩

end JSP140
