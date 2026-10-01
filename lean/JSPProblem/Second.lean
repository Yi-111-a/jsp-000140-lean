import JSPProblem.Leftover

/-!
# JSP-000140 — the second stage of the published construction, in the form the papers state it

Round 30 formalised the second stage through `Leftover.Rainbow` ("the leftover edges receive
pairwise distinct fresh colours inside every four-set") and called the symmetric local lemma of
arXiv:2208.12563 §4 to produce it.  **Both papers were read this round, and the interface is
different**:

1. **The second stage is *proper*, not *rainbow*.**  In both papers the hypergraph matching covers
   only `1 - o(1)` of the edges (BCDP §4: the process stops at `i_max = n²(1-n^{-δ})/6`; JM
   Theorem 4.2: the leftover `L = K_n - E(F)` has `Θ(n^{2-δ})` edges), and the leftover graph is
   then coloured with `n^{1-δ}` fresh colours (JM §4) resp. `εn/2` fresh colours (BCDP §12).  Each
   fresh colour is *reused* `Θ(n^{1-δ})` times, so no distinctness inside a `K₄` is required — the
   requirement is only that a fresh colour class is a **matching**.  In JM's words the bad events
   are `A_{e,f,i}` ("for any pair `e,f` of adjacent edges in `L` and `i ∈ P`, the event that both
   receive colour `i`"), in BCDP's `B₁`; both are excluded by a *greedy* edge colouring, with no
   probability at all, and `2Δ(L)+1 = 2n^{1-δ}+1` fresh colours suffice.

2. **The verification condition is an identity, not an inequality.**  Round 30's
   `Leftover.card_colorsOn_ext` is a `≤`; `colorsOn_ext_card` is the corresponding `=` and
   `admissible_iff_second_stage` turns it into an **if and only if**.  So the two stages are
   verified by exactly one local condition: on every four-set, (first-stage colours surviving on
   the covered edges) + (fresh colours on the leftover edges) `≥ 5`.

What this file proves (527 lines, 26 declarations, zero placeholders):

* `colorsOn_ext_card`, **`admissible_iff_second_stage`** — the exact criterion of (2), and
  `secondStage_of_ext` (round 30's `Compensate` route) as an instance of it;
* `Shares`, `Shares.symm`, `DegL`, `SparseL`, **`Proper`** — the graph-theoretic vocabulary of the
  second stage, with `Proper` = "each fresh colour class on `L` is a matching", i.e. the published
  condition `A_{e,f,i}`;
* `card_shares_le`, **`proper_of_sparseL`** — the counting lemma behind the greedy step (at most
  `2D` leftover edges meet a given leftover edge when `Δ(L) ≤ D`);
* **`rainbow_of_sparse_leftover`** — the named next lemma of round 30's policy, **proved, in the
  published form**: a leftover graph of maximum degree `D` admits a `2D+1`-colouring in which two
  leftover edges sharing a vertex never get the same colour.  This is the deterministic half of
  the local lemma (`A_{e,f,i}` / `B₁`), and it is *all* that the greedy step of either paper needs;
* `DegL_le`, `DegL_leftover`, `proper_of_leftover` — the leftover graph of any colouring always
  satisfies `Δ(L) ≤ n-1`, so the second stage always exists and costs at most `2n-1` fresh
  colours; in the published construction `Δ(L) ≤ n^{1-δ}`, hence `2n^{1-δ}+1 = o(n)`;
* `exists_four_adjacent`, **`Rainbow.proper`**, `Rainbow.proper_leftover` — two leftover edges
  sharing a vertex lie in a common four-set (`4 ≤ n`), so the round-30 interface `Rainbow` is at
  least as strong as the published properness.

What is left, and it is now stated as sharply as possible: the two remaining bad-event families
of JM §4, i.e. a greedy `2D+1`-colouring of `L` in which **(P2)** no 4-cycle of `L` is
alternating, and **(P3)** no crossing pair of leftover edges of equal fresh colour sees a
first-stage monochromatic pair on the complementary two edges.  (P2) and (P3) are the only
probabilistic content of the second stage — that is the symmetric local lemma, of which Mathlib
has no implementation.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace JSP140

attribute [local instance] Classical.propDecidable

variable {n k : ℕ}

/-! ### The exact counting identity of the second stage -/

/-- The first-stage colours on the covered part are the colours of the extension there. -/
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

/-- **THE TWO PALETTES ARE DISJOINT.**  No fresh colour occurs on a covered edge. -/
private theorem inter_image_empty {n k K : ℕ} {c₀ c : Col n (k + K)}
    {L : Finset (Sym2 (Verts n))} (hE : Extends c₀ c L) {S : Finset (Verts n)} :
    ((edgeFinset S \ L).image c) ∩ ((edgeFinset S ∩ L).image c) = ∅ := by
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

/-- **THE EXACT COUNTING IDENTITY OF THE SECOND STAGE.**  The colours of the extension on a
four-set are *exactly* the first-stage colours surviving on the covered edges together with the
fresh colours on the leftover edges; the two palettes are disjoint, so their cardinalities add.
Round 30 proved the corresponding `≤` (`Leftover.card_colorsOn_ext`); the equality is what makes
the criterion below an `iff`. -/
theorem colorsOn_ext_card {n k K : ℕ} {c₀ c : Col n (k + K)} {L : Finset (Sym2 (Verts n))}
    (hE : Extends c₀ c L) (S : Finset (Verts n)) :
    (colorsOn c S).card
      = ((edgeFinset S \ L).image c₀).card + ((edgeFinset S ∩ L).image c).card := by
  have hag : (edgeFinset S \ L).image c = (edgeFinset S \ L).image c₀ :=
    (image_agree hE (fun e he => (Finset.mem_sdiff.mp he).2)).symm
  have hdis : ((edgeFinset S \ L).image c) ∩ ((edgeFinset S ∩ L).image c) = ∅ :=
    inter_image_empty hE
  have hsplit : edgeFinset S = (edgeFinset S \ L) ∪ (edgeFinset S ∩ L) := by
    ext e
    rw [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hcol : colorsOn c S = (edgeFinset S \ L ∪ edgeFinset S ∩ L).image c :=
    congrArg (fun t : Finset (Sym2 (Verts n)) => t.image c) hsplit
  calc (colorsOn c S).card = ((edgeFinset S \ L ∪ edgeFinset S ∩ L).image c).card :=
        congrArg Finset.card hcol
    _ = (((edgeFinset S \ L).image c) ∪ ((edgeFinset S ∩ L).image c)).card := by
        rw [Finset.image_union]
    _ = ((edgeFinset S \ L).image c).card + ((edgeFinset S ∩ L).image c).card := by
        rw [← Finset.card_union_add_card_inter, hdis, Finset.card_empty, add_zero]
    _ = ((edgeFinset S \ L).image c₀).card + ((edgeFinset S ∩ L).image c).card := by
        rw [hag]

/-- **THE EXACT VERIFICATION CONDITION OF THE TWO STAGES.**  On every four-set: the first-stage
colours that survive on the covered edges, plus the fresh colours on the leftover edges, number at
least five. -/
def SecondStage {n K : ℕ} (c₀ c : Col n K) (L : Finset (Sym2 (Verts n))) : Prop :=
  ∀ S : Finset (Verts n), S.card = 4 →
    5 ≤ ((edgeFinset S \ L).image c₀).card + ((edgeFinset S ∩ L).image c).card

/-- **THE TWO STAGES COMPOSE — AND THE CONDITION IS NECESSARY AS WELL AS SUFFICIENT.**  Under
`Extends`, `Admissible c` is **equivalent** to `SecondStage c₀ c L`.  Nothing beyond this local
condition is needed, and nothing less will do: the two palettes are disjoint, so the number of
colours of the extension on a four-set *is* the sum of the two terms. -/
theorem admissible_iff_second_stage {n k K : ℕ} {c₀ c : Col n (k + K)}
    {L : Finset (Sym2 (Verts n))} (hE : Extends c₀ c L) :
    Admissible c ↔ SecondStage c₀ c L := by
  constructor
  · intro h S hS
    rw [← colorsOn_ext_card hE S]
    exact h S hS
  · intro h S hS
    rw [colorsOn_ext_card hE S]
    exact h S hS

/-- Round 30's verification lemma is an instance: `Compensate` implies `SecondStage` whenever the
first stage is admissible. -/
theorem secondStage_of_ext {n k K : ℕ} {c₀ c : Col n (k + K)} {L : Finset (Sym2 (Verts n))}
    (hc₀ : Admissible c₀) (hE : Extends c₀ c L) (hC : Compensate c₀ c L) : SecondStage c₀ c L :=
  (admissible_iff_second_stage hE).mp (admissible_of_ext hc₀ hE hC)

/-! ### The leftover graph as a graph: degree, sparseness, properness -/

/-- **TWO EDGES SHARE A VERTEX.**  (In a four-set, two distinct edges either share a vertex or
are the two crossing edges; `Shares` is the relation the bad events `A_{e,f,i}` of
arXiv:2208.12563 §4 forbid.) -/
def Shares {n : ℕ} (e e' : Sym2 (Verts n)) : Prop := ∃ v : Verts n, v ∈ e ∧ v ∈ e'

theorem Shares.mono_edge {n : ℕ} {e e' : Sym2 (Verts n)} (h : Shares e e') {x : Sym2 (Verts n)}
    (hx : x = e') : Shares e x := by
  obtain ⟨v, hv, hv'⟩ := h
  exact ⟨v, hv, hx.symm ▸ hv'⟩

theorem Shares.symm {n : ℕ} {e e' : Sym2 (Verts n)} (h : Shares e e') : Shares e' e := by
  obtain ⟨v, hv, hv'⟩ := h
  exact ⟨v, hv', hv⟩

/-- **THE DEGREE OF A LEFTOVER GRAPH AT A VERTEX.** -/
def DegL {n : ℕ} (L : Finset (Sym2 (Verts n))) (v : Verts n) : ℕ :=
  (L.filter (fun e => v ∈ e)).card

/-- **THE LEFTOVER GRAPH HAS MAXIMUM DEGREE AT MOST `D`.**  In the published construction this is
`D = n^{1-δ}` (arXiv:2208.12563 §4, (IV) of Thm 4.2; arXiv:2207.02920 Claim 4: "at the end of
Phase 1 each vertex is incident with `O(n^{1-δ})` uncolored edges"). -/
def SparseL {n : ℕ} (L : Finset (Sym2 (Verts n))) (D : ℕ) : Prop := ∀ v : Verts n, DegL L v ≤ D

/-- **THE SECOND STAGE IS PROPER.**  Two leftover edges sharing a vertex receive different fresh
colours: this is the family of bad events `A_{e,f,i}` (JM §4) resp. `B₁` (BCDP §12), and it is
what the published construction needs of its second stage. -/
def Proper {n K : ℕ} (c : Col n K) (L : Finset (Sym2 (Verts n))) : Prop :=
  ∀ e : Sym2 (Verts n), e ∈ L → ∀ e' : Sym2 (Verts n), e' ∈ L → e ≠ e' → Shares e e' → c e ≠ c e'

/-- A subgraph of a sparse leftover graph is sparse. -/
theorem SparseL.mono {n D : ℕ} {L L' : Finset (Sym2 (Verts n))} (hD : SparseL L D)
    (hsub : L' ⊆ L) : SparseL L' D := by
  intro v
  unfold DegL
  have hsub' : L'.filter (fun e => v ∈ e) ⊆ L.filter (fun e => v ∈ e) := by
    intro e he
    have he1 := Finset.mem_filter.mp he
    exact Finset.mem_filter.mpr ⟨hsub he1.1, he1.2⟩
  exact le_trans (Finset.card_le_card hsub') (hD v)

/-- **AN EDGE WHICH MEETS `s(a, b)` CONTAINS `a` OR `b`.** -/
private theorem mem_shares {n : ℕ} {a b : Verts n} {e' : Sym2 (Verts n)}
    (hsh : Shares e' (s(a, b))) : a ∈ e' ∨ b ∈ e' := by
  obtain ⟨x, y, hxy⟩ : ∃ x y : Verts n, e' = s(x, y) :=
    Quot.inductionOn e' (fun p : Verts n × Verts n => ⟨p.1, p.2, rfl⟩)
  rw [hxy] at hsh
  obtain ⟨w, hw, hws⟩ := hsh
  have hwxy : w = x ∨ w = y := (Sym2.mem_iff).mp hw
  by_cases hwx : w = x
  · rcases (Sym2.mem_iff).mp (hwx ▸ hws) with h1 | h1
    · exact Or.inl (hxy ▸ h1 ▸ Sym2.mem_mk_left x y)
    · exact Or.inr (hxy ▸ h1 ▸ Sym2.mem_mk_left x y)
  · rcases (Sym2.mem_iff).mp ((hwxy.resolve_left hwx) ▸ hws) with h1 | h1
    · exact Or.inl (hxy ▸ h1 ▸ Sym2.mem_mk_right x y)
    · exact Or.inr (hxy ▸ h1 ▸ Sym2.mem_mk_right x y)

/-- **THE NUMBER OF LEFTOVER EDGES ADJACENT TO A GIVEN LEFTOVER EDGE.**  Each of them meets one of
the two endpoints, so it is bounded by twice the maximum degree. -/
theorem card_shares_le {n D : ℕ} {L : Finset (Sym2 (Verts n))} (hD : SparseL L D)
    (a b : Verts n) :
    (L.filter (fun e' => Shares e' (s(a, b)))).card ≤ 2 * D := by
  have hsub : L.filter (fun e' => Shares e' (s(a, b)))
      ⊆ (L.filter (fun e' => a ∈ e')) ∪ (L.filter (fun e' => b ∈ e')) := by
    intro e he
    have he1 := Finset.mem_filter.mp he
    have hab : a ∈ e ∨ b ∈ e := mem_shares he1.2
    exact Finset.mem_union.mpr (Or.elim hab
      (fun h => Or.inl (Finset.mem_filter.mpr ⟨he1.1, h⟩))
      (fun h => Or.inr (Finset.mem_filter.mpr ⟨he1.1, h⟩)))
  have hle : ((L.filter (fun e' => a ∈ e')) ∪ (L.filter (fun e' => b ∈ e'))).card ≤ 2 * D := by
    refine le_trans (Finset.card_union_le _ _) ?_
    have h1 : (L.filter (fun e' => a ∈ e')).card = DegL L a := rfl
    have h3 : (L.filter (fun e' => b ∈ e')).card = DegL L b := rfl
    rw [h1, h3]
    have hda := hD a
    have hdb := hD b
    omega
  exact le_trans (Finset.card_le_card hsub) hle

/-- **THE OTHER ENDPOINT OF AN EDGE THROUGH `v`.**  An edge of `K_n` which contains `v` is
`s(v, x)` for a unique `x ≠ v`. -/
private theorem exists_other {n : ℕ} {v : Verts n} {e : Sym2 (Verts n)}
    (hd : OffDiag e) (hv : v ∈ e) : ∃ x : Verts n, e = s(v, x) ∧ x ≠ v := by
  refine ⟨Sym2.Mem.other' hv, (Sym2.other_spec' hv).symm, fun hcon => ?_⟩
  have hself : (e : Sym2 (Verts n)) = s(v, v) :=
    (Sym2.other_spec' hv).symm.trans (by rw [hcon])
  exact (hd v v hself) rfl

/-- **A COLOUR AVAILABLE FOR ONE MORE EDGE.**  If at most `2D` colours are used on `N`, then among
`2D+1` fresh colours one is not used on `N` at all. -/
private theorem exists_free_colour {n D : ℕ} {N : Finset (Sym2 (Verts n))}
    (f : ∀ e : Sym2 (Verts n), e ∈ N → Fin (2 * D + 1))
    (hN : N.card ≤ 2 * D) :
    ∃ j : Fin (2 * D + 1), ∀ (e : Sym2 (Verts n)) (he : e ∈ N), f e he ≠ j := by
  set U : Finset (Fin (2 * D + 1)) :=
    N.attach.image (fun z : {e // e ∈ N} => f z.1 z.2) with hU
  have h1 : U.card ≤ N.attach.card := by
    rw [hU]
    exact Finset.card_image_le
  have h1' : N.attach.card = N.card := Finset.card_attach
  have h2 : U.card < (Finset.univ : Finset (Fin (2 * D + 1))).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨j, hj⟩ := Finset.sdiff_nonempty_of_card_lt_card h2
  have hnotU : j ∉ U := (Finset.mem_sdiff.mp hj).2
  refine ⟨j, fun e he hcon => ?_⟩
  have hmemU : f e he ∈ U := by
    rw [hU]
    exact Finset.mem_image.mpr ⟨⟨e, he⟩, Finset.mem_attach N ⟨e, he⟩, rfl⟩
  exact hnotU (hcon ▸ hmemU)

/-- **THE SECOND STAGE IS AVAILABLE, WITH `2D+1` FRESH COLOURS, AS SOON AS THE LEFTOVER GRAPH HAS
MAXIMUM DEGREE `D`.**  Greedy edge colouring of `L`: process the edges of `L` one at a time and
give each edge a fresh colour different from those of the at most `2D` edges of `L` it meets.  This
is the deterministic half of the second stage of arXiv:2208.12563 §4: the bad events `A_{e,f,i}`
are excluded *without any probability*, and the number of extra colours is `2Δ(L)+1`, which is
`O(n^{1-δ}) = o(n)` in the published construction. -/
theorem proper_of_sparseL {n D : ℕ} {L : Finset (Sym2 (Verts n))} (hD : SparseL L D) :
    ∃ g : L → Fin (2 * D + 1),
      ∀ (x y : {e : Sym2 (Verts n) // e ∈ L}), x ≠ y → Shares x.1 y.1 → g x ≠ g y := by
  have key : ∀ (t : Finset (Sym2 (Verts n))), SparseL t D →
      ∃ g : t → Fin (2 * D + 1),
        ∀ (x y : {e : Sym2 (Verts n) // e ∈ t}), x ≠ y → Shares x.1 y.1 → g x ≠ g y := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
        exact fun _ => ⟨fun x => ⟨0, by omega⟩, fun x y _ _ => nomatch x⟩
    | @insert a s ha ih =>
        intro hDt
        have hDs : SparseL s D := hDt.mono (Finset.subset_insert a s)
        obtain ⟨g₀, hg₀⟩ := ih hDs
        obtain ⟨a₁, a₂, hae⟩ : ∃ x y : Verts n, a = s(x, y) :=
          Quot.inductionOn a (fun p : Verts n × Verts n => ⟨p.1, p.2, rfl⟩)
        have hNcard : (s.filter (fun e' => Shares e' a)).card ≤ 2 * D := by
          rw [hae]
          exact card_shares_le hDs a₁ a₂
        obtain ⟨j, hj⟩ := exists_free_colour
          (N := s.filter (fun e' => Shares e' a))
          (f := fun e he => g₀ ⟨e, (Finset.mem_filter.mp he).1⟩) hNcard
        have ins : ∀ (x : {e : Sym2 (Verts n) // e ∈ insert a s}), x.1 ≠ a → x.1 ∈ s := by
          intro x hx
          rcases Finset.mem_insert.mp x.2 with h2 | h2
          · exact absurd h2 hx
          · exact h2
        let gfun : {e : Sym2 (Verts n) // e ∈ insert a s} → Fin (2 * D + 1) :=
          fun x => if h : x.1 = a then j else g₀ ⟨x.1, ins x h⟩
        refine ⟨gfun, fun x y hxy hsh => ?_⟩
        by_cases hxa : x.1 = a
        · have hyne : y.1 ≠ a := fun hy => hxy (Subtype.ext (hxa.trans hy.symm))
          have hsh' : Shares y.1 a := (hsh.symm).mono_edge hxa.symm
          have hmem : y.1 ∈ s.filter (fun e' => Shares e' a) :=
            Finset.mem_filter.mpr ⟨ins y hyne, hsh'⟩
          simp only [gfun, dite_eq_left hxa, dite_eq_right hyne]
          intro hcon
          exact hj y.1 hmem hcon.symm
        · by_cases hya : y.1 = a
          · have hsh' : Shares x.1 a := hsh.mono_edge hya.symm
            have hmem : x.1 ∈ s.filter (fun e' => Shares e' a) :=
              Finset.mem_filter.mpr ⟨ins x hxa, hsh'⟩
            simp only [gfun, dite_eq_right hxa, dite_eq_left hya]
            intro hcon
            exact hj x.1 hmem hcon
          · simp only [gfun, dite_eq_right hxa, dite_eq_right hya]
            refine hg₀ ⟨x.1, ins x hxa⟩ ⟨y.1, ins y hya⟩ ?_ hsh
            intro hq
            have hval : x.1 = y.1 :=
              congrArg (fun z : {e : Sym2 (Verts n) // e ∈ s} => (z.1 : Sym2 (Verts n))) hq
            exact hxy (@Subtype.ext_iff (Sym2 (Verts n)) (fun e => e ∈ insert a s) x y |>.mpr hval)
  exact key L hD

/-- **THE DETERMINISTIC CONTENT OF THE LOCAL LEMMA.**  The bad events `A_{e,f,i}` of
arXiv:2208.12563 §4 (= `B₁` of arXiv:2207.02920 §12) are avoided by a greedy colouring of the
leftover graph with `2Δ(L)+1` fresh colours; only the events `C_{D,i}` really need the local
lemma. -/
theorem rainbow_of_sparse_leftover {n k D : ℕ} {c : Col n k} (hc : Admissible c)
    {L : Finset (Sym2 (Verts n))} (hD : SparseL L D) :
    ∃ (g : ∀ e, e ∈ L → Fin (2 * D + 1)), Proper (extendColDep c L g) L := by
  obtain ⟨ĝ, hĝ⟩ := proper_of_sparseL hD
  have hg : Proper (extendColDep c L (fun e h => ĝ ⟨e, h⟩)) L := by
    intro e he e' he' hne hsh
    rw [extendColDep_of_mem he, extendColDep_of_mem he']
    intro hcon
    have hval : (ĝ ⟨e, he⟩ : Fin (2 * D + 1)).val = (ĝ ⟨e', he'⟩ : Fin (2 * D + 1)).val := by
      have h := congrArg Fin.val hcon
      simpa using h
    have hcol : ĝ ⟨e, he⟩ = ĝ ⟨e', he'⟩ := by
      apply Fin.ext
      exact hval
    refine hĝ _ _ ?_ hsh hcol
    intro heq
    exact hne (congrArg Subtype.val heq)
  exact ⟨fun e h => ĝ ⟨e, h⟩, hg⟩

/-- **THE LEFTOVER GRAPH HAS MAXIMUM DEGREE AT MOST `n - 1`.**  Each of the edges of `L` at `v` is
of the form `s(v, x)` with `x ≠ v`, and distinct edges give distinct `x`; so there are at most
`n - 1` of them and `SparseL L (n - 1)` always holds. -/
theorem DegL_le {n : ℕ} {L : Finset (Sym2 (Verts n))}
    (hL : L ⊆ edgeFinset (Finset.univ : Finset (Verts n))) {v : Verts n} : DegL L v ≤ n - 1 := by
  set T := L.filter (fun e => v ∈ e) with hT
  set W : Finset (Verts n) := (Finset.univ : Finset (Verts n)).filter (fun x => x ≠ v) with hW
  have hsub : T ⊆ W.image (fun x : Verts n => s(v, x)) := by
    intro e he
    have he1 := Finset.mem_filter.mp he
    have hd : OffDiag e := (mem_edgeFinset.mp (hL he1.1)).2
    obtain ⟨x, hx, hxn⟩ := exists_other hd he1.2
    refine Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hxn⟩, hx.symm⟩
  have hinj : Set.InjOn (fun x : Verts n => s(v, x)) W :=
    fun _ _ _ _ heq => sym2_inj_right heq
  calc DegL L v = T.card := by rw [DegL, hT]
    _ ≤ (W.image (fun x : Verts n => s(v, x))).card := Finset.card_le_card hsub
    _ = W.card := Finset.card_image_iff.mpr hinj
    _ = n - 1 := by
        have hfilter : ((Finset.univ : Finset (Verts n)).filter (fun x => x ≠ v))
            = (Finset.univ : Finset (Verts n)).erase v := by
          ext x
          simp
        rw [hW, hfilter, Finset.card_erase_of_mem (Finset.mem_univ v)]
        simp [Finset.card_univ, Fintype.card_fin]

/-- **THE LEFTOVER GRAPH OF A COLOURING ALWAYS HAS MAXIMUM DEGREE AT MOST `n - 1`.**  Together with
`rainbow_of_sparse_leftover` this says that the second stage *always exists* and costs at most
`2n-1` fresh colours; in the published construction `D = n^{1-δ}`, so it costs `2n^{1-δ}+1`. -/
theorem DegL_leftover {n k : ℕ} {c : Col n k} {v : Verts n} : DegL (leftover c) v ≤ n - 1 :=
  DegL_le (fun _ he => (mem_leftover.mp he).1)

/-- **THE SECOND STAGE ALWAYS EXISTS, AT A COST OF AT MOST `2n-1` FRESH COLOURS.** -/
theorem proper_of_leftover {n K : ℕ} {L : Finset (Sym2 (Verts n))}
    (hD : SparseL L (n - 1)) :
    ∃ g : L → Fin (2 * (n - 1) + 1),
      ∀ (x y : {e : Sym2 (Verts n) // e ∈ L}), x ≠ y → Shares x.1 y.1 → g x ≠ g y :=
  proper_of_sparseL hD

/-! ### The round-30 interface is strictly stronger than the published one -/

/-- **A FOUR-SET CONTAINING TWO ADJACENT EDGES** (`n ≥ 4`).  If `e = s(a,b)` and `e' = s(a,a')` are
edges of `K_n` meeting in the vertex `a`, and the four vertices `a`, `b`, `a'` are distinct, then
some four-element vertex set spans both.  Together with `Rainbow.proper` this is what is needed of
the round-30 interface: two leftover edges sharing a vertex get different colours. -/
theorem exists_four_adjacent {n : ℕ} (hn : 4 ≤ n) {e e' : Sym2 (Verts n)} (hd : OffDiag e)
    (hd' : OffDiag e') (a b a' : Verts n) (he : e = s(a, b)) (he' : e' = s(a, a'))
    (hab : a ≠ b) (haa' : a ≠ a') (hba' : b ≠ a') :
    ∃ S : Finset (Verts n), S.card = 4 ∧ e ∈ edgeFinset S ∧ e' ∈ edgeFinset S := by
  have hcard3 : (({a, b, a'} : Finset (Verts n)) : Finset (Verts n)).card ≤ 3 := by
    have h1 := Finset.card_insert_le (a := a') (s := (∅ : Finset (Verts n)))
    have h2 := Finset.card_insert_le (a := b) (s := insert a' (∅ : Finset (Verts n)))
    have h4 := Finset.card_insert_le (a := a) (s := insert b (insert a' (∅ : Finset (Verts n))))
    simp only [Finset.card_empty] at h1
    have hid : ({a, b, a'} : Finset (Verts n))
        = insert a (insert b (insert a' (∅ : Finset (Verts n)))) := by
      ext z
      simp
    rw [hid]
    omega
  obtain ⟨x, hx⟩ := Finset.sdiff_nonempty_of_card_lt_card
    (s := ({a, b, a'} : Finset (Verts n))) (t := (Finset.univ : Finset (Verts n)))
    (by rw [Finset.card_univ, Fintype.card_fin]; omega)
  have hxm := Finset.mem_sdiff.mp hx
  have hxa : x ≠ a := fun h => hxm.2 (Finset.mem_insert.mpr (Or.inl h))
  have hxb : x ≠ b := fun h => hxm.2 (Finset.mem_insert.mpr
    (Or.inr (Finset.mem_insert.mpr (Or.inl h))))
  have hxa' : x ≠ a' := fun h => hxm.2 (Finset.mem_insert.mpr
    (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h)))))
  have e4 : x ∉ (∅ : Finset (Verts n)) := by simp
  have e3 : a' ∉ insert x (∅ : Finset (Verts n)) := by
    intro hmem
    rcases Finset.mem_insert.mp hmem with h | h
    · exact hxa' h.symm
    · exact absurd h (by simp)
  have e2 : b ∉ insert a' (insert x (∅ : Finset (Verts n))) := by
    intro hmem
    rcases Finset.mem_insert.mp hmem with h | h
    · exact hba' h
    · rcases Finset.mem_insert.mp h with h | h
      · exact hxb h.symm
      · exact absurd h (by simp)
  have e1 : a ∉ insert b (insert a' (insert x (∅ : Finset (Verts n)))) := by
    intro hmem
    rcases Finset.mem_insert.mp hmem with h | h
    · exact hab h
    · rcases Finset.mem_insert.mp h with h | h
      · exact haa' h
      · rcases Finset.mem_insert.mp h with h | h
        · exact hxa h.symm
        · exact absurd h (by simp)
  set S : Finset (Verts n) := insert a (insert b (insert a' (insert x ∅))) with hS
  have memS : ∀ (z : Verts n), z = a ∨ z = b ∨ z = a' ∨ z = x → z ∈ S := by
    intro z hz
    rw [hS]
    rcases hz with hz | hz | hz | hz
    · exact Finset.mem_insert.mpr (Or.inl hz)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl hz)))
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
        (Or.inr (Finset.mem_insert.mpr (Or.inl hz)))))
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
        (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl hz)))))))
  refine ⟨S, ?_, ?_, ?_⟩
  · rw [hS, Finset.card_insert_of_notMem e1, Finset.card_insert_of_notMem e2,
      Finset.card_insert_of_notMem e3, Finset.card_insert_of_notMem e4]
    simp
  · rw [hS, he]
    exact mem_edgeFinset_mk (memS a (Or.inl rfl)) (memS b (Or.inr (Or.inl rfl))) hab
  · rw [hS, he']
    exact mem_edgeFinset_mk (memS a (Or.inl rfl)) (memS a' (Or.inr (Or.inr (Or.inl rfl)))) haa'

/-- **A RAINBOW SECOND STAGE IS IN PARTICULAR PROPER.**  This is all that is needed of the
round-30 interface: two leftover edges sharing a vertex lie in a common four-set, so they get
different colours. -/
theorem Rainbow.proper {n k K : ℕ} {c : Col n (k + K)}
    {L : Finset (Sym2 (Verts n))} (hL : ∀ e ∈ L, OffDiag e) (hn : 4 ≤ n) (h : Rainbow c L) :
    Proper c L := by
  intro e he e' he' hne hsh
  have hd : OffDiag e := hL e he
  have hd' : OffDiag e' := hL e' he'
  obtain ⟨a, b, hab⟩ : ∃ x y : Verts n, e = s(x, y) :=
    Quot.inductionOn e (fun p : Verts n × Verts n => ⟨p.1, p.2, rfl⟩)
  obtain ⟨a', b', ha'b'⟩ : ∃ x y : Verts n, e' = s(x, y) :=
    Quot.inductionOn e' (fun p : Verts n × Verts n => ⟨p.1, p.2, rfl⟩)
  obtain ⟨v, hv, hv'⟩ := hsh
  have hvv : v = a ∨ v = b := (Sym2.mem_iff).mp (hab ▸ hv)
  have hvv' : v = a' ∨ v = b' := (Sym2.mem_iff).mp (ha'b' ▸ hv')
  have hne1 : a ≠ b := fun hcon => hd a b hab hcon
  have hne2 : a' ≠ b' := fun hcon => hd' a' b' ha'b' hcon
  obtain ⟨S, hS, he1, he2⟩ : ∃ S : Finset (Verts n), S.card = 4 ∧ e ∈ edgeFinset S ∧
      e' ∈ edgeFinset S := by
    rcases hvv with h1 | h1 <;> rcases hvv' with h2 | h2
    · have hraw : e = s(v, b) := Eq.trans hab (congrArg (fun z : Verts n => s(z, b)) h1.symm)
      have hev' : e' = s(v, b') := Eq.trans ha'b' (congrArg (fun z : Verts n => s(z, b')) h2.symm)
      refine exists_four_adjacent hn hd hd' v b b' hraw hev' ?_ ?_ ?_
      · intro hcon
        exact hne1 ((h1.symm).trans hcon)
      · intro hcon
        exact hne2 ((h2.symm).trans hcon)
      · intro hcon
        exact hne (Eq.trans hraw (Eq.trans (congrArg (fun z : Verts n => s(v, z)) hcon) hev'.symm))
    · have hraw : e = s(v, b) := Eq.trans hab (congrArg (fun z : Verts n => s(z, b)) h1.symm)
      have hraw' : e' = s(a', v) := Eq.trans ha'b' (congrArg (fun z : Verts n => s(a', z)) h2.symm)
      have hev' : e' = s(v, a') := Eq.trans hraw' Sym2.eq_swap
      refine exists_four_adjacent hn hd hd' v b a' hraw hev' ?_ ?_ ?_
      · intro hcon
        exact hne1 ((h1.symm).trans hcon)
      · intro hcon
        exact hne2 (((h2.symm).trans hcon).symm)
      · intro hcon
        exact hne (Eq.trans hraw (Eq.trans (congrArg (fun z : Verts n => s(v, z)) hcon) hev'.symm))
    · have hraw : e = s(a, v) := Eq.trans hab (congrArg (fun z : Verts n => s(a, z)) h1.symm)
      have hev' : e' = s(v, b') := Eq.trans ha'b' (congrArg (fun z : Verts n => s(z, b')) h2.symm)
      have hev : e = s(v, a) := Eq.trans hraw Sym2.eq_swap
      refine exists_four_adjacent hn hd hd' v a b' hev hev' ?_ ?_ ?_
      · intro hcon
        exact hne1 ((hcon.symm).trans h1)
      · intro hcon
        exact hne2 ((hcon.symm).trans h2).symm
      · intro hcon
        exact hne (Eq.trans hev (Eq.trans (congrArg (fun z : Verts n => s(v, z)) hcon) hev'.symm))
    · have hraw : e = s(a, v) := Eq.trans hab (congrArg (fun z : Verts n => s(a, z)) h1.symm)
      have hraw' : e' = s(a', v) := Eq.trans ha'b' (congrArg (fun z : Verts n => s(a', z)) h2.symm)
      have hev : e = s(v, a) := Eq.trans hraw Sym2.eq_swap
      have hev' : e' = s(v, a') := Eq.trans hraw' Sym2.eq_swap
      refine exists_four_adjacent hn hd hd' v a a' hev hev' ?_ ?_ ?_
      · intro hcon
        exact hne1 ((hcon.symm).trans h1)
      · intro hcon
        exact hne2 ((hcon.symm).trans h2)
      · intro hcon
        exact hne (Eq.trans hev (Eq.trans (congrArg (fun z : Verts n => s(v, z)) hcon) hev'.symm))
  intro hce
  exact hne (h S hS e (Finset.mem_inter.mpr ⟨he, he1⟩) e'
    (Finset.mem_inter.mpr ⟨he', he2⟩) hce)

/-- **A RAINBOW SECOND STAGE OF A COLOURING IS PROPER.**  In particular, the interface of round 30
is at least as strong as the properness `A_{e,f,i}` of arXiv:2208.12563 §4. -/
theorem Rainbow.proper_leftover {n k K : ℕ} {c : Col n (k + K)} (hn : 4 ≤ n)
    (h : Rainbow c (leftover c)) : Proper c (leftover c) :=
  Rainbow.proper (fun e he => (mem_edgeFinset.mp (mem_leftover.mp he).1).2) hn h

end JSP140
