import JSPProblem.StarColour

/-!
# JSP-000140 — the *whole* second stage of the published construction is deterministic

Round 33 (`StarColour.lean`) removed the first of the two residual bad events of the second stage
(`B_D` = a two-coloured 4-cycle of leftover edges) and left the second one,

    `C_{D,i}` — two *crossing* leftover edges of equal fresh colour above a phase-1 monochromatic
    complementary pair,

as "not handleable by any greedy rule, because it constrains *disjoint* pairs of leftover edges",
with the symmetric Lovász Local Lemma of arXiv:2208.12563 §4 = arXiv:2207.02920 §12 as the
remaining tool.  **That diagnosis is quantitative, and this file corrects it.**

The greedy rule does not care whether the two constrained edges meet or not — what it needs is a
*bound* on the number of partners each edge has:

* `greedy_of_boundedRel` — the general engine: for **any** symmetric relation `R` on a finite set
  `F` in which every element is `R`-related to at most `M` others, there is a map `g : F → Fin (M+1)`
  which is injective on every `R`-related pair of *distinct* elements.  No probability and no
  ordering assumption: the elements are processed by `Finset.induction_on` and each new element
  avoids the colours of the at most `M` already-coloured elements it is related to.  Round 31's
  `rainbow_of_sparse_leftover` is the instance `R = Shares`, `M = 2D`; round 33's `star_greedy` is
  the instance `R = Shares ∨ Sep`, `M = 2D² + 2D`;
* `Cross c₀ L e f` — the crossing relation of the bad event `C_{D,i}`: two crossing leftover edges
  whose complementary pair is covered and phase-1 monochromatic.  `Cross.symm` makes it a symmetric
  relation, `ne_of_Cross` and `noCrossFresh_of_inj` show that a fresh colouring injective on `Cross`
  pairs **cannot** produce the bad event at all (a strictly stronger statement than `NoCrossFresh`);
* `crossF`, `card_crossF_le` — **at most `4n` leftover edges cross a given one over a phase-1
  monochromatic pair**: a partner of `e = s(a,c)` is `s(b,d)` with `c₀ s(a,d) = c₀ s(b,c)` (or the
  same statement for the other complementary pairing), so for each of the `≤ n` choices of `b` there
  are at most two choices of `d`, by the *colour-degree bound of the first stage* (`Tile`, i.e. round
  29's `tile_of_tri`; for an admissible colouring this is `Cherry`'s `5/6` count).  This bound uses
  no hypothesis at all, and is superseded by the next one;
* `CrossPairs`, `CrossThin`, `card_crossF_le_of_thin` — the *usable* bound.  What the probabilistic
  analysis of the first stage has to deliver is a **counting statement about its own output**
  ("at most `T` pairs of crossing leftover edges have a monochromatic complement"), and
  `card_crossF_le_of_thin` turns such a *total* bound — the shape a first-moment argument produces —
  into the *per-edge* bound the greedy engine consumes;
* `FreshRel` = `Shares ∨ Sep ∨ Cross`, `card_freshRel_le` (`2D² + 2D + T`), `cross_greedy_extend`,
  **`second_stage_of_cross`** — the complete second stage: `Proper` (event `A_{e,f,i}` = `B₁`),
  `NoAltCycle` (event `B_D` = `B₂`) and `NoCrossFresh` (event `C_{D,i}` = `B₃`) hold simultaneously
  with `2D² + 2D + T + 1` fresh colours, given only that the leftover has maximum degree `D` and at
  most `T` crossing pairs;
* `admissible_of_cross`, `CrossStageFamily`, `SlackFamily.of_cross`,
  `jsp_000140_main_of_cross_stage_family` — the required theorem `jsp_000140_main` reduced to the
  published construction with **no probabilistic object whatsoever in the second stage**;
  `CrossThin.mono` and `second_stage_of_cross_wide` record that the fresh-colour cost is monotone
  in the crossing count, so a first stage with *no* crossing pair at all reproduces exactly the
  `2D² + 2D + 1` fresh colours of round 33.

**What is left.**  Exactly one probabilistic ingredient, the hypergraph matching of the first stage
(arXiv:2208.12563 §4, Thm 4.2) together with the two density statements about *its own output* that
its analysis delivers: maximum degree `D = n^{1-δ}` (JM (IV), BCDP Claim 4) and the crossing-pair
count `T`.  Both are first-moment statements about a random object; neither needs conditional
probability, entropy or a local lemma.  The second stage of both papers is thereby reduced to a
greedy colouring, and the Lovász Local Lemma is no longer needed at all in this development.
-/

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace JSP140

attribute [local instance] Classical.propDecidable

variable {n k : ℕ}

/-! ### 1. A general greedy engine for bounded-degree relations -/

/-- **A COLOUR AVAILABLE FOR ONE MORE ELEMENT.**  Fewer than `K` colours are used on `N`, so some
colour of the `K` available ones is not used on `N`. -/
private theorem exists_free_colour {α : Type*} [DecidableEq α] {K : ℕ} {s : Finset α}
    (g : ∀ e, e ∈ s → Fin K) (N : Finset α) (hsub : N ⊆ s) (hN : N.card < K) :
    ∃ j : Fin K, ∀ (f : α) (hf : f ∈ N), g f (hsub hf) ≠ j := by
  set U : Finset (Fin K) := N.attach.image
    (fun z : {f : α // f ∈ N} => g z.1 (hsub z.2)) with hU
  have h1 : U.card ≤ N.attach.card := by rw [hU]; exact Finset.card_image_le
  have h1' : N.attach.card = N.card := Finset.card_attach
  have h2 : U.card < (Finset.univ : Finset (Fin K)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨j, hj⟩ := Finset.sdiff_nonempty_of_card_lt_card h2
  have hnotU : j ∉ U := (Finset.mem_sdiff.mp hj).2
  refine ⟨j, fun f hf hcon => ?_⟩
  have hmemU : g f (hsub hf) ∈ U := by
    rw [hU]
    exact Finset.mem_image.mpr ⟨⟨f, hf⟩, Finset.mem_attach N ⟨f, hf⟩, rfl⟩
  exact hnotU (hcon ▸ hmemU)

/-- **THE GREEDY COLOURING OF A BOUNDED-DEGREE RELATION.**  Let `R` be a symmetric relation on a
finite set `F` such that every `e ∈ F` is `R`-related to at most `M` members of `F`.  Then there is
a map `g : F → Fin (M + 1)` which is **injective on every `R`-related pair of distinct elements**.

This is the whole engine behind rounds 31 and 33, abstracted.  Proof: the elements are added one at
a time (`Finset.induction_on`), and each new element takes a colour which none of the at most `M`
already-coloured elements related to it uses. -/
theorem greedy_of_boundedRel {α : Type*} [DecidableEq α] {F : Finset α} {R : α → α → Prop}
    {M : ℕ} (hdeg : ∀ e, e ∈ F → (F.filter (fun f => R e f)).card ≤ M)
    (hsym : ∀ {x y : α}, R x y → R y x) :
    ∃ g : F → Fin (M + 1), ∀ (x y : {e : α // e ∈ F}), x ≠ y → R x.1 y.1 → g x ≠ g y := by
  have key : ∀ (t : Finset α), t ⊆ F →
      (∀ e, e ∈ t → (t.filter (fun f => R e f)).card ≤ M) →
      ∃ g : α → Fin (M + 1), ∀ e f : α, e ∈ t → f ∈ t → e ≠ f → R e f → g e ≠ g f := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
        exact fun _ _ => ⟨fun _ => ⟨0, by omega⟩,
          fun e f he hf hne hrel => absurd he (by simp)⟩
    | @insert a s ha ih =>
      intro hts hdeg'
      have hdeg'' : ∀ e, e ∈ s → (s.filter (fun f => R e f)).card ≤ M := by
        intro e he
        refine le_trans (Finset.card_le_card ?_) (hdeg' e (Finset.mem_insert.mpr (Or.inr he)))
        intro f hf
        have hf' := Finset.mem_filter.mp hf
        exact Finset.mem_filter.mpr ⟨Finset.mem_insert.mpr (Or.inr hf'.1), hf'.2⟩
      obtain ⟨g₀, hg₀⟩ := ih (Finset.Subset.trans (Finset.subset_insert a s) hts) hdeg''
      have hNcard : (s.filter (fun f => R f a)).card ≤ M := by
        refine le_trans (Finset.card_le_card ?_) (hdeg' a (Finset.mem_insert_self a s))
        intro f hf
        have hf' := Finset.mem_filter.mp hf
        exact Finset.mem_filter.mpr ⟨Finset.mem_insert.mpr (Or.inr hf'.1), hsym hf'.2⟩
      have hcard : (s.filter (fun f => R f a)).card < M + 1 := by have := hNcard; omega
      obtain ⟨j, hj⟩ := exists_free_colour (fun e _ => g₀ e)
        (s.filter (fun f => R f a)) (Finset.filter_subset _ _) hcard
      let gfun : α → Fin (M + 1) := fun e => if h : e = a then j else g₀ e
      refine ⟨gfun, fun e f he hf hne hrel => ?_⟩
      by_cases h1 : e = a
      · have h2 : f ≠ a := fun hh => hne (hh ▸ h1)
        have hfs : f ∈ s := by
          rcases Finset.mem_insert.mp hf with h | h
          · exact absurd h h2
          · exact h
        simp only [gfun, dite_eq_left h1, dite_eq_right h2]
        intro hcon
        refine hj f ?_ hcon.symm
        refine Finset.mem_filter.mpr ⟨hfs, hsym (h1 ▸ hrel)⟩
      · have h3 : e ∈ s := by
          rcases Finset.mem_insert.mp he with h | h
          · exact absurd h h1
          · exact h
        by_cases h2 : f = a
        · simp only [gfun, dite_eq_right h1, dite_eq_left h2]
          refine hj e ?_
          exact Finset.mem_filter.mpr ⟨h3, (h2 ▸ hrel)⟩
        · have h4 : f ∈ s := by
            rcases Finset.mem_insert.mp hf with h | h
            · exact absurd h h2
            · exact h
          simp only [gfun, dite_eq_right h1, dite_eq_right h2]
          exact hg₀ e f h3 h4 hne hrel
  obtain ⟨g, hg⟩ := key F (Finset.Subset.refl _) hdeg
  refine ⟨fun e => g e.1, fun x y hxy hrel => ?_⟩
  exact hg x.1 y.1 x.2 y.2 (fun h => hxy (Subtype.ext h)) hrel

/-! ### 2. The crossing relation of the bad event `C_{D,i}` -/

/-- **TWO LEFTOVER EDGES CROSSING OVER A PHASE-1 MONOCHROMATIC PAIR.**  `Cross c₀ L e f` holds when
`e = s(a,c)` and `f = s(b,d)` are the two *crossing* (diagonal) leftover edges of a four-set with
four distinct vertices, the two *complementary* edges `s(a,d)` and `s(b,c)` are **not** leftover —
hence covered, so the extension agrees with the first stage on them — and those two complementary
edges are **monochromatic in phase 1**.

A fresh colouring injective on the `Cross` pairs makes the bad event `C_{D,i}` of arXiv:2208.12563 §4
(= `B₃` of arXiv:2207.02920 §12) impossible: the two uncoloured edges of a `C_{D,i}` are exactly a
`Cross` pair. -/
def Cross {n k : ℕ} (c₀ : Col n k) (L : Finset (Sym2 (Verts n))) (e f : Sym2 (Verts n)) : Prop :=
  ∃ (a c b d : Verts n), FourDistinct a c b d ∧ e = s(a, c) ∧ f = s(b, d) ∧
    s(a, d) ∉ L ∧ s(b, c) ∉ L ∧ c₀ s(a, d) = c₀ s(b, c)

/-- **`Cross` is symmetric**: the two crossing edges of a 4-set may be exchanged, and the
complementary pair is unchanged. -/
theorem Cross.symm {n k : ℕ} {c₀ : Col n k} {L : Finset (Sym2 (Verts n))}
    {e f : Sym2 (Verts n)} (h : Cross c₀ L e f) : Cross c₀ L f e := by
  obtain ⟨a, c, b, d, h4, he, hf, h1, h2, h3⟩ := h
  exact ⟨b, d, a, c, ⟨h4.2.2.2.2.2, h4.2.1.symm, h4.2.2.2.1.symm, h4.2.2.1.symm,
    h4.2.2.2.2.1.symm, h4.1⟩, hf, he, h2, h1, h3.symm⟩

/-- **TWO CROSSING EDGES OF A `Cross` WITNESS ARE DISTINCT.** -/
theorem ne_of_Cross {n k : ℕ} {c₀ : Col n k} {L : Finset (Sym2 (Verts n))}
    {e f : Sym2 (Verts n)} (h : Cross c₀ L e f) : e ≠ f := by
  obtain ⟨a, c, b, d, h4, he, hf, h1, h2, h3⟩ := h
  intro hcon
  have hEq : s(a, c) = s(b, d) := he.symm.trans (hcon.trans hf)
  rcases sym2_inj hEq with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exact absurd e1 h4.2.1
  · exact absurd e1 h4.2.2.1

/-- **NO BAD EVENT `C_{D,i}` FOR A FRESH COLOURING INJECTIVE ON THE CROSSING PAIRS.**  Injectivity on
`Cross` pairs implies `NoCrossFresh`, and the implication is strict in form: `NoCrossFresh` only asks
for distinctness when the complementary pair is phase-1 monochromatic, injectivity asks for it
always. -/
theorem noCrossFresh_of_inj {n k K : ℕ} {c₀ : Col n k} {L : Finset (Sym2 (Verts n))}
    (c : Col n (k + K))
    (h : ∀ e f : Sym2 (Verts n), e ∈ L → f ∈ L → Cross c₀ L e f → c e ≠ c f) :
    NoCrossFresh c₀ c L := by
  intro a b p q h4 h1 h2 hc h3 h4' hc0
  have hpb : s(b, p) = s(p, b) := Sym2.eq_swap
  have hcf : Cross c₀ L s(a, b) s(p, q) :=
    ⟨a, b, p, q, h4, rfl, rfl, h3, hpb ▸ h4', hpb ▸ hc0⟩
  exact absurd hc (h s(a, b) s(p, q) h1 h2 hcf)

/-! ### 3. Counting: at most `4n` crossing leftover edges per leftover edge -/

/-- **THE LEFTOVER EDGES CROSSING `e` OVER A PHASE-1 MONOCHROMATIC PAIR.** -/
noncomputable def crossF {n k : ℕ} (c₀ : Col n k) (L : Finset (Sym2 (Verts n)))
    (e : Sym2 (Verts n)) : Finset (Sym2 (Verts n)) :=
  L.filter (fun f => Cross c₀ L e f)

theorem mem_crossF {n k : ℕ} {c₀ : Col n k} {L : Finset (Sym2 (Verts n))}
    {e f : Sym2 (Verts n)} : f ∈ crossF c₀ L e ↔ f ∈ L ∧ Cross c₀ L e f := Finset.mem_filter

/-- **A VERTEX IS IN AN EDGE IFF IT IS ONE OF ITS TWO ENDPOINTS.** -/
private theorem mem_s_iff {n : ℕ} (x a b : Verts n) : x ∈ s(a, b) ↔ x = a ∨ x = b := by simp

/-- **A VERTEX WHICH IS NEITHER ENDPOINT OF AN EDGE IS NOT IN IT.** -/
private theorem not_mem_s {n : ℕ} {x a b : Verts n} (h1 : x ≠ a) (h2 : x ≠ b) :
    x ∉ s(a, b) := by
  rw [mem_s_iff]
  tauto

/-- **AT MOST TWO NEIGHBOURS OF `a` IN ONE PHASE-1 COLOUR.**  This is the colour-degree bound of the
first stage, `Tile`; for an admissible colouring it is `Cherry`'s counting lemma. -/
private theorem card_colour_le_two {n k : ℕ} {c₀ : Col n k} (hT : Tile c₀) (a : Verts n)
    (j : Fin k) :
    ((Finset.univ : Finset (Verts n)).filter (fun d => d ≠ a ∧ c₀ s(a, d) = j)).card ≤ 2 := by
  have hsub : ((Finset.univ : Finset (Verts n)).filter (fun d => d ≠ a ∧ c₀ s(a, d) = j))
      ⊆ Nbrs c₀ j a := by
    intro d hd
    have hd' := Finset.mem_filter.mp hd
    rw [mem_Nbrs]
    exact hd'.2
  exact le_trans (Finset.card_le_card hsub) (hT.nb_le_two j a)

/-- **THE CANDIDATE WITNESSES `d` FOR A GIVEN `b`.**  `d` is a candidate when the four vertices are
distinct, `s(b,d)` is leftover and the complementary pair is covered and phase-1 monochromatic.  The
last disjunction covers the two possible complementary pairings of the 4-set: exchanging the two
endpoints of `e` exchanges them, and both occur in the definition of `Cross` (which quantifies over
the decomposition). -/
private noncomputable def witFilt {n k : ℕ} (c₀ : Col n k) (L : Finset (Sym2 (Verts n)))
    (a c b : Verts n) : Finset (Verts n) :=
  (Finset.univ : Finset (Verts n)).filter (fun d =>
    d ∉ s(a, c) ∧ b ∉ s(a, c) ∧ b ≠ d ∧ s(b, d) ∈ L ∧
      ((s(a, d) ∉ L ∧ s(b, c) ∉ L ∧ c₀ s(a, d) = c₀ s(b, c)) ∨
       (s(a, b) ∉ L ∧ s(c, d) ∉ L ∧ c₀ s(a, b) = c₀ s(c, d))))

/-- **THE WITNESSES THAT `s(b, d)` CROSSES `s(a, c)` OVER A PHASE-1 MONOCHROMATIC PAIR.** -/
private noncomputable def crossWit {n k : ℕ} (c₀ : Col n k) (L : Finset (Sym2 (Verts n)))
    (a c : Verts n) : Finset (Verts n × Verts n) :=
  (Finset.univ : Finset (Verts n)).biUnion fun b => (witFilt c₀ L a c b).image (fun d => (b, d))

/-- **AT MOST `4n` WITNESSES PER EDGE.**  For each of the `n` choices of `b` there are at most two
choices of `d` making `c₀ s(a,d) = c₀ s(b,c)`, and at most two making `c₀ s(c,d) = c₀ s(a,b)`, by
the phase-1 colour-degree bound. -/
private theorem card_crossWit_le {n k : ℕ} {c₀ : Col n k} (hT : Tile c₀)
    (L : Finset (Sym2 (Verts n))) (a c : Verts n) : (crossWit c₀ L a c).card ≤ 4 * n := by
  have hsub : ∀ b d : Verts n, d ∈ witFilt c₀ L a c b →
      (d ∈ (Finset.univ : Finset (Verts n)) ∧ (d ≠ a ∧ c₀ s(a, d) = c₀ s(b, c)))
        ∨ (d ∈ (Finset.univ : Finset (Verts n)) ∧ (d ≠ c ∧ c₀ s(c, d) = c₀ s(a, b))) := by
    intro b d hd
    have hd' := Finset.mem_filter.mp hd
    have hne : d ≠ a := fun hda => hd'.2.1 ((mem_s_iff d a c).2 (Or.inl hda))
    have hne' : d ≠ c := fun hdc => hd'.2.1 ((mem_s_iff d a c).2 (Or.inr hdc))
    rcases hd'.2.2.2.2.2 with hd'' | hd''
    · exact Or.inl ⟨hd'.1, hne, hd''.2.2⟩
    · exact Or.inr ⟨hd'.1, hne', hd''.2.2.symm⟩
  have h4 : ∀ b : Verts n, (witFilt c₀ L a c b).card ≤ 4 := by
    intro b
    have hsub' : witFilt c₀ L a c b ⊆
        (Finset.univ : Finset (Verts n)).filter (fun d => d ≠ a ∧ c₀ s(a, d) = c₀ s(b, c)) ∪
        (Finset.univ : Finset (Verts n)).filter (fun d => d ≠ c ∧ c₀ s(c, d) = c₀ s(a, b)) := by
      intro d hd
      have hd' := Finset.mem_filter.mp hd
      have hne : d ≠ a := fun hda => hd'.2.1 ((mem_s_iff d a c).2 (Or.inl hda))
      have hne' : d ≠ c := fun hdc => hd'.2.1 ((mem_s_iff d a c).2 (Or.inr hdc))
      simp only [Finset.mem_filter, Finset.mem_union]
      rcases hd'.2.2.2.2.2 with hd'' | hd''
      · exact Or.inl ⟨hd'.1, hne, hd''.2.2⟩
      · exact Or.inr ⟨hd'.1, hne', hd''.2.2.symm⟩
    have hU : ((Finset.univ : Finset (Verts n)).filter
          (fun d => d ≠ a ∧ c₀ s(a, d) = c₀ s(b, c)) ∪
        (Finset.univ : Finset (Verts n)).filter
          (fun d => d ≠ c ∧ c₀ s(c, d) = c₀ s(a, b))).card ≤ 4 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      have hX := card_colour_le_two hT a (c₀ s(b, c))
      have hY := card_colour_le_two hT c (c₀ s(a, b))
      omega
    exact le_trans (Finset.card_le_card hsub') hU
  rw [crossWit]
  refine le_trans (Finset.card_biUnion_le_card_mul _ _ 4 ?_) ?_
  · intro b _
    exact le_trans (Finset.card_image_le) (h4 b)
  · rw [Finset.card_univ, Fintype.card_fin, Nat.mul_comm]

/-- **EVERY CROSSING LEFTOVER EDGE IS CAUGHT BY THE WITNESSES.**  There are two cases, according to
which endpoint of `e = s(x,y)` is the `a` of the `Cross` witness; they exchange the two possible
complementary pairings of the four-set, which is why `witFilt` carries a disjunction. -/
private theorem mem_crossWit {n k : ℕ} {c₀ : Col n k} {L : Finset (Sym2 (Verts n))}
    {x y : Verts n} {f : Sym2 (Verts n)} (h : f ∈ crossF c₀ L s(x, y)) :
    f ∈ (crossWit c₀ L x y).image (fun t => s(t.1, t.2)) := by
  obtain ⟨hL, hc⟩ := (mem_crossF (e := s(x, y)) (f := f)).mp h
  obtain ⟨a, c, b, d, h4, he, hf, h1, h2, h3⟩ := hc
  have hbc : s(b, c) = s(c, b) := Sym2.eq_swap
  refine Finset.mem_image.mpr ⟨(b, d), ?_, hf.symm⟩
  rw [crossWit]
  refine Finset.mem_biUnion.mpr ⟨b, Finset.mem_univ _, ?_⟩
  refine Finset.mem_image.mpr ⟨d, ?_, rfl⟩
  simp only [witFilt, Finset.mem_filter]
  rcases sym2_inj he with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rw [e1, e2]
    exact ⟨Finset.mem_univ _, ⟨not_mem_s h4.2.2.1.symm h4.2.2.2.2.1.symm,
      not_mem_s h4.2.1.symm h4.2.2.2.1.symm, h4.2.2.2.2.2, hf.symm ▸ hL, Or.inl ⟨h1, h2, h3⟩⟩⟩
  · rw [e1, e2]
    exact ⟨Finset.mem_univ _, ⟨not_mem_s h4.2.2.2.2.1.symm h4.2.2.1.symm,
      not_mem_s h4.2.2.2.1.symm h4.2.1.symm, h4.2.2.2.2.2, hf.symm ▸ hL,
      Or.inr ⟨hbc ▸ h2, h1, (hbc ▸ h3).symm⟩⟩⟩

/-- **AT MOST `4n` LEFTOVER EDGES CROSS A GIVEN LEFTOVER EDGE OVER A PHASE-1 MONOCHROMATIC PAIR.**

This is the **unconditional** bound: a partner of `e = s(a,c)` is `s(b,d)` with
`c₀ s(a,d) = c₀ s(b,c)` (or the same statement for the other complementary pairing), and the first
stage's colour-degree bound gives at most two such `d` for each of the `n` choices of `b`.  It uses
no hypothesis, not even sparsity of the leftover graph, and is superseded by `CrossThin`. -/
theorem card_crossF_le {n k : ℕ} {c₀ : Col n k} (hT : Tile c₀)
    (L : Finset (Sym2 (Verts n))) (e : Sym2 (Verts n)) : (crossF c₀ L e).card ≤ 4 * n := by
  obtain ⟨a, c, h⟩ : ∃ a c : Verts n, e = s(a, c) :=
    Quot.inductionOn e (fun p : Verts n × Verts n => ⟨p.1, p.2, rfl⟩)
  have h1 : (crossF c₀ L e).card ≤ ((crossWit c₀ L a c).image (fun t => s(t.1, t.2))).card :=
    Finset.card_le_card (by
      intro f hf
      rw [h] at hf
      exact mem_crossWit (x := a) (y := c) (f := f) hf)
  exact le_trans h1 (le_trans (Finset.card_image_le) (card_crossWit_le hT L a c))

/-! ### 4. The usable bound: a first-moment statement about the first stage -/

/-- **THE NUMBER OF CROSSING LEFTOVER PAIRS OVER A PHASE-1 MONOCHROMATIC PAIR**, counted over the
leftover.  This is the quantity a first-moment argument about the first stage bounds: the
expectation of `CrossPairs c₀ L` counts 4-sets in which two crossing edges are uncoloured and the
complementary pair is phase-1 monochromatic. -/
noncomputable def CrossPairs {n k : ℕ} (c₀ : Col n k) (L : Finset (Sym2 (Verts n))) : ℕ :=
  ∑ e ∈ L, (crossF c₀ L e).card

/-- **SPARSE CROSSING PAIRS.**  At most `T` pairs of crossing leftover edges have a phase-1
monochromatic complementary pair.  This is the *second* density property the first stage has to
deliver, alongside `SparseL` (`D = n^{1-δ}`, JM (IV) / BCDP Claim 4). -/
def CrossThin {n k : ℕ} (c₀ : Col n k) (L : Finset (Sym2 (Verts n))) (T : ℕ) : Prop :=
  CrossPairs c₀ L ≤ T

/-- **THE PER-EDGE BOUND FOLLOWS FROM THE TOTAL ONE.**  A bound on the *number* of crossing pairs —
the shape a first-moment argument produces — suffices for the greedy engine, which needs it edge by
edge. -/
theorem card_crossF_le_of_thin {n k : ℕ} {c₀ : Col n k} {L : Finset (Sym2 (Verts n))}
    (hT : CrossThin c₀ L T) (e : Sym2 (Verts n)) (he : e ∈ L) : (crossF c₀ L e).card ≤ T := by
  have hsum : (∑ e' ∈ L, (crossF c₀ L e').card) ≤ T := by
    simpa only [CrossThin, CrossPairs] using hT
  exact le_trans
    (Finset.single_le_sum (fun i _ => Nat.zero_le ((crossF c₀ L i).card)) he) hsum

/-! ### 5. The whole second stage, deterministically -/

/-- **THE RELATION WHICH THE FRESH COLOURING MUST AVOID**: the leftover edges meeting `e`
(properness, event `A_{e,f,i}` = `B₁`), those separated from `e` (event `B_D` = `B₂`) and those
crossing `e` over a phase-1 monochromatic pair (event `C_{D,i}` = `B₃`). -/
def FreshRel {n k : ℕ} (c₀ : Col n k) (L : Finset (Sym2 (Verts n)))
    (e f : Sym2 (Verts n)) : Prop :=
  Shares e f ∨ Sep L e f ∨ Cross c₀ L e f

/-- **`FreshRel` is symmetric.** -/
theorem FreshRel.symm {n k : ℕ} {c₀ : Col n k} {L : Finset (Sym2 (Verts n))} :
    ∀ {e f : Sym2 (Verts n)}, FreshRel c₀ L e f → FreshRel c₀ L f e := by
  intro e f h
  rcases h with h | h | h
  · exact Or.inl h.symm
  · exact Or.inr (Or.inl h.symm)
  · exact Or.inr (Or.inr h.symm)

/-- **AT MOST `2D² + 2D + T` LEFTOVER EDGES ARE `FreshRel`-RELATED TO A GIVEN ONE**: `2D` meet it,
`2D²` are separated from it (`StarColour.card_sepF_le`) and `T` cross it over a phase-1 monochromatic
pair (`card_crossF_le_of_thin`). -/
theorem card_freshRel_le {n k D T : ℕ} {c₀ : Col n k} {L : Finset (Sym2 (Verts n))}
    (hD : SparseL L D) (hThin : CrossThin c₀ L T) (e : Sym2 (Verts n)) (he : e ∈ L) :
    (L.filter (fun f => FreshRel c₀ L f e)).card ≤ 2 * D * D + 2 * D + T := by
  obtain ⟨a, c, h⟩ : ∃ a c : Verts n, e = s(a, c) :=
    Quot.inductionOn e (fun p : Verts n × Verts n => ⟨p.1, p.2, rfl⟩)
  have hsub : (L.filter (fun f => FreshRel c₀ L f e)) ⊆
      (L.filter (fun f => Shares f e)) ∪ (L.filter (fun f => Sep L f e)) ∪
        (L.filter (fun f => Cross c₀ L f e)) := by
    intro f hf
    have hf' := Finset.mem_filter.mp hf
    simp only [Finset.mem_filter, Finset.mem_union]
    rcases hf'.2 with hsh | hsh | hcr
    · exact Or.inl (Or.inl ⟨hf'.1, hsh⟩)
    · exact Or.inl (Or.inr ⟨hf'.1, hsh⟩)
    · exact Or.inr ⟨hf'.1, hcr⟩
  have hcA : (L.filter (fun f => Shares f e)).card ≤ 2 * D := by
    have h2 : (L.filter (fun f => Shares f s(a, c))).card ≤ 2 * D := card_shares_le hD a c
    rw [← h] at h2
    exact h2
  have hcB : (L.filter (fun f => Sep L f e)).card ≤ 2 * D * D := by
    refine le_trans (Finset.card_le_card ?_) (card_sepF_le hD e)
    intro f hf
    have hf' := Finset.mem_filter.mp hf
    exact mem_sepF hf'.1 (Sep.symm hf'.2)
  have hcC : (L.filter (fun f => Cross c₀ L f e)).card ≤ T := by
    refine le_trans (Finset.card_le_card ?_) (card_crossF_le_of_thin hThin e he)
    intro f hf
    have hf' := Finset.mem_filter.mp hf
    exact mem_crossF.mpr ⟨hf'.1, Cross.symm hf'.2⟩
  have hAB : ((L.filter (fun f => Shares f e)) ∪ (L.filter (fun f => Sep L f e))).card
      ≤ 2 * D * D + 2 * D := by
    refine le_trans (Finset.card_union_le _ _) ?_
    have := Nat.add_le_add hcA hcB
    omega
  have hcard : ((L.filter (fun f => Shares f e)) ∪ (L.filter (fun f => Sep L f e)) ∪
      (L.filter (fun f => Cross c₀ L f e))).card ≤ 2 * D * D + 2 * D + T := by
    refine le_trans (Finset.card_union_le _ _) ?_
    have := Nat.add_le_add hAB hcC
    omega
  exact le_trans (Finset.card_le_card hsub) hcard

/-- **THE GREEDY CROSSING COLOURING OF THE LEFTOVER GRAPH, AS AN EXTENSION.**  A leftover graph of
maximum degree `D` with at most `T` crossing pairs over a phase-1 monochromatic pair carries a fresh
colouring with `2D² + 2D + T + 1` colours which is **proper**, **injective on the separated pairs**
(so `B_D` is absent) and **injective on the crossing pairs** (so `C_{D,i}` is absent).  No probability
is involved. -/
theorem cross_greedy_extend {n k D T : ℕ} {c₀ : Col n k} {L : Finset (Sym2 (Verts n))}
    (hD : SparseL L D) (hThin : CrossThin c₀ L T) :
    ∃ (g : ∀ e, e ∈ L → Fin (2 * D * D + 2 * D + T + 1)),
      Proper (extendColDep c₀ L g) L ∧
        (∀ e f : Sym2 (Verts n), e ∈ L → f ∈ L → Sep L e f →
          (extendColDep c₀ L g) e ≠ (extendColDep c₀ L g) f) ∧
        (∀ e f : Sym2 (Verts n), e ∈ L → f ∈ L → Cross c₀ L e f →
          (extendColDep c₀ L g) e ≠ (extendColDep c₀ L g) f) := by
  obtain ⟨ĝ, hĝ⟩ := greedy_of_boundedRel (F := L) (R := FreshRel c₀ L) (M := 2 * D * D + 2 * D + T)
    (fun e he => by
      refine le_trans (Finset.card_le_card ?_) (card_freshRel_le hD hThin e he)
      intro f hf
      have hf' := Finset.mem_filter.mp hf
      exact Finset.mem_filter.mpr ⟨hf'.1, FreshRel.symm hf'.2⟩) FreshRel.symm
  have hRel : ∀ (x y : {e : Sym2 (Verts n) // e ∈ L}), x ≠ y → FreshRel c₀ L x.1 y.1 →
      extendColDep c₀ L (fun e h => ĝ ⟨e, h⟩) x.1 ≠ extendColDep c₀ L (fun e h => ĝ ⟨e, h⟩) y.1 := by
    intro x y hxy hrel
    rw [extendColDep_of_mem x.2, extendColDep_of_mem y.2]
    intro hcon
    apply hĝ x y (fun hv => hxy ((@Subtype.ext_iff _ (fun e => e ∈ L) x y).mpr
      (congrArg Subtype.val hv))) hrel
    apply Fin.ext
    exact congrArg Fin.val (freshCol_inj _ _ hcon)
  refine ⟨fun e h => ĝ ⟨e, h⟩, ?_, ?_, ?_⟩
  · intro e he e' he' hne hsh
    exact hRel ⟨e, he⟩ ⟨e', he'⟩ (fun hv => hne (congrArg Subtype.val hv)) (Or.inl hsh)
  · intro e f he hf hsep
    exact hRel ⟨e, he⟩ ⟨f, hf⟩ (fun hv => ne_of_Sep hsep (congrArg Subtype.val hv))
      (Or.inr (Or.inl hsep))
  · intro e f he hf hcr
    exact hRel ⟨e, he⟩ ⟨f, hf⟩ (fun hv => ne_of_Cross hcr (congrArg Subtype.val hv))
      (Or.inr (Or.inr hcr))

/-- **THE COMPLETE SECOND STAGE, DETERMINISTICALLY.**  Given only the two density properties of the
leftover graph — maximum degree `D` and at most `T` crossing pairs over a phase-1 monochromatic
pair — the second stage of arXiv:2208.12563 §4 exists with `2D² + 2D + T + 1` fresh colours and
satisfies **all three** published conditions: `Proper` (`A_{e,f,i}` = `B₁`), `NoAltCycle`
(`B_D` = `B₂`) and `NoCrossFresh` (`C_{D,i}` = `B₃`).

So the symmetric Lovász Local Lemma is not needed anywhere in the second stage. -/
theorem second_stage_of_cross {n k D T : ℕ} {c₀ : Col n k} {L : Finset (Sym2 (Verts n))}
    (hD : SparseL L D) (hT : Tile c₀) (hThin : CrossThin c₀ L T) :
    ∃ (g : ∀ e, e ∈ L → Fin (2 * D * D + 2 * D + T + 1)),
      Proper (extendColDep c₀ L g) L ∧ NoAltCycle (extendColDep c₀ L g) L ∧
        NoCrossFresh c₀ (extendColDep c₀ L g) L := by
  obtain ⟨g, hPr, hS, hX⟩ := cross_greedy_extend hD hThin
  exact ⟨g, hPr, noAltCycle_of_starProper ⟨hPr, hS⟩, noCrossFresh_of_inj _ hX⟩

/-- **THE VERIFICATION LEMMA WITH ALL THREE BAD EVENTS HANDLED DETERMINISTICALLY.** -/
theorem admissible_of_cross {n k K : ℕ} {c₀ : Col n k} {c : Col n (k + K)}
    {L : Finset (Sym2 (Verts n))} (hE : Extends (liftCol c₀ (Nat.le_add_right k K)) c L)
    (hP : Proper c L)
    (hS : ∀ e f : Sym2 (Verts n), e ∈ L → f ∈ L → Sep L e f → c e ≠ c f)
    (hX : ∀ e f : Sym2 (Verts n), e ∈ L → f ∈ L → Cross c₀ L e f → c e ≠ c f)
    (hD₀ : Design c₀) (hLC : LeafClosed c₀ L) (hn : 4 ≤ n) : Admissible c :=
  admissible_of_star hE hP hS hD₀ hLC (noCrossFresh_of_inj c hX) hn

/-! ### 6. The required theorem: a purely deterministic second stage -/

/-- **THE PUBLISHED CONSTRUCTION WITH A FULLY DETERMINISTIC SECOND STAGE.**  For every `δ > 0` and
all large `m ≡ 1 (mod 6)`: a first-stage `k`-colouring `c₀` (a labelled-triangle system with disjoint
`(vertex, colour)` usage, no bad and no crossing four-set) whose leftover graph has maximum degree
`D` and at most `T` crossing pairs over a phase-1 monochromatic pair, bringing the total number of
colours to at most `5(m-1)/6 + δm/6`.

Nothing probabilistic is assumed about the second stage: `second_stage_of_cross` builds it.  The only
probabilistic object left in the development is the first stage together with the two density
statements about its output (`SparseL` and `CrossThin`). -/
def CrossStageFamily : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ M D T : ℕ, ∀ m : ℕ, M ≤ m → m % 6 = 1 →
    ∃ (k : ℕ) (c₀ : Col m k),
      Covers c₀ ∧ PairFree c₀ ∧ NoCrossFour c₀ ∧ NoBadFour c₀ ∧
        SparseL (leftover c₀) D ∧ CrossThin c₀ (leftover c₀) T ∧
        (6 : ℝ) * ((k + (2 * D * D + 2 * D + T + 1) : ℕ) : ℝ) ≤ 5 * ((m - 1 : ℕ) : ℝ) + δ * (m : ℝ)

/-- **THE TWO STAGES COMPOSE, WITH NO PROBABILITY IN THE SECOND ONE.** -/
theorem SlackFamily.of_cross (hfam : CrossStageFamily) : SlackFamily := by
  rw [CrossStageFamily] at hfam
  intro δ hδ
  obtain ⟨M, D, T, hM⟩ := hfam δ hδ
  refine ⟨max M 4, fun m hMm hm => ?_⟩
  obtain ⟨k, c₀, hC, hP, hX, hB, hD, hThin, hk⟩ := hM m (Nat.le_trans (Nat.le_max_left _ _) hMm) hm
  have h4m : 4 ≤ m := Nat.le_trans (Nat.le_max_right _ _) hMm
  have hT : Tile c₀ := tile_of_tri hC hP h4m
  have hPk : Packed c₀ := packed_of_tri hC hP h4m
  have hLC : LeafClosed c₀ (leftover c₀) := leafClosed_of_tri hC hP
  obtain ⟨g, hPr, hS, hX'⟩ := cross_greedy_extend hD hThin
  have hE : Extends (liftCol c₀ (Nat.le_add_right k (2 * D * D + 2 * D + T + 1)))
      (extendColDep c₀ (leftover c₀) g) (leftover c₀) :=
    Extends_extendColDep (c := c₀) (L := leftover c₀) (g := g)
  exact ⟨k + (2 * D * D + 2 * D + T + 1), extendColDep c₀ (leftover c₀) g,
    admissible_of_cross hE hPr hS hX' ⟨hT, hPk, hX, hB⟩ hLC h4m, hk⟩

/-- **THE HYPOTHESIS IS MONOTONE IN `T`.** -/
theorem CrossThin.mono {n k T T' : ℕ} {c₀ : Col n k} {L : Finset (Sym2 (Verts n))}
    (h : CrossThin c₀ L T) (hT : T ≤ T') : CrossThin c₀ L T' := by
  rw [CrossThin] at h ⊢
  omega

/-- **THE FRESH-COLOUR COST IS MONOTONE IN THE CROSSING COUNT.**  A first stage whose crossing-pair
count is bounded by `T'` yields the complete second stage with `2D² + 2D + T + 1` fresh colours for
every `T ≥ T'`; in particular, when the first stage has *no* crossing pair at all (`T' = 0`) this is
exactly the `2D² + 2D + 1` fresh colours of round 33. -/
theorem second_stage_of_cross_wide {n k D T T' : ℕ} {c₀ : Col n k} {L : Finset (Sym2 (Verts n))}
    (hD : SparseL L D) (hT : Tile c₀) (hThin : CrossThin c₀ L T') (hT' : T' ≤ T) :
    ∃ (g : ∀ e, e ∈ L → Fin (2 * D * D + 2 * D + T + 1)),
      Proper (extendColDep c₀ L g) L ∧ NoAltCycle (extendColDep c₀ L g) L ∧
        NoCrossFresh c₀ (extendColDep c₀ L g) L := by
  obtain ⟨g, hPr, hS, hX⟩ := cross_greedy_extend hD (CrossThin.mono hThin hT')
  let g' : ∀ e, e ∈ L → Fin (2 * D * D + 2 * D + T + 1) :=
    fun e h => ⟨(g e h).val, by have := (g e h).isLt; omega⟩
  have hval : ∀ (e : Sym2 (Verts n)) (he : e ∈ L), (g' e he).val = (g e he).val := by
    intro e he
    rfl
  have hPr' : Proper (extendColDep c₀ L g') L := by
    intro e he e' he' hne hsh
    rw [extendColDep_of_mem he, extendColDep_of_mem he']
    intro hcon
    refine hPr e he e' he' hne hsh (Fin.ext ?_)
    have h5 := congrArg Fin.val hcon
    simp only [extendColDep_of_mem he, extendColDep_of_mem he', freshCol_val] at h5 ⊢
    have h6 := hval e he
    have h7 := hval e' he'
    omega
  have hS' : ∀ e f : Sym2 (Verts n), e ∈ L → f ∈ L → Sep L e f →
      (extendColDep c₀ L g') e ≠ (extendColDep c₀ L g') f := by
    intro e f he hf hsep
    rw [extendColDep_of_mem he, extendColDep_of_mem hf]
    intro hcon
    refine hS e f he hf hsep (Fin.ext ?_)
    have h5 := congrArg Fin.val hcon
    simp only [extendColDep_of_mem he, extendColDep_of_mem hf, freshCol_val] at h5 ⊢
    have h6 := hval e he
    have h7 := hval f hf
    omega
  have hX' : ∀ e f : Sym2 (Verts n), e ∈ L → f ∈ L → Cross c₀ L e f →
      (extendColDep c₀ L g') e ≠ (extendColDep c₀ L g') f := by
    intro e f he hf hcr
    rw [extendColDep_of_mem he, extendColDep_of_mem hf]
    intro hcon
    refine hX e f he hf hcr (Fin.ext ?_)
    have h5 := congrArg Fin.val hcon
    simp only [extendColDep_of_mem he, extendColDep_of_mem hf, freshCol_val] at h5 ⊢
    have h6 := hval e he
    have h7 := hval f hf
    omega
  exact ⟨g', hPr', noAltCycle_of_starProper ⟨hPr', hS'⟩, noCrossFresh_of_inj _ hX'⟩

/-- **THE REQUIRED THEOREM `jsp_000140_main`, WITH NO PROBABILISTIC OBJECT IN THE SECOND STAGE.** -/
theorem jsp_000140_main_of_cross_stage_family (hfam : CrossStageFamily) : jsp_000140_target :=
  jsp_000140_main_of_slack_family (SlackFamily.of_cross hfam)

end JSP140
