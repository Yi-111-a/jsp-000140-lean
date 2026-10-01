import JSPProblem.Rigidity

/-!
# JSP-000140 — a structural criterion for admissibility: `Admissible c ↔ four local conditions`

Rounds 10–27 of this development established everything about the **lower** half of the catalog
answer `f(n, 4, 5) = 5n/6 + o(n)` and a very detailed description of the structure an **extremal**
colouring must have:

* `Cherry.five_sixth_lower` — `5(n-1) ≤ 6k` for every admissible `k`-colouring of `K_n`;
* `Rigidity.tight_pathFinset_is_STS` — in the extremal case the two-edge paths form a Steiner
  triple system; `Classwise.classwise_tiling_iff_extremal` — extremality is *equivalent* to every
  colour class being a vertex-disjoint union of two-edge paths and isolated single edges
  (`3 a_i + 2 s_i = n`).

All of those are **necessity** statements: they start from an admissible colouring.  What is
missing for the *construction* half of the prize (the upper bound, arXiv:2207.02920) is a
**sufficiency** statement: a criterion saying *when a candidate colouring is admissible*, so that
the candidate produced by a construction can be **verified** without re-checking every
four-vertex clique.  This file provides that, in the strongest provable form:

* `Tile` — **every colour class is a vertex-disjoint union of two-edge paths and isolated single
  edges** (pointwise: colour-degree at most `2`, and a vertex of colour-degree `2` has only
  colour-degree-`1` neighbours).  This is the structure `Rigidity`/`Classwise`/`Local` show an
  extremal admissible colouring has, and `Tile.of_admissible` proves it for *every* admissible
  colouring — so `Tile` is a genuine *weakening* of the catalog condition;
* `Packed` — **the three-element vertex sets of two-edge paths form a linear hypergraph** (the
  packing lemma `Rigidity.pathSet_sub_inter`);
* `NoBadFour` — **no four-vertex clique contains both a two-edge path and two vertex-disjoint
  edges of one colour**;
* `NoCrossFour` — **no four-vertex clique has two vertex-disjoint edges of one colour and two
  vertex-disjoint edges of another colour**.

**THE CRITERION (`design_iff_admissible`):**

    `Admissible c  ↔  Tile c ∧ Packed c ∧ NoCrossFour c ∧ NoBadFour c`.

So "every `K₄` spans at least five colours" is *equivalent* to four conditions which only speak
about colour classes, two-edge paths and four-element vertex sets — all of them local, and all of
them of the same shape as the structure theorems of rounds 13–27.  The machinery:

* `card_classIn_four` — under `Tile`, **every colour meets every `K₄` in at most two edges**;
* `two_of_two` — the refinement: those two edges are either the two edges of a two-edge path
  contained in the clique, or two vertex-disjoint edges;
* `four_of_two_doubled` — conversely, if two colours each meet a `K₄` in two edges, that clique
  spans at most four colours, hence is not admissible;
* `noFourDouble_of_design` — `Tile`, `Packed`, `NoCrossFour` and `NoBadFour` exclude the three
  ways in which two colours can be doubled on one clique (two paths / path + crossing / two
  crossings).

Finally, `jsp_000140_main_of_design_family` reduces the required theorem `jsp_000140_main` to

    `DesignFamily`  —  for every `δ > 0` and all large `m ≡ 1 (mod 6)` there is a colouring of `K_m`
    satisfying the four local conditions above and using at most `5(m-1)/6 + δm/6` colours,

which replaces the hypothesis `Slack.STSFamily` (which speaks of *admissible* colourings) by a
*verifiable* one.  What remains for the prize is then only the construction itself, and the amount
of checking it needs is explicit and local.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace JSP140

variable {n k : ℕ}

/-! ### The four local conditions -/

/-- **THE TILING CONDITION.**  Every colour class of `c` is a vertex-disjoint union of two-edge
paths and isolated single edges; equivalently, pointwise: a vertex has at most two colour-`i`
neighbours, and if it has exactly two then each of them has that vertex as its only colour-`i`
neighbour.

This is the local form of the extremal structure proved in `Rigidity.tight_degree`,
`Classwise.tight_class_vertex_count` (`3 a_i + 2 s_i = n`) and `Local.tight_local_profile`; it is
what `Tile.of_admissible` shows every admissible colouring satisfies. -/
def Tile {n k : ℕ} (c : Col n k) : Prop :=
  ∀ i : Fin k, ∀ v : Verts n, (Nbrs c i v).card ≤ 2 ∧
    ∀ a : Verts n, a ∈ Nbrs c i v → (Nbrs c i v).card = 2 → (Nbrs c i a).card = 1

theorem Tile.nb_le_two {c : Col n k} (hT : Tile c) (i : Fin k) (v : Verts n) :
    (Nbrs c i v).card ≤ 2 :=
  (hT i v).1

theorem Tile.nb_one_of_mem {c : Col n k} (hT : Tile c) {i : Fin k} {v a : Verts n}
    (ha : a ∈ Nbrs c i v) (hv : (Nbrs c i v).card = 2) : (Nbrs c i a).card = 1 :=
  (hT i v).2 a ha hv

/-- **UNDER THE TILING CONDITION A LEAF IS JOINED TO THE CENTRE ONLY.**  If `a ∈ Nbrs c i v` and
`v` is a centre of colour `i`, then `v` is the only colour-`i` neighbour of `a`: the colour-`i`
component of `a` is the isolated single edge `s(v, a)`. -/
theorem Tile.nb_singleton_of_path {c : Col n k} (hT : Tile c) {i : Fin k} {v a : Verts n}
    (ha : a ∈ Nbrs c i v) (hv : (Nbrs c i v).card = 2) : Nbrs c i a = {v} := by
  have h1 : (Nbrs c i a).card = 1 := hT.nb_one_of_mem ha hv
  have hva : a ≠ v := (mem_Nbrs.mp ha).1
  have hvN : v ∈ Nbrs c i a := mem_Nbrs.mpr ⟨hva.symm, c_swap (mem_Nbrs.mp ha).2⟩
  obtain ⟨w, hw⟩ := Finset.card_eq_one.mp h1
  rw [hw] at hvN
  exact hw.trans (by rw [Finset.mem_singleton.mp hvN])

/-- **THE PACKING CONDITION.**  The three-element vertex sets of the two-edge paths of `c` form a
*linear hypergraph*: two of them share at most one vertex, unless they are equal.  This is the
local form of `Rigidity.pathSet_sub_inter`, the lemma which makes the paths of an extremal
colouring a Steiner triple system. -/
def Packed {n k : ℕ} (c : Col n k) : Prop :=
  ∀ i j : Fin k, ∀ v w : Verts n, v ∈ twoA c i → w ∈ twoA c j →
    2 ≤ (pathSet c i v ∩ pathSet c j w).card → i = j

/-- Two **vertex-disjoint** edges of colour `i` inside a vertex set `S`: the two "isolated single
edges" of the tiling condition, side by side. -/
def Crossed {n k : ℕ} (c : Col n k) (i : Fin k) (S : Finset (Verts n)) : Prop :=
  ∃ e e' : Sym2 (Verts n), e ∈ classIn c i S ∧ e' ∈ classIn c i S ∧ e ≠ e' ∧
    ∀ v : Verts n, v ∈ e → v ∉ e'

/-- **NO CROSSING FOUR-SET.**  No four-vertex clique has two vertex-disjoint edges of one colour
*and* two vertex-disjoint edges of another colour: such a clique spans at most four colours. -/
def NoCrossFour {n k : ℕ} (c : Col n k) : Prop :=
  ∀ S : Finset (Verts n), S.card = 4 → ∀ i j : Fin k, i ≠ j → ¬ (Crossed c i S ∧ Crossed c j S)

/-- **NO BAD FOUR-SET.**  No four-vertex clique contains both a two-edge path (a `pathSet`) and two
vertex-disjoint edges of one colour: such a clique spans at most four colours. -/
def NoBadFour {n k : ℕ} (c : Col n k) : Prop :=
  ∀ S : Finset (Verts n), S.card = 4 → ∀ i j : Fin k, i ≠ j →
    ¬ (Crossed c i S ∧ ∃ w : Verts n, w ∈ twoA c j ∧ pathSet c j w ⊆ S)

/-- A colouring is a `Design` if it satisfies the four local conditions. -/
def Design {n k : ℕ} (c : Col n k) : Prop := Tile c ∧ Packed c ∧ NoCrossFour c ∧ NoBadFour c

/-! ### The tiling and packing conditions are implied by admissibility -/

/-- The colour-degree bound, in the language of `Nbrs`. -/
theorem Nbrs_le_two {c : Col n k} (hc : Admissible c) (i : Fin k) (v : Verts n) :
    (Nbrs c i v).card ≤ 2 := by
  simpa [Nbrs] using nb_card_le_two hc i v (Finset.univ : Finset (Verts n))

/-- **EVERY ADMISSIBLE COLOURING IS TILED.**  `Admissible c → Tile c`: every colour class of an
admissible colouring is a vertex-disjoint union of two-edge paths and isolated single edges
(`Counting.nb_card_le_two` gives the degree bound, `Cherry.leaf_not_centre` says that a leaf of a
two-edge path is never a centre of the same colour).

So `Tile` is a genuine **weakening** of the catalog condition: it can be verified *without*
checking four-vertex cliques, and it is exactly the structure the extremal colourings have. -/
theorem Tile.of_admissible {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) : Tile c := by
  intro i v
  refine ⟨Nbrs_le_two hc i v, ?_⟩
  intro a ha hcard2
  have hle : (Nbrs c i a).card ≤ 2 := Nbrs_le_two hc i a
  have hvN : v ∈ Nbrs c i a := mem_Nbrs.mpr
    ⟨Ne.symm (mem_Nbrs.mp ha).1, c_swap (mem_Nbrs.mp ha).2⟩
  have hge : 1 ≤ (Nbrs c i a).card := Finset.card_pos.mpr ⟨v, hvN⟩
  by_cases h1 : (Nbrs c i a).card = 1
  · exact h1
  · have hcard2' : (Nbrs c i a).card = 2 := by omega
    exact (leaf_not_centre hc hn i (Ne.symm (mem_Nbrs.mp ha).1) ha hcard2 hcard2').elim

/-- **EVERY ADMISSIBLE COLOURING IS PACKED.**  `Admissible c → Packed c`, from the packing lemma
`Rigidity.pathSet_sub_inter`. -/
theorem Packed.of_admissible {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) : Packed c := by
  intro i j v w hv hw hinter
  obtain ⟨hij, hvw⟩ := pathSet_sub_inter hc hn hv hw
    (B := pathSet c i v ∩ pathSet c j w)
    (Finset.inter_subset_left (s₁ := pathSet c i v) (s₂ := pathSet c j w))
    (Finset.inter_subset_right (s₁ := pathSet c i v) (s₂ := pathSet c j w))
    hinter
  exact hij

/-! ### Under the tiling condition a colour meets a clique in at most two edges -/

/-- An edge of `edgeFinset S` is a pair of distinct elements of `S`. -/
private lemma exists_mk_of_mem_edgeFinset {n : ℕ} {S : Finset (Verts n)}
    {e : Sym2 (Verts n)} (he : e ∈ edgeFinset S) :
    ∃ a b : Verts n, e = s(a, b) ∧ a ∈ S ∧ b ∈ S ∧ a ≠ b := by
  obtain ⟨a, b, hab⟩ : ∃ a b : Verts n, e = s(a, b) :=
    Quot.inductionOn e (fun p : Verts n × Verts n => ⟨p.1, p.2, rfl⟩)
  obtain ⟨h1, h2⟩ := mem_edgeFinset.mp (hab ▸ he)
  have hmem := Finset.mem_sym2_iff.mp h1
  exact ⟨a, b, hab, hmem a (Sym2.mem_mk_left a b), hmem b (Sym2.mem_mk_right a b), h2 a b rfl⟩

/-- If `a` is in none of the two-element sets `{b, c}` then `b` and `c` differ from `a`. -/
private lemma ne_of_not_mem_pair {α : Type*} [DecidableEq α] {a b c : α}
    (h : a ∉ ({b, c} : Finset α)) : b ≠ a ∧ c ≠ a := by
  refine ⟨fun h1 => ?_, fun h1 => ?_⟩
  · rw [h1] at h
    simpa using h
  · rw [h1] at h
    simpa using h

/-- Membership in a two-element finset. -/
private lemma mem_pair {α : Type*} [DecidableEq α] {p q u : α} (hpq : p ≠ q) :
    u ∈ ({p, q} : Finset α) ↔ u = p ∨ u = q := by
  simp only [Finset.mem_insert, Finset.mem_singleton]

private lemma no_five_of_four {n : ℕ} {S : Finset (Verts n)} (hS : S.card = 4)
    {x p q y z : Verts n} (hxS : x ∈ S) (hpS : p ∈ S) (hqS : q ∈ S) (hyS : y ∈ S)
    (hzS : z ∈ S) (hpx : p ≠ x) (hqx : q ≠ x) (hpq : p ≠ q)
    (hxn : x ∉ ({y, z} : Finset (Verts n)))
    (hpn : p ∉ ({y, z} : Finset (Verts n))) (hqn : q ∉ ({y, z} : Finset (Verts n)))
    (hyn : y ≠ z) : False := by
  have hmem : ∀ u ∈ ({x, p, q, y, z} : Finset (Verts n)), u ∈ S := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with h | h | h | h | h
    · rw [h]; exact hxS
    · rw [h]; exact hpS
    · rw [h]; exact hqS
    · rw [h]; exact hyS
    · rw [h]; exact hzS
  have hle : ({x, p, q, y, z} : Finset (Verts n)).card ≤ 4 := by
    have h2 := Finset.card_le_card hmem
    rwa [hS] at h2
  have hyx : y ≠ x := (ne_of_not_mem_pair hxn).1
  have hyp : y ≠ p := (ne_of_not_mem_pair hpn).1
  have hyq : y ≠ q := (ne_of_not_mem_pair hqn).1
  have hzx : z ≠ x := (ne_of_not_mem_pair hxn).2
  have hzp : z ≠ p := (ne_of_not_mem_pair hpn).2
  have hzq : z ≠ q := (ne_of_not_mem_pair hqn).2
  have h1 : x ∉ ({p, q, y, z} : Finset (Verts n)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at *
    tauto
  have h2 : p ∉ ({q, y, z} : Finset (Verts n)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at *
    tauto
  have h3 : q ∉ ({y, z} : Finset (Verts n)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at *
    tauto
  have h4 : y ∉ ({z} : Finset (Verts n)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at *
    tauto
  have hcard : ({x, p, q, y, z} : Finset (Verts n)).card = 5 := by
    rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
      Finset.card_insert_of_notMem h3, Finset.card_insert_of_notMem h4]
    simp
  omega

/-- **THE KEY LOCAL STEP.**  Let `c` satisfy `Tile`, let `S` be a four-element set, and suppose a
vertex `x ∈ S` has two colour-`i` neighbours `p, q` in `S`.  Then every colour-`i` edge of `K[S]`
is one of `s(x, p)`, `s(x, q)`: the three vertices span one two-edge path of colour `i`, and the
fourth vertex of `S` cannot carry another colour-`i` edge inside `S` (that would need five
vertices). -/
private lemma classIn_subset_of_path {c : Col n k} (hT : Tile c) {S : Finset (Verts n)}
    (hS : S.card = 4) {i : Fin k} {x p q : Verts n} (hxS : x ∈ S)
    (hT2 : (Nbrs c i x ∩ S).card = 2) (hN : Nbrs c i x ∩ S = {p, q}) :
    classIn c i S ⊆ {s(x, p), s(x, q)} := by
  classical
  have hpq : p ≠ q := by
    intro h
    have h' : ({p, q} : Finset (Verts n)).card = 2 := by rw [← hN]; exact hT2
    rw [h] at h'
    simp at h'
  have hxcard : (Nbrs c i x).card = 2 := by
    have h1 := Finset.card_le_card
      (Finset.inter_subset_left (s₁ := Nbrs c i x) (s₂ := S))
    have h2 := hT.nb_le_two i x
    rw [hT2] at h1
    omega
  have hpI : p ∈ Nbrs c i x ∩ S := by rw [hN]; simp
  have hqI : q ∈ Nbrs c i x ∩ S := by rw [hN]; simp
  have hpN : p ∈ Nbrs c i x := (Finset.mem_inter.mp hpI).1
  have hqN : q ∈ Nbrs c i x := (Finset.mem_inter.mp hqI).1
  have hpS : p ∈ S := (Finset.mem_inter.mp hpI).2
  have hqS : q ∈ S := (Finset.mem_inter.mp hqI).2
  have hpx : Nbrs c i p = {x} := hT.nb_singleton_of_path hpN hxcard
  have hqx : Nbrs c i q = {x} := hT.nb_singleton_of_path hqN hxcard
  intro e he
  obtain ⟨y, z, rfl, hyS, hzS, hne⟩ := exists_mk_of_mem_edgeFinset (mem_classIn.mp he).1
  have hci : c s(y, z) = i := (mem_classIn.mp he).2
  have hzN : z ∈ Nbrs c i y := mem_Nbrs.mpr ⟨hne.symm, hci⟩
  by_cases hyN : y ∈ Nbrs c i x
  · have hyI : y ∈ Nbrs c i x ∩ S := Finset.mem_inter.mpr ⟨hyN, hyS⟩
    rw [hN] at hyI
    rcases (mem_pair hpq).mp hyI with hyz' | hyz'
    · have hzy : z ∈ Nbrs c i p := by rw [hyz'] at hzN; exact hzN
      have hzy2 : z = x := by rw [hpx] at hzy; exact Finset.mem_singleton.mp hzy
      have heq : s(y, z) = s(x, p) := by rw [hyz', hzy2, Sym2.eq_swap]
      simp [heq]
    · have hzy : z ∈ Nbrs c i q := by rw [hyz'] at hzN; exact hzN
      have hzy2 : z = x := by rw [hqx] at hzy; exact Finset.mem_singleton.mp hzy
      have heq : s(y, z) = s(x, q) := by rw [hyz', hzy2, Sym2.eq_swap]
      simp [heq]
  · by_cases hxy : y = x
    · have hzNx : z ∈ Nbrs c i x := by rw [hxy] at hzN; exact hzN
      have hzI : z ∈ Nbrs c i x ∩ S := Finset.mem_inter.mpr ⟨hzNx, hzS⟩
      rw [hN] at hzI
      rcases (mem_pair hpq).mp hzI with h | h
      · have heq : s(y, z) = s(x, p) := by rw [hxy, h]
        simp [heq]
      · have heq : s(y, z) = s(x, q) := by rw [hxy, h]
        simp [heq]
    · by_cases hzN' : z ∈ Nbrs c i x
      · have hzI : z ∈ Nbrs c i x ∩ S := Finset.mem_inter.mpr ⟨hzN', hzS⟩
        rw [hN] at hzI
        rcases (mem_pair hpq).mp hzI with h | h
        · have hzy : p ∈ Nbrs c i y := by rw [h] at hzN; exact hzN
          have hy' : y ∈ Nbrs c i p := mem_Nbrs.mpr
            ⟨(mem_Nbrs.mp hzy).1.symm, c_swap (mem_Nbrs.mp hzy).2⟩
          rw [hpx] at hy'
          exact (hxy (Finset.mem_singleton.mp hy')).elim
        · have hzy : q ∈ Nbrs c i y := by rw [h] at hzN; exact hzN
          have hy' : y ∈ Nbrs c i q := mem_Nbrs.mpr
            ⟨(mem_Nbrs.mp hzy).1.symm, c_swap (mem_Nbrs.mp hzy).2⟩
          rw [hqx] at hy'
          exact (hxy (Finset.mem_singleton.mp hy')).elim
      · have hzx : z ≠ x := by
          intro h
          have hzy : x ∈ Nbrs c i y := by rw [h] at hzN; exact hzN
          have hyx : y ∈ Nbrs c i x := mem_Nbrs.mpr
            ⟨hxy, c_swap (mem_Nbrs.mp hzy).2⟩
          exact hyN hyx
        have hxn' : x ∉ ({y, z} : Finset (Verts n)) := by
          intro hc
          rcases (mem_pair hne).mp hc with h' | h'
          · exact hxy h'.symm
          · exact hzx h'.symm
        have hpn' : p ∉ ({y, z} : Finset (Verts n)) := by
          intro hc
          rcases (mem_pair hne).mp hc with h' | h'
          · exact hyN (h' ▸ hpN)
          · have hzy : p ∈ Nbrs c i y := by rw [← h'] at hzN; exact hzN
            have hy' : y ∈ Nbrs c i p := mem_Nbrs.mpr
              ⟨(mem_Nbrs.mp hzy).1.symm, c_swap (mem_Nbrs.mp hzy).2⟩
            rw [hpx] at hy'
            exact (hxy (Finset.mem_singleton.mp hy')).elim
        have hqn' : q ∉ ({y, z} : Finset (Verts n)) := by
          intro hc
          rcases (mem_pair hne).mp hc with h' | h'
          · exact hyN (h' ▸ hqN)
          · have hzy : q ∈ Nbrs c i y := by rw [← h'] at hzN; exact hzN
            have hy' : y ∈ Nbrs c i q := mem_Nbrs.mpr
              ⟨(mem_Nbrs.mp hzy).1.symm, c_swap (mem_Nbrs.mp hzy).2⟩
            rw [hqx] at hy'
            exact (hxy (Finset.mem_singleton.mp hy')).elim
        exact (no_five_of_four hS hxS hpS hqS hyS hzS
          ((mem_Nbrs.mp hpN).1) ((mem_Nbrs.mp hqN).1) hpq
          hxn' hpn' hqn' hne).elim

/-- **UNDER THE TILING CONDITION A COLOUR MEETS A `K₄` IN AT MOST TWO EDGES.**  Let `c` satisfy
`Tile` and let `S` be a four-element vertex set.  Then for every colour `i`,
`(classIn c i S).card ≤ 2`.

This is the key local bound: the edges of one colour inside a `K₄` are the two edges of a single
two-edge path, or two isolated single edges, but never more. -/
theorem card_classIn_four {c : Col n k} (hT : Tile c) {S : Finset (Verts n)} (hS : S.card = 4)
    (i : Fin k) : (classIn c i S).card ≤ 2 := by
  classical
  by_cases hex : ∃ x : Verts n, x ∈ S ∧ (Nbrs c i x ∩ S).card = 2
  · obtain ⟨x, hxS, hx⟩ := hex
    obtain ⟨p, q, hpq, hN⟩ := Finset.card_eq_two.mp hx
    have hsub := classIn_subset_of_path hT hS hxS hx hN
    have hcard : ({s(x, p), s(x, q)} : Finset (Sym2 (Verts n))).card = 2 := by
      refine Finset.card_pair ?_
      intro hh
      rcases sym2_inj hh with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact absurd h2 hpq
      · exact absurd (h2.trans h1) hpq
    exact le_trans (Finset.card_le_card hsub) (by omega)
  · by_cases hne : classIn c i S = ∅
    · rw [hne]; simp
    · obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      obtain ⟨x, y, rfl, hxS, hyS, hxyne⟩ := exists_mk_of_mem_edgeFinset (mem_classIn.mp he).1
      have hci : c s(x, y) = i := (mem_classIn.mp he).2
      have hxyN : y ∈ Nbrs c i x ∩ S := Finset.mem_inter.mpr
        ⟨mem_Nbrs.mpr ⟨hxyne.symm, hci⟩, hyS⟩
      have hyxN : x ∈ Nbrs c i y ∩ S := Finset.mem_inter.mpr
        ⟨mem_Nbrs.mpr ⟨hxyne, c_swap hci⟩, hxS⟩
      -- every vertex of `S` has at most one colour-`i` neighbour in `S`
      have hne2 : ∀ u : Verts n, u ∈ S → (Nbrs c i u ∩ S).card ≠ 2 := by
        intro u hu h2
        exact hex ⟨u, hu, h2⟩
      have hdeg : ∀ u : Verts n, u ∈ S → (Nbrs c i u ∩ S).card ≤ 1 := by
        intro u hu
        have h1 := Finset.card_le_card
          (Finset.inter_subset_left (s₁ := Nbrs c i u) (s₂ := S))
        have h2 := hT.nb_le_two i u
        have h3 := hne2 u hu
        omega
      have h1 : Nbrs c i x ∩ S = {y} := by
        have hcard : (Nbrs c i x ∩ S).card = 1 := by
          have h4 := hdeg x hxS
          have h5 : 1 ≤ (Nbrs c i x ∩ S).card := Finset.card_pos.mpr ⟨y, hxyN⟩
          omega
        obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
        have hay : a = y := by rw [ha] at hxyN; exact (Finset.mem_singleton.mp hxyN).symm
        rw [ha, hay]
      have h2 : Nbrs c i y ∩ S = {x} := by
        have hcard : (Nbrs c i y ∩ S).card = 1 := by
          have h4 := hdeg y hyS
          have h5 : 1 ≤ (Nbrs c i y ∩ S).card := Finset.card_pos.mpr ⟨x, hyxN⟩
          omega
        obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
        have hax : a = x := by rw [ha] at hyxN; exact (Finset.mem_singleton.mp hyxN).symm
        rw [ha, hax]
      -- `S = {x, y, z, w}` with `{z, w} = S \ {x, y}`
      have hsub : ({x, y} : Finset (Verts n)) ⊆ S := by
        intro u hu
        rcases (mem_pair hxyne).mp hu with h' | h'
        · rw [h']; exact hxS
        · rw [h']; exact hyS
      have hrem : (S \ ({x, y} : Finset (Verts n))).card = 2 := by
        have hcard : ({x, y} : Finset (Verts n)).card = 2 := Finset.card_pair hxyne
        have h2 : ({x, y} : Finset (Verts n)) ∩ S = {x, y} := by
          ext u
          simp only [Finset.mem_inter]
          constructor
          · intro hu
            exact hu.1
          · intro hu
            exact ⟨hu, hsub hu⟩
        rw [Finset.card_sdiff, h2, hcard]
        omega
      obtain ⟨z, w, hzw, hzw2⟩ := Finset.card_eq_two.mp hrem
      have hmem4 : ∀ u : Verts n, u ∈ S → u = x ∨ u = y ∨ u = z ∨ u = w := by
        intro u hu
        by_cases hu2 : u ∈ ({x, y} : Finset (Verts n))
        · rcases (mem_pair hxyne).mp hu2 with h' | h'
          · left
            exact h'
          · right
            left
            exact h'
        · have h3 : u ∈ S \ ({x, y} : Finset (Verts n)) := Finset.mem_sdiff.mpr ⟨hu, hu2⟩
          rw [hzw2] at h3
          rcases (mem_pair hzw).mp h3 with h' | h'
          · right
            right
            left
            exact h'
          · right
            right
            right
            exact h'
      have hsub : classIn c i S ⊆ {s(x, y), s(z, w)} := by
        intro e' he'
        obtain ⟨u, t, rfl, huS, htS, hutne⟩ :=
          exists_mk_of_mem_edgeFinset (mem_classIn.mp he').1
        have hci' : c s(u, t) = i := (mem_classIn.mp he').2
        have htN : t ∈ Nbrs c i u := mem_Nbrs.mpr ⟨hutne.symm, hci'⟩
        have huN : u ∈ Nbrs c i t := mem_Nbrs.mpr ⟨hutne, c_swap hci'⟩
        by_cases hutXY : t ∈ ({x, y} : Finset (Verts n))
        · rcases (mem_pair hxyne).mp hutXY with h' | h'
          · have hu' : u ∈ Nbrs c i x ∩ S := Finset.mem_inter.mpr
              ⟨by rw [← h']; exact huN, huS⟩
            rw [h1] at hu'
            have huy : u = y := Finset.mem_singleton.mp hu'
            have heq : s(u, t) = s(x, y) := by rw [h', huy, Sym2.eq_swap]
            simp [heq]
          · have hu' : u ∈ Nbrs c i y ∩ S := Finset.mem_inter.mpr
              ⟨by rw [← h']; exact huN, huS⟩
            rw [h2] at hu'
            have hux : u = x := Finset.mem_singleton.mp hu'
            have heq : s(u, t) = s(x, y) := by rw [h', hux, Sym2.eq_swap]
            simp [heq]
        · have hntx : t ≠ x := fun hh => hutXY ((mem_pair hxyne).mpr (Or.inl hh))
          have hnty : t ≠ y := fun hh => hutXY ((mem_pair hxyne).mpr (Or.inr hh))
          have hutZW : t ∈ ({z, w} : Finset (Verts n)) := by
            rcases hmem4 t htS with h'' | h'' | h'' | h''
            · exact absurd h'' hntx
            · exact absurd h'' hnty
            · exact (mem_pair hzw).mpr (Or.inl h'')
            · exact (mem_pair hzw).mpr (Or.inr h'')
          by_cases huXY : u ∈ ({x, y} : Finset (Verts n))
          · rcases (mem_pair hxyne).mp huXY with h'' | h''
            · have ht' : t ∈ Nbrs c i x ∩ S := Finset.mem_inter.mpr
                ⟨by rw [← h'']; exact htN, htS⟩
              rw [h1] at ht'
              have hty : t = y := Finset.mem_singleton.mp ht'
              exact (hutXY ((mem_pair hxyne).mpr (Or.inr hty))).elim
            · have ht' : t ∈ Nbrs c i y ∩ S := Finset.mem_inter.mpr
                ⟨by rw [← h'']; exact htN, htS⟩
              rw [h2] at ht'
              have htx : t = x := Finset.mem_singleton.mp ht'
              exact (hutXY ((mem_pair hxyne).mpr (Or.inl htx))).elim
          · have huZW : u ∈ ({z, w} : Finset (Verts n)) := by
              rcases hmem4 u huS with h'' | h'' | h'' | h''
              · exact absurd ((mem_pair hxyne).mpr (Or.inl h'')) huXY
              · exact absurd ((mem_pair hxyne).mpr (Or.inr h'')) huXY
              · exact (mem_pair hzw).mpr (Or.inl h'')
              · exact (mem_pair hzw).mpr (Or.inr h'')
            have huZW' : u ∈ s(z, w) :=
              Sym2.mem_iff.mpr ((mem_pair hzw).mp huZW)
            have htZW' : t ∈ s(z, w) :=
              Sym2.mem_iff.mpr ((mem_pair hzw).mp hutZW)
            have heq : s(u, t) = s(z, w) := Sym2.eq_of_ne_mem hutne
              (Sym2.mem_mk_left u t) (Sym2.mem_mk_right u t) huZW' htZW'
            simp [heq]
      refine le_trans (Finset.card_le_card hsub) ?_
      have hxz : x ≠ z ∧ x ≠ w := by
        have h1 : x ∉ S \ ({x, y} : Finset (Verts n)) := by
          intro hh
          exact (Finset.mem_sdiff.mp hh).2 (by simp [hxyne])
        rw [hzw2] at h1
        constructor
        · intro hh
          exact h1 ((mem_pair hzw).mpr (Or.inl hh))
        · intro hh
          exact h1 ((mem_pair hzw).mpr (Or.inr hh))
      have hcard : ({s(x, y), s(z, w)} : Finset (Sym2 (Verts n))).card = 2 := by
        refine Finset.card_pair ?_
        intro hh
        rcases sym2_inj hh with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact absurd h1 hxz.1
        · exact absurd h1 hxz.2
      omega

/-- **THE TILING CONDITION CLASSIFIES THE TWO EDGES OF A COLOUR IN A `K₄`.**  Let `c` satisfy `Tile`
and suppose a colour `i` meets a four-element set `S` in exactly two edges.  Then those two
edges are either the two edges of a two-edge path whose three vertices lie in `S` (a `pathSet`
inside the clique), or two vertex-disjoint edges (`Crossed c i S`).  These are the only two
possibilities, and they are the two cases a construction has to avoid combining on one clique
(`NoBadFour`, `NoCrossFour`). -/
theorem two_of_two {c : Col n k} (hT : Tile c) {S : Finset (Verts n)} (hS : S.card = 4)
    {i : Fin k} (hc2 : (classIn c i S).card = 2) :
    (∃ v : Verts n, v ∈ S ∧ v ∈ twoA c i ∧ pathSet c i v ⊆ S) ∨ Crossed c i S := by
  classical
  by_cases hex : ∃ x : Verts n, x ∈ S ∧ (Nbrs c i x ∩ S).card = 2
  · obtain ⟨x, hxS, hx⟩ := hex
    obtain ⟨p, q, hpq, hN⟩ := Finset.card_eq_two.mp hx
    have hsub := classIn_subset_of_path hT hS hxS hx hN
    have hxcard : (Nbrs c i x).card = 2 := by
      have h1 := Finset.card_le_card
        (Finset.inter_subset_left (s₁ := Nbrs c i x) (s₂ := S))
      have h2 := hT.nb_le_two i x
      rw [hx] at h1
      omega
    have hpS : p ∈ S := (Finset.mem_inter.mp (by rw [hN]; simp)).2
    have hqS : q ∈ S := (Finset.mem_inter.mp (by rw [hN]; simp)).2
    have hxNbrs : Nbrs c i x = {p, q} := by
      have h1 : (Nbrs c i x ∩ S).card = (Nbrs c i x).card := by
        have h2 := Finset.card_le_card
          (Finset.inter_subset_left (s₁ := Nbrs c i x) (s₂ := S))
        rw [hx, hxcard] at h2
        omega
      have h3 : Nbrs c i x ∩ S = Nbrs c i x :=
        Finset.eq_of_subset_of_card_le
          (Finset.inter_subset_left (s₁ := Nbrs c i x) (s₂ := S)) (by rw [h1])
      rw [← h3, hN]
    have hxtwo : x ∈ twoA c i := by
      rw [twoA, Finset.mem_filter]
      exact ⟨Finset.mem_univ x, hxcard⟩
    refine Or.inl ⟨x, hxS, hxtwo, ?_⟩
    intro v hv
    rcases Finset.mem_insert.mp hv with hv' | hv'
    · rw [hv']; exact hxS
    · rw [hxNbrs] at hv'
      rcases (mem_pair hpq).mp hv' with h' | h'
      · rw [h']; exact hpS
      · rw [h']; exact hqS
  · obtain ⟨e, he⟩ := Finset.card_pos.mp (show 0 < (classIn c i S).card by rw [hc2]; omega)
    obtain ⟨x, y, rfl, hxS, hyS, hxyne⟩ := exists_mk_of_mem_edgeFinset (mem_classIn.mp he).1
    have hci : c s(x, y) = i := (mem_classIn.mp he).2
    have hxyN : y ∈ Nbrs c i x ∩ S := Finset.mem_inter.mpr
      ⟨mem_Nbrs.mpr ⟨hxyne.symm, hci⟩, hyS⟩
    have hyxN : x ∈ Nbrs c i y ∩ S := Finset.mem_inter.mpr
      ⟨mem_Nbrs.mpr ⟨hxyne, c_swap hci⟩, hxS⟩
    have hne2 : ∀ u : Verts n, u ∈ S → (Nbrs c i u ∩ S).card ≠ 2 := by
      intro u hu h2
      exact hex ⟨u, hu, h2⟩
    have hdeg : ∀ u : Verts n, u ∈ S → (Nbrs c i u ∩ S).card ≤ 1 := by
      intro u hu
      have h1 := Finset.card_le_card
        (Finset.inter_subset_left (s₁ := Nbrs c i u) (s₂ := S))
      have h2 := hT.nb_le_two i u
      have h3 := hne2 u hu
      omega
    have h1 : Nbrs c i x ∩ S = {y} := by
      have hcard : (Nbrs c i x ∩ S).card = 1 := by
        have h4 := hdeg x hxS
        have h5 : 1 ≤ (Nbrs c i x ∩ S).card := Finset.card_pos.mpr ⟨y, hxyN⟩
        omega
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
      have hay : a = y := by rw [ha] at hxyN; exact (Finset.mem_singleton.mp hxyN).symm
      rw [ha, hay]
    have h2 : Nbrs c i y ∩ S = {x} := by
      have hcard : (Nbrs c i y ∩ S).card = 1 := by
        have h4 := hdeg y hyS
        have h5 : 1 ≤ (Nbrs c i y ∩ S).card := Finset.card_pos.mpr ⟨x, hyxN⟩
        omega
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
      have hax : a = x := by rw [ha] at hyxN; exact (Finset.mem_singleton.mp hyxN).symm
      rw [ha, hax]
    have hsub : ({x, y} : Finset (Verts n)) ⊆ S := by
      intro u hu
      rcases (mem_pair hxyne).mp hu with h' | h'
      · rw [h']; exact hxS
      · rw [h']; exact hyS
    have hrem : (S \ ({x, y} : Finset (Verts n))).card = 2 := by
      have hcard : ({x, y} : Finset (Verts n)).card = 2 := Finset.card_pair hxyne
      have h2' : ({x, y} : Finset (Verts n)) ∩ S = {x, y} := by
        ext u
        simp only [Finset.mem_inter]
        constructor
        · intro hu
          exact hu.1
        · intro hu
          exact ⟨hu, hsub hu⟩
      rw [Finset.card_sdiff, h2', hcard]
      omega
    obtain ⟨z, w, hzw, hzw2⟩ := Finset.card_eq_two.mp hrem
    have hmem4 : ∀ u : Verts n, u ∈ S → u = x ∨ u = y ∨ u = z ∨ u = w := by
      intro u hu
      by_cases hu2 : u ∈ ({x, y} : Finset (Verts n))
      · rcases (mem_pair hxyne).mp hu2 with h' | h'
        · left
          exact h'
        · right
          left
          exact h'
      · have h3 : u ∈ S \ ({x, y} : Finset (Verts n)) := Finset.mem_sdiff.mpr ⟨hu, hu2⟩
        rw [hzw2] at h3
        rcases (mem_pair hzw).mp h3 with h' | h'
        · right
          right
          left
          exact h'
        · right
          right
          right
          exact h'
    have hxz : x ≠ z ∧ x ≠ w := by
      have h1 : x ∉ S \ ({x, y} : Finset (Verts n)) := by
        intro hh
        exact (Finset.mem_sdiff.mp hh).2 (by simp [hxyne])
      rw [hzw2] at h1
      constructor
      · intro hh
        exact h1 ((mem_pair hzw).mpr (Or.inl hh))
      · intro hh
        exact h1 ((mem_pair hzw).mpr (Or.inr hh))
    -- the two edges of colour `i` in `S` are `s(x, y)` and `s(z, w)`
    have hsub' : classIn c i S ⊆ {s(x, y), s(z, w)} := by
      intro e' he'
      obtain ⟨u, t, rfl, huS, htS, hutne⟩ :=
        exists_mk_of_mem_edgeFinset (mem_classIn.mp he').1
      have hci' : c s(u, t) = i := (mem_classIn.mp he').2
      have htN : t ∈ Nbrs c i u := mem_Nbrs.mpr ⟨hutne.symm, hci'⟩
      have huN : u ∈ Nbrs c i t := mem_Nbrs.mpr ⟨hutne, c_swap hci'⟩
      by_cases hutXY : t ∈ ({x, y} : Finset (Verts n))
      · rcases (mem_pair hxyne).mp hutXY with h' | h'
        · have hu' : u ∈ Nbrs c i x ∩ S := Finset.mem_inter.mpr
            ⟨by rw [← h']; exact huN, huS⟩
          rw [h1] at hu'
          have huy : u = y := Finset.mem_singleton.mp hu'
          have heq : s(u, t) = s(x, y) := by rw [h', huy, Sym2.eq_swap]
          simp [heq]
        · have hu' : u ∈ Nbrs c i y ∩ S := Finset.mem_inter.mpr
            ⟨by rw [← h']; exact huN, huS⟩
          rw [h2] at hu'
          have hux : u = x := Finset.mem_singleton.mp hu'
          have heq : s(u, t) = s(x, y) := by rw [h', hux]
          simp [heq]
      · have hntx : t ≠ x := fun hh => hutXY ((mem_pair hxyne).mpr (Or.inl hh))
        have hnty : t ≠ y := fun hh => hutXY ((mem_pair hxyne).mpr (Or.inr hh))
        have hutZW : t ∈ ({z, w} : Finset (Verts n)) := by
          rcases hmem4 t htS with h'' | h'' | h'' | h''
          · exact absurd h'' hntx
          · exact absurd h'' hnty
          · exact (mem_pair hzw).mpr (Or.inl h'')
          · exact (mem_pair hzw).mpr (Or.inr h'')
        by_cases huXY : u ∈ ({x, y} : Finset (Verts n))
        · rcases (mem_pair hxyne).mp huXY with h'' | h''
          · have ht' : t ∈ Nbrs c i x ∩ S := Finset.mem_inter.mpr
              ⟨by rw [← h'']; exact htN, htS⟩
            rw [h1] at ht'
            have hty : t = y := Finset.mem_singleton.mp ht'
            exact (hutXY ((mem_pair hxyne).mpr (Or.inr hty))).elim
          · have ht' : t ∈ Nbrs c i y ∩ S := Finset.mem_inter.mpr
              ⟨by rw [← h'']; exact htN, htS⟩
            rw [h2] at ht'
            have htx : t = x := Finset.mem_singleton.mp ht'
            exact (hutXY ((mem_pair hxyne).mpr (Or.inl htx))).elim
        · have huZW : u ∈ ({z, w} : Finset (Verts n)) := by
            rcases hmem4 u huS with h'' | h'' | h'' | h''
            · exact absurd ((mem_pair hxyne).mpr (Or.inl h'')) huXY
            · exact absurd ((mem_pair hxyne).mpr (Or.inr h'')) huXY
            · exact (mem_pair hzw).mpr (Or.inl h'')
            · exact (mem_pair hzw).mpr (Or.inr h'')
          have huZW' : u ∈ s(z, w) := Sym2.mem_iff.mpr ((mem_pair hzw).mp huZW)
          have htZW' : t ∈ s(z, w) := Sym2.mem_iff.mpr ((mem_pair hzw).mp hutZW)
          have heq : s(u, t) = s(z, w) := Sym2.eq_of_ne_mem hutne
            (Sym2.mem_mk_left u t) (Sym2.mem_mk_right u t) huZW' htZW'
          simp [heq]
    have hyz : y ≠ z ∧ y ≠ w := by
      have h1 : y ∉ S \ ({x, y} : Finset (Verts n)) := by
        intro hh
        exact (Finset.mem_sdiff.mp hh).2 (by simp [hxyne])
      rw [hzw2] at h1
      constructor
      · intro hh
        exact h1 ((mem_pair hzw).mpr (Or.inl hh))
      · intro hh
        exact h1 ((mem_pair hzw).mpr (Or.inr hh))
    have hcard2 : ({s(x, y), s(z, w)} : Finset (Sym2 (Verts n))).card = 2 := by
      refine Finset.card_pair ?_
      intro hh
      rcases sym2_inj hh with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact absurd h1 hxz.1
      · exact absurd h1 hxz.2
    have heqfin : classIn c i S = ({s(x, y), s(z, w)} : Finset (Sym2 (Verts n))) :=
      Finset.eq_of_subset_of_card_le (Finset.Subset.trans hsub' (by rfl)) (by rw [hcard2, hc2])
    have hsup : ({s(x, y), s(z, w)} : Finset (Sym2 (Verts n))) ⊆ classIn c i S :=
      heqfin.symm ▸ (Finset.Subset.rfl)
    refine Or.inr ⟨s(x, y), s(z, w), he, ?_, ?_, ?_⟩
    · rw [heqfin]
      simp
    · intro hh
      rcases sym2_inj hh with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact absurd h1 hxz.1
      · exact absurd h1 hxz.2
    · intro v hv
      rcases Sym2.mem_iff.mp hv with h' | h'
      · intro hv'
        rcases Sym2.mem_iff.mp hv' with h'' | h''
        · exact absurd (h'.symm.trans h'') hxz.1
        · exact absurd (h'.symm.trans h'') hxz.2
      · intro hv'
        rcases Sym2.mem_iff.mp hv' with h'' | h''
        · exact absurd (h'.symm.trans h'') hyz.1
        · exact absurd (h'.symm.trans h'') hyz.2

/-! ### Counting the colours on a clique -/

/-- The edges of a clique are partitioned by their colours. -/
private lemma sum_classIn_card {n k : ℕ} (c : Col n k) (S : Finset (Verts n)) :
    (edgeFinset S).card = ∑ i ∈ (colorsOn c S), (classIn c i S).card := by
  refine Finset.card_eq_sum_card_fiberwise (f := c) (s := edgeFinset S)
    (t := colorsOn c S) ?_
  intro e he
  exact Finset.mem_image.mpr ⟨e, he, rfl⟩

/-- Two distinct members force cardinality at least two. -/
private lemma card_ge_two_of_mem {α : Type*} [DecidableEq α] {s : Finset α} {e e' : α}
    (he : e ∈ s) (he' : e' ∈ s) (hne : e ≠ e') : 2 ≤ s.card := by
  have hsub : ({e, e'} : Finset α) ⊆ s := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with h'' | h''
    · rw [h'']; exact he
    · rw [h'']; exact he'
  have h2 := Finset.card_le_card hsub
  rw [Finset.card_pair hne] at h2
  exact h2

/-- A colour which appears on an edge of `S` appears on at least one edge of `S`. -/
private lemma mem_colorsOn_of_card_ne_zero {c : Col n k} {S : Finset (Verts n)} {i : Fin k}
    (hi : (classIn c i S).card ≠ 0) : i ∈ colorsOn c S := by
  have hne : classIn c i S ≠ ∅ := by
    intro h
    have h1 : (classIn c i S).card = 0 := by rw [h]; simp
    exact hi h1
  obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  exact Finset.mem_image.mpr ⟨e, (mem_classIn.mp he).1, (mem_classIn.mp he).2⟩

/-- **A COLOUR WHICH IS DOUBLED ON A `K₄` IS PRESENT ON IT.** -/
private lemma mem_colorsOn_of_card_two {c : Col n k} {S : Finset (Verts n)} {i : Fin k}
    (hi : (classIn c i S).card = 2) : i ∈ colorsOn c S :=
  mem_colorsOn_of_card_ne_zero (by rw [hi]; omega)

/-- **THE COLOUR COUNT OF A `K₄`.**  Let `c` satisfy `Tile` and let `S` have four elements.
Writing `I` for the colours of `S` and `D` for those which meet `S` in *two* edges (no colour
meets `S` in three edges, by `card_classIn_four`), one has

    `6 ≤ |I| + |D|`:

the six edges of the clique are distributed over `|I|` colours, each contributing at least one
edge, and each of the `|D|` doubled colours contributing one edge more. -/
private lemma colorsOn_add_doubled {c : Col n k} (hT : Tile c) {S : Finset (Verts n)}
    (hS : S.card = 4) (D : Finset (Fin k)) (hDsub : D ⊆ (colorsOn c S))
    (hDin : ∀ x ∈ D, (classIn c x S).card = 2)
    (hDout : ∀ x ∈ (colorsOn c S) \ D, (classIn c x S).card ≤ 1) :
    (colorsOn c S).card + D.card = 6 := by
  classical
  have hge : ∀ x ∈ (colorsOn c S), 1 ≤ (classIn c x S).card := by
    intro x hx
    obtain ⟨e, he⟩ := Finset.mem_image.mp hx
    exact Finset.card_pos.mpr ⟨e, mem_classIn.mpr ⟨he.1, he.2⟩⟩
  have hsumI : ∑ x ∈ (colorsOn c S) \ D, (classIn c x S).card
      = ((colorsOn c S) \ D).card := by
    rw [Finset.card_eq_sum_ones]
    refine Finset.sum_congr rfl fun x hx => ?_
    have h5 := hge x ((Finset.mem_sdiff.mp hx).1)
    have h4 := hDout x hx
    omega
  have hsumD : ∑ x ∈ D, (classIn c x S).card = 2 * D.card := by
    have h1 : ∑ x ∈ D, (classIn c x S).card = ∑ x ∈ D, ((2 : ℕ)) := by
      refine Finset.sum_congr rfl fun x hx => ?_
      exact hDin x hx
    rw [h1, Finset.sum_const, nsmul_eq_mul, Nat.mul_comm]
    simp only [Nat.cast_id]
  have hrest : (edgeFinset S).card = (colorsOn c S).card + D.card := by
    rw [sum_classIn_card c S, ← Finset.sum_sdiff hDsub, hsumI, hsumD]
    have heq : D ∩ (colorsOn c S) = D := by
      ext x
      constructor
      · intro hx
        exact (Finset.mem_inter.mp hx).1
      · intro hx
        exact Finset.mem_inter.mpr ⟨hx, hDsub hx⟩
    rw [Finset.card_sdiff, heq]
    have hle' : D.card ≤ (colorsOn c S).card := Finset.card_le_card hDsub
    omega
  have h6 : (edgeFinset S).card = 6 := card_edgeFinset_four hS
  omega

/-- **THE COLOUR COUNT OF A `K₄`.**  Under the tiling condition, if `D` is the set of colours which
meet a four-element set in two edges, then the clique spans exactly `6 - |D|` colours. -/
private lemma colorsOn_card_eq_six_sub_doubled {c : Col n k} (hT : Tile c)
    {S : Finset (Verts n)} (hS : S.card = 4) :
    (colorsOn c S).card
      + ((colorsOn c S).filter (fun x => (classIn c x S).card = 2)).card = 6 := by
  refine colorsOn_add_doubled hT hS _ (Finset.filter_subset _ _) ?_ ?_
  · intro x hx
    exact (Finset.mem_filter.mp hx).2
  · intro x hx
    have hne : (classIn c x S).card ≠ 2 := by
      intro hh
      exact (Finset.mem_sdiff.mp hx).2
        (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hx).1, hh⟩)
    have hle := card_classIn_four hT hS x
    omega

/-- **TWO DOUBLED COLOURS ON A `K₄` SPAN AT MOST FOUR COLOURS.**  Under the tiling condition, if
two distinct colours meet a four-element set in two edges each, then that clique spans at most
four colours — so it is *not* admissible. -/
theorem four_of_two_doubled {c : Col n k} (hT : Tile c) {S : Finset (Verts n)} (hS : S.card = 4)
    {i j : Fin k} (hij : i ≠ j) (hci : (classIn c i S).card = 2) (hcj : (classIn c j S).card = 2) :
    (colorsOn c S).card ≤ 4 := by
  have h6 := colorsOn_card_eq_six_sub_doubled hT hS
  have hDmem : i ∈ (colorsOn c S).filter (fun x => (classIn c x S).card = 2) :=
    Finset.mem_filter.mpr ⟨mem_colorsOn_of_card_two hci, hci⟩
  have hDmem' : j ∈ (colorsOn c S).filter (fun x => (classIn c x S).card = 2) :=
    Finset.mem_filter.mpr ⟨mem_colorsOn_of_card_two hcj, hcj⟩
  have hD2 : 2 ≤ ((colorsOn c S).filter (fun x => (classIn c x S).card = 2)).card :=
    card_ge_two_of_mem hDmem hDmem' hij
  omega

/-- **A CROSSING COLOUR MEETS THE CLIQUE IN EXACTLY TWO EDGES.**  Under the tiling condition,
two vertex-disjoint edges of colour `i` inside a `K₄` are all the colour-`i` edges there. -/
private lemma card_eq_two_of_Crossed {c : Col n k} (hT : Tile c) {S : Finset (Verts n)}
    (hS : S.card = 4) {i : Fin k} (hX : Crossed c i S) : (classIn c i S).card = 2 := by
  obtain ⟨e, e', he, he', hne, hdis⟩ := hX
  exact le_antisymm (card_classIn_four hT hS i) (card_ge_two_of_mem he he' hne)

/-! ### The criterion -/

/-- Two three-element subsets of a four-element set share at least two elements. -/
private lemma inter_card_ge_two {n : ℕ} {S A B : Finset (Verts n)} (hS : S.card = 4)
    (hA : A.card = 3) (hB : B.card = 3) (hAS : A ⊆ S) (hBS : B ⊆ S) : 2 ≤ (A ∩ B).card := by
  have h1 := Finset.card_le_card (Finset.union_subset hAS hBS)
  have h2 := Finset.card_inter_add_card_union A B
  omega

/-- **THE LOCAL CONDITIONS EXCLUDE A DOUBLE-DOUBLED CLIQUE.**  Let `c` satisfy the four local
conditions of `Design`.  Then no four-element set is met by two distinct colours in two edges
each.  The three possibilities are excluded by `Packed` (two paths in one clique), `NoBadFour`
(a path and a crossing in one clique) and `NoCrossFour` (two crossings in one clique). -/
theorem noFourDouble_of_design {c : Col n k} (hT : Tile c) (hP : Packed c) (hX : NoCrossFour c)
    (hB : NoBadFour c) : ∀ S : Finset (Verts n), S.card = 4 → ∀ i j : Fin k, i ≠ j →
      ¬ ((classIn c i S).card = 2 ∧ (classIn c j S).card = 2) := by
  intro S hS i j hij
  rintro ⟨hci, hcj⟩
  have h1 := two_of_two hT hS hci
  have h2 := two_of_two hT hS hcj
  rcases h1 with ⟨v, hvS, hvi, hvsub⟩ | ⟨e, e', he, he', hne, hdis⟩
  · rcases h2 with ⟨w, hwS, hwi, hwsub⟩ | ⟨f, f', hf, hf', hne', hdis'⟩
    · have hinter : 2 ≤ (pathSet c i v ∩ pathSet c j w).card :=
        inter_card_ge_two hS (card_pathSet hvi) (card_pathSet hwi) hvsub hwsub
      exact absurd (hP i j v w hvi hwi hinter) hij
    · exact hB S hS j i (Ne.symm hij) ⟨⟨f, f', hf, hf', hne', hdis'⟩, v, hvi, hvsub⟩
  · rcases h2 with ⟨w, hwS, hwi, hwsub⟩ | ⟨f, f', hf, hf', hne', hdis'⟩
    · exact hB S hS i j hij ⟨⟨e, e', he, he', hne, hdis⟩, w, hwi, hwsub⟩
    · exact hX S hS i j hij ⟨⟨e, e', he, he', hne, hdis⟩, ⟨f, f', hf, hf', hne', hdis'⟩⟩

/-! ### `Admissible` is equivalent to the four local conditions -/

theorem five_of_noFourDouble {c : Col n k} (hT : Tile c) {S : Finset (Verts n)} (hS : S.card = 4)
    (hnd : ∀ i j : Fin k, i ≠ j → ¬ ((classIn c i S).card = 2 ∧ (classIn c j S).card = 2)) :
    5 ≤ (colorsOn c S).card := by
  classical
  have h6 := colorsOn_card_eq_six_sub_doubled hT hS
  have hsub : ∀ a b : Fin k, (classIn c a S).card = 2 → (classIn c b S).card = 2 → a ≠ b → False := by
    intro a b ha hb hab
    exact hnd a b hab ⟨ha, hb⟩
  have hDcard : ((colorsOn c S).filter (fun x => (classIn c x S).card = 2)).card ≤ 1 := by
    refine Finset.card_le_one.mpr ?_
    intro a ha
    intro b hb
    have hba : a = b := by
      by_contra h
      have ha2 : (classIn c a S).card = 2 := (Finset.mem_filter.mp ha).2
      have hb2 : (classIn c b S).card = 2 := (Finset.mem_filter.mp hb).2
      exact hsub a b ha2 hb2 h
    exact hba
  omega

/-- **THE CRITERION (SUFFICIENCY).**  The four local conditions of `Design` imply the catalog
condition: every four-vertex clique spans at least five colours. -/
theorem admissible_of_design {c : Col n k} (hT : Tile c) (hP : Packed c) (hX : NoCrossFour c)
    (hB : NoBadFour c) : Admissible c := by
  intro S hS
  exact five_of_noFourDouble hT hS (noFourDouble_of_design hT hP hX hB S hS)

/-- **THE CRITERION.**  `Admissible c ↔ Design c`: the catalog condition "every `K₄` spans at least
five colours" is *equivalent* to the four local conditions on colour classes, two-edge paths and
four-element vertex sets.  So a candidate colouring obtained from a construction (e.g. the
probabilistic construction of arXiv:2207.02920) can be verified by these four properties instead
of by checking all `C(n,4)` cliques. -/
theorem design_iff_admissible {c : Col n k} (hn : 4 ≤ n) : Admissible c ↔ Design c := by
  constructor
  · intro hc
    have hT : Tile c := Tile.of_admissible hc hn
    have hP : Packed c := Packed.of_admissible hc hn
    refine ⟨hT, hP, ?_, ?_⟩
    · intro S hS i j hij hX
      obtain ⟨hX, hY⟩ := hX
      have h2i := card_eq_two_of_Crossed hT hS hX
      have h2j := card_eq_two_of_Crossed hT hS hY
      have h4 := four_of_two_doubled hT hS hij h2i h2j
      have h5 := hc S hS
      omega
    · intro S hS i j hij hX
      obtain ⟨hX, hpath⟩ := hX
      obtain ⟨w, hwi, hwsub⟩ := hpath
      have h2i := card_eq_two_of_Crossed hT hS hX
      obtain ⟨a, b, hab, hNab⟩ := Finset.card_eq_two.mp (card_twoA j hwi)
      have haN : a ∈ Nbrs c j w := by rw [hNab]; simp
      have hbN : b ∈ Nbrs c j w := by rw [hNab]; simp
      have hwa : w ∈ S := hwsub (Finset.mem_insert_self w (Nbrs c j w))
      have haa : a ∈ S := hwsub (by rw [mem_pathSet]; exact Or.inr haN)
      have hbb : b ∈ S := hwsub (by rw [mem_pathSet]; exact Or.inr hbN)
      have he1 : s(w, a) ∈ classIn c j S := mem_classIn.mpr
        ⟨mem_edgeFinset_mk hwa haa (mem_Nbrs.mp haN).1.symm, (mem_Nbrs.mp haN).2⟩
      have he2 : s(w, b) ∈ classIn c j S := mem_classIn.mpr
        ⟨mem_edgeFinset_mk hwa hbb (mem_Nbrs.mp hbN).1.symm, (mem_Nbrs.mp hbN).2⟩
      have hneab : s(w, a) ≠ s(w, b) := by
        intro hh
        rcases Sym2.rel_iff.mp (Sym2.eq.mp hh) with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact hab h2
        · exact hab (h2.trans h1)
      have h2j : (classIn c j S).card = 2 :=
        le_antisymm (card_classIn_four hT hS j) (card_ge_two_of_mem he1 he2 hneab)
      have h4 := four_of_two_doubled hT hS (Ne.symm hij) h2j h2i
      have h5 := hc S hS
      omega
  · rintro ⟨hT, hP, hX, hB⟩
    exact admissible_of_design hT hP hX hB

/-! ### The remaining construction hypothesis, in a checkable form -/

/-- **THE CONSTRUCTION HYPOTHESIS, IN CHECKABLE FORM.**  For every `δ > 0` and all sufficiently
large `m ≡ 1 (mod 6)` there is a `k`-edge-colouring `c` of `K_m` which *satisfies the four local
conditions of `Criterion.design_iff_admissible`* — hence is admissible, by
`Criterion.design_iff_admissible` — and uses at most `5(m-1)/6 + δm/6` colours.

This is `Slack.STSFamily` with the Steiner triple system condition replaced by the local
conditions of a design, and with `Admissible c` replaced by `Design c`: the hypothesis is now
*verifiable* rather than presupposing the catalog condition. -/
def DesignFamily : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ M : ℕ, 4 ≤ M ∧ ∀ m : ℕ, M ≤ m → m % 6 = 1 →
    ∃ (k : ℕ) (c : Col m k), Design c ∧
      (6 : ℝ) * (k : ℝ) ≤ 5 * ((m - 1 : ℕ) : ℝ) + δ * (m : ℝ)

/-- **SANITY CHECK: THE CRITERION IS SATISFIABLE AND NOT VACUOUS.**  The injective colouring
`injCol` (every edge its own colour) satisfies all four local conditions, by the criterion applied
to `Definitions.admissible_injCol` — as it must, since every four-vertex clique of `injCol` spans
six colours. -/
theorem design_injCol (n : ℕ) (hn : 4 ≤ n) : Design (injCol n) :=
  (design_iff_admissible hn).mp (admissible_injCol n)

end JSP140
