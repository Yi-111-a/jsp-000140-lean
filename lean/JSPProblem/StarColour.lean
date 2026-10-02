import JSPProblem.Stage2

/-!
# JSP-000140 — the bad event `B_D` is a GREEDY matter, not a probabilistic one

Round 32 (`Stage2.lean`) proved that the verification criterion of the published two-stage
construction is exactly

```
Design c₀  +  Extends  +  Proper  +  LeafClosed  +  NoAltCycle  +  NoCrossFresh  ⟹  Admissible c
```

so the two residual bad events of the second stage are `B_D` (a 4-cycle of *uncoloured* edges
receiving at most two colours — arXiv:2208.12563 §4, event `B_D`; arXiv:2207.02920 §12, event `B₂`)
and `C_{D,i}` (two *crossing* uncoloured edges receiving the same fresh colour while the other two
opposite edges are coloured alike in Phase 1 — events `C_{D,i}` resp. `B₃`).  Both papers obtain
their second stage from the symmetric **Lovász Local Lemma**, which Mathlib does not contain.

**This file proves that the first of the two bad events never needed the local lemma at all.**

The point is that `B_D` is a *forbidden-pair* condition on the fresh colouring, not an existential
one, and a greedy edge colouring of the leftover graph can be arranged to respect it: when the edge
`e` is coloured, the colours to be avoided are

* those of the at most `2D` leftover edges **meeting** `e` (the properness condition `A_{e,f,i}` /
  `B₁`, already handled by `Second.proper_of_sparseL`), and
* those of the leftover edges **separated from `e` by a third leftover edge** (`Sep` below), of
  which there are at most `2D²`, because each of them is reached from `e` through a middle edge
  incident with one of the two endpoints of `e`.

The main results are

* `Sep`, `Sep.symm` — two leftover edges separated by a third leftover edge: the two *outer*
  edges of a path of three leftover edges, i.e. exactly the two diagonals of a two-coloured
  4-cycle of `L`;
* `noAltCycle_of_starProper` — a fresh colouring which is proper **and** injective on the separated
  pairs satisfies `NoAltCycle`, i.e. the bad event `B_D` is absent.  This is the combinatorial
  content of the reduction;
* `star_greedy` — **the greedy star colouring**: a leftover graph of maximum degree `D` carries a
  colouring with `2D² + 2D + 1` fresh colours which is proper and injective on the separated pairs;
* `second_stage_of_sparseL`, `second_stage_of_leftover` — **the deterministic half of the second
  stage**: `Proper` *and* `NoAltCycle` are available with `2Δ(L)² + 2Δ(L) + 1` fresh colours and no
  probability whatsoever;
* `admissible_of_star` — a first-stage `Design` with leaf closure, extended properly on `L` by such
  a greedy star colouring and avoiding `C_{D,i}`, is **admissible**;
* `StarStageFamily`, `jsp_000140_main_of_star_stage_family` — the required theorem
  `jsp_000140_main` reduced to the published construction with **only one** probabilistic
  hypothesis left: no two crossing leftover edges of equal fresh colour above a phase-1
  monochromatic pair.

The price is quantitative and honest: `2D²` fresh colours rather than the `Θ(n^{1-δ})` of the
papers, so `B_D` costs `Θ(Δ(L)²)` deterministically while `C_{D,i}` — which cannot be handled by
any greedy rule, because it constrains *disjoint* pairs of leftover edges — still needs the local
lemma.  That is the precise division of labour between determinism and probability in the second
stage of arXiv:2208.12563 §4 = arXiv:2207.02920 §12.
-/

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace JSP140

attribute [local instance] Classical.propDecidable

variable {n k : ℕ}

/-! ### Separated pairs of leftover edges -/

/-- **TWO LEFTOVER EDGES SEPARATED BY A THIRD LEFTOVER EDGE.**  `Sep L e f` says that `e` and `f`
are the two outer edges of a path of three leftover edges `a – b – p – q`, on four distinct
vertices: `e = s(a,b)`, `f = s(p,q)` and at least one of the two middle edges `s(b,p)`,
`s(q,a)` is leftover.

In a 4-cycle of leftover edges the two *diagonals* are separated by either of the two paths around
the cycle, so a two-coloured 4-cycle forces its two diagonals to have the same fresh colour.  This
is exactly the bad event `B_D` of arXiv:2208.12563 §4 (= `B₂` of arXiv:2207.02920 §12). -/
def Sep {n : ℕ} (L : Finset (Sym2 (Verts n))) (e f : Sym2 (Verts n)) : Prop :=
  ∃ (a b p q : Verts n), FourDistinct a b p q ∧ e = s(a, b) ∧ f = s(p, q) ∧
    (s(b, p) ∈ L ∨ s(q, a) ∈ L)

/-- **`Sep` is symmetric in its two arguments.** -/
theorem Sep.symm {n : ℕ} {L : Finset (Sym2 (Verts n))} {e f : Sym2 (Verts n)}
    (h : Sep L e f) : Sep L f e := by
  obtain ⟨a, b, p, q, h4, he, hf, hm⟩ := h
  refine ⟨p, q, a, b, ⟨h4.2.2.2.2.2, h4.2.1.symm, h4.2.2.2.1.symm, h4.2.2.1.symm,
    h4.2.2.2.2.1.symm, h4.1⟩, hf, he, ?_⟩
  rcases hm with hm | hm
  · exact Or.inr hm
  · exact Or.inl hm

/-- **THE TWO EDGES OF A SEPARATED PAIR ARE DISTINCT.**  Public from round 34 on: the generalised
greedy engine of `JSPProblem/Cross.lean` needs the distinctness of `FreshRel`-related pairs to apply
`greedy_of_boundedRel`. -/
theorem ne_of_Sep {n : ℕ} {L : Finset (Sym2 (Verts n))} {e f : Sym2 (Verts n)}
    (h : Sep L e f) : e ≠ f := by
  obtain ⟨a, b, p, q, h4, he, hf, hm⟩ := h
  intro hcon
  have hEq : s(a, b) = s(p, q) := he.symm.trans (hcon.trans hf)
  rcases sym2_inj hEq with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exact absurd e1 h4.2.1
  · exact absurd e1 h4.2.2.1

/-- **A FRESH COLOURING WHICH RESPECTS THE SEPARATED PAIRS.**  The first conjunct is the published
properness (`A_{e,f,i}` / `B₁`, already proved to exist with `2Δ+1` colours by
`Second.proper_of_sparseL`); the second is the additional condition that this file proves to be
achievable **deterministically**. -/
def StarProper {n K : ℕ} (c : Col n K) (L : Finset (Sym2 (Verts n))) : Prop :=
  Proper c L ∧ ∀ e f : Sym2 (Verts n), e ∈ L → f ∈ L → Sep L e f → c e ≠ c f

private theorem card_ge_two {α : Type*} [DecidableEq α] {F : Finset α} {s t : α}
    (hs : s ∈ F) (ht : t ∈ F) (h : s ≠ t) : 2 ≤ F.card := by
  have hsub : insert s (insert t (∅ : Finset α)) ⊆ F := by
    intro x hx
    simp only [Finset.mem_insert] at hx
    rcases hx with rfl | rfl | hx
    · exact hs
    · exact ht
    · exact absurd hx (by simp)
  calc 2 = (insert s (insert t (∅ : Finset α))).card := by
        rw [Finset.card_insert_of_notMem (by simp [h]), Finset.card_insert_of_notMem (by simp),
          Finset.card_empty]
    _ ≤ F.card := Finset.card_le_card hsub

/-- **THE FOUR EDGES OF A CYCLE ARE PAIRWISE DISTINCT AS ADJACENT PAIRS.** -/
private theorem cyc_ne {n : ℕ} {a b p q : Verts n} (h4 : FourDistinct a b p q) :
    s(a, b) ≠ s(b, p) ∧ s(p, q) ≠ s(q, a) ∧ s(q, a) ≠ s(a, b) ∧ s(b, p) ≠ s(p, q) := by
  have h1 : a ≠ b := h4.1
  have h2 : a ≠ p := h4.2.1
  have h3 : a ≠ q := h4.2.2.1
  have h5 : b ≠ p := h4.2.2.2.1
  have h6 : b ≠ q := h4.2.2.2.2.1
  have h7 : p ≠ q := h4.2.2.2.2.2
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro hcon <;>
    rcases sym2_inj hcon with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exact absurd e1 h1
  · exact absurd e1 h2
  · exact absurd e1 h7
  · exact absurd e1 h2.symm
  · exact absurd e1 h3.symm
  · exact absurd e1 h6.symm
  · exact absurd e1 h5
  · exact absurd e1 h6

private theorem card_ge_four {α : Type*} [DecidableEq α] {F : Finset α} {w x y z : α}
    (h1 : w ∈ F) (h2 : x ∈ F) (h3 : y ∈ F) (h4 : z ∈ F)
    (hne : w ≠ x ∧ w ≠ y ∧ w ≠ z ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z) : 4 ≤ F.card := by
  have hsub : insert w (insert x (insert y (insert z (∅ : Finset α)))) ⊆ F := by
    intro t ht
    simp only [Finset.mem_insert] at ht
    rcases ht with ht | ht | ht | ht | ht
    · exact ht ▸ h1
    · exact ht ▸ h2
    · exact ht ▸ h3
    · exact ht ▸ h4
    · exact absurd ht (by simp)
  calc 4 = (insert w (insert x (insert y (insert z (∅ : Finset α))))).card := by
        rw [Finset.card_insert_of_notMem (by simp [hne.1, hne.2.1, hne.2.2.1]),
          Finset.card_insert_of_notMem (by simp [hne.2.2.2]),
          Finset.card_insert_of_notMem (by simp [hne.2.2.2])]
        simp
    _ ≤ F.card := Finset.card_le_card hsub

/-- **NO 4-CYCLE OF LEFTOVER EDGES SPANS FEWER THAN THREE COLOURS.**  If a fresh colouring is
proper and injective on the separated pairs, then no 4-cycle of leftover edges spans at most two
colours.

Proof: in the 4-cycle `a – b – p – q` the neighbouring edges receive different colours by
properness, and the two diagonals `s(a,b)`, `s(p,q)` are separated (they are the outer edges of the
path `a – b – p – q`, whose middle edge `s(b,p)` is leftover), as are `s(b,p)`, `s(q,a)`.  So all
four colours are **pairwise distinct**, and in particular there are at least three.  This is the
whole content of the bad event `B_D` of arXiv:2208.12563 §4 (= `B₂` of arXiv:2207.02920 §12): it is
excluded by a *greedy* colouring and needs no local lemma. -/
theorem noAltCycle_of_starProper {n K : ℕ} {c : Col n K} {L : Finset (Sym2 (Verts n))}
    (h : StarProper c L) : NoAltCycle c L := by
  obtain ⟨hP, hS⟩ := h
  intro a b p q h4 h1 h2 h3 h4'
  have hne := cyc_ne h4
  have hAB : c s(a, b) ≠ c s(b, p) := hP (e := s(a, b)) (e' := s(b, p)) h1 h2 hne.1
    ⟨b, Sym2.mem_mk_right a b, Sym2.mem_mk_left b p⟩
  have hBC : c s(b, p) ≠ c s(p, q) := hP (e := s(b, p)) (e' := s(p, q)) h2 h3 hne.2.2.2
    ⟨p, Sym2.mem_mk_right b p, Sym2.mem_mk_left p q⟩
  have hCD : c s(p, q) ≠ c s(q, a) := hP (e := s(p, q)) (e' := s(q, a)) h3 h4' hne.2.1
    ⟨q, Sym2.mem_mk_right p q, Sym2.mem_mk_left q a⟩
  have hDA : c s(q, a) ≠ c s(a, b) := hP (e := s(q, a)) (e' := s(a, b)) h4' h1 hne.2.2.1
    ⟨a, Sym2.mem_mk_right q a, Sym2.mem_mk_left a b⟩
  have hAC : c s(a, b) ≠ c s(p, q) :=
    hS s(a, b) s(p, q) h1 h3 ⟨a, b, p, q, h4, rfl, rfl, Or.inl h2⟩
  have hBD : c s(b, p) ≠ c s(q, a) :=
    hS s(b, p) s(q, a) h2 h4'
      ⟨b, p, q, a, ⟨h4.2.2.2.1, h4.2.2.2.2.1, h4.1.symm, h4.2.2.2.2.2, h4.2.1.symm,
        h4.2.2.1.symm⟩,
        rfl, rfl, Or.inl h3⟩
  have hm1 : c s(a, b) ∈ cycleColours c a b p q := by simp [cycleColours]
  have hm2 : c s(b, p) ∈ cycleColours c a b p q := by simp [cycleColours]
  have hm3 : c s(p, q) ∈ cycleColours c a b p q := by simp [cycleColours]
  have hm4 : c s(q, a) ∈ cycleColours c a b p q := by simp [cycleColours]
  have h4le : 4 ≤ (cycleColours c a b p q).card :=
    card_ge_four hm1 hm2 hm3 hm4 ⟨hAB, hAC, hDA.symm, hBC, hBD, hCD⟩
  omega

/-- **A VERTEX IS IN AN EDGE IFF IT IS ONE OF ITS TWO ENDPOINTS.** -/
private theorem mem_s_iff {n : ℕ} (x a b : Verts n) : x ∈ s(a, b) ↔ x = a ∨ x = b := by simp

/-- **A VERTEX WHICH IS NEITHER ENDPOINT OF AN EDGE IS NOT IN IT.** -/
private theorem not_mem_s {n : ℕ} {x a b : Verts n} (h1 : x ≠ a) (h2 : x ≠ b) :
    x ∉ s(a, b) := by
  rw [mem_s_iff]
  tauto

/-! ### Counting: at most `2D²` leftover edges are separated from a given one -/

/-- **THE NEIGHBOURS OF A VERTEX AMONG THE LEFTOVER EDGES, AS VERTICES.** -/
private noncomputable def NbL {n : ℕ} (L : Finset (Sym2 (Verts n))) (v : Verts n) :
    Finset (Verts n) :=
  (Finset.univ : Finset (Verts n)).filter (fun x => s(v, x) ∈ L)

private theorem card_NbL {n : ℕ} {L : Finset (Sym2 (Verts n))} (v : Verts n) :
    (NbL L v).card = DegL L v := by
  set E : Finset (Sym2 (Verts n)) :=
    (NbL L v).image (fun x : Verts n => s(v, x)) with hE
  have hc1 : E.card ≤ (L.filter (fun e => v ∈ e)).card := by
    refine Finset.card_le_card (fun e he => ?_)
    rw [hE] at he
    rcases Finset.mem_image.mp he with ⟨x, hx, hxe⟩
    rw [← hxe]
    simp only [NbL, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact Finset.mem_filter.mpr ⟨hx, Sym2.mem_mk_left v x⟩
  have hc2 : (L.filter (fun e => v ∈ e)).card ≤ E.card := by
    refine Finset.card_le_card (fun e he => ?_)
    rw [hE]
    have hmem := Finset.mem_filter.mp he
    have hx : Sym2.Mem.other' hmem.2 ∈ NbL L v := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [Sym2.other_spec' hmem.2]
      exact hmem.1
    exact Finset.mem_image.mpr ⟨Sym2.Mem.other' hmem.2, hx, Sym2.other_spec' hmem.2⟩
  have hc3' : ((NbL L v).image (fun x : Verts n => s(v, x))).card = (NbL L v).card :=
    Finset.card_image_iff.mpr (fun x _ y _ hxy => sym2_inj_right hxy)
  rw [DegL, ← hc3', ← hE]
  exact le_antisymm hc1 hc2

private theorem card_NbL_le {n D : ℕ} {L : Finset (Sym2 (Verts n))} (hD : SparseL L D)
    (v : Verts n) : (NbL L v).card ≤ D := by
  rw [card_NbL]; exact hD v

/-- **AN EDGE HAS AT MOST TWO ENDPOINTS.** -/
private theorem card_mem_e_le {n : ℕ} (e : Sym2 (Verts n)) :
    ((Finset.univ : Finset (Verts n)).filter (fun v => v ∈ e)).card ≤ 2 := by
  obtain ⟨a, b, h⟩ : ∃ a b : Verts n, e = s(a, b) :=
    Quot.inductionOn e (fun p : Verts n × Verts n => ⟨p.1, p.2, rfl⟩)
  have hex : ((Finset.univ : Finset (Verts n)).filter (fun v => v ∈ e))
      = insert a (insert b (∅ : Finset (Verts n))) := by
    rw [h]
    ext x
    simp
  rw [hex]
  have h1 := Finset.card_insert_le b (∅ : Finset (Verts n))
  simp only [Finset.card_empty, zero_add] at h1
  have h2 := Finset.card_insert_le a (insert b (∅ : Finset (Verts n)))
  omega

/-- **WITNESSES THAT `s(y, z)` IS SEPARATED FROM `e` THROUGH THE ENDPOINT `v` OF `e`.**

The pair `(y, z)` is a witness when `s(y, v) ∈ L`, `y ∉ e`, `s(z, y) ∈ L`, `z ∉ e` and `y ≠ z`:
then, writing `e = s(v, v')` with `v' ≠ v`, the path `z – y – v – v'` has four distinct vertices,
its middle edge `s(y, v)` is leftover, and its two outer edges are `s(z, y)` and `e`. -/
private noncomputable def wit {n : ℕ} (L : Finset (Sym2 (Verts n))) (e : Sym2 (Verts n))
    (v : Verts n) : Finset (Verts n × Verts n) :=
  ((NbL L v).filter (fun y => y ∉ e)).biUnion
    fun y => (NbL L y).filter (fun z => z ∉ e ∧ z ≠ y) |>.image (fun z => (y, z))

/-- **AT MOST `D²` WITNESSES THROUGH ONE ENDPOINT.** -/
private theorem card_wit_le {n D : ℕ} {L : Finset (Sym2 (Verts n))} (hD : SparseL L D)
    (e : Sym2 (Verts n)) (v : Verts n) : (wit L e v).card ≤ D * D := by
  have h3 : (wit L e v).card ≤ ∑ y ∈ (NbL L v).filter (fun y => y ∉ e),
      (((NbL L y).filter (fun z => z ∉ e ∧ z ≠ y)).image (fun z => (y, z))).card := by
    simpa only [wit] using (Finset.card_biUnion_le)
  have h4 : ∑ y ∈ (NbL L v).filter (fun y => y ∉ e),
      (((NbL L y).filter (fun z => z ∉ e ∧ z ≠ y)).image (fun z => (y, z))).card
      ≤ ∑ _y ∈ (NbL L v).filter (fun y => y ∉ e), D :=
    Finset.sum_le_sum
      (s := (NbL L v).filter (fun y => y ∉ e))
      (f := fun y => (((NbL L y).filter (fun z => z ∉ e ∧ z ≠ y)).image
        (fun z => (y, z))).card) (g := fun _ => D)
      (fun y _ => le_trans (Finset.card_image_le) (le_trans
        (Finset.card_le_card (Finset.filter_subset _ _)) (card_NbL_le hD y)))
  have h6 : ((NbL L v).filter (fun y => y ∉ e)).card ≤ D :=
    le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (card_NbL_le hD v)
  have h7 : ∑ _y ∈ (NbL L v).filter (fun y => y ∉ e), D ≤ D * D := by
    rw [Finset.sum_const]
    exact Nat.mul_le_mul h6 (le_refl D)
  exact le_trans h3 (le_trans h4 h7)

/-- **THE LEFTOVER EDGES SEPARATED FROM `e`.**  Public from round 34 on: `Cross.card_freshRel_le`
of `JSPProblem/Cross.lean` reuses this bound together with the crossing bound to drive the
generalised greedy engine. -/
noncomputable def sepF {n : ℕ} (L : Finset (Sym2 (Verts n))) (e : Sym2 (Verts n)) :
    Finset (Sym2 (Verts n)) :=
  (((Finset.univ : Finset (Verts n)).filter (fun v => v ∈ e)).biUnion
      fun v => (wit L e v).image (fun t => s(t.1, t.2))).filter (fun f => Sep L e f)

/-- **AT MOST `2D²` LEFTOVER EDGES ARE SEPARATED FROM A GIVEN LEFTOVER EDGE.** -/
theorem card_sepF_le {n D : ℕ} {L : Finset (Sym2 (Verts n))} (hD : SparseL L D)
    (e : Sym2 (Verts n)) : (sepF L e).card ≤ 2 * D * D := by
  set E : Finset (Sym2 (Verts n)) :=
    ((Finset.univ : Finset (Verts n)).filter (fun v => v ∈ e)).biUnion
      fun v => (wit L e v).image (fun t => s(t.1, t.2)) with hE
  have h3 : E.card ≤ ∑ v ∈ (Finset.univ : Finset (Verts n)).filter (fun v => v ∈ e),
      ((wit L e v).image (fun t => s(t.1, t.2))).card := by
    simpa only [hE] using (Finset.card_biUnion_le)
  have h4 : ∑ v ∈ (Finset.univ : Finset (Verts n)).filter (fun v => v ∈ e),
      ((wit L e v).image (fun t => s(t.1, t.2))).card
      ≤ ∑ _v ∈ (Finset.univ : Finset (Verts n)).filter (fun v => v ∈ e), D * D :=
    Finset.sum_le_sum
      (s := (Finset.univ : Finset (Verts n)).filter (fun v => v ∈ e))
      (f := fun v => ((wit L e v).image (fun t => s(t.1, t.2))).card) (g := fun _ => D * D)
      (fun v _ => le_trans (Finset.card_image_le) (card_wit_le hD e v))
  have h7 : ∑ _v ∈ (Finset.univ : Finset (Verts n)).filter (fun v => v ∈ e), D * D
      ≤ 2 * D * D := by
    rw [Finset.sum_const]
    have hle := card_mem_e_le e
    exact le_trans (Nat.mul_le_mul hle (le_refl (D * D))) (by rw [Nat.mul_assoc])
  exact le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (le_trans h3 (le_trans h4 h7))

private theorem mem_wit {n : ℕ} {L : Finset (Sym2 (Verts n))} {e : Sym2 (Verts n)}
    {v y z : Verts n} (ht : (y, z) ∈ wit L e v) :
    y ∉ e ∧ z ∉ e ∧ y ≠ z ∧ s(y, v) ∈ L ∧ s(z, y) ∈ L := by
  rw [wit] at ht
  obtain ⟨y', hy', hmem⟩ := Finset.mem_biUnion.mp ht
  obtain ⟨hyNb, hyE⟩ := Finset.mem_filter.mp hy'
  obtain ⟨z', hz', hz⟩ := Finset.mem_image.mp hmem
  obtain ⟨hEqa, hEqb⟩ : y' = y ∧ z' = z := by simpa using hz
  simp only [hEqa, hEqb] at hy' hyNb hyE hz'
  obtain ⟨hzNb, hpred⟩ := Finset.mem_filter.mp hz'
  have h1 : y ∉ e := hyE
  have h2 : z ∉ e := hpred.1
  have h3 : y ≠ z := hpred.2.symm
  have hyNb' : s(v, y) ∈ L :=
    (Finset.mem_filter.mp (show y ∈ (Finset.univ : Finset (Verts n)).filter
      (fun x => s(v, x) ∈ L) from hyNb)).2
  have hzNb' : s(y, z) ∈ L :=
    (Finset.mem_filter.mp (show z ∈ (Finset.univ : Finset (Verts n)).filter
      (fun x => s(y, x) ∈ L) from hzNb)).2
  have h4 : s(y, v) ∈ L := (show s(y, v) = s(v, y) from Sym2.eq_swap) ▸ hyNb'
  have h5 : s(z, y) ∈ L := (show s(z, y) = s(y, z) from Sym2.eq_swap) ▸ hzNb'
  exact ⟨h1, h2, h3, h4, h5⟩

/-- **EVERY SEPARATED LEFTOVER EDGE IS IN `sepF`.** -/
theorem mem_sepF {n : ℕ} {L : Finset (Sym2 (Verts n))} {e f : Sym2 (Verts n)}
    (hf : f ∈ L) (h : Sep L e f) : f ∈ sepF L e := by
  obtain ⟨a, b, p, q, h4, he, hf', hm⟩ := h
  have hsep : Sep L e f := ⟨a, b, p, q, h4, he, hf', hm⟩
  refine Finset.mem_filter.mpr ⟨?_, hsep⟩
  rcases hm with hm | hm
  · -- the middle edge is `s(b, p)`: the witness is `(p, q)` at the endpoint `b` of `e`
    refine Finset.mem_biUnion.mpr ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · exact he ▸ (mem_s_iff b a b).2 (Or.inr rfl)
    · refine Finset.mem_image.mpr ⟨(p, q), ?_, hf'.symm⟩
      refine Finset.mem_biUnion.mpr ⟨p, Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
      · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩
      · exact he ▸ not_mem_s h4.2.1.symm h4.2.2.2.1.symm
      · refine Finset.mem_image.mpr ⟨q, Finset.mem_filter.mpr ⟨?_, ⟨?_, ?_⟩⟩, rfl⟩
        · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf'.symm ▸ hf⟩
        · exact he ▸ not_mem_s h4.2.2.1.symm h4.2.2.2.2.1.symm
        · exact h4.2.2.2.2.2.symm
  · -- the middle edge is `s(q, a)`: the witness is `(q, p)` at the endpoint `a` of `e`
    refine Finset.mem_biUnion.mpr ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · exact he ▸ (mem_s_iff a a b).2 (Or.inl rfl)
    · refine Finset.mem_image.mpr ⟨(q, p), ?_, (Sym2.eq_swap ▸ hf'.symm)⟩
      refine Finset.mem_biUnion.mpr ⟨q, Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
      · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Sym2.eq_swap ▸ hm)⟩
      · exact he ▸ not_mem_s h4.2.2.1.symm h4.2.2.2.2.1.symm
      · refine Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨?_, ⟨?_, ?_⟩⟩, rfl⟩
        · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Sym2.eq_swap ▸ hf'.symm ▸ hf⟩
        · exact he ▸ not_mem_s h4.2.1.symm h4.2.2.2.1.symm
        · exact h4.2.2.2.2.2

/-! ### The greedy star colouring of the leftover graph -/

/-- **A COLOUR AVAILABLE FOR ONE MORE EDGE.** -/
private theorem exists_free_colour' {n K : ℕ} {s : Finset (Sym2 (Verts n))}
    (g : ∀ e, e ∈ s → Fin K) (N : Finset (Sym2 (Verts n))) (hsub : N ⊆ s) (hN : N.card < K) :
    ∃ j : Fin K, ∀ (f : Sym2 (Verts n)) (hf : f ∈ N), g f (hsub hf) ≠ j := by
  set U : Finset (Fin K) := N.attach.image
    (fun z : {f : Sym2 (Verts n) // f ∈ N} => g z.1 (hsub z.2)) with hU
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

/-- **THE GREEDY STAR COLOURING OF A LEFTOVER GRAPH.**  If `L` has maximum degree `D`, then the
edges of `L` can be coloured with `2D² + 2D + 1` fresh colours so that two edges of `L` which share
a vertex, **or which are separated by a third edge of `L`, get different colours**.  No
probability is involved: the edges of `L` are processed one at a time and each new edge avoids the
colours of the at most `2D` edges it meets and of the at most `2D²` edges separated from it. -/
theorem star_greedy {n D : ℕ} {L : Finset (Sym2 (Verts n))} (hD : SparseL L D)
    (hf : L ⊆ edgeFinset (Finset.univ : Finset (Verts n))) :
    ∃ g : L → Fin (2 * D * D + 2 * D + 1),
      ∀ (x y : {e : Sym2 (Verts n) // e ∈ L}), x ≠ y →
        (Shares x.1 y.1 ∨ Sep L x.1 y.1) → g x ≠ g y := by
  have key : ∀ (t : Finset (Sym2 (Verts n))), t ⊆ L → SparseL t D →
      ∃ g : t → Fin (2 * D * D + 2 * D + 1), ∀ (x y : {e : Sym2 (Verts n) // e ∈ t}), x ≠ y →
        (Shares x.1 y.1 ∨ Sep L x.1 y.1) → g x ≠ g y := by
    intro t
    induction t using Finset.induction_on with
    | empty => exact fun _ _ => ⟨fun x => ⟨0, by omega⟩, fun x y _ _ => nomatch x⟩
    | @insert a s ha ih =>
      intro hts hDs
      obtain ⟨g₀, hg₀⟩ := ih (Finset.Subset.trans (Finset.subset_insert a s) hts)
        (hD.mono (Finset.Subset.trans (Finset.subset_insert a s) hts))
      obtain ⟨a₁, a₂, ha₁₂⟩ : ∃ x y : Verts n, a = s(x, y) :=
        Quot.inductionOn a (fun p : Verts n × Verts n => ⟨p.1, p.2, rfl⟩)
      set N : Finset (Sym2 (Verts n)) := s.filter (fun f => Shares f a) with hN
      set M : Finset (Sym2 (Verts n)) := (sepF L a).filter (fun f => f ∈ s) with hM
      have hsub' : s.filter (fun f => Shares f a) ⊆ L.filter (fun e' => Shares e' a) := by
        intro f hf
        have hf1 := Finset.mem_filter.mp hf
        refine Finset.mem_filter.mpr ⟨hts (show f ∈ insert a s by
          exact Finset.mem_insert.mpr (Or.inr hf1.1)), hf1.2⟩
      have hNcard : N.card ≤ 2 * D := by
        rw [hN]
        exact le_trans (Finset.card_le_card hsub')
          ((show a = s(a₁, a₂) from ha₁₂) ▸ card_shares_le hD a₁ a₂)
      have hMcard : M.card ≤ 2 * D * D := by
        rw [hM]
        exact le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (card_sepF_le hD a)
      have hNMsub : N ∪ M ⊆ s := by
        intro f hf
        rcases Finset.mem_union.mp hf with hf | hf
        · rw [hN] at hf
          exact (Finset.mem_filter.mp hf).1
        · rw [hM] at hf
          exact (Finset.mem_filter.mp hf).2
      have hcard : (N ∪ M).card < 2 * D * D + 2 * D + 1 := by
        have h1 := Finset.card_union_le N M
        omega
      obtain ⟨j, hj⟩ := exists_free_colour' (fun e he => g₀ ⟨e, he⟩) (N ∪ M) hNMsub hcard
      have ins : ∀ (x : {e : Sym2 (Verts n) // e ∈ insert a s}), x.1 ≠ a → x.1 ∈ s := by
        intro x hx
        rcases Finset.mem_insert.mp x.2 with h2 | h2
        · exact absurd h2 hx
        · exact h2
      have insL : ∀ (x : {e : Sym2 (Verts n) // e ∈ insert a s}), x.1 ≠ a → x.1 ∈ L :=
        fun x hx => hts (show x.1 ∈ insert a s from Finset.mem_insert.mpr (Or.inr (ins x hx)))
      let gfun : {e : Sym2 (Verts n) // e ∈ insert a s} → Fin (2 * D * D + 2 * D + 1) :=
        fun x => if h : x.1 = a then j else g₀ ⟨x.1, ins x h⟩
      refine ⟨gfun, fun x y hxy hrel => ?_⟩
      by_cases hxa : x.1 = a
      · have hyne : y.1 ≠ a := fun hy => hxy (Subtype.ext (hxa.trans hy.symm))
        simp only [gfun, dite_eq_left hxa, dite_eq_right hyne]
        intro hcon
        refine hj y.1 ?_ hcon.symm
        rcases hrel with hrel | hrel
        · refine Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨ins y hyne, ?_⟩))
          exact hrel.symm.mono_edge hxa.symm
        · refine Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨?_, ins y hyne⟩))
          exact mem_sepF (insL y hyne) (show Sep L a y.1 from by rwa [hxa] at hrel)
      · by_cases hya : y.1 = a
        · simp only [gfun, dite_eq_right hxa, dite_eq_left hya]
          refine hj x.1 ?_
          rcases hrel with hrel | hrel
          · refine Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨ins x hxa, ?_⟩))
            exact hrel.mono_edge hya.symm
          · refine Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨?_, ins x hxa⟩))
            exact mem_sepF (insL x hxa)
              (Sep.symm (show Sep L x.1 a from by rwa [hya] at hrel))
        · simp only [gfun, dite_eq_right hxa, dite_eq_right hya]
          refine hg₀ ⟨x.1, ins x hxa⟩ ⟨y.1, ins y hya⟩ ?_ hrel
          intro hq
          have hval : x.1 = y.1 :=
            congrArg (fun z : {e : Sym2 (Verts n) // e ∈ s} => (z.1 : Sym2 (Verts n))) hq
          exact hxy (@Subtype.ext_iff (Sym2 (Verts n)) (fun e => e ∈ insert a s) x y |>.mpr hval)
  exact key L (Finset.Subset.refl _) hD

/-- **THE DETERMINISTIC HALF OF THE SECOND STAGE.**  A leftover graph of maximum degree `D`
carries a fresh colouring which is proper (`A_{e,f,i}` / `B₁`) **and** avoids the bad event `B_D`
(`B₂`), with `2D² + 2D + 1` fresh colours and **no probability at all**.

This is the main result of the round: the local lemma of arXiv:2208.12563 §4 / arXiv:2207.02920 §12
is needed for the events `C_{D,i}` (`B₃`) only; the event `B_D` is a `Θ(Δ(L)²)`-coloured
deterministic constraint. -/
theorem second_stage_of_sparseL {n k D : ℕ} {c₀ : Col n k} {L : Finset (Sym2 (Verts n))}
    (hD : SparseL L D) (hf : L ⊆ edgeFinset (Finset.univ : Finset (Verts n))) :
    ∃ (g : ∀ e, e ∈ L → Fin (2 * D * D + 2 * D + 1)),
      Proper (extendColDep c₀ L g) L ∧ NoAltCycle (extendColDep c₀ L g) L := by
  obtain ⟨ĝ, hĝ⟩ := star_greedy hD hf
  refine ⟨fun e h => ĝ ⟨e, h⟩, ⟨?_, ?_⟩⟩
  · intro e he e' he' hne hsh
    rw [extendColDep_of_mem he, extendColDep_of_mem he']
    intro hcon
    apply hĝ ⟨e, he⟩ ⟨e', he'⟩ (fun hv => hne (congrArg Subtype.val hv)) (Or.inl hsh)
    apply Fin.ext
    exact congrArg Fin.val (freshCol_inj _ _ hcon)
  · refine noAltCycle_of_starProper ⟨?_, ?_⟩
    · intro e he e' he' hne hsh
      rw [extendColDep_of_mem he, extendColDep_of_mem he']
      intro hcon
      apply hĝ ⟨e, he⟩ ⟨e', he'⟩ (fun hv => hne (congrArg Subtype.val hv)) (Or.inl hsh)
      apply Fin.ext
      exact congrArg Fin.val (freshCol_inj _ _ hcon)
    · intro e f he hf hsep
      rw [extendColDep_of_mem he, extendColDep_of_mem hf]
      intro hcon
      apply hĝ ⟨e, he⟩ ⟨f, hf⟩
      · intro hcon
        obtain ⟨a, b, p, q, h4, he', hf', hm⟩ := hsep
        have heq : e = f := congrArg Subtype.val hcon
        have hEq : s(a, b) = s(p, q) := he'.symm.trans (heq.trans hf')
        rcases sym2_inj hEq with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · exact absurd e1 h4.2.1
        · exact absurd e1 h4.2.2.1
      · exact Or.inr hsep
      · apply Fin.ext
        exact congrArg Fin.val (freshCol_inj _ _ hcon)

/-- **THE DETERMINISTIC HALF OF THE SECOND STAGE, FOR THE LEFTOVER OF A COLOURING.** -/
theorem second_stage_of_leftover {n k D : ℕ} {c₀ : Col n k} (hD : SparseL (leftover c₀) D) :
    ∃ (g : ∀ e, e ∈ leftover c₀ → Fin (2 * D * D + 2 * D + 1)),
      Proper (extendColDep c₀ (leftover c₀) g) (leftover c₀) ∧
      NoAltCycle (extendColDep c₀ (leftover c₀) g) (leftover c₀) :=
  second_stage_of_sparseL hD (fun _ he => (mem_leftover.mp he).1)

/-! ### The composition: the required theorem with ONE probabilistic hypothesis left -/

/-- **THE VERIFICATION LEMMA WITH THE BAD EVENT `B_D` HANDLED DETERMINISTICALLY.**  If the
extension is proper *and* respects the separated pairs of leftover edges, then the extension is a
`Design`, hence admissible.  Compared with `Stage2.admissible_of_stage2` the hypothesis
`NoAltCycle` is replaced by the separated-pair condition, which this file proves to be achievable
by a greedy colouring. -/
theorem admissible_of_star {n k K : ℕ} {c₀ : Col n k} {c : Col n (k + K)}
    {L : Finset (Sym2 (Verts n))} (hE : Extends (liftCol c₀ (Nat.le_add_right k K)) c L)
    (hP : Proper c L) (hS : ∀ e f : Sym2 (Verts n), e ∈ L → f ∈ L → Sep L e f → c e ≠ c f)
    (hD₀ : Design c₀) (hLC : LeafClosed c₀ L) (hCF : NoCrossFresh c₀ c L) (hn : 4 ≤ n) :
    Admissible c :=
  admissible_of_stage2 hE hP hD₀ hLC (noAltCycle_of_starProper ⟨hP, hS⟩) hCF hn

/-- **THE PUBLISHED CONSTRUCTION, WITH `B_D` DELETED FROM ITS HYPOTHESES.**  For every `δ > 0` and
all large `m ≡ 1 (mod 6)`: a first-stage `k`-colouring `c₀` (a labelled-triangle system with disjoint
`(vertex, colour)` usage, no bad and no crossing four-set) whose leftover graph has maximum degree
`D`, together with a fresh colouring `g` of that leftover graph which is proper, respects the
separated pairs, and avoids `C_{D,i}`, bringing the total number of colours to at most
`5(m-1)/6 + δm/6`.

Note what is **not** a hypothesis: `NoAltCycle` — the bad event `B_D` follows from properness and
the separated-pair condition by `noAltCycle_of_starProper`; `Extends`, which holds automatically for
`extendColDep`; and leaf closure, which is free for a labelled-triangle system
(`Stage2.leafClosed_of_tri`).  Properness together with the separated-pair condition is
achievable by the greedy colouring of `second_stage_of_leftover` with `2D²+2D+1` fresh colours and
no probability.  So the only genuinely probabilistic content left is the hypergraph matching of the
first stage and the single bad-event family `C_{D,i}`. -/
def StarStageFamily : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ M D : ℕ, ∀ m : ℕ, M ≤ m → m % 6 = 1 →
    ∃ (k : ℕ) (c₀ : Col m k), Covers c₀ ∧ PairFree c₀ ∧ NoCrossFour c₀ ∧ NoBadFour c₀ ∧
      SparseL (leftover c₀) D ∧
      (6 : ℝ) * ((k + (2 * D * D + 2 * D + 1) : ℕ) : ℝ) ≤ 5 * ((m - 1 : ℕ) : ℝ) + δ * (m : ℝ) ∧
      ∃ (g : ∀ e, e ∈ leftover c₀ → Fin (2 * D * D + 2 * D + 1)),
        Proper (extendColDep c₀ (leftover c₀) g) (leftover c₀) ∧
        (∀ e f : Sym2 (Verts m), e ∈ leftover c₀ → f ∈ leftover c₀ →
          Sep (leftover c₀) e f → (extendColDep c₀ (leftover c₀) g) e ≠
            (extendColDep c₀ (leftover c₀) g) f) ∧
        NoCrossFresh c₀ (extendColDep c₀ (leftover c₀) g) (leftover c₀)

/-- **THE TWO STAGES COMPOSE, WITH `B_D` EXCLUDED DETERMINISTICALLY.** -/
theorem SlackFamily.of_star (hfam : StarStageFamily) : SlackFamily := by
  rw [StarStageFamily] at hfam
  intro δ hδ
  obtain ⟨M, D, hM⟩ := hfam δ hδ
  refine ⟨max M 4, fun m hMm hm => ?_⟩
  obtain ⟨k, c₀, hC, hP, hX, hB, hSp, hk, g, hPr, hS, hCF⟩ := hM m (by omega) hm
  have hT : Tile c₀ := tile_of_tri hC hP (by omega)
  have hPk : Packed c₀ := packed_of_tri hC hP (by omega)
  have hLC : LeafClosed c₀ (leftover c₀) := leafClosed_of_tri hC hP
  have hE : Extends (liftCol c₀ (Nat.le_add_right k (2 * D * D + 2 * D + 1)))
      (extendColDep c₀ (leftover c₀) g) (leftover c₀) :=
    Extends_extendColDep (c := c₀) (L := leftover c₀) (g := g)
  exact ⟨k + (2 * D * D + 2 * D + 1), extendColDep c₀ (leftover c₀) g,
    admissible_of_star hE hPr hS ⟨hT, hPk, hX, hB⟩ hLC hCF (by omega), hk⟩

/-- **THE REQUIRED THEOREM `jsp_000140_main`, WITH ONLY ONE BAD-EVENT FAMILY PROBABILISTIC.** -/
theorem jsp_000140_main_of_star_stage_family (hfam : StarStageFamily) : jsp_000140_target :=
  jsp_000140_main_of_slack_family (SlackFamily.of_star hfam)

end JSP140