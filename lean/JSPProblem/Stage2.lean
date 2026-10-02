import JSPProblem.Second

/-!
# JSP-000140 — the two stages of the published construction, composed exactly

Round 30 formalised the second stage through `Leftover.Rainbow` (a *rainbow* second stage: pairwise
distinct fresh colours inside every four-set).  Round 31 read both papers and corrected the
interface: the second stage only has to be **proper** (`Second.Proper`, i.e. every fresh colour
class on the leftover graph `L` is a matching — the bad events `A_{e,f,i}` of arXiv:2208.12563 §4
resp. `B₁` of arXiv:2207.02920 §12), and `Second.rainbow_of_sparse_leftover` proved that this
deterministic half always exists with `2Δ(L)+1 = 2n^{1-δ}+1 = o(n)` fresh colours.

What is left of the second stage is exactly **two** families of bad events:

* **`B_D` (JM §4) / `B₂` (BCDP §12)** — for a 4-cycle `D` of *uncoloured* edges, the event that `D`
  receives exactly two colours;
* **`C_{D,i}` (JM §4) / `B₃` (BCDP §12)** — for a 4-cycle whose two *opposite* edges are uncoloured
  and get the same colour `i`, the event that the other two opposite edges are coloured alike in
  Phase 1.

**This file proves that these two events, together with three conditions the *first* stage provides
for free, are exactly what is needed.**  It is the composition theorem `admissible_of_stage2`, whose
case analysis round 31 worked out but could not fit into that round's budget.  Nothing here is
probabilistic: the local lemma of the two papers is the only place where `NoAltCycle` and
`NoCrossFresh` are used, and this file shows that they are *sufficient* — no other probabilistic
content is needed.

## The hypotheses

* `Extends c₀ c L` (`Leftover.Extends`) — the first-stage colours are kept off `L` and the fresh ones
  occur exactly on `L`.  This gives the **colour dichotomy** used throughout: a colour `< k` occurs
  on covered edges only, a colour `≥ k` on leftover edges only (`mem_L_of_fresh`,
  `not_mem_L_of_old`, `sub_Nbrs_old`);
* `LeafClosed c₀ L` (**(P1)**) — the **leaf edge of every first-stage two-edge path is covered**.
  This is where the labelled-triangle encoding of arXiv:2208.12563 §4 enters, and it is *free* for
  it: `leafClosed_of_tri` proves it for the leftover of any labelled-triangle system with the
  matching condition.  It is the reason why a fresh crossing pair cannot be combined with a
  first-stage two-edge path on one clique;
* `Tile c₀`, `Packed c₀`, `NoCrossFour c₀`, `NoBadFour c₀` — the four local conditions of
  `Criterion.Design` for the first stage, all of them *free* for the published shape
  (`Triangles.tile_of_tri`, `Triangles.packed_of_tri`, plus the two four-set conditions the
  construction verifies);
* `Proper c L` — the second stage, deterministic (`Second.rainbow_of_sparse_leftover`);
* `NoAltCycle c L` (**(P2)** = the event `B_D` / `B₂`);
* `NoCrossFresh c₀ c L` (**(P3)** = the event `C_{D,i}` / `B₃`).

## The conclusions

* `tile_of_stage2`, `packed_of_stage2`, `noCrossFour_of_stage2`, `noBadFour_of_stage2`,
  **`design_of_stage2`** — the *extension* `c` is itself a `Design` colouring, i.e. it satisfies the
  four local conditions of `Criterion.design_iff_admissible`;
* **`admissible_of_stage2`** — hence `Admissible c`: the catalog condition of `JSP-000140` holds on
  `K_n`.  This is the verification lemma the second stage of both papers needs, in the exact form in
  which the papers state it;
* `StageFamily`, `jsp_000140_main_of_stage_family` — the required theorem `jsp_000140_main`, reduced
  to the existence of the published two-stage construction with the two bad-event families excluded.
  `StageFamily_of_ext` shows this is *weaker* than round 30's `ExtFamily` (which demanded a
  `Rainbow` second stage, i.e. `|L|` fresh colours instead of `2n^{1-δ}+1`), so nothing of rounds
  29–31 is lost.

The case analysis behind `admissible_of_stage2`: a four-set `S` splits into its covered edges `E⁰`
and its leftover edges `E¹`, and `Second.colorsOn_ext_card` identifies the number of colours of the
extension on `S` with `|image c₀ on E⁰| + |image c on E¹|`.  A violating clique therefore has few
colours on both parts, and (fresh classes being matchings) the doubled fresh pairs are *crossing*:

| `|P|` | `|Q|` | obstruction |
|---|---|---|
| 0 | ≤ 4 | two fresh classes are doubled: a two-coloured 4-cycle of `L` — **(P2)** |
| 1 | ≤ 3 | a doubled fresh pair whose complement is a phase-1 monochromatic pair — **(P3)**; five leftover edges give **(P2)** |
| 2 | ≤ 2 | four covered edges: `Packed`/`NoBadFour`/`NoCrossFour` of the first stage; three covered edges: **(P3)**; two covered edges: **(P2)** |
| 3 | 1 | the doubled fresh pair is crossed over a phase-1 monochromatic pair — **(P3)** |
| 4 | 0 | the clique is entirely covered, so `c = c₀` there — excluded by the first stage itself |

which is exactly the content of the four theorems below, phrased in the local language of
`Criterion.Crossed`, `twoA` and `pathSet`.
-/

set_option maxHeartbeats 8000000
set_option linter.unusedVariables false

namespace JSP140

attribute [local instance] Classical.propDecidable

variable {n k : ℕ}

/-! ### The two remaining bad events of the second stage, and leaf closure -/

/-- **THE COLOURS OF A 4-CYCLE.** -/
def cycleColours {n K : ℕ} (c : Col n K) (a b p q : Verts n) : Finset (Fin K) :=
  insert (c s(a, b)) (insert (c s(b, p)) (insert (c s(p, q)) (insert (c s(q, a)) ∅)))

/-- A three-element finset of vertices. -/
def threeFin {n : ℕ} (a b c : Verts n) : Finset (Verts n) :=
  Insert.insert a (Insert.insert b (Insert.insert c (∅ : Finset (Verts n))))

@[simp] theorem mem_threeFin {n : ℕ} {a b c z : Verts n} :
    z ∈ threeFin a b c ↔ z = a ∨ z = b ∨ z = c := by
  simp [threeFin]

/-- A four-element finset of vertices. -/
def fourFin {n : ℕ} (a b c d : Verts n) : Finset (Verts n) :=
  Insert.insert a (Insert.insert b (Insert.insert c (Insert.insert d (∅ : Finset (Verts n)))))

/-- A two-element finset of vertices. -/
def twoFin {n : ℕ} (a b : Verts n) : Finset (Verts n) :=
  Insert.insert a (Insert.insert b (∅ : Finset (Verts n)))

@[simp] theorem mem_twoFin {n : ℕ} {a b z : Verts n} : z ∈ twoFin a b ↔ z = a ∨ z = b := by
  simp [twoFin]

@[simp] theorem mem_fourFin {n : ℕ} {a b c d z : Verts n} :
    z ∈ fourFin a b c d ↔ z = a ∨ z = b ∨ z = c ∨ z = d := by
  simp [fourFin]

/-- **(P1) LEAF CLOSURE OF THE FIRST STAGE.**  The edge joining the two leaves of a first-stage
two-edge path is never a leftover edge.

In the published construction this is *free*: a two-edge path `s(u,p), s(u,q)` of colour `i` with
centre `u` is the pair of path edges of the labelled triangle `(u, p, q)`, and its leaf edge
`s(p, q)` is that triangle's *opposite* edge, which the hypergraph matching of arXiv:2208.12563 §4
covers (`leafClosed_of_tri` below).  So `L` never contains a leaf edge. -/
def LeafClosed {n k : ℕ} (c₀ : Col n k) (L : Finset (Sym2 (Verts n))) : Prop :=
  ∀ (i : Fin k) (v p q : Verts n), Nbrs c₀ i v = insert p (insert q ∅) → s(p, q) ∉ L

/-- **(P2) NO TWO-COLOURED 4-CYCLE OF LEFTOVER EDGES** — the bad event `B_D` of arXiv:2208.12563 §4
resp. `B₂` of arXiv:2207.02920 §12: a 4-cycle of *uncoloured* edges receiving at most two colours.
Such a cycle, together with the two diagonals, spans at most four colours, so it is a violating
clique. -/
def NoAltCycle {n K : ℕ} (c : Col n K) (L : Finset (Sym2 (Verts n))) : Prop :=
  ∀ {a b p q : Verts n}, FourDistinct a b p q →
    s(a, b) ∈ L → s(b, p) ∈ L → s(p, q) ∈ L → s(q, a) ∈ L →
    3 ≤ (cycleColours c a b p q).card

/-- **(P3) NO CROSSING FRESH PAIR OVER A PHASE-1 MONOCHROMATIC PAIR** — the bad event `C_{D,i}` of
arXiv:2208.12563 §4 resp. `B₃` of arXiv:2207.02920 §12: two *uncoloured* opposite edges of a 4-cycle
receiving the same fresh colour, while the other two opposite edges are coloured alike in Phase 1.
(Both of those are `∉ L`, hence covered, hence their Phase-1 colours are the colours of the
extension there.) -/
def NoCrossFresh {n k K : ℕ} (c₀ : Col n k) (c : Col n (k + K))
    (L : Finset (Sym2 (Verts n))) : Prop :=
  ∀ {a b p q : Verts n}, FourDistinct a b p q →
    s(a, b) ∈ L → s(p, q) ∈ L → c s(a, b) = c s(p, q) →
    s(a, q) ∉ L → s(b, p) ∉ L → c₀ s(a, q) ≠ c₀ s(b, p)

/-- **THE BAD EVENT `B_D` NEVER HAPPENS.**  A 4-cycle of leftover edges whose four colours all lie
in a two-element set contradicts `NoAltCycle`. -/
theorem NoAltCycle.no_two {n K : ℕ} {c : Col n K} {L : Finset (Sym2 (Verts n))}
    (h : NoAltCycle c L) {a b p q : Verts n} (h4 : FourDistinct a b p q)
    (h1 : s(a, b) ∈ L) (h2 : s(b, p) ∈ L) (h3 : s(p, q) ∈ L) (h4' : s(q, a) ∈ L)
    {x y : Fin K} (hxy : x ≠ y)
    (hc1 : c s(a, b) = x ∨ c s(a, b) = y) (hc2 : c s(b, p) = x ∨ c s(b, p) = y)
    (hc3 : c s(p, q) = x ∨ c s(p, q) = y) (hc4 : c s(q, a) = x ∨ c s(q, a) = y) : False := by
  have hle : (cycleColours c a b p q).card ≤ 2 := by
    have hsub : cycleColours c a b p q ⊆ ({x, y} : Finset (Fin K)) := by
      intro z hz
      simp only [cycleColours, Finset.mem_insert, Finset.mem_singleton, or_false] at hz
      rcases hz with hz | hz | hz | hz | hz
      · rw [hz]; simpa using hc1
      · rw [hz]; simpa using hc2
      · rw [hz]; simpa using hc3
      · rw [hz]; simpa using hc4
      · exact absurd hz (by simp)
    have hcard : ({x, y} : Finset (Fin K)).card = 2 := Finset.card_pair hxy
    have hle' := Finset.card_le_card hsub
    rw [hcard] at hle'
    omega
  have h5 := h h4 h1 h2 h3 h4'
  omega

/-- **THE BAD EVENT `C_{D,i}` NEVER HAPPENS.** -/
theorem NoCrossFresh.no_cross {n k K : ℕ} {c₀ : Col n k} {c : Col n (k + K)}
    {L : Finset (Sym2 (Verts n))} (h : NoCrossFresh c₀ c L) {a b p q : Verts n}
    (h4 : FourDistinct a b p q) (h1 : s(a, b) ∈ L) (h2 : s(p, q) ∈ L) (hc : c s(a, b) = c s(p, q))
    (h3 : s(a, q) ∉ L) (h4' : s(b, p) ∉ L) (hc0 : c₀ s(a, q) = c₀ s(b, p)) : False :=
  h h4 h1 h2 hc h3 h4' hc0

/-! ### The shape of a `K₄` -/

/-- Two distinct members of a finset of cardinality at least two. -/
private theorem exists_two_mem {α : Type*} [DecidableEq α] {s : Finset α} (h : 2 ≤ s.card) :
    ∃ x y : α, x ≠ y ∧ x ∈ s ∧ y ∈ s := by
  by_cases he : s.card = 2
  · obtain ⟨x, y, hxy, hs⟩ := Finset.card_eq_two.mp he
    rw [hs] at h ⊢
    exact ⟨x, y, hxy, by simp, by simp⟩
  · have hne : s.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hE
      rw [hE, Finset.card_empty] at h
      omega
    obtain ⟨x, hx⟩ := hne
    have hrem : (s.erase x).card = s.card - 1 := Finset.card_erase_of_mem hx
    have hrem2 : 1 ≤ (s.erase x).card := by omega
    obtain ⟨y, hy⟩ := Finset.card_pos.mp hrem2
    exact ⟨x, y, Ne.symm (Finset.mem_erase.mp hy).1, hx, (Finset.mem_erase.mp hy).2⟩

/-- The endpoints of an edge of `edgeFinset S`. -/
private theorem exists_mk {n : ℕ} {S : Finset (Verts n)} {e : Sym2 (Verts n)}
    (he : e ∈ edgeFinset S) :
    ∃ x y : Verts n, e = s(x, y) ∧ x ∈ S ∧ y ∈ S ∧ x ≠ y := by
  obtain ⟨a, b, hab⟩ : ∃ a b : Verts n, e = s(a, b) :=
    Quot.inductionOn e (fun p : Verts n × Verts n => ⟨p.1, p.2, rfl⟩)
  obtain ⟨h1, h2⟩ := mem_edgeFinset.mp (hab ▸ he)
  have hmem := Finset.mem_sym2_iff.mp h1
  exact ⟨a, b, hab, hmem a (Sym2.mem_mk_left a b), hmem b (Sym2.mem_mk_right a b), h2 a b rfl⟩

/-- `s(x,y) = s(u,v)` when the endpoints agree. -/
private theorem sym2_congr {n : ℕ} {a b c d : Verts n} (h1 : a = c) (h2 : b = d) :
    s(a, b) = s(c, d) := by
  rw [h1, h2]

/-- **THE SIX EDGES OF A `K₄`.**  Every edge of the complete graph on a four-element set is one of
the six pairs of its vertices. -/
private theorem mem_six_of_mem_edgeFinset {n : ℕ} {a b c d : Verts n} (h : FourDistinct a b c d)
    {S : Finset (Verts n)} (hS : S = fourSet a b c d) {e : Sym2 (Verts n)} (he : e ∈ edgeFinset S) :
    e = s(a, b) ∨ e = s(a, c) ∨ e = s(a, d) ∨ e = s(b, c) ∨ e = s(b, d) ∨ e = s(c, d) := by
  obtain ⟨x, y, hxy, hxS, hyS, hne⟩ := exists_mk he
  rw [hS] at hxS hyS
  have mk : ∀ (p q : Verts n), x = p → y = q → e = s(p, q) :=
    fun p q hp hq => hxy.trans (sym2_congr hp hq)
  rcases (mem_fourSet h).mp hxS with hxa' | hxb' | hxc' | hxd' <;>
    rcases (mem_fourSet h).mp hyS with hya' | hyb' | hyc' | hyd'
  · exact (hne (hxa'.trans hya'.symm)).elim
  · exact Or.inl (mk a b hxa' hyb')
  · exact Or.inr (Or.inl (mk a c hxa' hyc'))
  · exact Or.inr (Or.inr (Or.inl (mk a d hxa' hyd')))
  · exact Or.inl ((mk b a hxb' hya').trans Sym2.eq_swap)
  · exact (hne (hxb'.trans hyb'.symm)).elim
  · exact Or.inr (Or.inr (Or.inr (Or.inl (mk b c hxb' hyc'))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (mk b d hxb' hyd')))))
  · exact Or.inr (Or.inl ((mk c a hxc' hya').trans Sym2.eq_swap))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ((mk c b hxc' hyb').trans Sym2.eq_swap))))
  · exact (hne (hxc'.trans hyc'.symm)).elim
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (mk c d hxc' hyd')))))
  · exact Or.inr (Or.inr (Or.inl ((mk d a hxd' hya').trans Sym2.eq_swap)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((mk d b hxd' hyb').trans Sym2.eq_swap)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ((mk d c hxd' hyc').trans Sym2.eq_swap)))))
  · exact (hne (hxd'.trans hyd'.symm)).elim

/-- **AN EDGE VERTEX-DISJOINT FROM `s(x, y)` AVOIDS BOTH `x` AND `y`.** -/
private theorem mem_of_avoid {n : ℕ} {f e : Sym2 (Verts n)}
    (hd : ∀ v, v ∈ f → v ∉ e) {x y : Verts n} (h : f = s(x, y)) : x ∉ e ∧ y ∉ e :=
  ⟨fun hmem => hd x (h ▸ Sym2.mem_mk_left x y) hmem,
    fun hmem => hd y (h ▸ Sym2.mem_mk_right x y) hmem⟩

/-- **THE COMPLEMENT OF AN EDGE IN A `K₄`.**  If `x, y, u, v` are the four vertices of a
four-set, then the only edge of `K[S]` vertex-disjoint from `s(x,y)` is `s(u,v)`. -/
private theorem complement_edge {n : ℕ} {S : Finset (Verts n)} {x y u v : Verts n}
    {f f' : Sym2 (Verts n)} (hS4 : fourFin x y u v = S) (hf : f = s(x, y)) (hf' : f' ∈ edgeFinset S)
    (hd' : ∀ w : Verts n, w ∈ f → w ∉ f') : f' = s(u, v) := by
  obtain ⟨p, q, hpq, hpS, hqS, hpq'⟩ := exists_mk hf'
  have memfp : p ∈ f' := hpq ▸ Sym2.mem_mk_left p q
  have memfq : q ∈ f' := hpq ▸ Sym2.mem_mk_right p q
  have hpx : p ≠ x := fun hh => hd' x (hf ▸ Sym2.mem_mk_left x y) (hh ▸ memfp)
  have hpy : p ≠ y := fun hh => hd' y (hf ▸ Sym2.mem_mk_right x y) (hh ▸ memfp)
  have hqx : q ≠ x := fun hh => hd' x (hf ▸ Sym2.mem_mk_left x y) (hh ▸ memfq)
  have hqy : q ≠ y := fun hh => hd' y (hf ▸ Sym2.mem_mk_right x y) (hh ▸ memfq)
  have hsub2 : twoFin x y ∪ twoFin u v = S := by
    rw [← hS4]
    ext z
    simp only [Finset.mem_union, mem_twoFin, mem_fourFin, fourFin, Finset.mem_insert,
      Finset.mem_singleton, or_false]
    tauto
  have key : ∀ z : Verts n, z ∈ S → z ≠ x → z ≠ y → z = u ∨ z = v := by
    intro z hz hzx hzy
    rcases Finset.mem_union.mp (hsub2.symm ▸ hz) with h' | h'
    · have hne : z ∉ twoFin x y := fun hh => (mem_twoFin.mp hh).elim hzx hzy
      exact (hne h').elim
    · rw [mem_twoFin] at h'
      exact h'
  have hmem : p = u ∨ p = v := key p hpS hpx hpy
  have hmem' : q = u ∨ q = v := key q hqS hqx hqy
  rcases hmem with hp' | hp' <;> rcases hmem' with hq' | hq'
  · exact (hpq' (hp'.trans hq'.symm)).elim
  · exact hpq.trans (sym2_congr hp' hq')
  · have hh : f' = s(v, u) := hpq.trans (sym2_congr hp' hq')
    exact hh.trans Sym2.eq_swap
  · exact (hpq' (hp'.trans hq'.symm)).elim

/-- **THE OPPOSITE EDGE OF `s(a,b)` IS `(c, d`.** -/
private theorem partner_ab {n : ℕ} {a b c d : Verts n} (h : FourDistinct a b c d)
    {S : Finset (Verts n)} (hS : S = fourSet a b c d) {f f' : Sym2 (Verts n)}
    (hf : f ∈ edgeFinset S) (hf' : f' ∈ edgeFinset S) (hd' : ∀ v, v ∈ f → v ∉ f')
    (hfe : f = s(a, b)) : f' = s(c, d) := by
  have hS4 : fourFin a b c d = S := by
    rw [hS]
    ext z
    simp only [fourSet, mem_fourFin, fourFin, Finset.mem_insert, Finset.mem_singleton, or_false] <;>
      tauto
  exact complement_edge hS4 hfe hf' hd'

/-- **THE OPPOSITE EDGE OF `s(a,c)` IS `(b, d`.** -/
private theorem partner_ac {n : ℕ} {a b c d : Verts n} (h : FourDistinct a b c d)
    {S : Finset (Verts n)} (hS : S = fourSet a b c d) {f f' : Sym2 (Verts n)}
    (hf : f ∈ edgeFinset S) (hf' : f' ∈ edgeFinset S) (hd' : ∀ v, v ∈ f → v ∉ f')
    (hfe : f = s(a, c)) : f' = s(b, d) := by
  have hS4 : fourFin a c b d = S := by
    rw [hS]
    ext z
    simp only [fourSet, mem_fourFin, fourFin, Finset.mem_insert, Finset.mem_singleton, or_false] <;>
      tauto
  exact complement_edge hS4 hfe hf' hd'

/-- **THE OPPOSITE EDGE OF `s(a,d)` IS `(b, c`.** -/
private theorem partner_ad {n : ℕ} {a b c d : Verts n} (h : FourDistinct a b c d)
    {S : Finset (Verts n)} (hS : S = fourSet a b c d) {f f' : Sym2 (Verts n)}
    (hf : f ∈ edgeFinset S) (hf' : f' ∈ edgeFinset S) (hd' : ∀ v, v ∈ f → v ∉ f')
    (hfe : f = s(a, d)) : f' = s(b, c) := by
  have hS4 : fourFin a d b c = S := by
    rw [hS]
    ext z
    simp only [fourSet, mem_fourFin, fourFin, Finset.mem_insert, Finset.mem_singleton, or_false] <;>
      tauto
  exact complement_edge hS4 hfe hf' hd'

/-- **THE OPPOSITE EDGE OF `s(b,c)` IS `(a, d`.** -/
private theorem partner_bc {n : ℕ} {a b c d : Verts n} (h : FourDistinct a b c d)
    {S : Finset (Verts n)} (hS : S = fourSet a b c d) {f f' : Sym2 (Verts n)}
    (hf : f ∈ edgeFinset S) (hf' : f' ∈ edgeFinset S) (hd' : ∀ v, v ∈ f → v ∉ f')
    (hfe : f = s(b, c)) : f' = s(a, d) := by
  have hS4 : fourFin b c a d = S := by
    rw [hS]
    ext z
    simp only [fourSet, mem_fourFin, fourFin, Finset.mem_insert, Finset.mem_singleton, or_false] <;>
      tauto
  exact complement_edge hS4 hfe hf' hd'

/-- **THE OPPOSITE EDGE OF `s(b,d)` IS `(a, c`.** -/
private theorem partner_bd {n : ℕ} {a b c d : Verts n} (h : FourDistinct a b c d)
    {S : Finset (Verts n)} (hS : S = fourSet a b c d) {f f' : Sym2 (Verts n)}
    (hf : f ∈ edgeFinset S) (hf' : f' ∈ edgeFinset S) (hd' : ∀ v, v ∈ f → v ∉ f')
    (hfe : f = s(b, d)) : f' = s(a, c) := by
  have hS4 : fourFin b d a c = S := by
    rw [hS]
    ext z
    simp only [fourSet, mem_fourFin, fourFin, Finset.mem_insert, Finset.mem_singleton, or_false] <;>
      tauto
  exact complement_edge hS4 hfe hf' hd'

/-- **THE OPPOSITE EDGE OF `s(c,d)` IS `(a, b`.** -/
private theorem partner_cd {n : ℕ} {a b c d : Verts n} (h : FourDistinct a b c d)
    {S : Finset (Verts n)} (hS : S = fourSet a b c d) {f f' : Sym2 (Verts n)}
    (hf : f ∈ edgeFinset S) (hf' : f' ∈ edgeFinset S) (hd' : ∀ v, v ∈ f → v ∉ f')
    (hfe : f = s(c, d)) : f' = s(a, b) := by
  have hS4 : fourFin c d a b = S := by
    rw [hS]
    ext z
    simp only [fourSet, mem_fourFin, fourFin, Finset.mem_insert, Finset.mem_singleton, or_false] <;>
      tauto
  exact complement_edge hS4 hfe hf' hd'

/-- **TWO OF THREE.**  If `p ≠ q` are two members of a three-element set of pairwise distinct
vertices and neither is `r`, then they are the other two, `s` and `t`, in some order. -/
private theorem two_of_three {n : ℕ} {r s t p q : Verts n} (hp : p = r ∨ p = s ∨ p = t)
    (hq : q = r ∨ q = s ∨ q = t) (hpq : p ≠ q) (hne : r ≠ p) (hne' : r ≠ q) :
    (p = s ∧ q = t) ∨ (p = t ∧ q = s) := by
  have hpr : p ≠ r := Ne.symm hne
  have hqr : q ≠ r := Ne.symm hne'
  have strip : ∀ z : Verts n, z = r ∨ z = s ∨ z = t → z ≠ r → z = s ∨ z = t := by
    intro z hz hzr
    rcases hz with hz | hz | hz
    · exact absurd hz hzr
    · exact Or.inl hz
    · exact Or.inr hz
  rcases strip p hp hpr with hp' | hp'
  · rcases strip q hq hqr with hq' | hq'
    · exact (hpq (hp'.trans hq'.symm)).elim
    · exact Or.inl ⟨hp', hq'⟩
  · rcases strip q hq hqr with hq' | hq'
    · exact Or.inr ⟨hp', hq'⟩
    · exact (hpq (hp'.trans hq'.symm)).elim

/-- Rotating a three-way disjunction. -/
private theorem rot3 {n : ℕ} {r s t z : Verts n} (hz : z = s ∨ z = t ∨ z = r) :
    z = r ∨ z = s ∨ z = t := by
  rcases hz with hz | hz | hz
  · exact Or.inr (Or.inl hz)
  · exact Or.inr (Or.inr hz)
  · exact Or.inl hz

/-- **THE SHAPE OF A CROSSING PAIR.**  Two vertex-disjoint edges inside a `K₄` use all four
vertices of the clique. -/
private theorem four_of_disjoint {n K : ℕ} {c : Col n K} {S : Finset (Verts n)} (hS : S.card = 4)
    {i : Fin K} {e f : Sym2 (Verts n)} (he : e ∈ classIn c i S) (hf : f ∈ classIn c i S)
    (hdis : ∀ v, v ∈ e → v ∉ f) :
    ∃ (a b p q : Verts n), FourDistinct a b p q ∧ e = s(a, b) ∧ f = s(p, q) ∧
      S = fourSet a b p q := by
  obtain ⟨a, b, hab, haS, hbS, habne⟩ := exists_mk (mem_classIn.mp he).1
  obtain ⟨p, q, hpq', hpS, hqS, hpqne⟩ := exists_mk (mem_classIn.mp hf).1
  have ha : a ∉ f := hdis a (hab ▸ Sym2.mem_mk_left a b)
  have hb : b ∉ f := hdis b (hab ▸ Sym2.mem_mk_right a b)
  have memp : p ∈ f := by rw [hpq']; exact Sym2.mem_mk_left p q
  have memq : q ∈ f := by rw [hpq']; exact Sym2.mem_mk_right p q
  have hap : a ≠ p := fun hh => ha (hh ▸ memp)
  have haq : a ≠ q := fun hh => ha (hh ▸ memq)
  have hbp : b ≠ p := fun hh => hb (hh ▸ memp)
  have hbq : b ≠ q := fun hh => hb (hh ▸ memq)
  have h4 : FourDistinct a b p q := ⟨habne, hap, haq, hbp, hbq, hpqne⟩
  have hsub : fourSet a b p q ⊆ S := by
    intro z hz
    rcases (mem_fourSet h4).mp hz with hz | hz | hz | hz
    · rw [hz]; exact haS
    · rw [hz]; exact hbS
    · rw [hz]; exact hpS
    · rw [hz]; exact hqS
  refine ⟨a, b, p, q, h4, hab, hpq', ?_⟩
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [card_fourSet h4]; omega)).symm

/-- **THE COLOUR OF A NAMED EDGE.** -/
private lemma c_named {n K : ℕ} {c : Col n K} {a b : Verts n} {e : Sym2 (Verts n)} {i : Fin K}
    (h : e = s(a, b)) (hc : c e = i) : c s(a, b) = i := by rw [h] at hc; exact hc

/-- **THE COLOUR OF A NAMED EDGE, REVERSED.** -/
private lemma c_named' {n K : ℕ} {c : Col n K} {a b : Verts n} {e : Sym2 (Verts n)} {i : Fin K}
    (h : e = s(a, b)) (hc : c e = i) : c s(b, a) = i := by rw [h] at hc; rw [Sym2.eq_swap]; exact hc

/-- **THE PERMUTED FOUR-DISTINCTNESS.** -/
private lemma four_dist_comm {n : ℕ} {a b p q : Verts n} (h : FourDistinct a b p q) :
    FourDistinct a b q p :=
  ⟨h.1, h.2.2.1, h.2.1, h.2.2.2.2.1, h.2.2.2.1, h.2.2.2.2.2.symm⟩

/-- **A CROSSING PAIR IS ONE OF THE TWO OTHER MATCHINGS OF THE `K₄`.** -/
private lemma matching_case {n : ℕ} {a b p q : Verts n} (h4 : FourDistinct a b p q)
    {S : Finset (Verts n)} (hS : S = fourSet a b p q) {g t : Sym2 (Verts n)}
    (hg : g ∈ edgeFinset S) (ht : t ∈ edgeFinset S) (hab : g ≠ s(a, b))
    (hpq : g ≠ s(p, q)) (hdis : ∀ v : Verts n, v ∈ g → v ∉ t) :
    (g = s(a, p) ∧ t = s(b, q)) ∨ (g = s(a, q) ∧ t = s(b, p)) ∨
      (g = s(b, p) ∧ t = s(a, q)) ∨ (g = s(b, q) ∧ t = s(a, p)) := by
  rcases mem_six_of_mem_edgeFinset h4 hS hg with hg' | hg' | hg' | hg' | hg' | hg'
  · exact absurd hg' hab
  · exact Or.inl ⟨hg', partner_ac h4 hS hg ht hdis hg'⟩
  · exact Or.inr (Or.inl ⟨hg', partner_ad h4 hS hg ht hdis hg'⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hg', partner_bc h4 hS hg ht hdis hg'⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hg', partner_bd h4 hS hg ht hdis hg'⟩))
  · exact absurd hg' hpq

/-- **A TWO-COLOURED 4-CYCLE OF LEFTOVER EDGES IS EXCLUDED.** -/
private lemma alt_two {n K : ℕ} {c : Col n K} {L : Finset (Sym2 (Verts n))} (hAlt : NoAltCycle c L)
    {a b p q : Verts n} (h4 : FourDistinct a b p q) {i j : Fin K} (hij : i ≠ j)
    (h1 : s(a, b) ∈ L) (h2 : s(b, p) ∈ L) (h3 : s(p, q) ∈ L) (h4' : s(q, a) ∈ L)
    (hc1 : c s(a, b) = i) (hc2 : c s(b, p) = j) (hc3 : c s(p, q) = i) (hc4 : c s(q, a) = j) :
    False :=
  hAlt.no_two h4 h1 h2 h3 h4' hij (Or.inl hc1) (Or.inr hc2) (Or.inl hc3) (Or.inr hc4)



/-! ### The colour dichotomy of the two stages -/

/-- **THE OLD PALETTE EMBEDS IN THE EXTENDED ONE.** -/
def embed {k K : ℕ} (i : Fin k) : Fin (k + K) :=
  ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right k K)⟩

theorem embed_val {k K : ℕ} (i : Fin k) : ((embed (k := k) (K := K) i) : Fin (k + K)).val = i.val := rfl

/-- **AN OLD COLOUR OF THE EXTENSION IS THE FIRST-STAGE COLOUR OF THE EDGE.** -/
theorem agree_of_embed {n k K : ℕ} {c₀ : Col n k} {c : Col n (k + K)}
    {L : Finset (Sym2 (Verts n))} (hE : Extends (liftCol c₀ (Nat.le_add_right k K)) c L)
    {e : Sym2 (Verts n)} {j : Fin k} (he : e ∉ L) (hce : c e = embed j) : c₀ e = j := by
  have hx : (c₀ e).val = (j : ℕ) := by
    have h1 := hE.agree he
    have hz : ((liftCol c₀ (Nat.le_add_right k K) e) : Fin (k + K)).val = (j : ℕ) := by
      have := congrArg Fin.val (h1.symm.trans hce)
      simpa [liftCol, embed] using this
    simpa [liftCol, embed] using hz
  exact Fin.ext hx

/-- **A FIRST-STAGE COLOUR OF A COVERED EDGE IS THE OLD PALETTE COLOUR.** -/
theorem embed_of_agree {n k K : ℕ} {c₀ : Col n k} {c : Col n (k + K)}
    {L : Finset (Sym2 (Verts n))} (hE : Extends (liftCol c₀ (Nat.le_add_right k K)) c L)
    {e : Sym2 (Verts n)} {j : Fin k} (he : e ∉ L) (hce : c₀ e = j) : c e = embed j := by
  have h1 := hE.agree he
  have hz : ((liftCol c₀ (Nat.le_add_right k K) e) : Fin (k + K)).val = (j : ℕ) := by
    simp [liftCol]
    exact congrArg Fin.val hce
  have hx : ((c e) : Fin (k + K)).val = (embed (k := k) (K := K) j : Fin (k + K)).val := by
    rw [h1, embed_val]
    exact hz
  exact Fin.ext hx

/-- **TWO OLD COLOURS OF THE EXTENSION ON THE SAME COVERED EDGE AGREE.** -/
theorem eq_of_agree {n k K : ℕ} {c₀ : Col n k} {c : Col n (k + K)}
    {L : Finset (Sym2 (Verts n))} (hE : Extends (liftCol c₀ (Nat.le_add_right k K)) c L)
    {e : Sym2 (Verts n)} {i j : Fin k} (he : e ∉ L) (h1 : c e = embed i) (h2 : c e = embed j) :
    i = j := by
  apply Fin.ext
  have hx : ((embed (k := k) (K := K) i) : Fin (k + K)).val
      = (embed (k := k) (K := K) j : Fin (k + K)).val := by
    rw [h1] at h2
    exact congrArg Fin.val h2
  simpa [embed] using hx

/-- **THE FIRST-STAGE COLOUR CARRIED BY AN OLD COLOUR OF THE EXTENSION.** -/
def oldOf {k K : ℕ} (i : Fin (k + K)) (hi : i.val < k) : Fin k := ⟨i.val, hi⟩

/-- **A COLOUR `≥ k` OCCURS ONLY ON LEFTOVER EDGES.** -/
theorem mem_L_of_fresh {n k K : ℕ} {c₀ : Col n k} {c : Col n (k + K)}
    {L : Finset (Sym2 (Verts n))} (hE : Extends (liftCol c₀ (Nat.le_add_right k K)) c L)
    {e : Sym2 (Verts n)} {i : Fin (k + K)} (he : c e = i) (hi : k ≤ i.val) : e ∈ L := by
  refine (hE.2 e).mpr ?_
  rw [he]
  exact hi

/-- **A COLOUR `< k` OCCURS ONLY ON COVERED EDGES.** -/
theorem not_mem_L_of_old {n k K : ℕ} {c₀ : Col n k} {c : Col n (k + K)}
    {L : Finset (Sym2 (Verts n))} (hE : Extends (liftCol c₀ (Nat.le_add_right k K)) c L)
    {e : Sym2 (Verts n)} {i : Fin (k + K)} (he : c e = i) (hi : i.val < k) : e ∉ L := by
  intro hmem
  have h2 := hE.fresh hmem
  rw [he] at h2
  omega

/-- **THE FIRST-STAGE COLOUR-`i` NEIGHBOURS CONTAIN THE ONES OF THE EXTENSION.** -/
theorem sub_Nbrs_old {n k K : ℕ} {c₀ : Col n k} {c : Col n (k + K)} {L : Finset (Sym2 (Verts n))}
    (hE : Extends (liftCol c₀ (Nat.le_add_right k K)) c L) (i : Fin (k + K)) (hi : i.val < k)
    (v : Verts n) : Nbrs c i v ⊆ Nbrs c₀ (oldOf i hi) v := by
  intro a ha
  have hne : a ≠ v := (mem_Nbrs.mp ha).1
  have hci : c s(v, a) = i := (mem_Nbrs.mp ha).2
  have hnmem : s(v, a) ∉ L := not_mem_L_of_old hE hci hi
  have hce : c s(v, a) = embed (oldOf i hi) := by rw [hci]; rfl
  rw [mem_Nbrs]
  exact ⟨hne, agree_of_embed hE hnmem hce⟩

/-- **A FRESH COLOUR HAS AT MOST ONE NEIGHBOUR AT A VERTEX** — the deterministic content of the local
lemma (`A_{e,f,i}` of arXiv:2208.12563 §4 resp. `B₁` of arXiv:2207.02920 §12). -/
theorem nb_le_one_fresh {n k K : ℕ} {c₀ : Col n k} {c : Col n (k + K)}
    {L : Finset (Sym2 (Verts n))} (hE : Extends (liftCol c₀ (Nat.le_add_right k K)) c L)
    (hP : Proper c L) (i : Fin (k + K)) (hi : k ≤ i.val) (v : Verts n) :
    (Nbrs c i v).card ≤ 1 := by
  by_contra hcon
  have h2 : 2 ≤ (Nbrs c i v).card := by omega
  obtain ⟨a, b, hab, ha, hb⟩ := exists_two_mem (s := Nbrs c i v) h2
  have hcai : c s(v, a) = i := (mem_Nbrs.mp ha).2
  have hcbi : c s(v, b) = i := (mem_Nbrs.mp hb).2
  have hLa : s(v, a) ∈ L := mem_L_of_fresh hE hcai hi
  have hLb : s(v, b) ∈ L := mem_L_of_fresh hE hcbi hi
  have hne : s(v, a) ≠ s(v, b) := by
    intro hc
    rcases sym2_inj hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hab h2
    · exact hab (h2.trans h1)
  exact absurd (hP s(v, a) hLa s(v, b) hLb hne
    ⟨v, Sym2.mem_mk_left v a, Sym2.mem_mk_left v b⟩) (fun hcon => hcon (hcai.trans hcbi.symm))

/-- **THE FIRST-STAGE COLOUR OF A NAMED EDGE.** -/
private lemma c₀_named {n k : ℕ} {c₀ : Col n k} {a b : Verts n} {e : Sym2 (Verts n)}
    {i : Fin k} (h : e = s(a, b)) (hc : c₀ e = i) : c₀ s(a, b) = i := by rw [h] at hc; exact hc

/-- **THE FIRST-STAGE COLOUR OF A NAMED EDGE, REVERSED.** -/
private lemma c₀_named' {n k : ℕ} {c₀ : Col n k} {a b : Verts n} {e : Sym2 (Verts n)}
    {i : Fin k} (h : e = s(a, b)) (hc : c₀ e = i) : c₀ s(b, a) = i := by
  rw [h] at hc
  rw [Sym2.eq_swap]
  exact hc

/-! ### The extension is a `Design` -/

/-- **THE EXTENSION IS TILED.**  Deleting the leftover edges from a first-stage colour class leaves a
tiling, and a fresh colour class is a matching. -/
theorem tile_of_stage2 {n k K : ℕ} {c₀ : Col n k} {c : Col n (k + K)} {L : Finset (Sym2 (Verts n))}
    (hE : Extends (liftCol c₀ (Nat.le_add_right k K)) c L) (hP : Proper c L)
    (hT : Tile c₀) : Tile c := by
  intro i v
  by_cases hfr : k ≤ i.val
  · refine ⟨le_trans (nb_le_one_fresh hE hP i hfr v) (by omega), ?_⟩
    intro a ha hcard2
    have hle := nb_le_one_fresh hE hP i hfr v
    omega
  · have hi : i.val < k := Nat.lt_of_not_ge hfr
    have hsub : Nbrs c i v ⊆ Nbrs c₀ (oldOf i hi) v := sub_Nbrs_old hE i hi v
    have hcard : (Nbrs c₀ (oldOf i hi) v).card ≤ 2 := hT.nb_le_two (oldOf i hi) v
    refine ⟨le_trans (Finset.card_le_card hsub) hcard, ?_⟩
    intro a ha hcard2
    have heq : Nbrs c i v = Nbrs c₀ (oldOf i hi) v :=
      Finset.eq_of_subset_of_card_le hsub (by rw [hcard2]; exact hcard)
    have hone : (Nbrs c₀ (oldOf i hi) a).card = 1 := hT.nb_one_of_mem (heq ▸ ha) (heq ▸ hcard2)
    have hsuba : Nbrs c i a ⊆ Nbrs c₀ (oldOf i hi) a := sub_Nbrs_old hE i hi a
    have hmem : v ∈ Nbrs c i a := mem_Nbrs.mpr
      ⟨Ne.symm (mem_Nbrs.mp ha).1, c_swap (mem_Nbrs.mp ha).2⟩
    have hle' : (Nbrs c i a).card ≤ 1 := by
      have h2 := Finset.card_le_card hsuba
      rw [hone] at h2
      exact h2
    have hge : 1 ≤ (Nbrs c i a).card := Finset.card_pos.mpr ⟨v, hmem⟩
    omega

/-- **THE EXTENSION IS PACKED.** -/
theorem packed_of_stage2 {n k K : ℕ} {c₀ : Col n k} {c : Col n (k + K)}
    {L : Finset (Sym2 (Verts n))} (hE : Extends (liftCol c₀ (Nat.le_add_right k K)) c L)
    (hP : Proper c L) (hT : Tile c₀) (hPk : Packed c₀) : Packed c := by
  intro i j v w hv hw hinter
  by_cases hfr : k ≤ i.val
  · have hle := nb_le_one_fresh hE hP i hfr v
    rw [card_twoA i hv] at hle
    omega
  · have hii : i.val < k := Nat.lt_of_not_ge hfr
    by_cases hfr' : k ≤ j.val
    · have hle := nb_le_one_fresh hE hP j hfr' w
      rw [card_twoA j hw] at hle
      omega
    · have hjj : j.val < k := Nat.lt_of_not_ge hfr'
      have hsubv : Nbrs c i v ⊆ Nbrs c₀ (oldOf i hii) v := sub_Nbrs_old hE i hii v
      have heqv : Nbrs c i v = Nbrs c₀ (oldOf i hii) v :=
        Finset.eq_of_subset_of_card_le hsubv (by rw [card_twoA i hv]; exact hT.nb_le_two _ v)
      have hsubw : Nbrs c j w ⊆ Nbrs c₀ (oldOf j hjj) w := sub_Nbrs_old hE j hjj w
      have heqw : Nbrs c j w = Nbrs c₀ (oldOf j hjj) w :=
        Finset.eq_of_subset_of_card_le hsubw (by rw [card_twoA j hw]; exact hT.nb_le_two _ w)
      have hvi : v ∈ twoA c₀ (oldOf i hii) := by
        rw [twoA, Finset.mem_filter]
        refine ⟨Finset.mem_univ v, ?_⟩
        rw [← card_Nbrs, ← heqv]
        exact card_twoA i hv
      have hwj : w ∈ twoA c₀ (oldOf j hjj) := by
        rw [twoA, Finset.mem_filter]
        refine ⟨Finset.mem_univ w, ?_⟩
        rw [← card_Nbrs, ← heqw]
        exact card_twoA j hw
      have hps : pathSet c i v = pathSet c₀ (oldOf i hii) v := by
        unfold pathSet
        rw [heqv]
      have hps' : pathSet c j w = pathSet c₀ (oldOf j hjj) w := by
        unfold pathSet
        rw [heqw]
      have hinter' : 2 ≤ (pathSet c₀ (oldOf i hii) v ∩ pathSet c₀ (oldOf j hjj) w).card := by
        rw [← hps, ← hps']
        exact hinter
      have hij0 : oldOf i hii = oldOf j hjj :=
        hPk (oldOf i hii) (oldOf j hjj) v w hvi hwj hinter'
      apply Fin.ext
      exact congrArg (fun z : Fin k => (z : ℕ)) hij0

/-- **NO CROSSING FOUR-SET IN THE EXTENSION.**  Two crossing pairs on one clique are excluded by
`NoCrossFour c₀` (both first-stage), by `NoAltCycle` (both fresh) and by `NoCrossFresh` (one of
each) — this is the whole content of the two bad events of the local lemma. -/
theorem noCrossFour_of_stage2 {n k K : ℕ} {c₀ : Col n k} {c : Col n (k + K)}
    {L : Finset (Sym2 (Verts n))} (hE : Extends (liftCol c₀ (Nat.le_add_right k K)) c L)
    (hP : Proper c L) (hT : Tile c₀) (hX : NoCrossFour c₀) (hLC : LeafClosed c₀ L)
    (hAlt : NoAltCycle c L) (hCF : NoCrossFresh c₀ c L) : NoCrossFour c := by
  intro S hS i j hij hX'
  obtain ⟨hXi, hXj⟩ := hX'
  obtain ⟨e, f, he, hf, hefne, hdis⟩ := hXi
  obtain ⟨a, b, p, q, h4, hab, hpq, hS'⟩ := four_of_disjoint hS he hf hdis
  obtain ⟨g, t, hg, ht, hgt, hdgt⟩ := hXj
  have h4qp : FourDistinct a b q p := four_dist_comm h4
  have hci : c e = i := (mem_classIn.mp he).2
  have hcf : c f = i := (mem_classIn.mp hf).2
  have hcg : c g = j := (mem_classIn.mp hg).2
  have hct : c t = j := (mem_classIn.mp ht).2
  have hgef : g ≠ e := fun h => hij (hci.symm.trans (h ▸ hcg))
  have hget : g ≠ f := fun h => hij (hcf.symm.trans (h ▸ hcg))
  have htef : t ≠ e := fun h => hij (hci.symm.trans (h ▸ hct))
  have htef' : t ≠ f := fun h => hij (hcf.symm.trans (h ▸ hct))
  by_cases hfj : k ≤ j.val
  · by_cases hfi : k ≤ i.val
    · -- both fresh: the four leftover edges form a two-coloured 4-cycle
      have hLe : e ∈ L := mem_L_of_fresh hE hci hfi
      have hLf : f ∈ L := mem_L_of_fresh hE hcf hfi
      have hLg : g ∈ L := mem_L_of_fresh hE hcg hfj
      have hLt : t ∈ L := mem_L_of_fresh hE hct hfj
      have hLe' : s(a, b) ∈ L := by rw [← hab]; exact hLe
      have hLf' : s(p, q) ∈ L := by rw [← hpq]; exact hLf
      have hLf'' : s(q, p) ∈ L := by rw [Sym2.eq_swap]; exact hLf'
      rcases matching_case h4 hS' (mem_classIn.mp hg).1 (mem_classIn.mp ht).1
        (by rw [← hab]; exact hgef) (by rw [← hpq]; exact hget) hdgt with
        hgt' | hgt' | hgt' | hgt'
      · have h2 : s(b, q) ∈ L := by rw [← hgt'.2]; exact hLt
        have h4' : s(p, a) ∈ L := by rw [Sym2.eq_swap, ← hgt'.1]; exact hLg
        exact alt_two hAlt h4qp hij hLe' h2 hLf'' h4' (c_named hab hci) (c_named hgt'.2 hct)
          (c_named' hpq hcf) (c_named' hgt'.1 hcg)
      · have h2 : s(b, p) ∈ L := by rw [← hgt'.2]; exact hLt
        have h4' : s(q, a) ∈ L := by rw [Sym2.eq_swap, ← hgt'.1]; exact hLg
        exact alt_two hAlt h4 hij hLe' h2 hLf' h4' (c_named hab hci) (c_named hgt'.2 hct)
          (c_named hpq hcf) (c_named' hgt'.1 hcg)
      · have h2 : s(b, p) ∈ L := by rw [← hgt'.1]; exact hLg
        have h4' : s(q, a) ∈ L := by rw [Sym2.eq_swap, ← hgt'.2]; exact hLt
        exact alt_two hAlt h4 hij hLe' h2 hLf' h4' (c_named hab hci) (c_named hgt'.1 hcg)
          (c_named hpq hcf) (c_named' hgt'.2 hct)
      · have h2 : s(b, q) ∈ L := by rw [← hgt'.1]; exact hLg
        have h4' : s(p, a) ∈ L := by rw [Sym2.eq_swap, ← hgt'.2]; exact hLt
        exact alt_two hAlt h4qp hij hLe' h2 hLf'' h4' (c_named hab hci) (c_named hgt'.1 hcg)
          (c_named' hpq hcf) (c_named' hgt'.2 hct)
    · -- `i` first-stage, `j` fresh: a fresh crossing pair over a first-stage monochromatic pair
      have hii : i.val < k := Nat.lt_of_not_ge hfi
      have hne : e ∉ L := not_mem_L_of_old hE hci hii
      have hnf : f ∉ L := not_mem_L_of_old hE hcf hii
      have hc₀e : c₀ e = oldOf i hii := agree_of_embed hE hne hci
      have hc₀f : c₀ f = oldOf i hii := agree_of_embed hE hnf hcf
      have hLg : g ∈ L := mem_L_of_fresh hE hcg hfj
      have hLt : t ∈ L := mem_L_of_fresh hE hct hfj
      rcases matching_case h4 hS' (mem_classIn.mp hg).1 (mem_classIn.mp ht).1
        (by rw [← hab]; exact hgef) (by rw [← hpq]; exact hget) hdgt with
        hgt' | hgt' | hgt' | hgt'
      · have hAB : s(a, p) ∈ L := by rw [← hgt'.1]; exact hLg
        refine hCF.no_cross ⟨h4.2.1, h4.2.2.1, h4.1, h4.2.2.2.2.2, h4.2.2.2.1.symm, h4.2.2.2.2.1.symm⟩ hAB ?_ ?_ ?_ ?_ ?_
        · rw [Sym2.eq_swap, ← hgt'.2]; exact hLt
        · rw [← hgt'.1, Sym2.eq_swap, ← hgt'.2]; exact hcg.trans hct.symm
        · rw [← hab]; exact hne
        · rw [← hpq]; exact hnf
        · exact (c₀_named hab hc₀e).trans (c₀_named hpq hc₀f).symm
      · have hAB : s(a, q) ∈ L := by rw [← hgt'.1]; exact hLg
        refine hCF.no_cross ⟨h4.2.2.1, h4.2.1, h4.1, h4.2.2.2.2.2.symm, h4.2.2.2.2.1.symm, h4.2.2.2.1.symm⟩ hAB ?_ ?_ ?_ ?_ ?_
        · rw [Sym2.eq_swap, ← hgt'.2]; exact hLt
        · rw [← hgt'.1, Sym2.eq_swap, ← hgt'.2]; exact hcg.trans hct.symm
        · rw [← hab]; exact hne
        · rw [Sym2.eq_swap, ← hpq]; exact hnf
        · exact (c₀_named hab hc₀e).trans (c₀_named' hpq hc₀f).symm
      · have hAB : s(b, p) ∈ L := by rw [← hgt'.1]; exact hLg
        refine hCF.no_cross ⟨h4.2.2.2.1, h4.2.2.2.2.1, h4.1.symm, h4.2.2.2.2.2, h4.2.1.symm, h4.2.2.1.symm⟩ hAB ?_ ?_ ?_ ?_ ?_
        · rw [Sym2.eq_swap, ← hgt'.2]; exact hLt
        · rw [← hgt'.1, Sym2.eq_swap, ← hgt'.2]; exact hcg.trans hct.symm
        · rw [Sym2.eq_swap, ← hab]; exact hne
        · rw [← hpq]; exact hnf
        · exact (c₀_named' hab hc₀e).trans (c₀_named hpq hc₀f).symm
      · have hAB : s(b, q) ∈ L := by rw [← hgt'.1]; exact hLg
        refine hCF.no_cross ⟨h4.2.2.2.2.1, h4.2.2.2.1, h4.1.symm, h4.2.2.2.2.2.symm, h4.2.2.1.symm, h4.2.1.symm⟩ hAB ?_ ?_ ?_ ?_ ?_
        · rw [Sym2.eq_swap, ← hgt'.2]; exact hLt
        · rw [← hgt'.1, Sym2.eq_swap, ← hgt'.2]; exact hcg.trans hct.symm
        · rw [Sym2.eq_swap, ← hab]; exact hne
        · rw [Sym2.eq_swap, ← hpq]; exact hnf
        · exact (c₀_named' hab hc₀e).trans (c₀_named' hpq hc₀f).symm
  · by_cases hfi : k ≤ i.val
    · -- `i` fresh, `j` first-stage: the same event with the roles reversed
      have hjj : j.val < k := Nat.lt_of_not_ge hfj
      have hng : g ∉ L := not_mem_L_of_old hE hcg hjj
      have hnt : t ∉ L := not_mem_L_of_old hE hct hjj
      have hngt : ∀ e' : Sym2 (Verts n), e' = g ∨ e' = t → e' ∉ L := by
        intro e' he'
        rcases he' with rfl | rfl
        · exact hng
        · exact hnt
      have hc₀g : c₀ g = oldOf j hjj := agree_of_embed hE hng hcg
      have hc₀t : c₀ t = oldOf j hjj := agree_of_embed hE hnt hct
      have hLe : e ∈ L := mem_L_of_fresh hE hci hfi
      have hLf : f ∈ L := mem_L_of_fresh hE hcf hfi
      rcases matching_case h4 hS' (mem_classIn.mp hg).1 (mem_classIn.mp ht).1
        (by rw [← hab]; exact hgef) (by rw [← hpq]; exact hget) hdgt with
        hgt' | hgt' | hgt' | hgt'
      · have hAB : s(a, b) ∈ L := by rw [← hab]; exact hLe
        refine hCF.no_cross h4qp hAB ?_ ?_ ?_ ?_ ?_
        · rw [Sym2.eq_swap, ← hpq]; exact hLf
        · rw [← hab, Sym2.eq_swap, ← hpq]; exact hci.trans hcf.symm
        · exact hngt _ (Or.inl (hgt'.1.symm))
        · exact hngt _ (Or.inr (hgt'.2.symm))
        · rw [hgt'.1.symm, hgt'.2.symm]; exact hc₀g.trans hc₀t.symm
      · have hAB : s(a, b) ∈ L := by rw [← hab]; exact hLe
        refine hCF.no_cross h4 hAB ?_ ?_ ?_ ?_ ?_
        · rw [← hpq]; exact hLf
        · rw [← hab, ← hpq]; exact hci.trans hcf.symm
        · exact hngt _ (Or.inl (hgt'.1.symm))
        · exact hngt _ (Or.inr (hgt'.2.symm))
        · rw [hgt'.1.symm, hgt'.2.symm]; exact hc₀g.trans hc₀t.symm
      · have hAB : s(a, b) ∈ L := by rw [← hab]; exact hLe
        refine hCF.no_cross h4 hAB ?_ ?_ ?_ ?_ ?_
        · rw [← hpq]; exact hLf
        · rw [← hab, ← hpq]; exact hci.trans hcf.symm
        · exact hngt _ (Or.inr (hgt'.2.symm))
        · exact hngt _ (Or.inl (hgt'.1.symm))
        · rw [hgt'.2.symm, hgt'.1.symm]; exact hc₀t.trans hc₀g.symm
      · have hAB : s(a, b) ∈ L := by rw [← hab]; exact hLe
        refine hCF.no_cross h4qp hAB ?_ ?_ ?_ ?_ ?_
        · rw [Sym2.eq_swap, ← hpq]; exact hLf
        · rw [← hab, Sym2.eq_swap, ← hpq]; exact hci.trans hcf.symm
        · exact hngt _ (Or.inr (hgt'.2.symm))
        · exact hngt _ (Or.inl (hgt'.1.symm))
        · rw [hgt'.2.symm, hgt'.1.symm]; exact hc₀t.trans hc₀g.symm
    · -- both colours first-stage
      have hii : i.val < k := Nat.lt_of_not_ge hfi
      have hjj : j.val < k := Nat.lt_of_not_ge hfj
      have hne : e ∉ L := not_mem_L_of_old hE hci hii
      have hnf : f ∉ L := not_mem_L_of_old hE hcf hii
      have hng : g ∉ L := not_mem_L_of_old hE hcg hjj
      have hnt : t ∉ L := not_mem_L_of_old hE hct hjj
      have hc₀e : c₀ e = oldOf i hii := agree_of_embed hE hne hci
      have hc₀f : c₀ f = oldOf i hii := agree_of_embed hE hnf hcf
      have hc₀g : c₀ g = oldOf j hjj := agree_of_embed hE hng hcg
      have hc₀t : c₀ t = oldOf j hjj := agree_of_embed hE hnt hct
      refine hX S hS (oldOf i hii) (oldOf j hjj) ?_ ⟨⟨e, f, ?_, ?_, hefne, hdis⟩,
        ⟨g, t, ?_, ?_, hgt, hdgt⟩⟩
      · intro hcon
        apply hij
        apply Fin.ext
        exact congrArg (fun z : Fin k => (z : ℕ)) hcon
      · exact mem_classIn.mpr ⟨(mem_classIn.mp he).1, hc₀e⟩
      · exact mem_classIn.mpr ⟨(mem_classIn.mp hf).1, hc₀f⟩
      · exact mem_classIn.mpr ⟨(mem_classIn.mp hg).1, hc₀g⟩
      · exact mem_classIn.mpr ⟨(mem_classIn.mp ht).1, hc₀t⟩



/-- **THREE OF FOUR.**  A member of the four vertices, different from the first, is one of the
other three. -/
private theorem three_of_four {n : ℕ} {x y t u z : Verts n}
    (hz : z = x ∨ z = y ∨ z = t ∨ z = u) (hxz : z ≠ x) : z = y ∨ z = t ∨ z = u := by
  rcases hz with hz | hz | hz | hz
  · exact absurd hz hxz
  · exact Or.inl hz
  · exact Or.inr (Or.inl hz)
  · exact Or.inr (Or.inr hz)

/-- Swapping the first two of a four-way disjunction. -/
private theorem four_swap {n : ℕ} {a b p q z : Verts n} (hz : z = a ∨ z = b ∨ z = p ∨ z = q) :
    z = b ∨ z = a ∨ z = p ∨ z = q := by
  rcases hz with hz | hz | hz | hz
  · exact Or.inr (Or.inl hz)
  · exact Or.inl hz
  · exact Or.inr (Or.inr (Or.inl hz))
  · exact Or.inr (Or.inr (Or.inr hz))

/-- Moving the third entry to the front. -/
private theorem four_rot {n : ℕ} {a b p q z : Verts n} (hz : z = a ∨ z = b ∨ z = p ∨ z = q) :
    z = p ∨ z = a ∨ z = b ∨ z = q := by
  rcases hz with hz | hz | hz | hz
  · exact Or.inr (Or.inl hz)
  · exact Or.inr (Or.inr (Or.inl hz))
  · exact Or.inl hz
  · exact Or.inr (Or.inr (Or.inr hz))

/-- Moving the fourth entry to the front. -/
private theorem four_rot2 {n : ℕ} {a b p q z : Verts n} (hz : z = a ∨ z = b ∨ z = p ∨ z = q) :
    z = q ∨ z = a ∨ z = b ∨ z = p := by
  rcases hz with hz | hz | hz | hz
  · exact Or.inr (Or.inl hz)
  · exact Or.inr (Or.inr (Or.inl hz))
  · exact Or.inr (Or.inr (Or.inr hz))
  · exact Or.inl hz

/-- **THE LEAF-CLOSURE STEP.**  A leftover crossing pair `{s(a,b), s(p,q)}` of a four-set, together
with a two-edge path of a first-stage colour whose three vertices lie in the four-set, is impossible:
either a path edge is one of the two leftover edges — impossible, a leftover edge carries a fresh
colour — or the two leaves are the endpoints of the other leftover edge, contradicting the leaf
closure. -/
private lemma leafClosure_step {n : ℕ} {L : Finset (Sym2 (Verts n))}
    {a b p q w p₁ q₁ : Verts n}
    (h4 : FourDistinct a b p q) (he : s(a, b) ∈ L) (hf : s(p, q) ∈ L)
    (hw : w = a ∨ w = b ∨ w = p ∨ w = q) (hp₁q₁ : p₁ ≠ q₁)
    (hp₁S : p₁ ∈ fourSet a b p q) (hq₁S : q₁ ∈ fourSet a b p q)
    (hp₁w : p₁ ≠ w) (hq₁w : q₁ ≠ w)
    (hnp₁ : s(w, p₁) ∉ L) (hnq₁ : s(w, q₁) ∉ L) (hleaf : s(p₁, q₁) ∉ L) :
    False := by
  rcases hw with hw' | hw' | hw' | hw'
  · -- `w = a`: the leftover edge through `a` is `s(a, b)`
    by_cases hb : b = p₁ ∨ b = q₁
    · rcases hb with hb | hb
      · exact hnp₁ (by rw [hw', ← hb]; exact he)
      · exact hnq₁ (by rw [hw', ← hb]; exact he)
    · have hb1 : b ≠ p₁ := fun hh => hb (Or.inl hh)
      have hb2 : b ≠ q₁ := fun hh => hb (Or.inr hh)
      rcases two_of_three
        (three_of_four (mem_fourSet h4 |>.mp hp₁S) (fun hh => hp₁w (hh.trans hw'.symm)))
        (three_of_four (mem_fourSet h4 |>.mp hq₁S) (fun hh => hq₁w (hh.trans hw'.symm)))
        hp₁q₁ hb1 hb2 with htwo | htwo
      · rw [show s(p₁, q₁) = s(p, q) from by rw [htwo.1, htwo.2]] at hleaf
        exact hleaf hf
      · rw [show s(p₁, q₁) = s(p, q) from by rw [htwo.1, htwo.2, Sym2.eq_swap]] at hleaf
        exact hleaf hf
  · -- `w = b`
    by_cases ha : a = p₁ ∨ a = q₁
    · rcases ha with ha | ha
      · exact hnp₁ (by rw [hw', ← ha, Sym2.eq_swap]; exact he)
      · exact hnq₁ (by rw [hw', ← ha, Sym2.eq_swap]; exact he)
    · have ha1 : a ≠ p₁ := fun hh => ha (Or.inl hh)
      have ha2 : a ≠ q₁ := fun hh => ha (Or.inr hh)
      rcases two_of_three
        (three_of_four (four_swap (mem_fourSet h4 |>.mp hp₁S))
          (fun hh => hp₁w (hh.trans hw'.symm)))
        (three_of_four (four_swap (mem_fourSet h4 |>.mp hq₁S))
          (fun hh => hq₁w (hh.trans hw'.symm)))
        hp₁q₁ ha1 ha2 with htwo | htwo
      · rw [show s(p₁, q₁) = s(p, q) from by rw [htwo.1, htwo.2]] at hleaf
        exact hleaf hf
      · rw [show s(p₁, q₁) = s(p, q) from by rw [htwo.1, htwo.2, Sym2.eq_swap]] at hleaf
        exact hleaf hf
  · -- `w = p`: the leftover edge through `p` is `s(p, q)`
    by_cases hq : q = p₁ ∨ q = q₁
    · rcases hq with hq | hq
      · exact hnp₁ (by rw [hw', ← hq]; exact hf)
      · exact hnq₁ (by rw [hw', ← hq]; exact hf)
    · have hq1 : q ≠ p₁ := fun hh => hq (Or.inl hh)
      have hq2 : q ≠ q₁ := fun hh => hq (Or.inr hh)
      rcases two_of_three
        (rot3 (three_of_four (four_rot (mem_fourSet h4 |>.mp hp₁S))
          (fun hh => hp₁w (hh.trans hw'.symm))))
        (rot3 (three_of_four (four_rot (mem_fourSet h4 |>.mp hq₁S))
          (fun hh => hq₁w (hh.trans hw'.symm))))
        hp₁q₁ hq1 hq2 with htwo | htwo
      · rw [show s(p₁, q₁) = s(a, b) from by rw [htwo.1, htwo.2]] at hleaf
        exact hleaf he
      · rw [show s(p₁, q₁) = s(a, b) from by rw [htwo.1, htwo.2, Sym2.eq_swap]] at hleaf
        exact hleaf he
  · -- `w = q`
    by_cases hp : p = p₁ ∨ p = q₁
    · rcases hp with hp | hp
      · exact hnp₁ (by rw [hw', ← hp, Sym2.eq_swap]; exact hf)
      · exact hnq₁ (by rw [hw', ← hp, Sym2.eq_swap]; exact hf)
    · have hp1 : p ≠ p₁ := fun hh => hp (Or.inl hh)
      have hp2 : p ≠ q₁ := fun hh => hp (Or.inr hh)
      rcases two_of_three
        (rot3 (three_of_four (four_rot2 (mem_fourSet h4 |>.mp hp₁S))
          (fun hh => hp₁w (hh.trans hw'.symm))))
        (rot3 (three_of_four (four_rot2 (mem_fourSet h4 |>.mp hq₁S))
          (fun hh => hq₁w (hh.trans hw'.symm))))
        hp₁q₁ hp1 hp2 with htwo | htwo
      · rw [show s(p₁, q₁) = s(a, b) from by rw [htwo.1, htwo.2]] at hleaf
        exact hleaf he
      · rw [show s(p₁, q₁) = s(a, b) from by rw [htwo.1, htwo.2, Sym2.eq_swap]] at hleaf
        exact hleaf he

/-- **A TWO-EDGE PATH INSIDE A FOUR-SET.**  If `w` is the centre of a two-edge path of colour `j` all
of whose three vertices lie in a four-set `S`, then the two leaves are distinct elements of `S`
different from `w`, and the leaf edge joins them. -/
private theorem path_in_four {n K : ℕ} {c : Col n K} {S : Finset (Verts n)} (hS : S.card = 4)
    {j : Fin K} {w : Verts n} (hw : w ∈ twoA c j) (hsub : pathSet c j w ⊆ S) :
    ∃ p q : Verts n, p ≠ q ∧ p ∈ S ∧ q ∈ S ∧ w ∉ twoFin p q ∧
      c s(w, p) = j ∧ c s(w, q) = j ∧ Nbrs c j w = {p, q} := by
  obtain ⟨p, q, hpq, hN⟩ := Finset.card_eq_two.mp (card_twoA j hw)
  have hpN : p ∈ Nbrs c j w := by rw [hN]; simp
  have hqN : q ∈ Nbrs c j w := by rw [hN]; simp
  have hpS : p ∈ S := hsub (mem_pathSet.mpr (Or.inr hpN))
  have hqS : q ∈ S := hsub (mem_pathSet.mpr (Or.inr hqN))
  refine ⟨p, q, hpq, hpS, hqS, ?_, ?_, ?_, hN⟩
  · intro hcon
    exact not_mem_Nbrs_self j w (by rw [hN]; exact hcon)
  · exact (mem_Nbrs.mp hpN).2
  · exact (mem_Nbrs.mp hqN).2

set_option maxHeartbeats 40000000 in
/-- **NO BAD FOUR-SET IN THE EXTENSION.**  A fresh crossing pair and a first-stage two-edge path on
one clique are excluded by the **leaf closure** of the first stage: the leaf edge of the path is
covered, so it cannot be a leftover edge, and the leftover crossing pair cannot contain a path edge
either (a covered edge carries a colour `< k`). -/
theorem noBadFour_of_stage2 {n k K : ℕ} {c₀ : Col n k} {c : Col n (k + K)}
    {L : Finset (Sym2 (Verts n))} (hE : Extends (liftCol c₀ (Nat.le_add_right k K)) c L)
    (hP : Proper c L) (hT : Tile c₀) (hPk : Packed c₀) (hB : NoBadFour c₀)
    (hLC : LeafClosed c₀ L) : NoBadFour c := by
  intro S hS i j hij hX'
  obtain ⟨hXi, w, hw, hwsub⟩ := hX'
  obtain ⟨e, f, he, hf, hefne, hdis⟩ := hXi
  obtain ⟨a, b, p, q, h4, hab, hpq, hS'⟩ := four_of_disjoint hS he hf hdis
  have hci : c e = i := (mem_classIn.mp he).2
  have hcf : c f = i := (mem_classIn.mp hf).2
  have hwS : w ∈ S := by
    refine hwsub ?_
    rw [pathSet]
    exact Finset.mem_insert_self w _
  by_cases hfj : k ≤ j.val
  · -- a fresh colour has no two-edge path
    have hle := nb_le_one_fresh hE hP j hfj w
    rw [card_twoA j hw] at hle
    omega
  · have hjj : j.val < k := Nat.lt_of_not_ge hfj
    by_cases hfi : k ≤ i.val
    · -- `i` fresh: the crossing pair is a leftover pair, the path is a first-stage path
      have hLe : e ∈ L := mem_L_of_fresh hE hci hfi
      have hLf : f ∈ L := mem_L_of_fresh hE hcf hfi
      obtain ⟨p₁, q₁, hp₁q₁, hp₁S, hq₁S, hwnot, hcolp₁, hcolq₁, hN⟩ :=
        path_in_four hS hw hwsub
      have hN₀ : Nbrs c₀ (oldOf j hjj) w = {p₁, q₁} := (hN.symm.trans
        (Finset.eq_of_subset_of_card_le (sub_Nbrs_old hE j hjj w)
          (by rw [card_twoA j hw]; exact hT.nb_le_two _ w))).symm
      have hnp₁ : s(w, p₁) ∉ L := not_mem_L_of_old hE hcolp₁ hjj
      have hnq₁ : s(w, q₁) ∉ L := not_mem_L_of_old hE hcolq₁ hjj
      have hleaf : s(p₁, q₁) ∉ L := hLC (oldOf j hjj) w p₁ q₁ hN₀
      have hwp₁ : p₁ ≠ w := fun hh => hwnot (by rw [← hh, mem_twoFin]; exact Or.inl rfl)
      have hwq₁ : q₁ ≠ w := fun hh => hwnot (by rw [← hh, mem_twoFin]; exact Or.inr rfl)
      have hLe' : s(a, b) ∈ L := by rw [← hab]; exact hLe
      have hLf' : s(p, q) ∈ L := by rw [← hpq]; exact hLf
      have hwS' : w = a ∨ w = b ∨ w = p ∨ w = q := (mem_fourSet h4).mp (by rw [← hS']; exact hwS)
      have hp₁S' : p₁ ∈ fourSet a b p q := by rw [← hS']; exact hp₁S
      have hq₁S' : q₁ ∈ fourSet a b p q := by rw [← hS']; exact hq₁S
      exact @leafClosure_step n L a b p q w p₁ q₁ h4 hLe' hLf' hwS' hp₁q₁ hp₁S'
        hq₁S' hwp₁ hwq₁ hnp₁ hnq₁ hleaf
    · -- both colours first-stage: the first stage itself forbids it
      have hii : i.val < k := Nat.lt_of_not_ge hfi
      have hne : e ∉ L := not_mem_L_of_old hE hci hii
      have hnf : f ∉ L := not_mem_L_of_old hE hcf hii
      have heqj : Nbrs c j w = Nbrs c₀ (oldOf j hjj) w :=
        Finset.eq_of_subset_of_card_le (sub_Nbrs_old hE j hjj w)
          (by rw [card_twoA j hw]; exact hT.nb_le_two _ w)
      have hwj : w ∈ twoA c₀ (oldOf j hjj) := by
        rw [twoA, Finset.mem_filter]
        refine ⟨Finset.mem_univ w, ?_⟩
        rw [← card_Nbrs, ← heqj]
        exact card_twoA j hw
      refine hB S hS (oldOf i hii) (oldOf j hjj) ?_ ⟨⟨e, f, ?_, ?_, hefne, hdis⟩, w, hwj, ?_⟩
      · intro hcon
        apply hij
        apply Fin.ext
        exact congrArg (fun z : Fin k => (z : ℕ)) hcon
      · exact mem_classIn.mpr ⟨(mem_classIn.mp he).1, agree_of_embed hE hne hci⟩
      · exact mem_classIn.mpr ⟨(mem_classIn.mp hf).1, agree_of_embed hE hnf hcf⟩
      · intro z hz
        rcases Finset.mem_insert.mp hz with hz | hz
        · exact hwsub (Finset.mem_insert.mpr (Or.inl hz))
        · exact hwsub (Finset.mem_insert.mpr (Or.inr (heqj ▸ hz)))

/-! ### The two bad events are NECESSARY as well as sufficient -/

/-- **(P2) IS NECESSARY.**  If the extension `c` is admissible and four edges of a 4-cycle are
leftover edges, then those four edges span at least three colours.  Indeed a 4-cycle with at most two
colours, together with its two diagonals, would span at most `2 + 2 = 4` colours on the four-set,
contradicting the catalog condition.  No structural hypothesis on the first stage is used: this is a
property of `Admissible c` alone. -/
theorem NoAltCycle.of_admissible {n K : ℕ} {c : Col n K} {L : Finset (Sym2 (Verts n))}
    (h : Admissible c) : NoAltCycle c L := by
  intro a b p q h4 h1 h2 h3 h4p
  by_contra hlt
  have hle : (cycleColours c a b p q).card ≤ 2 := by omega
  have hsub : colorsOn c (fourSet a b p q)
      ⊆ insert (c s(a, p)) (insert (c s(b, q)) (cycleColours c a b p q)) := by
    intro z hz
    rw [colorsOn, Finset.mem_image] at hz
    obtain ⟨e, heS, he⟩ := hz
    rw [← he]
    obtain ⟨hxy, hxS, hyS, hne⟩ := exists_mk heS
    rcases mem_six_of_mem_edgeFinset h4 rfl heS with hz | hz | hz | hz | hz | hz
    · rw [hz]; simp [cycleColours]
    · rw [hz]; simp [cycleColours]
    · rw [hz]
      have hq : c s(a, q) = c s(q, a) := congrArg (fun e => c e) (Sym2.eq_swap (a := a) (b := q))
      rw [hq]; simp [cycleColours]
    · rw [hz]; simp [cycleColours]
    · rw [hz]; simp [cycleColours]
    · rw [hz]; simp [cycleColours]
  have hc1 := Finset.card_le_card hsub
  have hc2 : (insert (c s(b, q)) (cycleColours c a b p q)).card
      ≤ (cycleColours c a b p q).card + 1 := Finset.card_insert_le _ _
  have hc3 : (insert (c s(a, p)) (insert (c s(b, q)) (cycleColours c a b p q))).card
      ≤ (insert (c s(b, q)) (cycleColours c a b p q)).card + 1 := Finset.card_insert_le _ _
  have h5 := h (fourSet a b p q) (card_fourSet h4)
  omega

/-- **(P3) IS NECESSARY.**  If the extension `c` is admissible, two opposite leftover edges of a
4-cycle never carry the same colour above a first-stage monochromatic complementary pair.  The two
coincidences give two *distinct* colours on the four-set (the leftover edge carries a fresh colour
`≥ k`, the covered pair an old colour `< k`), and the remaining two edges add at most two more, so
at most four colours — contradicting admissibility. -/
theorem NoCrossFresh.of_admissible {n k K : ℕ} {c₀ : Col n k} {c : Col n (k + K)}
    {L : Finset (Sym2 (Verts n))} (hE : Extends (liftCol c₀ (Nat.le_add_right k K)) c L)
    (h : Admissible c) : NoCrossFresh c₀ c L := by
  intro a b p q h4 h1 h2 hc h3 h4p hc0
  have hej : c s(a, q) = c s(b, p) := by
    have hx : c s(a, q) = embed (c₀ s(a, q)) := embed_of_agree hE h3 rfl
    have hy : c s(b, p) = embed (c₀ s(b, p)) := embed_of_agree hE h4p rfl
    calc c s(a, q) = embed (c₀ s(a, q)) := hx
      _ = embed (c₀ s(b, p)) := by rw [hc0]
      _ = c s(b, p) := hy.symm
  have hval : ((c s(a, q)) : Fin (k + K)).val = (c₀ s(a, q)).val := by
    rw [embed_of_agree hE h3 rfl, embed_val]
  have hv' : ((c s(a, q)) : Fin (k + K)).val < k := hval ▸ (c₀ s(a, q)).isLt
  have hne : c s(a, b) ≠ c s(a, q) := by
    intro hh
    have hv : k ≤ (c s(a, b)).val := (hE.2 s(a, b)).mp h1
    rw [← hh] at hv'
    omega
  have hsub : colorsOn c (fourSet a b p q)
      ⊆ insert (c s(a, b)) (insert (c s(a, q)) (insert (c s(a, p)) (insert (c s(b, q)) ∅))) := by
    intro z hz
    rw [colorsOn, Finset.mem_image] at hz
    obtain ⟨e, heS, he⟩ := hz
    rw [← he]
    obtain ⟨hxy, hxS, hyS, hne2⟩ := exists_mk heS
    rcases mem_six_of_mem_edgeFinset h4 rfl heS with hz | hz | hz | hz | hz | hz
    · rw [hz]; simp
    · rw [hz]; simp
    · rw [hz]; simp
    · rw [hz, hej]; simp
    · rw [hz]; simp
    · rw [hz, hc]; simp
  have hc1 := Finset.card_le_card hsub
  have hc2 : ((insert (c s(b, q)) ∅ : Finset (Fin (k + K))) : Finset (Fin (k + K))).card
      ≤ (0 : ℕ) + 1 := Finset.card_insert_le _ _
  have hc3 : ((insert (c s(a, p)) (insert (c s(b, q)) ∅) : Finset (Fin (k + K)))).card
      ≤ (insert (c s(b, q)) ∅ : Finset (Fin (k + K))).card + 1 := Finset.card_insert_le _ _
  have hc4 : ((insert (c s(a, q)) (insert (c s(a, p))
      (insert (c s(b, q)) ∅)) : Finset (Fin (k + K)))).card
      ≤ (insert (c s(a, p)) (insert (c s(b, q)) ∅) : Finset (Fin (k + K))).card + 1 :=
    Finset.card_insert_le _ _
  have hc5 : ((insert (c s(a, b)) (insert (c s(a, q)) (insert (c s(a, p))
      (insert (c s(b, q)) ∅))) : Finset (Fin (k + K)))).card
      ≤ (insert (c s(a, q)) (insert (c s(a, p))
      (insert (c s(b, q)) ∅)) : Finset (Fin (k + K))).card + 1 :=
    Finset.card_insert_le _ _
  have h5 := h (fourSet a b p q) (card_fourSet h4)
  omega


/-! ### The two stages compose -/

/-- **THE TWO STAGES COMPOSE: THE EXTENSION IS A `Design`.**  This is the composition theorem: a
first-stage colouring which is a `Design`, extended on the leftover graph by a proper fresh colouring
whose two bad events (`B_D`/`B₂` and `C_{D,i}`/`B₃`) are absent, and whose two-edge paths satisfy the
leaf closure, is again a `Design` colouring. -/
theorem design_of_stage2 {n k K : ℕ} {c₀ : Col n k} {c : Col n (k + K)}
    {L : Finset (Sym2 (Verts n))} (hE : Extends (liftCol c₀ (Nat.le_add_right k K)) c L)
    (hP : Proper c L) (hD₀ : Design c₀) (hLC : LeafClosed c₀ L) (hAlt : NoAltCycle c L)
    (hCF : NoCrossFresh c₀ c L) : Design c :=
  ⟨tile_of_stage2 hE hP hD₀.1, packed_of_stage2 hE hP hD₀.1 hD₀.2.1,
    noCrossFour_of_stage2 hE hP hD₀.1 hD₀.2.2.1 hLC hAlt hCF,
    noBadFour_of_stage2 hE hP hD₀.1 hD₀.2.1 hD₀.2.2.2 hLC⟩

/-- **THE VERIFICATION LEMMA OF THE PUBLISHED SECOND STAGE.**  Under the hypotheses of
`design_of_stage2` the extension `c` is **admissible**: every four-vertex clique of `K_n` spans at
least five colours.  This is the whole verification content of phase 2 of arXiv:2208.12563 §4
(= arXiv:2207.02920): the properness, together with the two bad events `B_D` and `C_{D,i}`, is
*sufficient* — no further probabilistic input is needed. -/
theorem admissible_of_stage2 {n k K : ℕ} {c₀ : Col n k} {c : Col n (k + K)}
    {L : Finset (Sym2 (Verts n))} (hE : Extends (liftCol c₀ (Nat.le_add_right k K)) c L)
    (hP : Proper c L) (hD₀ : Design c₀) (hLC : LeafClosed c₀ L) (hAlt : NoAltCycle c L)
    (hCF : NoCrossFresh c₀ c L) (hn : 4 ≤ n) : Admissible c := by
  have hDes : Design c := design_of_stage2 (c₀ := c₀) (c := c) (L := L) hE hP hD₀ hLC hAlt hCF
  exact (design_iff_admissible hn).mpr hDes

/-- **THE VERIFICATION CRITERION OF THE PUBLISHED SECOND STAGE, AS AN IFF.**  Under the structural
hypotheses of `design_of_stage2` (a first-stage `Design`, the extension interface, leaf closure and
properness) the extension is admissible **exactly** when the two bad events `B_D` and `C_{D,i}` are
absent.  Sufficiency is `admissible_of_stage2`; necessity is `NoAltCycle.of_admissible` and
`NoCrossFresh.of_admissible`.  So the residual hypothesis of `StageFamily` is not an artefact of
this formalisation: it is precisely the published verification condition, and nothing else is needed.
This is the round-31 blocker "the composition theorem is not proved" closed in BOTH directions. -/
theorem admissible_iff_stage2 {n k K : ℕ} {c₀ : Col n k} {c : Col n (k + K)}
    {L : Finset (Sym2 (Verts n))} (hE : Extends (liftCol c₀ (Nat.le_add_right k K)) c L)
    (hP : Proper c L) (hD₀ : Design c₀) (hLC : LeafClosed c₀ L) (hn : 4 ≤ n) :
    Admissible c ↔ NoAltCycle c L ∧ NoCrossFresh c₀ c L :=
  ⟨fun hc => And.intro (NoAltCycle.of_admissible hc) (NoCrossFresh.of_admissible hE hc),
    fun h => admissible_of_stage2 hE hP hD₀ hLC h.1 h.2 hn⟩

private theorem not_mem_leftover_loop {n k : ℕ} {c : Col n k} (a : Verts n) :
    s(a, a) ∉ leftover c := by
  intro h
  obtain ⟨h1, h2⟩ := mem_leftover.mp h
  exact h2 ((mem_edgeFinset.mp h1).2 a a rfl rfl).elim

/-- **LEAF CLOSURE IS FREE FOR THE LABELLED-TRIANGLE ENCODING.**  If the colouring is covered by
labelled triangles with the matching condition, then the edge joining the two leaves of every
two-edge path is covered, i.e. it lies in no leftover edge.  (This is where the two-edge paths of
arXiv:2208.12563 §4 come from: they are the path edges of a labelled triangle, whose third edge is
the leaf edge.) -/
theorem leafClosed_of_tri {n k : ℕ} {c : Col n k} (hC : Covers c) (hP : PairFree c) :
    LeafClosed c (leftover c) := by
  intro i v p q hN
  rcases eq_or_ne p q with hpq | hpq
  · -- the degenerate two-edge path `p - v - p`: `s(p, p)` is a loop, not an edge of `K_n`
    exact hpq ▸ not_mem_leftover_loop p
  · have hcard : (Nbrs c i v).card = 2 := by rw [hN]; simp [hpq]
    obtain ⟨u, p', q', h, hv, hN', hpN, hqN⟩ := centre_of_card_two hC hP hcard
    have hpq1 : p' = p ∨ p' = q := by
      rw [hN] at hpN
      rcases Finset.mem_insert.mp hpN with hz | hz
      · exact Or.inl hz
      · rcases Finset.mem_insert.mp hz with hz' | hz'
        · exact Or.inr hz'
        · simp at hz'
    have hpq2 : q' = p ∨ q' = q := by
      rw [hN] at hqN
      rcases Finset.mem_insert.mp hqN with hz | hz
      · exact Or.inl hz
      · rcases Finset.mem_insert.mp hz with hz' | hz'
        · exact Or.inr hz'
        · simp at hz'
    have hco : ({p', q'} : Finset (Verts n)) = {p, q} := by
      rcases hpq1 with hp1 | hp1
      · rcases hpq2 with hq2 | hq2
        · exact absurd (hp1.trans hq2.symm) h.2.2.1
        · rw [hp1, hq2]
      · rcases hpq2 with hq2 | hq2
        · apply Finset.ext
          intro z
          simp only [Finset.mem_insert, Finset.mem_singleton, or_false]
          rw [hp1, hq2, or_comm]
        · exact absurd (hp1.trans hq2.symm) h.2.2.1
    have hcov0 : s(p', q') ∈ insert (s(p', q')) (∅ : Finset (Sym2 (Verts n))) :=
      Finset.mem_insert.mpr (Or.inl rfl)
    have hcov1 : s(p', q') ∈ insert (s(u, q')) (insert (s(p', q')) ∅) :=
      Finset.mem_insert.mpr (Or.inr hcov0)
    have hcov : s(p', q') ∈ triEdges c u p' q' := by
      rw [triEdges]
      exact Finset.mem_insert.mpr (Or.inr hcov1)
    refine mem_leftover_of_covered ⟨u, p', q', h, ?_⟩
    rcases hpq1 with hp1 | hp1 <;> rcases hpq2 with hq2 | hq2
    · exact absurd (hp1.trans hq2.symm) h.2.2.1
    · rw [← hp1, ← hq2]
      exact hcov
    · rw [← hp1, ← hq2]
      have hsw : s(p', q') = s(q', p') := Sym2.eq_swap ..
      rw [← hsw]
      exact hcov
    · exact absurd (hp1.trans hq2.symm) h.2.2.1

/-- **THE PUBLISHED CONSTRUCTION IN ITS FAITHFUL TWO-STAGE FORM (arXiv:2208.12563 §4).**  For every
`δ > 0` and all large `m ≡ 1 (mod 6)` there is a first-stage `k`-colouring `c₀` of `K_m` — a family of
labelled triangles with pairwise disjoint `(vertex, colour)` usage, with neither a bad nor a
crossing four-set — whose leftover graph `L = leftover c₀` is given a proper `K`-colouring with fresh
colours avoiding the two bad events `B_D` and `C_{D,i}`, using at most `5(m-1)/6 + δm/6` colours in
total.  Note that leaf closure is *not* assumed: it is automatic for a labelled-triangle system
(`leafClosed_of_tri`). -/
def StageFamily : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ M K : ℕ, ∀ m : ℕ, M ≤ m → m % 6 = 1 →
    ∃ (k : ℕ) (c₀ : Col m k) (c : Col m (k + K)),
      Covers c₀ ∧ PairFree c₀ ∧ NoCrossFour c₀ ∧ NoBadFour c₀ ∧
      Extends (liftCol c₀ (Nat.le_add_right k K)) c (leftover c₀) ∧ Proper c (leftover c₀) ∧
      NoAltCycle c (leftover c₀) ∧
      NoCrossFresh c₀ c (leftover c₀) ∧
      (6 : ℝ) * ((k + K : ℕ) : ℝ) ≤ 5 * ((m - 1 : ℕ) : ℝ) + δ * (m : ℝ)

/-- **THE TWO STAGES COMPOSE INTO ADMISSIBLE COLOURINGS.**  A family as in `StageFamily` gives a
family of admissible colourings of `K_m` using at most `5(m-1)/6 + δm/6` colours: the three
structural conditions of the first stage are *free* for a labelled-triangle system
(`Triangles.tile_of_tri`, `Triangles.packed_of_tri`, `leafClosed_of_tri`), and the second stage is
verified by `admissible_of_stage2`. -/
theorem SlackFamily.of_stage (hfam : StageFamily) : SlackFamily := by
  rw [StageFamily] at hfam
  intro δ hδ
  obtain ⟨M, K, hM⟩ := hfam δ hδ
  refine ⟨max M 4, fun m hMm hm => ?_⟩
  obtain ⟨k, c₀, c, hC, hP, hX, hB, hE, hPr, hAlt, hCF, hk⟩ := hM m (by omega) hm
  have hT : Tile c₀ := tile_of_tri hC hP (by omega)
  have hPk : Packed c₀ := packed_of_tri hC hP (by omega)
  have hLC : LeafClosed c₀ (leftover c₀) := leafClosed_of_tri hC hP
  exact ⟨k + K, c, admissible_of_stage2 hE hPr ⟨hT, hPk, hX, hB⟩ hLC hAlt hCF (by omega), hk⟩

/-- **THE REQUIRED THEOREM `jsp_000140_main`, REDUCED TO THE PUBLISHED TWO-STAGE CONSTRUCTION.**
Together with the lower half proved in `Cherry.lean` (`Main.fiveSixthLower_eg`) this identifies the
remaining content of the prize as exactly the existence of the two-stage construction of
arXiv:2208.12563 §4 with the two bad-event families excluded — and `admissible_of_stage2` says that
*this* is the only condition to be verified. -/
theorem jsp_000140_main_of_stage_family (hfam : StageFamily) : jsp_000140_target :=
  jsp_000140_main_of_slack_family (SlackFamily.of_stage hfam)

end JSP140
