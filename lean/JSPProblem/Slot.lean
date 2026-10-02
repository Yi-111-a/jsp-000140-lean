import JSPProblem.Second

/-!
# JSP-000140 — the **slot counting** of the first stage: the constant `5/6` as a theorem

This file closes the blocker named at the end of round 35: the formalisation of the slot
counting of the first stage, i.e. of the step that produced the isolated hypothesis
`First.FirstStageCounting`.  Everything here is proved from the two structural conditions of the
published construction — the *labelled-triangle* encoding of arXiv:2208.12563 §4
(`Triangles.lean`) and the leftover-graph vocabulary of arXiv:2207.02920 Claim 4
(`Second.lean`) — and **no four-vertex clique is ever checked**.

## The counting

A labelled triangle `(u,p,q)` uses the five `(vertex, colour)` pairs

    `(u,i), (p,i), (q,i), (p,j), (q,j)`,   `i = c s(u,p) = c s(u,q) ≠ j = c s(p,q)`,

which are exactly the hypervertices `{u_i, v_i, w_i, v_j, w_j}` of the auxiliary `8`-uniform
hypergraph `H` of arXiv:2208.12563 §4.  A matching in `H` uses each of them at most once
(`PairFree`), and there are `n·k` of them.  Hence:

* **`triPairs_eq_anchorPairs`** — the five pairs of a labelled triangle depend only on its
  *vertex set* and on the colouring: they are the "anchor" pairs `(v,i)` with `i` the colour of
  an edge of the triangle at `v`.  This is the ingredient round 35 was missing; it replaces the
  impossible "canonical labelling" by a finset-valued one;
* **`card_triPairs`** — the five pairs are distinct, so each triangle uses five slots;
* **`triSets`** — the finset of *vertex sets* of labelled triangles (the image of the finset of
  labelled triangles, so no representative has to be chosen), with `Tri3` and `Lin3` of round 35
  available for it (`lin3_triSets`: two triangles sharing an edge are the same triangle, by
  `PairFree`);
* **`Slots`, `card_Slots`, `slots_five`** — the slots of the distinct triangles are distinct
  `(vertex, colour)` pairs, so

      **`5 · |triSets| ≤ n · k`,**

  the slot counting, whose ratio "five slots per three edges" is the source of the constant
  `5/6` of the catalog answer;
* **`edgeCover_count`** — the exact accounting of the first stage,

      **`C(n,2) = 3 · |triSets| + |leftover c|`**,

  every edge of `K_n` being either in a unique labelled triangle or leftover;
* **`handshake_le`, `sum_DegL_two_mul_card`, `sum_degL_edgeFinset`** — the handshaking lemma
  for a leftover graph of maximum degree `D` in the sharp form `2 · |L| ≤ n · D`, together with
  `2 · C(n,2) = n(n-1)`.

`First.count_lower` then combines the three of them into

      **`5(n-1) ≤ 6k + 5D`   (`First.FirstStageCounting`)**

from `PairFree` and `SparseL (leftover c) D` alone — the statement round 35 had to isolate as a
hypothesis.
-/

set_option maxHeartbeats 1200000
set_option linter.unusedVariables false

namespace JSP140

attribute [local instance] Classical.propDecidable

variable {n k : ℕ}

/-! ### Small helpers -/

/-- Two elements of a finset of cardinality at least two. -/
private theorem exists_two_mem' {α : Type*} [DecidableEq α] {s : Finset α} (h : 2 ≤ s.card) :
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

/-- The edges spanned inside a vertex subset are a subset of the edges spanned inside the
superset. -/
private theorem edgeFinset_sub {n : ℕ} {S T : Finset (Verts n)} (hST : S ⊆ T) :
    edgeFinset S ⊆ edgeFinset T := by
  intro e he
  obtain ⟨a, b, rfl⟩ : ∃ a b : Verts n, e = s(a, b) :=
    Quot.inductionOn e (fun p : Verts n × Verts n => ⟨p.1, p.2, rfl⟩)
  rw [mem_edgeFinset] at he ⊢
  obtain ⟨h1, h2⟩ := he
  have ha : a ∈ S := Finset.mem_sym2_iff.mp h1 a (Sym2.mem_mk_left a b)
  have hb : b ∈ S := Finset.mem_sym2_iff.mp h1 b (Sym2.mem_mk_right a b)
  exact ⟨Finset.mem_sym2_iff.mpr fun z hz => by
    rw [Sym2.mem_iff] at hz
    rcases hz with hz | hz
    · rw [hz]; exact hST ha
    · rw [hz]; exact hST hb, h2⟩

/-! ### 1. The slots of a vertex set -/

/-- **THE ANCHOR SLOTS OF A VERTEX SET.**  `(x,j) ∈ anchorPairs c T` iff `x ∈ T` and `j` is the
colour of one of the edges of the triangle on `T` at `x`.

This is the replacement for round 35's impossible "canonical labelling": the slots of a labelled
triangle are determined by its *vertex set* and the colouring, so the slot count can be carried
out on finsets of vertex sets without ever choosing a representative labelling. -/
noncomputable def anchorPairs {n k : ℕ} (c : Col n k) (T : Finset (Verts n)) :
    Finset (Verts n × Fin k) :=
  T.biUnion fun x => (T.erase x).image fun y => (x, c s(x, y))

@[simp] theorem mem_anchorPairs {n k : ℕ} {c : Col n k} {T : Finset (Verts n)} {x : Verts n}
    {j : Fin k} :
    (x, j) ∈ anchorPairs c T ↔ x ∈ T ∧ ∃ y ∈ T, y ≠ x ∧ c s(x, y) = j := by
  unfold anchorPairs
  rw [Finset.mem_biUnion]
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨a, ha, y, hmem, heq⟩
    rw [Finset.mem_erase] at hmem
    rw [Prod.mk.injEq] at heq
    exact ⟨heq.1 ▸ ha, y, hmem.2, heq.1 ▸ hmem.1, heq.1.symm ▸ heq.2⟩
  · rintro ⟨hx, y, hy, hyn, hcy⟩
    exact ⟨x, hx, y, Finset.mem_erase.mpr ⟨hyn, hy⟩, by rw [hcy]⟩

/-- **THE FIVE SLOTS OF A LABELLED TRIANGLE ARE THE ANCHOR SLOTS OF ITS VERTEX SET.**  The five
pairs of arXiv:2208.12563 §4 depend only on the vertex set of the triangle and on the colouring
— not on which of the two leaves is called `p`. -/
theorem triPairs_eq_anchorPairs {n k : ℕ} {c : Col n k} {u p q : Verts n} (h : LabTri c u p q) :
    triPairs c u p q = anchorPairs c (triVerts u p q) := by
  refine Finset.Subset.antisymm ?_ ?_
  · intro vp hvp
    obtain ⟨x, j, rfl⟩ : ∃ a : Verts n, ∃ b : Fin k, vp = (a, b) := ⟨vp.1, vp.2, rfl⟩
    rw [mem_triPairs] at hvp
    rcases hvp with ⟨hj, hx⟩ | ⟨hj, hx⟩
    · rcases hx with hxu | hxp | hxq
      · exact mem_anchorPairs.mpr ⟨by rw [hxu]; simp, p, by simp, by rw [hxu]; exact Ne.symm h.1,
          by rw [hxu]; exact hj.symm⟩
      · exact mem_anchorPairs.mpr ⟨by rw [hxp]; simp, u, by simp, by rw [hxp]; exact h.1,
          by rw [hxp, Sym2.eq_swap]; exact hj.symm⟩
      · exact mem_anchorPairs.mpr ⟨by rw [hxq]; simp, u, by simp, by rw [hxq]; exact h.2.1,
          by rw [hxq, Sym2.eq_swap, ← h.2.2.2.1]; exact hj.symm⟩
    · rcases hx with hxp | hxq
      · exact mem_anchorPairs.mpr ⟨by rw [hxp]; simp, q, by simp, by rw [hxp]; exact Ne.symm h.2.2.1,
          by rw [hxp]; exact hj.symm⟩
      · exact mem_anchorPairs.mpr ⟨by rw [hxq]; simp, p, by simp, by rw [hxq]; exact h.2.2.1,
          by rw [hxq, Sym2.eq_swap]; exact hj.symm⟩
  · intro vp hvp
    obtain ⟨x, j, rfl⟩ : ∃ a : Verts n, ∃ b : Fin k, vp = (a, b) := ⟨vp.1, vp.2, rfl⟩
    rw [mem_anchorPairs] at hvp
    obtain ⟨hxv, y, hyv, hyx, hc⟩ := hvp
    have hedge : s(x, y) ∈ triEdges c u p q := by
      rw [triEdges_eq_edgeFinset h]
      exact mem_edgeFinset_mk hxv hyv (Ne.symm hyx)
    rcases eq_triEdges hedge with he | he | he
    · have hxy : x = u ∨ x = p := Sym2.mem_iff.mp (he ▸ Sym2.mem_mk_left x y)
      have hxy3 : x = u ∨ x = p ∨ x = q := hxy.elim Or.inl (fun h => Or.inr (Or.inl h))
      exact mem_triPairs.mpr (Or.inl ⟨(he ▸ hc).symm, hxy3⟩)
    · have hxy : x = u ∨ x = q := Sym2.mem_iff.mp (he ▸ Sym2.mem_mk_left x y)
      have hxy3 : x = u ∨ x = p ∨ x = q := hxy.elim Or.inl (fun h => Or.inr (Or.inr h))
      exact mem_triPairs.mpr (Or.inl ⟨(he ▸ hc).symm.trans h.2.2.2.1.symm, hxy3⟩)
    · have hxy : x = p ∨ x = q := Sym2.mem_iff.mp (he ▸ Sym2.mem_mk_left x y)
      exact mem_triPairs.mpr (Or.inr ⟨(he ▸ hc).symm, hxy⟩)

/-- **EACH LABELLED TRIANGLE USES EXACTLY FIVE SLOTS.** -/
theorem card_triPairs {n k : ℕ} {c : Col n k} {u p q : Verts n} (h : LabTri c u p q) :
    (triPairs c u p q).card = 5 := by
  have hne := LabTri.ne h
  have hcol : c s(u, p) ≠ c s(p, q) := h.2.2.2.2
  have e1 : (u, c s(u, p)) ∉ insert (p, c s(u, p)) (insert (q, c s(u, p))
      (insert (p, c s(p, q)) (insert (q, c s(p, q)) (∅ : Finset (Verts n × Fin k))))) := by
    intro hc
    rw [Finset.mem_insert] at hc
    rcases hc with hc | hc
    · exact hne.1 (congrArg Prod.fst hc)
    · rw [Finset.mem_insert] at hc
      rcases hc with hc | hc
      · exact hne.2.1 (congrArg Prod.fst hc)
      · rw [Finset.mem_insert] at hc
        rcases hc with hc | hc
        · exact hne.1 (congrArg Prod.fst hc)
        · rw [Finset.mem_insert] at hc
          rcases hc with hc | hc
          · exact hne.2.1 (congrArg Prod.fst hc)
          · simp at hc
  have e2 : (p, c s(u, p)) ∉ insert (q, c s(u, p)) (insert (p, c s(p, q))
      (insert (q, c s(p, q)) (∅ : Finset (Verts n × Fin k)))) := by
    intro hc
    rw [Finset.mem_insert] at hc
    rcases hc with hc | hc
    · exact hne.2.2 (congrArg Prod.fst hc)
    · rw [Finset.mem_insert] at hc
      rcases hc with hc | hc
      · exact hcol (congrArg Prod.snd hc)
      · rw [Finset.mem_insert] at hc
        rcases hc with hc | hc
        · exact hne.2.2 (congrArg Prod.fst hc)
        · simp at hc
  have e3 : (q, c s(u, p)) ∉ insert (p, c s(p, q))
      (insert (q, c s(p, q)) (∅ : Finset (Verts n × Fin k))) := by
    intro hc
    rw [Finset.mem_insert] at hc
    rcases hc with hc | hc
    · exact hne.2.2 (Eq.symm (congrArg Prod.fst hc))
    · rw [Finset.mem_insert] at hc
      rcases hc with hc | hc
      · exact hcol (congrArg Prod.snd hc)
      · simp at hc
  have e4 : (p, c s(p, q)) ∉ insert (q, c s(p, q)) (∅ : Finset (Verts n × Fin k)) := by
    intro hc
    rw [Finset.mem_insert] at hc
    rcases hc with hc | hc
    · exact hne.2.2 (congrArg Prod.fst hc)
    · simp at hc
  have e5 : (q, c s(p, q)) ∉ (∅ : Finset (Verts n × Fin k)) := by simp
  rw [triPairs, Finset.card_insert_of_notMem e1, Finset.card_insert_of_notMem e2,
    Finset.card_insert_of_notMem e3, Finset.card_insert_of_notMem e4,
    Finset.card_insert_of_notMem e5]
  simp

/-- The vertex set of a labelled triangle carries exactly five slots. -/
theorem card_anchorPairs_of_tri {n k : ℕ} {c : Col n k} {u p q : Verts n} (h : LabTri c u p q) :
    (anchorPairs c (triVerts u p q)).card = 5 := by
  calc (anchorPairs c (triVerts u p q)).card = (triPairs c u p q).card := by
        rw [triPairs_eq_anchorPairs h]
    _ = 5 := card_triPairs h

/-! ### 2. The vertex sets of the labelled triangles -/

/-- **THE VERTEX SETS OF THE LABELLED TRIANGLES OF `c`.**  The image of the finset of labelled
triangles, so that no representative labelling has to be chosen — the point of the
construction. -/
noncomputable def triSets {n k : ℕ} (c : Col n k) : Finset (Finset (Verts n)) :=
  (Finset.filter (fun t : Verts n × Verts n × Verts n => LabTri c t.1 t.2.1 t.2.2)
    (Finset.univ : Finset (Verts n × Verts n × Verts n))).image
    (fun t : Verts n × Verts n × Verts n => triVerts t.1 t.2.1 t.2.2)

theorem mem_triSets {n k : ℕ} {c : Col n k} {T : Finset (Verts n)} :
    T ∈ triSets c ↔ ∃ u p q : Verts n, LabTri c u p q ∧ triVerts u p q = T := by
  unfold triSets
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨t, ht, heq⟩
    obtain ⟨u, p, q⟩ := t
    exact ⟨u, p, q, ht, heq⟩
  · rintro ⟨u, p, q, h, rfl⟩
    exact ⟨(u, p, q), h, rfl⟩

/-- Every vertex set of `triSets c` is a triple: `triSets c` is a triple system. -/
theorem card_mem_triSets {n k : ℕ} {c : Col n k} {T : Finset (Verts n)} (hT : T ∈ triSets c) :
    T.card = 3 := by
  obtain ⟨u, p, q, h, hE⟩ := mem_triSets.mp hT
  rw [← hE, card_triVerts (LabTri.ne h)]

/-- **TWO TRIANGLES OF THE SYSTEM SHARE AN EDGE ONLY IF THEY ARE THE SAME TRIANGLE.**  So
`triSets c` is *linear*, the edge-disjointness of the first stage of arXiv:2208.12563 §4 — and
this is where `PairFree` is used the first time. -/
theorem lin3_triSets {n k : ℕ} {c : Col n k} (hP : PairFree c) :
    ∀ T T' : Finset (Verts n), T ∈ triSets c → T' ∈ triSets c → T ≠ T' → (T ∩ T').card ≤ 1 := by
  intro T T' hT hT' hTT'
  have key : ∀ (x y : Verts n), x ∈ T → y ∈ T → x ∈ T' → y ∈ T' → x ≠ y → False := by
    intro x y hxT hyT hxT' hyT' hxy
    obtain ⟨u, p, q, h1, hE1⟩ := mem_triSets.mp hT
    obtain ⟨u', p', q', h2, hE2⟩ := mem_triSets.mp hT'
    have hxe1 : s(x, y) ∈ triEdges c u p q := by
      rw [triEdges_eq_edgeFinset h1, hE1]
      exact mem_edgeFinset_mk hxT hyT hxy
    have hxe2 : s(x, y) ∈ triEdges c u' p' q' := by
      rw [triEdges_eq_edgeFinset h2, hE2]
      exact mem_edgeFinset_mk hxT' hyT' hxy
    have hvv := triVerts_eq_of_mem_triEdges hP h1 h2 (Finset.mem_inter.mpr ⟨hxe1, hxe2⟩)
    exact absurd (hE1.symm.trans (hvv.trans hE2)) hTT'
  by_contra hcon
  have h2 : 2 ≤ (T ∩ T').card := by omega
  obtain ⟨x, y, hxy, hmem⟩ := exists_two_mem' h2
  obtain ⟨hxT, hxT'⟩ := Finset.mem_inter.mp hmem.1
  obtain ⟨hyT, hyT'⟩ := Finset.mem_inter.mp hmem.2
  exact key x y hxT hyT hxT' hyT' hxy

/-! ### 3. The slot counting -/

/-- **THE SLOTS OF THE WHOLE FIRST STAGE.** -/
noncomputable def Slots {n k : ℕ} (c : Col n k) : Finset (Verts n × Fin k) :=
  (triSets c).biUnion (anchorPairs c)

theorem mem_Slots {n k : ℕ} {c : Col n k} {vp : Verts n × Fin k} :
    vp ∈ Slots c ↔ ∃ T ∈ triSets c, vp ∈ anchorPairs c T := Finset.mem_biUnion

/-- **THE SLOTS OF THE FIRST STAGE ARE `5 · |triSets c|` IN NUMBER.**  The five slots of two
different triangles are disjoint (`PairFree`), and there are five of them each. -/
theorem card_Slots {n k : ℕ} {c : Col n k} (hP : PairFree c) :
    (Slots c).card = 5 * (triSets c).card := by
  have hcard : ∀ T ∈ triSets c, (anchorPairs c T).card = 5 := by
    intro T hT
    obtain ⟨u, p, q, h, hE⟩ := mem_triSets.mp hT
    have h1 : anchorPairs c T = triPairs c u p q := by
      rw [triPairs_eq_anchorPairs h, ← hE]
    rw [h1, card_triPairs h]
  calc (Slots c).card = ∑ T ∈ triSets c, (anchorPairs c T).card := by
        rw [Slots, Finset.card_biUnion (fun a ha b hb hab => by
              refine Finset.disjoint_left.2 ?_
              intro x hxa hxb
              obtain ⟨u, p, q, h1, hE1⟩ := mem_triSets.mp ha
              obtain ⟨u', p', q', h2, hE2⟩ := mem_triSets.mp hb
              obtain ⟨y, j, rfl⟩ : ∃ a : Verts n, ∃ b : Fin k, x = (a, b) := ⟨x.1, x.2, rfl⟩
              have hxa1 : (y, j) ∈ triPairs c u p q :=
                (triPairs_eq_anchorPairs h1).symm ▸ (hE1.symm ▸ hxa)
              have hxb1 : (y, j) ∈ triPairs c u' p' q' :=
                (triPairs_eq_anchorPairs h2).symm ▸ (hE2.symm ▸ hxb)
              have hvv := hP.of_common h1 h2 (Finset.mem_inter.mpr ⟨hxa1, hxb1⟩)
              exact hab (hE1.symm.trans (hvv.trans hE2)))]
    _ = ∑ _T ∈ triSets c, 5 := Finset.sum_congr rfl (fun T hT => hcard T hT)
    _ = 5 * (triSets c).card := by rw [Finset.sum_const]; norm_num [Nat.mul_comm]

/-- **THE SLOT COUNTING.**  A matching in the auxiliary `8`-uniform hypergraph of
arXiv:2208.12563 §4 uses each of the `n·k` `(vertex, colour)` pairs at most once and five pairs
per triangle, so

    `5 · |triSets c| ≤ n · k`.

This is the whole content of the constant `5/6`: five slots buy three edges. -/
theorem slots_five {n k : ℕ} {c : Col n k} (hP : PairFree c) : 5 * (triSets c).card ≤ n * k := by
  have h1 := card_Slots hP
  have h2 : (Slots c).card ≤ (Finset.univ : Finset (Verts n × Fin k)).card :=
    Finset.card_le_card fun vp _ => Finset.mem_univ vp
  have h3 : ((Finset.univ : Finset (Verts n × Fin k)).card) = n * k := by
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  omega

/-- The slots of the first stage lie in `V × [k]`, whose cardinality is `n·k`: the same bound,
stated directly about the finset. -/
theorem card_Slots_le {n k : ℕ} {c : Col n k} (hP : PairFree c) :
    (Slots c).card ≤ (Finset.univ : Finset (Verts n × Fin k)).card :=
  Finset.card_le_card fun vp _ => Finset.mem_univ vp

/-! ### 4. The accounting of the covered edges -/

/-- **THE EDGES COVERED BY THE FIRST STAGE.** -/
noncomputable def covered {n k : ℕ} (c : Col n k) : Finset (Sym2 (Verts n)) :=
  (triSets c).biUnion edgeFinset

theorem mem_covered {n k : ℕ} {c : Col n k} {e : Sym2 (Verts n)} :
    e ∈ covered c ↔ ∃ T ∈ triSets c, e ∈ edgeFinset T := Finset.mem_biUnion

/-- A covered edge lies in a labelled triangle. -/
theorem covered_is_Covered {n k : ℕ} {c : Col n k} {e : Sym2 (Verts n)} (he : e ∈ covered c) :
    Covered c e := by
  obtain ⟨T, hT, heT⟩ := mem_covered.mp he
  obtain ⟨u, p, q, h, hE⟩ := mem_triSets.mp hT
  refine ⟨u, p, q, h, ?_⟩
  rw [triEdges_eq_edgeFinset h, hE]
  exact heT

/-- Every covered edge is covered by a labelled triangle of `triSets c`. -/
theorem covered_of_Covered {n k : ℕ} {c : Col n k} {e : Sym2 (Verts n)} (h : Covered c e) :
    e ∈ covered c := by
  obtain ⟨u, p, q, h1, he1⟩ := h
  refine mem_covered.mpr ⟨triVerts u p q, mem_triSets.mpr ⟨u, p, q, h1, rfl⟩, ?_⟩
  exact (triEdges_eq_edgeFinset h1).symm ▸ he1

theorem covered_subset {n k : ℕ} (c : Col n k) : covered c ⊆ edgeFinset (Finset.univ : Finset (Verts n)) := by
  intro e he
  obtain ⟨T, hT, heT⟩ := mem_covered.mp he
  exact edgeFinset_sub (S := T) (fun x _ => Finset.mem_univ x) heT

/-- **THE EXACT ACCOUNTING OF THE FIRST STAGE.**

      **`C(n,2) = 3 · |triSets c| + |leftover c|`:**

every edge of `K_n` lies in exactly one labelled triangle, or is leftover.  This is the *other*
half of the slot counting: `3` edges per triangle. -/
theorem edgeCover_count {n k : ℕ} {c : Col n k} (hP : PairFree c) :
    (edgeFinset (Finset.univ : Finset (Verts n))).card = 3 * (triSets c).card + (leftover c).card := by
  have hcard : ∀ T ∈ triSets c, (edgeFinset T).card = 3 := by
    intro T hT
    obtain ⟨u, p, q, h, hE⟩ := mem_triSets.mp hT
    rw [← hE, card_edgeFinset, card_triVerts (LabTri.ne h)]
    decide
  have hcardc : (covered c).card = 3 * (triSets c).card := by
    calc (covered c).card = ∑ T ∈ triSets c, (edgeFinset T).card := by
          rw [covered, Finset.card_biUnion (fun a ha b hb hab => by
                refine Finset.disjoint_left.2 ?_
                intro e hea heb
                obtain ⟨u, p, q, h1, hE1⟩ := mem_triSets.mp ha
                obtain ⟨u', p', q', h2, hE2⟩ := mem_triSets.mp hb
                have hea1 : e ∈ triEdges c u p q := by
                  rw [triEdges_eq_edgeFinset h1]
                  exact hE1.symm ▸ hea
                have heb1 : e ∈ triEdges c u' p' q' := by
                  rw [triEdges_eq_edgeFinset h2]
                  exact hE2.symm ▸ heb
                have hvv := triVerts_eq_of_mem_triEdges hP h1 h2
                  (Finset.mem_inter.mpr ⟨hea1, heb1⟩)
                exact hab (hE1.symm.trans (hvv.trans hE2)))]
      _ = ∑ _T ∈ triSets c, 3 := Finset.sum_congr rfl (fun T hT => hcard T hT)
      _ = 3 * (triSets c).card := by rw [Finset.sum_const]; norm_num [Nat.mul_comm]
  have hsub : covered c ⊆ edgeFinset (Finset.univ : Finset (Verts n)) := covered_subset c
  have hLsub : leftover c ⊆ edgeFinset (Finset.univ : Finset (Verts n)) :=
    fun _ he => (mem_leftover.mp he).1
  have hdisj : covered c ∩ leftover c = ∅ := by
    refine Finset.eq_empty_iff_forall_notMem.mpr fun e he => ?_
    obtain ⟨he1, he2⟩ := Finset.mem_inter.mp he
    exact mem_leftover_of_covered (covered_is_Covered he1) he2
  have hunion : (edgeFinset (Finset.univ : Finset (Verts n))) = covered c ∪ leftover c := by
    refine Finset.Subset.antisymm ?_ ?_
    · intro e he
      refine Finset.mem_union.mpr ?_
      by_cases hd : Covered c e
      · exact Or.inl (covered_of_Covered hd)
      · exact Or.inr (mem_leftover.mpr ⟨he, hd⟩)
    · intro e he
      rcases Finset.mem_union.mp he with he | he
      · exact hsub he
      · exact hLsub he
  have hcardE : (edgeFinset (Finset.univ : Finset (Verts n))).card
      = (covered c).card + (leftover c).card := by
    have h := Finset.card_union_add_card_inter (s := covered c) (t := leftover c)
    rw [hdisj, Finset.card_empty, ← hunion] at h
    exact h
  omega

/-! ### 5. The handshaking lemma, in the form the budget needs -/

/-- An edge of `K_n` has two endpoints. -/
private theorem card_two_of_edge {n : ℕ} {e : Sym2 (Verts n)} (he : OffDiag e) :
    ((Finset.univ : Finset (Verts n)).filter (fun v => v ∈ e)).card = 2 := by
  obtain ⟨a, b, rfl⟩ := Sym2.exists.mp ⟨e, rfl⟩
  have hab : a ≠ b := he a b rfl
  have heq : ((Finset.univ : Finset (Verts n)).filter (fun v => v ∈ s(a, b)))
      = ({a, b} : Finset (Verts n)) := by
    ext v
    constructor
    · intro hv
      rw [Finset.mem_filter] at hv
      rcases (Sym2.mem_iff.mp hv.2) with hv' | hv'
      · simp [hv']
      · simp [hv']
    · intro hv
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ v, ?_⟩
      rcases (show v = a ∨ v = b by simpa using hv) with hv' | hv'
      · rw [hv']; exact Sym2.mem_mk_left a b
      · rw [hv']; exact Sym2.mem_mk_right a b
  rw [heq]
  exact Finset.card_eq_two.mpr ⟨a, b, hab, by simp⟩

/-- **THE HANDSHAKING LEMMA.**  Every edge has two endpoints, so the degrees of a graph sum to
twice its number of edges. -/
theorem sum_DegL_two_mul_card {n : ℕ} {L : Finset (Sym2 (Verts n))}
    (hL : L ⊆ edgeFinset (Finset.univ : Finset (Verts n))) :
    ∑ v : Verts n, DegL L v = 2 * L.card := by
  have h1 : ∀ v : Verts n, DegL L v = ∑ e ∈ L, (if v ∈ e then (1 : ℕ) else 0) := by
    intro v
    unfold DegL
    have h : (L.filter (fun e => v ∈ e)).card
        = ∑ e ∈ L, (if v ∈ e then (1 : ℕ) else 0) := by
      calc (L.filter (fun e => v ∈ e)).card
          = ∑ e ∈ L.filter (fun e => v ∈ e), (1 : ℕ) := Finset.card_eq_sum_ones _
        _ = ∑ e ∈ L, (if v ∈ e then (1 : ℕ) else 0) := Finset.sum_filter _ _
    exact h
  have h2 : ∀ e ∈ L, ∑ v : Verts n, (if v ∈ e then (1 : ℕ) else 0) = 2 := by
    intro e he
    have hd : ((Finset.univ : Finset (Verts n)).filter (fun v => v ∈ e)).card = 2 :=
      card_two_of_edge ((mem_edgeFinset.mp (hL he)).2)
    have h3 : ∑ v ∈ (Finset.univ : Finset (Verts n)), (if v ∈ e then (1 : ℕ) else 0)
        = ((Finset.univ : Finset (Verts n)).filter (fun v => v ∈ e)).card := by
      calc ∑ v ∈ (Finset.univ : Finset (Verts n)), (if v ∈ e then (1 : ℕ) else 0)
          = ∑ v ∈ (Finset.univ : Finset (Verts n)).filter (fun v => v ∈ e), (1 : ℕ) :=
            (Finset.sum_filter _ _).symm
        _ = ((Finset.univ : Finset (Verts n)).filter (fun v => v ∈ e)).card :=
            (Finset.card_eq_sum_ones _).symm
    rw [h3]
    exact hd
  calc ∑ v : Verts n, DegL L v
      = ∑ v ∈ (Finset.univ : Finset (Verts n)), ∑ e ∈ L, (if v ∈ e then (1 : ℕ) else 0) :=
        Finset.sum_congr rfl (fun v _ => h1 v)
    _ = ∑ e ∈ L, ∑ v ∈ (Finset.univ : Finset (Verts n)), if v ∈ e then 1 else 0 := Finset.sum_comm
    _ = ∑ _e ∈ L, 2 := Finset.sum_congr rfl (fun e he => h2 e he)
    _ = 2 * L.card := by rw [Finset.sum_const]; ring

/-- **THE TOTAL FORM OF THE DENSITY BOUND, SHARPLY.**  A leftover graph of maximum degree `D`
has at most `nD/2` edges — the exact form of arXiv:2207.02920 Claim 4, and the reason the
counting below has a `5D` and not a `10D` slack. -/
theorem handshake_le {n D : ℕ} {L : Finset (Sym2 (Verts n))}
    (hL : L ⊆ edgeFinset (Finset.univ : Finset (Verts n))) (hD : SparseL L D) :
    2 * L.card ≤ n * D := by
  have h1 := sum_DegL_two_mul_card hL
  have h2 : (∑ v : Verts n, DegL L v) ≤ ∑ v : Verts n, D :=
    Finset.sum_le_sum fun v _ => hD v
  have h3 : (∑ v : Verts n, D) = n * D := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    norm_num
  omega

end JSP140
