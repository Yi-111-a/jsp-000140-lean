import JSPProblem.VertexSearch

/-!
# The bridge between the `Finset` world and the `Quad` world — `JSP-000140`

`Admissible c` of `Definitions.lean` quantifies over the **finitely many four-element
`Finset`s** of `Verts n`:

```lean
JSP140.Admissible c : Prop :=
  ∀ S : Finset (Verts n), S.card = 4 → 5 ≤ (JSP140.colorsOn c S).card
```

while the pruning test of the searches of `FastSearch.lean` / `VertexSearch.lean` is phrased on the
**increasing quadruples** `Quad n` collected in the list `quadsOf n`.  Turning a certificate of the
search into a theorem about `Admissible` — the engine `EG_ge_of_certC`, which is what pins
`f(7,4,5) = 7` and `f(8,4,5) = 7` — needs the two facts proved here:

* **`mem_quadsOf_of_incQuad`** — every increasing quadruple occurs in the list `quadsOf n`, so the
  search really does test every `K₄` of `K_n`;
* **`exists_quadSet_of_card`** — and conversely, **every four-element vertex set of `K_n` is the
  vertex set of an increasing quadruple**, so a `K₄` of the `Finset` world is tested by the search.

`admissible_iff_all_quads` combines the two into the equivalence the search engine needs:
`Admissible c` iff the six colours of every `K₄` of the list `quadsOf n` span at least five
distinct colours.
-/

namespace JSP140

/-! ### Every increasing quadruple is a member of `quadsOf n` -/

/-- **Every increasing quadruple is one of the `K₄`s the search tests.** -/
theorem mem_quadsOf_of_incQuad {n : ℕ} {q : Quad n} (h : incQuad q) : q ∈ quadsOf n := by
  unfold quadsOf
  refine List.mem_filter.2 ⟨?_, incQuadB_iff.mpr h⟩
  refine List.mem_flatMap.2 ⟨q.a, List.mem_finRange q.a, ?_⟩
  refine List.mem_flatMap.2 ⟨q.b, List.mem_finRange q.b, ?_⟩
  refine List.mem_flatMap.2 ⟨q.c, List.mem_finRange q.c,
    List.mem_map.2 ⟨q.d, List.mem_finRange q.d, rfl⟩⟩

/-- **The `K₄`s of `quadsOf n` are exactly the increasing quadruples.** -/
theorem incQuad_of_mem_quadsOf {n : ℕ} {q : Quad n} (h : q ∈ quadsOf n) : incQuad q := by
  unfold quadsOf at h
  exact incQuadB_iff.mp (List.mem_filter.mp h).2

/-! ### Every four-element vertex set is a `quadSet` -/

private theorem pairwise_lt_of_nodup_pairwise_le {α : Type*} [LinearOrder α] :
    ∀ {l : List α}, l.Nodup → l.Pairwise (· ≤ ·) → l.Pairwise (· < ·) := by
  intro l
  induction l with
  | nil => intro _ _; exact .nil
  | cons a l ih =>
      intro hnd hpw
      refine List.pairwise_cons.2 ⟨?_, ih hnd.tail (List.pairwise_cons.1 hpw).2⟩
      intro b hb
      have h := (List.pairwise_cons.1 hpw).1 b hb
      by_cases he : a = b
      · exact False.elim (((List.pairwise_cons.1 hnd).1 a (he ▸ hb)) rfl)
      · exact lt_of_le_of_ne h he

/-- **Every four-element vertex set of `K_n` is the vertex set of an increasing quadruple**, hence
a member of `quadsOf n`.  This is the fact that lets the pruning test of the search stand in for
`Admissible`. -/
theorem exists_quadSet_of_card {n : ℕ} {S : Finset (Verts n)} (hS : S.card = 4) :
    ∃ q : Quad n, incQuad q ∧ quadSet q = S := by
  classical
  have hpw0 : (S.sort (· ≤ ·)).Pairwise (fun a b : Verts n => a.val < b.val) := by
    refine pairwise_lt_of_nodup_pairwise_le (Finset.sort_nodup (s := S) (r := (· ≤ ·)))
      (Finset.pairwise_sort (s := S) (r := (· ≤ ·)))
  have htoF0 : ((S.sort (· ≤ ·)) : List (Verts n)).toFinset = S :=
    Finset.sort_toFinset (s := S) (r := (· ≤ ·))
  have hlen0 : (S.sort (· ≤ ·)).length = 4 := by
    have h1 : ((S.sort (· ≤ ·)) : List (Verts n)).toFinset.card
        = (S.sort (· ≤ ·)).length :=
      List.toFinset_card_of_nodup (Finset.sort_nodup (s := S) (r := (· ≤ ·)))
    have h2 : ((S.sort (· ≤ ·)) : List (Verts n)).toFinset.card = S.card := by rw [htoF0]
    omega
  obtain ⟨a, b, c, d, hlist⟩ := List.length_eq_four.mp hlen0
  rw [hlist] at hpw0 htoF0
  have hpw : [a, b, c, d].Pairwise (fun a b : Verts n => a.val < b.val) := hpw0
  have htoF : [a, b, c, d].toFinset = S := htoF0
  have hlt1 : a.val < b.val := by
    have h := (List.pairwise_cons.1 hpw).1 b (by simp)
    simpa using h
  have hlt2 : b.val < c.val := by
    have h := (List.pairwise_cons.1 (List.pairwise_cons.1 hpw).2).1 c (by simp)
    simpa using h
  have hlt3 : c.val < d.val := by
    have h := (List.pairwise_cons.1 (List.pairwise_cons.1 (List.pairwise_cons.1 hpw).2).2).1 d
      (by simp)
    simpa using h
  have hmem : ∀ x : Verts n, x = a ∨ x = b ∨ x = c ∨ x = d ↔ x ∈ S := by
    intro x
    rw [← htoF, List.mem_toFinset]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
  refine ⟨⟨a, b, c, d⟩, ⟨⟨hlt1, hlt2, hlt3⟩, ?_⟩⟩
  ext x
  simp only [quadSet, Finset.mem_insert]
  rw [Finset.mem_singleton]
  exact hmem x

/-- **Every four-element vertex set of `K_n` is tested by the search.** -/
theorem exists_mem_quadsOf_of_card {n : ℕ} {S : Finset (Verts n)} (hS : S.card = 4) :
    ∃ q : Quad n, q ∈ quadsOf n ∧ quadSet q = S := by
  obtain ⟨q, hq1, hq2⟩ := exists_quadSet_of_card hS
  exact ⟨q, mem_quadsOf_of_incQuad hq1, hq2⟩

/-! ### The equivalence the search engine needs -/

/-- **`Admissible` is exactly "every `K₄` of the list `quadsOf n` spans at least five colours".** -/
theorem admissible_iff_all_quads {n k : ℕ} (c : Col n k) :
    Admissible c ↔ ∀ q : Quad n, q ∈ quadsOf n →
      decide (5 ≤ ((quadColors c q).toFinset : Finset (Fin k)).card) = true := by
  constructor
  · intro hc q hq
    exact quad_ok_of_admissible (incQuad_of_mem_quadsOf hq) hc
  · intro hall S hS
    obtain ⟨q, hq1, hq2⟩ := exists_mem_quadsOf_of_card hS
    have h1 : 5 ≤ (quadColors c q).toFinset.card := by
      have h := hall q hq1
      exact of_decide_eq_true h
    rw [← hq2, ← quadColors_toFinset c q (incQuad_of_mem_quadsOf hq1)]
    exact h1

/-- **Every admissible colouring passes every `K₄` of the list, with its six colours.** -/
theorem quadColors_of_admissible_mem {n k : ℕ} {c : Col n k} (hc : Admissible c) {q : Quad n}
    (hq : q ∈ quadsOf n) :
    decide (5 ≤ ((quadColors c q).toFinset : Finset (Fin k)).card) = true :=
  (admissible_iff_all_quads c).1 hc q hq

end JSP140
