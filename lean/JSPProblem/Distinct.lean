import JSPProblem.Search

/-!
# Counting distinct colours without a `Finset` — `JSP-000140`

The pruning test of every search of this development (`FastSearch.quadOKC`, used by
`FastSearch.lean`, `VertexSearch.lean` and `LeafFree.lean`) asks

```lean
decide (5 ≤ (l.toFinset : Finset (Fin k)).card)
```

for the list `l` of the six colours of a `K₄`.  In compiled code `Finset` insertion is a
red-black-tree insertion: **six of them per `K₄` test**, and the searches of this development
perform of the order `10^8` such tests (the certificate "no admissible 7-colouring of `K₉`" needs
270 000 000 of them).

`insAll l []` computes the same number — the *length of the duplicate-free list of the elements of
`l`* — with a linear scan per element and no allocation when the element is already present:

* `insAll_nil_toFinset` and `ndist_eq_card` — **`ndist l = (l.toFinset).card`**, the fact that makes
  the two tests interchangeable;
* **`decide_ndist`** — the two `decide`s agree, which is all that is needed to replace the `Finset`
  test inside `quadOKC` without changing a single proof of the search engines.

This is the second of the two concrete optimisations named in blocker **B2′** of round 21 ("replace
`l.toFinset` by a `List`-level distinctness count"), the first being the removal of the leaf test
(`LeafFree.lean`).
-/

namespace JSP140
/-! ### The number of distinct colours, without a `Finset` -/

/-- **Insert `x` into a duplicate-free list**, if it is not there already. -/
def insNew {α : Type} [DecidableEq α] (x : α) (l : List α) : List α :=
  if x ∈ l then l else x :: l

/-- **The duplicate-free list of all the elements of two lists.** -/
def insAll {α : Type} [DecidableEq α] : List α → List α → List α
  | [], acc => acc
  | x :: xs, acc => insAll xs (insNew x acc)

theorem mem_insNew_iff {α : Type} [DecidableEq α] (x y : α) (l : List α) :
    y ∈ insNew x l ↔ y = x ∨ y ∈ l := by
  by_cases h : x ∈ l
  · simp only [insNew, if_pos h]
    constructor
    · intro hy
      exact Or.inr hy
    · intro hy
      rcases hy with he | he
      · rw [he]; exact h
      · exact he
  · simp only [insNew, if_neg h]
    constructor
    · intro hy
      rcases List.mem_cons.mp hy with he | he
      · exact Or.inl he
      · exact Or.inr he
    · intro hy
      rcases hy with he | he
      · exact List.mem_cons.mpr (Or.inl he)
      · exact List.mem_cons.mpr (Or.inr he)

theorem insNew_mem {α : Type} [DecidableEq α] (x : α) (l : List α) : x ∈ insNew x l :=
  (mem_insNew_iff x x l).2 (Or.inl rfl)

theorem insNew_nodup {α : Type} [DecidableEq α] (x : α) {l : List α} (h : l.Nodup) :
    (insNew x l).Nodup := by
  by_cases hm : x ∈ l
  · simp [insNew, hm, h]
  · simp only [insNew, if_neg hm]
    exact List.Pairwise.cons (fun a ha he => hm (he ▸ ha)) h

theorem insAll_mem {α : Type} [DecidableEq α] {l acc : List α} {y : α} :
    y ∈ insAll l acc ↔ y ∈ acc ∨ y ∈ l := by
  induction l generalizing acc with
  | nil => simp [insAll]
  | cons x xs ih =>
      simp only [insAll, ih, mem_insNew_iff, List.mem_cons]
      tauto

theorem insAll_nodup {α : Type} [DecidableEq α] {l acc : List α} (h : acc.Nodup) :
    (insAll l acc).Nodup := by
  induction l generalizing acc with
  | nil => exact h
  | cons x xs ih => exact ih (insNew_nodup x h)

theorem insAll_nil_toFinset {α : Type} [DecidableEq α] (l : List α) :
    (insAll l []).toFinset = l.toFinset := by
  ext y
  simp only [List.mem_toFinset, insAll_mem]
  simp

/-- **THE DISTINCTNESS COUNT.**  The number of distinct colours of a `K₄`, computed without
building a `Finset` (which costs a red-black-tree insertion per colour). -/
def ndist {k : ℕ} (l : List (Fin k)) : ℕ := (insAll l []).length

theorem ndist_eq_card {k : ℕ} (l : List (Fin k)) : ndist l = (l.toFinset : Finset (Fin k)).card := by
  rw [ndist, ← insAll_nil_toFinset l]
  exact (List.toFinset_card_of_nodup (insAll_nodup (l := l) List.Pairwise.nil)).symm

theorem decide_ndist {k : ℕ} (l : List (Fin k)) :
    decide (5 ≤ ndist l) = decide (5 ≤ (l.toFinset : Finset (Fin k)).card) := by
  rw [ndist_eq_card]



end JSP140
