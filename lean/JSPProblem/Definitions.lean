import Mathlib.Data.Finset.Sym
import Mathlib.Tactic

/-!
# JSP-000140 — the Erdős–Gyárfás function `f(n, 4, 5)`

**Catalog statement** (recovered from the awards catalog, `problems/catalog-0101-0200.md`,
record `JSP-000140`, fetched 2026-09-30):

> **JSP-000140 · How many edge colors are necessary if every four-vertex clique must contain
> at least five colors?**
>
> Graph theory.  Date proposed: no later than 1997.  Current status: **Solved**.
> Lean proof in the catalog: **No**.  Publications: `[BCDP22]` S. Banerjee, P. Bradshaw,
> S. Letzter, A. Pokrovskiy, *The Erdős–Gyárfás function `f(n,4,5) = 5n/6 + o(n)` — so
> Gyárfás was right*, arXiv:2207.02920 (2022); `[JoMu22]` G. J. Chang, D. M. Evans,
> R. R. Munemasa, *Ramsey theory constructions from hypergraph matchings*,
> arXiv:2208.12563 (2022).

The quantity asked for is the **Erdős–Gyárfás function**

`f(n, p, q)` = the least number of colours in an edge-colouring of `K_n` in which every
`K_p` spans at least `q` colours,

specialised to `f(n, 4, 5)`.  `JSP140.EG n` below is exactly that number; the headline
theorem (see `Main.lean`) is the solved answer `f(n, 4, 5) = 5n/6 + o(n)`.

Main definitions.

* `Col n k` — a `k`-edge-colouring of `K_n`, i.e. a function on *unordered* pairs.
* `edgeFinset S` — the edges of `K` on `S`: the unordered pairs of two distinct elements.
* `colorsOn c S` — the set of colours appearing on those edges.
* `Admissible c` — every four-element `S` spans at least five colours (the catalog
  condition).
* `classIn c i S` — the edges of colour `i` inside `S`.
* `EG n` — the least number of colours of an admissible colouring, i.e. `f(n, 4, 5)`.
-/

namespace JSP140

/-- The vertex set of `K_n` is `Fin n`. -/
abbrev Verts (n : ℕ) := Fin n

/-- A `k`-edge-colouring of the complete graph `K_n`: a function from unordered pairs of
vertices to colours.  A loop `s(a, a)` is not an edge of `K_n`; the value there is
irrelevant and is discarded by `edgeFinset`. -/
abbrev Col (n k : ℕ) := Sym2 (Verts n) → Fin k

/-- An unordered pair has two distinct endpoints, i.e. it is an edge rather than a loop. -/
def OffDiag {α : Type*} (e : Sym2 α) : Prop := ∀ a b : α, e = s(a, b) → a ≠ b

/-- Unordered pairs are determined by their two endpoints. -/
theorem sym2_inj {α : Type*} {a b a' b' : α} (h : s(a, b) = s(a', b')) :
    a = a' ∧ b = b' ∨ a = b' ∧ b = a' := Sym2.rel_iff.mp (Sym2.eq.mp h)

/-- Edges sharing their first endpoint are determined by their second endpoint. -/
theorem sym2_inj_right {α : Type*} {a b c : α} (h : s(a, b) = s(a, c)) : b = c := by
  rcases sym2_inj h with ⟨_, h2⟩ | ⟨h1, h2⟩
  · exact h2
  · exact h2.trans h1

/-- Edges `s(a, b)` and `s(c, a)` which share `a` in the two different positions, with
`a ≠ b`: their other endpoints agree. -/
theorem sym2_inj_flip {α : Type*} {a b c : α} (hab : a ≠ b) (h : s(a, b) = s(c, a)) : b = c := by
  rcases sym2_inj h.symm with ⟨_, h2⟩ | ⟨h1, _⟩
  · exact (hab h2).elim
  · exact h1.symm

theorem offDiag_iff {α : Type*} {a b : α} : OffDiag s(a, b) ↔ a ≠ b := by
  constructor
  · rintro h
    exact h a b rfl
  · intro hab c d hcd
    rcases sym2_inj hcd.symm with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · intro e
      exact hab (h1.symm.trans (e.trans h2))
    · intro e
      exact hab (h2.symm.trans (e.symm.trans h1))

/-! ### Edges, colour classes, colour sets -/

/-- The loops `s(a, a)` on a vertex set `S`.  These are not edges of `K_n`. -/
def loops {n : ℕ} (S : Finset (Verts n)) : Finset (Sym2 (Verts n)) := S.image fun a => s(a, a)

/-- The edges of the complete graph on a vertex set `S`: the unordered pairs of two
*distinct* elements of `S`.  A four-element set spans `6` edges, a three-element set `3`. -/
def edgeFinset {n : ℕ} (S : Finset (Verts n)) : Finset (Sym2 (Verts n)) := S.sym2 \ loops S

theorem mem_loops {n : ℕ} {S : Finset (Verts n)} {e : Sym2 (Verts n)} :
    e ∈ loops S ↔ ∃ a ∈ S, e = s(a, a) := by
  rw [loops, Finset.mem_image]
  constructor
  · rintro ⟨a, ha, he⟩
    exact ⟨a, ha, he.symm⟩
  · rintro ⟨a, ha, he⟩
    exact ⟨a, ha, he.symm⟩

theorem mem_edgeFinset {n : ℕ} {S : Finset (Verts n)} {e : Sym2 (Verts n)} :
    e ∈ edgeFinset S ↔ e ∈ S.sym2 ∧ OffDiag e := by
  constructor
  · intro h
    have h1 : e ∈ S.sym2 := (Finset.mem_sdiff.mp h).1
    have h2 : e ∉ loops S := (Finset.mem_sdiff.mp h).2
    refine ⟨h1, fun a b hEq hab => ?_⟩
    apply h2
    rw [mem_loops, hEq]
    exact ⟨a, Finset.mem_sym2_iff.mp h1 a (hEq.symm ▸ Sym2.mem_mk_left a b),
      congrArg (fun y => s(a, y)) hab.symm⟩
  · rintro ⟨h1, h2⟩
    refine Finset.mem_sdiff.mpr ⟨h1, fun hx => ?_⟩
    rcases mem_loops.mp hx with ⟨a', _, he'⟩
    exact h2 a' a' he' rfl

private theorem diag_inj {α : Type*} {a b : α} (h : s(a, a) = s(b, b)) : a = b := by
  rcases sym2_inj h with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact h1
  · exact h1

/-- `S.sym2` contains one loop per element, and `choose |S|+1 2` unordered pairs in all. -/
theorem card_loops {n : ℕ} (S : Finset (Verts n)) : (loops S).card = S.card := by
  rw [loops]
  exact Finset.card_image_of_injective S fun {a b} h => diag_inj h

/-- A set of `t` vertices spans `choose t 2` edges. -/
theorem card_edgeFinset {n : ℕ} (S : Finset (Verts n)) :
    (edgeFinset S).card = Nat.choose (S.card + 1) 2 - S.card := by
  have hsub : loops S ⊆ S.sym2 := by
    intro e he
    rcases mem_loops.mp he with ⟨a, ha, heq⟩
    rw [heq]
    exact Finset.mk_mem_sym2_iff.mpr ⟨ha, ha⟩
  rw [edgeFinset, Finset.card_sdiff_of_subset hsub, Finset.card_sym2, card_loops]

/-- Four vertices span six edges: the six edges of a `K₄`. -/
theorem card_edgeFinset_four {n : ℕ} {S : Finset (Verts n)} (hS : S.card = 4) :
    (edgeFinset S).card = 6 := by
  rw [card_edgeFinset, hS]
  decide

/-- The colours appearing on the edges of the complete graph on a vertex set `S`. -/
def colorsOn {n k : ℕ} (c : Col n k) (S : Finset (Verts n)) : Finset (Fin k) := (edgeFinset S).image c

/-- A `k`-edge-colouring of `K_n` is **admissible** if every four-vertex clique spans at
least five colours.  This is exactly the catalog condition of `JSP-000140`. -/
def Admissible {n k : ℕ} (c : Col n k) : Prop :=
  ∀ S : Finset (Verts n), S.card = 4 → 5 ≤ (colorsOn c S).card

/-- The edges of colour `i` inside a vertex set `S`. -/
def classIn {n k : ℕ} (c : Col n k) (i : Fin k) (S : Finset (Verts n)) : Finset (Sym2 (Verts n)) :=
  (edgeFinset S).filter fun e => c e = i

@[simp] theorem mem_classIn {n k : ℕ} {c : Col n k} {i : Fin k} {S : Finset (Verts n)}
    {e : Sym2 (Verts n)} : e ∈ classIn c i S ↔ e ∈ edgeFinset S ∧ c e = i := Finset.mem_filter

theorem classIn_subset {n k : ℕ} {c : Col n k} {i : Fin k} {S : Finset (Verts n)} :
    classIn c i S ⊆ edgeFinset S := fun _ he => (mem_classIn.mp he).1

@[simp] theorem classIn_empty {n k : ℕ} {c : Col n k} {i : Fin k} :
    classIn c i (∅ : Finset (Verts n)) = ∅ := by ext e; simp [classIn, edgeFinset]

/-! ### Small counting tools -/

/-- A finset built from four given elements has at most four elements. -/
theorem card_four_le {α : Type*} [DecidableEq α] (a b c d : α) :
    ({a, b, c, d} : Finset α).card ≤ 4 := by
  have h1 : ({a, b, c, d} : Finset α).card ≤ ({b, c, d} : Finset α).card + 1 := Finset.card_insert_le _ _
  have h2 : ({b, c, d} : Finset α).card ≤ ({c, d} : Finset α).card + 1 := Finset.card_insert_le _ _
  have h3 : ({c, d} : Finset α).card ≤ ({d} : Finset α).card + 1 := Finset.card_insert_le _ _
  have h4 : ({d} : Finset α).card ≤ 1 := by simp
  omega

/-- Three pairwise distinct elements of a finset span at least three elements. -/
theorem card_ge_three {α : Type*} [DecidableEq α] {e₁ e₂ e₃ : α} {s : Finset α}
    (h12 : e₁ ≠ e₂) (h13 : e₁ ≠ e₃) (h23 : e₂ ≠ e₃)
    (hmem : e₁ ∈ s ∧ e₂ ∈ s ∧ e₃ ∈ s) : 3 ≤ s.card := by
  have hcard : ({e₁, e₂, e₃} : Finset α).card = 3 := by
    rw [show ({e₁, e₂, e₃} : Finset α) = insert e₁ (insert e₂ (insert e₃ ∅)) from rfl,
      Finset.card_insert_of_notMem (by simp [h12, h13]),
      Finset.card_insert_of_notMem (by simp [h23])]
    simp
  have hsub : ({e₁, e₂, e₃} : Finset α) ⊆ s := by
    intro e he
    rcases Finset.mem_insert.mp he with rfl | he
    · exact hmem.1
    · rcases Finset.mem_insert.mp he with rfl | he
      · exact hmem.2.1
      · rcases Finset.mem_singleton.mp he with rfl
        exact hmem.2.2
  calc 3 = ({e₁, e₂, e₃} : Finset α).card := hcard.symm
    _ ≤ s.card := Finset.card_le_card hsub

/-- Four pairwise distinct vertices: the shape of a `K₄`. -/
def FourDistinct {n : ℕ} (a b d e : Verts n) : Prop :=
  a ≠ b ∧ a ≠ d ∧ a ≠ e ∧ b ≠ d ∧ b ≠ e ∧ d ≠ e

/-- A four-element vertex set, given by its four (distinct) vertices. -/
def fourSet {n : ℕ} (a b d e : Verts n) : Finset (Verts n) := insert a (insert b (insert d (insert e ∅)))

theorem card_fourSet {n : ℕ} {a b d e : Verts n} (h : FourDistinct a b d e) :
    (fourSet a b d e).card = 4 := by
  have h1 : a ∉ insert b (insert d (insert e ∅) : Finset (Verts n)) := by
    simp [h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1]
  have h2 : b ∉ insert d (insert e ∅ : Finset (Verts n)) := by simp [h.2.2.2.1, h.2.2.2.2.1]
  have h3 : d ∉ insert e (∅ : Finset (Verts n)) := by simp [h.2.2.2.2]
  have h4 : e ∉ (∅ : Finset (Verts n)) := by simp
  rw [fourSet, Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
    Finset.card_insert_of_notMem h3, Finset.card_insert_of_notMem h4]
  simp

theorem mem_fourSet {n : ℕ} {a b d e : Verts n} (h : FourDistinct a b d e) {x : Verts n} :
    x ∈ fourSet a b d e ↔ x = a ∨ x = b ∨ x = d ∨ x = e := by
  simp [fourSet]

theorem mem_edgeFinset_mk {n : ℕ} {S : Finset (Verts n)} {a b : Verts n} (ha : a ∈ S) (hb : b ∈ S)
    (hab : a ≠ b) : s(a, b) ∈ edgeFinset S :=
  (mem_edgeFinset.mpr ⟨Finset.mk_mem_sym2_iff.mpr ⟨ha, hb⟩, offDiag_iff.mpr hab⟩)

/-! ### The structural content -/

/-- **The key local fact.**  If three edges of a `K₄` have the same colour, the `K₄` spans
at most four colours.  Contrapositively, in an admissible colouring no four vertices carry
three edges of one colour. -/
theorem colorsOn_card_le_four {n k : ℕ} {c : Col n k} {S : Finset (Verts n)} {i : Fin k}
    (hS : S.card = 4) (h3 : 3 ≤ (classIn c i S).card) : (colorsOn c S).card ≤ 4 := by
  have hrest : (edgeFinset S \ classIn c i S).card ≤ 3 := by
    have hsplit : (edgeFinset S \ classIn c i S).card + (classIn c i S).card = (edgeFinset S).card :=
      Finset.card_sdiff_add_card_eq_card classIn_subset
    have htot : (edgeFinset S).card = 6 := card_edgeFinset_four hS
    omega
  have himg : (colorsOn c S) ⊆ insert i ((edgeFinset S \ classIn c i S).image c) := by
    intro x hx
    simp only [colorsOn, Finset.mem_image] at hx
    obtain ⟨e, he, hec⟩ := hx
    by_cases hc : e ∈ classIn c i S
    · have hc' : c e = i := (mem_classIn.mp hc).2
      rw [hc'] at hec
      exact Finset.mem_insert.mpr (Or.inl hec.symm)
    · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨e, Finset.mem_sdiff.mpr ⟨he, hc⟩, hec⟩)
  calc (colorsOn c S).card ≤ (insert i ((edgeFinset S \ classIn c i S).image c)).card :=
        Finset.card_le_card himg
    _ ≤ ((edgeFinset S \ classIn c i S).image c).card + 1 := Finset.card_insert_le _ _
    _ ≤ 1 + (edgeFinset S \ classIn c i S).card := by
      have hle : ((edgeFinset S \ classIn c i S).image c).card ≤ (edgeFinset S \ classIn c i S).card :=
        Finset.card_image_le
      omega
    _ ≤ 4 := Nat.add_le_add_left hrest 1

/-- In an admissible colouring, every four vertices span **at most two edges of any one
colour**.  Equivalently: every colour class of an admissible colouring is a disjoint union
of edges and two-edge paths. -/
theorem classIn_card_le_two {n k : ℕ} {c : Col n k} (hc : Admissible c) (i : Fin k)
    (S : Finset (Verts n)) (hS : S.card = 4) : (classIn c i S).card ≤ 2 := by
  by_contra h
  have h3 : 3 ≤ (classIn c i S).card := by omega
  have hle := colorsOn_card_le_four hS h3
  have := hc S hS
  omega

/-! ### The Erdős–Gyárfás function `f(n, 4, 5)` and the headline statement -/

/-- The two-element subset of `{x, y}` is `{min x y, max x y}`. -/
theorem minmax_eq_pair {α : Type*} [LinearOrder α] [DecidableEq α] (x y : α) :
    ({min x y, max x y} : Finset α) = {x, y} := by
  rcases le_total x y with h | h
  · simp [min_eq_left h, max_eq_right h]
  · ext z
    simp [min_eq_right h, max_eq_left h, or_comm, or_left_comm]

/-- The injective colouring of `K_n` in which the edge `{a, b}` receives the colour
`(min a b, max a b)`.  Every edge gets a different colour. -/
def pairEnc (n : ℕ) (a b : Verts n) : Fin (n * n) :=
  ⟨a.val * n + b.val, by
    have h1 : a.val * n ≤ (n - 1) * n := Nat.mul_le_mul_right n (Nat.le_pred_of_lt a.isLt)
    have h2 : b.val ≤ n - 1 := Nat.le_pred_of_lt b.isLt
    have h3 : (n - 1) * n + (n - 1) + 1 = n * n := by
      have h4 : (n - 1) * n + (n - 1) + 1 = (n - 1) * n + n := by omega
      rw [h4, ← Nat.succ_mul]
      congr 1
      omega
    omega⟩

/-- The injective colouring of `K_n` in which the edge `{a, b}` receives the colour
`pairEnc n (min a b) (max a b)`.  Every edge gets a different colour. -/
def injCol (n : ℕ) : Col n (n * n) :=
  Sym2.rec (motive := fun _ => Fin (n * n))
    (fun a b => pairEnc n (min a b) (max a b))
    (by
      intro a b c d h
      cases h with
      | refl => rfl
      | swap x y => simp [min_comm, max_comm])

theorem pairEnc_inj {n : ℕ} {a b a' b' : Verts n} (h : pairEnc n a b = pairEnc n a' b') :
    (a, b) = (a', b') := by
  have hv : a.val * n + b.val = a'.val * n + b'.val := congrArg Fin.val h
  have ha : a = a' := by
    apply Fin.ext
    by_contra hc
    rcases lt_or_gt_of_ne hc with hc | hc
    · exfalso
      have h1 : a.val * n + b.val < a.val * n + n := Nat.add_lt_add_left b.isLt _
      have h2 : a.val * n + n ≤ a'.val * n := by
        rw [← Nat.succ_mul]
        exact Nat.mul_le_mul (Nat.succ_le_of_lt hc) (le_refl n)
      have h3 : a'.val * n ≤ a'.val * n + b'.val := Nat.le_add_right _ _
      have h4 : a.val * n + b.val < a'.val * n + b'.val := lt_of_lt_of_le (lt_of_lt_of_le h1 h2) h3
      exact absurd h4 (by rw [hv]; exact Nat.lt_irrefl _)
    · exfalso
      have h1 : a'.val * n + b'.val < a'.val * n + n := Nat.add_lt_add_left b'.isLt _
      have h2 : a'.val * n + n ≤ a.val * n := by
        rw [← Nat.succ_mul]
        exact Nat.mul_le_mul (Nat.succ_le_of_lt hc) (le_refl n)
      have h3 : a.val * n ≤ a.val * n + b.val := Nat.le_add_right _ _
      have h4 : a'.val * n + b'.val < a.val * n + b.val := lt_of_lt_of_le (lt_of_lt_of_le h1 h2) h3
      exact absurd h4 (by rw [← hv]; exact Nat.lt_irrefl _)
  have hb : b = b' := by
    apply Fin.ext
    have hmod : b.val = b'.val := by
      have h := congrArg (fun t : ℕ => t % n) hv
      rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_mod_self_left, Nat.add_comm, Nat.mul_comm,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt b.isLt, Nat.mod_eq_of_lt b'.isLt] at h
      exact h
    exact hmod
  rw [ha, hb]

/-- `injCol` separates edges. -/
theorem injCol_inj {n : ℕ} {a b a' b' : Verts n} (h : injCol n s(a, b) = injCol n s(a', b')) :
    s(a, b) = s(a', b') := by
  have h' : pairEnc n (min a b) (max a b) = pairEnc n (min a' b') (max a' b') := h
  have hmm : ((min a b, max a b) : Verts n × Verts n) = (min a' b', max a' b') := pairEnc_inj h'
  have hm1 : min a b = min a' b' := congrArg Prod.fst hmm
  have hm2 : max a b = max a' b' := congrArg Prod.snd hmm
  have hset : ({min a b, max a b} : Finset (Verts n)) = ({min a' b', max a' b'} : Finset (Verts n)) := by
    ext z
    simp only [Finset.mem_insert, Finset.mem_singleton, or_false]
    constructor
    · rintro (rfl | rfl)
      · rw [hm1]; exact Or.inl rfl
      · rw [hm2]; exact Or.inr rfl
    · rintro (rfl | rfl)
      · rw [← hm1]; exact Or.inl rfl
      · rw [← hm2]; exact Or.inr rfl
  have key : ∀ (u v : Verts n) (z : Verts n), (z = u ∨ z = v) ↔ z ∈ ({u, v} : Finset (Verts n)) := by
    intro u v z
    simp [Finset.mem_insert, Finset.mem_singleton]
  apply Sym2.ext
  intro z
  rw [Sym2.mem_iff, Sym2.mem_iff, key a b z, key a' b' z, ← minmax_eq_pair a b,
    ← minmax_eq_pair a' b', hset]

/-- `injCol` is admissible: every clique of four vertices spans six colours. -/
theorem admissible_injCol (n : ℕ) : Admissible (injCol n) := by
  intro S hS
  have hcard : (edgeFinset S).card = 6 := card_edgeFinset_four hS
  have hinj : Set.InjOn (injCol n) (edgeFinset S) := by
    intro e he e' he' heeq
    obtain ⟨x, y, rfl⟩ := Sym2.exists.mp ⟨e, rfl⟩
    obtain ⟨x', y', rfl⟩ := Sym2.exists.mp ⟨e', rfl⟩
    exact injCol_inj heeq
  have h6 : (colorsOn (injCol n) S).card = 6 := by
    calc (colorsOn (injCol n) S).card = (edgeFinset S).card := Finset.card_image_iff.mpr hinj
      _ = 6 := hcard
  rw [h6]
  norm_num

/-- The set of numbers of colours occurring in some admissible colouring of `K_n`. -/
noncomputable def ColCount (n : ℕ) : Set ℕ := {k | ∃ c : Col n k, Admissible c}

theorem ColCount_nonempty (n : ℕ) : (ColCount n).Nonempty := ⟨n * n, injCol n, admissible_injCol n⟩

/-- `EG n` is the least number of colours in an edge-colouring of `K_n` in which every `K₄`
spans at least five colours: the **Erdős–Gyárfás function `f(n, 4, 5)`**, the quantity asked
for in the catalog problem `JSP-000140`. -/
noncomputable def EG (n : ℕ) : ℕ := sInf (ColCount n)

/-- `EG n` colours are attained by an admissible colouring. -/
theorem EG_admissible (n : ℕ) : ∃ c : Col n (EG n), Admissible c :=
  (Nat.sInf_mem (ColCount_nonempty n) : EG n ∈ ColCount n)

/-- No admissible colouring of `K_n` uses fewer than `EG n` colours. -/
theorem EG_le (n k : ℕ) (c : Col n k) (hc : Admissible c) : EG n ≤ k := Nat.sInf_le ⟨c, hc⟩

/-- The elementary upper bound: `f(n,4,5) ≤ n²` (the injective colouring). -/
theorem EG_le_sq (n : ℕ) : EG n ≤ n * n := EG_le n (n * n) (injCol n) (admissible_injCol n)

/-- The catalog answer, in the ε-form of `f(n,4,5) = 5n/6 + o(n)`.  This is the statement of
the required theorem `jsp_000140_main` (see `Main.lean`). -/
def FiveSixth (f : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |(f n : ℝ) - 5 * (n : ℝ) / 6| ≤ ε * n

/-- The lower half of the catalog answer: `f(n,4,5) ≥ 5n/6 - ε n` for all large `n`. -/
def FiveSixthLower (f : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 5 * (n : ℝ) / 6 - ε * n ≤ (f n : ℝ)

/-- The upper half of the catalog answer: `f(n,4,5) ≤ 5n/6 + ε n` for all large `n`. -/
def FiveSixthUpper (f : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (f n : ℝ) ≤ 5 * (n : ℝ) / 6 + ε * n

theorem fiveSixth_iff {f : ℕ → ℕ} : FiveSixth f ↔ FiveSixthLower f ∧ FiveSixthUpper f := by
  constructor
  · rintro h
    constructor
    · intro ε hε
      obtain ⟨N, hN⟩ := h ε hε
      refine ⟨N, fun n hn => ?_⟩
      linarith [(abs_le.mp (hN n hn)).1]
    · intro ε hε
      obtain ⟨N, hN⟩ := h ε hε
      refine ⟨N, fun n hn => ?_⟩
      linarith [(abs_le.mp (hN n hn)).2]
  · rintro ⟨hL, hU⟩ ε hε
    obtain ⟨N₁, hN₁⟩ := hL ε hε
    obtain ⟨N₂, hN₂⟩ := hU ε hε
    refine ⟨max N₁ N₂, fun n hn => ?_⟩
    have h1 := hN₁ n (le_trans (le_max_left _ _) hn)
    have h2 := hN₂ n (le_trans (le_max_right _ _) hn)
    rw [abs_le]
    constructor <;> linarith

end JSP140
