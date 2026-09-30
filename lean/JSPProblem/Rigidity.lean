import JSPProblem.Cherry

/-!
# JSP-000140 — the rigidity of the extremal case: the two-edge paths form a Steiner triple system

`Cherry.lean` proved the counting lemma of the lower bound of the catalog answer
`f(n, 4, 5) = 5n/6 + o(n)` (arXiv:2207.02920):

    `three_mul_paths_le_edges` :  `3 * Paths c ≤ |E(K_n)| = n(n-1)/2`,

i.e. every two-edge path `a - v - b` of a colour class brings three edges with it — its own two
edges and the isolated single edge `s(a,b)` between its leaves — and the triples belonging to
different two-edge paths are pairwise disjoint.  The whole lower bound `5(n-1) ≤ 6k` is the
consequence (`Cherry.five_sixth_lower`).

This file analyses **the equality case** of that counting lemma, which is what the *upper* half of
the catalog answer has to achieve.  (The construction of arXiv:2207.02920 — Ben–Cushman–Dudek–
Prałat, *The Erdős–Gyárfás function `f(n,4,5) = 5n/6 + o(n)`* — is a *randomised* process based on
random triangle removal, and produces `(4,5)`-colourings of `K_n` with `5n/6 + o(n)` colours, i.e.
colourings whose two-edge paths number `n(n-1)/6 - o(n²)`.)  The following is the structural
content such a construction must have, and it is the reason the construction is hard:

* `pathSet` — the **three vertices** of a two-edge path: its centre and its two leaves;
* `pathSet_dichotomy` — for two distinct vertices `x, y` of a `pathSet`, either one of them is the
  centre (and `c s(x,y)` is the colour of the path) or both are leaves (and `c s(x,y)` is the
  colour of the *isolated* leaf edge, hence different);
* `pathSet_sub_inter` — **THE PACKING LEMMA**: two two-edge paths of an admissible colouring
  cannot have a common two-element vertex set, unless they are the *same* path.  So the
  `pathSet`s of `c` form a family of three-element sets in which every pair of vertices occurs in
  at most one member;
* `tight_pathFinset_is_STS` — **THE RIGIDITY THEOREM.**  If the counting lemma of `Cherry.lean`
  is an equality, `3 * Paths c = |E(K_n)|`, then the `pathSet`s of `c` are a **Steiner triple
  system** on the vertex set of `K_n`: they are three-element sets, pairwise almost disjoint, and
  *every pair of vertices lies in exactly one of them*.

So the extremal colourings of `JSP-000140` are exactly the colourings whose two-edge paths decompose
`K_n` into triangles: a triangle decomposition of `K_n` *is* a Steiner triple system, and it exists
only for `n ≡ 1, 3 (mod 6)`.  This is the combinatorial object the probabilistic construction of
arXiv:2207.02920 has to find, and it explains both the constant `5/6` (a Steiner triple system of
order `n` has `n(n-1)/6` blocks, and `Cherry.five_sixth_of_paths` turns `Paths c = n(n-1)/6` into
`5(n-1) ≤ 6k`) and the difficulty of the construction (finding a Steiner triple system, or a good
approximation of one, is precisely the "random triangle removal" step of the paper).

Consequences proved here:

* `tight_paths` — in the extremal case there are exactly `n(n-1)/6` two-edge paths;
* `tight_mod6` — **the extremal value is only attained for `n ≡ 1 (mod 6)`**: an admissible
  colouring of `K_n` which attains the counting bound *and* uses exactly the number of colours
  `5(n-1)/6` forced by the lower bound can exist only when `6 ∣ (n-1)`;
* `tight_classes_span` — **in the extremal case every colour class spans the vertex set**: every
  vertex is either the centre of a two-edge path of that colour or has exactly one neighbour in it
  (`2a_i + 3b_i = n`, the equality case of `Paths.twoA_oneB_card_le`).
-/

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace JSP140

variable {n k : ℕ}

/-! ### A pair lies inside a vertex set -/

/-- The two endpoints of the pair `p` both lie in the vertex set `B`.  Equivalently
`p ∈ B.sym2`. -/
def pairIn (p : Sym2 (Verts n)) (B : Finset (Verts n)) : Prop := ∀ x ∈ p, x ∈ B

instance pairInDecidable (p : Sym2 (Verts n)) :
    DecidablePred (fun B : Finset (Verts n) => pairIn p B) := fun B => by
  unfold pairIn; infer_instance

theorem pairIn_iff {p : Sym2 (Verts n)} {B : Finset (Verts n)} :
    pairIn p B ↔ p ∈ B.sym2 := by
  unfold pairIn; exact Finset.mem_sym2_iff.symm

theorem mem_pairIn {B : Finset (Verts n)} {x y : Verts n} :
    pairIn s(x, y) B ↔ x ∈ B ∧ y ∈ B := by
  rw [pairIn_iff, Finset.mk_mem_sym2_iff]

/-- Two distinct elements of a finset of cardinality at least two. -/
private lemma exists_two_of_card_ge_two {α : Type*} [DecidableEq α] {B : Finset α} (h2 : 2 ≤ B.card) :
    ∃ x y, x ∈ B ∧ y ∈ B ∧ x ≠ y := by
  have hne : B.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨x, hx⟩ := hne
  have hrest : (B.erase x).Nonempty := Finset.card_pos.mp (by
    have h := Finset.card_erase_of_mem hx
    omega)
  obtain ⟨y, hy⟩ := hrest
  exact ⟨x, y, hx, (Finset.mem_erase.mp hy).2, Ne.symm (Finset.mem_erase.mp hy).1⟩

/-! ### The three vertices of a two-edge path -/

/-- **The three vertices of a two-edge path** of colour `i` centred at `v`: the centre `v` together
with its two colour-`i` neighbours (its leaves).  For `v ∈ twoA c i` this is a three-element set. -/
def pathSet (c : Col n k) (i : Fin k) (v : Verts n) : Finset (Verts n) := insert v (Nbrs c i v)

theorem mem_pathSet {c : Col n k} {i : Fin k} {v x : Verts n} :
    x ∈ pathSet c i v ↔ x = v ∨ x ∈ Nbrs c i v := by
  rw [pathSet, Finset.mem_insert]

/-- A two-edge path spans three vertices. -/
theorem card_pathSet {c : Col n k} {i : Fin k} {v : Verts n} (hv : v ∈ twoA c i) :
    (pathSet c i v).card = 3 := by
  rw [pathSet, Finset.card_insert_of_notMem (not_mem_Nbrs_self i v), card_twoA i hv]

/-- **The two leaves of a two-edge path span an isolated edge of a different colour.**  If
`a, b` are two distinct colour-`i` neighbours of a centre `v` of colour `i`, then the edge `s(a,b)`
has a colour different from `i`, and at `a` and at `b` it is the only edge of its own colour. -/
theorem cherry_leaf_pair {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) {i : Fin k} {v : Verts n}
    (_hv : v ∈ twoA c i) {a b : Verts n} (ha : a ∈ Nbrs c i v) (hb : b ∈ Nbrs c i v) (hab : a ≠ b) :
    c s(a, b) ≠ i ∧ (Nbrs c (c s(a, b)) a).card = 1 ∧ (Nbrs c (c s(a, b)) b).card = 1 := by
  obtain ⟨hne, h1, h2⟩ := nb_eq_singleton_of_cherry (a := a) (b := b) hc hn i
    (fun hh => (mem_Nbrs.mp ha).1 hh.symm) (fun hh => (mem_Nbrs.mp hb).1 hh.symm) hab
    (mem_Nbrs.mp ha).2 (mem_Nbrs.mp hb).2 (c s(a, b)) rfl
  exact ⟨hne, by rw [Nbrs, h1]; simp, by rw [Nbrs, h2]; simp⟩

/-- **The dichotomy on a pair of vertices of a `pathSet`.**  Let `x ≠ y` be two vertices of the
`pathSet` of a two-edge path of colour `i` centred at `v`.  Then either `v` is one of `x, y` and
`c s(x,y) = i` (the pair is a *path* pair), or `x, y` are the two leaves and `c s(x,y) ≠ i` (the
pair is the *leaf* edge, an isolated single edge of a different colour). -/
theorem pathSet_dichotomy {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) {i : Fin k} {v : Verts n}
    (hv : v ∈ twoA c i) {x y : Verts n} (hx : x ∈ pathSet c i v) (hy : y ∈ pathSet c i v)
    (hxy : x ≠ y) :
    (v = x ∨ v = y) ∧ c s(x, y) = i ∨ (x ≠ v ∧ y ≠ v ∧ c s(x, y) ≠ i) := by
  by_cases hvx : x = v
  · refine Or.inl ⟨Or.inl hvx.symm, ?_⟩
    have hyN : y ∈ Nbrs c i v := Or.resolve_left (mem_pathSet.mp hy) (fun h => hxy (hvx.trans h.symm))
    rw [hvx]
    exact (mem_Nbrs.mp hyN).2
  by_cases hvy : y = v
  · refine Or.inl ⟨Or.inr hvy.symm, ?_⟩
    have hxN : x ∈ Nbrs c i v := Or.resolve_left (mem_pathSet.mp hx) hvx
    rw [hvy]
    exact c_swap (mem_Nbrs.mp hxN).2
  refine Or.inr ⟨hvx, hvy, ?_⟩
  have hxN : x ∈ Nbrs c i v := Or.resolve_left (mem_pathSet.mp hx) hvx
  have hyN : y ∈ Nbrs c i v := Or.resolve_left (mem_pathSet.mp hy) hvy
  exact (cherry_leaf_pair hc hn hv (a := x) (b := y) hxN hyN hxy).1

/-! ### Two two-edge paths cannot share two vertices -/

/-- **THE PACKING LEMMA.**  In an admissible colouring of `K_n` (`n ≥ 4`), two two-edge paths
cannot have a common two-element set of vertices, unless they are the same path: if a two-element
set `B` is contained in the `pathSet` of the path centred at `v` of colour `i` *and* in the
`pathSet` of the path centred at `w` of colour `j`, then `i = j` and `v = w`.

This is the local form of the fact that makes the two-edge paths of an extremal colouring a
*Steiner triple system*: their three-element vertex sets cover every pair of vertices at most once
(`tight_pathFinset_is_STS` below). -/
theorem pathSet_sub_inter {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) {i j : Fin k} {v w : Verts n}
    (hv : v ∈ twoA c i) (hw : w ∈ twoA c j) {B : Finset (Verts n)}
    (hB : B ⊆ pathSet c i v) (hB' : B ⊆ pathSet c j w) (h2 : 2 ≤ B.card) : i = j ∧ v = w := by
  obtain ⟨x, y, hxB, hyB, hxy⟩ := exists_two_of_card_ge_two h2
  have hx1 : x ∈ pathSet c i v := hB hxB
  have hy1 : y ∈ pathSet c i v := hB hyB
  have hx2 : x ∈ pathSet c j w := hB' hxB
  have hy2 : y ∈ pathSet c j w := hB' hyB
  have hd1 := pathSet_dichotomy hc hn hv hx1 hy1 hxy
  have hd2 := pathSet_dichotomy hc hn hw hx2 hy2 hxy
  rcases hd1 with ⟨hctr1, hcol1⟩ | ⟨hxv, hyv, hne1⟩
  · rcases hd2 with ⟨hctr2, hcol2⟩ | ⟨hxw, hyw, hne2⟩
    · -- both pairs are path pairs: the colours agree and the centres are joined by that colour
      have hij : i = j := hcol1.symm.trans hcol2
      by_cases hvw : v = w
      · exact ⟨hij, hvw⟩
      · exfalso
        have hstep : v = w ∨ c s(v, w) = i := by
          rcases hctr1 with hvx | hvy <;> rcases hctr2 with hwx | hwy
          · exact Or.inl (hvx.trans hwx.symm)
          · exact Or.inr (by rw [hvx, hwy]; exact hcol1)
          · exact Or.inr (by rw [hvy, hwx]; exact c_swap hcol1)
          · exact Or.inl (hvy.trans hwy.symm)
        rcases hstep with h | h
        · exact absurd h hvw
        · exact not_two_centres (a := v) (b := w) hc hn i hvw (card_twoA i hv)
            (hij ▸ card_twoA j hw) h
    · -- the pair is a path pair of the first path and the leaf edge of the second one
      have hxN : x ∈ Nbrs c j w := Or.resolve_left (mem_pathSet.mp hx2) hxw
      have hyN : y ∈ Nbrs c j w := Or.resolve_left (mem_pathSet.mp hy2) hyw
      obtain ⟨_, hcardx, hcardy⟩ := cherry_leaf_pair hc hn hw hxN hyN hxy
      rcases hctr1 with hvx | hvy
      · have h1 : (Nbrs c i x).card = 1 := by rw [← hcol1]; exact hcardx
        have h2c : (Nbrs c i x).card = 2 := hvx ▸ card_twoA i hv
        omega
      · have h1 : (Nbrs c i y).card = 1 := by rw [← hcol1]; exact hcardy
        have h2c : (Nbrs c i y).card = 2 := hvy ▸ card_twoA i hv
        omega
  · rcases hd2 with ⟨hctr2, hcol2⟩ | ⟨hxw, hyw, hne2⟩
    · -- the pair is the leaf edge of the first path and a path pair of the second one
      have hxN : x ∈ Nbrs c i v := Or.resolve_left (mem_pathSet.mp hx1) hxv
      have hyN : y ∈ Nbrs c i v := Or.resolve_left (mem_pathSet.mp hy1) hyv
      obtain ⟨_, hcardx, hcardy⟩ := cherry_leaf_pair hc hn hv hxN hyN hxy
      rcases hctr2 with hwx | hwy
      · have h1 : (Nbrs c j x).card = 1 := by rw [← hcol2]; exact hcardx
        have h2c : (Nbrs c j x).card = 2 := hwx ▸ card_twoA j hw
        omega
      · have h1 : (Nbrs c j y).card = 1 := by rw [← hcol2]; exact hcardy
        have h2c : (Nbrs c j y).card = 2 := hwy ▸ card_twoA j hw
        omega
    · -- the pair is the leaf edge of both paths: a pair of leaves determines the centre
      have hxN : x ∈ Nbrs c i v := Or.resolve_left (mem_pathSet.mp hx1) hxv
      have hyN : y ∈ Nbrs c i v := Or.resolve_left (mem_pathSet.mp hy1) hyv
      have hxwN : x ∈ Nbrs c j w := Or.resolve_left (mem_pathSet.mp hx2) hxw
      have hywN : y ∈ Nbrs c j w := Or.resolve_left (mem_pathSet.mp hy2) hyw
      have hvw' : v = w := centre_eq_of_leaves' hc hn i (v := v) (a := x) (b := y) (v' := w)
        hxv.symm hyv.symm hxy (mem_Nbrs.mp hxN).2 (mem_Nbrs.mp hyN).2
        hxw.symm hyw.symm ⟨j, (mem_Nbrs.mp hxwN).2, (mem_Nbrs.mp hywN).2⟩
      refine ⟨?_, hvw'⟩
      exact (mem_Nbrs.mp hxN).2.symm.trans (hvw' ▸ (mem_Nbrs.mp hxwN).2)

/-! ### The family of `pathSet`s -/

/-- The family of three-element vertex sets spanned by the two-edge paths of `c`. -/
def pathFinset (c : Col n k) : Finset (Finset (Verts n)) :=
  (cherryFinset c).image (fun p => pathSet c p.1 p.2)

theorem mem_pathFinset {c : Col n k} {b : Finset (Verts n)} (hb : b ∈ pathFinset c) :
    ∃ (i : Fin k) (v : Verts n), v ∈ twoA c i ∧ b = pathSet c i v := by
  rw [pathFinset, Finset.mem_image] at hb
  obtain ⟨p, hp, he⟩ := hb
  exact ⟨p.1, p.2, twoA_of_mem_cherryFinset hp, he.symm⟩

theorem card_pathFinset_mem {c : Col n k} {b : Finset (Verts n)} (hb : b ∈ pathFinset c) :
    b.card = 3 := by
  obtain ⟨i, v, hv, rfl⟩ := mem_pathFinset hb
  exact card_pathSet hv

/-- The number of three-element vertex sets spanned by the two-edge paths of `c` is `Paths c`. -/
theorem card_pathFinset (c : Col n k) (hc : Admissible c) (hn : 4 ≤ n) : (pathFinset c).card = Paths c := by
  have hinj : Set.InjOn (fun p : Fin k × Verts n => pathSet c p.1 p.2) (↑(cherryFinset c) : Set _) := by
    intro p hp q hq he
    have hp' : p.2 ∈ twoA c p.1 := twoA_of_mem_cherryFinset hp
    have hq' : q.2 ∈ twoA c q.1 := twoA_of_mem_cherryFinset hq
    have h2 : 2 ≤ (pathSet c p.1 p.2).card := by have := card_pathSet hp'; omega
    have he' : pathSet c p.1 p.2 = pathSet c q.1 q.2 := he
    have hsub' : pathSet c p.1 p.2 ⊆ pathSet c q.1 q.2 := he' ▸ Finset.Subset.rfl
    obtain ⟨hij, hvw⟩ := pathSet_sub_inter hc hn hp' hq' Finset.Subset.rfl hsub' h2
    exact Prod.ext hij hvw
  rw [pathFinset, Finset.card_image_iff.mpr hinj, card_cherryFinset]

/-- **At most one `pathSet` contains a given pair of vertices.** -/
theorem card_filter_pairIn_le (c : Col n k) (hc : Admissible c) (hn : 4 ≤ n)
    (p : Sym2 (Verts n)) (h0 : p ∈ edgeFinset (Finset.univ : Finset (Verts n))) :
    ((pathFinset c).filter (fun b => pairIn p b)).card ≤ 1 := by
  by_contra hcon
  have h1 : 2 ≤ ((pathFinset c).filter (fun b => pairIn p b)).card := by omega
  obtain ⟨B1, B2, hB1, hB2, hB1B2⟩ := exists_two_of_card_ge_two h1
  obtain ⟨x, y, rfl⟩ := Sym2.exists.mp ⟨p, rfl⟩
  have hoff := mem_edgeFinset.mp h0
  have hxy : x ≠ y := offDiag_iff.mp hoff.2
  have hpair1 : x ∈ B1 ∧ y ∈ B1 := mem_pairIn.mp (Finset.mem_filter.mp hB1).2
  have hpair2 : x ∈ B2 ∧ y ∈ B2 := mem_pairIn.mp (Finset.mem_filter.mp hB2).2
  have hsub1 : ({x, y} : Finset (Verts n)) ⊆ B1 := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hpair1.1
    · exact hpair1.2
  have hsub2 : ({x, y} : Finset (Verts n)) ⊆ B2 := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hpair2.1
    · exact hpair2.2
  have hne : x ∉ ({y} : Finset (Verts n)) := fun h => hxy (Finset.mem_singleton.mp h)
  have h2 : 2 ≤ ({x, y} : Finset (Verts n)).card := by
    rw [Finset.card_insert_of_notMem hne]
    simp
  obtain ⟨i, v, hv, hB1'⟩ := mem_pathFinset (Finset.mem_filter.mp hB1).1
  obtain ⟨j, w, hw, hB2'⟩ := mem_pathFinset (Finset.mem_filter.mp hB2).1
  have hsub1' : ({x, y} : Finset (Verts n)) ⊆ pathSet c i v := hB1' ▸ hsub1
  have hsub2' : ({x, y} : Finset (Verts n)) ⊆ pathSet c j w := hB2' ▸ hsub2
  obtain ⟨hij, hvw⟩ := pathSet_sub_inter hc hn hv hw hsub1' hsub2' h2
  exact hB1B2 (hB1'.trans (hij ▸ hvw ▸ hB2').symm)

theorem mem_filter_pairIn (b : Finset (Verts n)) (p : Sym2 (Verts n)) :
    p ∈ (edgeFinset (Finset.univ : Finset (Verts n))).filter (fun q => pairIn q b) ↔ p ∈ edgeFinset b := by
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨h1, h2⟩
    exact mem_edgeFinset.mpr ⟨pairIn_iff.mp h2, (mem_edgeFinset.mp h1).2⟩
  · intro h
    exact ⟨edgeFinset_mono (Finset.subset_univ b) h, pairIn_iff.mpr (mem_edgeFinset.mp h).1⟩

/-- For a three-element vertex set `b`, exactly three pairs lie inside it. -/
theorem sum_pairIn_three (b : Finset (Verts n)) (hb : b.card = 3) :
    (∑ p ∈ edgeFinset (Finset.univ : Finset (Verts n)), (if pairIn p b then 1 else 0)) = 3 := by
  have hfilter : ((edgeFinset (Finset.univ : Finset (Verts n))).filter (fun p => pairIn p b))
      = edgeFinset b := Finset.ext fun p => mem_filter_pairIn b p
  have hconv : (∑ p ∈ edgeFinset (Finset.univ : Finset (Verts n)),
        (if pairIn p b then 1 else 0))
      = ∑ p ∈ (edgeFinset (Finset.univ : Finset (Verts n))).filter (fun p => pairIn p b), (1 : ℕ) :=
    (Finset.sum_filter (fun p => pairIn p b) (fun _ => (1 : ℕ))).symm
  calc (∑ p ∈ edgeFinset (Finset.univ : Finset (Verts n)), (if pairIn p b then 1 else 0))
      = ∑ p ∈ (edgeFinset (Finset.univ : Finset (Verts n))).filter (fun p => pairIn p b),
          (1 : ℕ) := hconv
    _ = ((edgeFinset (Finset.univ : Finset (Verts n))).filter (fun p => pairIn p b)).card :=
      (Finset.card_eq_sum_ones _).symm
    _ = (edgeFinset b).card := by rw [hfilter]
    _ = 3 := by rw [card_edgeFinset, hb]; decide

/-- **THE DOUBLE COUNTING.**  Counting, for every pair of vertices of `K_n`, the number of
`pathSet`s containing it, in two ways: the total is `3 * (pathFinset c).card`, i.e. every two-edge
path contributes its three pairs. -/
theorem sum_card_filter_pairIn (c : Col n k) :
    (∑ p ∈ edgeFinset (Finset.univ : Finset (Verts n)),
      ((pathFinset c).filter (fun b => pairIn p b)).card) = 3 * (pathFinset c).card := by
  have key : ∀ p, ((pathFinset c).filter (fun b' => pairIn p b')).card
      = ∑ b' ∈ pathFinset c, (if pairIn p b' then 1 else 0) := by
    intro p
    have h1 : (∑ b' ∈ (pathFinset c).filter (fun b' => pairIn p b'), (1 : ℕ))
        = ∑ b' ∈ pathFinset c, (if pairIn p b' then 1 else 0) :=
      Finset.sum_filter (s := pathFinset c) (fun b' => pairIn p b') (fun _ => (1 : ℕ))
    have h2 : (∑ b' ∈ (pathFinset c).filter (fun b' => pairIn p b'), (1 : ℕ))
        = ((pathFinset c).filter (fun b' => pairIn p b')).card :=
      (Finset.card_eq_sum_ones _).symm
    exact h2.symm.trans h1
  have hcard : ∀ b ∈ pathFinset c, b.card = 3 := fun b hb => card_pathFinset_mem hb
  calc (∑ p ∈ edgeFinset (Finset.univ : Finset (Verts n)),
        ((pathFinset c).filter (fun b => pairIn p b)).card)
      = ∑ p ∈ edgeFinset (Finset.univ : Finset (Verts n)),
          ∑ b ∈ pathFinset c, (if pairIn p b then 1 else 0) := by
          refine Finset.sum_congr rfl fun p _ => key p
    _ = ∑ b ∈ pathFinset c,
          ∑ p ∈ edgeFinset (Finset.univ : Finset (Verts n)), (if pairIn p b then 1 else 0) := by
          exact Finset.sum_comm
    _ = ∑ b ∈ pathFinset c, 3 := by
          refine Finset.sum_congr rfl fun b hb => sum_pairIn_three b (hcard b hb)
    _ = 3 * (pathFinset c).card := by
      calc (∑ _ ∈ pathFinset c, (3 : ℕ)) = (pathFinset c).card • (3 : ℕ) := Finset.sum_const _
        _ = 3 * (pathFinset c).card := by rw [nsmul_eq_mul]; exact Nat.mul_comm _ _

/-! ### Steiner triple systems -/

/-- A **Steiner triple system** on the vertex set `Fin n`: a family of three-element sets of
vertices in which every pair of distinct vertices lies in exactly one member. -/
def IsSTS (B : Finset (Finset (Verts n))) : Prop :=
  (∀ b ∈ B, b.card = 3) ∧
    ∀ p ∈ edgeFinset (Finset.univ : Finset (Verts n)), ∃! b ∈ B, pairIn p b

theorem IsSTS.pairs_cover {B : Finset (Finset (Verts n))} (hB : IsSTS B)
    (p : Sym2 (Verts n)) (hp : p ∈ edgeFinset (Finset.univ : Finset (Verts n))) :
    ∃ b ∈ B, pairIn p b := (hB.2 p hp).exists

/-! ### The rigidity theorem -/

/-- **THE RIGIDITY THEOREM.**  Let `c` be an admissible colouring of `K_n` (`n ≥ 4`) for which the
counting lemma of `Cherry.lean` is an equality, `3 * Paths c = |E(K_n)|`.  Then the three-element
vertex sets spanned by the two-edge paths of `c` form a **Steiner triple system** on `Fin n`.

In other words: *the extremal colourings of `JSP-000140` are exactly the colourings whose two-edge
paths decompose `K_n` into triangles*.  This identifies the combinatorial object which the
construction of the upper half of the catalog answer `f(n,4,5) = 5n/6 + o(n)` (arXiv:2207.02920)
has to produce — a Steiner triple system, or rather a partial one with `(1-o(1))n²/6` blocks (its
construction is a random triangle removal process) — and it explains the constant `5/6`:
`Cherry.five_sixth_of_paths` turns `Paths c = n(n-1)/6` into `5(n-1) ≤ 6k`. -/
theorem tight_pathFinset_is_STS {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (h3 : 3 * Paths c = (edgeFinset (Finset.univ : Finset (Verts n))).card) :
    IsSTS (pathFinset c) := by
  have key : ∀ p ∈ edgeFinset (Finset.univ : Finset (Verts n)),
      ((pathFinset c).filter (fun b => pairIn p b)).card = 1 := by
    intro p hp
    have hle : ((pathFinset c).filter (fun b => pairIn p b)).card ≤ 1 :=
      card_filter_pairIn_le c hc hn p hp
    by_contra hcon
    have h0 : ((pathFinset c).filter (fun b => pairIn p b)).card = 0 := by omega
    have hsum := sum_card_filter_pairIn c
    have hsum' : (∑ q ∈ edgeFinset (Finset.univ : Finset (Verts n)),
        ((pathFinset c).filter (fun b => pairIn q b)).card)
        = (edgeFinset (Finset.univ : Finset (Verts n))).card :=
      hsum.trans (card_pathFinset c hc hn ▸ h3)
    have hcardp := Finset.card_erase_of_mem hp
    have hsplit := Finset.sum_erase_add (edgeFinset (Finset.univ : Finset (Verts n)))
      (fun q => ((pathFinset c).filter (fun b => pairIn q b)).card) hp
    have hbound : ∀ q ∈ (edgeFinset (Finset.univ : Finset (Verts n))).erase p,
        ((pathFinset c).filter (fun b => pairIn q b)).card ≤ 1 := by
      intro q hq
      exact Nat.le_trans (card_filter_pairIn_le c hc hn q (Finset.mem_erase.mp hq).2) (by omega)
    have hrest : (∑ q ∈ (edgeFinset (Finset.univ : Finset (Verts n))).erase p,
          ((pathFinset c).filter (fun b => pairIn q b)).card)
        ≤ ((edgeFinset (Finset.univ : Finset (Verts n))).erase p).card :=
      le_trans (Finset.sum_le_sum fun q hq => hbound q hq)
        (Nat.le_of_eq (Finset.card_eq_sum_ones _).symm)
    have hE1 : 1 ≤ (edgeFinset (Finset.univ : Finset (Verts n))).card := by
      simpa using Finset.card_le_card (Finset.singleton_subset_iff.mpr hp)
    have hmain := hsplit.symm
    rw [h0, Nat.add_zero] at hmain
    have hL : (∑ q ∈ (edgeFinset (Finset.univ : Finset (Verts n))).erase p,
        ((pathFinset c).filter (fun b => pairIn q b)).card)
        = (edgeFinset (Finset.univ : Finset (Verts n))).card := hmain.symm.trans hsum'
    have hfin : (∑ q ∈ (edgeFinset (Finset.univ : Finset (Verts n))).erase p,
          ((pathFinset c).filter (fun b => pairIn q b)).card)
        < (edgeFinset (Finset.univ : Finset (Verts n))).card := by
      refine lt_of_le_of_lt hrest ?_
      rw [hcardp]
      omega
    exact Nat.lt_irrefl _ (hL.symm ▸ hfin)
  refine ⟨fun b hb => card_pathFinset_mem hb, fun p hp => ?_⟩
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp (key p hp)
  have hbmem : b ∈ (pathFinset c).filter (fun b' => pairIn p b') := by rw [hb]; simp
  refine ⟨b, ⟨?_, ?_⟩, ?_⟩
  · exact (Finset.mem_filter.mp hbmem).1
  · exact (Finset.mem_filter.mp hbmem).2
  · intro y hy
    have hymem : y ∈ (pathFinset c).filter (fun b' => pairIn p b') := Finset.mem_filter.mpr hy
    have h1 : y = b := by rw [hb] at hymem; simpa using hymem
    exact h1

/-- **Attainment forces tightness.**  If an admissible colouring of `K_n` (`n ≥ 4`) uses exactly
`5(n-1)/6` colours — the number of colours forced by the lower bound `Cherry.five_sixth_lower` —
then the counting lemma `Cherry.three_mul_paths_le_edges` is an *equality*, so the two-edge paths of
the colouring form a Steiner triple system (`tight_pathFinset_is_STS`) and there are exactly
`n(n-1)/6` of them.

Together with `tight_pathFinset_is_STS` this gives the exact characterisation of the extremal
colourings of `JSP-000140`:

* an admissible colouring of `K_n` uses the extremal number `5(n-1)/6` of colours **iff** its
  two-edge paths form a Steiner triple system of order `n`. -/
theorem tight_attained {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (hk : 6 * k = 5 * (n - 1)) :
    3 * Paths c = (edgeFinset (Finset.univ : Finset (Verts n))).card := by
  have h1 := mul_n_sub_one_le (c := c) hc
  have h2 := six_mul_paths_le (c := c) hc hn
  have h3 : 6 * (n * (n - 1)) ≤ 6 * (n * k + Paths c) := Nat.mul_le_mul_left 6 h1
  have h4 : 6 * (n * k) = 5 * (n * (n - 1)) := by
    have hnn : 6 * (n * k) = n * (6 * k) := by ring
    rw [hnn, hk]
    ring
  have h5 : n * (n - 1) ≤ 6 * Paths c := by omega
  have h6 : 6 * Paths c = n * (n - 1) := by omega
  have h7 := card_edgeFinset_univ_two n
  omega

/-! ### The consequences for the extremal case -/

/-- **In the extremal case there are exactly `n(n-1)/6` two-edge paths**, i.e. the counting lemma
`Cherry.three_mul_paths_le_edges` is attained; equivalently the two-edge paths decompose `K_n` into
`n(n-1)/6` triangles, the number of blocks of a Steiner triple system of order `n`. -/
theorem tight_paths {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (h3 : 3 * Paths c = (edgeFinset (Finset.univ : Finset (Verts n))).card) :
    Paths c = n * (n - 1) / 6 := by
  have h2 := card_edgeFinset_univ_two n
  have h6 : 6 * Paths c = n * (n - 1) := by omega
  refine le_antisymm ((Nat.le_div_iff_mul_le (by omega)).2 (by simpa only [Nat.mul_comm] using h6.le)) ?_
  exact (Nat.div_le_iff_le_mul (by omega)).2 (by omega)

/-- **The extremal value is only attained for `n ≡ 1 (mod 6)`.**  If an admissible colouring of
`K_n` attains the counting bound of `Cherry.lean` *and* uses exactly the number of colours
`5(n-1)/6` which the lower bound `Cherry.five_sixth_lower` forces, then `6 ∣ (n-1)`, i.e.
`n ≡ 1 (mod 6)`.  So on the other five residue classes the sharp constant `5/6` is not attained:
there `f(n,4,5) > 5(n-1)/6`. -/
theorem tight_mod6 {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (h3 : 3 * Paths c = (edgeFinset (Finset.univ : Finset (Verts n))).card) (hk : 6 * k = 5 * (n - 1)) :
    n % 6 = 1 ∧ (pathFinset c).card = n * (n - 1) / 6 := by
  have hdvd : (6 : ℕ) ∣ 5 * (n - 1) := ⟨k, by omega⟩
  have hdvd' : (6 : ℕ) ∣ (n - 1) := (show Nat.Coprime 6 5 from by decide).dvd_of_dvd_mul_left hdvd
  obtain ⟨t, ht⟩ := hdvd'
  constructor
  · omega
  · exact (card_pathFinset c hc hn).trans (tight_paths hc hn h3)

/-- The degree sum of a colour class, split by the number of colour-`i` neighbours (as in
`Paths.sum_nb_card_eq`, repeated here because that lemma is private to `Paths.lean`). -/
private lemma sum_nb_card_eq (c : Col n k) (hc : Admissible c) (i : Fin k) :
    (∑ v ∈ (Finset.univ : Finset (Verts n)), (nb c i v (Finset.univ : Finset (Verts n))).card)
      = 2 * (twoA c i).card + 1 * (oneB c i).card := by
  have key : ∀ v ∈ (Finset.univ : Finset (Verts n)),
      (nb c i v (Finset.univ : Finset (Verts n))).card
        = (if (nb c i v (Finset.univ : Finset (Verts n))).card = 2 then (2 : ℕ) else 0)
          + (if (nb c i v (Finset.univ : Finset (Verts n))).card = 1 then (1 : ℕ) else 0) := by
    intro v _
    by_cases h2 : (nb c i v (Finset.univ : Finset (Verts n))).card = 2
    · rw [if_pos h2, if_neg (by omega)]
      omega
    · rw [if_neg h2]
      by_cases h1 : (nb c i v (Finset.univ : Finset (Verts n))).card = 1
      · rw [if_pos h1]
        omega
      · rw [if_neg h1]
        have hle := nb_card_le_two hc i v (Finset.univ : Finset (Verts n))
        omega
  have h1 : (∑ v ∈ (Finset.univ : Finset (Verts n)),
      (if (nb c i v (Finset.univ : Finset (Verts n))).card = 2 then (2 : ℕ) else 0))
      = 2 * (twoA c i).card := by
    calc _ = ∑ v ∈ twoA c i, (2 : ℕ) := by
          rw [twoA]; exact (Finset.sum_filter (fun v : Verts n =>
            (nb c i v (Finset.univ : Finset (Verts n))).card = 2) fun _ => (2 : ℕ)).symm
      _ = (twoA c i).card • (2 : ℕ) := Finset.sum_const _
      _ = 2 * (twoA c i).card := by rw [nsmul_eq_mul]; exact Nat.mul_comm _ _
  have h2 : (∑ v ∈ (Finset.univ : Finset (Verts n)),
      (if (nb c i v (Finset.univ : Finset (Verts n))).card = 1 then (1 : ℕ) else 0))
      = 1 * (oneB c i).card := by
    calc _ = ∑ v ∈ oneB c i, (1 : ℕ) := by
          rw [oneB]; exact (Finset.sum_filter (fun v : Verts n =>
            (nb c i v (Finset.univ : Finset (Verts n))).card = 1) fun _ => (1 : ℕ)).symm
      _ = (oneB c i).card • (1 : ℕ) := Finset.sum_const _
      _ = 1 * (oneB c i).card := by rw [nsmul_eq_mul]; exact Nat.mul_comm _ _
  calc (∑ v ∈ (Finset.univ : Finset (Verts n)), (nb c i v (Finset.univ : Finset (Verts n))).card)
      = ∑ v ∈ (Finset.univ : Finset (Verts n)),
          ((if (nb c i v (Finset.univ : Finset (Verts n))).card = 2 then (2 : ℕ) else 0)
            + (if (nb c i v (Finset.univ : Finset (Verts n))).card = 1 then (1 : ℕ) else 0)) :=
        Finset.sum_congr rfl fun v hv => key v hv
    _ = (∑ v ∈ (Finset.univ : Finset (Verts n)),
          (if (nb c i v (Finset.univ : Finset (Verts n))).card = 2 then (2 : ℕ) else 0))
        + ∑ v ∈ (Finset.univ : Finset (Verts n)),
          (if (nb c i v (Finset.univ : Finset (Verts n))).card = 1 then (1 : ℕ) else 0) :=
        Finset.sum_add_distrib
    _ = 2 * (twoA c i).card + 1 * (oneB c i).card := by rw [h1, h2]

/-- **In the extremal case every colour class spans the vertex set.**  If `c` attains the counting
bound of `Cherry.lean` and uses exactly `5(n-1)/6` colours, then for every colour `i` each vertex
of `K_n` is either the centre of a two-edge path of colour `i` or has exactly one colour-`i`
neighbour: `(twoA c i).card + (oneB c i).card = n`.  Equivalently, each colour class is a
*spanning* vertex-disjoint union of two-edge paths and isolated single edges (`2a_i + 3b_i = n`),
the equality case of the refined counting lemma `Paths.two_mul_classIn_le_add`.  So in the
extremal case no colour class is "wasting" vertices, and the `5/6` constant of the lower bound is
attained exactly when all `k` classes are spanning. -/
theorem tight_classes_span {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (h3 : 3 * Paths c = (edgeFinset (Finset.univ : Finset (Verts n))).card) (hk : 6 * k = 5 * (n - 1)) :
    ∀ i : Fin k, (twoA c i).card + (oneB c i).card = n := by
  have h2 := card_edgeFinset_univ_two n
  have h6P : 6 * Paths c = n * (n - 1) := by omega
  have hmul : 6 * (n * (n - 1)) = 6 * (n * k + Paths c) := by
    have hrest : n * (5 * (n - 1)) + 6 * Paths c = 6 * (n * (n - 1)) := by
      calc n * (5 * (n - 1)) + 6 * Paths c = 5 * (n * (n - 1)) + 6 * Paths c := by ring
        _ = 5 * (6 * Paths c) + 6 * Paths c := by rw [h6P]
        _ = 6 * (6 * Paths c) := by ring
        _ = 6 * (n * (n - 1)) := by rw [h6P]
    have hnn : 6 * (n * k) = n * (6 * k) := by ring
    calc 6 * (n * (n - 1)) = n * (6 * k) + 6 * Paths c := by rw [hk]; exact hrest.symm
      _ = 6 * (n * k) + 6 * Paths c := by rw [← hnn]
      _ = 6 * (n * k + Paths c) := by ring
  have hnle : n * (n - 1) ≤ n * k + Paths c := mul_n_sub_one_le hc
  have heq0 : n * (n - 1) = n * k + Paths c :=
    le_antisymm hnle (Nat.le_of_mul_le_mul_left hmul.symm.le (by omega : (0 : ℕ) < 6))
  have hleft : (∑ i : Fin k, 2 * (classIn c i (Finset.univ : Finset (Verts n))).card)
      = 2 * (edgeFinset (Finset.univ : Finset (Verts n))).card := by
    calc (∑ i : Fin k, 2 * (classIn c i (Finset.univ : Finset (Verts n))).card)
        = 2 * ∑ i : Fin k, (classIn c i (Finset.univ : Finset (Verts n))).card := by
          rw [← Finset.mul_sum]
      _ = 2 * (edgeFinset (Finset.univ : Finset (Verts n))).card := by rw [sum_card_classIn]
  have hsum_n : (∑ i : Fin k, (n : ℕ)) = n * k := by
    simp [Nat.mul_comm]
  have hright : (∑ i : Fin k, (n + (twoA c i).card)) = n * k + Paths c := by
    rw [Finset.sum_add_distrib, Paths, hsum_n]
  have heq : (∑ i : Fin k, 2 * (classIn c i (Finset.univ : Finset (Verts n))).card)
      = ∑ i : Fin k, (n + (twoA c i).card) := by
    rw [hleft, card_edgeFinset_univ_two, hright, heq0]
  clear hk hmul hnle h2 h6P heq0 hleft hright hsum_n
  have hle : ∀ i : Fin k, 2 * (classIn c i (Finset.univ : Finset (Verts n))).card ≤ n + (twoA c i).card :=
    fun i => two_mul_classIn_le_add hc i
  have hterm : ∀ i : Fin k, 2 * (classIn c i (Finset.univ : Finset (Verts n))).card
      = n + (twoA c i).card := by
    intro i
    by_contra hcon
    have hlt : 2 * (classIn c i (Finset.univ : Finset (Verts n))).card
        < n + (twoA c i).card := by
      rcases lt_trichotomy (2 * (classIn c i (Finset.univ : Finset (Verts n))).card)
        (n + (twoA c i).card) with h | h | h
      · exact h
      · exact absurd h hcon
      · exact (Nat.not_lt_of_ge (hle i) h).elim
    have h1 : (∑ q ∈ (Finset.univ : Finset (Fin k)).erase i,
        2 * (classIn c q (Finset.univ : Finset (Verts n))).card)
        ≤ (∑ q ∈ (Finset.univ : Finset (Fin k)).erase i, (n + (twoA c q).card)) :=
      Finset.sum_le_sum fun q _ => hle q
    have hsplitL := Finset.sum_erase_add (Finset.univ : Finset (Fin k))
      (fun q => 2 * (classIn c q (Finset.univ : Finset (Verts n))).card) (Finset.mem_univ i)
    have hsplitR := Finset.sum_erase_add (Finset.univ : Finset (Fin k))
      (fun q => (n + (twoA c q).card)) (Finset.mem_univ i)
    have hMain : (∑ q : Fin k, 2 * (classIn c q (Finset.univ : Finset (Verts n))).card)
        = ((∑ q ∈ (Finset.univ : Finset (Fin k)).erase i, (n + (twoA c q).card))
          + (n + (twoA c i).card)) := heq.trans hsplitR.symm
    omega
  intro i
  have hdeg := degree_sum (c := c) (i := i) (S := (Finset.univ : Finset (Verts n)))
  have hsplit := sum_nb_card_eq c hc i
  rw [hterm i] at hdeg
  omega

end JSP140
