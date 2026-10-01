import JSPProblem.Star

/-!
# `JSP-000140` — the single edges at a vertex: the local completion of the extremal structure

`Star.lean` gives the *colour-degree* profile of an extremal admissible colouring of `K_n`
(`6k = 5(n-1)`): every vertex `v` is the centre of exactly `(n-1)/6` two-edge paths, lies in
exactly `(n-1)/2` blocks of the Steiner triple system of paths, and has colour-degree `1` in
exactly `2(n-1)/3` colours.  What was missing is the identification asked for in round 24: of those
`2(n-1)/3` colours in which `v` has colour-degree `1`, which are the *isolated single edges* at
`v`?  This file answers it, and thereby pins down the last local quantity of the extremal case.

* **`singleStar`** — the single edges incident to a vertex; `mem_singleStar`, `mem_singleStar_mk`,
  `not_mem_singleStar_of_pathEdge`;
* **`single_iff_leaf` — THE MISSING IDENTIFICATION.**  Let `v` have colour-degree `1` in colour
  `i` and let `w` be its unique colour-`i` neighbour.  Then

      the edge `s(v, w)` is an isolated single edge   ⟺   `w` has colour-degree `1` in colour `i`,

  i.e. **an isolated single edge is exactly an edge joining the two leaves of a two-edge path**.
  This is the local form of `Cherry.nb_eq_singleton_of_cherry`, with the hypothesis weakened to
  one endpoint: the *converse* direction is the new content, and it is exactly what is needed to
  read the single edges off the colour-degree profile.  `single_or_leaf` is the corresponding
  dichotomy: the unique colour-`i` edge at a colour-degree-`1` vertex is either a single edge, or
  an edge of a two-edge path through `v`;
* **`card_singleStar` — THE PER-COLOUR FORM**: the single edges at `v` are counted colour by
  colour, and colour `i` contributes one exactly when `v` has colour-degree `1` in `i` *and* the
  partner is a leaf;
* **`sum_singleStar` — THE PER-VERTEX DOUBLE COUNT**, `∑_v (singleStar c v).card = 2 * (#single
  edges)`, for every colouring;
* **`leafThrough`**, `mem_leafEdge_iff`, `card_cherryFinset_centred`, `tight_card_leafThrough` —
  the single edges at `v` are counted by the blocks of the Steiner triple system in which `v` is a
  **leaf**, the other blocks through `v` being the ones centred at `v`;
* **`tight_singleStar` — THE LAST LOCAL QUANTITY OF THE EXTREMAL CASE**: in an extremal colouring

      every vertex is incident with exactly `(n-1)/3` single edges,

  one for each of the `(n-1)/2 - (n-1)/6 = (n-1)/3` blocks through `v` in which `v` is a leaf.
  Summed over the `n` vertices this is `2 n(n-1)/6` incidences, i.e. exactly `n(n-1)/6` single
  edges, as the global count `Singles.tight_card_singles` says (`tight_sum_singleStar`).
-/

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace JSP140

variable {n k : ℕ}

/-! ### Endpoints of a finset of edges -/

/-- **A vertex is an endpoint of a family of edges.**  (`Sym2` is `SetLike`, so `x ∈ e` is
defined for a *single* edge `e`, but not for a `Finset` of edges; this packages the two.) -/
def endpt (v : Verts n) (S : Finset (Sym2 (Verts n))) : Prop := ∃ e ∈ S, v ∈ e

theorem mem_endpt {v : Verts n} {S : Finset (Sym2 (Verts n))} :
    endpt v S ↔ ∃ e ∈ S, v ∈ e := Iff.rfl

instance endptDecidable (v : Verts n) (S : Finset (Sym2 (Verts n))) : Decidable (endpt v S) := by
  unfold endpt
  infer_instance

/-! ### The single edges at a vertex -/

/-- **The single edges incident to a vertex** `v`: the isolated single edges of the colouring which
have `v` as an endpoint. -/
def singleStar (c : Col n k) (v : Verts n) : Finset (Sym2 (Verts n)) :=
  (singleFinset c).filter (fun e => v ∈ e)

theorem mem_singleStar {c : Col n k} {v : Verts n} {e : Sym2 (Verts n)} :
    e ∈ singleStar c v ↔ e ∈ singleFinset c ∧ v ∈ e :=
  Finset.mem_filter

theorem mem_singleStar_mk {c : Col n k} {v w : Verts n} (hvw : v ≠ w) :
    s(v, w) ∈ singleStar c v ↔ Single c s(v, w) := by
  rw [mem_singleStar, mem_singleFinset]
  constructor
  · rintro ⟨⟨-, hS⟩, -⟩
    exact hS
  · rintro hS
    exact ⟨⟨mem_edgeFinset_mk (Finset.mem_univ v) (Finset.mem_univ w) hvw, hS⟩,
      Sym2.mem_iff.mpr (Or.inl rfl)⟩

/-- Every single edge has two distinct endpoints. -/
theorem singleStar_offDiag {c : Col n k} {v : Verts n} {e : Sym2 (Verts n)}
    (he : e ∈ singleStar c v) : OffDiag e :=
  (mem_edgeFinset.mp (mem_singleFinset.mp (mem_singleStar.mp he).1).1).2

/-- A single edge at `v` is never an edge of a two-edge path. -/
theorem not_mem_singleStar_of_pathEdge {c : Col n k} (i : Fin k)
    {v : Verts n} (hv : v ∈ twoA c i) {a : Verts n} (ha : a ∈ Nbrs c i v) :
    s(v, a) ∉ singleStar c v := by
  rw [mem_singleStar_mk (fun h => (mem_Nbrs.mp ha).1 h.symm)]
  exact not_Single_of_path_edge i hv ha

/-! ### A single edge is a pair of leaves -/

/-- **THE MISSING IDENTIFICATION.**  Let `v` have colour-degree `1` in colour `i` and let `w` be its
unique colour-`i` neighbour (`w ∈ Nbrs c i v`, which is then a singleton).  Then

    the edge `s(v, w)` is an isolated single edge  ⟺  `w` has colour-degree `1` in colour `i`.

In words: **an isolated single edge is exactly an edge joining the two leaves of a two-edge
path.**  The global statement `Cherry.nb_eq_singleton_of_cherry` assumes that *both* endpoints are
leaves; the new content here is the converse, obtained by assuming only about `v`. -/
theorem single_iff_leaf {c : Col n k} {i : Fin k} {v w : Verts n}
    (hv : v ∈ oneB c i) (hw : w ∈ Nbrs c i v) :
    Single c s(v, w) ↔ w ∈ oneB c i := by
  have hcol : c s(v, w) = i := (mem_Nbrs.mp hw).2
  have hv1 : (nb c i v (Finset.univ : Finset (Verts n))).card = 1 := (Finset.mem_filter.mp hv).2
  constructor
  · rintro ⟨a, b, he, hab, h1, h2⟩
    rcases sym2_inj he with ⟨hav, hbw⟩ | ⟨hbv, haw⟩
    · rw [← hbw, hcol] at h2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ w, h2⟩
    · rw [← haw, hcol] at h1
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ w, h1⟩
  · intro hw1
    have hw1' : (nb c i w (Finset.univ : Finset (Verts n))).card = 1 :=
      (Finset.mem_filter.mp hw1).2
    exact ⟨v, w, rfl, (mem_Nbrs.mp hw).1.symm, by rw [hcol]; exact hv1,
      by rw [hcol]; exact hw1'⟩

/-- A colour class has at least two colour-`i` neighbours at `w`, so `w` is the centre of a two-edge
path. -/
private lemma nb_card_eq_two_of_three {c : Col n k} (hc : Admissible c) (i : Fin k) (w a : Verts n)
    (hne : a ≠ w) (hcol : c s(w, a) = i)
    (hne1 : (nb c i w (Finset.univ : Finset (Verts n))).card ≠ 1) :
    (nb c i w (Finset.univ : Finset (Verts n))).card = 2 := by
  have hpos : 0 < (nb c i w (Finset.univ : Finset (Verts n))).card :=
    Finset.card_pos.mpr ⟨a, mem_Nbrs.mpr ⟨hne, hcol⟩⟩
  have hle : (nb c i w (Finset.univ : Finset (Verts n))).card ≤ 2 :=
    nb_card_le_two hc i w (Finset.univ : Finset (Verts n))
  omega

/-- **THE LOCAL SINGLE-EDGE STRUCTURE AT A COLOUR-DEGREE-`1` VERTEX.**  The unique colour-`i` edge
at such a vertex `v` (with `w` its unique colour-`i` neighbour) is either

* an isolated single edge — in which case `w` is a leaf too (`single_iff_leaf`), so `v` and `w` are
  the two leaves of a two-edge path centred elsewhere; or
* an edge of a two-edge path of colour `i` — in which case `w` is the centre of that path.

This is the vertex-by-vertex shadow of the global description `Singles.mem_classIn_single_or_path`,
and it is the local fact a *construction* of the extremal family has to satisfy. -/
theorem single_or_leaf {c : Col n k} (hc : Admissible c) {i : Fin k} {v : Verts n}
    (hv : v ∈ oneB c i) {w : Verts n} (hw : w ∈ Nbrs c i v) :
    Single c s(v, w) ∨ ∃ u ∈ twoA c i, s(v, w) ∈ pathEdges c i u := by
  by_cases hS : Single c s(v, w)
  · exact Or.inl hS
  · have hnot : w ∉ oneB c i := fun h => hS ((single_iff_leaf hv hw).mpr h)
    have hne1 : (nb c i w (Finset.univ : Finset (Verts n))).card ≠ 1 := by
      intro hh
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ w, hh⟩)
    have h2 := nb_card_eq_two_of_three hc i w v (mem_Nbrs.mp hw).1.symm
      (c_swap (mem_Nbrs.mp hw).2) hne1
    have hvw : v ∈ Nbrs c i w := mem_Nbrs.mpr ⟨(mem_Nbrs.mp hw).1.symm, c_swap (mem_Nbrs.mp hw).2⟩
    refine Or.inr ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ w, h2⟩, ?_⟩
    exact (mem_pathEdges i).mpr ⟨v, hvw, Sym2.eq_swap⟩

/-! ### The number of single edges at a vertex -/

/-- The colour-`i` edges at `v`. -/
def starIn (c : Col n k) (i : Fin k) (v : Verts n) : Finset (Sym2 (Verts n)) :=
  (Nbrs c i v).image (fun w => s(v, w))

theorem mem_starIn {c : Col n k} {i : Fin k} {v w : Verts n} :
    s(v, w) ∈ starIn c i v ↔ w ∈ Nbrs c i v := by
  rw [starIn, Finset.mem_image]
  constructor
  · rintro ⟨x, hx, he⟩
    have hxw : x = w := sym2_inj_right he
    rw [← hxw]
    exact hx
  · intro hw
    exact ⟨w, hw, rfl⟩

/-- **AT MOST ONE SINGLE EDGE AT `v` IN EACH COLOUR.** -/
theorem card_singleStar_inter {c : Col n k} (v : Verts n) (i : Fin k) :
    (singleStar c v ∩ starIn c i v).card ≤ 1 := by
  refine Finset.card_le_one.mpr fun e₁ he₁ e₂ he₂ => ?_
  obtain ⟨he₁1, he₁2⟩ := Finset.mem_inter.mp he₁
  obtain ⟨he₂1, he₂2⟩ := Finset.mem_inter.mp he₂
  obtain ⟨w₁, hw₁, h1⟩ := Finset.mem_image.mp he₁2
  obtain ⟨w₂, hw₂, h2⟩ := Finset.mem_image.mp he₂2
  have hS : Single c s(v, w₁) := by
    rw [h1]
    exact (mem_singleFinset.mp (mem_singleStar.mp he₁1).1).2
  have hcol : c s(v, w₁) = i := (mem_Nbrs.mp hw₁).2
  have hdeg : (nb c i v (Finset.univ : Finset (Verts n))).card = 1 := by
    obtain ⟨a, b, he, hab, ha1, hb1⟩ := hS
    rcases sym2_inj he with ⟨hav, -⟩ | ⟨hbv, -⟩
    · rw [← hav, hcol] at ha1
      exact ha1
    · rw [← hbv, hcol] at hb1
      exact hb1
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hdeg
  have hw₁n : w₁ ∈ nb c i v (Finset.univ : Finset (Verts n)) := hw₁
  have hw₂n : w₂ ∈ nb c i v (Finset.univ : Finset (Verts n)) := hw₂
  have hw₁' : w₁ = x := Finset.mem_singleton.mp
    (show w₁ ∈ ({x} : Finset (Verts n)) from by rw [← hx]; exact hw₁n)
  have hw₂' : w₂ = x := Finset.mem_singleton.mp
    (show w₂ ∈ ({x} : Finset (Verts n)) from by rw [← hx]; exact hw₂n)
  have h12 : s(v, w₁) = s(v, w₂) := by rw [hw₁', hw₂']
  exact h1.symm.trans (h12.trans h2)

/-- **THE PER-COLOUR FORM OF THE SINGLE-EDGE COUNT AT A VERTEX.**  The single edges at `v` are
counted colour by colour: colour `i` contributes one exactly when `v` has colour-degree `1` in `i`
*and* the unique colour-`i` neighbour of `v` is a leaf itself (`single_iff_leaf`). -/
theorem card_singleStar {c : Col n k} (v : Verts n) :
    (singleStar c v).card
      = ∑ i : Fin k, if v ∈ oneB c i ∧ (∀ w ∈ Nbrs c i v, w ∈ oneB c i) then (1 : ℕ) else 0 := by
  have hsplit : (singleStar c v).card
      = ∑ i : Fin k, (singleStar c v ∩ starIn c i v).card := by
    have hdisj : (↑(Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint
        (fun i => singleStar c v ∩ starIn c i v) := by
      intro i _ j _ hij
      refine Finset.disjoint_left.mpr fun e he1 he2 => ?_
      obtain ⟨w₁, hw₁, h1⟩ := Finset.mem_image.mp (Finset.mem_inter.mp he1).2
      obtain ⟨w₂, hw₂, h2⟩ := Finset.mem_image.mp (Finset.mem_inter.mp he2).2
      have h12 : s(v, w₁) = s(v, w₂) := h1.trans h2.symm
      have hcol12 : c s(v, w₁) = c s(v, w₂) := congrArg (fun t : Sym2 (Verts n) => c t) h12
      exact hij ((mem_Nbrs.mp hw₁).2.symm.trans (hcol12.trans (mem_Nbrs.mp hw₂).2))
    have h1 : ((Finset.univ : Finset (Fin k)).biUnion
        (fun i => singleStar c v ∩ starIn c i v)).card
        = ∑ i : Fin k, (singleStar c v ∩ starIn c i v).card := Finset.card_biUnion hdisj
    have hsub : ((Finset.univ : Finset (Fin k)).biUnion
        (fun i => singleStar c v ∩ starIn c i v)) ⊆ singleStar c v :=
      Finset.biUnion_subset.mpr fun i _ => Finset.inter_subset_left
    have hsup : singleStar c v ⊆ ((Finset.univ : Finset (Fin k)).biUnion
        (fun i => singleStar c v ∩ starIn c i v)) := by
      intro e he
      obtain ⟨a, b, hab⟩ := Sym2.exists.mp (show ∃ e' : Sym2 (Verts n), e = e' from ⟨e, rfl⟩)
      obtain ⟨hmem, hvb⟩ := (mem_singleStar.mp he)
      have hne : a ≠ b := (mem_edgeFinset.mp (mem_singleFinset.mp hmem).1).2 a b hab
      refine Finset.mem_biUnion.mpr
        ⟨c s(a, b), Finset.mem_univ _,
          Finset.mem_inter.mpr ⟨hab ▸ he, ?_⟩⟩
      rw [hab] at hvb
      rw [hab]
      rcases Sym2.mem_iff.mp hvb with hva | hvb
      · rw [hva]
        exact mem_starIn.mpr (mem_Nbrs.mpr ⟨fun h => hne h.symm, rfl⟩)
      · rw [hvb, Sym2.eq_swap]
        exact mem_starIn.mpr (mem_Nbrs.mpr ⟨hne, rfl⟩)
    have heq : ((Finset.univ : Finset (Fin k)).biUnion
        (fun i => singleStar c v ∩ starIn c i v)) = singleStar c v :=
      Finset.Subset.antisymm hsub hsup
    rw [heq] at h1
    exact h1
  have hcard : ∀ i : Fin k, (singleStar c v ∩ starIn c i v).card
      = if v ∈ oneB c i ∧ (∀ w ∈ Nbrs c i v, w ∈ oneB c i) then (1 : ℕ) else 0 := by
    intro i
    by_cases hgood : v ∈ oneB c i ∧ (∀ w ∈ Nbrs c i v, w ∈ oneB c i)
    · rw [if_pos hgood]
      have hv1 : (nb c i v (Finset.univ : Finset (Verts n))).card = 1 :=
        (Finset.mem_filter.mp hgood.1).2
      obtain ⟨w, hws⟩ := Finset.card_eq_one.mp hv1
      have hw : w ∈ nb c i v (Finset.univ : Finset (Verts n)) := by
        rw [hws]
        exact Finset.mem_singleton.mpr rfl
      have hne : w ≠ v := (mem_Nbrs.mp hw).1
      have hmem : s(v, w) ∈ singleStar c v ∩ starIn c i v := by
        refine Finset.mem_inter.mpr
          ⟨(mem_singleStar_mk (fun h => hne h.symm)).mpr
              ((single_iff_leaf hgood.1 hw).mpr (hgood.2 w hw)),
            mem_starIn.mpr hw⟩
      have hpos : 0 < (singleStar c v ∩ starIn c i v).card := Finset.card_pos.mpr ⟨s(v, w), hmem⟩
      have hle : (singleStar c v ∩ starIn c i v).card ≤ 1 := card_singleStar_inter v i
      omega
    · rw [if_neg hgood]
      refine Finset.card_eq_zero.mpr (Finset.eq_empty_iff_forall_notMem.mpr fun e he => ?_)
      obtain ⟨he1, he2⟩ := Finset.mem_inter.mp he
      obtain ⟨w, hw, heq⟩ := Finset.mem_image.mp he2
      have hne : w ≠ v := (mem_Nbrs.mp hw).1
      have hS : Single c s(v, w) := by
        rw [heq]
        exact (mem_singleFinset.mp (mem_singleStar.mp he1).1).2
      have hcol : c s(v, w) = i := (mem_Nbrs.mp hw).2
      have hdeg : (nb c i v (Finset.univ : Finset (Verts n))).card = 1 := by
        obtain ⟨a, b, he', hab, ha1, hb1⟩ := hS
        rcases sym2_inj he' with ⟨hav, -⟩ | ⟨hbv, -⟩
        · rw [← hav, hcol] at ha1
          exact ha1
        · rw [← hbv, hcol] at hb1
          exact hb1
      by_cases hin : v ∈ oneB c i
      · have hdegN : (Nbrs c i v).card = 1 := hdeg
        obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hdegN
        rw [single_iff_leaf hin hw] at hS
        have hwx : w = x := Finset.mem_singleton.mp (hx ▸ hw)
        exact absurd hS (fun hh => hgood ⟨hin, fun w' hw' => by
          rw [hx] at hw'
          have hw'x : w' = x := Finset.mem_singleton.mp hw'
          rw [hw'x.trans hwx.symm]
          exact hh⟩)
      · exact absurd hdeg (fun hh => hin (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hh⟩))
  rw [hsplit]
  exact Finset.sum_congr rfl fun i _ => hcard i

/-! ### The per-vertex double count -/

/-- **THE PER-VERTEX DOUBLE COUNT FOR SINGLE EDGES.**  For every colouring, single edges or not,

    ∑_v (number of single edges at `v`) = 2 * (number of single edges),

the handshaking lemma for the isolated single edges. -/
theorem sum_singleStar (c : Col n k) :
    (∑ v : Verts n, (singleStar c v).card) = 2 * (singleFinset c).card := by
  classical
  have hstep : (∑ v : Verts n, (singleStar c v).card)
      = ∑ e ∈ singleFinset c, (∑ v : Verts n, if v ∈ e then (1 : ℕ) else 0) := by
    calc (∑ v : Verts n, (singleStar c v).card)
        = ∑ v : Verts n, ∑ e ∈ singleFinset c, (if v ∈ e then (1 : ℕ) else 0) := by
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [singleStar, Finset.card_eq_sum_ones, Finset.sum_filter]
      _ = ∑ e ∈ singleFinset c, (∑ v : Verts n, if v ∈ e then (1 : ℕ) else 0) := Finset.sum_comm
  have hinter : ∀ e ∈ singleFinset c, (∑ v : Verts n, if v ∈ e then (1 : ℕ) else 0) = 2 := by
    intro e he
    obtain ⟨hmem, hS⟩ := mem_singleFinset.mp he
    obtain ⟨a, b, he', hab, h1, h2⟩ := hS
    rw [he']
    have hsub : ((Finset.univ : Finset (Verts n)).filter (fun v : Verts n => v ∈ s(a, b)))
        = insert a (insert b ∅) := filter_mem_edge (Finset.mem_univ a) (Finset.mem_univ b)
    have hins : (insert a (insert b ∅) : Finset (Verts n)) = {a, b} := rfl
    rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones, hsub, hins,
      Finset.card_eq_two.mpr ⟨a, b, hab, rfl⟩]
  calc (∑ v : Verts n, (singleStar c v).card) = ∑ e ∈ singleFinset c, 2 := by
        rw [hstep, Finset.sum_congr rfl fun e he => hinter e he]
    _ = (singleFinset c).card • (2 : ℕ) := Finset.sum_const _
    _ = (singleFinset c).card * 2 := by rw [nsmul_eq_mul, Nat.cast_id]
    _ = 2 * (singleFinset c).card := Nat.mul_comm _ _

/-! ### The single edges at a vertex are the leaf edges of the blocks through `v` -/

/-- **A vertex is an endpoint of the leaf edge of a two-edge path exactly when it is one of its
two leaves** (`not_mem_Nbrs_self` says a centre is never one of its own leaves). -/
theorem endpt_leafEdge_iff {c : Col n k} {i : Fin k} {u v : Verts n} (hu : u ∈ twoA c i) :
    endpt v (leafEdge c i u) ↔ v ∈ Nbrs c i u := by
  have h2 := card_twoA i hu
  obtain ⟨a, b, hab, hN⟩ := Finset.card_eq_two.mp h2
  have hB : leafEdge c i u = {s(a, b)} := image_pairs_two h2 hN hab
  constructor
  · rintro ⟨e, he, hv⟩
    rw [hB, Finset.mem_singleton] at he
    have hve : v = a ∨ v = b := by rw [he] at hv; exact Sym2.mem_iff.mp hv
    rw [hN, Finset.mem_insert, Finset.mem_singleton]
    exact hve.elim Or.inl fun h => Or.inr h
  · intro hv
    refine ⟨s(a, b), by rw [hB, Finset.mem_singleton], ?_⟩
    rw [hN] at hv
    rcases Finset.mem_insert.mp hv with hv | hv
    · exact Sym2.mem_iff.mpr (Or.inl hv)
    · exact Sym2.mem_iff.mpr (Or.inr (Finset.mem_singleton.mp hv))

/-- **A vertex is a leaf of the two-edge path of colour `i` centred at `u` exactly when it is in the
`pathSet` but is not the centre.** -/
theorem endpt_leafEdge_iff_ne {c : Col n k} {i : Fin k} {u v : Verts n} (hu : u ∈ twoA c i) :
    endpt v (leafEdge c i u) ↔ (v ∈ pathSet c i u ∧ v ≠ u) := by
  constructor
  · intro h
    refine ⟨mem_pathSet.mpr (Or.inr ((endpt_leafEdge_iff hu).mp h)), ?_⟩
    intro he
    have hne' : v ∉ Nbrs c i u := by rw [he]; exact not_mem_Nbrs_self i u
    exact hne' ((endpt_leafEdge_iff hu).mp h)
  · rintro ⟨h1, h2⟩
    refine (endpt_leafEdge_iff hu).mpr ?_
    rcases (mem_pathSet (c := c) (i := i) (v := u) (x := v)).mp h1 with h | h
    · exfalso
      exact h2 h
    · exact h

/-- **The two-edge paths whose leaf edge contains `v`**: the blocks of the Steiner triple system in
which `v` is a leaf. -/
def leafThrough (c : Col n k) (v : Verts n) : Finset (Fin k × Verts n) :=
  (cherryFinset c).filter (fun p => endpt v (leafEdge c p.1 p.2))

theorem mem_leafThrough {c : Col n k} {v : Verts n} {p : Fin k × Verts n} :
    p ∈ leafThrough c v ↔ p ∈ cherryFinset c ∧ endpt v (leafEdge c p.1 p.2) :=
  Finset.mem_filter

/-- **THE NUMBER OF TWO-EDGE PATHS CENTRED AT `v` IS THE CENTRE COUNT.**  For every colouring, the
number of two-edge paths of which `v` is the centre is

    ∑_i [ v ∈ twoA c i ],

i.e. the quantity bounded by `Star.tight_star_centre` in the extremal case.  (No admissibility is
needed: each colour contributes at most one path centred at `v`.  The converse reading — that a
vertex of colour-degree `2` is the centre of exactly one two-edge path — is the content of
`rigidity`'s `pathSet`.) -/
theorem card_cherryFinset_centred {c : Col n k} (v : Verts n) :
    ((cherryFinset c).filter (fun p => p.2 = v)).card
      = ∑ i : Fin k, if v ∈ twoA c i then (1 : ℕ) else 0 := by
  have hset : (cherryFinset c).filter (fun p => p.2 = v)
      = (Finset.univ : Finset (Fin k)).biUnion
          (fun i => ((twoA c i).filter (fun u => u = v)).image (fun u => (i, u))) := by
    ext p
    constructor
    · intro hp
      have hp' := Finset.mem_filter.mp hp
      have hp1 : p ∈ (Finset.univ : Finset (Fin k)).biUnion
          (fun i => (twoA c i).image fun v => (i, v)) := hp'.1
      rw [Finset.mem_biUnion]
      obtain ⟨i, hi, hp2⟩ := Finset.mem_biUnion.mp hp1
      obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hp2
      refine ⟨i, hi, ?_⟩
      rw [← he]
      refine Finset.mem_image.mpr ⟨u, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨hu, (congrArg Prod.snd he).trans hp'.2⟩
    · intro hp
      obtain ⟨i, hi, hp2⟩ := Finset.mem_biUnion.mp hp
      obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hp2
      have huv : u = v := (Finset.mem_filter.mp hu).2
      have hpu : p.2 = u := congrArg Prod.snd he.symm
      have hmem : p ∈ (Finset.univ : Finset (Fin k)).biUnion
          (fun i => (twoA c i).image fun v => (i, v)) := by
        rw [Finset.mem_biUnion]
        exact ⟨i, hi, Finset.mem_image.mpr ⟨u, (Finset.mem_filter.mp hu).1, he⟩⟩
      exact Finset.mem_filter.mpr ⟨hmem, hpu.trans huv⟩
  have hdisc : (↑(Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint
      (fun i => ((twoA c i).filter (fun u => u = v)).image (fun u => (i, u))) := by
    intro i _ j _ hij
    refine Finset.disjoint_left.mpr fun p hp1 hp2 => ?_
    obtain ⟨u, hu, h1⟩ := Finset.mem_image.mp hp1
    obtain ⟨u', hu', h2⟩ := Finset.mem_image.mp hp2
    exact hij (congrArg Prod.fst (h1.trans h2.symm))
  rw [hset, Finset.card_biUnion hdisc]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h)]
  by_cases hvi : v ∈ twoA c i
  · have hone : (twoA c i).filter (fun u : Verts n => u = v) = {v} := by
      ext u
      constructor
      · intro h
        exact Finset.mem_singleton.mpr (Finset.mem_filter.mp h).2
      · intro h
        rw [Finset.mem_singleton] at h
        refine Finset.mem_filter.mpr ⟨?_, h⟩
        rwa [h]
    rw [hone, Finset.card_eq_one.mpr ⟨v, rfl⟩, if_pos hvi]
  · have hzero : (twoA c i).filter (fun u : Verts n => u = v) = ∅ := by
      refine Finset.eq_empty_iff_forall_notMem.mpr fun u hu => ?_
      exact hvi ((Finset.mem_filter.mp hu).2 ▸ (Finset.mem_filter.mp hu).1)
    rw [hzero, Finset.card_empty, if_neg hvi]

/-- The map from a two-edge path to the vertex set it spans is injective on the two-edge paths
(the hypothesis of `Rigidity.card_pathFinset`, extracted). -/
theorem injOn_pathSet {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) :
    Set.InjOn (fun p : Fin k × Verts n => pathSet c p.1 p.2) (↑(cherryFinset c) : Set _) := by
  intro p hp q hq he
  have hp' : p.2 ∈ twoA c p.1 := twoA_of_mem_cherryFinset hp
  have hq' : q.2 ∈ twoA c q.1 := twoA_of_mem_cherryFinset hq
  have h2 : 2 ≤ (pathSet c p.1 p.2).card := by have := card_pathSet hp'; omega
  have he' : pathSet c p.1 p.2 = pathSet c q.1 q.2 := he
  have hsub' : pathSet c p.1 p.2 ⊆ pathSet c q.1 q.2 := he' ▸ Finset.Subset.rfl
  obtain ⟨hij, hvw⟩ := pathSet_sub_inter hc hn hp' hq' Finset.Subset.rfl hsub' h2
  exact Prod.ext hij hvw

/-- **IN THE EXTREMAL CASE THE LEAF EDGES SPAN THE SINGLE EDGES.**  This is the finset form of
`Singles.tight_single_is_leaf`, exposed so that the local count can be read off from it. -/
theorem tight_leafEdge_biUnion {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (h3 : 3 * Paths c = (edgeFinset (Finset.univ : Finset (Verts n))).card)
    (hk : 6 * k = 5 * (n - 1)) :
    (cherryFinset c).biUnion (fun p => leafEdge c p.1 p.2) = singleFinset c := by
  have hdisc : (↑(cherryFinset c) : Set (Fin k × Verts n)).PairwiseDisjoint
      (fun p => leafEdge c p.1 p.2) := by
    intro p hp q hq hpq
    exact leafEdge_disjoint hc hn (twoA_of_mem_cherryFinset (Finset.mem_coe.mp hp))
      (twoA_of_mem_cherryFinset (Finset.mem_coe.mp hq)) hpq
  have hsub : ((cherryFinset c).biUnion (fun p => leafEdge c p.1 p.2)) ⊆ singleFinset c := by
    intro e he
    obtain ⟨p, hp, he'⟩ := Finset.mem_biUnion.mp he
    exact leafEdge_subset_single hc hn (twoA_of_mem_cherryFinset (Finset.mem_coe.mp hp)) he'
  have hcardBI : ((cherryFinset c).biUnion (fun p => leafEdge c p.1 p.2)).card
      = (cherryFinset c).card := by
    have h1 : ((cherryFinset c).biUnion (fun p => leafEdge c p.1 p.2)).card
        = ∑ p ∈ cherryFinset c, (leafEdge c p.1 p.2).card := Finset.card_biUnion hdisc
    calc _ = ∑ p ∈ cherryFinset c, (leafEdge c p.1 p.2).card := h1
      _ = ∑ p ∈ cherryFinset c, (1 : ℕ) := by
          refine Finset.sum_congr rfl fun p hp =>
            card_leafEdge p.1 (twoA_of_mem_cherryFinset (Finset.mem_coe.mp hp))
      _ = (cherryFinset c).card • (1 : ℕ) := Finset.sum_const _
      _ = (cherryFinset c).card := by rw [nsmul_eq_mul, Nat.mul_one, Nat.cast_id]
  have hcards : (singleFinset c).card = (cherryFinset c).card := by
    have h := card_singleFinset hc hn
    have hpaths := tight_paths hc hn h3
    rw [card_cherryFinset]
    omega
  exact Finset.eq_of_subset_of_card_le hsub (by rw [hcards, hcardBI])

/-- **THE SINGLE EDGES AT `v` ARE COUNTED BY THE BLOCKS IN WHICH `v` IS A LEAF.**  (Extremal case:
by `tight_leafEdge_biUnion` and the pairwise disjointness of the leaf edges.) -/
theorem tight_card_singleStar_eq_leafThrough {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (h3 : 3 * Paths c = (edgeFinset (Finset.univ : Finset (Verts n))).card)
    (hk : 6 * k = 5 * (n - 1)) (v : Verts n) :
    (singleStar c v).card = (leafThrough c v).card := by
  have hBI := tight_leafEdge_biUnion hc hn h3 hk
  have hdisc : (↑(cherryFinset c) : Set (Fin k × Verts n)).PairwiseDisjoint
      (fun p => leafEdge c p.1 p.2) := by
    intro p hp q hq hpq
    exact leafEdge_disjoint hc hn (twoA_of_mem_cherryFinset (Finset.mem_coe.mp hp))
      (twoA_of_mem_cherryFinset (Finset.mem_coe.mp hq)) hpq
  have hleft : ((singleStar c v).card)
      = (((cherryFinset c).biUnion (fun p => leafEdge c p.1 p.2)).filter
        (fun e : Sym2 (Verts n) => v ∈ e)).card := by
    rw [singleStar, hBI]
  rw [hleft]
  have hdisc' : (↑(cherryFinset c) : Set (Fin k × Verts n)).PairwiseDisjoint
      (fun p => (leafEdge c p.1 p.2).filter (fun e : Sym2 (Verts n) => v ∈ e)) := by
    intro p hp q hq hpq
    refine Finset.disjoint_left.mpr fun e he1 he2 => ?_
    exact Finset.disjoint_left.mp
      (leafEdge_disjoint hc hn (twoA_of_mem_cherryFinset (Finset.mem_coe.mp hp))
        (twoA_of_mem_cherryFinset (Finset.mem_coe.mp hq)) hpq)
      (Finset.mem_filter.mp he1).1 (Finset.mem_filter.mp he2).1
  have h1 : (((cherryFinset c).biUnion (fun p => leafEdge c p.1 p.2)).filter
      (fun e : Sym2 (Verts n) => v ∈ e)).card
      = ∑ p ∈ cherryFinset c, ((leafEdge c p.1 p.2).filter
          (fun e : Sym2 (Verts n) => v ∈ e)).card := by
    rw [Finset.filter_biUnion, Finset.card_biUnion hdisc']
  have h2 : ∀ p ∈ cherryFinset c,
      ((leafEdge c p.1 p.2).filter (fun e : Sym2 (Verts n) => v ∈ e)).card
        = if endpt v (leafEdge c p.1 p.2) then (1 : ℕ) else 0 := by
    intro p hp
    by_cases hv : endpt v (leafEdge c p.1 p.2)
    · rw [if_pos hv]
      obtain ⟨x, hx⟩ := Finset.card_eq_one.mp
        (card_leafEdge p.1 (twoA_of_mem_cherryFinset hp))
      have hle : ((leafEdge c p.1 p.2).filter (fun e : Sym2 (Verts n) => v ∈ e)).card ≤ 1 :=
        Finset.card_le_one.mpr fun e₁ he₁ e₂ he₂ => by
          have he₁' := Finset.mem_filter.mp he₁
          have he₂' := Finset.mem_filter.mp he₂
          have h1 : e₁ = x := Finset.mem_singleton.mp (hx ▸ he₁'.1)
          have h2 : e₂ = x := Finset.mem_singleton.mp (hx ▸ he₂'.1)
          exact h1.trans h2.symm
      obtain ⟨e, he, hve⟩ := hv
      have hmem : e ∈ (leafEdge c p.1 p.2).filter
          (fun e' : Sym2 (Verts n) => v ∈ e') := Finset.mem_filter.mpr ⟨he, hve⟩
      have hpos : 0 < ((leafEdge c p.1 p.2).filter
          (fun e' : Sym2 (Verts n) => v ∈ e')).card := Finset.card_pos.mpr ⟨e, hmem⟩
      omega
    · rw [if_neg hv]
      refine Finset.card_eq_zero.mpr (Finset.eq_empty_iff_forall_notMem.mpr fun e he => ?_)
      exact hv ⟨e, (Finset.mem_filter.mp he).1, (Finset.mem_filter.mp he).2⟩
  calc (((cherryFinset c).biUnion (fun p => leafEdge c p.1 p.2)).filter
          (fun e : Sym2 (Verts n) => v ∈ e)).card
      = ∑ p ∈ cherryFinset c, ((leafEdge c p.1 p.2).filter
          (fun e : Sym2 (Verts n) => v ∈ e)).card := h1
    _ = ∑ p ∈ cherryFinset c, (if endpt v (leafEdge c p.1 p.2) then (1 : ℕ) else 0) :=
        Finset.sum_congr rfl fun p hp => h2 p hp
    _ = ((cherryFinset c).filter (fun p => endpt v (leafEdge c p.1 p.2))).card := by
        rw [← Finset.sum_filter, Finset.card_eq_sum_ones]
    _ = (leafThrough c v).card := rfl

/-- **THE BLOCKS THROUGH `v` SPLIT INTO THE ONES IN WHICH `v` IS A LEAF AND THE ONE IN WHICH `v` IS
THE CENTRE.**  Formally: the two-edge paths through `v` are the disjoint union of those in which `v`
is a leaf and those centred at `v`, and the two families are counted by the blocks of the Steiner
triple system through `v` and by `card_cherryFinset_centred` (which `Star.tight_star_centre` then
bounds by `(n-1)/6` in the extremal case). -/
theorem tight_card_leafThrough {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (h3 : 3 * Paths c = (edgeFinset (Finset.univ : Finset (Verts n))).card)
    (hk : 6 * k = 5 * (n - 1)) (v : Verts n) :
    (leafThrough c v).card + ((cherryFinset c).filter (fun p => p.2 = v)).card
      = ((pathFinset c).filter (fun b => v ∈ b)).card := by
  have hsplit : ∀ p ∈ cherryFinset c,
      (if v ∈ pathSet c p.1 p.2 then (1 : ℕ) else 0)
        = (if endpt v (leafEdge c p.1 p.2) then (1 : ℕ) else 0)
          + (if p.2 = v then (1 : ℕ) else 0) := by
    intro p hp
    have hu : p.2 ∈ twoA c p.1 := twoA_of_mem_cherryFinset hp
    have hiff : endpt v (leafEdge c p.1 p.2) ↔ (v ∈ pathSet c p.1 p.2 ∧ v ≠ p.2) :=
      (endpt_leafEdge_iff_ne hu : endpt v (leafEdge c p.1 p.2) ↔
        (v ∈ pathSet c p.1 p.2 ∧ v ≠ p.2))
    by_cases hne : p.2 = v
    · have hL : ¬ endpt v (leafEdge c p.1 p.2) := by
        intro h
        have hmem := (endpt_leafEdge_iff (twoA_of_mem_cherryFinset hp)).mp h
        exact absurd (hne ▸ hmem) (not_mem_Nbrs_self (c := c) p.1 p.2)
      have hP : v ∈ pathSet c p.1 p.2 := (mem_pathSet (c := c) (i := p.1) (v := p.2)
        (x := v)).mpr (Or.inl hne.symm)
      simp only [hP, if_neg hL, if_pos hne, if_true, zero_add]
    · have hP' : v ∈ pathSet c p.1 p.2 ↔ endpt v (leafEdge c p.1 p.2) :=
        ⟨fun h => hiff.mpr ⟨h, fun hv => hne hv.symm⟩, fun h => (hiff.mp h).1⟩
      simp only [hP', if_neg hne, add_zero]
  have heq : (cherryFinset c).filter (fun p => v ∈ pathSet c p.1 p.2)
      = (leafThrough c v) ∪ (cherryFinset c).filter (fun p => p.2 = v) := by
    ext p
    constructor
    · intro hp
      have hp' := Finset.mem_filter.mp hp
      by_cases hne : p.2 = v
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hp'.1, hne⟩))
      · refine Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hp'.1, ?_⟩))
        refine (endpt_leafEdge_iff_ne (twoA_of_mem_cherryFinset hp'.1)).mpr ?_
        exact ⟨hp'.2, fun hv => hne hv.symm⟩
    · intro hp
      rcases Finset.mem_union.mp hp with hp' | hp'
      · obtain ⟨hp'1, hp'2⟩ := mem_leafThrough.mp hp'
        exact Finset.mem_filter.mpr ⟨hp'1,
          (mem_pathSet (c := c) (i := p.1) (v := p.2) (x := v)).mpr
            (Or.inr ((endpt_leafEdge_iff (twoA_of_mem_cherryFinset hp'1)).mp hp'2))⟩
      · obtain ⟨hp'1, hp'2⟩ := Finset.mem_filter.mp hp'
        exact Finset.mem_filter.mpr ⟨hp'1,
          (mem_pathSet (c := c) (i := p.1) (v := p.2) (x := v)).mpr (Or.inl hp'2.symm)⟩
  have hdisj : Disjoint (leafThrough c v) ((cherryFinset c).filter (fun p => p.2 = v)) := by
    refine Finset.disjoint_left.mpr fun p hp1 hp2 => ?_
    obtain ⟨hp11, hp12⟩ := mem_leafThrough.mp hp1
    obtain ⟨hp21, hp22⟩ := Finset.mem_filter.mp hp2
    exact ((endpt_leafEdge_iff_ne (twoA_of_mem_cherryFinset hp11)).mp hp12).2 hp22.symm
  have htotal : ((cherryFinset c).filter (fun p => v ∈ pathSet c p.1 p.2)).card
      = ((pathFinset c).filter (fun b => v ∈ b)).card := by
    have hinj := injOn_pathSet hc hn
    have h2 : ((cherryFinset c).filter (fun p => v ∈ pathSet c p.1 p.2)).image
        (fun p => pathSet c p.1 p.2) = (pathFinset c).filter (fun b => v ∈ b) := by
      apply Finset.Subset.antisymm
      · intro (b : Finset (Verts n)) hb
        obtain ⟨p, hp, he⟩ := Finset.mem_image.mp hb
        obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
        have hmem : b ∈ (cherryFinset c).image
            (fun p : Fin k × Verts n => pathSet c p.1 p.2) := by
          have hcf : (p.1, p.2) ∈ cherryFinset c := by
            rw [cherryFinset, Finset.mem_biUnion]
            exact ⟨p.1, Finset.mem_univ p.1, Finset.mem_image.mpr
              ⟨p.2, twoA_of_mem_cherryFinset hp1, rfl⟩⟩
          refine Finset.mem_image.mpr ⟨(p.1, p.2), hcf, he⟩
        have hmem' : b ∈ pathFinset c ∧ v ∈ b := And.intro hmem (he ▸ hp2)
        simp only [Finset.mem_filter]
        exact hmem'
      · intro b hb
        obtain ⟨hb1, hb2⟩ := Finset.mem_filter.mp hb
        obtain ⟨i, u, hu, he⟩ := mem_pathFinset hb1
        have hcf : (i, u) ∈ cherryFinset c := by
          rw [cherryFinset, Finset.mem_biUnion]
          exact ⟨i, Finset.mem_univ i, Finset.mem_image.mpr ⟨u, hu, rfl⟩⟩
        have hmem : (i, u) ∈ (cherryFinset c).filter
            (fun p : Fin k × Verts n => v ∈ pathSet c p.1 p.2) :=
          Finset.mem_filter.mpr ⟨hcf, he ▸ hb2⟩
        exact Finset.mem_image.mpr ⟨(i, u), hmem, he.symm⟩
    have hinj' : Set.InjOn (fun p : Fin k × Verts n => pathSet c p.1 p.2)
        (↑((cherryFinset c).filter (fun p => v ∈ pathSet c p.1 p.2)) : Set _) := by
      intro x hx y hy hxy
      obtain ⟨hx1, -⟩ := Finset.mem_filter.mp hx
      obtain ⟨hy1, -⟩ := Finset.mem_filter.mp hy
      exact hinj hx1 hy1 hxy
    have hcard := Finset.card_image_iff.mpr hinj'
    rw [h2] at hcard
    exact hcard.symm
  have hleft : (∑ p ∈ cherryFinset c, (if v ∈ pathSet c p.1 p.2 then (1 : ℕ) else 0))
      = (leafThrough c v).card + ((cherryFinset c).filter (fun p => p.2 = v)).card := by
    have hA : (∑ p ∈ cherryFinset c, (if endpt v (leafEdge c p.1 p.2) then (1 : ℕ) else 0))
        = (leafThrough c v).card := by
      rw [leafThrough, Finset.card_eq_sum_ones, Finset.sum_filter]
    have hB : (∑ p ∈ cherryFinset c, (if p.2 = v then (1 : ℕ) else 0))
        = ((cherryFinset c).filter (fun p => p.2 = v)).card := by
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    calc (∑ p ∈ cherryFinset c, (if v ∈ pathSet c p.1 p.2 then (1 : ℕ) else 0))
        = ∑ p ∈ cherryFinset c, ((if endpt v (leafEdge c p.1 p.2) then (1 : ℕ) else 0)
            + (if p.2 = v then (1 : ℕ) else 0)) := by
            apply Finset.sum_congr rfl
            intro p hp
            exact hsplit p hp
      _ = (leafThrough c v).card + ((cherryFinset c).filter (fun p => p.2 = v)).card := by
        rw [Finset.sum_add_distrib, hA, hB]
  have hleft' : (∑ p ∈ cherryFinset c, (if v ∈ pathSet c p.1 p.2 then (1 : ℕ) else 0))
      = ((cherryFinset c).filter (fun p => v ∈ pathSet c p.1 p.2)).card := by
    rw [← Finset.sum_filter, Finset.card_eq_sum_ones]
  rw [hleft'] at hleft
  have hfinal : (leafThrough c v).card + ((cherryFinset c).filter (fun p => p.2 = v)).card
      = ((pathFinset c).filter (fun b => v ∈ b)).card := by
    calc (leafThrough c v).card + ((cherryFinset c).filter (fun p => p.2 = v)).card
        = ((cherryFinset c).filter (fun p => v ∈ pathSet c p.1 p.2)).card := hleft.symm
      _ = ((pathFinset c).filter (fun b => v ∈ b)).card := htotal
  exact hfinal


/-! ### The last local quantity of the extremal case -/

/-- **EVERY VERTEX IS INCIDENT WITH EXACTLY `(n-1)/3` SINGLE EDGES.**  In an extremal admissible
colouring of `K_n` (`6k = 5(n-1)`) each vertex lies in `(n-1)/2` blocks of the Steiner triple
system of two-edge paths and is the centre of `(n-1)/6` of them, so it is a *leaf* in
`(n-1)/2 - (n-1)/6 = (n-1)/3` of them; and the single edges at `v` are counted by the blocks in
which `v` is a leaf (`tight_card_singleStar_eq_leafThrough`, `tight_card_leafThrough`).

Together with `Star.tight_star_centre` and `Star.tight_star_oneB` this is the **complete local
profile of an extremal colouring at every vertex**:

* `(n-1)/6` colours in which `v` is the centre of a two-edge path;
* `(n-1)/3` single edges at `v`, each of them an isolated single edge whose two ends are leaves
  of a two-edge path;
* `(n-1)/3` colours in which `v` is a leaf of a two-edge path whose leaf edge is elsewhere. -/
theorem tight_singleStar {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (h3 : 3 * Paths c = (edgeFinset (Finset.univ : Finset (Verts n))).card)
    (hk : 6 * k = 5 * (n - 1)) (v : Verts n) :
    3 * (singleStar c v).card = n - 1 := by
  have h1 := tight_card_singleStar_eq_leafThrough hc hn h3 hk v
  have h2 := tight_card_leafThrough hc hn h3 hk v
  have h3' := tight_blocks_through hc hn h3 v
  have h4 := tight_star_centre hc hn h3 hk v
  have h5 := card_cherryFinset_centred (c := c) v
  omega

/-- **THE LOCAL COUNT, TOTALLY SUMMED.**  In an extremal colouring the `n` vertices carry
`n (n-1)/3` single-edge incidences in total — the sum of the per-vertex counts
`tight_singleStar`. -/
theorem tight_sum_singleStar {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (h3 : 3 * Paths c = (edgeFinset (Finset.univ : Finset (Verts n))).card)
    (hk : 6 * k = 5 * (n - 1)) :
    (∑ v : Verts n, (singleStar c v).card) = n * (n - 1) / 3 := by
  have hper : ∀ v : Verts n, 3 * (singleStar c v).card = n - 1 :=
    fun v => tight_singleStar hc hn h3 hk v
  have hsum : (∑ v : Verts n, 3 * (singleStar c v).card) = ∑ v : Verts n, (n - 1) :=
    Finset.sum_congr rfl fun v _ => hper v
  rw [← Finset.mul_sum] at hsum
  simp at hsum
  omega

/-- **THE LOCAL AND THE GLOBAL COUNT AGREE.**  The per-vertex counts of `tight_singleStar` are the
global count of single edges of `Singles.tight_card_singles` seen vertex by vertex: summing them
and dividing by two (the handshaking lemma `sum_singleStar`) returns `n(n-1)/6`.  So the
description of the extremal case is *uniform at every point and consistent globally*. -/
theorem tight_singleFinset_of_star {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n)
    (h3 : 3 * Paths c = (edgeFinset (Finset.univ : Finset (Verts n))).card)
    (hk : 6 * k = 5 * (n - 1)) :
    (singleFinset c).card = (∑ v : Verts n, (singleStar c v).card) / 2 := by
  have h1 := sum_singleStar c
  have h2 := tight_sum_singleStar hc hn h3 hk
  omega

end JSP140
