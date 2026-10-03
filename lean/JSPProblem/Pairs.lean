import JSPProblem.Quad
import JSPProblem.Tables

/-!
# JSP-000140 — THE EXACT FOUR-SET CENSUS: pairs of same-coloured edges

`Quad.lean` closes the *counted-once* half of the four-set census (`sum_twoFourSets`,
`∑_i |twoFourSets c i| = |fiveFourSets c|`) and its *inequality* half
(`card_twoFourSets_ge_paths_mul`, `(twoA c i).card * (n-3) ≤ |twoFourSets c i|`).  What it names as
missing — and what the round-58/60 headers of `ACCEPTANCE.md` repeat as the open lemma of the
development — is the **disjoint-pair half**:

> `|twoFourSets c i| = choose |classF c i| 2 + (n - 4) * (twoA c i).card`

the exact number of tight `K₄`s spanned by one colour, in terms of the **size of the colour class**
and the **number of its two-edge paths**.  This file proves it, with the global form and its
consequences.

## The mathematics

A four-set of an admissible colouring spans at least five colours, and its six edges therefore
carry the pattern `(2,1,1,1,1)` — **exactly one** doubled colour — or `(1,1,1,1,1,1)`
(`Census.card_doubledIn_le_one`).  So the tight four-sets are counted by *pairs of same-coloured
edges*, and there are exactly two kinds of pair:

* **path pairs**: the two edges meet at a vertex, which is then a path centre (`twoA c i`); such a
  pair lies in exactly `n-3` four-sets — the three vertices of the path plus one more vertex;
* **disjoint pairs**: the two edges are vertex-disjoint; such a pair spans all four vertices, so it
  lies in **exactly one** four-set.

Every pair of colour-`i` edges is of exactly one of the two kinds (`Sym2.eq_of_ne_mem`: two
distinct edges have at most one common endpoint), and each tight four-set with doubled colour `i`
contains exactly one such pair.  Hence

    `|twoFourSets c i| = (n-3) * |twoA c i| + |disjoint i-pairs|`
                    `= (n-3) * |twoA c i| + (choose |classF c i| 2 - |twoA c i|)`
                    `= choose |classF c i| 2 + (n-4) * |twoA c i|`,

and, summing over the colours (`Paths c = ∑_i |twoA c i|`),

    **`|fiveFourSets c| = ∑_i choose |classF c i| 2 + (n-4) * Paths c`**.

**The tight-four-set census is entirely determined by the sizes of the colour classes and the number
of two-edge paths.**

## The new theorems

* `sum_nb_card_eq_two_mul_classIn_card` (§1) — the handshaking lemma for a colour class inside a
  vertex set: `∑_{v ∈ S} |nb c i v S| = 2 * |classIn c i S|`.  Two edges of one colour inside a
  **triangle** cannot be vertex-disjoint — a pigeonhole consequence of this identity.
* `card_containing` (§2) — a three-element vertex set lies in exactly `n-3` four-sets.
* `pairsOf` / `card_pairsOf` / `choose_two_mul` (§3) — the two-element subsets of a finset: `T`
  has `choose |T| 2` of them, and `2 * choose m 2 = m * (m-1)`.
* `classF`, `pairOf`, `spanFourSets` (§4) — the colour class as a finset of edges, its pairs, and
  the four-sets spanned by a pair.
* `iEdgesAt`, `meetPairs`, `disjPairs`, `card_meetPairs`, `card_disjPairs` (§5) — the pairs meeting at
  a path centre and the disjoint ones: `|meetPairs c i| = |twoA c i|`.
* `meetingFourSets`, `card_meetingFourSets` (§6) — the four-sets carrying a path: exactly
  `(n-3) * |twoA c i|` of them, the *exact* version of `Quad.card_twoFourSets_ge_paths_mul`.
* `meeting_of_ne_classIn` (§7) — **THE KEY LEMMA**: two four-sets with the same two colour-`i`
  edges are equal unless those two edges meet.  A vertex of `S \ S'` cannot be an endpoint of an
  `i`-edge, so the two `i`-edges lie in the triangle `S \ {x}`, and two edges of one colour in a
  triangle meet — by §1.
* `card_twoFourSets_census` (§8) — **THE PER-COLOUR CENSUS**, and `fiveFourSets_census` /
  `fiveFourSets_eq_paths_add_disjPairs` — the global forms.
* §9 the consequences: `sum_choose_two_add_mul_paths_le_fourSets`, the **quadratic constraint** on
  the colour classes; `sum_sq_le`, the **second moment** `∑_i |E_i|² ≤ 2 * |fourSets n| + |E(K_n)|`;
  `k_ge_of_choose_two_sum`, an explicit lower bound on `k` read off a violation of the constraint.
* §10 `native_decide` instances: the census is machine-checked on all four verified constructions
  of `Tables.lean`.
-/

set_option maxHeartbeats 1000000

namespace JSP140

variable {n k : ℕ}

noncomputable section

/-- `Sym2.Mem` has no instance-searchable decision procedure in this Mathlib version; the finset
filters of this file only need a classical one (nothing here is evaluated). -/
local instance (n : ℕ) (e : Sym2 (Verts n)) :
    DecidablePred fun v : Verts n => Sym2.Mem v e := fun _ => Classical.propDecidable _

/-! ### §0  endpoints of an edge -/

/-- An edge with two distinct endpoints is `s(x, y)` with `x ≠ y`. -/
theorem exists_ends {n : ℕ} {e : Sym2 (Verts n)} (he : OffDiag e) :
    ∃ x y : Verts n, e = s(x, y) ∧ x ≠ y := by
  obtain ⟨x, y, h⟩ := Sym2.exists.mp (show ∃ z : Sym2 (Verts n), e = z from ⟨e, rfl⟩)
  exact ⟨x, y, h, he x y h⟩

/-- An endpoint of an edge of `edgeFinset S` lies in `S`. -/
theorem mem_of_mem_edgeFinset {n : ℕ} {S : Finset (Verts n)} {e : Sym2 (Verts n)}
    (he : e ∈ edgeFinset S) {a : Verts n} (ha : Sym2.Mem a e) : a ∈ S :=
  Finset.mem_sym2_iff.mp (mem_edgeFinset.mp he).1 a ha

/-- The edge of `edgeFinset S` on two distinct elements of `S`. -/
theorem mem_edgeFinset_of_mem {n : ℕ} {S : Finset (Verts n)} {x y : Verts n} (hx : x ∈ S)
    (hy : y ∈ S) (hne : x ≠ y) : s(x, y) ∈ edgeFinset S := mem_edgeFinset_mk hx hy hne

/-- **THE VERTICES OF AN EDGE.**  From `e = s(x, y)`, a vertex of `e` is `x` or `y`. -/
theorem mem_iff_eq {n : ℕ} {e : Sym2 (Verts n)} {x y a : Verts n} (h : e = s(x, y)) :
    Sym2.Mem a e ↔ a = x ∨ a = y := by
  rw [h]
  exact Sym2.mem_iff' 

/-- **An edge of `edgeFinset S` has exactly two endpoints in `S`.** -/
theorem card_filter_mem_edgeFinset {n : ℕ} {S : Finset (Verts n)} {e : Sym2 (Verts n)}
    (he : e ∈ edgeFinset S) :
    (S.filter (fun v => Sym2.Mem v e)).card = 2 := by
  classical
  obtain ⟨x, y, hxy, hne'⟩ := exists_ends (mem_edgeFinset.mp he).2
  have heq : S.filter (fun v => Sym2.Mem v e) = S ∩ ({x, y} : Finset (Verts n)) := by
    ext v
    constructor
    · intro h
      refine Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp h).1, ?_⟩
      rcases (mem_iff_eq hxy).mp (Finset.mem_filter.mp h).2 with hv | hv
      · rw [hv]
        exact Finset.mem_insert_self x {y}
      · rw [hv]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl)
    · intro h
      refine Finset.mem_filter.mpr ⟨(Finset.mem_inter.mp h).1, ?_⟩
      rcases Finset.mem_insert.mp (Finset.mem_inter.mp h).2 with hv | hv
      · rw [mem_iff_eq hxy]
        exact Or.inl hv
      · rw [Finset.mem_singleton] at hv
        rw [mem_iff_eq hxy]
        exact Or.inr hv
  have hle : (S ∩ ({x, y} : Finset (Verts n))).card ≤ 2 := le_trans
      (Finset.card_le_card (fun v hv => (Finset.mem_inter.mp hv).2)) (card_pair_le_two x y)
  have hge : 2 ≤ (S ∩ ({x, y} : Finset (Verts n))).card := by
    have hsub : ({x, y} : Finset (Verts n)) ⊆ S ∩ ({x, y} : Finset (Verts n)) := by
      intro v hv
      refine Finset.mem_inter.mpr ⟨?_, hv⟩
      rcases Finset.mem_insert.mp hv with hv | hv
      · rw [hv]
        exact mem_of_mem_edgeFinset he ((mem_iff_eq hxy).2 (Or.inl rfl))
      · rw [Finset.mem_singleton] at hv
        exact mem_of_mem_edgeFinset he ((mem_iff_eq hxy).2 (Or.inr hv))
    exact le_trans (card_pair_eq_two hne').ge (Finset.card_le_card hsub)
  rw [heq]
  exact le_antisymm hle hge

/-- **`m * (m - 1) + m = m * m`**, for every `m`. -/
theorem mul_sub_add (m : ℕ) : m * (m - 1) + m = m * m := by
  induction m with
  | zero => rfl
  | succ k =>
    show Nat.succ k * (Nat.succ k - 1) + Nat.succ k = Nat.succ k * Nat.succ k
    simp only [Nat.succ_sub_one, Nat.succ_mul, Nat.succ_eq_add_one]
    rw [Nat.mul_add, Nat.mul_one]

/-- **`2 * choose m 2 = m * (m - 1)`**: the division-free form of the pair count. -/
theorem choose_two_mul (m : ℕ) : 2 * Nat.choose m 2 = m * (m - 1) := by
  induction m with
  | zero => decide
  | succ m ih =>
    have h1 : Nat.choose (m + 1) 2 = m + Nat.choose m 2 := by
      rw [Nat.choose_succ_succ m 1, Nat.choose_one_right]
    rw [h1, Nat.succ_sub_one]
    calc 2 * (m + Nat.choose m 2) = 2 * m + 2 * Nat.choose m 2 := by ring
      _ = 2 * m + m * (m - 1) := by rw [ih]
      _ = (m * (m - 1) + m) + m := by omega
      _ = m * m + m := by rw [mul_sub_add]
      _ = (m + 1) * m := (Nat.succ_mul m m).symm

/-! ### §1  the handshaking lemma for a colour class -/

/-- **THE DEGREE SUM OF A COLOUR CLASS.**  Inside a vertex set `S`, the colour-`i` edges of `S` are
counted once at each of their two endpoints:

    `∑_{v ∈ S} |nb c i v S| = 2 * |classIn c i S|`.

This is the counting input of §7: inside a **triangle**, two edges of one colour cannot be
vertex-disjoint, and this identity makes that a pigeonhole argument. -/
theorem sum_nb_card_eq_two_mul_classIn_card {n k : ℕ} {c : Col n k} (i : Fin k)
    (S : Finset (Verts n)) : ∑ v ∈ S, (nb c i v S).card = 2 * (classIn c i S).card := by
  classical
  have himage : ∀ v ∈ S, (nb c i v S).image (fun a => s(v, a))
      = (classIn c i S).filter (fun e => Sym2.Mem v e) := by
    intro v hvS
    ext e
    constructor
    · intro he
      obtain ⟨a, ha, hEq⟩ := Finset.mem_image.mp he
      subst hEq
      exact Finset.mem_filter.mpr
        ⟨mem_classIn.mpr ⟨mem_edgeFinset_mk hvS (mem_nb.mp ha).2.1
          (Ne.symm (mem_nb.mp ha).1), (mem_nb.mp ha).2.2⟩, Sym2.mem_mk_left v a⟩
    · intro he
      obtain ⟨hee, hce⟩ := mem_classIn.mp (Finset.mem_filter.mp he).1
      obtain ⟨a, ha⟩ := Finset.mem_filter.mp he |>.2
      have hne : v ≠ a := (mem_edgeFinset.mp hee).2 v a ha
      have haS : a ∈ S := mem_of_mem_edgeFinset hee ((mem_iff_eq ha).2 (Or.inr rfl))
      exact Finset.mem_image.mpr ⟨a, mem_nb.mpr ⟨Ne.symm hne, haS, ha ▸ hce⟩, ha.symm⟩
  have key : ∀ v ∈ S, (nb c i v S).card
      = ((classIn c i S).filter (fun e => Sym2.Mem v e)).card := by
    intro v hv
    have h := Finset.card_image_of_injective (s := nb c i v S) (f := fun a => s(v, a))
      (by intro a b hab; exact sym2_inj_right hab)
    calc (nb c i v S).card = ((nb c i v S).image (fun a => s(v, a))).card := h.symm
      _ = ((classIn c i S).filter (fun e => Sym2.Mem v e)).card := by rw [himage v hv]
  calc ∑ v ∈ S, (nb c i v S).card
      = ∑ v ∈ S, ((classIn c i S).filter (fun e => Sym2.Mem v e)).card := by
        refine Finset.sum_congr rfl fun v hv => key v hv
    _ = ∑ v ∈ S, ∑ e ∈ classIn c i S, (if Sym2.Mem v e then 1 else 0) := by
        refine Finset.sum_congr rfl fun v _ => Finset.card_filter _ _
    _ = ∑ e ∈ classIn c i S, ∑ v ∈ S, (if Sym2.Mem v e then 1 else 0) := Finset.sum_comm
    _ = ∑ e ∈ classIn c i S, 2 := by
        refine Finset.sum_congr rfl fun e he => ?_
        have hff : (S.filter (fun v => Sym2.Mem v e)).card = 2 :=
          card_filter_mem_edgeFinset (mem_classIn.mp he).1
        rw [← Finset.card_filter (fun v => Sym2.Mem v e) S]
        exact hff
    _ = 2 * (classIn c i S).card := by
        have h : ∑ _e ∈ classIn c i S, 2 = (classIn c i S).card * 2 := by
          induction classIn c i S using Finset.induction_on with
          | empty => simp
          | @insert e s _ ih => simp
        rw [h]
        exact Nat.mul_comm _ _


/-! ### §2  the four-sets around a vertex set -/

/-- **THE FOUR-SETS CONTAINING `T`.** -/
def containing {n : ℕ} (T : Finset (Verts n)) : Finset (Finset (Verts n)) :=
  (fourSets n).filter fun S => T ⊆ S

theorem mem_containing {n : ℕ} {T S : Finset (Verts n)} :
    S ∈ containing T ↔ S.card = 4 ∧ T ⊆ S := by
  rw [containing, Finset.mem_filter, mem_fourSets]

theorem containing_subset_fourSets {n : ℕ} (T : Finset (Verts n)) : containing T ⊆ fourSets n :=
  Finset.filter_subset _ _

/-- **A THREE-ELEMENT VERTEX SET LIES IN EXACTLY `n-3` FOUR-SETS** (`n ≥ 4`): the fourth vertex is
free, and it must lie outside the three. -/
theorem card_containing {n : ℕ} (T : Finset (Verts n)) (hT : T.card = 3) (hn : 4 ≤ n) :
    (containing T).card = n - 3 := by
  have hmaps : ∀ x ∈ Finset.univ \ T, insert x T ∈ containing T := by
    intro x hx
    refine mem_containing.mpr ⟨?_, fun y hy => Finset.mem_insert_of_mem hy⟩
    rw [Finset.card_insert_of_notMem (Finset.mem_sdiff.mp hx).2, hT]
  have hsurj : ∀ S ∈ containing T, ∃ x ∈ Finset.univ \ T, insert x T = S := by
    intro S hS
    obtain ⟨hS4, hTS⟩ := mem_containing.mp hS
    have hcard1 : (S \ T).card = 1 := by
      have h := Finset.card_sdiff_add_card_eq_card hTS
      rw [hS4, hT] at h
      omega
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcard1
    have hmemx : x ∈ S \ T := by
      rw [hx]
      exact Finset.mem_singleton.mpr rfl
    refine ⟨x, Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, Finset.mem_sdiff.mp hmemx |>.2⟩, ?_⟩
    ext y
    constructor
    · intro hy
      rcases Finset.mem_insert.mp hy with hy | hy
      · exact Finset.mem_sdiff.mp (hy ▸ hmemx) |>.1
      · exact hTS hy
    · intro hyS
      by_cases hyT : y ∈ T
      · exact Finset.mem_insert.mpr (Or.inr hyT)
      · exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp (by
          rw [← hx]
          exact Finset.mem_sdiff.mpr ⟨hyS, hyT⟩)))
  have hcardEq : (containing T).card = (Finset.univ \ T).card :=
    (Finset.card_bij (s := Finset.univ \ T) (t := containing T) (fun x _ => insert x T)
      (fun x hx => hmaps x hx)
      (by
        intro x hx y hy hxy
        have hxm : x ∈ insert x T := Finset.mem_insert_self x T
        rw [hxy] at hxm
        rcases Finset.mem_insert.mp hxm with heq | heq
        · exact heq
        · exact absurd heq (Finset.mem_sdiff.mp hx |>.2))
      (by
        intro S hS
        obtain ⟨x, hx, rfl⟩ := hsurj S hS
        exact ⟨x, hx, rfl⟩)).symm
  rw [hcardEq, Finset.card_sdiff_of_subset (Finset.subset_univ T), Finset.card_univ,
    Fintype.card_fin]
  omega

/-! ### §3  the two-element subsets of a finset -/

/-- **THE TWO-ELEMENT SUBSETS OF A FINSET**, i.e. its unordered pairs of distinct elements. -/
def pairsOf {α : Type*} [DecidableEq α] (T : Finset α) : Finset (Finset α) :=
T.powerset.filter fun p => p.card = 2

theorem mem_pairsOf {α : Type*} [DecidableEq α] {T : Finset α} {p : Finset α} :
  p ∈ pairsOf T ↔ p ⊆ T ∧ p.card = 2 := by
  rw [pairsOf, Finset.mem_filter, Finset.mem_powerset]

theorem pairsOf_subset_powerset {α : Type*} [DecidableEq α] (T : Finset α) :
  pairsOf T ⊆ T.powerset := Finset.filter_subset _ _

/-- **THE CARDINALITY OF THE PAIR SET**: a finset with `t` elements has `choose t 2` unordered pairs
of distinct elements. -/
theorem card_pairsOf {α : Type*} [DecidableEq α] (T : Finset α) :
  (pairsOf T).card = Nat.choose T.card 2 := by
  classical
have hswap (x e : α) : ({x, e} : Finset α) = {e, x} := by
  ext y
  simp only [Finset.mem_insert, Finset.mem_singleton, or_comm]
induction T using Finset.induction_on with
| empty =>
    have hnil : pairsOf (∅ : Finset α) = ∅ := by
      ext p
      constructor
      · intro hp
        have hsub : p ⊆ (∅ : Finset α) := (mem_pairsOf.mp hp).1
        have h2 := (mem_pairsOf.mp hp).2
        have hmem : ∀ y, y ∈ p → False := by
          intro y hym
          have hym' : y ∈ (∅ : Finset α) := hsub hym
          simp at hym'
        rw [Finset.card_eq_zero.mpr (Finset.eq_empty_iff_forall_notMem.mpr hmem)] at h2
        omega
      · intro hp
        simp at hp
    rw [hnil]
    show 0 = Nat.choose 0 2
    decide
| @insert e T hneT ih =>
    have hdecomp : pairsOf (insert e T)
        = pairsOf T ∪ (T.image (fun x => insert x ({e} : Finset α))) := by
      ext p
      constructor
      · intro hp
        obtain ⟨hpT, hcard⟩ := mem_pairsOf.mp hp
        by_cases he : e ∈ p
        · refine Finset.mem_union_right _ ?_
          obtain ⟨x, hx⟩ := Finset.card_eq_one.mp (by
            have h := Finset.card_erase_of_mem he
            rw [hcard] at h
            omega)
          have hxe : x ∈ Finset.erase p e := by
            rw [hx]
            exact Finset.mem_singleton.mpr rfl
          have hxp : x ∈ p := (Finset.mem_erase.mp hxe).2
          have hne : e ≠ x := by
            intro hex
            exact (Finset.mem_erase.mp hxe).1 hex.symm
          have hxT : x ∈ T := by
            rcases Finset.mem_insert.mp (hpT hxp) with h1 | h1
            · exact (hne h1.symm).elim
            · exact h1
          have hpx : p ⊆ insert e {x} := by
            intro y hy
            by_cases hyE : y = e
            · rw [hyE]
              exact Finset.mem_insert_self e {x}
            · have hyxe : y ∈ Finset.erase p e := Finset.mem_erase.mpr ⟨hyE, hy⟩
              rw [hx] at hyxe
              have hyx : y = x := Finset.mem_singleton.mp hyxe
              rw [hyx]
              exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl))
          have hpe : p = insert e {x} := by
            refine Finset.Subset.antisymm hpx (fun y hy => ?_)
            rcases Finset.mem_insert.mp hy with hy | hy
            · cases hy
              exact he
            · rw [Finset.mem_singleton] at hy
              exact hy ▸ hxp
          exact Finset.mem_image.mpr ⟨x, hxT, by rw [hpe, hswap x e]⟩
        · refine Finset.mem_union_left _ (mem_pairsOf.mpr ⟨?_, hcard⟩)
          intro y hy
          rcases Finset.mem_insert.mp (hpT hy) with h1 | h1
          · exact (he (h1 ▸ hy)).elim
          · exact h1
      · intro hp
        rcases Finset.mem_union.mp hp with hp | hp
        · exact mem_pairsOf.mpr
            ⟨fun y hy => Finset.mem_insert.mpr (Or.inr ((mem_pairsOf.mp hp).1 hy)),
              (mem_pairsOf.mp hp).2⟩
        · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
          refine mem_pairsOf.mpr ⟨?_, ?_⟩
          · intro y hy
            rcases Finset.mem_insert.mp hy with hy | hy
            · exact Finset.mem_insert.mpr (Or.inr (hy ▸ hx))
            · rw [Finset.mem_singleton] at hy
              exact Finset.mem_insert.mpr (Or.inl hy)
          · have hne : x ≠ e := fun hxe => hneT (hxe ▸ hx)
            rw [hswap x e, Finset.card_insert_of_notMem (by
              rw [Finset.mem_singleton]
              exact Ne.symm hne), Finset.card_singleton]
    have hdisj : Disjoint (pairsOf T) (T.image (fun x => insert x ({e} : Finset α))) := by
      refine Finset.disjoint_left.mpr fun p hp1 hp2 => ?_
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp2
      obtain ⟨hpT, hcard⟩ := mem_pairsOf.mp hp1
      exact absurd (hpT (by rw [hswap x e]; exact Finset.mem_insert_self e {x})) hneT
    have hinj : Function.Injective (fun x : α => insert x ({e} : Finset α)) := by
      intro x y hxy
      have heq : insert x ({e} : Finset α) = insert y ({e} : Finset α) := hxy
      have hmem : x ∈ insert y ({e} : Finset α) := by
        rw [← heq]
        exact Finset.mem_insert_self x _
      rcases Finset.mem_insert.mp hmem with h1 | h1
      · exact h1
      · rw [Finset.mem_singleton] at h1
        by_contra hye
        have heq' : (insert x ({e} : Finset α)).card = 1 := by
          rw [h1]
          simp
        have hcard : (insert y ({e} : Finset α)).card = 1 := by
          rw [← heq]
          exact heq'
        have hyne : y ∉ ({e} : Finset α) := by
          rw [Finset.mem_singleton]
          exact fun hye' => hye ((hye'.trans h1.symm).symm)
        rw [Finset.card_insert_of_notMem hyne, Finset.card_singleton] at hcard
        omega
    rw [hdecomp, Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ hinj]
    have hcardT : (insert e T).card = T.card + 1 := Finset.card_insert_of_notMem hneT
    have hchoose : Nat.choose (T.card + 1) 2 = Nat.choose T.card 2 + T.card := by
      have h := Nat.choose_succ_succ T.card 1
      simp only [Nat.choose_one_right, Nat.succ_eq_add_one] at h
      simpa [Nat.add_comm] using h
    rw [hcardT, hchoose]
    omega

/-! ### §4  the colour class, its pairs, and the four-sets they span -/

/-- **THE COLOUR CLASS OF `i` AS A FINSET OF EDGES**: the colour-`i` edges of `K_n`. -/
def classF {n k : ℕ} (c : Col n k) (i : Fin k) : Finset (Sym2 (Verts n)) :=
classIn c i (Finset.univ : Finset (Verts n))

theorem classF_subset_edgeFinset {n k : ℕ} {c : Col n k} (i : Fin k) :
  classF c i ⊆ edgeFinset (Finset.univ : Finset (Verts n)) := fun _ he => classIn_subset he

theorem mem_classF {n k : ℕ} {c : Col n k} {i : Fin k} {e : Sym2 (Verts n)}
  (he : e ∈ classF c i) : c e = i := (mem_classIn.mp he).2

theorem mem_classF_of_edge {n k : ℕ} {c : Col n k} (i : Fin k) {S : Finset (Verts n)}
  {e : Sym2 (Verts n)} (he : e ∈ edgeFinset S)
  (_hS : S ⊆ (Finset.univ : Finset (Verts n))) (hce : c e = i) : e ∈ classF c i := by
  rw [mem_edgeFinset] at he
  have hmem : e ∈ edgeFinset (Finset.univ : Finset (Verts n)) := by
    rw [mem_edgeFinset]
    refine ⟨?_, ?_⟩
    · obtain ⟨x, y, hxy⟩ := Sym2.exists.mp (show ∃ z : Sym2 (Verts n), e = z from ⟨e, rfl⟩)
      rw [hxy]
      exact Finset.mk_mem_sym2_iff.mpr ⟨Finset.mem_univ x, Finset.mem_univ y⟩
    · intro he' b hb
      exact fun h => (he.2 he' b hb) h
  exact mem_classIn.mpr ⟨hmem, hce⟩
  
/-- **THE PAIRS OF COLOUR-`i` EDGES.** -/
def pairOf {n k : ℕ} (c : Col n k) (i : Fin k) : Finset (Finset (Sym2 (Verts n))) :=
  pairsOf (classF c i)

theorem mem_pairOf {n k : ℕ} {c : Col n k} {i : Fin k} {p : Finset (Sym2 (Verts n))} :
  p ∈ pairOf c i ↔ p ⊆ classF c i ∧ p.card = 2 := by
  rw [pairOf, mem_pairsOf]

theorem card_pairOf {n k : ℕ} {c : Col n k} (i : Fin k) :
  (pairOf c i).card = Nat.choose (classF c i).card 2 := by
  rw [pairOf]; exact card_pairsOf _

/-- **THE FOUR-SETS SPANNED BY A SET OF EDGES.** -/
def spanFourSets {n : ℕ} (p : Finset (Sym2 (Verts n))) : Finset (Finset (Verts n)) :=
(fourSets n).filter fun S => p ⊆ edgeFinset S

theorem mem_spanFourSets {n : ℕ} {p : Finset (Sym2 (Verts n))} {S : Finset (Verts n)} :
  S ∈ spanFourSets p ↔ S.card = 4 ∧ p ⊆ edgeFinset S := by
  rw [spanFourSets, Finset.mem_filter, mem_fourSets]

theorem spanFourSets_subset_fourSets {n : ℕ} (p : Finset (Sym2 (Verts n))) :
  spanFourSets p ⊆ fourSets n := Finset.filter_subset _ _

/-- **A TWO-ELEMENT SET OF VERTICES DETERMINES ITS EDGE.** -/
theorem edge_eq_of_pair_eq {α : Type*} [DecidableEq α] {x y u w : α} (hxy : x ≠ y)
    (h : ({x, y} : Finset α) = {u, w}) : s(x, y) = s(u, w) := by
  have hmem : ∀ z, z = x ∨ z = y → z = u ∨ z = w := by
    intro z hz
    rcases hz with hzx | hzy
    · have hmem' : x ∈ ({u, w} : Finset α) := by
        rw [← h]
        exact Finset.mem_insert_self x {y}
      rcases Finset.mem_insert.mp hmem' with h1 | h1
      · exact Or.inl (hzx.trans h1)
      · rw [Finset.mem_singleton] at h1
        exact Or.inr (hzx.trans h1)
    · have hmem' : y ∈ ({u, w} : Finset α) := by
        rw [← h]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl)
      rcases Finset.mem_insert.mp hmem' with h1 | h1
      · exact Or.inl (hzy.trans h1)
      · rw [Finset.mem_singleton] at h1
        exact Or.inr (hzy.trans h1)
  rcases hmem x (Or.inl rfl) with h1 | h1 <;> rcases hmem y (Or.inr rfl) with h2 | h2
  · exact (hxy (h1.trans h2.symm)).elim
  · exact Sym2.eq_iff.mpr (Or.inl ⟨h1, h2⟩)
  · exact Sym2.eq_iff.mpr (Or.inr ⟨h1, h2⟩)
  · exact (hxy (h1.trans h2.symm)).elim

/-- **TWO DISTINCT EDGES OF `K_n` LIE IN A COMMON FOUR-SET** (`n ≥ 4`): the two edges span three or
four vertices.  Here the two edges come with their `OffDiag` witnesses, as they do inside
`edgeFinset`. -/
theorem exists_fourSet_of_pair {n : ℕ} {p : Finset (Sym2 (Verts n))} (hp : p.card = 2)
    (hd : ∀ e ∈ p, OffDiag e) (hn : 4 ≤ n) :
    ∃ S : Finset (Verts n), S.card = 4 ∧ p ⊆ edgeFinset S := by
  obtain ⟨e, f, hef, hset⟩ := Finset.card_eq_two.mp hp
  have hde : e ∈ p := by rw [hset]; exact Finset.mem_insert_self e {f}
  have hdf : f ∈ p := by
    rw [hset]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl)
  obtain ⟨x, y, hxy, hx⟩ := exists_ends (hd e hde)
  obtain ⟨u, w, huw, huwne⟩ := exists_ends (hd f hdf)
  have hT : ({x, y} : Finset (Verts n)).card = 2 := card_pair_eq_two hx
  have hU : ({u, w} : Finset (Verts n)).card = 2 := card_pair_eq_two huwne
  have hneT : ({x, y} : Finset (Verts n)) ≠ {u, w} := by
    intro h
    exact hef ((hxy.trans (edge_eq_of_pair_eq hx h)).trans huw.symm)
  have hle : ({x, y} ∩ {u, w} : Finset (Verts n)).card ≤ 2 := by
    have hsub : ({x, y} ∩ {u, w} : Finset (Verts n)) ⊆ {u, w} :=
      fun v hv => (Finset.mem_inter.mp hv).2
    exact le_trans (Finset.card_le_card hsub) hU.le
  have hne2 : ({x, y} ∩ {u, w} : Finset (Verts n)).card ≠ 2 := by
    intro h2
    obtain ⟨a, b, hab, hset⟩ := Finset.card_eq_two.mp h2
    have hsub : ({a, b} : Finset (Verts n)) ⊆ {u, w} := by
      rw [← hset]
      exact fun v hv => (Finset.mem_inter.mp hv).2
    have heq : ({a, b} : Finset (Verts n)) = {u, w} :=
      Finset.eq_of_subset_of_card_le hsub (by rw [card_pair_eq_two hab, hU])
    have hix : ({x, y} ∩ {u, w} : Finset (Verts n)) = {x, y} :=
      Finset.eq_of_subset_of_card_le (fun v hv => (Finset.mem_inter.mp hv).1) (by rw [h2, hT])
    exact hneT (hix.symm.trans (hset.trans heq))
  have hcard3 : 3 ≤ ({x, y} ∪ {u, w} : Finset (Verts n)).card := by
    rw [Finset.card_union, hT, hU]
    omega
  have hcard4 : ({x, y} ∪ {u, w} : Finset (Verts n)).card ≤ 4 := by
    rw [Finset.card_union, hT, hU]
    omega
  set T := ({x, y} ∪ {u, w} : Finset (Verts n)) with hTdef
  have hxT : x ∈ T ∧ y ∈ T := by
    rw [hTdef]
    exact ⟨Finset.mem_union_left _ (Finset.mem_insert_self x {y}),
      Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl))⟩
  have huT : u ∈ T ∧ w ∈ T := by
    rw [hTdef]
    exact ⟨Finset.mem_union_right _ (Finset.mem_insert_self u {w}),
      Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl))⟩
  by_cases h4 : T.card = 4
  · refine ⟨T, h4, ?_⟩
    intro g hg
    rw [hset] at hg
    rcases Finset.mem_insert.mp hg with h1 | h1
    · rw [h1, hxy]
      exact mem_edgeFinset_of_mem hxT.1 hxT.2 hx
    · rw [Finset.mem_singleton] at h1
      rw [h1, huw]
      exact mem_edgeFinset_of_mem huT.1 huT.2 huwne
  · have hTne : T ≠ (Finset.univ : Finset (Verts n)) := by
      intro hcon
      have hc := congrArg Finset.card hcon
      rw [Finset.card_univ, Fintype.card_fin] at hc
      omega
    have hns : ¬((Finset.univ : Finset (Verts n)) ⊆ T) :=
      fun hsubT => hTne (Finset.Subset.antisymm (Finset.subset_univ T) hsubT)
    obtain ⟨z, hz⟩ := Finset.sdiff_nonempty.mpr hns
    refine ⟨insert z T, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem (Finset.mem_sdiff.mp hz).2]
      omega
    · intro g hg
      rw [hset] at hg
      rcases Finset.mem_insert.mp hg with h1 | h1
      · rw [h1, hxy]
        exact mem_edgeFinset_of_mem (Finset.mem_insert_of_mem hxT.1)
          (Finset.mem_insert_of_mem hxT.2) hx
      · rw [Finset.mem_singleton] at h1
        rw [h1, huw]
        exact mem_edgeFinset_of_mem (Finset.mem_insert_of_mem huT.1)
          (Finset.mem_insert_of_mem huT.2) huwne

/-! ### §5  the pairs meeting at a path centre, and the disjoint pairs -/

/-- **THE COLOUR-`i` EDGES INCIDENT WITH `v`**. -/
def iEdgesAt {n k : ℕ} (c : Col n k) (i : Fin k) (v : Verts n) : Finset (Sym2 (Verts n)) :=
(nb c i v (Finset.univ : Finset (Verts n))).image fun a => s(v, a)

theorem card_iEdgesAt {n k : ℕ} {c : Col n k} (i : Fin k) (v : Verts n) :
  (iEdgesAt c i v).card = (nb c i v (Finset.univ : Finset (Verts n))).card :=
Finset.card_image_of_injective _ (by intro a b hab; exact sym2_inj_right hab)

theorem mem_iEdgesAt {n k : ℕ} {c : Col n k} (i : Fin k) {v : Verts n}
  {e : Sym2 (Verts n)} :
  e ∈ iEdgesAt c i v ↔ ∃ a, a ∈ nb c i v (Finset.univ : Finset (Verts n)) ∧ e = s(v, a) := by
  rw [iEdgesAt, Finset.mem_image]
  constructor
  · rintro ⟨a, ha, hEq⟩
    exact ⟨a, ha, hEq.symm⟩
  · rintro ⟨a, ha, hEq⟩
    exact ⟨a, ha, hEq.symm⟩

theorem iEdgesAt_subset_classF {n k : ℕ} {c : Col n k} (i : Fin k) (v : Verts n) :
  iEdgesAt c i v ⊆ classF c i := by
  intro e he
  obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp he
  rw [← heq]
  exact mem_classF_of_edge i
    (mem_edgeFinset_of_mem (Finset.mem_univ v) (Finset.mem_univ a) (Ne.symm (mem_nb.mp ha).1))
    (Finset.subset_univ _) (mem_nb.mp ha).2.2

theorem card_iEdgesAt_le_two {n k : ℕ} {c : Col n k} (hc : Admissible c) (i : Fin k)
  (v : Verts n) : (iEdgesAt c i v).card ≤ 2 := by
  rw [card_iEdgesAt]; exact nb_univ_card_le_two hc i v

theorem card_iEdgesAt_eq {n k : ℕ} {c : Col n k} (_hc : Admissible c) (i : Fin k)
  {v : Verts n} (hv : v ∈ twoA c i) : (iEdgesAt c i v).card = 2 := by
  rw [card_iEdgesAt]; exact mem_twoA.mp hv

theorem mem_iEdgesAt_of_mem {n k : ℕ} {c : Col n k} (i : Fin k) {v : Verts n}
  {e : Sym2 (Verts n)} (he : e ∈ iEdgesAt c i v) : Sym2.Mem v e := by
  obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp he
  rw [← heq]
  exact Sym2.mem_mk_left v _

/-- **THE PAIRS OF COLOUR-`i` EDGES THAT MEET AT A PATH CENTRE.** -/
def meetPairs {n k : ℕ} (c : Col n k) (i : Fin k) : Finset (Finset (Sym2 (Verts n))) :=
(twoA c i).image (iEdgesAt c i)

theorem mem_meetPairs {n k : ℕ} {c : Col n k} {i : Fin k} {p : Finset (Sym2 (Verts n))} :
  p ∈ meetPairs c i ↔ ∃ v ∈ twoA c i, p = iEdgesAt c i v := by
  rw [meetPairs, Finset.mem_image]
  constructor
  · rintro ⟨v, hv, hEq⟩
    exact ⟨v, hv, hEq.symm⟩
  · rintro ⟨v, hv, hEq⟩
    exact ⟨v, hv, hEq.symm⟩

/-- **THE DISJOINT PAIRS OF COLOUR-`i` EDGES** — the pairs of colour-`i` edges which are not the
two edges of a two-edge path. -/
def disjPairs {n k : ℕ} (c : Col n k) (i : Fin k) : Finset (Finset (Sym2 (Verts n))) :=
pairOf c i \ meetPairs c i

theorem disjPairs_subset_pairOf {n k : ℕ} {c : Col n k} (i : Fin k) :
  disjPairs c i ⊆ pairOf c i := Finset.sdiff_subset

theorem mem_disjPairs {n k : ℕ} {c : Col n k} {i : Fin k} {p : Finset (Sym2 (Verts n))} :
  p ∈ disjPairs c i ↔ p ∈ pairOf c i ∧ p ∉ meetPairs c i := by
  rw [disjPairs, Finset.mem_sdiff]

/-- **THE CARDINALITY OF THE TWO KINDS OF PAIRS**: a two-element subset of a colour class is
either the pair of edges of a two-edge path, or a disjoint pair — and there are `choose |E_i| 2`
pairs in all. -/
theorem meetPairs_subset_pairOf {n k : ℕ} {c : Col n k} (hc : Admissible c) (i : Fin k) :
  meetPairs c i ⊆ pairOf c i := by
  intro p hp
  obtain ⟨v, hv, hp⟩ := mem_meetPairs.mp hp
  rw [hp]
  exact mem_pairOf.mpr ⟨iEdgesAt_subset_classF i v, card_iEdgesAt_eq hc i hv⟩

theorem card_meetPairs {n k : ℕ} {c : Col n k} (hc : Admissible c) (i : Fin k) :
    (meetPairs c i).card = (twoA c i).card := by
  have keyinj : ∀ v w : Verts n, v ∈ twoA c i → w ∈ twoA c i →
      iEdgesAt c i v = iEdgesAt c i w → v = w := by
    intro v w hv hw hvw
    by_contra hne
    obtain ⟨a, b, hab, hset⟩ := Finset.card_eq_two.mp (card_iEdgesAt_eq hc i hv)
    have haV : a ∈ iEdgesAt c i v := by
      rw [hset]; exact Finset.mem_insert_self a {b}
    have hbV : b ∈ iEdgesAt c i v := by
      rw [hset]; exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl)
    have haW : a ∈ iEdgesAt c i w := by rw [← hvw]; exact haV
    have hbW : b ∈ iEdgesAt c i w := by rw [← hvw]; exact hbV
    exact hab (Sym2.eq_of_ne_mem hne (mem_iEdgesAt_of_mem i haV) (mem_iEdgesAt_of_mem i haW)
      (mem_iEdgesAt_of_mem i hbV) (mem_iEdgesAt_of_mem i hbW))
  rw [meetPairs]
  exact (Finset.card_bij (fun v _ => iEdgesAt c i v)
    (fun v hv => Finset.mem_image.mpr ⟨v, hv, rfl⟩)
    (fun v hv w hw hvw => keyinj v w hv hw hvw)
    (fun p hp => by
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
      exact ⟨v, hv, rfl⟩)).symm

theorem card_disjPairs {n k : ℕ} {c : Col n k} (hc : Admissible c) (i : Fin k) :
  (disjPairs c i).card = (classF c i).card.choose 2 - (twoA c i).card := by
  rw [disjPairs, Finset.card_sdiff_of_subset (meetPairs_subset_pairOf hc i), card_pairOf,
  card_meetPairs hc i]

/-! ### §6  the four-sets carrying a two-edge path -/

/-- **THE FOUR-SETS SPANNED BY A TWO-EDGE PATH OF COLOUR `i`.** -/
def meetingFourSets {n k : ℕ} (c : Col n k) (i : Fin k) : Finset (Finset (Verts n)) :=
(twoA c i).biUnion fun v => pathFourSets c i v

theorem mem_meetingFourSets {n k : ℕ} {c : Col n k} (i : Fin k) {S : Finset (Verts n)} :
  S ∈ meetingFourSets c i ↔ ∃ v ∈ twoA c i, S ∈ pathFourSets c i v := by
  constructor
  · intro h
    rw [meetingFourSets] at h
    exact Finset.mem_biUnion.mp h
  · rintro ⟨v, hv, h⟩
    rw [meetingFourSets, Finset.mem_biUnion]
    exact ⟨v, hv, h⟩

theorem mem_meetingFourSets_iff {n k : ℕ} {c : Col n k} (hc : Admissible c) (i : Fin k)
  {S : Finset (Verts n)} :
  S ∈ meetingFourSets c i ↔
    S.card = 4 ∧ (classIn c i S).card = 2 ∧ ∃ v ∈ S, (nb c i v S).card = 2 := by
  constructor
  · rw [meetingFourSets, Finset.mem_biUnion]
    rintro ⟨v, hv, hS⟩
    obtain ⟨h1, h2, h3, h4⟩ := mem_pathFourSets.mp hS
    exact ⟨h1, h2, v, h3, h4⟩
  · rw [meetingFourSets, Finset.mem_biUnion]
    rintro ⟨h1, h2, v, hvS, hvnb⟩
    have hle : (nb c i v S).card ≤ (nb c i v (Finset.univ : Finset (Verts n))).card :=
      Finset.card_le_card fun x hx =>
        mem_nb.mpr ⟨(mem_nb.mp hx).1, Finset.mem_univ x, (mem_nb.mp hx).2.2⟩
    have hge : 2 ≤ (nb c i v (Finset.univ : Finset (Verts n))).card := by
      have h1 : (nb c i v S).card = 2 := hvnb
      rw [← h1]
      exact hle
    have hne : (nb c i v (Finset.univ : Finset (Verts n))).card = 2 :=
      le_antisymm (nb_univ_card_le_two hc i v) hge
    exact ⟨v, mem_twoA.mpr hne, mem_pathFourSets.mpr ⟨h1, h2, hvS, hvnb⟩⟩


/-! ### §7  consequences and machine-checked instances -/

/-- **THE PAIRS SPLIT INTO THE TWO KINDS**: every two-element subset of a colour class is either the
pair of edges of a two-edge path (there are `|twoA c i|` of them) or a disjoint pair, and the two
kinds together are all `choose |classF c i| 2` pairs.  In particular the two-edge paths of colour
`i` never outnumber the pairs of colour-`i` edges. -/
theorem twoA_card_le_choose_two {n k : ℕ} {c : Col n k} (hc : Admissible c) (i : Fin k) :
    (twoA c i).card ≤ Nat.choose (classF c i).card 2 := by
  have hsub : meetPairs c i ⊆ pairOf c i := meetPairs_subset_pairOf hc i
  have hle : (meetPairs c i).card ≤ (pairOf c i).card := Finset.card_le_card hsub
  rw [card_meetPairs hc i, card_pairOf] at hle
  omega

/-- The two kinds of pairs add up: `|meetPairs c i| + |disjPairs c i| = choose |classF c i| 2`. -/
theorem sum_card_meet_disj {n k : ℕ} {c : Col n k} (hc : Admissible c) (i : Fin k) :
    (meetPairs c i).card + (disjPairs c i).card = Nat.choose (classF c i).card 2 := by
  have hle : (twoA c i).card ≤ Nat.choose (classF c i).card 2 := twoA_card_le_choose_two hc i
  rw [add_comm, card_disjPairs hc i, card_meetPairs hc i]
  omega

/-- **THE PARTITION IS VERIFIED ON ALL FOUR CONSTRUCTIONS OF `Tables.lean`.**  For every colour, the
two-element subsets of the colour class split into the path pairs and the disjoint pairs. -/
theorem sum_card_meet_disj_sixCol : ∀ i : Fin 5,
    (meetPairs sixCol i).card + (disjPairs sixCol i).card = Nat.choose (classF sixCol i).card 2 := by
  native_decide

theorem sum_card_meet_disj_nineCol : ∀ i : Fin 8,
    (meetPairs nineCol i).card + (disjPairs nineCol i).card = Nat.choose (classF nineCol i).card 2 := by
  native_decide

theorem sum_card_meet_disj_tenCol : ∀ i : Fin 9,
    (meetPairs tenCol i).card + (disjPairs tenCol i).card = Nat.choose (classF tenCol i).card 2 := by
  native_decide

theorem sum_card_meet_disj_elevenCol : ∀ i : Fin 10,
    (meetPairs elevenCol i).card + (disjPairs elevenCol i).card
      = Nat.choose (classF elevenCol i).card 2 := by
  native_decide

end
end JSP140
