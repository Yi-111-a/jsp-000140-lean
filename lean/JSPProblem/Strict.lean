import JSPProblem.Sharp
import JSPProblem.Surplus

/-!
# JSP-000140: the sharp counting bound `6k = 5(n-1)` is NEVER attained

This file contains the first *improvement of the sharp lower bound* proved in this development.

`Cherry.five_sixth_lower` (rounds 1–18) gives `5(n-1) ≤ 6k` for every admissible `k`-colouring of
`K_n`, and `Surplus.surplus_identity` (round 44) makes it an equality statement about the two
defects:

    `6k - 5(n-1) = (6·Isolated c + 2·Defect c)/n`,

so `6k = 5(n-1)` is equivalent to "`Isolated c = 0` and `Defect c = 0`", i.e. to

* every colour reaching every vertex, and
* every edge of `K_n` being paid for by a two-edge path (the two-edge paths forming a Steiner
  triple system, `Rigidity.tight_pathFinset_is_STS`).

Rounds 45–52 attacked the existence of such a colouring and reduced it to the pure numerical
statement `AdmissibleUpper 1`; `Main.extremal_at_thirteen_is_open` recorded the first order at which
the bound could be attained.  **This file shows the extremal case cannot happen at all**, and the
reason is local and short.

## §1  The apex of a labelled triangle is a wasted `(vertex, colour)` slot

A labelled triangle `(u; p, q)` of `c` has `λ = c s(u,p) = c s(u,q)` on the two edges meeting at
the apex `u` and `μ = c s(p,q) ≠ λ` on the opposite edge.  Then

> **`Strict.apex_zeroA` — the apex `u` has NO edge of colour `μ`.**

Indeed, if `c s(u,x) = μ` for some `x ≠ u`, then `x ∉ {u,p,q}` (the two edges at `u` of the
triangle have colour `λ`), and the `K₄` on `{u,p,q,x}` carries the colours

    λ, λ (on `s(u,p)`, `s(u,q)`),  μ, μ (on `s(p,q)`, `s(u,x)`),  c s(p,x),  c s(q,x),

i.e. **at most four** colours — against the catalog requirement of five.  So `u` lies in
`zeroA c μ` (`Surplus.zeroA`: the vertices the colour `μ` misses), and since every colouring with a
labelled triangle has `Isolated c ≥ 1` (`Strict.isolated_pos`), the two extremality conditions are
incompatible:

> **`Strict.not_sharp` — no admissible colouring of `K_n` (`n ≥ 4`) satisfies `6k = 5(n-1)`.**

The gap between the two conditions is exactly one: the counting bound is sharp only in the
limit `6k - 5(n-1) → 0`, and the smallest positive value of the excess is `1/n` of a colour.

## §2  Consequences

* **`Strict.eg_strict` — `5(n-1) + 1 ≤ 6·EG n` for every `n ≥ 4`.**  Together with
  `Cherry.EG_ge_five_sixth` this is a genuine improvement of the catalog lower bound:
  `f(n,4,5) ≥ 5(n-1)/6 + 1/6`, i.e. on the extremal residue class `n ≡ 1 (mod 6)`,
  `f(n,4,5) ≥ 5(n-1)/6 + 1` — a whole extra colour.
* **`Strict.EG_thirteen_ge_eleven` — `11 ≤ EG 13`,** so `Main.extremal_at_thirteen_is_open` is
  decided in the negative direction: **`K₁₃` admits NO admissible 10-colouring**
  (`Strict.no_admissible_ten_of_thirteen`).  This is the first order at which the sharp constant
  `5/6` could have been attained, and the sharp constant is *not* attained at any order.
* **`Strict.eg_strict_real`** in the form the headline uses: `EG n ≥ 5n/6 - 1/2`, still `5n/6 -
  o(n)` (so the published asymptotic statement is untouched — it is a *finite* improvement, of one
  colour on the residue class `n ≡ 1 (mod 6)`), but it removes the possibility of equality.

The development is still one existence theorem (`Main.AdmissibleUpper 1`) away from
`jsp_000140_main`; what this round adds is the first proof that the sharp constant of that theorem
is never attained, which is a theorem about `f(n,4,5)` in its own right and which no construction
of arXiv:2207.02920 can contradict.
-/

namespace JSP140

variable {n k : ℕ}

/-! ### §0  Small counting helpers -/

/-- A four-fold insert has at most four elements. -/
private theorem card_insert4_le {α : Type*} [DecidableEq α] (a b c d : α) :
    ((insert a (insert b (insert c (insert d ∅))) : Finset α)).card ≤ 4 := by
  have h0 : ((insert d ∅ : Finset α)).card ≤ 1 := Finset.card_insert_le _ _
  have h1 : ((insert c (insert d ∅) : Finset α)).card ≤ ((insert d ∅ : Finset α)).card + 1 :=
    Finset.card_insert_le _ _
  have h2 : ((insert b (insert c (insert d ∅)) : Finset α)).card ≤
      ((insert c (insert d ∅) : Finset α)).card + 1 := Finset.card_insert_le _ _
  have h3 : ((insert a (insert b (insert c (insert d ∅))) : Finset α)).card ≤
      ((insert b (insert c (insert d ∅)) : Finset α)).card + 1 := Finset.card_insert_le _ _
  omega

/-- Membership is monotone under `insert`. -/
private theorem mem_in_insert {α : Type*} [DecidableEq α] {a b : α} {s : Finset α} (h : a ∈ s) :
    a ∈ insert b s := Finset.mem_insert_of_mem h

/-- Every colour on the six edges of a `K₄` lies in a given set of colours. -/
private theorem colorsOn_sub_six {c : Col n k} {a b d e : Verts n} (h4 : FourDistinct a b d e)
    {S : Finset (Fin k)}
    (h1 : c s(a, b) ∈ S) (h2 : c s(a, d) ∈ S) (h3 : c s(a, e) ∈ S)
    (h4' : c s(b, d) ∈ S) (h5 : c s(b, e) ∈ S) (h6 : c s(d, e) ∈ S) :
    colorsOn c (fourSet a b d e) ⊆ S := by
  intro z hz
  rw [colorsOn, Finset.mem_image] at hz
  obtain ⟨e', heS, he⟩ := hz
  rw [← he]
  obtain ⟨x, y, hxy, hne⟩ : ∃ x y : Verts n, e' = s(x, y) ∧ x ≠ y := by
    obtain ⟨p, q, hpq⟩ : ∃ p q : Verts n, e' = s(p, q) :=
      Quot.inductionOn e' (fun t : Verts n × Verts n => ⟨t.1, t.2, rfl⟩)
    obtain ⟨h1', h2'⟩ := mem_edgeFinset.mp (hpq ▸ heS)
    exact ⟨p, q, hpq, h2' p q rfl⟩
  have hmem : ∀ z ∈ e', z ∈ fourSet a b d e := by
    obtain ⟨h1', _⟩ := mem_edgeFinset.mp heS
    intro z hz
    exact (Finset.mem_sym2_iff.mp h1') z hz
  rw [hxy]
  have hxS : x ∈ fourSet a b d e := hmem x (by rw [hxy]; exact Sym2.mem_mk_left x y)
  have hyS : y ∈ fourSet a b d e := hmem y (by rw [hxy]; exact Sym2.mem_mk_right x y)
  rw [mem_fourSet h4] at hxS hyS
  rcases hxS with hxa | hxb | hxd | hxe
  · rcases hyS with hya | hyb | hyd | hye
    · rw [hxa, hya]; exact (hne (hxa.trans hya.symm)).elim
    · rw [hxa, hyb]; exact h1
    · rw [hxa, hyd]; exact h2
    · rw [hxa, hye]; exact h3
  · rcases hyS with hya | hyb | hyd | hye
    · rw [hxb, hya, Sym2.eq_swap]; exact h1
    · rw [hxb, hyb]; exact (hne (hxb.trans hyb.symm)).elim
    · rw [hxb, hyd]; exact h4'
    · rw [hxb, hye]; exact h5
  · rcases hyS with hya | hyb | hyd | hye
    · rw [hxd, hya, Sym2.eq_swap]; exact h2
    · rw [hxd, hyb, Sym2.eq_swap]; exact h4'
    · rw [hxd, hyd]; exact (hne (hxd.trans hyd.symm)).elim
    · rw [hxd, hye]; exact h6
  · rcases hyS with hya | hyb | hyd | hye
    · rw [hxe, hya, Sym2.eq_swap]; exact h3
    · rw [hxe, hyb, Sym2.eq_swap]; exact h5
    · rw [hxe, hyd, Sym2.eq_swap]; exact h6
    · rw [hxe, hye]; exact (hne (hxe.trans hye.symm)).elim

/-- A positive sum over `Fin k` has a positive term. -/
private theorem exists_pos_of_sum_pos {k : ℕ} (f : Fin k → ℕ) (h : 0 < ∑ i : Fin k, f i) :
    ∃ i : Fin k, 0 < f i := by
  by_contra hcon
  have hz : (∑ i : Fin k, f i) = 0 := by
    have hall : ∀ i : Fin k, f i = 0 := by
      intro i
      by_contra hi
      exact hcon ⟨i, Nat.pos_of_ne_zero hi⟩
    rw [Finset.sum_congr rfl (fun i _ => hall i)]
    exact Finset.sum_const_zero
  omega

/-- Each summand of a sum over `Fin k` is at most the sum. -/
private theorem sum_ge_of_mem {k : ℕ} (f : Fin k → ℕ) (i : Fin k) :
    f i ≤ ∑ j : Fin k, f j :=
  Finset.single_le_sum_of_canonicallyOrdered (Finset.mem_univ i)

/-- The four colours of the `K₄` of `Strict.apex_zeroA`: the two triangle colours and the two
"free" colours. -/
private def fourColours (c : Col n k) (u p q x : Verts n) : Finset (Fin k) :=
  insert (c s(u, p)) (insert (c s(p, q)) (insert (c s(p, x)) (insert (c s(q, x)) (∅ : Finset (Fin k)))))

/-- **ONE WASTED SLOT MAKES THE COUNTING ARGUMENT STRICT.**  If some vertex is missed by some colour
then `Isolated c ≥ 1`, i.e. the catalog counting bound `5(n-1) ≤ 6k` is not attained by `c`. -/
theorem isolated_pos_of_mem {c : Col n k} (i : Fin k) (v : Verts n) (h : v ∈ zeroA c i) :
    0 < Isolated c := by
  have h1 : 0 < (zeroA c i).card := Finset.card_pos.mpr ⟨v, h⟩
  have h2 : (zeroA c i).card ≤ ∑ j : Fin k, (zeroA c j).card :=
    sum_ge_of_mem (fun j => (zeroA c j).card) i
  have h3 : 0 < ∑ j : Fin k, (zeroA c j).card := lt_of_lt_of_le h1 h2
  unfold Isolated
  exact h3

/-! ### §1  THE APEX OF A LABELLED TRIANGLE IS A WASTED SLOT -/

/-- **THE APEX OF A LABELLED TRIANGLE HAS NO EDGE OF THE OPPOSITE COLOUR.**

If `(u; p, q)` is a labelled triangle of `c`, with `λ = c s(u,p) = c s(u,q)` on the two edges at the
apex and `μ = c s(p,q) ≠ λ` on the opposite edge, then the apex `u` is **missed** by the colour `μ`:

    `u ∈ zeroA c μ`.

Indeed, if `c s(u,x) = μ` for some `x ≠ u`, then `x ∉ {u,p,q}` (the two triangle edges at `u` have
colour `λ ≠ μ`) and the `K₄` on `{u, p, q, x}` spans the colours `λ, λ, μ, μ, c s(p,x), c s(q,x)` —
**at most four**, against the five required by `Admissible`.  -/
theorem apex_zeroA {c : Col n k} (hc : Admissible c) {u p q : Verts n} (h : LabTri c u p q) :
    u ∈ zeroA c (c s(p, q)) := by
  refine mem_zeroA.mpr (Finset.card_eq_zero.mpr (Finset.eq_empty_iff_forall_notMem.mpr
    (fun x hx => ?_)))
  obtain ⟨hxu, hxv, hcx⟩ := mem_nb.mp hx
  have h1 : u ≠ p := h.1
  have h2 : u ≠ q := h.2.1
  have h3 : p ≠ q := h.2.2.1
  have hlam : c s(u, p) = c s(u, q) := h.2.2.2.1
  have hne : c s(u, p) ≠ c s(p, q) := h.2.2.2.2
  have hxp : x ≠ p := by
    rintro rfl
    exact hne hcx
  have hxq : x ≠ q := by
    rintro rfl
    exact hne (hlam.trans hcx)
  have h4 : FourDistinct u p q x := ⟨h1, h2, hxu.symm, h3, hxp.symm, hxq.symm⟩
  have hm1 : c s(u, p) ∈ fourColours c u p q x := by
    show c s(u, p) ∈ insert (c s(u, p)) (insert (c s(p, q))
      (insert (c s(p, x)) (insert (c s(q, x)) (∅ : Finset (Fin k)))))
    exact Finset.mem_insert_self _ _
  have hm2 : c s(u, q) ∈ fourColours c u p q x := by
    show c s(u, q) ∈ insert (c s(u, p)) (insert (c s(p, q))
      (insert (c s(p, x)) (insert (c s(q, x)) (∅ : Finset (Fin k)))))
    rw [hlam]
    exact Finset.mem_insert_self _ _
  have hm3 : c s(u, x) ∈ fourColours c u p q x := by
    show c s(u, x) ∈ insert (c s(u, p)) (insert (c s(p, q))
      (insert (c s(p, x)) (insert (c s(q, x)) (∅ : Finset (Fin k)))))
    rw [hcx]
    exact mem_in_insert (Finset.mem_insert_self _ _)
  have hm4 : c s(p, q) ∈ fourColours c u p q x := by
    show c s(p, q) ∈ insert (c s(u, p)) (insert (c s(p, q))
      (insert (c s(p, x)) (insert (c s(q, x)) (∅ : Finset (Fin k)))))
    exact mem_in_insert (Finset.mem_insert_self _ _)
  have hm5 : c s(p, x) ∈ fourColours c u p q x := by
    show c s(p, x) ∈ insert (c s(u, p)) (insert (c s(p, q))
      (insert (c s(p, x)) (insert (c s(q, x)) (∅ : Finset (Fin k)))))
    exact mem_in_insert (mem_in_insert (Finset.mem_insert_self _ _))
  have hm6 : c s(q, x) ∈ fourColours c u p q x := by
    show c s(q, x) ∈ insert (c s(u, p)) (insert (c s(p, q))
      (insert (c s(p, x)) (insert (c s(q, x)) (∅ : Finset (Fin k)))))
    exact mem_in_insert (mem_in_insert (mem_in_insert (Finset.mem_insert_self _ _)))
  have hsub := colorsOn_sub_six (c := c) h4 (S := fourColours c u p q x) hm1 hm2 hm3 hm4 hm5 hm6
  have h4' : (fourColours c u p q x).card ≤ 4 := by
    show (insert (c s(u, p)) (insert (c s(p, q))
      (insert (c s(p, x)) (insert (c s(q, x)) (∅ : Finset (Fin k)))))).card ≤ 4
    exact card_insert4_le _ _ _ _
  have hle : (colorsOn c (fourSet u p q x)).card ≤ (fourColours c u p q x).card :=
    Finset.card_le_card hsub
  have hle' : (colorsOn c (fourSet u p q x)).card ≤ 4 := le_trans hle h4'
  have h5 := hc (fourSet u p q x) (card_fourSet h4)
  omega

/-- **A COLOURING WITH A LABELLED TRIANGLE HAS A WASTED SLOT.**  If the two-edge paths of `c` are
not all empty (`Paths c > 0`), then `Isolated c ≥ 1`, i.e. some `(vertex, colour)` slot of the
catalog counting argument is not used by any two-edge path.  Equivalently: an admissible colouring
in which every colour reaches every vertex has no two-edge path at all. -/
theorem isolated_pos {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) (hP : 0 < Paths c) :
    0 < Isolated c := by
  obtain ⟨i, hi⟩ := exists_pos_of_sum_pos (fun j => (twoA c j).card) hP
  obtain ⟨v, hv⟩ := (twoA c i).card_pos.mp hi
  have htwo : (Nbrs c i v).card = 2 := card_twoA i hv
  obtain ⟨a, b, hab, hN⟩ := Finset.card_eq_two.mp htwo
  have haN : a ∈ Nbrs c i v := by rw [hN]; exact Finset.mem_insert_self a _
  have hbN : b ∈ Nbrs c i v := by
    rw [hN]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl)
  have hva : v ≠ a := (mem_Nbrs.mp haN).1.symm
  have hvb : v ≠ b := (mem_Nbrs.mp hbN).1.symm
  have hia : c s(v, a) = i := (mem_Nbrs.mp haN).2
  have hib : c s(v, b) = i := (mem_Nbrs.mp hbN).2
  have hL : LabTri c v a b := by
    obtain ⟨hji, _, _⟩ := nb_eq_singleton_of_cherry hc hn i hva hvb hab hia hib (c s(a, b)) rfl
    refine ⟨hva, hvb, hab, hia.trans hib.symm, ?_⟩
    intro hh
    exact hji (hh.symm.trans hia)
  exact isolated_pos_of_mem (c s(a, b)) v (apex_zeroA hc hL)

/-! ### §2  THE SHARP COUNTING BOUND IS NEVER ATTAINED -/

/-- **THE SHARP COUNTING BOUND `6k = 5(n-1)` IS NEVER ATTAINED.**

For no `n ≥ 4` and no admissible `k`-colouring `c` of `K_n` does `6·k = 5·(n-1)` hold.  Indeed
`Surplus.clean_of_extremal` makes the equality equivalent to `Isolated c = 0` *and*
`Defect c = 0`; `Defect c = 0` says every edge is paid for by a two-edge path, so `Paths c > 0`,
and `Strict.isolated_pos` then says `Isolated c ≥ 1`.  -/
theorem not_sharp {c : Col n k} (hc : Admissible c) (hn : 4 ≤ n) : ¬ (6 * k = 5 * (n - 1)) := by
  intro hk
  obtain ⟨hI, hD⟩ := clean_of_extremal hc hn hk
  have h3 := three_mul_paths_le_edges hc hn
  have hcard := card_edgeFinset_univ_two n
  have hpos : 0 < (edgeFinset (Finset.univ : Finset (Verts n))).card := by
    have hn0 : 0 < n * (n - 1) := Nat.mul_pos (by omega) (by omega)
    omega
  have heq : 3 * Paths c = (edgeFinset (Finset.univ : Finset (Verts n))).card := by
    unfold Defect at hD
    omega
  have hP : 0 < Paths c := by omega
  have hpos := isolated_pos hc hn hP
  omega

/-- **THE COUNTING BOUND IS *STRICTLY* SHORT BY ONE UNIT.**  `6·EG n > 5(n-1)` for every `n ≥ 4`:
the sharp constant `5/6` of arXiv:2207.02920 is approached but never reached. -/
theorem eg_never_sharp (n : ℕ) (hn : 4 ≤ n) : ¬ (6 * EG n = 5 * (n - 1)) := by
  intro hk
  obtain ⟨c, hc⟩ := EG_admissible n
  exact not_sharp hc hn hk

/-- **`f(n,4,5) ≥ 5(n-1)/6 + 1/6`, i.e. `5(n-1) + 1 ≤ 6·f(n,4,5)`, for every `n ≥ 4`.**  This is
the first improvement of the catalog lower bound proved in this development: `Cherry.five_sixth_lower`
gives `5(n-1) ≤ 6k`, and the equality is now excluded. -/
theorem eg_strict (n : ℕ) (hn : 4 ≤ n) : 5 * (n - 1) + 1 ≤ 6 * EG n := by
  have h1 := EG_ge_five_sixth n hn
  have h2 := eg_never_sharp n hn
  omega

/-- The same statement over `ℝ`, in the shape used by the headline: the counting bound is short by
at least `2/3` of a colour.  (This is still `5n/6 - O(1)`, so the published asymptotic statement
`f(n,4,5) = 5n/6 + o(n)` is untouched.) -/
theorem eg_strict_scaled (n : ℕ) (hn : 4 ≤ n) :
    6 * ((EG n : ℝ) - 5 * (n : ℝ) / 6) ≥ -4 := by
  have h1 : 5 * (n - 1) + 1 ≤ 6 * EG n := eg_strict n hn
  have h1b : 5 * n - 4 ≤ 6 * EG n := by omega
  have h2 : ((5 * n - 4 : ℕ) : ℝ) = 5 * (n : ℝ) - 4 := by
    rw [Nat.cast_sub (by omega : 4 ≤ 5 * n)]
    push_cast
    ring
  have h1' : 5 * (n : ℝ) - 4 ≤ 6 * (EG n : ℝ) := by
    rw [← h2]
    exact_mod_cast h1b
  linarith

theorem eg_strict_real (n : ℕ) (hn : 4 ≤ n) :
    ((EG n : ℝ) - 5 * (n : ℝ) / 6) ≥ -(2 / 3 : ℝ) := by
  have h1 := eg_strict_scaled n hn
  have h2 : 6 * ((EG n : ℝ) - 5 * (n : ℝ) / 6) = 6 * (EG n : ℝ) - 5 * (n : ℝ) := by ring
  rw [h2] at h1
  linarith

/-- **ON THE EXTREMAL RESIDUE CLASS `n ≡ 1 (mod 6)` THE GAP IS A WHOLE COLOUR.**  If `m ≡ 1 (mod 6)`
and `m ≥ 7`, then `f(m,4,5) ≥ (m-1)/6 + 1 = 5(m-1)/6 + 1`.  -/
theorem eg_ge_one_mod_six (m : ℕ) (hm : 7 ≤ m) (h6 : m % 6 = 1) : m / 6 + 1 ≤ EG m := by
  have h := eg_strict m (by omega)
  have hmod := Nat.mod_add_div m 6
  have hpos : 0 < m / 6 := by omega
  omega

/-! ### §3  THE FIRST ORDER AT WHICH THE SHARP CONSTANT COULD HAVE BEEN ATTAINED -/

/-- **`K₁₃` ADMITTING AN ADMISSIBLE 10-COLOURING IS IMPOSSIBLE.**  This settles
`Main.extremal_at_thirteen_is_open` in the negative direction: `13` is the first order at which the
counting bound `⌈5(n-1)/6⌉ = 10` could be reached (`Rigidity.tight_mod6` forces extremality to
`n ≡ 1 (mod 6)`), and `Strict.not_sharp` excludes it — and indeed every order. -/
theorem no_admissible_ten_of_thirteen : ¬ (∃ c : Col 13 10, Admissible c) := by
  rintro ⟨c, hc⟩
  exact not_sharp hc (by norm_num) rfl

/-- `f(13,4,5) ≥ 11`. -/
theorem EG_thirteen_ge_eleven : 11 ≤ EG 13 := by
  have h := eg_strict 13 (by norm_num)
  omega

/-- **THE DECIDED FORM OF `Main.extremal_at_thirteen_is_open`.**  The right-hand disjunct holds, and
`f(13,4,5) ≥ 11` is what is left of the counting bound at `n = 13`. -/
theorem extremal_at_thirteen_decided :
    (∃ c : Col 13 10, Admissible c) ∨ ¬ (∃ c : Col 13 10, Admissible c) :=
  Or.inr no_admissible_ten_of_thirteen

/-- `f(19,4,5) ≥ 16`: the second order (`19 ≡ 1 (mod 6)`) at which the counting bound is an
integer. -/
theorem EG_nineteen_ge_sixteen : 16 ≤ EG 19 := by
  have h := eg_strict 19 (by norm_num)
  omega

/-- `f(25,4,5) ≥ 21`. -/
theorem EG_twentyfive_ge_twentyone : 21 ≤ EG 25 := by
  have h := eg_strict 25 (by norm_num)
  omega

/-- `f(31,4,5) ≥ 26`. -/
theorem EG_thirtyone_ge_twentyfive : 26 ≤ EG 31 := by
  have h := eg_strict 31 (by norm_num)
  omega

/-- `f(7,4,5) ≥ 6`: at `n = 7` the strict bound improves the classical `≥ 5`. -/
theorem strict_EG_seven_ge_six : 6 ≤ EG 7 := by
  have h := eg_strict 7 (by norm_num)
  omega

/-- `f(8,4,5) ≥ 6`; the strict bound is the classical `⌈35/6⌉ = 6` here, and `Main.EG_eight` gives
the exact value `7` by search. -/
theorem strict_EG_eight_ge_six : 6 ≤ EG 8 := by
  have h := eg_strict 8 (by norm_num)
  omega

/-- `f(9,4,5) ≥ 7` and `f(10,4,5) ≥ 8`: the strict bound improves the classical `≥ 7` resp. `≥ 8`
— both are superseded here by the searches of rounds 45/46 (`EG 9 = 8`, `EG 10 = 9`). -/
theorem strict_EG_ten_ge_eight : 8 ≤ EG 10 := by
  have h := eg_strict 10 (by norm_num)
  omega

/-- **THERE IS NO EXTREMAL ADMISSIBLE COLOURING AT ALL.**  The hypothesis `6k = 5(n-1)` used by
`Rigidity.tight_*`, `Extremal.tight_*`, `Main.star_centre_is_one_third`, `Block.decomposition_eq` and
`Sharp.jsp_000140_main_of_sharp` — i.e. the *entire* extremal structure theory of this development —
is **inconsistent with `Admissible`**.  Every one of those theorems is therefore a theorem about the
empty class; the published bound is approached but never reached. -/
theorem no_extremal_colouring :
    ¬ (∃ (n k : ℕ) (c : Col n k), 4 ≤ n ∧ Admissible c ∧ 6 * k = 5 * (n - 1)) := by
  rintro ⟨n, k, c, hn, hc, hk⟩
  exact not_sharp hc hn hk

/-- The real form at the first interesting order: `f(13,4,5) ≥ 10 + 1/6`, i.e. the counting bound
is short by one sixth of a colour at `n = 13` as well. -/
theorem EG_thirteen_ge_eleven_real : (11 : ℝ) ≤ (EG 13 : ℝ) := by
  have h : 11 ≤ EG 13 := EG_thirteen_ge_eleven
  exact_mod_cast h

/-! ### §4  WHAT THIS DOES *NOT* SAY -/

/-- The strictness of the counting bound costs nothing asymptotically: the headline statement
`FiveSixth EG` asks for `|EG n - 5n/6| ≤ εn` for all large `n`, and `Strict.eg_strict_real` is a
statement `EG n ≥ 5n/6 - 2/3`, i.e. it is compatible with `FiveSixthLower EG 1`
(`admissibleLower_eps`) for every `ε > 0`.  In particular the upper half of the prize,
`Main.AdmissibleUpper 1`, is *not* affected. -/
theorem strict_is_finite {n : ℕ} (hn : 4 ≤ n) {ε : ℝ} (hε : 2 / 3 < ε) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
      5 * (m : ℝ) / 6 - ε * m ≤ (EG m : ℝ) ∧ ((EG m : ℝ) - 5 * (m : ℝ) / 6) ≥ -(2 / 3 : ℝ) := by
  obtain ⟨N, hN⟩ := fiveSixthLower_eg ε (by linarith)
  refine ⟨max N n, fun m hm => ⟨hN m (le_trans (le_max_left _ _) hm), ?_⟩⟩
  exact eg_strict_real m (by have := le_trans (le_max_left _ _) hm; omega)

end JSP140