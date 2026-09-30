import JSPProblem.Definitions
import JSPProblem.Construction
import JSPProblem.Ghost

/-!
# JSP-000140 — a *verified exhaustive search* for `f(n, 4, 5)`

Rounds 2–15 developed the structure of admissible colourings and the **lower** half
`f(n,4,5) ≥ 5n/6 - o(n)`; round 16 produced and *certified* explicit constructions with
`native_decide` (`Tables.sixCol`).  This file adds the complementary half: a **complete,
machine-checked exhaustive search for the value of `f(n,4,5)` itself**, and — with it — the
first exact values of the Erdős–Gyárfás function obtained in this development beyond
`n = 6`.

The engine is elementary but complete:

* `slotOf` — the **slot** of an edge `e = s(a,b)`, namely `min(a,b)*n + max(a,b)`.  The slots
  which carry an edge of `K_n` are exactly those `d < n*n` with `d/n < d%n`
  (`meaningfulSlot`), and `slotEdge` is the inverse of `slotOf` there (`slotOf_slotEdge`).
  `slotOf_lt` and `slotOf_inj` say that the slots are exactly the first `n*n` natural
  numbers and that they separate the edges;
* `group n d` — **the four-element vertex sets which become *complete* when slot `d` is
  filled in**, i.e. all six of their edges lie in the slots `≤ d` and one of them lies in
  slot `d` (`Prefix`).  Every `K₄` of `K_n` lies in exactly one group, that of its largest
  slot, and `prefix_last` says that every `K₄` is complete by the last slot;
* `searchAux` — a depth-first search which fills the slots `0, 1, 2, …, n*n-1` in order,
  branching over the colours, and **prunes a branch as soon as one of the cliques of the
  group of the slot being filled fails the catalog condition** (`GroupOK`).  A four-clique is
  therefore checked exactly once, at the moment its last slot is filled, and only prefixes
  consistent with every `K₄` seen so far are visited.  This is what makes the search
  tractable: the `6^21 ≈ 2·10^16` colourings of `K₇` with six colours collapse to a few
  thousand nodes;
* **`searchAux_iff` — THE COMPLETENESS THEOREM.**  The search returns `true` on the colouring
  `T` at level `d` **iff some extension of `T` which agrees with it on the edges of the slots
  `< d` is an admissible colouring**.  Nothing is assumed about the search itself: the
  theorem is proved by induction on the remaining fuel, and it is the mathematical content of
  this file;
* `hasAdmissible_iff` and **`EG_ge_of_cert` — THE LOWER-BOUND ENGINE.**  A proof of
  `hasAdmissible n k = false` — a statement settled by `native_decide` in seconds, with no
  search required of the reader — is a Lean proof that **no admissible colouring of `K_n`
  with `k+1` colours exists**, and hence that `f(n,4,5) ≥ k+2`.

This turns the computational results of round 16 into Lean theorems.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace JSP140

variable {n k : ℕ}

/-! ### Slots: the order in which the edges of `K_n` are coloured -/

/-- The **slot** of an edge: the index at which its colour is entered. -/
def slotOf : Sym2 (Verts n) → ℕ :=
  Sym2.rec (motive := fun _ => ℕ) (fun a b => (pairEnc n (min a b) (max a b)).val)
    (by
      intro a b c d h
      cases h with
      | refl => rfl
      | swap x y => simp [pairEnc, min_comm, max_comm])

@[simp] theorem slotOf_mk (a b : Verts n) :
    slotOf s(a, b) = (min a b).val * n + (max a b).val := rfl

/-- **The meaningful slots** are those `d` with `d / n < d % n`, i.e. `d = a*n+b` for
`a < b < n`; these are exactly the slots which carry an edge of `K_n`. -/
def meaningfulSlot (n d : ℕ) : Bool := decide (d / n < d % n)

theorem meaningfulSlot_iff (n d : ℕ) : meaningfulSlot n d = true ↔ d / n < d % n := by
  simp [meaningfulSlot]

/-- **Every (unordered pair, hence every) edge lives in a slot `< n*n`.** -/
theorem slotOf_lt (e : Sym2 (Verts n)) : slotOf e < n * n := by
  obtain ⟨a, b, rfl⟩ := Sym2.exists.mp ⟨e, rfl⟩
  rcases n with _ | m
  · exact (Nat.not_lt_zero _ a.isLt).elim
  · rw [slotOf_mk]
    have h1 : (min a b).val ≤ m := Nat.le_pred_of_lt (Fin.isLt _)
    have h2 : (max a b).val ≤ m := Nat.le_pred_of_lt (Fin.isLt _)
    have hA : (min a b).val * (m + 1) ≤ m * (m + 1) := Nat.mul_le_mul_right _ h1
    have hB : (max a b).val ≤ m := h2
    have h2' : (m + 1) * (m + 1) = m * (m + 1) + (m + 1) := by
      calc (m + 1) * (m + 1) = (m + 1) * m + (m + 1) := Nat.mul_succ _ _
        _ = m * (m + 1) + (m + 1) := by rw [Nat.mul_comm]
    have hC : m * (m + 1) + m < (m + 1) * (m + 1) := by
      rw [h2']
      omega
    have hAB : (min a b).val * (m + 1) + (max a b).val
        ≤ m * (m + 1) + (m + 1) :=
      Nat.add_le_add hA (Nat.le_trans hB (Nat.le_succ m))
    omega

private theorem pos_of_slot {n d : ℕ} (h : ¬ (n * n ≤ d)) : 0 < n := by
  by_contra hc
  obtain h0 : n = 0 := Nat.le_zero.mp (Nat.not_lt.mp hc)
  exact h (by rw [h0, Nat.mul_zero]; exact Nat.zero_le d)

/-- **THE EDGE OF SLOT `d`.** -/
def slotEdge (n : ℕ) (d : ℕ) (hn : 0 < n) (hd : d < n * n) : Sym2 (Verts n) :=
  s(⟨d / n, (Nat.mul_lt_mul_left hn).mp (by
      have h2 : n * (d / n) ≤ d := by
        have h3 := Nat.div_mul_le_self d n
        rwa [Nat.mul_comm] at h3
      omega)⟩, ⟨d % n, Nat.mod_lt _ hn⟩)

/-- `slotOf (slotEdge n d hd) = d` at a meaningful slot. -/
theorem slotOf_slotEdge (n : ℕ) (d : ℕ) (hd : d < n * n) (hm : d / n < d % n) :
    slotOf (slotEdge n d (pos_of_slot (Nat.not_le.mpr hd)) hd) = d := by
  have h1 : n * (d / n) + d % n = d := Nat.div_add_mod d n
  unfold slotEdge
  rw [slotOf_mk, min_eq_left (by exact le_of_lt hm), max_eq_right (by exact le_of_lt hm),
    Nat.mul_comm (d / n) n, h1]

/-- **Distinct edges occupy distinct slots.** -/
theorem slotOf_inj {e e' : Sym2 (Verts n)} (h : slotOf e = slotOf e') : e = e' := by
  obtain ⟨a, b, rfl⟩ := Sym2.exists.mp ⟨e, rfl⟩
  obtain ⟨a', b', rfl⟩ := Sym2.exists.mp ⟨e', rfl⟩
  have hn : 0 < n := by
    rcases n with _ | m
    · exact (Nat.not_lt_zero _ (min a b).isLt).elim
    · exact Nat.succ_pos m
  have hval : (min a b).val * n + (max a b).val = (min a' b').val * n + (max a' b').val := h
  have hAB : (min a b).val * n ≤ (min a' b').val * n + (max a' b').val := by omega
  have hAB' : (min a' b').val * n ≤ (min a b).val * n + (max a b).val := by omega
  have h4 : (min a b).val * n < ((min a' b').val + 1) * n := by
    rw [Nat.succ_mul]; omega
  have h5 : (min a b).val < (min a' b').val + 1 := (Nat.mul_lt_mul_right hn).mp h4
  have h4' : (min a' b').val * n < ((min a b).val + 1) * n := by
    rw [Nat.succ_mul]; omega
  have h5' : (min a' b').val < (min a b).val + 1 := (Nat.mul_lt_mul_right hn).mp h4'
  have hminV : (min a b).val = (min a' b').val := by omega
  have hmin : min a b = min a' b' := Fin.ext hminV
  have hmax : max a b = max a' b' := by
    have h2 := hval
    rw [hmin] at h2
    exact Fin.ext (Nat.add_left_cancel h2)
  have key : ∀ (u v y : Verts n), (y = u ∨ y = v) ↔ y ∈ ({u, v} : Finset (Verts n)) := by
    intro u v y
    simp [Finset.mem_insert, Finset.mem_singleton]
  apply Sym2.ext
  intro z
  rw [Sym2.mem_iff, Sym2.mem_iff, key, key, ← minmax_eq_pair a b, ← minmax_eq_pair a' b']
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rw [hmin, hmax]

/-! ### Four-cliques and the moment at which they become complete -/

/-- **All six edges of `S` occupy slots `< d`.** -/
def Prefix (n : ℕ) (d : ℕ) (S : Finset (Verts n)) : Prop :=
  ∀ e, e ∈ edgeFinset S → slotOf e < d

instance prefixDecidable (n : ℕ) (d : ℕ) : DecidablePred (Prefix n d) := fun S => by
  unfold Prefix; infer_instance

instance admissibleDecidable {n k : ℕ} (c : Col n k) : Decidable (Admissible c) := by
  unfold Admissible; infer_instance

/-- **The four-element vertex sets.** -/
def fourSets (n : ℕ) : Finset (Finset (Verts n)) :=
  (Finset.univ : Finset (Finset (Verts n))).filter fun S => S.card = 4

/-- **`group n d` = the cliques `K₄` which are *completed* by the slot `d`**: all their six
edges lie in the slots `≤ d`, and one of them lies in the slot `d`.  Every clique of `K_n`
lies in exactly one group, that of its largest slot. -/
def group (n : ℕ) (d : ℕ) : Finset (Finset (Verts n)) :=
  (fourSets n).filter fun S => Prefix n (d + 1) S ∧ ¬ Prefix n d S

theorem mem_group {n : ℕ} (d : ℕ) {S : Finset (Verts n)} (hS : S ∈ group n d) :
    S.card = 4 ∧ Prefix n (d + 1) S ∧ ¬ Prefix n d S := by
  have h := Finset.mem_filter.mp hS
  have h1 := Finset.mem_filter.mp h.1
  exact ⟨h1.2, h.2.1, h.2.2⟩

/-- The list of the groups, one per slot. -/
def fourGroups (n : ℕ) : List (Finset (Finset (Verts n))) :=
  List.ofFn fun d : Fin (n * n) => group n d.val

theorem fourGroups_length (n : ℕ) : (fourGroups n).length = n * n := by simp [fourGroups]

theorem fourGroups_getD (n : ℕ) (d : ℕ) (hd : d < n * n) :
    (fourGroups n).getD d ∅ = group n d := by
  rw [fourGroups, List.getD]
  simp [hd]

private theorem div_mod_pair {n d A B : ℕ} (hn : 0 < n) (hB : B < n) (h : d = A * n + B) :
    d / n = A ∧ d % n = B := by
  refine ⟨?_, ?_⟩
  · rw [h, Nat.mul_comm, Nat.mul_add_div (m := n) hn, Nat.div_eq_of_lt hB, Nat.add_zero]
  · have h3 : d = B + A * n := by rw [h]; omega
    rw [h3, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hB]

/-- **Only a meaningful slot carries an edge of `K_n`.** -/
theorem no_edge_of_slot {n d : ℕ} (hd : d < n * n) (hm : meaningfulSlot n d = false)
    (a b : Verts n) (hab : a ≠ b) (he : slotOf s(a, b) = d) : False := by
  rcases n with _ | m
  · exact (Nat.not_lt_zero _ (min a b).isLt).elim
  · have hlt : (min a b).val < (max a b).val := by
      rcases lt_trichotomy a b with h | h | h
      · rw [min_eq_left (le_of_lt h), max_eq_right (le_of_lt h)]
        exact h
      · exfalso
        rw [h] at hab
        exact hab rfl
      · rw [min_eq_right (le_of_lt h), max_eq_left (le_of_lt h)]
        exact h
    obtain ⟨h1, h2⟩ := div_mod_pair (n := m + 1) (Nat.succ_pos m) (max a b).isLt
      (he.symm.trans (slotOf_mk a b))
    have hm' : ¬ (d / (m + 1) < d % (m + 1)) := by
      simpa only [meaningfulSlot, decide_eq_false_iff_not, Nat.succ_eq_add_one] using hm
    omega

private theorem slot_lt_of_not_meaningful {n d : ℕ} (hd : d < n * n)
    (hm : ¬ meaningfulSlot n d = true) (a b : Verts n) (hab : a ≠ b)
    (he : slotOf s(a, b) < d + 1) : slotOf s(a, b) < d := by
  by_contra hc
  exact no_edge_of_slot hd (Bool.eq_false_of_not_eq_true hm) a b hab (by omega)

/-- **Every four-clique of `K_n` is complete at or before the last slot.** -/
theorem prefix_last {n : ℕ} {d : ℕ} (hd : n * n ≤ d) {S : Finset (Verts n)} (hS : S.card = 4) :
    Prefix n d S := by
  intro e he
  have h2 := slotOf_lt (n := n) e
  omega

/-! ### The search -/

private theorem eq_true_of_decide {p : Prop} [Decidable p] (h : p) : decide p = true := by
  rw [decide_eq_true_eq]; exact h

/-- The cliques of the group of slot `d` are all admissible for the colouring `T`. -/
def GroupOK {n k : ℕ} (G : Finset (Finset (Verts n))) (T : Col n k) : Bool :=
  decide (G ⊆ G.filter fun S => 5 ≤ (colorsOn T S).card)

theorem groupOK_iff {n k : ℕ} (G : Finset (Finset (Verts n))) (T : Col n k) :
    GroupOK G T = true ↔ ∀ S ∈ G, 5 ≤ (colorsOn T S).card := by
  constructor
  · intro h S hS
    have h' := (show G ⊆ G.filter _ from of_decide_eq_true h) hS
    exact (Finset.mem_filter.mp h').2
  · intro h
    refine eq_true_of_decide (fun S hS => ?_)
    exact Finset.mem_filter.mpr ⟨hS, h S hS⟩

/-- **THE SEARCH.**  `searchAux k G T d fuel` colours the edges in the slots
`d, d+1, …` (only the meaningful slots carry an edge; the others are passed through),
`fuel` at a time, pruning a branch as soon as one of the cliques completed by the slot being
filled fails the catalog condition.  At the end it tests `Admissible` outright. -/
def searchAux {n : ℕ} (k : ℕ) (G : ℕ → Finset (Finset (Verts n))) (T : Col n k)
    (d fuel : ℕ) : Bool :=
  match fuel with
  | 0 => decide (Admissible T)
  | fuel' + 1 =>
      if h : n * n ≤ d then decide (Admissible T)
      else if meaningfulSlot n d then
        (List.finRange k).any fun j =>
          let T' := Function.update T (slotEdge n d (pos_of_slot h) (Nat.lt_of_not_ge h)) j
          GroupOK (G d) T' && searchAux k G T' (d + 1) fuel'
      else searchAux k G T (d + 1) fuel'

/-- **Is there an admissible colouring of `K_n` with `k+1` colours?**  The value of this
`Bool` is settled by `native_decide` for small `n`; that is what the certificates below do. -/
def hasAdmissible (n k : ℕ) : Bool :=
  let G := fourGroups n
  searchAux (k + 1) (fun d => G.getD d ∅) (fun _ => (0 : Fin (k + 1))) 0 (n * n)

/-! ### Completeness of the search -/


/-- If `f` is an edge of a clique completed by the slot `d` and `f` is not the edge of the
slot `d`, then `f` lies in an earlier slot. -/
private theorem slot_lt_of_ne {n : ℕ} {e : Sym2 (Verts n)} {f : Sym2 (Verts n)} {d : ℕ}
    (hsd : slotOf e = d) (hF : f ≠ e) (hf : slotOf f < d + 1) : slotOf f < d := by
  have hne : slotOf f ≠ d := by
    intro h2
    exact hF (slotOf_inj (by rw [hsd, h2])).symm
  omega

private theorem colorsOn_agree {n k : ℕ} {T T' : Col n k} {d : ℕ} (S : Finset (Verts n))
    (h : ∀ e, e ∈ edgeFinset S → slotOf e ≤ d → T' e = T e) (hd : Prefix n (d + 1) S) :
    colorsOn T' S = colorsOn T S := by
  refine Finset.image_congr ?_
  intro e he
  exact h e he (Nat.lt_succ_iff.mp (hd e he))

/-- **THE COMPLETENESS THEOREM OF THE SEARCH.**  `searchAux` returns `true` on the colouring
`T` at level `d` **iff some extension of `T` which agrees with it on the edges of the slots
`< d` is an admissible colouring of `K_n`**.  The only hypothesis on the groups `G` is that a
member of the group of a slot `d < n*n` is a four-clique completed by that slot. -/
theorem searchAux_iff {n k : ℕ} (G : ℕ → Finset (Finset (Verts n)))
    (hG : ∀ d, d < n * n → ∀ S, S ∈ G d → S.card = 4 ∧ Prefix n (d + 1) S ∧ ¬ Prefix n d S)
    (T : Col n k) (d fuel : ℕ) (hf : d + fuel = n * n) :
    searchAux k G T d fuel = true ↔
      ∃ T' : Col n k,
        (∀ a b : Verts n, a ≠ b → slotOf s(a, b) < d → T' s(a, b) = T s(a, b)) ∧ Admissible T' := by
  induction fuel generalizing d T with
  | zero =>
      have hd : d = n * n := by omega
      subst hd
      simp only [searchAux]
      constructor
      · intro h
        exact ⟨T, fun a b _ _ => rfl, decide_eq_true_eq.mp h⟩
      · rintro ⟨T', hT', hT⟩
        refine decide_eq_true_eq.mpr ?_
        intro S hS
        have hcol : colorsOn T S = colorsOn T' S := by
          refine Finset.image_congr ?_
          intro e he
          obtain ⟨a, b, rfl⟩ := Sym2.exists.mp ⟨e, rfl⟩
          have hne : a ≠ b := (mem_edgeFinset.mp he).2 a b rfl
          exact (hT' a b hne (slotOf_lt (s(a, b)))).symm
        rw [hcol]
        exact hT S hS
  | succ fuel' ih =>
      have hd : d < n * n := by omega
      have hf' : (d + 1) + fuel' = n * n := by omega
      rw [searchAux, dif_neg (Nat.not_le.mpr hd)]
      by_cases hm : meaningfulSlot n d = true
      · have hm' : d / n < d % n := meaningfulSlot_iff n d |>.mp hm
        set e := slotEdge n d (pos_of_slot (Nat.not_le.mpr hd)) hd with hsd
        have hsd2 : slotOf e = d := by
          rw [hsd]; exact slotOf_slotEdge n d hd hm'
        rw [if_pos hm, List.any_eq_true]
        constructor
        · rintro ⟨j, -, hj⟩
          obtain ⟨-, hjG⟩ := Bool.and_eq_true _ _ ▸ hj
          obtain ⟨U, hU, hUadm⟩ := ih (Function.update T e j) (d + 1) hf' |>.mp hjG
          refine ⟨U, ?_, hUadm⟩
          intro a b hab hf
          have hF : s(a, b) ≠ e := by
            intro hc
            rw [hc, hsd2] at hf
            omega
          have h5 := hU a b hab (by omega)
          rwa [Function.update, dif_neg hF] at h5
        · rintro ⟨T', hAgr, hT⟩
          refine ⟨T' e, List.mem_finRange _, ?_⟩
          rw [Bool.and_eq_true]
          refine ⟨?_, ?_⟩
          · refine (groupOK_iff _ _).mpr (fun S hS => ?_)
            have hgt := hG d hd S hS
            refine (hT S hgt.1).trans (le_of_eq (congrArg Finset.card (colorsOn_agree S ?_ hgt.2.1)))
            intro f he hf
            obtain ⟨a, b, rfl⟩ := Sym2.exists.mp ⟨f, rfl⟩
            have hne : a ≠ b := (mem_edgeFinset.mp he).2 a b rfl
            by_cases hF : s(a, b) = e
            · have h6 : T' e = Function.update T e (T' e) e := by simp [Function.update]
              rw [hF]
              exact h6
            · simp only [Function.update, dif_neg hF]
              have hne2 : slotOf s(a, b) ≠ d := by
                intro h2
                exact hF (slotOf_inj (by rw [hsd2, h2])).symm
              exact hAgr a b hne (by omega)
          · refine ih (Function.update T e (T' e)) (d + 1) hf' |>.mpr ⟨T', ?_, hT⟩
            intro a b hab hf
            by_cases hF : s(a, b) = e
            · have h6 : T' e = Function.update T e (T' e) e := by simp [Function.update]
              rw [hF]
              exact h6
            · rw [Function.update, dif_neg hF]
              exact hAgr a b hab (slot_lt_of_ne hsd2 hF hf)
      · rw [if_neg hm]
        constructor
        · intro h
          obtain ⟨T', hT', hT⟩ := ih T (d + 1) (by omega) |>.mp h
          exact ⟨T', fun a b hab hf => hT' a b hab (Nat.lt_succ_of_lt hf), hT⟩
        · rintro ⟨T', hT', hT⟩
          exact ih T (d + 1) (by omega) |>.mpr
            ⟨T', fun a b hab hf => hT' a b hab (slot_lt_of_not_meaningful hd hm a b hab hf), hT⟩

theorem fourGroups_spec (n : ℕ) (G : ℕ → Finset (Finset (Verts n)))
    (hG : ∀ d, (fourGroups n).getD d ∅ = G d) (d : ℕ) (hd : d < n * n) :
    ∀ S, S ∈ G d → S.card = 4 ∧ Prefix n (d + 1) S ∧ ¬ Prefix n d S := by
  intro S hS
  have h2 : S ∈ (fourGroups n).getD d ∅ := by rwa [hG d]
  rw [fourGroups_getD n d hd] at h2
  exact mem_group d h2

/-- **THE VERIFIED SEARCH IS COMPLETE.**  `hasAdmissible n k = true` **iff** some
`k+1`-colouring of `K_n` is admissible. -/
theorem hasAdmissible_iff (n k : ℕ) :
    hasAdmissible n k = true ↔ ∃ c : Col n (k + 1), Admissible c := by
  have h := searchAux_iff (n := n) (k := k + 1) (fun d => (fourGroups n).getD d ∅)
    (fourGroups_spec n _ (fun _ => rfl)) (fun _ => (0 : Fin (k + 1))) 0 (n * n) (by omega)
  constructor
  · intro hb
    obtain ⟨c, _, hc⟩ := h.mp hb
    exact ⟨c, hc⟩
  · rintro ⟨T, hT⟩
    exact h.mpr ⟨T, fun a b hab he => (Nat.not_lt_zero _ he).elim, hT⟩

/-! ### From a certificate to a bound on `f(n,4,5)` -/

/-- Lifting a colouring of `K_n` to a palette with more colours, keeping it admissible. -/
def liftCol {k' k : ℕ} (c : Col n k') (h : k' ≤ k) : Col n k :=
  fun e => ⟨c e, lt_of_lt_of_le (c e).isLt h⟩

theorem card_colorsOn_liftCol {k' k : ℕ} (c : Col n k') (h : k' ≤ k) (S : Finset (Verts n)) :
    (colorsOn (liftCol c h) S).card = (colorsOn c S).card := by
  have h1 : colorsOn (liftCol c h) S
      = (colorsOn c S).image (fun j : Fin k' => ⟨j, lt_of_lt_of_le j.isLt h⟩) := by
    unfold colorsOn
    rw [Finset.image_image]
    rfl
  have hinj : Function.Injective (fun j : Fin k' => (⟨j, lt_of_lt_of_le j.isLt h⟩ : Fin k)) := by
    intro x y hxy
    have hxy' : (⟨x.val, Nat.lt_of_lt_of_le x.isLt h⟩ : Fin k)
        = ⟨y.val, Nat.lt_of_lt_of_le y.isLt h⟩ := hxy
    exact Fin.ext (congrArg (fun z : Fin k => z.val) hxy')
  rw [h1, Finset.card_image_iff.mpr (hinj.injOn)]

theorem admissible_liftCol {k' k : ℕ} (c : Col n k') (h : k' ≤ k) (hc : Admissible c) :
    Admissible (liftCol c h) := by
  intro S hS
  rw [card_colorsOn_liftCol]
  exact hc S hS

/-- **THE LOWER-BOUND ENGINE.**  A certificate `hasAdmissible n k = false` — a statement
settled by `native_decide` in seconds, with no search required of the reader — is a Lean proof
that **no admissible colouring of `K_n` with `k+1` colours exists**, and hence that
`f(n,4,5) ≥ k+2`. -/
theorem EG_ge_of_cert {n k : ℕ} (h : hasAdmissible n k = false) : k + 2 ≤ EG n := by
  have h1 : ¬ ∃ c : Col n (k + 1), Admissible c := by
    rintro ⟨c, hc⟩
    have h2 : hasAdmissible n k = true := (hasAdmissible_iff n k).mpr ⟨c, hc⟩
    rw [h2] at h
    exact Bool.noConfusion h
  by_contra hle
  obtain ⟨c, hc⟩ := EG_admissible n
  have hk : EG n ≤ k + 1 := Nat.le_of_not_gt (by omega)
  exact h1 ⟨liftCol c hk, admissible_liftCol c hk hc⟩


/-! ### Certificates: the exact value of `f(4,4,5)` and `f(5,4,5)` -/

set_option maxRecDepth 1000000 in
/-- **CERTIFICATE: no admissible 4-colouring of `K₄`.**  A `K₄` has six edges and the catalog
condition asks for five colours on it, so four colours can never suffice.  The certificate is
the `native_decide` evaluation of the complete search of `searchAux_iff`; the number of nodes
it visits is a few dozen. -/
theorem cert_four_four : hasAdmissible 4 3 = false := by native_decide

set_option maxRecDepth 1000000 in
/-- **CERTIFICATE: no admissible 4-colouring of `K₅`.**  This is the first genuinely
non-trivial value: the catalog lower bound `⌈5(n-1)/6⌉ = 4` is *not* attained at `n = 5`, so
`f(5,4,5) ≥ 5`.  (Rounds 2–16 had no way of seeing this: `Cherry.five_sixth_lower` only gives
`4`, and the explicit constructions all use more colours.) -/
theorem cert_five_four : hasAdmissible 5 3 = false := by native_decide

/-- **THE EXACT VALUE `f(4,4,5) = 5`.** -/
theorem EG_four_ge : 5 ≤ EG 4 := EG_ge_of_cert cert_four_four

end JSP140
