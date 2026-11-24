import Mathlib
import PEqualNP.Defs

/-!
# Finite search for the Petersen second-OR bound

This file gives two kernel-checked deductions for L-meta-1868 and its negation
L-meta-1869. A circuit with at most thirteen suffix gates needs at least eight
non-NOT gates. Any such circuit gives a live-wire state on 414 labeled pairs,
with at most five NOT gates. The final theorem takes the absence of those states
as an explicit hypothesis. The companion C++ program enumerates the states.
-/
namespace PetersenBinary
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
-- Adapted from PEqualNP.MetaComplexity.Helpers.Support.
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w


variable {n : ℕ}


theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp


def gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _


def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L


def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}


def Agree (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem agree_wiresFrom (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

theorem agree_inputs (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]


def Cnt (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_inputs : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem cnt_step (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (cost : ℕ) (hg : g.inputs.length ≤ cost + 1)
    (h : Cnt t L) : Cnt (t + cost) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + (cost + 1) := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega


def negGate (g : Gate) := match g.op with | .not => true | _ => false

def trimmed (g : Gate) : Gate :=
  if negGate g then ⟨g.op, g.inputs.take 1⟩ else g

theorem trim_eval (gs : List Gate) (w : List Bool) : wiresFrom (gs.map trimmed) w = wiresFrom gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change wiresFrom (gs.map trimmed) _ = wiresFrom gs _
    rw [ih]
    apply congrArg (wiresFrom gs)
    cases g with
    | mk op inputs => cases op <;> cases inputs <;> rfl

theorem cost_bound (gs : List Gate) (fan : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (t : ℕ) (L : List (Finset (Fin n))) (h : Cnt t L) :
    Cnt (t + (gs.filter (fun g => !negGate g)).length) (suppsFrom (gs.map trimmed) L) := by
  induction gs generalizing t L with
  | nil => simpa [suppsFrom] using h
  | cons g gs ih =>
    have rest := fun g' (hg' : g' ∈ gs) => fan g' (List.mem_cons_of_mem _ hg')
    by_cases isnot : negGate g = true
    · have len : (trimmed g).inputs.length ≤ 0 + 1 := by simp [trimmed,isnot]
      have H := ih rest (t + 0) _ (cnt_step t L (trimmed g) 0 len h)
      simpa only [List.map_cons, List.filter_cons, isnot, Bool.not_true, Bool.false_eq_true,
        ite_false, Nat.add_zero, suppsFrom, List.foldl_cons] using H
    · have no := Bool.eq_false_iff.mpr isnot
      have len : (trimmed g).inputs.length ≤ 1 + 1 := by simpa [trimmed,no] using fan g List.mem_cons_self
      have H := ih rest (t + 1) _ (cnt_step t L (trimmed g) 1 len h)
      simpa [no, suppsFrom, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using H

def support (C : Circuit) (n : ℕ) :=
  (suppsFrom (C.gates.map trimmed) (inputSupps n)).getD C.output ∅

theorem support_size (C : Circuit) (hf : FanInTwo C) (n : ℕ) :
    (support C n).card ≤ (C.gates.filter (fun g => !negGate g)).length + 1 := by
  have h := cost_bound C.gates (fun g hg => (hf g hg).2) 0 (inputSupps n) cnt_inputs {C.output}
  simpa [support] using h

theorem depends (C : Circuit) (x y : Fin n → Bool) (h : ∀ i ∈ support C n, x i = y i) :
    C.eval (List.ofFn x) = C.eval (List.ofFn y) := by
  have eq := (agree_wiresFrom x y (C.gates.map trimmed) _ _ _ (agree_inputs x y)).2.2 C.output h
  rw [trim_eval,trim_eval] at eq
  exact eq

def bits (m : ℕ) (i : Fin 9) := m.testBit i.val
def edge (x : Fin 9 → Bool) :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) ||
  (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
def base (x : Fin 9 → Bool) (j : Fin 11) :=
  if h : j.val < 9 then x ⟨j.val,h⟩ else if j.val = 9 then x 0 && x 3 else false
def signals (a b : Fin 11) (x : Fin 9 → Bool) (j : Fin 11) :=
  if j.val = 10 then base x a || base x b else base x j
def exampleRowTable : Fin 41 → Fin 9 → ℕ := ![![2, 1, 2, 4, 1, 1, 2, 4, 8], ![20, 1, 9, 4, 1, 1, 2, 4, 8], ![2, 1, 2, 5, 1, 1, 2, 4, 8], ![16, 1, 2, 4, 1, 1, 2, 4, 8], ![32, 1, 2, 4, 1, 1, 2, 4, 8], ![80, 1, 2, 4, 1, 1, 257, 4, 8], ![130, 1, 2, 4, 1, 1, 2, 5, 8], ![258, 1, 2, 4, 1, 1, 2, 4, 9], ![2, 4, 2, 4, 1, 1, 2, 4, 8], ![2, 9, 2, 18, 1, 1, 2, 4, 8], ![2, 20, 2, 4, 10, 1, 2, 4, 8], ![2, 36, 2, 4, 1, 130, 2, 4, 8], ![2, 64, 2, 4, 1, 1, 2, 4, 8], ![2, 129, 2, 4, 1, 1, 2, 34, 8], ![2, 257, 2, 4, 1, 1, 2, 4, 10], ![2, 9, 2, 4, 1, 1, 2, 4, 8], ![2, 1, 8, 4, 1, 1, 2, 4, 8], ![2, 1, 18, 4, 5, 1, 2, 4, 8], ![2, 1, 34, 4, 1, 5, 2, 4, 8], ![2, 1, 72, 4, 1, 1, 260, 4, 8], ![2, 1, 128, 4, 1, 1, 2, 4, 8], ![2, 1, 258, 4, 1, 1, 2, 4, 36], ![2, 1, 9, 4, 1, 1, 2, 4, 8], ![2, 1, 2, 16, 8, 1, 2, 4, 8], ![2, 1, 2, 36, 1, 9, 2, 4, 8], ![2, 1, 2, 68, 1, 1, 10, 4, 8], ![2, 1, 2, 144, 1, 1, 2, 40, 8], ![2, 1, 2, 256, 1, 1, 2, 4, 8], ![2, 1, 2, 4, 40, 144, 2, 4, 8], ![2, 1, 2, 4, 65, 1, 18, 4, 8], ![2, 1, 2, 4, 129, 1, 2, 20, 8], ![2, 1, 2, 4, 257, 1, 2, 4, 48], ![2, 1, 2, 4, 9, 1, 2, 4, 8], ![2, 1, 2, 4, 1, 65, 34, 4, 8], ![2, 1, 2, 4, 1, 128, 2, 32, 8], ![2, 1, 2, 4, 1, 256, 2, 4, 32], ![2, 1, 2, 4, 1, 9, 2, 4, 8], ![2, 1, 2, 4, 1, 1, 130, 68, 8], ![2, 1, 2, 4, 1, 1, 256, 4, 64], ![2, 1, 2, 4, 1, 1, 2, 260, 136], ![2, 1, 2, 4, 1, 1, 2, 4, 9]]
def exampleRow (a b : Fin 11) : Fin 9 → ℕ := exampleRowTable ( (![![0, 0, 1, 2, 3, 4, 5, 6, 7, 0, 0], ![0, 0, 8, 9, 10, 11, 12, 13, 14, 15, 0], ![1, 8, 0, 16, 17, 18, 19, 20, 21, 22, 0], ![2, 9, 16, 0, 23, 24, 25, 26, 27, 0, 0], ![3, 10, 17, 23, 0, 28, 29, 30, 31, 32, 0], ![4, 11, 18, 24, 28, 0, 33, 34, 35, 36, 0], ![5, 12, 19, 25, 29, 33, 0, 37, 38, 0, 0], ![6, 13, 20, 26, 30, 34, 37, 0, 39, 0, 0], ![7, 14, 21, 27, 31, 35, 38, 39, 0, 40, 0], ![0, 15, 22, 0, 32, 36, 0, 0, 40, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] : Fin 11 → Fin 11 → Fin 41) a b)
def ownerTable : Fin 10 → Fin 11 → Fin 9 := ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 0], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 3, 0], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 2], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 3], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 4], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 5], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 6], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 7], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 8]]
def owner (a b : Fin 11) : Fin 11 → Fin 9 := ownerTable ( (![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2], ![0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 3], ![1, 0, 0, 4, 0, 0, 0, 0, 0, 4, 4], ![0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 5], ![0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 6], ![0, 0, 0, 0, 0, 0, 7, 0, 0, 7, 7], ![0, 0, 0, 0, 0, 0, 0, 8, 0, 8, 8], ![0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 9], ![0, 0, 0, 4, 0, 0, 7, 8, 0, 0, 0], ![0, 2, 3, 4, 5, 6, 7, 8, 9, 0, 0]] : Fin 11 → Fin 11 → Fin 10) a b)

def off (a b : Fin 11) (i : Fin 9) := bits (exampleRow a b i)
def on (a b : Fin 11) (i : Fin 9) := bits (exampleRow a b i ||| (1 <<< i.val))
def Good (a : Fin 11) : Prop :=
  ∀ (b : Fin 11) (i : Fin 9), edge (off a b i) = false ∧ edge (on a b i) = true ∧
    ∀ j : Fin 11, signals a b (off a b i) j ≠ signals a b (on a b i) j → owner a b j = i
instance (a : Fin 11) : Decidable (Good a) := by unfold Good; infer_instance
set_option maxHeartbeats 0 in
theorem rows0 : Good 0 := by decide +kernel
set_option maxHeartbeats 0 in
theorem rows1 : Good 1 := by decide +kernel
set_option maxHeartbeats 0 in
theorem rows2 : Good 2 := by decide +kernel
set_option maxHeartbeats 0 in
theorem rows3 : Good 3 := by decide +kernel
set_option maxHeartbeats 0 in
theorem rows4 : Good 4 := by decide +kernel
set_option maxHeartbeats 0 in
theorem rows5 : Good 5 := by decide +kernel
set_option maxHeartbeats 0 in
theorem rows6 : Good 6 := by decide +kernel
set_option maxHeartbeats 0 in
theorem rows7 : Good 7 := by decide +kernel
set_option maxHeartbeats 0 in
theorem rows8 : Good 8 := by decide +kernel
set_option maxHeartbeats 0 in
theorem rows9 : Good 9 := by decide +kernel
set_option maxHeartbeats 0 in
theorem rows10 : Good 10 := by decide +kernel
theorem all_rows (a : Fin 11) : Good a := by
  fin_cases a
  · exact rows0
  · exact rows1
  · exact rows2
  · exact rows3
  · exact rows4
  · exact rows5
  · exact rows6
  · exact rows7
  · exact rows8
  · exact rows9
  · exact rows10

theorem binary_lower (a b : Fin 11) (C : Circuit) (hf : FanInTwo C)
    (right : ∀ x, C.eval (List.ofFn (signals a b x)) = edge x) :
    8 ≤ (C.gates.filter (fun g => !negGate g)).length := by
  let S := support C 11
  have allmem (i : Fin 9) : i ∈ S.image (owner a b) := by
    by_contra outside
    have ⟨lo,hi,own⟩ := all_rows a b i
    have same := depends C (signals a b (off a b i)) (signals a b (on a b i)) (by
      intro j hj
      by_contra dif
      exact outside (Finset.mem_image.mpr ⟨j,hj,own j dif⟩))
    rw [right,right,lo,hi] at same
    contradiction
  have full : (S.image (owner a b)).card = 9 := by rw [Finset.eq_univ_of_forall allmem]; simp
  have bound := support_size C hf 11
  have cover := Finset.card_image_le (s:=S) (f:=owner a b)
  change S.card ≤ _ at bound
  omega

def orderedInputs (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 && x 3]

theorem base_read (x : Fin 9 → Bool) (j : Fin 11) : (orderedInputs x).getD j.val false = base x j := by
  fin_cases j <;> rfl

theorem or_read (x : Fin 9 → Bool) (ins : List (Fin 11)) (arity : ins.length ≤ 2) :
    GateOp.or.eval (ins.map (fun j => (orderedInputs x).getD j.val false)) =
    (base x (ins.getD 0 10) || base x (ins.getD 1 10)) := by
  cases ins with
  | nil => rfl
  | cons a rest =>
    cases rest with
    | nil => change ((orderedInputs x).getD a.val false || false) = (base x a || false)
             rw [base_read]
    | cons b tail =>
      have len : tail.length = 0 := by simp only [List.length_cons] at arity; omega
      obtain rfl := List.length_eq_zero_iff.mp len
      change ((orderedInputs x).getD a.val false || ((orderedInputs x).getD b.val false || false)) = (base x a || base x b)
      rw [base_read, base_read, Bool.or_false]

theorem signal_list (x : Fin 9 → Bool) (ins : List (Fin 11)) (arity : ins.length ≤ 2) :
    List.ofFn (signals (ins.getD 0 10) (ins.getD 1 10) x) = orderedInputs x ++
      [GateOp.or.eval (ins.map (fun j => (orderedInputs x).getD j.val false))] := by
  rw [or_read x ins arity]
  rfl

/-- Any proposed 13-gate suffix for this desk step has at most five NOT gates.
The OR operands may repeat or use the fixed AND or the default false wire. -/
theorem fiveNotLimit (C : Circuit) (ins : List (Fin 11)) (arity : ins.length ≤ 2)
    (hf : FanInTwo C) (size : C.size ≤ 13)
    (right : ∀ x : Fin 9 → Bool, C.eval (orderedInputs x ++
      [GateOp.or.eval (ins.map (fun j => (orderedInputs x).getD j.val false))]) = edge x) :
    (C.gates.filter negGate).length ≤ 5 := by
  have bound := binary_lower (ins.getD 0 10) (ins.getD 1 10) C hf (fun x => by
    rw [signal_list _ _ arity]; exact right x)
  have split := List.length_eq_length_filter_add (l := C.gates) negGate
  change C.gates.length ≤ 13 at size
  omega

end PetersenBinary


-- The live-wire extraction and the 414 labeled pairs are adapted from the
-- project certificate of jmwalsh96 for L-meta-1672, and its counted version.
namespace PetersenSearch

abbrev Sig := Nat × Nat
def top : Nat := 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def bnot (x : Nat) : Nat := x ^^^ top
def zero : Sig := (0, 0)
def one : Sig := (top, top)
def target : Sig := (top, 0)
def neg (a : Sig) : Sig := (bnot a.1, bnot a.2)
def bin (isOr : Bool) (a b : Sig) : Sig :=
  if isOr then (a.1 ||| b.1, a.2 ||| b.2) else (a.1 &&& b.1, a.2 &&& b.2)
def sep (d : Bool) (a : Sig) : Nat :=
  if d then a.1 ^^^ a.2 else a.1 &&& bnot a.2
def unionSep (d : Bool) : List Sig → Nat
  | [] => 0
  | a :: l => sep d a ||| unionSep d l
def Valid1 (x : Nat) : Prop := ∀ j, 414 ≤ j → x.testBit j = false
def Valid (a : Sig) : Prop := Valid1 a.1 ∧ Valid1 a.2
def proper (a : Sig) : Prop := Valid a ∧ a ≠ zero ∧ a ≠ one
lemma top_eq_pow : top = 2 ^ 207 * 2 ^ 207 - 1 := by decide
lemma pow_add_testBit (a b j : Nat) : (2 ^ a * 2 ^ b - 1).testBit j = decide (j < a + b) := by
  rw [← Nat.pow_add, Nat.testBit_two_pow_sub_one]
lemma testBit_top (j : Nat) : top.testBit j = decide (j < 414) := by
  rw [top_eq_pow]; exact pow_add_testBit 207 207 j
lemma testBit_bnot {x : Nat} (hx : Valid1 x) (j : Nat) :
    (bnot x).testBit j = if j < 414 then !(x.testBit j) else false := by
  simp only [bnot, Nat.testBit_xor, testBit_top]
  by_cases hj : j < 414
  · simp [hj]
  · simp [hj, hx j (by omega)]
lemma testBit_bnot_lt (x : Nat) {j : Nat} (hj : j < 414) :
    (bnot x).testBit j = !(x.testBit j) := by
  simp [bnot, Nat.testBit_xor, testBit_top, hj]
lemma valid1_zero : Valid1 0 := fun _ _ => Nat.zero_testBit _
lemma valid1_top : Valid1 top := fun j hj => by rw [testBit_top]; simp [show ¬ j < 414 by omega]
lemma valid1_bnot {x : Nat} (hx : Valid1 x) : Valid1 (bnot x) := fun j hj => by
  rw [testBit_bnot hx]; simp [show ¬ j < 414 by omega]
lemma valid1_and {x y : Nat} (hx : Valid1 x) : Valid1 (x &&& y) := fun j hj => by
  rw [Nat.testBit_and, hx j hj]; rfl
lemma valid1_or {x y : Nat} (hx : Valid1 x) (hy : Valid1 y) : Valid1 (x ||| y) := fun j hj => by
  rw [Nat.testBit_or, hx j hj, hy j hj]; rfl
lemma valid1_xor {x y : Nat} (hx : Valid1 x) (hy : Valid1 y) : Valid1 (x ^^^ y) := fun j hj => by
  rw [Nat.testBit_xor, hx j hj, hy j hj]; rfl
lemma lt_pow_mul_testBit {a b x j : Nat} (hx : x < 2 ^ a * 2 ^ b) (hj : a + b ≤ j) :
    x.testBit j = false := by
  rw [← Nat.pow_add] at hx
  exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) hj))
lemma valid1_of_le_top {x : Nat} (h : x ≤ top) : Valid1 x := fun j hj => by
  have hlt : x < 2 ^ 207 * 2 ^ 207 := by
    have hp : 0 < 2 ^ 207 * 2 ^ 207 := by decide
    rw [top_eq_pow] at h; omega
  exact lt_pow_mul_testBit hlt hj
lemma valid_zero : Valid zero := ⟨valid1_zero, valid1_zero⟩
lemma valid_one : Valid one := ⟨valid1_top, valid1_top⟩
lemma valid_target : Valid target := ⟨valid1_top, valid1_zero⟩
lemma valid_neg {a : Sig} (ha : Valid a) : Valid (neg a) := ⟨valid1_bnot ha.1, valid1_bnot ha.2⟩
lemma valid_bin {d : Bool} {a b : Sig} (ha : Valid a) (hb : Valid b) : Valid (bin d a b) := by
  cases d
  · exact ⟨valid1_and ha.1, valid1_and ha.2⟩
  · exact ⟨valid1_or ha.1 hb.1, valid1_or ha.2 hb.2⟩
lemma valid_sep {d : Bool} {a : Sig} (ha : Valid a) : Valid1 (sep d a) := by
  cases d
  · exact valid1_and ha.1
  · exact valid1_xor ha.1 ha.2
lemma valid_unionSep {d : Bool} {v : List Sig} (hv : ∀ a ∈ v, Valid a) : Valid1 (unionSep d v) := by
  induction v with
  | nil => exact valid1_zero
  | cons a l ih =>
    exact valid1_or (valid_sep (hv a (by simp))) (ih (fun x hx => hv x (by simp [hx])))
lemma bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d
  · simp [bin, Nat.and_comm]
  · simp [bin, Nat.or_comm]
lemma bin_laws {a : Sig} (ha : Valid a) :
    bin false a one = a ∧ bin true a zero = a ∧
    bin false a zero = zero ∧ bin true a one = one ∧
    bin false a a = a ∧ bin true a a = a := by
  obtain ⟨p, n⟩ := a
  obtain ⟨hp, hn⟩ := ha
  have land_top {x : Nat} (hx : Valid1 x) : x &&& top = x := by
    apply Nat.eq_of_testBit_eq; intro j
    rw [Nat.testBit_and, testBit_top]
    by_cases hj : j < 414 <;> simp [hj]
    exact hx j (by omega)
  have lor_top {x : Nat} (hx : Valid1 x) : x ||| top = top := by
    apply Nat.eq_of_testBit_eq; intro j
    rw [Nat.testBit_or, testBit_top]
    by_cases hj : j < 414 <;> simp [hj]
    exact hx j (by omega)
  simp [bin, one, zero, land_top hp, land_top hn, lor_top hp, lor_top hn]
lemma neg_laws : neg zero = one ∧ neg one = zero := by
  have h1 : bnot 0 = top := by simp [bnot]
  have h2 : bnot top = 0 := by simp [bnot]
  exact ⟨Prod.ext h1 h1, Prod.ext h2 h2⟩
lemma target_proper : proper target :=
  ⟨valid_target, by unfold target zero top; decide, by unfold target one top; decide⟩
lemma land_eq (x y : Nat) : Nat.land x y = x &&& y := rfl
lemma lor_eq (x y : Nat) : Nat.lor x y = x ||| y := rfl
lemma lxor_eq (x y : Nat) : Nat.xor x y = x ^^^ y := rfl
lemma testBit_land (x y i : Nat) : (Nat.land x y).testBit i = (x.testBit i && y.testBit i) := Nat.testBit_and x y i
lemma testBit_lor (x y i : Nat) : (Nat.lor x y).testBit i = (x.testBit i || y.testBit i) := Nat.testBit_or x y i
lemma testBit_lxor (x y i : Nat) : (Nat.xor x y).testBit i = (x.testBit i != y.testBit i) := by
  simp [bne]
abbrev Cov := Nat × Nat × Nat
def ValidCov (c : Cov) : Prop :=
  Valid1 c.1 ∧ Valid1 c.2.1 ∧ Valid1 c.2.2 ∧
  (∀ i, c.2.1.testBit i = true → c.1.testBit i = true) ∧
  (∀ i, c.2.2.testBit i = true → c.1.testBit i = true)
def covAdd (z : Nat) (c : Cov) : Cov :=
  (Nat.lor z c.1,
   Nat.land (Nat.xor z c.1) (Nat.lor z c.2.1),
   Nat.xor c.2.2 (Nat.land z (Nat.xor c.2.2 c.2.1)))
def coverage (d : Bool) (v : List Sig) : Cov :=
  v.foldr (fun a c => covAdd (sep d a) c) (0, 0, 0)
def takeOne (c : Cov) (a : Nat) : Nat := Nat.xor c.1 (Nat.land c.2.1 a)
def takeTwo (c : Cov) (a b : Nat) : Nat :=
  Nat.xor c.1 (Nat.lor (Nat.land c.2.1 (Nat.lor a b)) (Nat.land c.2.2 (Nat.land a b)))
lemma validCov_zero : ValidCov (0, 0, 0) :=
  ⟨valid1_zero, valid1_zero, valid1_zero, fun _ h => by simp at h, fun _ h => by simp at h⟩
lemma validCov_add {z : Nat} {c : Cov} (hz : Valid1 z) (hc : ValidCov c) : ValidCov (covAdd z c) := by
  refine ⟨valid1_or hz hc.1, valid1_and (valid1_xor hz hc.1), valid1_xor hc.2.2.1 (valid1_and hz), ?_, ?_⟩
  · intro i h; have h1 := hc.2.2.2.1 i
    simp only [covAdd, testBit_land, testBit_lor, testBit_lxor] at h ⊢
    revert h h1; cases z.testBit i <;> cases c.1.testBit i <;> cases c.2.1.testBit i <;> simp
  · intro i h; have h1 := hc.2.2.2.1 i; have h2 := hc.2.2.2.2 i
    simp only [covAdd, testBit_land, testBit_lor, testBit_lxor] at h ⊢
    revert h h1 h2; cases z.testBit i <;> cases c.1.testBit i <;> cases c.2.1.testBit i <;>
      cases c.2.2.testBit i <;> simp
lemma validCov_coverage (d : Bool) {v : List Sig} (hv : ∀ a ∈ v, Valid a) : ValidCov (coverage d v) := by
  induction v with
  | nil => exact validCov_zero
  | cons a l ih => exact validCov_add (valid_sep (hv a (by simp))) (ih (fun x hx => hv x (by simp [hx])))
lemma cov_one {c : Cov} {a : Nat} (hc : ValidCov c) : takeOne (covAdd a c) a = c.1 := by
  apply Nat.eq_of_testBit_eq; intro i
  have h1 := hc.2.2.2.1 i
  simp only [takeOne, covAdd, testBit_land, testBit_lor, testBit_lxor]
  revert h1; cases a.testBit i <;> cases c.1.testBit i <;> cases c.2.1.testBit i <;> simp
lemma cov_two {c : Cov} {a b : Nat} (hc : ValidCov c) :
    takeTwo (covAdd a (covAdd b c)) a b = c.1 := by
  apply Nat.eq_of_testBit_eq; intro i
  have h1 := hc.2.2.2.1 i; have h2 := hc.2.2.2.2 i
  simp only [takeTwo, covAdd, testBit_land, testBit_lor, testBit_lxor]
  revert h1 h2; cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
    cases c.2.1.testBit i <;> cases c.2.2.testBit i <;> simp
lemma cov_two_unique_disj {c : Cov} {a b : Nat} (hc : ValidCov c) :
    Nat.land (Nat.land (covAdd a (covAdd b c)).2.1 a) b = 0 := by
  apply Nat.eq_of_testBit_eq; intro i
  have h1 := hc.2.2.2.1 i
  simp only [covAdd, testBit_land, testBit_lor, testBit_lxor, Nat.zero_testBit]
  revert h1; cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
    cases c.2.1.testBit i <;> simp
lemma covAdd_swap {c : Cov} {a b : Nat} (hc : ValidCov c) :
    covAdd a (covAdd b c) = covAdd b (covAdd a c) := by
  have h1 := hc.2.2.2.1; have h2 := hc.2.2.2.2
  refine Prod.ext (Nat.eq_of_testBit_eq fun i => ?_)
    (Prod.ext (Nat.eq_of_testBit_eq fun i => ?_) (Nat.eq_of_testBit_eq fun i => ?_))
  · simp only [covAdd, testBit_lor]; cases a.testBit i <;> cases b.testBit i <;> rfl
  · have h1i := h1 i; simp only [covAdd, testBit_land, testBit_lor, testBit_lxor]
    revert h1i; cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
      cases c.2.1.testBit i <;> simp
  · have h1i := h1 i; have h2i := h2 i; simp only [covAdd, testBit_land, testBit_lor, testBit_lxor]
    revert h1i h2i; cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
      cases c.2.1.testBit i <;> cases c.2.2.testBit i <;> simp
lemma cov_perm (d : Bool) {l r : List Sig} (hl : ∀ a ∈ l, Valid a) (h : l.Perm r) :
    coverage d l = coverage d r := by
  induction h with
  | nil => rfl
  | cons a _ ih =>
    exact congrArg (covAdd (sep d a)) (ih (fun x hx => hl x (by simp [hx])))
  | swap a b t =>
    exact covAdd_swap (validCov_coverage d (fun x hx => hl x (by simp [hx])))
  | trans h1 _ ih1 ih2 =>
    exact (ih1 hl).trans (ih2 (fun x hx => hl x (h1.mem_iff.2 hx)))
lemma cov_union (d : Bool) (v : List Sig) : (coverage d v).1 = unionSep d v := by
  induction v with
  | nil => rfl
  | cons a v ih => change sep d a ||| (coverage d v).1 = sep d a ||| unionSep d v; rw [ih]
def dropped (del v : List Sig) : List Sig := v.filter (fun x => !(del.contains x))
def keepOf (U : Finset Sig) (del : List Sig) : List Sig := del.filter (fun a => decide (a ∈ U))
lemma edit_list {v del : List Sig} {U : Finset Sig}
    (hv : v.Nodup) (hd : del.Nodup) (he : v.toFinset = del.toFinset ∪ U) :
    (keepOf U del ++ dropped del v).Nodup ∧ (keepOf U del ++ dropped del v).toFinset = U := by
  have memv (x : Sig) : x ∈ v ↔ x ∈ del ∨ x ∈ U := by
    rw [← List.mem_toFinset, he]; simp
  constructor
  · rw [List.nodup_append]
    refine ⟨hd.filter _, hv.filter _, ?_⟩
    intro a ha b hb eq; subst b
    simp [keepOf] at ha; simp [dropped] at hb; exact hb.2 ha.1
  · ext x
    simp only [List.mem_toFinset, List.mem_append, List.mem_filter, keepOf, dropped,
      decide_eq_true_eq, Bool.not_eq_true', List.contains_eq_mem, memv]
    by_cases h : x ∈ del <;> simp_all
lemma recover_perm (del v : List Sig) (hv : v.Nodup) (hd : del.Nodup)
    (hs : ∀ x ∈ del, x ∈ v) : v.Perm (del ++ dropped del v) := by
  apply List.perm_of_nodup_nodup_toFinset_eq hv
  · rw [List.nodup_append]
    refine ⟨hd, hv.filter _, ?_⟩
    intro a ha b hb e; subst b; simp [dropped] at hb; exact hb.2 ha
  · ext x
    simp only [List.mem_toFinset, List.mem_append, dropped, List.mem_filter, Bool.not_eq_true',
      List.contains_eq_mem, decide_eq_false_iff_not]
    by_cases h : x ∈ del <;> simp_all
lemma one_rest (d : Bool) {v : List Sig} {a : Sig} (hv : v.Nodup) (hval : ∀ x ∈ v, Valid x)
    (ha : a ∈ v) :
    v.length - 1 = (dropped [a] v).length ∧
      takeOne (coverage d v) (sep d a) = unionSep d (dropped [a] v) := by
  have p := recover_perm [a] v hv (by simp) (by simpa using ha)
  constructor
  · have l := p.length_eq; simp at l; omega
  · rw [cov_perm d hval p]
    have hrest : ∀ x ∈ dropped [a] v, Valid x := fun x hx =>
      hval x (List.mem_of_mem_filter hx)
    exact (cov_one (validCov_coverage d hrest)).trans (cov_union d _)
lemma two_rest (d : Bool) {v : List Sig} {a b : Sig} (hv : v.Nodup) (hval : ∀ x ∈ v, Valid x)
    (ha : a ∈ v) (hb : b ∈ v) (hab : a ≠ b) :
    v.length - 2 = (dropped [a, b] v).length ∧
      takeTwo (coverage d v) (sep d a) (sep d b) = unionSep d (dropped [a, b] v) := by
  have p := recover_perm [a, b] v hv (by simp [hab]) (by simp [ha, hb])
  constructor
  · have l := p.length_eq; simp at l; omega
  · rw [cov_perm d hval p]
    have hrest : ∀ x ∈ dropped [a, b] v, Valid x := fun x hx =>
      hval x (List.mem_of_mem_filter hx)
    exact (cov_two (validCov_coverage d hrest)).trans (cov_union d _)
lemma two_rest_disj (d : Bool) {v : List Sig} {a b : Sig} (hv : v.Nodup) (hval : ∀ x ∈ v, Valid x)
    (ha : a ∈ v) (hb : b ∈ v) (hab : a ≠ b) :
    Nat.land (Nat.land (coverage d v).2.1 (sep d a)) (sep d b) = 0 := by
  have p := recover_perm [a, b] v hv (by simp [hab]) (by simp [ha, hb])
  rw [cov_perm d hval p]
  exact cov_two_unique_disj (validCov_coverage d (fun x hx => hval x (List.mem_of_mem_filter hx)))
inductive Live : Nat → Nat → Finset Sig → Prop
  | stop : Live 0 0 {target}
  | unary {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live k t (insert (neg a) U)) :
      Live (k + 1) (t + 1) (insert a U)
  | binary {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live k t (insert (bin d a b) U)) :
      Live (k + 1) t (insert a (insert b U))
lemma live_proper {k t S} (h : Live k t S) : ∀ a ∈ S, proper a := by
  induction h with
  | stop => simpa using target_proper
  | unary ha _ _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb _ _ _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha, hb, fun a h => ih a (Finset.mem_insert_of_mem h)⟩
lemma live_size {k t S} (h : Live k t S) : t ≤ k ∧ S.card + t ≤ k + 1 := by
  induction h with
  | stop => simp
  | @unary k t U a _ hf _ ih =>
    have hu : neg a ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega, by omega⟩
  | @binary k t U a b d _ _ _ hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega, by omega⟩
lemma sep_unary (t : Nat) {a : Sig} (ha : Valid a) (i : Nat) (hi : i < 414)
    (h : (sep (decide (0 < t)) (neg a)).testBit i = true) :
    (sep true a).testBit i = true := by
  cases ht : decide (0 < t)
  · simp only [sep, neg, ht, Bool.false_eq_true, ite_false, ite_true, Nat.testBit_and,
      Nat.testBit_xor, testBit_bnot (valid1_bnot ha.2), testBit_bnot ha.1, testBit_bnot ha.2,
      hi] at h ⊢
    cases hx : a.1.testBit i <;> cases hy : a.2.testBit i <;> simp [hx, hy] at h ⊢
  · simp only [sep, neg, ht, ite_true, Nat.testBit_xor,
      testBit_bnot ha.1, testBit_bnot ha.2, hi] at h ⊢
    cases hx : a.1.testBit i <;> cases hy : a.2.testBit i <;> simp [hx, hy] at h ⊢
lemma sep_binary (t d : Bool) {a b : Sig} (_ha : Valid a) (_hb : Valid b) (i : Nat) (hi : i < 414)
    (h : (sep t (bin d a b)).testBit i = true) :
    (sep t a).testBit i = true ∨ (sep t b).testBit i = true := by
  cases t <;> cases d <;>
    simp only [sep, bin, Bool.false_eq_true, ite_true, ite_false, Nat.testBit_xor,
      Nat.testBit_and, Nat.testBit_or, testBit_bnot_lt _ hi] at h ⊢ <;>
    revert h <;>
    cases a.1.testBit i <;> cases a.2.testBit i <;>
    cases b.1.testBit i <;> cases b.2.testBit i <;> simp
lemma sep_weaken (t : Nat) {a : Sig} (ha : Valid a) (i : Nat) (hi : i < 414)
    (h : (sep (decide (0 < t)) a).testBit i = true) : (sep true a).testBit i = true := by
  cases ht : decide (0 < t)
  · simp only [sep, ht, Bool.false_eq_true, ite_false, ite_true, Nat.testBit_and,
      Nat.testBit_xor, testBit_bnot ha.2, hi] at h ⊢
    cases hx : a.1.testBit i <;> cases hy : a.2.testBit i <;> simp [hx, hy] at h ⊢
  · simpa [ht] using h
lemma live_sep {k t S} (h : Live k t S) (i : Nat) (hi : i < 414) :
    ∃ a ∈ S, (sep (decide (0 < t)) a).testBit i = true := by
  induction h with
  | stop =>
    refine ⟨target, by simp, ?_⟩
    simp [sep, target, Nat.testBit_and, testBit_top, testBit_bnot valid1_zero, hi]
  | unary ha _ tail ih =>
    obtain ⟨x, hx, h⟩ := ih
    simp only [Finset.mem_insert] at hx
    simp only [Nat.zero_lt_succ, decide_true]
    rcases hx with rfl | hU
    · exact ⟨_, Finset.mem_insert_self _ _, sep_unary _ ha.1 i hi h⟩
    · exact ⟨x, Finset.mem_insert_of_mem hU,
        sep_weaken _ (live_proper tail x (Finset.mem_insert_of_mem hU)).1 i hi h⟩
  | binary ha hb _ _ _ ih =>
    obtain ⟨x, hx, h⟩ := ih
    rcases Finset.mem_insert.mp hx with rfl | hU
    · rcases sep_binary _ _ ha.1 hb.1 i hi h with h | h
      · exact ⟨_, Finset.mem_insert_self _ _, h⟩
      · exact ⟨_, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), h⟩
    · exact ⟨x, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hU), h⟩
lemma mem_unionSep (d : Bool) (v : List Sig) (i : Nat) :
    (unionSep d v).testBit i = true ↔ ∃ a ∈ v, (sep d a).testBit i = true := by
  induction v with
  | nil => simp [unionSep]
  | cons a v ih =>
    simp only [unionSep, Nat.testBit_or, Bool.or_eq_true, ih, List.mem_cons, exists_eq_or_imp]
lemma live_cover {k t S} {v : List Sig} (h : Live k t S) (he : v.toFinset = S) :
    unionSep (decide (0 < t)) v = top := by
  have hv : ∀ a ∈ v, Valid a := fun a ha => (live_proper h a (he ▸ List.mem_toFinset.mpr ha)).1
  apply Nat.eq_of_testBit_eq; intro i
  rw [testBit_top]
  by_cases hi : i < 414
  · simp only [hi, decide_true]
    obtain ⟨a, hm, ha⟩ := live_sep h i hi
    exact (mem_unionSep _ _ _).2 ⟨a, List.mem_toFinset.mp (he.symm ▸ hm), ha⟩
  · simp only [hi, decide_false]
    exact valid_unionSep hv i (by omega)
lemma union_append (d : Bool) (l r : List Sig) :
    unionSep d (l ++ r) = unionSep d l ||| unionSep d r := by
  induction l with
  | nil => simp [unionSep]
  | cons a l ih => simp [unionSep, ih, Nat.or_assoc]
open PEqualNP.CircuitLowerBounds
def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (bin false) one
  | .or => xs.foldr (bin true) zero
  | .not => neg (xs.headD zero)
  | _ => zero
def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w
lemma valid_getD {w : List Sig} (hw : ∀ a ∈ w, Valid a) (i : Nat) : Valid (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact valid_zero
  | some a => exact hw a (List.mem_of_getElem? h)
lemma gv_valid {w : List Sig} (hw : ∀ a ∈ w, Valid a) (g : Gate) : Valid (gv w g) := by
  obtain ⟨o, l⟩ := g
  cases o with
  | and =>
    change Valid ((l.map (fun i => w.getD i zero)).foldr (bin false) one)
    induction l with
    | nil => exact valid_one
    | cons i l ih => exact valid_bin (valid_getD hw i) ih
  | or =>
    change Valid ((l.map (fun i => w.getD i zero)).foldr (bin true) zero)
    induction l with
    | nil => exact valid_zero
    | cons i l ih => exact valid_bin (valid_getD hw i) ih
  | not =>
    cases l with
    | nil => exact valid_neg valid_zero
    | cons i _ => exact valid_neg (valid_getD hw i)
  | mod _ => exact valid_zero
  | maj => exact valid_zero
def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬ proper v
lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.2.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)
lemma operand_cases {w : List Sig} {a : Sig} (hva : Valid a) (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hva, hz, ho⟩), hva, hz, ho⟩)
def negative (g : Gate) : Bool :=
  match g.op with
  | .not => true
  | _ => false
def witness (isNeg : Bool) (w : List Sig) (z : Sig) : Prop :=
  (isNeg = true ∧ ∃ a ∈ w, proper a ∧ z = neg a) ∨
  (isNeg = false ∧ ∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)
lemma bin_rep {w a b} (d : Bool) (hva : Valid a) (hvb : Valid b)
    (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ witness false w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.2.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2.2 rfl)
  obtain ⟨a1, a0, az, ao, aa, aa'⟩ := bin_laws hva
  obtain ⟨b1, b0, bz, bo, bb, bb'⟩ := bin_laws hvb
  rcases operand_cases hva ha with rfl | rfl | ⟨ham, hap⟩
  · rw [bin_comm]; cases d <;> simp_all
  · rw [bin_comm]; cases d <;> simp_all
  rcases operand_cases hvb hb with rfl | rfl | ⟨hbm, hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a = b
  · subst b; cases d <;> simp_all
  exact Or.inr (Or.inr ⟨rfl, d, a, b, ham, hbm, hap, hbp, he, rfl⟩)
lemma gate_rep {w : List Sig} (hw : ∀ a ∈ w, Valid a) (g : Gate)
    (h : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    represented w (gv w g) ∨ witness (negative g) w (gv w g) := by
  obtain ⟨o, l⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  obtain ⟨ho, hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.2.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2.2 rfl)
  have nx (a : Sig) (hva : Valid a) (ha : represented w a) :
      represented w (neg a) ∨ witness true w (neg a) := by
    rcases operand_cases hva ha with rfl | rfl | ⟨hm, hp⟩
    · exact Or.inl (neg_laws.1 ▸ ro)
    · exact Or.inl (neg_laws.2 ▸ rz)
    · exact Or.inr (Or.inl ⟨rfl, a, hm, hp, rfl⟩)
  cases l with
  | nil =>
    rcases ho with rfl | rfl | rfl
    · exact Or.inl ro
    · exact Or.inl rz
    · exact nx _ valid_zero rz
  | cons i l =>
    cases l with
    | nil =>
      rcases ho with rfl | rfl | rfl
      · simpa only [negative, gv, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
          (bin_laws (valid_getD hw i)).1] using Or.inl (b := witness false w (w.getD i zero)) (get_rep w i)
      · simpa only [negative, gv, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
          (bin_laws (valid_getD hw i)).2.1] using Or.inl (b := witness false w (w.getD i zero)) (get_rep w i)
      · exact nx _ (valid_getD hw i) (get_rep w i)
    | cons j l =>
      cases l with
      | cons _ _ => simp at hl
      | nil =>
        rcases ho with rfl | rfl | rfl
        · simpa only [negative, gv, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
            (bin_laws (valid_getD hw j)).1] using
            bin_rep false (valid_getD hw i) (valid_getD hw j) (get_rep w i) (get_rep w j)
        · simpa only [negative, gv, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
            (bin_laws (valid_getD hw j)).2.1] using
            bin_rep true (valid_getD hw i) (valid_getD hw j) (get_rep w i) (get_rep w j)
        · exact nx _ (valid_getD hw i) (get_rep w i)
lemma pull_gate {isNeg : Bool} {w : List Sig} {z : Sig} {k t S} (h : Live k t S)
    (hz : represented w z ∨ witness isNeg w z) (sub : ∀ a ∈ S, a ∈ w ++ [z]) :
    ∃ k' t' S', k' ≤ k + 1 ∧ t' ≤ t + isNeg.toNat ∧ k' - t' ≤ k - t + (!isNeg).toNat ∧ Live k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k, t, S, by omega, by omega, by omega, h, ?_⟩
      intro a ha
      rcases (by simpa using sub a ha : a ∈ w ∨ a = z) with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨rfl, a, ha, hp', eq⟩ | ⟨rfl, d, a, b, ha, hb, pa, pb, hab, eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (neg a)
        have ht : Live k t (insert (neg a) U) := by simpa [U, Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv; obtain ⟨hne, hm⟩ := Finset.mem_erase.mp hv; simpa [hne] using sub v hm
        have hf : neg a ∉ insert a U := by
          intro hh; rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_, _, _, Nat.le_refl _, by simp, by simp, Live.unary hp' hf ht, by simpa using And.intro ha hu⟩
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live k t (insert (bin d a b) U) := by simpa [U, Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv; obtain ⟨hne, hm⟩ := Finset.mem_erase.mp hv; simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh; rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_, _, _, Nat.le_refl _, by simp, by simp; omega, Live.binary pa pb hab hf ht,
          by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k, t, S, by omega, by omega, by omega, h, ?_⟩
    intro a ha; have hn : a ≠ z := fun hh => hm (hh ▸ ha); simpa [hn] using sub a ha
lemma extract (gs : List Gate) (w : List Sig) (hw : ∀ a ∈ w, Valid a)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hout : target ∈ execute gs w) :
    ∃ k t S, k ≤ gs.length ∧ t ≤ (gs.filter negative).length ∧ k - t ≤ (gs.filter (fun g => !negative g)).length ∧ Live k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0, 0, {target}, by simp, by simp, by simp, Live.stop, by simpa [execute] using hout⟩
  | cons g gs ih =>
    have hw' : ∀ a ∈ w ++ [gv w g], Valid a := by
      intro a ha; rcases List.mem_append.mp ha with ha | ha
      · exact hw a ha
      · simp only [List.mem_singleton] at ha; exact ha ▸ gv_valid hw g
    obtain ⟨k, t, S, hk, hn, hb, ht, hs⟩ := ih (w ++ [gv w g]) hw' (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l, u, T, hl, hun, hub, hu, hT⟩ := pull_gate ht (gate_rep hw g (legal g (by simp))) hs
    refine ⟨l, u, T, by simp; omega, ?_, ?_, hu, hT⟩
    · cases e : negative g <;> simp [e] at hun ⊢ <;> omega
    · cases e : negative g <;> simp [e] at hub ⊢ <;> omega
def bit (side : Bool) (i : Fin 414) (a : Sig) : Bool :=
  (if side then a.1 else a.2).testBit i.val
lemma bit_zero (s i) : bit s i zero = false := by cases s <;> simp [bit, zero]
lemma bit_one (s i) : bit s i one = true := by
  cases s <;> simp [bit, one, testBit_top, i.isLt]
lemma bit_neg (s i) {a : Sig} (ha : Valid a) : bit s i (neg a) = !(bit s i a) := by
  cases s
  · simp [bit, neg, testBit_bnot ha.2, i.isLt]
  · simp [bit, neg, testBit_bnot ha.1, i.isLt]
lemma bit_bin (s i d) (a b : Sig) : bit s i (bin d a b) =
    (if d then bit s i a || bit s i b else bit s i a && bit s i b) := by
  cases s <;> cases d <;> simp [bit, bin, Nat.testBit_and, Nat.testBit_or]
lemma b_read (s i) (w : List Sig) (j : Nat) :
    (w.map (bit s i)).getD j false = bit s i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _ _).symm
  | some a => rfl
lemma run_bit (s i) (g : Gate) (w : List Sig) (hw : ∀ a ∈ w, Valid a)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    bit s i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit s i)).getD j false) := by
  obtain ⟨o, l⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _ _
    | cons a l ih =>
      change bit s i (bin false _ _) = (_ && _)
      rw [bit_bin]; exact congrArg (fun x => bit s i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _ _
    | cons a l ih =>
      change bit s i (bin true _ _) = (_ || _)
      rw [bit_bin]; exact congrArg (fun x => bit s i (w.getD a zero) || x) ih
  · cases l with
    | nil => exact (bit_neg s i valid_zero).trans (by rw [bit_zero]; rfl)
    | cons a l => exact bit_neg s i (valid_getD hw a)
lemma execute_bits (gs : List Gate) (s i) (w : List Sig) (hw : ∀ a ∈ w, Valid a)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit s i) =
    gs.foldl (fun (l : List Bool) g => l ++ [g.op.eval (g.inputs.map fun j => l.getD j false)])
      (w.map (bit s i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have hw' : ∀ a ∈ w ++ [gv w g], Valid a := by
      intro a ha; rcases List.mem_append.mp ha with ha | ha
      · exact hw a ha
      · simp only [List.mem_singleton] at ha; exact ha ▸ gv_valid hw g
    change (execute gs (w ++ [gv w g])).map _ = _
    rw [ih _ hw' (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons, List.map_append, List.map_singleton, run_bit s i g w hw (hg g (by simp))]
lemma foldl_append_getD {α : Type} (f : List α → Gate → α) (gs : List Gate)
    (l : List α) (i : Nat) (hi : i < l.length) (d : α) :
    (gs.foldl (fun acc g => acc ++ [f acc g]) l).getD i d = l.getD i d := by
  induction gs generalizing l with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (l ++ [f l g]).length := by simp; omega
    rw [ih (l ++ [f l g]) hlt]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
def raw0 : Sig := (0xc4000000000000000003fffffc000000003ffc210fe00847f007e01f83e01107e03e042084423f0fc3c08220842122287e3e0f, 0x15115115115115115115115115115115115100007e00003f003e00f83e00003e01e000000001f0fc3c00000000000003e3e07)
def raw1 : Sig := (0x10c000000000000003ffc000000000003ffffffe0f82017c010fc20208423f0fc21e208410884411044517e1f805f05e7c20279, 0x208e08e08e08e08e08e08e08e08e08e08e08fe0f80007c0007c00000001f0fc01e000000000000000007e1f801f01e7c00038)
def raw2 : Sig := (0x218000000000003ffc000000000003fffffc000421043f883ff880041084422084244fc027c3e022ffc0f84010be21e40847fd0, 0xc50c50c50c50c50c50c50c50c50c50c50c50000001f803ff8000000000000000007c007c3e000ffc0f800003e01e00003fc0)
def raw3 : Sig := (0x430000000003ffc000000000003fffffc00000084208421082110448ffc0044fffe00109f90089ff08802085ffc800897ffc480, 0x1a41a41a41a41a41a41a41a41a41a41a41a400000000000000000ffc0000fffe00001f80001ff00000001ffc000007ffc000)
def raw4 : Sig := (0x60000000000000000000003fffffc000000003ff0101fffc400083f21081ff1084087fe4003fe441008fffe210001ff9088802, 0x2a4aa4aa4aa4aa4aa4aa4aa4aa4aa4aa4aa4bff0001fffc000003f00001ff0000007fe0003fe000000fffe000001ff8000000)
def raw5 : Sig := (0x2883ffc003ffc000000003ffc0000000000000010842084210822109042108882108917fffffc00802010fffffffffe000101004, 0x6c06c06c06c06c06c06c06c06c06c06c06c0000000000000000000000000000007fffffc00000000fffffffffe000000000)
def raw6 : Sig := (0x1100003ffc000000003ffc0000000000000000021084108421044213ffffff004001007ffffffffffffff0100400040102000020, 0x3703703703703703703703703703703703700000000000000003fffffe000000007ffffffffffffff0000000000000000000)
def raw7 : Sig := (0xa00000003ffc003ffc000000000000000000003ffffff0002080003ffffffffffffffa108211000041004208821085000002100, 0x3383383383383383383383383383383383383fffffe0000000003ffffffffffffff8000000000000000000000000000000000)
def raw8 : Sig := (0x3403fffffc003ffc000000000000000000000003fffffffffffffffe084210008210004210422110882228411042108004210000, 0x3c03c03c03c03c03c03c03c03c03c03c03c03fffffffffffffffc000000000000000000000000000000000000000000000000)
def raw : List Sig := [raw0, raw1, raw2, raw3, raw4, raw5, raw6, raw7, raw8]
def sample (s : Bool) (i : Fin 414) (j : Fin 9) : Bool :=
  bit s i (raw.getD j.val zero)
def edgeF (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
set_option maxRecDepth 20000 in
lemma sample_ok : ∀ (s : Bool) (i : Fin 414), edgeF (sample s i) = s := by decide +kernel
lemma raw_id : List.ofFn (fun j : Fin 9 => raw.getD j.val zero) = raw := rfl
lemma sample_list (s i) : List.ofFn (sample s i) = raw.map (bit s i) := by
  calc
    _ = (List.ofFn (fun j : Fin 9 => raw.getD j.val zero)).map (bit s i) := by
      rw [List.map_ofFn]; rfl
    _ = _ := by rw [raw_id]
lemma raw_lt : raw.all (fun a => decide (a.1 ≤ top ∧ a.2 ≤ top)) = true := by decide +kernel
lemma raw_valid : ∀ a ∈ raw, Valid a := by
  intro a ha
  have h := of_decide_eq_true (List.all_eq_true.mp raw_lt a ha)
  exact ⟨valid1_of_le_top h.1, valid1_of_le_top h.2⟩
lemma raw_nd : raw.Nodup := by unfold raw; decide +kernel
lemma every_input : raw.all (fun a => unionSep true (raw.erase a) != top) = true := by decide +kernel
lemma necessary {k t S} (l : Live k t S) (hs : ∀ a ∈ S, a ∈ raw) : raw.toFinset = S := by
  ext a
  rw [List.mem_toFinset]
  refine ⟨fun hr => ?_, hs a⟩
  by_contra hn
  have fail := List.all_eq_true.mp every_input a hr
  have cov : unionSep true (raw.erase a) = top := by
    apply Nat.eq_of_testBit_eq; intro i
    rw [testBit_top]
    by_cases hi : i < 414
    · simp only [hi, decide_true]
      obtain ⟨b, hb, h⟩ := live_sep l i hi
      have ba : b ≠ a := fun he => hn (he ▸ hb)
      have hm := (List.mem_erase_of_ne ba).mpr (hs _ hb)
      exact (mem_unionSep true _ _).2 ⟨b, hm, sep_weaken _ (live_proper l b hb).1 i hi h⟩
    · simp only [hi, decide_false]
      exact valid_unionSep (fun x hx => raw_valid x (List.mem_of_mem_erase hx)) i (by omega)
  simp [cov] at fail
lemma execute_valid (gs : List Gate) (w : List Sig) (hw : ∀ a ∈ w, Valid a) :
    ∀ a ∈ execute gs w, Valid a := by
  induction gs generalizing w with
  | nil => exact hw
  | cons g gs ih =>
    apply ih (w ++ [gv w g])
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hw a ha
    · simp only [List.mem_singleton] at ha; exact ha ▸ gv_valid hw g

def baseWires := raw ++ [bin false raw0 raw3]
def start (a b : Fin 11) := baseWires ++ [bin true (baseWires.getD a.val zero) (baseWires.getD b.val zero)]

theorem prefixValid : ∀ v ∈ baseWires, Valid v := by
  intro v hv
  rcases List.mem_append.mp hv with old | last
  · exact raw_valid _ old
  · obtain rfl : v = bin false raw0 raw3 := by simpa using last
    exact valid_bin (raw_valid _ (by simp [raw])) (raw_valid _ (by simp [raw]))

theorem startValid (a b : Fin 11) : ∀ v ∈ start a b, Valid v := by
  intro v hv
  rcases List.mem_append.mp hv with old | last
  · exact prefixValid _ old
  · obtain rfl : v = bin true (baseWires.getD a.val zero) (baseWires.getD b.val zero) := by simpa using last
    exact valid_bin (valid_getD prefixValid _) (valid_getD prefixValid _)

theorem baseBit (s : Bool) (i : Fin 414) (j : Fin 11) :
    bit s i (baseWires.getD j.val zero) = PetersenBinary.base (sample s i) j := by
  fin_cases j <;> first | rfl | exact bit_bin s i false raw0 raw3 | exact bit_zero _ _

theorem startBits (s : Bool) (i : Fin 414) (a b : Fin 11) :
    (start a b).map (bit s i) = List.ofFn (PetersenBinary.signals a b (sample s i)) := by
  have atIndex (j : Fin 11) : bit s i ((start a b).getD j.val zero) =
      PetersenBinary.signals a b (sample s i) j := by
    fin_cases j <;> first | rfl | exact bit_bin s i false raw0 raw3 |
      (change bit s i (bin true (baseWires.getD a.val zero) (baseWires.getD b.val zero)) = _;
       rw [bit_bin, baseBit, baseBit]; rfl)
  apply List.ext_getElem
  · simp [start,baseWires,raw]
  · intro j hj _
    have small : j < 11 := by simpa [start,baseWires,raw] using hj
    have hsrc : j < (start a b).length := by simpa using hj
    have h := atIndex ⟨j, small⟩
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hsrc, Option.getD_some] at h
    simpa only [List.getElem_map, List.getElem_ofFn] using h

theorem member (a b : Fin 11) (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x, C.eval (List.ofFn (PetersenBinary.signals a b x)) = edgeF x) :
    target ∈ execute C.gates (start a b) := by
  let w := execute C.gates (start a b)
  have hwv : ∀ z ∈ w, Valid z := execute_valid C.gates _ (startValid _ _)
  have hproj (s : Bool) (i : Fin 414) : bit s i (w.getD C.output zero) = s := by
    rw [← b_read]
    change ((execute C.gates (start a b)).map _).getD C.output false = _
    rw [execute_bits _ _ _ _ (startValid _ _) (fun g hg => (h g hg).1),startBits]
    have eq := he (sample s i)
    rw [sample_ok] at eq
    exact eq
  have hvout : Valid (w.getD C.output zero) := valid_getD hwv C.output
  have et : w.getD C.output zero = target := by
    apply Prod.ext
    · apply Nat.eq_of_testBit_eq; intro i
      rw [target, testBit_top]
      by_cases hi : i < 414
      · simpa [bit, hi] using hproj true ⟨i, hi⟩
      · rw [hvout.1 i (by omega)]; simp [hi]
    · apply Nat.eq_of_testBit_eq; intro i
      by_cases hi : i < 414
      · simpa [bit, target] using hproj false ⟨i, hi⟩
      · rw [hvout.2 i (by omega), target]; exact (Nat.zero_testBit i).symm
  have rep := get_rep w C.output
  rw [et] at rep
  exact rep.resolve_right (fun hn => hn target_proper)

theorem boundedSearch (C : Circuit) (ins : List (Fin 11)) (arity : ins.length ≤ 2)
    (fan : PEqualNP.MetaComplexity.FanInTwo C) (budget : C.size ≤ 13)
    (right : ∀ x : Fin 9 → Bool, C.eval (PetersenBinary.orderedInputs x ++
      [GateOp.or.eval (ins.map (fun j => (PetersenBinary.orderedInputs x).getD j.val false))]) = edgeF x) :
    ∃ (a b : Fin 11) (k t : ℕ) (S : Finset Sig), a ≤ b ∧ k ≤ 13 ∧ t ≤ 5 ∧
      S ⊆ (start a b).toFinset ∧ Live k t S := by
  let a := ins.getD 0 10
  let b := ins.getD 1 10
  have eq : ∀ x, C.eval (List.ofFn (PetersenBinary.signals a b x)) = edgeF x :=
    fun x => by rw [PetersenBinary.signal_list _ _ arity]; exact right x
  obtain ⟨k,t,S,hk,ht,_,live,sub⟩ := extract C.gates (start a b) (startValid a b) fan (member a b C fan eq)
  have limit := PetersenBinary.fiveNotLimit C ins arity fan budget right
  have identical : negative = PetersenBinary.negGate := by funext g; cases g with | mk op l => cases op <;> rfl
  rw [identical] at ht
  have bound := le_trans hk budget
  have ht' := le_trans ht limit
  have sub' : S ⊆ (start a b).toFinset := fun z hz => List.mem_toFinset.mpr (sub _ hz)
  by_cases sorted : a ≤ b
  · exact ⟨a,b,k,t,S,sorted,bound,ht',sub',live⟩
  · have same : start b a = start a b := by simp [start,bin,Nat.or_comm]
    exact ⟨b,a,k,t,S,le_of_not_ge sorted,bound,ht',same ▸ sub',live⟩

def finiteObligation : Prop :=
  ∀ (a b : Fin 11) (k t : ℕ) (S : Finset Sig), a ≤ b → k ≤ 13 → t ≤ 5 →
    S ⊆ (start a b).toFinset → ¬ Live k t S

/-- The finite obligation implies the exact positive twin of desk step L-meta-1869. -/
theorem lowerBoundOfFiniteObligation (checked : finiteObligation) : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List (Fin (11 : ℕ))),   PEqualNP.MetaComplexity.FanInTwo x1 →     x2.length ≤ (2 : ℕ) →       (∀ (x5 : Fin (9 : ℕ) → Bool),           have x6 : List Bool := List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ))];           x1.eval (x6 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x7 : Fin (11 : ℕ)) => x6.getD (↑x7) Bool.false) x2)]) = (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))) →         (14 : ℕ) ≤ x1.size := by
  intro C ins fan arity right
  by_contra! short
  have budget : C.size ≤ 13 := by omega
  obtain ⟨a,b,k,t,S,order,hk,ht,sub,live⟩ := boundedSearch C ins arity fan budget right
  exact checked a b k t S order hk ht sub live

end PetersenSearch
