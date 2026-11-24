import Mathlib
import PEqualNP.Defs

/-!
A monotone suffix for L-meta-1869 can discard its first AND. No minimal
positive input contains both vertices 0 and 3. The shortened circuit keeps
the second OR, renumbers every later wire, and has exactly one more gate
than the suffix. The proof covers repeated and out-of-range operands.
-/
namespace PetersenNonedge
open PEqualNP.CircuitLowerBounds

def edges : List (Fin 9 × Fin 9) :=
  [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]

def edge (x : Fin 9 → Bool) : Bool :=
  edges.any fun e => x e.1 && x e.2

def pair (e : Fin 9 × Fin 9) (i : Fin 9) : Bool := decide (i = e.1 ∨ i = e.2)

theorem pinned_false_on_edges : ∀ e ∈ edges, (pair e 0 && pair e 3) = false := by decide

/-- A monotone continuation on the original inputs and the forced gate can
discard AND(0,3) wherever that precomputed value is read. -/
theorem eraseExtra (F : (Fin 9 → Bool) → Bool → Bool)
    (mono : ∀ {x y : Fin 9 → Bool} {s t : Bool}, (∀ i, x i ≤ y i) → s ≤ t → F x s ≤ F y t)
    (right : ∀ x, F x (x 0 && x 3) = edge x) : ∀ x, F x false = edge x := by
  intro x
  apply le_antisymm
  · rw [← right x]
    exact mono (fun _ => le_rfl) (by simp)
  · cases hx : edge x with
    | false => simp
    | true =>
      obtain ⟨e, he, ha⟩ := List.any_eq_true.mp hx
      have inside : ∀ i, pair e i ≤ x i := by
        intro i
        by_cases h : i = e.1 ∨ i = e.2
        · have hp := Bool.and_eq_true_iff.mp ha
          rcases h with rfl | rfl <;> simp [hp.1, hp.2]
        · simp [pair,h]
      have hedge : edge (pair e) = true := by
        exact List.any_eq_true.mpr ⟨e, he, by simp [pair]⟩
      have hf := right (pair e)
      rw [pinned_false_on_edges e he, hedge] at hf
      rw [← hf]
      exact mono inside le_rfl


-- The circuit monotonicity induction follows the project LowMergeWires proof.
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def LeL (a b : List Bool) : Prop := ∀ i, a.getD i false = true → b.getD i false = true

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
    (f f' : ℕ → Bool) (h : ∀ i, f i = true → f' i = true) :
    op.eval (l.map f) = true → op.eval (l.map f') = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
    intro H x hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact h i (H (f i) ⟨i, hi, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨x, ⟨i, hi, rfl⟩, hx⟩
    exact ⟨f' i, ⟨i, hi, rfl⟩, h i hx⟩

theorem fold_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ a b : List Bool, a.length = b.length → LeL a b →
      LeL (gs.foldl step a) (gs.foldl step b) := by
  induction gs with
  | nil => intro a b _ h; exact h
  | cons g gs ih =>
    intro a b hl h
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    · simp [step, hl]
    · intro i hi
      unfold step at hi ⊢
      by_cases hia : i < a.length
      · rw [List.getD_append _ _ _ _ hia] at hi
        rw [List.getD_append _ _ _ _ (by omega)]
        exact h i hi
      · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
        rw [List.getD_append_right _ _ _ _ (by omega)]
        rw [← hl]
        by_cases he : i - a.length = 0
        · rw [he] at hi ⊢
          simp only [List.getD_cons_zero] at hi ⊢
          exact eval_mono g.op (hgs g List.mem_cons_self) _ _ _ (fun k => h k) hi
        · obtain ⟨m, hm⟩ : ∃ m, i - a.length = m + 1 := ⟨i - a.length - 1, by omega⟩
          rw [hm] at hi; simp at hi


def feed (x : Fin 9 → Bool) (b : Bool) := List.ofFn x ++ [b]

theorem boolLe {a b : Bool} : a ≤ b ↔ (a = true → b = true) := by
  cases a <;> cases b <;> decide

theorem feedLe {x y : Fin 9 → Bool} {s t : Bool} (h : ∀ j, x j ≤ y j) (hst : s ≤ t) :
    LeL (feed x s) (feed y t) := by
  intro i hi
  by_cases small : i < 9
  · have rd (f : Fin 9 → Bool) (v : Bool) : (feed f v).getD i false = f ⟨i,small⟩ := by
      unfold feed
      rw [List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using small)]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left small, Option.getD_some]
    rw [rd] at hi ⊢
    exact boolLe.mp (h _) hi
  · by_cases last : i = 9
    · subst i
      simpa [feed] using boolLe.mp hst (by simpa [feed] using hi)
    · rw [List.getD_eq_default] at hi
      · contradiction
      · simp [feed]; omega

def augmented (C : Circuit) (ins : List (Fin 11)) (x : Fin 9 → Bool) (b : Bool) :=
  let w := feed x b
  C.eval (w ++ [GateOp.or.eval (ins.map (fun j => w.getD j.val false))])

theorem erasePinnedInCircuit (C : Circuit) (ins : List (Fin 11))
    (monotone : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (correct : ∀ x, augmented C ins x (x 0 && x 3) = edge x) :
    ∀ x, augmented C ins x false = edge x := by
  apply eraseExtra (augmented C ins) _ correct
  intro x y s t h hst
  let g : Gate := ⟨GateOp.or, ins.map Fin.val⟩
  apply boolLe.mpr
  have H := fold_mono (g :: C.gates) (by
    intro a ha
    rcases List.mem_cons.mp ha with rfl | mem
    · exact Or.inr rfl
    · exact monotone a mem) (feed x s) (feed y t) (by simp [feed]) (feedLe h hst)
  have gateEq (w : List Bool) : step w g = w ++ [GateOp.or.eval (ins.map fun j => w.getD j.val false)] := by
    simp [step, g, List.map_map, Function.comp_def]
  have out := H C.output
  change (C.gates.foldl step (step (feed x s) g)).getD C.output false = true →
    (C.gates.foldl step (step (feed y t) g)).getD C.output false = true at out
  rw [gateEq, gateEq] at out
  exact out


def renumber (slot dead i : ℕ) : ℕ :=
  if i < slot then i else if i = slot then dead else i - 1

def shiftGate (slot dead : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (renumber slot dead)⟩

theorem read_shift (left right : List Bool) (dead i : ℕ)
    (safe : left.length + right.length ≤ dead) :
    (left ++ false :: right).getD i false =
      (left ++ right).getD (renumber left.length dead i) false := by
  by_cases h : i < left.length
  · simp only [renumber, ite_eq_left h, List.getD_append _ _ _ _ h]
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    by_cases e : i = left.length
    · subst i
      simp only [renumber, lt_irrefl, ite_false, ite_eq_left, Nat.sub_self, List.getD_cons_zero]
      rw [List.getD_eq_default _ _ (by simp; omega)]
    · have pos : i - left.length = (i - 1 - left.length) + 1 := by omega
      rw [pos]
      simp only [List.getD_cons_succ, renumber, ite_eq_right h, ite_eq_right e]
      rw [List.getD_append_right _ _ _ _ (by omega)]

theorem folded_shift (gs : List Gate) (left right : List Bool) (dead : ℕ)
    (safe : left.length + right.length + gs.length ≤ dead) :
    ∃ last : List Bool, last.length = right.length + gs.length ∧
      gs.foldl step (left ++ false :: right) = left ++ false :: last ∧
      (gs.map (shiftGate left.length dead)).foldl step (left ++ right) = left ++ last := by
  induction gs generalizing right with
  | nil => exact ⟨right, by simp, rfl, rfl⟩
  | cons g gs ih =>
    let bit := g.op.eval (g.inputs.map fun i => (left ++ false :: right).getD i false)
    have eq : (shiftGate left.length dead g).op.eval
        ((shiftGate left.length dead g).inputs.map (fun i => (left ++ right).getD i false)) = bit := by
      apply congrArg g.op.eval
      simp only [shiftGate, List.map_map]
      apply List.map_congr_left
      intro i _
      exact (read_shift left right dead i (by omega)).symm
    have lim : left.length + (right ++ [bit]).length + gs.length ≤ dead := by
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using safe
    obtain ⟨last, length, original, shifted⟩ := ih (right ++ [bit]) lim
    refine ⟨last, by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using length, ?_, ?_⟩
    · simpa only [List.foldl_cons, step, bit, List.append_assoc, List.cons_append] using original
    · simp only [List.map_cons, List.foldl_cons, step, eq, List.append_assoc]
      exact shifted

theorem shorten (C : Circuit) (ins : List (Fin 11)) (arity : ins.length ≤ 2)
    (fan : PEqualNP.MetaComplexity.Monotone2 C)
    (correct : ∀ x, augmented C ins x (x 0 && x 3) = edge x) :
    ∃ D : Circuit, D.size = C.size + 1 ∧ PEqualNP.MetaComplexity.Monotone2 D ∧
      ∀ x : Fin 9 → Bool, D.eval (List.ofFn x) = edge x := by
  let g : Gate := ⟨GateOp.or, ins.map Fin.val⟩
  let gs := g :: C.gates
  let dead := 9 + gs.length
  let D : Circuit := ⟨gs.map (shiftGate 9 dead), renumber 9 dead C.output⟩
  refine ⟨D, ?_, ?_, ?_⟩
  · simp [D, gs, Circuit.size]
  · intro h hm
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
    have orig : a.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ a.inputs.length ≤ 2 := by
      rcases List.mem_cons.mp ha with rfl | mem
      · exact ⟨by simp [g], by simpa [g] using arity⟩
      · exact fan a mem
    simpa only [shiftGate, List.length_map] using orig
  · intro x
    have mono : ∀ a ∈ C.gates, a.op = GateOp.and ∨ a.op = GateOp.or := fun a ha => (fan a ha).1
    have h := erasePinnedInCircuit C ins mono correct x
    have lo := folded_shift gs (List.ofFn x) [] dead (by simp [dead])
    obtain ⟨last, len, old, new⟩ := lo
    simp only [List.length_ofFn, List.append_nil, List.length_nil, Nat.zero_add] at len old new
    change ((gs.map (shiftGate 9 dead)).foldl step (List.ofFn x)).getD (renumber 9 dead C.output) false = _
    rw [new]
    have lookup := read_shift (List.ofFn x) last dead C.output (by simp [len,dead])
    rw [List.length_ofFn] at lookup
    rw [←lookup, ←old]
    change (C.gates.foldl step (step (feed x false) g)).getD C.output false = _
    have hg : step (feed x false) g = feed x false ++
        [GateOp.or.eval (ins.map fun j => (feed x false).getD j.val false)] := by
      simp [step, g, List.map_map, Function.comp_def]
    rw [hg]
    exact h

end PetersenNonedge
