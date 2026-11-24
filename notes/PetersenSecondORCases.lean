import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_1672

/-!
Lower bounds for the second OR after AND(0,3). The last three theorems
use the project’s checked L-meta-1672 certificate by jmwalsh96 (PR 4290).
They exclude all monotone suffixes and 23 second-OR choices for arbitrary
AND/OR/NOT suffixes of at most thirteen gates.

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

namespace PetersenPadding
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def move (n i : ℕ) := if i < n then i else i + 1

def shifted (n : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (move n)⟩

theorem readMoved (left right : List Bool) (extra : Bool) (i : ℕ) :
    (left ++ extra :: right).getD (move left.length i) false = (left ++ right).getD i false := by
  by_cases h : i < left.length
  · simp only [move, ite_eq_left h, List.getD_append _ _ _ _ h]
  · have eq : i + 1 - left.length = (i - left.length) + 1 := by omega
    rw [move, ite_eq_right h, List.getD_append_right _ _ _ _ (by omega),
        List.getD_append_right _ _ _ _ (by omega), eq, List.getD_cons_succ]

theorem runMoved (gs : List Gate) (left right : List Bool) (extra : Bool) :
    ∃ rest, gs.foldl PetersenNonedge.step (left ++ right) = left ++ rest ∧
      (gs.map (shifted left.length)).foldl PetersenNonedge.step (left ++ extra :: right) =
        left ++ extra :: rest := by
  induction gs generalizing right with
  | nil => exact ⟨right,rfl,rfl⟩
  | cons g gs ih =>
    let out := g.op.eval (g.inputs.map fun i => (left ++ right).getD i false)
    have same : (shifted left.length g).op.eval ((shifted left.length g).inputs.map
        fun j => (left ++ extra :: right).getD j false) = out := by
      apply congrArg g.op.eval
      simp only [shifted, List.map_map, Function.comp_def, readMoved]
    obtain ⟨rest,old,new⟩ := ih (right ++ [out])
    refine ⟨rest,?_,?_⟩
    · simpa only [List.foldl_cons, PetersenNonedge.step, List.append_assoc, out] using old
    · simp only [List.map_cons,List.foldl_cons,PetersenNonedge.step,same,List.append_assoc,List.cons_append]
      exact new

def pad (D : Circuit) : Circuit :=
  ⟨⟨GateOp.and,[4,6]⟩ :: D.gates.map (shifted 9), move 9 D.output⟩

theorem padFan (D : Circuit) (fan : FanInTwo D) : FanInTwo (pad D) := by
  intro g hg
  rcases List.mem_cons.mp hg with rfl | old
  · exact ⟨by simp, by decide⟩
  · obtain ⟨h,hh,rfl⟩ := List.mem_map.mp old
    simpa only [shifted,List.length_map] using fan h hh

theorem padFacts (D : Circuit) (x : Fin 9 → Bool) :
    ((pad D).wires (List.ofFn x)).getD 9 false = (x 4 && x 6) ∧
      (pad D).eval (List.ofFn x) = D.eval (List.ofFn x) := by
  let extra := x 4 && x 6
  obtain ⟨rest,old,new⟩ := runMoved D.gates (List.ofFn x) [] extra
  simp only [List.length_ofFn,List.append_nil] at old new
  have first : PetersenNonedge.step (List.ofFn x) ⟨GateOp.and,[4,6]⟩ = List.ofFn x ++ [extra] := by
    simp [PetersenNonedge.step,GateOp.eval,extra]
  have all : (pad D).wires (List.ofFn x) = List.ofFn x ++ extra :: rest := by
    change (D.gates.map (shifted 9)).foldl PetersenNonedge.step
      (PetersenNonedge.step (List.ofFn x) ⟨GateOp.and,[4,6]⟩) = _
    rw [first]; exact new
  constructor
  · rw [all, List.getD_append_right _ _ _ _ (by simp)]; simp [extra]
  · change ((pad D).wires (List.ofFn x)).getD (move 9 D.output) false =
      (D.gates.foldl PetersenNonedge.step (List.ofFn x)).getD D.output false
    rw [all,old]
    simpa using readMoved (List.ofFn x) rest extra D.output

theorem ordinaryLower (known : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 && y 6)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) (D : Circuit) (fan : FanInTwo D)
    (right : ∀ x : Fin 9 → Bool, D.eval (List.ofFn x) = PetersenNonedge.edge x) : 15 ≤ D.size := by

  have lower := known (pad D) (padFan D fan) (fun y => (padFacts D y).1) (by
    funext x
    change (pad D).eval (List.ofFn x) = _
    rw [(padFacts D x).2, right]
    simp [PetersenNonedge.edge,PetersenNonedge.edges,Bool.or_assoc])
  simp only [pad,Circuit.size,List.length_cons,List.length_map] at lower
  change 15 ≤ D.gates.length
  omega

theorem monotoneLower (known : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 && y 6)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) (C : Circuit) (ins : List (Fin 11))
    (arity : ins.length ≤ 2) (mono : Monotone2 C)
    (right : ∀ x, PetersenNonedge.augmented C ins x (x 0 && x 3) = PetersenNonedge.edge x) :
    14 ≤ C.size := by
  obtain ⟨D,size,fan,correct⟩ := PetersenNonedge.shorten C ins arity mono right
  have weak : FanInTwo D := by
    intro g mem
    obtain ⟨op,n⟩ := fan g mem
    change g.op = GateOp.and ∨ g.op = GateOp.or at op
    exact ⟨op.imp_right Or.inl,n⟩
  have bound := ordinaryLower known D weak correct
  omega
end PetersenPadding

namespace PetersenAlias
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PetersenNonedge

/-- A wire can be deleted when it agrees with an existing input throughout
the computation, including the default-false wire beyond the final buffer. -/
theorem readAlias (left right : List Bool) (extra : Bool) (i aliasIdx : ℕ)
    (aliasEq : (left ++ right).getD aliasIdx false = extra) :
    (left ++ extra :: right).getD i false =
      (left ++ right).getD (renumber left.length aliasIdx i) false := by
  by_cases h : i < left.length
  · simp only [renumber, ite_eq_left h, List.getD_append _ _ _ _ h]
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    by_cases e : i = left.length
    · subst i
      simp only [renumber,lt_irrefl,ite_false,ite_eq_left,Nat.sub_self,List.getD_cons_zero]
      exact aliasEq.symm
    · have pos : i - left.length = (i - 1 - left.length) + 1 := by omega
      rw [pos]
      simp only [List.getD_cons_succ,renumber,ite_eq_right h,ite_eq_right e]
      rw [List.getD_append_right _ _ _ _ (by omega)]

theorem runAlias (gs : List Gate) (left right : List Bool) (extra : Bool) (aliasIdx : ℕ)
    (h : ∀ tail : List Bool, tail.length ≤ gs.length →
      (left ++ (right ++ tail)).getD aliasIdx false = extra) :
    ∃ rest : List Bool, rest.length = right.length + gs.length ∧
      gs.foldl step (left ++ extra :: right) = left ++ extra :: rest ∧
      (gs.map (shiftGate left.length aliasIdx)).foldl step (left ++ right) = left ++ rest := by
  induction gs generalizing right with
  | nil => exact ⟨right,by simp,rfl,rfl⟩
  | cons g gs ih =>
    let out := g.op.eval (g.inputs.map fun i => (left ++ extra :: right).getD i false)
    have aliasNow : (left ++ right).getD aliasIdx false = extra := by simpa using h [] (by simp)
    have eq : (shiftGate left.length aliasIdx g).op.eval
        ((shiftGate left.length aliasIdx g).inputs.map (fun i => (left ++ right).getD i false)) = out := by
      apply congrArg g.op.eval
      simp only [shiftGate,List.map_map]
      apply List.map_congr_left
      intro i _
      exact (readAlias left right extra i aliasIdx aliasNow).symm
    have next (tail : List Bool) (ht : tail.length ≤ gs.length) :
        (left ++ ((right ++ [out]) ++ tail)).getD aliasIdx false = extra := by
      simpa [List.append_assoc] using h (out :: tail) (by simpa using ht)
    obtain ⟨rest,length,old,new⟩ := ih (right ++ [out]) next
    refine ⟨rest,by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using length,?_,?_⟩
    · simpa only [List.foldl_cons, step, out, List.append_assoc, List.cons_append] using old
    · simp only [List.map_cons,List.foldl_cons,step,eq,List.append_assoc]
      exact new

def wire (x : Fin 9 → Bool) := feed x (x 0 && x 3)
def extraOR (ins : List (Fin 11)) (x : Fin 9 → Bool) :=
  GateOp.or.eval (ins.map fun i => (wire x).getD i.val false)

theorem detach (C : Circuit) (ins : List (Fin 11)) (j : Fin 11) (fan : FanInTwo C)
    (aliasEq : ∀ x, extraOR ins x = (wire x).getD j.val false)
    (right : ∀ x, augmented C ins x (x 0 && x 3) = edge x) :
    ∃ D : Circuit, D.size = C.size + 1 ∧ FanInTwo D ∧
      ∀ x : Fin 9 → Bool, D.eval (List.ofFn x) = edge x := by
  let k := if j.val < 10 then j.val else 10 + C.gates.length
  let first : Gate := ⟨GateOp.and,[0,3]⟩
  let D : Circuit := ⟨first :: C.gates.map (shiftGate 10 k), renumber 10 k C.output⟩
  refine ⟨D,by simp [D,Circuit.size],?_,?_⟩
  · intro g hg
    rcases List.mem_cons.mp hg with rfl | mem
    · exact ⟨by simp [first],by decide⟩
    · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp mem
      simpa only [shiftGate,List.length_map] using fan a ha
  · intro x
    have wl : (wire x).length = 10 := by simp [wire,feed]
    have aliasAll (tail : List Bool) (len : tail.length ≤ C.gates.length) :
        (wire x ++ tail).getD k false = extraOR ins x := by
      rw [aliasEq]
      by_cases h : j.val < 10
      · simp only [k,ite_eq_left h]
        exact List.getD_append _ _ _ _ (by omega)
      · simp only [k,ite_eq_right h]
        rw [List.getD_eq_default _ _ (by simp [wl]; omega),List.getD_eq_default _ _ (by omega)]
    obtain ⟨rest,len,old,new⟩ := runAlias C.gates (wire x) [] (extraOR ins x) k (by simpa using aliasAll)
    simp only [wl,List.append_nil,List.length_nil,Nat.zero_add] at old new len
    have val := readAlias (wire x) rest (extraOR ins x) C.output k (aliasAll rest (by omega))
    rw [wl] at val
    have step1 : step (List.ofFn x) first = wire x := by simp [step,first,wire,feed,GateOp.eval]
    change ((C.gates.map (shiftGate 10 k)).foldl step (step (List.ofFn x) first)).getD (renumber 10 k C.output) false = _
    rw [step1,new,←val,←old]
    exact right x

/-- The ordered pairs satisfying this predicate have an OR already present
in the ten-wire prefix or equal to the default false value. -/
def redundant (a b : Fin 11) : Bool := decide (a = b ∨ b = 10 ∨ (b = 9 ∧ (a = 0 ∨ a = 3)))

theorem countRedundant :
    (((Finset.univ : Finset (Fin 11 × Fin 11)).filter
      (fun p => p.1 ≤ p.2 ∧ redundant p.1 p.2)).card) = 23 := by decide

theorem identify (a b : Fin 11) (hr : redundant a b = true) :
    ∃ j : Fin 11, ∀ x, extraOR [a,b] x = (wire x).getD j.val false := by
  refine ⟨a,?_⟩
  intro x
  have h : a = b ∨ b = 10 ∨ (b = 9 ∧ (a = 0 ∨ a = 3)) := of_decide_eq_true hr
  have st : extraOR [a,b] x = ((wire x).getD a.val false || (wire x).getD b.val false) := by
    simp [extraOR,GateOp.eval]
  rw [st]
  rcases h with rfl | rfl | ⟨rfl, h | h⟩
  · simp
  · simp [wire,feed]
  · subst a; simp [wire,feed]; grind
  · subst a; simp [wire,feed]

theorem aliasLower (known : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 && y 6)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) (a b : Fin 11) (h : redundant a b = true) (C : Circuit) (fan : FanInTwo C)
    (right : ∀ x, augmented C [a,b] x (x 0 && x 3) = edge x) : 14 ≤ C.size := by
  obtain ⟨j,id⟩ := identify a b h
  obtain ⟨D,size,full,ok⟩ := detach C [a,b] j fan id right
  have lower := PetersenPadding.ordinaryLower known D full ok
  omega
end PetersenAlias


namespace PetersenSecondOR
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PetersenNonedge

theorem anyCircuitNeedsFifteen (D : Circuit) (fan : FanInTwo D)
    (right : ∀ x : Fin 9 → Bool, D.eval (List.ofFn x) = edge x) : 15 ≤ D.size :=
  PetersenPadding.ordinaryLower PEqualNP.Outside.L_meta_1672 D fan right

theorem monotoneSuffixNeedsFourteen (C : Circuit) (ins : List (Fin 11)) (arity : ins.length ≤ 2)
    (fan : Monotone2 C) (right : ∀ x, augmented C ins x (x 0 && x 3) = edge x) : 14 ≤ C.size :=
  PetersenPadding.monotoneLower PEqualNP.Outside.L_meta_1672 C ins arity fan right

theorem redundantORSuffixNeedsFourteen (a b : Fin 11) (h : PetersenAlias.redundant a b = true)
    (C : Circuit) (fan : FanInTwo C)
    (right : ∀ x, augmented C [a,b] x (x 0 && x 3) = edge x) : 14 ≤ C.size :=
  PetersenAlias.aliasLower PEqualNP.Outside.L_meta_1672 a b h C fan right
end PetersenSecondOR

namespace PetersenOrbit
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PetersenNonedge

def perm (n : Fin 4) : Fin 9 → Fin 9 :=
  (![![0,1,2,3,4,5,6,7,8], ![0,5,8,3,4,1,7,6,2],
    ![3,2,1,0,4,8,7,6,5], ![3,8,5,0,4,2,6,7,1]] : Fin 4 → Fin 9 → Fin 9) n

def pin (x : Fin 9 → Bool) := x 0 && x 3

theorem preserved (n : Fin 4) (x : Fin 9 → Bool) :
    edge (x ∘ perm n) = edge x ∧ pin (x ∘ perm n) = pin x := by
  fin_cases n <;> constructor <;>
    simp [edge,edges,pin,perm,Bool.and_comm,
      Bool.or_comm,Bool.or_left_comm,Bool.or_assoc]

def addr (n : Fin 4) (j : ℕ) := if h : j < 9 then (perm n ⟨j,h⟩).val else j
def addr11 (n : Fin 4) (j : Fin 11) : Fin 11 :=
  ⟨addr n j.val,by unfold addr; split <;> omega⟩

theorem readAddr (n : Fin 4) (x : Fin 9 → Bool) (tail : List Bool) (j : ℕ) :
    (List.ofFn x ++ tail).getD (addr n j) false =
    (List.ofFn (x ∘ perm n) ++ tail).getD j false := by
  by_cases h : j < 9
  · have small : (perm n ⟨j,h⟩).val < 9 := (perm n ⟨j,h⟩).isLt
    simp only [addr,dite_eq_left h]
    rw [List.getD_append _ _ _ _ (by simp),List.getD_append _ _ _ _ (by simpa using h)]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_left small,dite_eq_left h,Option.getD_some,Function.comp_apply]
  · simp only [addr,dite_eq_right h]
    rw [List.getD_append_right _ _ _ _ (by simp; omega),List.getD_append_right _ _ _ _ (by simp; omega)]
    simp

def rg (n : Fin 4) (g : Gate) : Gate := ⟨g.op,g.inputs.map (addr n)⟩
def rc (n : Fin 4) (C : Circuit) : Circuit := ⟨C.gates.map (rg n),addr n C.output⟩

theorem run (n : Fin 4) (gs : List Gate) (x : Fin 9 → Bool) (tail : List Bool) :
    ∃ rest, gs.foldl step (List.ofFn (x ∘ perm n) ++ tail) = List.ofFn (x ∘ perm n) ++ rest ∧
      (gs.map (rg n)).foldl step (List.ofFn x ++ tail) = List.ofFn x ++ rest := by
  induction gs generalizing tail with
  | nil => exact ⟨tail,rfl,rfl⟩
  | cons g gs ih =>
    let out := g.op.eval (g.inputs.map fun j => (List.ofFn (x ∘ perm n) ++ tail).getD j false)
    have same : (rg n g).op.eval ((rg n g).inputs.map fun j => (List.ofFn x ++ tail).getD j false) = out := by
      apply congrArg g.op.eval
      simp only [rg,List.map_map,Function.comp_def,readAddr]
    obtain ⟨rest,old,new⟩ := ih (tail ++ [out])
    refine ⟨rest,?_,?_⟩
    · simpa only [List.foldl_cons,step,out,List.append_assoc] using old
    · simp only [List.map_cons,List.foldl_cons,step,same,List.append_assoc]; exact new

theorem evalRC (n : Fin 4) (C : Circuit) (x : Fin 9 → Bool) (tail : List Bool) :
    (rc n C).eval (List.ofFn x ++ tail) = C.eval (List.ofFn (x ∘ perm n) ++ tail) := by
  obtain ⟨rest,old,new⟩ := run n C.gates x tail
  change ((C.gates.map (rg n)).foldl step (List.ofFn x ++ tail)).getD (addr n C.output) false =
      (C.gates.foldl step (List.ofFn (x ∘ perm n) ++ tail)).getD C.output false
  rw [old,new,readAddr]

def ordered (a b : Fin 11) := (min a b,max a b)

def inputs (a b : Fin 11) (x : Fin 9 → Bool) :=
  let w := List.ofFn x ++ [pin x]
  List.ofFn x ++ [pin x, (w.getD a.val false || w.getD b.val false)]

def solves (a b : Fin 11) (C : Circuit) :=
  ∀ x : Fin 9 → Bool, C.eval (inputs a b x) = edge x

theorem transport (n : Fin 4) (a b : Fin 11) (C : Circuit) (h : solves a b C) :
    solves (ordered (addr11 n a) (addr11 n b)).1 (ordered (addr11 n a) (addr11 n b)).2 (rc n C) := by
  intro x
  obtain ⟨edgeEq,pinEq⟩ := preserved n x
  let aa := addr11 n a
  let bb := addr11 n b
  have sortEq : inputs (ordered aa bb).1 (ordered aa bb).2 x = inputs aa bb x := by
    rcases le_total aa bb with p | p
    · simp [ordered,min_eq_left p,max_eq_right p]
    · simp [ordered,min_eq_right p,max_eq_left p,inputs,Bool.or_comm]
  change (rc n C).eval (inputs (ordered aa bb).1 (ordered aa bb).2 x) = _
  rw [sortEq]
  unfold inputs
  rw [evalRC]
  change C.eval (List.ofFn (x ∘ perm n) ++ [pin x,
    ((List.ofFn x ++ [pin x]).getD (addr n a.val) false ||
     (List.ofFn x ++ [pin x]).getD (addr n b.val) false)]) = _
  rw [readAddr,readAddr,←pinEq]
  exact (h (x ∘ perm n)).trans edgeEq

def reps : Finset (Fin 11 × Fin 11) :=
  {(0,1),(0,2),(0,3),(0,4),(0,6),(1,2),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9),(4,6),(4,9),(6,7),(6,9)}

theorem sixteen : reps.card = 16 := by decide

set_option maxRecDepth 30000 in
set_option maxHeartbeats 3000000 in
theorem cover : ∀ a b : Fin 11, a ≤ b → PetersenAlias.redundant a b = false →
    ∃ n : Fin 4, ordered (addr11 n a) (addr11 n b) ∈ reps := by decide

theorem rcFan (n : Fin 4) (C : Circuit) (fan : FanInTwo C) : FanInTwo (rc n C) := by
  intro g hg
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hg
  simpa only [rg,List.length_map] using fan p hp

theorem coreBound (cert : ∀ p ∈ reps, ∀ C : Circuit, FanInTwo C → solves p.1 p.2 C → 14 ≤ C.size)
    (a b : Fin 11) (order : a ≤ b) (C : Circuit) (fan : FanInTwo C) (h : solves a b C) : 14 ≤ C.size := by
  cases hr : PetersenAlias.redundant a b with
  | true =>
    apply PetersenSecondOR.redundantORSuffixNeedsFourteen a b hr C fan
    intro x
    simpa [augmented,feed,inputs,pin,GateOp.eval] using h x
  | false =>
    obtain ⟨n,hm⟩ := cover a b order hr
    have bound := cert _ hm (rc n C) (rcFan n C fan) (transport n a b C h)
    simpa [rc,Circuit.size] using bound

end PetersenOrbit

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


namespace PetersenCases
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PetersenNonedge PetersenOrbit

theorem edgeEq (x : Fin 9 → Bool) : edge x = PetersenBinary.edge x := by
  simp [edge,edges,PetersenBinary.edge,Bool.or_assoc]

theorem listEq (a b : Fin 11) (x : Fin 9 → Bool) :
    inputs a b x = PetersenBinary.orderedInputs x ++
      [GateOp.or.eval ([a,b].map fun j => (PetersenBinary.orderedInputs x).getD j.val false)] := by
  simp [inputs,pin,PetersenBinary.orderedInputs,GateOp.eval]

theorem fullSize (a b : Fin 11) (C : Circuit) (fan : FanInTwo C) (h : solves a b C) : 13 ≤ C.size := by
  let first : Gate := ⟨GateOp.and,[0,3]⟩
  let second : Gate := ⟨GateOp.or,[a.val,b.val]⟩
  let D : Circuit := ⟨first :: second :: C.gates,C.output⟩
  have wf : FanInTwo D := by
    intro g mem
    rcases List.mem_cons.mp mem with rfl | h₁
    · exact ⟨by simp [first],by decide⟩
    rcases List.mem_cons.mp h₁ with rfl | h₂
    · exact ⟨by simp [second],by simp [second]⟩
    exact fan g h₂
  have run (x : Fin 9 → Bool) : D.eval (List.ofFn x) = edge x := by
    have init : step (step (List.ofFn x) first) second = inputs a b x := by
      simp [step,first,second,inputs,pin,GateOp.eval]
    change (C.gates.foldl step (step (step (List.ofFn x) first) second)).getD C.output false = _
    rw [init]; exact h x
  have big := PetersenSecondOR.anyCircuitNeedsFifteen D wf run
  simp only [D,Circuit.size,List.length_cons] at big
  change 13 ≤ C.gates.length
  omega

def remaining : Prop :=
  ∀ p ∈ reps, ∀ C : Circuit, FanInTwo C → C.size = 13 →
    1 ≤ (C.gates.filter PetersenBinary.negGate).length →
    (C.gates.filter PetersenBinary.negGate).length ≤ 5 → ¬ solves p.1 p.2 C

theorem representativeBound (checked : remaining) :
    ∀ p ∈ reps, ∀ C : Circuit, FanInTwo C → solves p.1 p.2 C → 14 ≤ C.size := by
  intro p hp C fan right
  by_contra! small
  have lo := fullSize _ _ C fan right
  have sz : C.size = 13 := by omega
  have evalRight : ∀ x, C.eval (PetersenBinary.orderedInputs x ++ [GateOp.or.eval
      ([p.1,p.2].map fun j => (PetersenBinary.orderedInputs x).getD j.val false)]) = PetersenBinary.edge x :=
    fun x => by rw [←listEq,←edgeEq]; exact right x
  have hi := PetersenBinary.fiveNotLimit C [p.1,p.2] (by simp) fan (by omega) evalRight
  by_cases pos : 1 ≤ (C.gates.filter PetersenBinary.negGate).length
  · exact checked p hp C fan sz pos hi right
  · have empty : C.gates.filter PetersenBinary.negGate = [] := List.length_eq_zero_iff.mp (by omega)
    have mono : Monotone2 C := by
      intro g hg
      obtain ⟨hop,len⟩ := fan g hg
      change g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not at hop
      refine ⟨?_,len⟩
      rcases hop with hand | hor | hnot
      · exact Or.inl hand
      · exact Or.inr hor
      · have mem : g ∈ C.gates.filter PetersenBinary.negGate := List.mem_filter.mpr
            ⟨hg,by simp [PetersenBinary.negGate,hnot]⟩
        simp [empty] at mem
    have bound := PetersenSecondOR.monotoneSuffixNeedsFourteen C [p.1,p.2] (by simp) mono
      (fun x => by simpa [augmented,feed,inputs,pin,GateOp.eval] using right x)
    omega

/-- The remaining proof needs only sixteen ordered gate pairs, thirteen suffix gates
and one to five NOT gates. All other cases are discharged using L-meta-1672. -/
theorem exactBound (checked : remaining) : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List (Fin (11 : ℕ))),   PEqualNP.MetaComplexity.FanInTwo x1 →     x2.length ≤ (2 : ℕ) →       (∀ (x5 : Fin (9 : ℕ) → Bool),           have x6 : List Bool := List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ))];           x1.eval (x6 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x7 : Fin (11 : ℕ)) => x6.getD (↑x7) Bool.false) x2)]) = (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))) →         (14 : ℕ) ≤ x1.size := by
  intro C ins fan arity right
  let a := ins.getD 0 10
  let b := ins.getD 1 10
  have solvesPair : solves a b C := by
    intro x
    rw [listEq,edgeEq]
    have read := PetersenBinary.or_read x ins arity
    have h := right x
    change C.eval (PetersenBinary.orderedInputs x ++ [GateOp.or.eval (ins.map
        fun j => (PetersenBinary.orderedInputs x).getD j.val false)]) = PetersenBinary.edge x at h
    rw [read] at h
    have pair := PetersenBinary.or_read x [a,b] (by simp)
    rw [pair]
    exact h
  by_cases order : a ≤ b
  · exact coreBound (representativeBound checked) a b order C fan solvesPair
  · apply coreBound (representativeBound checked) b a (le_of_not_ge order) C fan
    intro x
    simpa [inputs,Bool.or_comm] using solvesPair x
end PetersenCases
