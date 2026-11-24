import TraceCircuit
namespace PetersenReaderTrace
open PetersenReaderGrammar PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
abbrev Coordinate := Sum (Fin 256) (Fin 3)
def readAt : Coordinate → Pair → Bool
  | .inl i,x => x.1.getLsbD i.val
  | .inr j,x => x.2.getLsbD j.val

def pins (s : Bool) (x : Fin 8 → Bool) :=
  [x 1,x 0,x 4,x 7,x 5,x 2,s,x 6,x 3,x 1 || s]
def inputRow : Coordinate → List Bool
  | .inl i=>pins false (inputAt i.val)
  | .inr j=>pins true (inputAt (![1,8,52] j))

theorem initialRow : ∀ r, initial.map (readAt r)=inputRow r := by
  intro r; cases r with
  | inl i => revert i; decide +kernel
  | inr j => revert j; decide +kernel
lemma z_at (r : Coordinate) : readAt r z=false := by cases r <;> simp [readAt,z]
lemma o_at (r : Coordinate) : readAt r o=true := by cases r with
  | inl i => simp only [readAt,o,BitVec.getLsbD_allOnes,i.isLt,decide_true]
  | inr j => fin_cases j <;> rfl
lemma neg_at (r : Coordinate) (x : Pair) : readAt r (flip x)= !readAt r x := by
  cases r <;> simp [readAt,flip,Fin.isLt]
lemma op_at (r : Coordinate) (d : Bool) (x y : Pair) : readAt r (op d x y) =
    if d then readAt r x || readAt r y else readAt r x && readAt r y := by
  cases r <;> cases d <;> simp [readAt,op,binary,combine]

lemma read_get (r : Coordinate) (b : Bank) (i : ℕ) :
    readAt r (b.getD i z)=(b.map (readAt r)).getD i false := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases b[i]? <;> simp [z_at]

lemma gate_coord (r : Coordinate) (b : Bank) (g : Gate)
    (leg : g.op∈({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2) :
    readAt r (eval g b)=g.op.eval (g.inputs.map fun i=>(b.map (readAt r)).getD i false) := by
  obtain ⟨oper,ins⟩:=g
  change (oper∈({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ ins.length≤2) at leg
  obtain ⟨modes,size⟩:=leg
  change oper=.and ∨ oper=.or ∨ oper=.not at modes
  have elem (i : Nat) : readAt r ((b[i]?).getD z)=((b[i]?).map (readAt r)).getD false := by
    cases b[i]? <;> simp [z_at]
  rcases ins with _|⟨i,_|⟨j,_|⟨k,rs⟩⟩⟩
  all_goals first | simp at size | skip
  all_goals rcases modes with rfl|rfl|rfl <;> simp [eval,GateOp.eval,op_at,neg_at,z_at,o_at,read_get] <;>
    simp_all only [elem]

lemma run_coord (r : Coordinate) (b : Bank) (gs : List Gate)
    (leg : ∀ g∈gs, g.op∈({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2) :
    (run gs b).map (readAt r)=(Circuit.mk gs 0).wires (b.map (readAt r)) := by
  induction gs generalizing b with
  | nil=>rfl
  | cons g gs ih=>
    change (run gs (b++[eval g b])).map _=_
    rw [ih _ (fun x hx=>leg x (by simp [hx]))]
    simp only [List.map_append,List.map_cons,List.map_nil,gate_coord r b g (leg g (by simp))]
    rfl

theorem output_coord (C : Circuit) (leg : FanInTwo C) (r : Coordinate) :
    readAt r ((run C.gates initial).getD C.output z)=C.eval (inputRow r) := by
  rw [read_get,run_coord r initial C.gates leg,initialRow]
  rfl

theorem output_pair (C : Circuit) (leg : FanInTwo C)
    (lo : ∀ y,C.eval (pins false y)=minor y)
    (hi : ∀ y,C.eval (pins true y)=(minor y || y 0 || y 3)) :
    (run C.gates initial).getD C.output z=(word goal,3) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro k hk
    let r : Fin 256 := ⟨k,hk⟩
    exact (output_coord C leg (.inl r)).trans ((lo _).trans (goalLow r).symm)
  · apply BitVec.eq_of_getLsbD_eq
    intro k hk
    let j : Fin 3:=⟨k,hk⟩
    have bits : ∀ j : Fin 3, highTarget (![1,8,52] j)=(3 : High).getLsbD j.val := by decide +kernel
    exact (output_coord C leg (.inr j)).trans ((hi _).trans (bits _))
end PetersenReaderTrace
#print axioms PetersenReaderTrace.output_pair
