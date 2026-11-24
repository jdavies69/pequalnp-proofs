import Mathlib
import PEqualNP.Defs

namespace ThetaUpper
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def graph (x : Fin 7 → Bool) : Bool :=
  ([(0,1),(1,2),(0,4),(1,5),(2,6),(3,5),(4,6),(6,3)] : List (Fin 7 × Fin 7)).any
    fun e => x e.1 && x e.2

def witness : Circuit :=
  ⟨[⟨.or,[0,2]⟩, ⟨.or,[7,5]⟩, ⟨.and,[1,8]⟩,
    ⟨.or,[2,4]⟩, ⟨.or,[10,3]⟩, ⟨.and,[6,11]⟩,
    ⟨.and,[0,4]⟩, ⟨.and,[3,5]⟩,
    ⟨.or,[9,12]⟩, ⟨.or,[13,14]⟩, ⟨.or,[15,16]⟩],17⟩

theorem eleven : FanInTwo witness ∧ circuitFun 7 witness = graph ∧ witness.size = 11 ∧
    witness.gates.countP (fun g => GateOp.rec true true false (fun _ => true) true g.op) = 11 := by
  refine ⟨?_, ?_, rfl, rfl⟩
  · intro g mem
    simp only [witness,List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp
  · funext x
    have all : ∀ y : Fin 7 → Bool, circuitFun 7 witness y = graph y := by decide +kernel
    exact all x

end ThetaUpper
#print axioms ThetaUpper.eleven
