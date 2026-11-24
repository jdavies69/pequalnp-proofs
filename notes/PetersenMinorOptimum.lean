import PEqualNP.Outside.L_meta_2036

namespace PetersenMinorOptimum
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def minorFunction (x : Fin 8 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
  (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
  (x 5 && x 7) || (x 7 && x 4)

def starCircuit : Circuit :=
  ⟨[⟨.or,[0,2]⟩, ⟨.or,[8,5]⟩, ⟨.and,[1,9]⟩,
    ⟨.or,[3,6]⟩, ⟨.and,[2,11]⟩,
    ⟨.or,[0,6]⟩, ⟨.or,[13,7]⟩, ⟨.and,[4,14]⟩,
    ⟨.or,[3,5]⟩, ⟨.and,[7,16]⟩,
    ⟨.or,[10,12]⟩, ⟨.or,[15,17]⟩, ⟨.or,[18,19]⟩],20⟩

theorem minorAttained : PEqualNP.MetaComplexity.HasCircuitSize 8 minorFunction 13 := by
  refine ⟨starCircuit,?_,by decide,?_⟩
  · intro g hg
    simp only [starCircuit,List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp,by decide⟩
  · decide +kernel

theorem exactSize : HasCircuitSize 8 minorFunction 13 ∧ ¬ HasCircuitSize 8 minorFunction 12 :=
  ⟨minorAttained,PEqualNP.Outside.L_meta_2036⟩

end PetersenMinorOptimum
