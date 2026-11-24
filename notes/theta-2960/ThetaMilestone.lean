import ThetaRows
import ThetaFinite
import ThetaUpper

namespace Theta2960

theorem lower_of_search (closed : ¬ Within thetaCanonical 10 inputs) :
  ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C →
    PEqualNP.MetaComplexity.circuitFun 7 C = targetFun → 11 ≤ C.gates.countP charge := by
  intro C fan computes
  obtain ⟨k,hk,run⟩ := canonicalTrace C fan computes
  by_contra! small
  exact closed ⟨k,by omega,run⟩

end Theta2960
#print axioms Theta2960.lower_of_search
#print axioms Theta2960.feasible_cover
#print axioms Theta2960.nextChoice
#print axioms ThetaUpper.eleven
