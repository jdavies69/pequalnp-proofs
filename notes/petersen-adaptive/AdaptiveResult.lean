import AdaptiveRoot
import AdaptiveData

namespace PetersenOrientation.Replay
open PEqualNP.Outside.L_meta_1667 PetersenCertificate

def RowsChecked := ∀ k ≤ 14, ∀ i < (g.levels k).1, checkRow k i = true

theorem rootImpossible (checked : RowsChecked) : Impossible graph 14 (inputs++[boostedWire]).toFinset := by
  have geometry : graphValid g (boundsBefore known383)=true := geomdead
  have tg : targetOf g=graph := by decide +kernel
  have valid (k : Nat) (xs : List Sig) (ok : cuts k xs=true) : Impossible (targetOf g) k xs.toFinset := by
    rw [tg]
    exact runCertificate_sound _ _ _ _ _ _ ok
  have start : indexedRoot g 14 0 (inputs++[boostedWire])=true := by decide +kernel
  obtain ⟨idx,eq⟩ := Bool.and_eq_true_iff.mp start
  rw [←sameWords_sound eq,←tg]
  exact PetersenOrientation.forest_all g cuts 14 _ (before_sound known383 valid383) geometry valid checked
    14 (Nat.le_refl _) 0 (of_decide_eq_true idx)

theorem desk (checked : RowsChecked) : have x1 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) => (if x1.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x1.inputs else x1.inputs).any fun (x2 : ℕ) => Decidable.decide (x2 = (6 : ℕ)); have x2 : Bool → (Fin (8 : ℕ) → Bool) → List Bool := fun (x2 : Bool) (x3 : Fin (8 : ℕ) → Bool) => [x3 (1 : Fin (8 : ℕ)), x3 (0 : Fin (8 : ℕ)), x3 (4 : Fin (8 : ℕ)), x3 (7 : Fin (8 : ℕ)), x3 (5 : Fin (8 : ℕ)), x3 (2 : Fin (8 : ℕ)), x2, x3 (6 : Fin (8 : ℕ)), x3 (3 : Fin (8 : ℕ)), x3 (1 : Fin (8 : ℕ)) || x2]; have x3 : (Fin (8 : ℕ) → Bool) → Bool := fun (x3 : Fin (8 : ℕ) → Bool) => x3 (0 : Fin (8 : ℕ)) && x3 (1 : Fin (8 : ℕ)) || x3 (1 : Fin (8 : ℕ)) && x3 (2 : Fin (8 : ℕ)) || x3 (2 : Fin (8 : ℕ)) && x3 (3 : Fin (8 : ℕ)) || x3 (0 : Fin (8 : ℕ)) && x3 (4 : Fin (8 : ℕ)) || x3 (1 : Fin (8 : ℕ)) && x3 (5 : Fin (8 : ℕ)) || x3 (2 : Fin (8 : ℕ)) && x3 (6 : Fin (8 : ℕ)) || x3 (3 : Fin (8 : ℕ)) && x3 (7 : Fin (8 : ℕ)) || x3 (4 : Fin (8 : ℕ)) && x3 (6 : Fin (8 : ℕ)) || x3 (5 : Fin (8 : ℕ)) && x3 (7 : Fin (8 : ℕ)) || x3 (7 : Fin (8 : ℕ)) && x3 (4 : Fin (8 : ℕ)); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 → x4.size ≤ (14 : ℕ) → List.countP x1 x4.gates ≤ (1 : ℕ) → (∀ (x8 : Fin (8 : ℕ) → Bool), x4.eval (x2 Bool.false x8) = x3 x8) → ∃ (x9 : Fin (8 : ℕ) → Bool), x4.eval (x2 Bool.true x9) ≠ (x3 x9 || x9 (0 : Fin (8 : ℕ)) || x9 (3 : Fin (8 : ℕ))) := deskFromRoot (rootImpossible checked)
end PetersenOrientation.Replay
#print axioms PetersenOrientation.Replay.desk
