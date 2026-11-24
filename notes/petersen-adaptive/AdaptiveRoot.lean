import AdaptiveForest
import ForestBridge
namespace PetersenOrientation
open PEqualNP.Outside.L_meta_1667 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PetersenCertificate
theorem forest_all (g : Forest) (cut : Nat → List Sig → Bool) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geometry : graphValid g prior = true) (valid : ∀ j xs, cut j xs=true → Impossible (targetOf g) j xs.toFinset)
    (rows : ∀ k ≤ top, ∀ i < (g.levels k).1, Adaptive.nodeVerified g cut k i=true) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible (targetOf g) k (stateSet g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    apply Adaptive.nodeVerified_sound g cut 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega) valid
    exact rows 0 hk i hi
  | succ k ih =>
    intro hk i hi
    apply Adaptive.nodeVerified_sound g cut _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega)) valid
    exact rows _ hk i hi

theorem parentFromRoot (root : Impossible graph 14 (inputs++[boostedWire]).toFinset) :
    ∀ C : Circuit, FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 6)) →
      circuitFun 9 C = edge → 16 ≤ C.size := by
  intro C legal first correct
  by_contra! small
  obtain ⟨k,t,hk,h|h⟩ := orLive C legal first correct (by omega)
  · exact dead_start (before_sound known383 valid383) geomdead tablesdead k t hk h
  · exact root k t hk h
theorem deskFromRoot (root : Impossible graph 14 (inputs++[boostedWire]).toFinset) :
have x1 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) => (if x1.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x1.inputs else x1.inputs).any fun (x2 : ℕ) => Decidable.decide (x2 = (6 : ℕ)); have x2 : Bool → (Fin (8 : ℕ) → Bool) → List Bool := fun (x2 : Bool) (x3 : Fin (8 : ℕ) → Bool) => [x3 (1 : Fin (8 : ℕ)), x3 (0 : Fin (8 : ℕ)), x3 (4 : Fin (8 : ℕ)), x3 (7 : Fin (8 : ℕ)), x3 (5 : Fin (8 : ℕ)), x3 (2 : Fin (8 : ℕ)), x2, x3 (6 : Fin (8 : ℕ)), x3 (3 : Fin (8 : ℕ)), x3 (1 : Fin (8 : ℕ)) || x2]; have x3 : (Fin (8 : ℕ) → Bool) → Bool := fun (x3 : Fin (8 : ℕ) → Bool) => x3 (0 : Fin (8 : ℕ)) && x3 (1 : Fin (8 : ℕ)) || x3 (1 : Fin (8 : ℕ)) && x3 (2 : Fin (8 : ℕ)) || x3 (2 : Fin (8 : ℕ)) && x3 (3 : Fin (8 : ℕ)) || x3 (0 : Fin (8 : ℕ)) && x3 (4 : Fin (8 : ℕ)) || x3 (1 : Fin (8 : ℕ)) && x3 (5 : Fin (8 : ℕ)) || x3 (2 : Fin (8 : ℕ)) && x3 (6 : Fin (8 : ℕ)) || x3 (3 : Fin (8 : ℕ)) && x3 (7 : Fin (8 : ℕ)) || x3 (4 : Fin (8 : ℕ)) && x3 (6 : Fin (8 : ℕ)) || x3 (5 : Fin (8 : ℕ)) && x3 (7 : Fin (8 : ℕ)) || x3 (7 : Fin (8 : ℕ)) && x3 (4 : Fin (8 : ℕ)); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 → x4.size ≤ (14 : ℕ) → List.countP x1 x4.gates ≤ (1 : ℕ) → (∀ (x8 : Fin (8 : ℕ) → Bool), x4.eval (x2 Bool.false x8) = x3 x8) → ∃ (x9 : Fin (8 : ℕ) → Bool), x4.eval (x2 Bool.true x9) ≠ (x3 x9 || x9 (0 : Fin (8 : ℕ)) || x9 (3 : Fin (8 : ℕ))) := by
  intro _ input z C fan budget _ low
  by_contra! high
  let g : Gate := ⟨.or,[0,6]⟩
  let D : Circuit := ⟨g::C.gates,C.output⟩
  have legal : FanInTwo D := by
    intro t mem
    rcases List.mem_cons.mp mem with rfl|m
    · exact ⟨by simp [g],by decide⟩
    · exact fan t m
  let step := fun (w : List Bool) (t : Gate) => w ++ [t.op.eval (t.inputs.map fun i => w.getD i false)]
  have start (x : Fin 9 → Bool) : step (List.ofFn x) g = subInput (x 6) (permute x) := by
    rw [feedEq]; simp [step,g,GateOp.eval]
  have keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons,ih]
      · simp [step,List.getD_eq_getElem?_getD,List.getElem?_append_left hi]
      · simp [step];omega
  have first (x : Fin 9 → Bool) : (D.wires (List.ofFn x)).getD 9 false = (x 0 || x 6) := by
    change (C.gates.foldl step (step (List.ofFn x) g)).getD 9 false = _
    rw [keep _ _ _ (by simp [step]),start,feedEq,List.getD_append_right _ _ _ _ (by simp)]
    simp
  have comp : circuitFun 9 D = edge := by
    funext x
    change (C.gates.foldl step (step (List.ofFn x) g)).getD C.output false = _
    rw [start]
    change C.eval (subInput (x 6) (permute x)) = _
    rw [←transform x]
    cases eq : x 6
    · exact low (permute x)
    · exact high (permute x)
  have lb := parentFromRoot root D legal first comp
  change 16 ≤ C.gates.length + 1 at lb
  change C.gates.length ≤ 14 at budget
  omega
end PetersenOrientation
#print axioms PetersenOrientation.deskFromRoot
#print axioms PetersenOrientation.forest_all
