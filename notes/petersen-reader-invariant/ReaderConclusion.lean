import CofactorJoin
import ReaderSetup
namespace PetersenReaderTrace
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_2502 PetersenReaderGrammar

theorem fromSearch (root : SearchRoot) (C : Circuit) (fan : FanInTwo C) (budget : C.size≤14)
    (single : C.gates.countP PetersenReader.reader ≤ 1)
    (low : ∀ y,C.eval (pins false y)=minor y) :
    ∃ y,C.eval (pins true y) ≠ (minor y || y 0 || y 3) := by
  by_contra! high
  have probe : C.eval (pins true PetersenReader.probe)=true :=
    (high _).trans (by decide +kernel)
  obtain ⟨g,hg,read,mode⟩ := PetersenReader.acceptsOnlyOr C fan budget low probe
  obtain ⟨pre,post,split⟩:=List.mem_iff_append.mp hg
  obtain ⟨gates,out⟩:=C
  change gates=pre++g::post at split
  subst gates
  change (pre++g::post).countP PetersenReader.reader≤1 at single
  rw [List.countP_append,List.countP_cons_of_pos read] at single
  have leftOff : pre.countP PetersenReader.reader=0 := by omega
  have rightOff : post.countP PetersenReader.reader=0 := by omega
  have lp : ∀ a∈pre.map normGate,Regular a := by
    intro a ha
    obtain ⟨b,hb,rfl⟩:=List.mem_map.mp ha
    exact norm_nonreader _ (fan b (by simp [hb])) (List.countP_eq_zero.mp leftOff _ hb)
  have rp : ∀ a∈post.map normGate,Regular a := by
    intro a ha
    obtain ⟨b,hb,rfl⟩:=List.mem_map.mp ha
    exact norm_nonreader _ (fan b (by simp [hb])) (List.countP_eq_zero.mp rightOff _ hb)
  have norm : normGate g = g := by obtain ⟨op,ins⟩:=g;change op=.or at mode;subst op;rfl
  let gs := pre.map normGate ++ g::post.map normGate
  have allg : (pre++g::post).map normGate=gs := by simp [gs,norm]
  have nf : FanInTwo ⟨gs,out⟩ := by
    intro a ha
    change a∈gs at ha
    rw [←allg] at ha
    obtain ⟨b,hb,rfl⟩:=List.mem_map.mp ha
    exact (normGate_nok b (fan b hb)).1
  have lengths : (pre.map normGate).length+(post.map normGate).length≤13 := by
    simp only [Circuit.size,List.length_append,List.length_cons] at budget
    simp only [List.length_map];omega
  have unchanged (w) : (Circuit.mk gs out).eval w=(Circuit.mk (pre++g::post) out).eval w := by
    change (wiresFrom gs w).getD out false=(wiresFrom _ w).getD out false
    rw [←allg,wiresFrom_norm]
  obtain ⟨i,readerEq⟩:=aliasOfOr (pre.map normGate) g mode read (fan g (by simp)).2
  exact splitContradiction _ _ g i out lp rp nf lengths readerEq
    (fun y=>(unchanged _).trans (low y)) (fun y=>(unchanged _).trans (high y)) root

theorem deskFromMarkedSearch (root : SearchRoot) :
have x1 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) => (if x1.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x1.inputs else x1.inputs).any fun (x2 : ℕ) => Decidable.decide (x2 = (6 : ℕ)); have x2 : Bool → (Fin (8 : ℕ) → Bool) → List Bool := fun (x2 : Bool) (x3 : Fin (8 : ℕ) → Bool) => [x3 (1 : Fin (8 : ℕ)), x3 (0 : Fin (8 : ℕ)), x3 (4 : Fin (8 : ℕ)), x3 (7 : Fin (8 : ℕ)), x3 (5 : Fin (8 : ℕ)), x3 (2 : Fin (8 : ℕ)), x2, x3 (6 : Fin (8 : ℕ)), x3 (3 : Fin (8 : ℕ)), x3 (1 : Fin (8 : ℕ)) || x2]; have x3 : (Fin (8 : ℕ) → Bool) → Bool := fun (x3 : Fin (8 : ℕ) → Bool) => x3 (0 : Fin (8 : ℕ)) && x3 (1 : Fin (8 : ℕ)) || x3 (1 : Fin (8 : ℕ)) && x3 (2 : Fin (8 : ℕ)) || x3 (2 : Fin (8 : ℕ)) && x3 (3 : Fin (8 : ℕ)) || x3 (0 : Fin (8 : ℕ)) && x3 (4 : Fin (8 : ℕ)) || x3 (1 : Fin (8 : ℕ)) && x3 (5 : Fin (8 : ℕ)) || x3 (2 : Fin (8 : ℕ)) && x3 (6 : Fin (8 : ℕ)) || x3 (3 : Fin (8 : ℕ)) && x3 (7 : Fin (8 : ℕ)) || x3 (4 : Fin (8 : ℕ)) && x3 (6 : Fin (8 : ℕ)) || x3 (5 : Fin (8 : ℕ)) && x3 (7 : Fin (8 : ℕ)) || x3 (7 : Fin (8 : ℕ)) && x3 (4 : Fin (8 : ℕ)); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 → x4.size ≤ (14 : ℕ) → List.countP x1 x4.gates ≤ (1 : ℕ) → (∀ (x8 : Fin (8 : ℕ) → Bool), x4.eval (x2 Bool.false x8) = x3 x8) → ∃ (x9 : Fin (8 : ℕ) → Bool), x4.eval (x2 Bool.true x9) ≠ (x3 x9 || x9 (0 : Fin (8 : ℕ)) || x9 (3 : Fin (8 : ℕ))) := by
  intro _ _ _ C fan size count low
  exact fromSearch root C fan size count low
end PetersenReaderTrace
#print axioms PetersenReaderTrace.deskFromMarkedSearch
