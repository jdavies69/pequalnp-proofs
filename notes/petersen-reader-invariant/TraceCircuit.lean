import ReaderTrace
namespace PetersenReaderTrace
open PetersenReaderGrammar PEqualNP.CircuitLowerBounds

def atom (i : Fin 8) : Pair := (word (base i),baseHigh i)
def initial : Bank := [atom 1,atom 0,atom 4,atom 7,atom 5,atom 2,(0,7),atom 6,atom 3,(word (base 1),7)]

theorem atomOK (p : Label) (i : Fin 8) : tracks p (atom i) := Or.inr ⟨_,rfl,.var i⟩

theorem initialOK (p : Label) : bankOK p initial := by
  intro i ne
  by_cases bound : i<10
  · interval_cases i <;> first | exact atomOK p _ | exact Or.inr ⟨_,rfl,Lift.inputOr⟩ | contradiction
  · have big : initial.length ≤ i := Nat.le_of_not_gt bound
    rw [List.getD_eq_default _ _ big]
    exact Or.inl rfl

lemma snocOK {p : Label} {b : Bank} (good : bankOK p b) {x : Pair} (ok : tracks p x) :
    bankOK p (b++[x]) := by
  intro i ne
  by_cases early : i<b.length
  · simpa [List.getD_eq_getElem?_getD,List.getElem?_append_left early] using good i ne
  by_cases eq : i=b.length
  · subst i; simpa [List.getD_eq_getElem?_getD,List.getElem?_append_right] using ok
  · rw [List.getD_eq_default _ _ (by simp;omega)];exact Or.inl rfl

def FreshSteps : List Gate → Bank → Prop
  | [],_ => True
  | g::gs,b => Fresh b g ∧ FreshSteps gs (b++[eval g b])

theorem runOK (p : Label) (gs : List Gate) (b : Bank)
    (legal : ∀ g∈gs, Regular g) (fresh : FreshSteps gs b) (good : bankOK p b) :
    bankOK p (run gs b) := by
  induction gs generalizing b with
  | nil => exact good
  | cons g gs ih =>
    exact ih _ (fun g hg=>legal g (by simp [hg])) fresh.2 (snocOK good (regularStep p b g (legal _ (by simp)) good fresh.1))

theorem sixUnchanged (gs : List Gate) (b : Bank) (bound : 6<b.length) :
    (run gs b).getD 6 z=b.getD 6 z := by
  induction gs generalizing b with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (b++[eval g b])).getD 6 z = _
    rw [ih _ (by simp;omega)]
    simp [List.getD_eq_getElem?_getD,List.getElem?_append_left bound]

theorem readerValue (pre : List Gate) (i : Nat) (comm : Bool) :
    let b := run pre initial
    let pins := if comm then [i,6] else [6,i]
    eval ⟨.or,pins⟩ b = ((b.getD i z).1,7) := by
  have fixed : (run pre initial).getD 6 z = (0,7) := sixUnchanged pre initial (by decide)
  cases comm <;> simp only [Bool.false_eq_true,ite_false,ite_true,eval,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(units _).2.1,fixed,op,binary,combine,BitVec.zero_or,BitVec.or_zero,Prod.mk.injEq,true_and]
  · simp [z]; exact BitVec.allOnes_or
  · simp [z]; exact BitVec.or_allOnes

theorem identityWord (a b : Label) (eq : word a=word b) : a=b := by
  rw [←identityLabels a,← identityLabels b,eq]

theorem traceEither (pre post : List Gate) (i out : Nat) (comm : Bool)
    (legal₁ : ∀ g∈pre, Regular g) (legal₂ : ∀ g∈post, Regular g)
    (fresh₁ : FreshSteps pre initial)
    (p : Label) (other : ((run pre initial).getD i z).1=0 ∨ ((run pre initial).getD i z).1=word p)
    (fresh₂ : FreshSteps post (run pre initial++[(((run pre initial).getD i z).1,7)]))
    (notSix : out≠6) :
    (run (pre++⟨.or,if comm then [i,6] else [6,i]⟩::post) initial).getD out z ≠ (word goal,3) := by
  intro hit
  have preOK := runOK p pre initial legal₁ fresh₁ (initialOK p)
  have special : tracks p (((run pre initial).getD i z).1,7) :=
    other.elim Or.inl (fun eq=>Or.inr ⟨p,eq,Lift.readerOr⟩)
  have full := runOK p post _ legal₂ fresh₂ (snocOK preOK special)
  have ev := readerValue pre i comm
  dsimp only at ev
  change ((pre++_).foldl _ initial).getD out z=_ at hit
  rw [List.foldl_append] at hit
  change (run post (run pre initial++[eval _ (run pre initial)])).getD out z=_ at hit
  rw [ev] at hit
  have last := full out notSix
  rw [hit] at last
  rcases last with zero|⟨a,eq,h⟩
  · exact (constants goal).1 zero
  · have same := identityWord goal a eq
    subst a
    exact noLift p h
end PetersenReaderTrace
#print axioms PetersenReaderTrace.traceEither
