import PetersenReaderCofactors
import PEqualNP.Defs
namespace PetersenReaderTrace
open PetersenReaderGrammar PEqualNP.CircuitLowerBounds
abbrev Pair := Low × High
abbrev Bank := List Pair
def z : Pair := (0,0)
def o : Pair := (BitVec.allOnes 256,7)
def op (d : Bool) (x y : Pair) := (binary d x.1 y.1,combine d x.2 y.2)
def flip (x : Pair) : Pair := (~~~x.1,~~~x.2)
def eval (g : Gate) (b : Bank) : Pair :=
  let ins := g.inputs.map (fun i=>b.getD i z)
  match g.op with
  | .and => ins.foldr (op false) o
  | .or => ins.foldr (op true) z
  | .not => flip (ins.headD z)
  | _ => z
def run (gs : List Gate) (b : Bank) := gs.foldl (fun w g=> w++[eval g w]) b

def tracks (p : Label) (x : Pair) := x.1=0 ∨ ∃ a, x.1=word a ∧ Lift p a x.2

def bankOK (p : Label) (b : Bank) := ∀ i : ℕ, i≠6 → tracks p (b.getD i z)

def Fresh (b : Bank) (g : Gate) :=
  (∃ c : Label, (eval g b).1=word c) ∧
  ∀ i ∈ g.inputs, (eval g b).1≠(b.getD i z).1

def Regular (g : Gate) := (g.op=.and ∨ g.op=.or ∨ g.op=.not) ∧
  g.inputs.length≤2 ∧ (g.op=.not → g.inputs.length≤1) ∧ 6∉g.inputs

theorem constants : (∀ a : Label, word a≠0 ∧ word a≠BitVec.allOnes 256) := by decide +kernel

lemma units (a : Pair) : op false a o=a ∧ op true a z=a ∧
    op false z a=z ∧ op false a z=z ∧ op true z a=a := by
  obtain ⟨l,h⟩:=a
  simp [op,o,z,binary,combine]
  exact ⟨BitVec.and_allOnes,BitVec.and_allOnes⟩

lemma binaryStep (p : Label) (d : Bool) (a b : Pair)
    (ha : tracks p a) (hb : tracks p b) (c : Label) (result : (op d a b).1=word c)
    (fa : (op d a b).1≠a.1) (fb : (op d a b).1≠b.1) : tracks p (op d a b) := by
  have proper := (constants c).1
  rcases ha with za|⟨u,hu,liftU⟩
  · cases d
    · apply False.elim; apply proper
      simpa [op,binary,za] using result.symm
    · exact False.elim (fb (by simp [op,binary,za]))
  rcases hb with zb|⟨v,hv,liftV⟩
  · cases d
    · apply False.elim; apply proper
      simpa [op,binary,zb] using result.symm
    · exact False.elim (fa (by simp [op,binary,zb]))
  refine Or.inr ⟨c,result,Lift.gate liftU liftV ?_ ?_ ?_⟩
  · simpa only [op,hu,hv] using result
  · intro e; exact fa (result.trans (e ▸ hu.symm))
  · intro e; exact fb (result.trans (e ▸ hv.symm))

theorem regularStep (p : Label) (b : Bank) (g : Gate) (legal : Regular g)
    (good : bankOK p b) (fresh : Fresh b g) : tracks p (eval g b) := by
  obtain ⟨oper,xs⟩ := g
  obtain ⟨kind,len,un,no⟩ := legal
  obtain ⟨⟨c,val⟩,diff⟩ := fresh
  have co := constants c
  change oper=.and ∨ oper=.or ∨ oper=.not at kind
  change xs.length≤2 at len
  change oper=.not → xs.length≤1 at un
  change 6∉xs at no
  cases xs with
  | nil =>
    rcases kind with rfl|rfl|rfl
    · exact False.elim (co.2 val.symm)
    · exact False.elim (co.1 val.symm)
    · apply False.elim; apply co.2
      simpa [eval,flip,z] using val.symm
  | cons i tail =>
    have ni : i≠6 := by intro e; subst i; simp at no
    have hi := good i ni
    cases tail with
    | nil =>
      have neq := diff i (by simp)
      rcases kind with rfl|rfl|rfl
      · exact False.elim (neq (congrArg Prod.fst (units _).1))
      · exact False.elim (neq (congrArg Prod.fst (units _).2.1))
      · change ~~~(b.getD i z).1=word c at val
        rcases hi with zero|⟨a,eq,_⟩
        · exact False.elim (co.2 (by rw [zero] at val; simpa [z] using val.symm))
        · exact False.elim (negAbsent a c (eq ▸ val))
    | cons j rest =>
      have nj : j≠6 := by intro e; subst j; simp at no
      cases rest with
      | cons k more => simp at len
      | nil =>
        have hj := good j nj
        have fi := diff i (by simp)
        have fj := diff j (by simp)
        rcases kind with rfl|rfl|rfl
        · simp only [eval,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(units _).1] at val fi fj ⊢
          exact binaryStep p false _ _ hi hj c val fi fj
        · simp only [eval,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(units _).2.1] at val fi fj ⊢
          exact binaryStep p true _ _ hi hj c val fi fj
        · have short := un rfl; simp at short

end PetersenReaderTrace
#print axioms PetersenReaderTrace.regularStep
