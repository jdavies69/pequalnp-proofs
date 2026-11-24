import TraceBudget
import TraceSemantics
namespace PetersenReaderTrace
open PetersenReaderGrammar PEqualNP.Outside.L_meta_1667 PetersenReaderInvariant PetersenTraced PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
abbrev SearchRoot := Excludes (targetOf g383) (outside lowerLabels) false 13 (vars 383).toFinset

theorem splitContradiction (pre post : List Gate) (g : Gate) (i out : Nat)
    (legal₁ : ∀ a∈pre,Regular a) (legal₂ : ∀ a∈post,Regular a)
    (fan : FanInTwo ⟨pre++g::post,out⟩) (budget : pre.length+post.length≤13)
    (readerEq : eval g (run pre initial)=(((run pre initial).getD i z).1,7))
    (low : ∀ y,(Circuit.mk (pre++g::post) out).eval (pins false y)=minor y)
    (high : ∀ y,(Circuit.mk (pre++g::post) out).eval (pins true y)=(minor y || y 0 || y 3))
    (root : SearchRoot) : False := by
  let gs := pre++g::post
  let b:=run pre initial
  let next:=b++[eval g b]
  let w:=lowBank initial
  let mid:=lowBank b
  let v:=gv mid g
  have sizes : ∀ a∈gs,a.inputs.length≤2 := fun a ha=>(fan a ha).2
  have preSizes : ∀ a∈pre,a.inputs.length≤2 := fun a ha=>(legal₁ a ha).2.1
  have postSizes : ∀ a∈post,a.inputs.length≤2 := fun a ha=>(legal₂ a ha).2.1
  have gm : g∈gs := by simp [gs]
  have equalMid : execute pre w=mid := (low_run pre initial preSizes).symm
  have vn : v=mid.getD i zero := by
    change gv (lowBank b) g = (lowBank b).getD i zero
    rw [low_get,←bank_regular b g (sizes g gm)]
    rw [show eval g b = ((b.getD i z).1,7) from readerEq]
  have skip : added mid v=false := by
    rcases freeIn b i with mem|eq
    · have yes : mid.contains v=true := List.contains_iff_mem.mpr (vn ▸ mem)
      simp only [added,yes,Bool.not_true,Bool.and_false]
    · rw [vn,show mid.getD i zero=zero from eq];simp [added,properB]
  have en : lowBank next=mid++[v] := by
    simp only [next,lowBank,List.map_append,List.map_singleton,bank_regular b g (sizes g gm)]
    rfl
  have vals : values gs w=values pre w++values post (lowBank next) := by
    rw [values_append,equalMid]
    change _++(if added mid v then _ else _)=_
    rw [skip,en];rfl
  have limits : (values gs w).length≤13 := by
    rw [vals,List.length_append]
    have := values_length pre w
    have := values_length post (lowBank next)
    omega
  have pair := output_pair ⟨gs,out⟩ fan low high
  change (run gs initial).getD out z=(word goal,3) at pair
  have output : (execute gs w).getD out zero=targetOf g383 := by
    rw [←low_run gs initial sizes,low_get,pair,goalWord]
  have present : targetOf g383 ∈ execute gs w := by
    cases e : (execute gs w)[out]? with
    | none =>
      simp only [List.getD_eq_getElem?_getD,e,Option.getD_none] at output
      exact False.elim ((by decide +kernel : (targetOf g383)≠zero) output.symm)
    | some y =>
      simp only [List.getD_eq_getElem?_getD,e,Option.getD_some] at output
      exact output ▸ List.mem_of_getElem? e
  obtain ⟨exactLen,goods⟩ := PetersenReaderSeed.readLabels rootMembers fan present limits root
  rw [vals,List.length_append] at exactLen
  have npre := values_length pre w
  have npost := values_length post (lowBank next)
  have firstCount : pre.length ≤ (values pre w).length := by omega
  have fp := tightSteps pre initial preSizes firstCount (by
    intro v hv;apply goods v;rw [vals];exact List.mem_append_left _ hv)
  have fq := tightSteps post next postSizes (by omega) (by
    intro v hv;apply goods v;rw [vals];exact List.mem_append_right _ hv)
  have bank : bankOK (0 : Label) b := runOK 0 pre initial legal₁ fp (initialOK 0)
  have choose : ∃ p : Label, (b.getD i z).1=0 ∨ (b.getD i z).1=word p := by
    by_cases ne : i=6
    · subst i; exact ⟨0,Or.inl (congrArg Prod.fst (sixUnchanged pre initial (by decide)))⟩
    · rcases bank i ne with zero | ⟨a,eq,_⟩
      · exact ⟨0,Or.inl zero⟩
      · exact ⟨a,Or.inr eq⟩
  obtain ⟨p,other⟩:=choose
  have preOK := runOK p pre initial legal₁ fp (initialOK p)
  have special : tracks p (eval g b) := by
    change tracks p (eval g (run pre initial))
    rw [readerEq]
    exact other.elim Or.inl (fun eq=>Or.inr ⟨p,eq,Lift.readerOr⟩)
  have all := runOK p post next legal₂ fq (snocOK preOK special)
  have boundSix : out ≠ 6 := by
    intro eq;subst out
    rw [sixUnchanged gs initial (by decide)] at pair
    exact (constants goal).1 (congrArg Prod.fst pair).symm
  have fin := all out boundSix
  have last : (run post next).getD out z=(word goal,3) := by
    change (((pre++g::post).foldl _ initial).getD out z)=_ at pair
    rw [List.foldl_append] at pair; exact pair
  rw [last] at fin
  rcases fin with zero|⟨a,eq,proof⟩
  · exact (constants goal).1 zero
  · obtain rfl := identityWord goal a eq
    exact noLift p proof
end PetersenReaderTrace
#print axioms PetersenReaderTrace.splitContradiction
