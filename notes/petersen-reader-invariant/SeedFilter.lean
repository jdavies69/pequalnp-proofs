import TracedOptimal
import SmallTables
namespace PetersenReaderSeed
open PEqualNP.Outside.L_meta_1667 PetersenReaderInvariant PetersenTraced
lemma proper_mem {T n t S} (h : Live T n t S) : ∀ v∈S,proper v := by
  induction h with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h=>ih a (Finset.mem_insert_of_mem h))
  | binary ha hb ne hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h=>ih a (Finset.mem_insert_of_mem h)⟩

lemma requiredSet {S k t} (h : Live (targetOf g383) k t S) (sub : ∀ a∈S,a∈(vars 383)) :
    S=(vars 383).toFinset := by
  apply Finset.Subset.antisymm (fun a ha => List.mem_toFinset.mpr (sub a ha))
  intro a ha
  have cert : checkEssential (targetOf g383) (vars 383) (graphPairs 383 12901687553)=true := by decide +kernel
  have same : (graphPairs 383 12901687553).map Prod.fst=vars 383 := by decide +kernel
  obtain ⟨r,s,neq,eq⟩ := essential_ok cert a (same ▸ ha)
  exact raw_required h _ a sub r s neq eq

lemma lowerLive {k t S} (h : Live (targetOf g383) k t S) (sub : ∀ a∈S,a∈(vars 383)) : 13≤k := by
  have eq := requiredSet h sub
  rw [eq] at h
  by_contra! short
  have stop := root_index (g:=g383) (before_sound known255 valid255) geom383 tables383
      (k:=12) (by decide) (i:=0) (ws:=vars 383) (by decide +kernel)
  exact stop k t (by omega) h

lemma usable {w : List Sig} (bank : w.toFinset=insert zero (vars 383).toFinset)
    {k t S} (h : Live (targetOf g383) k t S) (all : ∀ v∈S,v∈w) : ∀ v∈S,v∈(vars 383) := by
  intro v hv
  have mem := List.mem_toFinset.mpr (all v hv)
  rw [bank] at mem
  exact List.mem_toFinset.mp ((Finset.mem_insert.mp mem).resolve_left (proper_mem h v hv).1)

theorem readLabels {gs w} (base : w.toFinset=insert zero (vars 383).toFinset)
    (legal : ∀ g∈gs, g.op∈({PEqualNP.CircuitLowerBounds.GateOp.and,.or,.not} : Set _) ∧ g.inputs.length≤2)
    (out : targetOf g383 ∈ execute gs w) (budget : (values gs w).length≤13)
    (search : Excludes (targetOf g383) (outside lowerLabels) false 13 (vars 383).toFinset) :
    (values gs w).length=13 ∧ ∀ z∈values gs w, outside lowerLabels z=false := by
  apply labelsFromOptimal legal (by unfold proper;decide +kernel) out budget
  · intro k t S live sub; exact lowerLive live (usable base live sub)
  · intro S sub k t small marked
    have eq := requiredSet marked.erase (usable base marked.erase sub)
    rw [eq] at marked
    exact search k t small marked
end PetersenReaderSeed
#print axioms PetersenReaderSeed.readLabels
