import ReaderMapping
import SeedFilter
namespace PetersenReaderTrace
open PetersenReaderGrammar PEqualNP.Outside.L_meta_1667 PetersenReaderInvariant PetersenTraced PEqualNP.CircuitLowerBounds

theorem low_run (gs : List Gate) (b : Bank) (small : ∀ g∈gs, g.inputs.length≤2) :
    lowBank (run gs b)=execute gs (lowBank b) := by
  induction gs generalizing b with
  | nil=>rfl
  | cons g gs ih=>
    change lowBank (run gs (b++[eval g b]))=execute gs ((lowBank b)++[gv (lowBank b) g])
    rw [ih _ (fun x hx=>small x (by simp [hx]))]
    simp only [lowBank,List.map_append,List.map_singleton,bank_regular b g (small g (by simp))]

theorem values_append (a b : List Gate) (w : List Sig) :
    values (a++b) w= values a w++values b (execute a w) := by
  induction a generalizing w with
  | nil=>rfl
  | cons g gs ih=>
    simp only [List.cons_append,values,execute,List.foldl_cons]
    change (if added w (gv w g) then _::_ else _)=_
    rw [ih]; split <;> rfl

lemma values_length (gs : List Gate) (w : List Sig) : (values gs w).length≤gs.length := by
  induction gs generalizing w with
  | nil=>rfl
  | cons g gs ih=>
    have rem := ih (w++[gv w g]);rw [values];split <;> simp only [List.length_cons] <;> omega

lemma freeIn (b : Bank) (i : Nat) : (lowBank b).getD i zero∈lowBank b ∨ (lowBank b).getD i zero=zero := by
  cases h : (lowBank b)[i]? with
  | some w => exact Or.inl (by simpa [List.getD_eq_getElem?_getD,h] using List.mem_of_getElem? h)
  | none => exact Or.inr (by simp [List.getD_eq_getElem?_getD,h])

lemma added_fresh {w z} (h : added w z=true) : proper z ∧ z∉w := by
  simpa [added,properB,proper,and_assoc] using h

theorem tightSteps (gs : List Gate) (b : Bank)
    (sizes : ∀ g∈gs,g.inputs.length≤2)
    (count : gs.length ≤ (values gs (lowBank b)).length)
    (clean : ∀ z∈values gs (lowBank b), outside lowerLabels z=false) : FreshSteps gs b := by
  induction gs generalizing b with
  | nil=> trivial
  | cons g gs ih=>
    let w:=lowBank b
    let z := gv w g
    let next:=b++[eval g b]
    have nw : lowBank next=w++[z] := by
      simp only [next,lowBank,List.map_append,List.map_singleton,bank_regular b g (sizes g (by simp))]
      rfl
    have top : List.length (values gs (w++[z]))≤gs.length := values_length ..
    change gs.length+1 ≤ (if added w z then z::values gs (w++[z]) else values gs (w++[z])).length at count
    have used : added w z=true := by
      cases h : added w z
      · rw [if_neg (by simpa [h])] at count;omega
      · rfl
    rw [if_pos used,List.length_cons] at count
    change ∀ v∈ (if added w z then z::values gs (w++[z]) else values gs (w++[z])), _ at clean
    rw [if_pos used] at clean
    have ez : extendWord (eval g b).1=z := bank_regular b g (sizes g (by simp))
    have adm := added_fresh used
    have good := clean z (by simp)
    rw [←ez] at good
    refine ⟨⟨goodWord good,?_⟩,?_⟩
    · intro i hi eq
      have identical : z=w.getD i zero := by rw [←ez,eq]; exact (low_get b i).symm
      rcases freeIn b i with mem|zero
      · exact adm.2 (identical ▸ mem)
      · exact adm.1.1 (identical.trans zero)
    · apply ih next (fun v hv=>sizes v (by simp [hv]))
      · rw [nw];omega
      · rw [nw];exact fun v hv=>clean v (by simp [hv])

end PetersenReaderTrace
#print axioms PetersenReaderTrace.tightSteps
