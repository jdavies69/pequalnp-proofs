import Marked
namespace PetersenTraced
open PEqualNP.Outside.L_meta_1667 PEqualNP.CircuitLowerBounds PetersenReaderInvariant
set_option maxHeartbeats 1000000
inductive Trail (T : Sig) : List Sig → Nat → Finset Sig → Prop where
  | stop (hp : proper T) : Trail T [] 0 {T}
  | unary {zs t U a} (ha : proper a) (hf : neg a ∉ insert a U)
      (later : Trail T zs t (insert (neg a) U)) :
      Trail T (neg a::zs) (t+1) (insert a U)
  | binary {zs t U a b d} (ha : proper a) (hb : proper b) (ab : a≠b)
      (hf : bin d a b ∉ insert a (insert b U))
      (later : Trail T zs t (insert (bin d a b) U)) :
      Trail T (bin d a b::zs) t (insert a (insert b U))

theorem Trail.erase {T zs t S} (h : Trail T zs t S) : Live T zs.length t S := by
  induction h with
  | stop hp => exact .stop hp
  | unary ha hf _ ih => exact .unary ha hf ih
  | binary ha hb ne hf _ ih => exact .binary ha hb ne hf ih

theorem Trail.mark {T zs t S} (h : Trail T zs t S) (bad : Sig → Bool) (seen : Bool)
    (ends : (seen || zs.any bad) = true) : Marked T bad zs.length t S seen := by
  induction h generalizing seen with
  | stop hp => cases seen <;> first | exact .stop hp | simp at ends
  | @unary zs t U a ha hf _ ih =>
    apply Marked.unary ha hf (ih _ _); simpa [Bool.or_assoc] using ends
  | @binary zs t U a b d ha hb ne hf _ ih =>
    apply Marked.binary ha hb ne hf (ih _ _); simpa [Bool.or_assoc] using ends

def added (w : List Sig) (z : Sig) : Bool := properB z && !(w.contains z)
def values : List Gate → List Sig → List Sig
  | [],_ => []
  | g::gs,w =>
    let z:=gv w g
    let more:=values gs (w++[z])
    if added w z then z::more else more
private theorem bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]

private lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)

private lemma bin_laws (a : Sig) :
    bin false a one = a ∧ bin true a zero = a ∧
    bin false a zero = zero ∧ bin true a one = one ∧
    bin false a a = a ∧ bin true a a = a := by
  simp only [bin,one,zero,Bool.false_eq_true,ite_false,ite_true,BitVec.and_allOnes,BitVec.or_zero,BitVec.and_zero,BitVec.or_allOnes,BitVec.and_self,BitVec.or_self,and_self] <;> simp

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

private lemma bin_rep {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ witness w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a0,az,ao,aa,aa'⟩ := bin_laws a
  obtain ⟨b1,b0,bz,bo,bb,bb'⟩ := bin_laws b
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · rw [bin_comm]; cases d <;> simp_all
  · rw [bin_comm]; cases d <;> simp_all
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a=b
  · subst b; cases d <;> simp_all
  exact Or.inr (Or.inr ⟨d,a,b,ham,hbm,hap,hbp,he,rfl⟩)

private lemma gate_rep (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2) :
    represented w (gv w g) ∨ witness w (gv w g) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  have nx (a : Sig) (ha : represented w a) : represented w (neg a) ∨ witness w (neg a) := by
    rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
    · exact Or.inl (neg_laws.1 ▸ ro)
    · exact Or.inl (neg_laws.2 ▸ rz)
    · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)
  cases l with
  | nil =>
    rcases ho with rfl | rfl | rfl
    · exact Or.inl ro
    · exact Or.inl rz
    · exact nx _ rz
  | cons i l =>
    cases l with
    | nil =>
      rcases ho with rfl | rfl | rfl
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · exact nx _ (get_rep w i)
    | cons j l =>
      cases l with
      | cons a l => simp at hl
      | nil =>
        rcases ho with rfl | rfl | rfl
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using bin_rep false (get_rep w i) (get_rep w j)
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using bin_rep true (get_rep w i) (get_rep w j)
        · exact nx _ (get_rep w i)

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.

private lemma live_proper {k t S} (h : Live target k t S) : ∀ a ∈ S, proper a := by
  induction h with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private theorem pull {target w z zs t S} (h : Trail target zs t S)
    (hz : represented w z ∨ witness w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ (take : Bool) (u : Nat) (R : Finset Sig), (take=true → added w z=true) ∧
      Trail target (if take then z::zs else zs) u R ∧ ∀ a∈R, a∈w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨false,t,S,by simp,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h.erase z hm
      rcases hz with hr | (⟨a,ha,hp',eq⟩ | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (neg a)
        have ht : Trail target zs t (insert (neg a) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : neg a ∉ insert a U := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨true,_,_,by simpa [added,properB,proper,hw] using (fun (_ : true=true)=>hp),Trail.unary hp' hf ht,by simpa using And.intro ha hu⟩
      · subst z
        let U := S.erase (bin d a b)
        have ht : Trail target zs t (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨true,_,_,by simpa [added,properB,proper,hw] using (fun (_ : true=true)=>hp),Trail.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨false,t,S,by simp,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha


theorem extract {target} (gs : List Gate) (w : List Sig)
    (legal : ∀ g∈gs, g.op∈({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (hp : proper target) (out : target∈execute gs w) :
    ∃ zs t S, zs.Sublist (values gs w) ∧ Trail target zs t S ∧ ∀ a∈S, a∈w := by
  induction gs generalizing w with
  | nil => exact ⟨[],0,{target},.slnil,.stop hp,by simpa [execute] using out⟩
  | cons g gs ih =>
    obtain ⟨zs,t,S,sub,run,mem⟩ := ih (w++[gv w g]) (fun g hg => legal g (by simp [hg])) out
    obtain ⟨take,u,R,ok,run',mem'⟩ := pull run (gate_rep w g (legal g (by simp))) mem
    refine ⟨_,u,R,?_,run',mem'⟩
    cases take with
    | false =>
      change zs.Sublist (if added w (gv w g) then gv w g::values gs (w++[gv w g]) else values gs (w++[gv w g]))
      split <;> first | exact sub.cons _ | exact sub
    | true =>
      change (gv w g::zs).Sublist (if added w (gv w g) then gv w g::values gs (w++[gv w g]) else values gs (w++[gv w g]))
      rw [if_pos (ok rfl)]
      exact sub.cons₂ _

theorem labelsFromOptimal {T bad gs w cap}
    (legal : ∀ g∈gs, g.op∈({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (hp : proper T) (out : T∈execute gs w) (budget : (values gs w).length ≤ cap)
    (full : ∀ k t S, Live T k t S → (∀ a∈S,a∈w) → cap≤k)
    (marked : ∀ S, (∀ a∈S,a∈w) → Excludes T bad false cap S) :
    (values gs w).length=cap ∧ ∀ z∈values gs w, bad z=false := by
  obtain ⟨zs,t,S,sub,run,mem⟩ := extract gs w legal hp out
  have lo := full _ _ _ run.erase mem
  have hi := sub.length_le
  have eq : zs=values gs w := sub.eq_of_length (by omega)
  subst zs
  refine ⟨by omega,?_⟩
  intro z hz
  by_contra fail
  have someBad := List.any_eq_true.mpr ⟨z,hz,Bool.eq_true_of_not_eq_false fail⟩
  exact marked S mem _ _ budget (run.mark bad false (by simpa using someBad))

end PetersenTraced
#print axioms PetersenTraced.labelsFromOptimal
