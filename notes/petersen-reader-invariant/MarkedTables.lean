import SmallTables
namespace PetersenReaderInvariant
open PEqualNP.Outside.L_meta_1667

def wideBank (n : Nat) (bits : Nat) (ws : List Decor) : List Decor :=
  match n with
  | 0 => ws
  | k+1 =>
    let a := ws.getD (bits &&& 31) defaultDecor
    let b := ws.getD ((bits >>> 5) &&& 31) defaultDecor
    wideBank k (bits >>> 12) (ws++[codeDecor ((bits >>> 10) &&& 3) a b])
theorem wideFaith (n bits) (ws) (r s) (base : ∀ v ∈ ws, faithful r s v) :
    ∀ v ∈ wideBank n bits ws, faithful r s v := by
  induction n generalizing ws bits with
  | zero => exact base
  | succ n ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with hw | hz
    · exact base _ hw
    · obtain rfl := List.mem_singleton.mp hz
      unfold codeDecor
      split
      · exact faithful_neg (faithful_get base _)
      · exact faithful_bin _ (faithful_get base _) (faithful_get base _)


def bank (r : Record) := wideBank r.depth r.ops (wiresOf g383)
def decor (r : Record) := selectLive r.live (bank r)
def state (r : Record) := (decor r).map Prod.fst
def pools (r : Record) := r.recipes.filterMap fun (i,z) => buildRule g383 r.narrow r.depth (bank r) i z
def Accepted (k : Nat) (r : Record) := Excludes (targetOf g383) (outside lowerLabels) r.seen k (state r).toFinset
def bound (h : Bool) (k : Nat) (us : List Sig) :=
  Excludes (targetOf g383) (outside lowerLabels) h k us.toFinset

theorem zeroFalse (us : List Sig) : bound false 0 us := by
  rintro n t hn h
  have h0 : n=0 := by omega
  subst n
  generalize eq : us.toFinset = S at h
  cases h
theorem permit (r : Record) {incoming : Bool} (allowed : r.seen || !incoming = true)
    {k} (h : Accepted k r) : bound incoming k (state r) := by
  by_cases eq : incoming=r.seen
  · subst incoming; exact h
  · cases cur : r.seen <;> cases incoming <;> simp_all [Accepted,bound]
    intro n t hn h'
    exact h n t hn (.ofTrue h'.erase)

def moveList (r : Record) (perm : List Nat) := (state r).map (movedWord (perm.map swapRows).reverse)
def linked (k : Nat) (h : Bool) (us : List Sig) : Bool :=
  if k=0 && !h then true else
  match (links (k+1)).find? (fun item => item.1 == keySet us) with
  | some (_,idx,rot) =>
    match (level k)[idx]?, g383.autos[rot]? with
    | some r, some perm => (r.seen || !h) && sameWords us (moveList r perm)
    | _,_ => false
  | none => false

theorem stablePerms : g383.autos.toList.all (fun perm =>
  lowerLabels.all (fun w => lowerLabels.contains (movedWord (perm.map swapRows) w) &&
    lowerLabels.contains (movedWord (perm.map swapRows).reverse w)))=true := by decide +kernel

theorem linkedOK (k : Nat) (seen : Bool) (us : List Sig)
    (prior : ∀ r ∈ (level k).toList, Accepted k r) (res : linked k seen us = true) : bound seen k us := by
  unfold linked at res
  split at res
  next yes =>
    obtain ⟨hz,hf⟩ := Bool.and_eq_true_iff.mp yes
    have z : k=0 := by simpa using hz
    have f : seen=false := by simpa using hf
    subst k; subst seen; exact zeroFalse us
  next =>
    split at res
    next tag idx rot found =>
      split at res
      next r perm ix rx =>
        obtain ⟨ok,equal⟩ := Bool.and_eq_true_iff.mp res
        have mem : r ∈ (level k).toList := by simpa using Array.mem_of_getElem? ix
        have pm : perm ∈ g383.autos.toList := by simpa using Array.mem_of_getElem? rx
        have valid := List.all_eq_true.mp stablePerms _ pm
        have geo := geom383
        simp only [graphValid,Bool.and_eq_true,List.all_eq_true] at geo
        change Excludes _ _ _ _ us.toFinset
        rw [sameWords_sound equal]
        exact rotated (permit r ok (prior r mem)) (perm.map swapRows) (geo.2 _ pm) valid
      next => contradiction
    next => contradiction

def verified (k : Nat) (r : Record) :=
  let ws := decor r
  let vals := state r
  decide vals.Nodup && !(vals.contains (targetOf g383)) &&
    full ((k,ws.length,ws,preCov ws,pools r,fun _=>[]),outside lowerLabels,r.seen,linked (k-1)) ws

theorem verifiedOK (k : Nat) (r : Record)
    (last : ∀ prev ∈ (level (k-1)).toList, Accepted (k-1) prev)
    (test : verified k r=true) : Accepted k r := by
  obtain ⟨⟨nd,miss⟩,checks⟩ := (Bool.and_eq_true_iff.mp test).imp_left Bool.and_eq_true_iff.mp
  have geo := geom383
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geo
  have missing : targetOf g383 ∉ state r := by simpa [List.contains_eq_mem] using miss
  apply fullOK (raw:=vars g383.mask) (chart_pairs geo.1.1.1 geo.1.1.2) _ (of_decide_eq_true nd)
    missing _ (fun seen xs pass => linkedOK _ seen xs last pass) checks
  · intro v hv
    apply wideFaith _ _ _ _ _ (wires_faithful g383) v
    exact (selectLive_sub _ _).subset hv
  · intro v hv
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hv
    exact buildRule_sound g383 (fun x hx => col_sound _ _ (before_sound known255 valid255) (geo.1.2 x hx)) h

end PetersenReaderInvariant
#print axioms PetersenReaderInvariant.verifiedOK
