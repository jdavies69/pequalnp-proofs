import MarkedTables
import GrantMasks

namespace PetersenReaderInvariant
open PEqualNP.Outside.L_meta_1667
abbrev Layout := Nat × Nat × (Nat → Nat) × (Nat → Nat) × (Nat → Nat)
structure Store where
  layout : Nat → Layout
  lookup : Nat → Nat → Option (Nat × Nat)
  grant : Nat → PetersenReaderNear.GrantSet

def narrowCode : Nat → Nat → Nat
  | 0,_ => 0
  | n+1,s => (s &&& 15) ||| (((s >>> 5) &&& 15) <<< 4) |||
    (((s >>> 10) &&& 3) <<< 8) ||| ((narrowCode n (s >>> 12)) <<< 10)

def getRecord (b : Store) (k i : Nat) : Record :=
  let (_,depth,words,rules,offsets) := b.layout k
  let hbits := 12*depth
  let width := hbits+8+depth+1
  let v := packedAt words (i*width) width
  let ops := v &&& ((1 <<< hbits)-1)
  let m := v >>> hbits
  let pos := offsets i
  let rs := getPairs rules 6 depth (packedAt rules pos 6) (pos+6)
  ⟨depth,ops,narrowCode depth ops,m &&& ((1 <<< (8+depth))-1),rs,m.testBit (8+depth)⟩

def stableSort (us : List Sig) := us.mergeSort (fun a b => a.toNat ≤ b.toNat)
def grantFront (us : List Sig) (perm : List Nat) :=
  stableSort (us.map (movedWord (perm.map swapRows)))

theorem rawGrant {k : Nat} {seen : Bool} {us : List Sig} {perm : List Nat}
    (pm : perm ∈ g383.autos.toList) (g : PetersenReaderNear.GrantSet)
    (check : PetersenReaderNear.grantCheck k (grantFront us perm) g = true) : bound seen k us := by
  have geo := geom383
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true] at geo
  let p := perm.map swapRows
  have rot : autoOK (targetOf g383) p = true := geo.2 _ pm
  have both := rot
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at both
  have imp := PetersenReaderNear.grantSafe check
  have ord : (grantFront us perm).toFinset = (us.map (movedWord p)).toFinset := by
    apply Finset.ext
    intro w
    simp only [List.mem_toFinset]
    exact (List.mergeSort_perm ..).mem_iff
  rw [ord] at imp
  have raw := rotate_excluded imp p rot
  have idw (w : Sig) : movedWord p.reverse (movedWord p w)=w := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j,hj⟩ _ = bit ⟨j,hj⟩ _
    rw [bit_moved,bit_moved,composed_id both.2]
  have eq : (us.map (movedWord p)).map (movedWord p.reverse) = us := by
    simp [List.map_map,Function.comp_def,idw]
  rw [eq] at raw
  exact ofImpossible raw

def address (us : List Sig) := us.foldl (fun sum w =>
  let n := w.toNat % 18446744073709551557
  sum + ((n*(n+971)) % 18446744073709551557)) 0

def routed (b : Store) (k : Nat) (h : Bool) (us : List Sig) :=
  if k=0 && !h then true else
  match b.lookup (k+1) (address us) with
  | none => false
  | some (idx,i) => match g383.autos[i]? with
    | none => false
    | some perm =>
      let n := (b.layout k).1
      if idx < n then
        let r := getRecord b k idx
        (r.seen || !h) && sameWords us (moveList r perm)
      else PetersenReaderNear.grantCheck k (grantFront us perm) (b.grant (idx-n))

theorem routedOK {b k seen us} (prior : ∀ i < (b.layout k).1, Accepted k (getRecord b k i))
    (ok : routed b k seen us=true) : bound seen k us := by
  unfold routed at ok
  split at ok
  next yes =>
    obtain ⟨hz,hf⟩ := Bool.and_eq_true_iff.mp yes
    have z : k=0 := by simpa using hz
    have f : seen=false := by simpa using hf
    subst k; subst seen; exact zeroFalse us
  next =>
    split at ok
    next => contradiction
    next idx i hit =>
      split at ok
      next => contradiction
      next perm rx =>
        have pm : perm ∈ g383.autos.toList := by simpa using Array.mem_of_getElem? rx
        dsimp only at ok
        split at ok
        next boundI =>
          obtain ⟨allowed,equal⟩ := Bool.and_eq_true_iff.mp ok
          have geo := geom383
          simp only [graphValid,Bool.and_eq_true,List.all_eq_true] at geo
          change Excludes _ _ _ _ us.toFinset
          rw [sameWords_sound equal]
          exact rotated (permit _ allowed (prior _ boundI)) (perm.map swapRows) (geo.2 _ pm)
            (List.all_eq_true.mp stablePerms _ pm)
        next => exact rawGrant pm _ ok

def checkStored (b : Store) (k i : Nat) :=
  let r := getRecord b k i
  let ws := decor r
  let vals := state r
  decide vals.Nodup && !(vals.contains (targetOf g383)) &&
    full ((k,ws.length,ws,preCov ws,pools r,fun _=>[]),outside lowerLabels,r.seen,routed b (k-1)) ws

theorem storedOK (b : Store) (k i : Nat)
    (last : ∀ j < (b.layout (k-1)).1, Accepted (k-1) (getRecord b (k-1) j))
    (test : checkStored b k i=true) : Accepted k (getRecord b k i) := by
  let r := getRecord b k i
  obtain ⟨⟨nd,miss⟩,checks⟩ := (Bool.and_eq_true_iff.mp test).imp_left Bool.and_eq_true_iff.mp
  have geo := geom383
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geo
  have missing : targetOf g383 ∉ state r := by simpa [List.contains_eq_mem] using miss
  apply fullOK (raw:=vars g383.mask) (chart_pairs geo.1.1.1 geo.1.1.2) _ (of_decide_eq_true nd)
    missing _ (fun _ _ pass => routedOK last pass) checks
  · intro v hv
    apply wideFaith _ _ _ _ _ (wires_faithful g383) v
    exact (selectLive_sub _ _).subset hv
  · intro v hv
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hv
    exact buildRule_sound g383 (fun x hx => col_sound _ _ (before_sound known255 valid255) (geo.1.2 x hx)) h

def blockStored (b : Store) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => checkStored b k (start+n) && blockStored b k start n
theorem insideBlock {b k start n} (h : blockStored b k start n=true) (i : Nat) (lo : start ≤ i) (hi : i < start+n) :
    checkStored b k i=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [blockStored,Bool.and_eq_true] at h
    by_cases eq : i=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)

end PetersenReaderInvariant
#print axioms PetersenReaderInvariant.storedOK
