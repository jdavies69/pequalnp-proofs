import OrbitHit
import Cheap
namespace Replay2161
abbrev Rows := Array (Array ℕ)
def fetchRow (r : Rows) (i : ℕ) := ((r[i/24]?).getD #[])[Nat.mod i 24]?.getD 0

def tapeAt (r : Rows) (d i : ℕ) := Nat.mod (fetchRow r i) (2^(12*d))
def Region {x : Word} {c : Charts x} (root : Frame c) (d num : ℕ) (r : Rows) :=
  ∀ j<num, ∀ g, root.replay d (tapeAt r d j)=some g → g.No

def glimpse {x : Word} {c : Charts x} (f : Frame c) :=
  Nat.mod (f.v.foldl (fun acc w=>acc+w.w.toNat) (f.b+17*f.t)) 4093

def linkBits {x : Word} {c : Charts x} (root : Frame c) (next : Rows) (rot : Array (Rotation root))
    (d num key : ℕ) (f : Frame c) : ℕ→ℕ→Bool
  | 0,_ => false
  | cnt+1,blob =>
    if blob=0 then false else
      (let h:=blob &&& 0xfffffff
       let idx:=h >>> 16
       h &&& 4095 == key && decide (idx<num) &&
         (rot[(h >>> 12) &&& 15]?).any (fun a=>fromOrbit root d (tapeAt next d idx) a f)) ||
      linkBits root next rot d num key f cnt (blob >>> 28)

lemma links_valid {x : Word} {c : Charts x} {root f : Frame c} {r : Rows} {rot} {d num key blob cnt}
    (good : Region root d num r) (hit : linkBits root r rot d num key f cnt blob=true) : f.No := by
  induction cnt generalizing blob with
  | zero => contradiction
  | succ n ih =>
    simp only [linkBits] at hit
    split at hit
    · contradiction
    rcases Bool.or_eq_true_iff.mp hit with use|go
    · obtain ⟨⟨_,idx⟩,q⟩ := (Bool.and_eq_true_iff.mp use).imp_left Bool.and_eq_true_iff.mp
      obtain ⟨a,_,h⟩ := (Option.any_eq_true ..).1 q
      exact orbit_hit (good _ (of_decide_eq_true idx)) h
    · exact ih go

def selectPrices {x : Word} (ps : List (Price x)) : ℕ→ℕ→List (Price x)
  | 0,_ => []
  | n+1,blob => if blob=0 then [] else
      (ps[(blob &&& 15)-1]?).toList ++ selectPrices ps n (blob >>> 4)
lemma prices_mem {x : Word} {ps : List (Price x)} {n blob p} (h : p∈selectPrices ps n blob) : p∈ps := by
  induction n generalizing blob with
  | zero => contradiction
  | succ n ih =>
    simp only [selectPrices] at h
    split at h
    · contradiction
    rcases List.mem_append.mp h with a|b
    · exact List.mem_of_getElem? (Option.mem_toList.mp a)
    · exact ih b

def shapeCut {x : Word} {c : Charts x} (f : Frame c) :=
  if f.t=0 then tightConflict f else signCut f
lemma shape_sound {x : Word} {c : Charts x} {f : Frame c} (v : f.Valid) (h : shapeCut f=true) : f.No := by
  unfold shapeCut at h; split at h
  · exact tight_sound v h
  · exact sign_cut v h

def localClose {x : Word} {c : Charts x} (root : Frame c) (next : Rows) (rot : Array (Rotation root))
    (d num links : ℕ) (f : Frame c) :=
  f.ps.any (cheapCut f.b f.v) || shapeCut f ||
    (links != 0 && linkBits root next rot d num (glimpse f) f 100 links)
lemma local_close {x : Word} {c : Charts x} {root f : Frame c} {next : Rows} {rot d num links}
    (v : f.Valid) (gn : Region root d num next) (h : localClose root next rot d num links f=true) : f.No := by
  rcases Bool.or_eq_true_iff.mp h with h|h
  · rcases Bool.or_eq_true_iff.mp h with h|h
    · exact cheap_cut v h
    · exact shape_sound v h
  · exact links_valid gn (Bool.and_eq_true_iff.mp h).2

def atlasRow {x : Word} {c : Charts x} (root : Frame c) (d : ℕ) (rows next : Rows)
    (num : ℕ) (rot : Array (Rotation root)) (i : ℕ) :=
  let pack:=fetchRow rows i >>> (12*d)
  (root.replay d (tapeAt rows d i)).all (fun f =>
    let g:Frame c:={f with ps:=selectPrices f.ps 10 (pack &&& 0xffffffffff)}
    !(g.v.any (fun w=>w.w==x)) && scan g (localClose root next rot (d+1) num (pack >>> 40)))

lemma atlas_sound {x : Word} {c : Charts x} (hx : proper x) (root : Frame c) (v : root.Valid)
    (d n num : ℕ) (rows next : Rows) (rot : Array (Rotation root))
    (gn : Region root (d+1) num next) (h : Span (atlasRow root d rows next num rot) 0 n) : Region root d n rows := by
  intro i hi f ef
  have good:=Frame.replay_valid v ef
  let pack:=fetchRow rows i >>> (12*d)
  let g:Frame c:={f with ps:=selectPrices f.ps 10 (pack &&& 0xffffffffff)}
  have gv : g.Valid:=⟨good.1,fun p hp=>good.2 p (prices_mem hp)⟩
  have ck:=h i (Nat.zero_le _) hi
  simp only [atlasRow,ef,Option.all_some] at ck
  obtain ⟨none,run⟩ := Bool.and_eq_true_iff.mp ck
  intro he
  rcases descend c hx he with hm|⟨s,hs,el,nxt⟩
  · obtain ⟨w,hw,eq⟩:=Step.mem_wires.mp hm
    have found : f.v.any (fun z=>z.w==x)=true:=List.any_eq_true.mpr ⟨w,hw,beq_iff_eq.mpr eq⟩
    simp [found] at none
  · have ok:=scan_sound (f:=g) run gv.1 hs el nxt
    exact local_close (Frame.child_valid gv el (Step.all_legal hs)) gn ok nxt
end Replay2161
