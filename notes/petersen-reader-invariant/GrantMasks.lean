import Near
namespace PetersenReaderNear
open Replay2161 PetersenOrientation PEqualNP.Outside.L_meta_1667
def loc (t : Nat) := t >>> 10
def iPin (t : Nat) := (t >>> 2) &&& 15
def jPin (t : Nat) := (t >>> 6) &&& 15
def proofHint (t : Nat) : Witness :=
  if t.testBit 0 then Sum.inr (iPin t,jPin t,localPoint (loc t))
  else Sum.inl (chartIndex (loc t) 0, chartIndex (loc t) 1)

def cell {x : Word} {c : Charts x} (ws : List (Wire c)) (t : Nat) :=
  if t.testBit 0 then edgeMask ws (iPin t) (jPin t) (localPoint (loc t))
  else orderMask ws (chartIndex (loc t) 0) (chartIndex (loc t) 1)
    (chartIndex (loc t) 2) (chartIndex (loc t) 3)
def unionCells {x : Word} {c : Charts x} (ws : List (Wire c)) : List Nat → Nat
  | [] => 0
  | x::xs => cell ws x ||| unionCells ws xs

theorem unionClean {x : Word} {c : Charts x} (ws : List (Wire c)) (M : ModuleView x (wires ws)) (rs : List Nat) :
    (unionCells ws rs).testBit (picked (fun w => M.chosen w.w) ws)=false := by
  induction rs with
  | nil => simp [unionCells]
  | cons a as ih =>
    rw [unionCells,Nat.testBit_or,ih]
    simp only [Bool.or_false,cell]
    split
    · exact edge_clean ws M .. 
    · exact order_clean ws M ..

theorem noShare {x : Word} (a b : Fin 512) (ha : Replay2161.bit x a = true) (hb : Replay2161.bit x b = false)
    (ws : List Word) (rs : List Nat)
    (cover : unionCells (ws.map (liftWire a b ha hb)) rs = 2^(2^ws.length)-1) :
    ¬ Shared x ws.toFinset := by
  let v := ws.map (liftWire a b ha hb)
  have same : wires v = ws.toFinset := by simp [v,wires,List.map_map,liftWire,Function.comp_def]
  rintro ⟨u,w,eq,counts⟩
  let M : ModuleView x (wires v) := ⟨u,w,eq,by simpa only [same] using counts⟩
  have bad := unionClean v M rs
  change unionCells v rs = _ at cover
  rw [cover,Nat.testBit_two_pow_sub_one] at bad
  exact (of_decide_eq_false bad) (by simpa [v] using picked_lt (fun w => M.chosen w.w) v)

structure GrantSet where
  signed : List Nat
  moduleRows : List Nat

def graph : Word := targetOf g383
theorem pos : Replay2161.bit graph 3=true := by decide +kernel
theorem neg : Replay2161.bit graph 0=false := by decide +kernel

def grantCheck (cap : Nat) (ws : List Word) (g : GrantSet) :=
  decide ws.Nodup &&
  (if ws.length = cap+1 then thin graph ws (proofHint (g.signed.headD 0))
  else ws.length == cap &&
    cover graph ws (g.signed.map proofHint) == 2^(2^ws.length)-1 &&
    unionCells (ws.map (liftWire 3 0 pos neg)) g.moduleRows == 2^(2^ws.length)-1)

theorem grantSafe {k : Nat} {ws : List Word} {g : GrantSet} (h : grantCheck k ws g=true) :
    Impossible graph k ws.toFinset := by
  obtain ⟨nd,pr⟩ := Bool.and_eq_true_iff.mp h
  have hnd := of_decide_eq_true nd
  split at pr
  next width => exact thinOK hnd width _ pr
  next =>
    obtain ⟨⟨w,sg⟩,sh⟩ := (Bool.and_eq_true_iff.mp pr).imp_left Bool.and_eq_true_iff.mp
    apply excludeNear
    · rw [List.toFinset_card_of_nodup hnd,beq_iff_eq.mp w]
    · exact noSigned _ _ _ (beq_iff_eq.mp sg)
    · exact noShare 3 0 pos neg _ _ (beq_iff_eq.mp sh)
end PetersenReaderNear
#print axioms PetersenReaderNear.grantSafe
