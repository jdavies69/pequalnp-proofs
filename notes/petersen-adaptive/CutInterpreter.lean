import TightCertificate

namespace PetersenOrientation
open Replay2161
abbrev NatTab := ℕ → ℕ

def witnessAt (dict : Rows) (token : ℕ) : Witness :=
  let data := fetchRow dict (token >>> 8)
  let b := data >>> 1
  if data.testBit 0 then .inr (token &&& 15,(token >>> 4) &&& 15,localPoint b)
  else .inl (chartIndex b 0,chartIndex b 1)

def tokenList (tab : NatTab) : ℕ → ℕ → List ℕ
  | 0,_ => []
  | n+1,blob => if blob=0 then [] else tab (blob &&& 16383)::tokenList tab n (blob >>> 14)

def sharedCover {x : Word} {c : Charts x} (v : List (Wire c)) (dict : Rows) : List ℕ → ℕ
  | [] => 0
  | u::us => ruleMask v dict u ||| sharedCover v dict us

lemma sharedClean {x : Word} {c : Charts x} (v : List (Wire c)) (M : ModuleView x (wires v))
    (dict : Rows) (ts : List ℕ) :
    (sharedCover v dict ts).testBit (picked (fun w=>M.chosen w.w) v)=false := by
  induction ts with
  | nil => simp [sharedCover]
  | cons a l ih => rw [sharedCover,Nat.testBit_or,rule_clean v M,ih]; rfl

def graphWires (ws : List Word) := ws.map (liftWire (x:=PEqualNP.Outside.L_meta_1667.graph) 3 0
  (by decide +kernel) (by decide +kernel))

lemma graphWires_eq (ws : List Word) : wires (graphWires ws)=ws.toFinset := by
  simp [graphWires,wires,List.map_map,liftWire,Function.comp_def]

lemma sharedExclusion (ws : List Word) (dict : Rows) (ts : List ℕ)
    (full : sharedCover (graphWires ws) dict ts=2^(2^ws.length)-1) :
    ¬ Shared PEqualNP.Outside.L_meta_1667.graph ws.toFinset := by
  rintro ⟨u,w,eq,counts⟩
  let M : ModuleView _ (wires (graphWires ws)) := ⟨u,w,eq,by simpa only [graphWires_eq] using counts⟩
  have bad := sharedClean _ M dict ts
  rw [full,Nat.testBit_two_pow_sub_one] at bad
  exact (of_decide_eq_false bad) (by simpa [graphWires] using picked_lt (fun w=>M.chosen w.w) (graphWires ws))

open PEqualNP.Outside.L_meta_1667 in
def runCertificate (dict : Rows) (tokens programs index : NatTab) (k : ℕ) (raw : List Word) : Bool :=
  let ws := raw.mergeSort (fun a b => decide (a.toNat ≤ b.toNat))
  let code := index (keySet raw)
  decide raw.Nodup && (if code.testBit 0 then
    decide (k+1 ≤ ws.length) && positiveCut graph ws (witnessAt dict (tokens (code >>> 1)))
  else
    let a := tokenList tokens 64 (programs ((code >>> 1) &&& 16383))
    let b := tokenList tokens 64 (programs (code >>> 15))
    decide (k ≤ ws.length) &&
      cover graph ws (a.map (witnessAt dict)) == 2^(2^ws.length)-1 &&
      sharedCover (graphWires ws) dict b == 2^(2^ws.length)-1)

open PEqualNP.Outside.L_meta_1667 in
theorem runCertificate_sound (dict : Rows) (tokens programs index : NatTab) (k : ℕ) (raw : List Word)
    (checked : runCertificate dict tokens programs index k raw=true) : Impossible graph k raw.toFinset := by
  let ws := raw.mergeSort (fun a b => decide (a.toNat ≤ b.toNat))
  have perm : ws.Perm raw := List.mergeSort_perm _ _
  have sets : ws.toFinset=raw.toFinset := by ext w; simp only [List.mem_toFinset]; exact perm.mem_iff
  obtain ⟨nd,ok⟩ := Bool.and_eq_true_iff.mp checked
  have count : ws.toFinset.card=ws.length := List.toFinset_card_of_nodup (perm.nodup_iff.mpr (of_decide_eq_true nd))
  rw [←sets]
  dsimp only [runCertificate] at checked
  split at ok
  · obtain ⟨sz,cut⟩ := Bool.and_eq_true_iff.mp ok
    apply noTight (count ▸ of_decide_eq_true sz)
    exact positiveCutSound cut
  · obtain ⟨first,last⟩ := Bool.and_eq_true_iff.mp ok
    obtain ⟨sz,signed⟩ := Bool.and_eq_true_iff.mp first
    exact excludeNear (count ▸ of_decide_eq_true sz) (noSigned _ _ _ (beq_iff_eq.mp signed))
      (sharedExclusion _ _ _ (beq_iff_eq.mp last))
end PetersenOrientation
#print axioms PetersenOrientation.runCertificate_sound
