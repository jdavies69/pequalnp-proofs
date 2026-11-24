import ModuleCertificate
namespace PetersenReaderNear
open Replay2161 PetersenOrientation PEqualNP.Outside.L_meta_1667

def thin (x : Word) (ws : List Word) : Witness → Bool
  | .inl (i,j) => rises x i j && ws.all (fun w => !(rises w i j))
  | .inr (i,j,p) => match ws[i]?, ws[j]? with
    | some a, some b => p.sig x == 25 && ws.all (fun w => allowed (w==a) (w==b) (p.sig w))
    | _,_ => false

theorem thinOK {x : Word} {ws : List Word} {k : Nat} (nd : ws.Nodup)
    (len : ws.length = k+1) (r : Witness) (ck : thin x ws r = true) :
    Impossible x k ws.toFinset := by
  intro n t hn run
  obtain ⟨b,hb,h⟩ := countKinds run
  have size := count_live h
  rw [List.toFinset_card_of_nodup nd] at size
  have z : t=0 := by omega
  have wid : ws.toFinset.card=b+1 := by rw [List.toFinset_card_of_nodup nd]; omega
  rcases r with ⟨i,j⟩|⟨i,j,p⟩
  · obtain ⟨up,unseen⟩ := Bool.and_eq_true_iff.mp ck
    obtain ⟨w,wm,sep⟩ := distinguishes_live h (parts_rise up).1 (parts_rise up).2
    simp only [z,distinguishes,ite_true] at sep
    have none := List.all_eq_true.mp unseen w (List.mem_toFinset.mp wm)
    simp [rises_of sep.1 sep.2] at none
  · simp only [thin] at ck
    cases ha : ws[i]? with
    | none => simp [ha] at ck
    | some a =>
      cases hb : ws[j]? with
      | none => simp [ha,hb] at ck
      | some b =>
        simp only [ha,hb] at ck
        obtain ⟨goal,ok⟩ := Bool.and_eq_true_iff.mp ck
        have conflict := rof_live p h z wid a b (List.mem_toFinset.mpr (List.mem_of_getElem? ha))
            (List.mem_toFinset.mpr (List.mem_of_getElem? hb)) (fun w wm => List.all_eq_true.mp ok w (List.mem_toFinset.mp wm))
        rw [beq_iff_eq.mp goal] at conflict
        exact (by decide : allowed true true 25 ≠ true) conflict
end PetersenReaderNear
#print axioms PetersenReaderNear.thinOK
