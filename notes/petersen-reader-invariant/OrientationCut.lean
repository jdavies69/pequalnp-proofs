import PEqualNP.Outside.L_meta_1667
import Grant

namespace PetersenOrientation
open Replay2161

theorem countKinds {x n t S} (h : PEqualNP.Outside.L_meta_1667.Live x n t S) :
    ∃ b, n=b+t ∧ Live x b t S := by
  induction h with
  | stop _ => exact ⟨0,rfl,Live.done⟩
  | @unary n t U a ha hf _ ih =>
    obtain ⟨b,hb,live⟩ := ih
    exact ⟨b,by omega,Live.unary ha hf live⟩
  | @binary n t U a b d ha hb ne fresh _ ih =>
    obtain ⟨m,hm,live⟩ := ih
    exact ⟨m+1,by omega,Live.binary ha hb ne fresh live⟩

theorem excludeNear {x : Word} {S : Finset Word} {k : Nat}
    (width : k ≤ S.card) (signed : ¬Once x S) (shared : ¬Shared x S) :
    PEqualNP.Outside.L_meta_1667.Impossible x k S := by
  intro n t hn run
  obtain ⟨b,count,live⟩ := countKinds run
  by_cases zero : t=0
  · exact shared (shared_of_width live zero (by omega))
  · have bound := count_live live
    exact signed (once_of_tight live (by omega))

def Witness := Sum (Fin 512 × Fin 512) (ℕ × ℕ × TracePoint)
def orientationMask (x : Word) (ws : List Word) : Witness → ℕ
  | .inl (i,j) =>
    if rises x i j then patterns (fun w sign => !(rises (signedWord w sign) i j)) ws else 0
  | .inr (i,j,p) =>
    match ws[i]?,ws[j]? with
    | some a,some b => if p.sig x=25 then
        patterns (fun w sign => allowed (w==a) (w==b) (p.sig (signedWord w sign))) ws else 0
    | _,_ => 0

private noncomputable def signOf (t : ReadTree) (w : Word) : Bool := by
  classical exact decide (t.has w true)

theorem orientation_clean (x : Word) (ws : List Word) (t : ReadTree) (value : t.value=x)
    (one : ∀ w, t.hits w=if w∈ws.toFinset then 1 else 0) (r : Witness) :
    (orientationMask x ws r).testBit (picked (signOf t) ws)=false := by
  have known {w s} (used : t.has w s) : w ∈ ws ∧ signOf t w=s := by
    have present := ReadTree.has_hit used
    have here : w ∈ ws := by by_contra h; simp [one,h] at present
    refine ⟨here,?_⟩
    classical
    cases s
    · have no : ¬ t.has w true := fun ht => Bool.noConfusion (t.one_sign (by rw [one,if_pos (List.mem_toFinset.mpr here)]) ht used)
      simp [signOf,no]
    · simp [signOf,used]
  by_contra bad
  have hit := Bool.eq_true_of_not_eq_false bad
  rcases r with ⟨i,j⟩|⟨i,j,p⟩
  · simp only [orientationMask] at hit
    split at hit
    next ok =>
      obtain ⟨a,s,use,up,dn⟩ := t.separating i j (value ▸ (parts_rise ok).1) (value ▸ (parts_rise ok).2)
      obtain ⟨mem,eq⟩ := known use
      have no := pattern_true _ _ _ hit a mem
      simp [eq,rises_of up dn] at no
    next => simp at hit
  · simp only [orientationMask] at hit
    cases aeq : ws[i]? with
    | none => simp [aeq] at hit
    | some a =>
      cases beq : ws[j]? with
      | none => simp [aeq,beq] at hit
      | some b =>
        simp only [aeq,beq] at hit
        split at hit
        next goal =>
          have ca : t.hits a=1 := by rw [one,if_pos (List.mem_toFinset.mpr (List.mem_of_getElem? aeq))]
          have cb : t.hits b=1 := by rw [one,if_pos (List.mem_toFinset.mpr (List.mem_of_getElem? beq))]
          have fails := t.marks p a b ca.le cb.le (by
            intro w s hs
            obtain ⟨hm,eq⟩ := known hs
            simpa only [eq] using pattern_true _ _ _ hit w hm)
          rw [value,goal,ca,cb] at fails
          exact (by decide : allowed true true 25 ≠ true) fails
        next => simp at hit

def cover (x : Word) (ws : List Word) : List Witness → ℕ
  | [] => 0
  | a::as => orientationMask x ws a ||| cover x ws as

theorem noSigned (x : Word) (ws : List Word) (rs : List Witness)
    (full : cover x ws rs = 2^(2^ws.length)-1) : ¬Once x ws.toFinset := by
  rintro ⟨t,eq,hits⟩
  have clean (rules : List Witness) : (cover x ws rules).testBit (picked (signOf t) ws)=false := by
    induction rules with
    | nil => simp [cover]
    | cons a more ih => rw [cover,Nat.testBit_or,orientation_clean x ws t eq hits,ih];rfl
  have bad := clean rs
  rw [full,Nat.testBit_two_pow_sub_one] at bad
  exact (of_decide_eq_false bad) (picked_lt _ _)

end PetersenOrientation
#print axioms PetersenOrientation.excludeNear
#print axioms PetersenOrientation.noSigned
