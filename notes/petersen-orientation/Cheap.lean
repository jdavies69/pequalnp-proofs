import FastStages
namespace Replay2161
def countConst {x : Word} {c : Charts x} (m : Word) : List (Wire c) → ℕ
  | [] => 0
  | a::l => if maskedConst m a.w then (countConst m l)+1 else countConst m l

lemma count_const {x : Word} {c : Charts x} (f : Basis x) (v : List (Wire c)) :
    countConst f.mask v=loss f v := by
  induction v with
  | nil => rfl
  | cons a l ih =>
    cases e : maskedConst f.mask a.w <;> simp_all [countConst,loss,List.filter_cons]

def cheapCut {x : Word} {c : Charts x} (b : ℕ) (v : List (Wire c)) (p : Price x) :=
  let need := p.basis.lo+countConst p.basis.mask v
  decide (b<need) && decide (b+p.spent<need)

lemma cheap_sound_cut {x : Word} {c : Charts x} {b} {v : List (Wire c)} {p : Price x}
    (ok : cheapCut b v p=true) : p.cuts b v=true := by
  have q := (Bool.and_eq_true_iff.mp ok).2
  simpa only [Price.cuts,count_const] using q

def Cheap {x : Word} {c : Charts x} (known : Frame c → Bool) : ℕ → Frame c → Bool
  | 0,f => f.ps.any (cheapCut f.b f.v) || known f
  | k+1,f => f.ps.any (cheapCut f.b f.v) ||
      (!(f.v.any (fun a => a.w == x)) && scan f (Cheap known k))

lemma cheap_cut {x : Word} {c : Charts x} {f : Frame c} (v : f.Valid)
    (h : f.ps.any (cheapCut f.b f.v)=true) : f.No := by
  obtain ⟨p,hp,hc⟩ := List.any_eq_true.mp h
  exact cut_sound v.1 (v.2 _ hp) (cheap_sound_cut hc)
lemma cheap_sound {x : Word} {c : Charts x} (known : Frame c → Bool) (good : ∀ f, known f=true → f.No)
    (hx : proper x) (d : ℕ) {f : Frame c} (valid : f.Valid) (ok : Cheap known d f = true) : f.No := by
  induction d generalizing f with
  | zero =>
    rcases Bool.or_eq_true_iff.mp ok with h|h
    · exact cheap_cut valid h
    · exact good _ h
  | succ n ih =>
    rcases Bool.or_eq_true_iff.mp ok with h|q
    · exact cheap_cut valid h
    obtain ⟨no,rows⟩ := Bool.and_eq_true_iff.mp q
    intro hex
    rcases descend c hx hex with hm | ⟨s,hs,el,ht⟩
    · obtain ⟨w,hw,e⟩ := Step.mem_wires.mp hm
      have yes : f.v.any (fun a => a.w == x) = true := List.any_eq_true.mpr ⟨w,hw,beq_iff_eq.mpr e⟩
      simp [yes] at no
    · exact ih (Frame.child_valid valid el (Step.all_legal hs)) (scan_sound rows valid.1 hs el ht) ht

end Replay2161
