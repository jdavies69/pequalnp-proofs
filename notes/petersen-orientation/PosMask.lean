import Positive
namespace Replay2161
def diffWords {x : Word} {c : Charts x} : List (Wire c) → Word × Word
  | [] => (0,0)
  | w::v =>
    let r := diffWords v
    let d := w.p ^^^ w.n
    (d ||| r.1,(d &&& r.1) ||| r.2)

lemma df_bit {x : Word} {c : Charts x} (v : List (Wire c)) (i : Fin 512) :
    (∀ w ∈ v, bit (w.p ^^^ w.n) i=true → bit (diffWords v).1 i=true) ∧
    (∀ w ∈ v, ∀ u ∈ v, w.w≠u.w → bit (w.p ^^^ w.n) i=true → bit (u.p ^^^ u.n) i=true →
      bit (diffWords v).2 i=true) := by
  induction v with
  | nil => simp
  | cons h l ih =>
    obtain ⟨one,two⟩ := ih
    have bor (u z : Word) : bit (u ||| z) i = (bit u i || bit z i) := BitVec.getElem_or _
    have band (u z : Word) : bit (u &&& z) i = (bit u i && bit z i) := BitVec.getElem_and _
    simp only [diffWords,bor,band,Bool.or_eq_true,Bool.and_eq_true]
    constructor
    · intro w hw eq
      rcases List.mem_cons.mp hw with rfl|hw
      · exact Or.inl eq
      · exact Or.inr (one w hw eq)
    · intro w hw u hu ne pw pu
      rcases List.mem_cons.mp hw with rfl|hw
      · have ut := (List.mem_cons.mp hu).resolve_left (by rintro rfl; exact ne rfl)
        exact Or.inl ⟨pw,one u ut pu⟩
      rcases List.mem_cons.mp hu with rfl|hu
      · have tl : w∈l := (List.mem_cons.mp hw).resolve_left (by rintro rfl; exact ne rfl)
        exact Or.inl ⟨pu,one w tl pw⟩
      · exact Or.inr (two w hw u hu ne pw pu)

def allPositive {x : Word} {c : Charts x} (v : List (Wire c)) :=
  let single := ~~~(diffWords v).2
  v.all (fun w => (w.p &&& ~~~w.n &&& single) != 0)

lemma marked_word {q : Word} (n : q≠0) : ∃ i : Fin 512, bit q i=true := by
  by_contra! no
  apply n
  apply BitVec.eq_of_getElem_eq
  intro j h
  have z := no ⟨j,h⟩
  change bit q ⟨j,h⟩=bit 0 ⟨j,h⟩
  rw [bit_zero]
  cases eq : bit q ⟨j,h⟩ <;> simp_all

lemma positive_checked {x : Word} {c : Charts x} {v : List (Wire c)}
    (ok : allPositive v=true) : Positive x (wires v) := by
  intro a ha
  obtain ⟨w,hw,rfl⟩ := Step.mem_wires.mp ha
  have nz := List.all_eq_true.mp ok w hw
  obtain ⟨i,e⟩ := marked_word (bne_iff_ne.mp nz)
  have cast : bit (w.p &&& ~~~w.n &&& ~~~(diffWords v).2) i =
      ((bit w.p i && !bit w.n i) && !bit (diffWords v).2 i) := by
    simp only [bit,BitVec.getElem_and,BitVec.getElem_not]
  rw [cast] at e
  have ⟨a,e0⟩ := Bool.and_eq_true_iff.mp e
  have ⟨p,n⟩ := Bool.and_eq_true_iff.mp a
  have wn : bit w.n i=false := by simpa using n
  have wt : bit (w.p ^^^ w.n) i=true := by
    rw [show bit (w.p ^^^ w.n) i=(bit w.p i ^^ bit w.n i) from BitVec.getElem_xor _]
    simp [p,wn]
  refine ⟨c.p i,c.n i,c.hp i,c.hn i,(w.hp i) ▸ p,(w.hn i) ▸ wn,?_⟩
  intro u hu ne
  obtain ⟨z,hz,rfl⟩ := Step.mem_wires.mp hu
  rw [←z.hp i,←z.hn i]
  by_contra bad
  have dz : bit (z.p ^^^ z.n) i=true := by
    rw [show bit (z.p ^^^ z.n) i=(bit z.p i ^^ bit z.n i) from BitVec.getElem_xor _]
    cases e1 : bit z.p i <;> cases e2 : bit z.n i <;> simp_all
  have h2 := (df_bit v i).2 w hw z hz ne.symm wt dz
  simp [h2] at e0

def positiveConflict {x : Word} {c : Charts x} (f : Frame c) :=
  (f.b+1==f.v.length) && ((f.t==0 || (f.t==1 && allPositive f.v)) && (flagFold f.v).ab != 0)

lemma positive_conflict {x : Word} {c : Charts x} {f : Frame c} (valid : f.Valid)
    (ok : positiveConflict f=true) : f.No := by
  obtain ⟨width,rest⟩ := Bool.and_eq_true_iff.mp ok
  obtain ⟨tst,mask⟩ := Bool.and_eq_true_iff.mp rest
  have width := beq_iff_eq.mp width
  have no := certified_flags valid.1 width mask
  rcases Bool.or_eq_true_iff.mp tst with t|p
  · change ¬Exact x f.b f.t (wires f.v)
    rwa [beq_iff_eq.mp t]
  obtain ⟨one,positive⟩ := Bool.and_eq_true_iff.mp p
  have one := beq_iff_eq.mp one
  rintro ⟨b,hb,t,ht,h⟩
  have card : (wires f.v).card=f.v.length := by
    change (f.v.map Wire.w).toFinset.card=f.v.length
    rw [List.toFinset_card_of_nodup valid.1,List.length_map]
  have cap := count_live h
  have zero := tight_positive h (by omega) (by omega) (positive_checked positive)
  exact no ⟨b,hb,t,by omega,h⟩

end Replay2161
