import FlexMarks
import SignedTree
namespace Replay2161

def turned {x : Word} {c : Charts x} (w : Wire c) (s : Bool) : Wire c := if s then w.flip else w
lemma turned_word {x : Word} {c : Charts x} (w : Wire c) (s : Bool) : (turned w s).w=signedWord w.w s := by cases s <;> rfl

def adverse {x : Word} {c : Charts x} (single : Word) (w : Wire c) (s : Bool) :=
  let a:=turned w s
  (a.n &&& ~~~a.p &&& single) != 0

def pairedMask {x : Word} {c : Charts x} (single : Word) (m : Wire c→Patch) (w : Wire c) :=
  (if adverse single w false then BitVec.allOnes 36 else m w) &&&
  (if adverse single w true then BitVec.allOnes 36 else m w.flip)

lemma paired_bit {x : Word} {c : Charts x} {w : Wire c} {single : Word} {k : Fin 36}
    {m : Wire c→Patch} {s : Bool} (h : (pairedMask single m w)[k.val]=true)
    (go : adverse single w s=false) : (m (turned w s))[k.val]=true := by
  rw [pairedMask,BitVec.getElem_and,Bool.and_eq_true] at h
  cases s
  · simpa only [go,Bool.false_eq_true,ite_false,turned] using h.1
  · simpa only [go,Bool.false_eq_true,ite_false,turned,ite_true] using h.2

lemma turns_diff {x : Word} {c : Charts x} {w : Wire c} {s : Bool} {i : Fin 512}
    (dif : bit (signedWord w.w s) (c.p i) ≠ bit (signedWord w.w s) (c.n i)) :
    bit (w.p ^^^ w.n) i=true := by
  rw [show bit (w.p ^^^ w.n) i=(bit w.p i ^^ bit w.n i) from BitVec.getElem_xor _,w.hp,w.hn]
  cases s <;> cases a : bit w.w (c.p i) <;> cases b : bit w.w (c.n i) <;>
    simp_all [signedWord,bit_not]

lemma sign_used {x : Word} {c : Charts x} {v : List (Wire c)} {t : ReadTree} (val : t.value=x)
    (hits : ∀ w, t.hits w=if w∈wires v then 1 else 0) {w : Wire c} (hw : w∈v) {s : Bool}
    (used : t.has w.w s) : adverse (~~~(diffWords v).2) w s=false := by
  by_contra! fail
  have neq : ((turned w s).n &&& ~~~(turned w s).p &&& ~~~(diffWords v).2)≠0 := bne_iff_ne.mp (Bool.eq_true_of_not_eq_false fail)
  obtain ⟨i,fi⟩ := marked_word neq
  have detail : (bit (turned w s).n i && !bit (turned w s).p i && !bit (diffWords v).2 i)=true := by simpa only [bit,BitVec.getElem_and,BitVec.getElem_not] using fi
  obtain ⟨first,unique⟩ := Bool.and_eq_true_iff.mp detail
  obtain ⟨down,nup⟩ := Bool.and_eq_true_iff.mp first
  have up : bit (signedWord w.w s) (c.p i)=false := by simpa only [←turned_word,(turned w s).hp,Bool.not_eq_true'] using nup
  have dn : bit (signedWord w.w s) (c.n i)=true := by simpa only [←turned_word,(turned w s).hn] using down
  obtain ⟨a,j,here,pa,na⟩ := t.separating (c.p i) (c.n i) (val ▸ c.hp i) (val ▸ c.hn i)
  by_cases eq : a=w.w
  · subst a
    have jm := t.one_sign (by rw [hits]; split <;> omega) here used
    simp [jm,up] at pa
  · have present : a∈wires v := by
      have q:=ReadTree.has_hit here; by_contra hm; simp [hits,hm] at q
    obtain ⟨u,hu,rfl⟩ := Step.mem_wires.mp present
    have d1:=turns_diff (w:=u) (s:=j) (i:=i) (by simp [pa,na])
    have d2:=turns_diff (w:=w) (s:=s) (i:=i) (by simp [up,dn])
    have two := (df_bit v i).2 u hu w hw eq d1 d2
    simp [two] at unique

def signCut {x : Word} {c : Charts x} (f : Frame c) :=
  f.b+1==f.v.length &&
    (let single:= ~~~(diffWords f.v).2
     let m:=pairedMask single
     (maskFold (m pGrey) (m pLeft) (m pRight) f.v).ab != 0)

lemma sign_cut {x : Word} {c : Charts x} {f : Frame c} (valid : f.Valid) (cut : signCut f=true) : f.No := by
  obtain ⟨width,hit⟩ := Bool.and_eq_true_iff.mp cut
  have width:=beq_iff_eq.mp width
  rintro ⟨n,hn,j,hj,live⟩
  have len : (wires f.v).card=f.v.length := by
    change (f.v.map Wire.w).toFinset.card=f.v.length
    rw [List.toFinset_card_of_nodup valid.1,List.length_map]
  have cap:=count_live live
  obtain ⟨t,val,hits⟩ := once_of_tight live (by omega)
  let single:= ~~~(diffWords f.v).2
  let m:=pairedMask (c:=c) single
  obtain ⟨k,hk⟩ := uncovered (bne_iff_ne.mp hit)
  obtain ⟨a,ha,z,hz,nz,pa,pz,gy⟩ := (mask_sound (m pGrey) (m pLeft) (m pRight) k f.v valid.1).2.2.2 hk
  have ah : t.hits a.w=1 := by rw [hits,if_pos (Step.mem_wires.mpr ⟨a,ha,rfl⟩)]
  have zh : t.hits z.w=1 := by rw [hits,if_pos (Step.mem_wires.mpr ⟨z,hz,rfl⟩)]
  have allok := t.marks (patchPoint c k) a.w z.w ah.le zh.le (by
    intro w s hs
    have present : w∈wires f.v := by
      have q:=ReadTree.has_hit hs; by_contra h; simp [hits,h] at q
    obtain ⟨u,hu,rfl⟩ := Step.mem_wires.mp present
    have ok := sign_used val hits hu hs
    by_cases ua : u.w=a.w
    · rw [ua,beq_self_eq_true,beq_eq_false_iff_ne.mpr nz]
      have useA : t.has a.w s := ua ▸ hs
      have v := paired_bit pa (sign_used val hits ha useA)
      rw [←turned_word]
      exact legal_left _ ((patch_extract (turned a s) k).2.1 ▸ v)
    by_cases uz : u.w=z.w
    · rw [uz,beq_eq_false_iff_ne.mpr nz.symm,beq_self_eq_true]
      have useZ : t.has z.w s := uz ▸ hs
      have v := paired_bit pz (sign_used val hits hz useZ)
      rw [←turned_word]
      exact legal_right _ ((patch_extract (turned z s) k).2.2 ▸ v)
    · rw [beq_eq_false_iff_ne.mpr ua,beq_eq_false_iff_ne.mpr uz,←turned_word]
      have v := paired_bit (gy u hu ua uz) ok
      exact legal_grey _ ((patch_extract (turned u s) k).1 ▸ v))
  rw [val,patch_target,ah,zh] at allok
  exact (by decide : allowed true true 25 ≠ true) allok
end Replay2161
