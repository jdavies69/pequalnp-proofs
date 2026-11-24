import ReadOnce
namespace Replay2161
set_option maxRecDepth 100000
set_option maxHeartbeats 0
abbrev Patch := BitVec 36
def lane (v : Word) (n : ℕ) : Patch := v.extractLsb' n 36

def patchPoint {x : Word} (c : Charts x) (k : Fin 36) : TracePoint :=
  ⟨![c.p ⟨k.val, by omega⟩,c.n ⟨k.val,by omega⟩,c.n ⟨36+k.val,by omega⟩,
     c.p ⟨36+k.val,by omega⟩,c.p ⟨72+k.val,by omega⟩,c.n ⟨72+k.val,by omega⟩]⟩

def pGrey {x : Word} {c : Charts x} (w : Wire c) : Patch :=
  (~~~(lane w.p 0) ||| (lane w.n 0 &&& lane w.n 36)) &&&
  (~~~(lane w.p 36 ||| lane w.p 72) ||| lane w.n 72)
def pLeft {x : Word} {c : Charts x} (w : Wire c) : Patch := lane w.n 0 &&& ~~~(lane w.p 72)
def pRight {x : Word} {c : Charts x} (w : Wire c) : Patch := lane w.n 36 &&& ~~~(lane w.p 36)

def wordGrey (s : Tiny) := (!s[0] || (s[1] && s[2])) && (!(s[3] || s[4]) || s[5])
def wordLeft (s : Tiny) := s[1] && !s[4]
def wordRight (s : Tiny) := s[2] && !s[3]
lemma legal_grey : ∀ s, wordGrey s=true → allowed false false s=true := by decide +kernel
lemma legal_left : ∀ s, wordLeft s=true → allowed true false s=true := by decide +kernel
lemma legal_right : ∀ s, wordRight s=true → allowed false true s=true := by decide +kernel

lemma lane_bit (v : Word) (n : ℕ) (k : Fin 36) (h : n+k.val < 512) :
   (lane v n)[k.val] = bit v ⟨n+k.val,h⟩ := by
  exact (BitVec.getElem_extractLsb' (x:=v) (start:=n) k.isLt).trans (BitVec.getLsbD_eq_getElem h)

lemma patch_extract {x : Word} {c : Charts x} (w : Wire c) (k : Fin 36) :
    (pGrey w)[k.val] = wordGrey ((patchPoint c k).sig w.w) ∧
    (pLeft w)[k.val] = wordLeft ((patchPoint c k).sig w.w) ∧
    (pRight w)[k.val] = wordRight ((patchPoint c k).sig w.w) := by
  have point (j : ℕ) (h : j<6) : ((patchPoint c k).sig w.w)[j]=bit w.w ((patchPoint c k).row ⟨j,h⟩) := sig_bit (patchPoint c k) w.w ⟨j,h⟩
  simp only [wordGrey,wordLeft,wordRight,pGrey,pLeft,pRight,BitVec.getElem_and,BitVec.getElem_or,
    BitVec.getElem_not,lane_bit _ 0 k (by omega),lane_bit _ 36 k (by omega),lane_bit _ 72 k (by omega)]
  rw [point 0 (by decide),point 1 (by decide),point 2 (by decide),point 3 (by decide),point 4 (by decide),point 5 (by decide)]
  simp only [w.hp,w.hn,Nat.zero_add]
  exact ⟨rfl,rfl,rfl⟩

lemma patch_target {x : Word} (c : Charts x) (k : Fin 36) : (patchPoint c k).sig x=25 := by
  have q (i : Fin 6) : bit x ((patchPoint c k).row i) = (25 : Tiny)[i.val] := by
    fin_cases i <;> first | exact c.hp _ | exact c.hn _
  apply BitVec.eq_of_getElem_eq
  intro j hj
  exact (sig_bit (patchPoint c k) x ⟨j,hj⟩).trans (q ⟨j,hj⟩)

def greyRest {x : Word} {c : Charts x} (a b : Word) : List (Wire c) → Patch
  | [] => BitVec.allOnes 36
  | w::v => if w.w==a || w.w==b then greyRest a b v else pGrey w &&& greyRest a b v

def findConflict {x : Word} {c : Charts x} (v : List (Wire c)) :=
  v.any (fun a => v.any (fun b => a.w != b.w &&
    (pLeft a &&& pRight b &&& greyRest a.w b.w v) != 0))

lemma uncovered {u : Patch} (neq : u≠0) : ∃ k : Fin 36, u[k.val]=true := by
  by_contra! no
  apply neq
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have q := no ⟨j,hj⟩
  cases h : u[j] <;> simp_all

lemma rest_grey {x : Word} {c : Charts x} {a b : Word} {v : List (Wire c)} {k : Fin 36}
    (ok : (greyRest a b v)[k.val]=true) (w : Wire c) (inV : w∈v)
    (wa : w.w≠a) (wb : w.w≠b) : (pGrey w)[k.val]=true := by
  induction v with
  | nil => contradiction
  | cons h l ih =>
    cases e : (h.w==a || h.w==b)
    · rw [greyRest,e] at ok
      have val : (pGrey h &&& greyRest a b l)[k.val]=true := ok
      rw [BitVec.getElem_and] at val
      have two := Bool.and_eq_true_iff.mp val
      rcases List.mem_cons.mp inV with rfl|hw
      · exact two.1
      · exact ih two.2 hw
    · rw [greyRest,e] at ok
      apply ih ok
      apply (List.mem_cons.mp inV).resolve_left
      rintro rfl
      simp [beq_eq_false_iff_ne.mpr wa,beq_eq_false_iff_ne.mpr wb] at e

lemma no_readOnce {x : Word} {c : Charts x} {v : List (Wire c)} {b : ℕ}
    (nd : (v.map Wire.w).Nodup) (width : b+1=v.length) (hit : findConflict v=true) :
    ¬Exact x b 0 (wires v) := by
  rintro ⟨n,hn,t,ht,h⟩
  have card : (wires v).card=v.length := by
    change (v.map Wire.w).toFinset.card=v.length
    rw [List.toFinset_card_of_nodup nd,List.length_map]
  have cap := count_live h
  have eq : (wires v).card=n+1 := by omega
  obtain ⟨a,ha,yy⟩ := List.any_eq_true.mp hit
  obtain ⟨d,hd,yy⟩ := List.any_eq_true.mp yy
  obtain ⟨ad,mask⟩ := Bool.and_eq_true_iff.mp yy
  obtain ⟨k,hk⟩ := uncovered (bne_iff_ne.mp mask)
  rw [BitVec.getElem_and,BitVec.getElem_and] at hk
  obtain ⟨both,rest⟩ := Bool.and_eq_true_iff.mp hk
  obtain ⟨left,right⟩ := Bool.and_eq_true_iff.mp both
  have valid := rof_live (patchPoint c k) h (by omega) eq a.w d.w
    (Step.mem_wires.mpr ⟨a,ha,rfl⟩) (Step.mem_wires.mpr ⟨d,hd,rfl⟩)
  have bad := valid (by
    intro y hy; obtain ⟨u,hu,rfl⟩ := Step.mem_wires.mp hy
    by_cases ea : u.w=a.w
    · rw [ea,beq_self_eq_true,beq_eq_false_iff_ne.mpr (bne_iff_ne.mp ad)]
      exact legal_left _ ((patch_extract a k).2.1 ▸ left)
    by_cases eb : u.w=d.w
    · rw [eb,beq_self_eq_true,beq_eq_false_iff_ne.mpr (Ne.symm (bne_iff_ne.mp ad))]
      exact legal_right _ ((patch_extract d k).2.2 ▸ right)
    rw [beq_eq_false_iff_ne.mpr ea,beq_eq_false_iff_ne.mpr eb]
    apply legal_grey
    rw [←(patch_extract u k).1]
    exact rest_grey rest u hu ea eb)
  rw [patch_target] at bad
  exact (by decide : allowed true true 25 ≠ true) bad

end Replay2161
