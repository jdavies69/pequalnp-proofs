import FastStages
namespace Replay2161
set_option maxHeartbeats 0
set_option maxRecDepth 100000

abbrev Tiny := BitVec 6
structure TracePoint where
  row : Fin 6 → Fin 512

def TracePoint.sig (p : TracePoint) (w : Word) : Tiny :=
  BitVec.ofBoolListBE [bit w (p.row 5),bit w (p.row 4),bit w (p.row 3),
    bit w (p.row 2),bit w (p.row 1),bit w (p.row 0)]

lemma sig_bit (p : TracePoint) (w : Word) (i : Fin 6) : (p.sig w)[i.val] = bit w (p.row i) := by
  let rows := [bit w (p.row 5),bit w (p.row 4),bit w (p.row 3),bit w (p.row 2),bit w (p.row 1),bit w (p.row 0)]
  have q := BitVec.getElem_ofBoolListBE (bs:=rows) (i:=i.val) (show i.val<rows.length from i.isLt)
  exact q.trans (by fin_cases i <;> rfl)

lemma sig_combine (p : TracePoint) (d : Bool) (a b : Word) :
    p.sig (combine d a b) = if d then p.sig a ||| p.sig b else p.sig a &&& p.sig b := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  let i : Fin 6 := ⟨j,hj⟩
  rw [sig_bit p (combine d a b) i,bit_bin]
  cases d <;> simp only [Bool.false_eq_true,ite_false,ite_true,BitVec.getElem_and,BitVec.getElem_or] <;> rw [←sig_bit p a i,←sig_bit p b i]

def allowed (a b : Bool) (s : Tiny) : Bool :=
  (if a then (if b then 0xfffffffffdffffff else 0xdddddddd0000dddd)
    else (if b then 0xf5f5f5f500f500f5 else 0xd5d5d5d5000000d5) : ℕ).testBit s.toNat

lemma allowed_join : ∀ (a b c d : Bool) (s t : Tiny) (op : Bool),
    (a && c)=false → (b && d)=false → allowed a b s=true → allowed c d t=true →
    allowed (a||c) (b||d) (if op then s ||| t else s &&& t)=true := by decide +kernel

def mergeMark (a b z w : Word) := if w=a ∨ w=b then z else w

lemma rof_live {x : Word} (p : TracePoint) {n t S} (live : Live x n t S) (zero : t=0)
    (full : S.card=n+1) (A B : Word) (memA : A∈S) (memB : B∈S)
    (ok : ∀ w∈S, allowed (w==A) (w==B) (p.sig w)=true) :
    allowed true true (p.sig x)=true := by
  induction live generalizing A B with
  | done =>
    obtain rfl := Finset.mem_singleton.mp memA
    obtain rfl := Finset.mem_singleton.mp memB
    simpa using ok _ (Finset.mem_singleton_self _)
  | unary _ _ _ ih => omega
  | @binary n t U a b d pa pb ab fresh tail ih =>
    let z := combine d a b
    have zU : z∉U := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have cap := count_live tail
    rw [Finset.card_insert_of_notMem zU] at cap
    have hbU : b∉U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at full
      have bind := Finset.card_insert_le a U
      omega
    have hbcard := Finset.card_insert_of_notMem hbU
    have haB : a∉insert b U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at full
      omega
    rw [Finset.card_insert_of_notMem haB,hbcard] at full
    have member (w : Word) (pw : w∈insert a (insert b U)) :
        mergeMark a b z w ∈ insert z U := by
      by_cases eq : w=a ∨ w=b
      · simp [mergeMark,eq]
      · have hu : w∈U := ((Finset.mem_insert.mp ((Finset.mem_insert.mp pw).resolve_left (not_or.mp eq).1)).resolve_left (not_or.mp eq).2)
        simp [mergeMark,eq,hu]
    have mz (w : Word) (pw : w∈insert a (insert b U)) :
        (z==mergeMark a b z w) = ((a==w) || (b==w)) := by
      have zw : z≠w := fun e => fresh (show z∈insert a (insert b U) by rwa [e])
      by_cases e1 : w=a
      · simp [mergeMark,e1]
      by_cases e2 : w=b
      · simp [mergeMark,e2]
      simp only [mergeMark,e1,e2,or_self,ite_false]
      rw [beq_eq_false_iff_ne.mpr zw,beq_eq_false_iff_ne.mpr (Ne.symm e1),beq_eq_false_iff_ne.mpr (Ne.symm e2)]
      rfl
    have normal (u w : Word) (uU : u∈U) :
        (u==mergeMark a b z w)=(u==w) := by
      have ua : u≠a := by rintro rfl; exact haB (Finset.mem_insert_of_mem uU)
      have ub : u≠b := by rintro rfl; exact hbU uU
      have uz : u≠z := by rintro rfl; exact zU uU
      by_cases e1 : w=a <;> by_cases e2 : w=b <;> simp_all [mergeMark]
    apply ih zero (by rw [Finset.card_insert_of_notMem zU]; omega)
      (mergeMark a b z A) (mergeMark a b z B) (member A memA) (member B memB)
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl|hw
    · change allowed (z==_) (z==_) (p.sig (combine d a b))=true
      rw [mz A memA,mz B memB,sig_combine]
      apply allowed_join
      · by_cases h : a=A
        · have nb : b≠A := by rintro e; exact ab (h.trans e.symm)
          simp [h,nb]
        · simp [h]
      · by_cases h : a=B
        · have nb : b≠B := by rintro e; exact ab (h.trans e.symm)
          simp [h,nb]
        · simp [h]
      · exact ok a (Finset.mem_insert_self ..)
      · exact ok b (Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
    · rw [normal w A hw,normal w B hw]
      exact ok w (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hw))

end Replay2161
