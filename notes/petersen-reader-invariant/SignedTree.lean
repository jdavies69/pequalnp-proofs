import PosMask
namespace Replay2161

inductive ReadTree
  | atom (w : Word) (inv : Bool)
  | gate (d : Bool) (a b : ReadTree)

def signedWord (w : Word) (inv : Bool) := if inv then ~~~w else w
namespace ReadTree
def value : ReadTree → Word
  | atom w i => signedWord w i
  | gate d a b => combine d a.value b.value

def hits (w : Word) : ReadTree → ℕ
  | atom a _ => if a=w then 1 else 0
  | gate _ a b => a.hits w + b.hits w

def has (w : Word) (i : Bool) : ReadTree → Prop
  | atom a j => a=w ∧ j=i
  | gate _ a b => a.has w i ∨ b.has w i

lemma has_hit {t : ReadTree} {w i} (h : t.has w i) : 0<t.hits w := by
  induction t with
  | atom a j => obtain ⟨rfl,_⟩ := h; simp [hits]
  | gate d a b ia ib => rcases h with h|h <;> simp only [hits] <;> first | have := ia h; omega | have := ib h; omega

lemma one_sign (t : ReadTree) {w i j} (n : t.hits w ≤ 1) (p : t.has w i) (q : t.has w j) : i=j := by
  induction t with
  | atom a k => exact p.2.symm.trans q.2
  | gate d a b ai bi =>
    change a.hits w+b.hits w≤1 at n
    rcases p with p|p <;> rcases q with q|q
    · exact ai (by omega) p q
    · have := has_hit p; have := has_hit q; omega
    · have := has_hit p; have := has_hit q; omega
    · exact bi (by omega) p q

def splice (u : Word) (f : Bool → ReadTree) : ReadTree → ReadTree
  | atom a i => if a=u then f i else atom a i
  | gate d a b => gate d (a.splice u f) (b.splice u f)

lemma splice_value (t : ReadTree) (u : Word) (f : Bool → ReadTree)
    (ok : ∀ i, (f i).value=signedWord u i) : (t.splice u f).value=t.value := by
  induction t with
  | atom a i => by_cases e:a=u <;> simp [splice,value,e,ok]
  | gate d a b ia ib => simp only [splice,value,ia,ib]

lemma splice_hits (t : ReadTree) (u w : Word) (f : Bool → ReadTree) (m : ℕ)
    (ok : ∀ i, (f i).hits w=m) : (t.splice u f).hits w =
      (if w=u then 0 else t.hits w) + t.hits u*m := by
  induction t with
  | atom a i => cases i <;> by_cases e : a=u <;> by_cases q : w=u <;> simp_all [splice,hits,eq_comm] <;> omega
  | gate d a b ia ib =>
    simp only [splice,hits,ia,ib,Nat.add_mul]
    split <;> omega

lemma separating (t : ReadTree) (i j : Fin 512) (p : bit t.value i=true) (q : bit t.value j=false) :
    ∃ w s, t.has w s ∧ bit (signedWord w s) i=true ∧ bit (signedWord w s) j=false := by
  induction t with
  | atom w s => exact ⟨w,s,⟨rfl,rfl⟩,p,q⟩
  | gate d a b ia ib =>
    simp only [value,bit_bin] at p q
    have aux : (bit a.value i=true ∧ bit a.value j=false) ∨ (bit b.value i=true ∧ bit b.value j=false) := by
      cases d <;> cases h : bit a.value i <;> cases h' : bit a.value j <;> simp_all
    rcases aux with h|h
    · obtain ⟨w,s,z,e₁,e₂⟩ := ia h.1 h.2; exact ⟨w,s,Or.inl z,e₁,e₂⟩
    · obtain ⟨w,s,z,e₁,e₂⟩ := ib h.1 h.2; exact ⟨w,s,Or.inr z,e₁,e₂⟩

lemma marks (t : ReadTree) (p : TracePoint) (A B : Word) (ca : t.hits A≤1) (cb : t.hits B≤1)
    (ok : ∀ w s, t.has w s → allowed (w==A) (w==B) (p.sig (signedWord w s))=true) :
    allowed (decide (0<t.hits A)) (decide (0<t.hits B)) (p.sig t.value)=true := by
  induction t with
  | atom w s =>
    have eq (X : Word) : decide (0 < (ReadTree.atom w s).hits X) = (w==X) := by
      by_cases e : w=X
      · simp [hits,e]
      · simp [hits,e,beq_eq_false_iff_ne.mpr e]
    rw [eq,eq]; exact ok w s ⟨rfl,rfl⟩
  | gate d a b ia ib =>
    change a.hits A+b.hits A≤1 at ca; change a.hits B+b.hits B≤1 at cb
    have la := ia (by omega) (by omega) (fun w s h=>ok w s (Or.inl h))
    have lb := ib (by omega) (by omega) (fun w s h=>ok w s (Or.inr h))
    have one (j k : ℕ) (e : j+k≤1) : (decide (0<j) && decide (0<k))=false := by simp; omega
    have pos (j k : ℕ) : decide (0<j+k)=(decide (0<j)||decide (0<k)) := by
      by_cases hj : 0<j <;> by_cases hk : 0<k <;> simp_all <;> omega
    change allowed (decide (0<a.hits A+b.hits A)) (decide (0<a.hits B+b.hits B)) (p.sig (combine d a.value b.value))=true
    rw [pos,pos,sig_combine]
    exact allowed_join _ _ _ _ _ _ d (one _ _ ca) (one _ _ cb) la lb
end ReadTree

def deMorgan (d i : Bool) (a b : Word) :=
  ReadTree.gate (d ^^ i) (.atom a i) (.atom b i)
lemma deMorgan_value (d i : Bool) (a b : Word) : (deMorgan d i a b).value=signedWord (combine d a b) i := by
  cases d <;> cases i <;> simp [deMorgan,ReadTree.value,signedWord,combine]
  all_goals apply BitVec.eq_of_getElem_eq; intro j hj; simp [BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not]

def Once (x : Word) (S : Finset Word) := ∃ t : ReadTree, t.value=x ∧ ∀ w, t.hits w=if w∈S then 1 else 0
lemma once_of_tight {x n k S} (h : Live x n k S) (width : S.card=n+1) : Once x S := by
  induction h with
  | done => exact ⟨.atom x false,rfl,by intro w; by_cases e:x=w <;> simp_all [ReadTree.hits,eq_comm]⟩
  | @unary n k U a ha fresh tail ih =>
    have zu : ~~~a∉U := fun h=>fresh (Finset.mem_insert_of_mem h)
    have cnt:=count_live tail
    rw [Finset.card_insert_of_notMem zu] at cnt
    have au : a∉U := by rintro eh; rw [Finset.insert_eq_of_mem eh] at width; omega
    obtain ⟨t,eq,ht⟩ := ih (by rw [Finset.card_insert_of_notMem au] at width; rw [Finset.card_insert_of_notMem zu]; omega)
    let f := fun i => ReadTree.atom a (!i)
    refine ⟨t.splice (~~~a) f,(t.splice_value _ f (fun i=>by cases i <;> simp [f,ReadTree.value,signedWord])).trans eq,?_⟩
    intro w
    rw [t.splice_hits (~~~a) w f (if a=w then 1 else 0) (by intro i; rfl),ht,ht]
    have az : ~~~a≠a := fun e=>fresh (Finset.mem_insert.mpr (Or.inl e))
    by_cases e : w=a <;> by_cases z : w = ~~~a <;> simp_all [eq_comm]
  | @binary n k U a b d ha hb ab fresh tail ih =>
    let z:=combine d a b
    have zu : z∉U := fun h=>fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    obtain ⟨au,bu,tw⟩ := tight_parts ab fresh tail width
    obtain ⟨t,eq,ht⟩ := ih tw
    let f:=fun i=>deMorgan d i a b
    refine ⟨t.splice z f,(t.splice_value z f (fun i=>deMorgan_value ..)).trans eq,?_⟩
    intro w
    rw [t.splice_hits z w f ((if a=w then 1 else 0)+(if b=w then 1 else 0)) (by intro i; rfl),ht,ht]
    have za : z≠a := fun e=>fresh (Finset.mem_insert.mpr (Or.inl e))
    have zb : z≠b := fun e=>fresh (Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl e)))
    change _ + (if z∈insert z U then _ else _)*_=_
    by_cases e : w=a <;> by_cases g : w=b <;> by_cases q : w=z <;> simp_all [eq_comm,z]
end Replay2161
