import SharedTree
namespace Replay2161

def rises (w : Word) (i j : Fin 512) := bit w i && !bit w j
lemma rises_of {w i j} (p : bit w i=true) (n : bit w j=false) : rises w i j=true := by simp [rises,p,n]
lemma parts_rise {w i j} (h : rises w i j=true) : bit w i=true ∧ bit w j=false := by simpa [rises] using h

namespace Form
variable {α : Type} [DecidableEq α]
lemma source (t : Form α) (v : α→Word) {i j} (h : rises (t.eval v) i j=true) :
    ∃ a, 0<t.mass (weight a) ∧ rises (v a) i j=true := by
  induction t with
  | bot=>exact False.elim (Bool.noConfusion ((bit_zero i).symm.trans (parts_rise h).1))
  | atom a=>exact ⟨a,by simp [mass,weight],h⟩
  | gate d a b ia ib=>
    obtain ⟨p,n⟩:=parts_rise h
    simp only [eval,bit_bin] at p n
    have aux : rises (a.eval v) i j=true ∨ rises (b.eval v) i j=true := by
      cases d <;> cases h1 : bit (a.eval v) i <;> cases h2 : bit (a.eval v) j <;> simp_all [rises]
    rcases aux with h|h
    · obtain ⟨u,pu,hu⟩:=ia h; exact ⟨u,by simp only [mass]; omega,hu⟩
    · obtain ⟨u,pu,hu⟩:=ib h; exact ⟨u,by simp only [mass]; omega,hu⟩

lemma gateMarks (t : Form α) (f : α→Word) (p : TracePoint) (A B : α)
    (ca : t.mass (weight A)≤1) (cb : t.mass (weight B)≤1)
    (ok : ∀ w, 0<t.mass (weight w) → allowed (decide (w=A)) (decide (w=B)) (p.sig (f w))=true) :
    allowed (decide (0<t.mass (weight A))) (decide (0<t.mass (weight B))) (p.sig (t.eval f))=true := by
  induction t with
  | bot=>
    have zz : p.sig 0=0 := by
      apply BitVec.eq_of_getElem_eq; intro j hj
      change (p.sig 0)[j] = _; rw [show (p.sig 0)[j]=bit 0 (p.row ⟨j,hj⟩) from sig_bit p 0 ⟨j,hj⟩,bit_zero]; exact (BitVec.getElem_zero hj).symm
    change allowed false false (p.sig 0)=true; rw [zz]; decide
  | atom w=>
    have eq (X : α) : decide (0<(Form.atom w).mass (weight X))=decide (w=X) := by
      by_cases e:w=X
      · simp [mass,weight,e]
      · simp [mass,weight,e,beq_eq_false_iff_ne.mpr e]
    rw [eq,eq]; exact ok w (by simp [mass,weight])
  | gate d a b ia ib=>
    change a.mass (weight A)+b.mass (weight A)≤1 at ca
    change a.mass (weight B)+b.mass (weight B)≤1 at cb
    have la:=ia (by omega) (by omega) (fun w hw=>ok w (by change 0<a.mass (weight w)+b.mass (weight w); omega))
    have lb:=ib (by omega) (by omega) (fun w hw=>ok w (by change 0<a.mass (weight w)+b.mass (weight w); omega))
    have one (j k : ℕ) (e : j+k≤1) : (decide (0<j) && decide (0<k))=false := by simp; omega
    have pos (j k : ℕ) : decide (0<j+k)=(decide (0<j)||decide (0<k)) := by
      by_cases hj : 0<j <;> by_cases hk : 0<k <;> simp_all <;> omega
    change allowed (decide (0<a.mass (weight A)+b.mass (weight A))) (decide (0<a.mass (weight B)+b.mass (weight B))) (p.sig (combine d (a.eval f) (b.eval f)))=true
    rw [pos,pos,sig_combine]
    exact allowed_join _ _ _ _ _ _ d (one _ _ ca) (one _ _ cb) la lb
end Form

structure ModuleView (x : Word) (S : Finset Word) where
  inner : Form Word
  outer : Form (Option Word)
  eq : outer.eval (leg (inner.eval id))=x
  count (w : Word) : inner.mass (weight w)+outer.mass (weight (some w))=if w∈S then 1 else 0

namespace ModuleView
variable {x : Word} {S : Finset Word} (M : ModuleView x S)
def chosen (w : Word) := decide (0<M.inner.mass (weight w))
lemma included {w} (h : 0<M.inner.mass (weight w)) : w∈S ∧ M.chosen w=true := by
  have ct:=M.count w
  refine ⟨?_,by simpa [chosen] using h⟩
  by_contra miss; simp [miss] at ct; omega
lemma outer_mem {w} (h : 0<M.outer.mass (weight (some w))) : w∈S ∧ M.chosen w=false := by
  have ct:=M.count w
  by_cases wm:w∈S
  · simp [wm] at ct; exact ⟨wm,by simp [chosen]; omega⟩
  · simp [wm] at ct; omega
lemma bridge {i j} (up : rises x i j=true)
    (ex : ∀ w∈S, M.chosen w=false → rises w i j=false) : rises (M.inner.eval id) i j=true := by
  obtain ⟨a,ha,inc⟩:=M.outer.source (leg (M.inner.eval id)) (M.eq ▸ up)
  cases a with
  | none=>exact inc
  | some w=>obtain ⟨wm,notin⟩:=M.outer_mem ha; have := ex w wm notin; simp [leg,this] at inc
lemma order_exclusion (i j k l : Fin 512) (p : rises x i j=true) (q : rises x k l=true)
    (hi : ∀ w∈S, M.chosen w=true → rises w i l=false)
    (ho : ∀ w∈S, M.chosen w=false → rises w i j=false ∧ rises w k l=false) : False := by
  have a:=parts_rise (M.bridge p (fun w hw no=>(ho w hw no).1))
  have b:=parts_rise (M.bridge q (fun w hw no=>(ho w hw no).2))
  obtain ⟨w,hw,up⟩:=M.inner.source id (rises_of a.1 b.2)
  obtain ⟨wm,ch⟩:=M.included hw
  rw [show id w=w from rfl,hi w wm ch] at up; contradiction
end ModuleView

lemma grey_ineq (p : TracePoint) (w : Word) (g : wordGrey (p.sig w)=true) :
    rises w (p.row ⟨0,by decide⟩) (p.row ⟨1,by decide⟩)=false ∧ rises w (p.row ⟨0,by decide⟩) (p.row ⟨2,by decide⟩)=false ∧
    rises w (p.row ⟨3,by decide⟩) (p.row ⟨5,by decide⟩)=false ∧ rises w (p.row ⟨4,by decide⟩) (p.row ⟨5,by decide⟩)=false := by
  have eq (k : ℕ) (hk:k<6) : bit w (p.row ⟨k,hk⟩)=(p.sig w)[k] := (sig_bit p w ⟨k,hk⟩).symm
  have h : ∀ s : Tiny, wordGrey s=true → (s[0] && !s[1])=false ∧ (s[0] && !s[2])=false ∧
      (s[3] && !s[5])=false ∧ (s[4] && !s[5])=false := by decide +kernel
  simpa only [rises,←sig_bit,Fin.val_mk] using h _ g
lemma ineq_grey (p : TracePoint) (w : Word)
    (h : rises w (p.row ⟨0,by decide⟩) (p.row ⟨1,by decide⟩)=false ∧ rises w (p.row ⟨0,by decide⟩) (p.row ⟨2,by decide⟩)=false ∧
    rises w (p.row ⟨3,by decide⟩) (p.row ⟨5,by decide⟩)=false ∧ rises w (p.row ⟨4,by decide⟩) (p.row ⟨5,by decide⟩)=false) : wordGrey (p.sig w)=true := by
  have ck : ∀ s : Tiny, ((s[0] && !s[1])=false ∧ (s[0] && !s[2])=false ∧
      (s[3] && !s[5])=false ∧ (s[4] && !s[5])=false) → wordGrey s=true := by decide +kernel
  apply ck; simpa only [rises,←sig_bit,Fin.val_mk] using h

lemma full_sig (p : TracePoint) (w : Word) : p.sig w=25 ↔
    rises w (p.row ⟨0,by decide⟩) (p.row ⟨1,by decide⟩)=true ∧ rises w (p.row ⟨0,by decide⟩) (p.row ⟨2,by decide⟩)=true ∧
    rises w (p.row ⟨3,by decide⟩) (p.row ⟨5,by decide⟩)=true ∧ rises w (p.row ⟨4,by decide⟩) (p.row ⟨5,by decide⟩)=true := by
  have h : ∀ s : Tiny, s=25 ↔ ((s[0] && !s[1])=true ∧ (s[0] && !s[2])=true ∧
      (s[3] && !s[5])=true ∧ (s[4] && !s[5])=true) := by decide +kernel
  simpa only [rises,←sig_bit,Fin.val_mk] using h (p.sig w)

lemma ModuleView.edge {x : Word} {S : Finset Word} (M : ModuleView x S) (p : TracePoint) (a b : Word)
    (target : p.sig x=25) (aS : a∈S) (bS : b∈S) (ab : a≠b)
    (la : wordLeft (p.sig a)=true) (rb : wordRight (p.sig b)=true)
    (rest : ∀ w∈S, w≠a → w≠b → wordGrey (p.sig w)=true) : M.chosen a≠M.chosen b := by
  intro same
  have ac:=M.count a; have bc:=M.count b; simp [aS,bS] at ac bc
  have contradict25 : allowed true true 25≠true := by decide
  cases side : M.chosen a
  · have notB : M.chosen b=false := same ▸ side
    have ig (w) (h:0<M.inner.mass (weight w)) := rest w (M.included h).1
      (by rintro rfl; simp [(M.included h).2] at side) (by rintro rfl; simp [(M.included h).2] at notB)
    have cool (i j) (all : ∀ w, 0<M.inner.mass (weight w) → rises w i j=false) : rises (M.inner.eval id) i j=false := by
      by_contra e; obtain ⟨w,hw,up⟩:=M.inner.source id (Bool.eq_true_of_not_eq_false e)
      simp [all w hw] at up
    have qgrey := ineq_grey p (M.inner.eval id) ⟨cool _ _ (fun w hw=>(grey_ineq p w (ig w hw)).1),
        cool _ _ (fun w hw=>(grey_ineq p w (ig w hw)).2.1),cool _ _ (fun w hw=>(grey_ineq p w (ig w hw)).2.2.1),
        cool _ _ (fun w hw=>(grey_ineq p w (ig w hw)).2.2.2)⟩
    have ca : M.outer.mass (weight (some a))=1 := by simp [ModuleView.chosen] at side; omega
    have cb : M.outer.mass (weight (some b))=1 := by simp [ModuleView.chosen] at notB; omega
    have cmp (u v : Word) (e:u≠v) : (some u==some v)=false := beq_eq_false_iff_ne.mpr (fun h=>e (Option.some.inj h))
    have marks:=M.outer.gateMarks (leg (M.inner.eval id)) p (some a) (some b) ca.le cb.le (by
      intro w use
      cases w with
      | none=>exact legal_grey _ qgrey
      | some w=>
        obtain ⟨wm,_⟩:=M.outer_mem use
        by_cases ea:w=a
        · subst w; simpa [leg,ab] using legal_left _ la
        by_cases eb:w=b
        · subst w; simpa [leg,ab.symm] using legal_right _ rb
        simpa [leg,ea,eb] using legal_grey _ (rest w wm ea eb))
    rw [M.eq,target,ca,cb] at marks; exact contradict25 marks
  · have yesB : M.chosen b=true := same ▸ side
    have og (w) (hw:w∈S) (notin:M.chosen w=false) := rest w hw (by rintro rfl; simp [side] at notin) (by rintro rfl; simp [yesB] at notin)
    obtain ⟨p1,p2,p3,p4⟩ := (full_sig p x).1 target
    have qi : p.sig (M.inner.eval id)=25 := (full_sig ..).2 ⟨M.bridge p1 (fun w hw h=>(grey_ineq _ _ (og w hw h)).1),
        M.bridge p2 (fun w hw h=>(grey_ineq _ _ (og w hw h)).2.1),M.bridge p3 (fun w hw h=>(grey_ineq _ _ (og w hw h)).2.2.1),
        M.bridge p4 (fun w hw h=>(grey_ineq _ _ (og w hw h)).2.2.2)⟩
    have ca : M.inner.mass (weight a)=1 := by simp [ModuleView.chosen] at side; omega
    have cb : M.inner.mass (weight b)=1 := by simp [ModuleView.chosen] at yesB; omega
    have marks:=M.inner.gateMarks id p a b ca.le cb.le (by
      intro w use
      obtain ⟨wm,_⟩:=M.included use
      by_cases ea:w=a
      · subst w; simpa [ab] using legal_left _ la
      by_cases eb:w=b
      · subst w; simpa [ab.symm] using legal_right _ rb
      simpa [ea,eb] using legal_grey _ (rest w wm ea eb))
    rw [qi,ca,cb] at marks; exact contradict25 marks
end Replay2161
