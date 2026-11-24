import SignedTree
namespace Replay2161
set_option maxRecDepth 6000
set_option maxHeartbeats 1000000
inductive Form (α : Type)
  | bot
  | atom (v : α)
  | gate (d : Bool) (u v : Form α)
namespace Form
variable {α β : Type}
def eval (f : α→Word) : Form α → Word
  | bot => 0
  | atom v => f v
  | gate d u v => combine d (u.eval f) (v.eval f)
def mass (f : α→ℕ) : Form α → ℕ
  | bot => 0
  | atom v => f v
  | gate _ u v => u.mass f + v.mass f

def substF (f : α→Form β) : Form α → Form β
  | bot => bot
  | atom w => f w
  | gate d u v => gate d (u.substF f) (v.substF f)
lemma eval_subst (t : Form α) (f : α→Form β) (g : β→Word) :
    (t.substF f).eval g=t.eval (fun w=>(f w).eval g) := by induction t <;> simp_all [substF,eval]
lemma mass_subst (t : Form α) (f : α→Form β) (g : β→ℕ) :
    (t.substF f).mass g=t.mass (fun w=>(f w).mass g) := by induction t <;> simp_all [substF,mass]
lemma mass_add (t : Form α) (f g : α→ℕ) : t.mass (fun w=>f w+g w)=t.mass f+t.mass g := by
  induction t <;> simp_all [mass] <;> omega
lemma mass_mul (t : Form α) (f : α→ℕ) (n : ℕ) : t.mass (fun w=>f w*n)=t.mass f*n := by
  induction t <;> simp_all [mass,Nat.add_mul]
lemma mass_zero (t : Form α) : t.mass (fun _=>0)=0 := by induction t <;> simp_all [mass]
end Form

def leg (q : Word) : Option Word→Word | none=>q | some w=>w
def liftForm (f : Word→Form Word) : Option Word→Form (Option Word)
  | none => .atom none
  | some w => (f w).substF (fun i=>.atom (some i))

def splicePair (z a b : Word) (d : Bool) (w : Word) : Form Word :=
  if w=z then .gate d (.atom a) (.atom b) else .atom w
lemma sp_eval (z a b : Word) (d : Bool) (hz : z=combine d a b) :
    (fun w=>(splicePair z a b d w).eval id)=id := by
  funext w; by_cases e:w=z
  · subst w; simp [splicePair,Form.eval,hz]
  · simp [splicePair,e,Form.eval]
lemma lift_eval (q : Word) (f : Word→Form Word) (ok : (fun w=>(f w).eval id)=id) :
    (fun w=>(liftForm f w).eval (leg q))=leg q := by
  funext w; cases w with
  | none=>rfl
  | some w=>exact (Form.eval_subst ..).trans (congrFun ok w)

def weight {α : Type} [DecidableEq α] (w v : α) : ℕ := if v=w then 1 else 0

lemma some_weight {α : Type} [DecidableEq α] (u v : α) : weight (some u) (some v)=weight u v := by simp [weight]
lemma some_mass (w : Word) : (fun i:Word=>(Form.atom (some i)).mass (weight (some w)))=weight w := by funext i; exact some_weight ..

def Shared (x : Word) (S : Finset Word) := ∃ (inner : Form Word) (outer : Form (Option Word)),
  outer.eval (leg (inner.eval id))=x ∧
  ∀ w, inner.mass (weight w) + outer.mass (weight (some w))=if w∈S then 1 else 0

def Linear (x : Word) (S : Finset Word) := ∃ t : Form Word, t.eval id=x ∧
  ∀ w, t.mass (weight w)=if w∈S then 1 else 0

lemma sp_mass (z a b w : Word) (d : Bool) (v : Word) :
    (splicePair z a b d v).mass (weight w)=
      (if w=z then 0 else weight w v) + weight z v * (weight w a+weight w b) := by
  by_cases e:v=z <;> by_cases q:w=z <;> simp_all [splicePair,Form.mass,weight,eq_comm]
lemma sub_count (t : Form Word) (z a b w : Word) (d : Bool) :
    (t.substF (splicePair z a b d)).mass (weight w)=
      (if w=z then 0 else t.mass (weight w)) + t.mass (weight z)*(weight w a+weight w b) := by
  rw [Form.mass_subst]; simp_rw [sp_mass]; rw [Form.mass_add,Form.mass_mul]; split <;> simp [*,Form.mass_zero]
lemma lift_count (t : Form (Option Word)) (z a b w : Word) (d : Bool) :
    (t.substF (liftForm (splicePair z a b d))).mass (weight (some w))=
      (if w=z then 0 else t.mass (weight (some w))) + t.mass (weight (some z))*(weight w a+weight w b) := by
  rw [Form.mass_subst]
  have eq (v : Option Word) : (liftForm (splicePair z a b d) v).mass (weight (some w))=
      (if w=z then 0 else weight (some w) v)+weight (some z) v*(weight w a+weight w b) := by
    cases v with
    | none=>by_cases q:w=z <;> simp [liftForm,Form.mass,weight,q]
    | some v=> simpa only [liftForm,Form.mass_subst,some_mass,some_weight] using sp_mass z a b w d v
  simp_rw [eq]; rw [Form.mass_add,Form.mass_mul]; split <;> simp [*,Form.mass_zero]

lemma indicator_replace {U : Finset Word} {a b z w : Word} (au : a∉U) (bu : b∉U)
    (zu : z∉U) (za : z≠a) (zb : z≠b) (ab : a≠b) :
    (if w=z then 0 else if w∈insert z U then 1 else 0) +
    (if z∈insert z U then 1 else 0)*(weight w a+weight w b) =
      if w∈insert a (insert b U) then 1 else 0 := by
  by_cases e:w=a <;> by_cases g:w=b <;> by_cases q:w=z <;> simp_all [weight,eq_comm]

lemma linear_of_tight {x n k S} (h : Live x n k S) (hk : k=0) (width : S.card=n+1) : Linear x S := by
  induction h with
  | done=>exact ⟨.atom x,rfl,by intro w; by_cases e:w=x <;> simp_all [Form.mass,weight,eq_comm]⟩
  | unary _ _ _ _ => omega
  | @binary n k U a b d ha hb ab fresh tail ih=>
    let z:=combine d a b
    have zu:z∉U:=fun h=>fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    obtain ⟨au,bu,tw⟩:=tight_parts ab fresh tail width
    obtain ⟨t,eq,ct⟩:=ih hk tw
    refine ⟨t.substF (splicePair z a b d),?_,?_⟩
    · rw [Form.eval_subst,sp_eval _ _ _ _ rfl,eq]
    · intro w; rw [sub_count,ct,ct]
      exact indicator_replace au bu zu (fun e=>fresh (Finset.mem_insert.mpr (Or.inl e)))
        (fun e=>fresh (Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl e)))) ab

lemma share_linear {x : Word} {S : Finset Word} (lin : Linear x S) : Shared x S := by
  obtain ⟨t,eq,ct⟩:=lin
  refine ⟨.bot,t.substF (fun w=>.atom (some w)),?_,?_⟩
  · exact (t.eval_subst ..).trans eq
  · intro w; rw [Form.mass_subst]; simpa only [Form.mass,Nat.zero_add,some_weight] using ct w

-- Form a branch in which the first operand is retained and used twice.
def tee (z a b : Word) (d : Bool) (w : Word) : Form (Option Word) :=
  if w=z then .gate d (.atom none) (.atom (some b)) else if w=a then .atom none else .atom (some w)
lemma tee_linear {x : Word} {U : Finset Word} {z a b : Word} (d : Bool) (hz : z=combine d a b)
    (au : a∈U) (bu : b∉U) (zu : z∉U) (ab : a≠b) (lin : Linear x (insert z U)) :
    Shared x (insert a (insert b U)) := by
  have za : z≠a := by rintro rfl; exact zu au
  obtain ⟨t,eq,ct⟩:=lin
  refine ⟨.atom a,t.substF (tee z a b d),?_,?_⟩
  · rw [Form.eval_subst]; have e : (fun w=>(tee z a b d w).eval (leg (Form.atom a |>.eval id)))=id := by
      funext w
      by_cases q:w=z
      · subst w; simpa [tee,Form.eval,leg] using hz.symm
      · by_cases p:w=a
        · subst w; simp [tee,q,Form.eval,leg]
        · simp [tee,q,p,Form.eval,leg]
    rwa [e]
  · intro w
    have fm (v : Word) : (tee z a b d v).mass (weight (some w)) =
        (if w=z ∨ w=a then 0 else weight w v)+weight z v*weight w b := by
      clear eq ct t hz au bu zu ab
      simp only [tee,weight,Form.mass,Option.some.injEq,reduceCtorEq]
      split_ifs <;> simp_all [Form.mass,weight]
      all_goals grind
    rw [Form.mass_subst]; simp_rw [fm]; rw [Form.mass_add,Form.mass_mul]
    have adjust : t.mass (fun u=>if w=z ∨ w=a then 0 else weight w u) = if w=z ∨ w=a then 0 else t.mass (weight w) := by
      by_cases c:w=z ∨ w=a <;> simp [c,Form.mass_zero]
    rw [adjust,ct,ct]
    clear adjust fm eq ct t hz
    simp only [Form.mass,weight,Finset.mem_insert,Finset.mem_insert_self,ite_true,one_mul]
    split_ifs <;> simp_all <;> grind

lemma shared_of_width {x n k S} (h : Live x n k S) (hk : k=0) (width : n≤S.card) : Shared x S := by
  induction h with
  | done=>exact share_linear (linear_of_tight (.done (target:=x)) rfl (by simp))
  | unary _ _ _ _ => omega
  | @binary n k U a b d ha hb ab fresh tail ih=>
    let z:=combine d a b
    have zu:z∉U:=fun h=>fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have za:z≠a:=fun e=>fresh (Finset.mem_insert.mpr (Or.inl e))
    have zb:z≠b:=fun e=>fresh (Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl e)))
    have cap:=count_live tail
    have card : (insert z U).card=U.card+1:=Finset.card_insert_of_notMem zu
    change (insert z U).card≤n+1 at cap
    by_cases au:a∈U
    · by_cases bu:b∈U
      · rw [Finset.insert_eq_of_mem bu,Finset.insert_eq_of_mem au] at width; omega
      · apply tee_linear d rfl au bu zu ab
        apply linear_of_tight tail hk
        change (insert z U).card=n+1
        rw [Finset.insert_comm,Finset.insert_eq_of_mem au,Finset.card_insert_of_notMem bu] at width; omega
    · by_cases bu:b∈U
      · rw [Finset.insert_comm]; apply tee_linear d (z:=z) (comm d a b) bu au zu ab.symm
        apply linear_of_tight tail hk
        change (insert z U).card=n+1
        rw [Finset.insert_eq_of_mem bu,Finset.card_insert_of_notMem au] at width; omega
      · have anb:a∉insert b U:=by simp [au,ab]
        rw [Finset.card_insert_of_notMem anb,Finset.card_insert_of_notMem bu] at width
        obtain ⟨inner,outer,eq,ct⟩:=ih hk (by change n≤(insert z U).card; omega)
        let rep:=splicePair z a b d
        refine ⟨inner.substF rep,outer.substF (liftForm rep),?_,?_⟩
        · rw [Form.eval_subst,Form.eval_subst,sp_eval _ _ _ _ rfl,lift_eval _ _ (sp_eval _ _ _ _ rfl),eq]
        · intro w; rw [sub_count,lift_count]
          have merge (i j u v k : ℕ) (p : Prop) [Decidable p] :
              ((if p then 0 else i)+u*k)+((if p then 0 else j)+v*k)=(if p then 0 else i+j)+(u+v)*k := by rw [Nat.add_mul]; split <;> omega
          rw [merge,ct,ct]; exact indicator_replace au bu zu za zb ab
end Replay2161
