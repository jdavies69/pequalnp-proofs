import PEqualNP.Defs
-- The finite circuit verifier and the prior graph bounds are from loris-olsem.
-- This proof adds the first-OR forest and projects the desk statement onto it.
namespace PEqualNP.Outside.L_meta_2504
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Bool) (a b : Sig) : Sig := if d then a ||| b else a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
private theorem bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]

inductive Live (target : Sig) : Nat → Nat → Finset Sig → Prop
  | stop (hp : proper target) : Live target 0 0 {target}
  | unary {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live target k t (insert (neg a) U)) :
      Live target (k+1) (t+1) (insert a U)
  | binary {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live target k t (insert (bin d a b) U)) :
      Live target (k+1) t (insert a (insert b U))

private lemma live_proper {k t S} (h : Live target k t S) : ∀ a ∈ S, proper a := by
  induction h with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {k t S} (h : Live target k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h with
  | stop hp => simp
  | @unary k t U a ha hf _ ih =>
    have hu : neg a ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega,by omega⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega,by omega⟩


def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (bin false) one
  | .or => xs.foldr (bin true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v

private lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)

private lemma bin_laws (a : Sig) :
    bin false a one = a ∧ bin true a zero = a ∧
    bin false a zero = zero ∧ bin true a one = one ∧
    bin false a a = a ∧ bin true a a = a := by
  simp only [bin,one,zero,Bool.false_eq_true,ite_false,ite_true,BitVec.and_allOnes,BitVec.or_zero,BitVec.and_zero,BitVec.or_allOnes,BitVec.and_self,BitVec.or_self,and_self] <;> simp

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (w : List Sig) (z : Sig) : Prop :=
  (∃ a ∈ w, proper a ∧ z = neg a) ∨
  (∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)

private lemma bin_rep {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ witness w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a0,az,ao,aa,aa'⟩ := bin_laws a
  obtain ⟨b1,b0,bz,bo,bb,bb'⟩ := bin_laws b
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · rw [bin_comm]; cases d <;> simp_all
  · rw [bin_comm]; cases d <;> simp_all
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a=b
  · subst b; cases d <;> simp_all
  exact Or.inr (Or.inr ⟨d,a,b,ham,hbm,hap,hbp,he,rfl⟩)

private lemma gate_rep (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2) :
    represented w (gv w g) ∨ witness w (gv w g) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  have nx (a : Sig) (ha : represented w a) : represented w (neg a) ∨ witness w (neg a) := by
    rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
    · exact Or.inl (neg_laws.1 ▸ ro)
    · exact Or.inl (neg_laws.2 ▸ rz)
    · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)
  cases l with
  | nil =>
    rcases ho with rfl | rfl | rfl
    · exact Or.inl ro
    · exact Or.inl rz
    · exact nx _ rz
  | cons i l =>
    cases l with
    | nil =>
      rcases ho with rfl | rfl | rfl
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · exact nx _ (get_rep w i)
    | cons j l =>
      cases l with
      | cons a l => simp at hl
      | nil =>
        rcases ho with rfl | rfl | rfl
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using bin_rep false (get_rep w i) (get_rep w j)
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using bin_rep true (get_rep w i) (get_rep w j)
        · exact nx _ (get_rep w i)

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.
private lemma pull_gate {w : List Sig} {z : Sig} {k t S} (h : Live target k t S)
    (hz : represented w z ∨ witness w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live target k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨a,ha,hp',eq⟩ | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (neg a)
        have ht : Live target k t (insert (neg a) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : neg a ∉ insert a U := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.unary hp' hf ht,by simpa using And.intro ha hu⟩
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live target k t (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (hp : proper target) (hout : target ∈ execute gs w) :
    ∃ k t S, k ≤ gs.length ∧ Live target k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0,0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,t,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,u,T,hl,hu,hT⟩ := pull_gate ht (gate_rep w g (legal g (by simp))) hs
    exact ⟨l,u,T,by simp; omega,hu,hT⟩

def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [bit,bin]

private lemma b_read (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl

private lemma run_bit (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (bin false _ _) = (_ && _)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (bin true _ _) = (_ || _)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _

private lemma execute_bits (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit i g w (hg g (by simp))]




abbrev Wire (R : Type) := R → Bool

def inv {R} (a : Wire R) : Wire R := fun r => !(a r)

def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0

noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum

def Available {R} (pool : List (Wire R)) (v : Wire R) : Prop := v ∈ pool ∨ Constant v

def supply {R} (pool xs : List (Wire R)) := ∀ a ∈ xs, Available pool a

inductive Reach {R} (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | start : Reach roots 0 roots
  | one {p bank a} : Reach roots p bank → Available bank a →
      Reach roots (p+1) (inv a :: bank)
  | two {p bank a b} (op : Bool) : Reach roots p bank → Available bank a →
      Available bank b → Reach roots (p+1) (combine op a b :: bank)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

inductive Run {R} (goal : Wire R) : Nat → List (Wire R) → Prop
  | stop : Run goal 0 [goal]
  | perm {s xs zs} : xs.Perm zs → Run goal s xs → Run goal s zs
  | one {s a rest} (save : Bool) : Run goal s (inv a :: kept save a rest) →
      Run goal (s+1) (a::rest)
  | two {s a b rest} (op ka kb : Bool) :
      Run goal s (combine op a b :: kept ka a (kept kb b rest)) →
      Run goal (s+1) (a::b::rest)

theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]

theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]

theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩

theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩

theorem from_constant {R} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available bank a) (hb : Available bank b) :
    Available bank (combine op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false, by funext x; simp [combine]⟩
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr ⟨true, by funext x; simp [combine]⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false, by funext x; simp [combine]⟩
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr ⟨true, by funext x; simp [combine]⟩

theorem available_cons {R} {bank v} (w : Wire R) (h : Available bank v) :
    Available (w::bank) v := by
  exact h.elim (fun h => Or.inl (List.mem_cons_of_mem _ h)) Or.inr

theorem extend_one {R} (roots : List (Wire R)) {p bank a} (hp : Reach roots p bank)
    (ha : Available bank a) :
    ∃ q next, Reach roots q next ∧ Available next (inv a) ∧
        (∀ v, Available bank v → Available next v) ∧ q+cost a ≤ p+1+cost (inv a) := by
  classical
  by_cases c : Constant a
  · exact ⟨p,bank,hp,Or.inr (inv_constant c),fun _ h => h,by simp [cost,c,inv_constant c]⟩
  · exact ⟨p+1,_,Reach.one hp ha,Or.inl (by simp),fun _ h => available_cons _ h,by simp [cost,c]⟩

theorem extend_two {R} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach roots p bank)
    (ha : Available bank a) (hb : Available bank b) :
    ∃ q next, Reach roots q next ∧ Available next (combine op a b) ∧
        (∀ v, Available bank v → Available next v) ∧
        q+cost a+cost b ≤ p+1+cost (combine op a b) := by
  classical
  by_cases c : Constant a ∨ Constant b
  · refine ⟨p,bank,hp,from_constant op c ha hb,fun _ h => h,?_⟩
    by_cases ca : Constant a <;> by_cases cb : Constant b
    · simp [cost,ca,cb,both_constant op ca cb]
    · simp [cost,ca,cb]
    · simp [cost,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬Constant a := fun h => c (Or.inl h)
    have cb : ¬Constant b := fun h => c (Or.inr h)
    exact ⟨p+1,_,Reach.two op hp ha hb,Or.inl (by simp),fun _ h => available_cons _ h,
      by simp [cost,ca,cb]⟩

theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]

theorem contraction {R} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach roots p bank) (hs : supply bank ws) :
    ∃ q next, Reach roots q next ∧ Available next goal ∧ q+mass ws ≤ p+s := by
  classical
  induction h generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @one s a rest save _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_one roots hp (hs a (by simp))
    have ht : supply T (inv a :: kept save a rest) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · exact inc v (hs v (List.mem_cons.mpr (mem_kept hh)))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a rest save
    rw [mass_cons] at hl ⊢
    exact ⟨q,W,hW,hv,by omega⟩
  | @two s a b rest op ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_two roots op hp (hs a (by simp)) (hs b (by simp))
    have ht : supply T (combine op a b :: kept ka a (kept kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases mem_kept hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hh))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a (kept kb b rest) ka
    have hlen' := mass_kept b rest kb
    rw [mass_cons] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [mass_cons,mass_cons]
    omega

def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S :=
  fun r => a (rows r)

theorem restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) =
    kept k (restrictRows rows a) (ws.map (restrictRows rows)) := by
  cases k <;> simp [kept]

theorem restrict_run {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws) :
    Run (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | one save _ ih =>
    simp only [List.map_cons,restrict_kept] at ih ⊢
    exact Run.one save ih
  | two op ka kb _ ih =>
    simp only [List.map_cons,restrict_kept] at ih ⊢
    cases op
    · exact Run.two false ka kb ih
    · exact Run.two true ka kb ih

theorem projected_bound {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach roots p bank) (hs : supply bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach roots q bs → Available bs (restrictRows rows goal) → L ≤ q) :
    L + mass (ws.map (restrictRows rows)) ≤ p+s := by
  obtain ⟨q,bs,hq,ht,hle⟩ := contraction nc (restrict_run rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega


abbrev Row := Fin 512
def observe (a : Sig) : Wire Row := fun r => bit r a
def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)

theorem bit_table (f : Wire Row) (r : Row) : bit r (table f) = f r := by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]

theorem table_observe (v : Sig) : table (observe v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact bit_table (observe v) ⟨j,hj⟩

theorem observe_table (f : Wire Row) : observe (table f) = f := by
  funext r
  exact bit_table f r

theorem obs_neg (a : Sig) : observe (neg a) = inv (observe a) := by
  funext r
  exact bit_neg _ _

theorem obs_bin (d : Bool) (a b : Sig) :
    observe (bin d a b) = combine d (observe a) (observe b) := by
  funext r
  cases d <;> exact bit_bin _ _ _ _

theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl

theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

theorem list_run {T : Sig} {k u S} (h : Live T k u S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run (observe T) k (v.map observe) := by
  classical
  induction h generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @unary k u U a ha fresh _ ih =>
    let rest := (U.erase a).toList
    let save := decide (a ∈ U)
    let tail := kept save a rest
    have er : rest.toFinset = U.erase a := by simp [rest]
    have hm : a ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have ht : tail.toFinset = U := by
      rw [show tail=kept save a rest by rfl,kept_fin,er]
      by_cases hh : a ∈ U <;> simp [save,hh]
    have nd := kept_nd save a rest hr hm
    have hf : neg a ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz))
    have progress := ih (neg a::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    rw [List.map_cons,map_kept,obs_neg] at progress
    have perm : (a::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (List.nodup_cons.mpr ⟨hm,hr⟩) hv
      simp [er,eqv]
    exact Run.perm (perm.map _) (Run.one save progress)
  | @binary k u U a b d ha hb hab fresh _ ih =>
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tail := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm := kept_nd kb b rest hr br
    have am : a ∉ mid := by cases h : kb <;> simp [mid,kept,h,hab,ar]
    have nd := kept_nd ka a mid bm am
    have ht : tail.toFinset = U := by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kept_fin,kept_fin,er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : bin d a b ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change Run _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d ka kb progress)


theorem table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]

theorem table_bin (d : Bool) (f g : Wire Row) :
    table (combine d f g) = bin d (table f) (table g) := by
  rw [←table_observe (bin d (table f) (table g)),obs_bin,observe_table,observe_table]

theorem available_rep {bank : List (Wire Row)} {a} (h : Available bank a) :
    represented (bank.map table) (table a) := by
  rcases h with hm | ⟨b,rfl⟩
  · exact Or.inl (List.mem_map_of_mem hm)
  · apply Or.inr
    cases b
    · have z : table (fun _ => false) = zero := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (bit_table _ ⟨j,hj⟩).trans (bit_zero ⟨j,hj⟩).symm
      exact fun hp => hp.1 z
    · have z : table (fun _ => true) = one := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (bit_table _ ⟨j,hj⟩).trans (bit_one ⟨j,hj⟩).symm
      exact fun hp => hp.2 z

theorem inv_rep {w a} (ha : represented w a) :
    represented w (neg a) ∨ witness w (neg a) := by
  rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
  · exact Or.inl (Or.inr fun h => h.2 neg_laws.1)
  · exact Or.inl (Or.inr fun h => h.1 neg_laws.2)
  · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)

theorem pull_cons {w : List Sig} {z : Sig} {T k t S} (h : Live T k t S)
    (hz : represented w z ∨ witness w z) (hs : ∀ a ∈ S, a ∈ z::w) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live T k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  apply pull_gate h hz
  intro a hm
  simpa [or_comm] using hs a hm

theorem reach_live_sub {roots : List (Wire Row)} {p bank}
    (h : Reach roots p bank) {T k t S} (run : Live T k t S)
    (sub : ∀ a ∈ S, a ∈ bank.map table) :
    ∃ l v U, l ≤ p+k ∧ Live T l v U ∧ ∀ a ∈ U, a ∈ roots.map table := by
  induction h generalizing k t S with
  | start => exact ⟨k,t,S,by omega,run,sub⟩
  | @one p bank a h ha ih =>
    rw [List.map_cons,table_inv] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩ := pull_cons run (inv_rep (available_rep ha)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,table_bin] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩ := pull_cons run (bin_rep d (available_rep ha) (available_rep hb)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩

theorem reach_live {roots : List Sig} {p bank T} (hp : proper T)
    (h : Reach (roots.map observe) p bank) (hit : Available bank (observe T)) :
    ∃ k t S, k ≤ p ∧ Live T k t S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,v,U,hl,hr,hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,v,U,by omega,hr,?_⟩
  simpa [List.map_map,Function.comp_def,table_observe] using hs

theorem live_row_difference {T k t S} (h : Live T k t S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @unary k t U a hp hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · refine ⟨a,by simp,?_⟩
      exact fun he => hd (by rw [bit_neg,bit_neg,he])
    · exact ⟨v,Finset.mem_insert_of_mem hu,hd⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩

theorem raw_required {T k t S} (h : Live T k t S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig := 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
def seed : Sig := 0x88888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888

def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem seed_table : ∀ r : Row, bit r seed = (sample r 0 && sample r 1) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem seed_nonzero : seed ≠ zero := by decide +kernel
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
theorem sampled (r : Row) : List.ofFn (sample r) = inputs.map (bit r) := by
  rw [←input_list]
  rw [List.map_ofFn]
  rfl

theorem table_eval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates inputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sampled]
  rfl

theorem exec_extends (gs : List Gate) (ws : List Sig) : ∃ l, execute gs ws = ws ++ l := by
  induction gs generalizing ws with
  | nil => exact ⟨[],by simp [execute]⟩
  | cons g gs ih =>
    obtain ⟨l,hl⟩ := ih (ws++[gv ws g])
    exact ⟨gv ws g::l,by simpa [execute,List.append_assoc] using hl⟩

def neighbor (i : Fin 9) : Nat := [4,2,1,2,3,0,1,2,3].getD i.val 0
def absentRow (i : Fin 9) : Row := Fin.ofNat 512 (1 <<< neighbor i)
def presentRow (i : Fin 9) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< neighbor i))

theorem seed_witness : ∀ i : Fin 9,
    (bit (absentRow i) graph != bit (presentRow i) graph) &&
    ((inputs++[seed]).all fun w => w == inputs.getD i.val zero ||
      bit (absentRow i) w == bit (presentRow i) w) = true := by decide +kernel

theorem all_roots {k t S} (h : Live graph k t S) (sub : ∀ v ∈ S, v ∈ inputs++[seed]) :
    S=inputs.toFinset ∨ S=(inputs++[seed]).toFinset := by
  have all (i : Fin 9) : inputs.getD i.val zero ∈ S := by
    have cut := seed_witness i
    simp only [Bool.and_eq_true,Bool.not_eq_true',bne_iff_ne,List.all_eq_true,
      Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq] at cut
    apply raw_required h _ _ sub (absentRow i) (presentRow i) cut.1
    exact fun v hv hne => (cut.2 v hv).resolve_left hne
  have needed : inputs.toFinset ⊆ S := by
    intro v hv
    have hm := List.mem_toFinset.mp hv
    rw [←input_list,List.mem_ofFn] at hm
    obtain ⟨i,rfl⟩ := hm
    exact all i
  by_cases hseed : seed ∈ S
  · right
    ext w
    constructor
    · exact fun hw => List.mem_toFinset.mpr (sub w hw)
    · intro hw
      have hx := List.mem_toFinset.mp hw
      simp only [List.mem_append,List.mem_singleton] at hx
      exact hx.elim (fun h => needed (List.mem_toFinset.mpr h)) (fun e => e ▸ hseed)
  · left
    exact Finset.Subset.antisymm (fun w hw => by
      have hx := sub w hw
      simp only [List.mem_append,List.mem_singleton] at hx
      rcases hx with hin | rfl
      · exact List.mem_toFinset.mpr hin
      · exact False.elim (hseed hw)) needed

theorem initial_live (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (first : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 1))
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C = edge) (small : C.size ≤ 15) :
    ∃ k t, k ≤ 14 ∧ (Live graph k t inputs.toFinset ∨ Live graph k t (inputs++[seed]).toFinset) := by
  have headEq : (execute C.gates inputs).getD 9 zero = seed := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal 9 r).trans ((first (sample r)).trans (seed_table r).symm)
  have goalEq : (execute C.gates inputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal C.output r).trans ((congrFun computes (sample r)).trans (edge_table r).symm)
  have out := get_rep (execute C.gates inputs) C.output
  rw [goalEq] at out
  have targetIn := out.resolve_right (fun hn => hn graph_proper)
  cases hgs : C.gates with
  | nil =>
    rw [hgs] at headEq
    exact False.elim (seed_nonzero headEq.symm)
  | cons g gs =>
    have eq0 : gv inputs g = seed := by
      rw [hgs] at headEq
      change (execute gs (inputs++[gv inputs g])).getD 9 zero = seed at headEq
      obtain ⟨l,hl⟩ := exec_extends gs (inputs++[gv inputs g])
      rw [hl] at headEq
      exact headEq
    rw [hgs] at targetIn
    change graph ∈ execute gs (inputs++[gv inputs g]) at targetIn
    rw [eq0] at targetIn
    have tailLegal : ∀ gate ∈ gs, gate.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ gate.inputs.length≤2 := by
      intro gate hg
      apply legal
      rw [hgs]
      exact List.mem_cons_of_mem _ hg
    obtain ⟨k,t,S,hk,run,hs⟩ := extract gs _ tailLegal graph_proper targetIn
    have len : gs.length+1 ≤ 15 := by simpa [Circuit.size,hgs] using small
    refine ⟨k,t,by omega,?_⟩
    rcases all_roots run hs with h | h
    · exact Or.inl (h ▸ run)
    · exact Or.inr (h ▸ run)


def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r
theorem rename_neg (f : Row → Row) (a : Sig) : rename f (neg a) = neg (rename f a) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change bit ⟨j,hj⟩ (rename f (neg a)) = bit ⟨j,hj⟩ (neg (rename f a))
  rw [bit_rename,bit_neg,bit_neg,bit_rename]
theorem rename_bin (f : Row → Row) (d : Bool) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change bit ⟨j,hj⟩ (rename f (bin d a b)) = bit ⟨j,hj⟩ (bin d (rename f a) (rename f b))
  rw [bit_rename,bit_bin,bit_bin,bit_rename,bit_rename]
theorem rename_inj (f : Row → Row) (onto : Function.Surjective f) :
    Function.Injective (rename f) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨r,hr⟩ := onto ⟨j,hj⟩
  have he := congrArg (bit r) h
  change bit ⟨j,hj⟩ a = bit ⟨j,hj⟩ b
  rw [bit_rename,bit_rename,hr] at he
  exact he
theorem rename_constants (f : Row → Row) : rename f zero = zero ∧ rename f one = one := by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · exact (bit_rename f zero ⟨j,hj⟩).trans ((bit_zero _).trans (bit_zero ⟨j,hj⟩).symm)
  · exact (bit_rename f one ⟨j,hj⟩).trans ((bit_one _).trans (bit_one ⟨j,hj⟩).symm)
theorem live_rename {T k t S} (h : Live T k t S) (f : Row → Row) (onto : Function.Surjective f) :
    Live (rename f T) k t (S.image (rename f)) := by
  have inj := rename_inj f onto
  obtain ⟨fz,fo⟩ := rename_constants f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @unary k t U a hp hf _ ih =>
    have fresh : rename f (neg a) ∉ (insert a U).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_neg] at fresh ih ⊢
    exact Live.unary (pp _ hp) fresh ih
  | @binary k t U a b d ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    exact Live.binary (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih

theorem mono_row_difference {T k t S} (h : Live T k t S) (none : t=0) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | unary _ _ _ _ => omega
  | @binary k t U a b d ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih none
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      cases d <;> cases p : bit r a <;> cases q : bit s a <;>
        cases u : bit r b <;> cases z : bit s b <;> simp_all
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩

def Lower (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach (roots.map observe) p bank → Available bank (observe T) → L ≤ p

def Impossible (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k t, k ≤ cap → ¬Live T k t S

def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v

theorem lower_impossible {roots T L} (hp : proper T)
    (essential : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible T L roots.toFinset) : Lower roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,t,S,hk,run,hs⟩ := reach_live hp h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k t (by omega) (he.symm ▸ run)

theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : represented ([] : List Sig) v := by
    have avail : Available ([] : List (Wire Row)) (observe v) := Or.inr ⟨b,h⟩
    simpa only [List.map_nil,table_observe] using available_rep avail
  exact (hr.resolve_left (by simp)) hv

theorem mass_append {R} (a b : List (Wire R)) : mass (a++b) = mass a + mass b := by
  simp [mass]
theorem mass_constants {R} (xs : List (Wire R)) (hc : ∀ x ∈ xs, Constant x) :
    mass xs = xs.length := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [mass_cons,List.length_cons,cost,if_pos ha,ih (fun x hx => hc x (by simp [hx]))]
    omega

theorem lower_slice {roots other : List Sig} {T G : Sig} (pT : proper T) (pG : proper G)
    (r : Row → Row) (eq : rename r T = G)
    (covered : ∀ a ∈ roots, Available (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (observe (rename r a)))
    (L : Nat) (prior : Lower other G L) : Lower roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,t,S,hk,run,sub⟩ := reach_live pT hh ha
  have subS : singles ⊆ S := by
    intro a hs
    obtain ⟨i,j,hd,hiso⟩ := necessary a hs
    exact raw_required run roots a sub i j hd hiso
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front,List.nodup_append]
    refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro a ha b hb he
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset=S := by ext a; simp [front,Finset.union_sdiff_of_subset subS]
  have run' := list_run run front nd fe
  have gc : restrictRows r (observe T) = observe G := (observe_rename _ _).symm.trans (congrArg observe eq)
  have supp : supply (other.map observe) ((front.map observe).map (restrictRows r)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
    rw [←observe_rename]
    exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound := projected_bound r run' (gc ▸ observe_proper pG) Reach.start supp
    (L:=L) (gc ▸ prior)
  have massLo : singles.card ≤ mass ((front.map observe).map (restrictRows r)) := by
    simp only [front,List.map_append,mass_append]
    let xs := (singles.toList.map observe).map (restrictRows r)
    have only : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
      rw [←observe_rename]
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz := mass_constants xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz
    change singles.card ≤ mass xs + _
    rw [sz]
    omega
  omega



def childOne (ws : List Sig) (a : Sig) (keep : Bool) : List Sig :=
  neg a :: kept keep a (ws.erase a)
def childTwo (ws : List Sig) (a b : Sig) (d ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]

theorem enum_step {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (oneStep : ∀ a ∈ ws, ∀ keep, neg a ∉ ws → proper (neg a) →
      (childOne ws a keep).length ≤ cap →
      Impossible T (cap-1) (childOne ws a keep).toFinset)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible T cap ws.toFinset := by
  classical
  intro k t hk h
  generalize he : ws.toFinset = S at h
  cases h with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @unary k t U a ha hf tail =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have fresh : neg a ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let keep := decide (a ∈ U)
    have er := erase_fin hn a
    have rest : (kept keep a (ws.erase a)).toFinset = U := by
      rw [kept_fin,er,he]
      by_cases hm : a ∈ U <;> simp [keep,hm]
    have nd : (childOne ws a keep).Nodup := by
      have na : a ∉ ws.erase a := hn.not_mem_erase
      have nk := kept_nd keep a (ws.erase a) (hn.erase _) na
      refine List.nodup_cons.mpr ⟨?_,nk⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (rest ▸ List.mem_toFinset.mpr h))
    have eq : (childOne ws a keep).toFinset = insert (neg a) U := by simp [childOne,rest]
    have sc := (live_size tail).2
    have len : (childOne ws a keep).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact oneStep a am keep fresh hz len k t (by omega) (eq.symm ▸ tail)
  | @binary k t U a b d ha hb hab hf tail =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest=(ws.erase a).erase b by rfl,erase_fin (hn.erase _) b,
        erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kept_fin,kept_fin,er,he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j=a <;>
        by_cases jb : j=b <;> simp_all [ka,kb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept,ar,hab]
    have nd : (childTwo ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨?_,kept_nd ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset = _
      simp [ke]
    have sc := (live_size tail).2
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d ka kb hab fresh hz len k t (by omega) (eq.symm ▸ tail)

def Sep (T : Sig) (width : Nat) (pos negRow : Fin width → Row)
    (asig : Sig → BitVec width × BitVec width) : Prop :=
  (∀ i, bit (pos i) T = true ∧ bit (negRow i) T = false) ∧
  ∀ w i, (asig w).1.getLsbD i.val = bit (pos i) w ∧
    (asig w).2.getLsbD i.val = bit (negRow i) w

def column {n} (oriented : Bool) (s : BitVec n × BitVec n) : BitVec n :=
  if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2

def covered {n} (oriented : Bool) (sig : Sig → BitVec n × BitVec n) : List Sig → BitVec n
  | [] => 0
  | a::ws => column oriented (sig a) ||| covered oriented sig ws

theorem covered_bit {n : Nat} {oriented : Bool} {sig : Sig → BitVec n × BitVec n} {ws : List Sig} {i : Fin n} :
    (covered oriented sig ws).getLsbD i.val = true ↔
    ∃ a ∈ ws, (column oriented (sig a)).getLsbD i.val = true := by
  induction ws with
  | nil => simp [covered]
  | cons a ws ih =>
    simp only [covered,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]

theorem cover_sound {T k t S} (h : Live T k t S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → t=0) :
    covered oriented sig ws = BitVec.allOnes width := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin width := ⟨j,hj⟩
  have yes := (correct.1 i).1
  have no := (correct.1 i).2
  rw [BitVec.getLsbD_allOnes]; simp only [hj,decide_true]
  apply (covered_bit (i:=i)).mpr
  cases oriented with
  | false =>
    obtain ⟨a,ha,hd⟩ := live_row_difference h (show bit (r i) T ≠ bit (s i) T by simp [yes,no])
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,Bool.false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
    cases hx : bit (r i) a <;> cases hy : bit (s i) a <;> simp_all
  | true =>
    obtain ⟨a,ha,hp,hn⟩ := mono_row_difference h (zeroNot rfl) yes no
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,
      Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]

theorem cover_required {T cap ws k t} (h : Live T k t (List.toFinset ws))
    (hk : k ≤ cap) (hn : ws.Nodup) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (decide (ws.length=cap+1)) sig ws = BitVec.allOnes n := by
  apply cover_sound h rfl correct
  intro hh
  have eq := of_decide_eq_true hh
  have bound := (live_size h).2
  rw [List.toFinset_card_of_nodup hn] at bound
  omega



def Slice (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank, Reach (roots.map observe) p bank → Available bank (restrictRows f (observe T)) → L ≤ p

def masked (d a : Sig) := a &&& d
def availableB (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m)

theorem masked_eq {f : Row → Row} {d a b : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = masked d b) :
    restrictRows f (observe a) = restrictRows f (observe b) := by
  funext r
  have h := congrArg (bit (f r)) eq
  change bit (f r) a = bit (f r) b
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using h

theorem masked_zero {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = zero) : restrictRows f (observe a) = fun _ => false := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = false
  rw [bit_zero] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

theorem masked_one {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = d) : restrictRows f (observe a) = fun _ => true := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = true
  rw [dom r] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

def poolSupply (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool, Available bank (restrictRows f (observe a))

theorem availableB_sound {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : poolSupply f bank pool)
    (check : availableB d pool a = true) : Available bank (restrictRows f (observe a)) := by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with (hz | ho) | ⟨v,hv,he⟩
  · exact Or.inr ⟨false,masked_zero dom hz⟩
  · exact Or.inr ⟨true,masked_one dom ho⟩
  · exact masked_eq dom he ▸ supplyB v hv

abbrev Choice := Nat × Sig × Sig
def choiceVal (c : Choice) :=
  if c.1=2 then neg c.2.1 else bin (c.1==1) c.2.1 c.2.2
def choiceOK (d : Sig) (pool : List Sig) (c : Choice) :=
  availableB d pool c.2.1 && (c.1==2 || availableB d pool c.2.2)

theorem pay_choice {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bit (f r) d = true) (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (c : Choice) (valid : choiceOK d pool c = true) :
    ∃ next, Reach roots (q+1) next ∧ poolSupply f next (choiceVal c :: pool) := by
  have ok : availableB d pool c.2.1 = true ∧ (c.1==2 || availableB d pool c.2.2) = true := by simpa only [choiceOK,Bool.and_eq_true] using valid
  have ha := availableB_sound dom hs ok.1
  let z := restrictRows f (observe (choiceVal c))
  have hz : Reach roots (q+1) (z::bank) := by
    by_cases unary : c.1=2
    · change Reach _ _ (restrictRows f (observe (choiceVal c)) :: _)
      rw [choiceVal,if_pos unary,obs_neg]
      exact Reach.one hp ha
    · have hb : availableB d pool c.2.2 = true := by simpa [unary] using ok.2
      have hz' := Reach.two (c.1==1) hp ha (availableB_sound dom hs hb)
      change Reach _ _ (restrictRows f (observe (choiceVal c)) :: _)
      rw [choiceVal,if_neg unary,obs_bin]
      have comm (b : Bool) (v w : Wire Row) : restrictRows f (combine b v w) = combine b (restrictRows f v) (restrictRows f w) := by cases b <;> rfl
      rw [comm]
      exact hz'
  refine ⟨_,hz,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · exact Or.inl (by simp [z])
  · exact available_cons _ (hs _ hm)

def makePool (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK d pool c then makePool d (choiceVal c::pool) cs else none

theorem makePool_sound {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank q pool} (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (cs : List Choice) {result} (ok : makePool d pool cs = some result) :
    ∃ next, Reach roots (q+cs.length) next ∧ poolSupply f next result := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨_,hp,hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok
    split at ok
    next h =>
      obtain ⟨next,hr,sh⟩ := pay_choice dom hp hs c h
      obtain ⟨out,hr',sh'⟩ := ih hr sh ok
      exact ⟨out,by simpa [Nat.add_assoc,Nat.add_comm 1] using hr',sh'⟩
    next => contradiction

def isMaskedConstant (d a : Sig) := masked d a == zero || masked d a == d
theorem count_constants {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    (ws : List Sig) : ws.countP (isMaskedConstant d) ≤ mass ((ws.map observe).map (restrictRows f)) := by
  classical
  induction ws with
  | nil => simp [mass]
  | cons a ws ih =>
    simp only [List.countP_cons,List.map_cons,mass_cons]
    cases h : isMaskedConstant d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc : Constant (restrictRows f (observe a)) := by
        have hh : masked d a = zero ∨ masked d a = d := by simpa only [isMaskedConstant,Bool.or_eq_true,beq_iff_eq] using h
        rcases hh with hz | ho
        · exact ⟨false,masked_zero dom hz⟩
        · exact ⟨true,masked_one dom ho⟩
      simpa [cost,hc,Nat.add_comm] using Nat.succ_le_succ ih

def poolCut (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (isMaskedConstant d)) && ws.all (availableB d pool)

theorem poolCut_sound {raw T d L} (slice : Slice raw T d L) (cs : List Choice)
    {pool ws cap} (built : makePool d raw cs = some pool)
    (nd : ws.Nodup) (cut : poolCut d L cap cs.length pool ws = true) :
    Impossible T cap ws.toFinset := by
  intro k t hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩ := slice
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) base cs built
  simp only [poolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩ := cut
  have coveredS : supply bank ((ws.map observe).map (restrictRows f)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    exact availableB_sound dom hs (List.all_eq_true.mp all a ha)
  have b := projected_bound f (list_run h ws nd rfl) nc hr coveredS lo
  have massLo := count_constants dom ws
  have hu := ineq
  simp only [Nat.zero_add] at b
  omega



abbrev Move := Sig × Sig × Row
def shifted (d r : Row) : Row :=
  if h : r.val < 512-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(512-d.val),by omega⟩
def backwards (d : Row) : Row := Fin.ofNat 512 (512-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)

theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 512-d.val <;> simp [shifted,h,r.isLt]

theorem bool_mux (p x y : Bool) : (p && x || !p && y) = (if p then x else y) := by cases p <;> simp

theorem bit_mux (r : Row) (m a b : Sig) :
    bit r (mux m a b) = if bit r m then bit r a else bit r b := by
  simp only [bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,
    decide_true,Bool.true_and]
  exact bool_mux _ _ _

theorem bit_move (r : Row) (m : Move) (a : Sig) : bit r (wordMove m a) = bit (rowMove m r) a := by
  simp only [wordMove,bit_mux,bit_shift,rowMove]
  cases bit r m.1 <;> cases bit r m.2.1 <;> rfl

def movedRow (ms : List Move) (r : Row) := ms.foldl (fun j m => rowMove m j) r
def movedWord (ms : List Move) (a : Sig) := ms.foldr wordMove a
theorem bit_moved (ms : List Move) (a : Sig) (r : Row) :
    bit r (movedWord ms a) = bit (movedRow ms r) a := by
  induction ms generalizing r with
  | nil => rfl
  | cons m ms ih => exact (bit_move r m _).trans (ih _)
theorem moved_eq_rename (ms : List Move) (a : Sig) : movedWord ms a = rename (movedRow ms) a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact (bit_moved ms a ⟨j,hj⟩).trans (bit_rename _ _ ⟨j,hj⟩).symm

def freeWord (roots : List Sig) (w : Sig) := w==zero || w==one || roots.contains w
theorem freeWord_ok {roots w} (ok : freeWord roots w = true) :
    Available (roots.map observe) (observe w) := by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr ⟨false,funext bit_zero⟩
  · exact Or.inr ⟨true,funext bit_one⟩
  · exact Or.inl (List.mem_map_of_mem hm)

def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T == G && raw.all (fun a => freeWord base (movedWord ms a))

theorem map_correct {ms raw T base G} (ok : checkMap ms raw T base G = true) :
    rename (movedRow ms) T = G ∧
    ∀ a ∈ raw, Available (base.map observe) (observe (rename (movedRow ms) a)) := by
  simp only [checkMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,moved_eq_rename] at ok
  exact ⟨ok.1,fun a ha => freeWord_ok (ok.2 a ha)⟩

theorem lower_map {ms raw T base G L} (ok : checkMap ms raw T base G = true)
    (pT : proper T) (pG : proper G) (hL : Lower base G L) : Lower raw T L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  simpa using lower_slice pT pG (movedRow ms) eq supp ∅ (by simp) (by simp) L hL

theorem slice_correct {ms raw T base G L d} (ok : checkMap ms raw T base G = true)
    (all : movedWord ms d = one) (properG : proper G) (hL : Lower base G L) :
    Slice raw T d L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  have obs : restrictRows (movedRow ms) (observe T) = observe G :=
    (observe_rename _ _).symm.trans (congrArg observe eq)
  refine ⟨movedRow ms,base,?_,?_,?_,?_⟩
  · intro r
    rw [←bit_moved,all,bit_one]
  · intro a ha
    rw [←observe_rename]
    exact supp a ha
  · rw [obs]
    exact observe_proper properG
  · rw [obs]
    exact hL

def witnessB (T : Sig) (roots : List Sig) (a : Sig) (rs : Row × Row) :=
  (bit rs.1 T != bit rs.2 T) &&
  roots.all (fun w => w == a || bit rs.1 w == bit rs.2 w)
theorem witnessB_sound {T roots a rs} (ok : witnessB T roots a rs = true) : Essential T roots a := by
  simp only [witnessB,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
  exact ⟨rs.1,rs.2,ok.1,fun w hw hne => (ok.2 w hw).resolve_left hne⟩

def checkEssential (T : Sig) (raw : List Sig) (xs : List (Sig × Row × Row)) :=
  xs.all (fun a => witnessB T raw a.1 a.2)
theorem essential_ok {T raw xs} (ok : checkEssential T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, Essential T raw a := by
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact witnessB_sound (List.all_eq_true.mp ok _ hm)

theorem lower_count {raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : checkEssential T raw xs = true) :
    Lower raw T ((xs.map Prod.fst).toFinset.card-1) := by
  intro p bank hr hit
  obtain ⟨k,t,S,hk,run,sub⟩ := reach_live properT hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := essential_ok ok a ha
    exact raw_required run raw a sub r s hd iso
  have bound := (live_size run).2
  omega

def checkLift (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  checkMap ms raw T base G && checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1 == zero || movedWord ms a.1 == one)

theorem lift_ok {ms T raw base G xs L} (ok : checkLift ms T raw base G xs = true)
    (properT : proper T) (properG : proper G) (low : Lower base G L) :
    Lower raw T (L+(xs.map Prod.fst).toFinset.card) := by
  simp only [checkLift,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩ := map_correct ok.1.1
  apply lower_slice properT properG _ eq supp _ (essential_ok ok.1.2) _ L low
  intro a ha
  obtain ⟨⟨v,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  have hh := List.all_eq_true.mp ok.2 _ hm
  simp only [Bool.or_eq_true,beq_iff_eq,moved_eq_rename] at hh
  rcases hh with h | h
  · rw [h]
    exact ⟨false,funext bit_zero⟩
  · rw [h]
    exact ⟨true,funext bit_one⟩



def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat) := (selected m).map Prod.snd
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
def cube0 : Nat → Nat
  | 0 => 0xff
  | 1 => 0x55
  | 2 => 0x33
  | 3 => 0x11
  | 4 => 0xf
  | 5 => 0x5
  | 6 => 0x3
  | _ => 0x1
def cube3 : Nat → Nat
  | 0 => 0x101010101010101
  | 1 => 0x1000100010001
  | 2 => 0x10100000101
  | 3 => 0x100000001
  | 4 => 0x1010101
  | 5 => 0x10001
  | 6 => 0x101
  | _ => 0x1
def cube6 : Nat → Nat
  | 0 => 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
  | 1 => 0x1000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001
  | 2 => 0x100000000000000010000000000000000000000000000000000000000000000010000000000000001
  | 3 => 0x10000000000000000000000000000000000000000000000000000000000000001
  | 4 => 0x1000000000000000100000000000000010000000000000001
  | 5 => 0x100000000000000000000000000000001
  | 6 => 0x10000000000000001
  | _ => 0x1
def subcube (z o : Nat) : Sig :=
  let fixed := z ||| o
  if z &&& o != 0 then zero else
    BitVec.ofNat 512 ((cube0 (fixed &&& 7)*cube3 ((fixed >>> 3) &&& 7)*cube6 ((fixed >>> 6) &&& 7)) <<< o)
def fixRows (z o : Nat) : List Move :=
  (List.range 9).filterMap fun j =>
    let x := inputs.getD j zero
    let step := Fin.ofNat 512 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none
def swapRows (v : Nat) : Move :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  let d := (1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 512 d)

def supportPairs (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) => (a,0,Fin.ofNat 512 (1 <<< i))

def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
def assertSize (m hints L : Nat) :=
  let xs := graphPairs m hints
  properB (graphGoal m) && checkEssential (graphGoal m) (vars m) xs &&
    decide (L ≤ (xs.map Prod.fst).toFinset.card-1)
theorem size_of {m hints L} (h : assertSize m hints L = true) :
    Lower (vars m) (graphGoal m) L := by
  simp only [assertSize,Bool.and_eq_true,decide_eq_true_eq] at h
  intro p bank hr ha
  exact h.2.trans (lower_count (proper_of _ h.1.1) _ h.1.2 p bank hr ha)

abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
def colFree (m z o : Nat) := m ^^^ (m &&& (z ||| o))
def chartGoal (m : Nat) : Sig :=
  if m=1023 then graphGoal m &&& ~~~seed else graphGoal m
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs s
  let count := (xs.map Prod.fst).toFinset.card
  properB G && checkMap ms (vars m) (chartGoal m) (vars free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (vars free) xs && decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (vars free) (vars q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))

theorem col_sound {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (ok : colCheck m c prior = true) : Slice (vars m) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  obtain ⟨z,o,q,s,L⟩ := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs s
  change (((properB G && checkMap ms (vars m) (chartGoal m) (vars free) G) &&
    (movedWord ms (subcube z o)==one)) && _) = true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply slice_correct ok.1.1.2 ok.1.2 (proper_of _ ok.1.1.1)
  intro p bank hr ha
  have hh := ok.2
  by_cases hq : q=0
  · simp only [colCheck,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lower_count (proper_of _ ok.1.1.1) xs hh.1 p bank hr ha)
  · simp only [colCheck,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lift_ok hh.1.2 (proper_of _ ok.1.1.1) (proper_of _ hh.1.1) (valid q) p bank hr ha)

def relabelOK (old rep : Nat) (swaps : List Nat) :=
  properB (graphGoal old) && properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (vars old) (graphGoal old) (vars rep) (graphGoal rep)
theorem relabel_of {old rep L swaps} (ok : relabelOK old rep swaps = true)
    (h : Lower (vars rep) (graphGoal rep) L) : Lower (vars old) (graphGoal old) L := by
  simp only [relabelOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (proper_of _ ok.1.1) (proper_of _ ok.1.2) h

def boundsBefore (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0
theorem before_sound (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries, Lower (vars e.1) (graphGoal e.1) e.2) (q : Nat) :
    Lower (vars q) (graphGoal q) (boundsBefore entries q) := by
  unfold boundsBefore
  cases h : entries.find? (fun a => a.1 == q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he := List.mem_of_find?_eq_some h
    have hit : (fun a : Nat × Nat => a.1 == q) e = true := List.find?_some (p:=fun a : Nat × Nat => a.1 == q) (a:=e) h
    have eq : e.1=q := beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he


structure BoundPool where
  domain : Sig
  bound : Nat
  paid : Nat
  wires : List Sig

def ValidPool (raw : List Sig) (T : Sig) (c : BoundPool) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬Constant (restrictRows f (observe T)) ∧
    (∀ q ws, Reach (roots.map observe) q ws → Available ws (restrictRows f (observe T)) → c.bound ≤ q) ∧
    Reach (roots.map observe) c.paid bank ∧ poolSupply f bank c.wires ∧ True

theorem build_valid {raw T d lb} (h : Slice raw T d lb) (cs : List Choice) {ws}
    (build : makePool d raw cs = some ws) : ValidPool raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa using hr,hs,trivial⟩

theorem valid_exclude {raw T c} (valid : ValidPool raw T c) (k : Nat) (rest : List Sig)
    (choice : Choice) (paid : Bool)
    (known : ∀ a ∈ rest, availableB c.domain c.wires a = true)
    (buy : if paid then choiceOK c.domain c.wires choice = true
       else availableB c.domain c.wires (choiceVal choice) = true)
    (bound : k+c.paid+paid.toNat <
      c.bound+(choiceVal choice :: rest).countP (isMaskedConstant c.domain))
    (nd : (choiceVal choice :: rest).Nodup) :
    Impossible T k (choiceVal choice :: rest).toFinset := by
  intro t num ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩ := valid
  let ws := choiceVal choice::rest
  have done (n : Nat) (out : List (Wire Row)) (reach : Reach (roots.map observe) n out)
      (zs : poolSupply f out (choiceVal choice::rest)) (le : n = c.paid+paid.toNat) : False := by
    have covered : supply out ((ws.map observe).map (restrictRows f)) := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
      exact zs _ ha
    have b := projected_bound f (list_run run ws nd rfl) nc reach covered lo
    have cm := count_constants dom ws
    change k+c.paid+paid.toNat < c.bound+ws.countP (isMaskedConstant c.domain) at bound
    omega
  cases paid with
  | false =>
    apply done _ _ hp _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact availableB_sound dom hs buy
    · exact availableB_sound dom hs (known _ hm)
  | true =>
    obtain ⟨out,hr,hc⟩ := pay_choice dom hp hs choice buy
    apply done _ _ hr _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact hc _ (by simp)
    · have avail := availableB_sound dom hs (known _ hm)
      rcases avail with mem | con
      · have ha : availableB c.domain c.wires a = true := known _ hm
        have point : ∀ u ∈ c.wires, Available out (restrictRows f (observe u)) :=
          fun u hu => hc u (List.mem_cons_of_mem _ hu)
        exact availableB_sound dom point ha
      · exact Or.inr con

def scalarPoolCut (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) :=
  let z := choiceVal op
  let extra := !(availableB c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (isMaskedConstant c.domain)) &&
    rest.all (availableB c.domain c.wires)) && (!extra || choiceOK c.domain c.wires op)

theorem scalarPoolCut_sound {raw T c} (valid : ValidPool raw T c) {k rest op}
    (nd : (choiceVal op::rest).Nodup) (cut : scalarPoolCut c k rest op = true) :
    Impossible T k (choiceVal op::rest).toFinset := by
  let extra := !(availableB c.domain c.wires (choiceVal op))
  apply valid_exclude valid k rest op extra _ _ _ nd
  · simp only [scalarPoolCut,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [scalarPoolCut,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : availableB c.domain c.wires (choiceVal op) <;> simp_all [extra]
  · simp only [scalarPoolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1

def materialize (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option BoundPool :=
  (makePool d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
theorem materialize_sound {raw T d L cs c} (slice : Slice raw T d L)
    (h : materialize raw cs d L = some c) : ValidPool raw T c := by
  unfold materialize at h
  cases he : makePool d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst c
    exact build_valid slice cs he


abbrev Bits := BitVec 768
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 768 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 768 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 768 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 768 → Row) (x : Decor) := x.2 = pairSig r s x.1
def dneg (x : Decor) : Decor := (neg x.1,~~~x.2.1,~~~x.2.2)
def dbin (d : Bool) (x y : Decor) : Decor :=
  if d then (bin d x.1 y.1,x.2.1 ||| y.2.1,x.2.2 ||| y.2.2)
  else (bin d x.1 y.1,x.2.1 &&& y.2.1,x.2.2 &&& y.2.2)

theorem ofRows_neg (r : Fin 768 → Row) (a : Sig) : ofRows r (neg a) = ~~~ofRows r a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (neg a) ⟨j,hj⟩
  rw [bit_neg,←ofRows_bit r a ⟨j,hj⟩] at h
  simpa only [BitVec.getLsbD_not,hj,decide_true,Bool.true_and] using h
theorem ofRows_bin (r : Fin 768 → Row) (d : Bool) (a b : Sig) :
    ofRows r (bin d a b) = if d then ofRows r a ||| ofRows r b else ofRows r a &&& ofRows r b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (bin d a b) ⟨j,hj⟩
  rw [bit_bin,←ofRows_bit r a ⟨j,hj⟩,←ofRows_bit r b ⟨j,hj⟩] at h
  cases d <;> simpa only [Bool.false_eq_true,ite_false,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_or] using h
theorem faithful_neg {r s x} (h : faithful r s x) : faithful r s (dneg x) := by
  change x.2 = _ at h
  simp only [faithful,dneg,pairSig,ofRows_neg, h]
theorem faithful_bin {r s x y} (d) (hx : faithful r s x) (hy : faithful r s y) :
    faithful r s (dbin d x y) := by
  change x.2 = _ at hx
  change y.2 = _ at hy
  cases d <;> simp only [faithful,dbin,Bool.false_eq_true,ite_false,ite_true,pairSig,ofRows_bin,hx,hy]

def codeDecor (op : Nat) (x y : Decor) := if op=2 then dneg x else dbin (op==1) x y
def defaultDecor : Decor := (zero,0,0)
theorem faithful_default (r s) : faithful r s defaultDecor := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · change (0 : Bits).getLsbD j = (ofRows r zero).getLsbD j
    rw [show (ofRows r zero).getLsbD j = bit (r ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
  · change (0 : Bits).getLsbD j = (ofRows s zero).getLsbD j
    rw [show (ofRows s zero).getLsbD j = bit (s ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
theorem faithful_get {r s ws} (all : ∀ v ∈ ws, faithful r s v) (i : Nat) :
    faithful r s (List.getD ws i defaultDecor) := by
  simp only [List.getD_eq_getElem?_getD]
  cases e : ws[i]? with
  | none => exact faithful_default _ _
  | some v => exact all _ (List.mem_of_getElem? e)
def decodeBank (n : Nat) (bits : Nat) (ws : List Decor) : List Decor :=
  match n with
  | 0 => ws
  | k+1 =>
    let a := ws.getD (bits &&& 15) defaultDecor
    let b := ws.getD ((bits >>> 4) &&& 15) defaultDecor
    decodeBank k (bits >>> 10) (ws++[codeDecor ((bits >>> 8) &&& 3) a b])
theorem decode_faithful (n bits) (ws) (r s) (base : ∀ v ∈ ws, faithful r s v) :
    ∀ v ∈ decodeBank n bits ws, faithful r s v := by
  induction n generalizing ws bits with
  | zero => exact base
  | succ n ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with hw | hz
    · exact base _ hw
    · obtain rfl := List.mem_singleton.mp hz
      unfold codeDecor
      split
      · exact faithful_neg (faithful_get base _)
      · exact faithful_bin _ (faithful_get base _) (faithful_get base _)

def asRow (cols : Nat → Bits) (i : Fin 768) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 9 => (cols j.val).getLsbD i.val))).toFin.cast
    (by simp [List.length_ofFn])
theorem coordinate0 : ∀ r : Row, bit r (inputs.getD 0 zero) = r.val.testBit 0 := by decide +kernel
theorem coordinate1 : ∀ r : Row, bit r (inputs.getD 1 zero) = r.val.testBit 1 := by decide +kernel
theorem coordinate2 : ∀ r : Row, bit r (inputs.getD 2 zero) = r.val.testBit 2 := by decide +kernel
theorem coordinate3 : ∀ r : Row, bit r (inputs.getD 3 zero) = r.val.testBit 3 := by decide +kernel
theorem coordinate4 : ∀ r : Row, bit r (inputs.getD 4 zero) = r.val.testBit 4 := by decide +kernel
theorem coordinate5 : ∀ r : Row, bit r (inputs.getD 5 zero) = r.val.testBit 5 := by decide +kernel
theorem coordinate6 : ∀ r : Row, bit r (inputs.getD 6 zero) = r.val.testBit 6 := by decide +kernel
theorem coordinate7 : ∀ r : Row, bit r (inputs.getD 7 zero) = r.val.testBit 7 := by decide +kernel
theorem coordinate8 : ∀ r : Row, bit r (inputs.getD 8 zero) = r.val.testBit 8 := by decide +kernel
theorem input_coords : ∀ (j : Fin 9) (r : Row),
    bit r (inputs.getD j.val zero) = r.val.testBit j.val := by
  intro j r
  fin_cases j
  · exact coordinate0 r
  · exact coordinate1 r
  · exact coordinate2 r
  · exact coordinate3 r
  · exact coordinate4 r
  · exact coordinate5 r
  · exact coordinate6 r
  · exact coordinate7 r
  · exact coordinate8 r
theorem asRow_bit (cols : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow cols i) (inputs.getD j.val zero) = (cols j.val).getLsbD i.val := by
  rw [input_coords]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 9 => (cols h.val).getLsbD i.val))).getLsbD j.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]
def rawDecor (m : Nat) (p q : Nat → Bits) : List Decor :=
  (selected m).map (fun (j,a) => (a,p j,q j))
theorem selected_entry {m j a} (h : (j,a) ∈ selected m) :
    j<9 ∧ a=inputs.getD j zero := by
  obtain ⟨v,hv,hh⟩ := List.mem_filterMap.mp h
  simp only [List.mem_range] at hv
  split at hh
  next =>
    cases hh
    exact ⟨hv,rfl⟩
  next => contradiction
theorem raw_faithful (m) (p q : Nat → Bits) :
    ∀ a ∈ rawDecor m p q, faithful (asRow p) (asRow q) a := by
  intro a ha
  obtain ⟨⟨j,v⟩,hv,rfl⟩ := List.mem_map.mp ha
  obtain ⟨hj,rfl⟩ := selected_entry hv
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · exact (asRow_bit p ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm
  · exact (asRow_bit q ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm

def liftGoal (m : Nat) (v : Nat → Bits) : Bits :=
  let x := fun j => if m.testBit j then v j else 0
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide),pos 8 (by decide)]
abbrev Cov := Bits × Bits × Bits

def addCov (z : Bits) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))

def coverage (d : Bool) (v : List Decor) : Cov :=
  v.foldr (fun a c => addCov (column d a.2) c) (0,0,0)

def takeOne (c : Cov) (a : Bits) : Bits := c.1 &&& ~~~(c.2.1 &&& a)
def takeTwo (c : Cov) (a b : Bits) : Bits :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))

private theorem cov_one (c : Cov) (a : Bits) : takeOne (addCov a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl

private theorem cov_two (c : Cov) (a b : Bits) : takeTwo (addCov a (addCov b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem add_swap (c : Cov) (a b : Bits) : addCov a (addCov b c)=addCov b (addCov a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem cov_perm (d : Bool) {l r : List Decor} (h : l.Perm r) : coverage d l=coverage d r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (column d a.2)) ih
  | swap a b t => exact add_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2



theorem cov_word (d : Bool) (v : List Decor) {r s} (good : ∀ a ∈ v, faithful r s a) :
    (coverage d v).1 = covered d (pairSig r s) (v.map Prod.fst) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    change (column d a.2 ||| (coverage d v).1) = column d (pairSig r s a.1) ||| _
    rw [show a.2=pairSig r s a.1 from good _ (by simp),ih (fun a ha => good a (by simp [ha]))]

def delOne (ws : List Decor) (a : Decor) (keep : Bool) :=
  if keep then ws else ws.erase a
def delTwo (ws : List Decor) (a b : Decor) (ka kb : Bool) :=
  delOne (delOne ws a ka) b kb

theorem delOne_perm {ws : List Decor} (a : Decor) (ha : a ∈ ws) :
    ws.Perm (a::ws.erase a) := List.perm_cons_erase ha

theorem cover_one {ws : List Decor} (d : Bool) (a : Decor) (ha : a ∈ ws) (keep : Bool) :
    (coverage d (delOne ws a keep)).1 =
      (if keep then (coverage d ws).1 else takeOne (coverage d ws) (column d a.2)) := by
  cases keep
  · change (coverage d (ws.erase a)).1 = takeOne (coverage d ws) _
    rw [cov_perm d (delOne_perm a ha)]
    exact (cov_one _ _).symm
  · rfl
theorem delTwo_perm {ws : List Decor} (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws) (hne : a≠b) :
    ws.Perm (a::b::(ws.erase a).erase b) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm hne)).mpr hb
  exact (delOne_perm a ha).trans (List.Perm.cons _ (delOne_perm b hm))

theorem cover_two {ws : List Decor} (d : Bool) (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a ≠ b) (ka kb : Bool) :
    (coverage d (delTwo ws a b ka kb)).1 =
      (if ka then (if kb then (coverage d ws).1 else takeOne (coverage d ws) (column d b.2))
       else if kb then takeOne (coverage d ws) (column d a.2)
       else takeTwo (coverage d ws) (column d a.2) (column d b.2)) := by
  cases ka <;> cases kb
  · change (coverage d ((ws.erase a).erase b)).1 = takeTwo (coverage d ws) _ _
    rw [cov_perm d (delTwo_perm a b ha hb ne)]
    exact (cov_two _ _ _).symm
  · exact cover_one d a ha false
  · exact cover_one d b hb false
  · rfl

def sameWords (a b : List Sig) := (a.all (fun x => b.contains x)) && (b.all (fun x => a.contains x))
theorem sameWords_sound {xs ys} (h : sameWords xs ys = true) : xs.toFinset=ys.toFinset := by
  simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  ext a
  simp only [List.mem_toFinset]
  exact ⟨h.1 a,h.2 a⟩


def keyWord (v : Sig) :=
  let n := v.toNat % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
def keySet (xs : List Sig) := xs.foldl (fun v x => v+keyWord x) 0

def closeChild (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut p k rest op)

theorem closeChild_sound {raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild pools links k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok

abbrev CovPair := Cov × Cov
def preCov (ws : List Decor) : CovPair := (coverage false ws,coverage true ws)
def getCov (c : CovPair) (d : Bool) := if d then c.2 else c.1
theorem get_preCov (ws) (d : Bool) : getCov (preCov ws) d = coverage d ws := by cases d <;> rfl
def restCov (v : Cov) (a b : Bits) (un ka kb : Bool) :=
  if un then (if ka then v.1 else takeOne v a) else
    if ka then (if kb then v.1 else takeOne v b)
    else if kb then takeOne v a else takeTwo v a b
def opKeep (un ka kb : Bool) (a b : Decor) (ws : List Decor) :=
  if un then delOne ws a ka else delTwo ws a b ka kb

theorem rest_coverage {ws : List Decor} {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws)
    (un ka kb d : Bool) (ne : un=false → a≠b) :
    (coverage d (opKeep un ka kb a b ws)).1 =
      restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) un ka kb := by
  rw [get_preCov]
  cases un
  · exact cover_two d a b ha hb (ne rfl) ka kb
  · exact cover_one d a ha ka

theorem delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem keep_sub (ws : List Decor) (a b : Decor) (un ka kb : Bool) :
    (opKeep un ka kb a b ws).Sublist ws := by
  cases un
  · exact (delOne_sub _ _ _).trans (delOne_sub _ _ _)
  · exact delOne_sub _ _ _
theorem len_keep (ws : List Decor) (a b : Decor) (un ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : un=false → a≠b) :
    (opKeep un ka kb a b ws).length =
      ws.length - (if ka then 0 else 1) - (if un || kb then 0 else 1) := by
  cases un
  · have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm (ne rfl))).mpr hb
    cases ka <;> cases kb <;> simp [opKeep,delTwo,delOne,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]
  · cases ka <;> cases kb <;> simp [opKeep,delOne,List.length_erase_of_mem ha]

def movedDecor (op : Nat) (a b : Decor) := codeDecor op a b
def movedChoice (op : Nat) (a b : Decor) : Choice := (op,a.1,b.1)
theorem moved_full (op) (a b : Decor) :
    (movedDecor op a b).1 = choiceVal (movedChoice op a b) := by
  by_cases h : op=2
  · simp [movedDecor,codeDecor,h,dneg,choiceVal,movedChoice]
  · cases hh : op==1 <;> simp [movedDecor,codeDecor,h,hh,dbin,choiceVal,movedChoice]
theorem moved_faithful {r s a b} (ha : faithful r s a) (hb : faithful r s b) (op : Nat) :
    faithful r s (movedDecor op a b) := by
  unfold movedDecor codeDecor
  split
  · exact faithful_neg ha
  · exact faithful_bin _ ha hb

abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List (List Sig))
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let un := op==2
  let len := 1+(n - (if ka then 0 else 1) - (if un || kb then 0 else 1))
  if len>cap then true else
    let d := len==cap
    let rs := restCov (getCov cov d) (column d a.2) (column d b.2) un ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 768 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (opKeep un ka kb a b ws).map Prod.fst
      closeChild pools links (cap-1) rest (movedChoice op a b)

def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (movedDecor op a b).1 :: (opKeep (op==2) ka kb a b ws).map Prod.fst
theorem evalMove_sound {raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : (op==2)=false → a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible T (cap-1) (List.toFinset xs))
    (pro : proper (movedDecor op a b).1) (fresh : (movedDecor op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove (cap,ws.length,ws,preCov ws,pools,links) op a b (movedDecor op a b) ka kb = true) :
    Impossible T (cap-1) (moveFront ws op a b ka kb).toFinset := by
  let z := movedDecor op a b
  let rest := opKeep (op==2) ka kb a b ws
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := keep_sub _ _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : properB z.1 = true := by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if (op==2) || kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k t hk h
  have hsz := (live_size h).2
  change child.toFinset.card + t ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold evalMove at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  have sep := cover_required h hk ndc (pair_sep pairs)
  have ce : cap-1+1=cap := by omega
  rw [ce] at sep
  let d := child.length==cap
  have g : (coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz := rest_coverage ha hb (op==2) ka kb d ne
  have hf := moved_faithful (faith _ ha) (faith _ hb) op
  have deq : decide (child.length=cap) = (child.length==cap) := by by_cases he : child.length=cap <;> simp [he]
  change covered (decide (child.length = cap)) (pairSig r s) child = BitVec.allOnes 768 at sep
  rw [deq] at sep
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) (op==2) ka kb ||| column d z.2) != BitVec.allOnes 768) = false := by simp [sep]
  change (if (_ != _) then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  have val := moved_full op a b
  change z.1 = _ at val
  change Live T k t child.toFinset at h
  have nd' := ndc
  change (z.1::rest.map Prod.fst).Nodup at nd'
  change Live T k t (z.1::rest.map Prod.fst).toFinset at h
  rw [val] at nd' h
  exact closeChild_sound pv lv nd' test k t hk h


def testPair (ctx : NodeContext) (a b : Decor) (d : Bool) :=
  let op := if d then 1 else 0
  let z := movedDecor op a b
  let attempt := evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
  let z := movedDecor 2 a a
  evalMove ctx 2 a a z false false && evalMove ctx 2 a a z true true &&
    bs.all (fun b => testPair ctx a b false && testPair ctx a b true)
def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs && testAll ctx bs

theorem all_unary {ctx ws} (h : testAll ctx ws=true) {a : Decor} (ha : a∈ws) (keep : Bool) :
    evalMove ctx 2 a a (movedDecor 2 a a) keep keep=true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow] at h
    rcases List.mem_cons.mp ha with rfl | hm
    · cases keep
      · exact h.1.1.1
      · exact h.1.1.2
    · exact ih h.2 hm

theorem all_binary {ctx ws} (h : testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) (d : Bool) : testPair ctx a b d=true ∨ testPair ctx b a d=true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      left
      cases d <;> first | exact (h.1.2 b bm).1 | exact (h.1.2 b bm).2
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · right
        cases d <;> first | exact (h.1.2 a haTail).1 | exact (h.1.2 a haTail).2
      · exact ih h.2 haTail hbTail

theorem testPair_at {ctx a b d} (h : testPair ctx a b d = true) (ka kb : Bool) :
    evalMove ctx (if d then 1 else 0) a b (movedDecor (if d then 1 else 0) a b) ka kb = true := by
  simp only [testPair,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2

theorem keep_mem {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w=a ∧ k=true) ∨ w∈v := by cases k <;> simp [kept]
theorem mem_delone {v : List Decor} (nd : v.Nodup) (a w : Decor) (k : Bool) :
    w ∈ delOne v a k ↔ w∈v ∧ (w≠a ∨ k=true) := by
  cases k <;> simp [delOne,nd.mem_erase_iff,and_comm]

theorem unique_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (eq : a.1=b.1) : a=b := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    obtain ⟨hn,ht⟩ := List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | haTail <;> rcases List.mem_cons.mp hb with rfl | hbTail
    · rfl
    · exact False.elim (hn (eq ▸ List.mem_map_of_mem hbTail))
    · exact False.elim (hn (eq.symm ▸ List.mem_map_of_mem haTail))
    · exact ih ht haTail hbTail

theorem kept_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (un ka kb : Bool) (v : Sig) :
    v ∈ (opKeep un ka kb a b ws).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (un=true ∨ v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  cases un <;> simp only [opKeep,Bool.false_eq_true,ite_false,ite_true,delTwo,List.mem_map,
    mem_delone wn,mem_delone dn,or_false,false_or,true_or,and_true] <;> constructor
  all_goals
    first
    | rintro ⟨w,hw,rfl⟩
      first
      | exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (unique_value nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (unique_value nd hw.1.1 hb eq)) id⟩
      | exact ⟨⟨_,hw.1,rfl⟩,hw.2.imp (fun ne eq => ne (unique_value nd hw.1 ha eq)) id⟩
    | rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
      exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩
    | rintro ⟨⟨w,hm,rfl⟩,h1⟩
      exact ⟨w,⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩

theorem unary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a : Decor} (ha : a∈ws)
    (keep : Bool) :
    (moveFront ws 2 a a keep keep).toFinset = (childOne (ws.map Prod.fst) a.1 keep).toFinset := by
  ext v
  simp only [moveFront,childOne,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha ha,keep_mem,nd.mem_erase_iff,movedDecor,codeDecor,dneg,ite_true,
    Nat.reduceBEq,true_or,and_true]
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  by_cases e : v=a.1 <;> cases keep <;> simp_all

theorem binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d ka kb : Bool) :
    (moveFront ws (if d then 1 else 0) a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv := List.mem_map_of_mem (f:=Prod.fst) hb
  cases d <;> simp only [moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha hb,keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,movedDecor,codeDecor,dbin,
    Bool.false_eq_true,Nat.reduceBEq,ite_true,ite_false,false_or]
  all_goals by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all

theorem childTwo_swap (v : List Sig) (nd : v.Nodup) (a b : Sig) (d ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a d kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_comm d b a]
  tauto

theorem node_sound {raw T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible T (cap-1) (List.toFinset xs))
    (checks : testAll (cap,ws.length,ws,preCov ws,pools,links) ws = true) :
    Impossible T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k t hk h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    cases h
    exact out (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply enum_step nd out
  · intro v hv keep fresh pro len
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv
    have hf := unary_front nd ha keep
    rw [←hf]
    exact evalMove_sound pairs faith nd ha ha (by simp) hc' pv lv pro fresh (all_unary checks ha keep)
  · intro a ha b hb d ka kb ne fresh pro len
    obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
    obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
    have ab : a≠b := fun e => ne (congrArg Prod.fst e)
    have one (a b : Decor) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
        (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
        (test : testPair (cap,ws.length,ws,preCov ws,pools,links) a b d = true) :
        Impossible T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
      rw [←binary_front nd aa bb ne']
      have eq : (movedDecor (if d then 1 else 0) a b).1 = bin d a.1 b.1 := by cases d <;> rfl
      exact evalMove_sound pairs faith nd aa bb (fun _ e => ne' (congrArg Prod.fst e)) hc' pv lv
        (eq ▸ pr) (eq ▸ fr) (testPair_at test ka kb)
    rcases all_binary checks haW hbW ab d with hh | hh
    · exact one a b haW hbW ne ka kb pro fresh hh
    · rw [childTwo_swap _ nd]
      exact one b a hbW haW (Ne.symm ne) kb ka (bin_comm d a.1 b.1 ▸ pro)
        (bin_comm d a.1 b.1 ▸ fresh) hh


theorem agree_inputs (r s : Row) (h : ∀ a ∈ inputs, bit r a = bit s a) : r=s := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<9
  · let i : Fin 9 := ⟨j,hj⟩
    have hm : inputs.getD i.val zero ∈ inputs := by
      rw [← input_list]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (input_coords i r).symm.trans ((h _ hm).trans (input_coords i s))
  · have le : 512 ≤ 2^j := by
      change 2^9 ≤ 2^j
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt le)).trans
      (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le s.isLt le)).symm

def composedOK (p q : List Move) := inputs.all (fun a => movedWord p (movedWord q a) == a)
theorem composed_id {p q} (h : composedOK p q = true) (r : Row) :
    movedRow q (movedRow p r) = r := by
  apply agree_inputs
  intro a ha
  rw [←bit_moved,←bit_moved]
  have eq := beq_iff_eq.mp (List.all_eq_true.mp h a ha)
  rw [eq]

def autoOK (T : Sig) (p : List Move) :=
  (movedWord p T == T) && composedOK p p.reverse && composedOK p.reverse p
theorem rotate_excluded {T n} {ws : List Sig} (hi : Impossible T n ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) : Impossible T n (ws.map (movedWord p.reverse)).toFinset := by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p) := fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k t hk h
  have run := live_rename h (movedRow p) onto
  have goal : rename (movedRow p) T = T := (moved_eq_rename p T).symm.trans ok.1.1
  have inv (x : Sig) : rename (movedRow p) (movedWord p.reverse x) = x := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j,hj⟩ _ = bit ⟨j,hj⟩ _
    rw [bit_rename,bit_moved,composed_id ok.1.2]
  have back : (ws.map (movedWord p.reverse)).toFinset.image (rename (movedRow p)) = ws.toFinset := by
    ext a
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩
      simpa only [inv] using hw
    · intro ha
      exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k t hk run

abbrev Packing := Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)
def emptyPacking : Packing := (0,0,0,0,0,0,0,fun _ => 0)
def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/8192
  let shift := pos % 8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)


def lookupWord (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh)%slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots)%16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none


inductive IndexTree (α : Type) where
  | leaf (items : List α)
  | fork (pivot : Nat) (left right : IndexTree α)
def IndexTree.read {α} : IndexTree α → Nat → Option α
  | .leaf xs,i => xs[i]?
  | .fork pivot a b,i => if i<pivot then a.read i else b.read (i-pivot)
def IndexTree.values {α} : IndexTree α → List α
  | .leaf xs => xs
  | .fork _ a b => a.values ++ b.values
theorem IndexTree.read_mem {α} (tree : IndexTree α) {i x} (e : tree.read i=some x) :
    x ∈ tree.values := by
  induction tree generalizing i with
  | leaf xs => exact List.mem_of_getElem? e
  | fork pivot a b ia ib =>
    simp only [IndexTree.read] at e
    split at e
    · exact List.mem_append_left _ (ia e)
    · exact List.mem_append_right _ (ib e)

structure Forest where
  mask : Nat
  cap : Nat
  samples : Nat → Bits × Bits
  cols : IndexTree ColumnInfo
  autos : Array (List Nat)
  levels : Nat → Packing
  index : Nat → Nat → Option (Nat × Nat)

def wiresOf (g : Forest) :=
  let ws := rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  let nonedge := dneg (dbin false (ws.getD 0 defaultDecor) (ws.getD 1 defaultDecor))
  if g.mask=1023 then ws.map (fun w => dbin false w nonedge) else ws
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a := by
  have base := raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  intro a ha
  unfold wiresOf at ha
  split at ha
  · obtain ⟨w,hw,rfl⟩ := List.mem_map.mp ha
    exact faithful_bin false (base w hw) (faithful_neg (faithful_bin false
      (faithful_get base 0) (faithful_get base 1)))
  · exact base _ ha

def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) :=
  if m=1023 then liftGoal m v &&& ~~~(v 0 &&& v 1) else liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  by_cases e : m=1023
  · have u := asRow_bit v i (0 : Fin 9)
    have w := asRow_bit v i (1 : Fin 9)
    have h := bit_liftGoal m v i
    change (inputs.getD 0 zero).getLsbD (asRow v i).val = (v 0).getLsbD i.val at u
    change (inputs.getD 1 zero).getLsbD (asRow v i).val = (v 1).getLsbD i.val at w
    have seedEq : seed = inputs.getD 0 zero &&& inputs.getD 1 zero := by decide +kernel
    simp only [chartGoal,chartSamples,e,ite_true,bit,seedEq,BitVec.getLsbD_and,
      BitVec.getLsbD_not,(asRow v i).isLt,i.isLt,decide_true,Bool.true_and,u,w] at h ⊢
    rw [h]
  · simpa only [chartGoal,chartSamples,e,ite_false] using bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 768) (hq : chartSamples m q = 0) :
    properPairs (chartGoal m) (asRow p) (asRow q) := by
  intro i
  simp only [chart_bit,hp,hq,BitVec.getLsbD_allOnes,i.isLt,decide_true,BitVec.getLsbD_zero]
  simp
def selectLive {α : Type} (bits : Nat) : List α → List α
  | [] => []
  | w::ws => if bits &&& 1 == 1 then w::selectLive (bits >>> 1) ws else selectLive (bits >>> 1) ws
theorem selectLive_sub {α : Type} (bits : Nat) (ws : List α) : (selectLive bits ws).Sublist ws := by
  induction ws generalizing bits with
  | nil => exact List.Sublist.slnil
  | cons a ws ih =>
    unfold selectLive
    split
    · exact List.Sublist.cons₂ _ (ih _)
    · exact List.Sublist.cons _ (ih _)

def storedDepth (_g : Forest) (depth : Nat) := depth
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,_,_,lw,data) := g.levels k
  let len := 10*storedDepth g depth
  let width := len+raw.length+depth
  let recp := if lw=128 then data (2*i) else packedAt data (i*width) width
  let stored := recp &&& ((1 <<< len)-1)
  let ops := stored
  let bank := decodeBank depth ops raw
  (ops,bank,selectLive (recp >>> len) bank)

def getFieldV (x pos width : Nat) := (x >>> pos) &&& ((1 <<< width)-1)
def chosenSteps (bank : List Decor) (ops paid : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let more := chosenSteps bank (ops >>> 10) (paid >>> 1) n
    if paid &&& 1 == 0 then more else
      (getFieldV ops 8 2,(bank.getD (ops &&& 15) defaultDecor).1,
        (bank.getD (getFieldV ops 4 4) defaultDecor).1) :: more

def buildRule (g : Forest) (ops d : Nat) (bank : List Decor) (idx paid : Nat) : Option BoundPool :=
  (g.cols.read idx).bind fun ci =>
    materialize (vars g.mask) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols.values, Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid = some c) :
    ValidPool (vars g.mask) (targetOf g) c := by
  unfold buildRule at h
  cases e : g.cols.read i with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply materialize_sound _ h
    exact cols ci (g.cols.read_mem e)

def getPairs (data : Nat → Nat) (w v : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x := packedAt data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w) :: getPairs data w v n (pos+w+v)

def stateSet (g : Forest) (k i : Nat) := (readNode g k i).2.2.map Prod.fst
def linkedSet (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (stateSet g k pair.1).map (movedWord (perm.map swapRows).reverse)

theorem linkedSet_sound (g : Forest) (k : Nat)
    (names : ∀ x ∈ g.autos.toList, autoOK (targetOf g) (x.map swapRows) = true)
    (earlier : ∀ i < (g.levels k).1, Impossible (targetOf g) k (stateSet g k i).toFinset)
    {pair out} (h : linkedSet g k pair = some out) :
    Impossible (targetOf g) k out.toFinset := by
  unfold linkedSet at h
  split at h
  · contradiction
  next valid =>
    cases e : g.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact rotate_excluded (earlier _ (by omega)) _ (names _ (by simpa using Array.mem_of_getElem? e))

def readCutHints : Nat → Nat → List (Nat × Nat)
  | 0, _ => []
  | n+1, v => (v &&& 127,(v >>> 7) &&& 127)::readCutHints n (v >>> 14)

def usefulHint (k : Nat) (ws : List Decor) (pool : BoundPool) :=
  decide (k-1+pool.paid < pool.bound + 1 + (ws.countP fun w => isMaskedConstant pool.domain w.1)) &&
  decide ((ws.countP fun w => !(availableB pool.domain pool.wires w.1)) ≤ 2)

def smartHints (g : Forest) (k i ops depth : Nat) (bank ws : List Decor) (blob : Nat) :=
  (readCutHints (blob &&& 1023) (blob >>> 10)).filter fun (f,paid) =>
    match buildRule g ops depth bank f paid with
    | none => false
    | some pool => usefulHint k ws pool

def nodeVerified (g : Forest) (k i : Nat) :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let values := ws.map Prod.fst
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let rules := (if lw=128 then smartHints g k i ops depth bank ws (data (2*i+1)) else getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  decide values.Nodup && !(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov ws,rules,ls) ws)

theorem nodeVerified_sound (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols.values, Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos.toList, autoOK (targetOf g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Impossible (targetOf g) (k-1) (stateSet g (k-1) j).toFinset)
    (checked : nodeVerified g k i = true) : Impossible (targetOf g) k (stateSet g k i).toFinset := by
  simp only [nodeVerified,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : targetOf g ∉ stateSet g k i := by simpa [stateSet] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t u lo h
    have ht : t=0 := by omega
    subst t
    generalize he : (stateSet g 0 i).toFinset = S at h
    cases h
    exact hT (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  apply node_sound (raw:=vars g.mask) samples _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
  · intro v hv
    apply decode_faithful _ _ _ _ _ (wires_faithful g) v
    exact (selectLive_sub _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact buildRule_sound g cols h
  · intro tag xs hx
    have e : ((g.index k tag).bind (linkedSet g (k-1)))=some xs := by simpa using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    exact linkedSet_sound g _ names (prior (by omega)) h


def block (g : Forest) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => nodeVerified g k (start+n) && block g k start n
theorem block_at {g k start n} (h : block g k start n=true) (j : Nat) (lo : start≤j) (hi : j<start+n) :
    nodeVerified g k j=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [block,Bool.and_eq_true] at h
    by_cases eq : j=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)
theorem block_merge {g k start a b} (h : block g k start a=true)
    (h' : block g k (start+a) b=true) : block g k start (a+b)=true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [block,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,block,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩

def checkedTables (g : Forest) (top : Nat) :=
  ∀ k ≤ top, block g k 0 (g.levels k).1 = true
def graphValid (g : Forest) (prior : Nat → Nat) :=
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 768) &&
  (chartSamples g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.values.all (fun c => colCheck g.mask c prior) &&
  g.autos.toList.all (fun p => autoOK (targetOf g) (p.map swapRows))

theorem forest_all (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geometry : graphValid g prior = true) (rows : checkedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible (targetOf g) k (stateSet g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    apply nodeVerified_sound g 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact block_at (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega))
    exact block_at (rows _ hk) i (by omega) (by omega)

def indexedRoot (g : Forest) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1) && sameWords (stateSet g k i) ws
theorem root_index {g top prior k i ws} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g top) (le : k ≤ top)
    (idx : indexedRoot g k i ws = true) : Impossible (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact forest_all g top prior low geom blocks _ le i idx.1

theorem lower_forest {g prior i hints} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g g.cap)
    (idx : indexedRoot g g.cap i (vars g.mask) = true) (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask) :
    Lower (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) _ (root_index low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

theorem lower_discard {g prior ci hints} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (ok : colCheck g.mask ci prior = true)
    (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask)
    (nd : (vars g.mask).Nodup)
    (cut : poolCut (subcube ci.1 ci.2.1) ci.2.2.2.2 g.cap 0 (vars g.mask) (vars g.mask)=true) :
    Lower (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) _ (poolCut_sound (col_sound ci prior low ok) [] rfl nd cut)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

def Known (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower (vars e.1) (graphGoal e.1) e.2
def extendKnown (old : List (Nat × Nat)) (L : Nat) (relabels : List (Nat × List Nat)) :=
  relabels.map (fun v => (v.1,L)) ++ old
theorem extendKnown_ok {old L m relabels} (previous : Known old)
    (main : Lower (vars m) (graphGoal m) L)
    (ok : relabels.all (fun v => relabelOK v.1 m v.2) = true) :
    Known (extendKnown old L relabels) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact relabel_of (List.all_eq_true.mp ok _ hv) main
  · exact previous e h
theorem baseKnown : Known [] := by simp [Known]
def lanePlace (v : Nat) (upper : Nat) := 2^769*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^769 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
theorem lanes_and {α} (f g : α → Bits) (xs) :
    combineLanes f xs &&& combineLanes g xs = combineLanes (fun x => f x &&& g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_and,ih]
theorem lanes_or {α} (f g : α → Bits) (xs) :
    combineLanes f xs ||| combineLanes g xs = combineLanes (fun x => f x ||| g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_or,ih]
theorem lanes_xor {α} (f g : α → Bits) (xs) :
    combineLanes f xs ^^^ combineLanes g xs = combineLanes (fun x => f x ^^^ g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_xor,ih]
theorem broadcast {α} (a : Bits) (xs : List α) :
    units xs.length * a.toNat = combineLanes (fun _ => a) xs := by
  induction xs with
  | nil => simp [units,combineLanes]
  | cons v xs ih => simp only [List.length_cons,units,combineLanes,lanePlace,Nat.add_mul,Nat.mul_assoc,ih,Nat.one_mul]

def fullMarks (r packed : Nat) := ((packed+r) >>> 768) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (769*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^769)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 769*(i+1)-769=769*i := by omega
      have ge : ¬769*(i+1)<769 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 768 = (a==BitVec.allOnes 768) := by
  by_cases h : a=BitVec.allOnes 768
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^768-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^768 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm

set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (769*i) =
      (f xs[i]==BitVec.allOnes 768) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^769*u+x+(2^769*v+1)=2^769*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^769 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬769*(i+1)+768<769 := by omega
      have di : 769*(i+1)+768-769=769*i+768 := by omega
      simp only [ge,ite_false,di,List.getElem_cons_succ]
      apply ih i (by omega)


abbrev PackedSig := Nat × Nat
abbrev PackedCov := Nat × Nat × Nat

def packedSig {α} (s : α → Signals) (xs : List α) : PackedSig :=
  (combineLanes (fun x => (s x).1) xs,combineLanes (fun x => (s x).2) xs)
def packedCov {α} (c : α → Cov) (xs : List α) : PackedCov :=
  (combineLanes (fun x => (c x).1) xs,combineLanes (fun x => (c x).2.1) xs,
   combineLanes (fun x => (c x).2.2) xs)
def packedColumn (d : Bool) (a : PackedSig) :=
  if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2

theorem xor_meet (a b : Bits) : a ^^^ (a &&& b) = a &&& ~~~b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

theorem packed_column {α} (s : α → Signals) (xs : List α) (d : Bool) :
    packedColumn d (packedSig s xs) = combineLanes (fun x => column d (s x)) xs := by
  cases d <;> simp only [packedColumn,packedSig,column,Bool.false_eq_true,ite_false,ite_true,lanes_and,lanes_xor,xor_meet]

def packedOp (full : Nat) (op : Nat) (a b : PackedSig) : PackedSig :=
  if op=2 then (full ^^^ a.1,full ^^^ a.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else (a.1 &&& b.1,a.2 &&& b.2)
theorem top_xor (a : Bits) : BitVec.allOnes 768 ^^^ a = ~~~a := BitVec.allOnes_xor
theorem packed_op {α} (a b : α → Decor) (xs : List α) (op : Nat) :
    packedOp (units xs.length*(BitVec.allOnes 768).toNat) op
      (packedSig (fun x => (a x).2) xs) (packedSig (fun x => (b x).2) xs) =
    packedSig (fun x => (movedDecor op (a x) (b x)).2) xs := by
  by_cases un : op=2
  · simp only [packedOp,un,ite_true,packedSig,broadcast,lanes_xor,top_xor,movedDecor,codeDecor,dneg]
  · by_cases one : op=1 <;> simp [packedOp,un,one,packedSig,lanes_or,lanes_and,movedDecor,codeDecor,dbin]

def takePacked (c : PackedCov) (a b : Nat) (un ka kb : Bool) :=
  let without1 := fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2 := c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if un then (if ka then c.1 else without1 a)
  else if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2

theorem takePacked_ok {α} (c : α → Cov) (a b : α → Bits) (xs : List α) (un ka kb : Bool) :
    takePacked (packedCov c xs) (combineLanes a xs) (combineLanes b xs) un ka kb =
    combineLanes (fun x => restCov (c x) (a x) (b x) un ka kb) xs := by
  cases un <;> cases ka <;> cases kb <;>
    simp only [takePacked,packedCov,lanes_and,lanes_or,lanes_xor,xor_meet,restCov,takeOne,takeTwo,
      Bool.false_eq_true,ite_false,ite_true]

def contextWire (c : NodeContext) (i : Nat) := c.2.2.1.getD i defaultDecor
def checkAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  evalMove c op a b (movedDecor op a b) ka kb
def combField (c : NodeContext) (d un ka kb : Bool) (op i j : Nat) :=
  let a := contextWire c i
  let b := contextWire c j
  restCov (getCov c.2.2.2.1 d) (column d a.2) (column d b.2) un ka kb |||
    column d (movedDecor op a b).2

def onMarks {α : Type} (f : α → Bool) (mask : Nat) : List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 769) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (769*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
  induction xs generalizing mask i with
  | nil => simp at hi
  | cons x xs ih =>
    have ne : mask≠0 := by intro e; simp [e] at bitOn
    simp only [onMarks,ne,ite_false,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
    cases i with
    | zero =>
      have nonzero : mask &&& 1 ≠ 0 := by
        intro he
        have at0 := congrArg (fun n : Nat => n.testBit 0) he
        simp only [Nat.testBit_and] at at0
        change mask.testBit 0=true at bitOn
        simp [bitOn] at at0
      exact ok.1.resolve_left nonzero
    | succ i =>
      apply ih (mask:=mask >>> 769) (i:=i) (by simpa using hi) _ ok.2
      simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn

abbrev Batch := Nat × Nat × Nat × List PackedSig × PackedCov × PackedCov
def makeBatch (k n : Nat) (xs : List NodeContext) : Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => packedSig (fun c => (contextWire c i).2) xs),
    packedCov (fun c => c.2.2.2.1.1) xs,packedCov (fun c => c.2.2.2.1.2) xs)
def laneWire (b : Batch) (i : Nat) := b.2.2.2.1.getD i (0,0)
theorem laneWire_at (k n) (xs) {i : Nat} (h : i<n) :
    laneWire (makeBatch k n xs) i = packedSig (fun c => (contextWire c i).2) xs := by
  simp [laneWire,makeBatch,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]

def availableMasked (p : BoundPool) (m : Sig) :=
  m==zero || m==p.domain || (p.wires.map (masked p.domain)).any (fun v => v==m)
theorem available_mask (p : BoundPool) (x : Sig) :
    availableB p.domain p.wires x = availableMasked p (masked p.domain x) := rfl

def constantLoss (p : Decor → Bool) (a : Decor) (keep : Bool) :=
  if keep then 0 else (p a).toNat
theorem lossBound (p : Decor → Bool) (ws : List Decor) (a : Decor) (keep : Bool) :
    ws.countP p ≤ (delOne ws a keep).countP p + constantLoss p a keep := by
  cases keep
  · simp only [delOne,Bool.false_eq_true,ite_false,constantLoss,List.countP_erase]
    split
    next h => simp [h.2]; omega
    next => omega
  · simp [delOne,constantLoss]

theorem keptCount (p : Decor → Bool) (ws : List Decor) (a b : Decor) (un ka kb : Bool) :
    ws.countP p - constantLoss p a ka - constantLoss p b (un || kb) ≤
    (opKeep un ka kb a b ws).countP p := by
  have h1 := lossBound p ws a ka
  have h2 := lossBound p (delOne ws a ka) b kb
  cases un <;> simp only [opKeep,delTwo,Bool.false_eq_true,ite_false,ite_true,
    Bool.false_or,Bool.true_or] <;> first | omega | simp [constantLoss]; omega

abbrev QuickPool := BoundPool × Nat × Bool
def summarizePool (ws : List Decor) (p : BoundPool) : QuickPool :=
  (p,ws.countP (fun w => isMaskedConstant p.domain w.1),
     ws.all (fun w => availableB p.domain p.wires w.1))
def fastCost (s : QuickPool) (k : Nat) (a b : Decor) (op : Nat) (ka kb : Bool) :=
  if !s.2.2 then false else
  let p := s.1
  let un := op==2
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := choiceVal (movedChoice op a b)
  let zm := masked p.domain z
  let zc := isMaskedConstant p.domain z
  let cm := s.2.1 - constantLoss const a ka - constantLoss const b (un || kb) + zc.toNat
  let free := zc || zm==masked p.domain a.1 || zm==masked p.domain b.1
  decide (k+p.paid+(!free).toNat < p.bound+cm)

theorem fastCost_good {p k ws a b op ka kb} (ha : a∈ws) (hb : b∈ws)
    (h : fastCost (summarizePool ws p) k a b op ka kb=true) :
    scalarPoolCut p k ((opKeep (op==2) ka kb a b ws).map Prod.fst) (movedChoice op a b)=true := by
  let z := choiceVal (movedChoice op a b)
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let free := isMaskedConstant p.domain z || masked p.domain z==masked p.domain a.1 ||
      masked p.domain z==masked p.domain b.1
  let rest := opKeep (op==2) ka kb a b ws
  have ck := keptCount const ws a b (op==2) ka kb
  change ws.countP const - constantLoss const a ka - constantLoss const b ((op==2) || kb) ≤ rest.countP const at ck
  by_cases all : ws.all (fun w => availableB p.domain p.wires w.1)=true
  · have hav := List.all_eq_true.mp all
    have ready : free=true → availableB p.domain p.wires z=true := by
      intro f
      simp only [free,Bool.or_eq_true,beq_iff_eq] at f
      rcases f with (zc|za)|zb
      · simp only [availableB,isMaskedConstant,Bool.or_eq_true] at zc ⊢
        exact Or.inl zc
      · rw [available_mask,za,←available_mask]
        exact hav _ ha
      · rw [available_mask,zb,←available_mask]
        exact hav _ hb
    have extra : (!availableB p.domain p.wires z).toNat ≤ (!free).toNat := by
      cases hf : free <;> cases he : availableB p.domain p.wires z <;> simp_all
    have hs : (rest.map Prod.fst).all (availableB p.domain p.wires)=true := by
      apply List.all_eq_true.mpr
      intro _ hm
      obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
      exact hav w ((keep_sub ws a b (op==2) ka kb).subset hw)
    have opOK : choiceOK p.domain p.wires (movedChoice op a b)=true := by
      simp [choiceOK,movedChoice,hav _ ha,hav _ hb]
    simp only [fastCost,summarizePool,all,Bool.not_true,Bool.false_eq_true,ite_false,decide_eq_true_eq] at h
    change k+p.paid+(!free).toNat < p.bound+(ws.countP const - constantLoss const a ka -
        constantLoss const b ((op==2)||kb)+(isMaskedConstant p.domain z).toNat) at h
    dsimp only [rest] at hs
    simp only [scalarPoolCut,hs,opOK,Bool.or_true,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
    change k+p.paid+(!availableB p.domain p.wires z).toNat <
      p.bound+(rest.countP const + if isMaskedConstant p.domain z then 1 else 0)
    cases hc : isMaskedConstant p.domain z <;> simp [hc] at h ⊢ <;> omega
  · simp [fastCost,summarizePool,all] at h

def quickAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  (c.2.2.2.2.1.map (summarizePool c.2.2.1)).any (fun s => fastCost s (c.1-1) a b op ka kb)

theorem quickAt_good {c i j op ka kb} (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length)
    (h : quickAt c i j op ka kb=true) : checkAt c i j op ka kb=true := by
  have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
    simp [contextWire,List.getD_eq_getElem?_getD,ht]
  obtain ⟨_,hm,ok⟩ := List.any_eq_true.mp h
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
  have closed := fastCost_good (mem _ hi) (mem _ hj) ok
  have cut : c.2.2.2.2.1.any (fun p => scalarPoolCut p (c.1-1)
      ((opKeep (op==2) ka kb (contextWire c i) (contextWire c j) c.2.2.1).map Prod.fst)
      (movedChoice op (contextWire c i) (contextWire c j)))=true :=
    List.any_eq_true.mpr ⟨p,hp,closed⟩
  simp only [checkAt,evalMove,closeChild,cut,Bool.or_true]
  repeat' split
  all_goals rfl

def fallbackAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  (if i<c.2.2.1.length ∧ j<c.2.2.1.length then quickAt c i j op ka kb else false) ||
    checkAt c i j op ka kb
theorem fallback_sound {c i j op ka kb} (h : fallbackAt c i j op ka kb=true) :
    checkAt c i j op ka kb=true := by
  simp only [fallbackAt,Bool.or_eq_true] at h
  rcases h with h | h
  · split at h
    next yes => exact quickAt_good yes.1 yes.2 h
    next => contradiction
  · exact h
def batchMove (b : Batch) (xs : List NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,u,v) := b
  let un := op==2
  let len := 1+(n-(if ka then 0 else 1)-(if un || kb then 0 else 1))
  if len>k then true else
    let d := len==k
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp (r*(BitVec.allOnes 768).toNat) op a b'
    let cov := if d then v else u
    let mask := fullMarks r (takePacked cov (packedColumn d a) (packedColumn d b') un ka kb ||| packedColumn d z)
    onMarks (fun c => fallbackAt c i j op ka kb) mask xs

theorem batchMove_at (k n) (xs : List NodeContext) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n)
    (pass : batchMove (makeBatch k n xs) xs i j op ka kb=true) :
    checkAt xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if (op==2) || kb then 0 else 1))
  let d := len==k
  have eval : checkAt xs[q] i j op ka kb =
      if len>k then true else if combField xs[q] d (op==2) ka kb op i j != BitVec.allOnes 768 then true
      else if !properB (movedDecor op (contextWire xs[q] i) (contextWire xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(movedDecor op (contextWire xs[q] i) (contextWire xs[q] j)).1)
      then true else closeChild xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
        ((opKeep (op==2) ka kb (contextWire xs[q] i) (contextWire xs[q] j) xs[q].2.2.1).map Prod.fst)
        (movedChoice op (contextWire xs[q] i) (contextWire xs[q] j)) := by
    simp only [checkAt,evalMove,budget,arity,len,d,combField] <;> rfl
  by_cases small : len>k
  · simp [eval,small]
  · let r := units xs.length
    let a := laneWire (makeBatch k n xs) i
    let b := laneWire (makeBatch k n xs) j
    let cov := if d then packedCov (fun c : NodeContext => c.2.2.2.1.2) xs
            else packedCov (fun c : NodeContext => c.2.2.2.1.1) xs
    change (if len>k then true else onMarks _ (fullMarks r
       (takePacked cov (packedColumn d a) (packedColumn d b) (op==2) ka kb |||
        packedColumn d (packedOp (r*(BitVec.allOnes 768).toNat) op a b))) xs) = true at pass
    rw [if_neg small] at pass
    have chosen : cov = packedCov (fun c => getCov c.2.2.2.1 d) xs := by
      dsimp only [cov]
      cases d <;> rfl
    have ca : a = _ := laneWire_at k n xs hi
    have cb : b = _ := laneWire_at k n xs hj
    dsimp only [r] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,chosen,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] d (op==2) ka kb op i j = BitVec.allOnes 768
    · apply fallback_sound
      apply marked_ok _ _ _ q hq _ pass
      rw [mark_at _ _ _ hq]
      exact beq_iff_eq.mpr hit
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]


def batchPair (b : Batch) (xs : List NodeContext) (i j op : Nat) :=
  let f := batchMove b xs i j op
  f false false && f true false && f false true && f true true
def batchRow (b : Batch) (xs : List NodeContext) (i : Nat) (js : List Nat) :=
  batchMove b xs i i 2 false false && batchMove b xs i i 2 true true &&
    js.all (fun j => batchPair b xs i j 0 && batchPair b xs i j 1)
def batchRows (b : Batch) (xs : List NodeContext) : List Nat → Bool
  | [] => true
  | i::js => batchRow b xs i js && batchRows b xs js

theorem batchRows_at (k n) (xs : List NodeContext) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (js : List Nat)
    (bounds : ∀ j ∈ js, j<n) (allRows : batchRows (makeBatch k n xs) xs js=true) :
    testAll xs[q] (js.map (contextWire xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [batchRows,Bool.and_eq_true,batchRow,List.all_eq_true] at allRows
    simp only [List.map_cons,testAll,testRow,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi := bounds i List.mem_cons_self
    have check := @batchMove_at k n xs
    refine ⟨⟨⟨check hi hi hq budget arity allRows.1.1.1,check hi hi hq budget arity allRows.1.1.2⟩,?_⟩,
      ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    have both := allRows.1.2 j hj
    have opCheck (d : Bool) (pass : batchPair (makeBatch k n xs) xs i j (if d then 1 else 0)=true) :
        testPair xs[q] (contextWire xs[q] i) (contextWire xs[q] j) d=true := by
      simp only [batchPair,Bool.and_eq_true] at pass
      simp only [testPair,Bool.and_eq_true]
      exact ⟨⟨⟨check hi hj' hq budget arity pass.1.1.1,check hi hj' hq budget arity pass.1.1.2⟩,
        check hi hj' hq budget arity pass.1.2⟩,check hi hj' hq budget arity pass.2⟩
    exact ⟨opCheck false both.1,opCheck true both.2⟩

def runBatch (k n : Nat) (xs : List NodeContext) :=
    batchRows (makeBatch k n xs) xs (List.range n)
theorem runBatch_at {k n} {xs : List NodeContext} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hn : xs[q].2.2.1.length=n)
    (pass : runBatch k n xs=true) : testAll xs[q] xs[q].2.2.1=true := by
  have all := batchRows_at k n xs hq hb ha (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (contextWire xs[q]) = xs[q].2.2.1 := by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [contextWire,List.getD_eq_getElem?_getD,h2]
  rwa [eq] at all

def contextOf (g : Forest) (k i : Nat) : NodeContext :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let rules := (if lw=128 then smartHints g k i ops depth bank ws (data (2*i+1)) else getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  (k,ws.length,ws,preCov ws,rules,ls)


def prelim (T : Sig) (c : NodeContext) :=
  let ws := c.2.2.1.map Prod.fst
  decide ws.Nodup && !(ws.contains T)
theorem from_context (g : Forest) (k i : Nat) :
    nodeVerified g k i = (prelim (targetOf g) (contextOf g k i) &&
      (if k=0 then true else testAll (contextOf g k i) (contextOf g k i).2.2.1)) := rfl

theorem makeBlock {g k start n} (h : ∀ (i : Nat), start ≤ i → i < start + n → nodeVerified g k i = true) :
    block g k start n=true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [block,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i le lt => h i le (by omega))⟩

def contexts (g : Forest) (k start n : Nat) :=
  ((List.range n).map (start+·)).map (contextOf g k)
def header (g : Forest) (k start n ar : Nat) :=
  (contexts g k start n).all (fun c => c.2.1==ar && prelim (targetOf g) c)
def rowCut (g : Forest) (k start n ar lo len : Nat) :=
  let xs := contexts g k start n
  let b := makeBatch k ar xs
  (List.range len).all (fun d =>
    let i := lo+d
    batchRow b xs i (List.range' (i+1) (ar-(i+1))))
theorem rowCut_at {g k start n ar lo len} (h : rowCut g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRow (makeBatch k ar (contexts g k start n)) (contexts g k start n)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha

theorem rowCut_merge {g k start n ar lo a b}
    (h : rowCut g k start n ar lo a=true) (t : rowCut g k start n ar (lo+a) b=true) :
    rowCut g k start n ar lo (a+b)=true := by
  apply List.all_eq_true.mpr
  intro j hj
  have jlt := List.mem_range.mp hj
  by_cases first : j<a
  · exact rowCut_at h (lo+j) (by omega) (by omega)
  · exact rowCut_at t (lo+j) (by omega) (by omega)

theorem cutsRun {g k start n ar} (h : rowCut g k start n ar 0 ar=true) :
    runBatch k ar (contexts g k start n)=true := by
  let xs := contexts g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      batchRows (makeBatch k ar xs) xs (List.range' lo num)=true := by
    induction num generalizing lo with
    | zero => rfl
    | succ num ih =>
      simp only [List.range'_succ,batchRows,Bool.and_eq_true]
      refine ⟨?_,ih (lo+1) (by omega)⟩
      have ok := rowCut_at h lo (by omega) (by omega)
      simpa only [show ar-(lo+1)=num by omega] using ok
  unfold runBatch
  rw [List.range_eq_range']
  exact go 0 ar (by omega)

theorem cutsBlock {g k start n ar} (hd : header g k start n ar=true)
    (h : rowCut g k start n ar 0 ar=true) : block g k start n=true := by
  apply makeBlock
  intro i lo hi
  let xs := contexts g k start n
  have hm : contextOf g k i ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩ := List.getElem_of_mem hm
  have one := List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k := by rw [e]; rfl
  have ha : xs[q].2.1=ar := e ▸ one.1
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  rw [from_context,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ runBatch_at hq hb ha hn (cutsRun h)

def boxes (g : Forest) (k start n ar lo num : Nat) : Nat → Prop
  | 0 => rowCut g k start n ar lo num=true
  | d+1 => boxes g k start n ar lo (num/2) d ∧ boxes g k start n ar (lo+num/2) (num-num/2) d
theorem boxesCut {g k start n ar lo num d} (h : boxes g k start n ar lo num d) :
    rowCut g k start n ar lo num=true := by
  induction d generalizing lo num with
  | zero => exact h
  | succ d ih =>
    have v := rowCut_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v

def cells (g : Forest) (k start n ar rows : Nat) : Nat → Prop
  | 0 => header g k start n ar=true ∧ boxes g k start n ar 0 ar rows
  | d+1 => cells g k start (n/2) ar rows d ∧ cells g k (start+n/2) (n-n/2) ar rows d
theorem cellsBlock {g k start n ar rows d} (h : cells g k start n ar rows d) :
    block g k start n=true := by
  induction d generalizing start n with
  | zero => exact cutsBlock h.1 (boxesCut h.2)
  | succ d ih =>
    have v := block_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v

def listPieces {α} (f : α → Bool) (xs : List α) : Nat → Prop
  | 0 => xs.all f=true
  | d+1 => listPieces f (xs.take (xs.length/2)) d ∧ listPieces f (xs.drop (xs.length/2)) d
theorem listPieces_all {α f xs d} (h : @listPieces α f xs d) : xs.all f=true := by
  induction d generalizing xs with
  | zero => exact h
  | succ d ih =>
    have ap : ((xs.take (xs.length/2)) ++ (xs.drop (xs.length/2))).all f=true := by
      simp only [List.all_append,ih h.1,ih h.2,Bool.and_self]
    simpa only [List.take_append_drop] using ap
def g15d3 (i : Nat) : Nat := 0xf
def g15l3 : Packing := (1,0,0,0,1,0,0,g15d3)
def g15samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbaf3ea78de4d799d,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff450cc90c3c245919),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdf7ff8fe9f9b7ed5,0x20812421801324c4),(0xefbdbf97f9f6bf6a,0x102a401415600a0a),(0xf3a9d7437375f5ba,0xfc028ab620235b0),(0,0),(0,0),(0,0),(0,0),(0,0)]
def g15columns : IndexTree ColumnInfo := (.leaf [])
def g15autos : Array (List Nat) := #[[],[33,48]]
def g15levels : Nat → Packing
  | 3 => g15l3
  | _ => emptyPacking
def g15index : Nat → Nat → Option (Nat × Nat)
  | 3 => fun _ => none
  | _ => fun _ => none
def g15 : Forest := ⟨15,3,fun j => g15samples[j]?.getD (0,0),g15columns,g15autos,g15levels,g15index⟩
def key31l6 (i : Nat) : Nat := 0x820007028af371d000003180048302e380000000003819155875690d58000003d
def g31d5 (i : Nat) : Nat := 0x84001e90fd02fd01fa00
def g31l5 : Packing := (3,1,3,0,4,4,0,g31d5)
def g31d6 (i : Nat) : Nat := 0x11a20bf
def g31l6 : Packing := (1,0,3,2,4,0,0,g31d6)
def g31samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdafffab2d55fb9f999d9ceeefacb357b78f9ce2bb554a3bac97b2a9d65,0x250142092220460600407048c382809c2160e048740030a88143281c44),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffef5dfed46f26fea572a7ba9effd7341aff97ad1ab5bd2d547d6793334b,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff90aa211010d10141c4300836206168204010183680184d04682483210b),(0x73ef3f3c8ff8df3fe567b556c9567ffcd665219778a6bd6e36bfd946ac,0xc10d0c3000214920a0d648109801012344d60802686b04210115006a4),(0x7c7fd57b7ffa3476e74d6f3fc4bddbd44dc213c5eb8bdea95bf6ee7492,0x38022048645c06490200044a25241818912934541000824c322ae5002),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8fe76ff6451fda6ff84b6daf38f5bb6f6a5ee88a4d6be3f71c64aa3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8076989008882001270e063010011622500c04308a174300141c40a239),(0,0),(0,0),(0,0),(0,0)]
def g31columns : IndexTree ColumnInfo := (.fork 2 (.leaf [(1,0,30,0,4),(2,0,29,0,4)]) (.leaf [(4,0,27,0,4),(8,0,23,0,4),(16,0,15,0,4)]))
def g31autos : Array (List Nat) := #[[],[50,65],[66,16],[67,50,33,16],[67,32],[67,66,49,32],[33,48],[67,50,65,48],[67,66,65,64],[49,64]]
def g31levels : Nat → Packing
  | 5 => g31l5
  | 6 => g31l6
  | _ => emptyPacking
def g31index : Nat → Nat → Option (Nat × Nat)
  | 5 => fun _ => none
  | 6 => lookupWord 5 25 2 10 2 4 (key31l6)
  | _ => fun _ => none
def g31 : Forest := ⟨31,6,fun j => g31samples[j]?.getD (0,0),g31columns,g31autos,g31levels,g31index⟩
def g47samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffddffff5cfaafae7dd35b9ce7bbffd6b6b7b7cfbb8d3b7ad85ddf257b56b575,0x2200a042011011800c00803812181c2009c1061c0107200c09440143143444),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeebefed537937fcb8ab173daa7df7f7691aff9776b2b7dcb92a3f3678b2b59,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9149112428688034a38448020d64a21d120601022ea84882b022a624830919),(0x77db9fef67fc77f3ffe6e3dd55f86b6fffcab66472f7c57fb768dabfad4eae,0x820641080010508440806b120004c020121a4ec1002247c020840112806a4),(0x78ebe4ae9ffd0d576de696b3cff805db7d426c00d8ded437ed436ff6f66c92,0x71419416322f057a950700411b6b328381c4110e8d4580325370f22d66812),(0,0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0bf9ebdb2287acd4afec26dbb6d98eabb3768bb508ca4b7f1fdd1c709a3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80f74f1424444852a26637058ca3a012d22680c12e48c8e17411561c608a3b),(0,0),(0,0),(0,0)]
def g47columns : IndexTree ColumnInfo := (.leaf [(8,0,39,0,4)])
def g47autos : Array (List Nat) := #[[],[83,32]]
def g47levels : Nat → Packing
  | _ => emptyPacking
def g47index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g47 : Forest := ⟨47,4,fun j => g47samples[j]?.getD (0,0),g47columns,g47autos,g47levels,g47index⟩
def g55samples : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffffdf7defdfafbfd3fcebcfdeffcebffefe76de77fed7f1773f95eb2ebeb,0x400028000010005000000400701010180030103060043200102204010904888),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdb7fbfbb9ad3afd94caf0b9db5bbdf7f7d39bfcdadcf77ec9eccd2fb9cf16b5,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2484444214284026a4e002420468a8a43140a00408d944460a4082569431231),(0xeda5e7e7b2fc29de4ffc371dba2bf0775ff12db9b18bb528fedad96afcd3c5e,0x12589919410293410206d0396285445a082c5d2bf0022b20f0895d2048c2c4e),(0,0),(0xf1cd79264efe956afa7a64bb677ab40beba463600362eda36f3357b7d763926,0xe3a8651b1a36a0acc57538a080f6ea703078a0c13c28dc34c91f3868663126),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe05fe74eda341d5872cbf684d5e2ed19e7e3bba5e964550dd792aec724f479,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01fb53db1204342a549861b60b6727a22d48ac0b14da4445855161ae724b471),(0,0),(0,0),(0,0)]
def g55columns : IndexTree ColumnInfo := (.leaf [(16,0,39,0,4)])
def g55autos : Array (List Nat) := #[[],[84]]
def g55levels : Nat → Packing
  | _ => emptyPacking
def g55index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g55 : Forest := ⟨55,4,fun j => g55samples[j]?.getD (0,0),g55columns,g55autos,g55levels,g55index⟩
def g63samples : Array (Bits × Bits) := #[(0xdabffdfdbdf61bfbfc7dcbe34f7f1b17917df75df7edd9eff77b6dbd3dcebed3cfbfaddba50fcabded46bc9b579eb7bd3d92776566ad4ad3debe36d74deb7f9faf189ad76da7dc1a6b4eaf21eb254de4ae1f7451bb34d9456fd18e934db17349,0x4400202400040800310000100084000ac0000102800a1100490002240004b2800a001b4000190000008108000574009200040400000594000190004218c0010840002890800550053044a00410008802d0060013000c004400188120c206208),(0xb6678efeffcbf5a9cad5bfd527a7a5bd74d1314b7915f5b2ffdec2fc5d978f8ab3b44b2b5add5b771711b15ce99bf2b3f5bce975ef94cd59a34e76ab937848a94ef6be6c9579db5905539ea703c87a7d4ae11fe2ae423fade4a3c3299b0724e7,0x499461811a200a55004cf88854029340027a680613c002ec00233c1096d01045025d0203d400243150030b7e4900b00499e023395882049d0206ec00041398010bbb1000b7310ad00cc0858112c8207810e917400e423d0034024309910504e5),(0xbfdd27bedf8fade4776ebf9d185bc5bd76aeffb29711f77d628e86e5fffdff6d1a52bff6da987348e3e147dcecdbcc68d1accc4e7d7d77b9734cfbbcefbc022d72eff5a31a72e32584dd5a72accb1256ede309af577ea6b3ab2be572a2769632,0x20983204990108b1910222a2810c12a8041040402e00006394000908008912a582448429aad10a21a0240190b504314209040621245140c82010e8812042049440841100c0c52080310832a5111106e902488a012c82618908a42202729212),(0x77ddb87389d95f9f7bbe7e8eb89e6e76fbf75ca7fd5bb3758b555b578affe964ae7e7fa493e06d03bebc4fb5cff51e46b2dd5bdbb1eab66f60f7d916b9c6944fd85b6f0fc30a2ae7d2afc9dc369ef80bb1b0b2dd52e9331e786f7a5d38e8c8b4,0x1482478012444200420888514440810c402202189081ecc814422aa4c048408050190921c0450c000a080254044021081134422900082c11250884167012813a48094aca870a3283708e41084282480000c012150640581c30655a55288040a4),(0xdca768aafb78ce8d2db2ec3fbdddfa4ec963339dbac7a8e05eccbf0bb99ddf5febcef6dc7762a4a79d9ad8f70324ba6e724754bded1eed86f695f276b70acbd73dc66e39a88d0cfed920a0ee10b5a4dd5893bba709bff6dc1ece388c561e1ed5,0x210938550593284a984457082a220ca002159526023c0223a02100100d271046aa46f2022bb0201ea5730921b3008e848a002106a7520082d20653c8040064810364a00030c5086c0c2084761035a077101508a009ba22e00b822088521e1c51),(0x77dad76bd4ced656e7ec247a694c9eb5b66dc4de71aac18acebb177a9bac7a62d6f3e3996dd9d62d6ecf7b18557229a30b5ebb1ef46b568a8f3400a7c2d3365caade63d0f2234a24623735bcfaee29c0664eddfc63b2a86915f817ca03dc41fa,0x88252894b2b3256598a758928465236453b27d28c68c4c28a24dcc0d24d500d4a845700845b04bd175706d345a20a0a24d641d897dd822a1d52444cad2629c8e732b305273362844202335b73c8d8150424e93e44a78286995ec17c803dc01f2),(0,0),(0,0),(0,0)]
def g63columns : IndexTree ColumnInfo := (.leaf [(32,0,31,0,7)])
def g63autos : Array (List Nat) := #[[],[50,65]]
def g63levels : Nat → Packing
  | _ => emptyPacking
def g63index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g63 : Forest := ⟨63,7,fun j => g63samples[j]?.getD (0,0),g63columns,g63autos,g63levels,g63index⟩
def g111d6 (i : Nat) : Nat := 0x120ff
def g111l6 : Packing := (1,0,2,0,1,0,0,g111d6)
def g111samples : Array (Bits × Bits) := #[(0xeafcc7b96fc59ffd26c5e2bb3d7bd378fb35ff5dcb26f92afa5f57eff59a73b7aaa379b2fc8d7a99e2ef9efcf4defd4efabc9c89733cebade5579ad5abbcd64d8557ad3d63bd1c6a75510ce3b9bf05e462ee0edf6dfb2914efc74c7d31727465,0x4d00310a2003881269402d0c00406ccc142a8012908082d00025ac006a88036948003229000032d4001bf20024ec2018680000aaf2500325400423a6f02003840040a8016ea8106822700071012c01d500600ad401ea0010f407087831504444),(0xf771ad34ff2bcf4fbd7f5f5de52efaeb7ebbabfffefbf2eab7c7cf56f8ecea565ddfabcf87cb61db9d6ef4aecff7cebd76fe679cfb9935e6adabc77cdcdb677ed3da5e4f56b4cbe39cfd7aed1f519a6b999796b48a51f4f7b8ad91a66cc6d9cb,0x1204940050200482000010001c10308054448009004424020800871400ac0690000402004e0508404004081210450414000904018220d090010808000a44280600460810104d92040818880c1010088d8400200a10a1400808810604821909),(0xf5be76df5e79b8b5d13f5f6e3ecd176fbeee538a7cfb9f7f6b7fad9b13bb7fed97560ecd71f29f3f1e3ef959a338e3a9e32bd5e7cfc7b51df73d7e9e165479b3baa9a0d59e62e11eead3ad5c624777de8699f96d3766d64d1f3fa2ca8f3d2e52,0x8e4d19200884440101e4a802e100a0c04000830eb000289800c49240c1c411082c325a6812b0485430294040c52402008322a4b0e00c0021216842103a050a9080848145264020288841a770220547500211500d95204c05521120880b352452),(0xde2ebbc73c1cf83c4cedbed77297d7f5b666582db23d5c5d7bf4a54b37a75f4992f88d683d388ea5bafb57791a5deb9b257390777cf70e9d329773c24416edd93fe3d2909bc3b81d7e62dd94d70a759eb42b6b51587d63da2e7eea6ce78912bc,0x10b22099c5638280b403142808691e02bd9d04d1097a9640ce2041351e20e64283892100494815238b12089820999d9858901b4e1903515e001721098578a5416f515492d981d895722018845902b08a5c4a2a2248dd03d08c66ca64e48812ac),(0,0),(0x4a99db5e74fdf3bbfb83b4b12e735e58f515867b75942dba656f9eeac55739b971685432ece5b39368c30fbbb9f895ca9efa5eceda2fea7be4766f052ba5def635ccf928215f7640050f6846acafb2ca6efbba0bffbfdb9043d87d111c3c3ebd,0x12d68401de50564414b80023f49c0203c0413d800068400bbb08034f0177ac0427f40400f6de0023bcc009fc1201950403ff4900082ea08a2fc908010c8a4053de0011e801464d050407f806ac13f8026d9b800bfa055d40038875010c2c3ab9),(0x107b7e8791b6519a9ebd6f37d374faa298392ebad8b5e4afe6bd267679568b3365bebaabdf6ef4e9035a918e8ca50ef74769b2b74aea726a09a6c5e9463715fb76745a9b1b6212a1b9add6dec52a9ba55b57e399ab660ca6d0f217384af881fe,0xadc48a6a24248ac9294916cc74a18dce4988890976a839d0a90054480a8f001149b409fd5690d8d50882129489ae3083c83b5253565cd02541ca4550f495b985581508b28aaa022919a1e755a00eaaa54243a315f06a0c87d4f216384a7880f6),(0,0),(0,0)]
def g111columns : IndexTree ColumnInfo := (.leaf [(4,8,99,0,4),(1,32,78,0,4),(64,0,47,0,5)])
def g111autos : Array (List Nat) := #[[],[83,32]]
def g111levels : Nat → Packing
  | 6 => g111l6
  | _ => emptyPacking
def g111index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | _ => fun _ => none
def g111 : Forest := ⟨111,6,fun j => g111samples[j]?.getD (0,0),g111columns,g111autos,g111levels,g111index⟩
def g119samples : Array (Bits × Bits) := #[(0xfab75f3dfbfa3756f92d9ff7baf5ff7dbfebb9b33bef7dcdf77fbffe7bbbf75546cedccfd6f7eb762bef3ffdd2ede7abbef7e4e4b775eb9be6ab6f4d5fde77f2b955ece57b3feb97c6d99b5cdd2fdd2ea315de5f3efbf8d44ddcaa7566eda9cd,0x20100000802449000a820000c1900042800052080010000098c000620802429000050a2000012e00000be20013404000082000047420011240000c8b8000110080002480036500158018000c4009400c9000c0062803a0400e00885042a10888),(0xaf7efcd6de9febfb57d6f5ddedde36f3db7fffeed79fdbfafcf255738c743cbbbff3e3b86b8f9fb9f5bdf54fbff79bd74f5afb3f7fba34f5bf5f9afae879ab5feefe93fa9ee6566f7bbee6bf67d426d75cfb2bace9344fabf72bd58e999b76b3,0x9300010000091004000400382060802420900110020801010208161810541520000000800198110400c004084880812115000049028020c0800220200009220a01801050108206a8408406120184808104430800802442850101410609083421),(0xd3aee9d1a16b8afb579b1b1a2ede96c634714fced4ed35afb8d86696aabedb2eada373270f48f3a9b93de8a90d87d8f6684756adef8eb40bf672fc78b9342c9c7aaa652b2aec9422dd38b32b2a5255bdcc3d35b2da5f372953f3c4ba3a70d996,0x2c07b23e74020fd2aa41748155856818d263d681015680dac92709c7448b08586eaf3a512642c64b613a9091954b38c222671d26711d023332d48951dd0691952839212f8b6888039910b9ac2a42653c283c65315b1b95185ae084b83270c996),(0,0),(0x759a506bc07865de6f37bc2fabe39a5e2705b6a3eec6bd3cca572e3ed72f0325f632aa43d8e0e833eaeab6f86ad5fa72dbaf9c83b9e70faa212acf122e177ae733d8fa39a0b0bb12b7915f7134c3b9a9ed98d75362b1d9c725676c3caf04637c,0x16e5f59c6d01a255c44806523c0cddb5529a2196d082e7c24415d298c0f10d071e6090549dc090f8ed501938009f3fb2169588d90b0b506d102e01343cb84ad135f45369a498be0a36011e712702bb816af81651c4b05c0701a6642cad046374),(0x6339c3e76f77dc41ec6c9766b8b0f93592cd6e58a17db2abb9eea5cd269eeae2dc2c1c9ec755bae6a2821f6b678c3538a75edaf56c57e97ff4e8b90d55c4e75ce36b37ac511be4c610c6f229b9ab77956345b3a117ef6f3608dd37697870ba61,0x84ef690f5888a6bc0049f9381c0ba0115db000874a075d2102333605e754184fe100105f739880fb92c019ec481f2d2102dbf2480954a0ad3f922114724920d57f80032e5018c6a22083e62199863ec06b43378157e41d3d00d937293850b261),(0xd5cc96ab2735f4eedbcfece9fd4d847149d75b8aa71ff3959066dc7566c66ecb75975abde9bb8d684d89311f3151135dd1ce4d97acd9737d0b4d97b62b1596cf57b51ab1b6b408593b67d5bb928b32dabad66fc43367241aeaae177095e247ea,0x481560b0cd924918c5323d4303992d88d1232e6a49f254a2454320824e8122936522ef3572424e688310332525616c12e023da92a435d213539c9243b254cc21b63548a8e4258841b361f1c95a017252ba1c47902bc1245a7a8e167094e243ca),(0,0),(0,0)]
def g119columns : IndexTree ColumnInfo := (.leaf [(4,0,115,0,5)])
def g119autos : Array (List Nat) := #[[],[84],[98],[84,98],[101,66,16],[101,100,66,16],[101,84,82,16],[100,82,16]]
def g119levels : Nat → Packing
  | _ => emptyPacking
def g119index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g119 : Forest := ⟨119,5,fun j => g119samples[j]?.getD (0,0),g119columns,g119autos,g119levels,g119index⟩
def key189l7 (i : Nat) : Nat := 0xa81337040d4b600002948880000590cc33d41450272020001b1
def g189d6 (i : Nat) : Nat := 0x82000f487f40bfa03fa00
def g189l6 : Packing := (3,1,3,0,4,4,0,g189d6)
def g189d7 (i : Nat) : Nat := 0x1f5859bf
def g189l7 : Packing := (1,0,3,2,4,0,0,g189d7)
def g189samples : Array (Bits × Bits) := #[(0x76b7b935ad7f6fd4d735f26d2df10ff4361bcad97bdde979efcd6e58b7554d7ea7eff73e73de92e56562d7533a4ef3de34b1f6acf1d6e216666babd43dbaabce3ad8d545ed4e53771cb4e6d84ab365f9722155b0decf672135d0ab0e8aab3265,0x8404642124899480a2a81184400c4494a40542200633c0114901482008a100b4c40690c02a500485280025a8300be5004d078022244028e4a0122910034dd0088624c002500565400b4701a401901a06a801c60d40e430038408b0c08aa0264),(0,0),(0xb725f7b34edfbeffaf8e64c99fca263eeb8ebd6e6efba6759d07fff35f0d57cf0f1af1c8e8596f2d9f9a363b65aade972ff9af593499366f72b4e55d5e6f961954d5fce693a74e66d370dbbd59357a0ab5d8c2e2b4913d9ddc0ac963246654eb,0x2019084c910042485050a84580141012107000421c10cd02a29a004c0424911090cb1414ac1a4012048a60a1130c00921224ba8854044c203120d1318881010110848d88109408245548f0845c253042044cc0e02091152804424943044214c9),(0x6b3b37beb0d3b3db67cafb77eb9e1dd789aebdb18d1db77732f653e35977f97f4dd313687fb67a399a5d29e7c5c2df2ae361e9d1a8a6a7bdf9b41bf76bf3c59c972736ba642a6ec8e10ddd388a5d8a2fef454b2f6c5cd8cb4dafd1a5458caf32,0x84c42401462a8882042c15880121e0040f09501440a3008044047580824b00c92204cb801220a2e8d004050a8c13a8082552010080e322ce0002224042220e86c96110212062d680201609100358082de8010e0a0c4e080169249024018caa32),(0xeed4ecfef66eeb7efebdd9aee7077cf1671b7b7a97dfdfd372d0ed94ede3ade9c50737565e265d36d07689d4ac4faafe5abbfdc5676e89f79f8f9a623b38502f3db98ff0fa982b81b88d0790fae9d8d74f74351d5187af7a955e769667c1914c,0x112b0124099000041080680538580102a03620812918016ca82b084951200b0011391441e40a1406003a00a460640102802906c05910d52121d05c00b8012058249003c452192901d049060038a0e052051c011422a1a0780618649266411108),(0xd9cafe65094bbf5f7264b7bbce3ffbefdc6762cbb35969c8ac2ddbae62ff5a5f3ee2cea13be5ccd265ed5a725a1921f7f9e712e69e98fb2d45e97fd5f2e0abe4f3f7676b375491bf662220c7ec1235aaa52f7b260bfdf8f023b73c589c1c3f19,0x2215018860a440b0408528403b942810a5b0009c1c080302094a000184016510830b02e2ac10b810014a60046c8c012e120b028809b84c0105208c4e88802201101131880274018a550300819c02301e012cc3000b90a8a80382305084143519),(0,0),(0xe9cbc8feffb7f8e7b8d17ff4f26deb6af5fadcfef4fa8da189aed6c66eadfbba567e7aa58acda76b57bfee9d03799233ac5e277f4fab9af55d736c18d65d30adcab7ab9d1b9dcbcc02d24b67373e9182d29baedd99bcc115aa3d04dc337a48be,0x1420360100482d00252a00a2440945244a022b202187302c44004bb2035a00002400090800450025fa000d1a80010240a950404582409154ca522280124a1c0c672a40054909a2500214036203d800a092812c0514244211e81d048c33284826),(0,0)]
def g189columns : IndexTree ColumnInfo := (.fork 4 (.leaf [(1,0,188,0,5),(12,0,177,0,4),(16,0,173,0,5),(17,0,172,0,4)]) (.leaf [(24,0,165,0,4),(33,0,156,0,4),(132,0,57,0,4),(160,0,29,0,4)]))
def g189autos : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32],[82,48],[84,115,82,48],[117,116,115,114,64],[83,114,64],[116,50,80],[117,84,67,50,80],[84,115,66,112],[66,112]]
def g189levels : Nat → Packing
  | 6 => g189l6
  | 7 => g189l7
  | _ => emptyPacking
def g189index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => lookupWord 5 18 5 10 2 4 (key189l7)
  | _ => fun _ => none
def g189 : Forest := ⟨189,7,fun j => g189samples[j]?.getD (0,0),g189columns,g189autos,g189levels,g189index⟩
def g127samples : Array (Bits × Bits) := #[(0x27ec63be833e95d9cd8b1b0f8c7b949b955ab7ff06f2f46fb53d19a8b89e2cf938ea5b637a679113a99b1a558cf5d3757100e2a2d92956b1df648864a3a84cf9f5aafcc4980f547cd2d2abacb351593072ded0ca36876c216b176a15583d3069,0x215000b22a840210400a1040082a19401000220004808d00802008c02014082088420800402688520818425544410445400040805130408104600820a3600c001020e0440008143510802b10a111102142440000168440214816081150281060),(0xd1272c7d4d43f0bd72e56dab39ddfe7c6a407c139e413a8c95b2f6c7134bd9d2e6151acc0f6f6e61aecc859cb80ab9d38d1f9c08bbd08127631b9fb156aefb042a9049abe4f27cdb8815184a3fa2b5dede495570df2830da3c38c46cf1426d13,0x806000d540888802080408280406213088804000000320c048631024209804006241648090164a10080940a08001912a8109004a2408004431a0101080453200880088a80c0004a880100481a02008819080040c10830122428406420422c11),(0x3757a63bdee4ba3fd3e2275cd925bbac4327c3605b6a92ba668b6b375f5956a61c0ee4c8b6382a0c726a8d674c1d24e187c7697b46618e9a3259ec9e635cb1935494676727a9c6a3df6b34450ca72f271676b8367562d5a985429aaa9a64d626,0xe190134200c030558e6885084d0788a40161e860830e0412a109c61098d030850809a9902628890c322a09e446182064058721691005078a1841cc5c6248a09654242521162044855722240404692506023498262462c48981029a8a9a244222),(0x7c12f7ae7cb67a121957d4766ab145360dad0baa714fd5dd4ad95b9245e39e4cff88a61691dd24ee5570ea624367b54a6aea5375c626bc6f4082772e38770d5a1955fa1dcb198b20afa8d659c70c9ab5dbb42b955b55e374e0f839c3068a9694,0x100b203118264280010702e3020864421484020c18c0438c4090018044060d7096401604915660c20151c00201478d0220604290c2020821402022221025140809114a0c4919231288809339110498f1918002911b15216460582041008a9494),(0x5f0ed2cab79191489f9794fa9f865222c0c45f4f23977137ba6ec87e2fb718cbcb3281372d8190b9e5b2713c276012285f3b185c628f375c96ee95cada25845527c7ad5b31bc018c667be7de6cdf9480211b73e5e0fc0e1e03a683a80feb2399,0x4e04900c0410144f3ce0e018c1840020605099a3823d30032c4ce03413c1e08c412481b32c810028f486342022205010179b1c44008d375c030cd5d908008055e282051134c40088667900c444ea04000013f960e0680e1a03a083a80f412309),(0x64ed11ab034e6565aa5f6f0a73fb2abb553e90eaf5f2056f4f2ad1a6a7112f3107edc462d825611a42150349a39be3bcbdfa3bf68749fd950e410251758bd0aaed7e1f93ab81b400f6cd22629068e5bc2da9dbde283bbf115009f3b1a197a662,0x46299909050b25a18c71e62a5095c63ecb8f04a3c26b60b927cda532c109201915ade64b3091412042050108b390e3bab9cb9877060097580a090251508bf2aae7571e1ba185a2088a6c00621068c596ada8d9f5a83bbf101009f3a0a197a602),(0xed72aa63cb994444b8dcf183254b4e7cee24db3ad729ab4a1ba98c700af5e5480459e832e1cc5750368c89edf172492ed4565f186db3259850f427f3943aea1f7b1d745054d56ed5059c9e36e00b68fdae413f628aa9c64ad98b04d0b38dd9ac,0x4400b2628be723745844a119668f0ccc9303b92a933d014173710ec9a0c0658c41596832a4cc13563c0629c5d4a2402c44020f584d31651810e10cda143b2c95631f726414156f15141896b3a1182c75a6e53b222aa1c648d9830490938dd1ac),(0,0),(0,0)]
def g127columns : IndexTree ColumnInfo := (.leaf [(32,0,95,0,8)])
def g127autos : Array (List Nat) := #[[],[101,66,16]]
def g127levels : Nat → Packing
  | _ => emptyPacking
def g127index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g127 : Forest := ⟨127,8,fun j => g127samples[j]?.getD (0,0),g127columns,g127autos,g127levels,g127index⟩
def key191l10 (i : Nat) : Nat := 0xa2d43b28d7001ab368009df79a6668d8a485480048c00a24000002900046192841e000000005078511fa7b8000001d8000000000050332001c2200008044
def key191l9 (i : Nat) : Nat := 0xb5d65558d2140ea31b806b286019a820212fb2e35aa613228a5a077246e6fc20ca1a41bb2d080a9c3e39f318874648000323b01b537426ceae26842215792e4b19e71cc72290229e7cad73d5f333056000d205f83e366a30000000d49821b1f1088000bb771a5c8c0000000000eb0000e0cb6ac6bec3c000c1b800347e18451880000012040006004d1cd8e0000001866e151a0000282800081e2a5e9518b100010bc00000030815564ae0000000000000ba722a1a34000000e6c5a954a6f09e6780014941d61a7112de27d595e7f09e40be3dc9678ab0bf3d70002c438a3dd4912345fe50900b4e481ecbbcceb07786be83e621d46430465b9b583a98309000098f882ae3a444b1d707c001bdad01b2c800179a0001f6d90464c82da1658b094500004b589e042e51604dd58429e06b90ff614389938aaeb6d12bb049522a72f25c09129e0463116174d50c3960b150c0a182d435d81d03dcbc0b346f3525916e494182a5649d22c9002ab560902d0004c5bd2828ce425700001e0842090d9c2ec56f6a2934aac61902201440c3800d7464005040d9808000b00120008008026140608781000c78f2e086830a0c98000580830000a023a002141e004000c001040a00380
def key191l8 (i : Nat) : Nat := 0x18cd14b25011e7225b26001876a3412158c6fc726c2320d6e3243bdd05603f1613ebb0007f7c604089b00125f5892200bf9421800b5e245039f1cf3cb8436d7f2000047800310000002025492575bf0012c00000042000001b8021c00800c01d000c080081
def key191l7 (i : Nat) : Nat := 0x2c
def g191d6 (i : Nat) : Nat := 0x47d6448788a00
def g191l6 : Packing := (1,4,6,0,2,0,0,g191d6)
def g191d7 (i : Nat) : Nat := 0x1021aae2c480c58812165850610304200048200685020d100000000000200100000fce5cec0b2a49f918c877974664f4a45403b36312c2722140f0a0500fd51548d13edd3641903fd51544d03fe92540d02df57305d02ff10305d02df4179dd02bf5819dd02df5819dd029fd819dd02df5155cd019fe885c901fe92440901ff114409019fc8788a009bd849dd039f5819dd02ed6668ce11f56558ce119f47840a11f3a5591200eda668ce00f5a558ce00bb9841ca00fca3388a00fb24484600fd23384600fe22284600
def g191l7 : Packing := (28,3,6,0,2,8,0,g191d7)
def g191d8 (i : Nat) : Nat := 0x850910304081c2440c0e2128f09183458e0d563c424bf1e12406128b1c7846402045834a31022c1244b4112285081c2449f022410c0418818084041a2060210127868c180849614f082043003c28008103c00a001050011a0c10d03085c404064a2030a0610180108a409488504804aab1e40a0610805408d7f063c2499716b62841c098f1800a084818401971629005810a08556544b736241080077f04053c18a8a2824181120efe78c80844603045000e102828008e8b070510443840106263000efe5858a100024042202241d09811e292070e043021810a5c588002801000c0052e2c5001418110006003021810c08516144821810a085042001810afc7897e3c49e14f0a7850604482184f83a8258107f37d67c179c77f77274572070b6f66e16cc6bf6aa69568066b64e63962c61f61a60d5f85e35ce5b95ac59758256d55053b50e4f94d44bf4a247d45843b4264113e43d73ca3b53a039338635934432f3122d52c02b328e27925c24f22a21d1f81db1be1b11a419718217516815b14e13912c11710a0fd0f00e30d60c10b40a709a08d08007305e04903c02f02200d000ffa4c91ffd0548ffe93227ff41513ffa4c81ffd1640ffe83207ff49503ffa2a81ffd0540ffea2a05ff4d502ffae6817fd2340bfe89a05ff40d02ffa2e817fe7740bfe9b203ff51501ffa6a80ffd24407fe91a03ff5cd01ffa0680ffd72407fe81203ff4da00ffa47007fd13803fe89401ff88a00bfceea2dfe774d6febb247f74d923bfcee91dfd7644efebaa27fd45513bfcee89fdd2344efebb207f74d903bfaea81fdd3540eff3ba07f744d03fba4d19fdd168cfee83467f749633fba2b19fdd058cefeb9a05fe40d02fbc66817f41740aff3ba057f5cc02fbc66015fd7100afeba203fd45101f7c8880dfd73407ef19a037f5c901ff20480dfe77407faa2c23fd4d611fea4708ff503847fa81423fd00a11ff209007be44803fc81c01f78ce00ff205007f901803fb08c01fe4da00ff28b007f935803fc92401fe45200ff247007f913803fc89401fe1ca00ff445006de668cfaf2ac67f58ce11f7489007da33803f511401fc84600
def g191l8 : Packing := (100,2,6,5,2,12,0,g191d8)
def g191d9 (i : Nat) : Nat := 0x180327c7c11a70600f8f1304b1c05f0c3c541303017c38f1204e0ef8f13040180df9e0e080325463418a006077cbcf0238c0ef961b3c041381be3e0900df9e30006fcf825f86eb1755933dd9099319085000ff517fd35ff48ffd13ff40ffd02ff00bfd01ff803de33fd847fa00
def g191l9 : Packing := (12,1,6,7,2,9,0,g191d9)
def g191d10 (i : Nat) : Nat := 0x1f3c11ff
def g191l10 : Packing := (1,0,6,4,2,0,0,g191d10)
def g191samples : Array (Bits × Bits) := #[(0x6acfda3c2cb83a92b793db4cbe83faea9cb2634793e21db352fb83fe8df2bc07a86d83614e9e1d6652f73c866931a299021d0d35cea03b8bca899a3ae9b0852968ae39aed598c502d3cc66c95e3918558ba9636cd1546c95b4522b12e41c6251,0x8027018c1220821109402382a0c04040242201142810004800310a01021028020024504420900008134444101889108100844480011218a0808a088000429588a002494484002118004005c4110108908c2000154441190520210a0142200),(0x7913ceb593e8bd03514889e55f4c93639759259376fb3230720c9a865196f27cc74c193b9b758265cc3f7b6a39d891145642471fe1a3e402ed12036d66f3fc532a7d00122732be1cd6f8a0d631223ddb153772d463789a2c383ce02e7842d163,0x88036081c60419a2c82401d04754b2b302101402821d5c654204040641a4c69d42c491108805a675482c4b1a3210132646402113b58224122512010966d1b044833550122312b410427aa086012a6ec1101538c042289a0c282ca02a5842d161),(0x557693cafd0fd9424efb95e75ddf8ed5bd78c8ecb52fa208a8d45cb3574ccaab77d93b1e650b4399e9518160864e914bee471a4d6078d8cd3710b8c5462d299957d5836e24a95a7b253cdb2e6196070b78eaa32a2b4a267149c447650cd138a6,0x10c082401088400012d0c4008000004018ca8080142020182010002082500860100b028600824082a011044180428040210612040030c884904098c2002801191040822880a108c8040449084010010648220108084220210140474504110882),(0x9c642d62a2f2f7ba22bc048df67d49f5212576be5994f8cdc5e270babb8959b792802cb3e87f90d4054ae918d4ab1ce241d9cf541d5d16b72277276810cef58c9e0f2a3137066d66292bcd81a96583d025d9fd03afbb585aa2b81e898b063d44,0x8024093988519a8e002822a41919198600217873085849c0c483198871885081c08060615e498874054ab3104029780240914c50140c132321226228088464808a9608100702c12708ba84812c642a102598ac01a5195852a098180889063544),(0xd23eefb5d75806b89dcda38864b64661c9f5e2babc176a70b2d3a56f26f32e727e31fe7789e6e58a36284c9dbcb30e74d59821a10b67441120e71511dbf31ab50b42210b3baf1a3e4c47734dcff8958cfd1109f7ce27c18a062741ac46d7cd91,0x7413208444084451d48501104604c068b3980408840422121160844600658c78341c18180024668a9220480b8c940760b50821038273441010c51501633a18440140258228a50a1044455344031a81ae1001013e42228188062541a446c1c891),(0x44ee3263ec00331534507b30f50239085a477dc26fc97fafdd3677e1adedabf5a6627a917685fed951e16b05c441608531a6eebab7bf0ffa2c9d6923c000425ae070ded9cbf43ff0702d561449016826463c1cddf881bbc98109fdb0912bda0a,0x5c9601812402000310c10a308504200a188ca4d220b13a418220c4ac1700cc49329049900289169c4a408a09044020043184b638a739649c2011540242004250a0701ac901871eb02048c310010048264632184cec01aac801096da0110b580a),(0,0),(0x3ab08ab4b6d74c50e56bc9651caf5894b179e03465572acbdca5615696769c27053d6dc580568c9318a62a712d4d06df8fcf0933a8a96615b24c8891d85dee28deccf746ecda09546a23c7138dbf2215a9d969340b49504d34d905859a5a4fc,0x8020482e4971b288ed202044508b9ca5050108094844412451461041282e3192c9648008d0242841110660a6538444294c484083188002614b0e00011891a8820d8e45006648e00548a230c32acf32918089829300b41504d204901848a4a474),(0,0)]
def g191columns : IndexTree ColumnInfo := (.fork 19 (.fork 9 (.fork 4 (.leaf [(1,0,190,0,7),(2,0,189,0,8),(3,0,188,0,5),(4,0,187,0,7)]) (.fork 2 (.leaf [(6,0,185,0,5),(8,0,183,0,8)]) (.leaf [(0,8,163,20,6),(10,0,181,0,5),(12,0,179,0,5)]))) (.fork 5 (.fork 2 (.leaf [(4,8,163,16,5),(14,0,177,0,4)]) (.leaf [(16,0,175,0,8),(0,16,166,9,6),(1,16,166,8,5)])) (.fork 2 (.leaf [(19,0,172,0,4),(24,0,167,0,7)]) (.leaf [(16,8,163,4,5),(8,16,166,1,5),(25,0,166,0,4)])))) (.fork 9 (.fork 4 (.leaf [(9,16,166,0,4),(20,8,163,0,4),(32,0,159,0,8),(1,32,30,128,5)]) (.fork 2 (.leaf [(35,0,156,0,4),(40,0,151,0,5)]) (.leaf [(48,0,143,0,5),(56,0,135,0,4),(128,0,63,0,8)]))) (.fork 5 (.fork 2 (.leaf [(130,0,61,0,5),(4,128,27,32,5)]) (.leaf [(136,0,55,0,5),(160,0,31,0,7),(128,32,30,1,5)])) (.fork 2 (.leaf [(32,128,27,4,5),(161,0,30,0,4)]) (.leaf [(129,32,30,0,4),(164,0,27,0,4),(36,128,27,0,4)])))))
def g191autos : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32]]
def g191levels : Nat → Packing
  | 6 => g191l6
  | 7 => g191l7
  | 8 => g191l8
  | 9 => g191l9
  | 10 => g191l10
  | _ => emptyPacking
def g191index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => lookupWord 1 3 0 6 0 2 (key191l7)
  | 8 => lookupWord 17 64 6 11 5 2 (key191l8)
  | 9 => lookupWord 68 242 7 13 7 2 (key191l9)
  | 10 => lookupWord 9 46 4 10 4 2 (key191l10)
  | _ => fun _ => none
def g191 : Forest := ⟨191,10,fun j => g191samples[j]?.getD (0,0),g191columns,g191autos,g191levels,g191index⟩
def g251samples : Array (Bits × Bits) := #[(0x7c5b1073c997e37379da30f398119ee6fb6b9ec3f472bcb960b6e16b764eab308775a6f93b85666e9d3190b2b24d642ca5712b6de7ab3f7906c1699135342a691b3ae0a5aa4ef7bb316cf861cfcc30541d6a6cc4992b1a999615c8e8d911c1e1,0x2118206040004a02130d09680103a002090a061080141a8c00302460220208340600a251588102029c90b010225400202065234404234e080480294178042009180840240246b20a0024c060c50410001a48a084882a181106058840c1114140),(0xcce5a5f376b735aeaefe578ced15d32ecca61663a9af3bd1860bc21b19116b79223f9d41251db7915d2d676e62aaa4f819f9d341f91890478f7c179edecb18b88452ff03ce59b2503e9c1117dab8cd95ebc956b7a216470f30e3a2b3ec2d18bb,0x4842cb022293909020208080c0985104462050200a232050248f580a09002349282c0500277025a04229050a00aa2098018840837118b0c40a78400806c358a084123a0140090810bc8810142aa8e601010152222014470a10a222b02c2818b9),(0,0),(0x615f43b7c5899d56d0ed540d07e5651da134ed341e9bc1f74f237fc0ae8a342e74d0d54381c29b89aafb968c73300f2ad24e70d94c925aaf7c71d97b8e42ee34b1eb0d1c78f57307cdbb8ab0333b96f243ce283ea4988c525a6cf93575cb22d6,0x600508638c1a9f0381c44ce96aa5f40532886e32158a42c5402a7e6c4a89343c9410964685c08b09acb0120c353c06229a6c00c94c92de87444159522882ae0499430c1549527146cd2ac810537252985246622c84980c521a4cf835558922d2),(0x743743261165c64a5893c74b56706899b56f313d76fa70640bd59bea9f4cd6cd40c9796a92725dcea2baccf628444b5fc70e36349d152cf473b98c6d967cf8571ea4949a30a5a9a67c52f2db3fa12e66e966315b35ec80fa603e034c2e56ad7c,0x8e228200012500a04432a202145800c8c044118122412020998581138524c38140cb492802205484420a48e00002411d45001410a1402070b13084088559515204a0a28a24a10ca03050168720812c4621201151314480a8603203082a468c2c),(0xf3d9bb1a8ffcdc97c518eaf4c8cf14e122f0fafd99d5fdca7ef0f64eebb658a39d280ab679b66835384c18039df39cc970c09cab32e75b6d986af50aa1e14f67f56dcf6f41924d79e9e39f3990e7fa0a34138f4a5e417d209f607f101fc4fe09,0x9201861738918010c41062040c8818244620088911c0e1638783100880a45083c120082600262524204640020401ded90000982b30080131d06c4002816148a041658f0100904561e8880e0910f0e60220020e2216414120916065101cc4aa09),(0x8c34b489b6743f0cbbb4f14fa7d16d9fa49b993f9ba2b3789eb911d5e1cd7a6f64e2a177140a8013c504eb6dd8b5e7f7e94f5a351463882a81261e97691b96dcefd6ddbc37c1e3432aa0876640524995f6a595fd43d7d81429dbe94302afe942,0x269c30c1984c0e0408d2577d35632830a8c6a4165540daa693102041644d9ca647426045188a80110514e824d9155760ee46136c04410a2a918614976910825e2b85c52c35a0b36b4200852245520814f6b484dd43c398142959c9430287e142),(0x1bb2ab4aa0e85ba9e596de5ec3ce129b01134cce9757f2d674620576a8bd96bf3a893c9457f0a28da9ccac591d7731877093a6c205d64d4c2bcaa6363cd0b55e770f7a466dfb2a9c82572d4ce3aa90cf64d9c30549ce2fe50b809671629a567c,0xd9639e04222012901869c59f133e18908110146a61f169c201c69140019863c2e851098d7d900098988b54119762026501322c440c64c4e0e9086343c860556368a70222d632a1a145321c6e30c00cc44fdf181498e2ec50a809261621a5474),(0,0)]
def g251columns : IndexTree ColumnInfo := (.leaf [(8,0,243,0,7)])
def g251autos : Array (List Nat) := #[[],[84,115],[99,65],[118,84,115,65],[118,81],[118,84,99,81]]
def g251levels : Nat → Packing
  | _ => emptyPacking
def g251index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g251 : Forest := ⟨251,7,fun j => g251samples[j]?.getD (0,0),g251columns,g251autos,g251levels,g251index⟩
def g255samples : Array (Bits × Bits) := #[(0x9b665c544a8481c32c829a3849d25a0c2e734bceaece0410b1910c9246b692285657c973ca335d593cb00f0546b90059eb43e97a932728851785431870f031165ac8b80393ba6e576270cc58c906b870841734e15dc89803598ab05c2460a6b1,0x104454110880808228020a2041d8002c08600a02808c02009111060244ac12008614a1024802115108904700443200508241c8821224200116051018407029164080a01212302c0942400010c90428108414142154888803090a9048202086a0),(0xf315668af28fdb1ca228365b7ccc05a0011317731e21482f697635c521d4e57b4580944cacd08190116899ef79421d834fcee4e488905930903982805fb1c61927af17aaf49049a676974192f0d0160363a1bd03830701b0dc1f8281c2dc6123,0x83112a82400c43108201140b24040542001210600e014836084820c40800442b4181104024900000902098cc210099010006246088901220003082011981800902040620cc814002101041843090160043212902810201b054050081825c2101),(0x380526282fa13ac851f4c9c505254980d6e8ec3804b3594a769d93b950ebc251b0d8e2a15610b8154799066089743516386914b45de9a6e1e91c2d64aa4bec2945782990b2d68e61aa4d3cd1b24a6ab680984b4c1298da14a63264e421a50a46,0x184000082381184051a442400021c800c760240c008201086414493150c8805030586481420228050588002082640402084818905528808149002d00020c144045280184104604602a043c40824a60b20098024012185a048212646400810a02),(0x96903da21572f2b1f1c959078994a771bc47364121282ac5966e24786e0f6b8886ae49c27124b27b7242ff2e0094e0b4b1b582696d3c94568c371a6b03b30075a8d6353ad9672c0089eb12ba6325f80dd24d451b8459a7c113618d0b812f118c,0x86100cb01034a2a12848198388d4226018030240202c8a411a0a044824066a838a240842212092185a40cf0a0080e094a530c6680a1400448645526011312024a0c7343889210800016b021a61259805924545098441a1c11120810b812e1184),(0xca830c6ee5a1c1ac77b2c4bb013b84b271c7189edce77b42164b82b2ec44ccc2202552493f52e619512b4f09e2177ba801c291327039cbf4fba1fd7ca29d36ceca40c4508827295a1b45be11b7c00687be220f65622167c80c13fe90c415919,0x1282044674a181cc515204830038803270c71014e5265b22464b9241a4004482002443590d10ca0850630203a411b2a000c201185038c3861ba0d078200d6480c204804048212d4a89449e11258006869a220d60222163c80c12ea00c414819),(0xadcb89db333a54791fc5b16de6a74b1fbdaa5224c4caa060c8434905e130b3e50875189fa3aee40ebf67487ce98db2673644923b555505294552488c144494c2312ef3656d2d51ee39b1b44e04f3d3ec4d148000ab72771f011403179f478e82,0xa991884a13221d3803c5e045a0014312e78660240442614040424905201081f109410899826ca6043646807ca808b20b342020284941850001124c8410049440302c118d6904416438b533460072d3ec490080008b50771c0014031517470802),(0xccf1d170b069949f14600d7679a83ea985e068495997ad010287ff4ea745b576050c4fa9e8e0fabd2497448bd27a5aa8acea4ac0268e4d44dc2df9de452a225ad1457b3d721818b9bf9e05034d50ecb938aed67098a522a72856072e55b8d214,0xce85130b040942f1560095449a91aad8dc0e80b5196a18140955b282345b194266c47298868eeb9221d4601c27a00e8acf04a8036004c04cc8c58ecc43a23d68161791d311c0cb9abcc24434d40e8b9388ed67018a522072852072e55a0d214),(0x442aa5b9d884c622461c21eaaaf556fac8da8923687abbfb99c9c28096422e0eb83cb34c1d8918aec8c55d99f53bc2670104934ee2f27258616b2c55a56fa8970e02486406e9b92b5242282d15890d903f02672424a3e96d3ce1d022fa0aa8e8,0x460a679588446000a40a01aa08c414e80818810338389a92898982c08602320ec02091061180118a88016c815113416481048146a2821250206d8051a4632a958802cc600689381b004a400915810c003602652424a380613ce19002e808a0e8),(0,0)]
def g255columns : IndexTree ColumnInfo := (.leaf [(64,0,191,0,11)])
def g255autos : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32]]
def g255levels : Nat → Packing
  | _ => emptyPacking
def g255index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g255 : Forest := ⟨255,11,fun j => g255samples[j]?.getD (0,0),g255columns,g255autos,g255levels,g255index⟩
def key383l12 (i : Nat) : Nat := 0xf8400002630000023000000000000000000b83d5688000000000341000030000000000814000015d0000000210344000018d003b10000000000e080000000e70005c3803500091000000000008
def key383l11 (i : Nat) : Nat := 0x404c001fd7a0dd080d1200990f207c017043e0ac430a491c9aec7438f32422a414035a0e000e6f384202824e3e5491f317a0090ee161490000d0e481ce32000c4b9104c1860ad6100030920000000003c06000000722ae38f1200000035c780290bd08d23d219503209024ec0512fd44dc0985ef07266b48508d728f004824e9809324688ad260642ee33843c9e425582082c2260138002f8f81ac0c0002216a57414583e222000012800202204f00400024f34c01300e78608380c041012080080846040
def key383l10 (i : Nat) : Nat := 0x8a7028008f8208641c25de616202731427f0aa3ea6a9bc18603a40bac46606be46000184a7c7d25a0000000b98af69a264a6b01ac3b3a21709000001146294f5b28f5117b2b2368000000119a0000000503689a2858e10b056a96282c8039064ce4000005a1824c4b68b4a1ca0160003a96c1c5108908a005faaaa16a13000042ba8544116a040004b6aa18802880c23178071841517e2559911705a04117c6495c00000000085d314e242a96a0880000a01fc56687256502c84968668866a1180000003d68390f815a1fa922000012b8020000c2a6caf0234475dcf201fa032887c28e092c47a60725df80221bc02a000007a61e192100d1c1f61f683d817642e40874ab202e012c0cd05141d60b104cb094626909c0000000c0e573a858d7326a6285e00010ac0007468e22e50bc16f60921b5c8f41249001273800322800110cb04e0005728622182280ff076809bc29a93800081a596455d1053c0607cc3a5870000108081400524002801c04219100c0821c60cc13c0c2030a201001e00285000001f020030024000800c08280
def key383l9 (i : Nat) : Nat := 0x6977b1303806491384c288005f480044300b4273a470aef249bb09d0238c000000000000000603688ce51876813ab9e6c881d7b37687df408050502a181c84000606800000000000000424bbbaa9612800409100800346576b8a520800702905aa985610b9a10486080010008502020c0020a18085
def g383d8 (i : Nat) : Nat := 0x7c610014028800000000000000302080140040000000a09b827d78736e69645f5a55504b4637322d1e19140f0a0500cef45d94a2103afbaa93760801f7445d0744d03aaf69017618038fb68a9960d01ad76949760c01af34a89760c01af64289760c01adb6943760801aeb69037608018fb6683760801af94683760801afa42837608018ef690988ce009fcaa9190de009fa68a9944e009deaa99504e009deaa99520e009ee690988ce00be6690178ce00be6690918ce00be6690988ce00bf84a83784600bbc6989384600f749de3384600
def g383l8 : Packing := (25,4,6,0,3,8,0,g383d8)
def g383d9 (i : Nat) : Nat := 0x2dd0028c0601f18c02041010022160ac183c0004580028bb3c71c058816e807460680741c30700441602883bd0180c08009e92a09189248391a905315048c4c0a178c440a1c344e20480c5e3ec8c4124f1f67a1c70097c7d918050801b86cae3f18d8123489e81e3f187030392c68303e84a0683078305e30e0607e38f83c60f060a511f174250341f8c5e031010ee21078c3c161c0cee22050c28801004142c00504800c7c3000f402160a08ae97100120112003c70a082689408970b120030209083000c003000838e14007c610001c70838e1020020212004000023e3ec8cb8e14489e2f1a14a23e23d15c47a2b88f457115cca2f195c5e3ecf438e4f9debbcbf80ec1d2799709dd3b93626add2d9db38e63c8786afd5e3b876b2cad6ca75446864ec9992b24646c8990d60abf57bcf1dd3b7e6bccf98f3075e0b6565abd55ea85452734dc95d24a3b45a858ff9f13c6754e39b9356698cc18a2f85dcb916d2be568a61472724d08e918226438650b3138214370570800a4005ff65c1840f7fa2f442077fd9720d01dfe9bd1080dffa6537006ffd329bc017fd9704e009fe44a2e81ddf6541840f7ea300c2077bd94a2103ddeca51081cff6468840ffb20e89a07fd41844d03def4422681cff6241700f5fa2ec3007afc1761803d7e8cb0c01cff65d8100f7ea2ec08073fe99604039fe44a6e80cff65d834067fd32c1a03bdd8320d019fec4a0680cff64e884067fb121b8033fd9760c01dee9bb0600ef70dd830067fd32c1803bdd9760c01dee4bb0600ef7a65830077da6ec1003bec37608019fe44a6f005ef65037802fda521bc017f5190de00bfc8486f004ff22513802efb2a09c017f90904e00bfccba07007f644d03803fb20719c013fc988ce00bfcc9a03007fc406118027f93108c017f8894de00bfd4ca6f005fe46437802ff32e89c01ff11744e00bfc44a27005fea6513802ff32e09c017f99720e00fec89907005fe64483803fb26f19c01fd9138ce00bfc4c467007f645e33803fb02f19c01fd8918ce00fec4c467005fe64c81803fb46640c01ff11384600fed19c23005fe26211803fe26f08c01ff03784600ff849c23007fc8ce11803fe13108c013bd94a210397f4cb0c01cf7a6583006f73281bc017e9290de00bf88c86f005de65413802ef32a41c01fd23384600
def g383l9 : Packing := (91,3,6,5,3,11,0,g383d9)
def g383d10 (i : Nat) : Nat := 0xb1c029771ece80316e3a8b78f40771ca00d1002da03a69a8d16d01d28d4d3292968b98ba7f8c288f4271a30301042b0c2ce3d9d0c753d16f1a58de8639cbb8c715c8d44b554a1a9a3e0a89a12200921586544f91de7c3c6840c59058fc73e70a427a578082339c40459aa8af185209a7d34148d4cb55354aae60605689f215010071ece816c5e382c02c0800b78f67401b1c150a01655c62e06083462ae3d9d02d06c70541505820071ece801e380c14030a8b4a07c8d48497c63f8e66a4b4202e31fc73a14025b571ece863a00201e95c8d50005c7b3a084978e980d957652718d2b8da90a038f655cc3ed026a4b80d9d0683120b8d0ca07c4503e24b0080e3d9d0c73a100400171ece863a2041f8deb9e05d31c9dc29ad59e194d8397a571169d5a94d53c132d2591c5050edce08cf4b60acc9f89047f075c62859452044c3f83242b025c208114003ff45d03ffd1840fff06103ffe8840fff44d03ffd1700fff05c03ffd37407ff60d01ffc83407ff40d01ffe88407ff4dc01ffc37007ff4de00ffc37803ff44e00ffc13803ff8ce00ffe11802ffa2103fdd1340eff60403bfd83406ffa2101bfd83007fe40e00ff901803fe4de00ff837803fe44e00ff813803fe20e00ffa33803fe20600ffa11802bf61803bdd83006fb60801fda33803fc84600
def g383l10 : Packing := (41,2,6,7,3,12,0,g383d10)
def g383d11 (i : Nat) : Nat := 0x540b1d9a02e3804632e686a85e3b342382008507c4a8582c71cf98063b342397069da95ca003fe81ffc03ffa03ff007ff007fa00
def g383l11 : Packing := (6,1,6,6,3,8,0,g383d11)
def g383d12 (i : Nat) : Nat := 0x11b280e4ff
def g383l12 : Packing := (1,0,6,3,3,0,0,g383d12)
def g383samples : Array (Bits × Bits) := #[(0x22c0d3a3723e453b61b292904161c19166ba4156452239cb2ce776d1285888036922ca069735ba1c39466bb49cb80c880d6801ee650cd2ea8938a452f08d3169a1612a59384753bad95626662c63076161205bac29b905015369815a61884cb1,0x22a042a308281022412222104041018102a0455c0820218028210490004898014122a802062510400900403480940c80084001804506910881200012c0203148e041211030641239500420000c630440212052a0291101014268811220880c80),(0x3e4782180591e1e8ca415c93fb0e30440ddb7b080a80044a5e58703417b0ed0da2975b6df4e0151155ba1024096257dc7280e61c3739c9924483ab0a0d0a407f268250f5cf15b48886f76ba0ccf46838068d8de07060e07838bc1a040b61c283,0x9028018810161088ac0504223081040850928000290004c425070241b00400822080144b0c0241004a20000482053184202c40808184882448102000d0800b3040a404084018c8080110220c214483800898940502040781814120409604201),(0xc3b0d0243e2c92704a6d0bb89a642e3e324709614c855ba1b03c2574c53f0c84bca3b709607618aaaaca1686a79e094292d1a5b2e1a729d1ef4c761d2455891cd68664af136132ce19aaa19e6c55a2caed1460758145348a6cc923aa16a49516,0xc22070243c088a32102908b09820ae3610c20125cc051d809026055084360c62d8a3320940364922a8484682858e00c384d420b061233141a94434152055010c599024a50348105611a2a11e2441a2c2e41460350145348264c921aa12049512),(0x4138264952b1d12493a4452d72585b389605825093cff11edb60090262cf75191c382db2876b8a708e04945dba40fc5c0117030382d504a579e551698e39d387601c521a9a75d96750089c8958b895e01b82b803f01d0be08606741604bc230c,0x1080c0b03b031008084040c42504188060180103100c00a0a40008040890111041009902b010250040410442a404c140103030210c08ca050a00048c0a8c022200c1018d83149210000148108b815200b021800b00809600202141404b82204),(0x7a0c641d50044e150338db871c0d9c6d8b49b017941b1c71c485efc79a14e6ae159b09d8c200cd085276a758cd18f3623c4db7d00870524c281de7f5fe3e2adc1756b294808a0882ea6a1f2df107bc01d0df010f4d40469e2105ef94c107b239,0xd004201450464809021899a3188eb82288483003841b1c31c500f247991664ae92090048c000c90e723223084509b040f48cd45008304046281cf3843e140e8407928284000804822b6a8b24f004a801d0dd010f4440469e21056a80c1079039),(0xcc62da0a5fa8f5e2c996caf343c42faac6de9a345ff56a94813a6425060416282f4d23c281526277465dd835f65817a533b901ad51024edaaa84a94a69219208d911c25be8aad34a7f39eda22807bafd8e8540012ec5ecf42900c6dcd341c02,0x8452d0021128d5c8c9144a91d1c007ab845a00141d69e1982122246c02041428290423d28902225305595421e41c17a5023985a908040a15a0c4800269208200d9018058b1aa90485c38f99a2803baf58c8040010ec1ece00900c4d4d341002),(0xdaef1c77688221978d1e0c4ad4cf460c43747468370c9781a044ccfb808507cfc7550e6f05834be93d3c1e4e94918217a4e0da637baa95002472c84f89f63e421033ad28de7ab208228bfb0281a229d272553696158289b300da2c9976c32464,0x92e959624882001701040c005417432c02544069252c9701a0048cc280a00e56d4150e31071309c931151f4c9213080304e00a4233c09500a002c04d90b29c403071012c5a3a310c128ab91220a221c27244349605808983008a2c9966812464),(0,0),(0x941a1aee99450a81362f36506691ad42486aa7b56b55a36c2710c35afdccd2f0604110c2892f54d343a9228b60c516b3ea6e18394813263b179331842a516d8adc29c7c000c846f164b52014130d4016a078833106127956c94690a3b81ad1d8,0x4120210904c02803268a2402080b401402a07040a01006405204110294490a020401002d0205402c22800a1400c2280a20c04a14813021a0411310009012188c000460020c0069060300020050540108030832102126010c94480229002c198)]
def g383columns : IndexTree ColumnInfo := (.fork 29 (.fork 14 (.fork 7 (.fork 3 (.leaf [(1,0,382,0,9),(0,1,332,50,7),(2,0,381,0,9)]) (.leaf [(0,2,312,69,7),(3,0,380,0,6),(2,1,332,48,6),(1,2,312,68,6)])) (.fork 3 (.leaf [(4,0,379,0,11),(5,0,378,0,7),(7,0,376,0,5)]) (.leaf [(5,2,312,64,5),(8,0,375,0,9),(0,8,99,276,7),(12,0,371,0,8)]))) (.fork 7 (.fork 3 (.leaf [(13,0,354,0,4),(14,0,369,0,5),(16,0,367,0,11)]) (.leaf [(17,0,366,0,8),(18,0,365,0,7),(19,0,364,0,5),(18,1,332,32,5)])) (.fork 4 (.leaf [(24,0,359,0,8),(25,0,358,0,5),(28,0,355,0,7),(20,8,99,256,5)]) (.leaf [(32,0,351,0,11),(33,0,350,0,8),(32,1,332,18,6),(35,0,348,0,5)])))) (.fork 15 (.fork 7 (.fork 3 (.leaf [(34,1,332,16,5),(44,0,339,0,5),(49,0,334,0,7)]) (.leaf [(48,1,332,2,5),(33,16,326,8,5),(56,0,327,0,5),(64,0,319,0,11)])) (.fork 4 (.leaf [(65,0,318,0,7),(66,0,317,0,8),(67,0,316,0,5),(65,2,312,4,5)]) (.leaf [(70,0,313,0,7),(34,64,29,256,5),(256,0,127,0,9),(0,256,23,104,7)]))) (.fork 7 (.fork 3 (.leaf [(264,0,119,0,6),(256,8,99,20,6),(8,256,23,96,6)]) (.leaf [(268,0,115,0,5),(260,8,99,16,5),(280,0,103,0,5),(272,8,99,4,5)])) (.fork 4 (.leaf [(288,0,95,0,8),(289,0,94,0,5),(40,256,23,64,5),(304,0,79,0,5)]) (.leaf [(320,0,63,0,8),(322,0,61,0,5),(258,64,61,0,5),(352,0,31,0,7)])))))
def g383autos : Array (List Nat) := #[[],[84,131,98],[101,66,16],[100,131,82,16],[82,129,48],[101,100,131,98,129,48],[100,49,128],[101,84,131,66,49,128]]
def g383levels : Nat → Packing
  | 8 => g383l8
  | 9 => g383l9
  | 10 => g383l10
  | 11 => g383l11
  | 12 => g383l12
  | _ => emptyPacking
def g383index : Nat → Nat → Option (Nat × Nat)
  | 8 => fun _ => none
  | 9 => lookupWord 17 68 7 12 5 3 (key383l9)
  | 10 => lookupWord 57 200 7 14 7 3 (key383l10)
  | 11 => lookupWord 30 108 6 13 6 3 (key383l11)
  | 12 => lookupWord 6 61 1 10 3 3 (key383l12)
  | _ => fun _ => none
def g383 : Forest := ⟨383,12,fun j => g383samples[j]?.getD (0,0),g383columns,g383autos,g383levels,g383index⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low3 : Lower (vars 3) (graphGoal 3) 1 := size_of (hints:=1) (by decide +kernel)
def maps3 : List (Nat × List Nat) := []
def known3 := extendKnown [] 1 maps3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid3 : Known known3 := extendKnown_ok baseKnown low3 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low7 : Lower (vars 7) (graphGoal 7) 2 := size_of (hints:=257) (by decide +kernel)
def maps7 : List (Nat × List Nat) := []
def known7 := extendKnown known3 2 maps7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid7 : Known known7 := extendKnown_ok valid3 low7 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom15 : graphValid g15 (boundsBefore known7) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s15_3_0 : block g15 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl15_3 : block g15 3 0 1 = true := s15_3_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables15 : checkedTables g15 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g15 0 0 0 = true)
  · exact (rfl : block g15 1 0 0 = true)
  · exact (rfl : block g15 2 0 0 = true)
  · exact bl15_3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low15 : Lower (vars 15) (graphGoal 15) 4 :=
  lower_forest (g:=g15) (i:=0) (hints:=8449) (before_sound known7 valid7) geom15 tables15 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps15 : List (Nat × List Nat) := [(15,[]),(23,[32,67]),(27,[16,66]),(29,[65,50]),(30,[64,65,66,67]),(39,[32,67,84]),(57,[32,65,82,83]),(78,[64,33,67,84,101]),(99,[16,33,66,83,100,101]),(135,[67,84,101,118]),(156,[64,81,83,101,118]),(163,[16,66,83,100,101,118]),(165,[65,50,83,100,101,118]),(166,[64,65,66,83,100,118]),(172,[64,81,82,67,100,101,118]),(177,[16,65,82,99,118]),(198,[64,83,100,117]),(281,[65,82,83,101,118,135]),(305,[16,65,82,99,118,135]),(312,[64,81,98,83,118,135]),(326,[64,66,83,100,117,135]),(330,[64,65,82,100,117,135]),(332,[64,81,66,83,100,117,118,135]),(344,[64,81,98,83,117,118,135]),(353,[65,82,99,116,117,135]),(354,[64,65,82,99,116,101,118,135]),(396,[64,81,82,83,100,117,134,135]),(424,[64,81,98,67,116,101,134]),(480,[64,81,98,115,132,101,134])]
def known15 := extendKnown known7 4 maps15
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid15 : Known known15 := extendKnown_ok valid7 low15 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low45 : Lower (vars 45) (graphGoal 45) 3 := size_of (hints:=8965) (by decide +kernel)
def maps45 : List (Nat × List Nat) := []
def known45 := extendKnown known15 3 maps45
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid45 : Known known45 := extendKnown_ok valid15 low45 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low51 : Lower (vars 51) (graphGoal 51) 3 := size_of (hints:=1) (by decide +kernel)
def maps51 : List (Nat × List Nat) := []
def known51 := extendKnown known45 3 maps51
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid51 : Known known51 := extendKnown_ok valid45 low51 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom31 : graphValid g31 (boundsBefore known51) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_5_0 : block g31 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_5_1 : block g31 5 1 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl31_5 : block g31 5 0 3 = true := (@block_merge g31 5 0 1 2 s31_5_0 s31_5_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_6_0 : block g31 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl31_6 : block g31 6 0 1 = true := s31_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables31 : checkedTables g31 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g31 0 0 0 = true)
  · exact (rfl : block g31 1 0 0 = true)
  · exact (rfl : block g31 2 0 0 = true)
  · exact (rfl : block g31 3 0 0 = true)
  · exact (rfl : block g31 4 0 0 = true)
  · exact bl31_5
  · exact bl31_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low31 : Lower (vars 31) (graphGoal 31) 7 :=
  lower_forest (g:=g31) (i:=0) (hints:=8449) (before_sound known51 valid51) geom31 tables31 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps31 : List (Nat × List Nat) := [(31,[]),(167,[83,100,101,118]),(313,[81,98,99,84,118,135]),(334,[80,81,82,83,100,117,135]),(355,[82,99,116,117,118,135]),(428,[80,97,82,99,116,101,134])]
def known31 := extendKnown known51 7 maps31
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid31 : Known known31 := extendKnown_ok valid51 low31 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low47 : Lower (vars 47) (graphGoal 47) 5 :=
  lower_discard (g:=g47) (ci:=(8,0,39,0,4)) (hints:=8449) (before_sound known31 valid31) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps47 : List (Nat × List Nat) := [(47,[]),(61,[65,50]),(94,[64,65,66,67,101]),(151,[67,84,101,118]),(173,[48,65,50,83,100,118]),(181,[65,50,99,84,118]),(185,[16,65,98,83,101,118]),(188,[64,97,98,67,84,118]),(227,[16,66,99,116,117,118]),(230,[64,65,66,99,116,101]),(301,[48,65,82,100,118,135]),(331,[80,81,66,100,117,118,135]),(339,[66,99,84,117,118,135]),(345,[80,65,98,67,84,117,118,135]),(346,[64,49,98,67,84,117,135]),(358,[64,65,82,99,116,101,118,135]),(369,[65,98,115,84,118,135]),(422,[64,81,66,99,116,117,134]),(440,[64,97,114,67,84,117,134]),(454,[64,66,99,116,133,118,135]),(460,[64,97,66,99,116,133,135]),(482,[64,49,98,115,132,133,135]),(484,[64,97,82,115,132,101,118,135])]
def known47 := extendKnown known31 5 maps47
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid47 : Known known47 := extendKnown_ok valid31 low47 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low55 : Lower (vars 55) (graphGoal 55) 5 :=
  lower_discard (g:=g55) (ci:=(16,0,39,0,4)) (hints:=257) (before_sound known47 valid47) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps55 : List (Nat × List Nat) := [(55,[]),(79,[64,65,66,67,101]),(103,[16,66,100,101]),(115,[50,99]),(143,[32,67,101,118]),(174,[48,65,50,83,100,118]),(179,[65,50,99,84,118]),(206,[48,50,67,100,117]),(286,[48,33,101,118,135]),(316,[48,97,66,84,118,135]),(327,[64,65,82,100,117,135]),(348,[48,97,66,84,117,118,135]),(364,[48,97,99,116,118,135]),(376,[48,97,114,99,116,118,135]),(398,[48,65,50,67,100,117,134]),(433,[16,49,98,115,100,117,134,135])]
def known55 := extendKnown known47 5 maps55
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid55 : Known known55 := extendKnown_ok valid47 low55 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low63 : Lower (vars 63) (graphGoal 63) 8 :=
  lower_discard (g:=g63) (ci:=(32,0,31,0,7)) (hints:=8449) (before_sound known55 valid55) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps63 : List (Nat × List Nat) := [(63,[]),(95,[16,66,101]),(159,[32,67,101,118]),(175,[32,83,100,118]),(183,[99,84,118]),(231,[16,66,99,116,117,118]),(317,[32,97,82,83,100,118,135]),(350,[96,33,99,84,117,135]),(359,[16,82,99,116,118,135]),(366,[96,49,116,118,135]),(371,[98,115,84,135]),(377,[48,97,114,99,116,117,118,135]),(429,[80,97,116,134,135]),(430,[96,81,98,83,116,134]),(441,[16,97,114,116,101,134,135]),(444,[96,113,114,99,84,101,134]),(462,[96,98,67,116,133,135]),(492,[96,113,115,132,133,134])]
def known63 := extendKnown known55 8 maps63
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid63 : Known known63 := extendKnown_ok valid55 low63 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom111 : graphValid g111 (boundsBefore known63) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s111_6_0 : block g111 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl111_6 : block g111 6 0 1 = true := s111_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables111 : checkedTables g111 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g111 0 0 0 = true)
  · exact (rfl : block g111 1 0 0 = true)
  · exact (rfl : block g111 2 0 0 = true)
  · exact (rfl : block g111 3 0 0 = true)
  · exact (rfl : block g111 4 0 0 = true)
  · exact (rfl : block g111 5 0 0 = true)
  · exact bl111_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low111 : Lower (vars 111) (graphGoal 111) 7 :=
  lower_forest (g:=g111) (i:=0) (hints:=16785665) (before_sound known63 valid63) geom111 tables111 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps111 : List (Nat × List Nat) := [(187,[16,97,66,83,100,101,118]),(190,[64,97,98,67,84,118]),(215,[67,84,117]),(222,[64,65,66,67,117,118]),(238,[64,65,66,99,116,101]),(243,[16,66,115,100,101]),(318,[64,81,66,83,100,118,135]),(349,[80,65,98,67,84,117,118,135]),(365,[48,65,82,116,135]),(378,[64,49,114,67,84,101,118,135]),(413,[48,65,50,67,117,134]),(437,[65,50,115,84,134]),(455,[96,98,67,116,133,135]),(476,[64,113,66,115,100,133,118,135]),(490,[64,49,114,99,132,133,118,135]),(497,[65,114,131,84,134,135]),(504,[64,113,130,67,84,133,135])]
def known111 := extendKnown known63 7 maps111
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid111 : Known known111 := extendKnown_ok valid63 low111 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low119 : Lower (vars 119) (graphGoal 119) 6 :=
  lower_discard (g:=g119) (ci:=(4,0,115,0,5)) (hints:=16777473) (before_sound known111 valid111) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps119 : List (Nat × List Nat) := [(119,[]),(207,[64,65,66,67,117,118]),(380,[48,113,66,84,101,135]),(414,[48,65,50,67,117,134])]
def known119 := extendKnown known111 6 maps119
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid119 : Known known119 := extendKnown_ok valid111 low119 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom189 : graphValid g189 (boundsBefore known119) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_6_0 : block g189 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_6_1 : block g189 6 1 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl189_6 : block g189 6 0 3 = true := (@block_merge g189 6 0 1 2 s189_6_0 s189_6_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_7_0 : block g189 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl189_7 : block g189 7 0 1 = true := s189_7_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables189 : checkedTables g189 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g189 0 0 0 = true)
  · exact (rfl : block g189 1 0 0 = true)
  · exact (rfl : block g189 2 0 0 = true)
  · exact (rfl : block g189 3 0 0 = true)
  · exact (rfl : block g189 4 0 0 = true)
  · exact (rfl : block g189 5 0 0 = true)
  · exact bl189_6
  · exact bl189_7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low189 : Lower (vars 189) (graphGoal 189) 8 :=
  lower_forest (g:=g189) (i:=0) (hints:=536879876) (before_sound known119 valid119) geom189 tables189 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps189 : List (Nat × List Nat) := [(189,[]),(347,[65,66,115,84,101,118,135]),(486,[16,66,99,132,133,134,135])]
def known189 := extendKnown known119 8 maps189
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid189 : Known known189 := extendKnown_ok valid119 low189 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low250 : Lower (vars 250) (graphGoal 250) 5 := size_of (hints:=1366507616) (by decide +kernel)
def maps250 : List (Nat × List Nat) := []
def known250 := extendKnown known189 5 maps250
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid250 : Known known250 := extendKnown_ok valid189 low250 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low127 : Lower (vars 127) (graphGoal 127) 9 :=
  lower_discard (g:=g127) (ci:=(32,0,95,0,8)) (hints:=16785665) (before_sound known250 valid250) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps127 : List (Nat × List Nat) := [(127,[]),(223,[64,65,66,67,117,118]),(247,[115,84]),(375,[98,115,84,135]),(381,[48,113,82,135]),(382,[112,49,66,115,84,101,135]),(415,[48,65,50,67,117,134]),(446,[112,81,114,83,100,134,135]),(478,[112,65,114,67,100,133,135]),(493,[80,113,50,132,135]),(499,[65,114,131,84,134,135]),(505,[64,113,130,131,132,133,135]),(508,[112,129,66,115,84])]
def known127 := extendKnown known250 9 maps127
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid127 : Known known127 := extendKnown_ok valid250 low127 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom191 : graphValid g191 (boundsBefore known127) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_6_0 : block g191 6 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_6 : block g191 6 0 1 = true := s191_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_7_0 : block g191 7 0 13=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_7_1 : block g191 7 13 15=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_7 : block g191 7 0 28 = true := (@block_merge g191 7 0 13 15 s191_7_0 s191_7_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_0 : block g191 8 0 7=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_1 : block g191 8 7 61=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_2 : block g191 8 68 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_8 : block g191 8 0 100 = true := (@block_merge g191 8 0 68 32 (@block_merge g191 8 0 7 61 s191_8_0 s191_8_1) s191_8_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_9_0 : block g191 9 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_9_1 : block g191 9 3 9=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_9 : block g191 9 0 12 = true := (@block_merge g191 9 0 3 9 s191_9_0 s191_9_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_10_0 : block g191 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_10 : block g191 10 0 1 = true := s191_10_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables191 : checkedTables g191 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g191 0 0 0 = true)
  · exact (rfl : block g191 1 0 0 = true)
  · exact (rfl : block g191 2 0 0 = true)
  · exact (rfl : block g191 3 0 0 = true)
  · exact (rfl : block g191 4 0 0 = true)
  · exact (rfl : block g191 5 0 0 = true)
  · exact bl191_6
  · exact bl191_7
  · exact bl191_8
  · exact bl191_9
  · exact bl191_10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low191 : Lower (vars 191) (graphGoal 191) 11 :=
  lower_forest (g:=g191) (i:=0) (hints:=536879361) (before_sound known127 valid127) geom191 tables191 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps191 : List (Nat × List Nat) := [(191,[]),(319,[65,50,135]),(351,[64,65,66,67,101,135]),(367,[80,81,66,100,117,118,135]),(379,[81,98,118,135]),(431,[48,65,50,83,100,134,135]),(445,[48,97,82,134]),(487,[16,66,99,132,133,134,135]),(494,[96,65,98,67,132,117,134])]
def known191 := extendKnown known127 11 maps191
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid191 : Known known191 := extendKnown_ok valid127 low191 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low251 : Lower (vars 251) (graphGoal 251) 8 :=
  lower_discard (g:=g251) (ci:=(8,0,243,0,7)) (hints:=1358970881) (before_sound known191 valid191) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps251 : List (Nat × List Nat) := [(251,[]),(254,[32,67,117]),(471,[16,66,67,100,133,134,135]),(501,[16,33,50,131,100,133,118]),(506,[32,49,130,100])]
def known251 := extendKnown known191 8 maps251
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid251 : Known known251 := extendKnown_ok valid191 low251 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low255 : Lower (vars 255) (graphGoal 255) 12 :=
  lower_discard (g:=g255) (ci:=(64,0,191,0,11)) (hints:=553656577) (before_sound known251 valid251) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps255 : List (Nat × List Nat) := [(255,[]),(479,[64,65,66,67,133,134,135]),(503,[16,66,131,100,101,135]),(507,[81,130,118]),(509,[48,129,82]),(510,[128,65,130,67,100,117])]
def known255 := extendKnown known251 12 maps255
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid255 : Known known255 := extendKnown_ok valid251 low255 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom383 : graphValid g383 (boundsBefore known255) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_8_0 : block g383 8 0 23=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_8_1 : block g383 8 23 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_8 : block g383 8 0 25 = true := (@block_merge g383 8 0 23 2 s383_8_0 s383_8_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_0 : block g383 9 0 9=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_1 : block g383 9 9 75=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_2 : block g383 9 84 7=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_9 : block g383 9 0 91 = true := (@block_merge g383 9 0 84 7 (@block_merge g383 9 0 9 75 s383_9_0 s383_9_1) s383_9_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_0 : block g383 10 0 5=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_1 : block g383 10 5 16=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_2 : block g383 10 21 20=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_10 : block g383 10 0 41 = true := (@block_merge g383 10 0 21 20 (@block_merge g383 10 0 5 16 s383_10_0 s383_10_1) s383_10_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_11_0 : block g383 11 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_11_1 : block g383 11 1 5=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_11 : block g383 11 0 6 = true := (@block_merge g383 11 0 1 5 s383_11_0 s383_11_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_12_0 : block g383 12 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_12 : block g383 12 0 1 = true := s383_12_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables383 : checkedTables g383 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g383 0 0 0 = true)
  · exact (rfl : block g383 1 0 0 = true)
  · exact (rfl : block g383 2 0 0 = true)
  · exact (rfl : block g383 3 0 0 = true)
  · exact (rfl : block g383 4 0 0 = true)
  · exact (rfl : block g383 5 0 0 = true)
  · exact (rfl : block g383 6 0 0 = true)
  · exact (rfl : block g383 7 0 0 = true)
  · exact bl383_8
  · exact bl383_9
  · exact bl383_10
  · exact bl383_11
  · exact bl383_12
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low383 : Lower (vars 383) (graphGoal 383) 13 :=
  lower_forest (g:=g383) (i:=0) (hints:=12901687553) (before_sound known255 valid255) geom383 tables383 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps383 : List (Nat × List Nat) := [(383,[]),(447,[65,50,131,84,118,135]),(495,[80,81,82,83,116,133,118])]
def known383 := extendKnown known255 13 maps383
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid383 : Known known383 := extendKnown_ok valid255 low383 (by decide +kernel)
def hashdeadl14 (i : Nat) : Nat := 0x4592c8500000000002800049a6c68a83340e9800000aa00684000000054a001bcc7001e180000682000000000000001d46a1840000003a00000001c
def hashdeadl13 (i : Nat) : Nat := 0x301a0007b2f00e0aa2992094818000e2e0000000269e056438000000000d33e40e4a200074d00000000000003b10001e0240a9bd45d962582900000000000001430001e1400000fc03b84a000614e69108a1108000810000d04c9d0000000408800000160f24180010b9d040003080001e0c000000000001997f401183740ee12000000000080d312c00102c00000000012070000000001d35000308c000a4c0001b30000000cb3800183000070f0000001abcc008002c8cc133000000000000000000000020b000000064ec0a00000f8000cc5000105d8204160001a38001c1c467309c000000a7700000016de30f80000008380b08e000d3001
def hashdeadl12 (i : Nat) : Nat := (if i<1 then 0x7b02c3200425d610a000042a0327300000000106b33757005e04600006037d811679d009461963480703e1077f067f2582384275d80a540a20109b59b4006305d00000000ab6dfb0bf59ec084c806986b30597776440b146b100c50a956520000878e0000747c463e108bc029e7600000395ef090d06800000000f0550000d0b1e4af00000000f324d141840ca4380000000051505017000067300000e779907b0000e77730641201ea62a089a48ff0924111e9a7a041b2a180aee462f29d9b47b01eb0427030e02a5973605b9086f08d5081d04bb014363000006038c0b6d110106cc731308e0023a07fb1305601ba1839b4c088a10b88011043e427e75a600831464016903d3ba52b1ec095000ec050b011b0730478f11a0000755e331ef63db004a00a000069a91680e225f60f90092a9d0000764650a40000c591f95ac03baa33c5a1283d11871a6d2772c01c1057280f201f5012328b908232a5505e000fe02b507cf0809817c267c05c9528506d997696872194b206264030ad402d007d586d7228701d30605840f67838625a51443ce034d47ed45f704cb08730a1794e1252000070330000b56f0000b0b4000000000000a842e047609d406ae26b67b08a4de12aa0a34019000000000000b664342c50b50000c0af924dc9aa401870366002b26d00000000841e0000000060986614000000000000783ae10d980ee051d0ab4022a615808f0000a0832619a148d81500007000e007d616b032d01b483f163f00104028276b2015141030631049a027580cd0a7a05ab977802fb09ff07a97899053b0a80816e83be0790a1b809b8b460a4f0000178b0000847be03cf139a1170000b07850b3605408416262696b908af0aa7b1f5b446070d024601a42492101d496f4b4e035922127ab0000e18600008284831c00440000f031500310656013b071b045b25b4113766b5b4c6b0800008291b4888a50000000000000e38b0000225eb04d807230618425c0b097ae226f809e00000000f00d93480485e88728040000b11c3039204e9432711f445c905f004a300b97ada05680211292f09a7b1a696f3106704f19748066703f00000204d074ba20a118f025458794596091a06f000065946020913b783e342dd08c819b5b452076c21dc075e0991a4a183c3b19d7a750a68058c8379643a487b408d0523762d062b422e0b2d47fc0ac224a46231a5dca3b6069a4390000768a5433e07e0000da410b00003102090604000a010a1f88080000080d030b0c310304001300040113030203141f0c0001000232030b0801010a010007110002020208010605020401010119010b0304070203070506000210070d110100150b0a0504051d050002020b05000c0402003d0e1500260200020108040b03090500060204000d0602010100180501000001030f04 else 0xe0a0512830933085c048e216509713746026a02ec09cb040548400000268f701103ac254729fc29e8096145a39ab47552144806e00019612b7b4491ea44bc1)
def hashdeadl11 (i : Nat) : Nat := 0x5b144463e05aea749a36008e0000f05f008fc82400000000057a08357304bb42c02b0000807cd1701823000007095811411b96631031e07218223334c77b980e8010305dd000180820521064ca3ef0420000409b626cd483a833f03ac022e048a008f80a513f0000db73410f3393ca38834018881012b081c465a02c6142704300002631809700000000715300007115b00dd054b2886014000054161b183099000000000129f0870000a24110110427972915960000477d5b457113518aa01a00007134a023d08a1053002d678ef06b604a6076520f5468b025698fe62d5060c1370000e07eb793c95be02a510198285417000000000000000000005b72220ea00f9098e036e09602120000503908396112556c56084a3a211d0342f0784635707b4293308d0624205556235211962a72516903a0190235010e7765e07d5784f16feb3c248834149073d088b0134091f720f0803275f0052809446ed494b01b1b0305939136b20cf495111aba390000db890950e9807026e609a0205015880ba66b8778d4967988f077f007110cd289d0160000e278401d0000000000000000f032027400000000a08c6209804c4030102eb368a33f3b1d798e0000538a70215061a44e228300000000000000000000d01710838075e4517067406f00000000609a00003253a089a4002093b00a8125000090790000c0599583180c00000000c0411830f1160047224900000000906992725046700b000050511a67544b00000407c35bb06d0000504d3821ca470002762e0000cb1760948827b10a603b4009e06552019464444f9688a0286169097ab82524185057db2feb3d000e6303670ac01e70822426b090d664c05cf764008be03c365d6a2549347068706a71244461f086277c5780380d698dd120b27c20626037d807f403502fe1110000ea6e5071301cb0388044704f411c809595011003b20deb1a98372208b0561092820a91190049704bb03ec070670890335001a03f64504063613c50294b430832441aba46e146c8120193598c103df8314066401fd460e0745084044c100c7760b24b824f4006205b0000563070507a7c9058000000006a440000506e3040e97d006cd027646a6207807fb0450138e56fa018704e8482e0356085662f762c5b3be05eb81f1004f836000000000000000046203a6ac89692730000b034807a613d00008145702433536a79b0407805012a04e80082c50a0c0e782286421a0e4c00400004833a1491a02243880c0851202004211c6408c1835c192e081800c39681005000c04e408002001860c34c8040000000400008087400400100892c38005148410524200800478080001438126000000020022
def hashdeadl10 (i : Nat) : Nat := 0x1c05302000382d2ecf474c3a08f618409ea54931a0a2272b385214e934380040192451090d15cc0564307983441ce005970002c06068f08a82680cc070001a2c5d4a1440400018207150002808001022205d856c41e1700072d518800084a2900000a334a12801820030b1a27
def hashdeadl9 (i : Nat) : Nat := 0x202e0
def deadd8 (i : Nat) : Nat := 0xa24b7baf6624ad253281df927589c4d52540d02
def deadl8 : Packing := (2,6,7,0,4,3,0,deadd8)
def deadd9 (i : Nat) : Nat := 0x17a6100d01602e1f830400f202c200003405840f980801c0010720e8006a183c001d000f8007c00200001509fc5a0b0071b79b2bc5ba99429c459e8d258238d84a14078280a00a7becc495a4a6503c6fdb66689a4d50287fcbc661a544d029ef9c6aed1840d02bed9c626d3540d02ff49184d52540d02ff489c4d52540d02d7f11826d1540d02ffc1184951340d029f6cbc4a1354950195fdc7aed2564d01ff49384d52540901ff61384951540901ef4935496aa40d02df49b54951340d02f7493549503a6502bf62cc4951540901ef6125456aa40901f7612545502a6501fb61284612545600fbc1284612344e009dd9c7aed258ce009ee9c6aed1888a009df1c7aed2584600ff42558ce2284600
def deadl9 : Packing := (25,5,7,1,4,9,0,deadd9)
def deadd10 (i : Nat) : Nat := (if i<1 then 0x2693540b3fecd1349aa055ff26d1a4d502cffb30d2a26815ffabb4610340bfec8c26a81a05ff626d3540d02ffd23092a06817ff1184550340abff5da6b4ca059ff4d5a1a65029ff9569426a80cffdb8aa9354067fed95549aa03fdb4a13549501affb7092b2680e7fda849593407bf69424ac9a035ffaed2564d01cffab15532680e7fd25aa993406bfedc26ac92035ffaed3564901cffab0d1b2480e7fd38aa9924073fe9ad54c92037fe6e13540901fef2b09aa0480ffd9384d502406ffd5da6a81203ffa4e12540901ffe2708aa0480f7f95864d02406bff5da714ca03df74e135a6501affd769ad3280d7febb49699407bbe9aa4b4ca035ff6e123a6501efda5091d3280d7fdb548e99406bff5da474ca039ef495a4a65038ffb63553308167f9b0aa998408bff5dd54cc2053bf6daaa461028ffb6a4d2268157fabb6610340bbf4cc24a81a055fe26d1540d02cff33155206816fd935aa90340b7f492d5481a057f66d51340d02ff924a89a06816fdaaa44d0340b3fcd42074ca05df64d503a6502efd24a81d328157fabb40e9940bbec89a074ca059fd461a1a65029bfb6f5524a80c7febb6a1934063fedc554c9a031ff6d6aa64d01cf7b695532680c7fdb2aa9934073fcd8554c9a031ffaeda8649018ffb6ad1b2480c7febb68d92406ff55da4a81203fda4d52540901fee34a8aa0480f7e92564d02406bfd5db2681203bfa496aa40901dfe22b5520480e7f993aa902407bf492a054ca03dfc45502a65019ff36755251004ff9b1aa928802ff55da5092c01efa4a11849600dfd2515524b007f692849515803fb88c24a8ac017deaed2545600def55492a2b004ffabb6a123802ff55da5091c01efa4a11848e00dfd25155247004ffabb6a1138027fc55a5089c01afe6a12844e00bfe5768c227007bf128461138027fd5db4a89c01bde6952544e00dfe23155227004ff9b8aa9138027fcdad5489c013fe6caaa44e00ff925091a27007fd11848d13802fed5da4689c01bf6aa92344e00bfb57692c67005fdabb45633803fac92a2b19c013feaeda844a009ff370d2a25004ffabb695128027fcdc346894013fe6d5a344a009ff576d1a25006ff1a844d12802ff95da2689401bf66963344a00dfe22755225006fda33aa912802ff55da71114017faaed1888a00bfd3709ac45007fc9384d622802ff55da6b114017fa6e11388a00ffc23089c45007bea8844e22802ff4daa27114017faaed1388a00bfe5769c423007fd1384d611802ff95da6b08c017fcaed2584600fee26a92c23005ff1b848e11803ff09424708c017fc6d52384600bfe57691c23007fd1588ce11803fe89446708c01ff44963384600ffc27111423007fe13588a11803fa49aa4a81a05fd849515409019bf36f5524b007bd2888ce11803df14444508c01ff08ce2284600 else 0x4000888405e986c113905805080340b02e1f06087905c2003f080d05c2010004400c0288128f50060048004020800804100127c503a3f6c170230c990618643002074409038882341900e30020304004060800870140c00228180045c08224a09086c45817020801a183810008ad48702001100108e2b0c1c0800456383810230b0200117dff6de0be2c10281f00a20021f8a108140c707c503e3f8bed83901520010dd505020c988c1183426000e000e00086905c20a40d058002020340034003c1834002fd2040bdb798060306e1b00c84f01a5f8a10bc3024202bf0c090605c00880505210010fc506e1cc0693effc5f6de600097e28190cc11092183f1414080603412860a40cc6004380038003800340034003c003c0020e00107000f000801c0020e00100f78ee2192287800ec3041c003c00361820e001f8a1e001e001e00100000b0411ef1dc4377ae886cc5917b60fc50f000d8e083e2840000016a420f6c1b1c100000b521002c30416383f1420003e284000100c4aca220cd523db61a02c91b20b40600a0dbf169c61a02c9f6de60578fe2fb6f303f8bedbcc0fe2fb6f303d0acfaceacb9c93c83c68c63c53c38c1dc02bd1bb6b9bb96b70b4ab24b09aeeac8aada92a77a5ca41a31a169fb9eb9e69e19d19b69a698b97096094593591a8ff8c38a889887284c81b80b7f07bf7af79f78f7747597497397297197096f96de6b867c64b62560a5ef5df5ae5725415315164fb4d54c54b54a549548547546545545044043b42b41b4164114013fc3ec3e73cc3a639639138137136135c34c33c32c31c30c3073022fd2f82e82cd2b229728727726725725224223d23823322e2292192142041f41ef1ea1e51e01d01cb1c61b61b11a119118c18718217216d16810009807204c026000affd7692d3281defdb6)
def deadl10 : Packing := (156,4,7,5,4,12,0,deadd10)
def deadd11 (i : Nat) : Nat := (if i<1 then 0x86120d08111f407ad1db072b1c206d11ab867718d8613174859115b85231388497118042910183c50e603570c082b709d822b07a8195055010902a80410003ffd1849503fff6692540fffd2546503fff4613540bffd9a4d502fff2693540bffd1a4d502fff4619340bffd3546502fff4d69940bffd9a4e101fff6a135407ffd284d501fff4a935407ffd9a4d501fffaa935407ffd3849501fff4e925407ffd9a49501fff56123407ffd9a48d01fff56193407ffd2864d01fff49593407ffd5864901fff4e192407ffd3564901bff6a11940f7fd9846503dff6551940effeaa46503dff4a51940f7fd25a6503bffaa99840b7fd1a66102dffaa99840b7fd9a46102bffaa91840bbfd9846102dff6619340affda564d02dff6559340affeaa64d02bff6951340bfdd9344d02ffe6a10340bff99840d02ffe4610340bff9a540d02ffe6550340bff91540d02ffe4690340affda846502dff6611940affda346502dff64d1940bff90346502dff6629940b7fd93a6502ffe40e9940b7fd18a6502dff4d69940b7fd13a6502dff66935406ffeaa4d501dff66925406ffeaa49501fdf4d525406ffda864d01dff66193406ffeaa64d01dff561934077fda864d01dff4a1934077fda564d01dff495934077fd2a64d01dffaa993406ffda864901dff66192406ffda564901dff65592406ffda364901dff64d924077fd3864901dff6a1924077fd3564901dff68d92407ff95840901ffe4e102407ff9a840901ffe66102407ff93540901ffe69502407ff99540901ffe68d02407ff99340901dff4e2994077fd35a6501dff496994077fd23a6501ffe4e928803ff91a4a200ffeaa928803ff9a849600ffe46125803ff93a49600ffe46925803ff92845600ffe4e915803ff92a45600ffe6a123803ff91848e00ffe69523803ff91548e00ffe46923803ff9a844e00ffe4a113803ff9a544e00ffe49513803ff92a44e00ffeaa913803ff95844a00ffe4e112803ff9a844a00ffe4d512803ff9a544a00ffe68d128027feaa661029ff2693540a7fc9a44d02dfe6610340bfd93540d02ffa4950340affaaa40d02ff644d0340a7fda8a6502dfe40e9940a7fda3a65029ff6869940a7fda864d019ffaa9934067fda8649019ff68d924067feaa64901ffa49502407ff11540901dfe64d02406ffaaa40901dfe40a99406ffaaa4a200ffa4a125802ffaaa49600bfeaa915803f792545600bfe6a123803fe92848e00bfeaa923802ff9a844e00ffc46113802ff9a544e00bfeaa913803fd92344e00ff649633803fd9158ce00bfe6a112802ff9a544a00bfe68d12803ff11344a00ff68cd12802ffaaa44a00ffa4e222803fe91888a00ffa4d622803fe91388a00ffc4e211803ff13584600ffc49611803ff123846009ef6929940fbea8888a00ff48ce11803fe22284600 else (if i<2 then 0x6718d1b071686b63b38c6ac837ab208143ea5f4a804c20460a84911c7405186a093027a82ae19d57d066c694fa70dcc0ac4ea478ce31a1ecaeaf303c8c241ac2f19b38c69c83fbee47302190238ea2305424c6856399d2085637d12388c0c16cbeff1d208076416c80b40c0049e29d5208144b23f46802b201800c183275231bc58d5919c2ba9ed854030806003067bf9c352078df64634afd056e600c20020b418eaf319c182b832c8683382f1c2de703e3ac80ac412003efc19433aad06707f7f38754282036168bdf159a0ce09fa590158824f17a919786904bef86bc33ab209458f7dd8e39c8904deff5232b9120958e0b701b7e8611b1e288d8776dd9609e2b1c2f1582105b80098e0b90124824976d090cd009250909820be81c002d484d8f144c3068ea08444c12222609117812260911961224208de83785dd4e900b63480dfc5edb981b80c307224fbfd4f301f09477d2a0d202e2010188cddb353cc69017202256222f7fb60add5a80164f6c116903054660bb98d200c6e0e18f8afa73037818602100ed9a0d20beff8bdb752d00186f7fc5ea78e6e01e33bfe2f534770c056718d202388c2401066f7fc5ea68ee1b388131a6862ef8df646718d182bf7fa963ac8ce31a3fbfe2f6dd4f31c70187010d8f7c2b7561a05a04ce121581816fbfdb3530d74005590a1982b682c8ce0be2f6dcc0184f14410307c705b875e98d59067d2d5c686717058176d8d1b06f7c92f17b6e602d3634e457030b7007d2a0b20be2be9500fdf0b7b6c68d029b1803bfe2d415c1bc57d2a01fbfc3600ead415c1bdf363c5c6a8eae0d8d3915c0fdfe0b00ed9a9a81c83fbfc3600ead40dc1ba9e3b0e77f1ab22b839c4d4e356457053ab00682c8ae0bdb341640fdfea700682c8ae0dd49c58d1bc4ea782c02c87d1a03753c751d873bf64634dc23dfe0a86c03b6755a03fbfd4e0164340dc1a82ea786c03c57d1a03fbfc36015c3aad01bdfe3a8ec3ab86a71a7211eff5380570d03906f7fc5edba9e1b82040ec751d87590fa7538d71ddc2586a198ec1bdff16b8ea71ae195efb915c7ab8d74068ed23878d423198bda2f18b3a2a189fa24788e221f881a1e387521a785ea14384820fd83ba0cb82a2071816203f8099ff97ee1f8b7d29f137b21e9179b9e377829ddd76c1d8d7581d3373c9cb17239c6170f9bfd6f41ba36e01b536c99af96b31a9f69c9a4568619f5665990f63618ab610981f5f517935dc17435c0969959b163558495c7566954f54b14f552f949151914374f393a14ce130b4b2929349c124347e11cb46c9185456112143a90a941c9063415103b4088ff53f70fc33ea8f9b3e30f7d3d68f4b3cc8f233c50f053bd8edd3b38eb53a70e8339d0e5b3930e3d37a0da73570d2f3368c7b3160c0d2f30b952d50b132af8a3727d89ab2580901226 else 0x6c244e0445e2e80648bc5050262048e47300a0565ed8f60346f5d8ae98260a0c0068580a0c27015b807c906026158e08c030604c2b2a82103cee10cc378bc503c5a1a381a3a2d03cb121b082409e29104f14d80b00b29b02601632490481068e0401093981802127303093987200a0aca00c1820060c1003060ba9e62b81ec8b40d15c753cc0a26ae1d5e606624740ac47cc0483c9bdf72398ae02b28b1eff6cec705e2c44719c65bd0520ccbd4b702a0c67030651f4282f8a37f6c0f90083dbc507c95c01a2901847d2a015c7efbab500764fd1d5a800524460a84613d40171bdf12bb67568e07cc1703e060df4d22a00b883dd40220c2777c2ed22a06e0defe90110884fd1d5a800526915008831e748a802e219d5c0560f91f4ea40c1509ef89ad00884fd0566800c25702b3400611df1500c10c813b1c0f00a44001e0b8625494a83ec3b7532876c0fa40c07c018307cf7fb66a40f0d782d231a682c8a82a1e8185ce3c519b1a206a008183e7be5a8cd9c5ab50287af14281809827bfc7))
def deadl11 : Packing := (183,3,7,8,4,14,0,deadd11)
def deadd12 (i : Nat) : Nat := 0x226c48bbfb654c3991828d28cddfe2ea731865c0891b87a0bb538ea405a3487b1d9bfa906e3a90b8064694310477f6ca947523051a4f7f6c2ed4a3a91828d23bfa90b0351c15a42e0191a577f8ab8d4e631c0c3f7e91b6d4c6b1c0c3811c4dfe2ea51d869c41234a020c7bed54772271048d2408d8efaa71cc89c4123490277f528e4932271048d27e9c5d4a830c011d1fe8c8d4907400c377f8bb6d4e1b04223bd3538ea46e23461177f6da950523047efedb538ea4608191a477f8ba94761a711a3f7f538e644e0191a3f7f5398d032019383963e9c516e8018413c39e9a98d63991b83b6205dfdb2a635a0646093df6ac6b41c816ae0f00efedb52a0493230488077f8ba95061970704f7f531ac732112b842091d02eff176da98d61b04a4140bbec8db6a6358ec1250d06eff1571a98d6830c994a8fd8b08517fb7ae74f70b6c76686125bc5665224e74a34684243d739334f30b2c728322d1e919c15810b0ac056000ffe92a07ffd1940fffb30817ff46102ffe9aa05ffd9340bffa26817ff46502fff4ca05ffd38407ffa6a80fff49501ffe91a03ffd93407ffb2480dffa6503bfecc205ff90340affd32815ff64d01bfec9203ff902406ffd3280ffe4a200ffc92c01ff915803ff247007fe44e00ffc89401fda33803fd445007fc84600
def deadl12 : Packing := (32,2,7,8,4,12,0,deadd12)
def deadd13 (i : Nat) : Nat := 0x22dfc5b6a90e86821a4efdb54c724410d1f7f16a63a18e01069005bf8b6d52351d0d049cf924d00ffd03ffd02ffd01ffa00
def deadl13 : Packing := (4,1,7,5,4,8,0,deadd13)
def deadd14 (i : Nat) : Nat := 0x17e2b6526070604013ff
def deadl14 : Packing := (1,0,7,2,4,0,0,deadd14)
def deadsamples : Array (Bits × Bits) := #[(0xf854605d026923a5a16008862c9d18d42fd85e54d221898f1e440284a107a02910c3e03c06c40d2642ca74f54627022c11e389d9b43b30c961ca72386ce81500aa210d1ba1a121108a6c99348979d054ac200727ac054c0970110780155ad581,0x6844620d0040231585204884208800c4270824141201090814040082a10700282003e02402c4084602ca04a440240a1091218919100a2084314a220840a00480aa210819a02120100a4409048968c05484200702a805440920100380144a9480),(0x80b20c31f72bfc4e1481d27000d43c9c5bd438a9c5e0286040f054f111d001ce10920229bde170b8d339029e2bcac4cd494fb74d1052452141a61c5b9ca1e642f40c600258428f0e5c00df481e03202a204cd465e10fe01206e82c7b03150603,0x80100c30e6089040109182600012282018c41889c5e0204002b0604000c009861080028b1c2120a0d12000120908c00d005a724402504200402010501c01c208540860025840090e1400964816012008204cd0254102a00206a0247b01150201),(0x12ce100c308544478a85796a2341d206e4242e31335abb35943abb40be28c8e05c4c115123137950052a02a9ba0d31c096458c656cc338623e92230683d8962194d5145c2aa62229438824d8e06246d0cd124850733918c390189888a426380a,0x10ca0000108540870900790a0240900460282200221a991490081a0028289000cc41010021184410080a0a28a20020c0200184206c0128621092200a03d8103080d5145c02a2022143880090804206d04d100840322918c190088800a4221002),(0x8628ebbd17000228c83c0291b729e17b3643984a392a815889878936d04e41b82b8e28807cc302855ead3105d9868885c748c2b0724ae81086518e259124cd4278a18b4aa01db88524c3a3435a0814469349110c18f0c24c2a8052bd88818268,0xc2206a1d05000020401c0090e509051303449848110100480001811490070429238c000818c508010485900541c68805c240409012420000024186258024450270208b02a00da0842041a3414a08100690490104085040042a8052bc00818028),(0xbc8ccda8781e4d8151cd3cf93a4a0a01509a42078c1bc4a783ea4aec6c7bbbd02ef85be130b1750bcd872a062d01842a34826040203d5b99ac8899721d47b82106b4f88001d04ee6f42e103eb14e0a090b95e84905a08ef7a2230402e2b14bc5,0x148981a0109a5c8210c1a4690a42220050930202c418c4a7837a48680e50b9d00c601bc02020f518c9002a002c1124282402304220255b598c9019921c51b8010494708001d04e62d42a103a30060a090b94e84905a08af280230402e2304b45),(0xd3b19712becef4647857054f8773c68492608a46265cd6cd0106c449284294958830b40e8328a4102841c46a63b66493288c7290c714876750b08cb0eb0a532e014ce7e24f9c08720240400006971f885be46b00080a21145aa7f52cf42a8012,0x92218c003e8654007015040a0c73c50280c0084821449285810a8400004080918c301008002824100801c000230200c0688c40804110046300b00cb28307502a0004c5624f9c086200004000021315805bc46800000a00145205f42ce0200002),(0x3145d24845746a93b60987114c89950ee90ab5809889781e716b0d141d9e036fea797f20c896480c8b565809c5575a81eabcad03980701be24b7e8d7401960b32336416db2f0c4c050f169960250e8b311988b92828b0074bd455ad232c2112c,0x2307720c00346283a400011d4c09950fa108a4001a095004514a0014181e2261ab3d3060c0d6480a2ac41009e4571880ea848181d90321bc24d38a860208103323340169a2b084c040f169960050c8b211800b9082890074b8455a803282012c),(0x49615339cc24bb41a658244591d020101222d0f578b5376254a121290a30cd5c4e2ad1d6dabfa9e032f022500c91031b32331a7a9ace0ca4e96243014a4009cd0d2a3210b66014de852533c420acc80ff443ad9cc5d0f4808cd621151170ac54,0x4900539a4030aa408668006591882010120251355ca1242200a1212102144d6e020a42d6d2878b6832b420400cb9813312321a4a924e408ce04943054c0001c10d2a2200b040149c8425334420acc80fa003859cc5d0e4000cd201111150ac54),(0x2108654280dbc21c532263cad6a2ab60a053058994f658a43b3dd89384745a04932387065124c385d01899e2cc083e3c1e3327061d61ca921a4965c8583262f4485320b5c04953298d1f02098424a39520b6148b236021a80528c3236c545ab4,0xc0001428049001c03a04a4012802a200013019184320c200a34088304a0580410028702010083a440180cc2080827381411260a0400ca0098085048489022c408432094004053098d0e0008842422012032140b21202188052801030c545a90)]
def deadcolumns : IndexTree ColumnInfo := (.fork 63 (.fork 31 (.fork 15 (.fork 7 (.fork 3 (.leaf [(1,0,510,0,12),(0,1,460,50,8),(2,0,509,0,12)]) (.leaf [(0,2,440,69,8),(3,0,508,0,9),(2,1,460,48,7),(4,0,507,0,12)])) (.fork 4 (.leaf [(0,4,369,138,8),(5,0,506,0,8),(6,0,505,0,9),(4,2,440,65,7)]) (.leaf [(2,4,369,136,7),(7,0,504,0,7),(5,2,440,64,6),(8,0,503,0,12)]))) (.fork 8 (.fork 4 (.leaf [(0,8,227,276,8),(9,0,486,0,8),(10,0,501,0,8),(12,0,499,0,9)]) (.leaf [(8,4,369,130,7),(4,8,227,272,7),(14,0,497,0,7),(10,4,369,128,6)])) (.fork 4 (.leaf [(15,0,480,0,4),(16,0,495,0,13),(0,16,486,9,10),(17,0,494,0,11)]) (.leaf [(16,1,460,34,7),(19,0,492,0,8),(16,4,353,138,7),(21,0,490,0,7)])))) (.fork 16 (.fork 8 (.fork 4 (.leaf [(21,2,424,64,5),(24,0,487,0,11),(8,16,486,1,9),(25,0,486,0,8)]) (.leaf [(9,16,486,0,8),(27,0,484,0,5),(11,16,484,0,5),(24,4,353,130,6)])) (.fork 4 (.leaf [(29,0,482,0,5),(26,4,353,128,5),(32,0,479,0,12),(0,32,94,385,8)]) (.leaf [(32,1,460,18,7),(1,32,94,384,7),(35,0,476,0,7),(34,1,460,16,6)]))) (.fork 8 (.fork 4 (.leaf [(36,0,347,0,8),(39,0,344,0,4),(40,0,471,0,8),(49,0,462,0,8)]) (.leaf [(48,1,460,2,6),(50,1,460,0,5),(56,0,455,0,7),(64,0,447,0,13)])) (.fork 4 (.leaf [(0,64,189,258,10),(66,0,445,0,11),(2,64,189,256,9),(67,0,444,0,8)]) (.leaf [(66,1,396,48,6),(70,0,441,0,8),(69,2,440,0,5),(74,0,437,0,7)]))))) (.fork 31 (.fork 15 (.fork 7 (.fork 3 (.leaf [(74,4,305,128,5),(80,0,431,0,11),(83,0,428,0,7)]) (.leaf [(96,0,415,0,9),(96,1,396,18,6),(98,1,396,16,5),(128,0,383,0,13)])) (.fork 4 (.leaf [(128,1,332,50,7),(3,128,344,36,6),(132,0,379,0,11),(4,128,347,32,9)]) (.leaf [(133,0,378,0,7),(134,0,377,0,8),(132,2,312,65,6),(133,2,312,64,5)]))) (.fork 8 (.fork 4 (.leaf [(136,0,375,0,9),(128,8,99,276,7),(140,0,371,0,8),(132,8,99,272,6)]) (.leaf [(138,4,369,0,5),(144,0,367,0,11),(152,4,353,2,5),(160,0,351,0,11)])) (.fork 4 (.leaf [(160,1,332,18,6),(162,1,332,16,5),(164,0,347,0,8),(36,128,347,0,8)]) (.leaf [(172,0,339,0,5),(176,1,332,2,5),(180,0,331,0,5),(192,0,319,0,11)])))) (.fork 16 (.fork 8 (.fork 4 (.leaf [(198,0,313,0,7),(256,0,255,0,12),(258,0,189,0,8),(260,0,251,0,8)]) (.leaf [(264,0,247,0,9),(256,8,227,20,7),(8,256,151,96,7),(268,0,243,0,7)])) (.fork 4 (.leaf [(260,8,227,16,6),(273,0,238,0,7),(280,0,231,0,8),(276,8,227,0,5)]) (.leaf [(288,0,223,0,9),(256,32,94,129,7),(32,256,151,72,7),(257,32,94,128,6)]))) (.fork 8 (.fork 4 (.leaf [(296,0,215,0,7),(40,256,151,64,6),(304,0,207,0,6),(288,16,198,9,6)]) (.leaf [(273,32,78,128,5),(56,256,135,64,5),(320,0,191,0,11),(256,64,189,2,9)])) (.fork 4 (.leaf [(322,0,189,0,8),(258,64,189,0,8),(324,0,187,0,7),(324,8,163,16,5)]) (.leaf [(321,32,30,128,5),(388,8,99,16,5),(168,256,23,64,5),(224,256,23,8,5)]))))))
def deadautos : Array (List Nat) := #[[],[118,130,81],[100,131,82,16],[118,133,100,131,50,33,16],[116,83,32],[118,116,83,130,49,32],[118,133,33,48],[82,129,48],[118,133,116,83,82,81,80],[116,50,129,80],[100,49,128],[118,100,83,130,81,128]]
def deadlevels : Nat → Packing
  | 8 => deadl8
  | 9 => deadl9
  | 10 => deadl10
  | 11 => deadl11
  | 12 => deadl12
  | 13 => deadl13
  | 14 => deadl14
  | _ => emptyPacking
def deadindex : Nat → Nat → Option (Nat × Nat)
  | 8 => fun _ => none
  | 9 => lookupWord 1 3 0 9 1 4 (hashdeadl9)
  | 10 => lookupWord 17 61 5 13 5 4 (hashdeadl10)
  | 11 => lookupWord 124 434 7 16 8 4 (hashdeadl11)
  | 12 => lookupWord 137 475 8 16 8 4 (hashdeadl12)
  | 13 => lookupWord 26 148 3 13 5 4 (hashdeadl13)
  | 14 => lookupWord 7 47 1 10 2 4 (hashdeadl14)
  | _ => fun _ => none
def dead : Forest := ⟨511,14,fun j => deadsamples[j]?.getD (0,0),deadcolumns,deadautos,deadlevels,deadindex⟩
set_option maxHeartbeats 0 in
theorem geomdead : graphValid dead (boundsBefore known383) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=5) ?_⟩,listPieces_all (d:=3) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead8_0 : block dead 8 0 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead8 : block dead 8 0 2=true := sdead8_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead9_0 : block dead 9 0 12=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead9_12 : block dead 9 12 13=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead9 : block dead 9 0 25=true := (@block_merge dead 9 0 12 13 sdead9_0 sdead9_12)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_0 : block dead 10 0 6=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_6 : block dead 10 6 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_42 : block dead 10 42 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_78 : block dead 10 78 35=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_113 : block dead 10 113 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_149 : block dead 10 149 7=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead10 : block dead 10 0 156=true := (@block_merge dead 10 0 149 7 (@block_merge dead 10 0 113 36 (@block_merge dead 10 0 78 35 (@block_merge dead 10 0 42 36 (@block_merge dead 10 0 6 36 sdead10_0 sdead10_6) sdead10_42) sdead10_78) sdead10_113) sdead10_149)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_0 : block dead 11 0 4=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_4 : block dead 11 4 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_40 : block dead 11 40 15=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_55 : block dead 11 55 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_91 : block dead 11 91 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_127 : block dead 11 127 29=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_156 : block dead 11 156 27=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead11 : block dead 11 0 183=true := (@block_merge dead 11 0 156 27 (@block_merge dead 11 0 127 29 (@block_merge dead 11 0 91 36 (@block_merge dead 11 0 55 36 (@block_merge dead 11 0 40 15 (@block_merge dead 11 0 4 36 sdead11_0 sdead11_4) sdead11_40) sdead11_55) sdead11_91) sdead11_127) sdead11_156)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead12_0 : block dead 12 0 3=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead12_3 : block dead 12 3 14=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead12_17 : block dead 12 17 15=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead12 : block dead 12 0 32=true := (@block_merge dead 12 0 17 15 (@block_merge dead 12 0 3 14 sdead12_0 sdead12_3) sdead12_17)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead13_0 : block dead 13 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead13_1 : block dead 13 1 3=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead13 : block dead 13 0 4=true := (@block_merge dead 13 0 1 3 sdead13_0 sdead13_1)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead14_0 : block dead 14 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead14 : block dead 14 0 1=true := sdead14_0
theorem tablesdead : checkedTables dead 14 := by
  intro k hk
  interval_cases k
  · exact (rfl : block dead 0 0 0 = true)
  · exact (rfl : block dead 1 0 0 = true)
  · exact (rfl : block dead 2 0 0 = true)
  · exact (rfl : block dead 3 0 0 = true)
  · exact (rfl : block dead 4 0 0 = true)
  · exact (rfl : block dead 5 0 0 = true)
  · exact (rfl : block dead 6 0 0 = true)
  · exact (rfl : block dead 7 0 0 = true)
  · exact alldead8
  · exact alldead9
  · exact alldead10
  · exact alldead11
  · exact alldead12
  · exact alldead13
  · exact alldead14
theorem dead_start {prior : Nat → Nat}
    (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geometry : graphValid dead prior=true) (checks : checkedTables dead 14) :
    Impossible graph 14 inputs.toFinset := by
  have noRun := root_index (g:=dead) low geometry checks (k:=14) (by decide)
    (i:=0) (ws:=inputs) (by decide +kernel)
  have tgt : targetOf dead=graph := by decide +kernel
  exact tgt ▸ noRun

def field (data : Array Nat) := packedAt (fun i => data[i]?.getD 0)
def groupField (hdr raw : Array Nat) (sz a w wb i : Nat) :=
  let pos := (i/sz)*(a+w+wb)
  let base := field hdr (pos+a) w
  let width := field hdr (pos+a+w) wb
  base + field raw (field hdr pos a + i % sz*width) width
def pc32 (w : Nat) :=
  let a := w - ((w >>> 1) &&& 0x55555555)
  let b := (a &&& 0x33333333) + ((a >>> 2) &&& 0x33333333)
  let c := (b + (b >>> 4)) &&& 0x0f0f0f0f
  ((c * 0x01010101) >>> 24) &&& 255

def operandMask (g : Nat) : Nat → Nat
  | 0 => 0
  | k+1 => (1 <<< (g &&& 15)) ||| (1 <<< ((g >>> 4) &&& 15)) ||| operandMask (g >>> 10) k

def unrankRemoved (eligible : Nat) : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | j+1, count, rank =>
    if count = 0 then 0 else
    if !eligible.testBit j then unrankRemoved eligible j count rank else
    let low := pc32 (eligible &&& ((1 <<< j)-1))
    let skip := low.choose count
    if rank < skip then unrankRemoved eligible j count rank
    else (1 <<< j) ||| unrankRemoved eligible j (count-1) (rank-skip)

def packedLive (ops depth ar rank : Nat) :=
  let width := 9+depth
  let eligible := operandMask (ops >>> 10) (depth-1)
  let gone := unrankRemoved eligible width (width-ar) rank
  ((1 <<< width)-1-gone) <<< (10*depth)
def c8_1Data : Array Nat := #[0xbaaaa9999999998777777777765555555554432222100000000000444]
def c8_1 (i : Nat) := field c8_1Data (4*i) 4
def cd8_1 : Array Nat := #[0x889364d5344951544d0840d0109423]
def c8_2Data : Array Nat := #[0x4b111bbba641104dddc99944487111111115599982aee333311111555]
def c8_2 (i : Nat) := field c8_2Data (4*i) 4
def cd8_2 : Array Nat := #[0x156519394dd364d52548d1a461164551442107]
def c8_3Data : Array Nat := #[0x423c4293c84891e369084251aa31084514e739ce739c216000b49264739ce820e738421]
def c8_3 (i : Nat) := field c8_3Data (5*i) 5
def cd8_3 : Array Nat := #[0x2aa629785a959561564dd364d5274951a46116451082ac5b1682b]
def c8_4Data : Array Nat := #[0x86d94a9510d1a017321ef7ea6c42108446cb20842108632ce6173ce9c56094e6b048c63]
def c8_4 (i : Nat) := field c8_4Data (5*i) 5
def cd8_4 : Array Nat := #[0x2bb6318a5f17b5e9785ad6a5594a521464f1374ad1c469184310a420ab26c5b0b02a]
def c8_5Data : Array Nat := #[0x789a733b8a711dc173680044ef5500091084210842116b43130aa09318c639948423169]
def c8_5 (i : Nat) := field c8_5Data (5*i) 5
def cd8_5 : Array Nat := #[0xb32aa635895f16c5ad6a5694c4f128470bd2b0ab2749c26c8c1745c]
def c8_6Data : Array Nat := #[0x132c4a34a2335cdec11e7353c2234e6e2b0049564f6ae0a984229d2236318c3c6318c210]
def c8_6 (i : Nat) := field c8_6Data (5*i) 5
def cd8_6 : Array Nat := #[0x779ae5f97d5795d5353e4f52e4b51e438de338be2b8ad2788e2345d]
def c8_liveData : Array Nat := #[0xc0187146a30b8083817a48e8429c029b83e0d061d89c0102878180c02068984f219789e4c0892cc2110bd04dc1f0dd14c2c23a9d4e41e613ea8b41370703803]
def c8_live (i : Nat) := field c8_liveData (9*i) 9
def rec8 (i : Nat) :=
  let ops := 0x160 ||| (field cd8_1 (10*c8_1 i) 10 <<< 10) ||| (field cd8_2 (10*c8_2 i) 10 <<< 20) ||| (field cd8_3 (10*c8_3 i) 10 <<< 30) ||| (field cd8_4 (10*c8_4 i) 10 <<< 40) ||| (field cd8_5 (10*c8_5 i) 10 <<< 50) ||| (field cd8_6 (10*c8_6 i) 10 <<< 60)
  ops ||| packedLive ops 7 (if i<3 then 8 else 9) (c8_live i)
def c9_1Data : Array Nat := #[0x7cb6db5224924890000000ff80aa555554aaaa4000fffcfe00ff00ffc0aaaaa554ff00fc00fffefffec000aa5540000000000000003fff7bdea9555000fc00fff8fffeaaa898888885555500008db6db692000aaaa950080000000ffe95000]
def c9_1Head : Array Nat := #[0x3bbc06ef076b0152a014a80ce9013a404e9013a4146704e9403a500e9403a500e9403a502d900b2302b880aa10487c021f0087c021f02778099d02570091b0046c08da0036800da0036800da04060001800060001800060281305c440ed003a3c15cd08e241a060461001840430800c20400000000]
def c9_1 (i : Nat) := groupField c9_1Head c9_1Data 16 10 5 3 i
def cd9_1 : Array Nat := #[0x9de559123388a1180158559464dd364d5344a52849d254912345915451134490840d024043509423]
def c9_2Data : Array Nat := #[0x1230c30cdf7df7df7d637df7df49249030c30c30c309896aaa30c30c30c30ca616db68c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c2eeb6daaa92386182082082082081f7df7dc71c71b6964d249249249248c30c30c30c30c30c30b2cb2cb2c30c365949248c30c30c30059659634514533aebacb29e79e69249249249249249249228a28a289f7df79e79e79e79e79e79e79e79e79e79e79e79e79e79e79e6db69a69655555451349249249249249249249249230c30c30c30c30c30c8e375249249132791f55449249249249140c30c51451451430c30c30c30c30c30cca8a257da6596596594cc30c7996590b7c70befaa99e47df79a6596596596596596596596595d75d75d040c30c30c30c30c30c30c30c30c30c303cafb2ba679238a27df4cfaaa9a689451451451450618618618514514511e79e79e79e6db6db6db6523eba227df7df7d964f3ce389249249d34d1f7df79e79e79e79e79e79e7596596596596596596596596186186185d75d75d745145145145145145145145145041041040a24820104104151248c7df48c339e77df7df2cb1aeba28a28a28a28a28a1659555451451449249249249249245145145145145145145145130c30c30c30c30c30c30c30c30c30c30c30c30ce2491248c338dd2491302e38df7df6d9249130ce38df7df7db6db5d649234924503cf30c336db6d75d748d9338df5d33cf3cf833830c30c32d58c3037871c77f830c30c30c338653e37d6c5d75d441040c30f3cfaaaaaaaaa5145145145145145141867f6db5d75d75d74d34d34d34d34d1145145145145145140104104104c31230cca849249249245145144c30c30c30c30c]
def c9_2 (i : Nat) := field c9_2Data (6*i) 6
def cd9_2 : Array Nat := #[0x2aaa6677956448ce228458a6257a5e5785a95a5655855d565254851d46515394e1374d9354d1294a1274952448d1a4651845d164551444d124290841d0540d021e85a0e8390a82508c1a]
def c9_3Data : Array Nat := #[0x39cb12c256294c8cb945e3870e1c3870e1c393a64c64b962c3a2826eb98b162c58ab56e47394a9473972e5a3162c58b162c58b162c58b156ad5ab56ad5ab4e9d3a74e810061cd44896e012240001bb762a8f982c3c70e1c387456ab47a548d5aa42c5870e1c3873162c53a64c64b96160002448912241ed5ab57ad470e1cad5ab56acb020a0810212cd9b32ce5cb9100e2bb7715db05698e0e1c3870e1c387458b162b80e74c0e52a54a94891224489119d3a74e9c3870e1c2e58b142850a14285172574987028aeddc57471db06070b162c3870e1c3870e1c395ab569d3993258b160c18a1428a870e1c59cb366919ba665870e1c387165e58b163a74e9d3a758b12c58b162c58b162c5819c1a586965270e1c2a55bbb765923d58a518e70062b36e39c38700070e88f5aa64c991a3468c70000000003a489121cbd1b87080b162c58b162c58b162c58b162c58b3506b41ad4ccd98e66cd9b37508c990a1628a141428504080274e9d02040e5cb972e5c38467870d1a04810200c18344591c51d15bb31c386a344e8711188d122446e1121ce0f8d6cd9b2e50910101c0408126f1db05ea51a244891224488e837684993264da1a264c9935ebd7af5ebd19b366cd9b366cd9b3688d9b366cd93444c9bc5e4c99314587161c3873b2cedd981c387192061d9876ecc18306070e1c3873e78eddbb70b4c0f76edd8e1c3870e1c39dbb76e9d3a74e992f5ebd7af5ebdc3870e193162c58ad5ab56983060c1608102040810b161d0c7431c58b1e290c7166298f0e3c5071e290c7162c5930e5298a0e8708a141d0c70e8638b0e24398962d0e1c2870a0c11c2189e3c78f438501f8e62398ab56ad5896ac4b350315ebd3a398962c58b162c58b1c1c387362c4873a468d1962d0932388142850a162b814142850a142850408c991a4c9c1264c9932706013264c99326489435ebd7af5ebd7af5e6cf34264c9932658b0e2c58818763870e1c39db85a607b33060b162c58b16]
def c9_3 (i : Nat) := field c9_3Data (7*i) 7
def cd9_3 : Array Nat := #[0xaaa999de55912338899b6698b629895ed7a5e16b5a95b56959561575594b5294952147519454ed394e1374d9354d12b4a9294a1274952446d1a4651845d164551444d0b4290841d032ac9b2687b1e85b168590ec3a0ac2a]
def c9_4Data : Array Nat := #[0x708ba210c89122448911cc89122448e1224c88912244891204938f6a4028508081080226710882675422261d3a7121c386f1b355c9d326870de261020408870c408110d720a64468d7cf8abe7cf9f3e82f9f3e20f9cb95e48953a4f9f3e7c3c895a48ce1c38489430000891224489188f9f497cf8b167cd4f97a74dd9c390c4081021dbd1e3c78fa70da9720142851e3e9d4192aa15a548ad264c993212244d3a64c353a6ac54d548d1a2a2fdfb32a491b356acebf54a952a07151aa468d11c2a0c408a950e0fa75064aa546a1c2a569234748e1c3870e091226908102040811484085e80a952a55d9c39148d4a906a3ba88ce1c3870e451f4a1106c242850a14204a74c4080810204020478e55149453714e1544887100a44753a74c71ca83de931c72a54a920e1c234e9d300029800000e4992f9f3e40dca90383dc54864a9c3870de3c5c99311222040810203c71e4c7939952a32a84ea0c76a48045ebd3bd7abc78f1e3c78204082850a24489040a1bf2afc9bf7efc204092a54a2948a482720954a4e631454448a932aa04052a09b22752a2aa7321bf7efdfbf26fdfbf6f529a3a74e9c0548d1a2080848b7869bb76ec2a1a6eddbb754a911408040c162c54a9468d1224502a3162c58a980a50898eddbb79a8ce259ac8e045a244cb84d0f101ef4c4830424487a61cb97278f54202448f1e3c78f30244bb72e5cb972725bf1f1a1343c4e3468d09a1e1e3c4081020f3a74e8f08102040810204108509a343c7a9903855915394c8542a54e45104aa1ca854e542a54e45a642a1c2b50a9c58b0a9538559322a722b2527045320b122c489122c6528454a952a24489123988c844310204531eb88357e42a5456704431020408091628e3870e0f2040e3ba5407d3a4a40810f4e92f5ebc78f7a3c78f1e3c78f1e3e44054ddb9a80ddbb76e68d406eddbb76f3d8bfa54285084b968f02fde206eddbb76e7881c6840f983070e1c387078f1e3c7c0910264276d0f10]
def c9_4 (i : Nat) := field c9_4Data (7*i) 7
def cd9_4 : Array Nat := #[0x2ccaeeaaa6677955bc6b1ab6719b6698c62d8a6257c5ed7a5e16c5ad6a5715b56959561575594c52d4a52548519454f13b4e9394e1374d9354b12b4a9294a1274951c46d1a4651845d1544d0c42d0a421072f0ac2ac9c26c9a22c7c1ec7a1705b1684b0f03b0e82c0ac2a]
def c9_5Data : Array Nat := #[0x3c1906c11fbf7efdfbf2245fbf4e9c7bf7e2dfbf7efdfbf6cfc9271a85fa17ebd3a16c3c8211a84836063c7b61e4080f1c4080f1e4080f20108107e9d09c2011fa1383c7c4885df2026b990986b898f6e2448c6c25ba61efdf9c10244921284bb2884270f1efdf906ebdfbf7efdfbf090d70e1c25b8a12204087efc9bc6611fa742709515cf9716963060c6d15d175e9df3f22f9faa7efd53f9cf02837e9ce3e5efdf2f5e0c61220909231e3c48f1f1091156648899b01c150a48910484919e30140a76cbc6a77cfc8be7e71f9e3061f8508fe73c1e141bf4e71fbf38fce3f4efdfa774e8c1230609bc66481bf7e49f937ece73c66b0792423063604bdfb65e5dfb64e853a17efdb216c9d3a11e413903a420185656227189db3f7efe50d43109516c350a1425c68d36fdfbf88fdfc47e5c6c37d0df161a306441a845a108fc610181080c184063f18fd7a742306172d453d126fdf917f45f8c262938c74bc90200713207c8133f5e71faf391109c88701892425f911225b2f38d571b24bde924e493bf884893124fdf9444f07891e89f927e70e25102040912244897eb8d897afdfbb7efdf8924909a30ce4e1b26c27bd52c1fb09ef56a3a2a51a3429d7933a1ce8776922414625fd07c743bc12d113f6d09eada27cf8c24492bf18fcb92162c5b66c4861218d890d1ad5e2c352e2366cfcbb66cd9b366afcbc490f19ac34cc91642448912320b97162c58b90865a7427223c5869d3f4e84e4b7e9d0b686821a086806361aaa818a031b1c30628124f28e0d386069c306281218d978d54bcc0d2448c181aaa811314090b183538c6c488122040813224139c3870e1224489511b413847e84e4b1039b08132a51c23413847ebd3a17e408211a346884284693162d08c1828b974e993518ae9b03a32df365c9901b7c6c6c32342630194274c18c180ca13a60c16a260b9f3e70b262c9a15e2c9b9931a13d5a3242c19206b537223bc66b10a142850c31b0c60c1830648]
def c9_5 (i : Nat) := field c9_5Data (7*i) 7
def cd9_5 : Array Nat := #[0xb76ccaeeaaa6677735bd6f1ad6b1ab6758d6318b629895f57c5ed7a5e16d5b16b5a95d5715b5695855d565354c52d4a5254851d464f53c4e9384dd364b52c4a92849d1d4711a465184350c42107334bd2f0ad2b0ab2749c26c9a2348c1f07b1e85d1703d0f02d]
def c9_liveData : Array Nat := #[0x32f12345237373737373737104e781c33034e781231547c317c2134317d35206a1c211c21211f1f1cb8672008b85d26497209215454543121575721575757544e5757571e51512f262b282872311e107277782a2d081c132a260d00213232303201000c4e7834377d7d2c227d750912340f0f35b1f51f122131547c75fa571c3468131322030331367d7d7d7df1282e1c1f071b1b79347b7c7c79377c7b79795a5a577c35377c7c7c78092c7d076b1029100444424137366e597b6d007dbb2c032b03111d1d3226300d310305321c000100001437132d052c05030f140c010f2f2f36377c7c7c3703780108072b03006b0f280f0f0344441734211e2b282b2b34212118170c680f08f1282e34727d7d0e7d7d7d0f0f282e2e0f347a3479791f1f2121211e572108081e1e1b221e1e1e1e351d373477340330020103000957341e327d3636fb0f7a7a7d7d362e7a7632210f2e347d7d3620203620201c2e353535352f072f252f0f7928704ede081e1e1b1e1e081e1e17171e1b071a1e1e34797d367dfb7d7d317d7d7d7d79106b341e077d3434076b6b6b6b6ba6a3a2a5a2a14ea5a54ea55d550c59310c1b360d0d0c3333320d2c047d757d747d123472030efa75000004101f1000340c31252804346b7579574c793475752e791e757504347979572b0429041210062ef60f0f1e0303790b0f1e2e03080f0f031e1e4b25020f020f0102060602512e0c1b010c081f0f02bf342e2e287d0f2e79bb792e57795a575775726fe675bf34bf6b50bbbb572e34312e652e6be2c3bf7dfaf979f679c3bf34797934752e2ec3797a7dfaf979fb34347d7d7c347d35de4c4bab2e34312e2eae4948a5d8ab4847796b5f685c655b0519050000000005050500000004015205050500050500000004051705050005000505050000050000030000040503030105170505050505050403190104040400040404000009000a080a09091b53001952051b1b1900000b080a0909090a05050404040053030304190404170404050101010200020101193b19473d103b3b3b0f3d0f240f0000000003000000000000030000000000000004000000000d040f0a0a044a1616161616161650134d50501616161616161651514e164b192b16505050501650]
def c9_live (i : Nat) := field c9_liveData (8*i) 8
def rec9 (i : Nat) :=
  let ops := 0x160 ||| (field cd9_1 (10*c9_1 i) 10 <<< 10) ||| (field cd9_2 (10*c9_2 i) 10 <<< 20) ||| (field cd9_3 (10*c9_3 i) 10 <<< 30) ||| (field cd9_4 (10*c9_4 i) 10 <<< 40) ||| (field cd9_5 (10*c9_5 i) 10 <<< 50)
  ops ||| packedLive ops 6 (if i<198 then 9 else 10) (c9_live i)
def c10_1Data : Array Nat := #[0xa00000000000000000000000fff800000000db6db6db6d9b6892492492492492492492489246db6db6db6db6db6d2449000000000000fffaaaa50000000000000000954000000000000000000000ffffffff0000fc0000000000aaaa95000000000000000000aaaaaaa95555550000000000ff0000000000fc0000000000fffffffffff0aaa400000000000000000000ffffc0000000ffffffffc000ffff00000000fffe00000000ffff80000000fffffffff800ff8000000000fffffe000000ffffffe00000ffffffffffeaaa5540000000aaaaaaaaaaaaa95000000000ffffffffff80000000000000000000000000000000000000000000000baebaebaebaebaebaebaebaebaefff000000000800000000000ffe000000000ff8000000000ff0000000000fffe00000000b6db6db6db6db6db6db6db6da92440000000ff5b6db6db6db6db24924924924692240000f00000000000aaaaaaaaaaaaaaaaa9555550aaaaaa940000000000000000e00000000000fffffffffffef55555555555555000000000aaaaaaa55555555400000000c00000000000ffff00000000ffffe5554000000000000000aaa955555555555555550000b6db6db6db52492492492400000000000000ffffff800000000000000baeb6db6cb2caebaeaaaaaaaa69a68a2081040f34d30b2cb186186186186186]
def c10_1Head : Array Nat := #[0x5bf20abf3015f981abc0055e002af00727383837813bb009bd202d67806b3c0359e01acf00d6781673012f8c017c604ae000570002b80015c000ae000570002b80015c002a5e8052f40297a053ba009dd004ee802774013ba0295b8242c409f5c00fae027558136a001b5000da8006d40036a001b5004ca5006528032940974400ba20254f81227008f3200799003cc801e6408d2c006960034b001a5800d2c006960034b001a5800d2c006960034b001a5800d2c08390040c501021c0010e000870004380021c300ea06d72016b900b5c80d8de02c6f035b600adb0056d802b6c015b600adb0056d806a690153480a9a4054d202a690153480a9a4054d202a690153480a9a4054d202a69034b300a598052cc02966014b301a18c050c6028630143180a18c050c60286301431838d681b6a205a4e04c2402550802a840543f0291e023cd801e6c08d30006980034c001a6004c2d02595002ca8110480861e0030f00187800c3c0061e0030f00187800c3c0c1150200900004800024000120000900004800024180000]
def c10_1 (i : Nat) := groupField c10_1Head c10_1Data 48 12 6 3 i
def cd10_1 : Array Nat := #[0x277956448ce228460062559561575594851d46515394e1374d9354d1294a1274952448d1845d164551444d12421074150340901164390d42909423]
def c10_2Data : Array Nat := #[0xee733322220000008b9cd6b5ad63166318c0feaaa000db6c000000009999999999944440039e79e79e79e79e79e79e79c000fffffffffe00b4a4f7bce72106318000a988881111111000b6db6db6d0001c3870e1c3870e1c00040810204095555554fc00c000db6db0000000ecccccbbbb777000aa99999643333000ffe0a5555500db66db492490ffc0b6db6d924800eeeeeee999900000000000000000000102040810203fffe0ffc0ff808888883333333330909249240000b5b692400000eaaaaaa8ffe0f800db6dadb6da909248c9200000f5555540ffc0fffcc0000000b6db6db6a000180000000000efbefaebaebae000f000ff00ce739620c6318c1000008887722221111100eeeeeeeeeeebb330fe0000000000000000000000003ffffcaaaaa800fffcff80ccc6663300000000bbb3300000000000fb6db66da4808886661111000000aa800000fc008c421084000000000000010a135143dfb060c078f1e3c78f000575d654c5145145145145000000032c71c70c30c30c168921c703ffdcb47f228a26cb000000d34d34cf2cb1c71c71cccbbb6444440000a51ca494a52108108000aaa9999442222110b65555555555555008102407ee17a02c588102040000f3cf2f9df10200000002027cffe9500094a528b18b5ad4a52940ff6922249240bbaaaaaaaaaa6100eecccc66666110000c003aebaeb9e79e79e79e78dddd6666644440009de79c71c6db61854b140000bbbb987777765220fffddccaaa999880e66b5a51ad5ad4949400000d75d759604cd145145145000000000000000000000cf1955554008412949ce518000000008c6318a52841cc630420ddddddd88777770030c30c30c30c2c71c7000f3c48911224284f1b3668d1a1224041a50000008000a9555554db6db6249200ffffedccbbaa8850ffc000009555554444422110fffffc92400099999999955555509922222222220000000ffffbdf7df7df7df3cefbffffffff649082081f7de5144d3410000000888888888888880094a5294a318c631898c09999444444000000aaa00000ffffffff00000000082082081040009e313ce389032c70bedb6da289a68a27dfcb9cd6b5ad6a94a50c000c30c30c3030bedb6cb2ca23ff39ce52918c63150c60145143000000cf3cf2cb2cb2ffc0f000ddddddddddaaaa80d6b537bdef7358841cc0fb6db6d800009999998877770000fc00000000000000000000000000000020b7410208206180000000032cb2f77bda52883186318c609988888666666660000000000000032cb2cb2cb2fc00aaaa0000db6db6db6db08000fff8ffc00000b5ad6b58210842100000fe00aaaaa000ff00b6db6d00000088888888888000000000000007c888e23860e60e02e697180baeb6b4300300081000e1208badb2c145145144,0x8618555555553cf3ce00000030c30c30cc718a169a69a1008a2861861856596595551440e72d6b5ad6ad6b52900003ffee76ebaebaeb6d8e38e3b5ad6b59ef7bdc000000ddddccccccccc550feee654433221100aaaa777333331100fff0921249000000fffeb6da89249248ffe0ed2492248000db6db1200000ffe0bbbbbb7770000000000000000ef4caeb1c71a659ffffffe88000d6db6d0000001c3870e1c3870000182848302040cccccccc1111100088555555000000009ce6e7318c6318c63180fff08c6318c5294a52918c20041041041041041041041032cb29a181228a28a000f7cf3c9999998888888600ffffd000fff0a0000000fff00000fff095400000ffc0840000000000ff80c000f800f000db6db6db1000ffc0144041041000f3ce72cb2cb2db69246d8000ffaa4000d92492000000fedb63492000aaaaaaaaaaa88750fd555400b6db6db6db40000000000cf3cf3cf2cb2cb2fffc0000ffa489240000fd540000922491249248ffea54008db6db600000fff08655555444444110aaaaaaa8b64849249240aaaa8000f800b64800000000420e739ce308000bdef75145000005269a696081b6dbff6d80000000e888888880000000000a69a699e79a58a28617df9965555544100000fe00db5649249000f000db6db6db6c40842104a5294a508410000008a286186181f7df69a659def7bdef7bdef7bd6800a996666666600000aaaaa9549246db6db000fea95540b6db6b6da240db6b5b480000db6db5b6d240fc0095554000fffffffe4800924920000000a5554000997772222220000000000000000000000000003ddb6d249200008777544444222110ff4909249000b2491b449240cccccccccccbb650fffffffcbbbb888888880000032cb2c71baeb6cb2cb2cb2caaaa555555511100fffd80000000aa540000ff00000000000000fa5555540c30c1035d75b6271c71c344aaaa285471c702aa689a48e2e000db6c92492200aaaaaa533333000045145100003df7befbefbefbaaaa665552222220dccccbb999999210ff00f000db6c000000008888888888111100a8000000eaaaaaa0ea000000186186186186000038e38e36fe00fffc000088666644444400009988777744442200fc00f8008000fffefffffff0aaaaa950f000fe00db6db6db6c008000b6db6db6d248ffc0a9555550aaaaaaaa33333330fffe0000000379e79e79e7df5cb24e38e38e369965904000000099333222200000004d334d34d34d000035be4fffe4ce7210842108210840aaaaaa80a2529418c6318c63180028a28a28a28003cf3cf3cf3cdddddd7777776660fe00aaaaa800bdee2084210842108420ffc0b6db6db6db68aaaaaaa8186186186000000000000e79a6982081965450f3ce3871c0208000000000000000cb2cb2c00088888880,0x6da08420e739294a52910800000a69a69a698a081f7df7dfdb349249124090c621084208400000008888311111111000b6db6d00000038d34d34d34d34c30903df7daaaa8000eee9993332222220db36c9000000adb4924800008000dd31111110000000b249246db000b998888886310042000fffffefbecf3cb1c71aaa8e38dd7565965555430c002871c00ce739ce739ce7398e38cd34d30c0c0fff775bdc]
def c10_2Head : Array Nat := #[0x9788348bb819e5d604eaea007575003aba811b5d00ca2e50641710020b880105c40872e008096e0604b581b95a6118acf06a5660346b2421758a009ac50441618020b0c20557e182ab900c55c844ead419a56408c2b0082556020caa8303548187a9e028d4e833aa6821352c18129008cd46044ca200a450e0122870091438146a1819d50610aa7f044d3e82209ec10d4f2183a7300f53981789c81394e0118a6c08a134014a99c0a44cc012266028d3280469940234ca051264047d31023a98001d4c000ea60007530003a98009c4be00e25f026d2f003697801b4bc00da5e06552d802a96c0154b600aa5b00552d812896818f4ae04725604312a040494008149e000a4f000527800293c30149218fa4308591f86068e42a64680922320a4116860c89c03f44e11922302c511025e88029843600b21b02550d032085c01042e00821704390a801c85400e42a18420f0c6104862080c0c140402020208e0ff04547e82993ea08b1f30640f8040e7b03073cc05f9e506e0f105407742153b20c81d60e08e7828073404039a0201cd02fce6007e73003f39801f9cc00fce6017c72c03e3960dc1c808a8e2044070009f37e08e1bd0658dd012a6e419036c0081b60808d907046ac0c03540201aa02fcd4807e6a403f35201f9a900fcd4807e6a40be35001f1a800f8d4007c6a003e35001e9a800f4d4007a6a003d35001e9a800f4d4007a6a02353480d89a100bcd0835467812733805319b0090cd814666819d32e0cc1940454c9002a648094322049990004cc8002664011031c0c598b0c14c2807e6140be30805e98300f4c1807a60c0bc30401e18200f0c100786082a32fa10d9790808ba81025d00012e818096e02fcb6807e5b403f2da09e96b00f4b5807a5ac03d2d605e16a00f0b500785a803c2d401e16a00f0b501765a403b2d201d96908bcb2844858419d2bc10a95a044cac012455c2812a40009520004a9070252c30b28a18813f0c109c861e4cc23425e15012a0858930416488380236183915050089855c4381a621610c907082881860e3f42321f21858f308e07784523ac28b1cc1858e00c406d027e3602af1a614f0ce084065060831038217a0a00bb02fc5d027a2e01b716a1138b104905784362ac1941501058a408085006042681b612e189891082c46856222003111011408404604104121f83070f01880720a5836862019c2930c418685c02f82d807c16c03d0b601e85b00f42d817816803c0b401e05a00f02d045e1582950a200a851005428802a1440150a200a851063827040a128102090000848000424070210431007615203608401906200b004205806082b04fc14807e0a403f0520dc82600e41301700940b20480978220a640e813007011603400b01a02540c802a06419002c008016082009061003031000c1880000,0xd344f0a5a25062d1101af88214ec3c08561c03210d401086a18142f04f616845f0a41a984c0d2423028e11042b07819083600841b08160b860904430481614c4060c0e000620fe83047e8190bee0a11f48606f8c2907bc0083de0041ef0406f682347ac1153d202a5e8834af380a479a0cfbca0279e4832ef1801678c0c83c30041e1811ef0820477c1823b80659da8320ec838275611b3a708b9d18534e7809973a1443980c19c9060ce30230710096b8602b1c28254e0c02a706093b810299c00248df80a36fa011b7d008dbe8046df419f6f404f3790079bc8132de00986ee04b3760059bb0320dcc0106e6047b720c19b60364da412f6ce0d4b640689b08430d741156b60c83580041ac0620d4813f6a00dc34d04d5a58362d2012e68c0d534302a5a1043ecf811d6780cc33904599b802ccdc09566c00ab360641998020ccc28865c185b28067d928420c8401064218831b08998b8148c5819e62604eb12065d87850ec283046081412ff08e57d826cbe41b25ec097af406a]
def c10_2 (i : Nat) := groupField c10_2Head c10_2Data 16 15 7 3 i
def cd10_2 : Array Nat := #[0xaaa99a2277956448ce228459a629895e9795e16a56959561575594a5254851d465153a4e5384dd364d5344a9294a1274952448d1a4651845d164551444d124290841d0540d022687a168590e8390d42a0a42508c1a]
def c10_3Data : Array Nat := #[0x8892a710891a5463407ac141f3e5c891234a8d08d0141f3e5c993264c91222448d0a1423437ac16ad507cbd2a34279f3e5c891a711f382752485a6f9c1327120c1a710891a0449c408102040942850891170d0810204094e23e704c993224489122b49d23e7cf9b2e102538d18911a74685080e982d5aa0b92247cf9f3e4c9c87efe4c993264c0810204093018305ab48917d456922444891a0c28d09f3e74992e89122244d1aa6f9c38a84085370469be2244891a3427cf9f3a73a60c182d5ab56910a1643f1c244850a1620d1a3468d11529d4a74e9d3a54a9528af5caa443468d1a20407a74a20d1a36a441a3468d883468d1a229d3a71223e62a468d1a3468d1020404a74e9d3a6e593264a9122454e4538b4e3542e7cb8e1d4e9d3a71a1a8a94ea53a94e9972c58b4683054172f52a53014e9978d0dea83e5e9be5ae96c67ac2a54a94a89727523d2a31df132c7cb933468a5374b5625a31d451a142850a11da2d5ab56a81226850a13e7cf9f3e3ba5a70e1c3870e1c3870e02a342850a1427cf9f3e7cf9f3a74e9d3a74e8ee9d3a74d141c3870e1c3870e1c3870e1c3870e1b366cd951c38102a346850a1427cf9f3e7cf9f3e74e9d3a74e9d366cd9b366cd9b366cd9b1dd3a74d16ad5a70e1c3870e1c3870e1c3870e1c3870e1b366cd9b366cd951c1aa54a916a5088c4b54a1122168272a54a070e53a74a8d1a342850a142850a1427cf9f3e7cf9f3e3c78f1e2c17af5d3a74e9d3a74e9d3a74e9d3a74e9d3a74e9cb468cd92d5ab56ac50a12a54a952a54a952a54a952a54a952920b41a2d50952244808e1c3870e1c3870e1c3872a1c3870e1ca74a8c75089153a74a951a31e3c772d16ada74e9d3a74a952a54a951a3468d19f3e7cf9f2e4488f1e3c78f1dfbf7ee9d3a74e9d1c3870e1c38710d4a952321245cbd28f1cf9f3ee1c387149c20a8e1c122e5ea5470e05d270e234670e0952a2e0f9f2e5cbd2a51e3b8707cf9f3f1e3c78f1e3c48911f3e7cf9f3e70e1c2142850a14284c183062952a54a93e7cf90a142850204081018a54a952a5468d1a3264c78f1e3c78d1a3468d122408101f3870850a142850a040810203a74e9d3a60c182e5cb972e48954a95254a4488c993264c921c3870e1d523c788f9f3e7ce10a14284c18a95254a83060c182891222551c214285098314a952a54a9214285098183060c183254882fcc998f1e3c47cf9f384260c478f1a3468d1a34488f9f387085098304a952a54a952a3468d1a31e3c77cf8f9f3e7cf9f305cb972e5cb978f1e3c48911f3e7cf5ebd7af5eba74e9d3a74e1c3842850983060912a94a952a54a94b8f1e23e7cf9f3e78f1e3c78f1c2142850a13e7cf9f3e7cfc788f5ebd7af5eb84262a1f2e5cfb0a85ea173ec0bd42e7d82850a2a176c5cfc65a7d68da648e1c386e0ba74e9d34,0x724488912352a52a515ebc78f1e366cc0f9f264c9931c3870e1a304d490fdfb2652a51722448912e5cbd1a142850a14234668c182d5ab4b972e5c91224244d0a142850a13e7cf9f3e7cf74b4b97a342850a142850a13e7cf9f3e7cf9f3e7cf9d3a74e9d3a74e9d1a34386f5eba74e9a2850a0b972e5c9122448702a342850a1428509f3e7cf9f3e7cf9f3e7ce9d3a74e9d3a74e9d366cd9b366cd9b366cd9b366c68cf5eba74d18305ab4b972e489122ca2a282e5cb968d0e0c150a0ba82f5284a211a1bd60a25288af1e3c6cd870e1c384d450a0bd2a319cb05a5cbd2a54a952a3468d19f3e7cf91224468d1a3467efdfbd7af5ebd74e9d3a7464b972e5cbd1a3468bd78c18305ea14273e7e8d1a346850a1428468cf583060c182f5ab56ad5ab56ad5aa1428509cf9f3a74e9d244890912242d1a3468d0a142850a1427cf9f3e7cf9f3e346870debd7af1d3a74e9d3a74e9d305cb562850a14274c94f9f3c74e9d3a70e1c38489122438705040a8d1a3468d1a142850a13e7cf9f3e7cf9f3e7cf9b366cd9b366cd9b366cd9b363467af5ebc74e9d3a74e983060c182f5ab56ad5ab56ad58b14284e8cf9f3a74e9d3870e1c3468d1a244890e1c244860d42850a1427cf9f3e7cf9f3e7cd9b366cd9b366cd9b3264c993264c993264c74b410102040bd60a2a54a942850a14213c78bd3d4a952850a14285084f17a74f4284f8d060a8a9500437ac2a50a13c8509f36850a07e850a13e7bd74e9d1f3d428509f3e7cf9b363437ac16ad507e8509f3e6cd98a0f1a346a8c640768d1a3467cf9f3e7cf91223468d1a33f7efdebd7af5eba74e9d3a448912040810203a74e9d3a48953547de458425e3c78f1e3c7eaaa172e5cbc578f1e366cd9b366c3870e1d4e991234e8b62244891234e42a144895322fe9361c157d2a2b8993244891281248d18d020282e448c05a46a54a710993a71221122460178102017a9417408152a53804c01224448c0811891224489172f01e3c78f1e3c78f1e323e4c9aa93020172f10bd42e5df366cd840882489539221fc993264c99350fc58a48912254c7d3223e951931e3376080b938d529d42042a54a74c78fa63c912a740b8fa9529d31e2c911a74234182b93a74c202851e3e98f244a9d03e5e99f1c38748654e4c98e3c7c37ac08d18cf9eb022448d08cf581188f8993271c99327109932740b93264c8912246a177d21fb2244891222fa89224448d05150054a6f9c53704c9542042a537048892a89ea5412249123e5c912247dfbf64a8f972e5cb972e9e2bc78f0f9f3e7cf9f3e7cf9f1c3870e1c249112346340607cb9722448d13e5cb912246993274c99109418a93c78f162c44888094c99122469d022448918d00f9f3c5c84622f5ea622463c78e7cf9f3e4c9937b2192a9300891224681122462112341d1164a,0x52a122448912244aa54a549e3c78d9b1f72e592a1022952a4dd01122448912244408a54a952a5468d18cddb365e9d01f3e7cb972e5c3d4a84c993264c9931022513264e54a244a850a140b972f502932648891a248b122444893264c44a94489122246850a140f972e5cb881152a528af1e3c6cd9b363e7cf912244891122044864c954533468d18cf583060a14273e7cb972e5e8d1a342850a1423468cc0f9f3a74e9d2e5cb972e489120b52a54a952a54a05ea05a0be8412f52a0086c2a506042850a140f972f428508d0deba74e98303e78b97a915ebc78f1e323e3870e1cc0bc58afdfaa1b4a95250a1011224489122446d2a54a951a3468d1a31a34678a1428509d3a0407cf9f2e5cb972e5c89122448912246952a5468d1a3468d1a342850a142850a11a3468d1a13768d1a3450a14284e9d020407cf9f3a74e9d3a74b972e5cb972e5c9122448912244889122448912244885080e8d1a342850a14284f9f3e7cf9f3e7cf8d0d4284e98f9f3a74e9d3a5cb972e08154a84c993264c9931a4c993264d412244891123428502e5e8d02e4894a2d420972552a13264c993264c68d000004a9448891952aa51a0489112244890a3427c686f4912264c98d952891224448d0a1428503e5cb972e368d09f1a1c13e5cb922448891a3409122552a528af1e3c78f1e3c3e7cf9122448911c3870e1a346487efd552a32a5468280e972e4489122fdfb972c9952a549ba0224489122448d2a54a952a3468c67af1e376cd98305ebd01f3e7cb972e5cb972e1e952a54a8d1a3468d1a342850a1428508d1a3468d09bb76ed9b3468d1a3468c183060bd6ad5ab56a7408101f3e7ce9d3a74e9d2e5cb972e5cb93264c9922448912244891222448912244891224448912244080f468d1a342850a1428509f3e7cf9f3e7cf9f3e7c68d19ebd7af1d3a74e9d3a60c183060c17ad5ab56ad5ab161f3e74e9d3a70e1c385cb972e5cb91224468da54a951a3468d1a3468d0a142850a14284f9f3e7cf9f3e7cf9f3e7cf9f3e74e9d3a74e9d3a74e9d3a3468d1a3438709ebd7af1d3a74e9bb468d1a335ab12204080f9f3e74e9d3a74e9c3870e1c365cb972e5cb9224489122448911224489122448911c3870d1a32a54264c993264c9b0244aa13264c993264e54a2448891a942850a142346849cb972e448912244993272a5122542850a140b972f528d0a14254a6c5cb972448954a950993264c993262c5ca9448891a942850a1428508d1a1374e5cb9722448912346850a13e54a8d06097244889122468509f3e54a2f2893da33c91224c0993272a5468c4891222468d0a14281f3e5cb972f46850a1427ca951a0bd7af5d3a74e9d305a7cb97244891122468d0a14284f9f3e7ba6cd16972e5c912244a951a1428509f3e7cf9f3a74e9d2a53a60c182d5ab4f9f366cd9,0xad5b1e34686f9ebd745cb93a826a5310f9ebd62c09d413529d310c09d3a7097ae11529bda94a13d6080b93a74e9d3a71e3c78d1a346890a1427cf9e3c78ed8ae5c9cf172e5cb972c58b162c58b16264c70ea72a3c689060bd74c582d5a5cb96275172d5ab56ad5ab562c58b162c5874489102171f3e596ad4a4c9c67cf5d315ab56ad4a9529726b569a3468d1a3468d16285298910b972e78b96ad5ab56ac58b162c58b12a54a74d1a8ef9f365eb53cf8f1e3c689121c27af13a53870e1c3870e172c5414f9b19ebc6cc17ac3870e1b366cbd4a95070e12244850a16a54a952a54a8c5889a952a4462264275cb9316a952a0e5c9aa54a952a441c16a54a9223c78ef1b356a9d3a72f1223e7cf9dbb62c58ae5cb972e52a54a94c993162c58b162d52a54911e3c78f1e34589121c2850a0c18305d396cd1a3466cd9b366cd72e5cb972e5cb56ad5ab56ad54a14274e98c972e58b160a142c78ee9d285070e1c3870e1c380aa54a911cb11c3848912244c85cbaa54a952a5491223c78f1e3c78b1214276eddba72d9a3468d1a3364c57ae5ab56ad5ab56ac58b162c58b162c58b162c589d3a74e993262e58b102024489a952a4f8f1e3c784f1d3a74e9ab366cd7ae58ad5ab3870e1c3870e1c3870754a9527c88f1e3c78f1e2c48509fbf78f1dba74e9d3a6cd1a3468b96ad5ab56ad4e9d3a5489121c3870e1c3870e1c3870e1c3870d9b366cd9b365cb151d1e13a74d9ab568d1a3468cd7af5cb972e5cb972e5ab56ad5ab56ad5ab56ad5ab56ac58b13a74e993264c952a54a952a54a952a54a952a52c244850abd72e5cb96ad58b162c58b13264a952a54a952244890102a9504d4a951e2f5cb972e5c9d6ad5a70e1c3870e2d5ab56ad58b1625387172d5ab56ad5a9529c911d5274e9d3c88ed9a3264bd7af5ebd6ad5ab56cf9f3e7cf912244891223c68d1a3467efdfbf7efdfbd7af5ebd78f1e3c78f1e3a74e9d3a7470e172e5cb972a54a952aa6a5482a828552faa05531e3a952a512952163d2a54a5a040823a953194a94f1d4a74e9cf9f3e5e3a93e141838f1e33162fa3b162898b18f1d8af5ebcbc17288cd2a54a94b70ddbb76281020411cb972f1d8b1631d8b15ebd7af3e5e3b662c4f89121c3c78f1e3c78f1e3c7a54a9528e850a140810204074e9d3a74b972e5dfa2326490e42850c78f1e3a142850d2a54a9528f11c2142850a040810204080c478f1e3a14284bca8f1e3c78f1df3e7cf9f128f1e3c78f1e3be7cf9f3c78f1e3c78f0f972e5cb972e5e3c78f1a3468d19ebd7af5d3a74e9d172e5cbd2a54a947891224488f9e3c78f1e3870e1c3842850a142850a14285020408101f1c3870e1c3060c1830652a54a9478f1e3c78d1a346891203a74e1c2142850a140810204074e9d3a74b972e5e3c78f1e2384262952a54aa54a84891225,0xa7cf972e5cbc68911ebd74e9d3a6ad5ab05a7cf17264e9d38b162bf7af592a4488f9f3e7c993263870e1c349121c38753a74e9d38f1e24489106d3931e33768a13a03a5c954a8022bf728aa53a74e244704c7538ef9c54a74a93e7ae1bb7404c9548e48953a74e9b870e09d3a511ba040dd3a0a708b47884890d1b4e9d3a71e23e7d4e9d3a71e24284f9f3c78ed3a72e5cb97a710b92a8e21272e5c654a7120a72f50052850a13f7ce1baf5ebd7a24038654407490d1b4e9d3a71e23e7cfa9d38d1a34688f9c27254e9d38f121427cf9e3c769d3a73e7cf9f3e5cb972e5cb972f4e9d3931e3448911ebd7ae9d3a74e9c3860b539f3e5cb932449d12254e9c58b11fbc78f18224480f9f3e7cf93263870e1c3870d18329467a5c9c9932e3c6724870912244bf7eca2d4a950f9f2f52a540a16a54a8f2a54a8e470912244892e9d3a74e9d3a74f52a54a8f1e3c78f1e3c78f1e363e3870912244850a16a1222249116244404224572610109c6607cb97887949322448918cc0b9726448d3a74e9c462b94a62c4421122bc99224448918cc171f2e5c8916edda3468d182d5ab56a74c993264c993263c78b9122461264c5c8918ed8993264d71326ca4c09300891844489177057112246a499325bb76ed1a34689932684ed691254c6d2931941f2e4c892244488ea74e24488f8204081025424448d3a6f9f3e8911c132644891a710204081021322448d26ea0f97234e2444c5820408102448911f133e5e24488f9da62e5c684224624488edda62c58b161a34252827cb9744463373e7cb972246a53a54a4c9931a04080eddbb6ed183060c16ad5ab56ad4e9d3264c98f9f3e5cb930810204091a1bd747cb97274a02d4e9d3a73e7cf9b366cd9b2e5c8911b09e3b76b56ad4c952d3a7162c4891223f78f1b366ca8f9f3e7cf9f3e7cf93264c98e1c3870e1c342850a1020408123467aed417270202d5aa0f9790fe4c0812644880fdfc68d1a3406eddbb468d192d5ab4b972e5cbc98cc16ad231e3437cf5d54244870912f9c3162f9c31244aa1212e18916ec18be7cc5f3e76c571ea85cb97a8f9f3e7ce08916ef9f3e76c6549931e34182dda332e489492f519b79f3e7bc76ddab466cd82d5ab56a54a911a3468d1a3468cb972c54ac578f1e3c6cd9b36624c70e1c3870e1224489a868d1a3468d1a8d18b972f52a09a74ea5410c183060c18304448912122448810203870a1428508102031c346850a102541a169d3a824408a622a54a74c68d10204081010204a74c453a6346881020404081193264c993264c952a54a952a448992a8b162c58b162c488a914589115326552a0910f693d26484bea952a09887cf9f1352a54a752a5388582c489120bc78b94273a74b972c589050b529991224489a7529ac58b16172c5a99f3e7cf965ab539f2e58b1664b56,0x8d4264c993274a530404c8af2e5c8d24049e17a921b36605cb97255070ca949ea02245e172e5cb93274a44182f1bb44074b97264c9927e5c93c6cbcb972f19eba60c16ad24e9b362e5c9128cf5d177ef593260c18224480f93264c70e1c3870c13218549119fbd2efd93f2e4552a64c8912254e9d3244a9b85284912a74e2121048908a74e9c989264922448912850a14285084891214285a8142bc7825e2754ca9d31b52a12a952a54a952a3ca952a1778f1e3c78f070e0a1699122469b65c4553f243a9d3a74e9d4a648953a74c244a7129c4524890da74e984932e4be974e9d2a752a54a914b978b15b366c6470e0a157af5ebcbd4a952a54a952a458afdfbc78f1e3c78f1e3c78f1e3c6cd9b366cc993254a950e1c3870ea952a54a92139326c953f254e984a750993244499381029d3a6448858410253a74e9c7805e9d3a74e3c45cb93a74c5cb975cb939d3a102530a10204a54a140810204080f1e356ad54a14260c172e448972e5cb972e469d3a71e0384260054a74a0406ebd7af5ebd0405cb9717224a9d3a74e384a69c9528d02013a74e9c788b972e5ca13a74c7cf972e5cb972e5c211094e9d38b0de3c78f1e3c78f1e3c6cc983054a1122407cf9f264c99308102498d020405cb972830624c9554e9d393263c0810204070e0bc47d10bd4005ea49932604080ed3262f18b9f3e7cb972f1a1ba3c5cb978af1b366cd9b366c7cf8e1c387172ec9fbf1d4e9d3a6e06881020408a848891234dc081022a538844890a94e2447c4888da74e9be1b4a2be448470d1a3065388e189222346881020408a74e9b81a20408102089110204087efd94b89122447efdf3e7cf9f22448a5d4122495424484890e1e3468b4e988a84891224269d3a64c9931c4dbb64e9d3a03e7cf972e4a9d3a74e9d3a74e3c78f12231423c78fa74e944403e9d3a74e9d38f1e23b76edb366cc583060b93a74e993264c84f172e5cb971e3e9d3a74e9d3a74e2448911c21424c98f1e3c78fa7490111f49b97274e9d3a74e2384e850982e5cb972c589931e3e1b76edda3468d1a3468d1a2f5eb972e5cb53a74e9d3264c993264c99020408101f3e7cf1d3a74e9d3a74e9d3a74b96254e9d28ae5cb76ebd7af5ebd020244870e1224489114a952a51e3376cd98305eb972e4280f9f3e5cb8724229d3a74e9d3a71e3c78911c311e3c788114e9c68d1a2274e9c90fa499326a74e9d3a71e3c476eddb86cc57ae4e9d3a64c98f9f3e7cb972e5cb972e5cb0f1e20408a74e9c56cd9b3664c99306089122407cf9f3e7c993264c70e1022946605c99392464c71e3e1c3a74c8d4a74e9c4264c98ea74df13a4c08d3a74e244884c9937ac0891234e9c68cd5aa82e5e33d3e7cb978d1a13a747ce9d2e5ea1326388912e4c98e8cf5d3a747cf9d3a70e1c385cbd400448c68d1a2356,0x2026493a026448972e5dbaf404c9112449b2f4e7d4284074b91264c9d27aa10132648893a50d428404c8c850461172d5005287090119046a5291193a64074b932509e273e5cb972f2a446870d29f2e5c9938b162c37ef152a50a1122407c993264c8911c3870e194a3467aa0b9727222bf2f19bb460c16ad4074b92234a33d74e901d2e48]
def c10_3 (i : Nat) := field c10_3Data (7*i) 7
def cd10_3 : Array Nat := #[0x2bbaaa99a2277956448ce226ad9b6698b629895ed7a5e5785ad6a56d5a5655855d5652d4a5254851d465153b4e9394e1374d9354d12b4a9294a1274952448d1b4691946117459154511342d0a42107415032ac9b2687b1e85b1685912c4a0ec3a0e4350ac2a0a42508c1b]
def c10_4Data : Array Nat := #[0xed2a52a64315458d163584d51309aa4862a8b163458d51309a8504082cb9a9218d592d8d1a35870de354532a2c58b51309aa48366cd9b90c4297366cdc84018b95366ed482cc5006a9424414184b162c18b46a942441406cd9b3722820b5518da906502aa2b4c184d52097c3198d42e5db172e5f0e1bc68bd4638b0c63342863c6e69cf8f00fd39f1e01f810202980a64393658b596352439aa6cb55aa5aa9b365acb1a921b33366cd9ba158b9b3768d9bb552d482cd9b332cd9996c5842e2c3782d494831e3a951c54910485082e58aaa1207aac52e448c521c8e3188c18318b0b97342448838885062aa090a1058aa21420b9634152a2e5c8172e5e84172c5517a0a8b979f01c30538f1d7978f1d4974f1cfc750dc84d4534155060c1826cd9b7305cc1730609b36d0d9b2e54dc436e554113060a6366cd9ba29a09b3468d1b366d8d06264c9b72c4d99326cdc887493506ccd0d43468d32c38f0e1c382fd25d8ef61bc6cde1b342fd25d7ef5266bb1debd8efdebb4a5c266b95aac38705fa4bb0e0bf7a93b5d7ef5da509723c786f1b377b0e3c382fdebb4a5c5850a13b5cacc5fbd0972382aa0aac25f0e0bf4b0e0bf7a93b665efdebb4a133478705fbd76e5284ed1a22f8f0de2f7b0de2f8f0e0bf7aed2971614284ed9ab305c7dfbd764427aed9a354a952a5441561366cdc1c26cd9b2b09550370a162958b1612f8b0e0bf4a5455c5f0e0bf4a53b66bb1e23640be2c53b162c586f589f3a74078e1bb460bd61c1216562bd08be2c378bc2c5871e2c382fdea52a13b66b96ac2e4c2b182b965e8eeef425cef1e2bf7a9519d365c266ba0c28f1612b52a54a9538e5c053014c0534e029c6a6029a73e3c053629cf8f014d89f1e029b14e7c0538f1d9b54e7c780a71cb55629cf8f014dab14e7c785014d9b2a9417b349352c78aca8318e9b852ff1bfb38f159a4f6cc1c46ecbfc789fa8ac5ecbf7f8e93fa4fd3527f8f163c565fa8318ed538ea50538ea71daa72e3a9a71d4e3b54e5c752831d38ea67467ea0f63af2f1d796827467ea0f63a539fa83d39fa83c6cde3ae80b97a539fa83c5cb9b2e5cb972f8ebcb405cbd29cfd41ea539fa83d8cb97b34a73f5166c9830071e2ac631e28ea4bd6af425aa41671e2c58f15a978b1e2b5531e230631e2c78a997035a518ad67163c56a463c54a7467ea0f63b521063b34a73f507b198a6631c7c78ad62c78ad62c58f1562f627467ea0f562f58bd62f58bd62f6694e8cfd41e9d19fa83d8d520c76acd29d19f9ec76694e8cfd426ad28bd6945eb4a2f6294e7ea0f58a539fa83d5a517ad28bd6945ecb1b36294e8cfd463c78b163c55ea4bb3627467ea3163c56aa4bb3627467ea0c30616294e7ea0f3060c20987a98c1a5499526306dec14c60d9a346d53dc49b11a2e60b392f2214284ecbe2c378bde,0x6a922d4a732d5487243163c5807e2c18b118a142850a105caaa952841c78f1e3c668d53b56a54ac711e97c17e8be6c74d9bbc6cdde366f1c47a5ea39634105fa315b2e3b7ef519ad999dbd7b1c42f82fd18af971d2f82fdea335f3b5c74c17bf7aed19b1612e3a6cd9b366cdde366ef1b366b1c47a5ea5090c60c12f82fd18af9b1dc17ef517cedb333a60bdfbd768cd8b09b333b82fdebb728cd8b09f3b3a60b9b366cdde2f78d9bbc5f1c47b52439366901aa6f4d9b366cb95366a21a7b40d9aac6cd9b3668d1a218f10fc78a84172c6841346a9c081031c0814e0539f1e01f9f1e01fa73e01fc75d0539f1e01fc75e5d39f1e01fa73e3c03f8ed539f1e0456cb93e3af8cd1aaf8c1d7af45b2e4e5efd16cb939b378f19b3668d57c77ef516ab8d9b358cd9b075ebd1bf79726a8e58d7a12ebc55c9cbdfa315b2e4e5efdea2b93a4305cd9b366f19b375f1dfbd466c45c6cde3af7a5e3366c1d7af5ebd1af7ef2e4d5e5c58552848635e5d7af2e6c56cb9397bf462b64f7ef518b09b334e90c17bf7aed19b1613666b93a4305cd9bc66cdd7c77ef51885f19b3668d57c77ef516ab8d17af2f183af5ebd1bf79726af2e2c2af2db33a921cd7975e5d7977e8c56cbafdea3362c26ccd75fbd768cd8b09b335d7ef5db7466c584d99aebd7a0d4a12209b366dcb1738afd188b8de3986cdc8632315fa2d5719366f1b5375a54a365ca9b90e449b366e856375ab56ad5afae4cb6b4a8b5a562c5792d18b5a536ad29b33ad28d9b378b15e3746b2eacbab2ead8973666ba04081027c780a6b539f2a029c75e9cf8f014e3af2e9cf8f014d39f1e029c75e5d39f1e029a73e3c05352a1bc663198c4e31e3a06c506c78d56388f5e90c7887e29f1d80f0b41cb154810396280b16a8e58da72831e38f52a1bb58d8e28e80319326642a9121cb92a6d8963458a9a895189536c6a59366d8aa2860a626250ac42a58ac49058b172b6551b2aa8cd991698972a6acc87365cc44c571e2c382ac9706451931428638100abd7a6deaa7a98de2c1168482f52a1b13231c09f1e0293f04c182f224316342c507354c99326cc993264cd736aa850ac5ecc8a06ec17a162cb1a069e97b30681bb066cdaa068d972a69a9b6846b4aaa5e858b2c681a5a9a818a0e5563c663183315a51a3469c96346cd1aa921c963468d39366e439546ea39546ea39545cdd490aad54b521526378f1e372e58b1906cb59b35245536a85d9366cd9b3682cd0ac5ec9b3766d59626dcaaa0aacb15a9acd962631e3c78d6e388993264d8c863c43f1629f1e038603c485a105cb155415396258d163546926a8e5896a34935472c4db9626dcb18258b16c784b2534c58b7826d8da72e4d9663698b1345a8ad589ab61a98b096c4c71e2318b0993342841338f1e38101cb1b4e4b31b520dda6258b48c78,0xc50486321cc872c65aa90e71e2c18b0623468d1aa0820b96268d6382e5cb162aa820a905cb15581f27c78eb9830631d7a2631e07a99b39638dcb962c552aa080d5472c4d1a90c705f7a771c47a805a040c6d5a2f50dc8736ad5472c681a3521cb1b55305f4c756e38899350412d539358b019c580d16c460b63c589cb9a16a863c6331e3c781727c78f19a358c1d7af471e0889b0272f82fd14e7719b366abd1bf7931dc7822262f51cb1af21cb172e58b9c18d899c18e5158921c8f366a81b355afae4c756e3895a545366f162bc94d9aa3169a65443163c58079ac541cb1546a99a3468d1a83424313468d63a12243162aa0d490c55607cb93962d8cd1a318cd1a075cc63355e898c7822262c5b1d4a92243162aaa315581f2e4e5cb962d82fd17c9ce962d8cd9b3468c1bc17ef1dc66cd03ae6319b355e898c17ef2e4c771e08898b972c5b1d4a8e5cb162ab1d4a92243162a8dd7aebb02e4f82fd15c9cee0bf7a8ae4e90e98c78f183af5ebd1bf797263b8f0444d5e5c8638e44862c552a838d8b154a8dc872c58dab582f9dc710b97375189a365cac46321563a95244854aa0b1326479a3522d5a346a8173751cdab4c58d62e5cb9b366ea48a9218c1346a439636aa60beb931d5b8e2264d04b972e6cd97a34d35472c6d482e5ea48632d548218f1602c5878ec460b63c58a448a1058aaa906a63c78f1c08068d403502053816ad4a9468d1a3468d4882e4d1ac72244172e55549105caac0f93e3c75cc63ae6318cae631d7a2631e08b11eb64cdaa4172ab03e4e5cb962d82fd17cd939dc66cd9a346319b355cc60bf79eb63b8cd9a186305e3658398c66cd57a26305fbc98e96c78223d4c5cbd0a142863a9520b972c58aac752a489105cb9546ebd09682bcb6d826a72d82fd18ad939dc17ef516ccd3a43a60b63346b19a355f1e0bd44e96c66cd9b346abe3c17a89d2d5e5d7a37ef263b5e5c5858f04588d935490e6bcba9215609af93972e58b60bf45f273a5cbe0bf7a8be769d21d3060b972c5b05fbd768cd8b093a43a5b19b3668d1b366319b346301b2c34d60bf78e980260c63366abd13182fde4c74b579716118318f0444c5cbe3a95244862c5563a95244872e551baf2e0d79716439c72243972a951b90e5ce3a951cb954a8d1a72c6d5a738b0513a00d1a366f19b378f162a952a487268d486382fbd6c771c47a80bd6945cd1a2f4de9ba8e58c882831d4a92242a5464c9a3522d5a918b0517c743803468d9a378cd9bc78b154a85eb4a2e5cd1a365cac4a8c6d5a952ab4aad28d1a7a6a41a2e5ea48726aa487268d1a3521cb1b550b60be98ead2d8e2264c5eb4a8a5cb9a346cbe2346b15e2e5cb1b2f469a6a8e58da9520bd694f8bd67cecb972f78bd37a5ea4872c5517ad29b17ad29b332f5a5366668d17c468d62bc5a8986cccc2,0x9b326cd99366cd99326ccd47341cb9a06cd99366dcb996e6a39a065cd47268d1aa152a196338c999d38cd4a942439558cd9bc33a337c764d9ac64ec9b35671d99c6e7619d1a237a94a8c36ed1299a122cb19464d9b9464a993328cd83310ccaa940dd2a33a19d384a73668cd3a4389a592a12e7466ed23196751c999464cca9d19b9c94ccc99a91ce519b161366674e346685cd0a181b27353a9519f39a4b971199a34619b2649a5b39f3e51b366cd9b366cd9b366cd9b366cd9ba52e2c284b959b368d51b366cd9b366cd9b84ed9c27accdb972e5cb1a1218c882e6a5472e6439626cdd9a0e589b36ab1ccc6f1a34a1218aac6d2a54a12189b5566a48638f11b366cdd25d4e61b378f1e3c73acd9c78e763b365bb7c78e737b365a638d0dbb45f52831c78a79b366cde3366cdda9e6f1589e5714a378a7b4a52a13568baa52992a23c5d8ac589eddbb4958a7b536d2544373da1b950554f8f3e3cf8f4e94f9709eae56aa848726c51b82aacd09105563a74aa50a142839c64f14f366c910c66ed1ba5316e2246f14f86b0942246cd9bc562c4f86b0953a5425c276d5a335ab09090d31a922152934370cde2a6e1512a94241bc53e39b366f14f8ef295284b8d9b374a123c54e94f84f1d335cad554a120de3c53e3c0366f19bb46f193b46ed629f1e034378a7c7694b158b13e3b4991dadaa5091e2a74a7cb8b0a14076d19ae5aaf1539f1e1345a6cda3542b1b4598ea4a9ee1a3058cf1bdc75294c9515e2ec53e74e8d01e386ed182f58702bb66bb1cc6b529456931ebc76d9ab466cd72d587050969518d4738f1d498ba1acc7425b568ba3b4c7419b2584e6435aadcb372c685472c4d9ba749baf5c6f14f9d31ab466b564f9d1da2f97119b266ae7e29f3a3b86ecd933c6c31daa6c14e370a5c63976a9c070a6c5870a4fd39f1e029c78ebc840423d39f1e029c78ebd4972d0539f1e029b5629cf8f014d39f1e3c0534e1539f1e029a73e3c0538ea31c52a541c78d8cac78d863a6a4c63c5671d8a4bf1d8a4bf1e3c4beb175f8f1d9a4bd7ad3cbc2e35f66cd2b54ec63c78f1e352631cbc7071d9a4ddbd3952a558a4fdbe3c562937976293f6f8ecbd6f8f1e22f8f1dab349fb76edc4b7c72dbd9a16695aa78f1c88e81010a539fa82f5e5a0a53a33f514a7467ea273f505f198c71e4209081063c680c5490810529cfd41ec58b162af2d058a53a33f507b163c720c549082210c78e42040431e3c551048c78e42a4080863c751059a53a33f507a3529d1a3447ea2ba02f4a73f506e94e7ea294e7ea0bd29cfd4529cfd462c58a3a91ea67457ea1462c51d48fc58ad5797223a9403e94e8cfd446b341cb15566a4e7ec54529cfd462b55e9a0a539fa8c54f13f518a9e2af4e5a0a53a33f514a7467ea294e7ea2d5aa6c29d3a74e44172c643962e58c862,0xb3a3619d18d1bad2b0cec339e25ad2a29b33462a6a8e682a346481ac338d1934670ce8c668395541cb15552448af2e0d4a7423a9c71f1d38ea6c17365cd99326cb99325ea48403cc183062462a0ab1e2c542c9bc66cdd93760c9b326ec1932824502f51562546cde2366f197325ec5833626585468d172f524579752848558f1e32752848558f1d9358c9d93566646c33a3442e5cdd49060dccb26acb19528ab589207c8c119f1830623609b193988d06cd0b162457978aa50918f163c44eb17c33a33f2f5ab469152848c78ec9ac64ec9ab332335c33a33f5b8674688fd31a355a517365cdd6945f0ce7f8673f2e5eb4a365cbd15b4d354b350bd4914151a218cd619cfcc9a32670ce8cfccd0556684172c5554b350c993266a47a78ed5815220d0910500a0c40bd072c56ad89424315482a48626e848722a0d09105520898e84882e501014e5cb1638e84172c4d8a121828612e58d0a1218c882e5cb9725dcb937518b972c4b1662e589a3546926c6b0db1c569cb1346a926a989cd072c50162c58b1634c60b17259cd9918ad313468b51a49aa319c4a72c4a4892c2c58935c145f366898e967c75eb972e4b3e3af6a391539cb962c4cd4738d83070e31312d8a9c82c54b31a9228629e4b14f258a7ac25564be2c58b3891414aa366cd184cc58d09142417a0c71860c6ea509105054a952448638cd9b2c18db1418a431621aa509105031b5218aab068c2662c4b062c6aa5091050630c1b1b1a29b1860d8ecce4c6d8c8c5231860c58b4ec73a19e628242a2a62226312274ea262726a922831546714f246714f25564b68d1b14f241314f86b0904a46aac98cda8ad3098cd4ab528494064c993345319a8ab162a531aaaa2b4c519b0969d889a8482e5cbb62f0d60e6cd99d062688639e1831ac33b0ce8c6b14f8f01c30323c750a0c58d9a105cb15552cb9556aa509104d193324d19a98a7e29e6a8a6c78d8303f1eba08f5e5d880e14b8b0e14d870a65d870a6c5380e149b366cd96726cd9b366cdb990e4ba02e6cde3c66cd9bb2c5cb92e6f1b9b1631e3278f193b38ecc6414de9ba98cd9b266f148b18cc13b38cce2366cd992b62c5589658c77b42ac66cccb166d3db4f6ccc7c378707b666ce8c584f9db35a7623d6cd9990c339fb7c33a337c6e6cd082e58aab3418aa83466c584cce9cb0a6c5352e588f72c5cb1a18a7c070c0c851341cb1a0c555062aa8318301caa82e553962e58c85521531622d8b173428507341cb172c5cb1a14284863220b972c683962e58d0a1218c882e71e3972e0b1541b1e382e550a72c71e3c78d8aa4040310218f1e39e431e3c6e58d0966cc99736284a72c5ccbc78672d96c58d482c58c1c69504a945caae4f2a51b889a21b945d8cb94e6089ad220aa83420ae589d21b866e0e19d196b49e70dd14d3e5269760f,0x44872e6a397264d1932e5c9a366c4993320d444068d17354de9ba920c993464c99c520d1b3668d484064d192a68c993266219c7525d434f641a346a21a346cd173668c97a85cd177a5ea483264c993468d193464c9a3264cb972aa84172c5554a068d413468d1a3428d1aa74f1e3c78d8b15541cb172c5c983061cb1a0c4db92ee5897a0e58b03101c3162e5cb1c501c303e268314105ca0632100a0d4101bc78e83162e5cd8a0e58d490c551ba121cc4c741cb10c15cb190e503163890162d531e3550684f8ec58392f218c862c5018906cb972f21897a1218a0618e39fc71d4996341cb1406ad5030627c760158a090831c13642d50a12243972c58e3218e7e3c5427c78301cb862c0d86c53e3b01f8e78fc73dc5072e58aaa921cb15468dc8638f1e355418c154c58b154ab1b13666831554189493260d4a0c55632b12a5062ab1e38875a9a6986744c125ab5695e5d441524c162aa4d3a460b152b824e093124c93124b498955561b311c9a34ab154058f0c93724c9ab464d9933824c77c9cc95c126244a8c7154a0c71c1a8698aa3464aa0a9418e3c76223c3b85a9a69856e19d12226346a0b197418aa34667c070d982e529c304c264c993464d193384c99a0c58aaa9260993588c95ab24b1a925a7b0415a54080a605380a4f95ad29ee2366dec81ef68629e4b14f2526ac97b39ece8cb6746886cda58b4dea6213b14f8ec148f0b3a35072c55537b8f1e395423c0722a0d09105520632244154e454154828172f055177224b891322409a121c988320c1830618c172e58972e28bc89104bd09105017a121c8a83424415483148a1220aac6818e38f0149faf2e7c0527cc5796831c8b3424489122cd0b342c4f1541c917305cb9545e8395541cb972e71d77cd53e3af456bd4ce7154a14285072ab19b278f111238b0d2ad40cd6335aa50a141caac64f1bd5a770ce22470ce2269a9120f5b343a456619d10890c34b150a14282a362f1e2362c89b238e862c264b0ba064ce2aa64c99a94285054831912060891b2c4d1a866a820c258d52221694f6ad16ac3a442be4f828ca3a15f356a9f05194f9ab44e771d222202d7a2b56529ed5a2d5898e91101531a554280f2e3c5111f81f27223c88f82a9caaa105520a9520b954631e3ae6318c318289d318ebd130f5348725f154a142850738cd93c788891c586937235a8619c46b182241cd65581f1da942850738c9e35a98e913444d1a6a448344c770ce5a470ce8898d1a22421e1a4dc8cba0e551ac33888f34647993268c8f3386719223e83972a9caaa844c993266a3970e6998a6a6c47a941cc8c541562a0e5cb1a8a8db9326a462a8ab11b378dcb9346ad3973515619d44ee1c33b1e3af462a6c66cbd13b4531d4c6e45090c64483542431c78e8ae3b5e8a63b5e5c585153481f21ce19d1ab263,0x1962c4d1963898bd3468c9632e5ce272c4d1a34b4d193264bb162c55193264ce363224313264d1932c589a34c4d4435207993268cc835228193464c963264cd49068d1a5b1131a3468d1b3668c99a69aa3134648193514d193464d19326683162aa7b0a0e58aaa864d193268d19a868d06a66cc993464c963264bd47264c993258c993322]
def c10_4 (i : Nat) := field c10_4Data (7*i) 7
def cd10_4 : Array Nat := #[0xb32bbaaa99a2277956448cdbc6b1ab6719b6698c62d8a6257c5ed7a5e5785b16b5a95c56d5a5655855d565314b5294952147519454f13b4e9394e1374d9354b12b4a9294a1274951c46d1a4651845d164551444d0c42d0a421072f0ac2ac9c26c9a2308b1f07b1e85c16c5a1644c12c3c0ec3a0e42c0ac2a0701b0300b]
def c10_liveData : Array Nat := #[0x8470e0870b2245162a28b062a244891228b162c5062820c0a162a004262c5407d122448818718103060c0d28c180c0040208102040810254a142820a83a2443908e440c6024289104000c00d1c391458a8a2a2301070e02040843c61104308a2c540811228b15020423818000087030e0810c187c60c18081021ac222e428912242851228a811458a8a2c540390a1448a2870631122063908e441110314090a2440c70e42391031408c222c7cc08423910e1c110a14210204440c1000810200040068d45162c58a8102045162c5827513645162a145160953060c182c1020e16485843060c182c8a2c58b162418a890454486083060050a042040c0630f87183010c2c7c102047cc9f3e0810904c222244891224488fa2448911f8910f0a3c29122443911810847221c8870e1c387184484c08428400045162c544891228b151458a8a2a2180c1833030df0c30030c301f0858a21c70875144d44d34d351924c0c30010c33005835965810072161c70035164d369a71a65969c69a69c0011d651659659451419658659628924925965341964640a28a68334d08400514e38e38d34e36136136185c38005201a5d08012390221a8910242850a20800522448470d1a346a21a8911c8a362a245122c5003414508100033e305000628603060c1876298c65becb586760c676314a60421014213184618c633b06318cea60c6339d8052954fa98108421014240888530821094c0896c618c6319c6318cea50c6319cea00c6318c6739c001a94a5294a504210204005021008208142800204001020428500082800a1410612b848c74f4e1c18ea21c662449f3e24482040810204081020418104120800000402109294852222c022088000102108421084010929489294a5224a4421084230849488001081340908964608608600000004104100008230208208024925964925c25c25c25fe99719f597df7df25f7df7df25f7df7c9596596016596e16d34d10596038e385b441041040000a0d96560d6f160030c35805845d86041186575fc58165862cb18618603ebaf186180cb5a70034430d14564c05851456590d86591456051596186430d60d60c00d65961451430c51450c318339c8ec3294a3194a31bf2528cb92d6b39972f2e4a5c0c6300ed9ce476ce723b0c7698dad53f253003025aa2804d3402aaaaa79d60825555554954d34c04d308c3023024920165aa0965534d30134d65825534d34c035348c30c28a2a74271cd5965965965960134d65965965804f8e38e38e134f5d795965960135965804d601359640028a2875b45aaaaa280f3cf3cf3c6596596596435996596435bbefb5965b8e38f175960d34d34160c34d34d30cd5965834d04d0ce533ffffffa7fce39ce7319ace4a40008520080210040108420c600000418c81248000006000000,0x40304001334026c6d9377aa3330c23c73a33c302488b4b44403411023195a8e16c77c13816d1477e857776770024000123400001334400026d26d922261233ae7ea333723aab44403bb4411516366766224022403040012400300012244002030400001111440026c6d6c92c692c20622219022488b4b44400310b2c410b2c10410c124118c18c04320118d18d04420518614618030c29c89c89d89f7df30a7227227627227cc7223030c708252168a1867471ce52171c71c89f3030c03021890c930c30c7222490597df30c38d29c89c89d88739c89f7223030c730200252169628619d1c739484c30c3037227cc5827cc7225a230c30c7220873030c330c30375d75d8883a080d7481041000c004728210d34d10d11d8a034420e10410d12080228182035d5c834d34434d1043602c480a0da82080d08d34d10d34d10434d34411d8a010838410408904124182075720128924f2420820020890cc3d46e140f3cf18640d28a38a39c8897225a20420800000430c018c0c73031cc0400811871c71800420c30000010430c00830410000010820c0000000112230000001111306c6c6c26c27cc1111666757000122200001222200000011084420000000021084210000661982108cc10821098c6efd3f4873dffd96ffc5f1319667ffffb2cc3c208008240f3cf40d81f24a29a29c70940c30c30930c30930c30930c24c71c71930c31f7cc7197df31c6496494d34c33333a33aa32aa33330013336c037c3aa33370c7c337c2aa333c0677777723300120330001333006c6c26c9222660a6c020237c2aaaa3a33c0aa336667667aa2220300122300100223300000111100033006c26c922260226c29922260222990022a33330aa33aa336666666990122200110022200011110020000111111022694a53fffd8c60c67033410f38c6306338183d7023e3183fb2df6313fffd8c60d8c60c6c0098c18c6318c020b1836306318ffff8c63f898360d8318c221055ae718c6258c631896319ce732c633ff6733f3e30e19122449f3e7cf893e7cf9f12205a2447c093040400302001834488f8718183a51830180020818206a93a74e30622443070a42891453e7d12242205a28a887030244021423a244102c38a307910e4238c2206851080838f2245162c51c8508e447910c3028a0108385224488fa26d14fc54314fa2448a2a1411500c1288183060c183000c0093ec22224285103071451f18260830628f9f1a205a24021120428509f3e84f8e1c20587143870e443870e1c850a24488e0e1a70721428510d42890a2448a29f4488522448512244862c5448908e302c00a001018314891228679020001cd1d1e3c720403060a3e81020408100c3e810203e8100c3e31020870e1c3870e1c3870e1c3862cc43870e1a086805077e81020102c38a448871844,0xc6c771c534d324901325375d771971953b28a284dd65974f65d85d75977177164c771c7158604f77176c3ca74f771c7172bd6b38971861838e70514e0c33850c92430134c970570e60b49c71c71c730c1cc3072b70b5552cbc30c1860221249228105428451e79e79e7b2cb27b27b2cb279ecb2c9eb5ec8dc9eb7235741a89a7872d515e55500a51450a44a45450128a01154a528107bc4a294842a842294a5294a55284239542109b229442114a5114a2294a5528e5048454484544811848425294a29542514a551400528a5528a0282108694842f0843de6b4f087a1ad00210c000c30f04f1011060c33cf65974f3ca1097717717544ddc53c5d771768593b3675e75d74f6493dd85d3ddc61d75d5e1946105181adb58b15a2852341f2adb5462c54a0064104005141900096182175e52496172496096189d862761824662d511514514a690d352850d30235f09041f90ca535051451455235144c052850d7d35145141520d44a9511029527493310459659b98659b599d34641d555156482946e60028a64428a28a2476471c16592981d964a60744e2d55285199e854b58a54d1910c74865134511944d144d1ea56952846544650240d0d20c319554d55519555456a1945403555465505695644234234189e39d49d1614b58b2b52d6185c66185c66148df2895d75490d74104106065d45435cd40d01501544a28000a62ccb26daa654507ee5a58907de79d6de79e78c7b2c6f7b279d6ddc5b6ef6c6cf37b26f3cdec9b3164d077375ac70bae00010434d36186184e3a186186186104a28a0c30c30c32ce2cb2071041082012083883882070841041001040842cb2cb10b10b0410c300d34a7627627625541dd79e7623611040031c308e39a7e176236078d85d89d79e61d88d8617481040030c718898b054a9800018d831b0663329f8ea2a5a16b5008410c845906b5902110c04000012004662d6410400304100304620820c34d34d34d0c638e1013570cd38a82134d84d10e0030c728d34482010410086108128128f2420820140d03cf3e128a38a38b1830c420e2011c73883881820c41000c410010218d28420e0cb2c420b10b04108304a046d7e8e8244034403040013400426c6d9733324d83bb488b4b444e031103191a163010c83480463411083881482000041000011040000000441040000821032cb2c41043800c10410cb2cc34a7227627624ca76276281f32081c8830c218930c65f8072c31c034d30b7627627a25461cc29d8a076276234d36035d88630d34d36082082075d79576280d85d20410e0030c728211534d12080d08a06036174834d8208412893c208208c0000cc0c618c4df40f3cf18f18a28e2cb2dd89b75e78a45d89788a38a38a3830c31c80473871ce2020c30c40031020ca28328a0c328a10b4b11622630233403,0xda7947528618596528618618618618613de79ecf3ccdcdd75e75dc7179ecb2c8a5c42535960d69696a9356c9e79ecb3cf3cb33dd78f65e3decf379e6cc01a1b392aaaaa914606518034510e046a0d14510e082071920758d94d56aa91a86555a953d03d041035555515351400035351456779f7f379f7e9a6aaaa5676000c51451851557d57c52ce38e14e38e38e1a79e4aa79e79e782f820be0d1b6db82034d596c30c095c3689bf06ef530c1b5c3c1b51a31b6da31a6efbeaa5b6dbc2a55bbd4c306c95c3c1468c58100c30131b30118c38e20008634141d89a15010a69a41eb77b778b7de18a28a28b7862df7db17f7df78a2de24a049270649f6cc820df764f24375e78c01e7adb5e79e79e79bab266cb2ca5eb5e79e79e7b2394cf3a5ecf37aab6d66ca73c98ccccf3686cde766d34bef6eeae076c8353887d9a20d2023069a46040c58c7d135140069a6856ce1426357e039c608d7580f3a08358358348a174f8a24a048649c24648645f7db38c40478acb745b6d1577df7dd02b2dc74c92060c01c140b2cb00134469a69e78a74310328a29d76c95d3148ec3dd3dd76c0030c30030030e5b2cdaca255234d9b164f1668a28db6da1d9dda1d516f640345149249234a48d3679503929d03a740e09208088e64711149249249249249249286149d4a69924a79e784b4a14a64a7cb275d75d75dc5dc5565922d75d771771772c9d75dc4e75dc72c9db32c9d2ec5b22ce3590002d919919518600000300014514514514200128a38e3a641e79e41e79e7adb699a6554b6955488e38e388041ddec9e51e7958a279eb474101d01d00ca28a34d34d34d34d34334d34d34d34d34d34d35144a3554592945634510c34512915114514515558c000d34d40d34d41001434e28b2cb01428a2ca28a51405434d04d34b5945142da5145186124d762db580576186265c438735861859861648734e85174f3ce4a024609004471c4928454996588628490d34de1de84e61b4473c28480473404a24228a28a28a28a24800124a04928279e79e79d28524928679d14a59a68524a70434670d23a74514834914654659914659654929a69a60d14a084c5993cc59658f3063ccbf0c1a861db6d61c21861861846759d9279a69a1c30d034708745100569069a85a68f8764b7df7df7de27614c780f81ede014c30c3061800051404175c71d078734d34d08540214540510108440786289e7a27903dd86176185d85d75d2431c31c90cf3c024f3e185d76175d0c92490093d9761b2cb2cb2cb2c76176175d771dac75d771c1270e61c70e71c71261c72071c7304ab71c71c71cc30c1871c3b07157d88189f42d12cb55f00d62060e9f438b60e2c561c71c71cc1cc35d5cc35d7063039862f39cc1cac960e3830dc4d30c300954e62060340371cc0bc0b38570e0dc7274b0,0x739ce7396e711ce739ce5b9cec75d8ebb1def7bc471ceef78b5f58ceac19eb9ce73bbd77788e2398b336cb2f7bdec1766d9bd837ad6926d6d8cdef7bded6b05f7bdef779ee69da7734ec13dce0e70da65a18528618613d28613e1820820720712492d7585c71cd75861d75875d61861861861876db6db6005145145558618618859a492660358614d36a28a282186086187582185a1cd410410a69a697b7de279f8b74e175b4d34d34d04f6da28a2b62834460834d2082082b82081c81146039e41f7ed5450990c518d5965970460465537957c94157d301554514b2c538e14528a04a04728a2851474511e645292469b31b6e9befbcc6db5cd35635caf1adc731b9a30d35a6d70094dc71c71ca876db8a286108447645aa5014220821d74954e3964510952c52c57040071c238e6ce4411876cd34704d8624e24224e2da26a27dfc9ed0514038fd2d14500ad3341f7df7ed41fd0dd1eb6f79e7de79500e09f3f33ca35798d40e5f3b5f7db6dbab408400515115114538e3a0af5adcd4e3a0aebd6b618920d5f7ee1861b52ce451d114507a079f6a08118200e0d7526070b820d6083481b7182e02d560e9eb735d452dc2c891c0030c514315c7274a185c2d17d141145145965a69a6183b4820820b2d8204c655554f4845524a95525555554c641041000f0410065535695535545144555555628a38e33601955145125294556db6595d471b65975548f75db17c9dcb2a12b5274d38e38e76cb31b1d75d76cb325f235b1801cd6cd04823139d39871d86186182186185c4a0860876daf81272086181c8020463571e18758753c604064f0e1419a0f3c649c492720861711861bde83481bbdb4514507e0d607e0d70d516df8207e002f820602634474baf45b79f4456db18614539114c3442810002c00ce14b08d0023814e14c92214c821d74924820741324842175248140550d1474111c238669b2cc5d551435041045a41071c3897052c264f74f748249d2046045b7e082081f8208206d17d08207d1811d46181d6e3863c37d16df81f6df040160d61d754070900043161866683d06753c649271186175d76c3dd3c6b1d31ddac74cd8f74f3c6b2cdac596659876d9ddb639c75d71d74d38e75d39d75db2cc9575dcb2772c8e75d76cc98b32772c72c9c75cc1300e56430c6cd40830c68900d0082c982fbd8d7562ebd84106902df44539f7d14553913a0811820d401556189eb635d7445f45b1c579a375d4e2c8d7571c74e59d3a274074e00e38075d7595044ca35134d3030c30c30d20d24920c345249248301248e49144a8618614834924926eaa9b6f0c1b6db6f0c30c30c26c1a6efa8c6d66dbab059b6f0c30c300306eebdb6efbdb6db6db6db6db6da69b6da6aed21875d75319668b1d876c7649a7c430c8064a07001923cf18f3d96597411861,0x1ddb36936b6cdef6cdef5ad018c6312cded8cdef6cdef7b66f7bdef7bdef20d312cdb37bded8cded29f7b5ef73bd1b089ee7def79ec603deb323eb0eccf7accf0ed6f598c99a104bfdef798cf7bcf63def]
def c10_liveHead : Array Nat := #[0xa1a280a1e850284a000a167b02879d80c067003009a80c0a6403069780c025803039480c0a4c03029180c364003058e80c063403028b80c022803028880c061c03058580c0a1003108280c1e0403017f80c11f8030d7c80c09ec03077980c01e003047680c09d403007380c05c803107080c15bc03006d80c35b0030a6a80c01a403106780c059803006480c058c03026180c098003015e80c097403005b80a016902805900c055e030a5600c395203095300c3546030a5000c113a03004d00c012e02804a40c01230300474080119030044c0c010d030041c0c010102003f40800f902003d40800f103003ac0c00e5030037c0c00d9030034c0c00cd02003240a00c403002f80800ba02002d80800b202002b80a00a902802900e009d03802580e008f03802200e088103801e80e007303801b00e006503801780e005703001440c004b03801100a003f02800e80e003302800b80c002803090880c241c028905c0c3011030c02c0c240502800000]
def c10_live (i : Nat) := groupField c10_liveHead c10_liveData 64 16 7 3 i
def rec10 (i : Nat) :=
  let ops := 0x160 ||| (field cd10_1 (10*c10_1 i) 10 <<< 10) ||| (field cd10_2 (10*c10_2 i) 10 <<< 20) ||| (field cd10_3 (10*c10_3 i) 10 <<< 30) ||| (field cd10_4 (10*c10_4 i) 10 <<< 40)
  ops ||| packedLive ops 5 (if i<42 then 9 else if i<3522 then 10 else 11) (c10_live i)
def c11_1Data : Array Nat := #[0xaaaaaaaaaa000000000fffffffff000db6db6db6db6db6db6db6db6db6db6000000ffffffffffc092492491b6d2492491249249249248000000fffffffaaaa8000000000000ffffffeaaaaa555555554000fffffff80000aaaaaaaaaaaaaaaaa8000000fffffffffffcffffffc00000c00000000000fffffffffe00aaaa40000000000000000000f80000000000fffffffffff0ffffff000000ffffe0000000aaaaaa555555555555555550fffff0000000ffffff000000fffffffffff0ffffffe00000fffffffffffffffffaaaa554aaaaaaaaaaaaaa5400000000ffff00000000000000000000000000030c30c30c30befbefbefbefbefbefbefbefbefbefbefbefbefbeffff000000000e00000000000ffc000000000f00000000000fffffffff000ffff800000009249249249249249249249248db6db6c9000fffffffe00009249248db6db6db449249249249200000000fffffffaaaaaaaaaaa500000aaaaaaaaaaaa955555400000ff0000000000ffffc0000000aa5540000000000000000000fffff0000000800000000000ffffffffff00fff000000000fffffffffe80000000000000ffe000000000aaaaaaaaaa95555555555540fffffff00000fffffff00000aaaaaaaaaaaaa55000000000ffffffffff00fffc00000000fc0000000000aaaaaaaaaaaaaaaaaaaa5550ffc000000000aaaaaaaaaaa9555000000000ffffff000000000000000000000000000000000000000000000000000000000000000000000000c30c30955555555555554000000000fffffffffff8ff0000000000ffff00000000ffffffffffc0ffff80000000fffffffffffffffffffffffffffffedac6c8dbbbbbbbaaaaaaa999887666655555555554443322200000d6db6db6c9248db249249000000000000000eaaa95555555555555554000db6dadb6db6db6db6da89000000000000000db6db6db6db6cc924924900000000000000000000000000000000000000000000000000000000000000000000000002daa079840b186]
def c11_1Head : Array Nat := #[0x565b80596e035dac0576b015dac1cb6203257c1c15604ed4003b5004d5280354a00d5280354a02cd1c0334704bd0402f4102b4f80ab3b00acec02b3b00acec0a938029cd402735009cd402735009cd402735009cd402735009cd41212f027cb009d29026c9801b26006c9801b26006c9801b2602648c0192300648c0192300648c019230454740931a02445c0111700445c08f14003c5000f14003c5000f1402344400d1100344400d1100344400d1100344400d11041c2c10305020408300f00373b405ced0173b405ced036ba805aea016ba80d8e701639c058e701639c058e701639c058e701639c0d6e4015b90056e4015b90056e4015b90056e4015b90056e4015b90056e4015b900d4e1015384054e1015384054e1015384054e10153840d2de014b78052de014b78052de014b78052de072b540c8d207032413ac304daf40b4ba00d2e8034ba00d2e80b2b700cadc12eb102b2b80aaab00aaac02aab00aaac0a8a800a2a0028a8029a94026a5009a94026a5009a941209f027a7001e9c007a7011a96006a5801a96006a5801a96006a580989300624c0189300624c09690005a4001690044a280908700421c0108700421c08e84003a1000e84003a1000e84003a1008c8100320400c8100320400c8100320400c8100320400c8100320400c810421ec086780409c8002720201bc0006f0001bc3005d05715c0da540169500d8510161440d64e0159380564e03512c0544b034920052480710fc22a330678a81182406306c00c1b060048300000]
def c11_1 (i : Nat) := groupField c11_1Head c11_1Data 48 13 6 3 i
def cd11_1 : Array Nat := #[0x2889de559123388a11801895e559561575594851d46515394e1374d9354d1294a1274952448d1845d164551444d12421074150340901164390d42909423]
def c11_2Data : Array Nat := #[0xdb492448b6db636d9000d648db6900008420f4a0000000000000ffffffc02cb2cb2cb2c8200000fbefbe8c6318c631318c610840b6db6db52000ccccc88888811110aaaaa400fffff00000000000ea55550004104104104000089c104fffea555400a698e28a28606430c3082000f800041041041040cf3cf3cb2cb295555400aaaa800088888843333211108db691000000cc11110000000000fffc00009877533332210000fffaa000fffffc001c3870e1c3468d1a0000000020c1feaa5554ffc0aaaaa800fb6db5923648fffa9000999992111111110095000000db6000000000924924910000fe555550ffd55400aaaaaa00ff00aa800000db6db6db2480080000000f3cf3cf3cf3cefbaa555554fffcffc00000b6d9236d2480fa95400091b6db6db6d8aa54000091b6d2449240ff80fe00ffe0aaa55400eaa95554e000c000db6db6d80000b6d924900000ffc0ff00ff80ffffffffffc0ffffc000fe00000000000000e37de79e0e375d75955524914408618618618a18618618596586186010408888777722211110888866666666000034d34d340036d75c2f964fff9999999988888880feeeeee333322000924892249200ecccc11111100000886666666600000028a28a28a000f3cf3cf3cf3cffeaa000db6db6db6c00fe00c49249240000c6317bdef7bdeb5ad400a5555500fff55540b6db6da49000aaaaa000186180000000000000ebaebadef7bdef7ad6a2a314a086065349248a28a28a03cf3caa99999888888000ad69494a52939a708400dbbbbb55555550002082082081041040c103efbeff00a49cd5ad6b5ad6318c20febba33211111000263870e1c38000810204080fdfbfa9555500ffc0a5294739cc63167000008ad08420e73148108000bbbbbba9555555009999999777621000aa955400e000c000ee99963332200000db691b249240adb690000000edddcc9633222000feaa554088555555500000001861040c2081000efbefbefb95555500fe00f800efbefbeeea633cf3c1000000010204080fdfbf7efdfbe7cf9f3eaaa00000e000dcccccccccccc320bbbbbb3332100000eeddaa9875221000a4e739c6318c2031800000000000000042850a142142a08a035d75d75145e36d61000038fc01c71fef3c2fdf3bd30c1c202c5c080421806c2c5c3830058b036daeb287dd041077db5d01000000d75d75345145db5d2dae99e492491c64d30c145000035d757d9440037db5d75d74f7bdeee2d493ce42108034d249245000036d33cb2919208200000e38df7b269a69a195108208208103ca1deb9e79a5555000a555555094a5294a5294a52794a0ffb0000000000000a52939ce6d2042000000003e0c06eb5323305478f83060c19988888666666600a9999994443330009246db6c0000040000000017400cf3008144,0x40810203f7efdfbfa9555554fff8ff008833333333330000909249240000aa955550aaaaaaa0aa955540ff00aaaaa800f800e000fff8aaaaaaa0aaa80000aaa80000ffffd500d5555554ffe0fff0ffffff00fff8f000f800aaaaa000ffeaa550fc00000000efbefbefaebaebaebafff0fe00f000ccccccc551000000dadb512492408db6db6db6d8ffe0ff00924849200000c000fe00ff80ffe0a9555550fffeaaa3333333300000fe0003ffffffffffffefbefbefbeaaaaaaa8fffcfffefffffffcfec924848000a5554000aa22111111000000a9555540a91249249200f000aaaa0000924924924200aaa55540aaaaaaa8c000842108406318c6318c00fe0000204080c18303060c183850a1428c63084210820a520c60aebaa579e5d61040c304103faaaaaaa69a6055450e1c100048a28a28a28002baebaeb9400c3000ffefbed6f91d75c555000000030c308608208165553cf38e38e380000000000cb29238e38985d145138d3481c0492492100fffffffffffefbea69a6179e6955134ce20704018614504104003fffffffff59e69950206db6db6d34d34c4183060c0a140008102040810203fff8095555550db6db6d89240b249246db680db6d9b6db6d8b22249249240fff00000924924924000db6db6b6db209236da488000db6db6240000dddddd8881111110000fffffefbefbef7df7df7d8888777777777770cca6543333333300aa98877322100000db6b6d00000000000000c1428409060c183060c1ad294a528c4a528294a0a52937318c6318c6300092884208420840000000040000f3cf3cf3befbcab9e69a18604d249228a28a28a00003df7df7df7df7df3cf3cf3caa955500ff00ffa4912492008888877600000000d246db6d2400fffff540ffea40008000924924900000fc009236db692440db6db6d88000db6db6b48000041041040000f7df7df3cf3c98888888888700009977763333311000db6d92490000f6d8d2491000aaaaaa888875111086666666665555501c71c71c71c7082000ebaebaa9555550fc00e000ff80ffe0924924849200ffffa550892491249200fb5b6c8db640db6db56db000b6db21249248fffffff48db6db492000db6db6b6db60ffffffff54000400175f8e38e29a28a288e3deed5ad5ef739ce70000041041041041000034d34d34e94000008777777777721110db6ad9249248fffffe94ffedb491a448ff4912200000888777777777100099999999988444000c000003cf268a181f71a69a386cd9b3668d1a340000001060c1fea55400ffe0fffefffe924924924200ffaaa540b236db6d2248b6d9248da48891b6d2400000e0000000d5b492248000aaa95500ffffe4900000b6d449249248bbaaaa77755500000408102000000000000008102040f800e000e000ff00924924848000dab6,0x86186171659659600000000028a28a28a000000f33cabaea92484924920095550000909249249000aaa54000800095555554924924924920aaaaa550d6db6db6db689999999988400000000f32cb2cb2c30befbecb2c8777777766222000fffb12000000dbbb333222222100b6db6db6d0001c71c71c003aeb9e79e79e79fc000000a5555540aaaaa500feaaa80095555000f800feaa9554aaaa000095555400ffd55000f9555540ffffff008000aaaa8000ffffea80aa555550aa000000e000ffc0849248000000aa555554d9b249000000000000000004a5294a52baa6655500000000fffff92492483cf04102a9e679e75d75c71cb6db24909000ffe0db6dad649248ff806596596544c30c30008a1861ff6db6c49200366cd9b346800080f5ebd7af5ebd99999322222222009236db600000f800ffaaaaa4fa9555549246db6db6d8fd555000924924880000a5555540a95555008444444400000000fffcfe00cccccc777722000000003df7df7df7df7df7df7b8888888884433330b6d692449240ffffaaa8eaa55550c000b1b6d2492248fe00fff0b6db6da92400fff8ff808888888880000000fffff000fff0e000208208000000000000cb1baece60f4a52810842104201861041041030c1041040ff5c6baaaaa9618618613409240000000cb2c2ea9f7df7df7dedb6d6400000098888888772221001c71c6186180aa99a69a69a6fdcbbbbbbaa99990ffea5500fffeff00aaaaaa80fffffffcfea5550045145145144e340000f7befb8888888888843300924924448000bbbaa99999000000fc00e000c000924924900000a8000000aaaa8000b6db6db52440fe0000008000b6d6d240000020820410208208003aebaeb8ff00fffffff22400924924924000fff8aa99665553333330c000fff8ffe0fc000000ff00fe0095555400db6db6db60008332222111111110ff00b4441111100000000001c384e9d3a74081c386481041d6b59c8842104000000071655555334d340000da597f9ce7391cc6208421082082082082081349240a28a0009e79e79e7861859659659040dadb68000000a8888888888222200c3000fb5baebaeba98e38e3b41ef7bdef7a0000000028a28a28a280000000f3cf3ca95554008888888000000000d666622111110000b24924921240db6db6b6d000fff88888333222220000db6db6c00000aaaaa55555511110fffd550000003df7df7df7df7cf3cf3cffffffffffc0cbbbbbaaaaa99100fe54000092492420000095540000fffffffd1248f8009ce739ce6e739ce739c0000000000000000002040810204095554000fff0ff00db6d80000000fc00a9555550db6db6c49248fffdb6da36d8ffffff00fc00aa955554b6db6d2480008000b6db24800000aaa55000ffff0000db6b6da49200f000000000081020,0x348008dd71c71c71c5534c3000f3cfff85555111100009cc63108421042108400fffffffd0000dadb6db6da00aaaaaa50ccccccc661111000000000f7df7df7df7df7befb8c631630c5294a518c6091b6db6db240f5400000dddcccccccccc000aaaa5550ffc00000ff555550fffffffd2400040000000000f7dc71c71c70e739ce7394a51ce7202094a5294a4a51084000001030c1041041040a638e38e3699659659659480820809f3c71554514002db6db628a28a239ce739c19ce739c61ce41ce739ce108421002e840f3c804002db6db2cb2cb2cad54a52926318a528420ddcccc1111111000fff2492490008421042108421021080018514514104104000003fd6f9e69a27153809a699b6db6c5041000000000034d34d34d34ab1294a0e42108000000fd555550ffffaa80fffcdb1249249200fe00fd2492491200fe00fffe8924924830c20804104104104103cf3cfff88622111110008c631842010840000000a5554000db6db1240000f0009ce73739ce739c0000000000041830604081020408101ab598888855555000008777772222222000ff808a5294a52918c6108420082081041041040000000cab]
def c11_2Head : Array Nat := #[0xdec8220f5c0107ae047bd60239ea811af5010b7a40833d00215e7860af240be79005ebc700f5e38178f1803c78c1183c206a9df834cef00a4776011bbb0289dd033cedc09d76c04e3b5026dda0036ed008f766086bb10231d80018ec0202758040bab0c05d2827ae8c03d74605e3a200f1d10176e8413873e0d8b9c04bdcd044ae58123728011b940679c8813ae4011b71c0cbb8b0455c48226e1c01370e0493860a09c08102e003816f21593740c0db70630da03066c4181b5c0c41ab0620d4031e6941823440c659f0606ce030b6641c1b2b030595027eca01b964a0da32206b98f8352c701266340d0b1706698a032cc4419061c101b0a0c0d820470c0022c5f810b2f806417a8704bb82ae5d214d2e40a1d6f860cb643065a61832cd050165817eb281b858e1182c306a960024eaf8124578051abb067d5c013cadc1965680c82b1062957060caa0238548117aa006a54e8344a6821852c1082920c25460282a280c051205fa8802f943817aa181b950609aa8106c53f03549ec1a44f00cfa75047139832c9c01904da0c4a6a0c2132052097c30f4b20a025708e129836294012c49c0d224b067524003a920210488103a400c111d07048cc14046205fa3002f917817a8b81b945609aa2906c113035688c1a744009221e06790d823686401b4320ca216063d09840883c38241006020700fd03817c8180bd40a05e20406e10083607f81aa3f60d21f80a4cf982207c43053d60219eb0ac4f300627981ac3c61101df0460ee84127641063ae1819d104fce7862c7240953901879c204fce0027a6f82353740d79b7088cd982406c421635a0899ab0440d4870468814034005f99f04f4ce807a67403c33a0d919a04bccc044c6501243240ce98f0664c6022a628112310088186023cc2821a60c18730018297a0100bd007e5e803f2f409e97800f4bc007a5e00bc2ee01e17700f0bb80785dc1392ea0d997204c0b803585b41292d60d29680290b381465980a22ca0901630474b0803a58409c2c004d95f0654ae002a5700152b80c81590238ac011a55c08c2ac0c29530408a881025403012941909440c809f04304e821026c18193008e49604544a01a624a10c12108408e860c45c13f22a0dc91202e088836443829a21208c107045482832040810e2001840fa0a9c7a860c3bc2381d614c0e6082c7106063700bf1b61520d6085469070432c13f19205f0c80aa86185302f820b1741010b605005a017e2cc0be16401e8b208bc5703522ac1a415010b0a4044c51041627830513009f09602f44a817825030111c1c088704f442817821022f10011207c08583c05041cc3810d81858660c1030070016430a0a618584d0c2c2386161042a00781858360c2c18060e0a813e05009e0260aa810842a0742810301c081108e406845e02419600c1880000,0x69b6b8607b44230d9a14eec8065b628321b0810ed801016bc0c0b5b0559ac41a6d5c091eac085b540227a98110d48086ea2061b4f860ba64299d28143e8f0c0f44860da0c304cfa14c6780a7b39862d9b42adcd01106640667308513970303cac185e500c3f25055b91412ac86093e41029720004b90019fc7a04f63c065f1c812d8e018fc6a181e2f08c315853f89811dc480cbe21025710050586c382c28117610089b06004d830099c161446060c1b0006217e8306be80d65f104aaf7834d7b0124bd4051de9047af38335790117bc40c8ddf081eed860d754229ba20d15ce0856e5032171c309b8209fdbf04e2de826d6ec133b72098db702c2db025b6d012bb64094db0049ad702476b0120b5404fda90476d38235694118b4608b5a10256d0012967c190b3800859c043acd001d668188b2e14fd92089ac7033d62c30fb0a0d35820292c0833d5f809dafa1825770676ba07055b4236ad20d956602c2b2825b58c12aac20d355e048eae033f56411daae00ed57046eaa803755401baaa108551023ea8011d53c202a9618154508d6a083614f812da7809553a02a69c83494d80a3a6a05153406769881394c009ba5e109d2b044294811f4a008ea4e006d270c16908531470303a2c183d100c1e85033f41c216a06187cfd089a7c82473dc0239ee04f4f602767a82373cc1189e208acef004e7786053a42359ca0d8ce2089a6f014b3740a49b8051cdb067e6c023b35811b9a80cb4d1044e67812533818d996182cc500f66281793101b59820d8cbe02c25e844d2e4026972052cb802925b80472dc02396e0514b6047e5a013d2cc09d96400ecb200765902372c001b96000dcb0065656841b2a408c950100ca40e064e853f26030392415348d0c1a4386312041908fc10347a0c0e3a05211bc3068d20a046708e231845717c1a68b80d0459027a2c042d1501908a2008451081a26820712c30388a0dc442089a1f02470f019f87208ec37065a1a012b0cc28285c1c1427050212817f09003f84801fc2402fa1183710800b583e09841d06aa0d034705c12082a04fc14047609003b04819881e00b40f025607032102c010816087409042e0383070100828061c13fc04fdfd007efe803f7f405f3f900f9fc817afe003d7f001ebf800f5fc046afd01b17e2097bef04b5f68254fac0a97d4093be80299f38048f9c0a37cc0513e50481f1823af8411b7be08c3dd0455ed802af6c0947b4049bd9004]
def c11_2 (i : Nat) := groupField c11_2Head c11_2Data 16 15 7 3 i
def cd11_2 : Array Nat := #[0xaaa99a2277956448ce228459a629895e9795e16a56959561575594a5254851d465153a4e5384dd364d5344a9294a1274952448d1a4651845d164551444d124290841d0540d022687a168590e8390d42a0a42508c1a]
def c11_3Data : Array Nat := #[0xa53b695521b135e53b76d0dce9b2a4bb4856ad494eda22366abd59d3a53b76e5a24446e733972a54785060bb4a9121b37560a4466ead4992a5498f0e0bb48911a0366cd152b5ebcd9b0929c3854857951e0c1769121b375ebcd9b2e2253856bca8f05da4486cdce951e0bb486eaa4363a6cb8472bca951e0c17690d9b9d365498f05da43656ad4950511b353a6ca8f120c07aed21b2b2e125af5674e951e0c17eed224446e74c951e1c17690dce951e0c076b521b9109e355b2e13c6ab52d5748eb95af34ad71a54ad79b24ad7aafdca2672de355a96aba4650a55a925d23355cb16ae5a695ab529b93454a95ae5a6c92b56a53446abd57ee5114295e5cb78d5aad5a966c888719cd57555a3ab524c066ad19aab529c94680d15af5ebcdaf569c98cacd572c5a6d5a712b829b364cda94d5a235362407b5eac07e8a6c4972212d4b55d2b4650a55a925d2b4668a14ab529c974dd5a34068a952852ad4a74a4c6568d01aae58b572c58a95ab5299a2a56b962c0a6959a54ad72d36495ab529ab4468a95af55fa22852bcb97221425ab52cd88f204d573623c9709e354b5633a4650a55a92603a668cd55a94e4ba6ecd8234068a952852ad4a74a4c680f59b04680d14ab529d2a3263407ae9ba34068a952852b962c56b962d34ad7ab4e49a2850701ae5a695ab529b9666a6c42b5cb161b34ad7ab4e4ba3450a0903362159b10a95ae5a6c92b56a534468a4d8901e959b11d372b362336056bd580fdcb3455e5cb8509e356a966c481362339b12ad49301d333556a539319d3766c0d15a94e9498d01eb360acd55a94e951931a03d74dd59a2b56a53a5468498d01eba6ecd81a2b4e9d3aefdcbc972213c39019ab47524c066ad1d4a72603d66c15a34056a53a5263407acd82b4680ad4a74a8498d01eb360ad1a02b529d2a13e4c680f59b0575e6d7a94e4c67eaeb962d366d7a94e4b2565a6c4ae0a6cd9b366c99b529ab45362407b3623361355cd893623c9b2e44484f12c26ab5aad6ab56c25b56a39666abbf3850a1496d56ad383212d84b6a892c50a142c509967f2d6cc86e5a8a2d09ac8285a5b59930a162c58a969709a94985264b8509aadab5111a555dfa22850a162c52b564250a162926014948a5b55b31d14a650a355a94a4c86cca14990d9b02858b142c52b56a650a1692559b02a8a5c25a50a4c9850a1466c0a4b84d622584d4857ad547d6ab5a43c6ab52cb90f0b16ad5aad494aeb55a94e53760aea53a529eb0567eb55a94e95194f5bab3e7ab55a94e951a129eb7607cf15af5a9d3ad4eb57ad56a53a52a2407af5bb056a0ad360ad39f4af12ce972213c4b29dbb775ddbb76ee53b951e0bb486e3c17690dcc951e1bb486ebcd392a3c17690dd79b11da436ed21baf3621c951e0bb486e54782ed21baf3a54782ed2162ce5e254455eb7,0x79b26b54a72a3a2355eb54a7262447a8909aaf5aabf4688856ad2a3c1ad560ab475aad495260c0568cd56ab529ca93055a34068b151756a53a52a4c682ad1a03466bd7ad045d7af585ceaf5eb16173a6ceaf5aad3931e32b3466ad38e66bd6ab529d295263c488fd5a34068ad7ad2a3c158585829b366af9b5a54783364cdad529ca8f055a234666c480f6bd6a94e9498d1224280f582b4468cd7ad560c07ead1a2175aaab173a6c46a725c884d52d6951e0b4ad563c682d11d6ab525498301a33466ab55a94e54982d19b04680d162c543d6ab529d295263c68301eb4508d01a3258b15ab5295095260c07ad19b04680d17af5eb4782d03d7ad29a4e2d5c957ad2a0b42c1e74d2d3abd6ab4e5498f05a1a335ebd6951e0b42c1e74d2d3a396af5aad395263c16868c969d36216af5aad4a74a6ca931e03e7acd82f4680d19243e6d6951e0b49b2a4c7ad529ca8f05a2234666c48301ea82d3623466c0b57ad529d2a12634280f59b03a68c97af5aac68301fb4668d107af5aad4972a4be68cd8a3435eb55a94e950972a4c88f1a03d60bd423407454482f2444693a6c45a723c78305a3458b2a4a95260c180fdcb468cd92c58ad51aad56a54a72a54a931e3c68b060bf72e1bb468cd93160c162c56ad5293464587a515fbe64c57aa52a0256ab52a53a74a952952a5498f1e345830603f7cf5eb970d9a3464bd62c56ad529509cf9f3464c100e12b55a9529d2a54a8d0a14254a95263c78d160c180fdf3d7ae5c376cd1a3364c58305eb962c54a131f3e78d19305c80b115ebd79109e355a405878f05a2caf5e54168b2bd69d3abd7951e3b4595eb4e9d5aad49d3a5ca8aae9c78f060b868d18ac58a4cd7a92e52b7cc54d7a94e5ca90f5cb860aebd7951e3c1595eb4e9ce6bd6ab5274e972a2b8574e3c78305f3868d18ac58a4cd7ad56a53a53a74b952223f7addb3262c15d4a74a5ca9109eb9567ebd7951da478f060b4695eb4e9d15956ab5274e97298d7ad56a53a53a74b9521f3d6ec17ab54a4957a94e94b952213d70d982e567ebd6ab529d2a34274e972a4427af1bb160ad5273e7abd7a94e94d972a549911e3c68b120c07ef5e3970d9ab466c98b05eb562b54a5428346458764c57a95012bc782fda2caf525ca82f9a3158aebd4a74a5ca93223c67ac159faf529d2a12e549911e13d60bd62b3f5ea53a5427cb95264478d0a03d6ad19b0507eb55a93a74b94b55a5395aad49d3a5ca78f1bb56094e56ab5294e9d2e5ca910a13d7894f9caed1657895ebc782b2bc1595e247595e5ca5ab12a4375562b488cdd79b5d624375e6d79490d829d3652caf3625794b0dce9b25215ab5252c5688d9aaf5674e94b122237395d782d2bb4af065ca78eddb5689521baaedd34488cdd79b5ddbb6890dd794d124d2b56a4a72d19a4355e6c4aeed21b1b3,0x8cd55a725ea0355cb162852bd5a6acb14ab4e4c680f55a3406abd69408a14ad2a3cd935a9ca8f05c2b446a6c480f4b57ad567478301116970a6c497221253854ad69d2e5478505db55a96b55991e0ba568eb55a93254982edd33548cd56ab529cc95263c176e9bab548d01a2c58a95295aad4a74a64a931e34180f55aa4680d55a94e94c952634156a91a0355eb0d055e6ccaf5a74782ecb16af32b4a765a7162b5e6cc2a54957ad39d962d38b15293a656aaec74c2b5a5478332b55a94e54782a8d15af58b07af5aad38ead5070310ad7ad29db52c2c157ad566cd991a2c174cd92b462e715995eb4e951e0bb9b25515ad56a53951e0bb56a911a9b1203d2c54ad7ad5674782fdda22c58b4c9936644833a0572afd92a355ead4446aa2b446abd7aae2bb2ab518a2355ebc884fde355a40587aef98cb90d569c2b5a3d6295aad4992a4c374cd11a2956a4c95261ba6e88d56ae54a56af30a94ad5a3d6ad1ddb45828314ad5a3bb70d161b322834c875a396990e056a71d0cc8652b162858a56a650a4c8650b14295eb55a94e6cc931e1ba6ecd82a528909a2850906aca8a57ad5664374a4d14875eb4e952a3bf72951162d0cb4b6ab664369321bc58cd5a928529948f321ba2931d37294e33d5731d37292e4425a70ad68f06b4782eca56ab5264a930e0c076e99ab4468a56ab529cc95263c382e9bab4468b162a50a56a94e94c95263c6870603d5688d55a94e94c952634382ad11aad5ca94ad1e0bbaf30a940e1eb41773a396295a3d79b322432a52b479c58a4e990d994ad4e3bb29321d68f04b4c86ceb538f061b3615ab4782ed60f0c52b56a71e3c17cedc2c526cc8f0c52643ad1e0bb9458a4c8f0d994990e0b36058a4c86cd816af5aad4a74a8cd99324c6870e03d74dd9b056a911e341ab415452b54a7324c686f559a875eb4e8f05fb94458b47865a64366c25c885321c1992e44384f161c9d321bc6acd825ad1e0b4ad1e0bb6956a4a930603b74d199aad56a53992a4c782edd3768cd81a2c54a56a94e94c95263c68301eb466c0d56ab529d2a33264a931e34180f5d376868b15ab52951a12a4c180f5d3768cd81d355cad68f05db476d27579b30a92ad1e0bb6938a4ead4e3c176d26568f05a4cad4e3c16932bcd995a3c16938a56a71e0b49d30a4c9932bd6ab529d2a3426cc952634480f5d3766c131a0f5eb4e8f05fbb72d0b4c3b3a62591224428509e3c6ad5aad5ab52a54a405878f05db4583c506af58810af5a3d7af5ab55911e0bc76d5a2d58ad2a44658a8f16284870c16bd6ad1e0ac48407870d5eb47763c6d7ad1da56af5a3c176d160f141ab56ad1e0bb68b078a0d5a44182f1e356ab56a54b59aadad2244268d16a5ad2212dad09e3558b12d684d451688d2b4a8f5aaa3ad56a4a928cd55a92a4a3406abd7ac42bd6ab5a54,0xa24280f900e12a52a542849931a2c080fdf3d66cd93160bd5aa50991a24280f9d202c452a13e2bf7cc98af54a54261010190161c5d780cd5a32a2c3d79b16033568ea4b93159ab4715fb262a94a1161c807af36033568ebd497262c066ad1c57ef993154a50900f5ea53a5365c9911203f7acd93160ad1a02a405d79b1a2c066c95a32b525c980cd8a3af529d29b2e4c880f9eb360bd5aa528d012af529d2a1365c9911a1407acd8b056a91a0555ea4b931603356a62bf7cc98aa535ea53a5365c9911a2407acd82b50890d7a94e9509b2e4c88d121407acd82b4c8abd4a74a84f9b2e4c88d0a03d6acd82b4276a4b92b55a54682a4b92d59b04a8d054a52e4c280f52a340f1aad91096c278d5e3590d56a53854ad69d09e355b5a615ad5a6569856b4c9854ad698d274298b274b78d56a5aae91d7af34a952b5e6c92b5eace90e514e675ebc8161eac884b6135ad555a3af5ebd705366c9af5673f44fd92aaf56a39355ebd5aecaad472ccd579109aad201eb4a8f5aac7ad58a57aae6ad5a850a14ad523b85b0a4425a94e152b5a74884d56d6985664cad5a6569958ad6990673598b0e4e975a5c26ab52962c54a169956bd778403d6aa24057ad558966ab613597216a53854ad69d2e5478709aad4b5aacc8f0dd2b475aad4992a4c37ee99233452ad4992a4c374dd923406abd62636bcd995eb4e8f0cb16af30a95285abd6951ca942606bd6ab36643748c5cc875a543ad56a53951dfb2626ab55a9321b26282bd6ab3664374ad190af5aad499261bf7068a14990ca94af5a74a8658b029ac8b1528c4a4c8654a57ad3a54d9254ad6ab529ce951dfb262ad11a8652bd6ab3a6437efdaa22c5a62d4b3664486f164e84ae54783563c1568ead495260c072ad19aab529ca931dca34068ad78f06bd79b0ebd5a726339566aac0ae0a6cc87321ca9b266d4a72a3c172ad11a9b1203daf567478301fa29b322436b2214885222426a94e152b5a74278d56d69854a569854a4c2a505d6995eb559b31d23141ca94ac5213c4b320bc9cb664884f1a25393a5ad9709e354b55d23ae56bcd2b5c695af36495af5673f728a748672e44890d529c2a56b4e972a3c278d56a5235aacc8ee9191ad56a4c9525d33548cd16ab5264a92e9baa4680d57ac481579b30a95255eb4e8e58b11215e616ad56a4c92e95233530a91af5a74a8e466962b5aad4a72a3be72cd5293446615235eb4e8e58b111a58a942d5aad38ea4b11135eb55a94e6cc952644474dd93154a51a03454a91141ebd6ab3663a648ca952242b55a9324ba66c519a98548d7ad3a54723364aa2aa6b55a94e5477ca94a234448d7ad567477ee56a22c588907c5a65699325149b32234233a1339722125ad2a3c1295aaca93060334668a14af5a3c12c5ab4a2c52bd68e58b4c295eb55a7263b8566aac980,0x85090fae3c34d92a8a94ab529c57ef9c3256a94a23468c8f0d5ead4a74a6cb931a23a6ea111a2c58a9529529c6575ebd7ab564427efde355aad2a34488b162c58a14203c7070c16aab2c52bd5a94e94b93211a03e68b14972e44885096ad96b529c97260355b2e125392e4c280d59abab526cb9311d376a951a03868a149709e354a3c555748ca0f1c284d59301fba72cd92344684d5ab56a5493264c680fdd3a74e5c376ecd9b260ad523468d1204068d1a2c58b162a54a94285058a1356a52a5264c68b0203f7cf59b364c17ab54a11a2407cd0fab56ad4a94e952a5464c9931a3458101fbe7ae9d386ed99b25ead528468d1a24080f9e3468d193058b162c54a952850a101e3ab962c58b14203c58aaf55d334656b962c58b14162abd59b35d232c58a942956a4b9315d33466abd59315c2a3468c96283858a1206b8fab34b152956a4b93019a33556a457ef9cb364a8d0faf56a539b2e4c888f5cb866c101a2c54a572c58b16284078e1b5eacd9b19d232c58a14af564c57ce9c2a3468c962c5080f1c240d7ab529d29b365c98911fba6ed99234068b162a54a141f56a53a5365c98d121407ae51a03450709ab3603a66c91d5a94a6cb9301eba6ecd82f4680d55a94a8d09b2e4c280f5d3766c11a0355c78a9b255152956a457ef9c325488d1a323c557ab529d29b365c989120407af5d3766c14223458b152a507d4a74a6cb931a2427ae9cb766c0d15af56a53a54684d9b2e4c689121407af1d3766cd8304c88f1a2c58a0aaf5ebd5ab2214080fdfbc72d59b35a951a24458b162c50a101e3858a135ead496f99a3af56a53a52e4c87acd823407cd16295ead4a74a84b931a1407ac17a34074d192c525cb8509ab596f1aa5392e4c06ab65c24a725c9911a14066b6ad49b2e4c45a951a03868a147ee592a3556a497ee9cb86ecd93160a949a3464587a515fbe64c57aa52a0255a94e952931a2c07ef9eb970d992f56a94a84e68d193040384ab52952a3428498b01fbe7ae9cb86ed99b262c17ae54a131a3464c17202c4572b5ead497262ba6669c315266bd497260335669f31535ea5397264467ae5c3360acd57af56a4b931603a70ccd3e70c5499af56a53a5365c9911a2407ef5d376ccd93160acd15a94e94b932234280f5cab355e2b22b56a4b9301d33626abd5a94e94d97264407cf5d3766c17aa5268957a94e94b932234280f5c3666c172b355ead4a74a8d09b2e4c88d0a03d78e9bb360ad51aaf5e4427ef1aad202c3d7a92e4be66c4d57a94e94b9321eb3606abd4a74a84b932234280f582f5668cd7a94e9509f2e4c88d0a03d6acd8283464bd5a92e4ad5670d55a92e4bc74ddab36070d55a94a5c98501e9c352603f66c95aa45524c98d1603f66cd93160ad5aa528d121402c3d4a74a949931a3458101fbe7acd9315ead5aa52a11,0x5498b0603f7ad19b262c17aa5098d171629fb24515fb262bd5284c88ecb6b2e542832d6b964c1552952a4c78f1a2c18301fbe7ab162b54a541f3464c04a5424c07ef5cb666c982f5c68c17102c58b175ebce85060bc6ad1a2d58b0e0baf5e7488f1e0bc6ad1a2d58b0e0b0f2e2b964a98a9201dfb25515fb262a94d7af3a7488f1e14182f1a345ab161c201ebd79d2e5ca95262c2830603f78e5a3466c96ac58ad51c34f98a9af5e74d972e54a93224478f1a2c48301fbf7af1cb86cd1a3364c98b160b562c56a949c34643d28afdf2a52a0257af3a7488f1e2c28305e3568d192c587080b972a549830603f72d1a3364c4d57af3a6cb972a54991223c58301fbe7af1cb86cd5a3466c98b05ebd62c56a95293868c92174a2bf7cc98af54a0857af4a74e9b2e5ca95264488f1e345850a0c180fdf3d78e5c3668d19b262c17ac58ad52a509cf9c3464c108ac98aa522c3bf64a85c57ec98af54a54457ec98af54a5426a115fb262bd5284d2d6aa96e5ab2614a5c98501fbd3461aadaf2d68796d642d0f2e12c5a94e2c0f365a538b2bd59cb122336b162a36a96070b2e5496b2e13478d529c68d2aa465365bc4a71a57ab39d34488cdb476d193416265caab29223406a125395eaa4466e0c17e6a54980f4d57af5613f4a911901d5eacb9525ea44680d4b94d56c884b6135122ebd59ae91d5af566ba4626bd59ae99232aaabd7ab09fbc6ab52a3442c4cb930a02d96f1aad4a28355748ca0a12182d592e9cb364ad52344684d72c58b16282c5070d566ba475c3559a58a94ab524a33556a3f72c98aa52683162c52bd59ae91962c50a0aaf56a382c58a09af566ba648cb162a54a140d56a4974c519aae2834d92a8a94ab51fb864c55294468d0a0d5ebd7ab564427ef1cb55a951a24458b162c50a0b14243860b2e5b56ab56cb5a94e4b932234280cd6cb78d529c97261406acd5c980fd9b256a9155a9264c680fd9b262ad52946890a0341c8070f5eacd568ead4928cd210e1ebd59aad1d552403d7ab529d29b2e4c888fd931568d01a215eacd8cc95a32b56a49668cd57ab529d29b2e4c87ccd82f54a51a0344955780a4d3f7cc98aa535ea53a5365c9911a2407acd8284484d579109aad4a403d5a92e4b566c12a3406a5c884b528f0d555a3283c7060b56ad4932603f74cd92b56a91a34468d14ab56ad4a94e4c9931a03f74e9c3766c95ab54a51a346890203468d162c58b152a54a14281c305a52634580fdf2b54a54223e12b962c58b14203c386ae58b162c52bd574acb162a54a142c58a57ab35d2b4658b14283ead497262ba568cd142956a49568cd457ef9529ab529c940687559aad1d5a94e94d972623f568d01aae58b162c5080f1c0abd59b3634574c95a32c58a140d56a4d9725d233450a57ab529d29b2e4c87ce9baf54a51a03458b152,0xec95100efd92aaf2213c5a70807af2e13f78b4e579109e3538405bf6468587542da1468b2bd68f5a64a930d9a2351da3158a5a2caf5a714af5aacc95261b84468a568eedc3462b149b3219d37155eb4e6454a56ab2a4ba66c511a28e9cb86ecd93160a8c8b1429ccb94b65b5af5e5c57ca6bcd9111931572a0b3635e43360bd4928af9ab01f5aacc95261ba6ead11a2842b4782ed61b1e1ab4176b0dd7ad1dd96295a3c176b0d86af5a3bb295aacc972a4c586edd335688d14ad1e0bb70b149b32187c782b2b47835a64a930e0c05688d4782f9629ad325498f1a1bd5688d57ad1e0c782f96293666bd6ab2e5498f1a2437ec95a2343ebd69d160bb6496b55972a4c180edd22355eb55992e549910df3b74dd9b05ea94a23448356931e34180f511aaf5eb55a52e5ca9322345870a14180fdf3d78e1b325ea95284470d1a326080f1f15fbe54a540faf5eb569d223c78505fbc76d56ac365880f0e1abd6972a0be5688dd7ad325ca93223c37acd82b446a5ca5a725c29725d376ac0d56ab3254976e9bb466c0d56ab2a4c78d0603d34405c176d0dd782eda151705db4375eb4776d2acb95262bb74d199a82edc34626ccc1695eb4782d25ca9306034666a0be68c6bd6992e549911deb970d19b034420bb686ebd69d1e0b4ab060417cedc34626ccd7ad566cc972a4c88f11fba6ed9a326268b15ad2e549911e3428301eb9355e0b4655eacb952603d76e9bb466c17aa355e5c9850603d6ccd82e355eacb952614180f5e3a6ecd82a354a2bf7ce5c3664bd5284e98d193042bd7ad3a4478505fbc76d5a345a6c80baf2e5417cd19d7ad325ca93223bd68cd81aaf5a64b95264478d0a0c07ad182f3a6cd19ad565ca92b4e1a1628587161c386162850a16285070c2830a6ab64478eb52c758d5a344ad050b142abcd382abd59a70a8a142c54b950a0a5161c5d6475eb559d351d7ad56549351d1a0af5aace9b1d9232b5aaca92c519a4682b4754a5fb262a94b262a948b0e1ebd6aaad19c2c1c3d7ad566ab472e2c562a94d7ab1e0ab47560c05284807af565ca93223c588fd93156a94a34480d07af5aace9b1e345830192b46705d6ab2e549830119aaf5aacd972a4c880f9eb05ead5294680d19255eacb9526446850603d5ead5234068cd68f0554b8aa62bf64c552996c1422af2e549911a2c4850603f7ac97ab54a54264468c87552dab0615aaca931e34180f54234068c8b162abd6ab06034668cb15162c557ad566c768cd1cb8b15931542abd6ab3a6c78d060344672bd6ab2e5498f160c0668cd56951e2c17ef9a315491096203ebd6ab365ca93223c480fdeb466c98b04680d192c56bd6ab0603466c91d7ad565ca931603d68cd93160bd5234480d0b155eb55972a4c28301eb360a9423406a3c169162bf64c553095263c68301eb466c141a3342,0xe0c782b23c15892bd68f05d941f5a3c176b0d8faf5a3c176b0a8fad1e0bb586c786af5a3c1589034884b56a5395a7355b0a0a5395a7426b5ab56295ead6ad5ab42af203c884b4e57201ebcb84d56a52d2243c5ab52a50c1eb16290c3ba461c356ad2a3c75890356ab3254986fd92b466ab4a8efd62a52910868cad5200d5a394af5eb55910de2d569519c0e1abd6ad56acc95261bf76e99ac569119b3454a56ad2a3bb486cb16295eb559d0e13a648cb56ab2a4c37ee9931466ab56951e3bb586c356555eb55990dfba5258a56951dfbb70c98ac54a4d9a0c1a43c6ab55a5468834c865242dad325ca86ed29c6b565394680d470f06387af563ab475654972ad19a52843c78242bd59d1e341788eaca9301ca3355eacb952643e72a94a3406894782aabc980e549a7ef9529af365ca93223c68901eb9508909aaf2212d4a403d59729ca54680d15202eb4782eda1b1e2abd62959db4362abd68e54957ad1e08f175a3c1683ebd68f05d941f5eb488f0a0bc76d12a4386cb15284078eaf5a3c176d0a8f155a3c176d0d8f155eb4782d120a9109abc6a94e569cd56c88f0a0a5395a74884b45d7ab35d23ab5eace748ebd7ab09fbc6a951a216265c9850050b14e91ba72cd923455ab4a8f1da24235aac7235654966a919aad2a3bf68c98aa4886b568f1dda43658a11af5aace9b323ba4646ac9355a3bb7090d992919d3a70dd9b262ad52346890a0ad5ebd6ab21e3a6ac92a3382c555992a4bb74e5a3364911a2366848aad5a5478eeda1b222ab475446aba355a5477eedc3464c551b346450a90f1aad4a8d10aaaa9acc972929c8cb47d68e5880fad06a95295a396295aaca92cd19a425a4c0452634580ad121215df10931a2c07cad1213f5a090ad1e0d6972603334fabd6952644780f5c33608909aaf221355a94b101f2d295215ab4a8f1e0bb486c7d6ab3254976e9bab548d01aac42bd7ad2213c4a70a94215ab478f05dbb486cb14203e64aad2a0bb7690dd7ad5674176e8b57ad32547255ab4776ed21b2c52bd6ab3a6cc8eedd2b475aace992e5498aedd33548cd5676e121b295a64a8f047d6ad2a3c7830520fad565498301523355a5478b05fbe54907d6ab325498ef5520355a3c1203abd6ab1e341568ddca8b05f2a486cc901d5eb55972a4c788fd92b548d01aad05d901d5ebd6ad5644785060bc76e9925488ce1b2a5080f1d5eb55972a4ba6ed59b05ea91a0355ab471f5eb4a8f05d8fad5a5478f060bb363eb4e8f05daaad2a3c582fdf3b70c951b34647d7ad5674d992e5498f1203d76e9bb360a94223456b4a8f1a0bd555eb4a8f05257af5ab559d3a6488f1e1417ef1db55aad2a44688d96284078eaf5aace992e53e548cdd7ad5674c972a4c88ef59b056a91a03e6a5c2972929cad3a64b9525aadaf2213c6a7080b2b5e43c6ab4e0b,0x2ab2555eaba4626bd574c919554c952d6aceaab4680d07af55596af555a3ab2e2ab466880eaf5634547565c9466abd5972643e54a51a034495457ef95293466bd59b2e4c688a111a2b5ebd59109fad56951a22038385aaaebd59726423407cd4b5b2e4c281565a54680e1aab25d3766c11a035564c07a8d01a202c5d7ab35d23342c4d57ecabd59725eb966c101a203abd5748cd101d5eacb9311fba6ed99234068b5597261407ae51a034fd91a9301eba6ecd81a92f5cb3606a4c07ae9bb0355ebd58501fbc6acd2a32038589af565c97acd823406abd597261407ac17a3406a5c96b2e4c281565c94680e1a141ab3b686c55676d1624365054768b2b470c285568eeda2c362830a0d21aad911d6a539216bc76d5a2538d6ad7ab39d23135eace74c919554b6bbc0e2c7861e3c32d4b092d7ab351d7ab355a3af56732465555790d568764aa4425b5e5c27eb52d79109a907ecab57ab5ead6acc9895201eb4782ed61b1e1abd62a52b57ad1eb3b0d1]
def c11_3 (i : Nat) := field c11_3Data (7*i) 7
def cd11_3 : Array Nat := #[0xaeeaaa66889de5591233889ab66d9a62d8a6257b5e9795e16b5a95b56959561575594b5294952147519454ed3a4e5384dd364d5344ad2a4a52849d254912346d1a4651845d164551444d0b4290841d0540cab26c9a22c7b1e85b1685912c4a0ec3a0e4350ac2a0a42508c1b02c0a]
def c11_liveData : Array Nat := #[0xb7c11777ccc772cccc7c7777bbbc7117cccc222220255520477488004299eeeee999999ddee433ee9995eee999e5555558888888211133366636663033336663663633333331666666663106631d5cdd5eee76393939395177288222882288202224405770770040225288225828582200220000222222223353513516881881188116811115113969333302111133333551353135168818811881168116118811681115111020111111136966666666eeee696eee66ae6955ddd559d5559d992982c2855d55d5255999555555999500995855ddd559d55566aeaa36a93d6e663936e63666663aeaaa636a6116a666aaaaa3a0696666e6e6e66ae66666aeaa6666663aeaaa36aa661166666aaaaa33a66066666663aeaaaaaaa36611000444240077007704040400000070070007000400000000003663666f6cf3d9b676db67b06db3b6db66760db6cedb6db6db62366aeaaaa76666aeaaadaaa766666aeaeaeaeae7069999899999999989999999996266666666bbb666bbb3bb636666bbbbb63b66abb0b3333b67733b06666666665355555515555555557aaaa5aaaaa5590aaa255558aa4a5835aa05a8aaaaa5583b66abb0b3333b67937733b165656565636362666622656566253666360262654441434437797595904343444348837595994837554990111248988981599944aaa37b66ab0b3bbbbb666a37b333333b6a7a3a7833bbbbb6a83baa52937700003233333033283883388383811222023333033030013302593688333028883683833302110221715966969666650600330012333000013300222722255813388338328838339028833114128822233023303001233003000122333002030000113330259259772221723692888883683833390288111217159559696554060886aacacc1ab006abc230055af0001557c20325972597722251290125772220717772592772225712901777772236838333023883388833888338114114215959559655055077001222000011222200000124a48000024925000000124924809224dfff89240a4900404924000492024800012492120000092492ba4ad1d2ffa4a8388e7104e739ce23884701ce211ce211c4739ce539ce739c894a5299cd3398c60488a73a5279ce694a6739a460925239a5f314e69489279ce694a6734a5339cd139ce694a5339ce7318c02114e34a4739a46300d3398827386739a4691cd339892948d294a4631ce699cc6318d3311c21386739a5294a673108f39cc2739d42108021096a529455a6731084229c42108a739c42114a73804210842294a70004210842114a52800239ce739ce1084210102308c842042121020234908421021d088a252948eb4a52939d2949ce94a52939d293a652942094a65084a1039ce49ce733c2739ccf03c0ed6b5441808300c00,0x885853444442880999ed9999dd533655555119333331677033333610303999d999de99e6e4eee4e99d999dee9ee9999ddd544e369966666335066e5ddd9d9c3e61777377773366770771333666077137cc77cb777bb2c42574ccbcccc7c77bbc4d25dd8855599955dddd8cc888388884747888448c888c88c8a88444448810c855999507a25888066a42555551555a5aa54a5a5a222222a405145555141455519959555599955555889919382224455055185539999d899de9e8499e4444780808c888cdd8ddd8888cc43d22588c888cd8d87dddd888c2883444444477748811119935952133333637391033336663709d999dee9e94e49999dd54436996666a36066e315e555888d9d49e849999599955588999935599ee9e9eee99e9eee9998cc3853667033637088ddd88888d44777748824482888ddd888ccd4825dd88d555599955cccc888884747888888448444888484444778884082444447774888419935959955555588888885199322222444420551855399999deee9e999eeeeed8888c888cd8ddddddd88d48c8dddd8888ccd25d4440444474002884488441223339363663137099999deeeee94e9999ddee9436ee99eee6666aa6a66eee5d9d4d4444444777027c0277787877802070282222227888888844844444477488025222442550159999999995825455555925255555555999eeed899d39999eeee9999999eee55555558859999221135952333333316303966639a36046ededdd99388b3884dd8dddc7dd77d4774d77d888884488488844444774888848024444448885599913595595555588885888913222224442450159999eee99997b9eee8ec3677777777ccccccb5c77bc7777ccccb577bcc550322232370330622223333248888ddd8ddd8c7ddd877dddd77d44444444487748777744410021252222225536609666aa6646e9deee88ddd9959dd9dd4aeeed8886599959999558899999936db7b67ffff96fb6dbdb6db7fcb6db6fedb6db665b000092444444401999eeeeeee999999e9eeeee99d9ee99eeee99deee9999ee9ee99de9eeee9933333331336663666633100666aa6a6a6e4ee63693693636936936933333333333630b63615155331333333933911233333363133333333636661636696366666666915333333333c04abababab6aa3aca04aa6aaa3aaa04a6aa2ec45995595558891224455099949959eee9999dd4355558595221333163035999559995558899991555588599915522222444455500999e49994e99994eee9999ddde3355814444427774928880499eee9957eee599eeee9e999ddee433ee995555588598885921133366366303360eee869999959999559999955588999991555588599999159525555588888885299115952222444444445500999eee499eeee9997c7c72cccc7777bb,0x1552155553579244488794904445792544485879494904478581555955945525555513555034340021311183503790411111116272778887474421878888744285101122222110300022222242240234433377336704454448845454444247774200888144447548444788144442477728850088145475144555544424777744488500100011101447788888815555514ad04a412109202a954500514838002cb014494aa50506a82501522200000002222222516591334451659133676939396913336776939033661677039336770133443336701114411101331044405275924443444974724879490449777814944442477727720088179949425459559455524442955135545444424777477501794944478034340034001818350379040001114894444427778850741616162767776323777887474421449779774888814955555112550124804924a48828a0e000ba4ba59602954a0a0d50a834929042002010d34802aa880514414838180c062080000052a9520122203250250150005165913333336673516591333339676993933661667055813134411233335339993336666705513329313333339666930066706935165913335333966769395581393134415133323333313966391663077069393913333966696661770311113331411013311333314401111013333333114405449529455244442135544444424977494545777720179494244497779775257719444444249777497777774545200179420343400673403067018350379040000004447478444427774778850744444427777774288500741616166667763263667763636323339669377770391111211303113311311022110000111111111101330301800064921240924120b0c06c06180c00004920036dbd8ec1b71bdb6c1b6dbdb6606d836dec766c365c6db2f6d9b2f66c07836dedb6d8e0db6dedb661b6cbdb32f6d9801b6dedb6d89d9b0db6d97b6db6db36c01008000049fcf04917fe7e24917ffffe2e049245fffffffa0037b6dc37b6db6dc36f6db70555530075dd75d544cc30c01d5d74542086006030c06000192c90000000000000036dbdb66db6ded9ec76c4b6db6db6f3d9bd8e7b16c96db6db2f6cd96c07b66db79ecde6f6d9e6d97b665ecd81b36db2f6db6ccb6366dec76ccb6db6db2f6d9b7b66036d97b6cf6cde61b6d97b6db6666300366666663666666663366666666ddddddddddd999995858599959d95559d999dd993e793e9999959999eeee9e9e666166e3040228c8d8d559999996ee9555554447770277778771c2002222248844848d440222ddd88c38c888884747895959d99955599d994e693ae8599599eeeee580411288238885c8dd899999585899955599555959995555885291935222442550551855499999de89e999d9e85,0x25b2496d565b55125b6b405a25b25aa092492db6d922800000004b55b436d36db6e38e49238d472409b6da6db64a49245248929269b6d369b6db6d36db924923b65965b2db2492d924b4482002c02cb1c9224924e496472572da286db92391c9648db92492dae50dc92469c7124938dc61b6040cc200000000049244724b247256e50db72491c92400016086cb2d91cae496492b925b688c944925292449249b6e396cb6d124b6d915a0000000016b69b71b6db6e49231200115554596505559955aa51506650565b6cb2596d76c1439246e492392596492db450db72472492db050e46db72470a4da6db6db92468b1207236186c00201113090000db9248db42401811c924724b2c925b6b6db9248dc92492c96db24b6c858125b6d31c920824160140800100b0000092596c34492cb6db2486d82db2d95db244db6db8936db6db6db49b6db49b6da4db6db6db724924b25ae80e491c924924b5c02372372492492492496db0091b91b89b60596d92b924b09b6d92db0c4ad6db91c90071c92491c9248ac8e392492d924b6b76ca046dc924924925b25aeda0392492db64a037226db6db72491b46012492d624b6db6812496db1db6464810cb6db404db4a48a26a48944924520c36d2000000104005020000000024b6ca4492db6c92522cb6db6d9036e4924903724924124924b6c8e4925b65b5db68724924925b6db6da2492496db6256d12472496c96c923724924b6db1db2242496db6db6b0e46dc91b9249190e49245230dc9249248d900000000000920480502000500096d96c92db6cb68925b6db6db2320092db281006c4024020123b68968144a1c9240e482460596592492492c92d0e4924965925b2892591c9236d8924968924925b5b7237248e46db6e492168989450292496cb5ca1496db68924b6d8e4709b408dc9249244cc804b6571c6e4b217249139228946db2001648dc92490c80492496db64924925b6d6e4724925b6ca2496d6ed9436dc91b72392492db6c8e4894b4091b7248e36e485b9098cc5012db92492364c82dadc91db6db6c9100a4522922512480000000000005b65960100120900900824001000024100820000020820028028140100140028140158024000000000820140a04028004028b58168004800b4011c104145a28b44103800024082805a00000000000820160140160800a2d16802d100820a2d140103800005a05104812004000000000804828b45168145a05000120100902008000249200000000000000000000000168a28a2db4502472492492492592492492db6cb2816c924924b659249244454555555450055344440444445555544554400440405500445554555055888888824444884444885444858450441511118511748585555522255022220022222222225165914444114455499944478,0x1b6dc8db8e36dc8d36c36e36e471481b6e38e481b9220240da6db6db7246c061b01882300071b9248c491c6e49204db6db09b6d86db6e46db6db9199206db91b6dc8d48cc81b9248a40db8dc92091482492301b1181040006e472481b9248d482391c6e49206dc9226db69c91c92392492496db2dffbbfaafaaeeb155abfeaeafaae815514154155aaaa95155596666aaa559aa9a69b69b6d34db6db69b6dc9248e391c8e465b4db4dc2502496d269b4e371c72569c89392592492d685a1b6e49244dc6e20db08186125861801100124920392c91d7248d576c96b54ba1c92c9249248d59636dc8dc924900028b0472d72c72d8e190596c92db2d3689]
def c11_liveHead : Array Nat := #[0x6087406086806085c06085006084404283c04283406182806081c0608100608040607f80607ec0617e00607d40607c80607bc0607b00607a404379c06079006078406077806076c06076006075406074806073c06073006072406071806070c0607000606f40606e80606dc0606d00606c40606b80606ac0606a006069406068806067c06067006066406065806064c0606400606340606280806180806080805f80805e80805d80805c80805b80605ac08059c08058c08057c08056c08055c0605500605440805340805240805140805040804f40804e40804d40804c40604b80604ac0604a006049406048804048006047406046806045c0604500804400804300814200804100804000803f00803e00823d00813c00843b00803a00813900803800803700813600813500803400813300803200813100803000802f00812e00802d00822c00812b00802a00622940802840802740802640802540802440802340802240802140802040821f40801e40801d40811c40801b40801a40811940801840801740801640601580801480831380841280831180851080830f80800e80800d80800c80800b80400b00800a00800900600840600780a00640a00500a003c0a00280a00140a00000]
def c11_live (i : Nat) := groupField c11_liveHead c11_liveData 64 16 5 3 i
def rec11 (i : Nat) :=
  let ops := 0x160 ||| (field cd11_1 (10*c11_1 i) 10 <<< 10) ||| (field cd11_2 (10*c11_2 i) 10 <<< 20) ||| (field cd11_3 (10*c11_3 i) 10 <<< 30)
  ops ||| packedLive ops 4 (if i<9 then 9 else if i<964 then 10 else if i<6467 then 11 else 12) (c11_live i)
def c12_1Data : Array Nat := #[0xaaaa8000fffcdb6d8000000091b6db6db6c0924924492490ffe0aa800000c000fff0ff00fc008000924000000000aaaa5550ff80a9555500f000fe00fff8ffffffc0ffd55554000000000000000c71c70c30ffe0ff80ffe0f000fe008000fffffea4b6db249236c8aaa9554092491b492488f000ff80aaaa9500aa555400f000ffffffd0fe00fff8e000fffcfc00aaaa9000fe00fff0f000aa954000ffe08000000000000000000000032cb2ffaa5554ffc0ff00fe00ffc0ffe0db6db6dac680d6c6db6d2448887776655443310091a4892490008db692489000a00000000000b1b449000000]
def c12_1Head : Array Nat := #[0x17f3056f103670016700736d0716a06ee702e6604d6400d6402ce302b6202ae100ae102a60029df009df067dc046da006da026590065904557024d60245500455003d502354041d2040500c04a037c9017c903748036c7016c7016c7036460164601646035c5015c503544053c2070bf04fbd06dba02d3902cb804bb604ab400ab400a34029b304831027b00272f026ae0262d0062d025ac044aa02429023a8003a80232700327003270422502124020a30c01d0579b0371a036990361803597035160721306e9008a0c067890658606303060000]
def c12_1 (i : Nat) := groupField c12_1Head c12_1Data 16 11 6 3 i
def cd12_1 : Array Nat := #[0x299a2277956448ce2284600625795655855d565254851d46515394e1374d9354d1294a1274952448d19461164551444d12421074150340901164390d42909423]
def c12_2Data : Array Nat := #[0x59b25cb54273464886890ddba72e1bb364bd72d58a54274c910a03668c98244480c0e19cb76ccd8a84264c1615121c076e9cb86ed9a3364c57ae58a9427488501e3668c962a488901e3050988e9c325eb56294e99222407cf1222403844e9921f3c0a24074e1b3464c57ad58a93a44480f9e3a70911203c5040501f3a6cd19315eb562a529d3244680f1d38488901e382c470d14a2362838488e5a33508500774e5c3764a54274c91121407cf1b3260b4074e5c376cd19b2629d324448501f3c70d993058a028901f3a72e1bb668cd93152a13a64880f1c3664c16284c5070b01f3d6cc98a74c9101f3c70282030dca14068c91070dcae5aa139a324434380e59b23464b111e24486070dcb364b96a84e8501a32443438709cb96ecd92e5cb562b509d321407cd1a325c891181c3040701cb766c98a84e99221407cf193058143870a0c080e5cb76ed99b262b962a509d2214280f9e3468c972c54891203c60a1210182870e14080fdf3e72e5bb666cd93160b972d58ad528509d2a4468501e3868d192e58a94224480f1c305090e182c07cf5b3262b562a4e99223407cf1d384480f1c342820301f3d72ddb3364c54274c910a03e78e193058a130a0808a0e10384890ddae350e1395c688ac0c0e1c384e59a842688b2629d3203f121c274e182d585c484890ddae426a1ac3e40483890e14180edd3970d592e56a93a64268b91190e14180e9cb86ed19b05a84d172224386890ddb75c9cd0c8709cae50688c4870a0c076e9cb862b95a84a9101f345c88b890e0ba72e1bb466c162a50951a1345c88c890e14180fdf3b74e5c3768cd82f5cad4254280d172281931589d3203e44844870a0c076e9cb86ed59b05cad4253c64c111905ba84a84ec4870a0c07ef9dba72e1bb568cd82f5cad4254270c952232243850603f7cf5dba72e1bb466c17ae56a5425284624486e1a325ea51213668c8a121c304070e243850603a72e181a2e588c4870a0c07ce9cb86ed19b04a9109a2e50890890e14180f9eba72e1bb466c14a84a78d17264480e85060407cf9ebd74e9cb870ddb3468cd93160b562a52a54274c9522344890a03e78e9c2c4480f1c3428202e9ca944e9cb86ed19a28709d394484d9a2e488ba72d19a9510e13a72bd72b52a129b345c911870a03a72d19b03668b9222e9c345ea511b86b909a8709cae50688c38505cae5668b9118321c28301cb766c14254268b91870a0c07ee5bae5684d172230643850603f7ce5bb360b95a84a68b9118321c28301fbe7ae5bb360b95a84a848c28301f3d78e5bb360a12a1345e244883218988ec63b870a0ad5045db5191040c76321c10cd463b6b1003b1831d8c763223b72321c28284c9176d59b018ed72b18edaa84a31d8c890d92d33121c28301fbe7ae982b4a84b1566a1db542edaaf76e9c3568bcd92,0x86e572d509d0a03464886070e0396ed99b2628501f3c68c962240789060a1c07ce59b25cb55284e9119a3258a94223c7090c162385ea511b2430386080e1b95cb54274280d19221850472cd9284e8501972dd9a84e990c470d17a2364860a12101c376e59b25ca109a19121bb74e5c3766c97ae58a94274c890a03e6cd19304888c080e0396ecd9314280f9e3260b0288e1a2f526c90c142438686e]
def c12_2 (i : Nat) := field c12_2Data (7*i) 7
def cd12_2 : Array Nat := #[0x2aaa66889de559123388a116698a6257a5e5785a95a5655855d565294952147519454e9394e1374d9354d12a4a52849d2549123469194611745915451134490a42107415034089a1e85a1644a0e8390d42a0a42508c1a]
def c12_liveData : Array Nat := #[0x920124924924824200144a24924a28104920000124924924824821040000000144928a2412400490482410800804100804100000514490492000000000000000000492400000000000000000000024924936936c24924db6c24924926d00d24936d249249229b68b6806d84924db6db2db09249369a49b6c24914db2db6806c24936db6c96d26c249248a6db6db6d241b0924924924914db6926db40049b6d24924536da6db6d26800924924536db6db6db0024020030d000009248b6d36824922db6db45b68049248b6db6db65b4004820820d86c06c06000d80c00d80002000000d36d34d349b6db6c34d34936db6db6d84936db6db09249209200a48000a49008000925249000004929201000004924929008000004924924000004924925255056d490a6da95b5216da8db6db55552541b52b52b6a56d2492492492db6c002d16cb6db5b]
def c12_live (i : Nat) := field c12_liveData (3*i) 3
def rec12 (i : Nat) :=
  let ops := 0x160 ||| (field cd12_1 (10*c12_1 i) 10 <<< 10) ||| (field cd12_2 (10*c12_2 i) 10 <<< 20)
  ops ||| packedLive ops 3 (if i<211 then 10 else if i<870 then 11 else 12) (c12_live i)
def c13_1Data : Array Nat := #[0xcafb6ca689e69638a17de75c6996175955134913ce34c2ca2481c61440c2040cb1c2fbadb2baa9a2792381e6d84902c6]
def c13_1 (i : Nat) := field c13_1Data (6*i) 6
def cd13_1 : Array Nat := #[0x299a2277956448ce2284600625795655855d565254851d46515394e1374d9354d1294a1274952448d19461164551444d12421074150340901164390d42909423]
def c13_liveData : Array Nat := #[0x1ffc]
def c13_live (i : Nat) := field c13_liveData (1*i) 1
def rec13 (i : Nat) :=
  let ops := 0x160 ||| (field cd13_1 (10*c13_1 i) 10 <<< 10)
  ops ||| packedLive ops 2 (if i<22 then 10 else 11) (c13_live i)
def c14_liveData : Array Nat := #[0x0]
def c14_live (i : Nat) := field c14_liveData (0*i) 0
def rec14 (i : Nat) :=
  let ops := 0x160
  ops ||| packedLive ops 1 (10) (c14_live i)
def shift9Data : Array Nat := #[0x5800300ac30b103d804001438804580c60ebc480]
def shift9 (i : Nat) := field shift9Data (7*i) 7
def iv9 : Array Nat := #[0x19791bac00065c06322a32466dc1c3e1640b9f7ee250406d00ae454e8ac8316c9d19a0188021ef254800000b802be1a864ca8503bea09b3991f80b88b2f1d]
def rank9 : Array Nat := #[0x401010004400000000]
def pivot9 : Array Nat := #[0x100]
def rot9 : Array Nat := #[0x6366a]
def key9 (h : Nat) : Option (Nat × Nat) :=
  let row := (h/23 + shift9 (h % 23)) % 71
  let v := field iv9 (row*7) 7
  if v >>> 6 != h/1633 % 2 then none else
    let p := row % 32
    let f := field rank9 (row/32*32) 32
    let r := if f.testBit p then field rot9 (4*(field pivot9 (row/32*3) 3 + pc32 (f &&& ((1 <<< p)-1)))) 4 else 0
    some (v &&& 63,r)
def shift10Data : Array Nat := #[0x31e8310d80c0004f30001018011977fdfcb037f291b7a405c408cc0f8340dc129c4f2e50980f1500b001026cc0405c0f2000004025228010062c000054e8fd0044bb640604c041a002204050143b978ea0f80607c9c26803040020100e0f4dc0946f0087322dec07b280341623c03180430248905c202b40200c02068170040e4224500c4d17c0100c37008810080000c24d6855003ab12f2427313008671e0090000db6c7b0840537c020100a014000005a018982480c00c0204c04074030e0de03c030300005c741600609c020b1b313404174000c4010b85309c1a01a2e00c020300910017008180600d00c04000030201a0082f000541500e0180401341530331900a000000004f0102825050010030280100c0003c02000013243c0140195455000061000400012024000940fb681203407000001e0010e4100640d0000300c000300000c0000006022b30bc041e42879c010242d107ad1141900c2f07800]
def shift10 (i : Nat) := field shift10Data (10*i) 10
def iv10 : Array Nat := #[0x79c4e6a8001065db248ab1f427b9dee0800b50002bbe93001b3cb14fbc7607f0a190e558ac628552bcb284c5cd9c53e31da264f695aadd33e3a5f0a82023db47d42e60d964e0b571ebf7a512b87bd5556cbf0001d946f73a7245a8681cde100063ee5df60008422ea3335951d2106b078ca4fd571a09c5034cef34d0721ec753d74f218036b8c98d6725dac00840f8009e7945758a1c419ea74494cbf804b41ffb9601022c6e3ab510fbe3ed4f8f34f1688461e0b1cd79211f98d038b3fbe990af6532b693c54c27c6794b6f4a9c9f68b96b057932158f4000c956f17c0019bc9cb0f9209742f0c72b20033342a0006d01411e3030d6b402989743e7b5243031e981df51ca58ef9ad5c63cb31fb19024a9562da08070c8490004c9bb2b317906761a5a21c83ac5a8a9ff15cc3a656f73d83f8df852bf2aba3442013566169d29e1a784e74ce4454f4ce32d82eaab17000a8649e16cba5aecca0f4ea820540a0ddca2871f26aa249d152a94cf07682e9d47017c4675c09d2796acbfe2b240aa4bd836641aff04600621ab26d6b0c68744a09b2cd3b590387d4a413f2272859c65f1ac4d16d8bd1208cd5a830404f0aae51c0785146402939f18611156d8d07a412814bec3951a2ace99558d163605582e5aa547dbec1e0c99a4292ba5c12f1c811b49602ddfb47a82b456db091cd04856905b36841adceb5d0f75c4a186b908808e1696658cd319b52c15151a5c78b1bdfd3ce06485e2197fa9c7bac8d0d73053d2c2a88495ad5aa7f9e72a68e5fb6a6ee82d1990b882aa1a5f2ed70906afe4fcea302155a8e098189834ec30afc66d6f10f0b23b2b06d159a1ccac772a06a450736d09f3c80c530a7ee4eb71445911b11d845d0a407ae4d7e4816f4d50f4d4273518e2e9accd0cef8cd1d62622c98c9be644579d488b84a0b4e0ebc1b6f831c32fb09e18ed52547f37cd48381600f3204be13e57920a11560b5d023a7d0ff180b88fe8d8ae638d510e6e54f5cf824c9f31ba349ad755725e11829e53fdba6289b9c2342acc0a71f1d29637a81113c6e35b8a98a79fcb9447d0040005895af0816bb61bdf138284d493e49c745d1831b748c08862be78280ee0ab158584c771a06ec9692553843694074a12036565fbaee9d203ca402c98258274137604ec6191083f70d86ab2c50b3b5834463ca615fec3372598a841a486000d53c938b2a54d9103c069ee47ae5a6ceee2554851b9aeff16b0b13612a186139936290698356953465d8809b41b42d377891781c9bc5484dc31c1f18ba503b41bc636cbcdc939579db26a904877070c8b12ede1347472c002bd988738c74fa34b4b8ee7309e2acb41457099c89322dfb744ee13c6308237e0a8ff12c8b472df1d06b9ab71234732acd6ec2d02448114a3a615d543ec939eaf33883ed7d5148e43add3c448121d,0x77adc84a04a4987e0e124d48a41a5b181cbe4243d51b297151312cb9141c63112305290ae82508bc0f7244caad189d49bcb6beef9ef13119aef18945caaceb28c3b4b340d9693f42a465d3aa4723edaf0006f1cad9d628bfbbef78005c84cc4e0005dd29a819734db164e62560da5b0a0132bf0b4075e6284223cdb8d5497b80f101dc580f186471e090d4a54023d2222c9088107214128bdd42140adae234899ecda431337428ef1cacf099490de5b1c8af50000c52f34fe55a5e8f73770a01993ebd2700012e42db2b0139cb4c18c92e0002d4245a23b4f38e4a9774c21e68dc25d00054300074444ec710f118000a362b0fb82a9dade69e90d4f00128b0fc4230b7a27613149436d64000280a26ccd16000196030b322678eb9cd6dad85c7186cc609180714290f6500026a0911256cd3430eaec644378344ac2a0eeaa679a885b0df7b517f0add22590006e3666512db55500185591e9596a0016c8afcde8a364e5abaf973202652d80eaaaaa888194cc59bd91d7bc0055754d19c00444a9a1e673c2fd99adae60]
def rank10 : Array Nat := #[0xc43020806284d082003604286188000000004018d410203000201810080050aa100504010002402236100400000800424083809280480802420908b806808000064402204009900040040404001c0002000002081408308c0000440000244002869201a0c01002000083421012181020080028000010089d80406044051200110]
def pivot10 : Array Nat := #[0xafa8a097948e89857d79736f6b635e56524b46433f3c35332e24221b16130b0600]
def rot10 : Array Nat := #[0x9794997777b487996672647b9b4436936192799579476b74668689a9692a95766696436786363766976679192639769729799793996bb75631986867269969b397799297993691979b6667186626679476687782729329799]
def key10 (h : Nat) : Option (Nat × Nat) :=
  let row := (h/283 + shift10 (h % 283)) % 1031
  let v := field iv10 (row*11) 11
  if v >>> 10 != h/291773 % 2 then none else
    let p := row % 32
    let f := field rank10 (row/32*32) 32
    let r := if f.testBit p then field rot10 (4*(field pivot10 (row/32*8) 8 + pc32 (f &&& ((1 <<< p)-1)))) 4 else 0
    some (v &&& 1023,r)
def shift11Data : Array Nat := #[0x2004e03d009002800000700b057801800c00700d824600601b003000003599e84b412e060015800016e00000e863800600403c002c0940f8003010010600200080d8017278005814c04239e05e82bc346000013005169c0ac00000000760020190060424004000803c04c543017002400e00107f00b8158004008dfe00cc3ab00308a40100a700000045d400700400180aa1650048004010025000000005202d0298472430015009805801800500c800400000c00301e400600344c01200f001200080f4008000000003c2a600d035000c09801a00003cc01a00b01a805808e003023803800803e008000000a0095b000841d20f6001808e5f403400b002c8cc0240208050000250000c02b06640270054001001800401380000058002687c05f00040040024042008800900540190078017004800a0004005002c02301100160ca000c00900020000097002000701a000000940060000137007e246018800300a0015010425701c4001002000200d8004015409d00640f2011001c07612d013011c00c00100185e404a0bf0002d1c02602403880bb5f60240a8047000400b0038614424019013e30001c08d001013000200a00300300880b50061dac000000007907002803d00d80100080a300080140a000301f4fcc052004000000000a000010400f0014003003c02100a801d00040038b3c0070000003001c04200e8065013800601ec0080408005004000600000190108068000c006000000d000401d0020002002808b00180020268002000400300f000500a8018426c00700300010234001003410e01e409b013000503f8002001802401400b009803003a0a402083240000000070234000009ac6802c00207100900401ae011112009000800a00b80280020250001594000003005820021c01300a08600603d101816c817003796f851001600e0213cb4034007000800801800702680300046700050004001400074880b2000400801600200158008001c0010504087000001b3f300620008122001c015003001506e400400dc809005001c00980000040005000c025016000000a80010008005012c05700b0004000401b8a940030004055004c000008c01905a80750050082000000800700050150001002003b00040030005a33055dba5004177300800200020004000000e00b000000a0000030cf69000c00b00500410024001003800e002cd53000400200c98a2000407c01d001900000068bc8001001c000003800d002c0560238094000403d00b011d5744013000800001a80480a404ec1980540f800000f000004a00500500a400212300280300ca000089008c0b41fc05e0064004085000005c034004058807800600585b013406a0450028d1402a25b011826800601e005008c0320000050018009ce201305fcfaa081e5125d0034025,0xe0451d606804801029b882f8000d005c9283e0c4008fe813000000000000005b9050072953105000007e07a94180240440730be00d40003a4008017c052000064178404200b007802c01200c000809004a0ff00c01000001d30350268004005005006c1953cb000014034008808681480200a001080080da0010240ccc02601e0008005006c0095f94041093420900e802809899aa00140de0010004000c0410018048001000300c007c03ac06c0028019001c009771c07e000a3330728000012c00b07400063b90139000002700040cc00480120c7801500000340ac40330139047004400e0000083000c00e022c00b007036c004008000000415627c003001c01e042044800800609e000810c06a00100a011020a00f03d009d62e0000bd01f400d761008000411000005588043a400400b00280ca0b300d004022800000401302881b9001800807e00b5af800400000100100b4001f7600d800590202420e00c40000070f000074f617601881080120021aeddc40a234c012001c03c000000006006404d00100241a8009024800c00719201882c808600506b003c00000101a80140a201902680bc00c1571081614318002003803004000001083c0552026e95025007800402b80500bc00301e800019a05500bf92400402e00980400e4080014805c2380221a700840600bc03f009c00800400e827082400400184bc000024039e2bc09467300300e803c00700302240dc1c103180003d8010000801c02806a003129000000300500bc001b8104f01940fa008011033c08400d06f001800200900300ec00a5c400580e004400400401c80dc05500180805d60c100c801006602c01480046a802b0c8000018200900100c012400208e800c3aa01c00002c00f8020004000400400800000000aa06f00b829400000104a85c4150771023800c02f55e00400080fc00000180040500086b200c82a5725410000400805e010000822200214001e40da009038000431010f062001008d35e002800403c08b00002a00640000a0000c00800d046000410400002bc20800c02f00780000040000e380300b60390d3004425f7fe00301fc0120000de018402a001010843402b740136036c0040400cc00c805001b001800400601511e01b000411801e800c00202d032003002400700a801c00d4b901e801411e00204000c800204002180e457405c002c0000040002001c024026000000000000008000015803600fd37c007c04a0084048014002401f4000000178123c424301d00030224000519800503300000004031000c00100f801300000000fc0014008c02803cc093002408001a40000008007008000a02080230138013870003800ad00e6aa04101f0006ee4001cd18004000013cd68a1000c01501803103e600300c80140ba000007805000400900000,0x40a000000a90178003111400704780ac048400000083a10f75e180b6c01a0030003147807000c400900c00300489de4004c0090000001022402c0a3001b0004027012c06a08a8120005400c001011803900000034074070c31401102890738000000435e000801800180ad02d0028080099703080160694ec68a3801505a801700903e40ae00506600381540090228018518124001e63402a01d00702440960ad02902e404c180f88007407c08113601281e203c0950000e5405210a117053401026e8010000133060804de1200019c80c005e2c6000031800000702882c00ee0000b280900c2003010061c276292001800000009203102181e801a01a810c1d025000d834c57c00500f80a8000039001806800209abf215d937a0940140240168094001803c06c0b6e7380ec0060cc00100000321f3003f51407c3585bb80306a40000b78198b562f2000803c0080060ef800301f41bc00045ed00000000b8c0f600140042015f680000013005443a894001101640021c4007202c98121c2009d006c08e0280028042c1bf16e80190000bda0000001168c000008800b01380a109fc403000400700580c2000400500ec02400000ad0010006015c320008c1220fe003400618a1dd0241d9c032015804803808e00003cc0041e000101a78201b104400001bc192001003801400800002187fa01e002813400400c026804400017100f047000202b08c80c003a13061e81546a200207a007d2e60010cf991001e0001ca017c15a0f4008874c13e0050250aa401e002000008c06e1170d900040600020d7040c0620ff000019c00e00156b80b78441b5009812800800816c03b40040fa0098000001275000802c02002000488bc1fc00100b8ba06103b703d125820221102a8024028050009dc400d203b00001fc0c01e8068218801c1ba00b0000002008003a41804e05686080c001c02003483800060050475868c1a02807d044029a00007881340040010000795e2000011e042824000209380e7a0e0b902104380000ae084802869a14300b000000400a00002b401c00e001001901800120a9c001017000100a800000fc000000000901980ed002c0910624382011802f057c280007c00c0264025094c875008803a004c0010014060002c18a016000d0de5d7b00001cd0100005000401904200e88ae803d007c12801b00a9001000101280960b6400000440170ee19804800024a402e8012120102f82a12c0d4020202622a02d95703a320018030008287600700400c0f00a008010020097c00540880f01e0004d0370460302a00c07c0941290a80e000bf80b0081200016825e2180681306e490041b107801c510ba24600801bfa32017403021e7800ba5083870002d20040d6000d003e3c27d48f0270a80c0a000200c26c0038d00806cad96f0060e11,0xd1cc0136180080001eb062fe086dc02608c03dc12c0230928001456871368001400007f01b80000360770075dc107e00f004010c30843b95680000b600001f812911e0073679c0404518142f00f407216501001f81e8afc0052dec5b8000cb7801011206d00080d4002002ad502819d8b0100500b447c05b0bb80300002331a3008341400c0f882ac0185ad00037e409416b06e04af0018017090804300000080028385001c0cd016c58808fc0ac042002200702ca036000404dc00c00a618d1df800606300ae000816558c8f2508ac08a0188a25502003b013402b00040c806f4005163400103fc0391afc07b000001f0cf0000471c01027483e200187e9002403600503357d048f0141930154136000968c6c80000558cc400200200e80097caf9904703100420001172ca400201c0268cb408600a48180087880000d8800b386017006008401003f0120291bd853d06084b8e78003144a6ec37c008ef38008f44006099005004200601f40f4004832d04d828200000a3007001204c004c0d4405406d4004034c6190004679000001603d000601705ed000c56f01000ad036c2da0f680a607211b400022490b7d4f618dc55106b4000032804900445c877c06e31d1c3630000425071c39e2d4003b071000001a403f01a02ab00b13d015e010156804c00002d001005407c12a00580640f81d9112002001801b03180c402000300580000391b42c589fe80201600729b401402d05d01180340bd0ee04d03bc0045d091f81180151a5000aab20011dfa2181520041b3003801404607f0b2c1ba0002a2c009000802211197d901f4467000832d001c81000f0011083c01302c202f0918100001c02b054116d02d000f00f000400e800d032800a060c0ea01900280390015022cf7401b401f04b001003cc19f00105c60000246000002407d0007017]
def shift11Head : Array Nat := #[0xd00039e068001c2038000da01a00069c0e0003320680018c038000bf01c0005c00d0002c606800156038000a401a0004ec0d00025c06800121038000898160004200b0001fa068000f00380007101a0003540d000190068000bb0340005701a0002840d000128070000860340003c81a0001b00d0000be070000510340002201c0000d80d0000520700001b0380000681a0000000]
def shift11 (i : Nat) := groupField shift11Head shift11Data 64 15 14 4 i
def iv11 : Array Nat := #[0x284b806d6713134058a96f95f9d48c3d90b26e11d9d3ecdc82c26a433a5d87f103f9e5e1243ff5bb687bd01c4c12d561326bb03e38e1f0ab4bddb2a1358c8aae479fd78ed6ef03e2bb17061114f3e74932a9c54a40b221b118922aa7c0cde54d764070a1b40f019c35e6aa3cb309a57a194ceb1714be66304094ef4d66b823891ea9a7f327863916ba80a018c4423d3666f8e3f86467eeab2ed3aa8ab8a3b01e9ff27e8c9d2835f3165224d63eda954310cb6142f94b03662752830a91344608644f42f4892a29c7166d91b2ad82e854b30d2c2767bcf451c171d9a406ceca6a1704c00c4aea9fd126bf56e8a1537441a3d94ea2602d6792cc7650f24ef00d94fcd0e8c03250d170f3feb94de28946399a557fefef6e9c43db3445f51cf4af98238fbc04f9f08c55e15178c864799b50aa1a3a84c6858602c23b80075bb8e454e0f0772d2595b8a9cf6f9203efa8ac0b9262e2319b34058b850e30a54020e9d341d8c7c00799c2eab51d829a19cc235e3c11bb77b04909a3e8ad08800984c2d3a265186f53759502570e6f2e0f6ae2ef9b31329d453d684732327c308b49718bbe314bf4469e29f91d3de7afc767ed8966fbd5f532ff9e2e36436e8e9072f93cb2166420e06873e2d9dcc36bb0d1a0c45df8a6609504b5d9f20dce76799e0bc7af0ecd4e8e2152b18eac50f8d470b9daad2ba68aea9e6ec8723f9bbe40c4e0c52b98543f4c49714681d0903c3bcbfb5dd555bded1b51811519f9e3c64dd19780db8234ac15991c81e248b280cd930b0a68ef63131f744ca32b91893ba90cd5b298053610daec5bc8685d62292f1cc7d440f9f25a8fbb7562fbf6b2925e2a91d46d324b6772e8f2ebbab5c30181b6a7016f10db5a6310359d4d434910bb53a745bc02467135e4090e5078c67b44aff921eb04231dc6ee2a148b488707139d0cabc70c0fc45b4d5a6a46e1f196f06b427e878874254b813ebc0d2435fac412dbb13d990f1bb93aae275a89845d21f2a0ac5b8750a438c43c244baf04baae969d6817313ae5f074f77ce590efec14d3cf4401677c4492aab0ad0055832342d816532370f223e2d3311ec1ac92ca1cabd5ea0804e7f741c2c5ba928a9a8bd055a3c28b7a05ee31d01564753922c2c93e9764b7e20cb8ca1c57beba4845c8193819ab847036a12fa498b9b3c1ddc09540bba34f4b5af9832d0964934b7c0949707340cadb81d37b5acdbccac89a381b9cfb1bfb73b592c13456a42b4797beaad584d1704e0b861f44cb61336c7b3762d8a8022a52a0db1fd05f56846cc8ace5038a0ab948480ff2c2f8adac8565fa92f2f180992476e9c60e108cdb6f17de78c0497b4da20934b454a2f256e2ade404f2b4e27833cee7747b3e0ab95456c4f8905a17da7134dad5f363f603948eaf406d14350ee9567d1336fb36369032764d11f02f,0x38166e5e289e2afd45d10fbfa423aaec930f9e742b6656f0bfd9bb8a68148d3725b5a184b646b322c02c8c49af88a64e961c3797e21bb863b1da30fd1c36c825b4cb949b21a6951a8879b465b3de8972ef3d329d0b2e003a61a43c665bb7bbbfa0323dd77018d31823d0b6a556bc8802861cef75d47ec398e1775fdb4b6d0a2bfa9dbd4b13bc0eb11d243ce84d10f0bc0c556e0e4427a2dfa5732c4e872e163a7b8028da66a9e2933a3aa4d58a4e4e5b4a94f89004007b7083f28fd6798ba7cf37385936761b952050c19ed33b60a66d453f11f6b0858f95bc6befb1e794d667fc539140bf8c11338a06f448832b899e2dd592d271d8aef196cd2a21a397e0e2b5a4d96a08666485e80c72c66c3c14060cce151a38500251ce65d17687452511ba96caacf44083b7a9fc6ce546003024dabb413f33de796d9e3541a3cf06ad969c37a4fccde143bacf14943aaf00c4f01ca62d891c9ce29c2267668d5b9c7b20482bc2001bf9c408779ed4f2903dc2056022d7f8c3f02199410f39e32adc309242fd62dac2acee4b1a1ea21c95ea2ec04f509866e66bd19aea45abec8b123cad209bc6077d24b479be2e25ad4fb9f229a59baa001989476f14c291fbaaaa067b6db8ccd1668f35702b96e4ae26cead2031549ad2a60aa3c6f83f3d53d37ce3243e70a1e47b259244a330adaca5f3eddcdbad023b4a9835a6e69cd1393ccb5fc58b45a4256e94ea85d78d457891ebc6facd390c287091776846d9a295b39641ca0681b64d818b3b1946096331ff62454215b106db3a5d20fe24b803582b6aab088ff0b6188789eecc2a6bda7e78d661db09c973839b405b6dabace480b7d9df3e747ec5b056d5ea4bd03fecca3e0e94aee9bbc437c01a39d0115b8ff328353740eae5092956b5883f06bd87a4d50140af81848c37725c9b2a1cdd8e3bd2477cce9d632f555cdef5b141b4fcb9cc10fcf2935b44a13ab2a7cf003aebae94cba84496d6724b75e09558f191445944aa6485041bdc9653e6d831ebdc21499cd623c857a14ed735193ed915d33b3f453de2511487b4f38a3bc9680bbed02045c132872a7bc4d019d6bee75ef9bdef02aac30ca5fe17cd0bf0d4ce5f2e1705427af03637588824360b112a07a038a350bad2f1468ea67ced32cec210433b07d201e2b0252ded473289a767940239d7bc971f51baf0f785cd50dc80fbd84caac4f3c4d756002ba5e9009b48203e4495dc808e60a2f24e0fef97ea8217b1a70a29a5913b1c1435e4bc3f46e4e5b433e9d8c78ed7f002df1b2331c6762147e420459628da3f06651a1a8465388e5531c243b1d4264efd90c244886f7356668a95487a542a3937214f19930672e74c43954d598c17c760b00d2647dbbf168739b5cec23bd6a106d08bfb5938f50ab4ca75f33982d17b0831e6a6e7821239afbb25c81d0535,0x1c3e613b665c23a34135b7b78cdfc6608d98222b6f955bb580c3c0ea4536e59c687f22976259a2a3bee762db49f4cfe5487d4d724d23ef01c65ff93140a21f0f322c03621e304f926d6021f9075f017c824249a9486e61e5c6636988cb655c02128f3bbadb1595105408ea033497c9d9230d143887a967bb708bf2846b122745ec88a0bf1ba773128819ac11ed6fcbbc80255b433dc12a668014e793a9bb41f7987932a38ee29a490c94462ead8f8f283b6a6aa4f31af50aa8b74c16937778863b9697b956b63031a5d463a6683d2b4b6f2d1a5086faac8da230609dbc2e88e9df0a42c2f2f52de7071946c31ac1801d65ddac094626a24abe77138db5bc759d99251fb393206faf68c28b09fb190016ca1161a3d82763a8e9b63b0b09dc4089301945f98a0d0dade28b14a4e709681245b3415755358d680ce74feafe638aa22dcfa331cb8386821bb2ef7dd1281d25e85d2200e6ee563416accca1fbc3427fa5e3684f1f72c5ce7b551dbd0e83e2094471597f82f965b2498ca409c930d19224354b88a5cb7018b06c108d06a5387058a9f95a6bca448061280df16fa5654c9f007e21d202367582d71acd451a8de894c7f2f6ca94d4fe8b630bd118703cd7dc212eb40ea55726ff9055c1c2eff8ffa6a41524e156a43bbceb3a57c94eb99daf3e6f6b75a3946ece58789c546b57b18a643415f40f558e2d91151dbc0051728e3903679eed1f3edadec5005312f7190ed47049593c045aeb96da6eafd5177927be256acb9df2cce5b16b9111ad52148abb6240895f4ce09fd55182d6a3cd24c4f1435a4ed40040ac9b72b6011d1e82d47d05c849edc0b937df3b034e7d160221445519318ba74840fa309ea45641aa14b67c0fdf40debd7c7fd8bfa15f0430c7d0489650b8d8def7d590863749e11080522098f5c3db1a277a2634ac2328dedf445d1afa488c847c409c25dfa4accc9a226de5c5300aad1a14a04cd645cc3626983b1104a168d5cc667551ae58d3416c8a73099987d547fcd0863be80a134340a4772bf0e62d13f1f7a8f51054f54c97ac042a4e80b39bcd71d2a30820b2ca14390622384d87d5d10e0216a66d4f40458d42836e5aa7749483a55bc85e9515652ed28c02c59475aaa2033e9951ec49643e61634c4e74b542dd5f1905ae2b26bf787e40b371329a52440d1eb65bb10942c66433c437d691ca16f99a902fbfa01972f0bedb6b405a51978e44339e4e75f12967519a133b7f1b1302ce73eab34be4a0ba9d201c44d5a37debb07b1148fa00411490501f7b313c234769ad1073007398c0ef6e80ffb26004653f2dda7324a2af445cd548939bcc7128e8bb72c78150651f2ac049f5317bc342dc144b672cd8e34264ac0dd46057f5a7b54c3937a093970af360f763ad4ff3ac00b4cf9590124004010b386189b5097c910339a908,0x1c03c33f428f81f7293f0595ef20c517d61ddc1757fb2d916da23990f054ab05158159eed3c22759086ecd6ccaf2bbfd645055507b36fc0427307b1b43eb3495dfcafd9456875f8d90bb11b52d90684e9544e06a61374a6f782c153aa50d019d7fa1d518cd3e0c7452c9a0e2910be512093cc5545455642e484d44d8a18cdce8a2ef4c6589cbdb04737ad419bc8d7fb2a3bead61cb8d480254c8e854b1b0e3f0803d2c967fa86a780b6656cc11a04ebf5dcef261d979a94ff0434d883ba235746ddd066b65986d9b201d9b69c8949dc4870d7a43d05431e2f188e6b86f5085e7a64412e05c82aa19c4e2bbce7bc793ccfd57d19b968327cc75467becad01af82bb961584ccf2d9200ec25667b1aaad8d16ec52ff85f2db181d914a9e343151fd4b6a1d9241c530de7e5e85f4a9a6affcfdfc93c1ce9c6d234c95222102f49a202686c2c06c050541369e47725ea077d1a492a2cec6ceda4c9480f2fed5db452a1c8648be8911a83c58921716872169987da30e85a3d0625328cc1229c951bdb4fbbe15b366f187f0624cd20c350ae4ecac428cc3b0f7c1d9675d060eb861a98cce5659ab326239be05d4e8ad34d0dd83fe45c31527587157ced9e1f619745e972c35ac94b454d4b128941f984acc594cd2e183ad98041c0e72ddfdd257c8770fa0c322bc2ada5e6d5eefd9d7e7374436cbe9ec9a61c850d4d081333c52cac12a65c146c66fa260519d6ed337e0d4acc7b819c8e79c95f29a7bf042e446adbc55c56f7f6c578fb823ca9e0332b83dd6f0713a6e9311270627871e538e2f76c81cd2965e9cbb89dda966a26f2d7e1965581672025008966a0b66cb064f57178daebadb06286e7159d1e28afa50f18fb16d12e9aa5a545a6c4a687fb5547a4bb7906cb588c34c17240c0985da3611a8a66632300f0f14509b187018993db2d550c79625b898e1e494ad98a85ebed9912caff43255876cc345cfa4344648fbb018b29ca764935bb92a7103956d20cd3a5a334834c7fab4f44f2284d9eb218eed534fa1b74b7d0cb2531bc2ab0925e494d5bafb58f03257be7c8cf89e33a1b6e588d55e9b30c3a7637926e8d2a6c8856288812957089ee63f3458129e7826b7d195565ea9209067083044cb7be6bb8f437132962cb1880caa0d15aef74e135e6caa6636c0e2c10fc82fa52917c5006d3bd15c65388bc984e1891e4d1ed26a6d83255874760504202cbfa86295f100585c6d06474430329b93a50d8afed55ca33b4a2d75c7cdaf4e387ad2b6c307b889091a64d1302eb306c587252c14308260afdc2f61f66196adf498db7e2c19960300e20254871f7f22de6d41034668ce2925798f0d61a8d49229da6add9eb5901a856f7054344783dc887d182654ed4a81470d2a3654c9c3299fc04004dfd7ac3611468fa4910d1c56db6f2c9438a9bbb885524f,0x2e06cf1f8f1f6915350ebdaf4cde4132ee9fff5ee9eb8473ec4cbe196a4486534a00d034d754138ae8ce39511f0399123cffca7725d4722e30f9da3b5379c88e710b26c09d5919311e0930fcb46b03c3e77b07e4f7e2099c254d328e63a6d32f075490503acedad384d22eb51cc8ebbdbd71de894c978cb3d2845c38397155d2dda15e403e1d101a870d723593248bde4bb83a092e906ea0ef9481912e5e6fa2430ccdd099f5459808d5ec3c144923fc067714a082dc28ee9a2c3380f2316d87a7be6544eff9a02d25742ab38e4ebade89d367b37533cf940c2d727b01a94e986e94bda51e1636e6e2905a90a96e3d0a9e96f71110f4641119cd1bf853392b44aa11ba461ae4ceb40be54527546ba0a4e83667f2b776227530a9bd3b918f0d51698a89c165ca0ef6350f3470b5049420997f22c3f6c6b96e54787dbca5ef6941469b6abb03cec10916857706139a6d8adaf362d9ee24d56cd3fee25c790116b810a843b38b10511837dcbbbdf72ec12f8b6c7d9605c2bd8f23c0b34fa532d54c0e147a55c110099576597e3c2db9e6c3607a64cd5b01c9b23529c369c2d16216cbb6d9335f37fe891c6a650176ab366bb56ba4af34186aa9819619e9d05a60f498cbdc376d6f089def6a8c6f93e0b4ae429470856a6eb3c35b38273a4fc4b54decf5132cc5994b2d1e53fd1170aad807006c2ddacf5ae966e472b7935f170049f6e4d2fa243b3831d52362d2ec8ad3b8224131441c181c54ca29988fcdaf6e8769d4fd4094582f9f5b7bd9a5c092d005bb952db27e22b9ea05fd1cc6caeede07dca800d104662579d8736ccb3af42a3dc67f4916fa35ec16d062fe86d7d50242ae194c7bdc298f608cca7da52c9b184399d3c09552fc00232751786a89ee6bd88dd93d08a3f0be3eeb2bc6514d539bdb8c1235b1791877851d2cf92f37c85665caa93be66200797032684b6f01a5afb71f8ea192c8a344e985068a108dcdcb55bea981a679c63c58e721b71113cdc255982842e5b94d1be0c3aaf8acab82007aa31321d8e354fb86b8c19713d6bde686bd8b7741ed2d60c492349eb56bdad4168686e31747b44b6b0e3b2122089a681c27b0dd228c976a200c7e44c156a09b39cd2578813244d0203c5c09baa683419275180dc1e0cf3c8c6d2267318685b156be77da2bbac70c6c6a97fd136530e3ca61ab54319e31e5949d9900c6c95b5002a3873fec7c88dc5a342da9d456ed4f0d2c427ef52724d43ffada8ee82d1eb433a8ad2421481d03fa761d4674db1e7d7950b975112cd0f20205b4167b782e98d41720ca032fcbee2eb390aba030375a6f050b9a47a34801ddeb57ed867d3cadbf92008a820378677694470083a1bcb47c22207915ef50cdce50c36b71e52a00f2d22996f1c0e00a689496355928118f25589675350b818e4b3109bba95a335e47,0x5b1c1674f749100e41ff105858c43c2bcc07d447e033f51a8ceae36231c560a10243c4e33dee0f8b96acf1d995ebd66f87486ebf879c21f91e4576adac2b5081ce286786ac5554b80fb1c18ff75ba5b0ad912b46d390e570f92deb0f264c46b1cd1133b5b8667c5ae62ebea5a8535cae5f007eb0e25ad70ace94d07e8197ac6dc9ba745ba3483a6754e4eb96deaa17ad2d5b0405ca1203bfe69340243da3ba5cbd3a6cd5b982b7d8f5424bf274661ae8b10c99421f2b226502cccfdba5abb6a0aecb23474509323aa665e689386f633a4a28de811be7d10722aefc87d25258c56dbe9a934206cd3900f5c8a948755354fe7b128ae312dd3b8d3ac670bcbc11c4265f472b6ad6f134d2859949bc4487ac0061600d4ca25112e2bd670e5b4cca9e4845748f1c83800c9007e1b59743041f48a99e842a9929677f5c313c64d4d56ca816bc91d0af844cb2088a5df191e1c094568ef4f6cd381f2b86a90a89bb630d1bc1eb433124d6a114b4d8b0944093a63fd7ec8cea2703af48686dd4b713afb5b22161ff8efc632718d5bc4cf5a75a60959f6f505b9ba8793028a0cd963001e5b6e569979c443184284951884cd1f6f6cf94bf4a5199a6e67c1236880f803be2159ec62fa86f04db71d9d30d6143702e3986715b54dadb5c8d1a61ed82c222da21d320904dc95261c9ee771a5ed06653732125b8f5685e9d859bde7722348f36642217ba3d79055e47e0103ec4aa0054e7f33e28aa5d02626f5dbfa2d61358d61fe389a43ff6a12d9b4fdcbb2f648a2735a412376d693cbc6d3788dfb77c006bf719e22bac44d6b10588de0c7088cf7a3f1bc916207cd1ada58c46adeafb2c31c01aa0c5293be6106321634d1f933d8b9ac34719e7654e89cfc9a908b8898908d1ff032d4109dff0e54054248e22662e25332d217b5664560ea9707d4947c42f0011c1c1a20f1db10e69e9cc448a93c85d45211a4cb72bc382b902e33f49b2b3a81c8474eea57bff1a8a84cdf202d0415a8413aba01524be16b43178a0153d1835cc60793d644816a606b5e35c1540f9da0d4aee4cbbaca8db846ad01224b2e66e9e778b86f2f2967fa68cfe6362dc2d331cff3aa7a4ce60eb44e55a20f32106ba922f2d6108e6d63ad7392121ec37d246493aa50abc6b2c557292de44e9c6447d9a221fd1c9a204ce582630c7d798c9888bf0cfa0b122844a47c5c0ad2b9c5850d3dd4038e017ecceed7884a216051419e88d56f5514533a3ae224cae45ea0f53333e82d1c40220b133b1c4665c1fddde615c2df26a5a7c0a6847d243d49a70eb0b169c0c418e493e0ea23a49f61381b913610bc406bab60363c7d194e620e9e054939d91f86e3c50938769ed7ba0620f8665c7805368c7376c6e7d0c72d8fe445105ba7fbaee64a09f4b8995603bf710a4ccc1a01ae0701884fa545899105e,0x4dfaeed2d55838c0ecd9f3f1410830864bb5785045164cfa26c5a94a3c1fbb10cbe89fbf8b9ceb22b9d86d1a7bea17449a3eaa06438c362bd3aaaad44767d35a9cf7a5ddd98397762a76e5876269b13bbe59593788edb1cdce56805d56fb3b71a36fb5f60f90b150c945dc62f3294221b55f19c447909d06a87ab82de7712704cfc81cd20ed0b0c8b2bccdc5c04c4e7d1b45454f9186725f0ac942cee15bb6840e536ead2eeb0d845f7492e3e1d2276f2b62f06326a1ef0b0b9973c9f19f6e4d21b5cedc5a4ad50c6abb90379e891b6ef3e6b280caba57000b5b6e369528333e43b0f5fa4648368da96d9159b30730a0ff79e92262150159544bf6ae8eb221ade516cb5d84e25e9c118ac948f68c23515d9de46fcebb4213ca5199c9b0f1e980871e225d06b6b33426d2b14285102b5b51e363739fd45e0b745a32bf5e68e5fa24f556f9627c7c83dacd533163cfe256ab9e026e814af55c4971d466b02328e3bf9da2a989e97e5b1eed0807dc8f43c5404c32488cf27bd6a49a5f4f5539e94cd630c361b2c061066ad9826c43af9dc5bd5c86228a582306e2b1ddbb50e1e00d5540699701557e322ef90521551f033e03eb45ed94a8b8c714a8ef639405f6fbac2b57d1ded2141646adbc69a9b66f3c8a7227922e679b4e1096ef396b6b555a6e26d9eacef12c476440990f06728f2acf219f6ebbfab612c430cf7a4dc4e4bf472e5ea7d3a7ae6b2a51b4e89902f58f7264d177b23c3221ae47bc06a78b7b3932594d306d3213b0b636b8c480af57eeabfdbd0b5368e7b341491e5055a5ccc0acd6d3d14a2080ff1e2bb8eb23b35d031eb9739e4098bc34b7690cd42d3d304b5eccb56ab19f0ae2e8bdba0908a65a56b2c51d598ab53d2a7c4dc0bb9a9b9ad1561046d023163879614d0eee22913aacac75832a9993fb51519994aa987fcc86c7cbbe4670e0621ff10de49d982d825ccc5cb143bdbbba3d6c82b6c9b058ec73dd021f6e011a9b1a42e08a204ee804a5aab970ce3db0f6a5e0451b36a86bd9e0e72c3d145a143522991624f5444ef3001c97c71a4f2f450bbafb0a9bf55f047fba5627f13374d7b07fa0b80e7e6075aa16ca7574a7a0468fdaa3abd38d66534da1bc116057bad07e6bff2d18409963e1a7c2a56254bcf3072859eeca8355b346dc5b7a9db9305a88007c77dddb0e6cd9af39d8a6211fd1e2addbd6393dac1c83192c99fa89a4b761556371b26e94047d22182b2acb04c52d5baf56fb4a0f519ec5732c8d85b1742806c89c1e6ad6d26eea6c034c688e4c2c7eb29200b933bced3e52a9a8bd13be4eef0c5d785458892185a8d89a488d4fe122cd171cdf754786de56f6207538ad071d7d4fe70a1c0844c54fc2403f436beaae72bd9c6f395e40f0ae178ab1f423b89911ac4dc232515d52c0fa134c456ec14e516508877ecb95,0x32f78e12826c9de09ed91102ac0b49b88f4fabf3681431c08d2c6aa30775ae5907a1acb1a8539b7dfc13a5982c4e6a326cc51f5750d3b21a2be5e46af91cbe183337f923f3f105481786905ca248fcdbdef6f9b337190cdbb336c246e749e4a85ca343ba372a2e720af60164fce8687a04b75e995cdada794b856cd558af0f464b5d47b449e3b3e7a262187813588a895492ff4d59dba8c35a3c4adfc0f8e27021ba06c0cad2c057da07a036917cf12c881d242a89ccf9dd2a0f7efddb8971afd6181a97cf66c7be6b4aae43aab323765033f1af64e2dab1b7c8404ca000589d29f624a4e2fda8f41abca8a49cefb8be8aca628658729cdc5c9e24fae1fda69647446647f0a32b5d75de2b09e3ccfc9b9fd48d316475b249cf78c0f42ca4f8e44a8a28ba23c96ad3d27cb20a16511947acf73c2f15e9c4ccd49e77768999162e81199b2e000d962889d0a06346a0cc3d6f57a68c411f013372c6e04fe0ce34ec80702360f5456895ae57028fc922a933ac10fc3b7c4cfa92ce2d6d05cff468dd878b1ab254c91df0d4ad20376559a170d54a0bb710f6f29bc5c98190d002c38498fc4659ca899c1e6acafbd8492b1920be0aa83abbdb0631ddeaa88181466448711119f9452ab87b87cda7342a51cc006378b9ba2aa22a3fc187e6d3b412e6814685e8b049e0d6bb568b2069a7db10447dae2a471a6a91d1bbf411399f1277370d125e58a5c0d5675031bcd9a936e7ec7e5db2da073ecde1766bef90e45718f351ba26878ee46362cce63c8acb271dab41b282d50cb1edcfb7bf92672dade936905c0532fd8311174d044d0df3cdbdebbf390ea029e3ea7eb30c674c2e4d6881efdb4909e53a99770aea1a4a3c80d8f144817c8aceecf6c0a53c27c30fb0e6b778aaa169b9c552d913abe2b22853bb35f9b01882561afbd61814c61756bfc8022a34b46cc03a0a35edd9da9731242e7a526a90610c4e82d16d5f885f22e2efa097db05f33ddadb278e2a391682a205bc0278b1d7fd991892828521ef2fde685708d16bbe253889d8d70c5fbc163164d8244083f1955de92a2a30bbb4424b4e661ae09803c35618fe8a8e2e961cebd158ef90ceb38af9f48f88c61c21701a2f141a54aede973b1701cd1bb539e0a45a4c8d164d7680cd3d46ce9e941f8593b41179e18e5c54174c192773065006c93de8c24ff6953b940cba3a44257208a0e032e5041916354db14a7301e2144fae5ca11cf330ef2d45536a0aa464d595842cd712a1ade2db61d2a3f9c4dd7056e648c00106fd21dbd3aa83229de592988b557b813128f5f2314e5b68ba5ac34392c6b4cf240941aef3b3fb79994fce7a0c351b4b60d0f79a6bd43257d89d2984b98543646e55129703c4354640f648733dac96bd2a491596753e2d0a2acbb5dcf9eb18eba19b8364de3c6c791380308dd286f2,0xbc172d8b37f76b1cac5a0a01269d9051d11caa8881f3df26144d38d433b9cc97afbb5d1d7aefa28821aabbe9f8256ef53990ed42ce68d3448a17c4851d069fec18afff82778315b2d207d5f336330fe8726b45bbbc7cb4084e2c7fbdcdb3f4cd3440dad4ae44dd078d3d3ea970a9f348eb09541520452720dc88b7ae2b89b51389f595c514366f4436a7b228e3f4e73b12774f53ebb0e9bd46229d6149d7b88847f417910810ac3bee7296ff4f44c452c7807dd8ab945d80232343026b78d4d0bdc10a60ac02fa59c5b217113a82ff32a6d8a33324af017231ad0b768569bc5adde0768690fa3d45afc74a4d654cc08c2418982e413e1b771b86b93721a87027c765bae650d31d1e4e3b6059b92b28616f13f806bebe14a7a49bd4a389702aa4b78ad80f31522d1f696c51785f9502b6b83348c4a26a036c5c5a30b6cf8c2c6e137225b826f998dea842dfd49fe198da7cdbb10c6cf212c881ec502add62686013c88a7eac16f0003f488450d5710713698f6d4d1fb70627fc541e5a5ba3663b19ec630e27c6ea35b0fa15258798fa3b98a88ac6c80cd2eb1a0c5e38b0854205608ea6e4f17295218876808957ab958d4a9c8a19b8076c23a161954320119f5fd283bbba4e2d9eaa659bd6aaae1a7be4f9c0d9b76d61ed87c11fa0f4f1dc09f7de670d983068758fcc71a5d23b7c48c84c4c7f6919c4e38f81091918f0080cbebbcfa949eb1101fda92c46d4eefa39c017951e2e3cf5362905970ba48651c2866f8f561be87ea196eaccf4a35c97f1baf8207b425b36ddcc39f5ae22c953e47da3d8cc6f887566fbf5c94d0385a4544d166e00c99ec0853620748c68d84a9eb231fe3e7a2241b87a8d1913006d4ef06d0fb1a50feb5892bf16688a1101b20a54256d5a73e95961e4a7ff77aacb95e3d045855e5aa9980e183b728c9be647771f5c13195e332cd645eff21c8bc145f32130fe1a2d4610f4a0dbd317bd357533712a0044829737b2c108bd46f8aba037eba3dc99cb09daccf70cc0d44945052d4ed8832dad7ecee50a731fedf8a39ccc6f6e9d5fb37411ca534753086c7b20b36368fcd9c47417a874076c0a13debbd6048bf189b72e7852e1b3802c31c4d359890b211230ad95a596278bab5feeb2184301b51a72a9bae6dfacc7d4b7fb6e5bcd7e0566a200cd81473be9037c8188fd892d6a4a20160a79df378f3de323dec833da5b942798bd1763bdfec8f4ee5955e43c5fe453db9c51118752e623f388a90bbaa366834813a6d2f8423198c42a4eb5106f018ef1e6ca31e3555a25ad0f4de90dfb4a51867793205433e44015b79bcd9600ab304da5550dc41b18e2c2eb43fdc417afde8e0cee564d045efb6aea7354bc6a50018530857369f89cf1ea8843915e7452f011f7260f4514b4504629ecd99e2ef66944fb3626d9e2ecae1a343885,0x2ec3b010d07c55136668b6d6d5a73992323b812d32cb9b723a78ce6d036cf398d5dfac2b60f9642924b5a108cac37727509c3ea696c8086466c8e3fe1b689d92ce9a3fcb7143a1b7b6770638d2bf1089d4c13586122c9319e42dd3029399f1f77c2d4d698b88573fdfd2326a7a21a6d4ee06d1ecb6d82ee810ae42b6dae0ec0e8922a3bb0e6ede63898c46d7ead14a6b73968bf4fe6853492565f26e2644853fbf70ffbc1a38bcd45bb0b85f99c99ffd7e11dc02c2c7c68d32f3b236b0576d659146e1e7066c4bb25afa984143be56938d69f15d28d791f9d1e45a2e802ea122d7917116693f009e6c3d752eb92185462a77d05042d2e59c40a9beda077d699f75bcab1f439bd2ef35e6895e2090baf2d3b4d32617a201bf4104f9883528dc4a76ec152f9b4f62054b9a3ba4c57d27b68992e18adeda9d09213aace2aad0417437ce23709981ac58e60029ed3eea55695c5d7b342927581103c0d37ad329d8d85bca0f99800af65c0e405a844af0441aa0f2d4acf15c13e460e5ad3711c3d11052bab285be687d65e90d79d130a4b3c1a33e7c94d100532d59be902554b71221abea862fce05d699c49f29b81dc5a2efad06782ab01ef6a68b0092853ec5b0b347ae7b5ed38ccd448b631789873dccd4b679e0eca12709c5d81b855136d111ab8da5d17d30902949f3dc1d1d78065aeb85dd8ccc43a5d09ce830560c15b6b978680a580e571d1991e451f8d2e74d23ae55b1699a9c1b8dc4d944a364fa5177904a6910b0f2c48038529820a05a2eb337d2e1dd8a06c2cc2d1d6a3f5a31a5155075278dc888979969db691494667dfb19af6aa08f85a032425942e1a9b2161336ea8812889459fed6634935e623cbc741b8651c55de9e52070897a5503e1c7a3ab094ba0e4241a1dc88636202fc887bb6dd26307d8c058da435014330d9cce66c512fe5d316b20ac384f9f8183c99584b8bfb85b389784cd5ff37ff998979601093731c63278ec3cbf1d3d0abbd7f19e1442b2479db2066c45c02bb5db381e2b5b072f14e1430349c748527c856b5064c2eeac4c6daa1660cb877132cd3e2d13248c72f1951afe1311f74fee2518be3c6ccb5d5532aa15d731ea61dadcd6ddb810d73d7d4bd9c479cceec96928599252264379ce7b155140755a588ddf5290138416d70039f4b6056208b0e275885d72125ddc046c52ed2c141016aa71ee8151c8185be21bd6e28d776738d00d2610f1211a7471d6079ac3a960850c8088fe06acb40ce51219c03398db5b147a7404b8cd5bc2c1ded810d19d72b34a848d2b188a86e350505441c16e6eec36bd83e965a6c9d4ee34bc4ff26a700e05546a40b1d05a34f3640bec38944fbb9f717b14d8ee539d56ae93b7a2e6193cfef6facfda89a4c8ce12181435412c124e4f7424b138f871efc8e0cd130bbfaaf8a1569e523,0xff9706a73a7596bc0c9a6bbbf5099647b502daaf31aec0ceed2be8075d022886057821e55ee526c5b721d8cbada8989bc40b9b363a0c0f47ea03d4006e50f7a1bcd1211e7e84a01342cdbe4e64e8e6b469b0b281391d615ea0794ff8e8f060401dcf40125969087e00cd9aec36864f4fb6dac4d215b0f83e6cd8a56a3804a11c7401812d863addff624b3e44bfe85d0946df4f6d3009106d1a438250d51bcdbbf1153474891b53a2c8cec2c629b8c435335f6b5030ceb00d44926b544dfbb319a418344966acef0ce9c4879bd2068d464ef37f4a0247c87c271fd690bb39417afc083d21bb43d2aec3d0572b99e1ab23c1040ed0e0c20d4095785e72e74d0056142fa62dd06cbeb0394710bf53b5f4a17209cb90aba8be8000e7955ab44072199f374190512f193d487adb9f2a2ba29acc80324c1a4bcd80a4d269f7e424beb5d0c6a06112223663f868ed476fe6d729bed8c834ba976beac451c03eca505586912f6a923024d69d3e981e0bf6cecafdd4a7e68ca42136b0de75c1d49b6d34c649bf5e107f95adec940c1700c29b31d4dabe1113d7534643ec080599347247361cb89b41603f9d16e664e6e05726444035b40133a16d1ab54889cecf84b3b6f110b8d15bb019f4fcae47199c6eabdfb8de224469e34e51760e98dd53ecc3ca6ec435d19333291f1a9be81448901789f4830d2e4acc61d66fef807acda6c6c11d97cb86b63a99b156f2e52bee0fa913306bd0c1f4268a722c4151021543815dc41f5682eeacab5c84e13b80aa3b9167179a4b808a6b17dad80281b4c5cea78e94776fd587d32d8edcb75ebe07d610507d4934d26a0a0d5bd3f3af1ad8eaace62b0800496f2ab861f57b0fa55e688b971c1c020d019f8296c9d52124836ef1819d1c5db7d4ce31bf3a487f879d381d90cb867b92a4e868446c84d2dabe595a07a1b6d27066da1d353188464d62afd1a9d2b1499afc84a60dc336a209effdc5f050b9ab1159bf025a0c73d7e9ccba498a49a5bb88b3577c1312fc4a3e47ded118cb1c58d70cfb8d5e1a7714a6dc35b34ce9084507a3f7da10c5d2fa2f6dcd4b6d2ecc746364a76425be8330994848e03baf9c9b04f3aa004b4bad29a9a8a3108f8fb8d292c6ea41b95a54635b9949bcce2d523683342bc23ddded9b6c1d0e2668afef61c4ae7f43ee671ea6f32fba64a7958a766d20cc8b5cee4d81bc6c431ccaeaf895e434593a92004be67667af2291f496841e56a590b483814fea5e6a8d6cb3fa380a4941e15c0164f320ed99d74bdfc0edf49ce28cbfbe455a3a581659d965040ec23184c0e76eb8462b902c8abbc44f4196b27b16fc4d62d7e51eedb9a20288ca23ad72d20f05197e586b4fba21c4d56dc9064c9fc557ee158278dac304b36542b931806a20bcfb9fad0c80c9bd3084d0539076492cde50c471731962b39b,0x87d8532754dccc6f4c0b0e7997db697149d562089296d93653bd40037b25f855cc581bc8594689ad32f23384f9e77e84d8460d078cdc18607f802f614b4ace39ce66a6d4990c9981900bf0d9c33518d5abe8218583a04a5ca7a525bc51792e8e2f9437c7eda4f7639e092d32c5433854dac39d240207c2ef55b6ac4510549db4b92a99610c68b52c456b92d54c171189ef1c38c6c47ad366dd444e14403169a5a4d9ac57ce1a6c8c6578126f6732a525c357365ce2dcfff661a3aa465cea381f4ff5528a6677712e91102536388307687a9d2d54c8c9fcb03d0085dcce7cd94b9c605e1ca476a309c1105ccede00b26d542449ab89089a3936fcb246303704d0773d73ca0f5e9512b3c287d6c59a3cccb563f77b3dd881a05fea9de3719e0a119b1d4e9825ba23936827f737ec2be53701c47802dce15d95524301fbd107577b607ddaca6a80e44889e864ca525a45287f201ab125482598edb214d2735cfcabcd1921b579cd91679106dbe1fc07fe5c0281998604c72ff08506ea6fc3a2fa294cc9d8d03ecae36331cf9db23ad0d10a7b0c231d2011ff7b658047bee67df01d07efbcc1065299491c7612c750d0b0e19da2cfea1abe16607445b671530ccd58730fafc1df4cd4c6a26a47ee491d03b2760ced5da2e0517e26bb4b2ef9e9c9473a9b0316950bd3152315e765272ddee09481e0a9ca1b2b25df592cc63b66c4b8abd142d451e9031951152907fb87a6ea89dcb9c92fac87b01d78e4d4e5ce127a48e1f327060cb185d5f131fa14b723823fb7f616e2799c7095ccb60774f4f0a4ad6f8da8083be75a3424600896076260f743a13f188fe55d5aabc2064a4df6d1ed6f5579ea079a4aa73787b0450ed8ef76d701b399bc49cc90c5aa7230be313bda649e7303d2546016d74b20158a616cae5546322e6d579351f613a3b8cb4cb2d2072410c8016027f6bf29ae438da6b80e3c2b318cc41a458080febe986e616c69438c0c1656e2609cf609aa288378e0dc88639901b83bb41e4e80ec62f2bcf3a14a99a1bf6dbd31c1d08f512b58c259bea99f614f62c18a607ac04be9eba902fd6a530276e7c68b1d506f5c991b07402363d00ac4ab15f9c3033308ba56f26ee0bb8f217c5fe145ec659b14a2c6b2c2f0b1187517d78a6e1a11cab17adc256fdc7ee13f5d3418d4f4f714b5b74412960e7533f78b69bed2884312ee6d73c1ae9fac57e0be2de248b23b295d2410d6fc3a791164e1a9d4486299426bbf295ce962c7e25c63a235c31370290815adad95c50c4c6fe413f6b3d0ff98c2c15b5262958e832f96470f576c927d7338576f0da86d0c9a68c139e2d3552746e6a03a14876b04d3b1edb601a885856a9c6e0ecabdb98a902bd40b925b11ca6118469f66d44157135d3472649e1010b7ec6e7259e057eaafe60f4cad55d634fcbfba2899,0x6d8afb020e294b0b68d150748adc0848e63052988eae6b3ba8636c010bf5b7108cba04fe3aa2f4d61f6b6eac674fdc5f6fadc97c7acf5c076c601bccaa42c84f18321264dea71b0070501431d2c4708faf6fdc796df51fc116942b07a8bfc5db9dd2499163d4aa118c11c297aeaa3c9d3f051ebaaedb186df2d64aaa6cad41c59442308f52ca13980c4baa425c50c896efeb2d4f1225a009bb97782c086d3d00564acb39ee70db3da3a80d3391a10a3ec17183fb2f4cc9a503d0b114562e210348d0270b571dd4a703425b62c1695160e004f974fa827a82e772e8f8e942d2159b4434e77a4e82e6ea9b6439de9216e24c17ec596974628f7aeccef59522d50e79b51f12081027a3443220c4fe7513bf7643dac40a5c496c773005f18be219574c69531e02af6d9cdcd6498ed259a5d1457547cf0313af01de2e32e9d34c0246d454e10e132952a0de7285760a4b57c53476bd74dca060bb92eb4acf2b8d2b3e437a04d6e699ad78407591b0d8dd079844332b255415c3356f0cf82e9440ebabb2b991b1f9a1d3a9bc78f13902cd2c88fc9fa602e4e0d6faa589e99bd465d35ced8c255555aa6fd2a66084b04add2206447eec0204b4dfc81520d1d4705ab3004a4a2fe04b8a4905760d9b04bb3192e0a569b3b80578f5ca0b27b21708a1d8da274ab3b7a5a3983703135afd667611a237978994e9364c5970b5fccfe481a737a1a08e94c30798dd57e8398b38938bf7b67fdf792e85978b35d4ac7e9bffba1aa59e1f181fcdee611cff66c4437714991eb8c04524293689bb8eaac898d60f1897f6f76aa29d69cb0f83daf485fba354351de5319c6a092639365ba1ba35d9d8e907217377f9c83355262a9245229cba8402bb2e28862cc2bca98511c2bc4d1b35d1262314db7ac0adede6578a33f15866bc3f0eac0e04530464257c46cb2f0f9fcd7755781d4d67ee9b6d0ad9c05292f8a1213902a2e89470908746ad0a82148414fad5f0c58f98b9d0ec83eb41ea56406ab87bc08c2f9cce50c2837fd1af0d806e49ba633fa098c2421e9a5f59e8eba3391b6b6ad28c149a49972ca6b1cf95c9b4f6cc4e507691b27e44c2057641447eac46825dcdb26c0ed7954ec79c3863f3abede6ed404907e65e2db973d897c6cc9762611a01f6e7aa47326ce297ed08a70f91efb8c262ae778c7f06a16c679e3864ac1b21f06beae4345ec829184179606a595c6c6c82d2299ab64b987b0504824b764cb0b02269e054db29d45e46d43b8410ca312accce2bf2270f0e2ace0d5c8d0ca4e5006144c9abc4868425c9cd4509c6a9dd8b2c181af30d6c756fd869b88c7813a8e20c3eea99a99a2ec25edfcb929115e1ab0a2bae283329518b3d9d0b4ee27264b424e5830e213f82cc220daf5660347eefec1ce2ccdd63acf251709595f6a5e9cfdf3211da76eb94433646,0x522e4fac248a09126c968440c13ce993bb8b3fd27e948db980209692a8b77956e5d21b1d3cb61a3af43c4a5921763fc4661b7902b6a8d974c5a2895c92478eb366e9caf993206b252d0301591b8e6b26b25a66ce14d23cfabdf380db33633c66810d9aea381687a2c68ec22fb0192b3659e02553458743529cda206642441cd2af68e35a584863434a6ee3b89362756299cb67e0eef7b1c0826c6900e83519444b31a8fda2c53a0f9e95b6b32c79348341703aab034825fe3e438fc9f2c900efb66fda03e84bad9e75253148defd232bef96d6d11b7a53d62e0de1a11d05c53cd86730cda8b2a46d4948c888b2ea5444214d3dd7a0cc4f13c46915a29b952e989a9a190c0aa645bfecc43d22b2d382e53693eebf864aa9a0ea7857b0f851f8ebc56404e133c98aed5c090e92c7acdc1c0bf8b6ac3d4cbc2c38ecbc579f63606f2162463cea7278d6dda76c63ec0a66749b403a1b676fc21e03abc58568169752468d4f295dbea3b7f9a6b227da3ea3bc321affebce995be0293a1b78706c4e582e11d4d8207a2e7ba3b5500c66cb8792ae6f6881fbd15e0022c428f22b3f844fd2aba30eb3adab945c7454c7d2fdb25367d7a54b2539d7a0665aa21c62a6e9d06af68cbb1de64797137f84eb948a2c0b8e36a92e649749007106f7493bb26de468518dec97a46c29ad0b5ef0f845ef47839d6225283cfbdb3570f49becf24a078f2ff3ca89f8113d4382e7d70a9bfc58411b4e24c44d215b1d896f3e9d5ea811f004bb610a9d53d60838b243f67e6dc01e2ce0faee029fccffae359741f686634f343aa6a76b778df516f4746dd5762ad6af47265274865d54f66f968a826840cae5fcc54ad2cc7327ea3318f82e8706d704b2d28f896bf67db474adff8c5cfbf8cba9dba4f9711e6ace93cd0cf9640500f8c3c45d5b685525cce73ef1f751b9de1a5a8d23d0a3c0c0babd92d59425479b8c7687a2d1d750bd394c6daf1cbc1d3ca6492c394a2351938e06966b7ecbf0e111e128ed994b3eb3bcdedea2fbed4e26da8d054a028d548974265257e06b0cda3e1325b2738278d2a69f68227a58a26ffbc1a66f91f780fe42550a7548c23854771cc043079f8bfadc9b8a44729aa42fbe29d9f0a95c0fdcaff364a5a94935a5712063903341095afb87ae533e27c87d296b4608246667515ad30de5e69621cc0965cd2888af67b74c749926337a3bc974b7c5a1c0183203b879af616574a5e63d6f5c9b4d424ed72d0b0d6aaea00ece7267fa98a5e4ae12675120241c9eb527bc71f64e388228183f300915dc48490743b5272b7b839185114206306d52197b9d2c9bb27875fb06b24bb982d9b200b8cd3c79c84065a0b8f0ae930527ee0c2302aaac2f92aa9123499fc9059b3455d3a2e935bfcd43d9db81a2f209c708dd9a4695a260b7fa6ab00da4814c99e6c2,0x95075b47575e8771169980348efe19e4830536d9ba69f99b54f36422e981c46230b9045b24b4cf591093efd35100b570b7c564d01b6ca67e30205e2d9d499b106695631d8c935bde9d2c91b25f8469ec70e7b92daa3c8e0c86263f74e33f32cc19cd903f2c8d54a25225f4972cc2f5e166b63ef186cd3fcfde8df70f04a8a7728f7e711a4d0f1013528691cf3035cb01504e575131eafb07c69816d0532822223e5bdfe53eff74b3571001ad8c63cb97b9ce26502adb70cec4e99764c614183cb448303b4410d71ea1cb3ee70e2fdd4e0b4db45551de8c82d1582293af5acd64fa1c2d11457bc2404dc45ef7eeedef815f0a2659c8b93c079d534558e02da8a8b4087857ca901e5b91764e992d33182e8041bb93465861145845516b1fa39ad778da822265f9943eb49e7a69e2a3e022b0d9838e111a16f21acdaeb71056588baecbc336be52da624e0dcfb318fd65c25a7dd23582b16bc4d3004e714caa27cd1a7b2936f35436bff0fd7156d6626138b88b71210b82da6e49763732588af69911cac318a6f75275721bc8c10a88bcee3ee66741b2a3b8dd9bbef87a2e0bdb15fe1c5bb84e1360599aa95f744b10c67552214a51d7411aeb3fbb3fb953863c0e608b283a45f90ec79a847b3fe65505c76570001474fba5abbb208573a7cf2ba2a9984dc68838b456218d2c179ec39204ccd1a0382aa066470c83221940d9fdc7d682d28e3bb54dc11679354c6ad0debd130db57243e22a8f37e5f613938e52756ab92f974beb2a3ea331eb66a27cb531e00338c48c440429b1bd5853a8ead8a3690a90954df1290ad7382e40099b85611e81ab8fab4a80220a2a3af92ae2d8ed0f41705cf06bf21ac6ce6561815989a2d44522b8e1b7550ac01e6b535e2ed350b7b61a7ab857c26f90ebe36d253cf7931ed527a7a210fbb2b300900f7a148037cf8cc0f94009ccccbbc72a176e0790e06c847f6a6cabcaa9e7b02593d1636083503d96600809fcfd50be537747872165836f8bc2eea1ba70f0a5a03f6216d0f614be3d3639907b8ea30c94939f2dd9e24122433330ff0c62970842482c30823334c5f39a923e6c9ce3fbeda2cf5ca41e17041f9791562206e59d1a72b61fe96fa6b34cfd8f6ae09d8169f57d391edad083b49c2c6ee5de1e93ce30cdc662baedc84ea30a2c195bdf52f461c83922edc95846dc0ac13da31288406449f82dbd2ea81141d99418174600f6fde8a2421e7f7b023576dd9e90b9a42e2cb274c2e19abb82aadf7aae41841258ee534130a087aa0adb69ac0f77ab5c46ed4e59dbbef2bdebdefab464ccdb3ed762cfd863a4e0609bd842c10e117ba074324afa65aec9864cace6536f1bdd81130b48fc828f4427185b3daf7ca5e40e31c153f2ad5a8f58027397e809b3a411a0d7c4360bc84063a55c534f0d81a59710fd6bac406cd8,0x14949fb8670a116bbe5be3197b74e743bb5ab1c9ef60022782c7260301072542bcce7810b8a155b8dce546d6c8e45b7aa21414ac8a9b5e2924a22e019480e02e7e94bc0001f8c8aea0bc9f7bbfdbfd3f3d8e0db7b48215339720186c378158ea800038c5b9e07a44fe88105c5871308a21ec403ec0c6dce6bacd1a019380eaa58a465e333d1751a1c88e5917a9234c4b9f3a0277ac5c6b85ccf6edb532f64829aee206ac5c3049cc539ea4f6ca4cc56d6a2318bfa664e5cc88a36d7c5d4ec2c00123e37e4f96899ef4254dba8ec57e948050b49809f6fb3324ef3739a4ce10185561c9d45f65332e79ce61b23cc1a280c46e1dfaabf827a04092015a69e5a2d19295796c0e3fccaa44a41401df938294d1337c9a135cf0b91a0e8e5a3f14d155642aa34393d4eaf438f112686c50c3c07940b3abc288c9b900523785dac369b524f8439c9832c16de474039e6355060248fa24af922c38e2f79f182203f0eed11fc74925d01804ca2699ee05c55d81c89419c12aa682ef9d1d88961fc676344ea4d94854988f78fe3b5b534901f8bd7bced74d8065240e4b5b10cdd52acebe2ea65bfdcf8749874ade31eaf7cb8ac6679e3fc4778e7c4dba02f32b9f38d5aa20e9f4eaa701dcd445878fbba10a44]
def rank11 : Array Nat := #[0xa11116020008002108f22041a0824400860a20014818408180802a00060ac030408400420100808100201502760468000101000121454408041448448180024008110010328001002058265704201010005003008080604402008050500200010800203010008288000040001da06080000340410890100484062013244000048246001125cc98805854004102000008401082080a82000422500680232440c2053126a0184000005020062088010c2000180900702108406d1030000022b470810010006426400002408004c0a12010100830b00715a0214800022b5210314102d08b21200691a24aa200405028160c0e1585080044c01902390004289c0028140844014920f9002e0080018121a0024610a192000400005030264008008020100928098002487044220d001180040c02044000161a3080120c040120200251421c00028800a04250c0a900008851a001683560020004050020804e006001680a0003616a200244cc0400000004008201260c2d0000002941405d0100056802d08008254032c0100490c00500000200510461060000c080682300c8406040808100073014020048802800c001c5000029c40040140400000702a0002912202612040211002811881100782bc022050a00ca1802404138229806462203602022224000180481a0880284104222088360c6c034804400040000000a50d00000188450818a41950294d1890003106240006411019000000410b012c204000083840022310840290401000094e00010624880090805014428144a200240201022080210421a002ec200820d30201a01012c409000c840308440351200020c90204300000808264820a002248008c2060c0008000090200893010200030c8a0004002280048080ac82808088500aa01041a824004c85002113400b0800040204222000108511040220050014300031080010014060f94000412040082825420291910945844003020300000c02012404320670803260a008404a01001152036600060640030c200786408442f1298e4810d00429ab4200002008440202019988a005001380004200012204481000000a8301e26000011002e0c0643600821000249222048010031c10a68914c1026d440960400016004500619918841b0841a800000500c481080080010a06108404275200ea2f013826ab00108c2440542400142f2002171101801c4c0243004134104801a28100000010c8346000440ca1430460048a4008200402032004407c002108822254000024254000229840022001080400208070380a0880c08418001093329821215081028054850a0404908406000c6021400000091114442424881820044b40103160a484005500001c2b1090000000420085a940002050022000000004013800000881c19280402000400a0304c,0x11020144243206b94080030800924509008000c64044c40268811809a0100114994a08005128501018040044199200824883000409008720e80b402820800888280020820247044111010002502c80140e0a0a658e02748018900c1400003000004002804c03126284e]
def pivot11 : Array Nat := #[0x1d23a0736e63cab9271be27c2f826fededbc375ee2db5b57686c8d87aef57ea5d43a7b4ce8dd0ba0b3ce72cd99972fe57ca793f25640c7d8db17e29c4b8830be10c1981f015ffbf57dafa5ebbcf78aeddd6b9f70ede5bab6b6c2d45a0b2b64ac6586b055eeb9d6aacf582aed55a9d516a0535a5748a8d513a1140a7dcf39db38a6ecd699932a614bf9752c6554a694326249c8d90f2063c4718cf196304588a312621c418730d615c2583d0560840d80d005fcbf37d8fa1f13dd7acf4de6bc677eee5d8ba8740e61c7387704dedbab6c6c4d7dadb5769ed119e33565acad91b1e630c4985b06602be5792ee5d0b7d6bad1594b0d5eab6566aa95329e536a5548a8b50c9f93ca704d29852ea574a4939242434768d51822643a8610aa0e4067f8fb9f03d277cea9c937e6f4dc1af352694d019b328630c217e2f05c0b315a2ac538a213e2704d497125230438831001ea3b8738e01b4350678c417e2ec598ad14e2844d8971222284207a0e41ac3185f0b014c258450760d01702804a0740c81802802803800]
def rot11 : Array Nat := #[0x99675679b9992b99b7799474b82194999b777196a13167195624997a9678b74977b651799b76779496b49576774777619b9397b944774436779b59917a314799976799797797b277775777539479691943749ba649b4139427977a9b68791218467717797967779776979661398423769b76959267696997797699b6b2977899439677926193471477997779476a96787967694996799493b62b16b91a777944475b7669713266b489774877ba997669b31979a97265492241767779a1b89782679599736744498449baa827627b35a67796774a777922a94997bab9779989312976521974879a78a2877692947b674669b7b77779292647979992493133b974779172674a97767292242299562871b28877797592899971b99b5974b979537737767797b3267b27711788a82839797748677916796b79627687883b7a729924192974b29797b9477247b797b4769276bb73427397969419287b9179999367466666936777467649732977864b996975b7674797777a269998b9377795249b97b87b9b2b769a91687196729177a9679477293417978994b767999197799247799744a6996779871a4971312a7978b9b9469629b97946919b2674787777799447779996419769979b99249773913877797377b7258999776792965817439947697bb5777b26a239554b974b547646799778786997b77676767348b82252685746a264996997175449494973b2bb7949996997991737196776797aa44974142b94a757694997497679b992b2b376112b79661997b9795bb374396499766797b7b9877ab8961b192579797797764796b913213b92773a19997769676994744b71972711669796997764112977692189717274726775729b7b779547a7928929973462672b799b9437799797999977b7419267146918376689776799293719947147b7656777971a7777982775b67b72299277879276799796663979798799369b67866996714693b769284a69669b5699b79977327977b2457797279969b97789797969379999167567693891296427949279749733b77bb9792a965675676417399677997a3787661467b967126721b9792919b7295373b9669233927717171897799449a72b9746997475777814b617997992b73947746392799776bb99473a71999939977729897799999996744777b269b68b76b7969794576979979764749997274829b9796479a19693767a97a61762463471776949971566957a9727667697769674712923a7776699989526951388717979447691245b77798677712bb27775269677]
def key11 (h : Nat) : Option (Nat × Nat) :=
  let row := (h/2267 + shift11 (h % 2267)) % 9041
  let v := field iv11 (row*14) 14
  if v >>> 13 != h/20495947 % 2 then none else
    let p := row % 32
    let f := field rank11 (row/32*32) 32
    let r := if f.testBit p then field rot11 (4*(field pivot11 (row/32*11) 11 + pc32 (f &&& ((1 <<< p)-1)))) 4 else 0
    some (v &&& 8191,r)
def shift12Data : Array Nat := #[0x2f0784005001c02c00018fa0180000002c09f0030007000000200d800100000010048001004403d01680070ad400205e801701e803000000010008058005815c001c00801b006a00000170012fb128c400100000350030003005401b01a40030008010000c002000c00400000340c54010004807e01880140004005000c0a102fc00e002800e0000006008c017000003000e8005000164f001813b00242eb012801300ac02d00003190094034039804e036c004000010100940b3023c01f000003700ac024004c1230014020011021d0008020001800c00a0000000000300cc00800000000084001001c0b000440000028046001000a0000001002006e00440070044035021400100a80030170038a8d000d0054017017955800000be00205710010029000404a0094000007c064bcb80dd001000400a996700540000004001019c0040088002b0880030000029002000100000270160001000c0df01ec0000054074000400003d41020064001002408b00c802700e403c021808600280770204000000c0fd00200021d4400e0a6005c0000010002edda0700ead00000032f08013048806c0020000000000001940519c6c01200e8020000401c003001185d8044000002702e4042000004000c403d00a800c044c05a00800040004015004400a02f800902b4000002c08f0078022010806f02400ab000008c00980010144005035c00078a4002001c027000c02a189800500b800200000020015adb00302a2000800302d4025008568400e6b1b00009100048000000005e021800e00f001d000402e077c00a00380020064013002c00900000b80014033002c000007000000000ac001003d0060001001400202dc027000000d008800000000e502d400003b4034049c018007800000480060000003008400a00befde00040000000004007671901ac00400a0018006409d004401802d400d000805b0314004000005507a402b00280000000075047c006009000a003806200cc003004803b0014017000400e00740120000002002801600a40010024001000001a00e80ab00000110098000005c19300a000503400020040004020401100380f0000025b001006b000c00000b8002034c1340009c4b00a80370054000000402c008003b0014010005cce6004000203e0000479002000280060c800050042700000002a002c03c8c3402c8d88007067c059015000000a800e0050004000407d00f80160000000266c00f0028000003400f007803d01b400102400180058004008401b44d00310000033b2a801d001058302863a8002c010004801500240d50000016000000000f00c1007800100140010008000005002f94d017f000802100000180190033002010f00c800c001c05d0118003b85400900c401000040000004000001c03402d4064023c255,0x402d000000f01a900080d285185fc000c1090034005009803206a40bd03080150c1800d006009700040ab004d2b90330030001c010007400a0004027001c00301bc04a01800a2012404220c800b041404f010405606f4002005000e005000300000cc837808a000d81c007409900000630000001bc0c00400000830190005000001f051000d0004000000403d0008000023c000018000a04a402300d401601d000100003a1014c000000000300000020044005017000300b80f5000400001183a82248000000400000d0023042412d023c0090004000047018a00700ab00080012c64bed01f000000d80c102d000c0088001014001200000480015d4d004c012001c1e90348004000001f00400d7000806400053350064008124c004032001303600b50010000028801a000400e01400006b5416281d801900d8085010c080001003200000190010080005800b0024000004007801d408800bc012006000e0224009012441f01880ab000800f000402501640c0001c01f0244005001401d05bc004007402f02700009fd4001000c00400340e102900050000000003c003aff805a002800c00c40030180033030812b413c1210098000004c011002806a00b003a0256f7dbf48006008000d0004004036c0260010057000804b025002c02a400000b46000010257009c00600e401700080c6004405500200ba03f800b026c0ae004000000000022ce40f700180090000498055c025001808b00242530024001002400413e4005016001f04340bf001002d0528003aac401b049804a00c002c00ac049000c010031c0a9005c00a0024012016c1c00044089000001503c002c003401b002801100b40c5000000200040810068001010003901d1fc800140050070010000407e07b014d007801e0024082001401978d400005c5a180008002017402c0014000002805d00c800a001401d0014047027809d0010006016002900280050030000003820000900200000000001c01900207a800000c700000590008014004c062008c0360388005b7d8082043405100181c7018003e0014000000000100180a100380000084001002c000002c00002b011c00b41e6010c02300001c000e413c005400101d4000002400a00d400201f800300014e30004003000000300ac1029e7800700000000010017001c03300400180048008014400700d807300140a3000c006004c0110140035005c00c09e8018043402c00380080ab0019001001c072c0120010056000000e002c05e008404800080090038036001800f001c000009403d052c000002c00000982365d7c00901e80260040002001c001000c0040224001025c19201bc00100000330104089015802400500f60260019009028302bc094078016c00e8011009c001002402400001a8002802a000c005000801400b,0xc4062000408a06d818d0040007001000506d8ef108500300160001000400a0300062554c31f0b24028001805d004800c003403d0c1405b02d4015005c024000edcb00003d500000ac0014014017c222001012b000400004340a2015c001004400006780090a1c04d001000c00c41160000000001015d000002c0e8413c0330178005800106f82540d5400503d9901002803e01c813b00040b178ec00e015804c003400c001008a000c002029c4fd00000430086df102c0059004c042001810b03ec1c200182b7023409900a80210020030001dbe7090003e029420c002c2e7000ab0500c0005001c0c8001c0050da80010000011012c110000020d02920e10008000037c023000019f008800201f803d0024001000400000580d200000fd00a4001003400000d000841a801500000080088000012000201c869d033459a00040080130000012400e001400002a00090038214000006401140040000051000000100980210068007011c0020030e180014005000408c002808700b80160d98001115000900101524548024892c0230248001008006e03a8a3602b8000066c00904380380398004000c002059c047001c0260120001000005d00580b20474037000011100d400003180007c6c00100cc0060d6009a0488006001805908b800b00b800304f00015a9800a004000b038c2760438000012802800180030000133026c01b01e0006776400036c80d10008018012000302141110000007013c1b7100c0170000006016402686d01e801a80ee000c000025c0000024011000001301ac0cf00300240000027003409b00c80040004027003c40f0094001002000c0c2002e00181ab000402d014c001a34c0480014002012000103a0180c34400204ec192002004c002400503cc04700101b6001800f018001e04ec02e00114ba001805600a800015cc02002c014b000000200e00650014000000c000009c01c01a40020040000070001e046c05c01c401301c800000f0000b7c000a022000e000000802b80290320048003400337902170a48005005c002001000d0044000003566100400020000f880240026007c0020301890002c03300b8006000001c00043a5006e397b9500b7000403a0004001000024c03f007a001834400f401e000413d02600000000001037c017001402000000050054002017000200280e500dc000a1c45300260022001c04c0120041099c018001001500040040008003009c003000001d012c002000037902940140710008013c004003800000c40670020003014c015002001400241ce0078000016c0815c5400a0004282004004b02357eb001412b0480003015400a007001401fc07700300bf00100470010018006409d0008004000000e0000005004c07a00c40310018615000004b001e93f018c00b001c013028c02,0x12c157c43eb0505380530b7000001e400600fc003000408e00d00030008000001407200d8cb606ec10b0054000001805300ec3800648160000c20b00700040c0801e066c00000701cc00b4000014405d07a005b0008001055800d8aa400d008c10700186410000246002c0000198017009c0ca083c000012c3de00380010034034007c009003418906700074808000035c01d001c001016800d06fc011153eb9b05200de000803302c4104047c0d1058400502b01be000c1f605e005cc0cc024023c03400802dd002000701a0043041002900000461b2843a002002f004800a00e80c300000038ec802600d81cf0220067005c077021802f006419d0008003000ab230000014002037000ec001001400a069c006037c91a03b0007012400c000007a03c4008038811400f804002380000b58002000409d000000900001a700b4014013000138e81b9067c00101f000e04b00030081c9500980890384020163c057016c00201b801f00240060a0804b00e8036006800801a0004002017b00080fc0b38016820c007078000000040df001c11900441da02bc03e01080ee000c00a0d78cdd0b180060a5400362145e9001003506e801119fd07d005803e007800300000e301a00bd001000000a80160095acb057c04000180ac04780b506ba36d00480ca00140a200040c8041417900800cd000405401cc196000000003d813e007c00500280000000004001c00738b1c96040802607c80340204002001803306a004a14c000d00c80260000006007c00101ac00607c011400c0003007816500a8006002c0320077153816801e0a0c000039800287ec0260000039001000e000010702b81af5e902fa9ca8000000815500480110382adc002800002f800014dc0010014378000d2b70be000107400d00004192000007000002de07c417000000c6015019900180021024006bdd003200b00c1001d71a000c292007c0570018045001801200081e300040d6055408d003c03900201b30c0d52c00000ab000801000b80eb006c03b0020015009c0120018043087007102f806701480e000380d5060046901a8001022c0b50028002015c0810008003001000200e00af0004100051000400201490d54054000c0120004046000014900000a601cc004038c04b031c25900d400a00100579b481f0004c002003408a00dc07500380d904140180004110000018494c80750008062039435975983e003d80190010002004c0d801642ee5988206049000300140130038000002000000d0005004514749c421d01100120e9800600580650000034001c00005e809400068e1036402b03a007502ec01001581600040a91018001b00450d519740f5016400000dc0900054035074800000100c90a84023006c1350000000017400202300180014195002809c048400000,0xdcaba027c0020c0812a04500370018028001cd6003380190578000044af6d35f010c004c00218784c9000405f0db400101f00901fd00f0002c081004802b00d80000078004007400900c8140002820300141b3063002d042412d0030fa10008000011403d01201270b4c00d1e8013e455c012685421f001000205f4001000005e263912f03acaf50008081024c000005400000681da04d00010d3c17101ec3029018003435c0001805eb0010432f000c205000474a46c40000a7011b072816209e80b70f7401b06bc40a0361a1000a95aa04f40000ba41ff011400204e800006c402f191c0030004ee7180001d3c380d0000000000b400600080bd06c0002bd0400dbdc400502281f207000b10114a9d02e40bc00a8457000801c001c1ee0468005038407909fc10168a083202880be0130077017c00a040c035140a09a065416802c400b13201531f38002001801f004c04a548045b0d500290e604bd16c4003004800107e805813c1eb902bc02e0058000000c02b00c00100478000088c0010894074003c5d800600661aa40530238044023808c127401700002190004006024c0080048002013407306480091724010043c1b40b9400b02843b5060801b063c13a2b85ffe00800939a80d1e2cb004b0068175150c05e0104005091c0060144001006801b0004000000c00a2f2400e16a16a702a003b005811806e5b160f78acb0a7017a08d800b0068369000000097140081a30168014811800a800200040189fcc15e09400fe00083bd000039900e4aa5000c00d004c00700b400114ec09b01740160218000001818100fc001007802c073c13700c800000100541bd013901a800b0328eac008c0cc07480000060f9d00b4360006836e01f48ec01a403205347c6038c1ba005001a0088606004004b00024030a5805f000009400290a80054049072404a037871200680c7001c00803a84a4011001f3a1000500ac333011802a07b099d0fb86d0253003b160004d144456a050c1cb008c0c7ad200cb02e098a0f900860a24000000801401b0001934000b03b400901c443c010c2f3028c00000f829913f80190008061016800100280735e243df016c02f03d408c07ac224019411a015812b005426700001360074b6707b00b715e8066009800418cc164c22c000229c038006403b0004038022817f00000000060019003805b028485a00480610054001086802600080330dc8073007012c09700660000364000000200100df01c80014e381060014000005404c00100001ecc14003e4005008005c000407283c400015f40a702489a300343cd01f802e01e41ff008c3b50a340150008009001804814e000600b016346f4016020400101440010014014037c46c000010b0000002000428d00f019d067412c2bd413e000401253d410e037000009a80,0x1ba01d00001924eda0014f58000036d4d74025004109300046ca05bc15e0006fc23ec8001038400d006d4b50388870036400800c594d005d2440028f65001063f00083cf1ba0ff0017c664006048a06a00000a0c8740000f2700280071dbc90c00386ae014000402a00090000007096c25e0008a9f000404f008c157002800038b4969001877a00040411af0f34079c0f201500711d12124022829d002c171040816628180a100040580e5800b0778a3303c81dc00f4006000c04f00170fa00181e000b57d610e0a2a000001a003c014003c0191534026189c3d01260005001c70d02a8150001400030703b600200c30c402330894d880d5062f62f4115000000005f0be1060c01706d800900005900c781bb0722b460001d3b2ba0002000c00c0030000264c73b2774251221412203ec002a92400c005426e11b4002020404c26b8003007404d4c00230000000100b40c8078c478045c03503dc08f000010d00108fe04b248c006017400bc655205840102c4511019c0000538004056400900341a909ec013021000b0c241b1154800301641a5000404f00f952000000020]
def shift12 (i : Nat) := field shift12Data (14*i) 14
def iv12 : Array Nat := #[0x2f93cd05bf620b6329ba337a9161d831854552a6fb401a0ef45f11fde764c7720ef094ba8e7050b811eabed2954a4f48833d10387e73a4f0b979825b31b2c0064a2e3e230b5839e3fdb22f529b253306fc46549d8d159829b2b02e548df23cb208710f4db383c1c55a4198a3260af23fb2f52c47402b459826fb17d18e4d369247e545ca3aa123ac59d13a24737e64a18de189b1f55c9315a573bce296843f7477c9c2e088ceef033c31bb121007a9d5f2cbf2090eec9af7abf21a9e66392f8c82e2c5c0eacf9bc347958c85180c4a7f759aaf0e60321dad1cec331dd5aabe48b765781ce8c75b18ba51310f4bf612a486b8483ebd6f97b068246a8b15d14d6a5024ab2991523918401fe18a23a827ba58b90a985295309592a3a806b3860bd596b7867858d648571ae7b4df061a906c9f7f469a0955ba2cb1e3790177d4c2a0a88abecb49b7832ff5f83142d2bc17e97152534c7deb97c369e22b5dd2bf3c816ac9a9b9436458f1a61f8a323b444cb6a9f23fa229f10b4953558f156e587c5fbcd6b3fa73cfd1e7857dbd6c832c3ea47b6244870ae6ebe25907da02faa3b47b526e775b212b056e349089a215e83ae1c5f37526b18da025e563067c825fc0b6d289afdb1bcdc08a8e20ca083a99061502f154c27287e32402298021946cf123cc791c3b429c3016fdc8f9601c706c03cba37a3cdd71ea9b1de23466256bafb5e0379d0b0242ea25d2c198d463c759a1300587073711fdad2810282b83fb61bf8c3a17ca0af20caaad717185d8e1e0a6a737bf09496fbaa674dde8a9a2929e19061840a9d520c7970e68ea6211a7825c4b234da4e1b014f9289a1fd3ae152bcee335e86b0c601b25b360cc2d4e0bec3b619f144c9918aedd46644878586e7db96190f7e7109283d16e94a3178245746c8ca603a8a73e01bf02ca109a64385f782f018ae5205ebec37b7d18b4de62f845f6cc02b7a3ab996601cafe51a373e081d8ce055264c23c79c2d5f59531a4d8d2e2e7c4ed12655d2b22594eaa0cf19ba13c1ecf33f44fb844b807f9ad0642d21851512ebc15d8934849f3d3b21a31c1a10da14f401c97c60e7a65f1ba92ba06d4c1a01c9c375192f98443152a8b96348a278524d87179baade291ed73199f9b6185ee8784d17a5a58610e13869ba943454d190c6a1c9b836ca5d6458e04272096d11e54da60f6e392ed03461439897c59c4c9743b850b475b861ea15652221db95a61b3a42fe23847f1134a40daa515d0890aa5fcee63a1d0481f623238bcaff93d43062705176d001e88367619a90bd6e7aa4b1183fd1ac3474c297c850427166ce7b8853cb57f1daf1f0212b990b2d8e4f6020a04c339009a3d7423d26768c4ee07a582bb8d6717ed4181a3b7d406030878190996a06ce87bca038477234f8e2700df4ea6632dd548ad67c53169d324,0x904be8d8a60e40f8b2ed8db01f5876e2ba215130c349e93f4970420754914822425ce74c5fa9186d37932f6c2f923ff7b46d4387ec8cae59fca045ca81af87dfec3581f20b2216cb0d6d4c3b36f5a721a10d343909596e90a80e081f74e8cd0657c3ab7e60acafd17aec0c486900128c4cc26537b2f6460ea425514346a787518f8339ce40e8930a2cb452ac749b9398d523e462fc1d78b83046a3741cc104fa733cf3dc68f14235778e4ed2ec10fe273c80f55ce9690931a73c01c890d06f826848f1c2e3d4912588c6c62ab23b8a0809da1068f1dc0ce00da74b77679068858e39b911c96c771471bb515552df052c3821a5bea759222a0b5f16992b50ad30dd11f403d99f7404c348bcccc892a0dc328728d78c3b184c754627e828e3c981f48967c6a58139763913a08b93022471c47b9c00b48985747cd068415321e2cdab4165b96850a6066038589e41ba419c8d8524ae5e30a2981eda5a01f3883862318f581b0033b94c413b8330064a6256cab28c4e3e7457a80ba79dcf3c55bd0baa893e0f0cbe10c1960532600123bd90634014b06a4204185ba3cd07bab8ec2532f9e95ee2bb06acce32e0681aa248246a30e61c73e46282c25cd9399f89cad7f929f0c9611412df9b81b85f50382df4d0ccacf4878bb185bfa98e528c13e05e314cb0daaac9e1423a881e7d031cb4b358695307632633a2721938da69fcb0a3973248ec8f6581e56e08d50e581a5cf306adffdfb8152d5b725986062ab771818869600a8133180a516807110784be89314f9fabfa438218bc41c12fc7572ace9e11b4f34554e1f0c82b4419840cecc1d5305802c919d208d4b3f8ffaa8fe437356939eccf8e2263d798b2ad9b214a1b776f20d3f659ec91f479c731d4ed1b5b375e0ca5300b5c40b5c1338f8ea4ac85cc64a93812fc719ac8a8de4d35b76952079a531aee38ef6b7c07ec9a2a202e1cc9e27c32a44890464bb320bb7d2aff65a402a0416ee6bdd66d10244b80893462a1edd3cc2def143d3da68a8a58403ecaae342e0fea14333ae05ca913383c2a9ad980c4348bfc250d208037948a2c6d48a588dcdc518c433e891f764880f881ad0f1c8b65b07d223f0871dcabb6175e2df115b24b4b2db30f687a199584928733d544a7c20e22d64977e17911e8707e1bec24ff7ce32468dc195d45124fb4629dbbea4ab6443dd891ef38194bb64f5815546d963f448c5b1fd38573084d3b304e0d871ce8e12856d7bb119f0fadbedf6198a120da68c688d2b0941e3395f581087f605df23166c62020a4bc896429dc980d7fd86d61fee857c2b248026a6b0d00dc8ac61971e2ae505742da37ac24d0f770d194fb501da2bdb1aa50ae6425c8fa85f3d032b34547bee0263cd8d86f223112066fbf8ddc9df6662b12e123d17700e12e6a182f166b21b0b154ada83ee966,0xa69c9da97a9606c7e4620cb6225c11ac63bd05348ce8184089c9fa0fd52c246dd6052475c584c9142155025619f27edd9e526d8778c35bc664c116688639b649f0382574caa391969b1072830da86389228730b0310d2c2470619c9fb4b340786247cb0b926194ea123b224588143c65b95228411dbd151ef50760bf547ef0c4c50d91da95ec44a07f18f42aa554c4620fc1f0855c2c08ad3a4c390512f6c097598fa23851085cc1664435167fa86412993fd46b429fa15cf02e992f08bf59f6c2b97836425408e95f60cca67c0b7049ca38ee7f04fd0bb5882531f4de471a154b20d3b54203c5a8f5a677c9e81f2f4b191f44ed216d285626b3c206a34b4b48fbc8b31a67d96a4579c2bb3a116b970b81dffa77401ca2a8c63d0d594f0e002a419bc504a7b22647d83f7e86e6c481f893e751176868c425236a1dce8d083cc36cb678214490e595ad06f4b6d52c534e06074e444fb124c18c0eb311ed6a05336a90ec09ebc9886316e758ede04aa6820d4dd46ec603131e9cf12d9bf3570f02a7600e0e773de2bf423debfb01dc8b71c5432d6013b0d33c785c9ae7574a19c025306f62eb1911a8a243634e01af905a268a08b63011cfc411478c2c2a63d5950a5c4c1145da68737295e591df8d25292cf8a7b01a745e8549a59ece3c8d6d588a5159fa53e520d10fe844dc13537ea2d46138f3c12038a42ba35c3eb605620f48b41c2af2c3a782525941ab9504fd12114abad8bfe20822d8a476255219e8db52b4382387ad8961a64d55fe3dc922b031773c4c621144c89f8bdc97804432ae4166e3e30479046771ce7148bc081f95bd84d545072ecf89209d35175474d33068fe4b14b3445ef5269ca49a58f0cec02fa3ab3e6594d67371d034c463094f6a4b8509da56d30c2ccceb95c50c65050ab5aad854648f8218d416e8004b1b1f40180786bb1d916baabef2c5817a4fe1471a1d1e0c048bebabe2b48885e35495f83c90f07d719b1220b7cb734023053078302af9efb3bac51c26bf65d387c8572632ec7d29a576f8eabf16d1b00351d2b8bc0e921cf005e054da11a71320465bb4c23a77a61ec157e12b37af5caa8ad8835a49b2c94f43e2e41b652528530178b0659049a674e3af1855196ee7788a28c4e5f84fe21adeaa961880b57e19ea5201522a86084021364f870081e85a46930bc7765ca53d021250400dc33aa587eb4eae81ccb5026fe117540d419bc78690cc0c4d35104ebf111d29a2d0093c6a04c982298a0090d629f690c4b46dc64d07689f1631809c686f4136b42169020ace3b1418f2c5750cd045288c0be6519fb51e280aa39c99f9ee049229a61c8cc1d639f49e8168847972658906489e2bd8523285f1889377a242c0be504997b52aed08d5759c3067e48c09d803a167371292a167e962581e907d91eaab0c67351e0148,0xc8bbe987668084c3abce16b2c5ece56094e819b28b31485223785d2950de8cc0733644f3089a6b2692912360c730464594eef9289a10c442402cb9486939526e5503dcf004ae4670ce4a8a8c28b51e8a22c8590b86e46368c721d1a736470c1ba9698b96262fec04e52e957e3f58ecd1ef5453456b019c62070c1118449de568bb6586890ab5ddc5bcd74da29ab4b5d179789b86594667b979011808fce8792e95236df0a00305926d3894656c73c9c368ef37d14922c16adf0ee25b2398a5ac730f57c4385043d82d9cb779e1a1e1eb08cb001e5c44022b982b1a16e096067a139180ab66e0cd6e04e902d1dbc8ac1f8a88c63ddcb3ed74b9bce6486ecd97738c6e2ea406d96bf389f4da0a56614f46612070d418369c6ef74ec124e08fbb3d81d4a1a5df48e572a3cb8d9a5c9a63817eb971380a65b87cc09a057c2dc97be2e66546490f53a504c44d85af3d31e2ffadf0215ce393e3d95d3dae6c815b270dfaa439d28befd0a3253d615c367a61d73ac8936cceb09a41048561208ef9201b7f9607a55491ba992c50da974537fbd8a0e5e7e0614ccaee5ae32dec8a7a30e1fb48fd9fedb54d62d11c70df029c01ec6c7d403849763df880741fe21448e58414e2a01a7d8ba050b824d9841307cdcc211c4ab14fde61118b5201533ea54fc3eec34288282589f301c0f2fa704b21562ef005fe06a555597a194ea225e1bb0e1c0838b920a5e353d0d1c6ec4f68a9a8925ae9fda01a5034d88aee1bbabbd474a0b8f8b1f0c6b72424268807a3d31bce6e10ae63ab629963b6883dc84d2f6c36162083bbf4c432cbde17ad822d0c45f0577aaf941066349bea286b4b8e8045fafafe732e6bef4c2b9ae86d424000189296a5256c1664e3a94c31552525af5c9961f4ca1f827499ab7636cb78b6e0892858812319b233d928a20460345abda32931ad42509a8682889bd1b36b12f021ea2b157ac3457e18252607c8249190306a464c94ab2f165cc5eb44345219abe39aa3b902730a1a961bfbb5d7e08a8ed3f5a46a06293195c500e907d867314bc3b3d66e84cf9cd781d3d884089fa56e03c74e9eff21d32010905069d10a31aa503168a6723f98ab60ba2a89d17085ad12b0ab0247e434d8c388b48b1eca0c2cbeb854ccf451f2f8cf54c412c88287705a71cf7b76977b4fe625e392533d24c514e4713ab3b828dd9706a6196f96f134d2dbbc5482d1d70193b4ae7b6ac99cb8e4a14728abefce16b81718b324a552a21c307fc9d104c32d9b8fdcba965792d50732c1fd5e2098960ce868099b09bef8f66b9e063e19cf54586fe86a995352c6aac45b961a0e4a8f09b8c191fd470203ff1f57aeff6c2f20a162f07357d6912592ac0dcc032b1b0410aa8020f8898fd1a7be222a046fd96ab20811adabd64966bc763aea30adab3cc0298527ace3623a5b34,0xda919a9d42074155aa9abc631b7d650c12a561aea1c556506bcc7d62177767c5d80fd3426053709ab57f017b96fe67758b8808b76f7465ecd7f9b7e79c40530a0f29533606e149c102e2768a1199ddcd09822c90eb259fc307603a6f95d148a7f919f0009195b27bc546af9523c79446205efaa587e0018337d1a107b0bdb08c36c821706b90e664c54f5f550f0c6ff475a0e86cc27420cc47519a972b6bec38983629fb803da6e514f629a24c50a9c9a8d99e70d3a8c94b208e1d1f36acfc7a021a31c6a2568870b6472ab23ae5bd50fba549a4258bfb235f83f83bd60989cb64244ecc5fcf8cc603e46cd44f021d790bcf46933a95856c8210857f31bbd230ad4ccc96b8e82a2b0ce5de31ed176de2d454b3213d132a4d3c4229c1b54f40ef4ad1353713aada091408ebe279f0c0d1ef0369344e5a1593c356b4298e1cd2a9341f27ea5268328889c6b6688b968600885fac950431f84597bf07a5881440cc60d8308d865002171c43979a7a3a221cc4a675f81006c57ee5cfd2a4a3900f15061546f32254f58d8f0cf5b81a29986645fd402337ca03c8443b93a23bb808f52e920b422e8e53cdd917a90622760e241470a2484a7d99c2b40771b11b09e52a50544490f8115e9176252ca9384a6119032f08d19bfa1c51005467f5a46a69244f6b804f2987fc157c936167b1220712d0e48d1eaff206048039af240e388eecb5deb5bcad86aa81b92ba351f82da1f75dbcae6e690807b85e14a2d30f221707e606d97c9aeed4333c6a4764671894b614c3917b1a2cd6c3d836b10e5555213e61869c2d8109ec62409d66394d39819b561661647e796fe7212f6cd22982783e5413224b1a73b396a2605a90afb94a86986cb3796b385f8955cf54b30475d22729d9d4412894aa945f24b7a2518c50a883b3dd6526d01685fe486293e03cf52323c60225438642d94c4a3f3627fe35c1c390ef20c61a510003240624ac3e886c94ae83a75e9f98bb1110db957e99d731f72e1846fc36763158e5aca86c4020282b501ab1a3ca0cd6fa391de26e284ef29f45eb85ff7c481c6dc6d3681216841187690aec2af0e5a4935368a37fe894a59719381c06628623599834a10455ca269c4598a928762f3468444d48580e5c830a77230c701c7238b332a9520d691e8d80262391963129d6ee6f7bd6a1298d1fecedf05e498a61d80c3e067287055c5e5580b431b1c532b2bd14df36fc508a9a69e053a0b2eb48f4dee342d26e2c4054b54105d7be450881753c3c11a130ed4e281a6818f0770d754c6a3b744b25cb6be7b209e976c0148da645cebb30c4f48e619723818ded0cc56ec6291cdb647ec849ed0f5779c48864a6610d02b0d045f186ae220b1f3d41e808b4ecfaf4c4ec1085c232bf62244a621cee80d0473780c85e23024b42f46972600403519a6365c0,0xe2f25948a5c6d4c197a2f06bccbbd4aa005a88760dd54416adbf680ee5556ca446f3e1e4a1599a0e1270fec2907c534e71536858d6c0bfd31bec0b0c411b52369323f2cff841d88600306e287aeac7e74d5c20bd05dd55ee97bc050906c8928d25064947ba1c6044f09c6b57505a81b404339b2b25426e865519a9a647801d4933bad3883f1c065fd07445386fc0015b3d937c510fa9c208d8e66c411893dc1771249424f0b6fa2c741ecf4e63ac112d5adcbb50d11237f78ae21b48b44a320612c3c910835da6d205a911763e4e3d1c2f41364b57c3916dae170984f4733903f1797a9d324262fd4ba4bc9671686eadaef001b028a1ec099c2aae6f686505ae30d4100285c520b41edf91b032d4c2748212cd02bf517d99fa05141c7605c4b0763e0c2dd85d1769191d19e1ddc88a55bb0d6fd4aa30aa73da95455bea95528b451563970f87210ad52d1c2a1ff67a02348a0ebbb6790283f0524acb277c51544238345c61386c5584018f62c8eec14557c84630701185dec8ff84262fb0154d26e18a0911e502438b6688b0e81c9992276a92bd04661356331cedd60297a3c66984b674cc5a8ba6ac4326dc5cac3b0f3805210338aea4dd0784a47495cf4b3407ed061ad1e5c945da87744ab53fcf1ef016440754352f51c92495482c62c9b9c2c9ef91de31dc44da2b8368c27f58b40af4a0c6e6be91f705f50186bb7545ec78067187d1e5efb3a57b2e6de5eb2b8ac70ecbf71515076b392259a8b1d80f48b82195c03442203062fe448bf997541d30ad0b1b00a72d26a340f0a13e9613259a460ab30c2c2834c25d214ed840a44cd5df4b15499e61983e68ab468fa7c4df58029c3f6c20d5f59886f76be906081a961f18a4db4490e1660708805b18158f1703580fc4a088b53972eabd442a8b294268dee9e601a32659e2599ff4c3ec97025aaa24c9a9343ded130ce393878b5ecfccccd197122a8a4495c632d5762a43160351ba34fc41259c1b0ca92b7825e457a25a78d0b257a27a293f06ec47ede2f1d497c98ea44e4613325f682668bb08fcc68bcdac9f44a1ac5f8a4cc0d8c3d4c024c49042b7b0c40fdea3fca4c95994270d5398051d887ab4343c7f6149f6df2db252ce30e867a26059145cbad89e23f82370b1bd4d12df30fd8990900cadba92dca6bb19fc36b5dad436f2e968ac12dd94637f46bac5c88c7042ed91d8462bb9165146dac5fac231f1db4b70052bcbec79ac04b5b792938570a7fc8f75c9242b94452242228061ef63d1243412c709d28eb88cf0cd7960a2ee5a4943f1922c6e0555e40a77d583d4822e28d287b01b2d00497367c8cd028052be302618ea78258842c824086d87cd89c7121c4640e08cc2a79cac174008273a569526280374b09744e24812cd39124d1a04012069d3a933c0b1a5f423e5034665a5fff06a37,0x1e34abd83f8b58d078c6589cc302846730e92c4a8a3d18fc91078cb037038946052c14f0c6036a0afb23eb3dac832511205873d776200fdb4bff44e3712831d562db6851b3659592a7bb7414b72cac8eb44a88b04770c63783a9102aba6942e05a35122b6853b7489585c8589951db0d36768da25508936f5b0453c157cabc42bae6614b2205f870368df4c9c3c8f6460d3e893722be8f88b93ce2e0e69492c199024c17001a2aca31242420f3d8e09c4de196d158c8173c15219689218b474be83b815edaa5182b3bc7e5e42e321b8ebe165ce644e9eb681f674e84251f6a100c603f20dc659093750b304e8b091eaf2366577c83d393b4762b6dcacd11700e94e7481ea8e727176a9017b90e01680305dda7f8640926e6e3c0a3a7d019b64d124c7af957df4a4a0cdc3f9a93a093bcc002a7883fe77a5fabb2fa5a74a64c09ec0403320f1d5c0eb12b187f1b5416fa8d558f879c8001a41d087ae691bc1bed16af26ce021acab907f6099c13b8c7753f41605a6d2ae96f69140d828321f35da82114dd266971e24eee03c3a0f1726e0d972bca5342a43c7d16b93f6379af7e8d05032b403c9850c02c55b75d4a93a3fca92d55d4938470724a7454a980e409104750e2027c3d13b41462851f89973a7d3d08f4017dfbebe4e583e64ffe3d5418da724e35735582c6ef364c97aa2d1a0e464cbec95565196c67c678bc6b10b318cc3b91a3628763869d43b0fb88ae517cf553af62bfe6ba8c6b09bb51ee9d864b729b52d6eca7931936198404c15d832963187e51a41db9a87c2c8e5005e13a93d40d30379bbc49914caad29612cb60c7dc0d808649be5e538a0ec1b443c1b1898533a1aca7a974bcf80c6098bb161fedc55c670ede7604616a2a731fb6ce6936e0314111635c58240a4bea24f1882f161bb5ac3164d94dd5d9a6b3af4fbb4b193b8810c10729164ad72968028413908a3564041d457e333f42c2cbff1c0ca4be2aaa9e4e46e26694752e70e5dd27960f8293a9ac693854054fa19f173a83033f13acc9bc3e44584837e34c3b087ee883917903b9f10604b14574c5922ad80bc13e5a9975212cf9d6c7392e32f096bd22f22d493f268b579f9f269412c57a38423531ce65a74de6baff233709cdc9a4768787cab3a51fb781835f18f1a2b1f9d0852bcce2c6a2e284a70fdc2f5af151cb22409b8d846d15de36dc9164be266aac724522a8650cd32b8a2bf19c9175e63b227d9f9f0c6066864f2403193f63999cec275a305826bc846104d56d6a964fe5c56003b21630c92a3c377b12b24684cac7778403bcacbc36532ee2aa457816f77ecc47da21dac80152502e81a69ca38f8058e42fd97187ff8f2b9fc5caea11cf1f4a1c81db365cccf85ea21e064ea25e10da027ce32787468b7e136257d31ee1f77947b623420d97aabd3c45f2460d,0xc61afeb939c351230433102eda08781d00a50690e1f887b8c1835feb2a284c946690e60aab064f84bd1e76b019fb733178ed814d14fdb16c055e98bccf58096878d2bf824b3ed27c240b7416c3e5e8bc822013a5237c3348103cb641cdf3f9a74846310ac912e1281d9b61bb22576a2a18ecafe33310f1da32d33eb149a6a51da72f9d765709accdc815867dc76d11ee2e1f7732d9d93cf384a2d5d04f05ff28b03aae38d84f626523342236d04ca12f360a33419bfbe44044710a486f23e3288261c87bf3b947df2f12644d239291f29c7056996067eec8d9dcbfafb073b48281bf88907857b0f2c1480e904b322ce0407a2ae5da09798c28831c0192a1f9420249b870c193d970c29a269260ee5b8c6d231023cc0b51a9122cbcb9c478a982277bab3b543215d01d6d0add0761f393cc714801cfc4fe042c6e0d1d214371152b41e2d2b8916f1a8540d43300d812eb31df7413c96b36ff199be075b24b317d14f836415bd4d138c5544af29a8dfaccba38967c660fc9de62112807ae0b8f62036e4de870d1601a25892847529aa5213290972701da6c50115bb19f9c479b73277d30ac5fd104352af1d8c23441de257a5dd87bb335336a45e34d8380464dbaa3d52c64a312f952ca47ebba861eab22c006d852979a432a2081b1464d4128e9dde00c94326d35c38013355c2eb0a876283a7234d26c4831b19c6a189195150080a800a583463aac4f2b0631f8ac48d4c83d47bd1f7037a9552a416c3c117af848856464f58f6b51f413483384c0b6e1471a9b6fb1de4484ca29817317a0ed006ade5313898d0efcdcf1ba0ad6d327ae8ca11d143ed6a438671894621928f616ea44a61dee1494f17a97485821009f1cc5bd934af73c987b2a903ee7e454d93dba2d6a2061c1c352807e8efd57049b6f2544968645245491517221dbce2b41685663f175b1d466ccc756c65802277e9d08fc6fe3c052fae05a599b3e2a7cca34991460bc9214c796c5929c553b16be692b4a9518e66c22cfb9b9513f3c36fcc4e1bd57848409e0b58fa368f04e96298c8f35a6a3b80edfb8c9325255f1fb70cf5117849c5f6d0a7e1ab634c859b3d4e6e4acaf0dc44b937dd89842008463a09ce7aa46ef159979a510993c20e7d268a13d40488eb4776a1f2921625891620bd921c100385d802b6488b059f78e296d15bc913196e51e080cd9f5243b6ef35d003e05602c1b85b4246da6cc5110980cb65e871093e9e4287d6459a4bf9c49a9cc92ca0e91ac51e0c446ae20ddb5c96668b04435fac8c7a504cf5c4e3dcaac130839217d3b0d98f984384685c2783c7e2444d220bc55dda8179d4a044f834679e025744934ade0d70f7b02ab3a54b808088c8082bfaaa759e339db647efa606b8c65f965476f5661892e152e2a0a0b294f01bae3bdd8c614e01c48d33d6858e85,0x935ea6eed0939bb116120b61b2b89d200acf7f90dc1c26542619852e245f17c24f0a0f8c3dfd8e2a5e212d5970206a8378d0a123e0742cb0b5bfe93dc6472dd024e48b8003568f282afc49d318e03c8c41136027332a3e146908714046ef8bea01c27706f3a5cb34a3557220120139250a262854262dc9cf25a684ac855985136454898168a24348ec29d71fb2881f89180a3030f2e7e40ab1e511e0be788b085244f821ede3d2286292c513f776fe467626833be78140b54d79a64523709724855297e35cc1ae5fd61fc2631e0e05009c1373cf70c460efb67621f87e2d938958416304161b15135a05cf0f8c09fcafc1051235093694bf279a7f721a099165570a0f96879a6057e02ce8635997c7c1cd83cae41a9045f2f0ce6311f4b7db6a78e4508c3005f4a3c84d39e5800a462316541ae482e6b378b5c87021f73091d98d975c46ab1c007dd113083ca3fc20dd0fe4454848262c713ca39289e3d2d8affe281ed7cca73816b8830c9ed264bfcf51aefe70fd74acd2ae6d7c51c60b7500ba447a5a281b81e5ad0b6429015053ae55bde2e399740a0971c1be0de21ae72e18fb4bc44224c982065132641f58e0b2247361114463368d54b84782e0d875bae05b1677836b20991eb44f54a5255f3ba4785b0df21ad41dba8eea9fd066f825e53ae487d4910a0567f4867628a8ccd13d03095bbd93a99216c1c0346aeb261bcd2d20d600454a6c3ee94e4233e52150f7cd4489321f630e4d0120579297a606934e83414beeeec5fda9d8127a8920d89481434a3cef254723c5d7ba28f0006741752dcccff8154c88b180cb1fd5fe264201f2600cf9d26c581c4cdce3ebc52756745251ddc24ab22322c70c9d143d5a326de5cc6ca709492eab1ab0c59944bcc499af197086fb509f55250f4e51a6f691c7eb1b72df4a7c0291843f772c0d692cba6fc350118b4d87c1237d486cb48f74a173ff287e805baaf222c8d3b079c95826df6f4050c0b7a71728fb8a0f7a033656c56a4805c6f77de08eb04cf9b1e91ecf5ed72c981540846fa0902191223a8cd7206504310672ce98615bfa71e38c00645cc23072cce225a4b98d80532c22964c1ba5897a1d385cc9b1411849da152100406371014228bc66c51cc9359bd481224aba2d69f8414b1466edd88a192ee44fc906e0c191a6c65f0e780c80a3f34fa86a0564a489281a8840c8a6aaec05508d865dc0095510d0aba27c95e5484a92e0d862b0492a02df213a9bcb00b45581655c62f5973032541d25a28778e469c2d32749206c0e4bbf46c834a84f959d6aed28b991c9c9daade30e3ed0a458194020260549c0909a8b2a3637ed3d1ac785824b14a5218cca86e0a36d48f39015d5ac6d4170bf05008629ca19dc968524922fa3a7228281b806f9d90868b60feab449c78a5805dedd946b08ee230270bc,0x89ea82e874af91b34dae06041228a3e085fb6086fde19055129065627851f935449058fec81c85dc98106e180e7206030bc9436b6799a39a46902b28403e9b30b07321044d9e4b8d4b9c0a39625461f582ade8d03c3eea6c200099e329d51343e8eb2140aec4264121c928734d91db211a55c48b0b6850720184d91405ba43aed13584954cd520b50dfb8d124540e40a02a6112b242b1da94918155a03b2dddd8638767c323c80fa138136c042ca834abf5df4145ce6829bb011c301936d406766590095c6148063ad8522a1d3015b973c6b75dc794f25d5a11d51a289de1efa89f5d8593b670066705b0346b683ae05e429e049f2e968235b3db477930466a50c126c88f484ab1824426657523671e29246d54e051b9d96a1e49690dd5a3271d1c675ccce9cdacba4400519c2629b81b7a6a86adef1356a7df8951425b26032a12a895653022f3b6ee1d62e7b0ef5ad43880bb4bb70461c5d4c0bdb7df91c50d41c3626df0824d3c570599b0038edb9dd9842a109c8348479a0f8a12e6640c9449da8693f1a44fff2ba60bc0db0a398a0bc62b1226cd9f9a8a33b4287643d2b602ec446da21a173b6e83254ce4410139638a1e45673a6b55529e152313a7916e04a95ebc440c63c68fadebab2514e90b75a22e82046860ba4a2efc6f35154444d1fd17644e4ab3f1ba53f9a5aec9af0c83b61315787c061cd2c874e0e00f1668999d2810dc15fd98b692d3664c44b7b1cc305a9c307ff069a152e0fa5975b8186a0b152ddfe113b7650ddc1834906f981879dda65bfc1452e12d64513eb818702e712d605a587defe1c7881471606d1b5db8cabc992e6ec05b3323b2238f2e711f44af36f3ec54d72301c50f544b3db32213f21cc64f1cb19dff728c24b4efd3bc2797e2aa94c0b245575ef8254cb437561c68ced3128bf4907aaa9ce240bb1811c4d5c2e1a479476cba60ee691861d0f14a059f846a3f92d8e6476c5c659e7089809710b94edee125d209a1147d0e720aa530dc6c2a3ab87803c1755020d31fdfb86a7a77151a06b804f4c38320864e2545070b10c9475bf5f958c8d24512c8d62c009fc5c30c82b10e074fdac1c92139923920cdb2f505b5675de61f45b72e18c05047614d17c22d0b1bdcca006e3c4260306c3b75f208cbcefa176a765ece75f1a0b464e7cd3b0e8baa369266529048b42824a5ec3b4a8c1edc642a8501388394f60661f0df3e01fd7cf6d8699578f8e574ace8d701c4ee24af2e2261ba72d107eeb1ce96b70e3ccaa535073027f95b4de55e0444811bc1078494d41c62ca469bd191400b471292897071dda12d87350729c0444ddc397200f057e13c46894d903bc27fa69cfe4efc1e23a865b89bbba4125f050034492a77c2556249daabb4bc84f2a1c8ad93a9622ea2cd209f876d0dc69028d7b0d0d4146e9347f1205,0x89340ace220db10580baea97d8bea94e7c00d30439d852d50f8e31405191df1572c444cce0c0b9426fa011cf0dff221c9ba96a31434242268550f525fe18e5138583a0e9f4baf27d1a281cdb2a860019ef028326bea6b8cf08b7c921baf2c0bca04007ed00d4933bc5eb6aed2d9c354a12d874e8f7a4f0c04c33870f2992d00319737139a2df11a22afb0aec7830ccc0c38ac8a38bc6235218a03c53b29e683a2168103eaa9544d8d25036dc8fb18369b60d6d81744014edf80d9bb411500a72a095b6f3745ad2dcb3ab93173d0865d52bc9b22fbb0cd8bb3b3185faa63105d53f290b886448732267b605c2505aad47cf859cc16a60d935d1daaa6b8604ace4612ed6ac8bf1a9c09830ebe2153bc0005819f0a84ae7c18ba14a528e9d0596689c11e889e6950f0efb06618d1e594250918a03d6706ce70c8e32913d62907a7148ec68d1e14ec6de2c3596114c65b0fbda5c44abcc1a0cbfa920522cd055c600c77652aa25e1758d0d3d4af83423529fe79528755a0c36ab7e441c1debb99ba4822d3b94ad36c79158511c4d291a906d2ce0005896ad4f9a9958d200a1e21d4519cfce384d3394e54618217927d7600d07db026b86eae5e9896b7615b16f0382f60e514c611d0c680043a62865721b76434c46dcacac0c512504ba327f8926b62d222121c419bc68142c6c4f9e45b0d121e6923cfde4537412ecb66403b7a86262a2a0f35a3424bf9191c64196232c50cbc253c9007749c4749646c6f00856e5de32b1b696d5236fde7699d43bce90e4b87c0e075f8ce42238836327608a3889b401a2434430cb611ce126b2e25dab429dc3f6e00d92811d904de268e51839ee77ef06b1091d95aa8bdb0d0d41e0d7f331a6629530312433b85e707e28abd92c02460983a740339a04341058d775e06efb0ac540b77f1c73bdfe2150a1d48fd1dd9cc0fe11e28e042b91f774d72f9cd3fd9b326f6471b5093887586921220894c8cb5a921f19a6aaacc59dc9618d1d41cc4252fa7cc90cb68117e8951bfb09cc07f45f2401d28216f866cb810ccb332010aeca34741e472da0cfc7becbf74c5856810cfbfaa8290e7152b293e26f407074b96cbc893fa3a4de5da40f39662e087f5011f8c165ffd35f06620326ef7c03f11587efa63261d7b46a91d438e57edbd378f0e0a065964b604fa88fc625bb2938784e3e12ff3da15a08ac4624f367882f20c482a8143a3f121a99b24858f197a538a1f4bf7428bc42a02cc8dc97a3e57748f48602413ef0ad445ad511f5e535e257a78142a86e1554f0dbd85e8def4130901d54b451ac38caafe5cbeecc9a5a1b2646b09469561abcf5a4612e5b004b0b90aad6d1e8b45225700f51d52d45126a828821e46c0483d140fd99cf44f27d4240a837a2278955897a4852aafd8f626c8634d42de5915308d4f4094e49a664,0x28531ebf678c6c5001ae6165454f8b560cf20afc340ca9e9c4eaaf151e20d2a267b095505ab268984b34182befa70ef59b8f5ce8b5919689f0a0a18f2d4957c6357d3eb821065453926140be05aea44f506e2c46029c322406ea2ad5a34bbd537904be3ad38b3091416d639094f42d3ea684e1dc36c6482c8c9b78bd21661f0d283431a965f2cde34ecd31b368f44c70b4e95c5701457a92de38f353fa1e34788a57a30548f34faec20129b2556058691858c7c0f8d399043763e6452a5dfa79507b84fc9a8b2de4193b26745d9bee98f585c6236e8e6c44f0e701608915a524c0bd01990ff45af103ca61a34cd0b8c93651d38da424d2b6b4c8c916a1154585d03024df707ccb0443f0d547ff12e1464a1b676ca89c7580baeb091222279abdb77f71baa9aa358241739b009661483df621211228cb93915966f2888c1ea91e5fd003b1b633832345303396f323e14d8a5fc08599f4874130c7a58c41d52e2709fe35084fd476eb2751e396bd294c6c40e38b05316c0185a1be9f6155426ef06a0239782aab0ed71126ef65fa555895f96421c8e13447c8bcd62d30dcf965d453c1b70ee312eaba321e460304637aa76039672e9c1a032d1c82d12d9d3aab63dc22ea17bc21788b84fc38f719b410c8cef91fbbc42c23e2623de7d1dfd1cb69539a1723ab7068c0c419a3ed725a2686837b0fdb568e08a44d029c64d0a14c9bc481f99764518204880c797527c2620e931f43e8baa53438f2a83ee8ee8be6b2b335406e2550d4a4f8f3b2f2c8c1b1bf04ca65118aa0106836220c9bd3179a1f5279ca060acd72e0ac738d1b8ac113ea9b1d56606797874e99955f13f91bb420e9997b89a2caed014fe3ba6c02c048cc9cb34d21c6407463c2b48e6f48efcd58708162ca50da9c23978d519a2579f63b5540d20521c8683ff450028f8c1e6b60b9674c7261d4018832942a2251bc68e1a362f6451648e020e07ed4d8cbd5c6d2ee5765cc26094d7c6cfe07dc0743d6f2058a4f4c2d03c03c52408483b562c255d0cab1f65e38c220e4b210d51c884260b03fdf33281092351167f97aa41118f0b47507bc58652ef1b240eca67823e2a6013a5c383013912792e406e9016d06a1423e5274103be5345d65ef253da16a6976d761be287f314c8f17218718dc098a889da628569686b275c6031fe3750681941bc4321097a7b39ea0aa9e6ded07edcef4bdc18cf2b14336c05616aea45947b1612566008841b6301108aced6514cc7902ca0e3816e100f186bc8344bd53ee41a7ada3426b9d520ddf2249718c3b21958c829e8e032910f45790c24124f5d74e871b279742361a843d637cc5a1314872034b182f71a9244d1dec06c211e740864f46815a4a4f780de006010d70060a64320445c81c2d94c30391ac69b315c507481bd8548e028988b7e3122b9c9c0b,0x6234d6a7a792b6be598d8eadb11b8a05b810e9b4d597b226121a52087483bea9508bfb5124bec44cbb2aa895a00ae2e34e7a9df083464a7307984d50a9f0c1c3d3a108867657d4137589c1ab493eeea4462f9272986639540cd33b865b8f77c2542ccc57c6eefdc0e225b80847bc88b0bc4655a2c451db9c1bf16a2e8f852a8eb87c4e2a31839be8d89a713d9e8e0c3492e124b8b26a4d448266bbcca8a29a6ada47083be406c3ce850658b02af05cf63d7029541a13d92b90425ba9445e4a578d964977c134422bdbfab5ae898edef9eca2d09671e73f5e089bb92fa483540af156122272fc0cebbb923f891378ac317a4820309309a0c58a09465be8ac74b3714427de144dc4531fc83c080fa83c16546d75d1ae15fb25e40e192523923292ed67901a11141c1442dc75b0ae1761a69588d0082a30325bc062886dd769e967ccd319d429bab5b6076495392b908b0403adda634e6139e5b44a04e046c7535c187b53ca044cacf82a68cee14407218f3c6acb1094576c55692966cd97af913a265521462030a5713a0dbbe0ab0ec9315c3e0630c0be65444a12dabb9c0a86a429c979d249f0c282265a2c050a015a7a482d5113e1dbadc6cf389e64211128f0f153b647d4f039c8e64248771ecc0e48eb28f5bf86ca251c0176817f1cac93b115068fec5b858343ac96446d719ea8ee76a66052c0bf8ab67bf80c91ba5152a09b10741a5800920b9251f185abbd596b6b430f94bbb65b2ef314cf78c546f6c5c7a3412d4c34a0320585c3ae506a30eb13ff9673735a2a403e7236a98908f9c42729b63607081419140fd17ec77b06f5c81a52f7261643234554450667e31c8b747f204fa9082425f790d0d1d256a8c25e0adc5e1d0050132a277cd483b74c170909f4619ad4a67d09a311abb5d34a7614854e102cd95aae09d914a9f57fe6f851eafbe50149c5ba50fcb0b006371c4ca9aa85494ab2b840e4088f9168685d0d00420450ee6e81ce8645950e51c95b79442228c09b92631ccb0f671c0dc1516fb1c2c6c3c0c22a462016a05149f9377580a2cf117f960e0be26ec0eaf1884509aede5f512f437c4ed954dd016f1026c1aae3ed33d4482afbb0358161892b4b515b9dc42286b67048af4450880ce9e688ceb8bf2b7ccc4a569b0875530f6d80f435d1758301fc2e7191c304ab02a607945c941657608c6b0d536020b8cab3a90031bec88da5601284b06fd80bcb25130b06f7f22c0488f72482d2cbd5a9328704617a381bbd747f831c913b03744bb0a25445139fa84ccea6e41fa1f075d88f00f5c92b1009ac03c44a3af73e9effb4906426240088875ef72ae60eecd514989b5fd7d34aa11cff3e16477c5618181ab2424611cad52b96027fc72e503a3a7b39636424887b3e0e80f5141a1e74467773e17f14d34b0f8956e088c0537cb7d36c,0x1ddc8d423305236e7c11fa0b861c1a8a049f0304105ec6d79a433d163f7ee751233b28625d66a6615137b15ddc7ae591ab96e822252a452e824062980160ada9d10237843ec7db1f8d4b90a94874b245c1dd301c14bb264432a4197cbf04b0114f725fd1dac20b1e5e4488f568dce7144ec61305037f04a02f7cb0104555dd45c8cf23cadc08811ea0de5859a3baad655ab7b3f001303995abc13793ebd0a99dbd072b8bba11b43611b353fd6c414a0d93237e548fb024789c06cb447413e312906c9ad2e4537bf725ead25f1c9887a4202113714889cae8734681c5d19b7e8d125f8cec99e868c250ed0aeb0ca0873ce3bc84887e91410ea386c3c7c94ac632aa1b84b26579869251c7c33d0486e02c771b063307e8885deb81d695f4db80a5f26f83d847e3dfaaa3192d9e466cbd680c556044289250956949f8676d41f2c927dd40691bd2873f3ea07e88e7a1fbb1b6a9daa2fc8d808dd42bf9939c083002f2db16a99a0015e605f07ff1ca972712898097c9e80ca615d5f3397517904299e3c945fc29f0ad99f96866f5f240b5a5f73e6978e6891d50780441742a7be0cea7109157168da95060634a52b653650b6c521e12d2050344b2a727ee06d12ec80446d1e92bbc6e63ece9fccd85c38f3914a2fd2d12921470e63a0ca3adb22bdcd8d12061b250ff25fd0f4e95ad5a5cba909e724f86ebcd1bdc2e88404dad2d1c89436d72fbc77e2162a4dd28ec450146ca83d23b0010517a1c686366e1ec8d5381589629eee0f819da918505f449187891bb236799e1b4f6383c6c245d7b7c11988f3200c1158856f01178409442167da031660b4898165eddba5a016250438ed5e59d0d1f88be3b0e4b991a03d68d31a04d82ee50e851162278b1650f43fa9333b9488e6cf5c8a0844b1049e67102ca911b6b849ac87e1842e1ac929102c5852694311d48fc3a4f58fe2d8b8a20b4985044f0e0660980e1b8c7b9deef95a3303e8c0580d8b8a4c692d64b5f3e1411ee9e71ca6b2b40788cf6824f4037560e6e388d746d56d606f719a5924f077ea37d82136333a992a35e791c194f04e015df4ae62975cfa5823e8cce88170d3c6ad44580f2e90c10f3b7920300266244b2ec27f866fc05de07948361036e4ca961e194d2071e95ba1971181a620a1943a3432aa9c1d699a70b4cb661f9f1af452764852420a71872985a9e52832ab13e3116d7b101b5275a93988ba81db1d040374f9b96361e24c74486d16215e6016dcd509dde8f6116457b4220229d8d6e659c489d8ff6389e040bc796fcc7eacbd83c511752e738205295c907062c45171c405546b8453942d294b7caa696c9b34f5e56ad157b8488d6e44fb647e9b10f0cf44081b69a7917130dc483d4835e1a066d119652f6e3738838e193c14001d511d1ba8026d4a7a64f92b5008a2bc44441abf3,0x346146c7cc1493bdf96e22f0aa3cd268916900f6069210d518c8da917f2c24a2ab69a943729f0644c63e59c8ab6d38e3c993d8ad3be17744dc24aa2a3721796fde43b39c2487a2ad6a4bbc51a0a6d166de6299d78eb201dd48cb50879107ab0858b8ea69d52754261aa0895970ed5f480c2f2571304525a12dd28f045699e9a0f827d87d28e1e9ecd5fd2c11dfafba25136235d51eb470c4be0f5c00703cf417528814318050681d2efed633053f694efede06cb1ad1ad6877865a07b486e6ebccbaa35c37d902fe60a5cbff58c6a5c593099dd2a0b0669b06956319da20adcfb1b4a184d2881834a4458e81291838926f628290d9cc44b92c02080674cd11b31322246e935194c73d7adcd4a7ba69e701e37bce71a2ac98c00fad25e85d863029459b7c952f0372f9098493ef201bcb49c3304b8a23d44ec089a41e89666f6e0671c2c81746b7c19364ba292aaf31c129b50b857c0a5635590300254c70e2d5c1f37840d44e0dc02c496981e78dba80006eb6efbd4818a6211fae07c17287ae107433401761cff92e8db011aea3b175dc440927205463db035796e2a49d857a883e21c1b074adeab1d2580245845d2b24bb543667a52b165d4ec28880fa509a58b0eec2782836ddc3ad3371ca5dd06743d2e0f5a1514521ace172e255e83cdad102d5a7a6d2f51e66721ad63c33faac58ef2cca5a684b455488ecbcb461c9b24fd24013e023052cce0d0978da3d1355e71986898bcd7e0d053113bc1ed7b9ab1d023fca8001b51f8e4f5c7de7b5c3efd70d499265400dc51509fe423c512e83c0b3d613ef0da25db0bc077ea6fb930f916d36604198630a15452e6b109e924661552060d9e211aa486bd1304ed8ca7f95f300c936aa2576fa103811f318d8303499fc569afd92ba0539105ba00773ae8d043df1ed24f4efb5df49922391a32404ababcbb4d06a59e1e581fe7614b1c45cd91390f4e2f4c9b234644ce2d1b0eae422b6a8c2835b491e823c624010792b60e11183795d8fc94157a2e0a59af302274baf7cd820150108f419ad2193b1709da78a5288849c59ce3561d012b8130fac83df41c72241a65d30e7203234730d1c0b59496d734aa7bc71e314f080ade822864ad6890f22c8d472733335a6dbc799a84726db0cd0f3ecb750bdd1bf161c94127e4c83ecb75160a97a43f3d4ef213b839d0b8cae83ef79880887c1794bd788da28f931419f382a0aa5159a87bc8a062a69cabb6dd2ca09d61bf0a2f64bdd035a5f2ba8c6774385110d8cc3181ea7e5c15ab4546caf544911bffb0ea91ab0ccc82fa2ec84bd43c79c00665650c4abd399068a43770ebf115f2500efe803dba79645b1f55179964003748f6d361ba0d4b4c89620ff9c17927a2d0905f812261e915ddbd7bde936ca3e79d88c65b03bee4f4dc3c3784c1851c93ce03172601,0xe8f69f31947c6917161c57f289987989545a0dc3337b1003a9292a9eb0a0abc21045ca5b4dc2c7a1ee1a0ee447ea2919d02b08409e994cbd19a4a365cfdc04a12f9e1ff49acdb1d02b948b440f81ab216c2bb70b34a64831d745c464e0e415b86d4d0e4e5a3ca8b983a96a248c80c74466716dea0bf2e74d0ca716d82aab60ec00c9f66a18c01d00a89bf2831f95e0e31853a49ee021ad30a1591e0f712678841bda9082b630c55796b31d77421d5df033a5384b49dfc9ed2c3090922eb500d41ca8586f0b644a9ffb766e3b598a8c1582e0c958c059b68e3d7c67dc784313c37d49ed913da159589af749a8ec6643cea5d5a03443c87cd11020dda260475b4997d10a0f298dd4285c065913f188eb4b5ec6c03e4ecc3f18e2b223d1296a2b8e58ab700c42454468e1a5a721818c8af303646816a311cf2a2855ba223361c382cf957a24a61cb9532604a0a204ce90554033178c4649a64715c7331478a5f3394a3fa1cca24d605669620f8f9e811eae8e70180af4e3b721035115281925aaee1013a91a007acdedc905c30f3d3edb6a372c688789c218a349a1f6543ccdd43b0c2071d60d90907f003f91e89d5405bc87f33d633ee37d43ec92f43bbc5bba02c6e64efccdfe3c077f749918c42c5593d34b15cb424747784c502d577165c1f8279023b2474b1f6b025493e355001a0131cd5393a048010e6a1ab458814502624ee541a524b4c1713bb9c98405e573023982ed6d781bfa1aaaa8c059f2ae9c34aa638fb0bba022b44cb7b0a64798e5b7497a6408058c9be097fcc661ca06b8b2744281ad780c8888eaa6becdd92a3895805cb8694b24965eb1a7a4a7851875f6be284b51a3f229906206bc8ef34a450129657a6b090d89105bb5c93432aacc209fc46e99002ba2e1b022c30182e8f63a2c18f0ec4a875011905a61465ca1f45b4552e2e9dca0a7159f4dfe0fe1b7e1e4d1d504d7a2a61e26565e307d727a11041731594e9902e081e2c6a0373b5fa7a3b20491644b2e372af00c039811f5538a885edfbcbe921d1be0cc74a681414f76a2ec8fb2645d003995c33f62b6e3c6df6fa6167fa07a99ae5bbd32b02812cb8b897c1800ee8419d816f70cafbe0b4a034b0d7428c0b17038842ea334d4044a0319b812e9c1ea6805bdcf154237a4475666c0d1fa00e0871545ecd6eeabf8336a9b40daca2e905d843f9aed35dd57c0c95a567bd8e7ab131a4186985d0d242b2887642d187f24c6cad5bef73a4a504cf34c90661b4d6c4992b9cc29671d88e76a9bc817b2bb194b1b772908d4b14d84a1e3c6a27717e028808efafd71962909d7996eeddae431075438aa2471d0fd794485310cff8324916f1128414a40542e6466459eb8985a26b002085bf110c92901260c231364f80b5cb3b1b9a4de6fee5e1331d5376c1b392302c1931fec1923e8,0xd240267b85629ab2bf7e2030f7c5fd23aa75a9ce01da8687ed6de8341175305e248dcdb8e2da1ed55cc05f95313b7e88652fe08a2d22f37fa83afdf4984f2416721cc031a23b1864a7d1bd5b10974505591d5e12cb1ede0ecdaf21ab7450ce98821247e36d68aa08f3eb8f609c32d51e6a0ca49658fc6d558b7444200f245c4541c1285af52038a2b3f460b2ff416d1eaa594418441c9486b66eccf0488448cd1692bb853613e448e683f1e62221bc491aa5f216a38661d9ab4ad17c2bb23bc823b99c523ce5f524a98cec44374a020a847182e2b6ebd07316d3c5187e3caf95e6f1e0b8cf6bd20e53379c4638b9fda33ac1602aa6ba4386be0735aa9bed8cb9f932a1e5475a3926486164f41953bae884f888db4f788fca341eb9d85f43bf87fb0ceec2ffb5e0434cc700fdeb61347fc13fd23a4077080ef61904faa936ce87e41a83267f758c31c560db7bf18ec6e643afbc5b465232b973480500c52233da7cb79f4be83074231a7314d9f2810556881c2218eb0535cbdc417aa0958629975487af2d8cfcc9bd3295a2eb5384c36225f267b53531e2d952715c1490419e26533094c0e175e5dbcfc282538bb43eb04fc06b83fcc6b1e6710cd29da15deef795e0e968845e80d98f383c78766650d07ef3f2059c52996619262b01eed4c5a2bb53a07705fcda472b1869166d9a147a7df631e913a5d5a24f72ccad4c24e13198e7a8590f2f37e12ef211912f626376dd6a0c1b05144e49602ccc4de28cf25bc6c4a2cb10cb539e3e8878235a641af15aa046ae1972c08b45a261c2377c8152c8a5b8717aacacb60b32a48393c215936da43b422ae0e8bcf8b8e74aee6d0ddc81e2727abca252c8dbd084644964121fcc67be2e9944242ae7fee792dce38af90ba854de53b3ae0460493a4d8d4b0d6cc0d4990da9e880df07e1454584d9367a11e420b832b867cd8662d02adf6fe60c1418a2f7b50723191f7ebaf44bf68d8897d117d55c01a7839c11c84802db90922256c7908422a1604c337468b7f9e55943d8f846130a0b3cbc2286ef987d52bba7f14e7708ed9c4b1cde14bdb3a8e941afc53e935a999377562d3951e46de14f86190f99b81676cf2a46617a41b7b806d89d553f854cf2629056b1d5404c6e4fa42eb07970604df1b3918055740d88a310a89e3f50ecd55d5290e5b48b738d8b1d7934bad1e172608c0904408e09bfcbb66af71e8261bcb6b3b1e9e965658502850efc0852021d05c30b5551c191fc7fbc22e56bdbaa06c847d9060f831a826833f419888df8c82ea94af989f821dc551ce049b93599e38513328939280c2fa118493fb78dc98765afa4bb799a362e184277a3a72ccc0d56a48164211d561c0bd1a0c12d0e658d8fe723684454442052b08990a94b32be0c91fcb6ed9ac9ff683f8cad15cc45d21add01807c9a0a196a,0x8c7030a6d3c5314a7308da6e8c1773129ace34f0a3d3a10a9b40edbbc43bde0685c7e996a276c4b04594831897871c96590b3fd64b283a8f509aba19ee94c01e58be14dd663c805e0bff713c30094f08db339ac8d69b24061980b121c486ebc3a5ed440246bdc06e1000b17498b9b7c84d87010dbd07ba0eb2e87ce2612460fbe5948bb9a42785f4c81948aa2a85d00dc19979399b95a2217e1b69c833dc9172e136b9298f14362106036254ae6d54941a0a2a04f4374a2eba89c48e43599e84c9312e66c42d038830f842cd4918782696714c28e1a80973127ac5845befbb69441910306d0ad12643324e921f02310e4c6c6e2329a8488a051d458f9e3c388b0ed97830c09026ab10590d12f12caa50a0589b1573cae0f85ce2836094eaaf1cdb5cacd15a0fd3599e16c027848e8233204ca571e44c651496330679236927b301c356e1368ecb1e76712a662c8ed3c227f5edec9a089f573039083425293834accc61491a089a12371ca242b074c1106fbc5af023c347daa81a1d51d122abd135833e0af05d5f310a1b7457d411e37109b436e98ae84dd146003fe2be092609b3afa055f6bea933285628d06b120baab03e8d0c8bf5a74899666870cbc6168e2d16c6b9d9e6710ce3ed8857108f3acf5f74c92c7f8a1d83f2d313215c2a0014321738c7a81d41cfc3356046911d45ac6241aba0e705521290521d3d0511aa5cb0b3c8ca5376a0c1a1049fe87fba60bcbed127480551f82553433a6f2ca4a65769e427bba86180c7a95f2312d7265158ba74c0f10fd6bea3bb02e71a2d714b2cd6c4efd697bf0acd50191f80a7fbf81761e58f9974864b4d44c7b43b831b04d54ac4d6f490f3477028551540c296b3414e23d39b2c22c4170033880a96baa0cb9c85065c3040512ddbba81a760a97f4f57308e7766545cb4103f56c0b0ac62410dca648ccc1a4cd83b71f38831cba0bcde3a3f0e65072460e75a260d24d5961b193f0eba5e78826289edb54d84bc5d1ddea46124713be54a68828633349a852ce56132c8187039efbd21fd0b4e9008793d63d8e8803a0c5e5d0ab19b480e9e6012d09e715327e55cd4a0a2753245e0f7d20772938c20df4b42a938b09d0c68a4bdc1274f3fe10136206e8e7c094a4211a3cceef6c1daaa494cd8a4d6156bc396ee2d92878993b36940c75823a4aa576c6bc9e4d0a2076ea6b8ec8c037ed3f66d9a1dabb4aa65089392165b134335eb545376b2ee84a0c12d33ec12515a85d39ee9ae535d5e1acc72226e53fb2ff2ce10a57f16d4f8760c34233938aff599c9c4cd1f0831a42cba5a991744794d7c0cd9374470a18f327bf07ee5efe2b30270581acdea60903723ae319c566cab1b50d00d262ed4b9b2e24d8802b00552232d231e01cb7ad12d0825117fa5dd2c54fb99357495956e43ab233600f33c04084088,0x5dc8a74728ba36484361452083d6931fc365890b221618b36ad25c40398a46099050f4ce1517d05496788d1745f51e8a755ea47496989eb195633846758d576d9e655a1ff357056867561bd692b6472691f10fe8f5088780c54c6d480d6c8814520279b381bb4f4884e1492b7174abe9ebfc1c301083d91be7944b2a226499b62436f176b0a29732a9633ee880ed4d540e57b900cc642ca0c44f712ab9b82afe385e6061cdf93d6b8446feddba783bb47ca43048a5b53905ba6b2068a05e525ca021a62c04c6201c81311c6865b8f931355d47017f1402998058a933c96dcd0326083281326cf958b7211ca1ee0eb312968c5f936c16e98b1cbf37dbe2de9e61bdcb017cefde0fa168b5e24ac0c1e22b3d735c3fe9c0b40170faa9582060879242d26126598ab1d174018e8243aada74e4111497b130146249ce00f5b9b1587ac2bc02f47b43ad4821c23091f05ab51f2dbfc87213758e62c750977a239c1a30c57294a2c587b0456298525fee72a8d2aaa8a05fcbdd13830b278a5497c8ad82aeb5d549f99536b95b44dee00078ca9f243604a35c52183c8dbef5a46b31137196045208b7bb7b87ea8c99e8047df12f44e4c30999b21dfae5c985fcb5c53491d460ed00b319f4176c4e78e748ecf0de1fb4b42b0d5ee0e861bc616185b09eddab41bd4cc42ae9e7502e60a9e57489e2ade10c987afd53249bc0a1e680c16905d316e66c5c9bdb68723ea514e3432b087552d655cf0035947132a8505522d02150657d54f15f671732b28de3ae9c898a08ac1f39d942be912903ecb78a1a1e16405992bf677eef3553ba1b9e77c05a19138b7cd7c6e11b9c06c8083d4a13cdacc97b463286002032972469c4ba3df2336b6590b2df513285d57dcc7e908b318628808596c04db13683a439ada2d33001e58214c94fc87d3d44e5601931b9972e2bba4c663adc842af81ce373fdd779c8c60af8c2916828edf572184ef82b05f142e635fd35049299221a0446fc52959f6e17bb0a623ba939a8ee7791ee149d5196844998ad042718fc1284040a03f0b43f8dd023e5f9a10e34e1f130cba9a42e6640565224d2a1782c64400c7500d27f245f54712b27e04264f18a2eaeab4d60cf91350a3c9063e681e48a18426b0a79662aa2421388653b11233c4a06fabf6a11b17ac97c281ee19a1abe4bc419088342e6016fe15f5c04a2f66f8c2e7d5f90b1a2968d09552fbf5775146530c04b61e831a0358347838a372e62a8a94838d9510e2625a733b777c63af508db7b09144e08e4723faa73eadaea08d2bde179cf0ccce8b73e6b3099ce0510bdd460626f91b118297312e2c5e2011dd8524d5c98339a7f2c55297c9d7c60559a4461e1b01e9774aaef464a30eb26e3123e9750bdc136e20da9fde2c8e525ed14c57b05405f9e0c1ca96044909be4fdc55897b843,0xab8e18c6be18e2237f1df9c7dbb5b4c80dc82014c3324a30c4ecf28a6247e3abeb00dd06b64cb0a2d9dd9080478282b94e3a144864412301d8904814cc281d4da1a1bb646d248843284b215425cf1033abe84becc874315a80b3388596dcf9c1095d7c0825cd133785c3a30be5920ecf0a84b328665bb397ddd1bf87ca8a85095601e01408d447340b2b65e0960c5dad2bdc0c623bf7daa9d5820ca3e723dabebd96101626f1e3a0539aac1c54169bdd22abd7209eca43434107b914652b6ce034543606e99e153f8775340600491d5251513fa5cd0fdd0d393caaf3e588f0c5a7692b6f131dbe1e1946f96892e377d3d7a3f78683a09a7d12570635f0c8c2f609a94f6d0df41eb207e9d18a56b0d8121e1f8b901a55902dc261aa288552cdfb88c6494505e849ea47f9f957750b7c2569963135486f1178791c108ed292dac9205d36af138dc820571763d0e2c0332771240e9e0118b37ec79b0465591d0f3a31a2fe34b02027c7dde7fb5b6695183664316a418ba361d145be0841981e21d291bce8045692ff9093d534960863f01e81f904b785110d6459d8194e78e0c1990c402927dfacbda60f8b9c5d72abcc63ec60019cb0ee8804ad9017488be98222f6744b65b684bf0efc4d9eb61d35d358592f6d4f886b1868448b0a5e19611a543a7254c24da6cd2f4c79ba27e298214d8b7784659d071e6ebc417dbb7db468ed579560aa9635fd08665e6c8a41a2cfb5884f320c462076895b1b89e7dbb216a3b53e773c0a58f40b89af46ca2180120f0cbc4bf49344316155e551ced507e92f342971047904e86966fe0d4b8bf329f2386263e98cc0408395b036043c0ea6051e9600b2c41264ff835822cf97cf3ba6b94469609a9630e36c1d623c923fa21a620642c097c7f123d83d3e79949a29a48d0233951d0eac925bbb3b649ee5a49edb86a2a541a045b709122f36a011e5e0afa229d27c8260b4628a38dff5b6f90f84d8c6e841a7a66e6344b968ae187906860332c949b59011b23ef42b521857e72a8c4b03822323325771d56008036f63fa09412bca16a62fc4fcb93ee93cf11f4db0a96551bb1edd2fc06fb2a6065697fcbad55eecd5b431141b24d55018d565a82e88d2faf073c480e317a48da25a81b128ea7291791984b68c6d975ca60bec83208d011f9ac9e6626d600cfc426972d48b78d2f3c196e90fa50aae306179baace1f4e495c2e20b7e24f6304c683c0c6196d2a4b51d805586532429039d05fd3ec849c8946ee76109b13303d446c076dc7ff12c2e47492f460d00127e9061b90f546b6837255b9d84621a64621122b9d095258859d6c35f07865764d8900220fca0d147da3a2a4260ed14d5e23dc2f5c98152ce05eb02487cf45dd0be24292f0a170324238aaedab922c423a8138e84c17f2ce89016846550a19af980801f59,0x207caf04dac316c17d145f78032c4506437f56f640b405f38fa671a627bd1334aa58c86665a18c425c760041f8ed3a9da93b203f0580c867870acda5f2e3f01653693758f5bd74027b11e897705ca75ac50192e6880819426e30e694b915104bfc2087ca7802baef05de514c44914b091b5396d27b3713b60443ef63fe841500961e1f30a23f2155ac0d38edc2cac4e237f70fcef80dc4615248d3846081c7cb271a8c81f8ccd2ca475260c28f55260c53a0ee9d34225cb44610ad0e23bc6c0e5814255d830c97caa8ce9628212012a6974cd932b755b10f79c71198d55f748ec494500e32d8f0dc9da5bed11fc06e6dbc2855a26e6e595b4f41a68e850e5032c34171fdf1f1c49848f147e09184aa633cf8696aa8caa78c6c12e9075db9c3f8979465d3901813805b18b9442aa186f3f045f709de435968b72cd565a249334f50378714cc4f3c44b8d52823eeb272a638423c3eff231cc5c45f946d24fac6181d922df3504a8476564b627553a34aa3f33bef8012f4487e836a378aa99de1893c164b8608385a2991a135a4e98156141d035e0e589760ff2649a6c145bc2c34325695c243b065e2302b934035a87635e2f04d8e20cc07b54a67d9e61b706d8a209de96378b05a0af585098b405b300370bc60722190e8aee1002a6e079e7589ff8889151b023fdac040934430c9a0ee3b587281c6f8cf8d9bf87c748b144a226060bb4f8e08904c140e8630f48009c7c3d4c27223534b2868b45dd472320f26b8e0b98fa6851e22bd3145c9b3b5336860c85fb2c1523e470628e9b8c014fa668d417892390dbc6d7e1c638fe034e43ace5525735fcb2499c8a2bac38c21829331bc0607463d35741c55c704adcb9d78882f5600ea499e517c18a200c20ac64ade47341749537ab977c9404e8549baaa5eb6c98901f10c7266e88b119e35cc73b213557b018f87e2616e1586b34818392f42192815e2cb8e925fbdcba174c2ed0c8de8872444412995900b30763861189b822db306e0d20ce4c2ed42960f24ecc2a037d242cb07cd1df0341a08986481b7947e8f91e5f483e32cd2e2120342eb47eb800761d20ba551429ec475530977b3a2c160002cbc65124865df1b1778c90edc07af3bba1a767a0c75e8ab121e271cca04102e566ceb0d3d2af80464006f569faa5c7e3ce729988155035620b352799f4078f48e8cf123e496b16a0a56d796156042c3942c48d041aec44a10ad1d237c18d378da231d14c70f714b6818130dd0387d00099d293512a7c943122e09581079ec028505e1a4b6cf1d3bf197885dd5b3e3e2c099ad2cca7ec02c7d7a13898ffac2997cf2535b4a44da8d74d5b12b3a4107890abf550637362d1e76ae4e91b4c511cf3414eca5064da8bdf17102ef86b10f7b1edb2da95574f58851d1efe33fe2095d37c1b4509c7a29498c0231,0x951ee109c6bb9641b5cb5a51de877a6a7b1005ada00b909da9554b4b156e19aaaa1a4ee43386728083048bb44e5eaccd44cae8c935f98d5c81f625f78bc24ff0e5e325d61827b2e38c2cdc86ec8905a5f0e8d8b64d1f914110ad8ae6ba8d05235d8724f14cce5f82be65225dcc702bf2422162635f7a33951e80ddb435a1fd25540af51f3746513358538934736fe472cf4c538a8ce67928e2f58463b3d108e001555242fe52f2c278ddb2ecb18332689cc0b58398b836a9199ba05808e7dc23ccbe871b68df4d3c598935a7af9bca51470f2daece3dcc1411278303b709c887ff18400bd9d1c4aef53f8bc295163bde87886af5e1bcc396a447275aae2c1f1586a431d58c3b529848098c13853a83f616e2218c35716131b013b3a87f7cda6f3de89b42737a02c50fa14ba44dd0c215d38b66e67b04d1c31222126c36e3d4f928d93634916757d2ab1584ca84aa01d19896bc6fdf0e3f23f879702e4565896f52c9ebfbca33a6a456bf31ac7b4afdf6f98d7e167ab5c515b41a54c8a189b0a9a1c95e340cd68b8854844808f3359d491316aeb1171cf43a6a43a892b6d5d209cb0db7dc7c34db9a09c0ffc43e46c8d4ccb5cf8f7c572ca1fbe831f9a773cbb92f457d08f9008299d266ac0e6f981647731bc2206c4750a4a89421bc4fc9088b5f924391f7dc7eb1162f271ef6175f614ef09082f8f47821a46b1dfe21e2395ce078340c0992bd0dacdb0bbe7f958a4e69af621b3748442edd6f8e4a936a64317a91a7804aa79b53544a9716a90daa3e731da7a30b4460583e99820e1edcf4a0cf34d22e9140cb1fda41131a98656bd894867237832ac071601120d1952bcb933c4f1f5aedb2bf3d42d45d2a584e16b441c3e58c0977366c72180a71b7e5a06eb89efaa19923c26b785d9895c4496f82d3b643522a06b240e50a61f957e1c5a2bcb2b18ad8246423babd21168949db5f2e4535651fa23599074358257c555710793f7e5d1c645a5d64db8818da5fab9b2afd0411cc3951d6646f28243aac7203330ff48f3023650870f55dfa3ce7176cb549054cb2c77ccf62908cbfee66d4db62217b6d704ee583877fcaa86bd0392e0549acb53ec9cad1d7a6d2172ee37c08a81c85cce13011e416a005a640f20e990f76558753c9c51d35533511cd68da64b3dace031b352c8235550569bccc1ee2d6037ca0fc363f39d6f6b84eb45ad3ecaebe51b448c87c201af1b1da09164ee9829f0c858458d68ab95db26122bbf1b34dc9a3c494e67ed0462cab977f03fe6121aadc815ef0b9e0643635b0a8e1074c3cdb2d9623755ffcaf62b525d482deacf90ab03662546a7bc25c2e5717d9a27c91fa5718b05c05d6e7924e1364ae9110d062dc65fc6e328d27f821631a4f17b65fecbe5c5f287a23f7542218712d88db38f0e153a7c7ad039385490466ac2d60,0xe58283da1908fc48907383c71032585f05339627ccff965a992d680be4714add3e6b0aae12554599f7c1c7c0cb00001f8e3a32fb2cb794b3252dd1ebc56a3b0704a2b9143488bc461c27fb8bb740c21688df41a0224158d7843ec0cb80b508e4f3f0685a11d720cb48456d085063100ee9edea3ea5e8eb7ed9d49bac584246a52342c7781ccd048639466b664a932c143ab482d1c000527117ec5ca4000060b30050d9848f20ad838c162635f13db9b6220ae811dcd327b463dc18d515a30ac7356bce13289e323c8b273000092265548bef5a19b87400006620bc7039a2eb68d44d88b2002e4cb8b154c32e29150ff844f9201775950cd89ce37b951fa3d21f980108828e3120000c2b637eb25515e13ecf1a230efdd5e083c37cef50e02a3f378c525378eb00729974ca1b940f123b87328b3e04f24f00834e6da3390001419a70094bcb14a0000544e315a486206e9d1e1d695713172aae1cdc9b6f45dc38415da8e2d6fa70cfd34a9a67374c945e421895546029bc80b3456212165295c97943f11f636ed5201b4f7a4cae52177a76400028b664cc84426e160ec0f863984279a6250b64966d168056bcb4590bc1084b598021c4d926749ad06e095a0176f194d45b03e40000000182aa4ed037cb8e22d4427e435c8c320c09bc09103195407d8c5970aaa36d7352125346008f49ffbb8428b0a9d508b4b134572ae1947721dc2ab69ad9a751de2052e1bc96f747486cfc633a4b547a260d52ec52fcaa930a34d700356237890325e0a15929146ecefa11295a18f5594d070ac0009d7fae9be47179a7493b50da4947b6ec793e0bf55abb34c0906ad42202800e909f013ca720e3e19bc4040dda2fca52449675a04a60e15e03e0c31e93503598eebd1e248f85f086e29efaaae936ee7d5535b91ff1f5d26ee47745f76a848734b4ba78805e5268de0927e1532a73003fb1ecd05de60adaa24c0836d896dd4b433838702033047a1e9918072b0a2b7061a6992d0dd78f8cf6702680a52c2869a843e11443bf8a0607f2b258e23a71732649cba036b5fc343a0664233090568d0ac911b8c89f231c2a9e5fa049045ec912ddf801040234e2c62200e3473ce03504d9983a9358348a371a0b18dd90be63c40a953afa0776618a37a72bf08251658f853d649904c11a7af1df6598174fbe8a232c5cdc424ca9c2e72c3081ca1dae28d8d395ecc10308da055e8a50110463223aee1dec4451e4c4c9c3f5a0f19814167440188e28cc69b01d07bc627c42fcacdbe230b8a7cbed201386c74cb8a679cc00d5d5c08b3c4ba2a47f022e0949adaa54b581e9b28406374c56a8e86dd624c1a22f441cc05a1c370dd832407d50df17476e5d21c543dd6e011964697a29d459e29c601794b63908e50c48d40ee54502e7c776a88d4b26df1065c01cc3f9f2029c430305,0x46444b8397d4edb00004397505502a86e69eec3f3307159093d152c4ce7f0b4285e67ed6e2b18732e67920400000001a43517000009812e9022c50904225bc873028f75199cb421280702ccb4788101b2ad0e802ab1642daa34d587500013b3919715e09923283a7c5443e33aa01dc4549ac1c7be6b771d78cb72aa66c52498a1c549be166318c01e802c1076a38a]
def rank12 : Array Nat := #[0x8a006108ac012160001061230580901060040000d050008000241004520082062a0a280105c10b040641590638300040a0b04a9006004308a501244808808040872094a7d56340241660810410130010602173808070141b3c2008c02000020885ea205818067083040038689b888012a00132009804025230000c08a80002804029c040011420405a02100000025232d4080408d80104050028400001a4880e10c08009200982402cac4a0aa1202a5000c4142214080108003800a840c8841410a402214a0420810c6104003894650080200148090284548900420c100000e100d15041c5245284a0111219000884008641045024c002e1812228128d2000e00002483301412610204005280191902801020402000100c10000600082008040349006900980b220c0b0142484010022c46450add00208502101360e2a0004950aa006440051190502010200224cf0400030040880500561300522c20069808868820906580c001000a8b801e0025808b4062400044b090e0500100005404000408a808010442910441200000861080201004440001808004010c014008022211120800001f51000824412144d08041c0040092a0280422a801409122806401a000902a3049205310a810000184000230022484210204440088091c08200042218110987408201101006414486201e82880e0080140398001140385d48e00000211201102002041040e8045804002c44490114214440412401510688280002a204004c086a016ba101b0746060400804a30184020a0295002306c8818a09904f0c7407280c36004232007000013902200d040210482e9007000841c080200204e10440001410600060048c28636c20604101004010a000d0b600102c1184a449800054048322400000200052005c0042008a2080124208940900082540621ab315604228008e012a0100801002a9081008100200000001807482a0c918830502000220051020370208260062781301002100000948040018120022a15082a1800890005130464000c804d020850b04cf116880810048a200490032200014140248a08041091604402810100080102014410c00000743601882c10410a000280048010aa8205260410500947c084a12408040031601686020ac10286023406c85cc03bc25024c051204c0121b0880340120e23080040808384000081446049020411800c01c30030081221004025000600060e8904210402030000818208a4a2088090b11c00f04000984c24513a10c0a10e0202402813040b8024d3014020400aa05708a0315621323c238031610a012b4c00002a8001210248b0a828c80268008040ac00cac8300839300e4805021240404040840808030000600412ea244030a842001c0a180c100050b2224004824004888400501003508004040281ca410,0x9204041000c009418010020858d11168b1801040000ea80028020084201032802428004c502d8480a200300081211081396c0040574d048088511381881002b20002204412482895300000008810c84a02000008c124000580600629a02c03b204204cc100888818004110001301460005220024812841128810928918413f0c2004180029005227a0080c0ac1800200838c844008c200018800b080001610a6e01064a020a009c0309480004a622c1085000810e24101045080300480c74822230521f40810acb0120808498840004026480506010008100501c002080804002a0250084302682d5ac026008480821224b1641c208000c800288c2400020032949249a20220c00010210061140018484840202710648a614001807080484000609000088150458124842110340501821c21300832804023114003a1849601004948100214022ae0811eba010010d8036004a0000a2c92417000024010022381810463008503100004200425200068414802808b44428110040061a0542840062280200602441042045104b080d83a000484089b1508182416c00220c4804849710aa12441aa610c81e809804808800060e08891ca8082ee20143b90000892026110260081a0211509a308205501865340490085352806101000400024039203221828200440d0c000204010228080c000402209432c4a00200c0138802210220802061001094230039410880202040009c21c1040054410012040901500271101800280002a81420542]
def pivot12 : Array Nat := #[0xb13b0fb09b00af6af1aebae7adfad6ad0acaabfab5aaeaa6aa0a99a91a8ea87a81a7ca72a6aa62a5ca57a50a4aa43a39a2fa2aa20a18a11a0aa07a009f79ef9e69df9d89d09cb9c29b99b09a699f99999498f98a98597e97196b96195995494e94593d93893392c92391b91490f90a9018f98f18ea8e38d88d28cd8c18ba8b18aa8a289e89688d88a88587d87487086686085a85384a84383983082a81f8148098037fd7f37e87e07d87d17c67bf7b47ab7a77a279979478e78978577b77576e76976375a75574f74874373d73573072872171871170b7087026fe6f76ef6e66dc6d66cc6c66bd6b96ac6a069869368967f67767466865e65764d64763f63a63562e62962361c61560d60a6015fb5f55e95e05d95d45ce5c65bf5b85b25a85a359b59458f58757c57357056855f55754f54854153b53352f52b52952551c51450b5064f94f24e84e04d84d04cd4c34bf4b74ae4a749e49849048848047647346f46946245e45845445144b44644243a43242942341c41540d4063fd3f93f33ed3e83e13dc3d23cd3c63bc3b63af3a439f39939538c38637e37736f36936435734d34834033932f32331831030a3032fd2f22ed2e92e32de2d62cb2c72c12b82ae2a92a329f29929428c28627a27126926625f25c25a24e24624223a23322b22722221b21320d2071ff1f21ea1e51de1d91d21cb1c71c21be1b41ad1a91a119918f18818117a17116615815014714113913312f12812211b1151101081030fe0f60ed0e60dc0d20cb0c50ba0b60aa09f09408c08507f07506d06705e05304c04804303f03402e02501e01801300c009000]
def rot12 : Array Nat := #[0x715465737636a1631666a37316571b62b979b94bb68159674b3673516a4b498b79b59972b79177491155a239565466917568749821999a1b75917193996b9726774995b9719b7779977a78ab8757877bbb94b7999ba44b8739b269545342949715217192792a47999315a9b77797767568b2992b74b4317323658783279959597195717424369b4884a694184b39a36964672281515847699729897b48777b97a2815961773797386b76946256933395747779711b664a576182179313b19766798997386799543227b366129a743987986bb91786a7b385974468baa389175a5b7738759764488993795b276543885267562a91941957497996a919479675b497456449966447971a677716186946b94675bb197977a187b741578173117b788b7556b7817277576757b717955798166977939739425311677598637777549317a547696b316599a3679472354929737119a73a6a1999699b39965b87937279b3279916387665719b647213318b4464387b691441b7a2132b5994176bb7991673779b67794947891b744137993543b1977164157279466b7b7177279799712149459969b994b3825756447b9373943b4975a7291a567712a4b7979966b46313672195347899947679b53a9795997477917917455959b95797843869976721946979b11119b97388267661679767871795217579646177972294619b1791594b44226714a917666a695b1b4976924699529777a9294779691694b97924761b99954992775226b16156718247b931897137221117776874ab19342866974167b2a147297877756b969944395116177979786791934467718979463144399289774b277318996b79597a19b176997b8b7a8978199749117b3676b97a17717a7b7579468172547a6b699217757267196b6471661665959b986167b8a9687751373a698171954373b3899a69b77b216939995742365919617a77175919217159699562558771714b1782897714419727684b549a7179779b9b23b96a3777957a5974b917b1974966b7659693787a671775a1748564441453b867991821297a76499b961719b93b168922b6aa62792b83a9745a9761321a5b219b371b46574699774b918678791969b696919b96b419497975771b8745477145316177599537963794798937bb9496577699718b46615a496bb8954657633917a95742b779769511749476a1a7b94b599644449479b311187964279b867b87679566789971375469149bb499719297658163946919b1a73997199155497917291379986165b69966675b9662979466b949b73987499925637677a9831149993159a6b73972779499b9473777b21997969847262a9177757b91749a6b4218788b295959b979a6b749646674717b761ba27578482191147483586b6413b99a359996918b978611114b59,0x2849862495734993497297251679b1966429a7177b7371955b797589157a167b917677465359179167ab26b69584457641b7997752996327a31788495998964955727779889b416a7a9576a56b6a7499362793b1b2219b455483897176292716671a784a61649b7b3b794a471a582327737356847977337b174963ba971743494772577a356476665367594b664b29b946b753b3392932379a993ba99179776b93b2877478176698368453aa7976597596717677644915a4951a189744858765595973b67b6b2b9b765863956897b83944617b69b92b996697b965397666937b67b513697926269b1785917366493677777a169727946775b9b8569a1736b198896969978b4981617591773959ab6879519775b13b3419447921674b976931a935998175753699a812352165977145616b97694448176ab7655954b75912649a9646915984219599166b49172679953947657b2857747964283796b387776919a15891347b18844428791593795177495777235689b77119787668926718958519137141613317599999177]
def key12 (h : Nat) : Option (Nat × Nat) :=
  let row := (h/3163 + shift12 (h % 3163)) % 12637
  let v := field iv12 (row*15) 15
  if v >>> 14 != h/39970831 % 2 then none else
    let p := row % 32
    let f := field rank12 (row/32*32) 32
    let r := if f.testBit p then field rot12 (4*(field pivot12 (row/32*12) 12 + pc32 (f &&& ((1 <<< p)-1)))) 4 else 0
    some (v &&& 16383,r)
def shift13Data : Array Nat := #[0x300080209d24cab80417810c93801000f057080921605c01836000150049430581ec0703700a1785a0b506c605b558911c002f08be0fa6b017a2b0d03301608f10e5e8bc0122290a0150aa2f209a6f9320007f4068cc57285c0780103a00865a2106a2880000409c810262d722000c4301c0020540000d0a236c018aa000044208031e40007c90a27c010058430084271098a0a4534008000681140340500e62c01811946798059a43780001082b1821548700d57e0051983a020f6122bd04dcfec2e0120180043d80103801c0280206c0001fc6f0fc1400207900003d140130840202e24a1e41fc2407d032008020000ac00c1a09c09a0083c0220001e43904b0820b41f15e00e02b1381800801e5102f8364183739b09c0740002f0640440402d2dc0e0000081120040011609c061d180300002c0180d0101245288803200015000007350030240003180e00404e074320c70420540026f1660b4262c90240480cb121ba0305898c0500003d0620020531280c17a0882f80008c06c2004e00008c3f0a50360100481d01c54059005004006d905f0000042480003a090008080040044f8030000080b03411c0c8254bb08e000073520141641300485c0480682604605068800000362a0821b4a03410801000024000450006f050800000030190105660093d0080fe064148000000000f80003c000030000032f40381305c0b00280f0120009780b06e00801002b7a0000080300e14c0c80c044010108001360140061e1380040b8000121e403021184000948370880a4750020de18c02000]
def shift13 (i : Nat) := field shift13Data (11*i) 11
def iv13 : Array Nat := #[0x332c523a88f3e394690aa0a81b9c8a4051d1ac4a5144835345b5149136da6f8fe0a407dcbe1624d6a0d4cc0272de1478abaa99c6901bf221c99d378ba7cc717f0f541faa84eec3c401c1a343959baf91046e4c1329b05824cf93e401325cc240e89f598008f9224429e44bd0f2c5d829a041bf0c03b003c0c7be54378343cf958209ca7a5d39c50fcb182b9848f6227359038852b5d1af48315d4472db0f7a57a3048948182e92d32a16e36f1131bea619609071b3b089280313c092f25204aae2ac9c4e0daa912e4195410bd39eb00c0a6541068a1e4b435a207883cbb94a088ab499ea6e423a5e4f10893d386f2f623c3cac32c9f3ac3394114c24b0bef3fa0ca08cc2f4d25109ff520121a7ba669eebdf8c89f10b1511bd1c451ac85d2052bfa99350b938a0d3798d4e107718cd3b116ca08b7464451aae38289b1fb9650eda8348e84dac5964c03951c5fcfa9d73b489c08644e174afa13528a846d3690397da00b610cfbf0c6daaa355d42a5b1e51c50934c324548520f08ea3710b1e927813e0771b11178e28a1242808ccf1853adc882b5bb1a582fb8f8c008bb97c85c03aac3265333d2229b82d47c11e2b90c3ba346b51ebda927c0dc70c77ace4bc2ba30a9214629be0c94524f6aee4f2a3843f942bc1c12a70b249f453925443114045602c4d1b1a12585925315fc4d94d476b3c45f831048d05264a539a5a3e1e2421bd236ec749b251a954127ca35022a3bc3ae3905ae53e9cfca23c601614ba84b47334486b3be40c3f59c908124d9419a7c090b826dcc426ba3d8bf1f726aafc25e209cd70b688a2c6a2705409d4f720807e8e9197285a2bc6cc53c402a015bb0f2af37d3b21bd8dfa9838696eb139f04191cc3fdc2c1ca4ef090208a5ec2a8aed29a773cc0bc334a0d31492f85ea5d1b7040ce90e3a05430136812b85b7a93bbecc6acd11123dc92bd30926336b8a148d0b0cd51180a2c14c03914033f10b91f8849cce0ea31f4cbbbf1be4924600dc22e9e1a0c86c33d3d02022d81921941533321694b70584e089aa18239aab290caec9b0f0c9c22c516b4dcbe04a0008419e6a2a3b7aa1c67b2b2ec2ed96da2409106a996827019a8da8cb09ca9c65a878252e69238afc32c4c354139aa29bdb1bb7639512fa7c0c12811d69b03259e820b4959343211b2c75895219c449fd3a28fd2730efcb596a26789682d456876d0346f4bf4071061b6a4eb3ac6d3b89fe0c4424ba094ca44804a0f50d1800c216b8d8890418973987b271cb312d0ab2db2ed28037c260919c491994a0ce40811f94f540aeb9de99139a525806b73afdd0cc84b94909b663a5132850047be7866b9b19626b4e4c2502ad3c3c3a3c20b5322b642006bc259bb2728550a5316ad9a8912a94540619c15c8b58d223f4dd2c82430d752c13f52fb52384426844b479e0,0x992e4861a397531532c4414bb90f99287dab886cb7cd322da52113abdfc9412cb0b53d0be493260111501c49bde9bdc3e4a4068a0809930651584c33e268cf096024cc680ebbf48b4bcb38d94bccd9e899fad5aefb8ca5118c8d6b46bd75270fa00036c44b241479be240e91e25a90d81588b03f9c95354431f638f91503d1f02741ad0cc9d4bb345ca26803b4c17118d91a98f23d2b8b8b4aaa96854cd30a883e3b9a4f301af815d24e1821da000067457b0610281cc97d19809ca2072c981a49d59d030492e2b5b673f08368f1817b5bbdd055098beecc62eead22cb0d9ab331c8791cfc96167a6aa7a533884461a3a36486d5134e8190c139763feba6c0248d51c1001a61720a980bccd5183e226c20638089e111a6c8f4a6f0751448e747131434536a989933a204330730264d9ad427d3a889487f0a3341c9d23ebc64d820113720635847fad548a1a4aa7c1dbde1c84ecce5199338a2120e0001abb87c3abfc00545e1cdbed8e141cbc9d2d3723204908fba9c00f06121787b2c734ba04c0fb884db83fbbcc99c58cfeb90b42cf8b839313f48bd01eb97d198dd40b3e68d14ada5f1c125fa4c49e0570d080e43b2479d297eb4e000b5e4ed1ef9fa3f32332b7924060013000802016c6937f2835439602094abae5018268beaab1010a564221b4b491d85128a78542c2a408aa2c0000cff0299dd0cb0ffbe018abae8c500048c1b240542d23b82282f4af95aa04147869b23924478cfdba94b994687bb10aa49dd11cb35cd4aa3b40a2f21f2be2039dc43d865231459a7596f2159c2ae8c16cdf5174281f39ad0af84bbcd2e1842a6ed0e10c9791ae42eb8147ab00851839a5ccd504790e1b5a35ce64f5c622ddbce3a099a1d18e051b369cfb887815248a4a3ba1151eab0e53453aae0ca6bfba633300781b1001a9a95ca599e99864dc19b8f94eb53f0801193aa480b6031e26d07c09e14984a53e12943532fc043223b607a2a9988508ab2b9f2dfca2a88a064369b8af383b399d07463311828c40a0719393d841d0021db9241b203a7f2a61d98b208c415ccea1686324938fd241ce0322ca46147dc4a1f1c3985a44341749a966a4239e8e4c7748f3890eca82056157b962d19fcd049d04e2155a631bf14e9b9ac020c3f72bcb5626f15225022da4605f9819d30450db365a904b62b0bbbd26b4f8ee1630ab97ba07ce7843c55a8e0301938d4c1d4b34dabfc80da9e9ae9a10b084f91b143229830af01ed2f242b8b38f32f51a89832eb86a1fd326aacbab81a3791c1a9fa9588d2c42714acb189d927ebf8427bd6820210c723e147b1e78829e738b4c99a71a2012c0aacf2e19e3c26a80d14cf3d2e0621148e6041270aa5bffc8b2d1b7109f1201f92761a8b4a20c853b6b1bc1082ccb031ff8078c60acce3bd8cd01bfb3136807c15e1feaff8,0x353033a8b37e3d93ebcd4c7045088b92683207891fcde3a4328b629c7282a01d060ba9c3b98235a34ad601d2d01df069337bca509a14c7e4481183e00d530792a28f434211b0294921a1a993c24b29ba84a722f03631f2b0f15053898ecb2c1613d17840b37581fb1aa22ccca624ea3b3b17011a0a41e861abd97aa9d33b4e2c1451fcf452b8214e221b0d3855429a69976b749c1074c668fc225af90288dec46823ba10ad3f91a91912d397737b89731d860a61bc72d744f3c5297ac29434a1a032beb3f159b5c327ccfd23a6caad1c02120e52e316c2cdbc2bfe281a36a00b8e000279aea20086eafe138c8792d000085ce33a80009ecc651dbb5f3f6998871ae73db03f4549aaa55adcd2aa6dbc82bbbd591da02a3290445ac36af130c23b02abd4ca89c5a921ecb481a09ccb998ae4b80701cd482b5718b9914c889229330d1683774b33b546184dbc486405b4d22f40a2531286af79703e81c09bab9d228cc52e9000a9445b2759c084e1954ca438956814130c0f3bda1337031]
def rank13 : Array Nat := #[0x218a0420a000250080828410500040004302040102000044026020188080280000444004c04034400838148072020412a0100040020019a980100206002400132008a340001c06a003488240011110200220000400880a00005c00000158480849122204040000a190848160000010a5008008110430200008a0000801880c0140800026029040081000040002010001000004c10898020005000208002c031402004100202048090000080010004108420c200202400b003089008400011208800180000216e02110008]
def pivot13 : Array Nat := #[0x3fdf4f477badd0e26eb65a6cc62afd78b457aa1449949a411a87411e8ee6f35998be5c2c14c984a239187c3b1b0c058291307c38140802c0800]
def rot13 : Array Nat := #[0x96896b47878336b936112b86745b7ab98bb767211512436672717471989b6392828193a391a37365b51399bb7b317263971b37a63718a9666673b9b4794177b1b715862a6917a49998975797444723bb39547b954729321771261936677279b118b77112779565b9639b9319b149ba2564a9993418796b8a6b3b64941732759b3996]
def key13 (h : Nat) : Option (Nat × Nat) :=
  let row := (h/419 + shift13 (h % 419)) % 1619
  let v := field iv13 (row*12) 12
  if v >>> 11 != h/678361 % 2 then none else
    let p := row % 32
    let f := field rank13 (row/32*32) 32
    let r := if f.testBit p then field rot13 (4*(field pivot13 (row/32*9) 9 + pc32 (f &&& ((1 <<< p)-1)))) 4 else 0
    some (v &&& 2047,r)
def shift14Data : Array Nat := #[0x472a40009001624060030c000c0b18ae000000a05931e04027000054a0000001]
def shift14 (i : Nat) := field shift14Data (7*i) 7
def iv14 : Array Nat := #[0x6d1004c36880e594033000007301bfd1249f0e402a02e8000000160167c4e002000054023cf83dc335d3b9043f3a4b89587ad63dbed4675715f5fe94fe98c3405caa8118427ec6636]
def rank14 : Array Nat := #[0x1000000000800000000]
def pivot14 : Array Nat := #[0x10]
def rot14 : Array Nat := #[0x3b]
def key14 (h : Nat) : Option (Nat × Nat) :=
  let row := (h/37 + shift14 (h % 37)) % 83
  let v := field iv14 (row*7) 7
  if v >>> 6 != h/3071 % 2 then none else
    let p := row % 32
    let f := field rank14 (row/32*32) 32
    let r := if f.testBit p then field rot14 (4*(field pivot14 (row/32*2) 2 + pc32 (f &&& ((1 <<< p)-1)))) 4 else 0
    some (v &&& 63,r)
def hint8_8 : Nat := 0xfcd801
def hint8_9 : Nat := 0x337c03d540a9dffcd88771cdd477cf7f80ed8dae361267798d501ec5a1dc11
def hints8 (n : Nat) : Nat := if n < 3 then hint8_8 else hint8_9
def hint9_9 : Nat := 0x2b240090218dd13a44d950201dd42356187df6b200461e3823900b48d963542136dd03196c69b98041d48201d50777f1503974680130044fc541d444108e86756cd8786410442300106773cd99865ce1ca07238d3864e057748f1aa015d423c2f7c02c7c08ba02e3824166a483976600675aa407d6a18a3c3a80c026f1447701b48773aa422a69018236a6027749dc00d00b9dc5361803d45dcac825dc17768e17c551dc07a45d55385a8168e3a38ba974d9b381ea57366a3987578d98777b15d387cd870
def hint9_10 : Nat := 0x2400bc8337d7c554010672c00aa92e19832674cd366c0050210dc2a9277d68e27151c540c5509088d8411c39540007590e6b212c86314ddf02287c510640456860700208c023041c4116a187370384475537cc7751dd8a94f7de00280188e1c0800500e8d86036430e443808e14382c530d933648e9a8204dce36666079811dcbc550e8f0e1285d290825d0024d897514a517541d422a03a83df10e05006461d403c01ec57238f361cd9a0077157181808c0201dd7027a6180e10f9b0e6408e981e3833776619a92cd81df4ea40e8657c06d577daa07314ea9084570072a5c0e608c036743998e177c336003406c21d4299677d5360b7d9c56809e0231d5bc506a40df30dc06f237dcdf01e9ac55cd9d1864d80ee5e6007d00b827761dcdc505d40676c09d363b1487700b05366c616367409a3600f46376cd9e3661d5b987cd8b7
def hints9 (n : Nat) : Nat := if n < 198 then hint9_9 else hint9_10
def hint10_9 : Nat := 0x2a01868268190069821a0a40010081a2a6063808e0a3800e007c01d407301bced530e0ea900a00232280d983a80e8e112cec818640151024e8631d01d511dcbc5110406d1f5402e04a87a936082410d00bdf0108c0221049402100168150014016601390484398068051a09d487521d0d1a25d0b740cdcf1a1008d3809002232108804208c23704dc338386803d3c00067090820400b412314e01380504b3838d8f9808e473620e4fc500e803934d807720e08771f140412cd8277371417705d4ec53cd870
def hint10_10 : Nat := 0xa1821a8874146805b3b4c23220c8072094024e2140076188c48608c40b529d0918007462905382481d14831011821508a420620680d00848812374c84231081c8052014611784d9257cad310c8025251481102384122468adf190444b0e08c5f217cba02f2065f35744a010384a91d74155192021c1f4c404015c41c250001c078893702243550ce013828180ea21a064001544c90b248370e606820338162243805c024804c009cdd51f5401f3260449106460e00580650384a5f2914a3718e88d904a867405a82590128a3a002000c00e00cc21041402660bd502080563680070350018201e0b3708042c8288c14b237c44003b807c04c88d5188424922800282838606012c67501382c5071461a1e801a118e498605a0377150837410dc28e09002981a6006110a4349014c05227201072808519092c48e20248380f20677372040910f0ec836082d538a49c52e0898232a406e10187740a647001ce03d5057c83c0228a402a6006a390005a0c64e0e02846df00c4d453418c3636a47c8100498e1660499082408310d80a91e080e82164d00300804f086424101984750524063026403e38182003a08802002c6382680540048c58200281740ce4375277c28601a0a820048c291ca40693c00a751164f2912082383b5420e04a4f380438282172075f0e80b5f3c18c3a201042304849d53018d37038892908a893a3a80d180174b1a0e38d0e1000011012010008f0118308c43a2e38ba905640321b541410754b000ce8f7433540152e18f0e3b7c9a901882a901d4c7531d0cdf2c382182d1470e39d0cc5286843834a497524e45741ea4402006c0590b7c938015030e11041423d7c19936180143d143450464e8628001a91714c0e14e435f0034e0030e4d8e077c06b0c00c37008006d1754d5f0f7c04100d027515dc977037cb1800cc3863000c1a3468b7401bc90218dc14528e450e0108974019000938080c91808013208caa92400bdf377c02d008cc382208a772b54e8e2b14786019c00308d8a362ca403920e82370f147df24d85df2ce0fc53320c8e00f05751b147181e6078e1aa4c8616803292e6058e3aa487501d0439088cf1804086c828e031814e05a918d8f023280f981618b0200dc7020ea433720e40d91a80c77000407d1800136080823901dc23a14e8d98340852914dc1371a38e1a01b068600143021cd847709dc336157c03d04e802b00b85002cd854500b053621dcd363a6051800e8d3804e400701e8ac81408d7405dc00f38d817538e0a8e2a18aa0006402a0000bc5012405f00a40021f1401800d8045001800e3714ec53cda1e
def hint10_11 : Nat := 0x3a00341108c3825540d53a188ea044878630608e2218824121d00c810b0dd31100462274cdc8272004b1c1850920c4e2021e065f13205411500ac818a48d91178069088064920480031ea401b226021205044590d24bc808b440e2f54a3820184060c6482108844091054c09017885f00cce5f3154c4529146453914d4821400ce012804436180cb05000b5020c20120101e218e851a25884a115a853908a833820e0e8e01c024238a4e4005202a120c807305645d50554861097c6c81680120350001d268022910a4a2915880711a80018188c4a00130c121e3816201f0c8205240540924c210148016186021c20f0c4139d080e301824b2218606363823228e841c10c800a098820619005c80424aa03a802c803840780078506308ca182000119112c382018c8d535141612d14092114005d2a60a5d05749860dd40041a0808204e093915d060e0a809820194027275421509d023c00c0072317c4411b7c729357ce0610f083a101074518e4677126433a022416a25a8977250454500801320d14058204480911d41420538a74068443a00e409800d41230a640e228dca0e231421821047380c6005a10e00530d7c974046001f021805028e4498066070e2a0817424007742a3806800b40281a38066082475f380088e146030001b806b34005820dd006d00081861e6071800c863801d4015037cc98084404f032403e08e8c000e1859830e80a130dc53825d40ea017009901ec6750c18945010814528181060f7c1992ca48a9088c13901bcd38157c5753860ec51438c3629dc3a9080000d0190074000039820e44020e3800b057cd7404a4b38246004e01545862a18aa91638040040820e2d7c05f1a6043624e0177005010029d404530380ee1c084820a0803c2dd00311f14adf3838011036410e14a40a91a18298108c400366013a30080130120998263843724e853a1b142862438e3806380770314b0e18003292c0008e30e430e24089a90a38a00180806a01b0c8613143c500186a90024038018404110e41c506a4b9834a4502257c6370064059137c2df31dc9c52f145a932a4ac524dc0673a6000500a402e123800e24a47000c089df17145df11dc239008ccc5208c500337ca020cdc062323820209d42a92c082c508d807d077c00100b0b183714877121823724d800721d44a931d401218d800f09dc3363438e0214dc17500ac03614d8a3604d802a00f4d181cd8137012407a3408b3634d8e3600e8f3600de01
def hints10 (n : Nat) : Nat := if n < 42 then hint10_9 else if n < 3522 then hint10_10 else hint10_11
def hint11_9 : Nat := 0x177028021a16385c8161806809006380a8029900843981a386c804e068600e047414e0582010800405001a006640370a60738006471a08e063718d8374010003a0cdc3360660041008c7741c000751cd879800e40771f1432
def hint11_10 : Nat := 0x54006b04f0052116406101741091974268010005603b80e80a640c801c80460098016009c4d9106004c00280030a0802110f040911a84680870482033008a020c01c1004539098814e052007000fc05a032406401702500848475013400d0354586085405e00204400dd41a11070199092004800140660d7425d01d012000c40120a60629004c05012600a01178014137c45f01284420e8022001b037701b400c008011a00d400f0078051057455d00940730238142101005b00cc01110a40ea03646180ea4637001c04b0608402007c42316800a902644060388132058864001a024b09000570e3863a18e40a100b020900e007d01883d51720675197c1981068089103800115d423c183806501ec07c0e1808200f823201a806f141816a015006911d021a1104028001006e09083400f2058e00d02590b7c577048c6a91b546c8019c20405a06061a8014014e80091a382741b7c02a0108059160868610e80df088c03216a403c00b843600b400008842a9150068212a45d50054477000823719d0439143812100dc4000b5454500ac33712180180864275097c300006424504e048e1354518017c70600d807a157c22901d431a0924238072003d05644c81c6870e14dc03910e052906183980ce002305d018e08605021ca41a9011473808002c507144a0131424114001000a3820e1d7c1a007547451c6063601dc029077c23a1dd01491a602060124286146860200e82360a8004108e43df09dc2c8001814108083060dd0700003859805dc11914e05df1e6030e1c0813a14d83290c603450cd830204186381f1435f04e460015d01370438136186815f0460145040812905d43c517146c51cd961
def hint11_11 : Nat := 0x32001c024e09a844e1524231118410f0960455136434112644201140027124824a08b4419032c41108441070c644a10a8443c081c46a11a0462191420107a81e2033022a00980e100742d3083c21501784150d241d30228255094c620150403f039404c04a801a087044b110841c0ce455305602680170519090834004705551520058036045f0f4c13c15dc35314801501b4c4d3011425e0140432068411a0ce82620138250007025d092020405743550d20035014c2990224068014404f01c8055014808300a00a00424418052c6390028240009467510480d501c4618006005d174c04b00080ce000c440092c07b0120409048002003406400078021157435d18e8168007c13205383a0066407314e4375054c0540848142003065f00203d5032004d005805b088005a01d027408c82450128056050023c017c07815d406204483c800240e205201550198421058853a1680209101006a018c04608640400190637086003c097c069018406502480e8096462901f042903a80a1088444905a843604845c8004412301ac474116400b015c03401b800d00cc03201f4015006c06c0868540006406d0108382100803e01d4441004860e004c49800e45d500c431a01bc3371b5403810186c800104d5090440e00a424900501821c182290264437132053704e01c800b46741a801190038729056447508e006708386061c3850605d0582000030600181411a08041052470012804df0ce01a00ea40590818049041843810682020e38486031403616182d509d4098032458e100075f0e180771468774108c4a904602c8157c1001b7c02a001c43a15143000c3848e1d14086075415f00b01980ca400f0a8050e088c73802084c5040818614a468e14606860dd010e0f7c0d916a435f00b86a902a418e023860205144390a0871800140df0d145381800702120827708e450005dc129080050206a439800f47c511dc28e07141df0c0823a04e40231e605740a182a90b7c3180a6061a04e8698177c02b08dc23618e059804d82c5000403701e863605d403a14d83360f1413717146c51cd9b6
def hint11_12 : Nat := 0x51011003f018c0ee10a454101ac4530130045115416108104401b5404f01c40e508b42151868474002c53a1b4c02601c8058096011c11a00520844415197444e0ea404e16185c801c003315dc262195406d015c418008421c05745d5016c52005a00540d4c245015812114dc65319206c80170420009c35519d044508c805e0d20150141814b09a05d308f044b117c1581aa401904240d8010c38e163838600d425010704190190450007c6a000702d3095402901181d30198248088445e048004b032c55d10d81a000d000d094c2a00094438197c07c18a407316a40d019141230964640013405a00584620d74240086055504c806801a430600f055f007805010180081a3807d00a01d50d14620154c0d304601740b5406f1a1824102804590720112050014e151406c100815301ec04a0260013112443c03542c800e410608640141024249152000c019c0e81818145046406e110400e092c412033810205540060520404088c03e05a80c8028418208804d308a461810c804900244210208141057c0040d7c4a00564282022423801840c505881980044212135440e00b406a00a86c5005407814e002c082460e0a601000ce01771260031132030e016420001880df0ca4138038804112080ea019452901dc43700c807500b8149143857414004df043818604e42020dd00861800005001c0920c002c516600000e603180c084c514606380838037063820610000120aa40d902a41a90a1828e11dc2390238129008c5020714698003c03d108c60209dc2df00ac0990f145c5077c27510e80c904d84a910e448611d448e04e823608e817501e800118d853600e833608dc73604dd5e
def hints11 (n : Nat) : Nat := if n < 9 then hint11_9 else if n < 964 then hint11_10 else if n < 6467 then hint11_11 else hint11_12
def hint12_10 : Nat := 0x20824504e415d017404e004804b09d425f0070062012000908a425d09dc0650140099005406a008006e0068098001003200f015901a00420100206086020e05000740904237090002303540a908e418604e80c505040c804000590468021037c08e021818205d4038063823a0aa42c806a41980c182d50b7c1c8006430e080828609d01a0000028e075432902802360d7c3450c602000a60177012413804182a0017c3020460045051403601dc0290060136040803a00dc10e086804100181290038002057c1df08e028205d0075071403904dc2c50c683380dd03980c003360f1481
def hint12_11 : Nat := 0x1a0132048006401c425501f406d016802001e024809640d801540480864053005805c014004c012c01c08f025d048c05d03a004e0880018015000d0094026017c0c9010c00800500e200d407201ec02a00b0051014820900d815d004c168046414e0848028013406a012806f00f0155058814801b8061019401f00f8009005400503a8033024816a044806200780020978067034001905002770900074097c02908c800c01f001101cc0690b4c1490914218016c042074c0380178275006809800c400600b4032004800e0364159001002100d02230004118000022900ac02e0124241015820e028027408e414503200390818057020814100f413908dc0d5037c11a04e00590238202031407508e81060c0020006801c801e82df0a0810202a4175043808605dc13a0a6023601dc04108e01d50b54100057c2a004a4182008c3450d7c30600dc3290c382c80c6821a0c603380a381740a181360e602a906181980dd01370f1403a0c082c506381a9077c1c50cd8d5
def hint12_12 : Nat := 0x132092414b04080d8017001c057400801b007101f403501c805400a0011048c000013815f00cc06408d82180168068014401f0094026022425f097406901cc259086405009040340058209046006701340c5041800c015805b01f006601ec031053810e018416804a401e03401d3037c2290188149056406a05881190b4c21200b4200012801308080120050037005416a03880ce081806501b823903a00ea00f006f01e030000f80a008380490178275024823705dc0570014274001c0c900b800f0a0803202380d9040008602a41a003200d501dc1c80dd014104e0059060813608e0338046804107542d5000402b00e42c80d1430608e830e0a603180a8007504e41370b7c329066028e0e601740b1417504e803d0aa435f0f14286077c21a061818e06a43360714302008c07a00e8ae
def hints12 (n : Nat) : Nat := if n < 211 then hint12_10 else if n < 870 then hint12_11 else hint12_12
def hint13_10 : Nat := 0x59010008602a409802380c801d4039035401a00d80820280000010403a057c14504a4118043810601d00df00e0045001810201dc029006000e017c0c5000803704e01740468136040019807142c
def hint13_11 : Nat := 0x1a8068034c0620138049017803200000590048029057c145046000e001802301dc07400e008200d80390104075006819804080df0280098041810e032012904000d503141c5021803a00dc11a04e00a9023813605d031
def hints13 (n : Nat) : Nat := if n < 22 then hint13_10 else hint13_11
def hint14_10 : Nat := 0x74017c0c5011403800d80290068098006000e001800200000e
def hints14 (n : Nat) : Nat := hint14_10
def compactLevels : Nat → Packing
  | 8 => (57,7,7,0,0,0,128,fun i => if i % 2=0 then rec8 (i/2) else hints8 (i/2))
  | 9 => (823,6,7,0,0,0,128,fun i => if i % 2=0 then rec9 (i/2) else hints9 (i/2))
  | 10 => (7173,5,7,0,0,0,128,fun i => if i % 2=0 then rec10 (i/2) else hints10 (i/2))
  | 11 => (9782,4,7,0,0,0,128,fun i => if i % 2=0 then rec11 (i/2) else hints11 (i/2))
  | 12 => (1348,3,7,0,0,0,128,fun i => if i % 2=0 then rec12 (i/2) else hints12 (i/2))
  | 13 => (64,2,7,0,0,0,128,fun i => if i % 2=0 then rec13 (i/2) else hints13 (i/2))
  | 14 => (1,1,7,0,0,0,128,fun i => if i % 2=0 then rec14 (i/2) else hints14 (i/2))
  | _ => emptyPacking
def compactLinks : Nat → Nat → Option (Nat × Nat)
  | 9 => key9
  | 10 => key10
  | 11 => key11
  | 12 => key12
  | 13 => key13
  | 14 => key14
  | _ => fun _ => none
def boosted : Forest := { dead with levels := compactLevels, index := compactLinks }
open PEqualNP.MetaComplexity
def boostedWire := bin true (inputs.getD 0 zero) (inputs.getD 6 zero)
theorem wtable : ∀ r : Row, bit r boostedWire = (sample r 0 || sample r 6) := by decide +kernel
theorem nonzero : boostedWire ≠ zero := by decide +kernel
def offRow (i : Fin 9) : Row := ![80,1,2,4,1,1,257,4,8] i
def onRow (i : Fin 9) : Row := ![81,3,6,12,17,33,321,132,264] i
theorem orWitness : ∀ i : Fin 9,
    (bit (offRow i) graph != bit (onRow i) graph) &&
    ((inputs++[boostedWire]).all fun w => w == inputs.getD i.val zero ||
      bit (offRow i) w == bit (onRow i) w) = true := by decide +kernel

theorem rootCases {k t S} (h : Live graph k t S) (sub : ∀ v ∈ S, v ∈ inputs++[boostedWire]) :
    S=inputs.toFinset ∨ S=(inputs++[boostedWire]).toFinset := by
  have all (i : Fin 9) : inputs.getD i.val zero ∈ S := by
    have cut := orWitness i
    simp only [Bool.and_eq_true,Bool.not_eq_true',bne_iff_ne,List.all_eq_true,
      Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq] at cut
    apply raw_required h _ _ sub (offRow i) (onRow i) cut.1
    exact fun v hv hne => (cut.2 v hv).resolve_left hne
  have needed : inputs.toFinset ⊆ S := by
    intro v hv
    have hm := List.mem_toFinset.mp hv
    rw [←input_list,List.mem_ofFn] at hm
    obtain ⟨i,rfl⟩ := hm
    exact all i
  by_cases hboostedWire : boostedWire ∈ S
  · right
    ext w
    constructor
    · exact fun hw => List.mem_toFinset.mpr (sub w hw)
    · intro hw
      have hx := List.mem_toFinset.mp hw
      simp only [List.mem_append,List.mem_singleton] at hx
      exact hx.elim (fun h => needed (List.mem_toFinset.mpr h)) (fun e => e ▸ hboostedWire)
  · left
    exact Finset.Subset.antisymm (fun w hw => by
      have hx := sub w hw
      simp only [List.mem_append,List.mem_singleton] at hx
      rcases hx with hin | rfl
      · exact List.mem_toFinset.mpr hin
      · exact False.elim (hboostedWire hw)) needed

theorem orLive (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (first : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 6))
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C = edge) (small : C.size ≤ 15) :
    ∃ k t, k ≤ 14 ∧ (Live graph k t inputs.toFinset ∨ Live graph k t (inputs++[boostedWire]).toFinset) := by
  have headEq : (execute C.gates inputs).getD 9 zero = boostedWire := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal 9 r).trans ((first (sample r)).trans (wtable r).symm)
  have goalEq : (execute C.gates inputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal C.output r).trans ((congrFun computes (sample r)).trans (edge_table r).symm)
  have out := get_rep (execute C.gates inputs) C.output
  rw [goalEq] at out
  have targetIn := out.resolve_right (fun hn => hn graph_proper)
  cases hgs : C.gates with
  | nil =>
    rw [hgs] at headEq
    exact False.elim (nonzero headEq.symm)
  | cons g gs =>
    have eq0 : gv inputs g = boostedWire := by
      rw [hgs] at headEq
      change (execute gs (inputs++[gv inputs g])).getD 9 zero = boostedWire at headEq
      obtain ⟨l,hl⟩ := exec_extends gs (inputs++[gv inputs g])
      rw [hl] at headEq
      exact headEq
    rw [hgs] at targetIn
    change graph ∈ execute gs (inputs++[gv inputs g]) at targetIn
    rw [eq0] at targetIn
    have tailLegal : ∀ gate ∈ gs, gate.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ gate.inputs.length≤2 := by
      intro gate hg
      apply legal
      rw [hgs]
      exact List.mem_cons_of_mem _ hg
    obtain ⟨k,t,S,hk,run,hs⟩ := extract gs _ tailLegal graph_proper targetIn
    have len : gs.length+1 ≤ 15 := by simpa [Circuit.size,hgs] using small
    refine ⟨k,t,by omega,?_⟩
    rcases rootCases run hs with h | h
    · exact Or.inl (h ▸ run)
    · exact Or.inr (h ▸ run)


theorem parentFromChecks (checks : checkedTables boosted 14) :
    ∀ C : Circuit, FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 6)) →
      circuitFun 9 C = edge → 16 ≤ C.size := by
  intro C legal first correct
  by_contra! small
  obtain ⟨k,t,hk,h|h⟩ := orLive C legal first correct (by omega)
  · exact dead_start (before_sound known383 valid383) geomdead tablesdead k t hk h
  · have noRun := root_index (g:=boosted) (before_sound known383 valid383) geomdead checks
        (k:=14) (by decide) (i:=0) (ws:=inputs++[boostedWire]) (by decide +kernel)
    have tgt : targetOf boosted = graph := by decide +kernel
    rw [tgt] at noRun
    exact noRun k t hk h

def baseFun (y : Fin 8 → Bool) :=
  (y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 0 && y 4) ||
  (y 1 && y 5) || (y 2 && y 6) || (y 3 && y 7) || (y 4 && y 6) ||
  (y 5 && y 7) || (y 7 && y 4)
def subInput (s : Bool) (y : Fin 8 → Bool) :=
  [y 1,y 0,y 4,y 7,y 5,y 2,s,y 6,y 3,y 1 || s]
def permute (x : Fin 9 → Bool) : Fin 8 → Bool := ![x 1,x 0,x 5,x 8,x 2,x 4,x 7,x 3]
theorem transform : ∀ x : Fin 9 → Bool, let y := permute x
    (if x 6 then baseFun y || y 0 || y 3 else baseFun y) = edge x := by decide +kernel
theorem feedEq : ∀ x : Fin 9 → Bool, subInput (x 6) (permute x) = (List.ofFn x) ++ [x 0 || x 6] := by
  intro x; rfl

theorem deskFromChecks (checks : checkedTables boosted 14) :
have x1 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) => (if x1.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x1.inputs else x1.inputs).any fun (x2 : ℕ) => Decidable.decide (x2 = (6 : ℕ)); have x2 : Bool → (Fin (8 : ℕ) → Bool) → List Bool := fun (x2 : Bool) (x3 : Fin (8 : ℕ) → Bool) => [x3 (1 : Fin (8 : ℕ)), x3 (0 : Fin (8 : ℕ)), x3 (4 : Fin (8 : ℕ)), x3 (7 : Fin (8 : ℕ)), x3 (5 : Fin (8 : ℕ)), x3 (2 : Fin (8 : ℕ)), x2, x3 (6 : Fin (8 : ℕ)), x3 (3 : Fin (8 : ℕ)), x3 (1 : Fin (8 : ℕ)) || x2]; have x3 : (Fin (8 : ℕ) → Bool) → Bool := fun (x3 : Fin (8 : ℕ) → Bool) => x3 (0 : Fin (8 : ℕ)) && x3 (1 : Fin (8 : ℕ)) || x3 (1 : Fin (8 : ℕ)) && x3 (2 : Fin (8 : ℕ)) || x3 (2 : Fin (8 : ℕ)) && x3 (3 : Fin (8 : ℕ)) || x3 (0 : Fin (8 : ℕ)) && x3 (4 : Fin (8 : ℕ)) || x3 (1 : Fin (8 : ℕ)) && x3 (5 : Fin (8 : ℕ)) || x3 (2 : Fin (8 : ℕ)) && x3 (6 : Fin (8 : ℕ)) || x3 (3 : Fin (8 : ℕ)) && x3 (7 : Fin (8 : ℕ)) || x3 (4 : Fin (8 : ℕ)) && x3 (6 : Fin (8 : ℕ)) || x3 (5 : Fin (8 : ℕ)) && x3 (7 : Fin (8 : ℕ)) || x3 (7 : Fin (8 : ℕ)) && x3 (4 : Fin (8 : ℕ)); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 → x4.size ≤ (14 : ℕ) → List.countP x1 x4.gates ≤ (1 : ℕ) → (∀ (x8 : Fin (8 : ℕ) → Bool), x4.eval (x2 Bool.false x8) = x3 x8) → ∃ (x9 : Fin (8 : ℕ) → Bool), x4.eval (x2 Bool.true x9) ≠ (x3 x9 || x9 (0 : Fin (8 : ℕ)) || x9 (3 : Fin (8 : ℕ))) := by
  intro _ input z C fan budget _ low
  by_contra! high
  let g : Gate := ⟨.or,[0,6]⟩
  let D : Circuit := ⟨g::C.gates,C.output⟩
  have legal : FanInTwo D := by
    intro t mem
    rcases List.mem_cons.mp mem with rfl|m
    · exact ⟨by simp [g],by decide⟩
    · exact fan t m
  let step := fun (w : List Bool) (t : Gate) => w ++ [t.op.eval (t.inputs.map fun i => w.getD i false)]
  have start (x : Fin 9 → Bool) : step (List.ofFn x) g = subInput (x 6) (permute x) := by
    rw [feedEq]; simp [step,g,GateOp.eval]
  have keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons,ih]
      · simp [step,List.getD_eq_getElem?_getD,List.getElem?_append_left hi]
      · simp [step];omega
  have first (x : Fin 9 → Bool) : (D.wires (List.ofFn x)).getD 9 false = (x 0 || x 6) := by
    change (C.gates.foldl step (step (List.ofFn x) g)).getD 9 false = _
    rw [keep _ _ _ (by simp [step]),start,feedEq,List.getD_append_right _ _ _ _ (by simp)]
    simp
  have comp : circuitFun 9 D = edge := by
    funext x
    change (C.gates.foldl step (step (List.ofFn x) g)).getD C.output false = _
    rw [start]
    change C.eval (subInput (x 6) (permute x)) = _
    rw [←transform x]
    cases eq : x 6
    · exact low (permute x)
    · exact high (permute x)
  have lb := parentFromChecks checks D legal first comp
  change 16 ≤ C.gates.length + 1 at lb
  change C.gates.length ≤ 14 at budget
  omega
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v8_0 : block boosted 8 0 3 = true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v8_3 : block boosted 8 3 54 = true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem cap8 : block boosted 8 0 57 = true := (block_merge v8_0 v8_3)
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v9_0 : block boosted 9 0 198 = true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=6)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v9_198 : block boosted 9 198 312 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=6)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v9_510 : block boosted 9 510 313 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=6)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem cap9 : block boosted 9 0 823 = true := (block_merge v9_0 (block_merge v9_198 v9_510))
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v10_0 : block boosted 10 0 42 = true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v10_42 : block boosted 10 42 386 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=7)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v10_428 : block boosted 10 428 387 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=7)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v10_815 : block boosted 10 815 387 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=7)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v10_1202 : block boosted 10 1202 386 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=7)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v10_1588 : block boosted 10 1588 387 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=7)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v10_1975 : block boosted 10 1975 387 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=7)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v10_2362 : block boosted 10 2362 386 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=7)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v10_2748 : block boosted 10 2748 387 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=7)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v10_3135 : block boosted 10 3135 387 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=7)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v10_3522 : block boosted 10 3522 365 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=6)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v10_3887 : block boosted 10 3887 365 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=6)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v10_4252 : block boosted 10 4252 365 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=6)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v10_4617 : block boosted 10 4617 365 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=6)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v10_4982 : block boosted 10 4982 365 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=6)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v10_5347 : block boosted 10 5347 365 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=6)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v10_5712 : block boosted 10 5712 365 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=6)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v10_6077 : block boosted 10 6077 365 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=6)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v10_6442 : block boosted 10 6442 365 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=6)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v10_6807 : block boosted 10 6807 366 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=6)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem cap10 : block boosted 10 0 7173 = true := (block_merge (block_merge (block_merge (block_merge v10_0 v10_42) (block_merge v10_428 (block_merge v10_815 v10_1202))) (block_merge (block_merge v10_1588 v10_1975) (block_merge v10_2362 (block_merge v10_2748 v10_3135)))) (block_merge (block_merge (block_merge v10_3522 v10_3887) (block_merge v10_4252 (block_merge v10_4617 v10_4982))) (block_merge (block_merge v10_5347 v10_5712) (block_merge v10_6077 (block_merge v10_6442 v10_6807)))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v11_0 : block boosted 11 0 9 = true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v11_9 : block boosted 11 9 318 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=6)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v11_327 : block boosted 11 327 318 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=6)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v11_645 : block boosted 11 645 319 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=6)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v11_964 : block boosted 11 964 393 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=7)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v11_1357 : block boosted 11 1357 393 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=7)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v11_1750 : block boosted 11 1750 393 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=7)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v11_2143 : block boosted 11 2143 393 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=7)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v11_2536 : block boosted 11 2536 393 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=7)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v11_2929 : block boosted 11 2929 393 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=7)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v11_3322 : block boosted 11 3322 393 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=7)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v11_3715 : block boosted 11 3715 393 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=7)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v11_4108 : block boosted 11 4108 393 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=7)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v11_4501 : block boosted 11 4501 393 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=7)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v11_4894 : block boosted 11 4894 393 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=7)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v11_5287 : block boosted 11 5287 393 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=7)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v11_5680 : block boosted 11 5680 393 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=7)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v11_6073 : block boosted 11 6073 394 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=7)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v11_6467 : block boosted 11 6467 368 = true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=6)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v11_6835 : block boosted 11 6835 368 = true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=6)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v11_7203 : block boosted 11 7203 369 = true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=6)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v11_7572 : block boosted 11 7572 368 = true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=6)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v11_7940 : block boosted 11 7940 368 = true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=6)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v11_8308 : block boosted 11 8308 369 = true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=6)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v11_8677 : block boosted 11 8677 368 = true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=6)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v11_9045 : block boosted 11 9045 368 = true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=6)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v11_9413 : block boosted 11 9413 369 = true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=6)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem cap11 : block boosted 11 0 9782 = true := (block_merge (block_merge (block_merge (block_merge v11_0 (block_merge v11_9 v11_327)) (block_merge v11_645 (block_merge v11_964 v11_1357))) (block_merge (block_merge v11_1750 (block_merge v11_2143 v11_2536)) (block_merge (block_merge v11_2929 v11_3322) (block_merge v11_3715 v11_4108)))) (block_merge (block_merge (block_merge v11_4501 (block_merge v11_4894 v11_5287)) (block_merge (block_merge v11_5680 v11_6073) (block_merge v11_6467 v11_6835))) (block_merge (block_merge v11_7203 (block_merge v11_7572 v11_7940)) (block_merge (block_merge v11_8308 v11_8677) (block_merge v11_9045 v11_9413)))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v12_0 : block boosted 12 0 211 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=6)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v12_211 : block boosted 12 211 329 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=6)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v12_540 : block boosted 12 540 330 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=6)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v12_870 : block boosted 12 870 239 = true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=6)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v12_1109 : block boosted 12 1109 239 = true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=6)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem cap12 : block boosted 12 0 1348 = true := (block_merge (block_merge v12_0 v12_211) (block_merge v12_540 (block_merge v12_870 v12_1109)))
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v13_0 : block boosted 13 0 22 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v13_22 : block boosted 13 22 42 = true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem cap13 : block boosted 13 0 64 = true := (block_merge v13_0 v13_22)
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem v14_0 : block boosted 14 0 1 = true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem cap14 : block boosted 14 0 1 = true := v14_0
theorem allRows : checkedTables boosted 14 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact cap8
  · exact cap9
  · exact cap10
  · exact cap11
  · exact cap12
  · exact cap13
  · exact cap14
end PEqualNP.Outside.L_meta_2504

theorem PEqualNP.Outside.L_meta_2504 : have x1 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) => (if x1.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x1.inputs else x1.inputs).any fun (x2 : ℕ) => Decidable.decide (x2 = (6 : ℕ)); have x2 : Bool → (Fin (8 : ℕ) → Bool) → List Bool := fun (x2 : Bool) (x3 : Fin (8 : ℕ) → Bool) => [x3 (1 : Fin (8 : ℕ)), x3 (0 : Fin (8 : ℕ)), x3 (4 : Fin (8 : ℕ)), x3 (7 : Fin (8 : ℕ)), x3 (5 : Fin (8 : ℕ)), x3 (2 : Fin (8 : ℕ)), x2, x3 (6 : Fin (8 : ℕ)), x3 (3 : Fin (8 : ℕ)), x3 (1 : Fin (8 : ℕ)) || x2]; have x3 : (Fin (8 : ℕ) → Bool) → Bool := fun (x3 : Fin (8 : ℕ) → Bool) => x3 (0 : Fin (8 : ℕ)) && x3 (1 : Fin (8 : ℕ)) || x3 (1 : Fin (8 : ℕ)) && x3 (2 : Fin (8 : ℕ)) || x3 (2 : Fin (8 : ℕ)) && x3 (3 : Fin (8 : ℕ)) || x3 (0 : Fin (8 : ℕ)) && x3 (4 : Fin (8 : ℕ)) || x3 (1 : Fin (8 : ℕ)) && x3 (5 : Fin (8 : ℕ)) || x3 (2 : Fin (8 : ℕ)) && x3 (6 : Fin (8 : ℕ)) || x3 (3 : Fin (8 : ℕ)) && x3 (7 : Fin (8 : ℕ)) || x3 (4 : Fin (8 : ℕ)) && x3 (6 : Fin (8 : ℕ)) || x3 (5 : Fin (8 : ℕ)) && x3 (7 : Fin (8 : ℕ)) || x3 (7 : Fin (8 : ℕ)) && x3 (4 : Fin (8 : ℕ)); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 → x4.size ≤ (14 : ℕ) → List.countP x1 x4.gates ≤ (1 : ℕ) → (∀ (x8 : Fin (8 : ℕ) → Bool), x4.eval (x2 Bool.false x8) = x3 x8) → ∃ (x9 : Fin (8 : ℕ) → Bool), x4.eval (x2 Bool.true x9) ≠ (x3 x9 || x9 (0 : Fin (8 : ℕ)) || x9 (3 : Fin (8 : ℕ))) := by
  exact PEqualNP.Outside.L_meta_2504.deskFromChecks PEqualNP.Outside.L_meta_2504.allRows
