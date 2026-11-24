import PEqualNP.Defs
namespace Theta2960
open PEqualNP.CircuitLowerBounds
abbrev Word := BitVec 128
def signed (w : Word) (p : Bool) := if p then ~~~w else w
def norm (w : Word) := signed w (w[0])
def gate (a b : Word) (p q : Bool) := norm (signed a p &&& signed b q)
def Good (w : Word) := w ≠ 0 ∧ w[0] = false

theorem norm_flip (w : Word) : norm (~~~w) = norm w := by
  cases e : w[0] <;> simp [norm,signed,BitVec.getLsbD_not,e]

theorem norm_canonical (w : Word) : (norm w)[0] = false := by
  cases e : w[0] <;> simp [norm,signed,BitVec.getLsbD_not,e]

theorem reconstruct (w : Word) : signed (norm w) (w[0]) = w := by
  cases e : w[0] <;> simp [norm,signed,e]

theorem reconstruct_flip (w : Word) : signed (norm w) (!w[0]) = ~~~w := by
  cases e : w[0] <;> simp [norm,signed,e]

inductive Live (target : Word) : Nat → Finset Word → Prop
  | stop (ok : Good target) : Live target 0 {target}
  | binary {k : Nat} {U : Finset Word} {a b : Word} {p q : Bool}
      (ha : Good a) (hb : Good b) (ne : a ≠ b)
      (fresh : gate a b p q ∉ insert a (insert b U))
      (tail : Live target k (insert (gate a b p q) U)) :
      Live target (k+1) (insert a (insert b U))

theorem live_good {target k S} (h : Live target k S) : ∀ w ∈ S, Good w := by
  induction h with
  | stop ok => simpa using ok
  | binary ha hb _ _ _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun w hw => ih w (Finset.mem_insert_of_mem hw)⟩

theorem live_size {target k S} (h : Live target k S) : S.card ≤ k+1 := by
  induction h with
  | stop _ => simp
  | @binary k U a b p q _ _ _ fresh _ ih =>
    have absent : gate a b p q ∉ U := fun x => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem x))
    rw [Finset.card_insert_of_notMem absent] at ih
    have aBound := Finset.card_insert_le (a:=a) (s:=insert b U)
    have bBound := Finset.card_insert_le (a:=b) (s:=U)
    omega

private theorem signed_agree (w : Word) (p : Bool) (i j : Fin 128)
    (h : w.getLsbD i.val = w.getLsbD j.val) :
    (signed w p).getLsbD i.val = (signed w p).getLsbD j.val := by
  cases p
  · exact h
  · change (~~~w).getLsbD _ = (~~~w).getLsbD _
    simp only [BitVec.getLsbD_not,i.isLt,j.isLt,decide_true,Bool.true_and,h]

theorem live_distinguish {target k S} (h : Live target k S) (i j : Fin 128)
    (diff : target.getLsbD i.val ≠ target.getLsbD j.val) :
    ∃ a ∈ S, a.getLsbD i.val ≠ a.getLsbD j.val := by
  induction h with
  | stop _ => exact ⟨_,by simp,diff⟩
  | @binary k U a b p q ha hb ne fresh tail ih =>
    obtain ⟨w,mem,dist⟩ := ih
    rcases Finset.mem_insert.mp mem with rfl|u
    · by_contra fail
      push_neg at fail
      have ea := fail a (Finset.mem_insert_self ..)
      have eb := fail b (Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
      apply dist
      apply signed_agree
      simp only [BitVec.getLsbD_and,signed_agree a p i j ea,signed_agree b q i j eb]
    · exact ⟨w,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem u),dist⟩

-- Truth-table execution follows the circuit verifier of loris-olsem in upstream PR 4332.
abbrev Sig := Word
def zero : Sig := 0
def one : Sig := BitVec.allOnes 128
def neg (a : Sig) : Sig := ~~~a
def bin (d : Bool) (a b : Sig) : Sig := if d then a ||| b else a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
private theorem bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]

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

def bit (i : Fin 128) (a : Sig) : Bool := a.getLsbD i.val
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





def charge (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def Seen (w : List Word) (z : Word) := norm z = 0 ∨ norm z ∈ w.map norm

private theorem oldSeen {w : List Word} {z : Word} (h : represented w z) : Seen w z := by
  rcases h with hz|hz
  · exact Or.inr (List.mem_map.mpr ⟨z,hz,rfl⟩)
  · unfold proper at hz
    by_cases h₀ : z=zero
    · subst z; exact Or.inl (by decide)
    · have h₁ : z=one := by by_contra hn; exact hz ⟨h₀,hn⟩
      subst z; exact Or.inl (by decide)

private theorem sameGate (w : Word) (p q : Bool) : gate w w p q = 0 ∨ gate w w p q = norm w := by
  cases p <;> cases q <;> simp [gate,signed,BitVec.and_self,norm_flip]
  all_goals exact Or.inl (by decide)

private theorem normalizedGate (d : Bool) (a b : Word) :
    ∃ p q, norm (bin d a b) = gate (norm a) (norm b) p q := by
  cases d
  · exact ⟨a[0],b[0],by simp only [bin,gate,Bool.false_eq_true,ite_false,reconstruct]⟩
  · exact ⟨!a[0],!b[0],by simp only [bin,gate,ite_true,reconstruct_flip,←BitVec.not_or,norm_flip]⟩

def GateEvidence (w : List Word) (g : Gate) :=
  Seen w (gv w g) ∨ (charge g = true ∧ ∃ a ∈ w.map norm, ∃ b ∈ w.map norm,
    ∃ p q, Good a ∧ Good b ∧ a ≠ b ∧ norm (gv w g) = gate a b p q)
private lemma norm_idem (w : Word) : norm (norm w) = norm w := by
  change signed (norm w) (norm w)[0] = norm w
  rw [norm_canonical]; rfl

private lemma oldGood (w : Word) (hp : proper w) : Good (norm w) := by
  refine ⟨?_,norm_canonical w⟩
  intro z
  have eq := reconstruct w
  rw [z] at eq
  cases b : w[0] <;> rw [b] at eq
  · exact hp.1 eq.symm
  · exact hp.2 ((show signed (0 : Word) true = one by decide) ▸ eq.symm)

private theorem gateEvidence (w : List Word) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2) :
    GateEvidence w g := by
  by_cases charged : charge g = true
  · rcases gate_rep w g h with hrep | (⟨a,ha,_,eq⟩ | ⟨d,a,b,ha,hb,pa,pb,ne,eq⟩)
    · exact Or.inl (oldSeen hrep)
    · left; right
      rw [eq]; change norm (~~~a) ∈ w.map norm
      rw [norm_flip]; exact List.mem_map.mpr ⟨a,ha,rfl⟩
    · obtain ⟨p,q,geq⟩ := normalizedGate d a b
      have am : norm a ∈ w.map norm := List.mem_map.mpr ⟨a,ha,rfl⟩
      have bm : norm b ∈ w.map norm := List.mem_map.mpr ⟨b,hb,rfl⟩
      by_cases same : norm a = norm b
      · left; unfold Seen; rw [eq,geq,←same]
        rcases sameGate (norm a) p q with z|z
        · exact Or.inl z
        · exact Or.inr (by rwa [z,norm_idem])
      · exact Or.inr ⟨charged,norm a,am,norm b,bm,p,q,oldGood a pa,oldGood b pb,same,congrArg norm eq |>.trans geq⟩
  · obtain ⟨o,is⟩ := g; cases o <;> try {exact False.elim (charged rfl)}
    left; unfold Seen
    cases is with
    | nil => exact Or.inl (show norm (~~~(0 : Word)) = 0 by decide)
    | cons i is =>
      change norm (~~~(w.getD i zero)) = 0 ∨ norm (~~~(w.getD i zero)) ∈ w.map norm
      rw [norm_flip]; exact oldSeen (get_rep w i)
private lemma liftStep {target : Word} {k : Nat} {S : Finset Word} (run : Live target k S)
    (w : List Word) (g : Gate) (ev : GateEvidence w g)
    (sub : ∀ a ∈ S, a ∈ w.map norm ++ [norm (gv w g)]) :
    ∃ n U, n ≤ k+(charge g).toNat ∧ Live target n U ∧ ∀ a ∈ U, a ∈ w.map norm := by
  let z := norm (gv w g)
  by_cases mem : z ∈ S
  · by_cases prior : z ∈ w.map norm
    · refine ⟨k,S,by omega,run,?_⟩
      intro a ha
      rcases (show a ∈ w.map norm ∨ a=z by simpa [z] using sub a ha) with p|rfl
      · exact p
      · exact prior
    · have nz := (live_good run z mem).1
      rcases ev with old | ⟨charged,a,am,b,bm,p,q,ga,gb,ne,eq⟩
      · exact False.elim (old.elim nz prior)
      · let U := S.erase z
        have hu : ∀ t ∈ U, t ∈ w.map norm := by
          intro t ht
          obtain ⟨neq,mem⟩ := Finset.mem_erase.mp ht
          simpa [neq,z] using sub t mem
        have rz : z = gate a b p q := eq
        have tail : Live target k (insert (gate a b p q) U) := by
          simpa only [←rz,U,Finset.insert_erase mem] using run
        have fresh : gate a b p q ∉ insert a (insert b U) := by
          rw [←rz]
          intro h
          rcases Finset.mem_insert.mp h with e|hm
          · exact prior (e ▸ am)
          rcases Finset.mem_insert.mp hm with e|h
          · exact prior (e ▸ bm)
          · exact prior (hu _ h)
        refine ⟨k+1,insert a (insert b U),by simp [charged],Live.binary ga gb ne fresh tail,?_⟩
        simpa using And.intro am (And.intro bm hu)
  · refine ⟨k,S,by omega,run,?_⟩
    intro a ha
    rcases (show a ∈ w.map norm ∨ a=z by simpa [z] using sub a ha) with p|rfl
    · exact p
    · exact False.elim (mem ha)

theorem extract {target : Word} (gs : List Gate) (w : List Word)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (good : Good target) (out : target ∈ (execute gs w).map norm) :
    ∃ k S, k ≤ gs.countP charge ∧ Live target k S ∧ ∀ a ∈ S, a ∈ w.map norm := by
  induction gs generalizing w with
  | nil => exact ⟨0,{target},by simp,Live.stop good,by simpa [execute] using out⟩
  | cons g gs ih =>
    obtain ⟨k,S,hk,run,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) out
    obtain ⟨n,U,hn,hu,root⟩ := liftStep run w g (gateEvidence w g (legal g (by simp)))
      (by simpa only [List.map_append,List.map_singleton] using hs)
    refine ⟨n,U,?_,hu,root⟩
    cases h : charge g <;> simp [h] at hn ⊢ <;> omega

theorem required {T k S} (h : Live T k S) (roots : List Word) (a : Word)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Fin 128) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_distinguish h r s diff
  by_cases eq : v=a
  · exact eq ▸ hv
  · exact False.elim (hd (isolated v (sub _ hv) eq))
def inputs : List Word := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000]
def theta : Word := 0xfffffffcfffffff8ffeeffcceaeac8c8
def targetFun (x : Fin 7 → Bool) := [(0,1),(1,2),(0,4),(1,5),(2,6),(3,5),(4,6),(6,3)].any fun (p : Fin 7 × Fin 7) => x p.1 && x p.2
def sample (r : Fin 128) (j : Fin 7) := bit r (inputs.getD j.val zero)
theorem input_list : List.ofFn (fun j : Fin 7 => inputs.getD j.val zero) = inputs := rfl
theorem sampled (r : Fin 128) : List.ofFn (sample r) = inputs.map (bit r) := by
  rw [←input_list,List.map_ofFn]
  rfl
theorem table_eval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Fin 128) : bit r ((execute C.gates inputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sampled]
  rfl
theorem target_bits : ∀ r : Fin 128, bit r theta = targetFun (sample r) := by decide +kernel

def neighbor (i : Fin 7) : Nat := ![1,0,1,5,0,1,2] i
def offRow (i : Fin 7) : Fin 128 := Fin.ofNat 128 (1 <<< neighbor i)
def onRow (i : Fin 7) : Fin 128 := Fin.ofNat 128 ((1 <<< neighbor i) ||| (1 <<< i.val))
theorem separated : ∀ i : Fin 7,
    (bit (offRow i) theta != bit (onRow i) theta) &&
    (inputs.all fun w => w == inputs.getD i.val zero || bit (offRow i) w == bit (onRow i) w) = true := by
  decide +kernel

theorem circuitTrace (C : Circuit) (fan : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : PEqualNP.MetaComplexity.circuitFun 7 C = targetFun) :
    ∃ k ≤ C.gates.countP charge, Live theta k inputs.toFinset := by
  have eq : (execute C.gates inputs).getD C.output zero = theta := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Fin 128 := ⟨j,hj⟩
    exact (table_eval C fan C.output r).trans ((congrFun computes (sample r)).trans (target_bits r).symm)
  have r := get_rep (execute C.gates inputs) C.output
  rw [eq] at r
  have inside := r.resolve_right (fun hn => hn (by unfold proper; decide))
  have out : theta ∈ (execute C.gates inputs).map norm :=
    List.mem_map.mpr ⟨theta,inside,by decide⟩
  obtain ⟨k,S,hk,run,sub⟩ := extract C.gates inputs fan (by unfold Good; decide : Good theta) out
  rw [show inputs.map norm = inputs by decide +kernel] at sub
  have total : S = inputs.toFinset := by
    refine Finset.Subset.antisymm (fun w hw => List.mem_toFinset.mpr (sub _ hw)) ?_
    intro w hw
    have hm := List.mem_toFinset.mp hw
    rw [←input_list,List.mem_ofFn] at hm
    obtain ⟨i,rfl⟩ := hm
    have cut := separated i
    simp only [Bool.and_eq_true,Bool.not_eq_true',bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq] at cut
    apply required run inputs _ sub (offRow i) (onRow i) cut.1
    exact fun v hv hn => (cut.2 v hv).resolve_left hn
  exact ⟨k,hk,total ▸ run⟩

theorem charge_eq (g : Gate) : charge g =
    GateOp.rec true true false (fun _ => true) true g.op := by cases g with | mk op l => cases op <;> rfl
end Theta2960
