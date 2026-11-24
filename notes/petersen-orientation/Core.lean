import Mathlib
import PEqualNP.Defs

namespace Replay2161

set_option maxRecDepth 12000
set_option exponentiation.threshold 1024

abbrev Word := BitVec 512

def top : Word := BitVec.allOnes 512
def proper (a : Word) : Prop := a ≠ 0 ∧ a ≠ top
instance (a : Word) : Decidable (proper a) := by unfold proper; infer_instance

def combine (disj : Bool) (a b : Word) : Word := if disj then a ||| b else a &&& b

lemma laws (a : Word) :
    combine true a 0 = a ∧ combine false a 0 = 0 ∧
    combine true a top = top ∧ combine false a top = a ∧
    combine true a a = a ∧ combine false a a = a := by
  exact ⟨by simp [combine], by simp [combine], BitVec.or_allOnes, BitVec.and_allOnes,
    BitVec.or_self, BitVec.and_self⟩

lemma comm (d : Bool) (a b : Word) : combine d a b = combine d b a := by
  cases d <;> simp [combine, BitVec.and_comm, BitVec.or_comm]

inductive Live (target : Word) : ℕ → ℕ → Finset Word → Prop
  | done : Live target 0 0 {target}
  | unary {b t U a} (ha : proper a) (fresh : ~~~a ∉ insert a U)
      (tail : Live target b t (insert (~~~a) U)) : Live target b (t+1) (insert a U)
  | binary {b t U a c d} (ha : proper a) (hc : proper c) (ne : a ≠ c)
      (fresh : combine d a c ∉ insert a (insert c U))
      (tail : Live target b t (insert (combine d a c) U)) :
      Live target (b+1) t (insert a (insert c U))

lemma Live.good {target : Word} (valid : proper target) {b t S} (h : Live target b t S) :
    ∀ a ∈ S, proper a := by
  induction h with
  | done => simpa using valid
  | unary ha hf ht ih =>
    intro a h
    rcases Finset.mem_insert.mp h with rfl | h
    · exact ha
    · exact ih _ (Finset.mem_insert_of_mem h)
  | binary ha hc _ _ ht ih =>
    intro a h
    rcases Finset.mem_insert.mp h with rfl | h
    · exact ha
    rcases Finset.mem_insert.mp h with rfl | h
    · exact hc
    · exact ih _ (Finset.mem_insert_of_mem h)

def Feasible (target : Word) (b t : ℕ) (S : Finset Word) : Prop :=
  ∃ i ≤ b, ∃ j ≤ t, ∃ T ⊆ S, Live target i j T

lemma weaken {x b t S b' t' S'} (h : Feasible x b t S)
    (hb : b ≤ b') (ht : t ≤ t') (hs : S ⊆ S') : Feasible x b' t' S' := by
  obtain ⟨i,hi,j,hj,T,hT,hL⟩ := h
  exact ⟨i,hi.trans hb,j,hj.trans ht,T,hT.trans hs,hL⟩

lemma ignore {x z b t S} (hx : proper x) (h : Feasible x b t (insert z S))
    (hz : z ∈ S ∨ ¬ proper z) : Feasible x b t S := by
  obtain ⟨i,hi,j,hj,T,hT,hL⟩ := h
  refine ⟨i,hi,j,hj,T,?_,hL⟩
  intro a ha
  rcases Finset.mem_insert.mp (hT ha) with rfl | h
  · exact hz.resolve_right fun hnot => hnot (hL.good hx _ ha)
  · exact h

lemma unary_pull {x a b t S} (hx : proper x) (ha : a ∈ S)
    (h : Feasible x b t (insert (~~~a) S)) : Feasible x b (t+1) S := by
  by_cases bad : ~~~a ∈ S ∨ ¬ proper (~~~a)
  · exact weaken (ignore hx h bad) le_rfl (by omega) (by rfl)
  obtain ⟨i,hi,j,hj,T,hT,hL⟩ := h
  by_cases hm : ~~~a ∈ T
  · let U := T.erase (~~~a)
    have inS : U ⊆ S := by
      intro y hy; obtain ⟨hne,hyT⟩ := Finset.mem_erase.mp hy
      exact (Finset.mem_insert.mp (hT hyT)).resolve_left hne
    have p : proper a := by
      by_contra nh
      unfold proper at nh
      push Not at nh
      by_cases za : a = 0
      · subst a; exact bad (Or.inr (by simp [proper,top]))
      · have zt := nh za
        subst a; exact bad (Or.inr (by simp [proper,top]))
    refine ⟨i,hi,j+1,by omega,insert a U,Finset.insert_subset ha inS,Live.unary p ?_ ?_⟩
    · intro h'
      exact bad (Or.inl ((Finset.insert_subset ha inS) h'))
    · simpa [U, Finset.insert_erase hm] using hL
  · exact ⟨i,hi,j,by omega,T,fun y hy => (Finset.mem_insert.mp (hT hy)).resolve_left (by
      rintro rfl; exact hm hy), hL⟩

lemma binary_pull {x a c b t S} (hx : proper x) (d : Bool) (ha : a ∈ S) (hc : c ∈ S)
    (h : Feasible x b t (insert (combine d a c) S)) : Feasible x (b+1) t S := by
  let z := combine d a c
  by_cases redundant : z ∈ S ∨ ¬ proper z
  · exact weaken (ignore hx h redundant) (by omega) le_rfl (by rfl)
  have simple {a c : Word} (haS : a ∈ S) (hcS : c ∈ S) (hz : ¬ (combine d a c ∈ S ∨ ¬ proper (combine d a c))) :
      proper a := by
    constructor
    · rintro rfl
      rw [comm] at hz
      cases d
      · rw [(laws c).2.1] at hz
        exact hz (Or.inr fun h => h.1 rfl)
      · rw [(laws c).1] at hz
        exact hz (Or.inl hcS)
    · rintro rfl
      rw [comm] at hz
      cases d
      · rw [(laws c).2.2.2.1] at hz
        exact hz (Or.inl hcS)
      · rw [(laws c).2.2.1] at hz
        exact hz (Or.inr fun h => h.2 rfl)
  have pa := simple ha hc redundant
  have pc := simple hc ha (by rwa [comm])
  have unequal : a ≠ c := by
    rintro rfl; apply redundant; left; cases d <;> simpa [z,combine] using ha
  obtain ⟨i,hi,j,hj,T,hT,hL⟩ := h
  by_cases hm : z ∈ T
  · let U := T.erase z
    have inS : U ⊆ S := by
      intro y hy; obtain ⟨hne,hyT⟩ := Finset.mem_erase.mp hy
      exact (Finset.mem_insert.mp (hT hyT)).resolve_left hne
    have subset := Finset.insert_subset ha (Finset.insert_subset hc inS)
    refine ⟨i+1,by omega,j,hj,insert a (insert c U),subset,Live.binary (d := d) pa pc unequal ?_ ?_⟩
    · intro hz
      exact redundant (Or.inl (subset hz))
    · simpa [U,z, Finset.insert_erase hm] using hL
  · exact ⟨i,by omega,j,hj,T,fun y hy => (Finset.mem_insert.mp (hT hy)).resolve_left (by
      rintro rfl; exact hm hy), hL⟩

structure Projection where
  q : Word → Word
  neg (a) : q (~~~a) = ~~~(q a)
  bin (d a c) : q (combine d a c) = combine d (q a) (q c)

def constants (P : Projection) (S : Finset Word) : ℕ :=
  (S.filter fun w => ¬ proper (P.q w)).card

def charge (P : Projection) (w : Word) : ℕ := if proper (P.q w) then 0 else 1

lemma c_insert {P : Projection} (w : Word) (S : Finset Word) :
    constants P (insert w S) ≤ constants P S + charge P w := by
  by_cases h : proper (P.q w)
  · simp [constants, charge, Finset.filter_insert, h]
  · simpa [constants, charge, Finset.filter_insert, h] using
      Finset.card_insert_le w (S.filter fun v => ¬proper (P.q v))

lemma c_fresh {P : Projection} (w : Word) (S : Finset Word) (hw : w ∉ S) :
    constants P (insert w S) = constants P S + charge P w := by
  by_cases h : proper (P.q w)
  · simp [constants, charge, Finset.filter_insert, h]
  · simp [constants, charge, Finset.filter_insert, h,
      Finset.card_insert_of_notMem (by simp [Finset.mem_filter,hw] :
        w ∉ S.filter fun v => ¬proper (P.q v))]

lemma neg_proper_iff (w : Word) : proper (~~~w) ↔ proper w := by
  have aux (z : Word) : proper (~~~z) → proper z := by
    rintro h
    constructor <;> rintro rfl <;> simp [proper, top] at h
  exact ⟨aux _, fun h => aux (~~~w) (by simpa only [BitVec.not_not] using h)⟩

lemma const_cases {w : Word} (h : ¬proper w) : w = 0 ∨ w = top := by
  by_cases z : w = 0
  · exact Or.inl z
  · exact Or.inr <| by by_contra ho; exact h ⟨z,ho⟩

lemma idle_of_const {a c : Word} (d : Bool) (h : ¬proper a ∨ ¬proper c) :
    combine d a c = a ∨ combine d a c = c ∨ ¬proper (combine d a c) := by
  have aux (a c : Word) (h : ¬proper c) :
      combine d a c = a ∨ ¬proper (combine d a c) := by
    rcases const_cases h with rfl | rfl <;> cases d
    · exact Or.inr fun h => h.1 (laws a).2.1
    · exact Or.inl (laws a).1
    · exact Or.inl (laws a).2.2.2.1
    · exact Or.inr fun h => h.2 (laws a).2.2.1
  rcases h with h | h
  · rw [comm]; exact Or.inr (aux c a h)
  · exact (aux a c h).imp_right Or.inr

lemma const_bin {a c : Word} (d : Bool) (ha : ¬proper a) (hc : ¬proper c) :
    ¬proper (combine d a c) := by
  rcases idle_of_const d (Or.inl ha : ¬proper a ∨ ¬proper c) with e|e|h
  · rwa [e]
  · rwa [e]
  · exact h

theorem project_live (P : Projection) {x : Word} (hx : proper (P.q x)) {b t S}
    (h : Live x b t S) :
    ∃ n, n + constants P S ≤ b ∧ Feasible (P.q x) n t (S.image P.q) := by
  induction h with
  | done =>
    refine ⟨0, by simp [constants,hx], 0, le_rfl,0,le_rfl,{P.q x}, by simp, .done⟩
  | @unary b t U a _ fresh tail ih =>
    obtain ⟨n,hn,h⟩ := ih
    have f : ~~~a ∉ U := fun he => fresh (Finset.mem_insert_of_mem he)
    have eq := c_fresh (P := P) (~~~a) U f
    have le := c_insert (P := P) a U
    have ng : charge P (~~~a) = charge P a := by simp [charge,P.neg,neg_proper_iff]
    refine ⟨n, by omega, ?_⟩
    rw [Finset.image_insert]
    rw [Finset.image_insert,P.neg] at h
    apply unary_pull hx (Finset.mem_insert_self ..)
    apply weaken h le_rfl le_rfl
    exact Finset.insert_subset_insert _ (Finset.subset_insert ..)
  | @binary b t U a c d _ _ _ fresh tail ih =>
    let z := combine d a c
    let A := insert (P.q a) (insert (P.q c) (U.image P.q))
    obtain ⟨n,hn,h⟩ := ih
    have f : z ∉ U := fun he => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem he))
    have ez := c_fresh (P := P) z U f
    have ec := c_insert (P := P) c U
    have ea := c_insert (P := P) a (insert c U)
    change n + constants P (insert z U) ≤ b at hn
    have hq : P.q z = combine d (P.q a) (P.q c) := P.bin ..
    have htail : Feasible (P.q x) n t (insert (P.q z) A) := by
      rw [Finset.image_insert] at h
      apply weaken h le_rfl le_rfl
      exact Finset.insert_subset_insert _ ((Finset.subset_insert ..).trans (Finset.subset_insert ..))
    rw [Finset.image_insert,Finset.image_insert]
    change ∃ n, _ ∧ Feasible _ n t A
    have ma : P.q a ∈ A := Finset.mem_insert_self ..
    have mc : P.q c ∈ A := Finset.mem_insert_of_mem (Finset.mem_insert_self ..)
    by_cases pc : proper (P.q c) <;> by_cases pa : proper (P.q a)
    · have aa : charge P a = 0 := by simp [charge,pa]
      have ac : charge P c = 0 := by simp [charge,pc]
      refine ⟨n+1, by omega, binary_pull hx d ma mc ?_⟩
      rwa [←hq]
    all_goals
      have idle : P.q z ∈ A ∨ ¬proper (P.q z) := by
        rw [hq]
        rcases idle_of_const d (by tauto : ¬proper (P.q a) ∨ ¬proper (P.q c)) with ha|hc|hn
        · exact Or.inl (by rwa [ha])
        · exact Or.inl (by rwa [hc])
        · exact Or.inr hn
      refine ⟨n, ?_, ignore hx htail idle⟩
    · have aa : charge P a = 1 := by simp [charge,pa]
      have ac : charge P c = 0 := by simp [charge,pc]
      omega
    · have aa : charge P a = 0 := by simp [charge,pa]
      have ac : charge P c = 1 := by simp [charge,pc]
      omega
    · have aa : charge P a = 1 := by simp [charge,pa]
      have ac : charge P c = 1 := by simp [charge,pc]
      have az : charge P z = 1 := by simp [charge,hq,const_bin d pa pc]
      omega

def bit (a : Word) (i : Fin 512) : Bool := a[i.val]

def tab (f : Fin 512 → Bool) : Word :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast List.length_ofFn

lemma tab_bit (f : Fin 512 → Bool) (i : Fin 512) : bit (tab f) i = f i := by
  unfold bit tab
  rw [← BitVec.getLsbD_eq_getElem]
  rw [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using i.isLt), List.getElem_ofFn]

def faceQ (f : Fin 512 → Fin 512) : Projection where
  q a := tab (fun i => bit a (f i))
  neg a := by
    apply BitVec.eq_of_getElem_eq
    intro i hi
    change bit (tab _) ⟨i, hi⟩ = (~~~(tab _))[i]
    rw [tab_bit,BitVec.getElem_not]
    change bit (~~~a) _ = !bit (tab _) ⟨i,hi⟩
    rw [tab_bit]; exact BitVec.getElem_not _
  bin d a c := by
    apply BitVec.eq_of_getElem_eq
    intro i hi
    cases d <;> change bit (tab _) ⟨i,hi⟩ = _ <;> rw [tab_bit]
    · change _ = (tab _ &&& tab _)[i]
      rw [BitVec.getElem_and]
      change _ = (bit (tab _) ⟨i,hi⟩ && bit (tab _) ⟨i,hi⟩)
      rw [tab_bit,tab_bit]; exact BitVec.getElem_and _
    · change _ = (tab _ ||| tab _)[i]
      rw [BitVec.getElem_or]
      change _ = (bit (tab _) ⟨i,hi⟩ || bit (tab _) ⟨i,hi⟩)
      rw [tab_bit,tab_bit]; exact BitVec.getElem_or _

lemma q_bit (f : Fin 512 → Fin 512) (w : Word) (i : Fin 512) :
    bit ((faceQ f).q w) i = bit w (f i) := tab_bit _ _

def available (P : Projection) (S R : Finset Word) : Finset Word := S.image P.q ∪ R

def Guard (P : Projection) (x : Word) (S R : Finset Word) (t lo spent : ℕ) : Prop :=
  proper (P.q x) ∧ ∀ b, Feasible (P.q x) b t (available P S R) → lo ≤ b + spent

lemma guard_bound {P x b t S R lo spent} (g : Guard P x S R t lo spent)
    (h : Live x b t S) : lo + constants P S ≤ b + spent := by
  obtain ⟨n,hn,hf⟩ := project_live P g.1 h
  have hb := g.2 n <| weaken hf le_rfl le_rfl Finset.subset_union_left
  omega

lemma avail_child {P : Projection} {S T R : Finset Word} {z : Word}
    (h : T ⊆ insert z S) : available P T R ⊆ insert (P.q z) (available P S R) := by
  intro x hx
  rcases Finset.mem_union.mp hx with hi|hr
  · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hi
    rcases Finset.mem_insert.mp (h ha) with rfl|hs
    · exact Finset.mem_insert_self ..
    · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hs))
  · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ hr)

def cost (P : Projection) (S R : Finset Word) (z : Word) : ℕ :=
  if P.q z ∈ available P S R ∨ ¬ proper (P.q z) then 0 else 1

lemma guard_binary {P x S T R t lo spent a c d} (g : Guard P x S R t lo spent)
    (ha : a ∈ S) (hc : c ∈ S) (hT : T ⊆ insert (combine d a c) S) :
    Guard P x T R t lo (spent + cost P S R (combine d a c)) := by
  refine ⟨g.1,?_⟩
  intro b h
  let z := combine d a c
  let A := available P S R
  have h' := weaken h le_rfl le_rfl (avail_child hT)
  change Feasible _ _ _ (insert (P.q z) A) at h'
  change lo ≤ b+(spent+cost P S R z)
  unfold cost
  split_ifs with free
  · simpa using g.2 b (ignore g.1 h' free)
  · have ma : P.q a ∈ A := Finset.mem_union_left _ (Finset.mem_image_of_mem _ ha)
    have mc : P.q c ∈ A := Finset.mem_union_left _ (Finset.mem_image_of_mem _ hc)
    have hq : P.q z = combine d (P.q a) (P.q c) := P.bin ..
    rw [hq] at h'
    have hB := g.2 _ (binary_pull g.1 d ma mc h')
    omega

lemma guard_unary {P x S T R t lo spent a} (g : Guard P x S R (t+1) lo spent)
    (ha : a ∈ S) (hT : T ⊆ insert (~~~a) S) :
    Guard P x T R t lo spent := by
  refine ⟨g.1,?_⟩
  intro b h
  have h' := weaken h le_rfl le_rfl (avail_child hT)
  rw [P.neg] at h'
  exact g.2 b (unary_pull g.1 (Finset.mem_union_left _ (Finset.mem_image_of_mem _ ha)) h')

lemma count_live {x b t S} (h : Live x b t S) : S.card ≤ b+1 := by
  induction h with
  | done => simp
  | @unary b t U a _ fresh tail ih =>
    have hn : ~~~a ∉ U := fun he => fresh (Finset.mem_insert_of_mem he)
    rw [Finset.card_insert_of_notMem hn] at ih
    exact (Finset.card_insert_le ..).trans ih
  | @binary b t U a c d _ _ _ fresh tail ih =>
    have hn : combine d a c ∉ U := fun he => fresh
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem he))
    rw [Finset.card_insert_of_notMem hn] at ih
    have hc := Finset.card_insert_le c U
    have ha := Finset.card_insert_le a (insert c U)
    omega

def distinguishes (t : ℕ) (w : Word) (i j : Fin 512) : Prop :=
  if t = 0 then bit w i = true ∧ bit w j = false else bit w i ≠ bit w j

lemma distinguish_bit {a c : Word} {d : Bool} {t : ℕ} {i j : Fin 512}
    (h : distinguishes t (combine d a c) i j) :
    distinguishes t a i j ∨ distinguishes t c i j := by
  have eq (k : Fin 512) : bit (combine d a c) k =
      if d then (bit a k || bit c k) else (bit a k && bit c k) := by
    cases d <;> simp [bit,combine]
  cases d <;> by_cases ht : t=0 <;>
    simp only [distinguishes,ht,eq,ite_true,ite_false,Bool.false_eq_true] at h ⊢ <;>
    cases e1 : bit a i <;> cases e2 : bit a j <;> cases e3 : bit c i <;> cases e4 : bit c j <;> simp_all

lemma distinguish_old {a : Word} {t : ℕ} {i j : Fin 512} (h : distinguishes t a i j) :
    distinguishes (t+1) a i j := by
  simp only [distinguishes,Nat.succ_ne_zero,ite_false]
  by_cases ht : t=0
  · simp only [distinguishes,ht,ite_true] at h
    simp [h.1,h.2]
  · simpa [distinguishes,ht] using h

lemma distinguishes_live {x b t S} (h : Live x b t S) {i j : Fin 512}
    (hi : bit x i = true) (hj : bit x j = false) : ∃ a ∈ S, distinguishes t a i j := by
  induction h with
  | done => exact ⟨x,by simp,by simp [distinguishes,hi,hj]⟩
  | unary _ _ tail ih =>
    obtain ⟨a,ha,hm⟩ := ih
    rcases Finset.mem_insert.mp ha with rfl | hw
    · refine ⟨_,Finset.mem_insert_self ..,?_⟩
      have h := distinguish_old hm
      simpa [distinguishes,bit] using h
    · exact ⟨_,Finset.mem_insert_of_mem hw,distinguish_old hm⟩
  | binary _ _ _ _ tail ih =>
    obtain ⟨a,ha,hm⟩ := ih
    rcases Finset.mem_insert.mp ha with rfl | hw
    · rcases distinguish_bit hm with hl|hr
      · exact ⟨_,Finset.mem_insert_self ..,hl⟩
      · exact ⟨_,Finset.mem_insert_of_mem (Finset.mem_insert_self ..),hr⟩
    · exact ⟨_,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hw),hm⟩

open PEqualNP.CircuitLowerBounds

def gv (w : List Word) (g : Gate) : Word :=
  let xs := g.inputs.map (fun i => w.getD i 0)
  match g.op with
  | .and => xs.foldr (combine false) top
  | .or => xs.foldr (combine true) 0
  | .not => ~~~(xs.headD 0)
  | _ => 0

def execute (gs : List Gate) (w : List Word) : List Word :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def pool (w : List Word) : Finset Word := insert 0 (insert top w.toFinset)

lemma read_mem (w : List Word) (i : Nat) : w.getD i 0 ∈ pool w := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : w[i]? with
  | none => exact Finset.mem_insert_self ..
  | some a =>
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (List.mem_toFinset.mpr (List.mem_of_getElem? hi)))

def negative (g : Gate) : Bool :=
  match g.op with | .not => true | _ => false

lemma gate_pull {x b t w} (hx : proper x) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : Feasible x b t (insert (gv w g) (pool w))) :
    Feasible x (b + (if negative g then 0 else 1))
      (t + (if negative g then 1 else 0)) (pool w) := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  obtain ⟨ops,hi⟩ := hg
  have zero' : 0 ∈ pool w := Finset.mem_insert_self ..
  have top' : top ∈ pool w := Finset.mem_insert_of_mem (Finset.mem_insert_self ..)
  have idle (z : Word) (hz : z ∈ pool w) (h : Feasible x b t (insert z (pool w))) :
      Feasible x (b+1) t (pool w) := by
    exact weaken (ignore hx h (Or.inl hz)) (by omega) le_rfl (by rfl)
  cases ins with
  | nil =>
    rcases ops with rfl | rfl | rfl
    · exact idle top top' h
    · exact idle 0 zero' h
    · exact unary_pull hx zero' h
  | cons a ins =>
    cases ins with
    | nil =>
      rcases ops with rfl | rfl | rfl
      · exact idle _ (read_mem _ a) (by simpa only [gv,List.map_cons,List.map_nil,
          List.foldr_cons,List.foldr_nil,(laws _).2.2.2.1] using h)
      · exact idle _ (read_mem _ a) (by simpa only [gv,List.map_cons,List.map_nil,
          List.foldr_cons,List.foldr_nil,(laws _).1] using h)
      · exact unary_pull hx (read_mem _ a) h
    | cons c is =>
      cases is with
      | cons i ss => simp at hi
      | nil =>
        rcases ops with rfl | rfl | rfl
        · exact binary_pull (t := t) hx false (read_mem _ a) (read_mem _ c) (by
            simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,
              (laws _).2.2.2.1] using h)
        · exact binary_pull (t := t) hx true (read_mem _ a) (read_mem _ c) (by
            simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,
              (laws _).1] using h)
        · exact unary_pull hx (read_mem _ a) h

lemma extract {x} (hx : proper x) (gs : List Gate) (w : List Word)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2)
    (hout : x ∈ execute gs w) :
    Feasible x (gs.filter (fun g => !negative g)).length (gs.filter negative).length (pool w) := by
  induction gs generalizing w with
  | nil =>
    exact ⟨0,le_rfl,0,le_rfl,{x},Finset.singleton_subset_iff.mpr
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (List.mem_toFinset.mpr hout))),.done⟩
  | cons g gs ih =>
    have h := ih (w ++ [gv w g]) (fun a ha => legal a (by simp [ha])) hout
    have e : pool (w ++ [gv w g]) = insert (gv w g) (pool w) := by
      ext a; simp [pool]; tauto
    rw [e] at h
    have m := gate_pull hx g (legal g (by simp)) h
    cases n : negative g <;> simpa [List.filter_cons,n] using m

lemma bit_zero (i) : bit 0 i = false := by simp [bit]
lemma bit_top (i) : bit top i = true := by
  change (BitVec.allOnes 512)[i.val] = true
  exact BitVec.getElem_allOnes ..
lemma bit_not (w : Word) (i) : bit (~~~w) i = !bit w i := BitVec.getElem_not _
lemma bit_bin (d : Bool) (a b : Word) (i) : bit (combine d a b) i =
    if d then bit a i || bit b i else bit a i && bit b i := by
  cases d <;> simp [bit,combine]
lemma read_bit (w : List Word) (j : Nat) (i : Fin 512) :
    (w.map (fun a => bit a i)).getD j false = bit (w.getD j 0) i := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl
lemma run_bit (g : Gate) (w : List Word) (i : Fin 512)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit (gv w g) i = g.op.eval (g.inputs.map fun j => (w.map (fun a => bit a i)).getD j false) := by
  obtain ⟨o, l⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  simp only [read_bit]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_top _
    | cons a l ih =>
      change bit (combine false _ _) i = (_ && _)
      rw [bit_bin]; exact congrArg (fun x => bit (w.getD a 0) i && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit (combine true _ _) i = (_ || _)
      rw [bit_bin]; exact congrArg (fun x => bit (w.getD a 0) i || x) ih
  · cases l with
    | nil => exact (bit_not (0 : Word) i).trans (by rw [bit_zero]; rfl)
    | cons a l => exact bit_not _ _
lemma execute_bits (gs : List Gate) (w : List Word) (i : Fin 512)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    (execute gs w).map (fun a => bit a i) =
    gs.foldl (fun (l : List Bool) g => l ++ [g.op.eval (g.inputs.map fun j => l.getD j false)])
      (w.map (fun a => bit a i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w ++ [gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit g w i (hg g (by simp))]
lemma foldl_append_getD {α : Type} (f : List α → Gate → α) (gs : List Gate)
    (l : List α) (i : Nat) (hi : i < l.length) (d : α) :
    (gs.foldl (fun acc g => acc ++ [f acc g]) l).getD i d = l.getD i d := by
  induction gs generalizing l with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (l ++ [f l g]).length := by simp; omega
    rw [ih (l ++ [f l g]) hlt]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
def edgeF (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
set_option maxRecDepth 20000 in

def raw : List Word := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000, 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000, 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def target : Word := 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
def testRow (i : Fin 512) (j : Fin 9) := i.val.testBit j.val
lemma rawRow (i : Fin 512) : raw.map (fun a => bit a i) = List.ofFn (testRow i) := by
  have ok : ∀ r : Fin 512, raw.map (fun a => bit a r) = List.ofFn (testRow r) := by decide +kernel
  exact ok i
lemma targetRow (i : Fin 512) : bit target i = edgeF (testRow i) := by
  have ok : ∀ r : Fin 512, bit target r = edgeF (testRow r) := by decide +kernel
  exact ok i
lemma targetProper : proper target := by decide +kernel
lemma target_mem (C : Circuit) (hf : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ y : Fin 9 → Bool, C.eval (List.ofFn y) = edgeF y) :
    target ∈ execute C.gates raw := by
  let w := execute C.gates raw
  have e : w.getD C.output 0 = target := by
    apply BitVec.eq_of_getElem_eq
    intro r hr
    change bit (w.getD C.output 0) ⟨r,hr⟩ = bit target ⟨r,hr⟩
    rw [targetRow, ←read_bit]
    change ((execute C.gates raw).map _).getD C.output false = _
    rw [execute_bits _ _ _ (fun g hg => (hf g hg).1),rawRow]
    exact he _
  have h := read_mem w C.output
  rw [e] at h
  simpa only [pool,Finset.mem_insert,List.mem_toFinset, targetProper.1,targetProper.2,
    false_or] using h
def extra : Word := combine true (raw.getD 0 0) (raw.getD 2 0)
def start : List Word := raw ++ [extra]
lemma extraRow (r : Fin 512) : bit extra r = (testRow r 0 || testRow r 2) := by
  have ok : ∀ i : Fin 512, bit extra i = (testRow i 0 || testRow i 2) := by decide +kernel
  exact ok r
lemma first_value {g : Gate} {gs : List Gate}
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp))
    (first : ∀ y : Fin 9 → Bool,
      ((Circuit.mk (g :: gs) 0).wires (List.ofFn y)).getD 9 false = (y 0 || y 2)) :
    gv raw g = extra := by
  apply BitVec.eq_of_getElem_eq
  intro r hr
  let i : Fin 512 := ⟨r,hr⟩
  change bit (gv raw g) i = bit extra i
  rw [extraRow, run_bit g raw i hg,rawRow]
  have h := first (testRow i)
  simp only [Circuit.wires,List.foldl_cons] at h
  rw [foldl_append_getD _ gs _ 9 (by simp) false] at h
  simpa [List.getD_eq_getElem?_getD] using h
lemma uniqueNegCount (gs : List Gate)
    (h : ∃! i : Fin gs.length, negative (gs.get i) = true) :
    (gs.filter negative).length = 1 := by
  induction gs with
  | nil => obtain ⟨i, _⟩ := h; exact Fin.elim0 i
  | cons g gs ih =>
    obtain ⟨i, hi, only⟩ := h
    by_cases hg : negative g = true
    · have hone : (0 : Fin (g :: gs).length) = i := only 0 hg
      have nil : gs.filter negative = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro a ha hn
        obtain ⟨j, hj⟩ := List.mem_iff_get.mp ha
        have hs : negative ((g :: gs).get j.succ) = true := by
          change negative (gs.get j) = true
          rwa [hj]
        have eq := (only j.succ hs).trans hone.symm
        exact (Fin.succ_ne_zero j) eq
      simp [hg,nil]
    · have htail : ∃! j : Fin gs.length, negative (gs.get j) = true := by
        cases i using Fin.cases with
        | zero => exact (hg hi).elim
        | succ j =>
          refine ⟨j, hi, ?_⟩
          intro k hk
          exact Fin.succ_injective _ (only k.succ hk)
      simpa [hg] using ih htail

lemma first_nonneg {g : Gate} {gs : List Gate}
    (hfirst : ∀ y : Fin 9 → Bool,
      ((Circuit.mk (g :: gs) 0).wires (List.ofFn y)).getD 9 false = (y 0 || y 2)) :
    negative g = false := by
  cases hop : g.op <;> simp only [negative,hop]
  let x : Fin 9 → Bool := fun _ => false
  have z (j : ℕ) : (List.ofFn x).getD j false = false := by
    by_cases hj : j < 9
    · have hh : j < (List.ofFn x).length := by simpa only [List.length_ofFn] using hj
      rw [List.getD_eq_getElem _ _ hh,List.getElem_ofFn]
    · have hn : (List.ofFn x).length ≤ j := by simpa using Nat.le_of_not_gt hj
      exact List.getD_eq_default _ _ hn
  have h := hfirst x
  simp only [Circuit.wires, List.foldl_cons] at h
  have hl : 9 < (List.ofFn x ++ [g.op.eval (g.inputs.map fun j =>
      (List.ofFn x).getD j false)]).length := by simp
  rw [foldl_append_getD _ gs _ 9 hl false] at h
  have heq : (List.ofFn x ++ [g.op.eval (g.inputs.map fun j =>
      (List.ofFn x).getD j false)]).getD 9 false =
      g.op.eval (g.inputs.map fun j => (List.ofFn x).getD j false) := by
    simp [List.getD_eq_getElem?_getD]
  rw [heq,hop] at h
  cases he : g.inputs with
  | nil => simp [he,GateOp.eval,x] at h
  | cons a as =>
    simp only [he, List.map_cons, GateOp.eval, List.headD_cons, z] at h
    exact Bool.noConfusion h

lemma neg_iff (g : Gate) : negative g = true ↔ g.op = GateOp.not := by
  cases g with
  | mk op xs => cases op <;> simp [negative]

lemma starts {C : Circuit} (hsize : C.size ≤ 15) (hf : PEqualNP.MetaComplexity.FanInTwo C)
    (hn : ∃! i : Fin C.gates.length, (C.gates.get i).op = GateOp.not)
    (hw9 : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 2))
    (he : ∀ y : Fin 9 → Bool, C.eval (List.ofFn y) = edgeF y) :
    Feasible target 13 1 start.toFinset := by
  obtain ⟨i,hi,only⟩ := hn
  have hn1 := uniqueNegCount C.gates ⟨i,(neg_iff _).2 hi,fun j hj => only j ((neg_iff _).1 hj)⟩
  cases hgs : C.gates with
  | nil => simp [hgs] at hn1
  | cons g gs =>
    have hlen : gs.length ≤ 14 := by
      change C.gates.length ≤ 15 at hsize; rw [hgs] at hsize; simp at hsize; omega
    have hh : ∀ y : Fin 9 → Bool,
        ((Circuit.mk (g :: gs) 0).wires (List.ofFn y)).getD 9 false = (y 0 || y 2) := by
      intro y; simpa only [Circuit.wires,hgs] using hw9 y
    have hneg := first_nonneg hh
    rw [hgs] at hn1
    simp only [List.filter_cons, hneg, Bool.false_eq_true, ↓reduceIte] at hn1
    have counts := List.length_eq_length_filter_add (l:=gs) negative
    change gs.length = (gs.filter negative).length + (gs.filter (fun g => !negative g)).length at counts
    have hv := first_value (hf g (by rw [hgs]; simp)).1 hh
    have hm := target_mem C hf he
    rw [hgs] at hm
    change target ∈ execute gs (raw ++ [gv raw g]) at hm
    rw [hv] at hm
    have h := extract targetProper gs start (fun a ha => hf a (by rw [hgs]; simp [ha])) hm
    have h' := weaken h (show (gs.filter (fun g => !negative g)).length ≤ 13 by omega)
      (show (gs.filter negative).length ≤ 1 by omega) (by rfl)
    exact ignore targetProper (ignore targetProper h' (Or.inr fun q => q.1 rfl))
      (Or.inr fun q => q.2 rfl)

end Replay2161
