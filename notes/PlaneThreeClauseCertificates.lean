import Mathlib
import PEqualNP.Outside.L_meta_1485

/-!
On the incidence and quadrangle inputs, a least candidate must distinguish
the two operands of each AND in both directions. Replacing the gate by either
operand must actually turn the output on for a rejected quadrangle.
The circuit deletion and monotonicity lemmas are from L-meta-1485.
The lemmas doubleStarFlag and doubleStarReject realize every incident point-line
double star by three clauses. The lemma noncrossingPair excludes every pair
with both cross incidences absent. Each finite frame certificate rules out one
three-flag matching via matchingObstruction. The companion exhaustive Python
calculation checks every matching and every remaining candidate flag family.
-/
namespace QuadSeparation
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_1485

def Fits (P N : List Bool → Prop) (C : Circuit) : Prop :=
  (∀ x, P x → C.eval x = true) ∧ (∀ x, N x → C.eval x = false)

def Shorter (n : ℕ) (P N : List Bool → Prop) (C : Circuit) : Prop :=
  ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧ Fits P N D ∧ D.size < C.size

theorem op_ao {C : Circuit} (m : Monotone2 C) :
    ∀ j < C.gates.length, (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := by
  intro j hj
  exact (m _ (gateAt_mem hj)).1

theorem legalBypass {n : ℕ} {C : Circuit} (m : Monotone2 C) (rb : ReadsBack n C)
    {j i : ℕ} (realJ : j < C.gates.length) (mem : i ∈ (gateAt C j).inputs) :
    Monotone2 (bypass n C j i) ∧ ReadsBack n (bypass n C j i) ∧ (bypass n C j i).size < C.size := by
  refine ⟨?_,bypass_readsBack (rb j realJ i mem) rb,?_⟩
  · intro g hg
    obtain ⟨k,hk,op,len⟩ := bypass_mem g hg
    simpa only [op,len] using m k hk
  · change (bypass n C j i).gates.length < C.gates.length
    rw [bypass_length]; omega

theorem andWitness {n : ℕ} {P N : List Bool → Prop} {C : Circuit}
    (m : Monotone2 C) (rb : ReadsBack n C) (correct : Fits P N C)
    (plen : ∀ x, P x → x.length = n) (nlen : ∀ x, N x → x.length = n)
    {j i : ℕ} (realJ : j < C.gates.length) (andJ : (gateAt C j).op = GateOp.and)
    (mem : i ∈ (gateAt C j).inputs) :
    Shorter n P N C ∨ ∃ x, N x ∧ val C x i = true ∧ val C x (n+j) = false ∧
      (bypass n C j i).eval x = true := by
  classical
  let D := bypass n C j i
  have early := rb j realJ i mem
  have pos (x) (px : P x) : D.eval x = true := by
    apply bypass_eval_rel (R := fun a b => a = true → b = true) (fun _ hy => hy)
      opMono_imp (plen x px) (op_ao m) realJ (Or.inl early) _ (correct.1 x px)
    exact fun hy => ((val_and (plen x px) realJ andJ).mp hy i mem).2
  by_cases ok : ∀ x, N x → D.eval x = false
  · obtain ⟨md,rd,sz⟩ := legalBypass m rb realJ mem
    exact Or.inl ⟨D,md,rd,⟨pos,ok⟩,sz⟩
  · push Not at ok
    obtain ⟨x,nx,changed⟩ := ok
    have newOn : D.eval x = true := by simpa using changed
    have ne : val C x (n+j) ≠ val C x i := by
      intro eq
      have same := bypass_eval_eq (nlen x nx) (op_ao m) realJ (Or.inl early) eq
      have old := correct.2 x nx
      change (bypass n C j i).eval x = true at newOn
      simp [same,old] at newOn
    have impl := fun h => ((val_and (nlen x nx) realJ andJ).mp h i mem).2
    exact Or.inr ⟨x,nx,by cases hi : val C x i <;> cases hj : val C x (n+j) <;> simp_all,
      by cases hi : val C x i <;> cases hj : val C x (n+j) <;> simp_all,newOn⟩


theorem andSplit {n : ℕ} {P N : List Bool → Prop} {C : Circuit}
    (m : Monotone2 C) (rb : ReadsBack n C) (ok : Fits P N C)
    (plen : ∀ x, P x → x.length = n) (nlen : ∀ x, N x → x.length = n)
    (least : ¬ Shorter n P N C) {j a b : ℕ} (realJ : j < C.gates.length)
    (op : (gateAt C j).op = GateOp.and) (ins : (gateAt C j).inputs = [a,b]) :
    ∃ x y, N x ∧ N y ∧ x ≠ y ∧ val C x a = true ∧ val C x b = false ∧
        val C y a = false ∧ val C y b = true ∧
        (bypass n C j a).eval x = true ∧ (bypass n C j b).eval y = true := by
  have ma : a ∈ (gateAt C j).inputs := by simp [ins]
  have mb : b ∈ (gateAt C j).inputs := by simp [ins]
  obtain ⟨x,nx,ax,jx,ox⟩ := (andWitness m rb ok plen nlen realJ op ma).resolve_left least
  obtain ⟨y,ny,by',jy,oy⟩ := (andWitness m rb ok plen nlen realJ op mb).resolve_left least
  have fire (z) (nz : N z) (az : val C z a = true) (bz : val C z b = true) : val C z (n+j) = true := by
    apply (val_and (nlen z nz) realJ op).mpr
    intro i im
    refine ⟨rb j realJ i im,?_⟩
    simp only [ins,List.mem_cons,List.not_mem_nil,or_false] at im
    rcases im with rfl | rfl <;> assumption
  have bx : val C x b = false := by cases h : val C x b <;> simp_all
  have ay : val C y a = false := by cases h : val C y a <;> simp_all
  exact ⟨x,y,nx,ny,fun e => by subst y; simp_all,ax,bx,ay,by',ox,oy⟩

abbrev D : Finset (Fin 13) := {0,1,3,9}
def flagInput (p l : Fin 13) := (List.ofFn fun v : Fin 13 => decide (v = p)) ++
    List.ofFn fun v : Fin 13 => decide (v = l)
def quadInput (Q : Finset (Fin 13)) := (List.ofFn fun v : Fin 13 => decide (v ∈ Q)) ++
    List.ofFn fun l : Fin 13 => decide (∀ p ∈ Q, p-l ∉ D)
def quadOK (Q : Finset (Fin 13)) : Prop := Q.card = 4 ∧
    ∀ l : Fin 13, (Q.filter fun p => p-l ∈ D).card ≤ 2
def flag (x : List Bool) : Prop := ∃ p l : Fin 13, p-l ∈ D ∧ x = flagInput p l
def quad (x : List Bool) : Prop := ∃ Q, quadOK Q ∧ x = quadInput Q

theorem planeSplit {C : Circuit} (m : Monotone2 C) (rb : ReadsBack 26 C)
    (pos : ∀ p l : Fin 13, p-l ∈ D → C.eval (flagInput p l) = true)
    (neg : ∀ Q, quadOK Q → C.eval (quadInput Q) = false)
    (least : ¬ Shorter 26 flag quad C) {j a b : ℕ} (realJ : j < C.gates.length)
    (op : (gateAt C j).op = GateOp.and) (ins : (gateAt C j).inputs = [a,b]) :
    ∃ Q R, quadOK Q ∧ quadOK R ∧ Q ≠ R ∧
      val C (quadInput Q) a = true ∧ val C (quadInput Q) b = false ∧
      val C (quadInput R) a = false ∧ val C (quadInput R) b = true ∧
      (bypass 26 C j a).eval (quadInput Q) = true ∧ (bypass 26 C j b).eval (quadInput R) = true := by
  have correct : Fits flag quad C := by
    constructor
    · rintro _ ⟨p,l,hit,rfl⟩; exact pos p l hit
    · rintro _ ⟨Q,good,rfl⟩; exact neg Q good
  have fp : ∀ x, flag x → x.length = 26 := by rintro _ ⟨p,l,_,rfl⟩; simp [flagInput]
  have qp : ∀ x, quad x → x.length = 26 := by rintro _ ⟨Q,_,rfl⟩; simp [quadInput]
  obtain ⟨x,y,⟨Q,q,rfl⟩,⟨R,r,rfl⟩,ne,rest⟩ := andSplit m rb correct fp qp least realJ op ins
  exact ⟨Q,R,q,r,fun e => ne (congrArg quadInput e),rest⟩


abbrev Flags3 := Fin 3 → Fin 13 × Fin 13
abbrev RawClause := Fin 13 → Bool × Bool
def acceptsFlag (A : RawClause) (e : Fin 13 × Fin 13) : Prop := (A e.1).1 = true ∨ (A e.2).2 = true
def acceptsQuad (A : RawClause) (Q : Finset (Fin 13)) : Prop :=
  (∃ p ∈ Q, (A p).1 = true) ∨ ∃ l : Fin 13, (A l).2 = true ∧ ∀ p ∈ Q, p-l ∉ D

def pickLine (k : Fin 8) (i : Fin 3) : Bool := k.val.testBit i.val

def rowHit (F : Flags3) (k : Fin 8) (Q : Finset (Fin 13)) : Prop :=
  ∃ i : Fin 3, if pickLine k i then ∀ p ∈ Q, p-(F i).2 ∉ D else (F i).1 ∈ Q
instance (F : Flags3) (k : Fin 8) (Q : Finset (Fin 13)) : Decidable (rowHit F k Q) := by unfold rowHit; infer_instance

def selects (A : RawClause) (F : Flags3) (k : Fin 8) : Prop :=
  ∀ i, if pickLine k i then (A (F i).2).2 = true else (A (F i).1).1 = true

theorem signCode (v : Fin 3 → Bool) : ∃ k : Fin 8, ∀ i, pickLine k i = v i := by
  have key : ∀ x y z : Bool, ∃ k : Fin 8, pickLine k 0 = x ∧ pickLine k 1 = y ∧ pickLine k 2 = z := by decide +kernel
  obtain ⟨k,a,b,c⟩ := key (v 0) (v 1) (v 2)
  exact ⟨k,fun i => by fin_cases i <;> assumption⟩

theorem selectClause (A : RawClause) (F : Flags3) (accepts : ∀ i, acceptsFlag A (F i)) :
    ∃ k, selects A F k := by
  obtain ⟨k,eq⟩ := signCode fun i => !(A (F i).1).1
  refine ⟨k,fun i => ?_⟩
  rw [eq i]
  have h := accepts i
  unfold acceptsFlag at h
  cases v : (A (F i).1).1 <;> simp_all

theorem hitClause {A : RawClause} {F : Flags3} {k : Fin 8} (sel : selects A F k)
    {Q : Finset (Fin 13)} (row : rowHit F k Q) : acceptsQuad A Q := by
  obtain ⟨i,good⟩ := row
  have h := sel i
  cases eq : pickLine k i <;> simp [eq] at h good
  · exact Or.inl ⟨_,good,h⟩
  · exact Or.inr ⟨_,h,by simpa using good⟩

def certified (F : Flags3) (bank : List (Finset (Fin 13))) : Prop :=
  (∀ Q ∈ bank, quadOK Q) ∧
  ∀ a b c : Fin 8, ∃ Q ∈ bank, rowHit F a Q ∧ rowHit F b Q ∧ rowHit F c Q

instance (Q : Finset (Fin 13)) : Decidable (quadOK Q) := by unfold quadOK; infer_instance
instance (F : Flags3) (bank : List (Finset (Fin 13))) : Decidable (certified F bank) := by unfold certified; infer_instance

theorem matchingObstruction (F : Flags3) (bank : List (Finset (Fin 13))) (cert : certified F bank)
    (A B C : RawClause) (each : ∀ i, acceptsFlag A (F i) ∧ acceptsFlag B (F i) ∧ acceptsFlag C (F i)) :
    ∃ Q, quadOK Q ∧ acceptsQuad A Q ∧ acceptsQuad B Q ∧ acceptsQuad C Q := by
  obtain ⟨a,sa⟩ := selectClause A F (fun i => (each i).1)
  obtain ⟨b,sb⟩ := selectClause B F (fun i => (each i).2.1)
  obtain ⟨c,sc⟩ := selectClause C F (fun i => (each i).2.2)
  obtain ⟨Q,mem,ra,rb,rc⟩ := cert.2 a b c
  exact ⟨Q,cert.1 Q mem,hitClause sa ra,hitClause sb rb,hitClause sc rc⟩

/-- The two centers, the points on the line, and the lines through the point
give three raw OR clauses realizing the whole incident double star. -/
def corner (p l : Fin 13) : RawClause := fun i => (decide (i = p), decide (i = l))
def pointsOn (l : Fin 13) : RawClause := fun i => (decide (i-l ∈ D),false)
def linesThrough (p : Fin 13) : RawClause := fun i => (false,decide (p-i ∈ D))

theorem doubleStarFlag (p l u v : Fin 13) (centers : p-l ∈ D) (flagged : u-v ∈ D) :
    (acceptsFlag (corner p l) (u,v) ∧ acceptsFlag (pointsOn l) (u,v) ∧
     acceptsFlag (linesThrough p) (u,v)) ↔ u = p ∨ v = l := by
  simp only [acceptsFlag,corner,pointsOn,linesThrough,decide_eq_true_eq,Bool.false_eq_true,
    or_false,false_or]
  exact ⟨And.left, fun h => ⟨h,by rcases h with rfl | rfl <;> exact ⟨by assumption,by assumption⟩⟩⟩

theorem doubleStarReject (p l : Fin 13) (Q : Finset (Fin 13)) :
    ¬ (acceptsQuad (corner p l) Q ∧ acceptsQuad (pointsOn l) Q ∧ acceptsQuad (linesThrough p) Q) := by
  rintro ⟨center,point,line⟩
  have lineW : ∃ k : Fin 13, p-k ∈ D ∧ ∀ x ∈ Q, x-k ∉ D := by
    rcases line with ⟨x,_,no⟩ | ⟨k,hk,hn⟩
    · contradiction
    · exact ⟨k,of_decide_eq_true hk,hn⟩
  have pointW : ∃ x ∈ Q, x-l ∈ D := by
    rcases point with ⟨x,hx,yes⟩ | ⟨_,no,_⟩
    · exact ⟨x,hx,of_decide_eq_true yes⟩
    · contradiction
  rcases center with ⟨x,xQ,eq⟩ | ⟨k,eq,kQ⟩
  · have xp : x = p := of_decide_eq_true eq
    subst x
    obtain ⟨v,pv,none⟩ := lineW
    exact none p xQ pv
  · have kl : k = l := of_decide_eq_true eq
    subst k
    obtain ⟨x,mem,xl⟩ := pointW
    exact kQ x mem xl

-- Projective-plane witness quadrangles and their finite checks are from L-meta-1751.
def TQ (Q : Finset (Fin 13)) : Finset (Fin 13) :=
  Finset.univ.filter (fun v : Fin 13 => ∀ r ∈ Q, r - v ∉ ({0, 1, 3, 9} : Finset (Fin 13)))

def Q0 (d : Fin 13) : Finset (Fin 13) :=
  if d = 4 ∨ d = 5 ∨ d = 6 then {2, 4, 5, 6} else if d = 7 ∨ d = 8 then {2, 4, 7, 8} else {2, 10, 11, 12}

def Qf (p l : Fin 13) : Finset (Fin 13) := (Q0 (p - l)).image (fun q => q + l)

theorem geo_quad : ∀ p l : Fin 13, p - l ∉ ({0, 1, 3, 9} : Finset (Fin 13)) →
    (Qf p l).card = 4 ∧
    (∀ k : Fin 13, ((Qf p l).filter (fun u0 : Fin 13 => u0 - k ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2) ∧
    p ∈ Qf p l ∧ l ∈ TQ (Qf p l) := by
  decide +kernel

def Q1 (d : Fin 13) : Finset (Fin 13) :=
  if d = 3 then {0, 2, 3, 4} else if d = 4 then {0, 1, 4, 6} else if d = 6 then {0, 1, 2, 6}
  else if d = 7 then {0, 1, 2, 7} else if d = 8 then {0, 1, 4, 8} else if d = 9 then {0, 2, 4, 9}
  else if d = 10 then {0, 1, 5, 10} else if d = 11 then {0, 1, 2, 11}
  else if d = 12 then {0, 1, 4, 12} else {0, 1, 2, 5}

def QP (p p' : Fin 13) : Finset (Fin 13) := (Q1 (p' - p)).image (fun q => q + p)

def Q2 (d : Fin 13) : Finset (Fin 13) :=
  if d = 1 then {5, 6, 7, 11} else if d = 2 then {4, 6, 7, 8} else if d = 3 then {2, 5, 7, 8}
  else if d = 4 then {2, 6, 8, 10} else if d = 5 then {2, 4, 7, 11} else if d = 6 then {4, 5, 8, 10}
  else if d = 8 then {2, 5, 6, 10} else if d = 9 then {2, 4, 6, 8} else if d = 10 then {2, 4, 5, 8}
  else if d = 12 then {4, 5, 6, 10} else {2, 4, 5, 6}

def QL (l l' : Fin 13) : Finset (Fin 13) := (Q2 (l' - l)).image (fun q => q + l)

theorem geoPP : ∀ p p' : Fin 13,
    (QP p p').card = 4 ∧
    (∀ k : Fin 13, ((QP p p').filter (fun u0 : Fin 13 => u0 - k ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2) ∧
    p ∈ QP p p' ∧ p' ∈ QP p p' := by
  decide +kernel

theorem geoLL : ∀ l l' : Fin 13,
    (QL l l').card = 4 ∧
    (∀ k : Fin 13, ((QL l l').filter (fun u0 : Fin 13 => u0 - k ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2) ∧
    l ∈ TQ (QL l l') ∧ l' ∈ TQ (QL l l') := by
  decide +kernel


def exposed (e : Fin 13 × Fin 13) (b : Bool) (Q : Finset (Fin 13)) : Prop :=
  if b then ∀ x ∈ Q, x-e.2 ∉ D else e.1 ∈ Q

theorem exposeBoth (e f : Fin 13 × Fin 13) (left : e.1-f.2 ∉ D) (right : f.1-e.2 ∉ D)
    (b c : Bool) : ∃ Q, quadOK Q ∧ exposed e b Q ∧ exposed f c Q := by
  cases b <;> cases c
  · obtain ⟨sz,good,h,k⟩ := geoPP e.1 f.1
    exact ⟨_,⟨sz,good⟩,h,k⟩
  · obtain ⟨sz,good,h,k⟩ := geo_quad e.1 f.2 left
    exact ⟨_,⟨sz,good⟩,h,(Finset.mem_filter.mp k).2⟩
  · obtain ⟨sz,good,h,k⟩ := geo_quad f.1 e.2 right
    exact ⟨_,⟨sz,good⟩,(Finset.mem_filter.mp k).2,h⟩
  · obtain ⟨sz,good,h,k⟩ := geoLL e.2 f.2
    exact ⟨_,⟨sz,good⟩,(Finset.mem_filter.mp h).2,(Finset.mem_filter.mp k).2⟩

def pick (A : RawClause) (e : Fin 13 × Fin 13) : Bool := !(A e.1).1

theorem exposedOn (A : RawClause) (e : Fin 13 × Fin 13) (flag : acceptsFlag A e)
    (Q : Finset (Fin 13)) (showed : exposed e (pick A e) Q) : acceptsQuad A Q := by
  cases h : (A e.1).1
  · have line : (A e.2).2 = true := flag.resolve_left (by simp [h])
    exact Or.inr ⟨_,line,by simpa only [exposed,pick,h,Bool.not_false,ite_true] using showed⟩
  · exact Or.inl ⟨_,by simpa only [exposed,pick,h,Bool.not_true,Bool.false_eq_true,ite_false] using showed,h⟩

/-- The two flags of an induced matching cannot both be accepted by a clean
three-clause term. Four orientations are available and three clauses can each
rule out at most one of them. -/
theorem noncrossingPair (e f : Fin 13 × Fin 13) (left : e.1-f.2 ∉ D) (right : f.1-e.2 ∉ D)
    (A B C : RawClause) (he : acceptsFlag A e ∧ acceptsFlag B e ∧ acceptsFlag C e)
    (hf : acceptsFlag A f ∧ acceptsFlag B f ∧ acceptsFlag C f) :
    ∃ Q, quadOK Q ∧ acceptsQuad A Q ∧ acceptsQuad B Q ∧ acceptsQuad C Q := by
  have choose : ∀ a b c d i j : Bool, ∃ v w : Bool,
      (v = a ∨ w = b) ∧ (v = c ∨ w = d) ∧ (v = i ∨ w = j) := by decide +kernel
  obtain ⟨v,w,va,vb,vc⟩ := choose (pick A e) (pick A f) (pick B e) (pick B f) (pick C e) (pick C f)
  obtain ⟨Q,good,ev,fw⟩ := exposeBoth e f left right v w
  have hit (X : RawClause) (onE : acceptsFlag X e) (onF : acceptsFlag X f)
      (covers : v = pick X e ∨ w = pick X f) : acceptsQuad X Q := by
    rcases covers with eq | eq
    · exact exposedOn X e onE Q (eq ▸ ev)
    · exact exposedOn X f onF Q (eq ▸ fw)
  exact ⟨Q,good,hit A he.1 hf.1 va,hit B he.2.1 hf.2.1 vb,hit C he.2.2 hf.2.2 vc⟩

def frame0 : Flags3 := ![(0, 0), (1, 1), (2, 2)]
def frame0Bank : List (Finset (Fin 13)) := [{0, 1, 2, 5}, {0, 1, 4, 6}, {0, 6, 7, 8}, {2, 4, 5, 6}]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 1500000 in
theorem frame0Checked : certified frame0 frame0Bank := by decide +kernel

def frame1 : Flags3 := ![(0, 0), (1, 1), (2, 12)]
def frame1Bank : List (Finset (Fin 13)) := [{0, 1, 2, 5}, {5, 6, 7, 11}, {0, 3, 5, 6}, {1, 3, 4, 5}]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 1500000 in
theorem frame1Checked : certified frame1 frame1Bank := by decide +kernel

def frame2 : Flags3 := ![(0, 0), (1, 1), (3, 2)]
def frame2Bank : List (Finset (Fin 13)) := [{0, 1, 4, 6}, {0, 3, 5, 6}, {0, 6, 7, 8}, {1, 2, 3, 6}]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 1500000 in
theorem frame2Checked : certified frame2 frame2Bank := by decide +kernel

def frame3 : Flags3 := ![(0, 0), (1, 1), (5, 2)]
def frame3Bank : List (Finset (Fin 13)) := [{0, 1, 2, 5}, {0, 1, 4, 6}, {0, 3, 5, 6}, {0, 6, 7, 8}]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 1500000 in
theorem frame3Checked : certified frame3 frame3Bank := by decide +kernel

def frame4 : Flags3 := ![(0, 0), (1, 1), (5, 5)]
def frame4Bank : List (Finset (Fin 13)) := [{0, 1, 2, 5}, {0, 3, 5, 6}, {0, 3, 7, 11}, {2, 4, 5, 6}]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 1500000 in
theorem frame4Checked : certified frame4 frame4Bank := by decide +kernel

def frame5 : Flags3 := ![(0, 0), (2, 1), (5, 5)]
def frame5Bank : List (Finset (Fin 13)) := [{0, 1, 2, 5}, {0, 2, 3, 4}, {0, 3, 5, 6}, {0, 3, 7, 11}]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 1500000 in
theorem frame5Checked : certified frame5 frame5Bank := by decide +kernel

def frame6 : Flags3 := ![(0, 0), (2, 1), (5, 9)]
def frame6Bank : List (Finset (Fin 13)) := [{0, 1, 2, 5}, {0, 1, 2, 6}, {0, 3, 5, 6}, {0, 3, 6, 7}]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 1500000 in
theorem frame6Checked : certified frame6 frame6Bank := by decide +kernel

def frame7 : Flags3 := ![(0, 0), (2, 1), (8, 5)]
def frame7Bank : List (Finset (Fin 13)) := [{0, 2, 3, 4}, {0, 3, 5, 8}, {0, 3, 7, 11}, {1, 2, 3, 8}]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 1500000 in
theorem frame7Checked : certified frame7 frame7Bank := by decide +kernel

def frame8 : Flags3 := ![(0, 0), (2, 1), (8, 7)]
def frame8Bank : List (Finset (Fin 13)) := [{0, 1, 2, 5}, {0, 3, 5, 8}, {0, 5, 6, 9}, {1, 2, 3, 8}]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 1500000 in
theorem frame8Checked : certified frame8 frame8Bank := by decide +kernel

end QuadSeparation
