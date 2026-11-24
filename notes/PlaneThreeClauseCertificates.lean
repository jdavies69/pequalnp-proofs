import Mathlib
import PEqualNP.Outside.L_meta_1485
import PEqualNP.Outside.L_meta_1490

/-!
On the incidence and quadrangle inputs, a least candidate must distinguish
the two operands of each AND in both directions. Replacing the gate by either
operand must actually turn the output on for a rejected quadrangle.
The circuit deletion and monotonicity lemmas are from L-meta-1485. The explicit
point-pair, line-pair and nonincident-point-line quadrangles come from L-meta-1751.
The theorem doubleStarClassification characterizes all flag families that can
be accepted simultaneously by three raw OR clauses while rejecting the 234
quadrangles. The sharp upper bound is seven flags. This is the geometric part
of the single-nested-AND circuit problem. The circuit results below use the
OR-path reconstruction from L-meta-1490. The final theorem deskGateCounts
takes the L-meta-1961 circuit hypotheses verbatim and bounds its AND gates.
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


set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem fourRows (F : Flags3) (i j : Fin 3) (qp ql qr qs : Finset (Fin 13))
    (good : quadOK qp ∧ quadOK ql ∧ quadOK qr ∧ quadOK qs)
    (everyP : ∀ v, (F v).1 ∈ qp) (everyL : ∀ v, ∀ x ∈ ql, x-(F v).2 ∉ D)
    (mixP : (F 0).1 ∈ qr ∧ ∀ x ∈ qr, x-(F i).2 ∉ D)
    (mixL : (∀ x ∈ qs, x-(F 0).2 ∉ D) ∧ (F j).1 ∈ qs)
    (A B C : RawClause) (covers : ∀ v, acceptsFlag A (F v) ∧ acceptsFlag B (F v) ∧ acceptsFlag C (F v)) :
    ∃ Q, quadOK Q ∧ acceptsQuad A Q ∧ acceptsQuad B Q ∧ acceptsQuad C Q := by
  obtain ⟨a,sa⟩ := selectClause A F (fun v => (covers v).1)
  obtain ⟨b,sb⟩ := selectClause B F (fun v => (covers v).2.1)
  obtain ⟨c,sc⟩ := selectClause C F (fun v => (covers v).2.2)
  have registry : ∀ a b c : Fin 8, ∀ i j : Fin 3,
      (∀ k ∈ [a,b,c], ∃ v : Fin 3, pickLine k v = false) ∨
      (∀ k ∈ [a,b,c], ∃ v : Fin 3, pickLine k v = true) ∨
      (∀ k ∈ [a,b,c], pickLine k 0 = false ∨ pickLine k i = true) ∨
      (∀ k ∈ [a,b,c], pickLine k 0 = true ∨ pickLine k j = false) := by decide +kernel
  have finish (Q) (ok : quadOK Q) (hits : ∀ k ∈ [a,b,c], rowHit F k Q) :
      ∃ R, quadOK R ∧ acceptsQuad A R ∧ acceptsQuad B R ∧ acceptsQuad C R :=
    ⟨Q,ok,hitClause sa (hits a (by simp)),hitClause sb (hits b (by simp)),hitClause sc (hits c (by simp))⟩
  rcases registry a b c i j with allP | allL | first | second
  · apply finish qp good.1
    intro k mem
    obtain ⟨v,sel⟩ := allP k mem
    exact ⟨v,by simp only [sel,Bool.false_eq_true,ite_false]; exact everyP v⟩
  · apply finish ql good.2.1
    intro k mem
    obtain ⟨v,sel⟩ := allL k mem
    exact ⟨v,by simp only [sel,ite_true]; exact everyL v⟩
  · apply finish qr good.2.2.1
    intro k mem
    rcases first k mem with h | h
    · exact ⟨0,by simp only [h,Bool.false_eq_true,ite_false]; exact mixP.1⟩
    · exact ⟨i,by simp only [h,ite_true]; exact mixP.2⟩
  · apply finish qs good.2.2.2
    intro k mem
    rcases second k mem with h | h
    · exact ⟨0,by simp only [h,ite_true]; exact mixL.1⟩
    · exact ⟨j,by simp only [h,Bool.false_eq_true,ite_false]; exact mixL.2⟩

def colP (x y z : Fin 13) : Prop := ∃ k : Fin 13, x-k ∈ D ∧ y-k ∈ D ∧ z-k ∈ D
def colL (x y z : Fin 13) : Prop := ∃ k : Fin 13, k-x ∈ D ∧ k-y ∈ D ∧ k-z ∈ D
instance (a b c : Fin 13) : Decidable (colP a b c) := by unfold colP; infer_instance
instance (a b c : Fin 13) : Decidable (colL a b c) := by unfold colL; infer_instance

def fourth : Fin 13 → Fin 13 → Fin 13 := ![
  ![1, 2, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1],
  ![2, 2, 5, 0, 6, 2, 2, 2, 4, 0, 5, 2, 4],
  ![1, 5, 1, 4, 3, 1, 1, 1, 0, 4, 3, 1, 0],
  ![2, 0, 4, 2, 2, 6, 2, 2, 4, 0, 2, 4, 5],
  ![1, 6, 3, 2, 1, 0, 1, 0, 1, 2, 3, 1, 1],
  ![1, 2, 1, 6, 0, 1, 2, 0, 3, 2, 1, 1, 1],
  ![1, 2, 1, 2, 1, 2, 1, 1, 3, 4, 0, 0, 1],
  ![1, 2, 1, 2, 0, 0, 1, 1, 1, 8, 1, 2, 3],
  ![1, 4, 0, 4, 1, 3, 3, 1, 1, 5, 1, 1, 0],
  ![2, 0, 4, 0, 2, 2, 4, 8, 5, 2, 2, 2, 4],
  ![1, 5, 3, 2, 3, 1, 0, 1, 1, 2, 1, 0, 1],
  ![1, 2, 1, 4, 1, 1, 0, 2, 1, 2, 0, 1, 3],
  ![1, 4, 0, 5, 1, 1, 1, 3, 0, 4, 1, 3, 1]]

def lineAvoid (q r : Fin 13) : Finset (Fin 13) :=
  Finset.univ.filter fun x => x ∉ D ∧ x-q ∉ D ∧ x-r ∉ D

set_option maxRecDepth 12000 in
theorem pTable : ∀ q r : Fin 13, ¬colP 0 q r → quadOK {0,q,r,fourth q r} := by decide +kernel

set_option maxRecDepth 12000 in
theorem lTable : ∀ q r : Fin 13, ¬colL 0 q r → quadOK (lineAvoid q r) := by decide +kernel

def shift (t : Fin 13) (Q : Finset (Fin 13)) := Q.map (Equiv.addRight t).toEmbedding

theorem shifted {t x : Fin 13} {Q : Finset (Fin 13)} : x ∈ shift t Q ↔ x-t ∈ Q := by
  constructor
  · rintro h
    obtain ⟨v,hv,e⟩ := Finset.mem_map.mp h
    change v + t = x at e
    simpa [←e] using hv
  · intro h
    exact Finset.mem_map.mpr ⟨x-t,h,by change x-t+t=x; abel⟩

theorem quadShift {t : Fin 13} {Q : Finset (Fin 13)} (good : quadOK Q) : quadOK (shift t Q) := by
  refine ⟨by simpa [shift] using good.1,fun k => ?_⟩
  have eq : ((shift t Q).filter fun p => p-k ∈ D) = shift t (Q.filter fun p => p-(k-t) ∈ D) := by
    ext p; simp only [Finset.mem_filter,shifted]; rw [show p-t-(k-t)=p-k by abel]
  rw [eq,shift,Finset.card_map]; exact good.2 (k-t)

theorem threePoints (p q r : Fin 13) (notcol : ¬colP p q r) :
    ∃ Q, quadOK Q ∧ p ∈ Q ∧ q ∈ Q ∧ r ∈ Q := by
  have norm : ¬colP 0 (q-p) (r-p) := by
    rintro ⟨k,a,b,c⟩
    exact notcol ⟨k+p,by rwa [show p-(k+p)=0-k by abel],by rwa [show q-(k+p)=q-p-k by abel],
      by rwa [show r-(k+p)=r-p-k by abel]⟩
  have good := pTable _ _ norm
  exact ⟨_,quadShift (t:=p) good,shifted.mpr (by simp),shifted.mpr (by simp),shifted.mpr (by simp)⟩

theorem threeLines (p q r : Fin 13) (notcol : ¬colL p q r) :
    ∃ Q, quadOK Q ∧ ∀ x ∈ Q, x-p ∉ D ∧ x-q ∉ D ∧ x-r ∉ D := by
  have norm : ¬colL 0 (q-p) (r-p) := by
    rintro ⟨k,a,b,c⟩
    exact notcol ⟨k+p,by rwa [show k+p-p=k-0 by abel],by rwa [show k+p-q=k-(q-p) by abel],
      by rwa [show k+p-r=k-(r-p) by abel]⟩
  refine ⟨_,quadShift (t:=p) (lTable _ _ norm),?_⟩
  intro x hx
  have h := (Finset.mem_filter.mp (shifted.mp hx)).2
  change x-p ∉ D ∧ x-p-(q-p) ∉ D ∧ x-p-(r-p) ∉ D at h
  rwa [show x-p-(q-p)=x-q by abel,show x-p-(r-p)=x-r by abel] at h

abbrev incidence (p l : Fin 13) : Prop := p-l ∈ D
set_option maxRecDepth 16000 in
set_option maxHeartbeats 3000000 in
theorem uniqueLine : ∀ p q l m : Fin 13, p ≠ q → incidence p l → incidence p m →
    incidence q l → incidence q m → l = m := by decide +kernel

theorem triangleBad (A B C : RawClause) (p q r l m n : Fin 13)
    (pl : incidence p l) (qm : incidence q m) (rn : incidence r n)
    (pm : incidence p m) (_qn : incidence q n) (rl : incidence r l)
    (pn : ¬ incidence p n) (ql : ¬ incidence q l) (rm : ¬ incidence r m)
    (on : ∀ e ∈ [(p,l),(q,m),(r,n)], acceptsFlag A e ∧ acceptsFlag B e ∧ acceptsFlag C e) :
    ∃ Q, quadOK Q ∧ acceptsQuad A Q ∧ acceptsQuad B Q ∧ acceptsQuad C Q := by
  have pr : p ≠ r := by rintro rfl; contradiction
  have lm : l ≠ m := by rintro rfl; contradiction
  have cP : ¬colP p q r := by
    rintro ⟨k,pk,qk,rk⟩
    have e := uniqueLine p r k l pr pk pl rk rl
    exact ql (e ▸ qk)
  have cL : ¬colL l m n := by
    rintro ⟨x,xl,xm,xn⟩
    by_cases e : x = p
    · exact pn (e ▸ xn)
    · exact lm (uniqueLine x p l m e xl xm pl pm)
  obtain ⟨P,hP,pP,qP,rP⟩ := threePoints p q r cP
  obtain ⟨L,hL,miss⟩ := threeLines l m n cL
  obtain ⟨szS,goodS,pS,nS⟩ := geo_quad _ _ pn
  obtain ⟨szT,goodT,qT,lT⟩ := geo_quad _ _ ql
  let F : Flags3 := ![(p,l),(q,m),(r,n)]
  apply fourRows F 2 1 P L (Qf p n) (Qf q l) ⟨hP,hL,⟨szS,goodS⟩,⟨szT,goodT⟩⟩
    (fun v => by fin_cases v <;> first | exact pP | exact qP | exact rP)
    (fun v x hx => by fin_cases v <;> first | exact (miss x hx).1 | exact (miss x hx).2.1 | exact (miss x hx).2.2)
    ⟨pS,(Finset.mem_filter.mp nS).2⟩ ⟨(Finset.mem_filter.mp lT).2,qT⟩ A B C
  intro v
  apply on
  fin_cases v <;> simp [F]



def covered (A B C : RawClause) (p l : Fin 13) : Prop :=
  incidence p l ∧ acceptsFlag A (p,l) ∧ acceptsFlag B (p,l) ∧ acceptsFlag C (p,l)

def cleanTerm (A B C : RawClause) : Prop :=
  ∀ Q, quadOK Q → ¬ (acceptsQuad A Q ∧ acceptsQuad B Q ∧ acceptsQuad C Q)

theorem cross (A B C : RawClause) (clean : cleanTerm A B C) {p l q m : Fin 13}
    (e : covered A B C p l) (f : covered A B C q m) : incidence p m ∨ incidence q l := by
  by_contra! no
  obtain ⟨Q,good,accept⟩ := noncrossingPair (p,l) (q,m) no.1 no.2 A B C e.2 f.2
  exact clean Q good accept

theorem forcedCenter (A B C : RawClause) (clean : cleanTerm A B C)
    {p l q m : Fin 13} (pq : p ≠ q) (lm : l ≠ m) (pm : incidence p m)
    (e : covered A B C p l) (f : covered A B C q m) :
    ∀ r n, covered A B C r n → r = p ∨ n = m := by
  intro r n g
  by_contra! off
  have pr := Ne.symm off.1
  have mn := Ne.symm off.2
  have ql : ¬incidence q l := fun h => lm (uniqueLine p q l m pq e.1 pm h f.1)
  have pn : ¬incidence p n := by
    intro h
    rcases cross A B C clean f g with qn | rm
    · exact mn (uniqueLine p q m n pq pm h f.1 qn)
    · exact mn (uniqueLine p r m n pr pm h rm g.1)
  have rl := (cross A B C clean e g).resolve_left pn
  have rm : ¬incidence r m := fun h => lm (uniqueLine p r l m pr e.1 pm rl h)
  have qn := (cross A B C clean f g).resolve_right rm
  obtain ⟨Q,good,accept⟩ := triangleBad A B C p q r l m n e.1 f.1 g.1 pm qn rl pn ql rm (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl
    · exact e.2
    · exact f.2
    · exact g.2)
  exact clean Q good accept

/-- Every incident input accepted by three raw OR clauses lies in one incident
double star if the conjunction rejects all legal quadrangles. -/
theorem containedCorner (A B C : RawClause) (clean : cleanTerm A B C) :
    ∃ p l : Fin 13, incidence p l ∧ ∀ u v, covered A B C u v → u = p ∨ v = l := by
  classical
  by_cases two : ∃ p l q m, covered A B C p l ∧ covered A B C q m ∧ p ≠ q ∧ l ≠ m
  · obtain ⟨p,l,q,m,e,f,pq,lm⟩ := two
    rcases cross A B C clean e f with pm | ql
    · exact ⟨p,m,pm,forcedCenter A B C clean pq lm pm e f⟩
    · exact ⟨q,l,ql,forcedCenter A B C clean pq.symm lm.symm ql f e⟩
  · by_cases hit : ∃ p l, covered A B C p l
    · obtain ⟨p,l,e⟩ := hit
      refine ⟨p,l,e.1,?_⟩
      intro q m f
      by_contra! off
      exact two ⟨p,l,q,m,e,f,off.1.symm,off.2.symm⟩
    · exact ⟨0,0,by decide,fun u v h => False.elim (hit ⟨u,v,h⟩)⟩


def doubleStar (p l : Fin 13) : Finset (Fin 13 × Fin 13) :=
  Finset.univ.filter fun e => incidence e.1 e.2 ∧ (e.1 = p ∨ e.2 = l)

instance (A B C : RawClause) (p l : Fin 13) : Decidable (covered A B C p l) := by
  unfold covered acceptsFlag; infer_instance

def positiveFlags (A B C : RawClause) : Finset (Fin 13 × Fin 13) :=
  Finset.univ.filter fun e => covered A B C e.1 e.2

set_option maxRecDepth 12000 in
theorem doubleStarSize : ∀ p l : Fin 13, incidence p l → (doubleStar p l).card = 7 := by decide +kernel

/-- A flag family can be simultaneously accepted by a clean three-clause term
exactly when it is a subset of one of the 52 incident double stars. -/
theorem doubleStarClassification (S : Finset (Fin 13 × Fin 13)) :
    (∃ A B C : RawClause, cleanTerm A B C ∧ S ⊆ positiveFlags A B C) ↔
    ∃ p l : Fin 13, incidence p l ∧ S ⊆ doubleStar p l := by
  constructor
  · rintro ⟨A,B,C,clean,sub⟩
    obtain ⟨p,l,inc,contain⟩ := containedCorner A B C clean
    refine ⟨p,l,inc,?_⟩
    intro e em
    have cov := (Finset.mem_filter.mp (sub em)).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,cov.1,contain e.1 e.2 cov⟩
  · rintro ⟨p,l,inc,sub⟩
    refine ⟨corner p l,pointsOn l,linesThrough p,fun Q _ => doubleStarReject p l Q,?_⟩
    intro e em
    obtain ⟨flag,side⟩ := (Finset.mem_filter.mp (sub em)).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,flag,(doubleStarFlag p l e.1 e.2 inc flag).mpr side⟩

theorem atMostSeven (A B C : RawClause) (clean : cleanTerm A B C) :
    (positiveFlags A B C).card ≤ 7 := by
  obtain ⟨p,l,inc,cover⟩ := (doubleStarClassification _).mp ⟨A,B,C,clean,Finset.Subset.rfl⟩
  exact (Finset.card_le_card cover).trans_eq (doubleStarSize p l inc)

theorem sevenAttained : ∃ A B C : RawClause, cleanTerm A B C ∧ (positiveFlags A B C).card = 7 := by
  have inc : incidence 0 0 := by decide
  obtain ⟨A,B,C,clean,cover⟩ := (doubleStarClassification (doubleStar 0 0)).mpr ⟨0,0,inc,Finset.Subset.rfl⟩
  have hi := atMostSeven A B C clean
  have lo := Finset.card_le_card cover
  rw [doubleStarSize 0 0 inc] at lo
  exact ⟨A,B,C,clean,by omega⟩

end QuadSeparation
namespace QuadSeparation

def cleanTwo (A B : RawClause) : Prop := ∀ Q, quadOK Q → ¬(acceptsQuad A Q ∧ acceptsQuad B Q)

theorem mixedPairBad (A B : RawClause) (e f : Fin 13 × Fin 13) (noncross : e.1-f.2 ∉ D)
    (ae : acceptsFlag A e) (af : acceptsFlag A f) (be : acceptsFlag B e) (bf : acceptsFlag B f) :
    ∃ Q, quadOK Q ∧ acceptsQuad A Q ∧ acceptsQuad B Q := by
  obtain ⟨ps,pg,pe,pf⟩ := geoPP e.1 f.1
  obtain ⟨ls,lg,le,lf⟩ := geoLL e.2 f.2
  obtain ⟨ms,mg,me,mf⟩ := geo_quad _ _ noncross
  let P := QP e.1 f.1
  let L := QL e.2 f.2
  let M := Qf e.1 f.2
  have hit (X : RawClause) (he : acceptsFlag X e) (hf : acceptsFlag X f) :
      ((acceptsQuad X P ∧ acceptsQuad X L) ∨ (acceptsQuad X P ∧ acceptsQuad X M) ∨
       (acceptsQuad X L ∧ acceptsQuad X M)) := by
    rcases he with ep | el <;> rcases hf with fp | fl
    · exact Or.inr (Or.inl ⟨Or.inl ⟨_,pe,ep⟩,Or.inl ⟨_,me,ep⟩⟩)
    · exact Or.inl ⟨Or.inl ⟨_,pe,ep⟩,Or.inr ⟨_,fl,(Finset.mem_filter.mp lf).2⟩⟩
    · exact Or.inl ⟨Or.inl ⟨_,pf,fp⟩,Or.inr ⟨_,el,(Finset.mem_filter.mp le).2⟩⟩
    · exact Or.inr (Or.inr ⟨Or.inr ⟨_,el,(Finset.mem_filter.mp le).2⟩,Or.inr ⟨_,fl,(Finset.mem_filter.mp mf).2⟩⟩)
  have ha := hit A ae af
  have hb := hit B be bf
  have existsCommon : (acceptsQuad A P ∧ acceptsQuad B P) ∨
       (acceptsQuad A L ∧ acceptsQuad B L) ∨ (acceptsQuad A M ∧ acceptsQuad B M) := by
    rcases ha with ⟨pa,la⟩ | ⟨pa,ma⟩ | ⟨la,ma⟩ <;>
      rcases hb with ⟨pb,lb⟩ | ⟨pb,mb⟩ | ⟨lb,mb⟩ <;>
      first | exact Or.inl ⟨pa,pb⟩ | exact Or.inr (Or.inl ⟨la,lb⟩) | exact Or.inr (Or.inr ⟨ma,mb⟩)
  rcases existsCommon with hp | hl | hm
  · exact ⟨P,⟨ps,pg⟩,hp⟩
  · exact ⟨L,⟨ls,lg⟩,hl⟩
  · exact ⟨M,⟨ms,mg⟩,hm⟩

def flagsTwo (A B : RawClause) : Finset (Fin 13 × Fin 13) :=
  Finset.univ.filter fun e => incidence e.1 e.2 ∧
      ((A e.1).1 = true ∨ (A e.2).2 = true) ∧ ((B e.1).1 = true ∨ (B e.2).2 = true)

theorem shareCenter (A B : RawClause) (clean : cleanTwo A B) {e f : Fin 13 × Fin 13}
    (he : e ∈ flagsTwo A B) (hf : f ∈ flagsTwo A B) : e.1 = f.1 ∨ e.2 = f.2 := by
  by_contra! no
  obtain ⟨i,a,b⟩ := (Finset.mem_filter.mp he).2
  obtain ⟨j,c,d⟩ := (Finset.mem_filter.mp hf).2
  by_cases em : incidence e.1 f.2
  · have fl : ¬incidence f.1 e.2 := fun h => no.2 (uniqueLine _ _ _ _ no.1 i em h j)
    obtain ⟨Q,good,yes⟩ := mixedPairBad A B f e fl c a d b
    exact clean Q good yes
  · obtain ⟨Q,good,yes⟩ := mixedPairBad A B e f em a c b d
    exact clean Q good yes

theorem ordinaryStar (A B : RawClause) (clean : cleanTwo A B) :
    (∃ p : Fin 13, ∀ e ∈ flagsTwo A B, e.1=p) ∨ (∃ l : Fin 13, ∀ e ∈ flagsTwo A B, e.2=l) := by
  classical
  by_cases varied : ∃ e ∈ flagsTwo A B, ∃ f ∈ flagsTwo A B, e.1 ≠ f.1
  · right
    obtain ⟨e,em,f,fm,ne⟩ := varied
    have common := (shareCenter A B clean em fm).resolve_left ne
    refine ⟨e.2,fun z zm => ?_⟩
    have x := shareCenter A B clean zm em
    have y := shareCenter A B clean zm fm
    grind
  · left
    by_cases pop : (flagsTwo A B).Nonempty
    · obtain ⟨e,em⟩ := pop
      exact ⟨e.1,fun z zm => by by_contra no; exact varied ⟨z,zm,e,em,no⟩⟩
    · exact ⟨0,fun _ hm => False.elim (pop ⟨_,hm⟩)⟩

end QuadSeparation

namespace QuadSeparation

def containsLines (X : RawClause) (p : Fin 13) : Prop := ∀ k : Fin 13, incidence p k → (X k).2 = true

theorem separatePoints : ∀ p q : Fin 13, p ≠ q → ∃ k : Fin 13, incidence p k ∧ ¬incidence q k := by decide +kernel

theorem saturatedRow (X : RawClause) (p : Fin 13) (full : ∀ l, incidence p l → acceptsFlag X (p,l)) :
    (X p).1 = true ∨ containsLines X p := by
  cases bit : (X p).1
  · exact Or.inr (fun k inc => (full k inc).resolve_left (by simp [bit]))
  · exact Or.inl rfl

theorem twoLineCoversBad (A B C : RawClause) (p q l : Fin 13) (diff : p ≠ q)
    (a : containsLines A p) (b : containsLines B p) (c : acceptsFlag C (q,l)) :
    ∃ Q, quadOK Q ∧ acceptsQuad A Q ∧ acceptsQuad B Q ∧ acceptsQuad C Q := by
  obtain ⟨k,pk,qk⟩ := separatePoints p q diff
  have lineHit (Q : Finset (Fin 13)) (missing : k ∈ TQ Q) :
      acceptsQuad A Q ∧ acceptsQuad B Q :=
    ⟨Or.inr ⟨k,a k pk,(Finset.mem_filter.mp missing).2⟩,Or.inr ⟨k,b k pk,(Finset.mem_filter.mp missing).2⟩⟩
  rcases c with qc | lc
  · obtain ⟨sz,ok,x,miss⟩ := geo_quad _ _ qk
    have hit := lineHit _ miss
    exact ⟨_,⟨sz,ok⟩,hit.1,hit.2,Or.inl ⟨_,x,qc⟩⟩
  · obtain ⟨sz,ok,x,miss⟩ := geoLL l k
    have hit := lineHit _ miss
    exact ⟨_,⟨sz,ok⟩,hit.1,hit.2,Or.inr ⟨_,lc,(Finset.mem_filter.mp x).2⟩⟩

def exactLines (X : RawClause) (p : Fin 13) : Prop :=
  (∀ q, (X q).1 = false) ∧ (∀ k, (X k).2 = true ↔ incidence p k)

theorem forceLineClause (A B C : RawClause) (p q l : Fin 13) (diff : p ≠ q)
    (clean : cleanTerm A B C) (row : ∀ k, incidence p k →
       acceptsFlag A (p,k) ∧ acceptsFlag B (p,k) ∧ acceptsFlag C (p,k))
    (extra : acceptsFlag A (q,l) ∧ acceptsFlag B (q,l) ∧ acceptsFlag C (q,l))
    (missing : (A p).1 = false) :
    exactLines A p ∧ (B p).1 = true ∧ (C p).1 = true := by
  have a := (saturatedRow A p (fun k h => (row k h).1)).resolve_left (by simp [missing])
  have bp : (B p).1 = true := by
    apply (saturatedRow B p (fun k h => (row k h).2.1)).resolve_right
    intro b
    obtain ⟨Q,g,on⟩ := twoLineCoversBad A B C p q l diff a b extra.2.2
    exact clean Q g on
  have cp : (C p).1 = true := by
    apply (saturatedRow C p (fun k h => (row k h).2.2)).resolve_right
    intro c
    obtain ⟨Q,g,aa,cc,bb⟩ := twoLineCoversBad A C B p q l diff a c extra.2.1
    exact clean Q g ⟨aa,bb,cc⟩
  have rejects (Q) (g : quadOK Q) (inQ : p ∈ Q) : ¬acceptsQuad A Q :=
    fun on => clean Q g ⟨on,Or.inl ⟨_,inQ,bp⟩,Or.inl ⟨_,inQ,cp⟩⟩
  refine ⟨⟨?_,?_⟩,bp,cp⟩
  · intro u
    cases bit : (A u).1
    · rfl
    · obtain ⟨s,g,hit,other⟩ := geoPP p u
      exact False.elim (rejects _ ⟨s,g⟩ hit (Or.inl ⟨_,other,bit⟩))
  · intro k
    refine ⟨?_,a k⟩
    intro fires
    by_contra no
    obtain ⟨s,g,hit,miss⟩ := geo_quad p k no
    exact rejects _ ⟨s,g⟩ hit (Or.inr ⟨_,fires,(Finset.mem_filter.mp miss).2⟩)

def purePointsOn (X : RawClause) (l : Fin 13) : Prop :=
  (∀ k, (X k).2 = false) ∧ (∀ u, (X u).1 = true → incidence u l)

theorem forcePointClause (A B C : RawClause) (p q l : Fin 13) (diff : p ≠ q)
    (pl : incidence p l) (clean : cleanTerm A B C) (la : containsLines A p)
    (extraB : acceptsFlag B (q,l)) (extraC : acceptsFlag C (q,l)) (no : (C l).2 = false) :
    (B l).2 = true ∧ purePointsOn C l := by
  have cq := extraC.resolve_right (by simp [no])
  have bl : (B l).2 = true := by
    cases bit : (B l).2
    · have bq := extraB.resolve_right (by simp [bit])
      obtain ⟨k,pk,qk⟩ := separatePoints p q diff
      obtain ⟨sz,good,on,off⟩ := geo_quad _ _ qk
      exact False.elim (clean _ ⟨sz,good⟩
        ⟨Or.inr ⟨_,la k pk,(Finset.mem_filter.mp off).2⟩,Or.inl ⟨_,on,bq⟩,Or.inl ⟨_,on,cq⟩⟩)
    · rfl
  have rejects (Q) (g : quadOK Q) (off : l ∈ TQ Q) : ¬acceptsQuad C Q :=
    fun on => clean Q g ⟨Or.inr ⟨_,la l pl,(Finset.mem_filter.mp off).2⟩,
      Or.inr ⟨_,bl,(Finset.mem_filter.mp off).2⟩,on⟩
  refine ⟨bl,?_,?_⟩
  · intro k
    cases bit : (C k).2
    · rfl
    · obtain ⟨sz,good,off,miss⟩ := geoLL l k
      exact False.elim (rejects _ ⟨sz,good⟩ off (Or.inr ⟨_,bit,(Finset.mem_filter.mp miss).2⟩))
  · intro u yes
    by_contra no
    obtain ⟨sz,good,on,off⟩ := geo_quad u l no
    exact rejects _ ⟨sz,good⟩ off (Or.inl ⟨_,on,yes⟩)

end QuadSeparation

/-! The exact-fan-in-two gate semantics and OR-trace facts are from L-meta-1490. -/
namespace SinglePairShape
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.MetaComplexity
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_1490
attribute [local instance] gateOpDecEq
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

def activeSide (C : Circuit) (g : ℕ) (b : Fin 2) (x : Fin n → Bool) : Prop :=
  ∃ u ∈ side C g b, x u = true

theorem coneLt {i j : ℕ} (h : InCone n C i j) : i < j := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    obtain ⟨_,k,hk,_,rfl|sub⟩ := (inCone_iff n C i j).mp h
    · exact hk
    · exact lt_trans (ih k hk sub) hk

theorem operandMem (ao : IsAO2 n C) (g : ℕ) (realG : g < C.gates.length) (b : Fin 2) :
    opnd C g b ∈ (gateAt C g).inputs := by
  obtain ⟨p,q,eq⟩ := List.length_eq_two.mp (ao.2.2 _ (gateAt_mem realG))
  fin_cases b <;> simp [opnd,eq]

theorem andVal (ao : IsAO2 n C) (g : ℕ) (realG : g < C.gates.length)
    (op : (gateAt C g).op = GateOp.and) (x : Fin n → Bool) :
    gateVal n C g x = true ↔ ∀ b : Fin 2, val C (List.ofFn x) (opnd C g b) = true := by
  change val C (List.ofFn x) (n+g) = true ↔ _
  rw [val_and (by simp : (List.ofFn x).length = n) realG op]
  constructor
  · exact fun h b => (h _ (operandMem ao g realG b)).2
  · intro h i hi
    refine ⟨ao.2.1 g realG i hi,?_⟩
    obtain ⟨p,q,eq⟩ := List.length_eq_two.mp (ao.2.2 _ (gateAt_mem realG))
    simp only [eq,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl
    · simpa [opnd,eq] using h 0
    · simpa [opnd,eq] using h 1


theorem uniquePair (count : andPairs n C ≤ 1) {a b i j : ℕ}
    (ra : a < C.gates.length) (rb : b < C.gates.length) (ri : i < C.gates.length) (rj : j < C.gates.length)
    (oa : (gateAt C a).op = GateOp.and) (ob : (gateAt C b).op = GateOp.and)
    (oi : (gateAt C i).op = GateOp.and) (oj : (gateAt C j).op = GateOp.and)
    (ab : InCone n C a b) (ij : InCone n C i j) : a = i ∧ b = j := by
  unfold andPairs at count
  have eq : (a,b) = (i,j) := by
    apply Finset.card_le_one.mp count
    · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr ra,Finset.mem_range.mpr rb⟩,oa,ob,ab⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr ri,Finset.mem_range.mpr rj⟩,oi,oj,ij⟩
  exact Prod.mk.inj eq

/-- With one nested pair, the only extra OR source for an AND operand is the
inner AND, and that source is possible only at the outer AND. -/
theorem sideForm (ao : IsAO2 n C) {a b j : ℕ} (count : andPairs n C ≤ 1)
    (ra : a < C.gates.length) (rb : b < C.gates.length) (rj : j < C.gates.length)
    (oa : (gateAt C a).op = GateOp.and) (ob : (gateAt C b).op = GateOp.and)
    (oj : (gateAt C j).op = GateOp.and) (ab : InCone n C a b) (d : Fin 2) (x : Fin n → Bool) :
    val C (List.ofFn x) (opnd C j d) = true ↔ activeSide C j d x ∨
       j=b ∧ OrReaches n C (opnd C j d) a ∧ gateVal n C a x = true := by
  have mem := operandMem ao j rj d
  constructor
  · intro on
    obtain ⟨w,path,yes,raw | ⟨k,rk,rfl,nonOR⟩⟩ := or_trace (n:=n) (by simp) _ on
    · let u : Fin n := ⟨w,raw⟩
      exact Or.inl ⟨u,reach_mem_orIn u path,(val_ofFn C x u).symm.trans yes⟩
    · have ok := (ao.1 _ (gateAt_mem rk)).resolve_right nonOR
      have kj := operand_cone rj mem (ao.2.1 j rj _ mem) path
      obtain ⟨rfl,rfl⟩ := uniquePair count ra rb rk rj oa ob ok oj ab kj
      exact Or.inr ⟨rfl,reach_orReaches path _ rfl rk,yes⟩
  · rintro (⟨u,hu,xu⟩ | ⟨_,read,yes⟩)
    · exact reach_var_val x _ u (mem_orIn_reach u hu) xu
    · exact orStep_up (by simp) (orReaches_reach a _ read).1 yes


def lit (S : Finset (Fin n)) (x : Fin n → Bool) : Prop := ∃ u ∈ S, x u = true

theorem litUnion (S T : Finset (Fin n)) (x : Fin n → Bool) :
    lit (S ∪ T) x ↔ lit S x ∨ lit T x := by
  constructor
  · rintro ⟨u,um,yes⟩
    rcases Finset.mem_union.mp um with us | ut
    · exact Or.inl ⟨u,us,yes⟩
    · exact Or.inr ⟨u,ut,yes⟩
  · rintro (⟨u,um,yes⟩ | ⟨u,um,yes⟩)
    · exact ⟨u,Finset.mem_union_left _ um,yes⟩
    · exact ⟨u,Finset.mem_union_right _ um,yes⟩

def twoTerm (n : ℕ) (C : Circuit) (j : ℕ) : Prop := ∃ S T : Finset (Fin n),
  ∀ x, gateVal n C j x = true ↔ lit S x ∧ lit T x

def threeTerm (n : ℕ) (C : Circuit) (j : ℕ) : Prop := ∃ S T U : Finset (Fin n),
  ∀ x, gateVal n C j x = true ↔ lit S x ∧ lit T x ∧ lit U x

def pairedTerms (n : ℕ) (C : Circuit) (j : ℕ) : Prop := ∃ S T U V : Finset (Fin n),
  ∀ x, gateVal n C j x = true ↔ (lit S x ∧ lit T x) ∨ (lit U x ∧ lit V x)

theorem formFromSides {a b j : ℕ} (ao : IsAO2 n C) (count : andPairs n C ≤ 1)
    (ra : a < C.gates.length) (rb : b < C.gates.length) (rj : j < C.gates.length)
    (oa : (gateAt C a).op = GateOp.and) (ob : (gateAt C b).op = GateOp.and)
    (oj : (gateAt C j).op = GateOp.and) (ab : InCone n C a b) :
    ∀ x, gateVal n C j x = true ↔
      (lit (side C j 0) x ∨ (j = b ∧ OrReaches n C (opnd C j 0) a) ∧ gateVal n C a x = true) ∧
      (lit (side C j 1) x ∨ (j = b ∧ OrReaches n C (opnd C j 1) a) ∧ gateVal n C a x = true) := by
  intro x
  rw [andVal ao j rj oj]
  have trace := sideForm ao count ra rb rj oa ob oj ab
  constructor
  · intro yes
    constructor
    · simpa only [and_assoc,lit,activeSide] using (trace 0 x).mp (yes 0)
    · simpa only [and_assoc,lit,activeSide] using (trace 1 x).mp (yes 1)
  · rintro ⟨h,k⟩ d
    have z := (trace 0 x).mpr (by simpa only [and_assoc,lit,activeSide] using h)
    have o := (trace 1 x).mpr (by simpa only [and_assoc,lit,activeSide] using k)
    fin_cases d <;> assumption

theorem otherAnd {a b j : ℕ} (ao : IsAO2 n C) (count : andPairs n C ≤ 1)
    (ra : a < C.gates.length) (rb : b < C.gates.length) (rj : j < C.gates.length)
    (oa : (gateAt C a).op = GateOp.and) (ob : (gateAt C b).op = GateOp.and)
    (oj : (gateAt C j).op = GateOp.and) (ab : InCone n C a b) (ordinary : j ≠ b) :
    twoTerm n C j := by
  refine ⟨side C j 0,side C j 1,fun x => ?_⟩
  simpa only [ordinary,false_and,or_false] using formFromSides ao count ra rb rj oa ob oj ab x

theorem outerAndCases {a b : ℕ} (ao : IsAO2 n C) (count : andPairs n C ≤ 1)
    (ra : a < C.gates.length) (rb : b < C.gates.length)
    (oa : (gateAt C a).op = GateOp.and) (ob : (gateAt C b).op = GateOp.and)
    (ab : InCone n C a b) : threeTerm n C b ∨ (∃ S T : Finset (Fin n), ∀ x, gateVal n C b x = true ↔
        (lit S x ∧ lit T x) ∨ gateVal n C a x = true) := by
  obtain ⟨A,B,inner⟩ := otherAnd ao count ra rb ra oa ob oa ab (Nat.ne_of_lt (coneLt ab))
  have outer := formFromSides ao count ra rb rb oa ob ob ab
  let S := side (n:=n) C b 0
  let T := side (n:=n) C b 1
  by_cases left : OrReaches n C (opnd C b 0) a <;> by_cases right : OrReaches n C (opnd C b 1) a
  · right; refine ⟨S,T,fun x => ?_⟩
    simp only [outer x,inner x,left,right,true_and]
    dsimp [S,T]; tauto
  · left; refine ⟨S ∪ A,S ∪ B,T,fun x => ?_⟩
    simp only [outer x,inner x,left,right,true_and,false_and,or_false,litUnion]
    dsimp [S,T]; tauto
  · left; refine ⟨S,T ∪ A,T ∪ B,fun x => ?_⟩
    simp only [outer x,inner x,left,right,true_and,false_and,or_false,litUnion]
    dsimp [S,T]; tauto
  · left; refine ⟨S,T,T,fun x => ?_⟩
    simp [outer x,left,right,S,T]


theorem outerAnd {a b : ℕ} (ao : IsAO2 n C) (count : andPairs n C ≤ 1)
    (ra : a < C.gates.length) (rb : b < C.gates.length)
    (oa : (gateAt C a).op = GateOp.and) (ob : (gateAt C b).op = GateOp.and)
    (ab : InCone n C a b) : threeTerm n C b ∨ pairedTerms n C b := by
  rcases outerAndCases ao count ra rb oa ob ab with three | ⟨S,T,eq⟩
  · exact Or.inl three
  · obtain ⟨U,V,inner⟩ := otherAnd ao count ra rb ra oa ob oa ab (Nat.ne_of_lt (coneLt ab))
    exact Or.inr ⟨S,T,U,V,fun x => by rw [eq,inner]⟩

end SinglePairShape

namespace PlaneCircuit
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.MetaComplexity
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open QuadSeparation SinglePairShape
attribute [local instance] gateOpDecEq

def flagBits (p l : Fin 13) : Fin 26 → Bool :=
  Fin.append (fun u : Fin 13 => decide (u=p)) (fun v : Fin 13 => decide (v=l))
def quadBits (Q : Finset (Fin 13)) : Fin 26 → Bool :=
  Fin.append (fun u : Fin 13 => decide (u ∈ Q)) (fun v : Fin 13 => decide (∀ p ∈ Q, p-v ∉ D))

theorem flagList (p l : Fin 13) : List.ofFn (flagBits p l) = flagInput p l := List.ofFn_fin_append ..
theorem quadList (Q : Finset (Fin 13)) : List.ofFn (quadBits Q) = quadInput Q := List.ofFn_fin_append ..

def raw (S : Finset (Fin 26)) : RawClause := fun i =>
  (decide (Fin.castAdd 13 i ∈ S),decide (Fin.natAdd 13 i ∈ S))

theorem splitLit (S : Finset (Fin 26)) (P L : Fin 13 → Bool) :
    lit S (Fin.append P L) ↔
      (∃ u : Fin 13, Fin.castAdd 13 u ∈ S ∧ P u = true) ∨
      ∃ v : Fin 13, Fin.natAdd 13 v ∈ S ∧ L v = true := by
  constructor
  · rintro ⟨i,si,on⟩
    induction i using (Fin.addCases (m:=13) (n:=13)) with
    | left u => exact Or.inl ⟨u,si,by simpa only [Fin.append_left,Fin.append_right] using on⟩
    | right v => exact Or.inr ⟨v,si,by simpa only [Fin.append_left,Fin.append_right] using on⟩
  · rintro (⟨u,mem,on⟩ | ⟨v,mem,on⟩)
    · exact ⟨_,mem,by simpa only [Fin.append_left,Fin.append_right] using on⟩
    · exact ⟨_,mem,by simpa only [Fin.append_left,Fin.append_right] using on⟩

theorem flagLit (S : Finset (Fin 26)) (p l : Fin 13) :
    lit S (flagBits p l) ↔ acceptsFlag (raw S) (p,l) := by
  simp [flagBits,splitLit,acceptsFlag,raw]

theorem quadLit (S : Finset (Fin 26)) (Q : Finset (Fin 13)) :
    lit S (quadBits Q) ↔ acceptsQuad (raw S) Q := by
  rw [quadBits,splitLit]
  simp only [acceptsQuad,raw,decide_eq_true_eq]
  grind

def flags (C : Circuit) (j : ℕ) : Finset (Fin 13 × Fin 13) :=
  Finset.univ.filter fun e => incidence e.1 e.2 ∧ gateVal 26 C j (flagBits e.1 e.2) = true

def safe (C : Circuit) (j : ℕ) : Prop := ∀ Q, quadOK Q → gateVal 26 C j (quadBits Q) = false

def star (S : Finset (Fin 13 × Fin 13)) : Prop :=
  (∃ p : Fin 13, ∀ e ∈ S, e.1=p) ∨ (∃ l : Fin 13, ∀ e ∈ S, e.2=l)

theorem threeSub {C : Circuit} {j : ℕ} (form : threeTerm 26 C j) (rejects : safe C j) :
    ∃ p l, incidence p l ∧ flags C j ⊆ doubleStar p l := by
  obtain ⟨S,T,U,eq⟩ := form
  apply (doubleStarClassification _).mp
  refine ⟨raw S,raw T,raw U,?_,?_⟩
  · intro Q good accepted
    have on := (eq (quadBits Q)).mpr ⟨(quadLit _ _).mpr accepted.1,(quadLit _ _).mpr accepted.2.1,(quadLit _ _).mpr accepted.2.2⟩
    simp [rejects Q good] at on
  · intro e mem
    obtain ⟨inc,on⟩ := (Finset.mem_filter.mp mem).2
    obtain ⟨a,b,c⟩ := (eq _).mp on
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,inc,(flagLit _ _ _).mp a,(flagLit _ _ _).mp b,(flagLit _ _ _).mp c⟩

theorem twoStar {C : Circuit} {j : ℕ} (form : twoTerm 26 C j) (rejects : safe C j) :
    star (flags C j) := by
  obtain ⟨S,T,eq⟩ := form
  have clean : cleanTwo (raw S) (raw T) := by
    intro Q good on
    have hit := (eq _).mpr ⟨(quadLit _ _).mpr on.1,(quadLit _ _).mpr on.2⟩
    simp [rejects Q good] at hit
  have fe : flags C j = flagsTwo (raw S) (raw T) := by
    ext e
    simp only [flags,flagsTwo,Finset.mem_filter,Finset.mem_univ,true_and,eq,flagLit,acceptsFlag]
  rw [fe]; exact ordinaryStar _ _ clean

theorem twoStars {C : Circuit} {j : ℕ} (form : pairedTerms 26 C j) (rejects : safe C j) :
    ∃ V W, star V ∧ star W ∧ flags C j = V ∪ W := by
  obtain ⟨S,T,U,V,eq⟩ := form
  have neither (Q) (good : quadOK Q) : ¬ ((acceptsQuad (raw S) Q ∧ acceptsQuad (raw T) Q) ∨
       (acceptsQuad (raw U) Q ∧ acceptsQuad (raw V) Q)) := by
    simp only [←quadLit,←eq,rejects Q good,Bool.false_eq_true,not_false_eq_true]
  have one : cleanTwo (raw S) (raw T) := fun Q h a => neither Q h (Or.inl a)
  have two : cleanTwo (raw U) (raw V) := fun Q h a => neither Q h (Or.inr a)
  refine ⟨flagsTwo (raw S) (raw T),flagsTwo (raw U) (raw V),ordinaryStar _ _ one,ordinaryStar _ _ two,?_⟩
  ext e
  simp only [flags,flagsTwo,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and,eq,flagLit,acceptsFlag]
  tauto

end PlaneCircuit

namespace PlaneCircuit
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.MetaComplexity
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.Outside.L_meta_1490
open QuadSeparation SinglePairShape
attribute [local instance] gateOpDecEq

def frontier (C : Circuit) : Finset ℕ :=
  (Finset.range C.gates.length).filter fun j =>
    (gateAt C j).op = GateOp.and ∧ OrReaches 26 C C.output j

def planeFlags : Finset (Fin 13 × Fin 13) := Finset.univ.filter fun e => incidence e.1 e.2

def acceptsAll (C : Circuit) := ∀ p l : Fin 13, incidence p l → C.eval (flagInput p l) = true
def rejectsAll (C : Circuit) := ∀ Q, quadOK Q → C.eval (quadInput Q) = false

theorem frontierSafe {C : Circuit} (neg : rejectsAll C) {j : ℕ} (front : j ∈ frontier C) : safe C j := by
  intro Q hQ
  cases yes : gateVal 26 C j (quadBits Q)
  · rfl
  · have e := (Finset.mem_filter.mp front).2.2
    have valOut := orStep_up (by simp : (List.ofFn (quadBits Q)).length = 26)
      (orReaches_reach j _ e).1 yes
    change C.eval (List.ofFn (quadBits Q)) = true at valOut
    simp only [quadList,neg Q hQ] at valOut
    contradiction

theorem quadActivates (i : Fin 26) : ∃ Q, quadOK Q ∧ quadBits Q i = true := by
  induction i using (Fin.addCases (m:=13) (n:=13)) with
  | left p =>
    obtain ⟨sz,ok,pm,_⟩ := geoPP p p
    exact ⟨_,⟨sz,ok⟩,by simpa only [quadBits,Fin.append_left,decide_eq_true_eq] using pm⟩
  | right l =>
    obtain ⟨sz,ok,lm,_⟩ := geoLL l l
    exact ⟨_,⟨sz,ok⟩,by simpa only [quadBits,Fin.append_right,decide_eq_true_eq] using (Finset.mem_filter.mp lm).2⟩

theorem frontierCovers {C : Circuit} (ao : IsAO2 26 C) (pos : acceptsAll C) (neg : rejectsAll C) :
    planeFlags ⊆ (frontier C).biUnion (flags C) := by
  rintro ⟨p,l⟩ mem
  have inc := (Finset.mem_filter.mp mem).2
  have on : val C (List.ofFn (flagBits p l)) C.output = true := by
    change C.eval (List.ofFn _) = true
    rw [flagList]; exact pos p l inc
  obtain ⟨w,path,yes,isRaw | ⟨j,realJ,rfl,nonOR⟩⟩ := or_trace (n:=26) (by simp) _ on
  · let i : Fin 26 := ⟨w,isRaw⟩
    obtain ⟨Q,ok,hQ⟩ := quadActivates i
    have inBit : val C (List.ofFn (quadBits Q)) w = true := (val_ofFn C _ i).trans hQ
    have bad := orStep_up (by simp : (List.ofFn (quadBits Q)).length = 26) path inBit
    change C.eval (List.ofFn (quadBits Q)) = true at bad
    simp only [quadList,neg Q ok] at bad
    contradiction
  · have andJ := (ao.1 _ (gateAt_mem realJ)).resolve_right nonOR
    apply Finset.mem_biUnion.mpr
    exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr realJ,andJ,reach_orReaches path _ rfl realJ⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,inc,yes⟩⟩

theorem planeSize : planeFlags.card = 52 := by decide +kernel
theorem pointSize : ∀ p : Fin 13, (planeFlags.filter fun e => e.1 = p).card = 4 := by decide +kernel
theorem lineSize : ∀ l : Fin 13, (planeFlags.filter fun e => e.2 = l).card = 4 := by decide +kernel

theorem sizeOfStar {S : Finset (Fin 13 × Fin 13)} (valid : S ⊆ planeFlags) (h : star S) : S.card ≤ 4 := by
  rcases h with ⟨p,all⟩ | ⟨l,all⟩
  · rw [← pointSize p]; exact Finset.card_le_card (fun e em => Finset.mem_filter.mpr ⟨valid em,all e em⟩)
  · rw [← lineSize l]; exact Finset.card_le_card (fun e em => Finset.mem_filter.mpr ⟨valid em,all e em⟩)

theorem flagsValid (C : Circuit) (j : ℕ) : flags C j ⊆ planeFlags :=
  fun _ em => Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp em).2.1⟩

theorem countFrontier {C : Circuit} {a b : ℕ} (ao : IsAO2 26 C) (count : andPairs 26 C ≤ 1)
    (ra : a < C.gates.length) (rb : b < C.gates.length)
    (oa : (gateAt C a).op = GateOp.and) (ob : (gateAt C b).op = GateOp.and)
    (ab : InCone 26 C a b) (pos : acceptsAll C) (neg : rejectsAll C) :
    12 ≤ (frontier C).card ∧ (threeTerm 26 C b → 13 ≤ (frontier C).card) := by
  let F := frontier C
  have base : ∀ j ∈ F.erase b, (flags C j).card ≤ 4 := by
    intro j hj
    obtain ⟨ne,fm⟩ := Finset.mem_erase.mp hj
    obtain ⟨real,op,_⟩ := Finset.mem_filter.mp fm
    exact sizeOfStar (flagsValid _ _) (twoStar
      (otherAnd ao count ra rb (Finset.mem_range.mp real) oa ob op ab ne) (frontierSafe neg fm))
  have covered := Finset.card_le_card (frontierCovers ao pos neg)
  rw [planeSize] at covered
  have rest := Finset.card_biUnion_le_card_mul (F.erase b) (flags C) 4 base
  by_cases inside : b ∈ F
  · have split : F.biUnion (flags C) = flags C b ∪ (F.erase b).biUnion (flags C) := by
      calc F.biUnion (flags C) = (insert b (F.erase b)).biUnion (flags C) := by rw [Finset.insert_erase inside]
           _ = _ := Finset.biUnion_insert
    change 52 ≤ (F.biUnion (flags C)).card at covered
    rw [split] at covered
    have union := Finset.card_union_le (flags C b) ((F.erase b).biUnion (flags C))
    have pop := Finset.card_erase_add_one inside
    have small (h : threeTerm 26 C b) : (flags C b).card ≤ 7 := by
      obtain ⟨p,l,inc,sub⟩ := threeSub h (frontierSafe neg inside)
      exact (Finset.card_le_card sub).trans_eq (doubleStarSize p l inc)
    have eight : (flags C b).card ≤ 8 := by
      rcases outerAnd ao count ra rb oa ob ab with h | h
      · exact (small h).trans (by decide)
      · obtain ⟨V,W,sv,sw,eq⟩ := twoStars h (frontierSafe neg inside)
        have val := flagsValid C b
        rw [eq] at val ⊢
        have v := sizeOfStar (Finset.Subset.trans Finset.subset_union_left val) sv
        have w := sizeOfStar (Finset.Subset.trans Finset.subset_union_right val) sw
        have u := Finset.card_union_le V W; omega
    change 12 ≤ F.card ∧ (_ → 13 ≤ F.card)
    exact ⟨by omega,fun h => by have upper := small h; omega⟩
  · rw [Finset.erase_eq_of_notMem inside] at rest
    change 52 ≤ (F.biUnion (flags C)).card at covered
    change 12 ≤ F.card ∧ (_ → 13 ≤ F.card)
    exact ⟨by omega,fun _ => by omega⟩

end PlaneCircuit

namespace PlaneCircuit
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.MetaComplexity
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open QuadSeparation SinglePairShape
attribute [local instance] gateOpDecEq

theorem twelveCase {C : Circuit} {a b : ℕ} (ao : IsAO2 26 C) (count : andPairs 26 C ≤ 1)
    (ra : a < C.gates.length) (rb : b < C.gates.length)
    (oa : (gateAt C a).op = GateOp.and) (ob : (gateAt C b).op = GateOp.and)
    (ab : InCone 26 C a b) (pos : acceptsAll C) (neg : rejectsAll C)
    (twelve : (frontier C).card = 12) :
    b ∈ frontier C ∧ a ∉ frontier C ∧ safe C a ∧ (flags C a).card = 4 ∧ (flags C b).card = 8 := by
  let F := frontier C
  let R := (F.erase b).biUnion (flags C)
  have otherBound : R.card ≤ (F.erase b).card * 4 := by
    apply Finset.card_biUnion_le_card_mul
    intro j hj
    obtain ⟨ne,fm⟩ := Finset.mem_erase.mp hj
    obtain ⟨real,op,_⟩ := Finset.mem_filter.mp fm
    exact sizeOfStar (flagsValid _ _) (twoStar
      (otherAnd ao count ra rb (Finset.mem_range.mp real) oa ob op ab ne) (frontierSafe neg fm))
  have covered := Finset.card_le_card (frontierCovers ao pos neg)
  rw [planeSize] at covered
  change 52 ≤ (F.biUnion (flags C)).card at covered
  change F.card = 12 at twelve
  have inside : b ∈ F := by
    by_contra miss
    unfold R at otherBound
    rw [Finset.erase_eq_of_notMem miss,twelve] at otherBound
    omega
  have pop := Finset.card_erase_add_one inside
  have cap : R.card ≤ 44 := by omega
  have split : F.biUnion (flags C) = flags C b ∪ R := by
    calc F.biUnion (flags C) = (insert b (F.erase b)).biUnion (flags C) := by rw [Finset.insert_erase inside]
         _ = _ := Finset.biUnion_insert
  rw [split] at covered
  have isPair := outerAndCases ao count ra rb oa ob ab
  obtain ⟨S,T,eq⟩ := isPair.resolve_left (fun three => by
    have n := (countFrontier ao count ra rb oa ob ab pos neg).2 three
    change 13 ≤ F.card at n; omega)
  have sb := frontierSafe neg inside
  have sa : safe C a := by
    intro Q good
    cases bit : gateVal 26 C a (quadBits Q)
    · rfl
    · have bad := (eq _).mpr (Or.inr bit)
      simp [sb Q good] at bad
  have clean : cleanTwo (raw S) (raw T) := by
    intro Q good fire
    have bad := (eq _).mpr (Or.inl ⟨(quadLit _ _).mpr fire.1,(quadLit _ _).mpr fire.2⟩)
    simp [sb Q good] at bad
  let V := flagsTwo (raw S) (raw T)
  have vOK : V ⊆ planeFlags := fun _ em => Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp em).2.1⟩
  have vCard := sizeOfStar vOK (ordinaryStar _ _ clean)
  have aCard := sizeOfStar (flagsValid C a) (twoStar (otherAnd ao count ra rb ra oa ob oa ab (Nat.ne_of_lt (coneLt ab))) sa)
  have beq : flags C b = V ∪ flags C a := by
    ext e; simp only [V,flags,flagsTwo,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and,eq,flagLit,acceptsFlag]
    tauto
  have bCard : (flags C b).card ≤ V.card + (flags C a).card := beq ▸ Finset.card_union_le _ _
  have lim := Finset.card_union_le (flags C b) R
  have outside : a ∉ F := by
    intro am
    have arm : a ∈ F.erase b := Finset.mem_erase.mpr ⟨Nat.ne_of_lt (coneLt ab),am⟩
    have sub : flags C a ⊆ R := fun _ hm => Finset.mem_biUnion.mpr ⟨a,arm,hm⟩
    rw [beq,Finset.union_assoc,Finset.union_eq_right.mpr sub] at covered
    have vlim := Finset.card_union_le V R
    omega
  exact ⟨inside,outside,sa,by omega,by omega⟩

def allAnd (C : Circuit) := (Finset.range C.gates.length).filter fun j => (gateAt C j).op = GateOp.and

theorem thirteenAnd {C : Circuit} {a b : ℕ} (ao : IsAO2 26 C) (count : andPairs 26 C ≤ 1)
    (ra : a < C.gates.length) (rb : b < C.gates.length)
    (oa : (gateAt C a).op = GateOp.and) (ob : (gateAt C b).op = GateOp.and)
    (ab : InCone 26 C a b) (pos : acceptsAll C) (neg : rejectsAll C) : 13 ≤ (allAnd C).card := by
  have sub : frontier C ⊆ allAnd C := by
    intro j h; obtain ⟨r,op,_⟩ := Finset.mem_filter.mp h; exact Finset.mem_filter.mpr ⟨r,op⟩
  have base := (countFrontier ao count ra rb oa ob ab pos neg).1
  by_cases eq : (frontier C).card = 12
  · have outside := (twelveCase ao count ra rb oa ob ab pos neg eq).2.1
    have am : a ∈ allAnd C := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ra,oa⟩
    have ss : insert a (frontier C) ⊆ allAnd C := Finset.insert_subset am sub
    have sz := Finset.card_le_card ss
    rw [Finset.card_insert_of_notMem outside,eq] at sz; exact sz
  · have sz := Finset.card_le_card sub; omega

end PlaneCircuit

namespace PlaneCircuit
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.MetaComplexity
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.Outside.L_meta_1490
open QuadSeparation SinglePairShape
attribute [local instance] gateOpDecEq

def outputOr (C : Circuit) := (Finset.range C.gates.length).filter fun j =>
  (gateAt C j).op = GateOp.or ∧ OrReaches 26 C C.output j

theorem outputTree {C : Circuit} (ao : IsAO2 26 C) : (frontier C).card ≤ (outputOr C).card + 1 := by
  let F := frontier C
  let O := outputOr C
  let inputs := fun k => (gateAt C k).inputs.toFinset
  have small : ∀ k ∈ O, (inputs k).card ≤ 2 := by
    intro k mem
    have len := ao.2.2 _ (gateAt_mem (Finset.mem_range.mp (Finset.mem_filter.mp mem).1))
    exact (List.toFinset_card_le _).trans_eq len
  have allInputs := Finset.card_biUnion_le_card_mul O inputs 2 small
  have sub : (F ∪ O).image (fun j => 26+j) ⊆ insert C.output (O.biUnion inputs) := by
    intro w mem
    obtain ⟨j,jm,rfl⟩ := Finset.mem_image.mp mem
    have reach : OrReaches 26 C C.output j := by
      rcases Finset.mem_union.mp jm with fj | oj
      · exact (Finset.mem_filter.mp fj).2.2
      · exact (Finset.mem_filter.mp oj).2.2
    rcases Relation.ReflTransGen.cases_tail (orReaches_reach j _ reach).1 with eq | ⟨u,prior,st⟩
    · exact Finset.mem_insert.mpr (Or.inl eq)
    · obtain ⟨k,rk,rfl,op,im,_⟩ := st
      have ko : k ∈ O := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr rk,op,reach_orReaches prior _ rfl rk⟩
      exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨k,ko,List.mem_toFinset.mpr im⟩)
  have counts := Finset.card_le_card sub
  have inj : Function.Injective (fun j : ℕ => 26+j) := fun i j h => Nat.add_left_cancel h
  rw [Finset.card_image_of_injective _ inj] at counts
  have dis : Disjoint F O := by
    apply Finset.disjoint_left.mpr
    intro j fj oj
    have p := (Finset.mem_filter.mp fj).2.1
    have q := (Finset.mem_filter.mp oj).2.1
    simp [p] at q
  rw [Finset.card_union_of_disjoint dis] at counts
  have ins := Finset.card_insert_le C.output (O.biUnion inputs)
  change F.card ≤ O.card + 1
  omega

theorem gateBudget (C : Circuit) : (allAnd C).card + (outputOr C).card ≤ C.size := by
  have dis : Disjoint (allAnd C) (outputOr C) := by
    apply Finset.disjoint_left.mpr; intro j am om
    have a := (Finset.mem_filter.mp am).2
    have o := (Finset.mem_filter.mp om).2.1
    simp [a] at o
  rw [←Finset.card_union_of_disjoint dis]
  have sub : allAnd C ∪ outputOr C ⊆ Finset.range C.gates.length := by
    intro j m
    rcases Finset.mem_union.mp m with a | o
    · exact (Finset.mem_filter.mp a).1
    · exact (Finset.mem_filter.mp o).1
  simpa [Circuit.size] using Finset.card_le_card sub

end PlaneCircuit


namespace PlaneCircuit
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.MetaComplexity
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_1490
open QuadSeparation SinglePairShape
attribute [local instance] gateOpDecEq

/-- The original L-meta-1961 hypotheses put explicit limits on the number and
flag coverage of the AND gates visible through output OR wires. -/
theorem deskGateCounts : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x3 x4 : Fin (13 : ℕ)), x3 - x4 ∈ x1 → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card = (4 : ℕ) → (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x3 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x7 - x6 ∉ x1)) = Bool.false; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => ∃ (x4 : ℕ) (x5 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x3 x4 x5; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x4 → x2 x4 → x4.size < (64 : ℕ) → x3 x4 → (∀ x10 ∈ x4.gates, x10.inputs.length = (2 : ℕ) ∧ x10.inputs.getD (0 : ℕ) (0 : ℕ) ≠ x10.inputs.getD (1 : ℕ) (0 : ℕ)) → PEqualNP.TopForm.andPairs (26 : ℕ) x4 ≤ (1 : ℕ) → 13 ≤ (allAnd x4).card ∧ 12 ≤ (frontier x4).card ∧ (frontier x4).card ≤ 32 ∧
    ((frontier x4).card = 12 → ∃ a b, InCone 26 x4 a b ∧ b ∈ frontier x4 ∧ a ∉ frontier x4 ∧
      safe x4 a ∧ (flags x4 a).card = 4 ∧ (flags x4 b).card = 8) := by
  dsimp only
  intro C mono back correct small nested strict count
  obtain ⟨a,b,oa,ob,ab⟩ := nested
  have rb := ((inCone_iff 26 C a b).mp ab).1
  have ra := lt_trans (coneLt ab) rb
  have ao : IsAO2 26 C := ⟨fun g h => (mono g h).1, back,fun g h => (strict g h).1⟩
  have pos : acceptsAll C := correct.1
  have neg : rejectsAll C := fun Q h => correct.2 Q h.1 h.2
  have ac := thirteenAnd ao count ra rb oa ob ab pos neg
  have fc := (countFrontier ao count ra rb oa ob ab pos neg).1
  have orc := outputTree ao
  have all := gateBudget C
  have sub : frontier C ⊆ allAnd C := by
    intro z hz; obtain ⟨r,o,_⟩ := Finset.mem_filter.mp hz; exact Finset.mem_filter.mpr ⟨r,o⟩
  have size := Finset.card_le_card sub
  exact ⟨ac,fc,by omega,fun eq => ⟨a,b,ab,twelveCase ao count ra rb oa ob ab pos neg eq⟩⟩

end PlaneCircuit
