import Mathlib
import PEqualNP.Outside.L_meta_1490

/-!
Two incomparable junk AND gates in an exact-fan-in-two top-form circuit.
The wire evaluator and OR-path lemmas come from L-meta-1490. The graph cover
argument uses the two triangles and five-cycle from R-meta-1597-318.
The lemma threeUncovered forces three missing edges in any counterexample.
The lemmas tripleConstraint and tripleCount leave 204 of 560 possible triples.
For an arbitrary deleted edge set, coverMaskIff characterizes exactly when
the remaining graph has a vertex cover of size at most five.

-/
namespace TwoJunkGeometry
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

theorem junkFacts {g : ℕ} (hg : g ∈ junk G C) :
    g < C.gates.length ∧ (gateAt C g).op = GateOp.and ∧
      ∃ x, gateVal n C g x = true ∧ graphFun G ∅ x = false := by
  obtain ⟨r,d⟩ := Finset.mem_filter.mp hg
  exact ⟨Finset.mem_range.mp r,d.1,d.2.2⟩

theorem operandSources (ao : IsAO2 n C) (form : TopForm G C) {g : ℕ}
    (realG : g < C.gates.length) (op : (gateAt C g).op = GateOp.and)
    (b : Fin 2) (x : Fin n → Bool) :
    val C (List.ofFn x) (opnd C g b) = true ↔ activeSide C g b x ∨
      ∃ j ∈ junk G C, OrReaches n C (opnd C g b) j ∧ InCone n C j g ∧ gateVal n C j x = true := by
  have mem := operandMem ao g realG b
  have lt := ao.2.1 g realG _ mem
  constructor
  · intro on
    obtain ⟨w,path,yes,hinput | ⟨j,hj,rfl,nonOR⟩⟩ := or_trace (n:=n) (by simp) _ on
    · left
      let u : Fin n := ⟨w,hinput⟩
      exact ⟨u,reach_mem_orIn u path,(val_ofFn C x u).symm.trans yes⟩
    · right
      have andJ : (gateAt C j).op = GateOp.and := (ao.1 _ (gateAt_mem hj)).resolve_right nonOR
      have inside := operand_cone realG mem lt path
      have bad : ¬ BelowF G C j := fun good => form j hj g realG andJ good op inside
      have witness : ∃ y, gateVal n C j y = true ∧ graphFun G ∅ y = false := by
        by_contra! no
        exact bad (fun y hy => Bool.eq_true_of_not_eq_false (no y hy))
      exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,andJ,hj,witness⟩,
        reach_orReaches path j rfl hj,inside,yes⟩
  · rintro (⟨u,hu,xu⟩ | ⟨j,_,p,_,yes⟩)
    · exact reach_var_val x _ u (mem_orIn_reach u hu) xu
    · exact orStep_up (by simp) (orReaches_reach j _ p).1 yes

theorem junkPure (ao : IsAO2 n C) (form : TopForm G C) {g h : ℕ}
    (both : junk G C = {g,h}) (incomparable : ¬ InCone n C g h ∧ ¬ InCone n C h g)
    {j : ℕ} (which : j = g ∨ j = h) (x : Fin n → Bool) :
    gateVal n C j x = true ↔ activeSide C j 0 x ∧ activeSide C j 1 x := by
  have mem : j ∈ junk G C := by rw [both]; simpa using which
  obtain ⟨hj,oj,_⟩ := junkFacts mem
  have any (b : Fin 2) : val C (List.ofFn x) (opnd C j b) = true ↔ activeSide C j b x := by
    rw [operandSources ao form hj oj]
    apply or_iff_left_of_imp
    rintro ⟨k,hk,_,inside,_⟩
    rw [both] at hk
    simp only [Finset.mem_insert,Finset.mem_singleton] at hk
    have strict := coneLt inside
    rcases which with rfl | rfl <;> rcases hk with rfl | rfl <;> first | omega | exact False.elim (incomparable.1 inside) | exact False.elim (incomparable.2 inside)
  rw [andVal ao j hj oj]
  constructor
  · exact fun all => ⟨(any 0).mp (all 0),(any 1).mp (all 1)⟩
  · intro bothSides b
    fin_cases b
    · exact (any 0).mpr bothSides.1
    · exact (any 1).mpr bothSides.2


theorem coneTrans {r k t : ℕ} (rk : InCone n C r k) (kt : InCone n C k t) : InCone n C r t := by
  induction t using Nat.strong_induction_on with
  | ind t ih =>
    obtain ⟨ht,m,mt,mem,eq|km⟩ := (inCone_iff n C k t).mp kt
    · exact (inCone_iff n C r t).mpr ⟨ht,m,mt,mem,Or.inr (eq ▸ rk)⟩
    · exact (inCone_iff n C r t).mpr ⟨ht,m,mt,mem,Or.inr (ih m mt km)⟩

theorem orPath {r j : ℕ} (has : r = j ∨ InCone n C r j)
    (onlyOR : ∀ m, InCone n C r m → (m = j ∨ InCone n C m j) → (gateAt C m).op = GateOp.or) :
    Relation.ReflTransGen (OrStep n C) (n+j) (n+r) := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    rcases has with rfl | h
    · exact .refl
    · obtain ⟨hj,k,kj,mem,inside⟩ := (inCone_iff n C r j).mp h
      have cone := (inCone_iff n C k j).mpr ⟨hj,k,kj,mem,Or.inl rfl⟩
      have step : OrStep n C (n+j) (n+k) := ⟨j,hj,rfl,onlyOR j h (Or.inl rfl),mem,by omega⟩
      apply Relation.ReflTransGen.head step
      apply ih k kj inside
      intro m rm mk
      apply onlyOR m rm
      rcases mk with rfl | mk
      · exact Or.inr cone
      · exact Or.inr (coneTrans mk cone)

theorem liftJunk {g h t r : ℕ} (ao : IsAO2 n C) (form : TopForm G C)
    (both : junk G C = {g,h}) (inc : ¬ InCone n C g h ∧ ¬ InCone n C h g)
    (which : r = g ∨ r = h) (top : t ∈ tops G C) (rt : InCone n C r t) :
    ∃ b : Fin 2, OrReaches n C (opnd C t b) r := by
  classical
  obtain ⟨ht,k,kt,mem,inside⟩ := (inCone_iff n C r t).mp rt
  have into := (inCone_iff n C k t).mpr ⟨ht,k,kt,mem,Or.inl rfl⟩
  have path : Relation.ReflTransGen (OrStep n C) (n+k) (n+r) := by
    apply orPath inside
    intro m rm before
    have mt : InCone n C m t := before.elim (fun eq => eq ▸ into) (fun mk => coneTrans mk into)
    have hm := lt_trans (coneLt mt) ht
    rcases ao.1 _ (gateAt_mem hm) with isAnd | isOr
    · exfalso
      by_cases below : BelowF G C m
      · exact form m hm t ht isAnd below (Finset.mem_filter.mp top).2.1 mt
      · have witness : ∃ x, gateVal n C m x = true ∧ graphFun G ∅ x = false := by
          by_contra! no
          exact below (fun x hx => Bool.eq_true_of_not_eq_false (no x hx))
        have dirty : m ∈ junk G C := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hm,isAnd,hm,witness⟩
        rw [both] at dirty
        simp only [Finset.mem_insert,Finset.mem_singleton] at dirty
        have strict := coneLt rm
        rcases dirty with rfl | rfl <;> rcases which with rfl | rfl <;> first | omega | exact inc.1 rm | exact inc.2 rm
    · exact isOr
  have rr := reach_orReaches path r rfl (lt_trans (coneLt rt) ht)
  obtain ⟨p,q,eq⟩ := List.length_eq_two.mp (ao.2.2 _ (gateAt_mem ht))
  simp only [eq,List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with eqp | eqq
  · exact ⟨0,by simpa [opnd,eq,←eqp] using rr⟩
  · exact ⟨1,by simpa [opnd,eq,←eqq] using rr⟩

def silent (n : ℕ) (C : Circuit) (w : ℕ) : Prop := orIn n C w = ∅

theorem andSilent {g : ℕ} (andG : (gateAt C g).op = GateOp.and) : silent n C (n+g) := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u mem
  have path := mem_orIn_reach u mem
  rcases Relation.ReflTransGen.cases_head path with eq | ⟨_,st,_⟩
  · have lim := u.isLt; omega
  · obtain ⟨k,_,eq,op,_,_⟩ := st
    have same : k = g := by omega
    simp [same,andG] at op

theorem lastReader {w g : ℕ} (path : OrReaches n C w g) (different : w ≠ n+g) :
    ∃ j, OrReaches n C w j ∧ j < C.gates.length ∧ (gateAt C j).op = GateOp.or ∧
      n+g ∈ (gateAt C j).inputs ∧ g < j := by
  rcases Relation.ReflTransGen.cases_tail (orReaches_reach g w path).1 with eq | ⟨c,prior,st⟩
  · exact False.elim (different eq.symm)
  · obtain ⟨j,hj,rfl,op,mem,lt⟩ := st
    exact ⟨j,reach_orReaches prior j rfl hj,hj,op,mem,by omega⟩

def dirtyWire (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (w : ℕ) : Prop :=
  ∃ x, val C (List.ofFn x) w = true ∧ graphFun G ∅ x = false

theorem chargedReader (ao : IsAO2 n C) {j w : ℕ} (realJ : j < C.gates.length)
    (op : (gateAt C j).op = GateOp.or) (mem : w ∈ (gateAt C j).inputs)
    (dirty : dirtyWire G C w) (zero : silent n C w) : j ∈ orN G C \ lam G C := by
  classical
  obtain ⟨x,on,off⟩ := dirty
  have truth : gateVal n C j x = true :=
    (val_or (n:=n) (by simp) realJ op).mpr ⟨w,mem,ao.2.1 j realJ w mem,on⟩
  have nb : ¬ BelowF G C j := fun bel => by simpa [off] using bel x truth
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr realJ,op,nb⟩,?_⟩
  intro l
  obtain ⟨_,non0,non1,_⟩ := Finset.mem_filter.mp l
  obtain ⟨p,q,eq⟩ := List.length_eq_two.mp (ao.2.2 _ (gateAt_mem realJ))
  simp only [eq,List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl | rfl
  · have ep : opnd C j 0 = w := by simp [opnd,eq]
    rw [ep,show orIn n C w = ∅ from zero] at non0; exact Finset.not_nonempty_empty non0
  · have ep : opnd C j 1 = w := by simp [opnd,eq]
    rw [ep,show orIn n C w = ∅ from zero] at non1; exact Finset.not_nonempty_empty non1


theorem silentOr {j : ℕ} (allSilent : ∀ w ∈ (gateAt C j).inputs, silent n C w) : silent n C (n+j) := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u mem
  rcases Relation.ReflTransGen.cases_head (mem_orIn_reach u mem) with eq | ⟨w,st,path⟩
  · have small := u.isLt; omega
  · obtain ⟨k,_,e,_,hw,_⟩ := st
    have eq : k = j := by omega
    have hu := reach_mem_orIn u path
    rw [show orIn n C w = ∅ from allSilent w (eq ▸ hw)] at hu
    exact Finset.notMem_empty _ hu

theorem bothInput {j g h : ℕ} (ao : IsAO2 n C) (realJ : j < C.gates.length) (diff : g ≠ h)
    (mg : n+g ∈ (gateAt C j).inputs) (mh : n+h ∈ (gateAt C j).inputs) :
    ∀ w ∈ (gateAt C j).inputs, w = n+g ∨ w = n+h := by
  obtain ⟨p,q,eq⟩ := List.length_eq_two.mp (ao.2.2 _ (gateAt_mem realJ))
  simp only [eq,List.mem_cons,List.not_mem_nil,or_false] at mg mh ⊢
  omega

theorem jointCharge (ao : IsAO2 n C) (form : TopForm G C) {g h t : ℕ}
    (both : junk G C = {g,h}) (diff : g ≠ h) (inc : ¬ InCone n C g h ∧ ¬ InCone n C h g)
    (top : t ∈ tops G C) (gt : InCone n C g t) (ht : InCone n C h t) :
    2 ≤ 2 * (centreless G C).card + (orN G C \ lam G C).card := by
  by_cases ct : t ∈ centreless G C
  · have pos := Finset.card_pos.mpr ⟨t,ct⟩; omega
  · have lit (b : Fin 2) : ¬ silent n C (opnd C t b) := by
      intro ss
      apply ct; apply Finset.mem_filter.mpr; refine ⟨top,?_⟩
      fin_cases b
      · exact Or.inl ss
      · exact Or.inr ss
    obtain ⟨b,gb⟩ := liftJunk ao form both inc (Or.inl rfl) top gt
    obtain ⟨c,hc⟩ := liftJunk ao form both inc (Or.inr rfl) top ht
    have gm : g ∈ junk G C := by simp [both]
    have hm : h ∈ junk G C := by simp [both]
    obtain ⟨_,go,gdirty⟩ := junkFacts gm
    obtain ⟨_,ho,hdirty⟩ := junkFacts hm
    have sg : silent n C (n+g) := andSilent go
    have sh : silent n C (n+h) := andSilent ho
    obtain ⟨i,pi,ri,io,gi,_⟩ := lastReader gb (fun eq => lit b (eq ▸ sg))
    obtain ⟨j,_,rj,jo,hj,_⟩ := lastReader hc (fun eq => lit c (eq ▸ sh))
    have iP := chargedReader ao ri io gi gdirty sg
    have two (k : ℕ) (kP : k ∈ orN G C \ lam G C) (distinct : i ≠ k) :
        2 ≤ (orN G C \ lam G C).card :=
      Finset.one_lt_card.mpr ⟨i,iP,k,kP,distinct⟩
    by_cases same : i = j
    · subst j
      have si : silent n C (n+i) := by
        apply silentOr
        intro w hw
        exact (bothInput ao ri diff gi hj w hw).elim (fun e => e ▸ sg) (fun e => e ▸ sh)
      obtain ⟨k,_,rk,ko,ik,lt⟩ := lastReader pi (fun eq => lit b (eq ▸ si))
      have di : dirtyWire G C (n+i) := by
        obtain ⟨x,on,off⟩ := gdirty
        exact ⟨x,(val_or (n:=n) (by simp) ri io).mpr ⟨n+g,gi,ao.2.1 i ri _ gi,on⟩,off⟩
      have bound := two k (chargedReader ao rk ko ik di si) (Nat.ne_of_lt lt)
      omega
    · have bound := two j (chargedReader ao rj jo hj hdirty sh) same
      omega


theorem makeTop (ao : IsAO2 n C) {t : ℕ} (top : t ∈ tops G C) (b : Fin 2) (x : Fin n → Bool)
    (on : val C (List.ofFn x) (opnd C t b) = true)
    (other : val C (List.ofFn x) (opnd C t (1-b)) = true) : graphFun G ∅ x = true := by
  obtain ⟨realT,op,below⟩ := (show t < C.gates.length ∧ (gateAt C t).op = GateOp.and ∧ BelowF G C t by
    simpa only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range] using top)
  apply below x
  apply (andVal ao t realT op x).mpr
  intro p
  fin_cases b <;> fin_cases p <;> first | exact on | exact other

theorem onSide {t j : ℕ} {b : Fin 2} {x : Fin n → Bool}
    (read : OrReaches n C (opnd C t b) j) (on : gateVal n C j x = true) :
    val C (List.ofFn x) (opnd C t b) = true :=
  orStep_up (n:=n) (by simp) (orReaches_reach j _ read).1 on

def compatible (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (g h : ℕ) : Prop :=
  ∀ x, gateVal n C g x = true → gateVal n C h x = true → graphFun G ∅ x = true

def singleUse (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (j : ℕ) (u v : Fin n) : Prop :=
  gateVal n C j (pairInput u v) = true ∧ (u ∈ wmax G C j ∨ v ∈ wmax G C j)

theorem pairRoutes (ao : IsAO2 n C) (form : TopForm G C) {g h : ℕ}
    (both : junk G C = {g,h}) {u v : Fin n} {t j : ℕ}
    (top : t ∈ tops G C) (b : Fin 2) (who : j = g ∨ j = h)
    (fires : gateVal n C t (pairInput u v) = true) (uses : OrReaches n C (opnd C t b) j)
    (on : gateVal n C j (pairInput u v) = true) :
    singleUse G C g u v ∨ singleUse G C h u v ∨
      (compatible G C g h ∧ gateVal n C g (pairInput u v) = true ∧ gateVal n C h (pairInput u v) = true) := by
  obtain ⟨rt,op,_⟩ := (show t < C.gates.length ∧ (gateAt C t).op = GateOp.and ∧ BelowF G C t by
    simpa only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range] using top)
  have opp := (andVal ao t rt op _).mp fires (1-b)
  rcases (operandSources ao form rt op _ _).mp opp with ⟨w,mem,wx⟩ | ⟨k,kin,reads,_,kOn⟩
  · have can : w ∈ wmax G C j := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
      intro x yes raw
      exact makeTop ao top b x (onSide uses yes) (reach_var_val x _ w (mem_orIn_reach w mem) raw)
    have side : u ∈ wmax G C j ∨ v ∈ wmax G C j := by
      rcases (pairInput_true u v w).mp wx with e | e
      · subst w; exact Or.inl can
      · subst w; exact Or.inr can
    rcases who with rfl | rfl
    · exact Or.inl ⟨on,side⟩
    · exact Or.inr (Or.inl ⟨on,side⟩)
  · have safe : compatible G C j k := fun x jy ky => makeTop ao top b x (onSide uses jy) (onSide reads ky)
    have jm : j ∈ junk G C := by rw [both]; simpa using who
    have distinct : j ≠ k := by
      intro e; subst k
      obtain ⟨_,_,x,jx,no⟩ := junkFacts jm
      simpa [no] using safe x jx jx
    rw [both] at kin
    simp only [Finset.mem_insert,Finset.mem_singleton] at kin
    rcases who with rfl | rfl <;> rcases kin with rfl | rfl
    · contradiction
    · exact Or.inr (Or.inr ⟨safe,on,kOn⟩)
    · exact Or.inr (Or.inr ⟨fun x a b => safe x b a,kOn,on⟩)
    · contradiction

theorem allOnWire (ao : IsAO2 n C) (w : ℕ) (realW : w < n + C.gates.length) :
    val C (List.ofFn (fun _ : Fin n => true)) w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases raw : w < n
    · exact val_ofFn C (fun _ => true) ⟨w,raw⟩
    · let j := w - n
      have ew : w = n+j := by dsimp [j]; omega
      have hj : j < C.gates.length := by omega
      have prev : ∀ i ∈ (gateAt C j).inputs, i < n+j ∧ val C (List.ofFn (fun _ : Fin n => true)) i = true := by
        intro i mem
        have lt := ao.2.1 j hj i mem
        exact ⟨lt,ih i (by omega) (by omega)⟩
      rw [ew]
      rcases ao.1 _ (gateAt_mem hj) with op | op
      · exact (val_and (by simp) hj op).mpr prev
      · exact (val_or (by simp) hj op).mpr ⟨_,operandMem ao j hj 0,prev _ (operandMem ao j hj 0)⟩

/-- At a common top either the two gates may safely fire together, or the same raw
vertex is safe to conjoin with each of them on every Boolean assignment. -/
theorem commonAlternatives (ao : IsAO2 n C) (form : TopForm G C) {g h t : ℕ}
    (both : junk G C = {g,h}) (inc : ¬ InCone n C g h ∧ ¬ InCone n C h g)
    (top : t ∈ tops G C) (gt : InCone n C g t) (ht : InCone n C h t) :
    compatible G C g h ∨ ∃ u, u ∈ wmax G C g ∧ u ∈ wmax G C h := by
  obtain ⟨b,gb⟩ := liftJunk ao form both inc (Or.inl rfl) top gt
  obtain ⟨c,hc⟩ := liftJunk ao form both inc (Or.inr rfl) top ht
  by_cases eq : c = b
  · subst c
    right
    obtain ⟨rt,op,_⟩ := (show t < C.gates.length ∧ (gateAt C t).op = GateOp.and ∧ BelowF G C t by
      simpa only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range] using top)
    have lt := ao.2.1 t rt _ (operandMem ao t rt (1-b))
    have on := allOnWire ao (opnd C t (1-b)) (by omega)
    rcases (operandSources ao form rt op (1-b) _).mp on with ⟨u,mem,_⟩ | ⟨k,kin,ko,_,_⟩
    · have safe {j} (jb : OrReaches n C (opnd C t b) j) : u ∈ wmax G C j := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
        exact fun x jy xu => makeTop ao top b x (onSide jb jy) (reach_var_val x _ u (mem_orIn_reach u mem) xu)
      exact ⟨u,safe gb,safe hc⟩
    · obtain ⟨_,_,x,kx,no⟩ := junkFacts kin
      rw [both] at kin
      simp only [Finset.mem_insert,Finset.mem_singleton] at kin
      have kb : OrReaches n C (opnd C t b) k := kin.elim (fun e => e ▸ gb) (fun e => e ▸ hc)
      have yes := makeTop ao top b x (onSide kb kx) (onSide ko kx)
      simp [no] at yes
  · left
    have other : c = 1-b := by fin_cases b <;> fin_cases c <;> first | exact False.elim (eq rfl) | decide
    rw [other] at hc
    exact fun x gx hx => makeTop ao top b x (onSide gb gx) (onSide hc hx)

theorem directRead (ao : IsAO2 n C) {j w : ℕ} (mem : j ∈ junk G C)
    (none : (orN G C \ lam G C).card = 0) (read : OrReaches n C w j) : w = n+j := by
  by_contra different
  obtain ⟨_,op,dirty⟩ := junkFacts mem
  obtain ⟨k,_,rk,ko,jk,_⟩ := lastReader read different
  have pays := chargedReader ao rk ko jk dirty (andSilent op)
  have pos := Finset.card_pos.mpr ⟨k,pays⟩
  omega

theorem directCentreless {t j : ℕ} (top : t ∈ tops G C) (b : Fin 2) (jm : j ∈ junk G C)
    (direct : opnd C t b = n+j) : t ∈ centreless G C := by
  obtain ⟨_,op,_⟩ := junkFacts jm
  have ss : side (n:=n) C t b = ∅ := by
    change orIn n C (opnd C t b) = ∅
    rw [direct]; exact andSilent op
  apply Finset.mem_filter.mpr
  refine ⟨top,?_⟩
  fin_cases b
  · exact Or.inl ss
  · exact Or.inr ss

theorem uncoveredBoth (ao : IsAO2 n C) (form : TopForm G C) {g h : ℕ} (diff : g ≠ h)
    (both : junk G C = {g,h}) (inc : ¬ InCone n C g h ∧ ¬ InCone n C h g)
    (joint : ∃ t ∈ tops G C, InCone n C g t ∧ InCone n C h t)
    (one : (centreless G C).card = 1) (none : (orN G C \ lam G C).card = 0)
    {u v : Fin n} (routed : ∃ t ∈ tops G C, ∃ (b : Fin 2) (j : ℕ), (j = g ∨ j = h) ∧
      gateVal n C t (pairInput u v) = true ∧ OrReaches n C (opnd C t b) j ∧
      gateVal n C j (pairInput u v) = true) :
    compatible G C g h ∧ gateVal n C g (pairInput u v) = true ∧ gateVal n C h (pairInput u v) = true := by
  obtain ⟨t,top,gt,ht⟩ := joint
  have gm : g ∈ junk G C := by simp [both]
  have hm : h ∈ junk G C := by simp [both]
  obtain ⟨b,gb⟩ := liftJunk ao form both inc (Or.inl rfl) top gt
  obtain ⟨c,hc⟩ := liftJunk ao form both inc (Or.inr rfl) top ht
  have gd := directRead ao gm none gb
  have hd := directRead ao hm none hc
  have neq : c ≠ b := by intro same; subst c; omega
  have opp : c = 1-b := by fin_cases b <;> fin_cases c <;> first | exact False.elim (neq rfl) | decide
  have safe : compatible G C g h := by
    rw [opp] at hc
    exact fun x gy hy => makeTop ao top b x (onSide gb gy) (onSide hc hy)
  obtain ⟨a,atop,d,j,who,fires,reads,_⟩ := routed
  have jm : j ∈ junk G C := by rw [both]; simpa using who
  have ac := directCentreless atop d jm (directRead ao jm none reads)
  have tc := directCentreless top b gm gd
  obtain ⟨only,honly⟩ := Finset.card_eq_one.mp one
  rw [honly,Finset.mem_singleton] at ac tc
  have same : a = t := ac.trans tc.symm
  rw [same] at fires
  obtain ⟨rt,op,_⟩ := (show t < C.gates.length ∧ (gateAt C t).op = GateOp.and ∧ BelowF G C t by
    simpa only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range] using top)
  have on := (andVal ao t rt op _).mp fires
  have og := on b
  have oh := on c
  rw [gd] at og
  rw [hd] at oh
  exact ⟨safe,og,oh⟩

abbrev graph11 : SimpleGraph (Fin 11) := edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]

/-- The two triangles and five-cycle give the cover lower bound as in R-meta-1597-318. -/
theorem coverSeven : ∀ K : Finset (Fin 11), graph11.IsVertexCover (K : Set (Fin 11)) → 7 ≤ K.card := by
    intro K hK
    classical
    let w (i : Fin 11) : ℕ := if i ∈ K then 1 else 0
    have ew (u v : Fin 11) (he : graph11.Adj u v) : 1 ≤ w u + w v := by
      rcases hK he with hu | hv
      · change u ∈ K at hu
        simp [w, hu]
      · change v ∈ K at hv
        simp [w, hv]
    have e0 := ew 1 4 (by decide +kernel)
    have e1 := ew 4 8 (by decide +kernel)
    have e2 := ew 8 1 (by decide +kernel)
    have e3 := ew 3 6 (by decide +kernel)
    have e4 := ew 6 7 (by decide +kernel)
    have e5 := ew 7 3 (by decide +kernel)
    have e6 := ew 0 9 (by decide +kernel)
    have e7 := ew 9 5 (by decide +kernel)
    have e8 := ew 5 2 (by decide +kernel)
    have e9 := ew 2 10 (by decide +kernel)
    have e10 := ew 10 0 (by decide +kernel)
    have hw : ∑ i, w i = K.card := by
      simp [w]
    rw [Fin.sum_univ_succ] at hw
    simp [Fin.sum_univ_succ] at hw
    omega

theorem residualCover (U : Finset (Sym2 (Fin 11))) :
    ∃ K : Finset (Fin 11), IsMinCover (graph11.deleteEdges ↑U) K ∧ 7 ≤ K.card + U.card := by
  classical
  let H := graph11.deleteEdges (↑U)
  let P (m : ℕ) := ∃ K : Finset (Fin 11), H.IsVertexCover (↑K) ∧ K.card = m
  have existsP : ∃ m, P m := ⟨_, Finset.univ, by simp [H], rfl⟩
  obtain ⟨K, hK, hcard⟩ := Nat.find_spec existsP
  have hmin : IsMinCover H K := by
    refine ⟨hK, fun T hT => ?_⟩
    exact hcard.trans_le (Nat.find_min' existsP ⟨T,hT,rfl⟩)
  let X := U.image (fun e => e.out.1)
  have hx : X.card ≤ U.card := Finset.card_image_le
  have hc : graph11.IsVertexCover (↑(K ∪ X)) := by
    intro u v huv
    by_cases eh : s(u,v) ∈ U
    · have vx : s(u,v).out.1 ∈ X := Finset.mem_image_of_mem _ eh
      have pick := Sym2.out_fst_mem s(u,v)
      rw [Sym2.mem_iff] at pick
      rcases pick with p | p
      · exact Or.inl (Finset.mem_union_right _ (p ▸ vx))
      · exact Or.inr (Finset.mem_union_right _ (p ▸ vx))
    · exact (hK (SimpleGraph.deleteEdges_adj.mpr ⟨huv,eh⟩ : H.Adj u v)).imp
          (Finset.mem_union_left _) (Finset.mem_union_left _)
  have tot := coverSeven _ hc
  have unionLe := Finset.card_union_le K X
  exact ⟨K,hmin,by omega⟩

theorem residualBound [d : DecidableRel graph11.Adj] (C : Circuit) {g h : ℕ} (least : IsLeastAO graph11 C)
    (form : TopForm graph11 C) (diff : g < h) (both : junk graph11 C = {g,h})
    (inc : ¬ InCone 11 C g h ∧ ¬ InCone 11 C h g)
    (joint : ∃ t ∈ tops graph11 C, InCone 11 C g t ∧ InCone 11 C h t)
    (budget : 17 + (tops graph11 C \ centreless graph11 C).card + 2 * (centreless graph11 C).card +
        (orN graph11 C \ lam graph11 C).card ≤ C.size + (Ustar graph11 C).card)
    (cover : ∀ K : Finset (Fin 11), IsMinCover (graph11.deleteEdges ↑(Ustar graph11 C)) K →
      K.card ≤ (tops graph11 C \ centreless graph11 C).card) :
    26 ≤ C.size + 2 * (Ustar graph11 C).card := by
  obtain ⟨t,ht,gt,ht'⟩ := joint
  have two := jointCharge least.1 form both (Nat.ne_of_lt diff) inc ht gt ht'
  obtain ⟨K,min,Kbound⟩ := residualCover (Ustar graph11 C)
  have card := cover K min
  omega

abbrev Vertex := Fin 11
abbrev EdgeId := Fin 16

def ends : EdgeId → Vertex × Vertex := ![(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
def undirected (i : EdgeId) : Sym2 Vertex := s((ends i).1,(ends i).2)

def masks : List (Finset EdgeId) := [
  {0, 2},
  {2, 4},
  {0, 6},
  {2, 6},
  {3, 6},
  {4, 6},
  {1, 7},
  {2, 7},
  {3, 7},
  {4, 7},
  {6, 8},
  {7, 8},
  {2, 12},
  {3, 12},
  {4, 12},
  {8, 12},
  {0, 1, 5},
  {1, 3, 5},
  {1, 4, 5},
  {2, 3, 8},
  {1, 2, 9},
  {2, 5, 9},
  {1, 3, 10},
  {3, 4, 10},
  {4, 8, 10},
  {0, 1, 11},
  {0, 4, 11},
  {4, 5, 11},
  {2, 9, 11},
  {6, 7, 12},
  {1, 6, 13},
  {5, 6, 13},
  {6, 11, 13},
  {1, 12, 13},
  {0, 7, 14},
  {5, 7, 14},
  {7, 11, 14},
  {0, 12, 14},
  {0, 3, 15},
  {3, 5, 15},
  {0, 8, 15},
  {1, 5, 8, 9},
  {1, 8, 9, 10},
  {5, 12, 13, 14},
  {11, 12, 13, 14},
  {5, 8, 9, 15},
  {3, 10, 11, 15},
  {8, 9, 10, 11, 15}]

def inside (S : Finset Vertex) (i : EdgeId) : Prop := (ends i).1 ∈ S ∧ (ends i).2 ∈ S
instance (S : Finset Vertex) (i : EdgeId) : Decidable (inside S i) := by unfold inside; infer_instance

theorem endsAdjacent : ∀ i : EdgeId, graph11.Adj (ends i).1 (ends i).2 := by decide +kernel


private def hitMask (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Bool) : Bool :=
    ((x0 && (x1 && (x4 && x9))) ||
    ((x1 && (x2 && (x4 && x5))) ||
    ((x0 && (x3 && (x6 && x9))) ||
    ((x1 && (x3 && (x4 && x6))) ||
    ((x1 && (x3 && (x6 && x8))) ||
    ((x2 && (x3 && (x5 && x6))) ||
    ((x0 && (x3 && (x7 && x10))) ||
    ((x1 && (x3 && (x4 && x7))) ||
    ((x1 && (x3 && (x7 && x8))) ||
    ((x2 && (x3 && (x5 && x7))) ||
    ((x3 && (x4 && (x6 && x8))) ||
    ((x3 && (x4 && (x7 && x8))) ||
    ((x1 && (x4 && (x6 && x7))) ||
    ((x1 && (x6 && (x7 && x8))) ||
    ((x2 && (x5 && (x6 && x7))) ||
    ((x4 && (x6 && (x7 && x8))) ||
    ((x0 && (x2 && (x9 && x10))) ||
    ((x0 && (x1 && (x2 && (x8 && x10)))) ||
    ((x0 && (x2 && (x5 && x10))) ||
    ((x1 && (x4 && x8)) ||
    ((x0 && (x1 && (x4 && x10))) ||
    ((x1 && (x2 && (x4 && x10))) ||
    ((x0 && (x1 && (x5 && (x8 && x10)))) ||
    ((x1 && (x2 && (x5 && x8))) ||
    ((x2 && (x4 && (x5 && x8))) ||
    ((x0 && (x5 && (x9 && x10))) ||
    ((x0 && (x2 && (x5 && x9))) ||
    ((x2 && (x5 && (x9 && x10))) ||
    ((x1 && (x4 && (x5 && (x9 && x10)))) ||
    ((x3 && (x6 && x7)) ||
    ((x0 && (x3 && (x6 && x10))) ||
    ((x2 && (x3 && (x6 && x10))) ||
    ((x3 && (x5 && (x6 && (x9 && x10)))) ||
    ((x0 && (x6 && (x7 && x10))) ||
    ((x0 && (x3 && (x7 && x9))) ||
    ((x2 && (x3 && (x7 && (x9 && x10)))) ||
    ((x3 && (x5 && (x7 && x9))) ||
    ((x0 && (x6 && (x7 && x9))) ||
    ((x0 && (x1 && (x8 && x9))) ||
    ((x1 && (x2 && (x8 && (x9 && x10)))) ||
    ((x0 && (x4 && (x8 && x9))) ||
    ((x0 && (x2 && (x4 && (x8 && x10)))) ||
    ((x0 && (x4 && (x5 && (x8 && x10)))) ||
    ((x2 && (x6 && (x7 && (x9 && x10)))) ||
    ((x5 && (x6 && (x7 && (x9 && x10)))) ||
    ((x2 && (x4 && (x8 && (x9 && x10)))) ||
    ((x1 && (x5 && (x8 && x9))) ||
    (x4 && (x5 && (x8 && (x9 && x10)))))))))))))))))))))))))))))))))))))))))))))))))))

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
private theorem coverBits : ∀ (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Bool),
    ((if x0 then (1 : ℕ) else 0) + ((if x1 then (1 : ℕ) else 0) + ((if x2 then (1 : ℕ) else 0) + ((if x3 then (1 : ℕ) else 0) + ((if x4 then (1 : ℕ) else 0) + ((if x5 then (1 : ℕ) else 0) + ((if x6 then (1 : ℕ) else 0) + ((if x7 then (1 : ℕ) else 0) + ((if x8 then (1 : ℕ) else 0) + ((if x9 then (1 : ℕ) else 0) + ((if x10 then (1 : ℕ) else 0) + 0))))))))))) = 6 → hitMask x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 = true := by decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 5000000 in
theorem sixWitness : ∀ S ∈ (Finset.univ : Finset Vertex).powersetCard 6,
    ∃ A ∈ masks, ∀ i ∈ A, inside S i := by
  intro S mem
  have n := (Finset.mem_powersetCard.mp mem).2
  have cnt : (∑ i : Vertex, if i ∈ S then (1 : ℕ) else 0) = 6 := by
    rw [← Finset.card_eq_sum_ite (Finset.subset_univ S)]; exact n
  simp only [Fin.sum_univ_succ,Finset.univ_eq_empty,Finset.sum_empty] at cnt
  rw [show (((((((((((0 : Fin 1)).succ).succ).succ).succ).succ).succ).succ).succ).succ).succ = 10 by decide] at cnt
  rw [show ((((((((((0 : Fin 2)).succ).succ).succ).succ).succ).succ).succ).succ).succ = 9 by decide] at cnt
  rw [show (((((((((0 : Fin 3)).succ).succ).succ).succ).succ).succ).succ).succ = 8 by decide] at cnt
  rw [show ((((((((0 : Fin 4)).succ).succ).succ).succ).succ).succ).succ = 7 by decide] at cnt
  rw [show (((((((0 : Fin 5)).succ).succ).succ).succ).succ).succ = 6 by decide] at cnt
  rw [show ((((((0 : Fin 6)).succ).succ).succ).succ).succ = 5 by decide] at cnt
  rw [show (((((0 : Fin 7)).succ).succ).succ).succ = 4 by decide] at cnt
  rw [show ((((0 : Fin 8)).succ).succ).succ = 3 by decide] at cnt
  rw [show (((0 : Fin 9)).succ).succ = 2 by decide] at cnt
  rw [show ((0 : Fin 10)).succ = 1 by decide] at cnt

  have good := coverBits (decide ((0 : Vertex) ∈ S)) (decide ((1 : Vertex) ∈ S)) (decide ((2 : Vertex) ∈ S)) (decide ((3 : Vertex) ∈ S)) (decide ((4 : Vertex) ∈ S)) (decide ((5 : Vertex) ∈ S)) (decide ((6 : Vertex) ∈ S)) (decide ((7 : Vertex) ∈ S)) (decide ((8 : Vertex) ∈ S)) (decide ((9 : Vertex) ∈ S)) (decide ((10 : Vertex) ∈ S)) (by simpa only [decide_eq_true_eq] using cnt)
  simp only [hitMask,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at good
  rcases good with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · obtain ⟨v0, v1, v4, v9⟩ := h
    refine ⟨({0, 2} : Finset EdgeId),by decide +kernel,?_⟩
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact ⟨v0,v9⟩
    · exact ⟨v1,v4⟩
  · obtain ⟨v1, v2, v4, v5⟩ := h
    refine ⟨({2, 4} : Finset EdgeId),by decide +kernel,?_⟩
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact ⟨v1,v4⟩
    · exact ⟨v2,v5⟩
  · obtain ⟨v0, v3, v6, v9⟩ := h
    refine ⟨({0, 6} : Finset EdgeId),by decide +kernel,?_⟩
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact ⟨v0,v9⟩
    · exact ⟨v3,v6⟩
  · obtain ⟨v1, v3, v4, v6⟩ := h
    refine ⟨({2, 6} : Finset EdgeId),by decide +kernel,?_⟩
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact ⟨v1,v4⟩
    · exact ⟨v3,v6⟩
  · obtain ⟨v1, v3, v6, v8⟩ := h
    refine ⟨({3, 6} : Finset EdgeId),by decide +kernel,?_⟩
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact ⟨v1,v8⟩
    · exact ⟨v3,v6⟩
  · obtain ⟨v2, v3, v5, v6⟩ := h
    refine ⟨({4, 6} : Finset EdgeId),by decide +kernel,?_⟩
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact ⟨v2,v5⟩
    · exact ⟨v3,v6⟩
  · obtain ⟨v0, v3, v7, v10⟩ := h
    refine ⟨({1, 7} : Finset EdgeId),by decide +kernel,?_⟩
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact ⟨v0,v10⟩
    · exact ⟨v3,v7⟩
  · obtain ⟨v1, v3, v4, v7⟩ := h
    refine ⟨({2, 7} : Finset EdgeId),by decide +kernel,?_⟩
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact ⟨v1,v4⟩
    · exact ⟨v3,v7⟩
  · obtain ⟨v1, v3, v7, v8⟩ := h
    refine ⟨({3, 7} : Finset EdgeId),by decide +kernel,?_⟩
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact ⟨v1,v8⟩
    · exact ⟨v3,v7⟩
  · obtain ⟨v2, v3, v5, v7⟩ := h
    refine ⟨({4, 7} : Finset EdgeId),by decide +kernel,?_⟩
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact ⟨v2,v5⟩
    · exact ⟨v3,v7⟩
  · obtain ⟨v3, v4, v6, v8⟩ := h
    refine ⟨({6, 8} : Finset EdgeId),by decide +kernel,?_⟩
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact ⟨v3,v6⟩
    · exact ⟨v4,v8⟩
  · obtain ⟨v3, v4, v7, v8⟩ := h
    refine ⟨({7, 8} : Finset EdgeId),by decide +kernel,?_⟩
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact ⟨v3,v7⟩
    · exact ⟨v4,v8⟩
  · obtain ⟨v1, v4, v6, v7⟩ := h
    refine ⟨({2, 12} : Finset EdgeId),by decide +kernel,?_⟩
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact ⟨v1,v4⟩
    · exact ⟨v6,v7⟩
  · obtain ⟨v1, v6, v7, v8⟩ := h
    refine ⟨({3, 12} : Finset EdgeId),by decide +kernel,?_⟩
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact ⟨v1,v8⟩
    · exact ⟨v6,v7⟩
  · obtain ⟨v2, v5, v6, v7⟩ := h
    refine ⟨({4, 12} : Finset EdgeId),by decide +kernel,?_⟩
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact ⟨v2,v5⟩
    · exact ⟨v6,v7⟩
  · obtain ⟨v4, v6, v7, v8⟩ := h
    refine ⟨({8, 12} : Finset EdgeId),by decide +kernel,?_⟩
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact ⟨v4,v8⟩
    · exact ⟨v6,v7⟩
  · obtain ⟨v0, v2, v9, v10⟩ := h
    refine ⟨({0, 1, 5} : Finset EdgeId),by decide +kernel,?_⟩
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact ⟨v0,v9⟩
    · exact ⟨v0,v10⟩
    · exact ⟨v2,v10⟩
  · obtain ⟨v0, v1, v2, v8, v10⟩ := h
    refine ⟨({1, 3, 5} : Finset EdgeId),by decide +kernel,?_⟩
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact ⟨v0,v10⟩
    · exact ⟨v1,v8⟩
    · exact ⟨v2,v10⟩
  · obtain ⟨v0, v2, v5, v10⟩ := h
    refine ⟨({1, 4, 5} : Finset EdgeId),by decide +kernel,?_⟩
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact ⟨v0,v10⟩
    · exact ⟨v2,v5⟩
    · exact ⟨v2,v10⟩
  · obtain ⟨v1, v4, v8⟩ := h
    refine ⟨({2, 3, 8} : Finset EdgeId),by decide +kernel,?_⟩
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact ⟨v1,v4⟩
    · exact ⟨v1,v8⟩
    · exact ⟨v4,v8⟩
  · obtain ⟨v0, v1, v4, v10⟩ := h
    refine ⟨({1, 2, 9} : Finset EdgeId),by decide +kernel,?_⟩
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact ⟨v0,v10⟩
    · exact ⟨v1,v4⟩
    · exact ⟨v4,v10⟩
  · obtain ⟨v1, v2, v4, v10⟩ := h
    refine ⟨({2, 5, 9} : Finset EdgeId),by decide +kernel,?_⟩
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact ⟨v1,v4⟩
    · exact ⟨v2,v10⟩
    · exact ⟨v4,v10⟩
  · obtain ⟨v0, v1, v5, v8, v10⟩ := h
    refine ⟨({1, 3, 10} : Finset EdgeId),by decide +kernel,?_⟩
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact ⟨v0,v10⟩
    · exact ⟨v1,v8⟩
    · exact ⟨v5,v8⟩
  · obtain ⟨v1, v2, v5, v8⟩ := h
    refine ⟨({3, 4, 10} : Finset EdgeId),by decide +kernel,?_⟩
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact ⟨v1,v8⟩
    · exact ⟨v2,v5⟩
    · exact ⟨v5,v8⟩
  · obtain ⟨v2, v4, v5, v8⟩ := h
    refine ⟨({4, 8, 10} : Finset EdgeId),by decide +kernel,?_⟩
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact ⟨v2,v5⟩
    · exact ⟨v4,v8⟩
    · exact ⟨v5,v8⟩
  · obtain ⟨v0, v5, v9, v10⟩ := h
    refine ⟨({0, 1, 11} : Finset EdgeId),by decide +kernel,?_⟩
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact ⟨v0,v9⟩
    · exact ⟨v0,v10⟩
    · exact ⟨v5,v9⟩
  · obtain ⟨v0, v2, v5, v9⟩ := h
    refine ⟨({0, 4, 11} : Finset EdgeId),by decide +kernel,?_⟩
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact ⟨v0,v9⟩
    · exact ⟨v2,v5⟩
    · exact ⟨v5,v9⟩
  · obtain ⟨v2, v5, v9, v10⟩ := h
    refine ⟨({4, 5, 11} : Finset EdgeId),by decide +kernel,?_⟩
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact ⟨v2,v5⟩
    · exact ⟨v2,v10⟩
    · exact ⟨v5,v9⟩
  · obtain ⟨v1, v4, v5, v9, v10⟩ := h
    refine ⟨({2, 9, 11} : Finset EdgeId),by decide +kernel,?_⟩
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact ⟨v1,v4⟩
    · exact ⟨v4,v10⟩
    · exact ⟨v5,v9⟩
  · obtain ⟨v3, v6, v7⟩ := h
    refine ⟨({6, 7, 12} : Finset EdgeId),by decide +kernel,?_⟩
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact ⟨v3,v6⟩
    · exact ⟨v3,v7⟩
    · exact ⟨v6,v7⟩
  · obtain ⟨v0, v3, v6, v10⟩ := h
    refine ⟨({1, 6, 13} : Finset EdgeId),by decide +kernel,?_⟩
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact ⟨v0,v10⟩
    · exact ⟨v3,v6⟩
    · exact ⟨v6,v10⟩
  · obtain ⟨v2, v3, v6, v10⟩ := h
    refine ⟨({5, 6, 13} : Finset EdgeId),by decide +kernel,?_⟩
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact ⟨v2,v10⟩
    · exact ⟨v3,v6⟩
    · exact ⟨v6,v10⟩
  · obtain ⟨v3, v5, v6, v9, v10⟩ := h
    refine ⟨({6, 11, 13} : Finset EdgeId),by decide +kernel,?_⟩
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact ⟨v3,v6⟩
    · exact ⟨v5,v9⟩
    · exact ⟨v6,v10⟩
  · obtain ⟨v0, v6, v7, v10⟩ := h
    refine ⟨({1, 12, 13} : Finset EdgeId),by decide +kernel,?_⟩
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact ⟨v0,v10⟩
    · exact ⟨v6,v7⟩
    · exact ⟨v6,v10⟩
  · obtain ⟨v0, v3, v7, v9⟩ := h
    refine ⟨({0, 7, 14} : Finset EdgeId),by decide +kernel,?_⟩
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact ⟨v0,v9⟩
    · exact ⟨v3,v7⟩
    · exact ⟨v7,v9⟩
  · obtain ⟨v2, v3, v7, v9, v10⟩ := h
    refine ⟨({5, 7, 14} : Finset EdgeId),by decide +kernel,?_⟩
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact ⟨v2,v10⟩
    · exact ⟨v3,v7⟩
    · exact ⟨v7,v9⟩
  · obtain ⟨v3, v5, v7, v9⟩ := h
    refine ⟨({7, 11, 14} : Finset EdgeId),by decide +kernel,?_⟩
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact ⟨v3,v7⟩
    · exact ⟨v5,v9⟩
    · exact ⟨v7,v9⟩
  · obtain ⟨v0, v6, v7, v9⟩ := h
    refine ⟨({0, 12, 14} : Finset EdgeId),by decide +kernel,?_⟩
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact ⟨v0,v9⟩
    · exact ⟨v6,v7⟩
    · exact ⟨v7,v9⟩
  · obtain ⟨v0, v1, v8, v9⟩ := h
    refine ⟨({0, 3, 15} : Finset EdgeId),by decide +kernel,?_⟩
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact ⟨v0,v9⟩
    · exact ⟨v1,v8⟩
    · exact ⟨v8,v9⟩
  · obtain ⟨v1, v2, v8, v9, v10⟩ := h
    refine ⟨({3, 5, 15} : Finset EdgeId),by decide +kernel,?_⟩
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact ⟨v1,v8⟩
    · exact ⟨v2,v10⟩
    · exact ⟨v8,v9⟩
  · obtain ⟨v0, v4, v8, v9⟩ := h
    refine ⟨({0, 8, 15} : Finset EdgeId),by decide +kernel,?_⟩
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact ⟨v0,v9⟩
    · exact ⟨v4,v8⟩
    · exact ⟨v8,v9⟩
  · obtain ⟨v0, v2, v4, v8, v10⟩ := h
    refine ⟨({1, 5, 8, 9} : Finset EdgeId),by decide +kernel,?_⟩
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact ⟨v0,v10⟩
    · exact ⟨v2,v10⟩
    · exact ⟨v4,v8⟩
    · exact ⟨v4,v10⟩
  · obtain ⟨v0, v4, v5, v8, v10⟩ := h
    refine ⟨({1, 8, 9, 10} : Finset EdgeId),by decide +kernel,?_⟩
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact ⟨v0,v10⟩
    · exact ⟨v4,v8⟩
    · exact ⟨v4,v10⟩
    · exact ⟨v5,v8⟩
  · obtain ⟨v2, v6, v7, v9, v10⟩ := h
    refine ⟨({5, 12, 13, 14} : Finset EdgeId),by decide +kernel,?_⟩
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact ⟨v2,v10⟩
    · exact ⟨v6,v7⟩
    · exact ⟨v6,v10⟩
    · exact ⟨v7,v9⟩
  · obtain ⟨v5, v6, v7, v9, v10⟩ := h
    refine ⟨({11, 12, 13, 14} : Finset EdgeId),by decide +kernel,?_⟩
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact ⟨v5,v9⟩
    · exact ⟨v6,v7⟩
    · exact ⟨v6,v10⟩
    · exact ⟨v7,v9⟩
  · obtain ⟨v2, v4, v8, v9, v10⟩ := h
    refine ⟨({5, 8, 9, 15} : Finset EdgeId),by decide +kernel,?_⟩
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact ⟨v2,v10⟩
    · exact ⟨v4,v8⟩
    · exact ⟨v4,v10⟩
    · exact ⟨v8,v9⟩
  · obtain ⟨v1, v5, v8, v9⟩ := h
    refine ⟨({3, 10, 11, 15} : Finset EdgeId),by decide +kernel,?_⟩
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact ⟨v1,v8⟩
    · exact ⟨v5,v8⟩
    · exact ⟨v5,v9⟩
    · exact ⟨v8,v9⟩
  · obtain ⟨v4, v5, v8, v9, v10⟩ := h
    refine ⟨({8, 9, 10, 11, 15} : Finset EdgeId),by decide +kernel,?_⟩
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl
    · exact ⟨v4,v8⟩
    · exact ⟨v4,v10⟩
    · exact ⟨v5,v8⟩
    · exact ⟨v5,v9⟩
    · exact ⟨v8,v9⟩
def edgeIds (U : Finset (Sym2 Vertex)) : Finset EdgeId :=
  Finset.univ.filter fun i => undirected i ∈ U

/-- Every residual vertex cover of size at most five forces one of 48 explicit edge subsets. -/
theorem smallCoverMask (U : Finset (Sym2 Vertex)) (K : Finset Vertex)
    (cover : (graph11.deleteEdges ↑U).IsVertexCover (↑K)) (small : K.card ≤ 5) :
    ∃ A ∈ masks, A ⊆ edgeIds U := by
  have size : 6 ≤ Kᶜ.card := by rw [Finset.card_compl]; simp; omega
  obtain ⟨S,sub,six⟩ := Finset.exists_subset_card_eq size
  obtain ⟨A,am,hit⟩ := sixWitness S (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,six⟩)
  refine ⟨A,am,?_⟩
  intro i im
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  by_contra miss
  have el : s((ends i).1,(ends i).2) ∉ U := miss
  have covered := cover (SimpleGraph.deleteEdges_adj.mpr ⟨endsAdjacent i,el⟩)
  obtain ⟨x,y⟩ := hit i im
  exact covered.elim (Finset.mem_compl.mp (sub x)) (Finset.mem_compl.mp (sub y))

def allowedTriples : Finset (Finset EdgeId) :=
  ((Finset.univ : Finset EdgeId).powersetCard 3).filter fun U => ∃ A ∈ masks, A ⊆ U

theorem tripleTotal : ((Finset.univ : Finset EdgeId).powersetCard 3).card = 560 := by
  rw [Finset.card_powersetCard]; decide

theorem allEdgesIndexed : ∀ u v : Vertex, graph11.Adj u v → ∃ i : EdgeId, undirected i = s(u,v) := by decide +kernel

theorem indexInj : Function.Injective undirected := by
  change ∀ i j : EdgeId, undirected i = undirected j → i = j
  decide +kernel

theorem edgeIdCard (U : Finset (Sym2 Vertex)) (valid : ∀ e ∈ U, e ∈ graph11.edgeSet) :
    (edgeIds U).card = U.card := by
  have eq : (edgeIds U).image undirected = U := by
    ext e
    constructor
    · intro em
      obtain ⟨i,mem,rfl⟩ := Finset.mem_image.mp em
      exact (Finset.mem_filter.mp mem).2
    · induction e using Sym2.inductionOn with
      | _ u v =>
        intro em
        obtain ⟨i,hi⟩ := allEdgesIndexed u v (valid _ em)
        exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi.symm ▸ em⟩,hi⟩
  exact (Finset.card_image_of_injective _ indexInj).symm.trans (congrArg Finset.card eq)

theorem tripleConstraint [d : DecidableRel graph11.Adj] (C : Circuit) {g h : ℕ}
    (least : IsLeastAO graph11 C) (form : TopForm graph11 C) (diff : g < h)
    (both : junk graph11 C = {g,h}) (inc : ¬ InCone 11 C g h ∧ ¬ InCone 11 C h g)
    (joint : ∃ t ∈ tops graph11 C, InCone 11 C g t ∧ InCone 11 C h t)
    (budget : 17 + (tops graph11 C \ centreless graph11 C).card + 2 * (centreless graph11 C).card +
        (orN graph11 C \ lam graph11 C).card ≤ C.size + (Ustar graph11 C).card)
    (cover : ∀ K : Finset Vertex, IsMinCover (graph11.deleteEdges ↑(Ustar graph11 C)) K →
      K.card ≤ (tops graph11 C \ centreless graph11 C).card)
    (short : C.size ≤ 21) (three : (Ustar graph11 C).card = 3) :
    edgeIds (Ustar graph11 C) ∈ allowedTriples := by
  obtain ⟨t,ht,gt,ht'⟩ := joint
  have two := jointCharge least.1 form both (Nat.ne_of_lt diff) inc ht gt ht'
  obtain ⟨K,hmin,_⟩ := residualCover (Ustar graph11 C)
  have bound := cover K hmin
  have A := smallCoverMask _ K hmin.1 (by omega)
  have card := edgeIdCard (Ustar graph11 C) (fun _ mem => SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp mem).1)
  exact Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,card.trans three⟩,A⟩

/-- Each mask has an explicit five-vertex cover after its edges are removed. -/
def coversMask (A : Finset EdgeId) (K : Finset Vertex) : Prop :=
  K.card = 5 ∧ ∀ u v : Vertex, graph11.Adj u v →
    u ∈ K ∨ v ∈ K ∨ s(u,v) ∈ A.image undirected

instance (A : Finset EdgeId) (K : Finset Vertex) : Decidable (coversMask A K) := by unfold coversMask; infer_instance

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem eachMaskCover : ∀ A ∈ masks, ∃ K, coversMask A K := by
  intro A mem
  simp only [masks,List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨{3, 5, 7, 8, 10},by decide +kernel⟩
  · exact ⟨{3, 6, 8, 9, 10},by decide +kernel⟩
  · exact ⟨{1, 5, 7, 8, 10},by decide +kernel⟩
  · exact ⟨{0, 5, 7, 8, 10},by decide +kernel⟩
  · exact ⟨{4, 5, 7, 9, 10},by decide +kernel⟩
  · exact ⟨{1, 7, 8, 9, 10},by decide +kernel⟩
  · exact ⟨{2, 4, 6, 8, 9},by decide +kernel⟩
  · exact ⟨{2, 6, 8, 9, 10},by decide +kernel⟩
  · exact ⟨{4, 5, 6, 9, 10},by decide +kernel⟩
  · exact ⟨{1, 6, 8, 9, 10},by decide +kernel⟩
  · exact ⟨{1, 5, 7, 9, 10},by decide +kernel⟩
  · exact ⟨{1, 5, 6, 9, 10},by decide +kernel⟩
  · exact ⟨{2, 3, 8, 9, 10},by decide +kernel⟩
  · exact ⟨{3, 4, 5, 9, 10},by decide +kernel⟩
  · exact ⟨{1, 3, 8, 9, 10},by decide +kernel⟩
  · exact ⟨{1, 3, 5, 9, 10},by decide +kernel⟩
  · exact ⟨{4, 5, 6, 7, 8},by decide +kernel⟩
  · exact ⟨{3, 4, 5, 6, 9},by decide +kernel⟩
  · exact ⟨{3, 4, 6, 8, 9},by decide +kernel⟩
  · exact ⟨{3, 5, 6, 9, 10},by decide +kernel⟩
  · exact ⟨{2, 3, 6, 8, 9},by decide +kernel⟩
  · exact ⟨{0, 5, 6, 7, 8},by decide +kernel⟩
  · exact ⟨{2, 3, 4, 6, 9},by decide +kernel⟩
  · exact ⟨{3, 4, 6, 9, 10},by decide +kernel⟩
  · exact ⟨{1, 3, 6, 9, 10},by decide +kernel⟩
  · exact ⟨{2, 4, 6, 7, 8},by decide +kernel⟩
  · exact ⟨{1, 3, 7, 8, 10},by decide +kernel⟩
  · exact ⟨{0, 4, 6, 7, 8},by decide +kernel⟩
  · exact ⟨{0, 2, 6, 7, 8},by decide +kernel⟩
  · exact ⟨{1, 4, 5, 9, 10},by decide +kernel⟩
  · exact ⟨{2, 4, 7, 8, 9},by decide +kernel⟩
  · exact ⟨{0, 4, 5, 7, 8},by decide +kernel⟩
  · exact ⟨{0, 2, 4, 7, 8},by decide +kernel⟩
  · exact ⟨{2, 3, 4, 8, 9},by decide +kernel⟩
  · exact ⟨{1, 5, 6, 8, 10},by decide +kernel⟩
  · exact ⟨{0, 4, 5, 6, 8},by decide +kernel⟩
  · exact ⟨{0, 2, 4, 6, 8},by decide +kernel⟩
  · exact ⟨{1, 3, 5, 8, 10},by decide +kernel⟩
  · exact ⟨{3, 4, 5, 7, 10},by decide +kernel⟩
  · exact ⟨{0, 4, 5, 6, 7},by decide +kernel⟩
  · exact ⟨{1, 3, 5, 7, 10},by decide +kernel⟩
  · exact ⟨{1, 3, 5, 6, 9},by decide +kernel⟩
  · exact ⟨{1, 2, 3, 6, 9},by decide +kernel⟩
  · exact ⟨{0, 3, 4, 5, 8},by decide +kernel⟩
  · exact ⟨{0, 2, 3, 4, 8},by decide +kernel⟩
  · exact ⟨{0, 1, 5, 6, 7},by decide +kernel⟩
  · exact ⟨{0, 2, 4, 6, 7},by decide +kernel⟩
  · exact ⟨{0, 1, 2, 6, 7},by decide +kernel⟩

theorem coverMaskIff (U : Finset (Sym2 Vertex)) :
    (∃ K : Finset Vertex, (graph11.deleteEdges ↑U).IsVertexCover (↑K) ∧ K.card ≤ 5) ↔
      ∃ A ∈ masks, A ⊆ edgeIds U := by
  constructor
  · rintro ⟨K,hK,sz⟩
    exact smallCoverMask U K hK sz
  · rintro ⟨A,am,sub⟩
    obtain ⟨K,five,cover⟩ := eachMaskCover A am
    refine ⟨K,?_,five.le⟩
    intro u v uv
    obtain ⟨edge,kept⟩ := SimpleGraph.deleteEdges_adj.mp uv
    rcases cover u v edge with left | right | erased
    · exact Or.inl left
    · exact Or.inr right
    · obtain ⟨i,im,hi⟩ := Finset.mem_image.mp erased
      have hit := (Finset.mem_filter.mp (sub im)).2
      exact False.elim (kept (hi ▸ hit))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 3000000 in
theorem tripleCount : allowedTriples.card = 204 := by decide +kernel

/-- A circuit of size at most 21 under the posted hypotheses must leave three or more edges uncovered. -/
theorem threeUncovered : ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [_x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         have x9 : Finset ℕ := PEqualNP.TopForm.tops x1 x3;         have x10 : Finset ℕ := PEqualNP.TopForm.centreless x1 x3;         have x11 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;         have x12 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3;         (∀ x13 ∈ x9,             have x15 : Fin (2 : ℕ) → Finset (Fin (11 : ℕ)) := PEqualNP.TopForm.side x3 x13;             (∀ x16 ∈ x15 (0 : Fin (2 : ℕ)), ∀ x18 ∈ x15 (1 : Fin (2 : ℕ)), x1.Adj x16 x18) ∧ ((x15 (0 : Fin (2 : ℕ))).card ≤ (1 : ℕ) ∨ (x15 (1 : Fin (2 : ℕ))).card ≤ (1 : ℕ))) →           (∀ (x14 x15 : Fin (11 : ℕ)), s(x14, x15) ∈ x11 → ∃ x17 ∈ x9, ∃ (x18 : Fin (2 : ℕ)) (x19 : ℕ), (x19 = x4 ∨ x19 = x5) ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x17 (PEqualNP.EdgeOwnership.pairInput x14 x15) = Bool.true ∧ PEqualNP.CleanedNonEdge.OrReaches (11 : ℕ) x3 (PEqualNP.TopForm.opnd x3 x17 x18) x19 ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x19 (PEqualNP.EdgeOwnership.pairInput x14 x15) = Bool.true) → (17 : ℕ) + (x9 \ x10).card + (2 : ℕ) * x10.card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card ≤ x3.size + x11.card → (∀ (x16 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x11) x16 → x16.card ≤ (x9 \ x10).card) → x4 < x5 → PEqualNP.TopForm.junk x1 x3 = {x4, x5} → ¬x12 x4 x5 → ¬x12 x5 x4 → (∃ x21 ∈ x9, x12 x4 x21 ∧ x12 x5 x21) → x3.size ≤ 21 → 3 ≤ x11.card := by
  intro H dec C g h graphEq least form
  dsimp only
  intro _ _ budget cover diff pair first second common short
  subst H
  have cls := @residualBound dec C g h least form diff pair ⟨first,second⟩ common budget cover
  change 3 ≤ (@Ustar 11 graph11 dec C).card
  omega

end TwoJunkGeometry
