import Mathlib
import PEqualNP.Outside.L_meta_1490

/-!
Two incomparable junk AND gates in an exact-fan-in-two top-form circuit.
The Boolean value of each gate can be traced along OR wires to its sources.
The wire evaluator and OR path lemmas come from the project proof L-meta-1490.
The graph cover bound uses the triangles and five-cycle from R-meta-1597-318.
When the gate is itself one of the two junk gates, all those sources are inputs.
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
