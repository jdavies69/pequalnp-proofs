import PEqualNP.Outside.L_meta_2036
import PEqualNP.Outside.L_meta_2502

/-! The checked gap L-meta-2036 supplies the eight-input lower bound.
The zero-restriction compiler and its invariants are from the project's
L-meta-2502. The projection and single-reader arguments below apply
these results to L-meta-2504. The displayed AND and NOT child statements
follow Arthur Guiot's proposed split in upstream PR 4795. -/

namespace PetersenReader
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_2502
abbrev Acc := List Stat × List Gate
def info (a : Acc) (g : Gate) := simplify g.op (8 + a.2.length)
  (g.inputs.map fun i => a.1.getD i (.inl false))
def step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def agrees (a : Acc) (lo hi : List Bool) : Prop :=
  a.1.length = lo.length ∧ lo.length = hi.length ∧
  ∀ i j, a.1.getD i (.inl false) = .inr j → lo.getD i false = hi.getD i false

theorem advance (a : Acc) (lo hi : List Bool) (g : Gate) (h : agrees a lo hi)
    (he : ∀ j, (info a g).2 = .inr j →
       g.op.eval (g.inputs.map fun i => lo.getD i false) =
       g.op.eval (g.inputs.map fun i => hi.getD i false)) :
    agrees (elimStep 8 a g) (step lo g) (step hi g) := by
  rcases h with ⟨hl,hr,ha⟩
  refine ⟨by simp [elimStep,step,hl], by simp [step,hr], ?_⟩
  intro i j hj
  change (a.1 ++ [(info a g).2]).getD i (.inl false) = .inr j at hj
  by_cases eq : i = a.1.length
  · subst i
    rw [getD_snoc_eq] at hj
    unfold step
    rw [hl,getD_snoc_eq,hr,getD_snoc_eq]
    exact he j hj
  · rw [getD_snoc_ne _ _ _ _ eq] at hj
    unfold step
    rw [getD_snoc_ne _ _ _ _ (by omega),getD_snoc_ne _ _ _ _ (by omega)]
    exact ha i j hj

theorem continueKept (a : Acc) (lo hi : List Bool) (g : Gate) (ok : NOk g)
    (h : agrees a lo hi) (kept : (info a g).1 ≠ none) :
    agrees (elimStep 8 a g) (step lo g) (step hi g) := by
  apply advance _ _ _ _ h
  intro j _
  apply congrArg g.op.eval
  apply List.map_congr_left
  intro i mem
  cases eq : a.1.getD i (.inl false) with
  | inr k => exact h.2.2 i k eq
  | inl c =>
    exfalso; apply kept
    apply simplify_count _ _ _ ok.1.1 (by simpa using ok.1.2) (fun e => by simpa using ok.2 e)
    exact ⟨c,List.mem_map.mpr ⟨i,mem,eq⟩⟩

theorem emitted (a : Acc) (g : Gate) :
    (elimStep 8 a g).2.length = a.2.length + (info a g).1.toList.length := by
  simp only [elimStep,info,List.length_append]

theorem growth (gs : List Gate) (a : Acc) :
    (elim 8 gs a).2.length ≤ a.2.length + gs.length := by
  induction gs generalizing a with
  | nil => simp [elim]
  | cons g gs ih =>
    rw [elim_cons]
    have h := ih (elimStep 8 a g)
    rw [emitted] at h
    have := toList_length_le (info a g).1
    simp only [List.length_cons]; omega

theorem preserved (gs : List Gate) (a : Acc) (lo hi : List Bool)
    (ok : ∀ g ∈ gs, NOk g) (h : agrees a lo hi)
    (full : a.2.length + gs.length ≤ (elim 8 gs a).2.length) :
    agrees (elim 8 gs a) (wiresFrom gs lo) (wiresFrom gs hi) := by
  induction gs generalizing a lo hi with
  | nil => exact h
  | cons g gs ih =>
    rw [elim_cons] at full ⊢
    have rest := growth gs (elimStep 8 a g)
    have atMost := toList_length_le (info a g).1
    have next := emitted a g
    simp only [List.length_cons] at full
    have kept : (info a g).1 ≠ none := by intro e; simp [e] at next; omega
    exact ih _ _ _ (fun k hk => ok k (by simp [hk]))
      (continueKept _ _ _ _ (ok g (by simp)) h kept) (by omega)

theorem forceConstant (op : GateOp) (m : ℕ) (xs : List Stat)
    (mode : op = GateOp.and ∨ op = GateOp.not) (len : xs.length ≤ 2)
    (un : op = GateOp.not → xs.length ≤ 1) (member : Sum.inl false ∈ xs) :
    (simplify op m xs).1 = none ∧ ∃ b, (simplify op m xs).2 = Sum.inl b := by
  rcases mode with rfl | rfl
  · rcases xs with _ | ⟨a,_ | ⟨b,_ | ⟨d,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify,simpAnd]
  · specialize un rfl
    rcases xs with _ | ⟨a,_ | ⟨b,l⟩⟩ <;> (try cases a) <;> simp_all [simplify,simpNot]
end PetersenReader


namespace PetersenReader
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_2502

def pins (s : Bool) (x : Fin 8 → Bool) : List Bool :=
  [x 1,x 0,x 4,x 7,x 5,x 2,s,x 6,x 3,x 1 || s]
def graph (x : Fin 8 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
  (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
  (x 5 && x 7) || (x 7 && x 4)
def probe (i : Fin 8) := decide (i = 1 ∨ i = 3)
def start : Acc := ([.inr 1,.inr 0,.inr 4,.inr 7,.inr 5,.inr 2,.inl false,.inr 6,.inr 3,.inr 1],[])
def reader (g : Gate) := (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).any (· == 6)

theorem startAgrees : agrees start (pins false probe) (pins true probe) := by
  refine ⟨rfl,rfl,?_⟩
  intro i j eq
  by_cases h : i < 10
  · interval_cases i <;> first | rfl | simp [start] at eq
  · rw [List.getD_eq_default _ _ (by change 10 ≤ i; omega)] at eq
    contradiction

theorem projection (C : Circuit) (fan : FanInTwo C)
    (low : ∀ x, C.eval (pins false x) = graph x) (lower : ¬ HasCircuitSize 8 graph 12) :
    let gs := C.gates.map normGate
    let a := elim 8 gs start
    13 ≤ a.2.length ∧ ∃ k, a.1.getD C.output (.inl false) = .inr k := by
  intro gs a
  have hok : ∀ g ∈ gs, NOk g := by
    intro g hg; obtain ⟨h,hh,rfl⟩ := List.mem_map.mp hg
    exact normGate_nok _ (fan _ hh)
  have inv (y : Fin 8 → Bool) : Inv 8 (List.ofFn y) (wiresFrom gs (pins false y)) a := by
    apply inv_elim _ _ (by simp) _ _ _ (fun g hg => (hok g hg).1)
    refine ⟨rfl,?_⟩
    intro k
    by_cases hk : k < 10
    · interval_cases k <;> simp [start,pins,Stat.Valid,Stat.val,wiresFrom]
    · rw [List.getD_eq_default _ _ (by change 10 ≤ k; omega),List.getD_eq_default _ _ (by change 10 ≤ k; omega)]
      exact ⟨trivial,rfl⟩
  have value (y : Fin 8 → Bool) :
      (a.1.getD C.output (.inl false)).val (wiresFrom a.2 (List.ofFn y)) = graph y := by
    rw [((inv y).2 C.output).2,show gs = C.gates.map normGate from rfl,wiresFrom_norm]
    exact low y
  cases eq : a.1.getD C.output (.inl false) with
  | inl b =>
    have f := value (fun _ => false)
    have t := value (fun _ => true)
    simp [eq,Stat.val,graph] at f t
    simp_all
  | inr k =>
    refine ⟨?_,k,rfl⟩
    by_contra! short
    apply lower
    refine ⟨⟨a.2,k⟩,elim_ok 8 gs _ (by simp [start]),by change a.2.length ≤ 12; omega,?_⟩
    intro x; change (wiresFrom a.2 (List.ofFn x)).getD k false = _
    simpa only [eq,Stat.val] using value x

/-- A reader fixed to a constant by the zero restriction would force a second gate loss.
One pair of assignments suffices to detect the contradiction. -/
theorem excludeConstant (pre post : List Gate) (g : Gate) (out : ℕ)
    (fan : FanInTwo (Circuit.mk (pre ++ g :: post) out)) (budget : pre.length + post.length ≤ 13)
    (reads : reader g = true) (mode : g.op = .and ∨ g.op = .not)
    (low : ∀ x, (Circuit.mk (pre ++ g :: post) out).eval (pins false x) = graph x)
    (lower : ¬ HasCircuitSize 8 graph 12) :
    (Circuit.mk (pre ++ g :: post) out).eval (pins true probe) = false := by
  let P := pre.map normGate
  let Q := post.map normGate
  let r := normGate g
  let A := elim 8 P start
  let B := elimStep 8 A r
  have f := projection _ fan low lower
  change 13 ≤ (elim 8 ((pre ++ g :: post).map normGate) start).2.length ∧ _ at f
  simp only [List.map_append,List.map_cons,elim_append,elim_cons] at f
  obtain ⟨big,k,outVar⟩ := f
  change 13 ≤ (elim 8 Q B).2.length at big
  have okReader := normGate_nok g (fan g (by simp))
  have modes : r.op = .and ∨ r.op = .not := by rcases mode with h|h <;> simp [r,normGate,h]
  have six : 6 ∈ r.inputs := by
    rcases g with ⟨op,xs⟩
    change op = .and ∨ op = .not at mode
    rcases mode with rfl|rfl <;> simpa [reader,r,normGate,GateOp.eval] using reads
  have sixValue : A.1.getD 6 (.inl false) = .inl false := by
    rw [show A = elim 8 P start from rfl,elim_getD _ _ _ _ _ (by decide)]; rfl
  obtain ⟨skip,c,hc⟩ := forceConstant r.op (8 + A.2.length)
    (r.inputs.map fun i => A.1.getD i (.inl false)) modes (by simpa using okReader.1.2)
    (fun e => by simpa using okReader.2 e) (List.mem_map.mpr ⟨6,six,sixValue⟩)
  change (info A r).1 = none at skip
  change (info A r).2 = .inl c at hc
  have sizeSkip := emitted A r
  rw [skip] at sizeSkip
  change B.2.length = A.2.length + 0 at sizeSkip
  have left := growth P start
  change A.2.length ≤ 0 + P.length at left
  have right := growth Q B
  have szP : P.length = pre.length := List.length_map _
  have szQ : Q.length = post.length := List.length_map _
  have okP (h : Gate) (hm : h ∈ P) : NOk h := by
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hm
    exact normGate_nok _ (fan _ (by simp [ht]))
  have okQ (h : Gate) (hm : h ∈ Q) : NOk h := by
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hm
    exact normGate_nok _ (fan _ (by simp [ht]))
  have hp := preserved P start _ _ okP startAgrees (by change 0 + P.length ≤ A.2.length; omega)
  have hb := advance A _ _ r hp (by intro j e; rw [hc] at e; contradiction)
  have hq := preserved Q B _ _ okQ hb (by omega)
  have eq := hq.2.2 out k outVar
  have unfoldRun (b : Bool) :
      wiresFrom Q (step (wiresFrom P (pins b probe)) r) =
        (Circuit.mk (pre ++ g :: post) out).wires (pins b probe) := by
    change _ = wiresFrom (pre ++ g :: post) (pins b probe)
    rw [←wiresFrom_norm (pre ++ g :: post),List.map_append,List.map_cons,wiresFrom_append]
    rfl
  rw [unfoldRun false,unfoldRun true] at eq
  change (Circuit.mk (pre ++ g :: post) out).eval (pins false probe) =
    (Circuit.mk (pre ++ g :: post) out).eval (pins true probe) at eq
  rw [←eq,low]; decide

end PetersenReader


namespace PetersenReader
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_2502

theorem insensitive (gs : List Gate) (lo hi : List Bool)
    (ok : ∀ g ∈ gs, Ok g) (nr : ∀ g ∈ gs, reader g = false)
    (len : lo.length = hi.length) (same : ∀ i ≠ 6, lo.getD i false = hi.getD i false) :
    ∀ i ≠ 6, (wiresFrom gs lo).getD i false = (wiresFrom gs hi).getD i false := by
  induction gs generalizing lo hi with
  | nil => exact same
  | cons g gs ih =>
    have clean : 6 ∉ (normGate g).inputs := by
      have r := nr g (by simp)
      obtain ⟨op,xs⟩ := g
      have allowed := (ok ⟨op,xs⟩ (by simp)).1
      rcases allowed with h|h|h <;> change op = _ at h <;> subst op <;>
        (simp [reader,normGate,GateOp.eval] at r ⊢; exact fun m => r 6 m rfl)
    have eq : g.op.eval (g.inputs.map fun i => lo.getD i false) =
        g.op.eval (g.inputs.map fun i => hi.getD i false) := by
      rw [← normGate_eval g (fun i => lo.getD i false), ← normGate_eval g (fun i => hi.getD i false)]
      apply congrArg (normGate g).op.eval
      apply List.map_congr_left
      exact fun i hi => same i (fun e => clean (e ▸ hi))
    apply ih (step lo g) (step hi g) (fun k h => ok k (by simp [h]))
      (fun k h => nr k (by simp [h])) (by simp [step,len])
    intro i ne
    unfold step; rw [eq]
    by_cases h : i = lo.length
    · subst i; rw [getD_snoc_eq,len,getD_snoc_eq]
    · rw [getD_snoc_ne _ _ _ _ h,getD_snoc_ne _ _ _ _ (by omega)]
      exact same i ne

theorem probeAgreement (i : ℕ) (ne : i ≠ 6) :
    (pins false probe).getD i false = (pins true probe).getD i false := by
  by_cases h : i < 10
  · interval_cases i <;> first | rfl | contradiction
  · rw [List.getD_eq_default _ _ (by change 10 ≤ i; omega),
        List.getD_eq_default _ _ (by change 10 ≤ i; omega)]

theorem output_ne_six (C : Circuit) (low : ∀ x, C.eval (pins false x) = graph x) :
    C.output ≠ 6 := by
  intro eq
  let allOn : Fin 8 → Bool := fun _ => true
  have t := low allOn
  obtain ⟨rest,hw,_⟩ := wiresFrom_prefix C.gates (pins false allOn)
  change (wiresFrom C.gates (pins false allOn)).getD C.output false = graph allOn at t
  rw [hw,eq,List.getD_append _ _ _ _ (by decide)] at t
  change false = true at t
  contradiction

theorem needsOr (C : Circuit) (fan : FanInTwo C) (size : C.size ≤ 14)
    (lower : ¬ HasCircuitSize 8 graph 12)
    (low : ∀ x, C.eval (pins false x) = graph x)
    (probeOn : C.eval (pins true probe) = true) :
    ∃ g ∈ C.gates, reader g = true ∧ g.op = .or := by
  by_cases someRead : ∃ g ∈ C.gates, reader g = true
  · obtain ⟨g,mem,reads⟩ := someRead
    refine ⟨g,mem,reads,?_⟩
    by_contra n
    have m := (fan g mem).1
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at m
    have mode : g.op = .and ∨ g.op = .not := by tauto
    obtain ⟨pre,post,split⟩ := List.mem_iff_append.mp mem
    cases C with
    | mk gates out =>
      dsimp only at split; subst gates
      have h := excludeConstant pre post g out fan (by
        simp only [Circuit.size,List.length_append,List.length_cons] at size; omega)
        reads mode low lower
      rw [h] at probeOn; contradiction
  · have nr : ∀ g ∈ C.gates, reader g = false := by
      intro g mem
      cases h : reader g
      · rfl
      · exact False.elim (someRead ⟨g,mem,h⟩)
    have eq := insensitive C.gates (pins false probe) (pins true probe) fan nr rfl probeAgreement
      C.output (output_ne_six C low)
    change C.eval (pins false probe) = C.eval (pins true probe) at eq
    rw [low,probeOn] at eq
    contradiction

end PetersenReader


namespace PetersenReader
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_2502

theorem optimalProjection (pre post : List Gate) (g : Gate) (out : ℕ)
    (fan : FanInTwo (Circuit.mk (pre ++ g :: post) out)) (budget : pre.length + post.length ≤ 13)
    (reads : reader g = true)
    (low : ∀ x, (Circuit.mk (pre ++ g :: post) out).eval (pins false x) = graph x)
    (lower : ¬ HasCircuitSize 8 graph 12)
    (probeOn : (Circuit.mk (pre ++ g :: post) out).eval (pins true probe) = true) :
    let a := elim 8 (pre.map normGate) start
    let r := normGate g
    let b := elimStep 8 a r
    let z := elim 8 (post.map normGate) b
    pre.length + post.length = 13 ∧ a.2.length = pre.length ∧
      b.2.length = pre.length ∧ z.2.length = 13 ∧ ∃ j, (info a r).2 = .inr j := by
  dsimp only
  let P := pre.map normGate
  let Q := post.map normGate
  let r := normGate g
  let A := elim 8 P start
  let B := elimStep 8 A r
  have f := projection _ fan low lower
  change 13 ≤ (elim 8 ((pre ++ g :: post).map normGate) start).2.length ∧ _ at f
  simp only [List.map_append,List.map_cons,elim_append,elim_cons] at f
  obtain ⟨big,k,outVar⟩ := f
  change 13 ≤ (elim 8 Q B).2.length at big
  have okReader := normGate_nok g (fan g (by simp))
  have six : 6 ∈ r.inputs := by
    rcases g with ⟨op,xs⟩
    have ok := (fan ⟨op,xs⟩ (by simp)).1
    rcases ok with h|h|h <;> change op = _ at h <;> subst op <;>
      simpa [reader,r,normGate,GateOp.eval] using reads
  have sixValue : A.1.getD 6 (.inl false) = .inl false := by
    rw [show A = elim 8 P start from rfl,elim_getD _ _ _ _ _ (by decide)]; rfl
  have skip : (info A r).1 = none := by
    apply simplify_count _ _ _ okReader.1.1 (by simpa using okReader.1.2) (fun e => by simpa using okReader.2 e)
    exact ⟨false,List.mem_map.mpr ⟨6,six,sixValue⟩⟩
  have sizeSkip := emitted A r
  rw [skip] at sizeSkip
  change B.2.length = A.2.length + 0 at sizeSkip
  have left := growth P start
  change A.2.length ≤ 0 + P.length at left
  have right := growth Q B
  have szP : P.length = pre.length := List.length_map _
  have szQ : Q.length = post.length := List.length_map _
  have okP (h : Gate) (hm : h ∈ P) : NOk h := by
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hm
    exact normGate_nok _ (fan _ (by simp [ht]))
  have okQ (h : Gate) (hm : h ∈ Q) : NOk h := by
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hm
    exact normGate_nok _ (fan _ (by simp [ht]))
  change pre.length + post.length = 13 ∧ A.2.length = pre.length ∧ B.2.length = pre.length ∧ (elim 8 Q B).2.length = 13 ∧ ∃ j, (info A r).2 = .inr j
  refine ⟨by omega,by omega,by omega,by omega,?_⟩
  cases hstat : (info A r).2 with
  | inr j => exact ⟨j,rfl⟩
  | inl c =>
    have hp := preserved P start _ _ okP startAgrees (by change 0 + P.length ≤ A.2.length; omega)
    have hb := advance A _ _ r hp (by intro j e; rw [hstat] at e; contradiction)
    have hq := preserved Q B _ _ okQ hb (by omega)
    have eq := hq.2.2 out k outVar
    have unfoldRun (b : Bool) :
        wiresFrom Q (step (wiresFrom P (pins b probe)) r) =
          (Circuit.mk (pre ++ g :: post) out).wires (pins b probe) := by
      change _ = wiresFrom (pre ++ g :: post) (pins b probe)
      rw [←wiresFrom_norm (pre ++ g :: post),List.map_append,List.map_cons,wiresFrom_append]
      rfl
    rw [unfoldRun false,unfoldRun true] at eq
    change (Circuit.mk (pre ++ g :: post) out).eval (pins false probe) =
      (Circuit.mk (pre ++ g :: post) out).eval (pins true probe) at eq
    rw [low,probeOn] at eq; contradiction

/-- Recognize the only operation that can return a variable when an effective operand
is fixed to false. The other pin already denotes the variable in the projected circuit. -/
theorem aliasShape (g : Gate) (ok : NOk g) (a : Acc) (six : 6 ∈ g.inputs)
    (zero : a.1.getD 6 (.inl false) = .inl false)
    (j : ℕ) (eq : (info a g).2 = .inr j) :
    g.op = .or ∧ ∃ k ≠ 6, (g.inputs = [6,k] ∨ g.inputs = [k,6]) ∧
        a.1.getD k (.inl false) = .inr j := by
  obtain ⟨op,xs⟩ := g
  obtain ⟨⟨h,l⟩,u⟩ := ok
  change op = .and ∨ op = .or ∨ op = .not at h
  change xs.length ≤ 2 at l
  change 6 ∈ xs at six
  rcases h with rfl|rfl|rfl
  · obtain ⟨_,c,hc⟩ := forceConstant .and (8+a.2.length) (xs.map fun i => a.1.getD i (.inl false)) (Or.inl rfl) (by simpa using l)
        (fun e => by contradiction) (List.mem_map.mpr ⟨6,six,zero⟩)
    change (simplify .and (8+a.2.length) (xs.map fun i => a.1.getD i (.inl false))).2 = .inr j at eq
    rw [hc] at eq; contradiction
  · refine ⟨rfl,?_⟩
    rcases xs with _ | ⟨i,_ | ⟨k,_ | ⟨d,rest⟩⟩⟩
    · simp at six
    · simp at six; subst i; simp only [info,simplify,List.map_cons,List.map_nil,simpOr,reduceCtorEq,zero] at eq
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at six
      rcases six with rfl|rfl
      · cases hv : a.1.getD k (.inl false) with
        | inl c => simp only [info,simplify,List.map_cons,List.map_nil,simpOr,reduceCtorEq,zero,hv] at eq
        | inr t =>
          refine ⟨k,fun e => by subst k; rw [zero] at hv; contradiction,Or.inl rfl,?_⟩
          simp only [info,simplify,List.map_cons,List.map_nil,simpOr,reduceCtorEq,zero,hv] at eq; rw [hv]; exact eq
      · cases hv : a.1.getD i (.inl false) with
        | inl c => simp only [info,simplify,List.map_cons,List.map_nil,simpOr,reduceCtorEq,zero,hv] at eq
        | inr t =>
          refine ⟨i,fun e => by subst i; rw [zero] at hv; contradiction,Or.inr rfl,?_⟩
          simp only [info,simplify,List.map_cons,List.map_nil,simpOr,reduceCtorEq,zero,hv] at eq; rw [hv]; exact eq
    · simp at l
  · obtain ⟨_,c,hc⟩ := forceConstant .not (8+a.2.length) (xs.map fun i => a.1.getD i (.inl false)) (Or.inr rfl) (by simpa using l)
        (fun _ => by simpa using u rfl) (List.mem_map.mpr ⟨6,six,zero⟩)
    change (simplify .not (8+a.2.length) (xs.map fun i => a.1.getD i (.inl false))).2 = .inr j at eq
    rw [hc] at eq; contradiction
end PetersenReader

namespace PetersenReader
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_2502

def sensitive (y : Fin 8 → Bool) := y 1 && !graph y && (y 0 || y 3)
def baseMask (y : Fin 8 → Bool) := ∑ i : Fin 8, if y i then 2 ^ i.val else 0

theorem allSensitive : ∀ y : Fin 8 → Bool,
    sensitive y = true ↔ baseMask y = 10 ∨ baseMask y = 26 ∨ baseMask y = 74 := by decide +kernel

theorem unchangedAway (y : Fin 8 → Bool) (h : y 1 = true) (i : ℕ) (ne : i ≠ 6) :
    (pins false y).getD i false = (pins true y).getD i false := by
  by_cases small : i < 10
  · interval_cases i <;> first | rfl | contradiction | simpa [pins,h]
  · rw [List.getD_eq_default _ _ (by change 10 ≤ i; omega),
        List.getD_eq_default _ _ (by change 10 ≤ i; omega)]

theorem otherPinOff (pre post : List Gate) (k out : ℕ) (g : Gate)
    (fan : FanInTwo (Circuit.mk (pre ++ g :: post) out))
    (nr : ∀ h ∈ pre ++ post, reader h = false)
    (op : g.op = .or) (pair : g.inputs = [6,k] ∨ g.inputs = [k,6])
    (low : ∀ y, (Circuit.mk (pre ++ g :: post) out).eval (pins false y) = graph y)
    (high : ∀ y, (Circuit.mk (pre ++ g :: post) out).eval (pins true y) = (graph y || y 0 || y 3))
    (y : Fin 8 → Bool) (hy : sensitive y = true) :
    (wiresFrom pre (pins false y)).getD k false = false := by
  have hs := hy
  simp only [sensitive,Bool.and_eq_true,Bool.not_eq_true'] at hs
  obtain ⟨⟨y1,gf⟩,pos⟩ := hs
  have p : ∀ h ∈ pre, Ok h := fun h hm => fan _ (by simp [hm])
  have q : ∀ h ∈ post, Ok h := fun h hm => fan _ (by simp [hm])
  have same := insensitive pre (pins false y) (pins true y) p (fun h hm => nr _ (by simp [hm])) rfl (unchangedAway y y1)
  have lens : (wiresFrom pre (pins false y)).length = (wiresFrom pre (pins true y)).length := by
    simp [length_wiresFrom,pins]
  have highSix : (wiresFrom pre (pins true y)).getD 6 false = true := by
    obtain ⟨rest,hw,_⟩ := wiresFrom_prefix pre (pins true y)
    rw [hw,List.getD_append _ _ _ _ (by change 6 < 10; decide)]; rfl
  by_contra! on
  have lowOn : (wiresFrom pre (pins false y)).getD k false = true := by cases h : (wiresFrom pre (pins false y)).getD k false <;> simp_all
  have ge : g.op.eval (g.inputs.map fun i => (wiresFrom pre (pins false y)).getD i false) =
      g.op.eval (g.inputs.map fun i => (wiresFrom pre (pins true y)).getD i false) := by
    rcases pair with e|e <;> simp only [op,e,GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,id_eq,lowOn,highSix] <;> simp
  have sameNext (i : ℕ) (ne : i ≠ 6) :
      (step (wiresFrom pre (pins false y)) g).getD i false =
      (step (wiresFrom pre (pins true y)) g).getD i false := by
    unfold step; rw [ge]
    by_cases e : i = (wiresFrom pre (pins false y)).length
    · subst i; rw [getD_snoc_eq,lens,getD_snoc_eq]
    · rw [getD_snoc_ne _ _ _ _ e,getD_snoc_ne _ _ _ _ (by omega)]; exact same _ ne
  have eq := insensitive post (step (wiresFrom pre (pins false y)) g) (step (wiresFrom pre (pins true y)) g) q (fun h hm => nr _ (by simp [hm]))
    (by simp [step,lens]) sameNext out (output_ne_six _ low)
  have unfoldRun (b : Bool) : wiresFrom post (step (wiresFrom pre (pins b y)) g) =
      (Circuit.mk (pre ++ g :: post) out).wires (pins b y) := by
    change _ = wiresFrom (pre ++ g :: post) (pins b y)
    rw [wiresFrom_append]; rfl
  rw [unfoldRun,unfoldRun] at eq
  change (Circuit.mk (pre ++ g :: post) out).eval (pins false y) =
    (Circuit.mk (pre ++ g :: post) out).eval (pins true y) at eq
  rw [low,high,gf] at eq
  simp only [Bool.false_or] at eq
  rw [pos] at eq
  contradiction

theorem eligibleInputs : ∀ k : Fin 10,
    (∀ y : Fin 8 → Bool, sensitive y = true → (pins false y).getD k.val false = false) ↔
    k.val ∈ ([1,3,4,5,6] : List ℕ) := by decide +kernel
end PetersenReader


namespace PetersenReader
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem acceptsOnlyOr (C : Circuit) (fan : FanInTwo C) (size : C.size ≤ 14)
    (low : ∀ x, C.eval (pins false x) = graph x)
    (probeOn : C.eval (pins true probe) = true) :
    ∃ g ∈ C.gates, reader g = true ∧ g.op = .or :=
  needsOr C fan size PEqualNP.Outside.L_meta_2036 low probeOn

theorem caseAnd :
      let read : PEqualNP.CircuitLowerBounds.Gate → Bool := fun g =>
        (if g.op.eval [false, false] then g.inputs.take 1 else g.inputs).any (fun i => decide (i = 6))
      let input : Bool → (Fin 8 → Bool) → List Bool := fun b x =>
        [x 1, x 0, x 4, x 7, x 5, x 2, b, x 6, x 3, x 1 || b]
      let z : (Fin 8 → Bool) → Bool := fun x =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) ||
        (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)
      ∀ (pre post : List Gate) (g : Gate) (out : ℕ),
        let D : Circuit := ⟨pre ++ g :: post, out⟩
        FanInTwo D → pre.length + post.length ≤ 13 →
        (∀ h ∈ pre ++ post, read h = false) → read g = true → g.op = .and →
        (let x : Fin 8 → Bool := fun i => decide (i = 1 ∨ i = 3)
         let value := fun b => g.op.eval (g.inputs.map fun i =>
           ((Circuit.mk pre 0).wires (input b x)).getD i false)
         value true ≠ value false) →
        (∀ x : Fin 8 → Bool, D.eval (input false x) = z x) →
        ∃ x : Fin 8 → Bool, D.eval (input true x) ≠ (z x || x 0 || x 3) := by
  intro read input z pre post g out D fan budget _ reads mode _ low
  refine ⟨probe,?_⟩
  have h := excludeConstant pre post g out fan budget reads (Or.inl mode) low PEqualNP.Outside.L_meta_2036
  change (Circuit.mk (pre ++ g :: post) out).eval (pins true probe) ≠ (graph probe || probe 0 || probe 3)
  rw [h]; decide

theorem caseNot :
      let read : PEqualNP.CircuitLowerBounds.Gate → Bool := fun g =>
        (if g.op.eval [false, false] then g.inputs.take 1 else g.inputs).any (fun i => decide (i = 6))
      let input : Bool → (Fin 8 → Bool) → List Bool := fun b x =>
        [x 1, x 0, x 4, x 7, x 5, x 2, b, x 6, x 3, x 1 || b]
      let z : (Fin 8 → Bool) → Bool := fun x =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) ||
        (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)
      ∀ (pre post : List Gate) (g : Gate) (out : ℕ),
        let D : Circuit := ⟨pre ++ g :: post, out⟩
        FanInTwo D → pre.length + post.length ≤ 13 →
        (∀ h ∈ pre ++ post, read h = false) → read g = true → g.op = .not →
        (let x : Fin 8 → Bool := fun i => decide (i = 1 ∨ i = 3)
         let value := fun b => g.op.eval (g.inputs.map fun i =>
           ((Circuit.mk pre 0).wires (input b x)).getD i false)
         value true ≠ value false) →
        (∀ x : Fin 8 → Bool, D.eval (input false x) = z x) →
        ∃ x : Fin 8 → Bool, D.eval (input true x) ≠ (z x || x 0 || x 3) := by
  intro read input z pre post g out D fan budget _ reads mode _ low
  refine ⟨probe,?_⟩
  have h := excludeConstant pre post g out fan budget reads (Or.inr mode) low PEqualNP.Outside.L_meta_2036
  change (Circuit.mk (pre ++ g :: post) out).eval (pins true probe) ≠ (graph probe || probe 0 || probe 3)
  rw [h]; decide

end PetersenReader
