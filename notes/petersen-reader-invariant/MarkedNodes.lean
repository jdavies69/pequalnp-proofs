import Marked
namespace PetersenReaderInvariant
open PEqualNP.Outside.L_meta_1667
abbrev Extra := Bool → List Sig → Bool
abbrev TrackContext := NodeContext × (Sig → Bool) × Bool × Extra
def checkMove (c : TrackContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  evalMove c.1 op a b z ka kb || c.2.2.2 (c.2.2.1 || c.2.1 z.1)
    (z.1 :: (opKeep (op==2) ka kb a b c.1.2.2.1).map Prod.fst)
def pair (ctx : TrackContext) (a b : Decor) (d : Bool) :=
  let op := if d then 1 else 0
  let z := movedDecor op a b
  let attempt := checkMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def row (ctx : TrackContext) (a : Decor) (bs : List Decor) :=
  let z := movedDecor 2 a a
  checkMove ctx 2 a a z false false && checkMove ctx 2 a a z true true &&
    bs.all (fun b => pair ctx a b false && pair ctx a b true)
def full (ctx : TrackContext) : List Decor → Bool
  | [] => true
  | a::bs => row ctx a bs && full ctx bs

theorem unaryOK {ctx ws} (h : full ctx ws=true) {a : Decor} (ha : a∈ws) (keep : Bool) :
    checkMove ctx 2 a a (movedDecor 2 a a) keep keep=true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [full,Bool.and_eq_true,row] at h
    rcases List.mem_cons.mp ha with rfl | hm
    · cases keep
      · exact h.1.1.1
      · exact h.1.1.2
    · exact ih h.2 hm

theorem binaryOK {ctx ws} (h : full ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) (d : Bool) : pair ctx a b d=true ∨ pair ctx b a d=true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [full,Bool.and_eq_true,row,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      left
      cases d <;> first | exact (h.1.2 b bm).1 | exact (h.1.2 b bm).2
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · right
        cases d <;> first | exact (h.1.2 a haTail).1 | exact (h.1.2 a haTail).2
      · exact ih h.2 haTail hbTail

theorem pairOK {ctx a b d} (h : pair ctx a b d = true) (ka kb : Bool) :
    checkMove ctx (if d then 1 else 0) a b (movedDecor (if d then 1 else 0) a b) ka kb = true := by
  simp only [pair,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2


theorem moveOK {raw T r s ws pools cap a b op ka kb bad seen extra}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : (op==2)=false → a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (ex : ∀ f us, extra f us = true → Excludes T bad f (cap-1) us.toFinset)
    (pro : proper (movedDecor op a b).1) (fresh : (movedDecor op a b).1 ∉ ws.map Prod.fst)
    (test : checkMove ((cap,ws.length,ws,preCov ws,pools,fun _=>[]),bad,seen,extra)
        op a b (movedDecor op a b) ka kb=true) :
    Excludes T bad (seen || bad (movedDecor op a b).1) (cap-1) (moveFront ws op a b ka kb).toFinset := by
  rcases Bool.or_eq_true_iff.mp test with base|added
  · exact ofImpossible (evalMove_sound pairs faith nd ha hb ne hcap pv
      (fun tag xs (hx : xs ∈ ([] : List (List Sig))) => by simp at hx) pro fresh base)
  · exact ex _ _ added
theorem fullOK {raw T r s ws pools bad seen extra cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ f xs, extra f xs = true → Excludes T bad f (cap-1) (List.toFinset xs))
    (checks : full ((cap,ws.length,ws,preCov ws,pools,fun _=>[]),bad,seen,extra) ws = true) :
    Excludes T bad seen cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k t hk h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    have bare := h.erase
    cases bare
    exact out (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply enumerate seen nd out
  · intro v hv keep fresh pro len
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv
    have hf := unary_front nd ha keep
    rw [←hf]
    exact moveOK pairs faith nd ha ha (by simp) hc' pv lv pro fresh (unaryOK checks ha keep)
  · intro a ha b hb d ka kb ne fresh pro len
    obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
    obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
    have ab : a≠b := fun e => ne (congrArg Prod.fst e)
    have one (a b : Decor) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
        (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
        (test : pair ((cap,ws.length,ws,preCov ws,pools,fun _=>[]),bad,seen,extra) a b d = true) :
        Excludes T bad (seen || bad (bin d a.1 b.1)) (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
      rw [←binary_front nd aa bb ne']
      have eq : (movedDecor (if d then 1 else 0) a b).1 = bin d a.1 b.1 := by cases d <;> rfl
      rw [←eq]
      exact moveOK pairs faith nd aa bb (fun _ e => ne' (congrArg Prod.fst e)) hc' pv lv
        (eq ▸ pr) (eq ▸ fr) (pairOK test ka kb)
    rcases binaryOK checks haW hbW ab d with hh | hh
    · exact one a b haW hbW ne ka kb pro fresh hh
    · rw [childTwo_swap _ nd, show bin d a.1 b.1 = bin d b.1 a.1 by cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]]
      exact one b a hbW haW (Ne.symm ne) kb ka (by cases d <;> simpa [bin,BitVec.and_comm,BitVec.or_comm] using pro)
        (by cases d <;> simpa [bin,BitVec.and_comm,BitVec.or_comm] using fresh) hh


end PetersenReaderInvariant
#print axioms PetersenReaderInvariant.fullOK
