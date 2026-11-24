import ThetaTrace
namespace Theta2960
abbrev Row := Fin 128
def tab (f : Row → Bool) : Word := (BitVec.ofBoolListLE (List.ofFn f)).cast List.length_ofFn
theorem bit_tab (f : Row → Bool) (r : Row) : bit r (tab f) = f r := by
  simp only [bit,tab,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [r.isLt]

def reindex (f : Row → Row) (w : Word) := tab (fun r => bit (f r) w)
theorem bit_reindex (f : Row → Row) (a : Word) (i : Row) :
    bit i (reindex f a) = bit (f i) a := bit_tab _ _
theorem reindex_flip (f : Row → Row) (a : Word) : reindex f (~~~a) = ~~~(reindex f a) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi; let j : Row := ⟨i,hi⟩
  change bit j (reindex f (~~~a)) = bit j (~~~reindex f a)
  rw [bit_reindex]
  have flip (r : Row) (w : Word) : bit r (~~~w) = !(bit r w) := by simp [bit, r.isLt]
  rw [flip,flip,bit_reindex]
theorem reindex_and (f : Row → Row) (a b : Word) : reindex f (a &&& b) = reindex f a &&& reindex f b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi; let j : Row := ⟨i,hi⟩
  change bit j (reindex f (a &&& b)) = bit j (reindex f a &&& reindex f b)
  have meet (r : Row) (w v : Word) : bit r (w &&& v) = (bit r w && bit r v) := by simp [bit]
  rw [bit_reindex,meet,meet,bit_reindex,bit_reindex]
theorem reindex_zero (f : Row → Row) : reindex f 0 = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi; exact (bit_reindex f 0 ⟨i,hi⟩).trans (by simp [bit])
theorem reindex_signed (f : Row → Row) (a : Word) (p : Bool) :
    reindex f (signed a p) = signed (reindex f a) p := by
  cases p
  · rfl
  · exact reindex_flip f a
theorem reindex_origin (f : Row → Row) (hz : f 0=0) (a : Word) : (reindex f a)[0] = a[0] := by
  have t := bit_reindex f a 0
  rw [hz] at t
  exact t
theorem reindex_gate (f : Row → Row) (hz : f 0=0) (a b : Word) (p q : Bool) :
    reindex f (gate a b p q) = gate (reindex f a) (reindex f b) p q := by
  have normEq (w : Word) : reindex f (norm w) = norm (reindex f w) := by
    simp only [norm,reindex_signed,reindex_origin f hz]
  simp only [gate,normEq,reindex_and,reindex_signed]
theorem reindex_inj (f : Row → Row) (onto : Function.Surjective f) :
    Function.Injective (reindex f) := by
  intro a b eq
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  obtain ⟨r,hr⟩ := onto ⟨j,hj⟩
  have e := congrArg (bit r) eq
  rw [bit_reindex,bit_reindex,hr] at e
  exact e

theorem live_reindex {T k S} (h : Live T k S) (f : Row → Row) (hz : f 0=0)
    (onto : Function.Surjective f) : Live (reindex f T) k (S.image (reindex f)) := by
  have inj := reindex_inj f onto
  have good (w : Word) (hw : Good w) : Good (reindex f w) :=
    ⟨fun e => hw.1 (inj (e.trans (reindex_zero f).symm)),(reindex_origin f hz w).trans hw.2⟩
  induction h with
  | stop hw => simpa using Live.stop (good _ hw)
  | @binary k U a b p q ha hb ne fresh tail ih =>
    have fr : reindex f (gate a b p q) ∉ (insert a (insert b U)).image (reindex f) := by
      rintro mem; obtain ⟨v,hv,e⟩ := Finset.mem_image.mp mem; exact fresh (inj e ▸ hv)
    simp only [Finset.image_insert,reindex_gate f hz] at fr ih ⊢
    exact Live.binary (good _ ha) (good _ hb) (fun e => ne (inj e)) fr ih

def reorderRow (r : Row) : Row := Fin.ofNat 128 (
  (r.val &&& 73) ||| ((r.val &&& 32) >>> 4) ||| ((r.val &&& 16) >>> 2) |||
  ((r.val &&& 2) <<< 3) ||| ((r.val &&& 4) <<< 3))
def undoRow (r : Row) : Row := Fin.ofNat 128 (
  (r.val &&& 73) ||| ((r.val &&& 2) <<< 4) ||| ((r.val &&& 4) <<< 2) |||
  ((r.val &&& 16) >>> 3) ||| ((r.val &&& 32) >>> 3))

theorem reorder_onto : Function.Surjective reorderRow := by
  have all : ∀ r : Row, reorderRow (undoRow r) = r := by decide +kernel
  exact fun r => ⟨undoRow r, all r⟩
def thetaCanonical : Word := 0xfffffffeffffffccfffffafaf888f888
theorem canonicalTrace (C : PEqualNP.CircuitLowerBounds.Circuit)
    (fan : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : PEqualNP.MetaComplexity.circuitFun 7 C = targetFun) :
    ∃ k ≤ C.gates.countP charge, Live thetaCanonical k inputs.toFinset := by
  obtain ⟨k,hk,run⟩ := circuitTrace C fan computes
  have h := live_reindex run reorderRow (by decide) reorder_onto
  rw [show reindex reorderRow theta = thetaCanonical by decide +kernel,
    show inputs.toFinset.image (reindex reorderRow) = inputs.toFinset by decide +kernel] at h
  exact ⟨k,hk,h⟩
end Theta2960
