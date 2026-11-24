import ThetaSearch

namespace Theta2960

-- Each chart lists pairs of an accepting row and a rejecting row. A mask records, in
-- parallel, which pairs still have distinct wire values.
structure Chart (x : Word) (n : Nat) where
  pos : Fin n → Fin 128
  neg : Fin n → Fin 128
  pos_ok : ∀ i, x.getLsbD (pos i).val = true
  neg_ok : ∀ i, x.getLsbD (neg i).val = false

def sampleAtRows {n : Nat} (rows : Fin n → Fin 128) (w : Word) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn fun i => w.getLsbD (rows i).val)).cast List.length_ofFn

theorem sample_at {n : Nat} (rows : Fin n → Fin 128) (w : Word) (i : Fin n) :
    (sampleAtRows rows w).getLsbD i.val = w.getLsbD (rows i).val := by
  simp only [sampleAtRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE]
  rw [List.getD_eq_getElem _ _ (by simpa using i.isLt), List.getElem_ofFn]

structure Decor (n : Nat) where
  w : Word
  pos : BitVec n
  neg : BitVec n
  deriving Inhabited

def Decor.OK {x n} (c : Chart x n) (d : Decor n) :=
  (∀ i : Fin n, d.pos.getLsbD i.val = d.w.getLsbD (c.pos i).val) ∧
  (∀ i : Fin n, d.neg.getLsbD i.val = d.w.getLsbD (c.neg i).val)

def signedN {n} (w : BitVec n) (s : Bool) := if s then ~~~w else w

theorem bit_signedN {n} (a : BitVec n) (p : Bool) (i : Fin n) :
    (signedN a p).getLsbD i.val = (a.getLsbD i.val ^^ p) := by
  cases p <;> simp [signedN,BitVec.getLsbD_not,i.isLt]

def Decor.mix {n} (a b : Decor n) (p q : Bool) : Decor n :=
  let phase := (signed a.w p &&& signed b.w q)[0]
  let make (x y : BitVec n) := signedN (signedN x p &&& signedN y q) phase
  ⟨gate a.w b.w p q,make a.pos b.pos,make a.neg b.neg⟩

theorem Decor.mix_ok {x n} {c : Chart x n} {a b : Decor n} (ha : a.OK c)
    (hb : b.OK c) (p q : Bool) : (a.mix b p q).OK c := by
  have bits (v : Fin 128) (s t : BitVec n) (i : Fin n)
      (es : s.getLsbD i.val = a.w.getLsbD v.val) (et : t.getLsbD i.val = b.w.getLsbD v.val) :
      (signedN (signedN s p &&& signedN t q) (signed a.w p &&& signed b.w q)[0]).getLsbD i.val =
        (gate a.w b.w p q).getLsbD v.val := by
    change _ = (signedN (signedN a.w p &&& signedN b.w q) (signed a.w p &&& signed b.w q)[0]).getLsbD v.val
    simp only [bit_signedN,BitVec.getLsbD_and,es,et]
  exact ⟨fun i => bits _ _ _ i (ha.1 i) (hb.1 i),fun i => bits _ _ _ i (ha.2 i) (hb.2 i)⟩

def cubeCover {n} : List (Decor n) → BitVec n
  | [] => 0
  | a::as => (a.pos ^^^ a.neg) ||| cubeCover as

theorem cover_at {x n} {c : Chart x n} (ds : List (Decor n)) (ok : ∀ d ∈ ds, d.OK c)
    (i : Fin n) : (cubeCover ds).getLsbD i.val = true ↔
      ∃ w ∈ ds.map Decor.w, w.getLsbD (c.pos i).val ≠ w.getLsbD (c.neg i).val := by
  induction ds with
  | nil => simp [cubeCover]
  | cons d ds ih =>
    have vd := ok d (by simp)
    simp only [cubeCover,BitVec.getLsbD_or,BitVec.getLsbD_xor,Bool.or_eq_true,
      vd.1 i,vd.2 i,ih (fun a ha => ok a (by simp [ha])),List.map_cons,
      List.mem_cons,exists_eq_or_imp]
    cases d.w.getLsbD (c.pos i).val <;> cases d.w.getLsbD (c.neg i).val <;> simp

theorem feasible_cover {x n b} {c : Chart x n} {ds : List (Decor n)} (ok : ∀ d ∈ ds, d.OK c)
    (h : Within x b (ds.map Decor.w)) : cubeCover ds = BitVec.allOnes n := by
  obtain ⟨k,_,live⟩ := h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin n := ⟨j,hj⟩
  simp only [BitVec.getLsbD_allOnes,hj,decide_true]
  apply (cover_at ds ok i).2
  obtain ⟨w,mem,ne⟩ := live_distinguish live (c.pos i) (c.neg i) (by rw [c.pos_ok,c.neg_ok]; decide)
  exact ⟨w,List.mem_toFinset.mp mem,ne⟩

end Theta2960
