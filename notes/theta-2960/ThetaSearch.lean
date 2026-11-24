import ThetaTrace

namespace Theta2960

abbrev Within (target : Word) (b : Nat) (v : List Word) :=
  ∃ k ≤ b, Live target k v.toFinset

structure Choice where
  a : Word
  b : Word
  p : Bool
  q : Bool
  ka : Bool
  kb : Bool

def Choice.result (s : Choice) := gate s.a s.b s.p s.q
def Choice.rest (s : Choice) (v : List Word) :=
  v.filter fun x => (s.ka || x != s.a) && (s.kb || x != s.b)
def Choice.after (s : Choice) (v : List Word) := s.result :: s.rest v

def choices (v : List Word) := v.flatMap fun a => v.flatMap fun b =>
  if a.toNat < b.toNat then
    [false,true].flatMap fun p => [false,true].flatMap fun q =>
    [false,true].flatMap fun ka => [false,true].map fun kb => Choice.mk a b p q ka kb
  else []

theorem mem_choices {a b : Word} {v : List Word} (ha : a ∈ v) (hb : b ∈ v)
    (lt : a.toNat < b.toNat) (p q ka kb : Bool) :
    Choice.mk a b p q ka kb ∈ choices v := by
  refine List.mem_flatMap.mpr ⟨a,ha,List.mem_flatMap.mpr ⟨b,hb,?_⟩⟩
  simp only [lt,ite_true]
  apply List.mem_flatMap.mpr
  refine ⟨p,by cases p <;> simp,?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨q,by cases q <;> simp,?_⟩
  apply List.mem_flatMap.mpr
  exact ⟨ka,by cases ka <;> simp,List.mem_map.mpr ⟨kb,by cases kb <;> simp,rfl⟩⟩

theorem choose_rest {a b : Word} {v : List Word} {U : Finset Word}
    (h : v.toFinset = insert a (insert b U)) (p q : Bool) :
    ((Choice.mk a b p q (decide (a∈U)) (decide (b∈U))).rest v).toFinset = U := by
  ext x
  simp only [Choice.rest,List.mem_toFinset,List.mem_filter,Bool.and_eq_true,
    Bool.or_eq_true,decide_eq_true_eq,bne_iff_ne]
  have hv : x ∈ v ↔ x=a ∨ x=b ∨ x∈U := by
    rw [← List.mem_toFinset,h,Finset.mem_insert,Finset.mem_insert]
  rw [hv]
  grind

theorem nextChoice {target b v} (ok : Within target b v) :
    target ∈ v ∨ ∃ s ∈ choices v, s.result ≠ 0 ∧ s.result ∉ v ∧
      0 < b ∧ Within target (b-1) (s.after v) := by
  obtain ⟨n,hn,live⟩ := ok
  generalize hs : v.toFinset = S at live
  cases live with
  | stop good => left; simpa using (show target ∈ v.toFinset by rw [hs]; simp)
  | @binary k U a c p q ga gc ne fresh tail =>
    right
    have mk (z w : Word) (f g : Bool) (lt : z.toNat<w.toNat)
        (head : v.toFinset=insert z (insert w U)) (fr : gate z w f g ∉ v.toFinset)
        (child : Live target k (insert (gate z w f g) U)) :
        ∃ s ∈ choices v, s.result ≠ 0 ∧ s.result ∉ v ∧ 0 < b ∧ Within target (b-1) (s.after v) := by
      let s := Choice.mk z w f g (decide (z∈U)) (decide (w∈U))
      have hz : z ∈ v.toFinset := by rw [head]; simp
      have hw : w ∈ v.toFinset := by rw [head]; simp
      exact ⟨s,mem_choices (by simpa using hz) (by simpa using hw) lt ..,
        (live_good child _ (Finset.mem_insert_self ..)).1,fun mem => fr (List.mem_toFinset.mpr mem),
        by omega, k,by omega, by simpa only [s,Choice.after,Choice.result,List.toFinset_cons,choose_rest head] using child⟩
    have ord : a.toNat ≠ c.toNat := fun e => ne (BitVec.eq_of_toNat_eq e)
    rcases lt_or_gt_of_ne ord with h|h
    · exact mk a c p q h hs (hs ▸ fresh) tail
    · apply mk c a q p h
      · rwa [Finset.insert_comm]
      · simpa only [gate,BitVec.and_comm (signed c q),hs] using fresh
      · simpa only [gate,BitVec.and_comm (signed c q)] using tail

-- A row collision is independent of how subsequent gates are wired.
def clashes (target : Word) (v : List Word) (i j : Fin 128) : Bool :=
  (target.getLsbD i.val != target.getLsbD j.val) &&
    v.all fun w => w.getLsbD i.val == w.getLsbD j.val

theorem clashes_sound {target b v i j} (hc : clashes target v i j = true) : ¬ Within target b v := by
  rintro ⟨k,_,h⟩
  simp only [clashes,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,beq_iff_eq] at hc
  obtain ⟨w,mem,ne⟩ := live_distinguish h i j hc.1
  exact ne (hc.2 w (List.mem_toFinset.mp mem))

theorem too_wide {target b v} (nd : v.Nodup) (h : b+1<v.length) : ¬Within target b v := by
  rintro ⟨k,hk,live⟩
  have bound := live_size live
  rw [List.toFinset_card_of_nodup nd] at bound
  omega

end Theta2960
