import ReadSearch
namespace Replay2161

def Positive (x : Word) (S : Finset Word) : Prop :=
  ∀ a∈S, ∃ i j : Fin 512, bit x i=true ∧ bit x j=false ∧ bit a i=true ∧ bit a j=false ∧
    ∀ w∈S, w≠a → bit w i=bit w j

lemma exact_difference {x b t S} (h : Live x b t S) {i j : Fin 512}
    (xi : bit x i=true) (xj : bit x j=false) : ∃ a∈S, bit a i≠bit a j := by
  obtain ⟨a,ha,d⟩ := distinguishes_live h xi xj
  refine ⟨a,ha,?_⟩
  by_cases z : t=0
  · obtain ⟨u,v⟩ := (by simpa [distinguishes,z] using d : bit a i=true ∧ bit a j=false)
    simp [u,v]
  · simpa [distinguishes,z] using d

lemma tight_parts {x : Word} {n t U a b d} (ab : a≠b)
    (fresh : combine d a b∉insert a (insert b U)) (tail : Live x n t (insert (combine d a b) U))
    (width : (insert a (insert b U)).card=n+1+1) :
    a∉U ∧ b∉U ∧ (insert (combine d a b) U).card=n+1 := by
  have zu : combine d a b∉U := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
  have cnt := count_live tail
  rw [Finset.card_insert_of_notMem zu] at cnt ⊢
  have notB : b∉U := by
    intro h
    rw [Finset.insert_eq_of_mem h] at width
    have lim := Finset.card_insert_le a U
    omega
  have bcard := Finset.card_insert_of_notMem notB
  have notA : a∉insert b U := by
    intro h
    rw [Finset.insert_eq_of_mem h] at width
    omega
  rw [Finset.card_insert_of_notMem notA,bcard] at width
  exact ⟨fun h => notA (Finset.mem_insert_of_mem h),notB,by omega⟩

lemma tight_positive {x : Word} {n t S} (live : Live x n t S) (one : t≤1)
    (width : S.card=n+1) (positive : Positive x S) : t=0 := by
  induction live with
  | done => rfl
  | @unary n t U a ha fresh tail ih =>
    have zero : t=0 := by omega
    have zu : ~~~a ∉ U := fun h => fresh (Finset.mem_insert_of_mem h)
    have cnt := count_live tail
    rw [Finset.card_insert_of_notMem zu] at cnt
    have au : a∉U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at width
      -- A unary operation keeps the same budget, so retaining its input violates the tight width.
      omega
    obtain ⟨i,j,xi,xj,ai,aj,q⟩ := positive a (Finset.mem_insert_self ..)
    obtain ⟨w,hw,dist⟩ := distinguishes_live tail xi xj
    have dl : bit w i=true ∧ bit w j=false := by simpa [distinguishes,zero] using dist
    rcases Finset.mem_insert.mp hw with rfl|wu
    · simp [bit_not,ai] at dl
    · have wa : w≠a := by rintro rfl; exact au wu
      have e := q w (Finset.mem_insert_of_mem wu) wa
      simp [dl.1,dl.2] at e
  | @binary n t U a b d pa pb ab fresh tail ih =>
    obtain ⟨au,bu,tw⟩ := tight_parts ab fresh tail width
    apply ih one tw
    intro w hw
    have am : a∈insert a (insert b U) := Finset.mem_insert_self ..
    have bm : b∈insert a (insert b U) := Finset.mem_insert_of_mem (Finset.mem_insert_self ..)
    rcases Finset.mem_insert.mp hw with rfl|wu
    · obtain ⟨i,j,xi,xj,ai,aj,other⟩ := positive a am
      have beq := other b bm ab.symm
      obtain ⟨w,hw,diff⟩ := exact_difference tail xi xj
      have wz : w=combine d a b := (Finset.mem_insert.mp hw).resolve_right (by
        intro hu
        apply diff
        exact other w (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu)) (by rintro rfl; exact au hu))
      subst w
      have pos : bit (combine d a b) i=true ∧ bit (combine d a b) j=false := by
        cases d <;> cases h : bit b j <;> simp_all only [bit_bin,Bool.false_eq_true,ite_false,ite_true,
          Bool.true_and,Bool.false_and,Bool.true_or,Bool.false_or] <;> decide
      refine ⟨i,j,xi,xj,pos.1,pos.2,?_⟩
      intro w hw wz
      have hu := (Finset.mem_insert.mp hw).resolve_left wz
      exact other w (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu)) (by rintro rfl; exact au hu)
    · obtain ⟨i,j,xi,xj,wi,wj,other⟩ := positive w
        (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem wu))
      refine ⟨i,j,xi,xj,wi,wj,?_⟩
      intro q hq qw
      rcases Finset.mem_insert.mp hq with rfl|qu
      · have ae := other a am (by rintro rfl; exact au wu)
        have be := other b bm (by rintro rfl; exact bu wu)
        simp only [bit_bin,ae,be]
      · exact other q (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem qu)) qw

end Replay2161
