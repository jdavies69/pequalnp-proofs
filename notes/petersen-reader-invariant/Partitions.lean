import Mathlib
namespace Replay2161

def picked {α : Type} (choose : α→Bool) : List α→ℕ
  | []=>0
  | a::v=>(if choose a then 2^v.length else 0) + picked choose v
lemma picked_lt {α : Type} (choose : α→Bool) (v : List α) : picked choose v<2^v.length := by
  induction v with
  | nil=>simp [picked]
  | cons a v ih=>simp only [picked,List.length_cons,pow_succ]; split <;> omega

def packHalves (n lo hi : ℕ) := (lo &&& (2^n-1)) ||| (hi <<< n)
lemma pack_left {n i} (lt : i<n) (lo hi : ℕ) : (packHalves n lo hi).testBit i=lo.testBit i := by
  simp [packHalves,Nat.testBit_two_pow_sub_one,lt,Nat.not_le.mpr lt]
lemma pack_right {n i} (lo hi : ℕ) : (packHalves n lo hi).testBit (n+i)=hi.testBit i := by
  simp [packHalves,Nat.testBit_two_pow_sub_one,Nat.not_lt_of_ge (Nat.le_add_right n i)]

def patterns {α : Type} (ok : α→Bool→Bool) : List α→ℕ
  | []=>1
  | a::v=>
    let rest:=patterns ok v
    packHalves (2^v.length) (if ok a false then rest else 0) (if ok a true then rest else 0)
lemma pattern_true {α : Type} (ok : α→Bool→Bool) (choose : α→Bool) (v : List α)
    (h : (patterns ok v).testBit (picked choose v)=true) : ∀ a∈v, ok a (choose a)=true := by
  induction v with
  | nil=>simp
  | cons a v ih=>
    have one : ok a (choose a)=true ∧ (patterns ok v).testBit (picked choose v)=true := by
      cases q : choose a
      · simp only [patterns,picked,q,Bool.false_eq_true,ite_false,Nat.zero_add,pack_left (picked_lt choose v)] at h
        split at h
        · rename_i good; exact ⟨good,h⟩
        · simp at h
      · simp only [patterns,picked,q,ite_true,pack_right] at h
        split at h
        · rename_i good; exact ⟨good,h⟩
        · simp at h
    intro w hw; rcases List.mem_cons.mp hw with rfl|hw
    · exact one.1
    · exact ih one.2 w hw
end Replay2161
