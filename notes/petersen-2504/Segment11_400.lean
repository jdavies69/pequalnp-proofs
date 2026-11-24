import DeskForestData
namespace PetersenCertificate
open PEqualNP.Outside.L_meta_1667
set_option maxRecDepth 30000
set_option maxHeartbeats 0
theorem B11_9563 : block boosted 11 9563 24 = true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem B11_9587 : block boosted 11 9587 24 = true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem B11_9611 : block boosted 11 9611 24 = true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem B11_9635 : block boosted 11 9635 24 = true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem B11_9659 : block boosted 11 9659 24 = true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem B11_9683 : block boosted 11 9683 24 = true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem B11_9707 : block boosted 11 9707 24 = true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem B11_9731 : block boosted 11 9731 24 = true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem checkedSegment11_400 : block boosted 11 9563 192 = true := (block_merge (block_merge (block_merge B11_9563 B11_9587) (block_merge B11_9611 B11_9635)) (block_merge (block_merge B11_9659 B11_9683) (block_merge B11_9707 B11_9731)))
end PetersenCertificate
