import DeskForestData
namespace PetersenCertificate
open PEqualNP.Outside.L_meta_1667
set_option maxRecDepth 30000
set_option maxHeartbeats 0
theorem B11_8603 : block boosted 11 8603 24 = true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem B11_8627 : block boosted 11 8627 24 = true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem B11_8651 : block boosted 11 8651 24 = true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem B11_8675 : block boosted 11 8675 24 = true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem B11_8699 : block boosted 11 8699 24 = true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem B11_8723 : block boosted 11 8723 24 = true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem B11_8747 : block boosted 11 8747 24 = true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem B11_8771 : block boosted 11 8771 24 = true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem checkedSegment11_360 : block boosted 11 8603 192 = true := (block_merge (block_merge (block_merge B11_8603 B11_8627) (block_merge B11_8651 B11_8675)) (block_merge (block_merge B11_8699 B11_8723) (block_merge B11_8747 B11_8771)))
end PetersenCertificate
