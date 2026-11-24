import DeskForestData
namespace PetersenCertificate
open PEqualNP.Outside.L_meta_1667
set_option maxRecDepth 30000
set_option maxHeartbeats 0
theorem B11_6491 : block boosted 11 6491 24 = true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem B11_6515 : block boosted 11 6515 24 = true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem B11_6539 : block boosted 11 6539 24 = true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem B11_6563 : block boosted 11 6563 24 = true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem B11_6587 : block boosted 11 6587 24 = true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem B11_6611 : block boosted 11 6611 24 = true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem B11_6635 : block boosted 11 6635 24 = true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem B11_6659 : block boosted 11 6659 24 = true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem checkedSegment11_272 : block boosted 11 6491 192 = true := (block_merge (block_merge (block_merge B11_6491 B11_6515) (block_merge B11_6539 B11_6563)) (block_merge (block_merge B11_6587 B11_6611) (block_merge B11_6635 B11_6659)))
end PetersenCertificate
