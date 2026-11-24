import AdaptiveData
open PetersenOrientation.Replay
def main : IO Unit := do
  for k in [14,13,12,11,10,9] do
    let n := (g.levels k).1
    for i in [0:n] do
      if !checkRow k i then throw (IO.userError s!"failed cap {k} node {i}")
    IO.println s!"checked all {n} rows at budget {k}"
