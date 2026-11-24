import BundleAll
namespace PetersenReaderInvariant.All
def main : IO Unit := do
  for k in [1:14] do
    let c := (rowLayout k).1
    let mut bad := []
    for i in [:c] do
      if !checkStored db k i then bad := i::bad
    IO.println (k,c,bad)
#eval main
end PetersenReaderInvariant.All
