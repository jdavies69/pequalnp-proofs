import Coherent
import DataAll
namespace PetersenReaderInvariant
namespace All
open PEqualNP.Outside.L_meta_1667
def decodeRule (i : Nat) :=
  let z := tokensAt i
  (z &&& 1023) ||| ((pointsAt (z >>> 10)) <<< 10)
def part (headers codes : Nat → Nat) (i : Nat) :=
  let data := headers i
  (List.range (data &&& 15)).map (fun j => decodeRule (codes ((data >>> 4)+j)))
def evidence (i : Nat) : PetersenReaderNear.GrantSet :=
  ⟨part signedOffsetsAt signedCodesAt (leftKeyAt i),part moduleOffsetsAt moduleCodesAt (rightKeyAt i)⟩
def db : Store := ⟨rowLayout,lookup,evidence⟩
end All
end PetersenReaderInvariant
