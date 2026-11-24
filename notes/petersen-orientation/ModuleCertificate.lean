import OrientationExample
namespace PetersenOrientation
open Replay2161

def pairChart (x : Word) (a b : Fin 512) (ha : bit x a = true) (hb : bit x b = false) : Charts x :=
  ⟨fun _ => a, fun _ => b, fun _ => ha, fun _ => hb⟩

private def repeatedBit (b : Bool) : Word := if b then top else 0
private lemma repeated (b : Bool) (i : Fin 512) : bit (repeatedBit b) i = b := by
  cases b
  · exact bit_zero i
  · exact bit_top i

def liftWire {x : Word} (a b : Fin 512) (ha : bit x a = true) (hb : bit x b = false)
    (w : Word) : Wire (pairChart x a b ha hb) :=
  ⟨w, repeatedBit (bit w a), repeatedBit (bit w b), fun i => repeated _ i, fun i => repeated _ i⟩

theorem noShared {x : Word} (a b : Fin 512) (ha : bit x a = true) (hb : bit x b = false)
    (ws : List Word) (dict : Rows) (k blob : ℕ)
    (cover : ruled (ws.map (liftWire a b ha hb)) dict k blob = 2^(2^ws.length)-1) :
    ¬ Shared x ws.toFinset := by
  let v := ws.map (liftWire a b ha hb)
  have same : wires v = ws.toFinset := by simp [v,wires,List.map_map,liftWire,Function.comp_def]
  rintro ⟨u,w,eq,counts⟩
  let M : ModuleView x (wires v) := ⟨u,w,eq,by simpa only [same] using counts⟩
  have bad := ruled_clean v M dict k blob
  change ruled v dict k blob = _ at cover
  rw [cover,Nat.testBit_two_pow_sub_one] at bad
  exact (of_decide_eq_false bad) (by simpa [v] using picked_lt (fun w => M.chosen w.w) v)
end PetersenOrientation
