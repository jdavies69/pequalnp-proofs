import SmallTables
import TraceCircuit
import TracedOptimal
namespace PetersenReaderTrace
open PetersenReaderGrammar PEqualNP.Outside.L_meta_1667 PetersenReaderInvariant
set_option maxRecDepth 16384
set_option maxHeartbeats 0
def toLocal (r : Fin 512) : Fin 256 := Fin.ofNat 256 ((0xfffbfdf9fefafcf8efebede9eeeaece8bfbbbdb9bebabcb8afabada9aeaaaca8f7f3f5f1f6f2f4f0e7e3e5e1e6e2e4e0b7b3b5b1b6b2b4b0a7a3a5a1a6a2a4a0dfdbddd9dedadcd8cfcbcdc9cecaccc89f9b9d999e9a9c988f8b8d898e8a8c88d7d3d5d1d6d2d4d0c7c3c5c1c6c2c4c097939591969294908783858186828480fffbfdf9fefafcf8efebede9eeeaece8bfbbbdb9bebabcb8afabada9aeaaaca8f7f3f5f1f6f2f4f0e7e3e5e1e6e2e4e0b7b3b5b1b6b2b4b0a7a3a5a1a6a2a4a0dfdbddd9dedadcd8cfcbcdc9cecaccc89f9b9d999e9a9c988f8b8d898e8a8c88d7d3d5d1d6d2d4d0c7c3c5c1c6c2c4c0979395919692949087838581868284807f7b7d797e7a7c786f6b6d696e6a6c683f3b3d393e3a3c382f2b2d292e2a2c2877737571767274706763656166626460373335313632343027232521262224205f5b5d595e5a5c584f4b4d494e4a4c481f1b1d191e1a1c180f0b0d090e0a0c0857535551565254504743454146424440171315111612141007030501060204007f7b7d797e7a7c786f6b6d696e6a6c683f3b3d393e3a3c382f2b2d292e2a2c2877737571767274706763656166626460373335313632343027232521262224205f5b5d595e5a5c584f4b4d494e4a4c481f1b1d191e1a1c180f0b0d090e0a0c085753555156525450474345414642444017131511161214100703050106020400 >>> (8*r.val)) &&& 255)
def toGlobal (r : Fin 256) : Fin 512 := Fin.ofNat 512 ((0xbfdeefb79bf5eaf978afd6ebb59af56ab958bbdceeb71bb5cae970abd4eab51ab54aa9509fcee7b399f4ea79388fc6e3b198f46a39189bcce6b319b4ca69308bc4e2b118b44a2910b7daedb69b75aad968a7d2e9b49a752a9948b3d8ecb61b358ac960a3d0e8b41a350a894097cae5b29974aa592887c2e1b098742a190893c8e4b219348a492083c0e0b018340a09003f9ecfa793f1e8f8782f96cba592f168b8583b9ccea713b1c8e8702b94caa512b148a8501f8ec7a391f0e878380f86c3a190f06838181b8cc6a311b0c868300b84c2a110b0482810379acda69371a8d8682792c9a492712898483398cca6133188c8602390c8a41231088840178ac5a29170a858280782c1a090702818081388c4a211308848200380c0a01030080800 >>> (9*r.val)) &&& 511)

def extendWord (w : Low) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn (fun r : Fin 512=>w.getLsbD (toLocal r).val))).cast List.length_ofFn

lemma extend_at (w : Low) (r : Fin 512) : (extendWord w).getLsbD r.val = w.getLsbD (toLocal r).val := by
  simp only [extendWord,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [r.isLt]

theorem local_global : ∀ r : Fin 256, toLocal (toGlobal r)=r := by decide +kernel
theorem extend_injective : Function.Injective extendWord := by
  intro x y e
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  let r : Fin 256:=⟨i,hi⟩
  have h:=congrArg (fun (v : Sig) => v.getLsbD (toGlobal r).val) e
  simpa only [extend_at,local_global] using h

theorem extend_zero : extendWord 0=zero := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  exact (extend_at 0 ⟨i,hi⟩).trans (by simp [zero])

theorem extend_bin (d : Bool) (a b : Low) :
    extendWord (binary d a b)=bin d (extendWord a) (extendWord b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  let r : Fin 512:=⟨i,hi⟩
  change (extendWord _).getLsbD r.val=(bin _ _ _).getLsbD r.val
  cases d <;> simp only [bin,binary,Bool.false_eq_true,ite_false,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_or,extend_at]

theorem extend_neg (a : Low) : extendWord (~~~a)=neg (extendWord a) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  let r : Fin 512:=⟨i,hi⟩
  change (extendWord _).getLsbD r.val=(neg _).getLsbD r.val
  simp only [neg,extend_at,BitVec.getLsbD_not,Fin.isLt,decide_true,Bool.true_and]

theorem extend_one : extendWord (BitVec.allOnes 256)=one := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  exact (extend_at _ ⟨i,hi⟩).trans (by simp only [one,BitVec.getLsbD_allOnes,Fin.isLt,hi,decide_true])

def lowBank (b : Bank) := b.map (fun x => extendWord x.1)
lemma low_get (b : Bank) (i : ℕ) : (lowBank b).getD i zero=extendWord (b.getD i z).1 := by
  simp only [lowBank,List.getD_eq_getElem?_getD,List.getElem?_map]
  cases b[i]? <;> first | exact extend_zero.symm | rfl

theorem bank_regular (b : Bank) (g : PEqualNP.CircuitLowerBounds.Gate)
    (size : g.inputs.length≤2) :
    extendWord (eval g b).1 = gv (lowBank b) g := by
  obtain ⟨op,ins⟩:=g
  change ins.length≤2 at size
  rcases ins with _|⟨i,_|⟨j,_|⟨k,rs⟩⟩⟩
  all_goals first | simp at size | skip
  all_goals cases op <;> simp only [eval,gv,low_get,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,List.headD_nil,List.headD_cons,PetersenReaderTrace.op,o,z,flip,extend_neg,extend_bin,extend_zero,extend_one]

theorem goalWord : extendWord (word goal) = targetOf g383 := by decide +kernel
theorem rootMembers : (lowBank initial).toFinset=insert zero (vars 383).toFinset := by decide +kernel
def extendedLabels := (List.finRange 63).map (fun a => extendWord (word a))
set_option maxRecDepth 30000 in
theorem labelSet : extendedLabels.toFinset=lowerLabels.toFinset := by decide +kernel

theorem goodWord {w : Low} (good : outside lowerLabels (extendWord w)=false) : ∃ a, w=word a := by
  have mem : extendWord w ∈ lowerLabels.toFinset := by simpa [outside] using good
  rw [←labelSet] at mem
  obtain ⟨a,_,eq⟩ := List.mem_map.mp (List.mem_toFinset.mp mem)
  exact ⟨a,(extend_injective eq).symm⟩

end PetersenReaderTrace
#print axioms PetersenReaderTrace.goodWord
