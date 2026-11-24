import ModuleCut
import Partitions
import LocalAtlas
namespace Replay2161

def chartIndex (blob i : ℕ) : Fin 512 := Fin.ofNat 512 ((blob >>> (9*i)) &&& 511)
def localPoint (blob : ℕ) : TracePoint := ⟨fun i=>chartIndex blob i.val⟩

def orderMask {x : Word} {c : Charts x} (v : List (Wire c)) (a b q r : Fin 512) :=
  if rises x a b && rises x q r then
    patterns (fun w inner=> if inner then !(rises w.w a r) else !(rises w.w a b || rises w.w q r)) v
  else 0
lemma order_clean {x : Word} {c : Charts x} (v : List (Wire c)) (M : ModuleView x (wires v))
    (a b q r : Fin 512) : (orderMask v a b q r).testBit (picked (fun w=>M.chosen w.w) v)=false := by
  unfold orderMask; split
  · rename_i ok; obtain ⟨p₁,p₂⟩:=Bool.and_eq_true_iff.mp ok
    by_contra nope
    have good:=pattern_true _ _ _ (Bool.eq_true_of_not_eq_false nope)
    exact M.order_exclusion a b q r p₁ p₂ (by
      intro w hw pin; obtain ⟨u,hu,rfl⟩:=Step.mem_wires.mp hw
      simpa only [pin,ite_true,Bool.not_eq_true'] using good u hu) (by
      intro w hw ext; obtain ⟨u,hu,rfl⟩:=Step.mem_wires.mp hw
      simpa only [ext,Bool.false_eq_true,ite_false,Bool.not_eq_true',Bool.or_eq_false_iff] using good u hu)
  · simp

def edgeGate {x : Word} {c : Charts x} (v : List (Wire c)) (a b : Wire c) (p : TracePoint) :=
  a.w != b.w && p.sig x == 25 && wordLeft (p.sig a.w) && wordRight (p.sig b.w) &&
    v.all (fun w=>w.w==a.w || w.w==b.w || wordGrey (p.sig w.w))
def sideMask {x : Word} {c : Charts x} (v : List (Wire c)) (a b : Word) (inside : Bool) :=
  patterns (fun w pick=> !(w.w==a || w.w==b) || pick==inside) v
lemma side_clean {x : Word} {c : Charts x} {v : List (Wire c)} (M : ModuleView x (wires v))
    {a b : Wire c} (ha : a∈v) (hb : b∈v) (ne : M.chosen a.w≠M.chosen b.w) (inside : Bool) :
    (sideMask v a.w b.w inside).testBit (picked (fun w=>M.chosen w.w) v)=false := by
  by_contra no
  have h:=pattern_true _ _ _ (Bool.eq_true_of_not_eq_false no)
  have aa : M.chosen a.w=inside := by simpa using h _ ha
  have bb : M.chosen b.w=inside := by simpa using h _ hb
  exact ne (aa.trans bb.symm)

def edgeMask {x : Word} {c : Charts x} (v : List (Wire c)) (i j : ℕ) (p : TracePoint) :=
  match v[i]?,v[j]? with
  | some a,some b => if edgeGate v a b p then sideMask v a.w b.w true ||| sideMask v a.w b.w false else 0
  | _,_ => 0
lemma edge_clean {x : Word} {c : Charts x} (v : List (Wire c)) (M : ModuleView x (wires v))
    (i j : ℕ) (p : TracePoint) : (edgeMask v i j p).testBit (picked (fun w=>M.chosen w.w) v)=false := by
  unfold edgeMask
  cases pa : v[i]? with
  | none=>simp
  | some a=>cases pb : v[j]? with
    | none=>simp
    | some b=>
      simp only; split
      · rename_i good
        obtain ⟨checks,rest⟩:=Bool.and_eq_true_iff.mp good
        obtain ⟨checks,rb⟩:=Bool.and_eq_true_iff.mp checks
        obtain ⟨checks,la⟩:=Bool.and_eq_true_iff.mp checks
        obtain ⟨ne,tar⟩:=Bool.and_eq_true_iff.mp checks
        have am:=List.mem_of_getElem? pa; have bm:=List.mem_of_getElem? pb
        have neq:=M.edge p a.w b.w (beq_iff_eq.mp tar) (Step.mem_wires.mpr ⟨a,am,rfl⟩) (Step.mem_wires.mpr ⟨b,bm,rfl⟩) (bne_iff_ne.mp ne) la rb (by
          intro w hw ea eb; obtain ⟨u,hu,rfl⟩:=Step.mem_wires.mp hw
          simpa only [beq_eq_false_iff_ne.mpr ea,beq_eq_false_iff_ne.mpr eb,Bool.false_or] using List.all_eq_true.mp rest u hu)
        rw [Nat.testBit_or,side_clean M am bm neq,side_clean M am bm neq]; rfl
      · simp

def ruleMask {x : Word} {c : Charts x} (v : List (Wire c)) (dict : Rows) (token : ℕ) :=
  let data:=fetchRow dict (token >>> 8)
  let blob:=data >>> 1
  if data.testBit 0 then edgeMask v (token &&& 15) ((token >>> 4) &&& 15) (localPoint blob)
  else orderMask v (chartIndex blob 0) (chartIndex blob 1) (chartIndex blob 2) (chartIndex blob 3)
lemma rule_clean {x : Word} {c : Charts x} (v : List (Wire c)) (M : ModuleView x (wires v))
    (dict : Rows) (token : ℕ) : (ruleMask v dict token).testBit (picked (fun w=>M.chosen w.w) v)=false := by
  dsimp only [ruleMask]; split
  · exact edge_clean v M ..
  · exact order_clean v M ..

def ruled {x : Word} {c : Charts x} (v : List (Wire c)) (dict : Rows) : ℕ→ℕ→ℕ
  | 0,_=>0
  | k+1,blob=>if blob=0 then 0 else ruleMask v dict (blob &&& 0xfffff) ||| ruled v dict k (blob >>> 20)
lemma ruled_clean {x : Word} {c : Charts x} (v : List (Wire c)) (M : ModuleView x (wires v))
    (dict : Rows) (k blob : ℕ) : (ruled v dict k blob).testBit (picked (fun w=>M.chosen w.w) v)=false := by
  induction k generalizing blob with
  | zero=>simp [ruled]
  | succ k ih=>rw [ruled]; split
               · simp
               · rw [Nat.testBit_or,rule_clean v M,ih]; rfl

def grant {x : Word} {c : Charts x} (f : Frame c) (dict : Rows) (blob : ℕ) :=
  f.t==0 && decide (f.b≤f.v.length) && ruled f.v dict 30 blob == 2^(2^f.v.length)-1
lemma grant_sound {x : Word} {c : Charts x} (f : Frame c) (v : f.Valid) (dict : Rows) (blob : ℕ)
    (h : grant f dict blob=true) : f.No := by
  obtain ⟨⟨nt,q⟩,coverAll⟩:=(Bool.and_eq_true_iff.mp h).imp_left Bool.and_eq_true_iff.mp
  have nt:=beq_iff_eq.mp nt; have q:=of_decide_eq_true q
  rintro ⟨n,hn,t,ht,live⟩
  have card : (wires f.v).card=f.v.length := by
    change (f.v.map Wire.w).toFinset.card=f.v.length; rw [List.toFinset_card_of_nodup v.1,List.length_map]
  obtain ⟨u,w,eq,counts⟩:=shared_of_width live (by omega) (by omega)
  let M: ModuleView x (wires f.v):=⟨u,w,eq,counts⟩
  have bad:=ruled_clean f.v M dict 30 blob
  rw [beq_iff_eq.mp coverAll,Nat.testBit_two_pow_sub_one] at bad
  exact (of_decide_eq_false bad) (picked_lt _ _)
end Replay2161
