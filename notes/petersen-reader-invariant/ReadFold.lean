import ReadMask
namespace Replay2161

structure Flags where
  grey : Patch
  a : Patch
  b : Patch
  ab : Patch

def flagFold {x : Word} {c : Charts x} : List (Wire c) → Flags
  | [] => ⟨BitVec.allOnes 36,0,0,0⟩
  | w::v =>
    let f := flagFold v
    let g := pGrey w
    let a := pLeft w
    let b := pRight w
    ⟨g &&& f.grey,(g &&& f.a) ||| (a &&& f.grey),(g &&& f.b) ||| (b &&& f.grey),
      (g &&& f.ab) ||| (a &&& f.b) ||| (b &&& f.a)⟩

def AllGrey {x : Word} {c : Charts x} (k : Fin 36) (v : List (Wire c)) :=
  ∀ w∈v, (pGrey w)[k.val]=true
def OneSlot {x : Word} {c : Charts x} (mark : Wire c→Patch) (k : Fin 36) (v : List (Wire c)) :=
  ∃ a∈v, (mark a)[k.val]=true ∧ ∀ w∈v, w.w≠a.w → (pGrey w)[k.val]=true
def TwoSlots {x : Word} {c : Charts x} (ma mb : Wire c→Patch) (k : Fin 36) (v : List (Wire c)) :=
  ∃ a∈v, ∃ b∈v, a.w≠b.w ∧ (ma a)[k.val]=true ∧ (mb b)[k.val]=true ∧
    ∀ w∈v, w.w≠a.w → w.w≠b.w → (pGrey w)[k.val]=true

lemma next_grey {x : Word} {c : Charts x} {k} {v : List (Wire c)} {w : Wire c}
    (h : (pGrey w)[k.val]=true) (hg : AllGrey k v) : AllGrey k (w::v) := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl|hq
  · exact h
  · exact hg q hq

lemma one_grey {x : Word} {c : Charts x} {k} {v : List (Wire c)} {w : Wire c} {mark}
    (h : (pGrey w)[k.val]=true) (hg : OneSlot mark k v) : OneSlot mark k (w::v) := by
  obtain ⟨a,ha,hm,hg⟩ := hg
  refine ⟨a,List.mem_cons_of_mem _ ha,hm,?_⟩
  intro q hq nq
  rcases List.mem_cons.mp hq with rfl|hq
  · exact h
  · exact hg q hq nq

lemma one_pick {x : Word} {c : Charts x} {k} {v : List (Wire c)} {w : Wire c} {mark : Wire c→Patch}
    (h : (mark w)[k.val]=true) (hg : AllGrey k v) : OneSlot mark k (w::v) := by
  refine ⟨w,List.mem_cons_self,h,?_⟩
  intro q hq nq
  exact hg q ((List.mem_cons.mp hq).resolve_left (by rintro rfl; exact nq rfl))

lemma two_grey {x : Word} {c : Charts x} {k} {v : List (Wire c)} {w : Wire c} {ma mb}
    (h : (pGrey w)[k.val]=true) (hg : TwoSlots ma mb k v) : TwoSlots ma mb k (w::v) := by
  obtain ⟨a,ha,b,hb,ne,pa,pb,hg⟩ := hg
  refine ⟨a,List.mem_cons_of_mem _ ha,b,List.mem_cons_of_mem _ hb,ne,pa,pb,?_⟩
  intro q hq qa qb
  rcases List.mem_cons.mp hq with rfl|hq
  · exact h
  · exact hg q hq qa qb

lemma two_pick {x : Word} {c : Charts x} {k} {v : List (Wire c)} {w : Wire c} {ma mb : Wire c→Patch}
    (nw : w.w∉wires v) (h : (ma w)[k.val]=true) (hg : OneSlot mb k v) : TwoSlots ma mb k (w::v) := by
  obtain ⟨a,ha,pa,hg⟩ := hg
  have ne : w.w≠a.w := fun eq => nw (Step.mem_wires.mpr ⟨a,ha,eq.symm⟩)
  refine ⟨w,List.mem_cons_self,a,List.mem_cons_of_mem _ ha,ne,h,pa,?_⟩
  intro q hq qw qa
  exact hg q ((List.mem_cons.mp hq).resolve_left (by rintro rfl; exact qw rfl)) qa

lemma two_swap {x : Word} {c : Charts x} {k} {v : List (Wire c)} {ma mb}
    (h : TwoSlots ma mb k v) : TwoSlots mb ma k v := by
  obtain ⟨a,ha,b,hb,n,pa,pb,hh⟩ := h
  exact ⟨b,hb,a,ha,n.symm,pb,pa,fun q hq qb qa => hh q hq qa qb⟩

lemma flags_sound {x : Word} {c : Charts x} (k : Fin 36) (v : List (Wire c)) (nd : (v.map Wire.w).Nodup) :
    ((flagFold v).grey[k.val]=true → AllGrey k v) ∧
    ((flagFold v).a[k.val]=true → OneSlot pLeft k v) ∧
    ((flagFold v).b[k.val]=true → OneSlot pRight k v) ∧
    ((flagFold v).ab[k.val]=true → TwoSlots pLeft pRight k v) := by
  induction v with
  | nil => simp [AllGrey,flagFold]
  | cons w l ih =>
    obtain ⟨nw,nl⟩ := List.nodup_cons.mp nd
    have nm : w.w∉wires l := fun hh => nw (List.mem_toFinset.mp hh)
    obtain ⟨ig,ia,ib,iab⟩ := ih nl
    simp only [flagFold,BitVec.getElem_and,BitVec.getElem_or,Bool.and_eq_true,Bool.or_eq_true]
    refine ⟨fun ⟨wG,g⟩ => next_grey wG (ig g),?_,?_,?_⟩
    · rintro (⟨wg,a⟩|⟨wa,g⟩)
      · exact one_grey wg (ia a)
      · exact one_pick wa (ig g)
    · rintro (⟨wg,b⟩|⟨wb,g⟩)
      · exact one_grey wg (ib b)
      · exact one_pick wb (ig g)
    · rintro ((⟨wg,ab⟩|⟨wa,b⟩)|⟨wb,a⟩)
      · exact two_grey wg (iab ab)
      · exact two_pick nm wa (ib b)
      · exact two_swap (two_pick nm wb (ia a))

lemma grey_rest_of {x : Word} {c : Charts x} {a b : Word} {v : List (Wire c)} {k : Fin 36}
    (h : ∀ w∈v, w.w≠a → w.w≠b → (pGrey w)[k.val]=true) : (greyRest a b v)[k.val]=true := by
  induction v with
  | nil => exact BitVec.getElem_allOnes k.val k.isLt
  | cons w l ih =>
    have tl := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    by_cases ea : w.w=a
    · simp [greyRest,ea,tl]
    by_cases eb : w.w=b
    · simp [greyRest,eb,tl]
    have ww := h w List.mem_cons_self ea eb
    simp only [greyRest,beq_eq_false_iff_ne.mpr ea,beq_eq_false_iff_ne.mpr eb,Bool.false_or,
      Bool.false_eq_true,ite_false,BitVec.getElem_and,ww,tl,Bool.true_and]

lemma certified_flags {x : Word} {c : Charts x} {v : List (Wire c)} {b : ℕ}
    (nd : (v.map Wire.w).Nodup) (width : b+1=v.length) (hit : (flagFold v).ab != 0) :
    ¬Exact x b 0 (wires v) := by
  obtain ⟨k,hk⟩ := uncovered (bne_iff_ne.mp hit)
  obtain ⟨a,ha,z,hz,nz,pa,pz,gy⟩ := (flags_sound k v nd).2.2.2 hk
  apply no_readOnce nd width
  apply List.any_eq_true.mpr
  refine ⟨a,ha,List.any_eq_true.mpr ⟨z,hz,Bool.and_eq_true_iff.mpr ⟨bne_iff_ne.mpr nz,?_⟩⟩⟩
  apply bne_iff_ne.mpr
  intro eq
  have h := congrArg (fun u : Patch => u[k.val]) eq
  simp only [BitVec.getElem_and,pa,pz,grey_rest_of gy,Bool.true_and] at h
  exact Bool.noConfusion (h.trans (BitVec.getElem_zero k.isLt))

end Replay2161
