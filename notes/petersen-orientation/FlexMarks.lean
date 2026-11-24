import ReadFold
namespace Replay2161
def maskFold {x : Word} {c : Charts x} (gray left right : Wire c→Patch) : List (Wire c) → Flags
  | [] => ⟨BitVec.allOnes 36,0,0,0⟩
  | w::v =>
    let f := maskFold gray left right v
    let g := gray w
    let a := left w
    let b := right w
    ⟨g &&& f.grey,(g &&& f.a) ||| (a &&& f.grey),(g &&& f.b) ||| (b &&& f.grey),
      (g &&& f.ab) ||| (a &&& f.b) ||| (b &&& f.a)⟩

def MaskGrey {x : Word} {c : Charts x} (gray : Wire c→Patch) (k : Fin 36) (v : List (Wire c)) :=
  ∀ w∈v, (gray w)[k.val]=true
def MaskOne {x : Word} {c : Charts x} (gray : Wire c→Patch) (mark : Wire c→Patch) (k : Fin 36) (v : List (Wire c)) :=
  ∃ a∈v, (mark a)[k.val]=true ∧ ∀ w∈v, w.w≠a.w → (gray w)[k.val]=true
def MaskTwo {x : Word} {c : Charts x} (gray : Wire c→Patch) (ma mb : Wire c→Patch) (k : Fin 36) (v : List (Wire c)) :=
  ∃ a∈v, ∃ b∈v, a.w≠b.w ∧ (ma a)[k.val]=true ∧ (mb b)[k.val]=true ∧
    ∀ w∈v, w.w≠a.w → w.w≠b.w → (gray w)[k.val]=true

lemma mask_next {x : Word} {c : Charts x} {gray : Wire c→Patch} {k} {v : List (Wire c)} {w : Wire c}
    (h : (gray w)[k.val]=true) (hg : MaskGrey gray k v) : MaskGrey gray k (w::v) := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl|hq
  · exact h
  · exact hg q hq

lemma mask_onegrey {x : Word} {c : Charts x} {gray : Wire c→Patch} {k} {v : List (Wire c)} {w : Wire c} {mark}
    (h : (gray w)[k.val]=true) (hg : MaskOne gray mark k v) : MaskOne gray mark k (w::v) := by
  obtain ⟨a,ha,hm,hg⟩ := hg
  refine ⟨a,List.mem_cons_of_mem _ ha,hm,?_⟩
  intro q hq nq
  rcases List.mem_cons.mp hq with rfl|hq
  · exact h
  · exact hg q hq nq

lemma mask_onepick {x : Word} {c : Charts x} {gray : Wire c→Patch} {k} {v : List (Wire c)} {w : Wire c} {mark : Wire c→Patch}
    (h : (mark w)[k.val]=true) (hg : MaskGrey gray k v) : MaskOne gray mark k (w::v) := by
  refine ⟨w,List.mem_cons_self,h,?_⟩
  intro q hq nq
  exact hg q ((List.mem_cons.mp hq).resolve_left (by rintro rfl; exact nq rfl))

lemma mask_twogrey {x : Word} {c : Charts x} {gray : Wire c→Patch} {k} {v : List (Wire c)} {w : Wire c} {ma mb}
    (h : (gray w)[k.val]=true) (hg : MaskTwo gray ma mb k v) : MaskTwo gray ma mb k (w::v) := by
  obtain ⟨a,ha,b,hb,ne,pa,pb,hg⟩ := hg
  refine ⟨a,List.mem_cons_of_mem _ ha,b,List.mem_cons_of_mem _ hb,ne,pa,pb,?_⟩
  intro q hq qa qb
  rcases List.mem_cons.mp hq with rfl|hq
  · exact h
  · exact hg q hq qa qb

lemma mask_twopick {x : Word} {c : Charts x} {gray : Wire c→Patch} {k} {v : List (Wire c)} {w : Wire c} {ma mb : Wire c→Patch}
    (nw : w.w∉wires v) (h : (ma w)[k.val]=true) (hg : MaskOne gray mb k v) : MaskTwo gray ma mb k (w::v) := by
  obtain ⟨a,ha,pa,hg⟩ := hg
  have ne : w.w≠a.w := fun eq => nw (Step.mem_wires.mpr ⟨a,ha,eq.symm⟩)
  refine ⟨w,List.mem_cons_self,a,List.mem_cons_of_mem _ ha,ne,h,pa,?_⟩
  intro q hq qw qa
  exact hg q ((List.mem_cons.mp hq).resolve_left (by rintro rfl; exact qw rfl)) qa

lemma mask_swap {x : Word} {c : Charts x} {gray : Wire c→Patch} {k} {v : List (Wire c)} {ma mb}
    (h : MaskTwo gray ma mb k v) : MaskTwo gray mb ma k v := by
  obtain ⟨a,ha,b,hb,n,pa,pb,hh⟩ := h
  exact ⟨b,hb,a,ha,n.symm,pb,pa,fun q hq qb qa => hh q hq qa qb⟩

lemma mask_sound {x : Word} {c : Charts x} (gray left right : Wire c→Patch) (k : Fin 36) (v : List (Wire c)) (nd : (v.map Wire.w).Nodup) :
    ((maskFold gray left right v).grey[k.val]=true → MaskGrey gray k v) ∧
    ((maskFold gray left right v).a[k.val]=true → MaskOne gray left k v) ∧
    ((maskFold gray left right v).b[k.val]=true → MaskOne gray right k v) ∧
    ((maskFold gray left right v).ab[k.val]=true → MaskTwo gray left right k v) := by
  induction v with
  | nil => simp [MaskGrey,maskFold]
  | cons w l ih =>
    obtain ⟨nw,nl⟩ := List.nodup_cons.mp nd
    have nm : w.w∉wires l := fun hh => nw (List.mem_toFinset.mp hh)
    obtain ⟨ig,ia,ib,iab⟩ := ih nl
    simp only [maskFold,BitVec.getElem_and,BitVec.getElem_or,Bool.and_eq_true,Bool.or_eq_true]
    refine ⟨fun ⟨wG,g⟩ => mask_next wG (ig g),?_,?_,?_⟩
    · rintro (⟨wg,a⟩|⟨wa,g⟩)
      · exact mask_onegrey wg (ia a)
      · exact mask_onepick wa (ig g)
    · rintro (⟨wg,b⟩|⟨wb,g⟩)
      · exact mask_onegrey wg (ib b)
      · exact mask_onepick wb (ig g)
    · rintro ((⟨wg,ab⟩|⟨wa,b⟩)|⟨wb,a⟩)
      · exact mask_twogrey wg (iab ab)
      · exact mask_twopick nm wa (ib b)
      · exact mask_swap (mask_twopick nm wb (ia a))

end Replay2161
