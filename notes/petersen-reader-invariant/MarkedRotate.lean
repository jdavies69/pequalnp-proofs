import MarkedNodes
namespace PetersenReaderInvariant
open PEqualNP.Outside.L_meta_1667
def outside (labels : List Sig) (v : Sig) := !(labels.contains v)
theorem markedRename {T bad k t S seen} (h : Marked T bad k t S seen) (f : Row → Row) (onto : Function.Surjective f)
    (stable : ∀ w, bad (rename f w) = bad w) : Marked (rename f T) bad k t (S.image (rename f)) seen := by
  have inj := rename_inj f onto
  obtain ⟨fz,fo⟩ := rename_constants f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h with
  | stop hp => simpa using Marked.stop (pp _ hp)
  | @unary g k t U a hp hf _ ih =>
    have fresh : rename f (neg a) ∉ (insert a U).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_neg] at fresh ih ⊢
    apply Marked.unary (pp _ hp) fresh
    simpa only [←rename_neg f a,stable] using ih
  | @binary g k t U a b d ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    apply Marked.binary (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh
    simpa only [←rename_bin f d a b,stable] using ih

theorem rotated {T n seen} {ws labels : List Sig} (hi : Excludes T (outside labels) seen n ws.toFinset)
    (p : List Move) (ok : autoOK T p = true)
    (valid : labels.all (fun w => labels.contains (movedWord p w) && labels.contains (movedWord p.reverse w))=true) : Excludes T (outside labels) seen n (ws.map (movedWord p.reverse)).toFinset := by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p) := fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k t hk h
  have goal : rename (movedRow p) T = T := (moved_eq_rename p T).symm.trans ok.1.1
  have inv (x : Sig) : rename (movedRow p) (movedWord p.reverse x) = x := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j,hj⟩ _ = bit ⟨j,hj⟩ _
    rw [bit_rename,bit_moved,composed_id ok.1.2]
  have stable (a : Sig) : outside labels (rename (movedRow p) a) = outside labels a := by
    have yes : rename (movedRow p) a ∈ labels ↔ a ∈ labels := by
      constructor
      · intro ha
        have reverse := (Bool.and_eq_true_iff.mp (List.all_eq_true.mp valid _ ha)).2
        have id : movedWord p.reverse (rename (movedRow p) a) = a := by
          apply (rename_inj (movedRow p) onto)
          exact inv _
        exact List.contains_iff_mem.mp (id ▸ reverse)
      · intro ha
        rw [←moved_eq_rename]
        exact List.contains_iff_mem.mp ((Bool.and_eq_true_iff.mp (List.all_eq_true.mp valid _ ha)).1)
    simp [outside,List.contains_eq_mem,yes]
  have run := markedRename h (movedRow p) onto stable
  have back : (ws.map (movedWord p.reverse)).toFinset.image (rename (movedRow p)) = ws.toFinset := by
    ext a
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩
      simpa only [inv] using hw
    · intro ha
      exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k t hk run

end PetersenReaderInvariant
#print axioms PetersenReaderInvariant.rotated
