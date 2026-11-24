import ModuleCertificate

namespace PetersenOrientation
open Replay2161

def positiveCut (x : Word) (ws : List Word) : Witness → Bool
  | .inl (i,j) => rises x i j && ws.all (fun w => !rises w i j)
  | .inr (i,j,p) =>
    match ws[i]?, ws[j]? with
    | some a, some b => p.sig x == 25 &&
        ws.all (fun w => allowed (w==a) (w==b) (p.sig w))
    | _,_ => false

lemma positiveCutSound {x : Word} {ws : List Word} {r : Witness}
    (test : positiveCut x ws r = true) : ¬ Linear x ws.toFinset := by
  rintro ⟨tree,val,mass⟩
  have member {w} (used : 0 < tree.mass (weight w)) : w ∈ ws := by
    by_contra h
    simp [mass,h] at used
  rcases r with ⟨i,j⟩ | ⟨i,j,p⟩
  · obtain ⟨rise,none⟩ := Bool.and_eq_true_iff.mp test
    obtain ⟨w,used,up⟩ := tree.source id (val ▸ rise)
    have no := List.all_eq_true.mp none w (member used)
    change (!rises w i j) = true at no
    simpa [show rises w i j=true from up] using no
  · simp only [positiveCut] at test
    cases ai : ws[i]? with
    | none => simp [ai] at test
    | some a =>
      cases bj : ws[j]? with
      | none => simp [ai,bj] at test
      | some b =>
        rw [ai,bj] at test
        obtain ⟨eq,all⟩ := Bool.and_eq_true_iff.mp test
        have limit (w : Word) : tree.mass (weight w) ≤ 1 := by rw [mass]; split <;> omega
        have hit := tree.gateMarks id p a b (limit a) (limit b) (by
          intro w used
          have hw := List.all_eq_true.mp all w (member used)
          have dec (u : Word) : decide (w=u) = (w==u) := by
            by_cases h : w=u
            · simp [h]
            · simp [h,beq_eq_false_iff_ne.mpr h]
          simpa only [dec,id_eq] using hw)
        rw [val, beq_iff_eq.mp eq] at hit
        revert hit
        generalize decide (0 < tree.mass (weight a))=qa
        generalize decide (0 < tree.mass (weight b))=qb
        cases qa <;> cases qb <;> decide

theorem noTight {x : Word} {S : Finset Word} {k : ℕ}
    (width : k+1 ≤ S.card) (cut : ¬ Linear x S) : PEqualNP.Outside.L_meta_1667.Impossible x k S := by
  intro n t hn run
  obtain ⟨b,eq,live⟩ := countKinds run
  have bound := count_live live
  exact cut (linear_of_tight live (by omega) (by omega))

end PetersenOrientation
#print axioms PetersenOrientation.noTight
