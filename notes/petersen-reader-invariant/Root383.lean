import BundleAll
namespace PetersenReaderInvariant
open PEqualNP.Outside.L_meta_1667
def tables383Checked :=
  ∀ k, 0 < k → k ≤ 13 → blockStored All.db k 0 (All.db.layout k).1=true

theorem tableRoot (ok : tables383Checked) :
    Excludes (targetOf g383) (outside lowerLabels) false 13 (vars 383).toFinset := by
  have rows (k : Nat) (hk : k ≤ 13) : ∀ i < (All.db.layout k).1, Accepted k (getRecord All.db k i) := by
    induction k with
    | zero => intro i hi; change i < 0 at hi; omega
    | succ k ih =>
      intro i hi
      apply storedOK All.db (k+1) i (by simpa using ih (by omega))
      exact insideBlock (ok (k+1) (by omega) hk) _ (by omega) (by simpa only [Nat.zero_add] using hi)
  have root := rows 13 (by decide) 0 (by decide +kernel)
  have seen : (getRecord All.db 13 0).seen = false := by decide +kernel
  have same : (state (getRecord All.db 13 0)).toFinset = (vars 383).toFinset := by decide +kernel
  unfold Accepted at root
  simpa only [seen,same] using root
end PetersenReaderInvariant
#print axioms PetersenReaderInvariant.tableRoot
