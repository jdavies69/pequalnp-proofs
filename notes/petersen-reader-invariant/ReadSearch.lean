import ReadFold
import SymCheck
namespace Replay2161

def tightConflict {x : Word} {c : Charts x} (f : Frame c) :=
  (f.t==0 && f.b+1==f.v.length) && (flagFold f.v).ab != 0

lemma tight_sound {x : Word} {c : Charts x} {f : Frame c} (valid : f.Valid)
    (ok : tightConflict f=true) : f.No := by
  obtain ⟨small,hit⟩ := Bool.and_eq_true_iff.mp ok
  obtain ⟨t,width⟩ := Bool.and_eq_true_iff.mp small
  have h := certified_flags valid.1 (beq_iff_eq.mp width) hit
  change ¬ Exact x f.b f.t (wires f.v)
  rwa [beq_iff_eq.mp t]

def readCut {x : Word} {c : Charts x} (f : Frame c) :=
  immediate f.b f.t f.v f.ps || tightConflict f

lemma read_cut {x : Word} {c : Charts x} {f : Frame c} (v : f.Valid) (h : readCut f=true) : f.No := by
  rcases Bool.or_eq_true_iff.mp h with hi|hc
  · exact immediate_sound v.1 v.2 hi
  · exact tight_sound v hc

def ReadSearch {x : Word} {c : Charts x} (known : Frame c → Bool) : ℕ → Frame c → Bool
  | 0,f => readCut f || known f
  | k+1,f => readCut f ||
      (!(f.v.any (fun a => a.w == x)) && scan f (ReadSearch known k))

lemma read_sound {x : Word} {c : Charts x} (known : Frame c → Bool) (good : ∀ f, known f=true → f.No)
    (hx : proper x) (d : ℕ) {f : Frame c} (valid : f.Valid) (ok : ReadSearch known d f = true) : f.No := by
  induction d generalizing f with
  | zero =>
    rcases Bool.or_eq_true_iff.mp ok with h|h
    · exact read_cut valid h
    · exact good _ h
  | succ n ih =>
    rcases Bool.or_eq_true_iff.mp ok with h|q
    · exact read_cut valid h
    obtain ⟨no,rows⟩ := Bool.and_eq_true_iff.mp q
    intro hex
    rcases descend c hx hex with hm | ⟨s,hs,el,ht⟩
    · obtain ⟨w,hw,e⟩ := Step.mem_wires.mp hm
      have yes : f.v.any (fun a => a.w == x) = true := List.any_eq_true.mpr ⟨w,hw,beq_iff_eq.mpr e⟩
      simp [yes] at no
    · exact ih (Frame.child_valid valid el (Step.all_legal hs)) (scan_sound rows valid.1 hs el ht) ht

def readRow {x : Word} {c : Charts x} (root : Frame c) (d : ℕ) (a : Table)
    (known : Frame c → Bool) (hops j : ℕ) :=
  (a[j]?).all (fun w => (root.replay d (w/65521)).all (ReadSearch known hops))

def rSymRow {x : Word} {c : Charts x} (root : Frame c) (d : ℕ) (rows links : Array ℕ)
    (rot : Array (Rotation root)) (known : Frame c → Bool) (hops j : ℕ) :=
  let tag := refCode links j
  if tag=0 then readRow root d rows known hops j else
    (rows[j]?).all (fun w => (root.replay d (w/65521)).all (linked root d rows links rot tag (w/65521)))

lemma rSym_table {x : Word} {c : Charts x} (hx : proper x) (root : Frame c) (vr : root.Valid)
    (d : ℕ) (rows links : Table) (rot : Array (Rotation root)) {known : Frame c → Bool}
    (sk : ∀ f, known f=true → f.No) (hops : ℕ)
    (h : Span (rSymRow root d rows links rot known hops) 0 rows.size) : TableSound root d rows := by
  have reps (j w : ℕ) (zero : refCode links j=0) (ew : rows[j]?=some w)
      (f : Frame c) (ef : root.replay d (w/65521)=some f) : f.No := by
    have hh := h j (Nat.zero_le _) (Array.getElem?_eq_some_iff.mp ew).choose
    have ck : ReadSearch known hops f=true := by
      simpa only [rSymRow,zero,ite_true,readRow,ew,Option.all_some,ef] using hh
    exact read_sound known sk hx hops (Frame.replay_valid vr ef) ck
  intro j w ew f ef
  by_cases z : refCode links j=0
  · exact reps j w z ew f ef
  · have hh := h j (Nat.zero_le _) (Array.getElem?_eq_some_iff.mp ew).choose
    apply linked_sound reps ef (rot:=rot) (tag:=refCode links j)
    simpa only [rSymRow,z,ite_false,ew,Option.all_some,ef] using hh

end Replay2161
