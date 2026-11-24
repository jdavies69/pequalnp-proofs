import Sym

namespace Replay2161

def gather (v : ℕ) : List ℕ → ℕ
  | [] => 0
  | j::xs => (if v.testBit j then 1 else 0) + 2*gather v xs

def assignRows (order : List ℕ) (i : Fin 512) : Fin 512 := Fin.ofNat 512 (gather i.val order)

structure Rotation {x : Word} {c : Charts x} (root : Frame c) where
  R : Automorphism x
  base : List Word
  eq : base=(root.v.map Wire.w).map R.p.q

def refCode (links : Array ℕ) (j : ℕ) := (links[j]?).getD 0

def linked {x : Word} {c : Charts x} (root : Frame c) (d : ℕ) (rows links : Array ℕ)
    (rot : Array (Rotation root)) (tag tape : ℕ) (f : Frame c) : Bool :=
  let k := tag/16-1
  refCode links k == 0 &&
    (rot[Nat.mod tag 16]?).any (fun A =>
      (rows[k]?).any (fun w => (root.replay d (w/65521)).any (fun g =>
        f.b==g.b && f.t==g.t && (bareReplay A.base d tape).isPerm (g.v.map Wire.w))))

def symRow {x : Word} {c : Charts x} (root : Frame c) (d : ℕ) (rows links : Array ℕ)
    (rot : Array (Rotation root)) (known : Frame c → Bool) (hops j : ℕ) :=
  let tag := refCode links j
  if tag=0 then fastRow root d rows known hops j else
    (rows[j]?).all (fun w => (root.replay d (w/65521)).all (linked root d rows links rot tag (w/65521)))

lemma linked_sound {x : Word} {c : Charts x} {root : Frame c} {d : ℕ} {rows links : Array ℕ}
    {rot : Array (Rotation root)} {tag tape : ℕ} {f : Frame c}
    (reps : ∀ (j w : ℕ), refCode links j=0 → rows[j]?=some w →
      ∀ g, root.replay d (w/65521)=some g → g.No)
    (he : root.replay d tape=some f) (h : linked root d rows links rot tag tape f=true) : f.No := by
  let k := tag/16-1
  obtain ⟨tagZero,rotHit⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨A,_,rowHit⟩ := (Option.any_eq_true ..).1 rotHit
  obtain ⟨word,ew,frameHit⟩ := (Option.any_eq_true ..).1 rowHit
  obtain ⟨g,eg,hit⟩ := (Option.any_eq_true ..).1 frameHit
  obtain ⟨bud,perm⟩ := Bool.and_eq_true_iff.mp hit
  obtain ⟨eb,et⟩ := Bool.and_eq_true_iff.mp bud
  have eb := beq_iff_eq.mp eb
  have et := beq_iff_eq.mp et
  have ng := reps k word (beq_iff_eq.mp tagZero) ew g eg
  have listEq : bareReplay A.base d tape=(f.v.map Wire.w).map A.R.p.q := by
    rw [A.eq,project_tape,←replay_words he]
  have eq : (wires f.v).image A.R.p.q = wires g.v := by
    ext a
    have p := (List.isPerm_iff.mp perm).mem_iff (a:=a)
    rw [listEq] at p
    simpa only [wires,List.mem_toFinset,List.mem_map,Finset.mem_image] using p
  intro hf
  have mapped := A.R.map_exact hf
  rw [eb,et,eq] at mapped
  exact ng mapped

lemma sym_table {x : Word} {c : Charts x} (hx : proper x) (root : Frame c) (vr : root.Valid)
    (d : ℕ) (rows links : Table) (rot : Array (Rotation root)) {known : Frame c → Bool}
    (sk : ∀ f, known f=true → f.No) (hops : ℕ)
    (h : Span (symRow root d rows links rot known hops) 0 rows.size) : TableSound root d rows := by
  have reps (j w : ℕ) (zero : refCode links j=0) (ew : rows[j]?=some w)
      (f : Frame c) (ef : root.replay d (w/65521)=some f) : f.No := by
    have hh := h j (Nat.zero_le _) (Array.getElem?_eq_some_iff.mp ew).choose
    have ck : Fast known hops f=true := by
      simpa only [symRow,zero,ite_true,fastRow,ew,Option.all_some,ef] using hh
    exact fast_sound known sk hx hops (Frame.replay_valid vr ef) ck
  intro j w ew f ef
  by_cases z : refCode links j=0
  · exact reps j w z ew f ef
  · have hh := h j (Nat.zero_le _) (Array.getElem?_eq_some_iff.mp ew).choose
    apply linked_sound reps ef (rot:=rot) (tag:=refCode links j)
    simpa only [symRow,z,ite_false,ew,Option.all_some,ef] using hh

end Replay2161
