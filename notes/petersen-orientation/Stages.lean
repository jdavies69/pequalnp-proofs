import Verify

namespace Replay2161

def vanished (keep : Bool) (a : Word) : Finset Word := if keep then ∅ else {a}
def debit (keep : Bool) := if keep then 0 else 1
lemma vanishes (keep : Bool) (a : Word) : (vanished keep a).card = debit keep := by
  cases keep <;> simp [vanished,debit]

def Step.discard {x : Word} {c : Charts x} : Step c → Finset Word
  | .flip a ka => vanished ka a.w
  | .binary _ a w ka kb => vanished ka a.w ∪ vanished kb w.w

def Step.drops {x : Word} {c : Charts x} : Step c → ℕ
  | .flip _ ka => debit ka
  | .binary _ _ _ ka kb => debit ka + debit kb

lemma discard_le {x : Word} {c : Charts x} (s : Step c) : s.discard.card ≤ s.drops := by
  cases s with
  | flip a ka => exact (vanishes ka a.w).le
  | binary d a b ka kb =>
    exact (Finset.card_union_le ..).trans (by simp only [Step.drops,vanishes,le_refl])

lemma rest_inclusion {x : Word} {c : Charts x} (s : Step c) (v : List (Wire c)) :
    wires v ⊆ wires (s.rest v) ∪ s.discard := by
  intro a ha
  obtain ⟨w,hw,rfl⟩ := Step.mem_wires.mp ha
  by_cases keepW : w ∈ s.rest v
  · exact Finset.mem_union_left _ (Step.mem_wires.mpr ⟨w,keepW,rfl⟩)
  · apply Finset.mem_union_right
    cases s with
    | flip a ka =>
      cases ka <;> simp_all [Step.discard,Step.rest,vanished,List.mem_filter]
    | binary d a b ka kb =>
      cases ka <;> cases kb <;> simp_all [Step.discard,Step.rest,vanished,List.mem_filter]
      all_goals tauto

lemma fits_step {x : Word} {c : Charts x} {b t} (v : List (Wire c)) (s : Step c)
    (nd : (v.map Wire.w).Nodup) (el : eligible v s) (h : Exact x (s.budget b t).1
      (s.budget b t).2 (wires (s.after v))) :
    v.length+1 ≤ (s.budget b t).1+1+s.drops := by
  have le₁ := Finset.card_le_card (rest_inclusion s v)
  have le₂ := Finset.card_union_le (wires (s.rest v)) s.discard
  have le₃ := discard_le s
  have le₄ := exact_size h
  have eq : (wires v).card = v.length := by simpa [wires] using List.toFinset_card_of_nodup nd
  have fresh : s.out.w ∉ wires (s.rest v) := by
    intro hm
    obtain ⟨w,hw,e⟩ := Step.mem_wires.mp hm
    have mem : w ∈ v := by cases s <;> exact List.mem_of_mem_filter hw
    exact el.2 (Step.mem_wires.mpr ⟨w,mem,e⟩)
  have ee : (wires (s.after v)).card = (wires (s.rest v)).card + 1 := by
    simpa only [wires,Step.after,List.map_cons,List.toFinset_cons] using
      Finset.card_insert_of_notMem fresh
  omega

def Step.anyBad {x : Word} {c : Charts x} (b t : ℕ) (v : List (Wire c)) (test : Step c → Bool) :=
  v.all (fun a =>
    ((t==0) || (test (.flip a false) && test (.flip a true))) &&
    ((b==0) || v.all (fun w =>
      !(decide (a.w.toNat < w.w.toNat)) ||
      [false,true].all (fun d => [false,true].all (fun ka =>
        test (.binary d a w ka false) && test (.binary d a w ka true))))))

lemma checked_steps {x : Word} {c : Charts x} {b t} {v : List (Wire c)} {test : Step c → Bool}
    (h : Step.anyBad b t v test=true) {s} (hs : s ∈ Step.all b t v) : test s=true := by
  obtain ⟨a,ha,hm⟩ := List.mem_flatMap.mp hs
  have hh := Bool.and_eq_true_iff.mp (List.all_eq_true.mp h a ha)
  rcases List.mem_append.mp hm with hu|hb
  · split at hu
    · contradiction
    rename_i ht
    have q := Bool.and_eq_true_iff.mp ((Bool.or_eq_true_iff.mp hh.1).resolve_left
      (by simpa only [beq_iff_eq] using ht))
    rcases List.mem_cons.mp hu with rfl|hu
    · exact q.1
    · obtain rfl := List.mem_singleton.mp hu; exact q.2
  · split at hb
    · contradiction
    rename_i hbPos
    have q := (Bool.or_eq_true_iff.mp hh.2).resolve_left (by simpa only [beq_iff_eq] using hbPos)
    obtain ⟨w,hw,hm⟩ := List.mem_flatMap.mp hb
    split at hm
    · rename_i lt
      have gate := (Bool.or_eq_true_iff.mp (List.all_eq_true.mp q w hw)).resolve_left (by simp [lt])
      obtain ⟨d,hd,h⟩ := List.mem_flatMap.mp hm
      obtain ⟨ka,hka,h⟩ := List.mem_flatMap.mp h
      obtain ⟨kb,hkb,rfl⟩ := List.mem_map.mp h
      have both := Bool.and_eq_true_iff.mp (List.all_eq_true.mp (List.all_eq_true.mp gate d hd) ka hka)
      cases kb
      · exact both.1
      · exact both.2
    · contradiction

structure Frame {x : Word} (c : Charts x) where
  b : ℕ
  t : ℕ
  v : List (Wire c)
  ps : List (Price x)

namespace Frame
variable {x : Word} {c : Charts x}

def Valid (f : Frame c) := (f.v.map Wire.w).Nodup ∧ ∀ p ∈ f.ps, p.Valid f.t (wires f.v)
def No (f : Frame c) := ¬Exact x f.b f.t (wires f.v)
def code (f : Frame c) := key f.b f.t f.v
def child (f : Frame c) (s : Step c) : Frame c :=
  ⟨(s.budget f.b f.t).1,(s.budget f.b f.t).2,s.after f.v,f.ps.map (fun p => p.advance f.v s)⟩

lemma child_valid {f : Frame c} (h : f.Valid) {s} (ok : eligible f.v s)
    (legal : s.Legal f.v f.b f.t) : (f.child s).Valid := by
  refine ⟨s.child_nd h.1 ok.2,?_⟩
  intro p hp; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  exact advance_valid (h.2 q hq) legal

lemma transfer {f g : Frame c} (eq : f.code = g.code) (h : f.No) : g.No := by
  obtain ⟨b,t,s⟩ := (by simpa only [code,key,List.cons.injEq] using eq :
    f.b=g.b ∧ f.t=g.t ∧ sorted f.v=sorted g.v)
  have e : wires f.v=wires g.v := by rw [←key_set f.v,←key_set g.v,s]
  unfold No at *
  rwa [←b,←t,←e]

def decoded (f : Frame c) (j : ℕ) : Option (Step c) :=
  if j < 32 then
    if f.t = 0 then none else
      (f.v[j/2]?).map (fun a => .flip a (Nat.mod j 2 == 1))
  else if f.b = 0 then none else
    let i := j-32
    (f.v[i/128]?).bind fun a =>
      (f.v[Nat.mod (i/8) 16]?).map fun w => .binary (Nat.mod (i/4) 2 == 1) a w
        (Nat.mod (i/2) 2 == 1) (Nat.mod i 2 == 1)

lemma decode_legal {f : Frame c} {j : ℕ} {s : Step c} (h : f.decoded j = some s) :
    s.Legal f.v f.b f.t := by
  unfold decoded at h
  split at h
  · split at h
    · contradiction
    rename_i ht
    cases e : f.v[j/2]? with
    | none => simp [e] at h
    | some a =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst s; exact ⟨List.mem_of_getElem? e,by omega⟩
  · split at h
    · contradiction
    rename_i hb
    let i := j-32
    change ((f.v[i/128]?).bind _)=some s at h
    cases e : f.v[i/128]? with
    | none => simp [e] at h
    | some a =>
      simp only [e,Option.bind_some] at h
      cases ew : f.v[Nat.mod (i/8) 16]? with
      | none => simp [i] at ew; simp [ew] at h
      | some w =>
        change Option.map _ (f.v[Nat.mod (i/8) 16]?) = some s at h
        simp only [ew,Option.map_some,Option.some.injEq] at h
        subst s; exact ⟨List.mem_of_getElem? e,List.mem_of_getElem? ew,by omega⟩

def jump (f : Frame c) (j : ℕ) : Option (Frame c) :=
  (f.decoded j).bind (fun s => if isEligible s f.v then some (f.child s) else none)

lemma jump_valid {f g : Frame c} {j : ℕ} (h : f.Valid) (eq : f.jump j=some g) : g.Valid := by
  unfold jump at eq
  cases e : f.decoded j with
  | none => simp [e] at eq
  | some s =>
    simp only [e,Option.bind_some] at eq
    split at eq
    · rename_i eligibleS
      obtain rfl := Option.some.inj eq
      exact child_valid h ((eligible_iff ..).1 eligibleS) (decode_legal e)
    · contradiction

def replay (f : Frame c) : ℕ → ℕ → Option (Frame c)
  | 0,_ => some f
  | d+1,tape => (f.replay d (tape / 4096)).bind fun g => g.jump (Nat.mod tape 4096-1)

lemma replay_valid {f g : Frame c} {d tape : ℕ} (h : f.Valid)
    (eq : f.replay d tape = some g) : g.Valid := by
  induction d generalizing tape g with
  | zero => exact (Option.some.inj eq) ▸ h
  | succ d ih =>
    unfold replay at eq
    cases e : f.replay d (tape/4096) with
    | none => simp [e] at eq
    | some g' =>
      exact jump_valid (ih e) (by simpa only [e,Option.bind_some] using eq)

def check (known : Frame c → Bool) : ℕ → Frame c → Bool
  | 0,f => immediate f.b f.t f.v f.ps || known f
  | d+1,f =>
    immediate f.b f.t f.v f.ps ||
      (!(f.v.any (fun a => a.w == x)) &&
        Step.anyBad f.b f.t f.v (fun s =>
          decide ((s.budget f.b f.t).1+1+s.drops < f.v.length+1) || !(isEligible s f.v) || check known d (f.child s)))

lemma check_sound (known : Frame c → Bool) (good : ∀ f, known f = true → f.No)
    (hx : proper x) (d : ℕ) {f : Frame c} (v : f.Valid) (h : check known d f=true) : f.No := by
  induction d generalizing f with
  | zero =>
    rcases Bool.or_eq_true_iff.mp h with hi|hk
    · exact immediate_sound v.1 v.2 hi
    · exact good f hk
  | succ d ih =>
    rcases Bool.or_eq_true_iff.mp h with hi|hs
    · exact immediate_sound v.1 v.2 hi
    obtain ⟨no,all⟩ := Bool.and_eq_true_iff.mp hs
    intro hex
    rcases descend c hx hex with hm | ⟨s,hs,el,ht⟩
    · obtain ⟨w,hw,e⟩ := Step.mem_wires.mp hm
      have yes : f.v.any (fun a => a.w == x) = true := List.any_eq_true.mpr ⟨w,hw,beq_iff_eq.mpr e⟩
      simp [yes] at no
    · have chk := checked_steps all hs
      have fits := fits_step f.v s v.1 el ht
      simp only [show ¬ ((s.budget f.b f.t).1+1+s.drops < f.v.length+1) by omega,
        decide_false,Bool.false_or,(eligible_iff ..).2 el,Bool.not_true] at chk
      exact ih (child_valid v el (Step.all_legal hs)) chk ht
end Frame

abbrev Table := Array ℕ

def lowerIndex (a : Table) (h : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0,l,_ => l
  | fuel+1,l,r =>
    if l<r then
      let m := (l+r)/2
      if Nat.mod a[m]! 65521 < h then lowerIndex a h fuel (m+1) r
        else lowerIndex a h fuel l m
    else l

def TableSound {x : Word} {c : Charts x} (root : Frame c) (depth : ℕ) (a : Table) :=
  ∀ (j w : ℕ), a[j]?=some w → ∀ f, root.replay depth (w/65521) = some f → f.No

def hitRow {x : Word} {c : Charts x} (root : Frame c) (depth h : ℕ) (k : Key) : Option ℕ → Bool
  | none => false
  | some w =>
    Nat.mod w 65521 == h && (root.replay depth (w/65521)).any (fun g => g.code == k)

def lookup {x : Word} {c : Charts x} (root : Frame c) (depth : ℕ) (a : Table) (f : Frame c) :=
  let k := f.code
  let h := Cache.hashKey k
  let j := lowerIndex a h 20 0 a.size
  [0,1,2,3,4,5].any (fun n => hitRow root depth h k (a[j+n]?))

lemma lookup_sound {x : Word} {c : Charts x} {root : Frame c} {depth} {a : Table}
    (sound : TableSound root depth a) (f : Frame c) (ok : lookup root depth a f = true) :
    f.No := by
  let k := f.code
  let h := Cache.hashKey k
  let j := lowerIndex a h 20 0 a.size
  obtain ⟨n,_,eh⟩ := List.any_eq_true.mp ok
  change hitRow root depth h k (a[j+n]?) = true at eh
  cases e : a[j+n]? with
  | none => simp [e,hitRow] at eh
  | some w =>
    have pair := Bool.and_eq_true_iff.mp (by simpa only [e,hitRow] using eh :
      Nat.mod w 65521 == h && (root.replay depth (w/65521)).any (fun g => g.code == k))
    cases eq : root.replay depth (w/65521) with
    | none => simp [eq] at pair
    | some g =>
      have hkey : g.code=k := by simpa [eq] using pair.2
      exact Frame.transfer hkey (sound (j+n) w e g eq)

def tableRow {x : Word} {c : Charts x} (root : Frame c) (d : ℕ) (a : Table)
    (known : Frame c → Bool) (hops j : ℕ) :=
  (a[j]?).all (fun w => (root.replay d (w/65521)).all (Frame.check known hops))

def Span (p : ℕ → Bool) (lo hi : ℕ) := ∀ j, lo ≤ j → j < hi → p j=true
def sampleSpan (p : ℕ → Bool) (lo n : ℕ) := (List.range n).all (fun i => p (lo+i))
lemma checked_span {p : ℕ → Bool} {lo n : ℕ} (h : sampleSpan p lo n = true) : Span p lo (lo+n) := by
  intro j hj htop
  have q := List.all_eq_true.mp h (j-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le hj] using q
lemma join_span {p : ℕ → Bool} {lo mid hi : ℕ} (h : Span p lo mid) (k : Span p mid hi) :
    Span p lo hi := by
  intro j hj ht
  by_cases e : j < mid
  · exact h j hj e
  · exact k j (by omega) ht
lemma certified_table {x : Word} {c : Charts x} (hx : proper x) (root : Frame c) (vr : root.Valid)
    (d : ℕ) (a : Table) {known : Frame c → Bool} (sk : ∀ f, known f=true → f.No)
    (hops : ℕ) (h : Span (tableRow root d a known hops) 0 a.size) : TableSound root d a := by
  intro j w ew f ef
  have hj := h j (Nat.zero_le _) (Array.getElem?_eq_some_iff.mp ew).choose
  have e : Frame.check known hops f=true := by simpa only [tableRow,ew,Option.all_some,ef] using hj
  exact Frame.check_sound known sk hx hops (Frame.replay_valid vr ef) e

def checkSubsets {x : Word} {c : Charts x} (root : Frame c) (known : Frame c → Bool) (hops : ℕ) :=
  root.v.sublists.all (fun u => Frame.check known hops {root with v:=u})

lemma checked_root {x : Word} {c : Charts x} (hx : proper x) (root : Frame c) (vr : root.Valid)
    {known : Frame c → Bool} (sk : ∀ f, known f=true → f.No)
    (hops : ℕ) (ok : checkSubsets root known hops=true) :
    ¬Feasible x root.b root.t (wires root.v) := by
  rintro ⟨i,hi,j,hj,T,sub,hL⟩
  let u := root.v.filter (fun a => decide (a.w ∈ T))
  have eq : wires u=T := by
    ext a; rw [Step.mem_wires]
    constructor
    · rintro ⟨w,hw,rfl⟩; exact of_decide_eq_true (List.mem_filter.mp hw).2
    · intro ha; obtain ⟨w,hw,e⟩ := Step.mem_wires.mp (sub ha)
      exact ⟨w,List.mem_filter.mpr ⟨hw,by simpa [e] using ha⟩,e⟩
  have hchk := List.all_eq_true.mp ok u (List.mem_sublists.mpr List.filter_sublist)
  have q : ({root with v:=u} : Frame c).Valid := ⟨vr.1.sublist (List.filter_sublist.map _), fun p hp =>
    price_subset (vr.2 p hp) (eq ▸ sub)⟩
  have no := Frame.check_sound known sk hx hops q hchk
  apply no
  change Exact x root.b root.t (wires u); rw [eq]
  exact ⟨i,hi,j,hj,hL⟩

lemma check_block {p : ℕ → Bool} {lo hi : ℕ} (h : sampleSpan p lo (hi-lo)=true) :
    Span p lo hi := by
  intro j hj htop
  exact checked_span h j hj (by omega)

end Replay2161
