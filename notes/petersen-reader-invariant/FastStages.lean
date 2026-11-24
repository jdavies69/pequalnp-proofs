import Stages

namespace Replay2161

def keepList {α : Type} (k : Bool) (a : α) := if k then [a] else []
def addSep (k : Bool) (a r : Word) := if k then a ||| r else r

lemma cover_keep {x : Word} {c : Charts x} (t : ℕ) (a : Wire c) (k : Bool)
    (tail : List (Wire c)) :
    cover t (keepList k a ++ tail)=addSep k (a.sep t) (cover t tail) := by
  cases k <;> rfl

lemma preserve_cover {x : Word} {c : Charts x} {b t} {S : Finset Word} (v : List (Wire c))
    (h : Exact x b t S) (sub : S ⊆ wires v) : cover t v=top := by
  obtain ⟨n,_,j,hj,h⟩ := h
  apply BitVec.eq_of_getElem_eq; intro k hk
  let i : Fin 512 := ⟨k,hk⟩
  change bit (cover t v) i=bit top i
  rw [bit_top,cover_bit]
  obtain ⟨a,ha,hd⟩ := distinguishes_live h (c.hp i) (c.hn i)
  obtain ⟨w,hw,e⟩ := Step.mem_wires.mp (sub ha)
  exact ⟨w,hw,e ▸ distinguish_more hd hj⟩

def alone {x : Word} {c : Charts x} (a : Wire c) (v : List (Wire c)) :=
  v.filter (fun w => w.w != a.w)
def aside {x : Word} {c : Charts x} (a b : Wire c) (v : List (Wire c)) :=
  v.filter (fun w => w.w != a.w && w.w != b.w)

lemma cover_unary {x : Word} {c : Charts x} {n t} {a : Wire c} {v : List (Wire c)} (k : Bool)
    (h : Exact x n t (wires ((Step.flip a k).after v))) :
    a.flip.sep t ||| addSep k (a.sep t) (cover t (alone a v))=top := by
  let v' := a.flip :: (keepList k a ++ alone a v)
  have hv : cover t v'=top := preserve_cover v' h (by
    intro z hz; obtain ⟨w,hw,rfl⟩ := Step.mem_wires.mp hz
    rcases List.mem_cons.mp hw with rfl|hw
    · exact Step.mem_wires.mpr ⟨_,List.mem_cons_self,rfl⟩
    obtain ⟨wm,ok⟩ := List.mem_filter.mp hw
    by_cases e : w.w=a.w
    · cases k
      · simp [e] at ok
      · exact Step.mem_wires.mpr ⟨a,by simp [v',keepList],e.symm⟩
    · exact Step.mem_wires.mpr ⟨w,List.mem_cons_of_mem _ (List.mem_append_right _
        (List.mem_filter.mpr ⟨wm,by simp [e]⟩)),rfl⟩)
  simpa only [v',cover,cover_keep] using hv

lemma cover_binary {x : Word} {c : Charts x} {n t} {a b : Wire c} {v : List (Wire c)}
    (d ka kb : Bool) (h : Exact x n t (wires ((Step.binary d a b ka kb).after v))) :
    (a.binary d b).sep t ||| addSep ka (a.sep t) (addSep kb (b.sep t) (cover t (aside a b v)))=top := by
  let v' := a.binary d b :: (keepList ka a ++ (keepList kb b ++ aside a b v))
  have hv : cover t v'=top := preserve_cover v' h (by
    intro z hz; obtain ⟨w,hw,rfl⟩ := Step.mem_wires.mp hz
    rcases List.mem_cons.mp hw with rfl|hw
    · exact Step.mem_wires.mpr ⟨_,List.mem_cons_self,rfl⟩
    obtain ⟨wm,ok⟩ := List.mem_filter.mp hw
    obtain ⟨okA,okB⟩ := Bool.and_eq_true_iff.mp ok
    by_cases ea : w.w=a.w
    · cases ka
      · simp [ea] at okA
      · exact Step.mem_wires.mpr ⟨a,by simp [v',keepList],ea.symm⟩
    by_cases eb : w.w=b.w
    · cases kb
      · simp [eb] at okB
      · exact Step.mem_wires.mpr ⟨b,by simp [v',keepList],eb.symm⟩
    exact Step.mem_wires.mpr ⟨w,List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_append_right _
      (List.mem_filter.mpr ⟨wm,by simp [ea,eb]⟩))),rfl⟩)
  simpa only [v',cover,cover_keep] using hv

def scan {x : Word} {c : Charts x} (f : Frame c) (next : Frame c → Bool) :=
  let len := f.v.length
  let test := fun (s : Step c) (budget : ℕ) (bits : Word) =>
    decide (budget+1+s.drops < len+1) || bits != top || !isEligible s f.v || next (f.child s)
  f.v.all (fun a =>
    ((f.t==0) ||
      (let t := f.t-1
       let r := cover t (alone a f.v)
       let g := a.flip.sep t
       test (.flip a false) f.b (g ||| r) && test (.flip a true) f.b (g ||| (a.sep t ||| r)))) &&
    ((f.b==0) || f.v.all (fun w => !(decide (a.w.toNat < w.w.toNat)) ||
      (let r := cover f.t (aside a w f.v)
       let wa := a.sep f.t
       let wb := w.sep f.t
       [false,true].all (fun d =>
         let g := (a.binary d w).sep f.t
         [false,true].all (fun ka => [false,true].all (fun kb =>
           test (.binary d a w ka kb) (f.b-1) (g ||| addSep ka wa (addSep kb wb r)))))))))

def Fast {x : Word} {c : Charts x} (known : Frame c → Bool) : ℕ → Frame c → Bool
  | 0,f => immediate f.b f.t f.v f.ps || known f
  | k+1,f => immediate f.b f.t f.v f.ps ||
      (!(f.v.any (fun a => a.w == x)) && scan f (Fast known k))

lemma scan_sound {x : Word} {c : Charts x} {f : Frame c} {s : Step c} {next : Frame c → Bool}
    (h : scan f next = true) (nd : (f.v.map Wire.w).Nodup)
    (hs : s ∈ Step.all f.b f.t f.v) (el : eligible f.v s)
    (ht : Exact x (s.budget f.b f.t).1 (s.budget f.b f.t).2 (wires (s.after f.v))) :
    next (f.child s)=true := by
  have fit := fits_step f.v s nd el ht
  obtain ⟨a,ha,hm⟩ := List.mem_flatMap.mp hs
  have hh := Bool.and_eq_true_iff.mp (List.all_eq_true.mp h a ha)
  rcases List.mem_append.mp hm with hu|hb
  · split at hu
    · contradiction
    rename_i tpos
    have q := Bool.and_eq_true_iff.mp ((Bool.or_eq_true_iff.mp hh.1).resolve_left
      (by simpa only [beq_iff_eq] using tpos))
    rcases List.mem_cons.mp hu with rfl|hu
    · have eq := cover_unary false ht
      change f.v.length+1 ≤ f.b+1+_ at fit
      simp only [Step.budget,addSep,Bool.false_eq_true,ite_false] at eq
      simpa only [not_lt_of_ge fit,decide_false,Bool.false_or,eq,bne_self_eq_false,
        (eligible_iff ..).2 el,Bool.not_true] using q.1
    · obtain rfl := List.mem_singleton.mp hu
      have eq := cover_unary true ht
      change f.v.length+1 ≤ f.b+1+_ at fit
      simp only [Step.budget,addSep,ite_true] at eq
      simpa only [not_lt_of_ge fit,decide_false,Bool.false_or,eq,bne_self_eq_false,
        (eligible_iff ..).2 el,Bool.not_true] using q.2
  · split at hb
    · contradiction
    rename_i bpos
    have q := (Bool.or_eq_true_iff.mp hh.2).resolve_left (by simpa only [beq_iff_eq] using bpos)
    obtain ⟨w,hw,hm⟩ := List.mem_flatMap.mp hb
    split at hm
    · rename_i lt
      have gate := (Bool.or_eq_true_iff.mp (List.all_eq_true.mp q w hw)).resolve_left (by simp [lt])
      obtain ⟨d,hd,h⟩ := List.mem_flatMap.mp hm
      obtain ⟨ka,hka,h⟩ := List.mem_flatMap.mp h
      obtain ⟨kb,hkb,rfl⟩ := List.mem_map.mp h
      have val := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp gate d hd) ka hka) kb hkb
      have eq := cover_binary d ka kb ht
      simp only [Step.budget] at eq
      change f.v.length+1 ≤ f.b-1+1+_ at fit
      simpa only [not_lt_of_ge fit,decide_false,Bool.false_or,eq,bne_self_eq_false,
        (eligible_iff ..).2 el,Bool.not_true] using val
    · contradiction

lemma fast_sound {x : Word} {c : Charts x} (known : Frame c → Bool) (good : ∀ f, known f=true → f.No)
    (hx : proper x) (d : ℕ) {f : Frame c} (valid : f.Valid) (ok : Fast known d f = true) : f.No := by
  induction d generalizing f with
  | zero =>
    rcases Bool.or_eq_true_iff.mp ok with h|h
    · exact immediate_sound valid.1 valid.2 h
    · exact good _ h
  | succ n ih =>
    rcases Bool.or_eq_true_iff.mp ok with h|q
    · exact immediate_sound valid.1 valid.2 h
    obtain ⟨no,rows⟩ := Bool.and_eq_true_iff.mp q
    intro hex
    rcases descend c hx hex with hm | ⟨s,hs,el,ht⟩
    · obtain ⟨w,hw,e⟩ := Step.mem_wires.mp hm
      have yes : f.v.any (fun a => a.w == x) = true := List.any_eq_true.mpr ⟨w,hw,beq_iff_eq.mpr e⟩
      simp [yes] at no
    · exact ih (Frame.child_valid valid el (Step.all_legal hs)) (scan_sound rows valid.1 hs el ht) ht

def fastRow {x : Word} {c : Charts x} (root : Frame c) (d : ℕ) (a : Table)
    (known : Frame c → Bool) (hops j : ℕ) :=
  (a[j]?).all (fun w => (root.replay d (w/65521)).all (Fast known hops))

lemma fast_table {x : Word} {c : Charts x} (hx : proper x) (root : Frame c) (vr : root.Valid)
    (d : ℕ) (a : Table) {known : Frame c → Bool} (sk : ∀ f, known f=true → f.No)
    (hops : ℕ) (h : Span (fastRow root d a known hops) 0 a.size) : TableSound root d a := by
  intro j w ew f ef
  have hj := h j (Nat.zero_le _) (Array.getElem?_eq_some_iff.mp ew).choose
  have e : Fast known hops f=true := by simpa only [fastRow,ew,Option.all_some,ef] using hj
  exact fast_sound known sk hx hops (Frame.replay_valid vr ef) e

end Replay2161
