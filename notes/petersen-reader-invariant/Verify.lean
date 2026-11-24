import Core

namespace Replay2161

structure Charts (x : Word) where
  p : Fin 512 → Fin 512
  n : Fin 512 → Fin 512
  hp : ∀ i, bit x (p i) = true
  hn : ∀ i, bit x (n i) = false

structure Wire {x : Word} (c : Charts x) where
  w : Word
  p : Word
  n : Word
  hp : ∀ i, bit p i = bit w (c.p i)
  hn : ∀ i, bit n i = bit w (c.n i)

namespace Wire
variable {x : Word} {c : Charts x}

def binary (d : Bool) (a b : Wire c) : Wire c :=
  ⟨combine d a.w b.w,combine d a.p b.p,combine d a.n b.n,
    fun i => by simp only [bit_bin,a.hp,b.hp],
    fun i => by simp only [bit_bin,a.hn,b.hn]⟩

def flip (a : Wire c) : Wire c :=
  ⟨~~~a.w,~~~a.p,~~~a.n,fun i => by simp only [bit_not,a.hp],
    fun i => by simp only [bit_not,a.hn]⟩

def sep (t : ℕ) (a : Wire c) : Word :=
  if t = 0 then a.p &&& ~~~a.n else a.p ^^^ a.n

lemma sep_bit {t : ℕ} (a : Wire c) (i : Fin 512) :
    bit (a.sep t) i = true ↔ distinguishes t a.w (c.p i) (c.n i) := by
  have p := a.hp i
  have n := a.hn i
  by_cases ht : t = 0
  · simpa only [sep,distinguishes,ht,ite_true,bit,BitVec.getElem_and,BitVec.getElem_not,
      Bool.and_eq_true,Bool.not_eq_true'] using (and_congr (congrArg (· = true) p).to_iff
      (congrArg (· = false) n).to_iff)
  · simp only [sep,distinguishes,ht,ite_false,bit,BitVec.getElem_xor]
    change (bit a.p i ^^ bit a.n i) = true ↔ bit a.w (c.p i) ≠ bit a.w (c.n i)
    rw [p,n]
    cases bit a.w (c.p i) <;> cases bit a.w (c.n i) <;> decide
end Wire

def wires {x : Word} {c : Charts x} (v : List (Wire c)) : Finset Word :=
  (v.map Wire.w).toFinset

def cover {x : Word} {c : Charts x} (t : ℕ) : List (Wire c) → Word
  | [] => 0
  | w :: v => w.sep t ||| cover t v

lemma cover_bit {x : Word} {c : Charts x} (t : ℕ) (v : List (Wire c)) (i : Fin 512) :
    bit (cover t v) i = true ↔ ∃ w ∈ v, distinguishes t w.w (c.p i) (c.n i) := by
  induction v with
  | nil => simp only [cover,bit_zero,Bool.false_eq_true,List.not_mem_nil,false_and]; tauto
  | cons a v ih =>
    change bit (combine true _ _) i = true ↔ _
    simp only [bit_bin,ite_true,Bool.or_eq_true,Wire.sep_bit,ih,List.mem_cons,
      exists_eq_or_imp]

lemma distinguish_more {a : Word} {i j : Fin 512} {u t : ℕ}
    (h : distinguishes u a i j) (hu : u ≤ t) : distinguishes t a i j := by
  cases t with
  | zero => simpa [show u=0 by omega] using h
  | succ t =>
    have hp := distinguish_old h
    simpa only [distinguishes,Nat.succ_ne_zero,ite_false] using hp

lemma cover_live {x : Word} (c : Charts x) {b j t} (v : List (Wire c))
    (h : Live x b j (wires v)) (ht : j ≤ t) : cover t v = top := by
  apply BitVec.eq_of_getElem_eq; intro k hk
  let i : Fin 512 := ⟨k,hk⟩
  change bit (cover t v) i = bit top i
  rw [bit_top,cover_bit]
  obtain ⟨a,ha,hd⟩ := distinguishes_live h (c.hp i) (c.hn i)
  obtain ⟨w, hw, hwa⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact ⟨w,hw,hwa ▸ distinguish_more hd ht⟩

def Exact (x : Word) (b t : ℕ) (S : Finset Word) : Prop :=
  ∃ n ≤ b, ∃ j ≤ t, Live x n j S

lemma exact_size {x b t S} (h : Exact x b t S) : S.card ≤ b+1 := by
  obtain ⟨n,hn,j,_,h⟩ := h
  exact (count_live h).trans (by omega)

lemma exact_cover {x : Word} (c : Charts x) {b t} (v : List (Wire c))
    (h : Exact x b t (wires v)) : cover t v = top := by
  obtain ⟨n,_,j,hj,h⟩ := h
  exact cover_live c v h hj

inductive Step {x : Word} (c : Charts x) where
  | flip (a : Wire c) (keep : Bool)
  | binary (d : Bool) (a b : Wire c) (keepA keepB : Bool)

namespace Step
variable {x : Word} {c : Charts x}
def out : Step c → Wire c
  | .flip a _ => a.flip
  | .binary d a b _ _ => a.binary d b

def rest (s : Step c) (v : List (Wire c)) : List (Wire c) :=
  match s with
  | .flip a ka => v.filter (fun y => ka || y.w != a.w)
  | .binary _ a b ka kb =>
    v.filter (fun y => (ka || y.w != a.w) && (kb || y.w != b.w))

def after (s : Step c) (v : List (Wire c)) := s.out :: s.rest v

def budget (s : Step c) (b t : ℕ) :=
  match s with
  | .flip .. => (b,t-1)
  | .binary .. => (b-1,t)

def all (b t : ℕ) (v : List (Wire c)) : List (Step c) :=
  v.flatMap fun a =>
    (if t=0 then [] else [Step.flip a false,Step.flip a true]) ++
    (if b=0 then [] else v.flatMap fun w =>
      if a.w.toNat < w.w.toNat then
        [false,true].flatMap fun d => [false,true].flatMap fun ka =>
          [false,true].map (fun kb => Step.binary d a w ka kb)
      else [])

lemma mem_flip {a : Wire c} {b t : ℕ} {v : List (Wire c)} (ht : 0<t) (ha : a ∈ v)
    (ka : Bool) : Step.flip a ka ∈ all b t v := by
  apply List.mem_flatMap.mpr
  refine ⟨a,ha,List.mem_append_left _ ?_⟩
  cases ka <;> simp [show t≠0 by omega]

lemma mem_binary {a w : Wire c} {b t : ℕ} {v : List (Wire c)} (hb : 0<b)
    (ha : a ∈ v) (hw : w ∈ v) (hlt : a.w.toNat < w.w.toNat) (d ka kb : Bool) :
    Step.binary d a w ka kb ∈ all b t v := by
  apply List.mem_flatMap.mpr
  refine ⟨a,ha,List.mem_append_right _ ?_⟩
  simp only [show b≠0 by omega,ite_false]
  apply List.mem_flatMap.mpr
  refine ⟨w,hw,?_⟩
  simp only [hlt,ite_true]
  apply List.mem_flatMap.mpr
  refine ⟨d,by cases d <;> simp,?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨ka,by cases ka <;> simp,List.mem_map.mpr ⟨kb,by cases kb <;> simp,rfl⟩⟩

lemma mem_wires {v : List (Wire c)} {w : Word} : w ∈ wires v ↔ ∃ a ∈ v, a.w = w := by
  simp [wires]

lemma next_flip {a : Wire c} {v : List (Wire c)} {U : Finset Word}
    (hs : wires v = insert a.w U) :
    wires ((Step.flip a (decide (a.w ∈ U))).after v) = insert (~~~a.w) U := by
  ext z
  simp only [after,wires,List.map_cons,List.toFinset_cons,Finset.mem_insert]
  apply or_congr_right
  change z ∈ wires (v.filter _) ↔ z ∈ U
  rw [mem_wires]
  constructor
  · rintro ⟨q,hq,rfl⟩
    obtain ⟨hv,cond⟩ := List.mem_filter.mp hq
    have eq : q.w ∈ insert a.w U := hs ▸ (mem_wires.mpr ⟨q,hv,rfl⟩)
    rcases Finset.mem_insert.mp eq with he|h
    · simpa [he] using cond
    · exact h
  · intro hz
    have hv : z ∈ wires v := hs ▸ Finset.mem_insert_of_mem hz
    obtain ⟨q,hq,eq⟩ := mem_wires.mp hv
    refine ⟨q,List.mem_filter.mpr ⟨hq,?_⟩,eq⟩
    by_cases h : z=a.w
    · simp [←h,eq,hz]
    · simp [eq,h]

lemma next_bin {a w : Wire c} {v : List (Wire c)} {U : Finset Word}
    (hs : wires v = insert a.w (insert w.w U)) :
    wires ((Step.binary d a w (decide (a.w ∈ U)) (decide (w.w ∈ U))).after v) =
      insert (combine d a.w w.w) U := by
  ext z
  simp only [after,wires,List.map_cons,List.toFinset_cons,Finset.mem_insert]
  apply or_congr_right
  change z ∈ wires (v.filter _) ↔ z ∈ U
  rw [mem_wires]
  constructor
  · rintro ⟨q,hq,rfl⟩
    obtain ⟨hv,cond⟩ := List.mem_filter.mp hq
    have eq : q.w ∈ insert a.w (insert w.w U) := hs ▸ (mem_wires.mpr ⟨q,hv,rfl⟩)
    obtain ⟨c1,c2⟩ := Bool.and_eq_true_iff.mp cond
    rcases Finset.mem_insert.mp eq with he|h
    · simpa [he] using c1
    rcases Finset.mem_insert.mp h with he|h
    · simpa [he] using c2
    · exact h
  · intro hz
    have hv : z ∈ wires v := hs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hz)
    obtain ⟨q,hq,eq⟩ := mem_wires.mp hv
    refine ⟨q,List.mem_filter.mpr ⟨hq,?_⟩,eq⟩
    apply Bool.and_eq_true_iff.mpr
    constructor
    · by_cases h : z=a.w
      · simp [←h,eq,hz]
      · simp [eq,h]
    · by_cases h : z=w.w
      · simp [←h,eq,hz]
      · simp [eq,h]
end Step

def eligible {x : Word} {c : Charts x} (v : List (Wire c)) (s : Step c) : Prop :=
  proper s.out.w ∧ s.out.w ∉ wires v

lemma descend {x : Word} (c : Charts x) (hx : proper x) {b t : ℕ} {v : List (Wire c)}
    (h : Exact x b t (wires v)) :
    x ∈ wires v ∨ ∃ s ∈ Step.all b t v, eligible v s ∧
      Exact x (s.budget b t).1 (s.budget b t).2 (wires (s.after v)) := by
  obtain ⟨n,hn,j,hj,h⟩ := h
  generalize hs : wires v = S at h
  cases h with
  | done =>
    left; simp
  | @unary nb nt U a pa fresh tail =>
    right
    have hv : a ∈ wires v := hs ▸ Finset.mem_insert_self ..
    obtain ⟨aw,hw,eq⟩ := Step.mem_wires.mp hv
    subst a
    let s := Step.flip aw (decide (aw.w ∈ U))
    refine ⟨s,Step.mem_flip (by omega) hw _,⟨tail.good hx _ (Finset.mem_insert_self ..),?_⟩,
      n,hn,nt,by change nt ≤ t-1; omega,?_⟩
    · change ~~~aw.w ∉ wires v
      rwa [hs]
    · change Live x n nt (wires ((Step.flip aw _).after _))
      rwa [Step.next_flip hs]
  | @binary nb nt U a w d pa pw ne fresh tail =>
    right
    have ha : a ∈ wires v := hs ▸ Finset.mem_insert_self ..
    have hw : w ∈ wires v := hs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self ..)
    obtain ⟨aw,ah,a_eq⟩ := Step.mem_wires.mp ha
    obtain ⟨ww,wh,w_eq⟩ := Step.mem_wires.mp hw
    subst a; subst w
    have ord : aw.w.toNat ≠ ww.w.toNat := fun e => ne (BitVec.eq_of_toNat_eq e)
    have mk (y z : Wire c) (hy : y ∈ v) (hz : z ∈ v) (hlt : y.w.toNat < z.w.toNat)
        (heads : wires v = insert y.w (insert z.w U))
        (fresh' : combine d y.w z.w ∉ wires v)
        (tail' : Live x nb j (insert (combine d y.w z.w) U)) :
        ∃ s ∈ Step.all b t v, eligible v s ∧
          Exact x (s.budget b t).1 (s.budget b t).2 (wires (s.after v)) := by
      let s := Step.binary d y z (decide (y.w ∈ U)) (decide (z.w ∈ U))
      refine ⟨s,Step.mem_binary (by omega) hy hz hlt ..,
        ⟨tail'.good hx _ (Finset.mem_insert_self ..), fresh'⟩,
        nb,by change nb ≤ b-1; omega,j,hj,?_⟩
      change Live x nb j (wires ((Step.binary d y z _ _).after _))
      rwa [Step.next_bin heads]
    rcases lt_or_gt_of_ne ord with hlt|hlt
    · exact mk aw ww ah wh hlt hs (hs ▸ fresh) tail
    · apply mk ww aw wh ah hlt
      · rwa [Finset.insert_comm]
      · rwa [comm,hs]
      · rwa [comm]

structure Basis (x : Word) where
  mask : Word
  raw : List Word
  lo : ℕ
  proj : Projection
  zero : proj.q 0 = 0
  one : proj.q top = top
  refl (a b : Word) : a &&& mask = b &&& mask → proj.q a = proj.q b

structure Price (x : Word) where
  basis : Basis x
  spent : ℕ

def Basis.base {x : Word} (f : Basis x) := (f.raw.map f.proj.q).toFinset

def Price.Valid {x : Word} (f : Price x) (t : ℕ) (S : Finset Word) :=
  Guard f.basis.proj x S f.basis.base t f.basis.lo f.spent

def maskedConst (m a : Word) : Bool := (a &&& m) == 0 || (a &&& m) == m

def freeAt {x : Word} {c : Charts x} (f : Basis x) (v : List (Wire c)) (w : Word) : Bool :=
  maskedConst f.mask w || v.any (fun a => (w &&& f.mask) == (a.w &&& f.mask)) ||
    f.raw.any (fun a => (w &&& f.mask) == (a &&& f.mask))

lemma maskedConst_sound {x : Word} {f : Basis x} {a : Word}
    (h : maskedConst f.mask a = true) : ¬proper (f.proj.q a) := by
  rcases Bool.or_eq_true_iff.mp h with h|h
  · have eq := f.refl a 0 (by simpa using beq_iff_eq.mp h)
    rw [f.zero] at eq; exact fun hp => hp.1 eq
  · have eq := f.refl a top (by simpa only [top,BitVec.allOnes_and] using beq_iff_eq.mp h)
    rw [f.one] at eq; exact fun hp => hp.2 eq

lemma freeAt_sound {x : Word} {c : Charts x} {f : Basis x} {v : List (Wire c)} {w : Word}
    (h : freeAt f v w = true) :
    f.proj.q w ∈ available f.proj (wires v) f.base ∨ ¬proper (f.proj.q w) := by
  rcases Bool.or_eq_true_iff.mp h with h | h
  · rcases Bool.or_eq_true_iff.mp h with h | h
    · exact Or.inr (maskedConst_sound h)
    · obtain ⟨a,ha,e⟩ := List.any_eq_true.mp h
      rw [f.refl w a.w (beq_iff_eq.mp e)]
      exact Or.inl (Finset.mem_union_left _
        (Finset.mem_image_of_mem _ (Step.mem_wires.mpr ⟨a,ha,rfl⟩)))
  · obtain ⟨a,ha,e⟩ := List.any_eq_true.mp h
    rw [f.refl w a (beq_iff_eq.mp e)]
    exact Or.inl (Finset.mem_union_right _
      (List.mem_toFinset.mpr (List.mem_map.mpr ⟨a,ha,rfl⟩)))

def Price.advance {x : Word} {c : Charts x} (f : Price x) (v : List (Wire c)) (s : Step c) :
    Price x := match s with
  | .flip .. => f
  | .binary .. => ⟨f.basis,f.spent + (if freeAt f.basis v s.out.w then 0 else 1)⟩

lemma Step.child_subset {x : Word} {c : Charts x} (s : Step c) (v : List (Wire c)) :
    wires (s.after v) ⊆ insert s.out.w (wires v) := by
  intro a ha
  obtain ⟨w,hw,rfl⟩ := Step.mem_wires.mp ha
  rcases List.mem_cons.mp hw with rfl|hw
  · exact Finset.mem_insert_self ..
  · have h : w ∈ v := by cases s <;> exact List.mem_of_mem_filter hw
    exact Finset.mem_insert_of_mem (Step.mem_wires.mpr ⟨w,h,rfl⟩)

lemma advance_flip {x : Word} {c : Charts x} {p : Price x} {a : Wire c}
    {v : List (Wire c)} {t : ℕ} (hv : p.Valid (t+1) (wires v)) (ha : a ∈ v) (ka : Bool) :
    (p.advance v (.flip a ka)).Valid t (wires ((Step.flip a ka).after v)) :=
  guard_unary hv (Step.mem_wires.mpr ⟨a,ha,rfl⟩) ((Step.flip a ka).child_subset v)

lemma advance_bin {x : Word} {c : Charts x} {p : Price x} {a b : Wire c}
    {v : List (Wire c)} {t : ℕ} (hv : p.Valid t (wires v)) (ha : a ∈ v) (hb : b ∈ v)
    (d ka kb : Bool) :
    (p.advance v (.binary d a b ka kb)).Valid t (wires ((Step.binary d a b ka kb).after v)) := by
  let s := Step.binary d a b ka kb
  have hnext := guard_binary hv (Step.mem_wires.mpr ⟨a,ha,rfl⟩)
    (Step.mem_wires.mpr ⟨b,hb,rfl⟩) (s.child_subset v)
  have cost_le : cost p.basis.proj (wires v) p.basis.base s.out.w ≤
      (if freeAt p.basis v s.out.w then 0 else 1) := by
    cases h : freeAt p.basis v s.out.w
    · change cost _ _ _ _ ≤ 1
      unfold cost; split <;> omega
    · simp [cost,freeAt_sound h]
  refine ⟨hnext.1,fun k hk => ?_⟩
  exact (hnext.2 k hk).trans (Nat.add_le_add_left (Nat.add_le_add_left cost_le _) _)

def Step.Legal {x : Word} {c : Charts x} (s : Step c) (v : List (Wire c)) (b t : ℕ) : Prop :=
  match s with
  | .flip a _ => a ∈ v ∧ 0<t
  | .binary _ a w _ _ => a ∈ v ∧ w ∈ v ∧ 0<b

lemma Step.all_legal {x : Word} {c : Charts x} {s : Step c} {v : List (Wire c)} {b t : ℕ}
    (h : s ∈ Step.all b t v) : s.Legal v b t := by
  obtain ⟨a,ha,hm⟩ := List.mem_flatMap.mp h
  rcases List.mem_append.mp hm with hu|hb
  · split at hu
    · contradiction
    rename_i ht
    rcases List.mem_cons.mp hu with rfl|hu
    · exact ⟨ha,by omega⟩
    · obtain rfl := List.mem_singleton.mp hu
      exact ⟨ha,by omega⟩
  · split at hb
    · contradiction
    rename_i hpos
    obtain ⟨w,hw,hm⟩ := List.mem_flatMap.mp hb
    split at hm
    · obtain ⟨d,_,h⟩ := List.mem_flatMap.mp hm
      obtain ⟨ka,_,h⟩ := List.mem_flatMap.mp h
      obtain ⟨kb,_,rfl⟩ := List.mem_map.mp h
      exact ⟨ha,hw,by omega⟩
    · contradiction

lemma advance_valid {x : Word} {c : Charts x} {p : Price x} {s : Step c}
    {v : List (Wire c)} {b t : ℕ} (hv : p.Valid t (wires v)) (h : s.Legal v b t) :
    (p.advance v s).Valid (s.budget b t).2 (wires (s.after v)) := by
  cases s with
  | flip a ka =>
    obtain ⟨hw,ht⟩ := h
    cases t with
    | zero => omega
    | succ t => exact advance_flip hv hw ka
  | binary d a w ka kb => exact advance_bin hv h.1 h.2.1 d ka kb

def loss {x : Word} {c : Charts x} (f : Basis x) (v : List (Wire c)) :=
  ((v.map Wire.w).filter (maskedConst f.mask)).length

lemma loss_le {x : Word} {c : Charts x} (f : Basis x) (v : List (Wire c))
    (nd : (v.map Wire.w).Nodup) : loss f v ≤ constants f.proj (wires v) := by
  rw [loss,←List.toFinset_card_of_nodup (nd.filter _)]
  apply Finset.card_le_card
  intro a ha
  obtain ⟨hm,hc⟩ := List.mem_filter.mp (List.mem_toFinset.mp ha)
  exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hm,maskedConst_sound hc⟩

def Price.cuts {x : Word} {c : Charts x} (p : Price x) (b : ℕ) (v : List (Wire c)) : Bool :=
  decide (b+p.spent < p.basis.lo+loss p.basis v)

lemma cut_sound {x : Word} {c : Charts x} {p : Price x} {b t : ℕ} {v : List (Wire c)}
    (nd : (v.map Wire.w).Nodup) (valid : p.Valid t (wires v)) (cut : p.cuts b v = true) :
    ¬ Exact x b t (wires v) := by
  rintro ⟨n,hn,j,hj,h⟩
  have g : Guard p.basis.proj x (wires v) p.basis.base j p.basis.lo p.spent :=
    ⟨valid.1,fun k hk => valid.2 k (weaken hk le_rfl hj (by rfl))⟩
  have e := guard_bound g h
  have l := loss_le p.basis v nd
  have q := of_decide_eq_true cut
  omega

lemma Step.child_nd {x : Word} {c : Charts x} {v : List (Wire c)} (s : Step c)
    (nd : (v.map Wire.w).Nodup) (hf : s.out.w ∉ wires v) :
    ((s.after v).map Wire.w).Nodup := by
  simp only [Step.after,List.map_cons,List.nodup_cons]
  have sub : List.Sublist (s.rest v) v := by cases s <;> exact List.filter_sublist
  exact ⟨fun hm => hf (List.mem_toFinset.mpr ((sub.map Wire.w).subset hm)),
    nd.sublist (sub.map Wire.w)⟩

abbrev Key := List ℕ

inductive Cache where
  | empty
  | bin (hash : ℕ) (bucket : List Key) (left right : Cache)

namespace Cache
instance : EmptyCollection Cache := ⟨empty⟩
def hashKey (k : Key) := k.foldl (fun h n => (h*101+n) % 65521) 7919
def find (h : ℕ) : Cache → List Key
  | .empty => []
  | .bin n keys l r => if h=n then keys else if h<n then find h l else find h r
def put (h : ℕ) (k : Key) : Cache → Cache
  | .empty => .bin h [k] .empty .empty
  | .bin n keys l r => if h=n then .bin n (k::keys) l r
      else if h<n then .bin n keys (put h k l) r else .bin n keys l (put h k r)
def contains (db : Cache) (k : Key) := (find (hashKey k) db).contains k
def insert (db : Cache) (k : Key) := put (hashKey k) k db
def Has (k : Key) : Cache → Prop
  | .empty => False
  | .bin _ keys l r => k ∈ keys ∨ Has k l ∨ Has k r
instance : Membership Key Cache where mem db k := Has k db
lemma find_mem {k : Key} (h : ℕ) (db : Cache) (m : k ∈ find h db) : k ∈ db := by
  induction db with
  | empty => contradiction
  | bin n keys l r il ir =>
    change k ∈ keys ∨ _ ∨ _
    simp only [find] at m
    split at m
    · exact Or.inl m
    split at m
    · exact Or.inr (Or.inl (il m))
    · exact Or.inr (Or.inr (ir m))
lemma contains_mem {k : Key} {db : Cache} (h : db.contains k) : k ∈ db :=
  find_mem _ _ (List.contains_iff_mem.mp h)
lemma mem_put {k v : Key} (h : ℕ) (db : Cache) (m : v ∈ put h k db) : v=k ∨ v ∈ db := by
  induction db with
  | empty =>
    change v ∈ [k] ∨ False ∨ False at m
    exact Or.inl (by simpa using m)
  | bin n keys l r il ir =>
    simp only [put] at m
    split at m
    · change v ∈ k::keys ∨ Has v l ∨ Has v r at m
      change v=k ∨ v∈keys ∨ Has v l ∨ Has v r
      simp only [List.mem_cons] at m
      tauto
    split at m
    · change v ∈ keys ∨ Has v (put h k l) ∨ Has v r at m
      change v=k ∨ v∈keys ∨ Has v l ∨ Has v r
      rcases m with a|m|a
      · tauto
      · rcases il m with e|e <;> tauto
      · tauto
    · change v ∈ keys ∨ Has v l ∨ Has v (put h k r) at m
      change v=k ∨ v∈keys ∨ Has v l ∨ Has v r
      rcases m with a|a|m
      · tauto
      · tauto
      · rcases ir m with e|e <;> tauto
end Cache

def sortNats : List ℕ → List ℕ
  | [] => []
  | a::xs => ordered a (sortNats xs)
where ordered (a : ℕ) : List ℕ → List ℕ
  | [] => [a]
  | b::ys => if a≤b then a::b::ys else b::ordered a ys

lemma sort_perm (x : List ℕ) : (sortNats x).Perm x := by
  have helper (a : ℕ) (xs : List ℕ) : (sortNats.ordered a xs).Perm (a::xs) := by
    induction xs with
    | nil => exact .refl _
    | cons b ys ih =>
      simp only [sortNats.ordered]
      split
      · exact .refl _
      · exact (List.Perm.cons b ih).trans (List.Perm.swap ..)
  induction x with
  | nil => exact .refl _
  | cons a xs ih => exact (helper a _).trans (List.Perm.cons a ih)

def sorted {x : Word} {c : Charts x} (v : List (Wire c)) : List ℕ :=
  sortNats (v.map fun a => a.w.toNat)

def key {x : Word} {c : Charts x} (b t : ℕ) (v : List (Wire c)) : Key :=
  b :: t :: sorted v

def Safe (x : Word) (db : Cache) :=
  ∀ b t ws, b::t::ws ∈ db → ¬ Exact x b t (ws.map (BitVec.ofNat 512)).toFinset

lemma key_set {x : Word} {c : Charts x} (v : List (Wire c)) :
    ((sorted v).map (BitVec.ofNat 512)).toFinset = wires v := by
  have perm := (sort_perm (v.map (fun a => a.w.toNat))).map
    (BitVec.ofNat 512)
  ext a
  rw [List.mem_toFinset]
  unfold sorted
  rw [perm.mem_iff]
  simp [wires,Function.comp_def]

lemma safe_insert {x : Word} {c : Charts x} {b t : ℕ} {v : List (Wire c)} {db : Cache}
    (hd : Safe x db) (h : ¬Exact x b t (wires v)) : Safe x (db.insert (key b t v)) := by
  intro b' t' ws hk
  rcases Cache.mem_put _ _ hk with e|hm
  · have eq : key b t v = b'::t'::ws := e.symm
    obtain ⟨rfl,rfl,rfl⟩ := (by simpa only [key,List.cons.injEq] using eq :
      b=b' ∧ t=t' ∧ sorted v=ws)
    rw [key_set]; exact h
  · exact hd _ _ _ hm

def batch {α : Type} (run : α → Cache → Option Cache) : List α → Cache → Option Cache
  | [], db => some db
  | a::xs, db => (run a db).bind (batch run xs)

lemma batch_sound {α : Type} {x : Word} {Q : α → Prop} {run : α → Cache → Option Cache}
    (xs : List α) {db out : Cache} (legal : ∀ a ∈ xs, ∀ d e, Safe x d → run a d = some e →
      Safe x e ∧ Q a) (sd : Safe x db) (done : batch run xs db = some out) :
      Safe x out ∧ ∀ a ∈ xs, Q a := by
  induction xs generalizing db with
  | nil => exact ⟨(Option.some.inj done) ▸ sd,by simp⟩
  | cons a xs ih =>
    simp only [batch] at done
    cases ha : run a db with
    | none => simp [ha] at done
    | some e =>
      have hh := legal a (by simp) db e sd ha
      have hr := ih (fun z hz => legal z (by simp [hz])) hh.1 (by simpa [ha] using done)
      exact ⟨hr.1,fun z hz => (List.mem_cons.mp hz).elim (fun eq => eq ▸ hh.2) (hr.2 z)⟩

def isEligible {x : Word} {c : Charts x} (s : Step c) (v : List (Wire c)) : Bool :=
  s.out.w != 0 && s.out.w != top && !(v.any fun a => a.w == s.out.w)

lemma eligible_iff {x : Word} {c : Charts x} (s : Step c) (v : List (Wire c)) :
    isEligible s v = true ↔ eligible v s := by
  simp only [isEligible,eligible,proper,Bool.and_eq_true,bne_iff_ne,Bool.not_eq_true',
    List.any_eq_false,beq_iff_eq,Step.mem_wires,not_exists,not_and]

def immediate {x : Word} {c : Charts x} (b t : ℕ) (v : List (Wire c)) (ps : List (Price x)) :
    Bool := decide (b+1 < v.length) || cover t v != top || ps.any (fun p => p.cuts b v)

lemma immediate_sound {x : Word} {c : Charts x} {b t} {v : List (Wire c)} {ps}
    (nd : (v.map Wire.w).Nodup) (valid : ∀ p ∈ ps, p.Valid t (wires v))
    (h : immediate b t v ps = true) : ¬Exact x b t (wires v) := by
  intro he
  rcases Bool.or_eq_true_iff.mp h with h|h
  · rcases Bool.or_eq_true_iff.mp h with hs|hc
    · have hsz := exact_size he
      have ec := List.toFinset_card_of_nodup nd
      rw [List.length_map] at ec
      change (v.map Wire.w).toFinset.card ≤ b+1 at hsz
      have hh := of_decide_eq_true hs
      omega
    · simp [exact_cover c v he] at hc
  · obtain ⟨p,hp,cut⟩ := List.any_eq_true.mp h
    exact cut_sound nd (valid p hp) cut he

def close {x : Word} (c : Charts x) : ℕ → ℕ → ℕ → List (Wire c) → List (Price x) →
    Cache → Option Cache
  | 0,_,_,_,_,_ => none
  | fuel+1,b,t,v,ps,db =>
    if immediate b t v ps then some db
    else
      let k := key b t v
      if db.contains k then some db
      else if v.any (fun a => a.w == x) then none
      else
        let act := fun s e =>
          if isEligible s v then
            close c fuel (s.budget b t).1 (s.budget b t).2 (s.after v)
              (ps.map (fun p => p.advance v s)) e
          else some e
        (batch act (Step.all b t v) db).map (fun e => e.insert k)

lemma close_sound {x : Word} (c : Charts x) (hx : proper x) (fuel : ℕ) {b t}
    {v : List (Wire c)} {ps} {db out : Cache}
    (nd : (v.map Wire.w).Nodup) (valid : ∀ p ∈ ps, p.Valid t (wires v)) (safe : Safe x db)
    (done : close c fuel b t v ps db = some out) : Safe x out ∧ ¬Exact x b t (wires v) := by
  induction fuel generalizing b t v ps db out with
  | zero => contradiction
  | succ fuel ih =>
    simp only [close] at done
    split at done
    · rename_i h
      obtain rfl := Option.some.inj done
      exact ⟨safe, immediate_sound nd valid h⟩
    split at done
    · rename_i h
      obtain rfl := Option.some.inj done
      have e := safe b t (sorted v) (Cache.contains_mem h)
      rw [key_set] at e; exact ⟨safe,e⟩
    split at done
    · contradiction
    rename_i nx
    have nox : x ∉ wires v := by
      rintro hm
      obtain ⟨w,hw,e⟩ := Step.mem_wires.mp hm
      exact nx (List.any_eq_true.mpr ⟨w,hw,beq_iff_eq.mpr e⟩)
    let act := fun (s : Step c) (e : Cache) =>
      if isEligible s v then
        close c fuel (s.budget b t).1 (s.budget b t).2 (s.after v)
          (ps.map (fun p => p.advance v s)) e
      else some e
    change (batch act (Step.all b t v) db).map (fun e => e.insert (key b t v)) = some out at done
    cases hb : batch act (Step.all b t v) db with
    | none => simp [hb] at done
    | some e =>
      have outEq : e.insert (key b t v) = out := by simpa only [hb,Option.map_some,
        Option.some.injEq] using done
      obtain ⟨se,branches⟩ := batch_sound (Q:=fun s => eligible v s →
        ¬Exact x (s.budget b t).1 (s.budget b t).2 (wires (s.after v)))
        (Step.all b t v) (run:=act) (db:=db) (out:=e) (by
          intro s hs d o sd sol
          by_cases he : isEligible s v = true
          · have h := (eligible_iff s v).1 he
            have sol' : close c fuel (s.budget b t).1 (s.budget b t).2 (s.after v) (ps.map (fun p => p.advance v s)) d = some o := by simpa [act,he] using sol
            have h' := ih (s.child_nd nd h.2) (by
              intro p hp
              obtain ⟨orig,hm,rfl⟩ := List.mem_map.mp hp
              exact advance_valid (valid _ hm) (Step.all_legal hs)) sd sol'
            exact ⟨h'.1,fun _ => h'.2⟩
          · have outEq : d=o := by simpa [act,he] using sol
            exact ⟨outEq ▸ sd,fun el => False.elim (he ((eligible_iff s v).2 el))⟩) safe hb
      have impossible : ¬Exact x b t (wires v) := by
        intro hypothetical
        rcases (descend c hx hypothetical).resolve_left nox with ⟨s,hs,el,h⟩
        exact branches s hs el h
      exact ⟨outEq ▸ safe_insert se impossible,impossible⟩

lemma price_subset {x : Word} {p : Price x} {t : ℕ} {S T : Finset Word}
    (h : p.Valid t S) (sub : T ⊆ S) : p.Valid t T := by
  refine ⟨h.1, fun b hb => h.2 b (weaken hb le_rfl le_rfl ?_)⟩
  exact Finset.union_subset_union_left (Finset.image_subset_image sub)

def validate {x : Word} (c : Charts x) (b t : ℕ) (v : List (Wire c)) (ps : List (Price x)) :=
  (batch (fun u db => close c (b+t+2) b t u ps db) v.sublists ∅).isSome

lemma verified {x : Word} (c : Charts x) (hx : proper x) {b t} {v : List (Wire c)} {ps}
    (nd : (v.map Wire.w).Nodup) (valid : ∀ p ∈ ps, p.Valid t (wires v))
    (check : validate c b t v ps = true) : ¬Feasible x b t (wires v) := by
  obtain ⟨out,done⟩ := Option.isSome_iff_exists.mp check
  have sf : Safe x ∅ := by intro b' t' ws h; exact False.elim h
  obtain ⟨_,no⟩ := batch_sound (Q:=fun u => ¬Exact x b t (wires u)) v.sublists
    (run:=fun u db => close c (b+t+2) b t u ps db) (db:=∅) (out:=out) (by
      intro u hu d e sd hh
      have sub := List.mem_sublists.mp hu
      have incl : wires u ⊆ wires v := by
        intro a ha; exact List.mem_toFinset.mpr ((sub.map Wire.w).subset (List.mem_toFinset.mp ha))
      exact close_sound c hx _ (nd.sublist (sub.map Wire.w))
        (fun p hp => price_subset (valid p hp) incl) sd hh) sf done
  rintro ⟨i,hi,j,hj,T,sub,hL⟩
  let u := v.filter (fun a => decide (a.w ∈ T))
  have eq : wires u = T := by
    ext a; rw [Step.mem_wires]
    constructor
    · rintro ⟨w,hw,rfl⟩; exact of_decide_eq_true (List.mem_filter.mp hw).2
    · intro ha
      obtain ⟨w,hw,e⟩ := Step.mem_wires.mp (sub ha)
      exact ⟨w,List.mem_filter.mpr ⟨hw,by simpa [e] using ha⟩,e⟩
  apply no u (List.mem_sublists.mpr List.filter_sublist)
  rw [eq]; exact ⟨i,hi,j,hj,hL⟩

def unpack (code : ℕ) (i : Fin 512) : Fin 512 := Fin.ofNat 512 (code >>> (9*i.val))

def basisFor (x : Word) (m : Word) (raw : List Word) (lo : ℕ) (row : Fin 512 → Fin 512)
    (good : ∀ i, bit m (row i) = true) : Basis x where
  mask := m
  raw := raw
  lo := lo
  proj := faceQ row
  zero := by
    apply BitVec.eq_of_getElem_eq; intro r hr
    change bit ((faceQ row).q 0) ⟨r,hr⟩ = bit 0 ⟨r,hr⟩
    rw [q_bit,bit_zero,bit_zero]
  one := by
    apply BitVec.eq_of_getElem_eq; intro r hr
    change bit ((faceQ row).q top) ⟨r,hr⟩ = bit top ⟨r,hr⟩
    rw [q_bit,bit_top,bit_top]
  refl a b e := by
    apply BitVec.eq_of_getElem_eq; intro r hr
    let i : Fin 512 := ⟨r,hr⟩
    change bit ((faceQ row).q a) i = bit ((faceQ row).q b) i
    rw [q_bit,q_bit]
    have he := congrArg (fun w => bit w (row i)) e
    change bit (combine false a m) (row i) = bit (combine false b m) (row i) at he
    simpa only [bit_bin,Bool.false_eq_true,ite_false,good,Bool.and_true] using he

lemma initial_price {x y : Word} {f : Basis x} {S child : Finset Word}
    (hy : proper y) (forbidden : ¬Feasible y (f.lo-1) 1 child) (ex : f.proj.q x = y)
    (inc : available f.proj S f.base ⊆ insert 0 child) :
    (Price.mk f 0).Valid 1 S := by
  refine ⟨ex ▸ hy, ?_⟩
  intro b h
  by_contra fail
  have bl : b ≤ f.lo-1 := by change ¬f.lo ≤ b+0 at fail; omega
  rw [ex] at h
  apply forbidden
  exact ignore hy (weaken h bl le_rfl inc) (Or.inr fun hp => hp.1 rfl)

end Replay2161
