import FastStages

namespace Replay2161

structure Automorphism (x : Word) where
  p : Projection
  zero : p.q 0=0
  one : p.q top=top
  inj : Function.Injective p.q
  fix : p.q x=x

def autoFor (x : Word) (f g : Fin 512 → Fin 512) (rightInv : ∀ i, f (g i)=i)
    (fixed : (faceQ f).q x=x) : Automorphism x where
  p := faceQ f
  zero := by
    apply BitVec.eq_of_getElem_eq; intro r hr
    change bit ((faceQ f).q 0) ⟨r,hr⟩ = bit 0 ⟨r,hr⟩; rw [q_bit,bit_zero,bit_zero]
  one := by
    apply BitVec.eq_of_getElem_eq; intro r hr
    change bit ((faceQ f).q top) ⟨r,hr⟩ = bit top ⟨r,hr⟩; rw [q_bit,bit_top,bit_top]
  inj := by
    intro a b h
    apply BitVec.eq_of_getElem_eq; intro r hr
    let i : Fin 512 := ⟨r,hr⟩
    have e := congrArg (fun w => bit w (g i)) h
    change bit a i=bit b i
    simpa only [q_bit,rightInv] using e
  fix := fixed

namespace Automorphism
variable {x : Word}

lemma maps_proper (R : Automorphism x) {a} (h : proper a) : proper (R.p.q a) := by
  constructor
  · exact fun e => h.1 (R.inj (e.trans R.zero.symm))
  · exact fun e => h.2 (R.inj (e.trans R.one.symm))

lemma map_live (R : Automorphism x) {b t S} (h : Live x b t S) :
    Live x b t (S.image R.p.q) := by
  induction h with
  | done => simpa only [Finset.image_singleton,R.fix] using (Live.done (target:=x))
  | @unary b t U a pa fresh tail ih =>
    rw [Finset.image_insert]
    rw [Finset.image_insert,R.p.neg] at ih
    apply Live.unary (R.maps_proper pa) _ ih
    rw [←R.p.neg,←Finset.image_insert]
    intro hm
    obtain ⟨y,hy,e⟩ := Finset.mem_image.mp hm
    exact fresh ((R.inj e) ▸ hy)
  | @binary b t U a w d pa pw ne fresh tail ih =>
    rw [Finset.image_insert,Finset.image_insert]
    rw [Finset.image_insert,R.p.bin] at ih
    apply Live.binary (d:=d) (R.maps_proper pa) (R.maps_proper pw) (fun e => ne (R.inj e)) _ ih
    rw [←R.p.bin,←Finset.image_insert,←Finset.image_insert]
    intro hm
    obtain ⟨y,hy,e⟩ := Finset.mem_image.mp hm
    exact fresh ((R.inj e) ▸ hy)

lemma map_exact (R : Automorphism x) {b t S} (h : Exact x b t S) :
    Exact x b t (S.image R.p.q) := by
  obtain ⟨n,hn,j,hj,hl⟩ := h
  exact ⟨n,hn,j,hj,R.map_live hl⟩
end Automorphism

def bareStep (v : List Word) (j : ℕ) : List Word :=
  if j < 32 then
    let a := v.getD (j/2) 0
    ~~~a :: v.filter (fun u => (Nat.mod j 2 == 1) || u != a)
  else
    let i := j-32
    let a := v.getD (i/128) 0
    let b := v.getD (Nat.mod (i/8) 16) 0
    combine (Nat.mod (i/4) 2 == 1) a b :: v.filter (fun u =>
      ((Nat.mod (i/2) 2 == 1) || u != a) && ((Nat.mod i 2 == 1) || u != b))

def bareReplay (v : List Word) : ℕ → ℕ → List Word
  | 0,_ => v
  | d+1,tape => bareStep (bareReplay v d (tape/4096)) (Nat.mod tape 4096-1)

lemma filt_map {α β : Type} (f : α→β) (p : α→Bool) (q : β→Bool) (ok : ∀ a, q (f a)=p a)
    (v : List α) : (v.map f).filter q = (v.filter p).map f := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    simp only [List.map_cons,List.filter_cons,ok]
    cases p a <;> simp [ih]

lemma mapped_get {α β : Type} (f : α→β) (a : α) (v : List α) (i : ℕ) :
    (v.map f).getD i (f a)=f (v.getD i a) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases v[i]? <;> rfl

lemma project_step {x : Word} (R : Automorphism x) (v : List Word) (j : ℕ) :
    bareStep (v.map R.p.q) j=(bareStep v j).map R.p.q := by
  have bne (a b : Word) : (R.p.q a != R.p.q b) = (a != b) := by
    apply Bool.eq_iff_iff.mpr; simp only [bne_iff_ne]; exact not_congr R.inj.eq_iff
  have get (i : ℕ) : (v.map R.p.q).getD i 0 = R.p.q (v.getD i 0) := by
    simpa only [R.zero] using mapped_get R.p.q 0 v i
  by_cases small : j < 32
  · simp only [bareStep,small,ite_true,get,List.map_cons,R.p.neg]
    congr 1; exact filt_map _ _ _ (fun u => by simp only [bne]) _
  · simp only [bareStep,small,ite_false,get,List.map_cons,R.p.bin]
    congr 1; exact filt_map _ _ _ (fun u => by simp only [bne]) _

lemma project_tape {x : Word} (R : Automorphism x) (v : List Word) (d tape : ℕ) :
    bareReplay (v.map R.p.q) d tape=(bareReplay v d tape).map R.p.q := by
  induction d generalizing tape with
  | zero => rfl
  | succ d ih => simp only [bareReplay,ih,project_step]

lemma decode_words {x : Word} {c : Charts x} {f : Frame c} {j : ℕ} {s : Step c}
    (eq : f.decoded j=some s) :
    (s.after f.v).map Wire.w=bareStep (f.v.map Wire.w) j := by
  unfold Frame.decoded at eq
  unfold bareStep
  split at eq
  · rename_i small
    simp only [small,ite_true]
    split at eq
    · contradiction
    cases e : f.v[j/2]? with
    | none => simp [e] at eq
    | some a =>
      simp only [e,Option.map_some,Option.some.injEq] at eq
      subst s
      simp only [List.getD_eq_getElem?_getD,List.getElem?_map,e,Option.map_some,Option.getD_some,
        Step.after,Step.out,Step.rest,Wire.flip,List.map_cons,List.cons.injEq,true_and]
      exact (filt_map Wire.w _ (fun u => (Nat.mod j 2 == 1) || u != a.w) (fun _ => rfl) f.v).symm
  · rename_i large
    simp only [large,ite_false]
    split at eq
    · contradiction
    let i := j-32
    change ((f.v[i/128]?).bind _)=some s at eq
    cases e : f.v[i/128]? with
    | none => simp [e] at eq
    | some a =>
      simp only [e,Option.bind_some] at eq
      cases z : f.v[Nat.mod (i/8) 16]? with
      | none => simp [i] at z; simp [z] at eq
      | some b =>
        change Option.map _ (f.v[Nat.mod (i/8) 16]?) = some s at eq
        simp only [z,Option.map_some,Option.some.injEq] at eq
        subst s
        simp only [i] at e z
        simp only [List.getD_eq_getElem?_getD,List.getElem?_map,e,z,Option.map_some,Option.getD_some,
          Step.after,Step.out,Step.rest,Wire.binary,List.map_cons,List.cons.injEq,true_and]
        exact (filt_map Wire.w _ (fun u => ((Nat.mod (i/2) 2 == 1) || u != a.w) && ((Nat.mod i 2 == 1) || u != b.w)) (fun _ => rfl) f.v).symm

lemma jump_words {x : Word} {c : Charts x} {f g : Frame c} {j : ℕ} (h : f.jump j=some g) :
    g.v.map Wire.w=bareStep (f.v.map Wire.w) j := by
  unfold Frame.jump at h
  cases e : f.decoded j with
  | none => simp [e] at h
  | some s =>
    simp only [e,Option.bind_some] at h
    split at h
    · obtain rfl := Option.some.inj h; exact decode_words e
    · contradiction

lemma replay_words {x : Word} {c : Charts x} {f g : Frame c} {d tape} (h : f.replay d tape=some g) :
    g.v.map Wire.w=bareReplay (f.v.map Wire.w) d tape := by
  induction d generalizing tape g with
  | zero => obtain rfl := Option.some.inj h; rfl
  | succ d ih =>
    unfold Frame.replay at h
    cases e : f.replay d (tape/4096) with
    | none => simp [e] at h
    | some q =>
      obtain hq := jump_words (by simpa only [e,Option.bind_some] using h :
        q.jump (Nat.mod tape 4096-1)=some g)
      rw [hq,ih e]; rfl

end Replay2161
