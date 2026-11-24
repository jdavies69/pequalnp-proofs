import SignedMask
import SymCheck
namespace Replay2161
noncomputable def permEquiv {x : Word} (a : Automorphism x) : Word ≃ Word :=
  Equiv.ofBijective a.p.q ⟨a.inj,Finite.surjective_of_injective a.inj⟩

noncomputable def Automorphism.back {x : Word} (a : Automorphism x) : Automorphism x := by
  let f := permEquiv a
  have inv (w : Word) : a.p.q (f.symm w)=w := f.apply_symm_apply w
  refine ⟨⟨f.symm,?_,?_⟩,?_,?_,f.symm.injective,?_⟩
  · intro w; apply a.inj; rw [inv,a.p.neg,inv]
  · intro d u v; apply a.inj; rw [inv,a.p.bin,inv,inv]
  · apply a.inj; rw [inv,a.zero]
  · apply a.inj; rw [inv,a.one]
  · apply a.inj; rw [inv,a.fix]
lemma Automorphism.back_q {x : Word} (a : Automorphism x) (w : Word) : a.back.p.q (a.p.q w)=w := by
  change (permEquiv a).symm (permEquiv a w)=w
  exact Equiv.symm_apply_apply ..
lemma Automorphism.reflect {x : Word} (a : Automorphism x) {b t S} (h : Exact x b t (S.image a.p.q)) : Exact x b t S := by
  have r:=a.back.map_exact h
  have eq : (S.image a.p.q).image a.back.p.q=S := by ext w; simp [Finset.mem_image,a.back_q]
  rwa [eq] at r

def fromOrbit {x : Word} {c : Charts x} (root : Frame c) (depth tape : ℕ) (a : Rotation root) (f : Frame c) :=
  (root.replay depth tape).any (fun g=>f.b==g.b && f.t==g.t && (bareReplay a.base depth tape).isPerm (f.v.map Wire.w))
lemma orbit_hit {x : Word} {c : Charts x} {root f : Frame c} {depth tape} {a : Rotation root}
    (good : ∀ g, root.replay depth tape=some g → g.No) (hit : fromOrbit root depth tape a f=true) : f.No := by
  obtain ⟨g,eg,h⟩ := (Option.any_eq_true ..).1 hit
  obtain ⟨⟨b,t⟩,pm⟩ := (Bool.and_eq_true_iff.mp h).imp_left Bool.and_eq_true_iff.mp
  have eq : (wires g.v).image a.R.p.q=wires f.v := by
    have words : bareReplay a.base depth tape=(g.v.map Wire.w).map a.R.p.q := by
      rw [a.eq,project_tape,←replay_words eg]
    ext z
    have p := (List.isPerm_iff.mp pm).mem_iff (a:=z)
    rw [words] at p
    simpa only [wires,List.mem_toFinset,List.mem_map,Finset.mem_image] using p
  intro he
  apply good g eg
  apply a.R.reflect
  rw [eq,←beq_iff_eq.mp b,←beq_iff_eq.mp t]
  exact he
end Replay2161
