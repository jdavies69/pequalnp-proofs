import TraceCircuit
import ReaderBranches
namespace PetersenReaderTrace
open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_2502

theorem norm_nonreader (g : Gate) (leg : Ok g) (off : ¬PetersenReader.reader g) :
    Regular (normGate g) := by
  have ok:=normGate_nok g leg
  refine ⟨ok.1.1,ok.1.2,ok.2,?_⟩
  intro mem
  apply off
  obtain ⟨op,ins⟩:=g
  have kind : op=.and ∨ op=.or ∨ op=.not := leg.1
  rcases kind with h|h|h <;> change op=_ at h <;> subst op <;>
    simpa [PetersenReader.reader,GateOp.eval,normGate] using mem

theorem aliasOfOr (pre : List Gate) (g : Gate) (mode : g.op=.or)
    (read : PetersenReader.reader g=true) (size : g.inputs.length≤2) :
    ∃ i, eval g (run pre initial)=(((run pre initial).getD i z).1,7) := by
  obtain ⟨op,ins⟩:=g
  change op=.or at mode;subst op
  change ins.length≤2 at size
  have six : 6∈ins := by simpa [PetersenReader.reader,GateOp.eval] using read
  rcases ins with _|⟨u,_|⟨v,_|⟨q,more⟩⟩⟩
  · simp at six
  · have e : 6=u := by simpa using six
    subst u
    have fixed : (run pre initial).getD 6 z=(0,7) := sixUnchanged pre initial (by decide)
    refine ⟨6,?_⟩
    change op true ((run pre initial).getD 6 z) z = _
    rw [fixed]
    exact (units _).2.1
  · rcases (by simpa using six : 6=u ∨ 6=v) with e|e
    · subst u;exact ⟨v,readerValue pre v false⟩
    · subst v;exact ⟨u,readerValue pre u true⟩
  · simp at size
end PetersenReaderTrace
