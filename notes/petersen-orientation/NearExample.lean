import ModuleCertificate
namespace PetersenOrientation.Example
open Replay2161 PEqualNP.Outside.L_meta_1667
def dict : Rows := #[#[0,270009350]]
theorem sharedImpossible : ¬Shared graph ws.toFinset := noShared 3 0 (by decide +kernel) (by decide +kernel) ws dict 1 256 (by decide +kernel)
theorem circuitImpossible : Impossible graph 11 ws.toFinset := excludeNear (by decide +kernel) signedImpossible sharedImpossible
end PetersenOrientation.Example
#print axioms PetersenOrientation.Example.circuitImpossible
