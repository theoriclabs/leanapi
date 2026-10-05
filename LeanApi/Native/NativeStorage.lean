import LeanApi.Native.Identity
import LeanApi.Native.Contract
import LeanDb.Native

/-! Typed framework failures of native storage steps. -/
namespace LeanApi.Native
open LeanDb

abbrev CommandM (Scope s Error : Type) [IsSchema s] := Txn Scope s (Contract.CallError Error)

def fault (code : String) (status : Nat := 500) : Contract.CallError Error :=
  .protocol ⟨code, some status, ""⟩

/-- LeanDB's storage-step failures (`LeanDb.Native.StorageFault`) as typed framework replies.
None of them is a domain conflict: declared conflicts come back as values. -/
def storageFault (fault : LeanDb.Native.StorageFault) : Contract.CallError Error :=
  Native.fault fault.code (match fault with
    | .invalidReference _ => 400
    | .invalidRow _ => 422
    | .missingReference _ | .restricted _ | .gone => 409
    | .invalidIdentity _ | .unmappedConflict _ => 500)

end LeanApi.Native
