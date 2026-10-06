import LeanApi.Native.AuthStorage
import LeanApi.Core.Flow
import LeanDb.Native

/-! The native operation family: LeanDB's native storage family (`storageResources s`, the
schema's own dictionaries) and, for `auth`, the app's session storage. A published
operation's `f.Requirements.infer` at `resources s` finds LeanDB's storage evidence and the
`Auth.HasStorage` instance `native_credential_storage%` generates. -/
namespace LeanApi.Native
open LeanDb.Model LeanApi.Core

@[reducible] def resources (s : Type) [LeanDb.IsSchema s] : Resources :=
  { toStorageResources := LeanDb.Native.storageResources s
    auth := fun storage => Auth.Storage s _ storage }

@[reducible] instance {s T} [LeanDb.IsSchema s] (storage : (resources s).entity T)
    [Auth.HasStorage s T storage] : HasAuthResource (resources s) T storage :=
  ⟨Auth.HasStorage.storage⟩

end LeanApi.Native
