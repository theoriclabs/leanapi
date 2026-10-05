import LeanApiDomain.Native

/-! Compatibility import for the now-complete native Flow algebra. Membership
probes are policy hooks; portable query Request has only now/find. -/
namespace LeanApi.Domain.Native
abbrev ReadM (s Error : Type) [LeanDb.IsSchema s] :=
  ExceptT (Contract.CallError Error) (LeanDb.Read s)
end LeanApi.Domain.Native
