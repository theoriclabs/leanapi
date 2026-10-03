import LeanApiDomain.Native
import LeanApp.Domain.Op

/-! Actor dictionaries for plain operations (DDD-LR-05): an app structure with
`deriving Principal` (`SignedIn`), or `Option` of one. Kept out of `Native` because the
portable `Op` module brings scoped do-element keywords (`create`, `Row`, …). -/
namespace LeanApi.Domain.Native

/-- `SignedIn`: built only here, by `Principal.trusted`, from the live profile row of a
valid session (cookie or bearer); no credential is 401. Assembly passes it by name with
`rfl`: its profile index is a class projection that instance search does not unfold. -/
def principalActor {A P : Type} [LeanApp.Domain.Entity P] (principal : LeanApp.Domain.Principal A)
    (profile : principal.Profile = P) : ActorContext (fun _ => A) P where
  resolve := fun store config env req mutation => do
    match ← Auth.resolve (Scope := Unit) config env req store.live mutation with
    | .error error => return .error (error.mapDomain Empty.elim)
    | .ok none => return .error .unauthenticated
    | .ok (some row) => return .ok (principal.trusted (profile ▸ row.id) (profile ▸ row.value))

/-- `Option SignedIn`: `none` only when no credential is presented; a presented invalid
credential is still 401. -/
def optionalPrincipalActor {A P : Type} [LeanApp.Domain.Entity P] (principal : LeanApp.Domain.Principal A)
    (profile : principal.Profile = P) : ActorContext (fun _ => Option A) P where
  resolve := fun store config env req mutation => do
    match ← Auth.resolve (Scope := Unit) config env req store.live mutation with
    | .error error => return .error (error.mapDomain Empty.elim)
    | .ok none => return .ok none
    | .ok (some row) => return .ok (some (principal.trusted (profile ▸ row.id) (profile ▸ row.value)))

end LeanApi.Domain.Native
