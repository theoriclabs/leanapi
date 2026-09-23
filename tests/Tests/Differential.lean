/-
  Differential check: the native service (LeanDB, scoped repository,
  single writer) against the reference model `step`, on random request
  sequences. The model is given the same sessions and players; each request
  goes to both, and statuses, bodies and the headers that matter must agree.
  Evidence for "native ≡ model" in EVIDENCE.md (checked, not proved).
-/
import PrivateGames.Model.Step
import PrivateGames.App.Service
import Tests.Games

namespace Tests.Differential

open LeanApi LeanApi.Test Lean PrivateGames PrivateGames.App PrivateGames.Model Tests.Games

/-- Compare responses on what is observable and deterministic. -/
def comparable (r : Res) : Nat × List (String × String) × String :=
  (r.status, r.headers.filter (fun (k, _) => k == "etag" || k == "location" || k == "idempotent-replayed" || k == "allow" || k == "www-authenticate"),
   r.bodyText)

def replyComparable (r : Reply) : Nat × List (String × String) × String :=
  (r.status, r.headers.filter (fun (k, _) => k == "etag" || k == "location" || k == "idempotent-replayed" || k == "allow" || k == "www-authenticate"),
   r.body)

def run : TestM Unit := do
  section_ "differential: native vs model" do
    let env ← freshEnv "differential"
    let names := ["n1", "n2", "n3", "n4"]
    let mut users : Array (Nat × String) := #[]
    for n in names do users := users.push (← signup env.svc n)
    let mut world : World := {
      games := [], receipts := [], nextGame := 1
      players := users.toList.map fun (id, _) => ⟨id⟩
      sessions := users.toList.map fun (id, t) => (Tokens.digest t, ⟨id⟩) }
    let mut mismatches := 0
    let mut total := 0
    for step_ in [0:400] do
      let u ← IO.rand 0 (users.size - 1)
      let (_, tok) := users[u]!
      let pick ← IO.rand 0 9
      let gid ← IO.rand 1 6
      let rev ← IO.rand 0 3
      let cell ← IO.rand 0 8
      let opp := users[← IO.rand 0 (users.size - 1)]!.1
      let key ← IO.rand 0 3
      let keyH : List (String × String) := if key == 0 then [] else [("Idempotency-Key", s!"k{key}")]
      let tokH := if pick == 9 then ("Authorization", "Bearer bogus") else ("Authorization", s!"Bearer {tok}")
      let (m, target, hs, body) : String × String × List (String × String) × String := match pick with
        | 0 | 1 => ("POST", "/games", [("Content-Type", "application/json")] ++ keyH,
                    (Json.mkObj [("opponent", Json.num opp)]).compress)
        | 2 => ("GET", s!"/games/{gid}", [], "")
        | 3 => ("GET", s!"/games?per=2&page={1 + gid % 3}", [], "")
        | 4 | 5 | 6 => ("POST", s!"/games/{gid}/moves",
                    [("Content-Type", "application/json"), ("If-Match", s!"\"{rev}\"")] ++ keyH,
                    (Json.mkObj [("cell", Json.num cell)]).compress)
        | 7 => ("POST", s!"/games/{gid}/resignation", keyH, "")
        | 8 => ("PUT", s!"/games/{gid}", [], "")
        | _ => ("GET", s!"/games/{gid}", [], "")
      let native ← request env.svc m target (tokH :: hs) body
      let some meth := Method.ofString? m | continue
      let req := Req.mk' meth target ((tokH :: hs).map fun (k, v) => (k.toLower, v)) body.toUTF8
      let (res, w') := Model.step req world
      world := w'
      total := total + 1
      if replyComparable native != comparable res then
        mismatches := mismatches + 1
        if mismatches ≤ 3 then
          IO.eprintln s!"  step {step_}: {m} {target}\n    native {repr (replyComparable native)}\n    model  {repr (comparable res)}"
    checkEq s!"{total} requests: native ≡ model" mismatches 0
    env.rt.close

end Tests.Differential
