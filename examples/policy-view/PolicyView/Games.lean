/-
  Row-level security as a LeanDB view: the application half, on the
  private-games schema.
-/
import PolicyView.Policy
import PrivateGames.DbApi
open LeanDb PolicyView PrivateGames PrivateGames.Storage

namespace PolicyView.Games

/-! ## 1. The policies: declared once, with the schema

What `policy% GameRow (p : PlayerId) := fun g => g.val.x == pref p || g.val.o == pref p`
would generate. `TokenRow` and `ReceiptRow` get no policy here, so no
scoped program can read them (default deny). -/

instance : Policy Games PlayerId GameRow where
  rule p g := g.val.x == pref p || g.val.o == pref p
  scope p := (LeanDb.Query.from GameRow).where' fun g => g.val.x == pref p || g.val.o == pref p

instance : Policy Games PlayerId PlayerRow where
  rule _ _ := true
  scope _ := LeanDb.Query.from PlayerRow

/-! ## 2. Handlers: written over the view, with no scoping code -/

/-- One game, by id. No `visibleTo` in sight: the view applies the policy. -/
def readGame (me : Actor PlayerId) (gid : GameId) : ReadAs Games me (Option Game) := do
  let row ← ReadAs.get GameRow (gidRef gid)
  return row.map (reconstruct ·.toStored)

/-- All my games. -/
def myGames (me : Actor PlayerId) : ReadAs Games me (List Game) := do
  return (← ReadAs.all GameRow).map (reconstruct ·.toStored)

/-! ## 3. What the view refuses, at compile time -/

/-- error: Invalid `⟨...⟩` notation: Constructor for `PolicyView.ReadAs` is marked as private -/
#guard_msgs (substring := true) in
/-- Bypass 1: an unscoped read, smuggled into the view. -/
def sneaky (me : Actor PlayerId) (gid : GameId) : ReadAs Games me (Option (LeanDb.Valid GameRow)) :=
  ⟨Read.get GameRow (gidRef gid)⟩

/-- error: failed to synthesize instance of type class
  Policy Games PlayerId TokenRow -/
#guard_msgs (substring := true) in
/-- Bypass 2: a table with no policy (everyone's session tokens). -/
def tokens (me : Actor PlayerId) : ReadAs Games me (List (LeanDb.Valid TokenRow)) :=
  ReadAs.all TokenRow

/--
error: Invalid `⟨...⟩` notation: Constructor for `PolicyView.Actor` is marked as private
---
error: Invalid `⟨...⟩` notation: Constructor for `PolicyView.Actor` is marked as private
-/
#guard_msgs (substring := true) in
/-- Bypass 3: acting as another player. -/
def spoof (gid : GameId) : ReadAs Games (⟨⟨2⟩⟩ : Actor PlayerId) (Option Game) :=
  readGame ⟨⟨2⟩⟩ gid

end PolicyView.Games
