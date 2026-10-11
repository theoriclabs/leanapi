import TestsNative.LibraryApp
import TestsNative.Evolving
import TestsNative.PartifulBefore
import TestsNative.ShopApp

/-! `leanapi_apps`: fixture apps served over HTTP and SQLite by the acceptance scripts.
`library …` (the generality fixture, `scripts/ddd_library_acceptance.mjs`), `evolving …` (the
migration gate, `scripts/ddd_migration_acceptance.mjs`), `partiful-before` (the post's app
before `guestList`, the old database of `scripts/ddd_partiful_api_acceptance.mjs`) and `shop`
(entities nested under entities, `scripts/ddd_shop_acceptance.mjs`). -/

def main (args : List String) : IO UInt32 := do
  match args with
  | "library" :: rest => Library.main rest
  | "evolving" :: rest => Evolving.main rest
  | "partiful-before" :: rest => PartifulBefore.server.main rest { database := "partiful.sqlite" }
  | "shop" :: rest => ShopApp.main rest { database := "shop.sqlite" }
  | _ => do
    IO.eprintln "usage: leanapi_apps (library … | evolving … | partiful-before | shop) [migrate [--check]]"
    return 2
