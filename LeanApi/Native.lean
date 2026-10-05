import LeanApi.Native.App

/-! # LeanApi.Native: operations served over HTTP and SQLite

`app% Name where api := api` (no accounts) and
`app% Name where authentication := P with C api := api` (accounts) serve a `LeanApi.Core` api
natively: LeanDB's schema and migration gate, the api's routes in the `{"ok"}`/`{"error"}`
envelope, cookie and bearer sessions with CSRF, and KDF work prepared before writer
admission. See `LeanApi.Native.App`. -/
