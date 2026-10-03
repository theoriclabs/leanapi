import LeanApiDomain
example {s : Type} [LeanDb.IsSchema s]
    (write : LeanApi.Env → LeanApi.Req → Unit → LeanApi.Tx s (Contract.CallError Unit) Unit)
    (codecs : Contract.Http.Codecs) (op : Contract.Operation .query Unit Unit Unit) :
    LeanApi.Domain.Published s :=
  LeanApi.Domain.TrustedAdapter.query codecs op write (fun _ => 409) {path := "/api/query"}
