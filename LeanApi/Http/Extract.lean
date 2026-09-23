/-
  Extraction and validation.

  Every decoder returns `Except (List FieldError) α`: a location such as
  `path.id`, `query.page` or `body.title`, and a message. Domain types plug
  in by giving a `FromParam` instance (one string: path, query, header,
  cookie, form field) or a `FromBody` instance (a JSON value), whose body
  calls the type's smart constructor. So `Title` rejects an empty title the
  same way whether it arrives in a URL, a form, or JSON.

  `Extract α` is a reader over `Req` that accumulates errors across
  independent fields (applicative `<*>` collects both sides' errors), so a
  client learns every bad field at once.
-/
import LeanApi.Http.Request
import Lean.Data.Json

namespace LeanApi

open Lean

structure FieldError where
  loc : String
  msg : String
  deriving Repr, BEq, Inhabited

def FieldError.toJson (e : FieldError) : Json :=
  Json.mkObj [("loc", .str e.loc), ("msg", .str e.msg)]

/-- 422 with an `errors` array; `400` when the body itself did not parse. -/
def FieldError.problem (es : List FieldError) (status : Nat := 422) : Problem :=
  (Problem.make status (some "request validation failed")).withExt "errors" (Json.arr (es.map FieldError.toJson).toArray)

/-! ## Scalar decoding -/

/-- Decode one string (a path segment, query value, header, cookie, form
    field). The message says what was expected; the location is added by
    the extractor. -/
class FromParam (α : Type) where
  fromParam : String → Except String α

instance : FromParam String := ⟨.ok⟩
instance : FromParam Nat := ⟨fun s => match s.toNat? with | some n => .ok n | none => .error "expected a natural number"⟩
instance : FromParam Int := ⟨fun s => match s.toInt? with | some n => .ok n | none => .error "expected an integer"⟩
instance : FromParam Int64 := ⟨fun s => match s.toInt? with
  | some n => if n ≥ Int64.minValue.toInt && n ≤ Int64.maxValue.toInt then .ok (Int64.ofInt n) else .error "out of range"
  | none => .error "expected an integer"⟩
instance : FromParam Bool := ⟨fun s => match s.toLower with
  | "true" | "1" | "yes" | "on" => .ok true
  | "false" | "0" | "no" | "off" => .ok false
  | _ => .error "expected a boolean"⟩

/-- A type with a validated constructor from a raw representation: define
    `SmartCtor` once and get `FromParam` and `FromBody` for free. -/
class SmartCtor (α : Type) (β : outParam Type) where
  make : β → Except String α
  raw : α → β

instance (priority := low) [SmartCtor α β] [FromParam β] : FromParam α :=
  ⟨fun s => do SmartCtor.make (← FromParam.fromParam (α := β) s)⟩

/-! ## Structured decoding -/

/-- Decode a JSON value at a location (`body`, `body.title`, `body.items[2]`). -/
class FromBody (α : Type) where
  fromBody : (loc : String) → Json → Except (List FieldError) α

/-- Any `FromJson` type decodes as a body, with the location of the whole
    value. Use `field` for per-field locations. -/
instance (priority := low) [FromJson α] : FromBody α :=
  ⟨fun loc j => match fromJson? j with
    | .ok a => .ok a
    | .error m => .error [⟨loc, m⟩]⟩

instance (priority := mid) [SmartCtor α β] [FromBody β] : FromBody α :=
  ⟨fun loc j => do
    let b ← FromBody.fromBody (α := β) loc j
    match SmartCtor.make b with
    | .ok a => .ok a
    | .error m => .error [⟨loc, m⟩]⟩

/-- Accumulating applicative for decoders. -/
abbrev Decoded := Except (List FieldError)

def both (a : Decoded α) (b : Decoded β) : Decoded (α × β) :=
  match a, b with
  | .ok x, .ok y => .ok (x, y)
  | .error e, .ok _ => .error e
  | .ok _, .error e => .error e
  | .error e₁, .error e₂ => .error (e₁ ++ e₂)

/-- A required object field, decoded with its own location. -/
def field [FromBody α] (loc : String) (j : Json) (name : String) : Decoded α :=
  let l := s!"{loc}.{name}"
  match j.getObjVal? name with
  | .ok v => if v.isNull then .error [⟨l, "field required"⟩] else FromBody.fromBody l v
  | .error _ =>
    match j with
    | .obj _ => .error [⟨l, "field required"⟩]
    | _ => .error [⟨loc, "expected an object"⟩]

/-- An optional object field: missing or `null` is `none`. -/
def fieldOpt [FromBody α] (loc : String) (j : Json) (name : String) : Decoded (Option α) :=
  match j.getObjVal? name with
  | .ok .null => .ok none
  | .ok v => (FromBody.fromBody s!"{loc}.{name}" v).map some
  | .error _ =>
    match j with
    | .obj _ => .ok none
    | _ => .error [⟨loc, "expected an object"⟩]

/-- An optional field with a default. -/
def fieldD [FromBody α] (loc : String) (j : Json) (name : String) (d : α) : Decoded α :=
  (fieldOpt loc j name).map (·.getD d)

/-! ## Extractors -/

/-- A request decoder with accumulated field errors. -/
def Extract (α : Type) := Req → Decoded α

instance : Functor Extract where
  map f x := fun r => (x r).map f

instance : Pure Extract := ⟨fun a _ => .ok a⟩

/-- Independent fields: errors from both sides are reported. -/
instance : Seq Extract where
  seq f x := fun r => (both (f r) (x () r)).map fun (g, a) => g a

instance : Applicative Extract := {}

instance : Monad Extract where
  bind x f := fun r => match x r with
    | .ok a => f a r
    | .error e => .error e

namespace Extract

def run (x : Extract α) (r : Req) : Decoded α := x r

private def decodeAt [FromParam α] (loc : String) (s : String) : Decoded α :=
  match FromParam.fromParam s with
  | .ok a => .ok a
  | .error m => .error [⟨loc, m⟩]

def path [FromParam α] (name : String) : Extract α := fun r =>
  match r.param? name with
  | some s => decodeAt s!"path.{name}" s
  | none => .error [⟨s!"path.{name}", "missing path parameter"⟩]

def query [FromParam α] (name : String) : Extract α := fun r =>
  match r.query? name with
  | some s => decodeAt s!"query.{name}" s
  | none => .error [⟨s!"query.{name}", "field required"⟩]

def queryOpt [FromParam α] (name : String) : Extract (Option α) := fun r =>
  match r.query? name with
  | some s => (decodeAt s!"query.{name}" s).map some
  | none => .ok none

def queryD [FromParam α] (name : String) (d : α) : Extract α := (·.getD d) <$> queryOpt name

def header [FromParam α] (name : String) : Extract α := fun r =>
  match r.header? name with
  | some s => decodeAt s!"header.{name.toLower}" s
  | none => .error [⟨s!"header.{name.toLower}", "header required"⟩]

def headerOpt [FromParam α] (name : String) : Extract (Option α) := fun r =>
  match r.header? name with
  | some s => (decodeAt s!"header.{name.toLower}" s).map some
  | none => .ok none

def cookie [FromParam α] (name : String) : Extract α := fun r =>
  match r.cookie? name with
  | some s => decodeAt s!"cookie.{name}" s
  | none => .error [⟨s!"cookie.{name}", "cookie required"⟩]

def cookieOpt [FromParam α] (name : String) : Extract (Option α) := fun r =>
  match r.cookie? name with
  | some s => (decodeAt s!"cookie.{name}" s).map some
  | none => .ok none

/-- The raw JSON body (checked `Content-Type` is done by `jsonBody`). -/
def rawJson : Extract Json := fun r =>
  match r.bodyText? with
  | none => .error [⟨"body", "body is not UTF-8"⟩]
  | some s =>
    if s.trimAscii.isEmpty then .error [⟨"body", "body required"⟩] else
    match Json.parse s with
    | .ok j => .ok j
    | .error m => .error [⟨"body", s!"invalid JSON: {m}"⟩]

/-- The JSON body, decoded with `FromBody` at location `body`. -/
def json [FromBody α] : Extract α := fun r => do FromBody.fromBody "body" (← rawJson r)

/-- A form body (`application/x-www-form-urlencoded`). -/
def formPairs : Extract (List (String × String)) := fun r =>
  match r.bodyText? >>= fun s => Url.parseForm s with
  | some ps => .ok ps
  | none => .error [⟨"body", "invalid form encoding"⟩]

def form [FromParam α] (name : String) : Extract α := fun r => do
  match (← formPairs r).lookup name with
  | some s => decodeAt s!"body.{name}" s
  | none => .error [⟨s!"body.{name}", "field required"⟩]

def formOpt [FromParam α] (name : String) : Extract (Option α) := fun r => do
  match (← formPairs r).lookup name with
  | some s => (decodeAt s!"body.{name}" s).map some
  | none => .ok none

end Extract

/-! ## Content negotiation -/

/-- Parsed `Accept` entries: media range and quality. -/
def parseAccept (v : String) : List (String × Float) :=
  (v.splitOn ",").filterMap fun part =>
    match (part.splitOn ";").map (·.trimAscii.toString) with
    | [] => none
    | range :: params =>
      if range.isEmpty then none else
      let q := params.findSome? fun p =>
        match p.splitOn "=" with
        | ["q", v] => some (if v == "0" || v == "0.0" || v == "0.00" || v == "0.000" then 0.0
                            else if v.startsWith "1" then 1.0 else 0.5)
        | _ => none
      some (range.toLower, q.getD 1.0)

/-- Does `accept` allow media type `mt`? A missing header accepts anything. -/
def accepts (accept : Option String) (mt : String) : Bool :=
  match accept with
  | none => true
  | some v =>
    let entries := parseAccept v
    if entries.isEmpty then true else
    let (ty, _) := match mt.splitOn "/" with | [a, b] => (a, b) | _ => (mt, "")
    entries.any fun (range, q) =>
      q > 0.0 && (range == "*/*" || range == mt || range == s!"{ty}/*")

/-- 415 unless the request has one of `types` as its media type. A request
    without a body (no Content-Type, empty body) passes. -/
def requireContentType (types : List String) (h : App) : App := fun req =>
  let refuse : IO Res :=
    pure ((Problem.make 415 (some s!"expected {", ".intercalate types}")).withHeader "accept-post" (", ".intercalate types)).toRes
  match req.contentType? with
  | some ct => if types.contains ct then h req else refuse
  | none => if req.body.isEmpty then h req else refuse

/-- 406 unless the client accepts one of `produces`. Problem bodies are
    exempt from the check once the handler runs. -/
def requireAccept (produces : List String) (h : App) : App := fun req =>
  if produces.any (accepts (req.header? "accept")) then h req
  else pure (Problem.make 406 (some s!"available: {", ".intercalate produces}")).toRes

/-! ## Handlers from extractors -/

/-- Decode the request, then run `f`. Decode failures become 422 (400 when
    the body is not parseable at all). -/
def handle (x : Extract α) (f : α → IO Res) : App := fun req =>
  match x req with
  | .ok a => f a
  | .error es =>
    let status := if es.any (fun e => e.loc == "body" && (e.msg.startsWith "invalid JSON" || e.msg == "body is not UTF-8" || e.msg == "invalid form encoding")) then 400 else 422
    pure (FieldError.problem es status).toRes

/-- `handle` for a JSON body: checks `Content-Type: application/json` (415)
    and requires a body. -/
def handleJson (x : Extract α) (f : α → IO Res) : App :=
  requireContentType ["application/json"] (handle x f)

end LeanApi
