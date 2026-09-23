/-
  `multipart/form-data` (RFC 7578), for buffered bodies within the route's
  body limit. Parts carry their headers, `name`, optional `filename`, and
  bytes. Limits: at most `maxParts` parts; malformed input is `none`.
-/
import LeanApi.Http.Extract

namespace LeanApi

structure Part where
  name : String
  filename : Option String
  contentType : Option String
  data : ByteArray

private def indexOf (hay needle : ByteArray) (start : Nat) : Option Nat := Id.run do
  if needle.size == 0 then return some start
  let mut i := start
  while i + needle.size ≤ hay.size do
    let mut ok := true
    for j in [0:needle.size] do
      if hay[i + j]! != needle[j]! then ok := false; break
    if ok then return some i
    i := i + 1
  return none

private def paramOf (header : String) (key : String) : Option String :=
  (header.splitOn ";").findSome? fun p =>
    match (p.trimAscii.toString).splitOn "=" with
    | k :: vs@(_ :: _) =>
      if k.trimAscii.toString.toLower == key then
        let v := ("=".intercalate vs).trimAscii.toString
        some (if v.startsWith "\"" && v.endsWith "\"" && v.length ≥ 2 then ((v.drop 1).dropEnd 1).toString else v)
      else none
    | _ => none

/-- The boundary from `Content-Type: multipart/form-data; boundary=...`. -/
def multipartBoundary (req : Req) : Option String := do
  let ct ← req.header? "content-type"
  if req.contentType? != some "multipart/form-data" then none
  let b ← paramOf ct "boundary"
  if b.isEmpty || b.length > 70 then none else some b

def parseMultipart (body : ByteArray) (boundary : String) (maxParts : Nat := 100) : Option (List Part) := do
  let delim := ("--" ++ boundary).toUTF8
  let crlf := "\r\n".toUTF8
  let sep := "\r\n\r\n".toUTF8
  let mut pos ← indexOf body delim 0
  let mut parts : Array Part := #[]
  repeat
    pos := pos + delim.size
    -- closing delimiter
    if pos + 1 < body.size && body[pos]! == 45 && body[pos+1]! == 45 then break
    if !(pos + 1 < body.size && body[pos]! == 13 && body[pos+1]! == 10) then none
    let hStart := pos + 2
    let hEnd ← indexOf body sep hStart
    let headText ← String.fromUTF8? (body.extract hStart hEnd)
    let headers := (headText.splitOn "\r\n").filterMap fun l =>
      match l.splitOn ":" with
      | k :: vs@(_ :: _) => some (k.trimAscii.toString.toLower, (":".intercalate vs).trimAscii.toString)
      | _ => none
    let dataStart := hEnd + sep.size
    let next ← indexOf body (crlf ++ delim) dataStart
    let disp ← headers.lookup "content-disposition"
    let name ← paramOf disp "name"
    parts := parts.push { name, filename := paramOf disp "filename", contentType := headers.lookup "content-type",
                          data := body.extract dataStart next }
    if parts.size > maxParts then none
    pos := next + crlf.size
  return parts.toList

/-- Extract all parts (422 at `body` on malformed multipart). -/
def Extract.multipart : Extract (List Part) := fun r =>
  match multipartBoundary r with
  | none => .error [⟨"body", "expected multipart/form-data with a boundary"⟩]
  | some b => match parseMultipart r.body b with
    | some ps => .ok ps
    | none => .error [⟨"body", "malformed multipart body"⟩]

end LeanApi
