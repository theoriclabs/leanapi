/-
  Percent-decoding for query strings and `application/x-www-form-urlencoded`
  bodies. Path segments are decoded by `Std.Http` after the path is split,
  so an encoded `/` (`%2F`) stays inside its segment.
-/
namespace LeanApi.Url

private def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Decode `%XX` escapes (and `+` as space when `plusSpace`). Invalid escapes
    or invalid UTF-8 yield `none`. -/
def percentDecode (s : String) (plusSpace : Bool := false) : Option String := do
  let rec go : List Char → ByteArray → Option ByteArray
    | [], acc => some acc
    | '%' :: a :: b :: rest, acc => do
        let hi ← hexVal a
        let lo ← hexVal b
        go rest (acc.push (hi * 16 + lo).toUInt8)
    | '%' :: _, _ => none
    | '+' :: rest, acc => go rest (if plusSpace then acc.push 32 else acc.push 43)
    | c :: rest, acc => go rest (acc ++ (String.singleton c).toUTF8)
  let bytes ← go s.toList ByteArray.empty
  String.fromUTF8? bytes

private def unreserved (c : Char) : Bool :=
  c.isAlphanum || c == '-' || c == '.' || c == '_' || c == '~'

private def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('A'.toNat + n - 10)

/-- Percent-encode everything outside the RFC 3986 unreserved set. -/
def percentEncode (s : String) : String := Id.run do
  let mut out := ""
  for b in s.toUTF8.toList do
    let c := Char.ofNat b.toNat
    if b.toNat < 128 && unreserved c then out := out.push c
    else out := out.push '%' |>.push (hexDigit (b.toNat / 16)) |>.push (hexDigit (b.toNat % 16))
  return out

/-- Parse `a=1&b=two` (form encoding: `+` is a space). Pairs whose key or
    value fail to decode make the whole parse fail. -/
def parseForm (s : String) : Option (List (String × String)) :=
  if s.isEmpty then some [] else
  (s.splitOn "&").filter (!·.isEmpty) |>.mapM fun part =>
    match part.splitOn "=" with
    | [k] => do return (← percentDecode k true, "")
    | k :: vs => do return (← percentDecode k true, ← percentDecode ("=".intercalate vs) true)
    | [] => none

end LeanApi.Url
