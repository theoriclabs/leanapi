/-
  Base64 (RFC 4648 §4), standard alphabet with padding, and base64url
  (§5) without padding. Pure Lean: encodings only. Anything secret-dependent
  lives in the crypto dependency (docs/decisions/0002-q10-crypto.md).
-/
namespace LeanApi.Base64

private def stdAlphabet : String :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
private def urlAlphabet : String :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_"

private def encodeWith (alpha : Array Char) (pad : Bool) (data : ByteArray) : String := Id.run do
  let mut out := ""
  let n := data.size
  let mut i := 0
  while i + 2 < n do
    let b := (data[i]!.toNat <<< 16) ||| (data[i+1]!.toNat <<< 8) ||| data[i+2]!.toNat
    out := out.push alpha[(b >>> 18) &&& 63]! |>.push alpha[(b >>> 12) &&& 63]!
      |>.push alpha[(b >>> 6) &&& 63]! |>.push alpha[b &&& 63]!
    i := i + 3
  let rest := n - i
  if rest == 1 then
    let b := data[i]!.toNat <<< 16
    out := out.push alpha[(b >>> 18) &&& 63]! |>.push alpha[(b >>> 12) &&& 63]!
    if pad then out := out ++ "=="
  else if rest == 2 then
    let b := (data[i]!.toNat <<< 16) ||| (data[i+1]!.toNat <<< 8)
    out := out.push alpha[(b >>> 18) &&& 63]! |>.push alpha[(b >>> 12) &&& 63]!
      |>.push alpha[(b >>> 6) &&& 63]!
    if pad then out := out ++ "="
  return out

private def valueOf (url : Bool) (c : Char) : Option Nat :=
  if 'A' ≤ c && c ≤ 'Z' then some (c.toNat - 'A'.toNat)
  else if 'a' ≤ c && c ≤ 'z' then some (c.toNat - 'a'.toNat + 26)
  else if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat + 52)
  else if url then
    if c == '-' then some 62 else if c == '_' then some 63 else none
  else
    if c == '+' then some 62 else if c == '/' then some 63 else none

/-- Strict decode of unpadded digits: rejects a lone trailing digit and
    non-zero leftover bits, so every accepted string is canonical. -/
private def decodeDigits (url : Bool) (cs : List Char) : Option ByteArray := do
  let vals ← cs.mapM (valueOf url)
  let arr := vals.toArray
  let n := arr.size
  if n % 4 == 1 then none
  let mut out := ByteArray.empty
  let mut i := 0
  while i + 3 < n do
    let b := (arr[i]! <<< 18) ||| (arr[i+1]! <<< 12) ||| (arr[i+2]! <<< 6) ||| arr[i+3]!
    out := out.push (b >>> 16).toUInt8 |>.push ((b >>> 8) &&& 255).toUInt8 |>.push (b &&& 255).toUInt8
    i := i + 4
  let rest := n - i
  if rest == 2 then
    if arr[i+1]! &&& 15 != 0 then none
    let b := (arr[i]! <<< 18) ||| (arr[i+1]! <<< 12)
    out := out.push (b >>> 16).toUInt8
  else if rest == 3 then
    if arr[i+2]! &&& 3 != 0 then none
    let b := (arr[i]! <<< 18) ||| (arr[i+1]! <<< 12) ||| (arr[i+2]! <<< 6)
    out := out.push (b >>> 16).toUInt8 |>.push ((b >>> 8) &&& 255).toUInt8
  return out

/-- Standard base64 with `=` padding. -/
def encode (data : ByteArray) : String := encodeWith stdAlphabet.toList.toArray true data

/-- Strict standard base64: length a multiple of 4, padding only at the end. -/
def decode (s : String) : Option ByteArray :=
  let cs := s.toList
  if cs.length % 4 != 0 then none
  else
    let body := cs.reverse.dropWhile (· == '=') |>.reverse
    if cs.length - body.length > 2 then none
    else decodeDigits false body

/-- base64url without padding (RFC 7515 §2). -/
def encodeUrl (data : ByteArray) : String := encodeWith urlAlphabet.toList.toArray false data

/-- Strict base64url: no padding, canonical trailing bits. -/
def decodeUrl (s : String) : Option ByteArray := decodeDigits true s.toList

end LeanApi.Base64
