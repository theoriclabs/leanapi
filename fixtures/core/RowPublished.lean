import TestsCore.PostPart1
open LeanDb.Model LeanApi.Core
inductive LeakError where
  | notFound
def leak (party : Ref Party) : ReadOp LeakError (Row Party) := do
  let some p ← Party.find party | throw .notFound
  return p
derive_operation leak
