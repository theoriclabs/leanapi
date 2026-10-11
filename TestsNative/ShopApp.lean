import LeanDb.Model
import LeanApi.Core
import LeanApi.Native
open LeanDb.Model LeanApi.Core

/-! Nested entities (theoriclabs/leanapi#6): an order's lines are declared under the order
(`Shop.Order.Line`), and a line's allocations under the line (`Shop.Order.Line.Allocation`), two
levels deep. A top-level `Refund` refers to a line. `app%` stores an entity when every name
between the api's namespace and the entity is a type, so all four are tables of `ShopApp`.
`Shop.Legacy` is a namespace, not a type: its `Order` is not part of the shop's domain (its table
would collide with `order`). `scripts/ddd_shop_acceptance.mjs` serves the app over real curl and
SQLite. -/

namespace Shop

structure Order where
  customer : Name
  deriving Entity

structure Order.Line where
  order    : Ref Order
  item     : Title
  quantity : Nat
  deriving Entity

structure Order.Line.Allocation where
  line      : Ref Order.Line
  warehouse : Title
  quantity  : Nat
  deriving Entity

structure Refund where
  line   : Ref Order.Line
  reason : Title
  deriving Entity

inductive OrderError where
  | notFound

structure OrderView where
  customer : Name

structure LineView where
  order    : Ref Order
  item     : Title
  quantity : Nat

structure AllocationView where
  line      : Ref Order.Line
  warehouse : Title
  quantity  : Nat

/-- A refund and the line it refunds, read through the refund's reference. -/
structure RefundView where
  reason   : Title
  item     : Title
  quantity : Nat

def placeOrder (customer : Name) : Op Empty (Ref Order) :=
  Order.insert { customer }

def addLine (order : Ref Order) (item : Title) (quantity : Nat) : Op OrderError (Ref Order.Line) := do
  let some _ ← Order.find order | throw .notFound
  Order.Line.insert { order, item, quantity }

def allocate (line : Ref Order.Line) (warehouse : Title) (quantity : Nat) :
    Op OrderError (Ref Order.Line.Allocation) := do
  let some _ ← Order.Line.find line | throw .notFound
  Order.Line.Allocation.insert { line, warehouse, quantity }

def refund (line : Ref Order.Line) (reason : Title) : Op OrderError (Ref Refund) := do
  let some _ ← Order.Line.find line | throw .notFound
  Refund.insert { line, reason }

def getOrder (order : Ref Order) : ReadOp OrderError OrderView := do
  let some o ← Order.find order | throw .notFound
  return { customer := o.customer }

def getLine (line : Ref Order.Line) : ReadOp OrderError LineView := do
  let some l ← Order.Line.find line | throw .notFound
  return { order := l.order, item := l.item, quantity := l.quantity }

def getAllocation (allocation : Ref Order.Line.Allocation) : ReadOp OrderError AllocationView := do
  let some a ← Order.Line.Allocation.find allocation | throw .notFound
  return { line := a.line, warehouse := a.warehouse, quantity := a.quantity }

def getRefund (refund : Ref Refund) : ReadOp OrderError RefundView := do
  let some r ← Refund.find refund | throw .notFound
  let some l ← Order.Line.find r.line | throw .notFound
  return { reason := r.reason, item := l.item, quantity := l.quantity }

def api : Api := [
  post "/orders"                        placeOrder,
  get  "/orders/:order"                 getOrder,
  post "/orders/:order/lines"           addLine,
  get  "/lines/:line"                   getLine,
  post "/lines/:line/allocations"       allocate,
  get  "/allocations/:allocation"       getAllocation,
  post "/lines/:line/refunds"           refund,
  get  "/refunds/:refund"               getRefund
]

/-! An entity in a namespace that is not a type is not part of the shop's domain. -/
namespace Legacy

structure Order where
  reference : Title
  deriving Entity

end Legacy

end Shop

app% ShopApp where
  api := Shop.api

-- The rule: every name between `Shop` and the entity is a type (`Shop.Order`, `Shop.Order.Line`);
-- `Shop.Legacy` is a namespace. An app at the root namespace takes none of the shop's entities.
run_cmd do
  let env ← Lean.getEnv
  for entity in [``Shop.Order, ``Shop.Order.Line, ``Shop.Order.Line.Allocation, ``Shop.Refund] do
    unless LeanApi.Native.isDomainEntity env `Shop entity do
      Lean.throwError "{entity} should be an entity of the Shop app"
  if LeanApi.Native.isDomainEntity env `Shop ``Shop.Legacy.Order then
    Lean.throwError "Shop.Legacy is a namespace, not a type: Shop.Legacy.Order is not the shop's"
  for entity in [``Shop.Order, ``Shop.Order.Line, ``Shop.Legacy.Order] do
    if LeanApi.Native.isDomainEntity env .anonymous entity then
      Lean.throwError "{entity} is not an entity of the root namespace"

-- The derived schema: the order, its lines, their allocations and the refunds, nothing else.
#guard (LeanDb.IsSchema.specs ShopApp.Database).map (·.name) == ["order", "line", "allocation", "refund"]
