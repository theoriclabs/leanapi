/-
  The shape of an application built on LeanAPI (DESIGN §3.2), checked
  against the example applications' imports.

  An application has a domain (what it means), a schema (how it is
  stored), policies (who may see and change which rows) and an API (how it
  is exposed over HTTP). Business rules live in the first three, and none
  of them depends on HTTP: they depend on who the actor is (`Auth`), not on
  how the actor was established.

  Covered: helpdesk, billing and scheduling, and the row-policy library
  they share (`PolicyView.Policy`). The graph has an edge for each import
  these modules make and stops at LeanAPI and LeanDB, whose own shape is
  `Architecture.Framework`. The executables' `main` modules are not in it:
  one Lean file cannot import several modules that each define `main`.
-/
import Architecture.Graph
import Helpdesk.Api
import Billing.Api
import Billing.Bypass
import Scheduling.Api
import Scheduling.Bypass

namespace Architecture.Apps

open Architecture Lean

/-- The layers of an application, and what it builds on. -/
inductive Layer where
  /-- What the application means: values, entities, invariants, decisions. -/
  | domain
  /-- How the domain is stored: tables, keys, row invariants. -/
  | schema
  /-- Who may see and change which rows. -/
  | policies
  /-- How operations are exposed: endpoints, codecs, errors. -/
  | api
  /-- What the types refuse: attempts to get around the policies, checked to fail. -/
  | bypass
  /-- The row-policy library (the prototype of DESIGN §7.5). -/
  | policyLib
  /-- LeanAPI's authenticated actor, `Auth`. -/
  | actor
  /-- LeanAPI's property library. -/
  | props
  /-- The rest of LeanAPI: HTTP. -/
  | http
  /-- LeanDB. -/
  | leandb
  /-- Lean's core and standard library. -/
  | lean
  deriving DecidableEq, Repr

open Layer

/-- Every module of the covered applications, by name, then the packages
    they use by prefix. A new module fails `conforms` until it is placed. -/
def rules : List (Name × Layer) := [
  (`Helpdesk.Domain,   domain),   (`Helpdesk.Schema,   schema),
  (`Helpdesk.Policies, policies), (`Helpdesk.Api,      api),
  (`Billing.Domain,    domain),   (`Billing.Schema,    schema),
  (`Billing.Policies,  policies), (`Billing.Api,       api),
  (`Billing.Bypass,    bypass),
  (`Scheduling.Domain,   domain),   (`Scheduling.Schema, schema),
  (`Scheduling.Policies, policies), (`Scheduling.Api,    api),
  (`Scheduling.Bypass,   bypass),
  (`PolicyView.Policy,  policyLib),
  (`LeanApi.Auth.Actor, actor),
  (`LeanApi.Props,      props),
  (`LeanApi,            http),
  (`LeanDb,             leandb),
  (`Init, lean), (`Std, lean), (`Lean, lean)]

def layerOf (m : Name) : Option Layer :=
  (rules.find? fun r => r.1.isPrefixOf m).map (·.2)

/-- Which layer may use which, directly. -/
def design : Graph Layer := ⟨[
  (domain, props), (domain, lean),
  (schema, domain), (schema, leandb),
  (policies, schema), (policies, policyLib),
  (policyLib, actor), (policyLib, leandb),
  (bypass, policies),
  (api, policies), (api, http),
  (http, actor), (http, props), (http, leandb),
  (props, lean), (actor, lean), (leandb, lean)]⟩

/-- The covered applications' imports, as this build compiled them. -/
def imports : Graph Name := imports% Helpdesk Billing Scheduling PolicyView.Policy

/-- **Every import of the covered applications follows the design.** -/
theorem conforms : imports.Conforms design layerOf := by conforms

/-- A module of layer `p` never reaches a module of layer `q`, through any
    chain of the applications' imports. -/
def NeverReaches (p q : Layer) : Prop :=
  ∀ m m', imports.Reaches m m' → layerOf m = some p → layerOf m' ≠ some q

theorem neverReaches_of {p q : Layer} (h : ¬ design.Reaches p q) : NeverReaches p q :=
  fun _ _ hr hp hq => h (conforms.reaches hr hp hq)

/-- **The domain needs no request, no socket and no database** (DESIGN
    §3.2): it reaches neither HTTP nor LeanDB, nor the policies. -/
theorem domain_is_plain_lean :
    NeverReaches domain http ∧ NeverReaches domain leandb ∧ NeverReaches domain policies :=
  ⟨neverReaches_of (Graph.not_reaches_of_check (by decide)),
   neverReaches_of (Graph.not_reaches_of_check (by decide)),
   neverReaches_of (Graph.not_reaches_of_check (by decide))⟩

/-- **Business rules do not depend on HTTP.** The schema, the policies and
    the policy library reach the actor, never the rest of LeanAPI: who may
    see a row depends on who is asking, not on how they logged in. -/
theorem rules_never_reach_http :
    NeverReaches schema http ∧ NeverReaches policies http ∧ NeverReaches policyLib http :=
  ⟨neverReaches_of (Graph.not_reaches_of_check (by decide)),
   neverReaches_of (Graph.not_reaches_of_check (by decide)),
   neverReaches_of (Graph.not_reaches_of_check (by decide))⟩

/-- **Nothing depends on the API**: it is the outermost layer, so the
    application can be exposed another way without touching its rules. -/
theorem nothing_reaches_the_api :
    NeverReaches domain api ∧ NeverReaches schema api ∧ NeverReaches policies api :=
  ⟨neverReaches_of (Graph.not_reaches_of_check (by decide)),
   neverReaches_of (Graph.not_reaches_of_check (by decide)),
   neverReaches_of (Graph.not_reaches_of_check (by decide))⟩

end Architecture.Apps
