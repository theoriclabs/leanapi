import Lake
open Lake DSL

package «leanapi-domain» where
  -- The released pin provides Contract. Domain execution/auth use peer work in progress.
  defaultTargets := #[`LeanApiDomain.Contract]

-- Same-repository native core; portable contracts are an optional git dependency.
require leanapi from "../.."
require leanreact from git "https://github.com/theoriclabs/leanreact" @ "c975968bfc7b46fbb2104b8996cfc4b7429755d3"

lean_lib LeanApiDomain where
  roots := #[`LeanApiDomain]
  globs := #[.one `LeanApiDomain, .submodules `LeanApiDomain]

lean_exe domain_contract_checks where
  srcDir := "tests"
  root := `ContractChecks

lean_lib DomainChecks where
  srcDir := "tests"
  roots := #[`AuthChecks, `ContractFixture]
  globs := #[.one `AuthChecks, .one `ContractFixture]
