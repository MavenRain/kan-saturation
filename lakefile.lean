import Lake
open Lake DSL

package «kan-saturation» where
  leanOptions := #[⟨`autoImplicit, false⟩]

-- Reservoir-ready dependencies: the categorical + tactic foundation is fetched
-- from git so this package is self-contained and `require`-able standalone.
-- comp-cat-theory is declared before kan-tactics so this package's pin wins over
-- kan-tactics' transitive require; the pin matches the rev kan-tactics uses,
-- keeping the diamond consistent.
require «comp-cat-theory» from git
  "https://github.com/MavenRain/comp-cat-theory.git" @ "f521081"

require «kan-tactics» from git
  "https://github.com/MavenRain/kan-tactics.git" @ "f914eaa6b499580929a0da547809b39f02e529cb"

@[default_target]
lean_lib «KanSaturation» where
  roots := #[`KanSaturation]

-- Examples and data-level tests, in a separate non-default target so the library
-- proper stays a clean reusable dependency.
lean_lib «KanSaturationExamples» where
  roots := #[`KanSaturationExamples]

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"
