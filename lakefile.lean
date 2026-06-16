import Lake
open Lake DSL

package «kan-saturation» where
  leanOptions := #[⟨`autoImplicit, false⟩]

-- Mathlib-free stack: the carriers are core Lean (Int/Nat/Rat) and the
-- saturation reflector is built in comp-cat-theory.  comp-cat-theory is
-- declared FIRST so this local checkout overrides kan-tactics' transitive
-- git require for the same package.
require «comp-cat-theory» from ".." / "comp-cat-theory"
require «kan-tactics» from ".." / "kan-tactics"

@[default_target]
lean_lib «KanSaturation» where
  roots := #[`KanSaturation]

-- Examples live in a separate, non-default target so the library stays
-- a clean reusable dependency.  (Added once example modules exist.)

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"
