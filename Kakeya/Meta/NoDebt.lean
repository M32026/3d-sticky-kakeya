/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Lean.Attributes

/-!
# The `@[no_debt]` attribute

Tag a declaration with `@[no_debt]` to exempt it from `#audit_debt`'s heartbeat
threshold (defined in `TechDebt.lean`). Use it for declarations that are inherently
expensive to elaborate and accepted as such, so the check does not keep flagging them.

This module is deliberately tiny and depends only on `Lean`, so any file in the library
can `import Kakeya.NoDebt` to tag a declaration without pulling in extra dependencies.
-/

open Lean

/-- The environment extension backing the `@[no_debt]` tag. -/
public initialize noDebtAttr : TagAttribute ←
  registerTagAttribute `no_debt
    "Exempt this declaration from #audit_debt's heartbeat threshold."
