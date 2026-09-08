/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

prelude

public import Init.Prelude

/-!
-/


@[expose] public section

theorem div_eq_div_of_eq_eq {G : Type u} [Div G] {a b c d : G}
    (h1 : Eq a c) (h2 : Eq b d) : Eq (HDiv.hDiv a b) (HDiv.hDiv c d) :=
  Eq.rec (Eq.rec (Eq.refl _) h2) h1
