/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Tube.Basic
public import Kakeya.Tube.CardEssentiallyDistinct
public import Kakeya.Tube.CylinderApprox
public import Kakeya.Tube.Dilate
public import Kakeya.Tube.EDUpToMult
public import Kakeya.Tube.EssentiallyDistinctReduction
public import Kakeya.Tube.IntersectionVolume
public import Kakeya.Tube.Volume

/-!
# Tubes (entry point)

This file is the public entry point for the `Kakeya.Tube.*` family.
It re-exports the core submodules so downstream files can keep importing
`Kakeya.Tube` as a single module.

`Kakeya.Tube.BoundedOverlap` and the `Kakeya.Tube.EDPacking.*` family are
deliberately *not* re-exported here: they import `Kakeya.Tube` themselves and
must be imported directly.  `Kakeya.Tube.Rescale` is excluded for the same
reason, one step removed: it reaches `Kakeya.Tube` through
`Kakeya.Homothety → Kakeya.Multiplicity → Kakeya.ShadedUniform`.
-/
