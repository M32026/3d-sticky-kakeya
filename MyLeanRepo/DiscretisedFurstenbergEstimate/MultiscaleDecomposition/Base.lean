module

/-
Copyright (c) 2024 The Discretised Furstenberg Estimate Team.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raven Team
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.Base.Core
public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.Base.CoveringBasics
public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.Base.CoveringProducts
public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.Base.GridHelpers
public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.Base.Dictionary
public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.Base.Superlinear
public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.Base.CodeFunctionLipschitz

@[expose] public section

/-! # Multiscale Decomposition Base

This module re-exports all sub-modules of the multiscale decomposition base:
- `Core`: foundational definitions (dyadic squares, uniform sets, code function, ε-linear)
- `CoveringBasics`: basic covering number lemmas
- `CoveringProducts`: product covering formulas for uniform sets
- `GridHelpers`: grid-based covering helpers
- `Dictionary`: dictionary constant and supporting lemmas
- `Superlinear`: ε-superlinear to IsDeltaSSet conversion
-/
