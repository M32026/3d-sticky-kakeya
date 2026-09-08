/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceDirectPaidClosure
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceDirectPaidTrialTerminal

@[expose] public section

namespace Kakeya.ML2Assembly

open Kakeya.ML2Core

universe u

/-- This final producer reaches the existing PointwiseCore. The already
proved pointwiseDrop_of_pointwiseCore_free and monotone-nu main adapter
remain exact, separate consumers. No beta0-uniform strengthening is used. -/
theorem source_pointwiseCore_of_actual_direct_trials
    (hSFE : StickyKakeya.StickyFrostmanEstimate.{0, 0}
      (E := EuclideanSpace Real (Fin 3))) : PointwiseCore.{u} := by
  intro beta hbeta hbeta1 hKT hF
  obtain ⟨c, hc, hcbeta, P, htrial⟩ :=
    source_exists_direct_paid_trial hSFE hbeta hbeta1 hKT hF
  exact ⟨c, hc, hcbeta, P.eta, P.dichotomy_exponent_pos, P.dichotomy_exponent_le_one,
    source_direct_dichotomy_of_fixedQ_runs P hbeta.le hc
      (source_exists_direct_fixedQ_run P htrial)⟩

end Kakeya.ML2Assembly
