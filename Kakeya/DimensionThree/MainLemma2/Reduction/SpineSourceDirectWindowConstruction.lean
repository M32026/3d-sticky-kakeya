/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceDirectWindowData

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal Classical

namespace Kakeya.ML2Core

universe u

/-- Choose a usable VNS window before building its ladder or mesh. This
does not replace varpi inside an already supplied dependent parameter pack.
The strict bound is an output of this new parameter-selection obligation. -/
theorem source_exists_direct_bounded_vns_parameters {beta : Real}
    (hbeta0 : 0 < beta) (hbeta1 : beta <= 1) :
    exists (varpi : Real) (rawGain rawDens : Real -> Real),
      0 < varpi /\ varpi < 1 / 2 /\
      ML2Assembly.Lemma91ParamsAt.{u} beta varpi rawGain rawDens := by
  obtain ⟨varpi, gain, dens, hp⟩ := ML2Assembly.exists_lemma91ParamsAt.{u} hbeta0 hbeta1
  refine ⟨min varpi (1 / 4), gain, dens, lt_min hp.window_pos (by norm_num),
    lt_of_le_of_lt (min_le_right _ _) (by norm_num), ?_⟩
  exact ⟨lt_min hp.window_pos (by norm_num), hp.gain_pos, hp.dens_pos,
    hp.gain_le_dens, fun z hz =>
      VNSUniform.VNSBody.mono_window (min_le_left _ _) (hp.body z hz)⟩

end Kakeya.ML2Core
