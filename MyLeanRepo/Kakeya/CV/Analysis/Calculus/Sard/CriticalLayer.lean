/-
Copyright (c) 2026 SeedProver. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SeedProver
-/
module

public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.CriticalLayerLocal
public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.LocalCriticalImage
public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.Measure

@[expose] public section

namespace ForMathlib.Analysis.Calculus.Sard

open MeasureTheory
open scoped ContDiff

/-- Sub-lemma A: For each `k ≥ 1`, the image of `C k \ C (k + 1)` has measure zero,
where `C k` is the set where all iterated derivatives of order `≤ k` vanish. -/
lemma sub_lemma_A {m : ℕ} (k : ℕ) (hk_pos : 1 ≤ k)
    (f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ) (hf : ContDiff ℝ ∞ f)
    (ih : ∀ (g : EuclideanSpace ℝ (Fin m) → ℝ), ContDiff ℝ ∞ g →
      (volume : Measure ℝ) (g '' {x | fderiv ℝ g x = 0}) = 0) :
    (volume : Measure ℝ) (f '' (C f k \ C f (k + 1))) = 0 :=
  sub_lemma_A_local k hk_pos f hf ih


end ForMathlib.Analysis.Calculus.Sard
