module

/-
  Coarse Normalized Ratio Producer (Lane 7)

  Produces `CoarseRatioData δ s` from:
  1. Coarse tube count NΔ and multiplicity MΔ (from B1 lane 5)
  2. Coarse bound NΔ ≥ δ^{-(s+ε)} (from Appendix A lane 6)
  3. Uniform Prop 5 / Corollary 2.5 effective bound on coarse config
  4. Parameter u0 = min(u, 1), α = (u0-s)/(1-s)

  The core two-case logic is `coarse_two_case_ratio` in AlgebraicAssembly.lean.
  This module provides a clean interface specialized to the B1+AppA context.

  Key correction: coarse gain = ε*α/2 - loss, NOT ε.
  α = (u0 - s)/(1 - s), u0 = min(u, 1).

  Two cases on X = MΔ * Δ^s:
    Case 1 (X ≥ Δ^{-ε}): Cor 2.5 gives
      NΔ/MΔ ≥ C_prop5 * Δ^{-s} * X^α ≥ Δ^{-(s+εα)} = δ^{-(s/2 + εα/2)}
    Case 2 (X < Δ^{-ε}): coarse bound gives
      NΔ/MΔ > δ^{-(s+ε)} / Δ^{-s-ε} = Δ^{-(s+ε)} = δ^{-(s/2 + ε/2)}

  Deliverable: `coarse_ratio_producer` theorem.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Section6.Types
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Section6.AlgebraicAssembly
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DirecretisedFurstenbergEstimate.Section6

open DiscretisedFurstenbergEstimate

/-- Clean coarse normalized ratio producer.

    Given coarse-scale data (NΔ, MΔ), the Appendix A coarse bound,
    and the effective Corollary 2.5 bound, produce `CoarseRatioData δ s`.

    Parameters:
    - `δ`: fine scale (= Δ^2)
    - `Δ`: coarse scale
    - `s`: tube dimension
    - `u0`: capped point dimension (`u0 = min(u, 1)`, must satisfy `s < u0 ≤ 1`)
    - `ε`: Appendix A gain parameter
    - `NΔ`: coarse tube count
    - `MΔ`: coarse multiplicity (tubes per point)
    - `C_prop5`: effective constant from Corollary 2.5 (polylogs absorbed)
    - `loss`: exponent lost to polylog/constant absorption
    - `α := (u0 - s)/(1 - s)`

    The effective Cor 2.5 bound is:
      `NΔ ≥ C_prop5 * MΔ * Δ^{-s} * (MΔ * Δ^s)^α`

    The coarse bound is:
      `NΔ ≥ δ^{-(s+ε)}`

    Output: `CoarseRatioData δ s` with `coarseGain = ε*α/2 - loss > 0`.
-/
def coarse_ratio_producer
    {δ Δ s u0 ε C_prop5 loss : ℝ}
    {NΔ MΔ : ℝ}
    (hδ_pos : 0 < δ) (hδ_one : δ ≤ 1)
    (hΔ_pos : 0 < Δ) (hΔ_one : Δ < 1)
    (hδ_eq2 : δ = Δ ^ 2)
    (hs : 0 < s) (hs1 : s < 1)
    (hsu : s < u0) (hu0_one : u0 ≤ 1)
    (hε_pos : 0 < ε)
    (hNΔ_nonneg : 0 ≤ NΔ)
    (hMΔ_pos : 0 < MΔ)
    -- Appendix A coarse bound
    (h_coarse_bound : NΔ ≥ δ ^ (-(s + ε)))
    -- Effective Corollary 2.5 / Uniform Prop 5 bound
    (hC_prop5_pos : 0 < C_prop5)
    (α : ℝ)
    (hα_def : α = (u0 - s) / (1 - s))
    (h_prop5 : NΔ ≥ C_prop5 * MΔ * Δ^(-s) * (MΔ * Δ^s)^α)
    -- Polylog absorption
    (hloss_pos : 0 ≤ loss)
    (h_absorb : C_prop5 ≥ δ ^ loss)
    (hloss_small : loss < ε * α / 2) :
    CoarseRatioData δ s :=
  coarse_two_case_ratio
    (hδ := hδ_pos) (hδ_one := hδ_one)
    (hΔ_pos := hΔ_pos) (hΔ_one := hΔ_one)
    (hδ_eq2 := hδ_eq2)
    (hs := hs) (hs1 := hs1) (hsu := hsu) (hu_one := hu0_one)
    (hε_pos := hε_pos)
    (NΔ := NΔ) (MΔ := MΔ)
    (hNΔ_nonneg := hNΔ_nonneg) (hMΔ_pos := hMΔ_pos)
    (h_coarse_bound := h_coarse_bound)
    (C_prop5 := C_prop5) (hC_prop5_pos := hC_prop5_pos)
    (α := α) (hα_def := hα_def)
    (h_prop5 := h_prop5)
    (loss := loss) (hloss_pos := hloss_pos)
    (h_absorb := h_absorb)
    (hloss_small := hloss_small)

/-- Convenience wrapper: compute α automatically from u0. -/
def coarse_ratio_producer'
    {δ Δ s u0 ε C_prop5 loss : ℝ}
    {NΔ MΔ : ℝ}
    (hδ_pos : 0 < δ) (hδ_one : δ ≤ 1)
    (hΔ_pos : 0 < Δ) (hΔ_one : Δ < 1)
    (hδ_eq2 : δ = Δ ^ 2)
    (hs : 0 < s) (hs1 : s < 1)
    (hsu : s < u0) (hu0_one : u0 ≤ 1)
    (hε_pos : 0 < ε)
    (hNΔ_nonneg : 0 ≤ NΔ)
    (hMΔ_pos : 0 < MΔ)
    (h_coarse_bound : NΔ ≥ δ ^ (-(s + ε)))
    (hC_prop5_pos : 0 < C_prop5)
    (h_prop5 : NΔ ≥ C_prop5 * MΔ * Δ^(-s) * (MΔ * Δ^s)^((u0 - s)/(1 - s)))
    (hloss_pos : 0 ≤ loss)
    (h_absorb : C_prop5 ≥ δ ^ loss)
    (hloss_small : loss < ε * ((u0 - s)/(1 - s)) / 2) :
    CoarseRatioData δ s :=
  coarse_ratio_producer
    (hδ_pos := hδ_pos) (hδ_one := hδ_one)
    (hΔ_pos := hΔ_pos) (hΔ_one := hΔ_one)
    (hδ_eq2 := hδ_eq2)
    (hs := hs) (hs1 := hs1)
    (hsu := hsu) (hu0_one := hu0_one)
    (hε_pos := hε_pos)
    (hNΔ_nonneg := hNΔ_nonneg) (hMΔ_pos := hMΔ_pos)
    (h_coarse_bound := h_coarse_bound)
    (hC_prop5_pos := hC_prop5_pos)
    (α := (u0 - s)/(1 - s))
    (hα_def := by rfl)
    (h_prop5 := h_prop5)
    (hloss_pos := hloss_pos)
    (h_absorb := h_absorb)
    (hloss_small := hloss_small)

end DirecretisedFurstenbergEstimate.Section6

end
