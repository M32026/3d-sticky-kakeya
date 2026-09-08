/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.WangZahl.EToD
public import Kakeya.DimensionThree.MainLemma2.WangZahl.WZBalancedCover
public import Kakeya.StickyKakeya.KatzTaoNodes

/-!
# Translating the Wang--Zahl every-scale hypothesis into the node reading

`Kakeya.WangZahl.KatzTaoEveryScale` (Wang--Zahl Definition `:4734`) says: for each
`ρ₀ ∈ [δ, 1]` there is a scale `ρ ∈ [ρ₀, K ρ₀)` and a `K`-balanced partitioning cover of the
family by `ρ`-tubes whose own canonical Katz--Tao convex Wolff constant is at most `K`.  The
project's `Tube.UniformTubeSet.IsKatzTaoAtEveryScale` instead reads `Kakeya.maxDensity` off the
node families of *one* nested hierarchy at the grid scales `ρ_k = δ^{k/N}`.

This file converts the first into the second, on any hierarchy carried by a subfamily.  Two
steps:

* `Kakeya.WangZahl.maxDensity_le_katzTaoConvexWolffConstant` — the source's `C_KT` bound on the
  parent family gives the project's `Kakeya.maxDensity` bound on it.  (The converse inequality
  is `Kakeya.WangZahl.katzTaoConvexWolffConstant_le_maxDensity`; together they say the two
  constants agree, but only this direction is used here.)
* `Kakeya.StickyKakeya.isKatzTaoAtEveryScale_nodes_of_ambient_covers` — the node-density
  comparison, which transfers a density bound from a cover at a comparable scale to the nodes.
-/

@[expose] public section

open MeasureTheory Convexity

namespace Kakeya.WangZahl

noncomputable section

universe u

/-! ### The two Katz--Tao constants, the direction the bridge needs -/

/-- **The canonical convex Wolff constant controls the project's maximal convex density.**

This is the converse of `Kakeya.WangZahl.katzTaoConvexWolffConstant_le_maxDensity`, and it is
the easy direction: every `ConvexSpaceBody` is a `ConvexTestSet`, and the members of a family of
`ρ`-tubes all have the same volume `tubeVolume ρ`, so the source's counting estimate is literally
the statement that the density in that test body is at most `C`. -/
theorem maxDensity_le_katzTaoConvexWolffConstant {ρ : NNReal} (hρ : 0 < ρ)
    {ι : Type u} (s : Finset ι) (P : ι → ShadedTube ρ Space3) :
    Kakeya.maxDensity s (fun j => ((P j).toTube).toConvexSpaceBody)
      ≤ katzTaoConvexWolffConstant s P := by
  classical
  have hvol := tubeVolume_pos_and_ne_top hρ
  rw [katzTaoConvexWolffConstant]
  refine le_sInf ?_
  rintro C ⟨hCpos, hC⟩
  rw [Kakeya.maxDensity_le_iff]
  intro K
  rw [Kakeya.densityIn_le_iff]
  set Wt : ConvexTestSet := ⟨K.carrier, K.convex⟩ with hWt
  have hfilt : (s.filter fun j => ((P j).toTube).toConvexSpaceBody ≤ K)
      = @Finset.filter ι (fun j => (P j).carrier ⊆ Wt.carrier) (Classical.decPred _) s := by
    refine Finset.filter_congr ?_
    intro j _
    simp only [hWt, eq_iff_iff]
    constructor
    · intro h; exact h
    · intro h; exact h
  have hsum : (∑ j ∈ s with ((P j).toTube).toConvexSpaceBody ≤ K,
        volume (((P j).toTube).toConvexSpaceBody).carrier)
      = ((@Finset.filter ι (fun j => (P j).carrier ⊆ Wt.carrier)
          (Classical.decPred _) s).card : ENNReal) * tubeVolume ρ := by
    rw [← hfilt, Finset.sum_congr rfl (fun j _ => volume_carrier_eq_tubeVolume P j),
      Finset.sum_const, nsmul_eq_mul]
  rw [hsum]
  calc ((@Finset.filter ι (fun j => (P j).carrier ⊆ Wt.carrier)
          (Classical.decPred _) s).card : ENNReal) * tubeVolume ρ
      ≤ (C * volume Wt.carrier * (tubeVolume ρ)⁻¹) * tubeVolume ρ := by
        exact mul_le_mul_right' (hC Wt) _
    _ = C * volume K.carrier := by
        rw [mul_assoc, ENNReal.inv_mul_cancel hvol.1.ne' hvol.2, mul_one]

end

end Kakeya.WangZahl

end
