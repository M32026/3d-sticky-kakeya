/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.RandomTranslation.RigidFrostman
public import Kakeya.DimensionThree.AffineTransport
public import Kakeya.Tube.EDPacking.FrostmanCount

/-!
# Pulling a convex test body back along a rigid motion

The deterministic Frostman packing count `ConvexSpaceBody.IsFrostmanIn.card_le_of_subset` bounds
the number of members of the *original* family contained in a test body. The random variable that
the Frostman conjunct of GWZ Lemma 3.8 actually controls counts members of the *moved* family
contained in the test body. The two are converted into each other by

`R(T) ⊆ K  ↔  T ⊆ R⁻¹(K)`,

so what is needed is the convex body `R⁻¹(K)` and the fact that it has the same volume as `K`.

Both come for free from the affine transport layer of `Section6/AffineTransport.lean`: a rigid
motion is an affine automorphism (`Kakeya.rigidAffineEquiv`) whose linear part is unitary, hence of
determinant `±1`, so `Kakeya.affineJacobian` is `1` and `ConvexSpaceBody.volume_mapAffine` becomes
plain volume invariance. No new geometry is developed here.
-/

@[expose] public section

open MeasureTheory Metric Set

namespace Kakeya

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A rigid motion, packaged as an affine automorphism of `E`. -/
def rigidAffineEquiv (u : unitary (E →L[ℝ] E)) (v : E) : E ≃ᵃ[ℝ] E :=
  ((Unitary.linearIsometryEquiv u).toLinearEquiv.toAffineEquiv).trans
    (AffineEquiv.constVAdd ℝ E v)

omit [MeasurableSpace E] [BorelSpace E] in
@[simp]
theorem rigidAffineEquiv_apply (u : unitary (E →L[ℝ] E)) (v x : E) :
    rigidAffineEquiv u v x = rigidMap u v x := by
  simp [rigidAffineEquiv, rigidMap, add_comm]
  rfl

omit [MeasurableSpace E] [BorelSpace E] in
theorem rigidAffineEquiv_coe (u : unitary (E →L[ℝ] E)) (v : E) :
    (rigidAffineEquiv u v : E → E) = rigidMap u v := by
  funext x
  simp [rigidAffineEquiv, rigidMap, add_comm]
  rfl

/-- The absolute Jacobian of a rigid motion is `1`: its linear part is a linear isometry of a
finite-dimensional inner product space, so its determinant is `±1`. -/
theorem affineJacobian_rigidAffineEquiv (u : unitary (E →L[ℝ] E)) (v : E) :
    affineJacobian (rigidAffineEquiv u v) = 1 := by
  let L : E ≃ₗᵢ[ℝ] E := Unitary.linearIsometryEquiv u
  have hlin : (rigidAffineEquiv u v).linear = L.toLinearEquiv := by
    rw [rigidAffineEquiv]
    rfl
  let B : Set E := Metric.closedBall (0 : E) 1
  have hBall_home : (rigidAffineEquiv u v).linear '' B = B := by
    rw [hlin]
    change ((L : E ≃ₗᵢ[ℝ] E) : E → E) '' Metric.closedBall (0 : E) 1 = Metric.closedBall (0 : E) 1
    rw [LinearIsometryEquiv.image_closedBall]
    simp
  have hBvol_zero : volume B ≠ 0 := by
    exact ne_of_gt (Metric.measure_closedBall_pos volume (0 : E) (by norm_num : (0 : ℝ) < 1))
  have hBvol_top : volume B ≠ ⊤ := by
    exact ne_of_lt (MeasureTheory.measure_closedBall_lt_top)
  have hAbs : |LinearMap.det ((rigidAffineEquiv u v).linear : E →ₗ[ℝ] E)| = (1 : ℝ) := by
    have hvol : volume B =
        ENNReal.ofReal |LinearMap.det ((rigidAffineEquiv u v).linear : E →ₗ[ℝ] E)| * volume B := by
      have hVol := MeasureTheory.Measure.addHaar_image_linearMap volume
        ((rigidAffineEquiv u v).linear : E →ₗ[ℝ] E) B
      simpa [hBall_home] using hVol
    have hx1 : ENNReal.ofReal |LinearMap.det ((rigidAffineEquiv u v).linear : E →ₗ[ℝ] E)| * volume B
        = 1 * volume B := by
      rw [one_mul]
      exact hvol.symm
    have hE : ENNReal.ofReal |LinearMap.det ((rigidAffineEquiv u v).linear : E →ₗ[ℝ] E)| = 1 := by
      apply le_antisymm
      · exact (ENNReal.mul_le_mul_iff_left hBvol_zero hBvol_top).mp (by simp [hx1])
      · exact (ENNReal.mul_le_mul_iff_left hBvol_zero hBvol_top).mp (by simp [hx1])
    exact (ENNReal.ofReal_eq_ofReal_iff (abs_nonneg _) (by norm_num)).mp (by simpa using hE)
  rw [affineJacobian]
  simp [hAbs]

/-- Transport along a rigid motion preserves volume. -/
theorem volume_mapAffine_rigidAffineEquiv (K : ConvexSpaceBody E)
    (u : unitary (E →L[ℝ] E)) (v : E) :
    volume (K.mapAffine (rigidAffineEquiv u v)).carrier = volume K.carrier := by
  rw [ConvexSpaceBody.volume_mapAffine]
  rw [affineJacobian_rigidAffineEquiv]
  simp

theorem volumeReal_mapAffine_rigidAffineEquiv (K : ConvexSpaceBody E)
    (u : unitary (E →L[ℝ] E)) (v : E) :
    volume.real (K.mapAffine (rigidAffineEquiv u v)).carrier = volume.real K.carrier := by
  rw [measureReal_def, measureReal_def]
  exact congrArg ENNReal.toReal (volume_mapAffine_rigidAffineEquiv K u v)

variable {δ : NNReal}

omit [MeasurableSpace E] [BorelSpace E] in
/-- The moved tube is the affine transport of the tube. -/
theorem rigidMove_toConvexSpaceBody (T : Tube δ E) (u : unitary (E →L[ℝ] E)) (v : E) :
    (T.rigidMove u v).toConvexSpaceBody
      = T.toConvexSpaceBody.mapAffine (rigidAffineEquiv u v) := by
  apply ConvexSpaceBody.ext
  change (T.rigidMove u v).carrier = (T.toConvexSpaceBody.mapAffine (rigidAffineEquiv u v)).carrier
  rw [Tube.rigidMove_carrier, ConvexSpaceBody.mapAffine_carrier]
  change Kakeya.rigidMap u v '' T.carrier = (rigidAffineEquiv u v : E → E) '' T.carrier
  rw [← rigidAffineEquiv_coe u v]

omit [MeasurableSpace E] [BorelSpace E] in
/-- **`R(T) ⊆ K` is `T ⊆ R⁻¹(K)`.** -/
theorem rigidMove_le_iff_le_mapAffine_symm (T : Tube δ E) (K : ConvexSpaceBody E)
    (u : unitary (E →L[ℝ] E)) (v : E) :
    (T.rigidMove u v).toConvexSpaceBody ≤ K
      ↔ T.toConvexSpaceBody ≤ K.mapAffine (rigidAffineEquiv u v).symm := by
  rw [rigidMove_toConvexSpaceBody]
  constructor
  · intro h
    exact (ConvexSpaceBody.mapAffine_le_mapAffine_iff (f := rigidAffineEquiv u v)).mp
      (by simpa [ConvexSpaceBody.symm_mapAffine_mapAffine] using h)
  · intro h
    simpa [ConvexSpaceBody.symm_mapAffine_mapAffine] using
      (ConvexSpaceBody.mapAffine_le_mapAffine_iff (f := rigidAffineEquiv u v)).mpr h

theorem volume_mapAffine_rigidAffineEquiv_symm (K : ConvexSpaceBody E)
    (u : unitary (E →L[ℝ] E)) (v : E) :
    volume (K.mapAffine (rigidAffineEquiv u v).symm).carrier = volume K.carrier := by
  have h := volume_mapAffine_rigidAffineEquiv (K.mapAffine (rigidAffineEquiv u v).symm) u v
  rw [ConvexSpaceBody.symm_mapAffine_mapAffine (K := K) (f := rigidAffineEquiv u v)] at h
  exact h.symm

theorem volumeReal_mapAffine_rigidAffineEquiv_symm (K : ConvexSpaceBody E)
    (u : unitary (E →L[ℝ] E)) (v : E) :
    volume.real (K.mapAffine (rigidAffineEquiv u v).symm).carrier = volume.real K.carrier := by
  simpa [Measure.real] using
    congrArg ENNReal.toReal (volume_mapAffine_rigidAffineEquiv_symm K u v)

/-- **The deterministic Frostman packing cap for one rigid copy.**

This is the rigid-motion analogue of
`Kakeya.HasUniformTranslation.tubeContainedCount_le_ED_packing`:
for *every* rigid motion `ω` and *every* convex test body `K`,

`rigidCountIn s T K ω · (c_vol · |B₁|) ≤ C_F · M_vol · |s| · |K|`,

with the Frostman constant of the *original* family. It is what supplies the deterministic bound
`hXM` required by `Kakeya.rigidCountIn_chernoff_tail`. -/
theorem rigidCountIn_le_frostman_packing [Nontrivial E] (hδ_pos : (0 : ℝ) < (δ : ℝ))
    {ι : Type*} (s : Finset ι) (T : ι → ShadedTube δ E)
    (CF : ℝ) (hCF_nn : 0 ≤ CF)
    (hFrost : ConvexSpaceBody.IsFrostmanIn s (fun i => (T i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall (ENNReal.ofReal CF))
    (hT_in_B1 : ∀ i ∈ s, (T i).toConvexSpaceBody ≤ ConvexSpaceBody.closedUnitBall)
    (c_vol M_vol : ℝ) (hc_vol_pos : 0 < c_vol) (hM_vol_nn : 0 ≤ M_vol)
    (hT_vol_lb :
      ∀ i ∈ s, c_vol * (δ : ℝ) ^ (Module.finrank ℝ E - 1) ≤ volume.real (T i).carrier)
    (hT_vol_ub :
      ∀ i ∈ s, volume.real (T i).carrier ≤ M_vol * (δ : ℝ) ^ (Module.finrank ℝ E - 1))
    (K : ConvexSpaceBody E) (ω : unitary (E →L[ℝ] E) × E) :
    ((rigidCountIn s (fun i => (T i).toTube) K ω : ℕ) : ℝ) *
        (c_vol * volume.real (ConvexSpaceBody.closedUnitBall (E := E)).carrier) ≤
      CF * M_vol * (s.card : ℝ) * volume.real K.carrier := by
  classical
  set K' : ConvexSpaceBody E := K.mapAffine (rigidAffineEquiv ω.1 ω.2).symm with hK'
  have hcount :
      rigidCountIn s (fun i => (T i).toTube) K ω
        = (@Finset.filter ι (fun i => (T i).toConvexSpaceBody ≤ K')
            (Classical.decPred _) s).card := by
    rw [rigidCountIn]
    congr 1
    apply Finset.filter_congr
    intro i hi
    change ((T i).rigidMove ω.1 ω.2).toConvexSpaceBody ≤ K ↔ (T i).toConvexSpaceBody ≤ K'
    rw [rigidMove_le_iff_le_mapAffine_symm (T := (T i).toTube) (K := K) (u := ω.1) (v := ω.2)]
  have hmain := ConvexSpaceBody.IsFrostmanIn.card_le_of_subset
    (E := E) (δ := δ) hδ_pos s
    (fun i => (T i).toConvexSpaceBody) CF hCF_nn hFrost hT_in_B1
    c_vol M_vol hc_vol_pos hM_vol_nn hT_vol_lb hT_vol_ub K'
  have hvol : volume.real K'.carrier = volume.real K.carrier := by
    rw [hK']
    exact volumeReal_mapAffine_rigidAffineEquiv_symm K ω.1 ω.2
  rw [hcount]
  simpa [hvol] using hmain

end

end Kakeya

end
