module

public import Kakeya.Factoring.FlatPrisms
public import Kakeya.DimensionThree.Slab.Multiplicity

@[expose] public section

open MeasureTheory ConvexSpaceBody Metric
open scoped NNReal ENNReal Real

namespace Kakeya

noncomputable section

/-- The exact plank representative of a body whose affine dimensions are only
comparable to `a x b x 1`.  The original body is contained in the `Cw`-dilation
of the representative; this keeps the actual hull and the exact prism separate. -/
structure RepresentativePlankGeometry (Cw a b : NNReal) (hab : a ≤ b) (hb1 : b ≤ 1)
    (K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) where
  plank : Plank a b hab hb1
  body_subset_dilation :
    (K.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
      (plank.toPrismNDim.dilation Cw).carrier
  dilation_volume_le :
    volume ((plank.toPrismNDim.dilation Cw).carrier : Set (EuclideanSpace ℝ (Fin 3))) ≤
      (Prism3D.enclosureVolumeConstant Cw : ENNReal) * volume K.carrier
  dilation_window :
    ((plank.toPrismNDim.dilation Cw).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
      Metric.closedBall 0 ((1 + 6 * Cw : NNReal) : ℝ)

/-- Convert the `ENNReal` affine-thickness formulation used by
`IsPlankOfDimensions` to the real-valued `HasThicknesses` enclosure API. -/
theorem hasThicknesses_of_isPlankOfDimensions {Cw a b : NNReal} (hCw : 1 ≤ Cw)
    (K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
    (hK : IsPlankOfDimensions Cw a b K) :
    HasThicknesses K.carrier Cw ![(1 : ℝ), (b : ℝ), (a : ℝ)] := by
  have hbdd : Bornology.IsBounded K.carrier := K.isCompact.isBounded
  have hCw0 : Cw ≠ 0 := ne_of_gt (zero_lt_one.trans_le hCw)
  have hCwE0 : (Cw : ENNReal) ≠ 0 := by exact_mod_cast hCw0
  have hCwEtop : (Cw : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  intro k
  fin_cases k
  · constructor
    · have h := hK.1.1
      rw [Metric.ethickness_thickness' hbdd 0] at h
      have h' := ENNReal.toReal_le_toReal
        (by simp [hCwE0, hCwEtop] : (Cw : ENNReal)⁻¹ ≠ ⊤)
        (by simp : ENNReal.ofReal (Metric.thickness ℝ K.carrier 0) ≠ ⊤) |>.mpr h
      rw [ENNReal.toReal_ofReal (Metric.thickness_nonneg K.carrier 0)] at h'
      simpa [hCw0] using h'
    · have h := hK.1.2
      rw [Metric.ethickness_thickness' hbdd 0] at h
      have h' := ENNReal.toReal_le_toReal
        (by simp : ENNReal.ofReal (Metric.thickness ℝ K.carrier 0) ≠ ⊤)
        ENNReal.coe_ne_top |>.mpr h
      rw [ENNReal.toReal_ofReal (Metric.thickness_nonneg K.carrier 0)] at h'
      simpa using h'
  · constructor
    · have h := hK.2.1.1
      rw [Metric.ethickness_thickness' hbdd 1] at h
      have h' := ENNReal.toReal_le_toReal
        (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hCwE0) ENNReal.coe_ne_top)
        (by simp : ENNReal.ofReal (Metric.thickness ℝ K.carrier 1) ≠ ⊤) |>.mpr h
      rw [ENNReal.toReal_ofReal (Metric.thickness_nonneg K.carrier 1)] at h'
      simpa [hCw0] using h'
    · have h := hK.2.1.2
      rw [Metric.ethickness_thickness' hbdd 1] at h
      have h' := ENNReal.toReal_le_toReal
        (by simp : ENNReal.ofReal (Metric.thickness ℝ K.carrier 1) ≠ ⊤)
        (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top) |>.mpr h
      rw [ENNReal.toReal_ofReal (Metric.thickness_nonneg K.carrier 1)] at h'
      simpa using h'
  · constructor
    · have h := hK.2.2.1
      rw [Metric.ethickness_thickness' hbdd 2] at h
      have h' := ENNReal.toReal_le_toReal
        (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hCwE0) ENNReal.coe_ne_top)
        (by simp : ENNReal.ofReal (Metric.thickness ℝ K.carrier 2) ≠ ⊤) |>.mpr h
      rw [ENNReal.toReal_ofReal (Metric.thickness_nonneg K.carrier 2)] at h'
      simpa [hCw0] using h'
    · have h := hK.2.2.2
      rw [Metric.ethickness_thickness' hbdd 2] at h
      have h' := ENNReal.toReal_le_toReal
        (by simp : ENNReal.ofReal (Metric.thickness ℝ K.carrier 2) ≠ ⊤)
        (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top) |>.mpr h
      rw [ENNReal.toReal_ofReal (Metric.thickness_nonneg K.carrier 2)] at h'
      simpa using h'

/-- A source-faithful comparable plank body has an exact `a x b x 1`
representative whose `Cw`-dilation contains the body, with controlled volume and
a common fixed-multiple window. -/
theorem exists_representativePlankGeometry {Cw a b : NNReal} (hCw : 1 ≤ Cw)
    (hab : a ≤ b) (hb1 : b ≤ 1)
    (K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
    (hK1 : K.carrier ⊆ Metric.closedBall 0 1)
    (hK : IsPlankOfDimensions Cw a b K) :
    Nonempty (RepresentativePlankGeometry Cw a b hab hb1 K) := by
  have hCaCb : Cw * a ≤ Cw * b := mul_le_mul_left' hab Cw
  have hCbC : Cw * b ≤ Cw := by
    simpa only [mul_one] using mul_le_mul_left' hb1 Cw
  have ht : HasThicknesses K.carrier Cw ![(1 : ℝ), (b : ℝ), (a : ℝ)] :=
    hasThicknesses_of_isPlankOfDimensions hCw K hK
  obtain ⟨Q, hKQ, hvolQ⟩ :=
    Prism3D.exists_superset_volume_le_of_hasThicknesses hCw
      (A := Cw * a) (B := Cw * b) (C := Cw) (hAB := hCaCb) (hBC := hCbC)
      K ht (by norm_num) (by norm_num) (by norm_num)
  let P : Plank a b hab hb1 :=
    { toPrismNDim := Q.toPrismNDim.resize ![a, b, (1 : NNReal)]
      thicknesses_eq := by simp }
  have hcarrier :
      ((P.toPrismNDim.dilation Cw).carrier : Set (EuclideanSpace ℝ (Fin 3))) = Q.carrier := by
    ext x
    rw [PrismNDim.dilation_eq_resize, PrismNDim.mem_resize_carrier]
    rw [Q.mem_carrier_iff]
    constructor <;> intro hx i
    · have hi := hx i
      fin_cases i <;> simpa [P, Q.thicknesses_eq] using hi
    · have hi := hx i
      fin_cases i <;> simpa [P, Q.thicknesses_eq] using hi
  let G : RepresentativePlankGeometry Cw a b hab hb1 K :=
    { plank := P
      body_subset_dilation := by simpa only [hcarrier] using hKQ
      dilation_volume_le := by simpa only [hcarrier] using hvolQ
      dilation_window := by
        rw [hcarrier]
        obtain ⟨z, hzK⟩ := K.nonempty
        have hzQ : z ∈ Q.carrier := hKQ hzK
        intro y hyQ
        have hz1 : ‖z‖ ≤ 1 := by
          simpa [Metric.mem_closedBall, dist_eq_norm] using hK1 hzK
        have hyz : ‖y - z‖ ≤
            2 * (((Cw * a : NNReal) : ℝ) + (Cw * b : NNReal) + Cw) :=
          Q.norm_sub_le_of_mem hzQ hyQ
        have ha1 : (a : ℝ) ≤ 1 := by exact_mod_cast hab.trans hb1
        have hb1r : (b : ℝ) ≤ 1 := by exact_mod_cast hb1
        have hC0 : (0 : ℝ) ≤ Cw := NNReal.coe_nonneg Cw
        have hdist : ‖y - z‖ ≤ 6 * (Cw : ℝ) := by
          calc
            ‖y - z‖ ≤ 2 * (((Cw * a : NNReal) : ℝ) + (Cw * b : NNReal) + Cw) := hyz
            _ ≤ 6 * (Cw : ℝ) := by
              push_cast
              nlinarith [mul_le_mul_of_nonneg_left ha1 hC0,
                mul_le_mul_of_nonneg_left hb1r hC0]
        rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
        calc
          ‖y‖ = ‖(y - z) + z‖ := by congr 1; abel
          _ ≤ ‖y - z‖ + ‖z‖ := norm_add_le _ _
          _ ≤ 6 * (Cw : ℝ) + 1 := add_le_add hdist hz1
          _ = ((1 + 6 * Cw : NNReal) : ℝ) := by push_cast; ring }
  exact ⟨G⟩

end

end Kakeya
