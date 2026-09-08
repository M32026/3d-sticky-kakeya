import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.TubeReversal
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.BackwardConflict
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.GeneralizedCellPack
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.Reanchoring
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.WeightedGraphSelection

/-!
# Paper-distinct selection after localized coaxial reanchoring

Coaxial reanchoring forgets the original longitudinal tube positions, so
streamlined essential distinctness does not pass directly to the reanchored
family.  This file proves the required replacement:

* a paper-containment conflict between two reanchored tubes puts their
  directions and transverse midpoints in an `O(delta)` parameter box;
* the original source midpoints differ from the reanchored midpoints by
  uniformly bounded axial shifts;
* five-dimensional capsule packing therefore gives an absolute conflict
  degree;
* weighted greedy selection retains a fixed fraction of arbitrary tube
  weights and makes the reanchored family paper-essentially-distinct.
-/

noncomputable section

namespace Kakeya.Assouad

open Kakeya.Streamlined
open Kakeya.Streamlined.GeometricLemmas
open MeasureTheory

attribute [local instance] Classical.propDecidable

private def pureWZ2ReanchoredPaperConflict
    {delta : ℝ}
    (family : Kakeya.Streamlined.TubeFamily delta)
    (fixed other : Fin family.card) : Prop :=
  other ≠ fixed ∧
    ((family.tube other).carrier ⊆
        wz2PaperCenteredDilatedCarrier 2 (family.tube fixed) ∨
      (family.tube fixed).carrier ⊆
        wz2PaperCenteredDilatedCarrier 2 (family.tube other))

private def pureWZ2CenteredFrame
    (linear : Point3 ≃ₗᵢ[ℝ] Point3) (center : Point3) :
    Point3 ≃ᵃⁱ[ℝ] Point3 where
  toFun point := linear point + center
  invFun point := linear.symm (point - center)
  left_inv point := by
    simp
  right_inv point := by
    simp
  linear := linear
  map_vadd' vector point := by
    simp [vadd_eq_add]
    abel
  norm_map vector := linear.norm_map vector

@[simp] private theorem pureWZ2CenteredFrame_symm_apply
    (linear : Point3 ≃ₗᵢ[ℝ] Point3) (center point : Point3) :
    (pureWZ2CenteredFrame linear center).symm point =
      linear.symm (point - center) :=
  rfl

private theorem pureWZ2CenteredFrame_symm_add_smul
    (linear : Point3 ≃ₗᵢ[ℝ] Point3) (center point vector : Point3)
    (scalar : ℝ) :
    (pureWZ2CenteredFrame linear center).symm
        (point + scalar • vector) =
      (pureWZ2CenteredFrame linear center).symm point +
        scalar • linear.symm vector := by
  simp only [pureWZ2CenteredFrame_symm_apply]
  rw [show point + scalar • vector - center =
    (point - center) + scalar • vector by abel,
    linear.symm.map_add, linear.symm.map_smul]

private theorem pureWZ2_source_midpoint_eq
    {delta : ℝ}
    {source reanchored : Kakeya.DeltaTube delta}
    {shift : ℝ}
    (hdirection : reanchored.direction = source.direction)
    (hbase :
      source.base =
        reanchored.base + shift • reanchored.direction) :
    wz2PaperTubeMidpoint source =
      wz2PaperTubeMidpoint reanchored +
        shift • reanchored.direction := by
  simp only [wz2PaperTubeMidpoint]
  rw [hbase, ← hdirection]
  abel

private theorem pureWZ2_abs_coordinate_le_one
    (vector : Point3) (hunit : ‖vector‖ = 1)
    (coordinate : Fin 3) :
    |vector coordinate| ≤ 1 := by
  have hsum :
      ‖vector‖ ^ 2 =
        ∑ index : Fin 3, (vector index) ^ 2 :=
    EuclideanSpace.real_norm_sq_eq vector
  have hcoordinate :
      (vector coordinate) ^ 2 ≤ ‖vector‖ ^ 2 := by
    rw [hsum]
    exact
      Finset.single_le_sum
        (fun index _ => sq_nonneg (vector index))
        (Finset.mem_univ coordinate)
  rw [hunit] at hcoordinate
  nlinarith [sq_abs (vector coordinate), abs_nonneg (vector coordinate)]

private theorem pureWZ2_source_parameter_bounds
    {delta : ℝ}
    (hdelta : 0 < delta)
    {n : ℕ}
    (reanchoredMidpoint sourceMidpoint transformedDirection :
      Fin n → Point3)
    (axialShift : Fin n → ℝ)
    (source_midpoint_eq :
      ∀ index,
        sourceMidpoint index =
          reanchoredMidpoint index +
            axialShift index • transformedDirection index)
    (axialShift_bound :
      ∀ index, |axialShift index| ≤ 1)
    (direction_unit :
      ∀ index, ‖transformedDirection index‖ = 1)
    (indices : Finset (Fin n))
    (reanchored_bounds :
      ∀ index ∈ indices,
        |transformedDirection index 0| ≤ 8 * delta ∧
        |transformedDirection index 1| ≤ 8 * delta ∧
        (transformedDirection index 2 ≥ 1 / 2 ∨
          transformedDirection index 2 ≤ -1 / 2) ∧
        |reanchoredMidpoint index 0| ≤ 10 * delta ∧
        |reanchoredMidpoint index 1| ≤ 10 * delta ∧
        |reanchoredMidpoint index 2| ≤ 2) :
    ∀ index ∈ indices,
      |transformedDirection index 0| ≤ 10 * delta ∧
      |transformedDirection index 1| ≤ 10 * delta ∧
      (transformedDirection index 2 ≥ 1 / 2 ∨
        transformedDirection index 2 ≤ -1 / 2) ∧
      |sourceMidpoint index 0| ≤ 18 * delta ∧
      |sourceMidpoint index 1| ≤ 18 * delta ∧
      |sourceMidpoint index 2| ≤ 3 := by
  intro index hindex
  have h := reanchored_bounds index hindex
  have hcoordinate :
      ∀ coordinate,
        |transformedDirection index coordinate| ≤ 1 :=
    fun coordinate =>
      pureWZ2_abs_coordinate_le_one
        (transformedDirection index) (direction_unit index) coordinate
  have hzero :
      |sourceMidpoint index 0| ≤ 18 * delta := by
    rw [source_midpoint_eq index]
    calc
      |(reanchoredMidpoint index +
            axialShift index • transformedDirection index) 0|
          ≤ |reanchoredMidpoint index 0| +
              |axialShift index| *
                |transformedDirection index 0| := by
            simpa [Pi.add_apply, Pi.smul_apply, abs_mul] using
              abs_add_le
                (reanchoredMidpoint index 0)
                (axialShift index * transformedDirection index 0)
      _ ≤ 10 * delta + 1 * (8 * delta) := by
            exact
              add_le_add h.2.2.2.1
                (mul_le_mul
                  (axialShift_bound index) h.1
                  (abs_nonneg _) (by norm_num))
      _ = 18 * delta := by ring
  have hone :
      |sourceMidpoint index 1| ≤ 18 * delta := by
    rw [source_midpoint_eq index]
    calc
      |(reanchoredMidpoint index +
            axialShift index • transformedDirection index) 1|
          ≤ |reanchoredMidpoint index 1| +
              |axialShift index| *
                |transformedDirection index 1| := by
            simpa [Pi.add_apply, Pi.smul_apply, abs_mul] using
              abs_add_le
                (reanchoredMidpoint index 1)
                (axialShift index * transformedDirection index 1)
      _ ≤ 10 * delta + 1 * (8 * delta) := by
            exact
              add_le_add h.2.2.2.2.1
                (mul_le_mul
                  (axialShift_bound index) h.2.1
                  (abs_nonneg _) (by norm_num))
      _ = 18 * delta := by ring
  have htwo :
      |sourceMidpoint index 2| ≤ 3 := by
    rw [source_midpoint_eq index]
    calc
      |(reanchoredMidpoint index +
            axialShift index • transformedDirection index) 2|
          ≤ |reanchoredMidpoint index 2| +
              |axialShift index| *
                |transformedDirection index 2| := by
            simpa [Pi.add_apply, Pi.smul_apply, abs_mul] using
              abs_add_le
                (reanchoredMidpoint index 2)
                (axialShift index * transformedDirection index 2)
      _ ≤ 2 + 1 * 1 := by
            exact
              add_le_add h.2.2.2.2.2
                (mul_le_mul
                  (axialShift_bound index) (hcoordinate 2)
                  (abs_nonneg _) (by norm_num))
      _ = 3 := by norm_num
  exact
    ⟨by linarith [h.1], by linarith [h.2.1],
      h.2.2.1, hzero, hone, htwo⟩

private theorem pureWZ2_parameter_pack
    {delta : ℝ}
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 200)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (family_distinct : family.IsEssentiallyDistinct)
    (indices : Finset (Fin family.card))
    (frame : Point3 ≃ᵃⁱ[ℝ] Point3)
    (midpoint direction : Fin family.card → Point3)
    (midpoint_eq :
      ∀ index,
        midpoint index =
          frame.symm (wz2PaperTubeMidpoint (family.tube index)))
    (direction_eq :
      ∀ index,
        direction index =
          frame.symm.linearIsometryEquiv
            (family.tube index).direction)
    (parameter_bounds :
      ∀ index ∈ indices,
        |direction index 0| ≤ 10 * delta ∧
        |direction index 1| ≤ 10 * delta ∧
        (direction index 2 ≥ 1 / 2 ∨
          direction index 2 ≤ -1 / 2) ∧
        |midpoint index 0| ≤ 18 * delta ∧
        |midpoint index 1| ≤ 18 * delta ∧
        |midpoint index 2| ≤ 3) :
    indices.card ≤
      2 * 4001 ^ 2 *
        (2 * Nat.ceil (200 * 18 * 1 : ℝ) + 1) ^ 2 *
        (2 * Nat.ceil (6400 * 3 * 1 : ℝ) + 1) := by
  have hpacking :=
    generalized_cell_pack
      hdelta (show (1 : ℝ) ≤ 1 by norm_num)
      (by simpa using hdeltaSmall)
      18 3 (by norm_num) (by norm_num)
      indices frame midpoint direction
      midpoint_eq direction_eq
      (fun index hindex =>
        ⟨(parameter_bounds index hindex).1,
          (parameter_bounds index hindex).2.1⟩)
      (fun index hindex =>
        (parameter_bounds index hindex).2.2.1)
      (fun index hindex =>
        ⟨by
          simpa only [mul_one] using
            (parameter_bounds index hindex).2.2.2.1,
          by
            simpa only [mul_one] using
              (parameter_bounds index hindex).2.2.2.2.1⟩)
      (fun index hindex => by
        simpa only [mul_one] using
          (parameter_bounds index hindex).2.2.2.2.2)
      (by
        intro first second _ _ hne
        exact family_distinct first second hne)
  exact hpacking

/-- A coarse absolute upper bound for the localized reanchoring degree. -/
def pureWZ2ReanchoredPaperConflictLossBound : ℕ := 10 ^ 40

/--
Every paper-conflict neighborhood in a bounded coaxially reanchored copy of
an essentially-distinct source family has absolute cardinality.
-/
theorem pureWZ2_reanchored_paper_conflict_degree
    {delta : ℝ}
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 200)
    {source reanchored : Kakeya.Streamlined.TubeFamily delta}
    (sourceIndex : Fin reanchored.card ↪ Fin source.card)
    (axialShift : Fin reanchored.card → ℝ)
    (direction_eq :
      ∀ index,
        (reanchored.tube index).direction =
          (source.tube (sourceIndex index)).direction)
    (source_base_eq :
      ∀ index,
        (source.tube (sourceIndex index)).base =
          (reanchored.tube index).base +
            axialShift index • (reanchored.tube index).direction)
    (axialShift_bound :
      ∀ index, |axialShift index| ≤ 1)
    (source_distinct : source.IsEssentiallyDistinct) :
    ∃ degree : ℕ,
      degree + 1 ≤ pureWZ2ReanchoredPaperConflictLossBound ∧
      ∀ fixed : Fin reanchored.card,
        (Finset.univ.filter
          (pureWZ2ReanchoredPaperConflict reanchored fixed)).card ≤
          degree := by
  let degree : ℕ :=
    2 * 4001 ^ 2 *
      (2 * Nat.ceil (200 * 18 * 1 : ℝ) + 1) ^ 2 *
      (2 * Nat.ceil (6400 * 3 * 1 : ℝ) + 1)
  refine ⟨degree, ?_, ?_⟩
  · norm_num [degree, pureWZ2ReanchoredPaperConflictLossBound,
      Nat.ceil_ofNat]
  intro fixed
  let conflicts : Finset (Fin reanchored.card) :=
    Finset.univ.filter
      (pureWZ2ReanchoredPaperConflict reanchored fixed)
  let sourceCopy : Kakeya.Streamlined.TubeFamily delta :=
    { card := reanchored.card
      tube := fun index => source.tube (sourceIndex index) }
  have sourceCopy_distinct : sourceCopy.IsEssentiallyDistinct := by
    intro first second hne
    exact
      source_distinct
        (sourceIndex first) (sourceIndex second)
        (fun heq => hne (sourceIndex.injective heq))
  let reference := reanchored.tube fixed
  rcases frame_of_axis reference.direction reference.direction_unit with
    ⟨_, _, rawFrame, haxisTwo, haxisZero, haxisOne⟩
  let linear := rawFrame.linearIsometryEquiv
  let center := wz2PaperTubeMidpoint reference
  let frame := pureWZ2CenteredFrame linear center
  let sourceMidpoint (index : Fin reanchored.card) : Point3 :=
    frame.symm (wz2PaperTubeMidpoint (sourceCopy.tube index))
  let reanchoredMidpoint (index : Fin reanchored.card) : Point3 :=
    frame.symm (wz2PaperTubeMidpoint (reanchored.tube index))
  let transformedDirection (index : Fin reanchored.card) : Point3 :=
    frame.symm.linearIsometryEquiv (sourceCopy.tube index).direction
  let referenceBase := frame.symm reference.base
  have hreferenceDirection :
      frame.symm.linearIsometryEquiv reference.direction =
        EuclideanSpace.single 2 1 := by
    change rawFrame.symm.linearIsometryEquiv reference.direction =
      EuclideanSpace.single 2 1
    ext coordinate
    fin_cases coordinate
    · simpa [EuclideanSpace.single] using haxisZero
    · simpa [EuclideanSpace.single] using haxisOne
    · simpa [EuclideanSpace.single] using haxisTwo
  have hreferenceBase :
      referenceBase =
        -(1 / 2 : ℝ) • EuclideanSpace.single 2 1 := by
    have hmidpoint :
        reference.base =
          center - (1 / 2 : ℝ) • reference.direction := by
      simp [center, wz2PaperTubeMidpoint]
    dsimp only [referenceBase, frame]
    rw [hmidpoint, pureWZ2CenteredFrame_symm_apply]
    simp only [sub_sub_cancel_left]
    rw [← neg_smul, linear.symm.map_smul]
    change
      -(1 / 2 : ℝ) •
          rawFrame.symm.linearIsometryEquiv reference.direction =
        _
    have hrawDirection :
        rawFrame.symm.linearIsometryEquiv reference.direction =
          EuclideanSpace.single 2 1 := by
      exact hreferenceDirection
    rw [hrawDirection]
  have hsourceMidpoint :
      ∀ index,
        sourceMidpoint index =
          reanchoredMidpoint index +
            axialShift index • transformedDirection index := by
    intro index
    have hmid :=
      pureWZ2_source_midpoint_eq
        (direction_eq index)
        (source_base_eq index)
    dsimp only [sourceMidpoint, reanchoredMidpoint,
      transformedDirection, sourceCopy]
    rw [hmid, pureWZ2CenteredFrame_symm_add_smul]
    change
      frame.symm (wz2PaperTubeMidpoint (reanchored.tube index)) +
          axialShift index •
            linear.symm (reanchored.tube index).direction =
        frame.symm (wz2PaperTubeMidpoint (reanchored.tube index)) +
          axialShift index •
            linear.symm (source.tube (sourceIndex index)).direction
    rw [← direction_eq index]
  have hparameters :
      ∀ index ∈ conflicts,
        |transformedDirection index 0| ≤ 8 * delta ∧
        |transformedDirection index 1| ≤ 8 * delta ∧
        (transformedDirection index 2 ≥ 1 / 2 ∨
          transformedDirection index 2 ≤ -1 / 2) ∧
        |reanchoredMidpoint index 0| ≤ 10 * delta ∧
        |reanchoredMidpoint index 1| ≤ 10 * delta ∧
        |reanchoredMidpoint index 2| ≤ 2 := by
    intro index hindex
    have hconflict :=
      (Finset.mem_filter.mp hindex).2.2
    let sourceBase := frame.symm (reanchored.tube index).base
    have hdirection :
        transformedDirection index =
          frame.symm.linearIsometryEquiv
            (reanchored.tube index).direction := by
      dsimp only [transformedDirection, sourceCopy]
      rw [direction_eq index]
    have hmidpoint :
        reanchoredMidpoint index =
          sourceBase +
            (1 / 2 : ℝ) • transformedDirection index := by
      dsimp only [reanchoredMidpoint, sourceBase]
      rw [wz2PaperTubeMidpoint,
        pureWZ2CenteredFrame_symm_add_smul]
      change
        frame.symm (reanchored.tube index).base +
            (1 / 2 : ℝ) •
              linear.symm (reanchored.tube index).direction =
          frame.symm (reanchored.tube index).base +
            (1 / 2 : ℝ) • transformedDirection index
      have hlinear :
          linear.symm (reanchored.tube index).direction =
            transformedDirection index := by
        exact hdirection.symm
      rw [hlinear]
    have hreferenceBaseDef :
        referenceBase = frame.symm reference.base := rfl
    have hraw :
        |transformedDirection index 0| ≤ 8 * delta ∧
        |transformedDirection index 1| ≤ 8 * delta ∧
        (transformedDirection index 2 ≥ 1 / 2 ∨
          transformedDirection index 2 ≤ -1 / 2) ∧
        |(reanchoredMidpoint index - referenceBase) 0| ≤
          10 * delta ∧
        |(reanchoredMidpoint index - referenceBase) 1| ≤
          10 * delta ∧
        -1 / 2 - 2 * delta ≤
          (reanchoredMidpoint index - referenceBase) 2 ∧
        (reanchoredMidpoint index - referenceBase) 2 ≤
          3 / 2 + 2 * delta := by
      rcases hconflict with hforward | hbackward
      · have h :=
          conflict_geometric_bounds
            hdelta (by linarith)
            frame referenceBase
            (frame.symm.linearIsometryEquiv reference.direction)
            sourceBase (transformedDirection index)
            (reanchoredMidpoint index)
            hreferenceBaseDef rfl
            (by simpa [hreferenceDirection, EuclideanSpace.single])
            (by simpa [hreferenceDirection, EuclideanSpace.single])
            (by simpa [hreferenceDirection, EuclideanSpace.single])
            rfl hdirection hmidpoint hforward
        exact
          ⟨by linarith [h.1], by linarith [h.2.1],
            h.2.2.1, by linarith [h.2.2.2.1],
            by linarith [h.2.2.2.2.1],
            h.2.2.2.2.2⟩
      · exact
          backward_conflict_geometric_bounds
            hdelta (by linarith)
            frame referenceBase
            (frame.symm.linearIsometryEquiv reference.direction)
            sourceBase (transformedDirection index)
            (reanchoredMidpoint index)
            hreferenceBaseDef rfl
            (by simpa [hreferenceDirection, EuclideanSpace.single])
            (by simpa [hreferenceDirection, EuclideanSpace.single])
            (by simpa [hreferenceDirection, EuclideanSpace.single])
            rfl hdirection hmidpoint hbackward
    have hreferenceBaseZero :
        referenceBase 0 = 0 := by
      rw [hreferenceBase]
      simp [EuclideanSpace.single, Pi.smul_apply]
    have hreferenceBaseOne :
        referenceBase 1 = 0 := by
      rw [hreferenceBase]
      simp [EuclideanSpace.single, Pi.smul_apply]
    have hreferenceBaseTwo :
        referenceBase 2 = -1 / 2 := by
      rw [hreferenceBase]
      norm_num [EuclideanSpace.single, Pi.smul_apply]
    have hmidZero :
        |reanchoredMidpoint index 0| ≤ 10 * delta := by
      simpa [Pi.sub_apply, hreferenceBaseZero] using hraw.2.2.2.1
    have hmidOne :
        |reanchoredMidpoint index 1| ≤ 10 * delta := by
      simpa [Pi.sub_apply, hreferenceBaseOne] using hraw.2.2.2.2.1
    have hmidTwoLower :
        -1 - 2 * delta ≤ reanchoredMidpoint index 2 := by
      have := hraw.2.2.2.2.2.1
      have hcoordinate :
          (reanchoredMidpoint index - referenceBase) 2 =
            reanchoredMidpoint index 2 - referenceBase 2 := rfl
      rw [hcoordinate, hreferenceBaseTwo] at this
      linarith
    have hmidTwoUpper :
        reanchoredMidpoint index 2 ≤ 1 + 2 * delta := by
      have := hraw.2.2.2.2.2.2
      have hcoordinate :
          (reanchoredMidpoint index - referenceBase) 2 =
            reanchoredMidpoint index 2 - referenceBase 2 := rfl
      rw [hcoordinate, hreferenceBaseTwo] at this
      linarith
    have hmidTwo :
        |reanchoredMidpoint index 2| ≤ 2 := by
      rw [abs_le]
      constructor <;> linarith [hdeltaSmall]
    exact
      ⟨hraw.1, hraw.2.1, hraw.2.2.1,
        hmidZero, hmidOne, hmidTwo⟩
  have hsourceDirectionUnit :
      ∀ index, ‖transformedDirection index‖ = 1 := by
    intro index
    dsimp only [transformedDirection, sourceCopy, frame]
    exact
      (linear.symm.norm_map
        (source.tube (sourceIndex index)).direction).trans
        (source.tube (sourceIndex index)).direction_unit
  have hsourceParameters :=
    pureWZ2_source_parameter_bounds
      hdelta reanchoredMidpoint sourceMidpoint transformedDirection
      axialShift hsourceMidpoint axialShift_bound
      hsourceDirectionUnit conflicts hparameters
  exact pureWZ2_parameter_pack
      hdelta hdeltaSmall sourceCopy_distinct conflicts frame
      sourceMidpoint transformedDirection
      (fun _ => rfl) (fun _ => rfl) hsourceParameters

/--
Select a paper-essentially-distinct reanchored subfamily while retaining a
fixed fraction of arbitrary nonnegative tube weights.
-/
theorem pureWZ2_select_reanchored_paper_distinct_weighted
    {delta : ℝ}
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 200)
    {source reanchored : Kakeya.Streamlined.TubeFamily delta}
    (sourceIndex : Fin reanchored.card ↪ Fin source.card)
    (axialShift : Fin reanchored.card → ℝ)
    (direction_eq :
      ∀ index,
        (reanchored.tube index).direction =
          (source.tube (sourceIndex index)).direction)
    (source_base_eq :
      ∀ index,
        (source.tube (sourceIndex index)).base =
          (reanchored.tube index).base +
            axialShift index • (reanchored.tube index).direction)
    (axialShift_bound :
      ∀ index, |axialShift index| ≤ 1)
    (source_distinct : source.IsEssentiallyDistinct)
    (weight : Fin reanchored.card → ENNReal) :
    ∃ loss : ℕ,
      0 < loss ∧
      loss ≤ pureWZ2ReanchoredPaperConflictLossBound ∧
      ∃ selected : Finset (Fin reanchored.card),
      WZ2PaperOrdinaryIsEssentiallyDistinct
        (Kakeya.Streamlined.TubeSubfamily.fromFinset
          reanchored selected).family ∧
      (∑ index : Fin reanchored.card, weight index) ≤
        (loss : ENNReal) *
          ∑ index ∈ selected, weight index := by
  let conflict :=
    pureWZ2ReanchoredPaperConflict reanchored
  have hsymm :
      ∀ first second, conflict first second →
        conflict second first := by
    intro first second h
    exact ⟨h.1.symm, h.2.symm⟩
  have hirrefl :
      ∀ index, ¬ conflict index index := by
    intro index h
    exact h.1 rfl
  rcases
      pureWZ2_reanchored_paper_conflict_degree
        hdelta hdeltaSmall sourceIndex axialShift
        direction_eq source_base_eq axialShift_bound
        source_distinct with
    ⟨degree, hdegreeBound, hrawDegree⟩
  have hdegree :
      ∀ index,
        (Finset.univ.filter fun other =>
          conflict index other).card ≤ degree := by
    intro index
    have heq :
        (Finset.univ.filter fun other =>
          conflict index other) =
        Finset.univ.filter
          (pureWZ2ReanchoredPaperConflict reanchored index) := by
      rfl
    rw [heq]
    exact hrawDegree index
  rcases
      pureWZ2_greedy_independent_set_weighted
        (D := degree)
        (relation := conflict) (weight := weight)
        hsymm hirrefl (fun index => hdegree index) with
    ⟨selected, hindependent, hmass⟩
  refine ⟨degree + 1, by omega, hdegreeBound, selected, ?_, ?_⟩
  · intro first second hne
    let embedding :=
      (Kakeya.Streamlined.TubeSubfamily.fromFinset
        reanchored selected).embedding
    have hfirst : embedding first ∈ selected := by
      exact Finset.orderEmbOfFin_mem selected rfl first
    have hsecond : embedding second ∈ selected := by
      exact Finset.orderEmbOfFin_mem selected rfl second
    have hindices : embedding first ≠ embedding second :=
      fun heq => hne (embedding.injective heq)
    have hnot :=
      hindependent
        (embedding first) hfirst
        (embedding second) hsecond hindices
    simp only [conflict, hindices, true_and] at hnot
    have htubeFirst :
        (Kakeya.Streamlined.TubeSubfamily.fromFinset
          reanchored selected).family.tube first =
            reanchored.tube (embedding first) :=
      (Kakeya.Streamlined.TubeSubfamily.fromFinset
        reanchored selected).tube_eq first
    have htubeSecond :
        (Kakeya.Streamlined.TubeSubfamily.fromFinset
          reanchored selected).family.tube second =
            reanchored.tube (embedding second) :=
      (Kakeya.Streamlined.TubeSubfamily.fromFinset
        reanchored selected).tube_eq second
    rw [htubeFirst, htubeSecond]
    have hnotOr :
        ¬((reanchored.tube (embedding second)).carrier ⊆
              wz2PaperCenteredDilatedCarrier 2
                (reanchored.tube (embedding first)) ∨
          (reanchored.tube (embedding first)).carrier ⊆
              wz2PaperCenteredDilatedCarrier 2
                (reanchored.tube (embedding second))) := by
      intro hor
      exact hnot ⟨hindices.symm, hor⟩
    constructor
    · intro hforward
      exact hnotOr (Or.inr hforward)
    · intro hbackward
      exact hnotOr (Or.inl hbackward)
  · simpa [Nat.cast_add, Nat.cast_one] using hmass

end Kakeya.Assouad

end
