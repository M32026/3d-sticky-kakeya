/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.FrostmanTransfer
public import Kakeya.Multiplicity
public import Kakeya.Tube.Rigidity

@[expose] public section

/-!
# Full-level shaded-node transport for the estimate WZ middle branch

At the terminal level of a uniform hierarchy the leaf and node radii agree.  Rigidity therefore
identifies the carrier of every leaf with the carrier of its assigned node.  This permits an honest
shaded node family: the shade of a node is the union of the shades in its assignment class.
-/

open MeasureTheory ConvexSpaceBody ShadedBody

namespace Kakeya.ml1Boot.W44FullNode

noncomputable section

universe u

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [FiniteDimensional Real E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-- Local scale cast, kept independent of the downstream WZ normalization module. -/
def castFullNodeScale {a b : NNReal} (h : a = b) (T : ShadedTube a E) : ShadedTube b E :=
  h ▸ T

@[simp] theorem castFullNodeScale_carrier {a b : NNReal} (h : a = b)
    (T : ShadedTube a E) : (castFullNodeScale h T).carrier = T.carrier := by
  subst b
  rfl

@[simp] theorem castFullNodeScale_shade {a b : NNReal} (h : a = b)
    (T : ShadedTube a E) : (castFullNodeScale h T).shade = T.shade := by
  subst b
  rfl

/-- Before casting the terminal grid radius to `delta`, shade a full node by the union of the
shades of all leaves assigned to it. -/
noncomputable def rawFullNodeFamily {ι : Type*} {delta C : NNReal} {s : Finset ι}
    (V : ι -> ShadedTube delta E) {N : Nat}
    (U : _root_.Tube.UniformTubeSet s (fun i => (V i).toTube) N C) (j : ι) :
    ShadedTube (_root_.Tube.gridScale delta N N) E := by
  classical
  refine
    { toTube := U.cover.tube N j
      shade := ⋃ i ∈ _root_.Tube.coverClass s (U.cover.assign N) j, (V i).shade
      measurableSet_shade :=
        Finset.measurableSet_biUnion _ (fun i _ => (V i).measurableSet_shade)
      shade_subset := ?_ }
  intro x hx
  rw [Set.mem_iUnion₂] at hx
  obtain ⟨i, hi, hxi⟩ := hx
  have hi' := (_root_.Finset.mem_filter.mp hi)
  rw [← hi'.2]
  exact U.cover.le_tube_assign N le_rfl i hi'.1 ((V i).shade_subset hxi)

/-- The honest shaded family on the hierarchy's actual terminal node set. -/
noncomputable def fullNodeFamily {ι : Type*} {delta C : NNReal} {s : Finset ι}
    (V : ι -> ShadedTube delta E) {N : Nat} (hN : 0 < N)
    (U : _root_.Tube.UniformTubeSet s (fun i => (V i).toTube) N C) (j : ι) :
    ShadedTube delta E :=
  castFullNodeScale (_root_.Tube.gridScale_self delta hN) (rawFullNodeFamily V U j)

@[simp] theorem rawFullNodeFamily_carrier {ι : Type*} {delta C : NNReal} {s : Finset ι}
    (V : ι -> ShadedTube delta E) {N : Nat}
    (U : _root_.Tube.UniformTubeSet s (fun i => (V i).toTube) N C) (j : ι) :
    (rawFullNodeFamily V U j).carrier = (U.cover.tube N j).carrier := rfl

@[simp] theorem rawFullNodeFamily_shade {ι : Type*} {delta C : NNReal} {s : Finset ι}
    (V : ι -> ShadedTube delta E) {N : Nat}
    (U : _root_.Tube.UniformTubeSet s (fun i => (V i).toTube) N C) (j : ι) :
    (rawFullNodeFamily V U j).shade =
      ⋃ i ∈ _root_.Tube.coverClass s (U.cover.assign N) j, (V i).shade := rfl

@[simp] theorem fullNodeFamily_carrier {ι : Type*} {delta C : NNReal} {s : Finset ι}
    (V : ι -> ShadedTube delta E) {N : Nat} (hN : 0 < N)
    (U : _root_.Tube.UniformTubeSet s (fun i => (V i).toTube) N C) (j : ι) :
    (fullNodeFamily V hN U j).carrier = (U.cover.tube N j).carrier := by
  simp [fullNodeFamily]

@[simp] theorem fullNodeFamily_shade {ι : Type*} {delta C : NNReal} {s : Finset ι}
    (V : ι -> ShadedTube delta E) {N : Nat} (hN : 0 < N)
    (U : _root_.Tube.UniformTubeSet s (fun i => (V i).toTube) N C) (j : ι) :
    (fullNodeFamily V hN U j).shade =
      ⋃ i ∈ _root_.Tube.coverClass s (U.cover.assign N) j, (V i).shade := by
  simp [fullNodeFamily]

/-- At the terminal hierarchy level, every leaf carrier is exactly its assigned node carrier. -/
theorem leaf_carrier_eq_assigned_fullNode {ι : Type*} {delta C : NNReal} {s : Finset ι}
    (V : ι -> ShadedTube delta E) {N : Nat} (hN : 0 < N)
    (U : _root_.Tube.UniformTubeSet s (fun i => (V i).toTube) N C)
    {i : ι} (hi : i ∈ s) :
    (V i).carrier = (fullNodeFamily V hN U (U.cover.assign N i)).carrier := by
  rw [fullNodeFamily_carrier]
  exact _root_.Tube.carrier_eq_of_subset'
    (_root_.Tube.gridScale_self delta hN).symm (V i).toTube
      (U.cover.tube N (U.cover.assign N i))
      (U.cover.le_tube_assign N le_rfl i hi)

/-- The convex body of a leaf is exactly the convex body of its assigned full node. -/
theorem leaf_body_eq_assigned_fullNode {ι : Type*} {delta C : NNReal} {s : Finset ι}
    (V : ι -> ShadedTube delta E) {N : Nat} (hN : 0 < N)
    (U : _root_.Tube.UniformTubeSet s (fun i => (V i).toTube) N C)
    {i : ι} (hi : i ∈ s) :
    (V i).toConvexSpaceBody =
      (fullNodeFamily V hN U (U.cover.assign N i)).toConvexSpaceBody := by
  ext x
  exact Set.ext_iff.mp (leaf_carrier_eq_assigned_fullNode V hN U hi) x

/-- Aggregation changes neither the global shaded union nor its measure. -/
theorem iUnionShade_fullNodeFamily {ι : Type*} {delta C : NNReal} {s : Finset ι}
    (V : ι -> ShadedTube delta E) {N : Nat} (hN : 0 < N)
    (U : _root_.Tube.UniformTubeSet s (fun i => (V i).toTube) N C) :
    ShadedBody.iUnionShade (U.cover.indexSet N)
        (fun j => (fullNodeFamily V hN U j).toShadedBody) =
      ShadedBody.iUnionShade s (fun i => (V i).toShadedBody) := by
  classical
  ext x
  constructor
  · intro hx
    rw [Set.mem_iUnion₂] at hx
    obtain ⟨j, hj, hxj⟩ := hx
    change x ∈ (fullNodeFamily V hN U j).shade at hxj
    rw [fullNodeFamily_shade, Set.mem_iUnion₂] at hxj
    obtain ⟨i, hi, hxi⟩ := hxj
    exact Set.mem_iUnion₂.mpr ⟨i, (_root_.Finset.mem_filter.mp hi).1, hxi⟩
  · intro hx
    rw [Set.mem_iUnion₂] at hx
    obtain ⟨i, hi, hxi⟩ := hx
    refine Set.mem_iUnion₂.mpr ⟨U.cover.assign N i,
      U.cover.assign_mem N le_rfl i hi, ?_⟩
    change x ∈ (fullNodeFamily V hN U (U.cover.assign N i)).shade
    rw [fullNodeFamily_shade, Set.mem_iUnion₂]
    exact ⟨i, _root_.Finset.mem_filter.mpr ⟨hi, rfl⟩, hxi⟩

/-- The leaf cardinality is at most `C * branching * full-node cardinality`. -/
theorem leaf_card_le_balance_mul_branch_mul_fullNode_card
    {ι : Type*} {delta C : NNReal} {s : Finset ι}
    (V : ι -> ShadedTube delta E) {N : Nat}
    (U : _root_.Tube.UniformTubeSet s (fun i => (V i).toTube) N C) :
    (s.card : NNReal) <=
      C * U.branchingN N * ((U.cover.indexSet N).card : NNReal) := by
  classical
  rw [show (s.card : NNReal) =
      ∑ j ∈ U.cover.indexSet N,
        ((_root_.Tube.coverClass s (U.cover.assign N) j).card : NNReal) by
    exact_mod_cast (Finset.card_eq_sum_card_fiberwise
      (fun i hi => U.cover.assign_mem N le_rfl i hi))]
  calc
    (∑ j ∈ U.cover.indexSet N,
        ((_root_.Tube.coverClass s (U.cover.assign N) j).card : NNReal)) <=
        ∑ _j ∈ U.cover.indexSet N, C * U.branchingN N :=
      Finset.sum_le_sum fun j hj => U.card_class_le N le_rfl j hj
    _ = C * U.branchingN N * ((U.cover.indexSet N).card : NNReal) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring

/-- The reverse class bracket, in the exact product order used by WZ cancellation. -/
theorem branch_mul_fullNode_card_le_balance_mul_leaf_card
    {ι : Type*} {delta C : NNReal} {s : Finset ι}
    (V : ι -> ShadedTube delta E) {N : Nat}
    (U : _root_.Tube.UniformTubeSet s (fun i => (V i).toTube) N C) :
    U.branchingN N * ((U.cover.indexSet N).card : NNReal) <=
      C * (s.card : NNReal) := by
  classical
  rw [show (s.card : NNReal) =
      ∑ j ∈ U.cover.indexSet N,
        ((_root_.Tube.coverClass s (U.cover.assign N) j).card : NNReal) by
    exact_mod_cast (Finset.card_eq_sum_card_fiberwise
      (fun i hi => U.cover.assign_mem N le_rfl i hi))]
  calc
    U.branchingN N * ((U.cover.indexSet N).card : NNReal) =
        ∑ _j ∈ U.cover.indexSet N, U.branchingN N := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring
    _ <= ∑ j ∈ U.cover.indexSet N,
        C * ((_root_.Tube.coverClass s (U.cover.assign N) j).card : NNReal) :=
      Finset.sum_le_sum fun j hj => U.le_card_class N le_rfl j hj
    _ = C * ∑ j ∈ U.cover.indexSet N,
        ((_root_.Tube.coverClass s (U.cover.assign N) j).card : NNReal) := by
      rw [Finset.mul_sum]

/-- The total leaf shade mass is at most `C * branching` times the aggregated node shade mass. -/
theorem sum_leaf_shade_le_balance_mul_branch_mul_sum_fullNode_shade
    {ι : Type*} {delta C : NNReal} {s : Finset ι}
    (V : ι -> ShadedTube delta E) {N : Nat} (hN : 0 < N)
    (U : _root_.Tube.UniformTubeSet s (fun i => (V i).toTube) N C) :
    ∑ i ∈ s, volume (V i).shade <=
      (C : ENNReal) * (U.branchingN N : ENNReal) *
        ∑ j ∈ U.cover.indexSet N, volume (fullNodeFamily V hN U j).shade := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to
    (fun i hi => U.cover.assign_mem N le_rfl i hi)
    (fun i => volume (V i).shade)]
  calc
    (∑ j ∈ U.cover.indexSet N,
        ∑ i ∈ _root_.Tube.coverClass s (U.cover.assign N) j,
          volume (V i).shade) <=
        ∑ j ∈ U.cover.indexSet N,
          (C : ENNReal) * (U.branchingN N : ENNReal) *
            volume (fullNodeFamily V hN U j).shade := by
      apply Finset.sum_le_sum
      intro j hj
      calc
        (∑ i ∈ _root_.Tube.coverClass s (U.cover.assign N) j,
            volume (V i).shade) <=
            (((_root_.Tube.coverClass s (U.cover.assign N) j).card : ENNReal) *
              volume (fullNodeFamily V hN U j).shade) := by
          rw [← nsmul_eq_mul]
          exact Finset.sum_le_card_nsmul _ _ _ fun i hi =>
            measure_mono (by
              intro x hx
              rw [fullNodeFamily_shade, Set.mem_iUnion₂]
              exact ⟨i, hi, hx⟩)
        _ <= (C : ENNReal) * (U.branchingN N : ENNReal) *
            volume (fullNodeFamily V hN U j).shade := by
          gcongr
          exact_mod_cast U.card_class_le N le_rfl j hj
    _ = (C : ENNReal) * (U.branchingN N : ENNReal) *
        ∑ j ∈ U.cover.indexSet N, volume (fullNodeFamily V hN U j).shade := by
      rw [Finset.mul_sum]

/-- Aggregation loses at most one upper class-size factor in multiplicity. -/
theorem multiplicity_leaf_le_balance_mul_branch_mul_fullNode
    {ι : Type*} {delta C : NNReal} {s : Finset ι}
    (V : ι -> ShadedTube delta E) {N : Nat} (hN : 0 < N)
    (U : _root_.Tube.UniformTubeSet s (fun i => (V i).toTube) N C) :
    ShadedBody.multiplicity s (fun i => (V i).toShadedBody) <=
      (C : ENNReal) * (U.branchingN N : ENNReal) *
        ShadedBody.multiplicity (U.cover.indexSet N)
          (fun j => (fullNodeFamily V hN U j).toShadedBody) := by
  unfold ShadedBody.multiplicity
  change (∑ i ∈ s, volume (V i).shade) /
      volume (ShadedBody.iUnionShade s (fun i => (V i).toShadedBody)) <=
    (C : ENNReal) * (U.branchingN N : ENNReal) *
      ((∑ j ∈ U.cover.indexSet N, volume (fullNodeFamily V hN U j).shade) /
        volume (ShadedBody.iUnionShade (U.cover.indexSet N)
          (fun j => (fullNodeFamily V hN U j).toShadedBody)))
  rw [iUnionShade_fullNodeFamily V hN U]
  calc
    (∑ i ∈ s, volume (V i).shade) /
          volume (ShadedBody.iUnionShade s (fun i => (V i).toShadedBody)) <=
        ((C : ENNReal) * (U.branchingN N : ENNReal) *
          ∑ j ∈ U.cover.indexSet N, volume (fullNodeFamily V hN U j).shade) /
            volume (ShadedBody.iUnionShade s (fun i => (V i).toShadedBody)) := by
      gcongr
      exact sum_leaf_shade_le_balance_mul_branch_mul_sum_fullNode_shade V hN U
    _ = (C : ENNReal) * (U.branchingN N : ENNReal) *
        ((∑ j ∈ U.cover.indexSet N, volume (fullNodeFamily V hN U j).shade) /
          volume (ShadedBody.iUnionShade s (fun i => (V i).toShadedBody))) := by
      rw [div_eq_mul_inv]
      simp only [div_eq_mul_inv]
      ac_rfl

/-- The lower class-size bracket compares total node-carrier mass to total leaf-carrier mass. -/
theorem branch_mul_sum_fullNode_carrier_le_balance_mul_sum_leaf_carrier
    {ι : Type*} {delta C : NNReal} {s : Finset ι}
    (V : ι -> ShadedTube delta E) {N : Nat} (hN : 0 < N)
    (U : _root_.Tube.UniformTubeSet s (fun i => (V i).toTube) N C)
    (hs : s.Nonempty) :
    (U.branchingN N : ENNReal) *
        ∑ j ∈ U.cover.indexSet N, volume (fullNodeFamily V hN U j).carrier <=
      (C : ENNReal) * ∑ i ∈ s, volume (V i).carrier := by
  obtain ⟨i0, hi0⟩ := hs
  have hnodeSum :
      ∑ j ∈ U.cover.indexSet N, volume (fullNodeFamily V hN U j).carrier =
        ((U.cover.indexSet N).card : ENNReal) * volume (V i0).carrier := by
    exact _root_.Tube.sum_volume_carrier_eq_card_mul
      (fun j => (fullNodeFamily V hN U j).toTube) (V i0).toTube
      (U.cover.indexSet N)
  have hleafSum :
      ∑ i ∈ s, volume (V i).carrier =
        (s.card : ENNReal) * volume (V i0).carrier := by
    exact _root_.Tube.sum_volume_carrier_eq_card_mul
      (fun i => (V i).toTube) (V i0).toTube s
  rw [hnodeSum, hleafSum]
  have hcard : (U.branchingN N : ENNReal) *
      ((U.cover.indexSet N).card : ENNReal) <=
        (C : ENNReal) * (s.card : ENNReal) := by
    exact_mod_cast branch_mul_fullNode_card_le_balance_mul_leaf_card V U
  calc
    (U.branchingN N : ENNReal) *
          (((U.cover.indexSet N).card : ENNReal) * volume (V i0).carrier) =
        ((U.branchingN N : ENNReal) *
          ((U.cover.indexSet N).card : ENNReal)) * volume (V i0).carrier := by ring
    _ <= ((C : ENNReal) * (s.card : ENNReal)) * volume (V i0).carrier := by
      exact mul_le_mul_right' hcard _
    _ = (C : ENNReal) * ((s.card : ENNReal) * volume (V i0).carrier) := by ring

/-- Fullness survives aggregation with the exact squared balance loss and no branching loss. -/
theorem coe_fullness_leaf_le_balance_sq_mul_fullNode
    {ι : Type*} {delta C : NNReal} {s : Finset ι}
    (V : ι -> ShadedTube delta E) {N : Nat} (hN : 0 < N)
    (U : _root_.Tube.UniformTubeSet s (fun i => (V i).toTube) N C)
    (hdelta0 : 0 < delta) (hs : s.Nonempty) :
    (ShadedBody.fullness s (fun i => (V i).toShadedBody) : ENNReal) <=
      (C : ENNReal) ^ 2 *
        (ShadedBody.fullness (U.cover.indexSet N)
          (fun j => (fullNodeFamily V hN U j).toShadedBody) : ENNReal) := by
  have hs_nonempty := hs
  obtain ⟨i0, hi0⟩ := hs
  let D : ENNReal := ∑ i ∈ s, volume (V i).carrier
  have hvpos : 0 < volume (V i0).carrier := by
    have hc : 0 < (_root_.Tube.le_volume.c (Module.finrank Real E) : ENNReal) :=
      ENNReal.coe_pos.mpr (_root_.Tube.le_volume.c_pos (Module.finrank Real E))
    have hd : 0 < (delta : ENNReal) ^ (Module.finrank Real E - 1) :=
      ENNReal.pow_pos (ENNReal.coe_pos.mpr hdelta0) (Module.finrank Real E - 1)
    exact lt_of_lt_of_le (ENNReal.mul_pos hc.ne' hd.ne')
      (by simpa using _root_.Tube.le_volume (V i0).toTube)
  have hDeq : D = (s.card : ENNReal) * volume (V i0).carrier := by
    dsimp [D]
    exact _root_.Tube.sum_volume_carrier_eq_card_mul
      (fun i => (V i).toTube) (V i0).toTube s
  have hD0 : D ≠ 0 := by
    rw [hDeq]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr
      (Finset.card_ne_zero.mpr hs_nonempty)) hvpos.ne'
  have hDtop : D ≠ ⊤ := by
    dsimp [D]
    intro htop
    rcases ENNReal.sum_eq_top.mp htop with ⟨i, _hi, hitop⟩
    exact (V i).isCompact.measure_ne_top hitop
  apply (ENNReal.mul_le_mul_iff_right hD0 hDtop).mp
  calc
    D * (ShadedBody.fullness s (fun i => (V i).toShadedBody) : ENNReal) =
        (ShadedBody.fullness s (fun i => (V i).toShadedBody) : ENNReal) * D := by
      ring
    _ =
        ∑ i ∈ s, volume (V i).shade := by
      dsimp [D]
      simpa using (ShadedBody.sum_volumeReal_shade_eq_fullness_mul
        s (fun i => (V i).toShadedBody)).symm
    _ <= (C : ENNReal) * (U.branchingN N : ENNReal) *
        ∑ j ∈ U.cover.indexSet N, volume (fullNodeFamily V hN U j).shade :=
      sum_leaf_shade_le_balance_mul_branch_mul_sum_fullNode_shade V hN U
    _ = (C : ENNReal) * (U.branchingN N : ENNReal) *
        ((ShadedBody.fullness (U.cover.indexSet N)
            (fun j => (fullNodeFamily V hN U j).toShadedBody) : ENNReal) *
          ∑ j ∈ U.cover.indexSet N, volume (fullNodeFamily V hN U j).carrier) := by
      congr 2
      simpa using (ShadedBody.sum_volumeReal_shade_eq_fullness_mul
        (U.cover.indexSet N)
        (fun j => (fullNodeFamily V hN U j).toShadedBody))
    _ = (C : ENNReal) *
        (ShadedBody.fullness (U.cover.indexSet N)
          (fun j => (fullNodeFamily V hN U j).toShadedBody) : ENNReal) *
        ((U.branchingN N : ENNReal) *
          ∑ j ∈ U.cover.indexSet N, volume (fullNodeFamily V hN U j).carrier) := by
      ring
    _ <= (C : ENNReal) *
        (ShadedBody.fullness (U.cover.indexSet N)
          (fun j => (fullNodeFamily V hN U j).toShadedBody) : ENNReal) *
        ((C : ENNReal) * ∑ i ∈ s, volume (V i).carrier) := by
      exact mul_le_mul_left'
        (branch_mul_sum_fullNode_carrier_le_balance_mul_sum_leaf_carrier
          V hN U hs_nonempty) _
    _ = D * ((C : ENNReal) ^ 2 *
        (ShadedBody.fullness (U.cover.indexSet N)
          (fun j => (fullNodeFamily V hN U j).toShadedBody) : ENNReal)) := by
      dsimp [D]
      ring

/-- Consumer-facing fullness lower bound. -/
theorem inv_balance_sq_mul_coe_fullness_leaf_le_fullNode
    {ι : Type*} {delta C : NNReal} {s : Finset ι}
    (V : ι -> ShadedTube delta E) {N : Nat} (hN : 0 < N)
    (U : _root_.Tube.UniformTubeSet s (fun i => (V i).toTube) N C)
    (hdelta0 : 0 < delta) (hs : s.Nonempty) (hC : C ≠ 0) :
    ((C : ENNReal) ^ 2)⁻¹ *
        (ShadedBody.fullness s (fun i => (V i).toShadedBody) : ENNReal) <=
      (ShadedBody.fullness (U.cover.indexSet N)
        (fun j => (fullNodeFamily V hN U j).toShadedBody) : ENNReal) := by
  rw [ENNReal.inv_mul_le_iff (pow_ne_zero 2 (ENNReal.coe_ne_zero.mpr hC))
    (ENNReal.pow_ne_top ENNReal.coe_ne_top)]
  exact coe_fullness_leaf_le_balance_sq_mul_fullNode V hN U hdelta0 hs

/-- Cross-multiplied density numerator control in every convex test body.  This is the sharp
form: the terminal branching factor is retained on the node side. -/
theorem branch_mul_filtered_fullNode_volume_le_balance_mul_filtered_leaf_volume
    {ι : Type*} {delta C : NNReal} {s : Finset ι}
    (V : ι -> ShadedTube delta E) {N : Nat} (hN : 0 < N)
    (U : _root_.Tube.UniformTubeSet s (fun i => (V i).toTube) N C)
    (K : ConvexSpaceBody E) :
    (U.branchingN N : ENNReal) *
        ∑ j ∈ U.cover.indexSet N with
          (fullNodeFamily V hN U j).toConvexSpaceBody <= K,
            volume (fullNodeFamily V hN U j).carrier <=
      (C : ENNReal) *
        ∑ i ∈ s with (V i).toConvexSpaceBody <= K, volume (V i).carrier := by
  classical
  let t : Finset ι := (U.cover.indexSet N).filter
    (fun j => (fullNodeFamily V hN U j).toConvexSpaceBody <= K)
  let q : Finset ι := s.filter (fun i => (V i).toConvexSpaceBody <= K)
  change (U.branchingN N : ENNReal) *
      ∑ j ∈ t, volume (fullNodeFamily V hN U j).carrier <=
    (C : ENNReal) * ∑ i ∈ q, volume (V i).carrier
  have hmaps : ∀ i ∈ q, U.cover.assign N i ∈ t := by
    intro i hi
    have hi' : i ∈ s ∧ (V i).toConvexSpaceBody <= K := by
      simpa [q] using Finset.mem_filter.mp hi
    apply Finset.mem_filter.mpr
    refine ⟨U.cover.assign_mem N le_rfl i hi'.1, ?_⟩
    rw [← leaf_body_eq_assigned_fullNode V hN U hi'.1]
    exact hi'.2
  have hfiber (j : ι) (hj : j ∈ t) :
      ({i ∈ q | U.cover.assign N i = j} : Finset ι) =
        _root_.Tube.coverClass s (U.cover.assign N) j := by
    ext i
    simp only [_root_.Tube.coverClass, q, Finset.mem_filter]
    constructor
    · intro hi
      exact ⟨hi.1.1, hi.2⟩
    · intro hi
      refine ⟨⟨hi.1, ?_⟩, hi.2⟩
      have hj' : j ∈ U.cover.indexSet N ∧
          (fullNodeFamily V hN U j).toConvexSpaceBody <= K := by
        simpa [t] using Finset.mem_filter.mp hj
      rw [leaf_body_eq_assigned_fullNode V hN U hi.1, hi.2]
      exact hj'.2
  have hpartition :
      ∑ i ∈ q, volume (V i).carrier =
        ∑ j ∈ t, ∑ i ∈ _root_.Tube.coverClass s (U.cover.assign N) j,
          volume (V i).carrier := by
    calc
      (∑ i ∈ q, volume (V i).carrier) =
          ∑ j ∈ t, ∑ i ∈ ({i ∈ q | U.cover.assign N i = j} : Finset ι),
            volume (V i).carrier :=
        (Finset.sum_fiberwise_of_maps_to hmaps
          (fun i => volume (V i).carrier)).symm
      _ = ∑ j ∈ t, ∑ i ∈ _root_.Tube.coverClass s (U.cover.assign N) j,
          volume (V i).carrier := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hfiber j hj]
  have hper (j : ι) (hj : j ∈ t) :
      (U.branchingN N : ENNReal) * volume (fullNodeFamily V hN U j).carrier <=
        (C : ENNReal) *
          ∑ i ∈ _root_.Tube.coverClass s (U.cover.assign N) j,
            volume (V i).carrier := by
    have hjNode : j ∈ U.cover.indexSet N :=
      (Finset.mem_filter.mp hj).1
    have hcard : (U.branchingN N : ENNReal) <=
        (C : ENNReal) *
          ((_root_.Tube.coverClass s (U.cover.assign N) j).card : ENNReal) := by
      exact_mod_cast U.le_card_class N le_rfl j hjNode
    have hsum :
        ∑ i ∈ _root_.Tube.coverClass s (U.cover.assign N) j,
            volume (V i).carrier =
          ((_root_.Tube.coverClass s (U.cover.assign N) j).card : ENNReal) *
            volume (fullNodeFamily V hN U j).carrier := by
      exact _root_.Tube.sum_volume_carrier_eq_card_mul
        (fun i => (V i).toTube) (fullNodeFamily V hN U j).toTube
        (_root_.Tube.coverClass s (U.cover.assign N) j)
    calc
      (U.branchingN N : ENNReal) * volume (fullNodeFamily V hN U j).carrier <=
          ((C : ENNReal) *
            ((_root_.Tube.coverClass s (U.cover.assign N) j).card : ENNReal)) *
              volume (fullNodeFamily V hN U j).carrier :=
        mul_le_mul_right' hcard _
      _ = (C : ENNReal) *
          (((_root_.Tube.coverClass s (U.cover.assign N) j).card : ENNReal) *
            volume (fullNodeFamily V hN U j).carrier) := by ring
      _ = (C : ENNReal) *
          ∑ i ∈ _root_.Tube.coverClass s (U.cover.assign N) j,
            volume (V i).carrier := by rw [hsum]
  calc
    (U.branchingN N : ENNReal) *
          ∑ j ∈ t, volume (fullNodeFamily V hN U j).carrier =
        ∑ j ∈ t, (U.branchingN N : ENNReal) *
          volume (fullNodeFamily V hN U j).carrier := by rw [Finset.mul_sum]
    _ <= ∑ j ∈ t, (C : ENNReal) *
        ∑ i ∈ _root_.Tube.coverClass s (U.cover.assign N) j,
          volume (V i).carrier := Finset.sum_le_sum hper
    _ = (C : ENNReal) *
        ∑ j ∈ t, ∑ i ∈ _root_.Tube.coverClass s (U.cover.assign N) j,
          volume (V i).carrier := by rw [Finset.mul_sum]
    _ = (C : ENNReal) * ∑ i ∈ q, volume (V i).carrier := by rw [hpartition]

/-- Pointwise density transport, with the same sharp branching/balance cross product. -/
theorem branch_mul_densityIn_fullNode_le_balance_mul_densityIn_leaf
    {ι : Type*} {delta C : NNReal} {s : Finset ι}
    (V : ι -> ShadedTube delta E) {N : Nat} (hN : 0 < N)
    (U : _root_.Tube.UniformTubeSet s (fun i => (V i).toTube) N C)
    (K : ConvexSpaceBody E) :
    (U.branchingN N : ENNReal) *
        densityIn (U.cover.indexSet N)
          (fun j => (fullNodeFamily V hN U j).toConvexSpaceBody) K <=
      (C : ENNReal) *
        densityIn s (fun i => (V i).toConvexSpaceBody) K := by
  unfold densityIn
  calc
    (U.branchingN N : ENNReal) *
        ((∑ j ∈ U.cover.indexSet N with
            (fullNodeFamily V hN U j).toConvexSpaceBody <= K,
              volume (fullNodeFamily V hN U j).carrier) / volume K.carrier) =
      ((U.branchingN N : ENNReal) *
        ∑ j ∈ U.cover.indexSet N with
          (fullNodeFamily V hN U j).toConvexSpaceBody <= K,
            volume (fullNodeFamily V hN U j).carrier) / volume K.carrier := by
      simp only [div_eq_mul_inv]
      ac_rfl
    _ <= ((C : ENNReal) *
        ∑ i ∈ s with (V i).toConvexSpaceBody <= K, volume (V i).carrier) /
          volume K.carrier := ENNReal.div_le_div_right
      (branch_mul_filtered_fullNode_volume_le_balance_mul_filtered_leaf_volume
        V hN U K) _
    _ = (C : ENNReal) *
        ((∑ i ∈ s with (V i).toConvexSpaceBody <= K, volume (V i).carrier) /
          volume K.carrier) := by
      simp only [div_eq_mul_inv]
      ac_rfl

/-- Sharp maximal-density transport.  Its branching factor cancels exactly against the full-node
cardinality and Q-band factors in the WZ middle estimate. -/
theorem branch_mul_maxDensity_fullNode_le_balance_mul_maxDensity_leaf
    {ι : Type*} {delta C : NNReal} {s : Finset ι}
    (V : ι -> ShadedTube delta E) {N : Nat} (hN : 0 < N)
    (U : _root_.Tube.UniformTubeSet s (fun i => (V i).toTube) N C) :
    (U.branchingN N : ENNReal) *
        maxDensity (U.cover.indexSet N)
          (fun j => (fullNodeFamily V hN U j).toConvexSpaceBody) <=
      (C : ENNReal) * maxDensity s (fun i => (V i).toConvexSpaceBody) := by
  let Wn : ι -> ConvexSpaceBody E :=
    fun j => (fullNodeFamily V hN U j).toConvexSpaceBody
  let Wl : ι -> ConvexSpaceBody E := fun i => (V i).toConvexSpaceBody
  let Kstar : ConvexSpaceBody E :=
    (density_maximizer (U.cover.indexSet N) Wn).convexHull_biUnion Wn
  change (U.branchingN N : ENNReal) * maxDensity (U.cover.indexSet N) Wn <=
    (C : ENNReal) * maxDensity s Wl
  rw [← densityIn_self_maximizer_eq (U.cover.indexSet N) Wn]
  calc
    (U.branchingN N : ENNReal) * densityIn (U.cover.indexSet N) Wn Kstar <=
        (C : ENNReal) * densityIn s Wl Kstar := by
      exact branch_mul_densityIn_fullNode_le_balance_mul_densityIn_leaf V hN U Kstar
    _ <= (C : ENNReal) * maxDensity s Wl :=
      mul_le_mul_left' (le_maxDensity s Wl Kstar) _

/-- At full level, the density of an assignment class inside its node is exactly the class
cardinality: every class member has exactly the node carrier. -/
theorem densityIn_coverClass_fullNode_eq_card
    {ι : Type*} {delta C : NNReal} {s : Finset ι}
    (V : ι -> ShadedTube delta E) {N : Nat} (hN : 0 < N)
    (U : _root_.Tube.UniformTubeSet s (fun i => (V i).toTube) N C)
    (hdelta0 : 0 < delta) {j : ι} (hj : j ∈ U.cover.indexSet N) :
    densityIn (_root_.Tube.coverClass s (U.cover.assign N) j)
        (fun i => (V i).toConvexSpaceBody)
        (fullNodeFamily V hN U j).toConvexSpaceBody =
      ((_root_.Tube.coverClass s (U.cover.assign N) j).card : ENNReal) := by
  classical
  have hall : ∀ i ∈ _root_.Tube.coverClass s (U.cover.assign N) j,
      (V i).toConvexSpaceBody <=
        (fullNodeFamily V hN U j).toConvexSpaceBody := by
    intro i hi
    have hi' : i ∈ s ∧ U.cover.assign N i = j := by
      simpa [_root_.Tube.coverClass] using Finset.mem_filter.mp hi
    rw [leaf_body_eq_assigned_fullNode V hN U hi'.1, hi'.2]
  have hsum :
      ∑ i ∈ _root_.Tube.coverClass s (U.cover.assign N) j, volume (V i).carrier =
        ((_root_.Tube.coverClass s (U.cover.assign N) j).card : ENNReal) *
          volume (fullNodeFamily V hN U j).carrier := by
    exact _root_.Tube.sum_volume_carrier_eq_card_mul
      (fun i => (V i).toTube) (fullNodeFamily V hN U j).toTube
      (_root_.Tube.coverClass s (U.cover.assign N) j)
  have hvpos : 0 < volume (fullNodeFamily V hN U j).carrier := by
    have hc : 0 < (_root_.Tube.le_volume.c (Module.finrank Real E) : ENNReal) :=
      ENNReal.coe_pos.mpr (_root_.Tube.le_volume.c_pos (Module.finrank Real E))
    have hd : 0 < (delta : ENNReal) ^ (Module.finrank Real E - 1) :=
      ENNReal.pow_pos (ENNReal.coe_pos.mpr hdelta0) (Module.finrank Real E - 1)
    exact lt_of_lt_of_le (ENNReal.mul_pos hc.ne' hd.ne')
      (by simpa using _root_.Tube.le_volume (fullNodeFamily V hN U j).toTube)
  have hvtop : volume (fullNodeFamily V hN U j).carrier ≠ ⊤ :=
    (fullNodeFamily V hN U j).isCompact.measure_ne_top
  rw [densityIn_of_all_le hall, hsum]
  exact ENNReal.mul_div_cancel_right hvpos.ne' hvtop

/-- Exact Frostman-predicate transport from leaves to honest full nodes.  The two class brackets
cost `C^2`; no branching factor remains. -/
theorem isFrostmanIn_fullNode_of_leaf
    {ι : Type*} {delta C : NNReal} {s : Finset ι}
    (V : ι -> ShadedTube delta E) {N : Nat} (hN : 0 < N)
    (U : _root_.Tube.UniformTubeSet s (fun i => (V i).toTube) N C)
    (hdelta0 : 0 < delta) (hs : s.Nonempty)
    {K : ConvexSpaceBody E} {Cf : ENNReal}
    (hFr : ConvexSpaceBody.IsFrostmanIn s
      (fun i => (V i).toConvexSpaceBody) K Cf)
    (hVK : ∀ i ∈ s, (V i).toConvexSpaceBody <= K) :
    ConvexSpaceBody.IsFrostmanIn (U.cover.indexSet N)
      (fun j => (fullNodeFamily V hN U j).toConvexSpaceBody) K
      ((C : ENNReal) ^ 2 * Cf) := by
  classical
  apply ConvexSpaceBody.isFrostmanIn_parents_of_uniform_fibres
    (q := s) (out := U.cover.indexSet N)
    (V := fun i => (V i).toConvexSpaceBody)
    (W := fun j => (fullNodeFamily V hN U j).toConvexSpaceBody)
    (par := U.cover.assign N)
    (fib := fun j => _root_.Tube.coverClass s (U.cover.assign N) j)
    (Cmass := (C : ENNReal) ^ 2) hFr
  · intro i hi
    have hc : 0 < (_root_.Tube.le_volume.c (Module.finrank Real E) : ENNReal) :=
      ENNReal.coe_pos.mpr (_root_.Tube.le_volume.c_pos (Module.finrank Real E))
    have hd : 0 < (delta : ENNReal) ^ (Module.finrank Real E - 1) :=
      ENNReal.pow_pos (ENNReal.coe_pos.mpr hdelta0) (Module.finrank Real E - 1)
    exact lt_of_lt_of_le (ENNReal.mul_pos hc.ne' hd.ne')
      (by simpa using _root_.Tube.le_volume (V i).toTube)
  · exact fun i hi => U.cover.assign_mem N le_rfl i hi
  · intro i hi
    exact (leaf_body_eq_assigned_fullNode V hN U hi).le
  · intro j hj
    obtain ⟨i, hi⟩ :=
      _root_.Kakeya.MultiScaleFac.coverClass_nonempty_of_mem_parent U le_rfl hs hj
    have hi' : i ∈ s ∧ U.cover.assign N i = j := by
      simpa [_root_.Tube.coverClass] using Finset.mem_filter.mp hi
    rw [← hi'.2, ← leaf_body_eq_assigned_fullNode V hN U hi'.1]
    exact hVK i hi'.1
  · intro j
    rfl
  · exact fun j hj =>
      _root_.Kakeya.MultiScaleFac.coverClass_nonempty_of_mem_parent U le_rfl hs hj
  · intro j hj j' hj'
    rw [densityIn_coverClass_fullNode_eq_card V hN U hdelta0 hj,
      densityIn_coverClass_fullNode_eq_card V hN U hdelta0 hj']
    have hcard :
        ((_root_.Tube.coverClass s (U.cover.assign N) j).card : NNReal) <=
          C ^ 2 *
            ((_root_.Tube.coverClass s (U.cover.assign N) j').card : NNReal) := by
      calc
        ((_root_.Tube.coverClass s (U.cover.assign N) j).card : NNReal) <=
            C * U.branchingN N := U.card_class_le N le_rfl j hj
        _ <= C * (C *
            ((_root_.Tube.coverClass s (U.cover.assign N) j').card : NNReal)) :=
          mul_le_mul_of_nonneg_left (U.le_card_class N le_rfl j' hj') (by positivity)
        _ = C ^ 2 *
            ((_root_.Tube.coverClass s (U.cover.assign N) j').card : NNReal) := by ring
    exact_mod_cast hcard

/-- Value-level Frostman transport used by the WZ consumer. -/
theorem frostmanConstIn_fullNode_le_balance_sq_mul_leaf
    {ι : Type*} {delta C : NNReal} {s : Finset ι}
    (V : ι -> ShadedTube delta E) {N : Nat} (hN : 0 < N)
    (U : _root_.Tube.UniformTubeSet s (fun i => (V i).toTube) N C)
    (hdelta0 : 0 < delta) (hs : s.Nonempty)
    {K : ConvexSpaceBody E}
    (hVK : ∀ i ∈ s, (V i).toConvexSpaceBody <= K) :
    frostmanConstIn (U.cover.indexSet N)
        (fun j => (fullNodeFamily V hN U j).toConvexSpaceBody) K <=
      (C : ENNReal) ^ 2 *
        frostmanConstIn s (fun i => (V i).toConvexSpaceBody) K := by
  apply frostmanConstIn_le
  apply isFrostmanIn_fullNode_of_leaf V hN U hdelta0 hs
  · simpa [frostmanConstIn_eq_frostmanConstant] using
      (ConvexSpaceBody.isFrostmanIn_frostmanConstant
        (s := s) (W := fun i => (V i).toConvexSpaceBody) (K := K))
  · exact hVK

end

end Kakeya.ml1Boot.W44FullNode
