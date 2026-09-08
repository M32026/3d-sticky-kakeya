/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.EnlargementCover
public import Kakeya.DimensionThree.BoundedOverlapCount

/-!
# Axial covers for parent conflicts

This file supplies the geometric core of the essentially-distinct parent selection used in
Section 8.  A family of same-scale parents which all fail essential distinctness against one
fixed parent lies in a bounded homothetic dilate of that parent.  Such a dilate is not covered by
constantly many same-scale tubes: unit cores may slide along the axis, and there are genuinely
`O(ρ⁻¹)` possible axial positions.  The declarations below isolate exactly that freedom.

For a thin tube `U` in the overlap dilate of a `ρ`-tube `V`, first orient `U` along `V`, round its
axial midpoint coordinate to an integer multiple of `ρ`, and place it in a concentric rescaling
of the corresponding axial translate of `V`.  The already-proved fixed-size rescaling cover
`Kakeya.ml1Boot.exists_cover_of_subset_rescale` then replaces that rescaling by one of constantly
many actual `ρ`-tubes.  The integer slice is returned explicitly; a later counting lemma bounds
the number of slices by `O(ρ⁻¹)`.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology ConvexSpaceBody

namespace Kakeya.ml1Boot

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

namespace parentConflictCover

/-- The rescaling ratio used within one axial slice.  It depends only on the ambient dimension. -/
noncomputable def Lambda (n : ℕ) : NNReal :=
  4 * ((Kakeya.Tube.tubeOverlapCoreClose.C n).toNNReal + 1)

theorem Lambda_pos (n : ℕ) : 0 < Lambda n := by
  unfold Lambda
  positivity

theorem Lambda_coe (n : ℕ) :
    (Lambda n : ℝ) = 4 * (Kakeya.Tube.tubeOverlapCoreClose.C n + 1) := by
  unfold Lambda
  push_cast
  rw [Real.coe_toNNReal _ (le_trans zero_le_one
    (le_of_lt (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C n)))]

/-- Dimensional constant in the axial parent-conflict count. -/
noncomputable def C (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [ProperSpace E] : NNReal :=
  (enlargementCoverConstant E (Lambda (Module.finrank ℝ E)) + 1 : ℕ) *
    (3 * (Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E)).toNNReal + 2)

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
theorem C_pos : 0 < C E := by
  unfold C
  positivity

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
theorem C_coe : (C E : ℝ) =
    (enlargementCoverConstant E (Lambda (Module.finrank ℝ E)) + 1 : ℕ) *
      (3 * Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) + 2) := by
  unfold C
  push_cast
  rw [Real.coe_toNNReal _ (le_trans zero_le_one
    (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C (Module.finrank ℝ E)).le)]

/-- Constant absorbing the global `ρ⁻⁵` parent count when `ρ` has the dimensional lower
bound complementary to the axial regime. -/
noncomputable def largeScaleC (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [ProperSpace E] : NNReal :=
  parentCount.C *
    (8 * (Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E)).toNNReal) ^ 4

/-- Uniform dimensional constant for the three parent-conflict regimes. -/
noncomputable def degreeC (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [ProperSpace E] : NNReal :=
  max (Tube.comparableReplacement.C (Module.finrank ℝ E) 2)
    (max (C E) (largeScaleC E))

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
theorem degreeC_pos : 0 < degreeC E := by
  unfold degreeC
  exact lt_of_lt_of_le zero_lt_one
    ((Tube.comparableReplacement.one_le_C (Module.finrank ℝ E) 2).trans (le_max_left _ _))

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
theorem comparable_le_degreeC :
    Tube.comparableReplacement.C (Module.finrank ℝ E) 2 ≤ degreeC E :=
  le_max_left _ _

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
theorem axial_le_degreeC : C E ≤ degreeC E :=
  le_trans (le_max_left _ _) (le_max_right _ _)

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
theorem largeScale_le_degreeC : largeScaleC E ≤ degreeC E :=
  le_trans (le_max_right _ _) (le_max_right _ _)

/-- The `z`-th same-scale axial translate of `V`, with midpoint shifted by `z ρ`. -/
noncomputable def axialTube {ρ : NNReal} (V : Tube ρ E) (z : ℤ) : Tube ρ E :=
  Tube.ofMidpointDirection ρ
    (V.center + ((z : ℝ) * (ρ : ℝ)) • V.direction) V.direction V.norm_direction

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
@[simp] theorem axialTube_midpoint {ρ : NNReal} (V : Tube ρ E) (z : ℤ) :
    (axialTube V z).midpoint = V.center + ((z : ℝ) * (ρ : ℝ)) • V.direction := by
  simp [axialTube, Tube.midpoint]
  module

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
@[simp] theorem axialTube_direction {ρ : NNReal} (V : Tube ρ E) (z : ℤ) :
    (axialTube V z).direction = V.direction := by
  simp [axialTube, Tube.direction]
  module

/-- The fixed finite cover attached to one axial slice. -/
noncomputable def axialCover {σ ρ : NNReal} (hσρ : 2 * (σ : ℝ) ≤ (ρ : ℝ))
    (V : Tube ρ E) (z : ℤ) :
    Fin (enlargementCoverConstant E (Lambda (Module.finrank ℝ E))) → Tube ρ E :=
  (exists_cover_of_subset_rescale (E := E) (δ := σ)
    (Lambda (Module.finrank ℝ E)) hσρ (axialTube V z)).choose

omit [Nontrivial E] in
theorem axialCover_spec {σ ρ : NNReal} (hσρ : 2 * (σ : ℝ) ≤ (ρ : ℝ))
    (V : Tube ρ E) (z : ℤ) (U : Tube σ E)
    (hU : U.toConvexSpaceBody ≤
      ((axialTube V z).rescale (Lambda (Module.finrank ℝ E) * ρ)).toConvexSpaceBody) :
    ∃ q : Fin (enlargementCoverConstant E (Lambda (Module.finrank ℝ E))),
      U.toConvexSpaceBody ≤ (axialCover hσρ V z q).toConvexSpaceBody := by
  exact (exists_cover_of_subset_rescale (E := E) (δ := σ)
    (Lambda (Module.finrank ℝ E)) hσρ (axialTube V z)).choose_spec U hU

/-- Flooring at mesh `h` rounds a real number down to an integer multiple of `h`, with error at
most `h`.  The second conclusion is the interval estimate later used to count the axial slices. -/
theorem exists_floor_mul_close {x h A : ℝ} (hh : 0 < h) (hx : |x| ≤ A) :
    ∃ z : ℤ, |x - (z : ℝ) * h| ≤ h ∧
      -(A / h + 1) ≤ (z : ℝ) ∧ (z : ℝ) ≤ A / h := by
  let z : ℤ := ⌊x / h⌋
  have hzlo : (z : ℝ) * h ≤ x := by
    exact (le_div_iff₀ hh).mp (Int.floor_le (x / h))
  have hzhi : x < ((z : ℝ) + 1) * h := by
    exact (div_lt_iff₀ hh).mp (Int.lt_floor_add_one (x / h))
  have hround : |x - (z : ℝ) * h| ≤ h := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hxlo : -A ≤ x := (abs_le.mp hx).1
  have hxhi : x ≤ A := (abs_le.mp hx).2
  refine ⟨z, hround, ?_, ?_⟩
  · have hxlo_div : -A / h ≤ x / h := div_le_div_of_nonneg_right hxlo hh.le
    have hxlo_div' : -(A / h) ≤ x / h := by simpa only [neg_div] using hxlo_div
    have hzstep : x / h < (z : ℝ) + 1 := Int.lt_floor_add_one (x / h)
    linarith
  · have hxhi_div : x / h ≤ A / h := div_le_div_of_nonneg_right hxhi hh.le
    exact (Int.floor_le (x / h)).trans hxhi_div

/-- Failure of essential distinctness between equal-scale tubes puts either carrier in the fixed
overlap dilate of the other. -/
theorem subset_overlapDilate_of_not_essDistinct {ρ : NNReal} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (V W : Tube ρ E) (hVW : ¬ IsEssentiallyDistinct V.carrier W.carrier) :
    W.carrier ⊆ (Kakeya.Tube.dilate V
      (Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E))).carrier := by
  apply Kakeya.Tube.tubeOverlapCoreClose hρ hρ1 V W
  have hvol : volume W.carrier = volume V.carrier :=
    Tube.volume_carrier_eq_volume_carrier W V
  rw [IsEssentiallyDistinct, hvol, max_self] at hVW
  exact lt_of_not_ge hVW

/-- A thin tube contained in the overlap dilate of `V` belongs to one member of the fixed cover
attached to an integer axial slice of `V`.  The two displayed bounds on `z` are retained for the
subsequent bounded-overlap count. -/
theorem exists_axialCover_of_subset_overlapDilate {σ ρ : NNReal}
    (hσ : 0 < σ) (hρ : 0 < ρ)
    (hσρ : 2 * (σ : ℝ) ≤ (ρ : ℝ))
    (hρsmall : 8 * Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) * (ρ : ℝ) ≤ 1)
    (V : Tube ρ E) (U : Tube σ E)
    (hU : U.carrier ⊆ (Kakeya.Tube.dilate V
      (Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E))).carrier) :
    ∃ z : ℤ,
      -((Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) / 2 +
          Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) * (ρ : ℝ)) /
            (ρ : ℝ) + 1) ≤ (z : ℝ) ∧
      (z : ℝ) ≤
        (Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) / 2 +
          Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) * (ρ : ℝ)) /
            (ρ : ℝ) ∧
      ∃ q : Fin (enlargementCoverConstant E (Lambda (Module.finrank ℝ E))),
        U.toConvexSpaceBody ≤ (axialCover hσρ V z q).toConvexSpaceBody := by
  let n : ℕ := Module.finrank ℝ E
  let Cn : ℝ := Kakeya.Tube.tubeOverlapCoreClose.C n
  have hCn : 0 < Cn := by
    exact (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C n).trans_le' zero_le_one
  have hρr : 0 < (ρ : ℝ) := NNReal.coe_pos.mpr hρ
  let Uo : Tube σ E :=
    if 0 ≤ inner ℝ U.direction V.direction then U else U.reverse
  have hUo_carrier : Uo.carrier = U.carrier := by
    dsimp [Uo]
    split_ifs
    · rfl
    · exact U.reverse_carrier
  have hUo_body : Uo.toConvexSpaceBody = U.toConvexSpaceBody := by
    dsimp [Uo]
    split_ifs <;> rfl
  have hUo_oriented : 0 ≤ inner ℝ Uo.direction V.direction := by
    dsimp [Uo]
    split_ifs with h
    · exact h
    · rw [Tube.reverse_direction, inner_neg_left]
      exact neg_nonneg.mpr (le_of_not_ge h)
  have hUo_subset : Uo.carrier ⊆ (Kakeya.Tube.dilate V Cn).carrier := by
    rw [hUo_carrier]
    simpa [Cn, n] using hU
  have hperp :
      ‖Uo.direction - inner ℝ V.direction Uo.direction • V.direction‖
        ≤ 2 * Cn * (ρ : ℝ) :=
    (Tube.parameters_mem_of_subset_dilate_free hCn V Uo hUo_subset).2.2
  have hperp_half :
      ‖Uo.direction - inner ℝ V.direction Uo.direction • V.direction‖ ≤ 1 / 2 := by
    have hs : 8 * Cn * (ρ : ℝ) ≤ 1 := by simpa [Cn, n] using hρsmall
    linarith
  have hVperp :
      ‖V.direction - inner ℝ V.direction V.direction • V.direction‖ ≤ 1 / 2 := by
    simp [V.norm_direction]
  have hV_oriented : 0 ≤ inner ℝ V.direction V.direction := by
    rw [real_inner_self_eq_norm_sq]
    exact sq_nonneg _
  have haxialDirection := Tube.abs_inner_sub_le_norm_perp_sub
    V.norm_direction Uo.norm_direction V.norm_direction hUo_oriented hV_oriented
      hperp_half hVperp
  have hdir : ‖Uo.direction - V.direction‖ ≤ 4 * Cn * (ρ : ℝ) := by
    let p : E := Uo.direction - inner ℝ V.direction Uo.direction • V.direction
    let pV : E := V.direction - inner ℝ V.direction V.direction • V.direction
    have hpV : pV = 0 := by
      dsimp [pV]
      simp [V.norm_direction]
    have hdecomp : Uo.direction - V.direction =
        inner ℝ (Uo.direction - V.direction) V.direction • V.direction + (p - pV) := by
      dsimp [p, pV]
      rw [inner_sub_left]
      rw [real_inner_comm Uo.direction V.direction]
      simp [V.norm_direction]
      module
    calc
      ‖Uo.direction - V.direction‖ ≤
          ‖inner ℝ (Uo.direction - V.direction) V.direction • V.direction‖ + ‖p - pV‖ := by
            calc
              _ = ‖inner ℝ (Uo.direction - V.direction) V.direction • V.direction +
                    (p - pV)‖ := congrArg norm hdecomp
              _ ≤ _ := norm_add_le _ _
      _ = |inner ℝ (Uo.direction - V.direction) V.direction| + ‖p - pV‖ := by
            rw [norm_smul, V.norm_direction, mul_one, Real.norm_eq_abs]
      _ ≤ 2 * ‖p - pV‖ := by linarith
      _ = 2 * ‖Uo.direction - inner ℝ V.direction Uo.direction • V.direction‖ := by
            rw [hpV, sub_zero]
      _ ≤ 4 * Cn * (ρ : ℝ) := by linarith
  have hmid_mem : Uo.midpoint ∈ Uo.carrier := Tube.midpoint_mem_carrier hσ Uo
  have hmid_bounds := Tube.abs_inner_and_perp_le_of_mem_dilate
    (T := V) (c := Cn) hCn (hUo_subset hmid_mem)
  let a : ℝ := inner ℝ (Uo.midpoint - V.center) V.direction
  let A : ℝ := Cn / 2 + Cn * (ρ : ℝ)
  have ha : |a| ≤ A := by simpa [a, A] using hmid_bounds.1
  obtain ⟨z, hzclose, hzlower, hzupper⟩ := exists_floor_mul_close hρr ha
  have hmid : ‖Uo.midpoint - (axialTube V z).midpoint‖ ≤ (Cn + 1) * (ρ : ℝ) := by
    have htrans :
        ‖Uo.midpoint - V.center - a • V.direction‖ ≤ Cn * (ρ : ℝ) := by
      simpa [a, real_inner_comm] using hmid_bounds.2
    have hdecomp : Uo.midpoint - (axialTube V z).midpoint =
        (Uo.midpoint - V.center - a • V.direction) +
          (a - (z : ℝ) * (ρ : ℝ)) • V.direction := by
      rw [axialTube_midpoint]
      module
    calc
      ‖Uo.midpoint - (axialTube V z).midpoint‖ ≤
          ‖Uo.midpoint - V.center - a • V.direction‖ +
            ‖(a - (z : ℝ) * (ρ : ℝ)) • V.direction‖ := by
              rw [hdecomp]
              exact norm_add_le _ _
      _ = ‖Uo.midpoint - V.center - a • V.direction‖ +
            |a - (z : ℝ) * (ρ : ℝ)| := by
              rw [norm_smul, V.norm_direction, mul_one, Real.norm_eq_abs]
      _ ≤ (Cn + 1) * (ρ : ℝ) := by linarith
  have hdir' : ‖Uo.direction - (axialTube V z).direction‖ ≤ 4 * Cn * (ρ : ℝ) := by
    simpa using hdir
  have hσ_le : (σ : ℝ) ≤ (ρ : ℝ) / 2 := by linarith
  have hrescale : Uo.toConvexSpaceBody ≤
      ((axialTube V z).rescale (Lambda n * ρ)).toConvexSpaceBody := by
    apply Tube.tube_le_rescale_of_close Uo (axialTube V z) hmid hdir'
    rw [NNReal.coe_mul, Lambda_coe]
    dsimp [n] at hρsmall ⊢
    have hCn1 : 1 ≤ Cn := le_of_lt (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C n)
    nlinarith
  obtain ⟨q, hq⟩ := axialCover_spec hσρ V z Uo (by simpa [n] using hrescale)
  refine ⟨z, ?_, ?_, q, ?_⟩
  · simpa [A, Cn, n] using hzlower
  · simpa [A, Cn, n] using hzupper
  · simpa [hUo_body] using hq

/-- In the thin, small-parent regime, active parents which fail essential distinctness against a
fixed parent can be classified by an integer axial slice and one member of the fixed finite
cover.  Each class has cardinality at most the leaf-mediated overlap constant. -/
theorem exists_activeConflictClassifier {σ ρ : NNReal}
    (hσ : 0 < σ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hσρ : 2 * (σ : ℝ) ≤ (ρ : ℝ))
    (hρsmall : 8 * Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) * (ρ : ℝ) ≤ 1)
    {ι κ : Type*} [DecidableEq κ] {s : Finset ι} (V : ι → Tube σ E)
    {t : Finset κ} (Vρ : κ → Tube ρ E) (p : ι → κ) {Co : NNReal}
    (hparent : IsParentFamily s V t Vρ p)
    (hoverlap : Tube.HasBoundedOverlap s V t Vρ Co) (k₀ : κ) :
    let bad := (open scoped Classical in t.filter fun k =>
      (fibre s p k).Nonempty ∧
        ¬ IsEssentiallyDistinct (Vρ k₀).carrier (Vρ k).carrier)
    ∃ classify : κ → ℤ × Option
      (Fin (enlargementCoverConstant E (Lambda (Module.finrank ℝ E)))),
      (∀ k ∈ bad, ∃ q,
        classify k = ((classify k).1, some q) ∧
        -((Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) / 2 +
            Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) * (ρ : ℝ)) /
              (ρ : ℝ) + 1) ≤ ((classify k).1 : ℝ) ∧
        ((classify k).1 : ℝ) ≤
          (Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) / 2 +
            Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) * (ρ : ℝ)) /
              (ρ : ℝ) ∧
        ∃ i ∈ s, p i = k ∧
          (V i).toConvexSpaceBody ≤ (Vρ k).toConvexSpaceBody ∧
          (V i).toConvexSpaceBody ≤
            (axialCover hσρ (Vρ k₀) (classify k).1 q).toConvexSpaceBody) ∧
      ∀ z q, (((bad.filter fun k => classify k = (z, some q)).card : ℕ) : NNReal) ≤ Co := by
  classical
  dsimp only
  let bad : Finset κ := t.filter fun k =>
    (fibre s p k).Nonempty ∧
      ¬ IsEssentiallyDistinct (Vρ k₀).carrier (Vρ k).carrier
  let Q := enlargementCoverConstant E (Lambda (Module.finrank ℝ E))
  have hex : ∀ k ∈ bad, ∃ d : ℤ × Fin Q,
      -((Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) / 2 +
          Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) * (ρ : ℝ)) /
            (ρ : ℝ) + 1) ≤ (d.1 : ℝ) ∧
      (d.1 : ℝ) ≤
        (Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) / 2 +
          Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) * (ρ : ℝ)) /
            (ρ : ℝ) ∧
      ∃ i ∈ s, p i = k ∧
        (V i).toConvexSpaceBody ≤ (Vρ k).toConvexSpaceBody ∧
        (V i).toConvexSpaceBody ≤
          (axialCover hσρ (Vρ k₀) d.1 d.2).toConvexSpaceBody := by
    intro k hk
    have hkbad := Finset.mem_filter.mp hk
    obtain ⟨i, hi⟩ := hkbad.2.1
    have his : i ∈ s := (Finset.mem_filter.mp hi).1
    have hpik : p i = k := (Finset.mem_filter.mp hi).2
    have hleafParent : (V i).toConvexSpaceBody ≤ (Vρ k).toConvexSpaceBody := by
      simpa [hpik] using hparent.le_parent i his
    have hparentDilate := subset_overlapDilate_of_not_essDistinct hρ hρ1
      (Vρ k₀) (Vρ k) hkbad.2.2
    have hleafDilate : (V i).carrier ⊆ (Kakeya.Tube.dilate (Vρ k₀)
        (Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E))).carrier :=
      fun x hx => hparentDilate (hleafParent hx)
    obtain ⟨z, hzlower, hzupper, q, hq⟩ :=
      exists_axialCover_of_subset_overlapDilate hσ hρ hσρ hρsmall (Vρ k₀) (V i) hleafDilate
    exact ⟨⟨z, q⟩, hzlower, hzupper, i, his, hpik, hleafParent, hq⟩
  let data : ∀ k, k ∈ bad → ℤ × Fin Q := fun k hk => (hex k hk).choose
  have data_spec : ∀ k (hk : k ∈ bad),
      -((Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) / 2 +
          Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) * (ρ : ℝ)) /
            (ρ : ℝ) + 1) ≤ ((data k hk).1 : ℝ) ∧
      ((data k hk).1 : ℝ) ≤
        (Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) / 2 +
          Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) * (ρ : ℝ)) /
            (ρ : ℝ) ∧
      ∃ i ∈ s, p i = k ∧
        (V i).toConvexSpaceBody ≤ (Vρ k).toConvexSpaceBody ∧
        (V i).toConvexSpaceBody ≤
          (axialCover hσρ (Vρ k₀) (data k hk).1 (data k hk).2).toConvexSpaceBody :=
    fun k hk => (hex k hk).choose_spec
  let classify : κ → ℤ × Option (Fin Q) := fun k =>
    if hk : k ∈ bad then ((data k hk).1, some (data k hk).2) else (0, none)
  refine ⟨classify, ?_, ?_⟩
  · intro k hk
    change k ∈ bad at hk
    have hspec := data_spec k hk
    refine ⟨(data k hk).2, ?_, ?_, ?_, ?_⟩
    · simp [classify, hk]
    · simpa [classify, hk] using hspec.1
    · simpa [classify, hk] using hspec.2.1
    · simpa [classify, hk] using hspec.2.2
  · intro z q
    let r : Finset κ := bad.filter fun k => classify k = (z, some q)
    let counted : Finset κ := t.filter fun k => ∃ i ∈ s,
      (V i).toConvexSpaceBody ≤ (Vρ k).toConvexSpaceBody ∧
      (V i).toConvexSpaceBody ≤ (axialCover hσρ (Vρ k₀) z q).toConvexSpaceBody
    have hrsub : r ⊆ counted := by
      intro k hk
      have hkr := Finset.mem_filter.mp hk
      have hkbad : k ∈ bad := hkr.1
      have hclass : classify k = (z, some q) := hkr.2
      have hspec := data_spec k hkbad
      have hclass' : ((data k hkbad).1, some (data k hkbad).2) = (z, some q) := by
        simpa [classify, hkbad] using hclass
      have hz : (data k hkbad).1 = z := congrArg Prod.fst hclass'
      have hq : (data k hkbad).2 = q := by
        simpa using congrArg Prod.snd hclass'
      rcases hspec.2.2 with ⟨i, his, hpik, hpar, hcover⟩
      refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hkbad).1, i, his, hpar, ?_⟩
      simpa [hz, hq] using hcover
    have hcard : r.card ≤ counted.card := Finset.card_le_card hrsub
    have hcounted : ((counted.card : ℕ) : NNReal) ≤ Co := by
      exact hoverlap (axialCover hσρ (Vρ k₀) z q)
    exact (by exact_mod_cast hcard : ((r.card : ℕ) : NNReal) ≤ counted.card).trans hcounted

/-- Quantitative form of `exists_activeConflictClassifier`: in the thin, small-parent regime the
number of active parents conflicting with one fixed parent is `O(Co / ρ)`. -/
theorem activeConflict_card_real_le_axial {σ ρ : NNReal}
    (hσ : 0 < σ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hσρ : 2 * (σ : ℝ) ≤ (ρ : ℝ))
    (hρsmall : 8 * Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) * (ρ : ℝ) ≤ 1)
    {ι κ : Type*} [DecidableEq κ] {s : Finset ι} (V : ι → Tube σ E)
    {t : Finset κ} (Vρ : κ → Tube ρ E) (p : ι → κ) {Co : NNReal}
    (hparent : IsParentFamily s V t Vρ p)
    (hoverlap : Tube.HasBoundedOverlap s V t Vρ Co) (k₀ : κ) :
    let bad := (open scoped Classical in t.filter fun k =>
      (fibre s p k).Nonempty ∧
        ¬ IsEssentiallyDistinct (Vρ k₀).carrier (Vρ k).carrier)
    (bad.card : ℝ) ≤ (Co : ℝ) *
      (enlargementCoverConstant E (Lambda (Module.finrank ℝ E)) + 1 : ℕ) *
      (2 * ((Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) / 2 +
          Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) * (ρ : ℝ)) /
            (ρ : ℝ)) + 2) := by
  classical
  dsimp only
  let bad : Finset κ := t.filter fun k =>
    (fibre s p k).Nonempty ∧
      ¬ IsEssentiallyDistinct (Vρ k₀).carrier (Vρ k).carrier
  let Q := enlargementCoverConstant E (Lambda (Module.finrank ℝ E))
  obtain ⟨classify, hspec, hclass⟩ := exists_activeConflictClassifier
    hσ hρ hρ1 hσρ hρsmall V Vρ p hparent hoverlap k₀
  let classes : Finset (ℤ × Option (Fin Q)) := bad.image classify
  have hbad_classes : (bad.card : ℝ) ≤ (classes.card : ℝ) * (Co : ℝ) := by
    rw [Finset.card_eq_sum_card_image classify bad, Nat.cast_sum]
    calc
      ∑ c ∈ classes, ((bad.filter fun k => classify k = c).card : ℝ) ≤
          ∑ _c ∈ classes, (Co : ℝ) := by
            apply Finset.sum_le_sum
            intro c hc
            obtain ⟨k, hkbad, rfl⟩ := Finset.mem_image.mp hc
            obtain ⟨q, hcq, _hzlo, _hzhi, _hi⟩ := hspec k (by simpa [bad] using hkbad)
            have hbucket := hclass (classify k).1 q
            change (((bad.filter fun l => classify l = ((classify k).1, some q)).card : ℕ) : NNReal)
              ≤ Co at hbucket
            have hfilter : (bad.filter fun l => classify l = classify k) =
                bad.filter fun l => classify l = ((classify k).1, some q) := by
              apply Finset.filter_congr
              intro l _hl
              exact iff_of_eq (congrArg (fun c => classify l = c) hcq)
            have hbucket' : (((bad.filter fun l => classify l = classify k).card : ℕ) : NNReal)
                ≤ Co := by rw [hfilter]; exact hbucket
            exact_mod_cast hbucket'
      _ = (classes.card : ℝ) * (Co : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
  let zset : Finset ℝ := bad.image fun k => ((classify k).1 : ℝ)
  let A : ℝ :=
    (Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) / 2 +
      Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) * (ρ : ℝ)) / (ρ : ℝ)
  have hzsub : ∀ x ∈ zset, x ∈ Set.Icc (-(A + 1)) A := by
    intro x hx
    obtain ⟨k, hkbad, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨q, _hcq, hzlo, hzhi, _hi⟩ := hspec k (by simpa [bad] using hkbad)
    simpa [A] using And.intro hzlo hzhi
  have hzsep : (zset : Set ℝ).Pairwise (fun x y => 1 ≤ |x - y|) := by
    intro x hx y hy hxy
    obtain ⟨k, hkbad, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨l, hlbad, rfl⟩ := Finset.mem_image.mp hy
    let z : ℤ := (classify k).1
    let w : ℤ := (classify l).1
    have hzw : z ≠ w := by
      intro heq
      apply hxy
      exact_mod_cast heq
    rcases lt_or_gt_of_ne hzw with hlt | hgt
    · have hstep : z + 1 ≤ w := (Int.add_one_le_iff).2 hlt
      have hstepR : (z : ℝ) + 1 ≤ (w : ℝ) := by exact_mod_cast hstep
      have hleR : (z : ℝ) ≤ (w : ℝ) := by exact_mod_cast hlt.le
      rw [abs_of_nonpos (sub_nonpos.mpr hleR)]
      linarith
    · have hstep : w + 1 ≤ z := (Int.add_one_le_iff).2 hgt
      have hstepR : (w : ℝ) + 1 ≤ (z : ℝ) := by exact_mod_cast hstep
      have hleR : (w : ℝ) ≤ (z : ℝ) := by exact_mod_cast hgt.le
      rw [abs_of_nonneg (sub_nonneg.mpr hleR)]
      linarith
  have hzcard : (zset.card : ℝ) ≤ 2 * A + 2 := by
    have h := card_le_of_pairwise_le_subset_Icc (s := zset) (a := -(A + 1)) (b := A)
      (by norm_num : (0 : ℝ) < 1) (by
        have hA0 : 0 ≤ A := by
          dsimp [A]
          have hC0 : 0 ≤ Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) :=
            le_trans zero_le_one
              (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C (Module.finrank ℝ E)).le
          have hρ0 : 0 ≤ (ρ : ℝ) := NNReal.coe_nonneg ρ
          exact div_nonneg (add_nonneg (div_nonneg hC0 (by norm_num)) (mul_nonneg hC0 hρ0)) hρ0
        linarith) hzsub hzsep
    calc
      (zset.card : ℝ) ≤ (A - -(A + 1)) / 1 + 1 := h
      _ = 2 * A + 2 := by ring
  let castClass : ℤ × Option (Fin Q) → ℝ × Option (Fin Q) :=
    fun c => ((c.1 : ℝ), c.2)
  have hcastClass : Function.Injective castClass := by
    intro c d hcd
    change ((c.1 : ℝ), c.2) = ((d.1 : ℝ), d.2) at hcd
    apply Prod.ext
    · have hfirst : (c.1 : ℝ) = (d.1 : ℝ) := congrArg Prod.fst hcd
      exact_mod_cast hfirst
    · exact congrArg (fun x : ℝ × Option (Fin Q) => x.2) hcd
  let realClasses : Finset (ℝ × Option (Fin Q)) := classes.image castClass
  have hrealClasses_card : realClasses.card = classes.card :=
    Finset.card_image_of_injective classes hcastClass
  have hrealClasses_sub : realClasses ⊆ zset.product Finset.univ := by
    intro c hc
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨k, hkbad, hkd⟩ := Finset.mem_image.mp hd
    subst d
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨k, hkbad, rfl⟩, Finset.mem_univ _⟩
  have hclasses_card : (classes.card : ℝ) ≤ (zset.card : ℝ) * (Q + 1 : ℕ) := by
    have hc := Finset.card_le_card hrealClasses_sub
    have hc' : realClasses.card ≤ zset.card * (Q + 1) := by simpa using hc
    rw [hrealClasses_card] at hc'
    exact_mod_cast hc'
  calc
    (bad.card : ℝ) ≤ (classes.card : ℝ) * (Co : ℝ) := hbad_classes
    _ ≤ ((zset.card : ℝ) * (Q + 1 : ℕ)) * (Co : ℝ) := by
      gcongr
    _ ≤ ((2 * A + 2) * (Q + 1 : ℕ)) * (Co : ℝ) := by
      gcongr
    _ = (Co : ℝ) * (Q + 1 : ℕ) * (2 * A + 2) := by ring
    _ = (Co : ℝ) *
        (enlargementCoverConstant E (Lambda (Module.finrank ℝ E)) + 1 : ℕ) *
        (2 * ((Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) / 2 +
          Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) * (ρ : ℝ)) /
            (ρ : ℝ)) + 2) := by rfl

/-- The axial conflict count with its scale dependence compressed into the dimensional constant
`parentConflictCover.C E`. -/
theorem activeConflict_card_real_le_const_mul_inv {σ ρ : NNReal}
    (hσ : 0 < σ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hσρ : 2 * (σ : ℝ) ≤ (ρ : ℝ))
    (hρsmall : 8 * Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) * (ρ : ℝ) ≤ 1)
    {ι κ : Type*} [DecidableEq κ] {s : Finset ι} (V : ι → Tube σ E)
    {t : Finset κ} (Vρ : κ → Tube ρ E) (p : ι → κ) {Co : NNReal}
    (hparent : IsParentFamily s V t Vρ p)
    (hoverlap : Tube.HasBoundedOverlap s V t Vρ Co) (k₀ : κ) :
    let bad := (open scoped Classical in t.filter fun k =>
      (fibre s p k).Nonempty ∧
        ¬ IsEssentiallyDistinct (Vρ k₀).carrier (Vρ k).carrier)
    (bad.card : ℝ) ≤ (Co : ℝ) * (C E : ℝ) / (ρ : ℝ) := by
  classical
  dsimp only
  let bad : Finset κ := t.filter fun k =>
    (fibre s p k).Nonempty ∧
      ¬ IsEssentiallyDistinct (Vρ k₀).carrier (Vρ k).carrier
  have hraw := activeConflict_card_real_le_axial
    hσ hρ hρ1 hσρ hρsmall V Vρ p hparent hoverlap k₀
  change (bad.card : ℝ) ≤ _ at hraw
  let Cn : ℝ := Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E)
  let Q : ℝ := (enlargementCoverConstant E (Lambda (Module.finrank ℝ E)) + 1 : ℕ)
  have hρr : 0 < (ρ : ℝ) := NNReal.coe_pos.mpr hρ
  have hρr1 : (ρ : ℝ) ≤ 1 := NNReal.coe_le_coe.mpr hρ1
  have hCn0 : 0 ≤ Cn := by
    exact le_trans zero_le_one
      (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C (Module.finrank ℝ E)).le
  have hQ0 : 0 ≤ Q := by positivity
  have hbracket :
      2 * ((Cn / 2 + Cn * (ρ : ℝ)) / (ρ : ℝ)) + 2 ≤
        (3 * Cn + 2) / (ρ : ℝ) := by
    apply (le_div_iff₀ hρr).2
    field_simp [hρr.ne']
    nlinarith
  calc
    (bad.card : ℝ) ≤ (Co : ℝ) * Q *
        (2 * ((Cn / 2 + Cn * (ρ : ℝ)) / (ρ : ℝ)) + 2) := by
          simpa [bad, Q, Cn] using hraw
    _ ≤ (Co : ℝ) * Q * ((3 * Cn + 2) / (ρ : ℝ)) := by
          gcongr
    _ = (Co : ℝ) * (C E : ℝ) / (ρ : ℝ) := by
          rw [C_coe]
          dsimp [Q, Cn]
          ring

/-- When the leaf and parent scales are comparable, pairwise essential distinctness of the leaves
itself gives a constant bound for the active parent-conflict degree. -/
theorem activeConflict_card_le_comparable {σ ρ : NNReal}
    (hσ : 0 < σ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hσρ : σ ≤ ρ) (hρσ : (ρ : ℝ) < 2 * (σ : ℝ))
    {ι κ : Type*} [DecidableEq κ] {s : Finset ι} (V : ι → Tube σ E)
    {t : Finset κ} (Vρ : κ → Tube ρ E) (p : ι → κ)
    (hED : (s : Set ι).Pairwise fun i j =>
      IsEssentiallyDistinct (V i).carrier (V j).carrier)
    (hparent : IsParentFamily s V t Vρ p) (k₀ : κ) :
    let bad := (open scoped Classical in t.filter fun k =>
      (fibre s p k).Nonempty ∧
        ¬ IsEssentiallyDistinct (Vρ k₀).carrier (Vρ k).carrier)
    (bad.card : ENNReal) ≤
      (Tube.comparableReplacement.C (Module.finrank ℝ E) 2 : ENNReal) := by
  classical
  dsimp only
  let bad : Finset κ := t.filter fun k =>
    (fibre s p k).Nonempty ∧
      ¬ IsEssentiallyDistinct (Vρ k₀).carrier (Vρ k).carrier
  by_cases hbad : bad.Nonempty
  · obtain ⟨kbase, hkbase⟩ := hbad
    have hexrep : ∀ k ∈ bad, ∃ i ∈ s, p i = k := by
      intro k hk
      obtain ⟨i, hi⟩ := (Finset.mem_filter.mp hk).2.1
      exact ⟨i, (Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2⟩
    obtain ⟨ibase, hibases, hpibase⟩ := hexrep kbase hkbase
    let rep : κ → ι := fun k =>
      if hk : k ∈ bad then (hexrep k hk).choose else ibase
    have hreps : ∀ k ∈ bad, rep k ∈ s := by
      intro k hk
      simpa [rep, hk] using (hexrep k hk).choose_spec.1
    have hprepk : ∀ k ∈ bad, p (rep k) = k := by
      intro k hk
      simpa [rep, hk] using (hexrep k hk).choose_spec.2
    have hrepinj : Set.InjOn rep ↑bad := by
      intro k hk l hl hkl
      rw [← hprepk k hk, ← hprepk l hl, hkl]
    let R : NNReal := σ⁻¹ * ρ
    have hσr : 0 < (σ : ℝ) := NNReal.coe_pos.mpr hσ
    have hρr : 0 < (ρ : ℝ) := NNReal.coe_pos.mpr hρ
    have hR1 : 1 ≤ R := by
      rw [← NNReal.coe_le_coe]
      dsimp [R]
      rw [← div_eq_inv_mul, le_div_iff₀ hσr]
      simpa using NNReal.coe_le_coe.mpr hσρ
    have hR2 : R ≤ 2 := by
      rw [← NNReal.coe_le_coe]
      dsimp [R]
      rw [← div_eq_inv_mul, div_le_iff₀ hσr]
      exact hρσ.le
    have hscale : R⁻¹ * ρ = σ := by
      apply NNReal.eq
      push_cast
      dsimp [R]
      field_simp
    let U : κ → Tube (R⁻¹ * ρ) E := fun k =>
      Tube.mk' (R⁻¹ * ρ) (V (rep k)).dist_eq_one
    have hUcarrier : ∀ k, (U k).carrier = (V (rep k)).carrier := by
      intro k
      rw [Tube.carrier_eq, Tube.carrier_eq]
      simpa [U] using congrArg (fun r : NNReal =>
        ⋃ z ∈ segment ℝ (V (rep k)).x (V (rep k)).y, Metric.closedBall z r) hscale
    have hUED : (bad : Set κ).Pairwise fun k l =>
        IsEssentiallyDistinct (U k).carrier (U l).carrier := by
      intro k hk l hl hkl
      rw [hUcarrier, hUcarrier]
      have hne : rep k ≠ rep l := fun heq => hkl (hrepinj hk hl heq)
      exact hED (hreps k hk) (hreps l hl) hne
    have hUV : ∀ k ∈ bad, (U k).carrier ⊆ (Kakeya.Tube.dilate (Vρ k₀)
        (Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E))).carrier := by
      intro k hk
      rw [hUcarrier]
      have hleafParent : (V (rep k)).toConvexSpaceBody ≤ (Vρ k).toConvexSpaceBody := by
        simpa [hprepk k hk] using hparent.le_parent (rep k) (hreps k hk)
      have hparentDilate := subset_overlapDilate_of_not_essDistinct hρ hρ1
        (Vρ k₀) (Vρ k) (Finset.mem_filter.mp hk).2.2
      exact fun x hx => hparentDilate (hleafParent hx)
    have hpack := Tube.essDistinctTubesInDilate hR1 hρ hρ1 (Vρ k₀) bad U hUED hUV
    have hmono : Tube.comparableReplacement.C (Module.finrank ℝ E) R ≤
        Tube.comparableReplacement.C (Module.finrank ℝ E) 2 := by
      unfold Tube.comparableReplacement.C
      gcongr
    exact hpack.trans (by exact_mod_cast hmono)
  · simp [bad, Finset.not_nonempty_iff_eq_empty.mp hbad]

/-- The global bounded-overlap parent count also bounds every active conflict set.  This is used
when the parent scale has a fixed dimensional lower bound, where its `ρ⁻⁵` loss is constant. -/
theorem activeConflict_card_le_global (hdim : Module.finrank ℝ E = 3)
    {σ ρ : NNReal} (hσ : 0 < σ) (hρ1 : ρ ≤ 1) (hσρ : 2 * σ ≤ ρ)
    {ι κ : Type*} [DecidableEq κ] {s : Finset ι} (V : ι → Tube σ E)
    {t : Finset κ} (Vρ : κ → Tube ρ E) (p : ι → κ) {Co : NNReal}
    (hball : ∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1)
    (hparent : IsParentFamily s V t Vρ p)
    (hoverlap : Tube.HasBoundedOverlap s V t Vρ Co) (k₀ : κ) :
    let bad := (open scoped Classical in t.filter fun k =>
      (fibre s p k).Nonempty ∧
        ¬ IsEssentiallyDistinct (Vρ k₀).carrier (Vρ k).carrier)
    (bad.card : ENNReal) ≤
      (Co : ENNReal) * (parentCount.C : ENNReal) * (ρ : ENNReal) ^ (-5 : ℝ) := by
  classical
  dsimp only
  let active : Finset κ := t.filter fun k => (fibre s p k).Nonempty
  let bad : Finset κ := active.filter fun k =>
    ¬ IsEssentiallyDistinct (Vρ k₀).carrier (Vρ k).carrier
  have hactive_sub : active ⊆ t := Finset.filter_subset _ _
  have hoverActive : Tube.HasBoundedOverlap s V active Vρ Co := by
    intro W
    refine le_trans ?_ (hoverlap W)
    have hn : (active.filter fun k => ∃ i ∈ s,
        (V i).toConvexSpaceBody ≤ (Vρ k).toConvexSpaceBody ∧
        (V i).toConvexSpaceBody ≤ W.toConvexSpaceBody).card ≤
        (t.filter fun k => ∃ i ∈ s,
          (V i).toConvexSpaceBody ≤ (Vρ k).toConvexSpaceBody ∧
          (V i).toConvexSpaceBody ≤ W.toConvexSpaceBody).card := by
      apply Finset.card_le_card
      intro k hk
      exact Finset.mem_filter.mpr
        ⟨hactive_sub (Finset.mem_filter.mp hk).1, (Finset.mem_filter.mp hk).2⟩
    exact_mod_cast hn
  have hactive_parent : ∀ k ∈ active, ∃ i ∈ s,
      (V i).toConvexSpaceBody ≤ (Vρ k).toConvexSpaceBody := by
    intro k hk
    obtain ⟨i, hi⟩ := (Finset.mem_filter.mp hk).2
    have his : i ∈ s := (Finset.mem_filter.mp hi).1
    have hpik : p i = k := (Finset.mem_filter.mp hi).2
    exact ⟨i, his, by simpa [hpik] using hparent.le_parent i his⟩
  have hcount := card_parents_le_of_hasBoundedOverlap hdim hσ hρ1 hσρ
    hball hoverActive hactive_parent
  have hbadsub : bad ⊆ active := Finset.filter_subset _ _
  have hbadcard : (bad.card : ENNReal) ≤ active.card := by
    exact_mod_cast Finset.card_le_card hbadsub
  have hbad_eq : bad = t.filter fun k =>
      (fibre s p k).Nonempty ∧
        ¬ IsEssentiallyDistinct (Vρ k₀).carrier (Vρ k).carrier := by
    ext k
    simp only [bad, active, Finset.mem_filter]
    tauto
  rw [← hbad_eq]
  exact hbadcard.trans hcount

/-- Uniform body-level conflict count obtained by combining the comparable-scale packing, the
small-scale axial slicing, and the fixed-lower-scale global parent count. -/
theorem activeConflict_card_real_le (hdim : Module.finrank ℝ E = 3)
    {σ ρ : NNReal} (hσ : 0 < σ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hσρ : σ ≤ ρ)
    {ι κ : Type*} [DecidableEq κ] {s : Finset ι} (V : ι → Tube σ E)
    {t : Finset κ} (Vρ : κ → Tube ρ E) (p : ι → κ) {Co : NNReal} (hCo : 1 ≤ Co)
    (hball : ∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1)
    (hED : (s : Set ι).Pairwise fun i j =>
      IsEssentiallyDistinct (V i).carrier (V j).carrier)
    (hparent : IsParentFamily s V t Vρ p)
    (hoverlap : Tube.HasBoundedOverlap s V t Vρ Co) (k₀ : κ) :
    let bad := (open scoped Classical in t.filter fun k =>
      (fibre s p k).Nonempty ∧
        ¬ IsEssentiallyDistinct (Vρ k₀).carrier (Vρ k).carrier)
    (bad.card : ℝ) ≤ (Co : ℝ) * (degreeC E : ℝ) / (ρ : ℝ) := by
  classical
  dsimp only
  let bad : Finset κ := t.filter fun k =>
    (fibre s p k).Nonempty ∧
      ¬ IsEssentiallyDistinct (Vρ k₀).carrier (Vρ k).carrier
  have hρr : 0 < (ρ : ℝ) := NNReal.coe_pos.mpr hρ
  have hρr1 : (ρ : ℝ) ≤ 1 := NNReal.coe_le_coe.mpr hρ1
  have hCoR : 1 ≤ (Co : ℝ) := NNReal.coe_le_coe.mpr hCo
  have hdeg0 : 0 ≤ (degreeC E : ℝ) := NNReal.coe_nonneg _
  by_cases hthin : 2 * (σ : ℝ) ≤ (ρ : ℝ)
  · have hthinNN : 2 * σ ≤ ρ := by exact_mod_cast hthin
    by_cases hsmall : 8 * Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) *
        (ρ : ℝ) ≤ 1
    · have haxial := activeConflict_card_real_le_const_mul_inv
        hσ hρ hρ1 hthin hsmall V Vρ p hparent hoverlap k₀
      change (bad.card : ℝ) ≤ _ at haxial
      calc
        (bad.card : ℝ) ≤ (Co : ℝ) * (C E : ℝ) / (ρ : ℝ) := haxial
        _ ≤ (Co : ℝ) * (degreeC E : ℝ) / (ρ : ℝ) := by
          gcongr
          exact_mod_cast axial_le_degreeC (E := E)
    · have hglobal := activeConflict_card_le_global hdim hσ hρ1 hthinNN
        V Vρ p hball hparent hoverlap k₀
      change (bad.card : ENNReal) ≤ _ at hglobal
      have htop : (Co : ENNReal) * (parentCount.C : ENNReal) *
          (ρ : ENNReal) ^ (-5 : ℝ) ≠ ⊤ := by finiteness
      have hglobalToReal := ENNReal.toReal_mono htop hglobal
      have hglobalR : (bad.card : ℝ) ≤
          (Co : ℝ) * (parentCount.C : ℝ) * (ρ : ℝ) ^ (-5 : ℝ) := by
        calc
          (bad.card : ℝ) = ((bad.card : ENNReal)).toReal := by simp
          _ ≤ ((Co : ENNReal) * (parentCount.C : ENNReal) *
              (ρ : ENNReal) ^ (-5 : ℝ)).toReal := hglobalToReal
          _ = (Co : ℝ) * (parentCount.C : ℝ) * (ρ : ℝ) ^ (-5 : ℝ) := by
            rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ← ENNReal.toReal_rpow]
            simp
      let K : ℝ := 8 * Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E)
      have hK0 : 0 ≤ K := by
        dsimp [K]
        exact mul_nonneg (by norm_num) (le_trans zero_le_one
          (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C (Module.finrank ℝ E)).le)
      have hlarge : 1 < K * (ρ : ℝ) := by
        exact lt_of_not_ge (by simpa [K] using hsmall)
      have hinv : (ρ : ℝ)⁻¹ ≤ K := by
        calc
          (ρ : ℝ)⁻¹ = 1 * (ρ : ℝ)⁻¹ := by ring
          _ ≤ (K * (ρ : ℝ)) * (ρ : ℝ)⁻¹ :=
            mul_le_mul_of_nonneg_right hlarge.le (inv_nonneg.mpr hρr.le)
          _ = K := by field_simp
      have hpow4 : ((ρ : ℝ)⁻¹) ^ 4 ≤ K ^ 4 := by
        exact pow_le_pow_left₀ (inv_nonneg.mpr hρr.le) hinv 4
      have hrpow : (ρ : ℝ) ^ (-5 : ℝ) = ((ρ : ℝ)⁻¹) ^ 5 := by
        rw [Real.rpow_neg hρr.le]
        norm_num [Real.rpow_natCast, inv_pow]
      have hrpow_le : (ρ : ℝ) ^ (-5 : ℝ) ≤ K ^ 4 / (ρ : ℝ) := by
        rw [hrpow, div_eq_mul_inv]
        calc
          ((ρ : ℝ)⁻¹) ^ 5 = ((ρ : ℝ)⁻¹) ^ 4 * (ρ : ℝ)⁻¹ := by ring
          _ ≤ K ^ 4 * (ρ : ℝ)⁻¹ :=
            mul_le_mul_of_nonneg_right hpow4 (inv_nonneg.mpr hρr.le)
      calc
        (bad.card : ℝ) ≤ (Co : ℝ) * (parentCount.C : ℝ) *
            (ρ : ℝ) ^ (-5 : ℝ) := hglobalR
        _ ≤ (Co : ℝ) * (parentCount.C : ℝ) * (K ^ 4 / (ρ : ℝ)) := by
          gcongr
        _ = (Co : ℝ) * (largeScaleC E : ℝ) / (ρ : ℝ) := by
          unfold largeScaleC
          push_cast
          rw [Real.coe_toNNReal _ (le_trans zero_le_one
            (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C (Module.finrank ℝ E)).le)]
          dsimp [K]
          ring
        _ ≤ (Co : ℝ) * (degreeC E : ℝ) / (ρ : ℝ) := by
          gcongr
          exact_mod_cast largeScale_le_degreeC (E := E)
  · have hcomparable := activeConflict_card_le_comparable hσ hρ hρ1 hσρ
        (lt_of_not_ge hthin) V Vρ p hED hparent k₀
    change (bad.card : ENNReal) ≤ _ at hcomparable
    have hcompR : (bad.card : ℝ) ≤
        (Tube.comparableReplacement.C (Module.finrank ℝ E) 2 : ℝ) := by
      exact_mod_cast hcomparable
    calc
      (bad.card : ℝ) ≤
          (Tube.comparableReplacement.C (Module.finrank ℝ E) 2 : ℝ) := hcompR
      _ ≤ (degreeC E : ℝ) := by exact_mod_cast comparable_le_degreeC (E := E)
      _ ≤ (Co : ℝ) * (degreeC E : ℝ) / (ρ : ℝ) := by
        apply (le_div_iff₀ hρr).2
        calc
          (degreeC E : ℝ) * (ρ : ℝ) ≤ (degreeC E : ℝ) * 1 := by gcongr
          _ ≤ (Co : ℝ) * (degreeC E : ℝ) := by nlinarith

/-- Integer multiplicity corresponding to the uniform body-conflict count. -/
noncomputable def degreeM (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [ProperSpace E] (Co ρ : NNReal) : ℕ :=
  Nat.ceil ((Co : ℝ) * (degreeC E : ℝ) / (ρ : ℝ))

/-- Active parents are essentially distinct up to the explicit multiplicity `degreeM E Co ρ`.
Unlike `Tube.HasBoundedOverlap`, this is the body-level statement consumed by weighted greedy
selection. -/
theorem activeParents_isEDUpToMult (hdim : Module.finrank ℝ E = 3)
    {σ ρ : NNReal} (hσ : 0 < σ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hσρ : σ ≤ ρ)
    {ι κ : Type*} [DecidableEq κ] {s : Finset ι} (V : ι → Tube σ E)
    {t : Finset κ} (Vρ : κ → Tube ρ E) (p : ι → κ) {Co : NNReal} (hCo : 1 ≤ Co)
    (hball : ∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1)
    (hED : (s : Set ι).Pairwise fun i j =>
      IsEssentiallyDistinct (V i).carrier (V j).carrier)
    (hparent : IsParentFamily s V t Vρ p)
    (hoverlap : Tube.HasBoundedOverlap s V t Vρ Co) :
    let active := (open scoped Classical in t.filter fun k => (fibre s p k).Nonempty)
    IsEDUpToMult active (fun k => (Vρ k).carrier) (degreeM E Co ρ) := by
  classical
  dsimp only
  let active : Finset κ := t.filter fun k => (fibre s p k).Nonempty
  unfold IsEDUpToMult
  intro k hk
  have hcount := activeConflict_card_real_le hdim hσ hρ hρ1 hσρ V Vρ p hCo
    hball hED hparent hoverlap k
  let bad : Finset κ := t.filter fun l =>
    (fibre s p l).Nonempty ∧
      ¬ IsEssentiallyDistinct (Vρ k).carrier (Vρ l).carrier
  change (bad.card : ℝ) ≤ _ at hcount
  have heq : notEssDistinctSet active (fun l => (Vρ l).carrier) (Vρ k).carrier = bad := by
    ext l
    simp only [notEssDistinctSet, active, bad, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hlt, hnonempty⟩, hnot⟩
      exact ⟨hlt, hnonempty, fun hkl => hnot (isEssentiallyDistinct_symm hkl)⟩
    · rintro ⟨hlt, hnonempty, hnot⟩
      exact ⟨⟨hlt, hnonempty⟩, fun hlk => hnot (isEssentiallyDistinct_symm hlk)⟩
  rw [heq]
  unfold degreeM
  exact_mod_cast hcount.trans (Nat.le_ceil _)

/-- Small dimensional constant converting the honest greedy retention `ρ / (Co · degreeC E)`
into the scale hypothesis used by the Section 8 repair. -/
noncomputable def selectionC (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [ProperSpace E] : NNReal :=
  (3 * degreeC E)⁻¹

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
theorem selectionC_pos : 0 < selectionC E := by
  unfold selectionC
  positivity [degreeC_pos (E := E)]

/-- Essentially distinct parent selection from the actual leaf-mediated bounded-overlap
hypothesis.  The geometric work is `activeParents_isEDUpToMult`; the remainder is weighted greedy
selection and fibre bookkeeping. -/
theorem exists_essDistinct_parentFamily_of_boundedOverlap
    (hdim : Module.finrank ℝ E = 3) :
    ∃ c : NNReal, 0 < c ∧
    ∀ {ε' : ℝ}, 0 < ε' → ∀ {Co : NNReal}, 1 ≤ Co →
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0, ∀ σ ρ : NNReal, δ ≤ σ → σ ≤ ρ → ρ ≤ 1 →
      (δ : ℝ) ^ ε' ≤ (c : ℝ) * ρ / Co →
      ∀ {ι κ : Type*} [DecidableEq κ] {s : Finset ι} {t : Finset κ}
        (V : ι → ShadedTube σ E) (Vρ : κ → Tube ρ E) (p : ι → κ) (w : ι → ENNReal),
        (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1) →
        (s : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (V i).carrier (V j).carrier) →
        IsParentFamily s (fun i => (V i).toTube) t Vρ p →
        Tube.HasBoundedOverlap s (fun i => (V i).toTube) t Vρ Co →
        ∃ s' ⊆ s, ∃ t' ⊆ t,
          IsParentFamily s' (fun i => (V i).toTube) t' Vρ p ∧
          (t' : Set κ).Pairwise
            (fun k l => IsEssentiallyDistinct (Vρ k).carrier (Vρ l).carrier) ∧
          (δ : ENNReal) ^ ε' * (∑ i ∈ s, w i) ≤ ∑ i ∈ s', w i ∧
          ∀ k ∈ t', ∀ K : ConvexSpaceBody E,
            (∀ i ∈ fibre s p k, (V i).toConvexSpaceBody ≤ K) →
            frostmanConstIn (fibre s' p k) (fun i => (V i).toConvexSpaceBody) K
              ≤ (δ : ENNReal) ^ (-ε')
                * frostmanConstIn (fibre s p k) (fun i => (V i).toConvexSpaceBody) K := by
  refine ⟨selectionC E, selectionC_pos (E := E), ?_⟩
  intro ε' hε' Co hCo
  filter_upwards [self_mem_nhdsWithin] with δ hδ0
  intro σ ρ hδσ hσρ hρ1 hscale ι κ _inst s t V Vρ p w hball hED hparent hoverlap
  classical
  have hδ : 0 < δ := hδ0
  have hσ : 0 < σ := hδ.trans_le hδσ
  have hρ : 0 < ρ := hσ.trans_le hσρ
  have hδ1 : δ ≤ 1 := hδσ.trans (hσρ.trans hρ1)
  have hδne : (δ : ENNReal) ≠ 0 := by simpa using hδ.ne'
  have hδtop : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  let active : Finset κ := t.filter fun k => (fibre s p k).Nonempty
  let M : ℕ := degreeM E Co ρ
  have hactiveED : IsEDUpToMult active (fun k => (Vρ k).carrier) M := by
    simpa [active, M] using activeParents_isEDUpToMult hdim hσ hρ hρ1 hσρ
      (fun i => (V i).toTube) Vρ p hCo hball hED hparent hoverlap
  have hactive_sub : active ⊆ t := Finset.filter_subset _ _
  have hpactive : ∀ i ∈ s, p i ∈ active := by
    intro i hi
    refine Finset.mem_filter.mpr ⟨hparent.mapsTo i hi, ?_⟩
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, rfl⟩⟩
  obtain ⟨t', ht'active, ht'pw, ht'wt⟩ :=
    exists_pairwise_notRel_weighted
      (Rel := fun k l => ¬ IsEssentiallyDistinct (Vρ k).carrier (Vρ l).carrier)
      (fun a b hab hba => hab (isEssentiallyDistinct_symm hba))
      (wt := fun k => ∑ i ∈ fibre s p k, w i) M active
      (fun k' hk' u hu hRel => by
        refine le_trans (Finset.card_le_card ?_) (hactiveED k' hk')
        intro k hk
        simp only [notEssDistinctSet, Finset.mem_filter]
        exact ⟨hu hk, hRel k hk⟩)
  let X : ℝ := (Co : ℝ) * (degreeC E : ℝ) / (ρ : ℝ)
  have hX0 : 0 ≤ X := by dsimp [X]; positivity
  have hdeg1 : 1 ≤ (degreeC E : ℝ) := by
    have hdegree := comparable_le_degreeC (E := E)
    exact_mod_cast (Tube.comparableReplacement.one_le_C (Module.finrank ℝ E) 2 |>.trans hdegree)
  have hX1 : 1 ≤ X := by
    apply (le_div_iff₀ (NNReal.coe_pos.mpr hρ)).2
    calc
      (1 : ℝ) * (ρ : ℝ) ≤ 1 := by simpa using NNReal.coe_le_coe.mpr hρ1
      _ ≤ (Co : ℝ) * (degreeC E : ℝ) := by nlinarith [NNReal.coe_le_coe.mpr hCo]
  have hMreal : (M : ℝ) + 1 ≤ 3 * X := by
    have hceil : (M : ℝ) < X + 1 := by
      simpa [M, degreeM, X] using Nat.ceil_lt_add_one hX0
    linarith
  have hscale' : (δ : ℝ) ^ ε' ≤ (ρ : ℝ) /
      (3 * (degreeC E : ℝ) * (Co : ℝ)) := by
    calc
      (δ : ℝ) ^ ε' ≤ (selectionC E : ℝ) * (ρ : ℝ) / (Co : ℝ) := hscale
      _ = (ρ : ℝ) / (3 * (degreeC E : ℝ) * (Co : ℝ)) := by
        unfold selectionC
        push_cast
        field_simp
  have hprodR : (δ : ℝ) ^ ε' * ((M : ℝ) + 1) ≤ 1 := by
    calc
      (δ : ℝ) ^ ε' * ((M : ℝ) + 1) ≤
          ((ρ : ℝ) / (3 * (degreeC E : ℝ) * (Co : ℝ))) * (3 * X) := by
            gcongr
      _ = 1 := by
        dsimp [X]
        field_simp
  have hprodE : (δ : ENNReal) ^ ε' * ((M : ENNReal) + 1) ≤ 1 := by
    apply (ENNReal.toReal_le_toReal (by finiteness) (by simp)).mp
    rw [ENNReal.toReal_mul, ennreal_coe_nnreal_rpow_toReal (NNReal.coe_pos.mpr hδ)]
    rw [ENNReal.toReal_add (by simp) (by simp)]
    simpa using hprodR
  have hone : (1 : ENNReal) ≤ (δ : ENNReal) ^ (-ε') := by
    rw [ENNReal.rpow_neg]
    refine ENNReal.le_inv_iff_mul_le.mpr ?_
    rw [one_mul]
    calc
      (δ : ENNReal) ^ ε' ≤ (1 : ENNReal) ^ ε' := by
        gcongr
        exact_mod_cast hδ1
      _ = 1 := ENNReal.one_rpow _
  set s' : Finset ι := {i ∈ s | p i ∈ t'} with hs'
  have hmaps : ∀ i ∈ s', p i ∈ t' := fun i hi => (Finset.mem_filter.mp hi).2
  have hfibre : ∀ k ∈ t', fibre s' p k = fibre s p k := by
    intro k hk
    ext i
    simp only [hs', fibre, Finset.mem_filter]
    constructor
    · exact fun h => ⟨h.1.1, h.2⟩
    · exact fun h => ⟨⟨h.1, h.2 ▸ hk⟩, h.2⟩
  refine ⟨s', Finset.filter_subset _ _, t', ht'active.trans hactive_sub, ?_, ?_, ?_, ?_⟩
  · exact
      { mapsTo := hmaps
        injOn := fun a ha b hb hab => hparent.injOn (hactive_sub (ht'active ha))
          (hactive_sub (ht'active hb)) hab
        le_parent := fun i hi => hparent.le_parent i (Finset.mem_filter.mp hi).1 }
  · intro a ha b hb hab
    exact not_not.mp (ht'pw ha hb hab)
  · have hsum_active : ∑ k ∈ active, (∑ i ∈ fibre s p k, w i) = ∑ i ∈ s, w i :=
      Finset.sum_fiberwise_of_maps_to hpactive w
    have hsum_t' : ∑ k ∈ t', (∑ i ∈ fibre s p k, w i) = ∑ i ∈ s', w i := by
      rw [← Finset.sum_fiberwise_of_maps_to (s := s') (t := t') (g := p) hmaps w]
      exact Finset.sum_congr rfl fun k hk => by
        change (∑ i ∈ fibre s p k, w i) = ∑ i ∈ fibre s' p k, w i
        rw [hfibre k hk]
    rw [hsum_active, hsum_t'] at ht'wt
    calc
      (δ : ENNReal) ^ ε' * ∑ i ∈ s, w i
          ≤ (δ : ENNReal) ^ ε' * (((M : ENNReal) + 1) * ∑ i ∈ s', w i) := by gcongr
      _ = ((δ : ENNReal) ^ ε' * ((M : ENNReal) + 1)) * ∑ i ∈ s', w i := by ring
      _ ≤ 1 * ∑ i ∈ s', w i := by gcongr
      _ = ∑ i ∈ s', w i := one_mul _
  · intro k hk K _hKside
    rw [hfibre k hk]
    calc
      frostmanConstIn (fibre s p k) (fun i => (V i).toConvexSpaceBody) K
          = 1 * frostmanConstIn (fibre s p k) (fun i => (V i).toConvexSpaceBody) K :=
            (one_mul _).symm
      _ ≤ (δ : ENNReal) ^ (-ε') *
          frostmanConstIn (fibre s p k) (fun i => (V i).toConvexSpaceBody) K := by gcongr

end parentConflictCover

end Kakeya.ml1Boot

namespace Kakeya.ml1Boot

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Essentially distinct parent selection at the protected Section 8 interface. -/
theorem exists_essDistinct_parentFamily (hdim : Module.finrank ℝ E = 3) :
    ∃ c : NNReal, 0 < c ∧
    ∀ {ε' : ℝ}, 0 < ε' → ∀ (Cunif : NNReal) {Co : NNReal}, 1 ≤ Co →
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0, ∀ σ ρ : NNReal, δ ≤ σ → σ ≤ ρ → ρ ≤ 1 →
      (δ : ℝ) ^ ε' ≤ (c : ℝ) * ρ / Co →
      ∀ {ι κ : Type*} [DecidableEq κ] {s : Finset ι} {t : Finset κ}
        (V : ι → ShadedTube σ E) (Vρ : κ → Tube ρ E) (p : ι → κ) (w : ι → ENNReal),
        s.Nonempty →
        ShadedTube.ShadedUniformTubeSet s V (Tube.ssfGridLen σ) Cunif →
        (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1) →
        (s : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (V i).carrier (V j).carrier) →
        IsParentFamily s (fun i => (V i).toTube) t Vρ p →
        HasBoundedOverlap s (fun i => (V i).toTube) t Vρ Co →
        ∃ s' ⊆ s, ∃ t' ⊆ t,
          IsParentFamily s' (fun i => (V i).toTube) t' Vρ p ∧
          (t' : Set κ).Pairwise
            (fun k l => IsEssentiallyDistinct (Vρ k).carrier (Vρ l).carrier) ∧
          (δ : ENNReal) ^ ε' * (∑ i ∈ s, w i) ≤ ∑ i ∈ s', w i ∧
          ∀ k ∈ t', ∀ K : ConvexSpaceBody E,
            (∀ i ∈ fibre s p k, (V i).toConvexSpaceBody ≤ K) →
            frostmanConstIn (fibre s' p k) (fun i => (V i).toConvexSpaceBody) K
              ≤ (δ : ENNReal) ^ (-ε')
                * frostmanConstIn (fibre s p k) (fun i => (V i).toConvexSpaceBody) K := by
  letI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [hdim]; norm_num)
  obtain ⟨c, hc, H⟩ :=
    parentConflictCover.exists_essDistinct_parentFamily_of_boundedOverlap (E := E) hdim
  refine ⟨c, hc, ?_⟩
  intro ε' hε' Cunif Co hCo
  filter_upwards [H hε' hCo] with δ hδ
  intro σ ρ hδσ hσρ hρ1 hscale ι κ _inst s t V Vρ p w _hs _hunif
    hball hED hparent hoverlap
  exact hδ σ ρ hδσ hσρ hρ1 hscale V Vρ p w hball hED hparent hoverlap

end Kakeya.ml1Boot
