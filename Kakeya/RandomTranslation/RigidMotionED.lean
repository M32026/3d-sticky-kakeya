/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.RandomTranslation.RigidMotionProb
public import Kakeya.Tube.EDPacking.BadAgainstSet

/-!
# The ED bad-count random variables of GWZ Lemma 3.8

Fix a test tube `T₀` and a pairwise essentially distinct family `T : ι → Tube δ E`. For a rigid
motion `ω` the **bad count**

`edBadCount s T T₀ ω = #{i ∈ s | (T i).rigidMove ω ⊆ 99δ-thickening of T₀}`

is the random variable whose sum over independent copies controls the ED multiplicity of the
randomised family.

Two bounds are proved here, and they are the two inputs to the Chernoff step:

* **deterministic**, `Kakeya.edBadCount_le`: `edBadCount ≤ C_pack` pointwise, a *dimensional*
  constant with no dependence on the number of copies. This is the existing
  `Kakeya.badAgainstSet_count_le_of_ED_thinBox`, which applies because a rigid motion carries the
  pairwise ED family to a pairwise ED family (`Kakeya.rigidMove_pairwise_isEssentiallyDistinct`) and
  because containment implies overlap-badness at any density threshold `≤ 1`.
* **expectation**, `Kakeya.lintegral_edBadCount_le`: `𝔼[edBadCount] ≤ C · |s| · δ^(2(n-1))`, by
  linearity of expectation from GWZ (106) (`Kakeya.prob_rigidMove_bad_le`).

Crucially the deterministic bound is *not* multiplied by the number of copies: that `J`-fold union
bound is exactly the defect this development removes.

The proof also establishes the thin-box volume hypothesis
`volume (cthickening (99δ) T₀.carrier) ≤ M · δ^(n-1)` (`Kakeya.volume_cthickening_tube_le`), which
is the hypothesis used by `badAgainstSet_count_le_of_ED_thinBox`,
`badAgainstSet_card_le_M2_cN` and `randCF_chernoff_witness`.
-/

@[expose] public section

open MeasureTheory Metric Set

namespace Kakeya

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The `99δ`-thickening of a `δ`-tube is a `100δ`-tube, so its volume is
bounded by a dimensional constant times `δ^(n-1)`. -/
theorem volume_cthickening_tube_le [Nontrivial E] :
    ∃ M : ℝ, 0 < M ∧
      ∀ {δ : NNReal}, (100 * δ : NNReal) ≤ 1 → ∀ T₀ : Tube δ E,
        volume (Metric.cthickening (99 * (δ : ℝ)) T₀.carrier)
          ≤ ENNReal.ofReal M * (δ : ENNReal) ^ (Module.finrank ℝ E - 1) := by
  let n : ℕ := Module.finrank ℝ E
  refine ⟨((Tube.volume_le.C n * 100 ^ (n - 1) : NNReal) : ℝ), ?_, ?_⟩
  · rw [NNReal.coe_pos]
    exact mul_pos (Tube.volume_le.C_pos n)
      (pow_pos (by norm_num : (0 : NNReal) < 100) (n - 1))
  · intro δ hδ T
    have h99 : (99 : ℝ) * (δ : ℝ) = ((99 * δ : NNReal) : ℝ) := by
      push_cast
      norm_num
    rw [h99, Tube.cthickening_carrier T (99 * δ)]
    have hsum : δ + 99 * δ = 100 * δ := by
      ring
    rw [hsum]
    apply (Tube.volume_le hδ (T.rescale (100 * δ))).trans
    rw [ENNReal.ofReal_coe_nnreal]
    refine le_of_eq ?_
    rw [show Module.finrank ℝ E = n from rfl]
    rw [← ENNReal.coe_pow, ← ENNReal.coe_mul]
    exact congrArg (fun x : NNReal => (x : ENNReal)) (by
      rw [mul_pow]
      ac_rfl)

/-- A rigid motion preserves Lebesgue measure. -/
theorem measurePreserving_rigidMap (u : unitary (E →L[ℝ] E)) (v : E) :
    MeasurePreserving (rigidMap u v) volume volume := by
  rw [show rigidMap u v = (fun y : E => y + v) ∘ (fun x : E => (u : E →L[ℝ] E) x) by
    funext x
    rfl]
  exact MeasurePreserving.comp (measurePreserving_add_right volume v) (by
    rw [show (fun x : E => (u : E →L[ℝ] E) x) =
        (Unitary.linearIsometryEquiv u : E → E) by
      funext x
      rfl]
    exact ((Unitary.linearIsometryEquiv u) : E ≃ₗᵢ[ℝ] E).measurePreserving)

/-- A rigid motion carries a pairwise essentially distinct family to a pairwise essentially
distinct family: essential distinctness is defined by volumes of intersections, and rigid motions
preserve volume. -/
theorem rigidMove_pairwise_isEssentiallyDistinct {δ : NNReal} {ι : Type*} {s : Finset ι}
    {T : ι → Tube δ E} (hED : (s : Set ι).Pairwise
      (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier))
    (u : unitary (E →L[ℝ] E)) (v : E) :
    (s : Set ι).Pairwise
      (fun i j => IsEssentiallyDistinct ((T i).rigidMove u v).carrier
        ((T j).rigidMove u v).carrier) := by
  intro i hi j hj hij
  rw [Tube.rigidMove_carrier, Tube.rigidMove_carrier]
  let L : E ≃ₗᵢ[ℝ] E := Unitary.linearIsometryEquiv u
  let g : E → E := fun y : E => (L.symm : E → E) (y - v)
  have h1 : Function.LeftInverse g (rigidMap u v) := by
    intro x
    dsimp [g]
    rw [add_sub_cancel_right]
    rw [← Unitary.coe_linearIsometryEquiv_apply u]
    apply LinearEquiv.symm_apply_apply
  have h2 : Function.RightInverse g (rigidMap u v) := by
    intro y
    dsimp [g]
    change (L : E → E) (L.symm (y - v)) + v = y
    simp
  have himage : ∀ s : Set E, rigidMap u v '' s = g ⁻¹' s := by
    intro s
    exact congrFun (Set.image_eq_preimage_of_inverse h1 h2) s
  have hmeas_f : Measurable (rigidMap u v) := (isometry_rigidMap u v).continuous.measurable
  have hmeas_g : Measurable g := by
    dsimp [g]
    exact ((L.symm : E →L[ℝ] E).continuous.comp
      (Continuous.sub continuous_id continuous_const)).measurable
  let e : E ≃ᵐ E :=
    { toEquiv := { toFun := rigidMap u v, invFun := g, left_inv := h1, right_inv := h2 }
      measurable_toFun := hmeas_f
      measurable_invFun := hmeas_g }
  have he : MeasurePreserving (e : E → E) volume volume := by
    change MeasurePreserving (rigidMap u v) volume volume
    exact measurePreserving_rigidMap u v
  have h_symm : MeasurePreserving (e.symm : E → E) volume volume :=
    MeasurePreserving.symm e he
  have hvol : ∀ s : Set E, volume (rigidMap u v '' s) = volume s := by
    intro s
    rw [himage s]
    change volume ((e.symm : E → E) ⁻¹' s) = volume s
    exact MeasurePreserving.measure_preimage_equiv h_symm s
  have hinter : rigidMap u v '' ((T i).carrier ∩ (T j).carrier) =
    (rigidMap u v '' (T i).carrier) ∩ (rigidMap u v '' (T j).carrier) := by
    rw [himage ((T i).carrier ∩ (T j).carrier), himage (T i).carrier, himage (T j).carrier]
    rw [Set.preimage_inter]
  unfold IsEssentiallyDistinct
  rw [← hinter]
  rw [hvol ((T i).carrier ∩ (T j).carrier), hvol (T i).carrier, hvol (T j).carrier]
  exact hED hi hj hij

/-- The number of members of the family that the rigid motion `ω` pushes into the `99δ`-thickening
of the test tube `T₀`. -/
def edBadCount {δ : NNReal} {ι : Type*} (s : Finset ι) (T : ι → Tube δ E) (T₀ : Tube δ E)
    (ω : unitary (E →L[ℝ] E) × E) : ℕ :=
  (@Finset.filter ι (fun i =>
      ((T i).rigidMove ω.1 ω.2).carrier ⊆ Metric.cthickening (99 * (δ : ℝ)) T₀.carrier)
    (Classical.decPred _) s).card

/-- **The deterministic bound.** For a pairwise essentially distinct family the bad count of a
*single* rigid copy is at most a dimensional constant. No factor of the number of copies appears. -/
theorem edBadCount_le [Nontrivial E] (hn : 1 < Module.finrank ℝ E) :
    ∃ (Cpack : ℕ) (δ₀ : NNReal), 0 < Cpack ∧ 0 < δ₀ ∧
      ∀ {δ : NNReal}, 0 < δ → δ ≤ δ₀ →
      ∀ {ι : Type*} (s : Finset ι) (T : ι → Tube δ E) (T₀ : Tube δ E),
        T₀.carrier ⊆ Metric.closedBall (0 : E) (7 / 2) →
        (s : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
        ∀ ω : unitary (E →L[ℝ] E) × E, edBadCount s T T₀ ω ≤ Cpack := by
  classical
  letI : ProperSpace E := FiniteDimensional.proper_real E
  obtain ⟨C_dim, δ₀bad, hC_dim_pos, hδ₀bad_pos, hδ₀bad_le1, hBad⟩ :=
    badAgainstSet_count_le_of_ED_thinBox (E := E) hn
  obtain ⟨M, hM_pos, hVol⟩ := volume_cthickening_tube_le (E := E)
  set c₀ : ℝ := ((Tube.le_volume.c (Module.finrank ℝ E) : NNReal) : ℝ) /
      (2 * ((Tube.volume_le.C (Module.finrank ℝ E) : NNReal) : ℝ)) with hc₀_def
  set Cpack : ℕ :=
    ⌈(C_dim : ℝ) * M ^ 2 / c₀ ^ Module.finrank ℝ E⌉₊ with hCpack_def
  have hc₀_pos : 0 < c₀ := by
    rw [hc₀_def]
    exact div_pos (by exact_mod_cast (Tube.le_volume.c_pos (Module.finrank ℝ E)))
      (by positivity)
  have hCpack_pos : 0 < Cpack := by
    rw [hCpack_def]
    rw [Nat.ceil_pos]
    exact div_pos
      (mul_pos (by exact_mod_cast hC_dim_pos) (sq_pos_of_ne_zero (ne_of_gt hM_pos)))
      (pow_pos hc₀_pos _)
  let δ₀ : NNReal :=
    ⟨min δ₀bad (1 / 100 : ℝ), le_min hδ₀bad_pos.le (by norm_num)⟩
  have hδ₀_cast : (δ₀ : ℝ) = min δ₀bad (1 / 100 : ℝ) := rfl
  have hδ₀_pos : (0 : NNReal) < δ₀ := by
    change (0 : ℝ) < (δ₀ : ℝ)
    rw [hδ₀_cast]
    exact lt_min hδ₀bad_pos (by norm_num)
  refine ⟨Cpack, δ₀, hCpack_pos, hδ₀_pos, ?_⟩
  intro δ hδ hδ_le
  -- δ is bounded above by both δ₀bad and 1/100
  have hδR : (δ : ℝ) ≤ (δ₀ : ℝ) := by exact_mod_cast hδ_le
  have hδminR : (δ : ℝ) ≤ min δ₀bad (1 / 100 : ℝ) := by
    rw [← hδ₀_cast]
    exact hδR
  have hδle100R : (δ : ℝ) ≤ (1 / 100 : ℝ) := le_trans hδminR (min_le_right _ _)
  have hδbadR : (δ : ℝ) ≤ δ₀bad := le_trans hδminR (min_le_left _ _)
  have hδ₁ : δ ≤ (1 : NNReal) := by
    exact_mod_cast (le_trans hδminR (le_trans (min_le_left _ _) hδ₀bad_le1))
  have h100δ : (100 * δ : NNReal) ≤ 1 := by
    have h₁ : (100 : ℝ) * (δ : ℝ) ≤ 1 := by nlinarith [hδle100R]
    exact_mod_cast h₁
  intro ι s T T₀ hB2 hED ω
  -- the density threshold `c₀` is at most 1: containment in the thickening implies
  -- `BadAgainstSet` at threshold `c₀` (used in the filter inclusion below)
  have hc₀_le_one : c₀ ≤ 1 := by
    rw [hc₀_def]
    have h2vol_pos : (0 : ℝ) < 2 * ((Tube.volume_le.C (Module.finrank ℝ E) : NNReal) : ℝ) := by
      positivity
    rw [div_le_iff₀ h2vol_pos]
    have hc_le_M :
        ((Tube.le_volume.c (Module.finrank ℝ E) : NNReal) : ℝ) ≤
          ((Tube.volume_le.C (Module.finrank ℝ E) : NNReal) : ℝ) := by
      have hlb := Tube.le_volume T₀
      have hup := Tube.volume_le hδ₁ T₀
      have hchain :
          (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) *
              (δ : ENNReal) ^ (Module.finrank ℝ E - 1) ≤
            (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal) *
              (δ : ENNReal) ^ (Module.finrank ℝ E - 1) :=
        hlb.trans hup
      have hfin :
          (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal) *
              (δ : ENNReal) ^ (Module.finrank ℝ E - 1) ≠ ⊤ :=
        ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
      have hR := ENNReal.toReal_mono hfin hchain
      rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal,
        ENNReal.coe_toReal] at hR
      have hpow_pos : (0 : ℝ) < (δ : ℝ) ^ (Module.finrank ℝ E - 1) :=
        pow_pos (by exact_mod_cast hδ) _
      exact le_of_mul_le_mul_right hR hpow_pos
    have hC_nonneg : (0 : ℝ) ≤ ((Tube.volume_le.C (Module.finrank ℝ E) : NNReal) : ℝ) :=
      NNReal.coe_nonneg _
    linarith
  let u : unitary (E →L[ℝ] E) := ω.1
  let v : E := ω.2
  let T' : ι → Tube δ E := fun i => (T i).rigidMove u 0
  have hED' : (s : Set ι).Pairwise
      (fun i j => IsEssentiallyDistinct (T' i).carrier (T' j).carrier) := by
    simpa [T'] using rigidMove_pairwise_isEssentiallyDistinct hED u 0
  have hcar : ∀ i : ι, ((T i).rigidMove u v).carrier = ((T' i).translate v).carrier := by
    intro i
    have r_im : (v + ·) '' (Kakeya.rigidMap u 0 '' (T i).carrier) =
        Kakeya.rigidMap u v '' (T i).carrier := by
      rw [← Set.image_comp]
      congr 1
      funext x
      simp [Kakeya.rigidMap, add_comm]
    calc
      ((T i).rigidMove u v).carrier = Kakeya.rigidMap u v '' (T i).carrier :=
        Tube.rigidMove_carrier (T i) u v
      _ = (v + ·) '' (Kakeya.rigidMap u 0 '' (T i).carrier) := r_im.symm
      _ = (v + ·) '' ((T i).rigidMove u 0).carrier := by simp [Tube.rigidMove_carrier]
      _ = ((T' i).translate v).carrier := by simp [T', Tube.translate]
  let K : Set E := Metric.cthickening (99 * (δ : ℝ)) T₀.carrier
  have hide : s.filter (fun i : ι => ((T i).rigidMove u v).carrier ⊆ K) ⊆
      s.filter (fun i : ι => BadAgainstSet ((T' i).translate v) K c₀) := by
    intro i hi
    rw [Finset.mem_filter] at hi ⊢
    refine ⟨hi.1, ?_⟩
    have hsubT : ((T' i).translate v).carrier ⊆ K := by
      rw [← hcar i]
      exact hi.2
    unfold BadAgainstSet
    rw [Set.inter_eq_self_of_subset_left hsubT]
    have hofReal : ENNReal.ofReal c₀ ≤ (1 : ENNReal) :=
      ENNReal.ofReal_le_one.mpr hc₀_le_one
    have h_refl : volume ((T' i).translate v).carrier ≤
        volume ((T' i).translate v).carrier := le_rfl
    simpa using mul_le_mul hofReal h_refl zero_le zero_le
  have hMain : (s.filter (fun i : ι => BadAgainstSet ((T' i).translate v) K c₀)).card ≤ Cpack := by
    have hvolT₀ : volume (Metric.cthickening (99 * (δ : ℝ)) T₀.carrier) ≤
        ENNReal.ofReal M * (δ : ENNReal) ^ (Module.finrank ℝ E - 1) :=
      hVol h100δ T₀
    have hB := hBad (ι := ι) (δ := δ) hδ hδbadR s T' T₀ hB2 M hM_pos hvolT₀ v hED'
    simpa [hCpack_def, c₀, K] using hB
  simpa [edBadCount, u, v, K] using (Finset.card_le_card hide).trans hMain

/-- **The expectation bound**, by linearity of expectation from GWZ (106). -/
theorem lintegral_edBadCount_le [Nontrivial E] (hn : 1 < Module.finrank ℝ E) :
    ∃ (C : ENNReal) (δ₀ : NNReal), C ≠ ⊤ ∧ 0 < δ₀ ∧
      ∀ {δ : NNReal}, 0 < δ → δ ≤ δ₀ →
      ∀ {ι : Type*} (s : Finset ι) (T : ι → Tube δ E) (T₀ : Tube δ E),
        ∫⁻ ω, (edBadCount s T T₀ ω : ENNReal) ∂(rigidMeasure E)
          ≤ C * (s.card : ENNReal) * (δ : ENNReal) ^ (2 * (Module.finrank ℝ E - 1)) := by
  classical
  obtain ⟨C₀, δ₀, hC₀, hδ₀, hKey⟩ := prob_rigidMove_bad_le (E := E) hn
  refine ⟨C₀, δ₀, hC₀, hδ₀, ?_⟩
  intro δ hδ hδ_le ι s T T₀
  let K : ConvexSpaceBody E := T₀.toConvexSpaceBody.cthickening (99 * (δ : ℝ))
  let P : ι → Set (unitary (E →L[ℝ] E) × E) := fun i =>
    {ω : unitary (E →L[ℝ] E) × E | ((T i).rigidMove ω.1 ω.2).carrier ⊆ K.carrier}
  have hP_meas : ∀ i, MeasurableSet (P i) := by
    intro i
    dsimp [P]
    exact (isClosed_rigidMove_subset (T i) K).measurableSet
  have hmeas : ∀ i, Measurable (fun ω : unitary (E →L[ℝ] E) × E =>
      if ((T i).rigidMove ω.1 ω.2).carrier ⊆ K.carrier then (1 : ENNReal) else 0) := by
    intro i
    exact Measurable.ite (hP_meas i) measurable_const measurable_const
  have hcount : ∀ ω : unitary (E →L[ℝ] E) × E,
      (edBadCount s T T₀ ω : ENNReal) =
        ∑ i ∈ s, if ((T i).rigidMove ω.1 ω.2).carrier ⊆ K.carrier then (1 : ENNReal) else 0 := by
    intro ω
    dsimp [edBadCount]
    rw [Finset.natCast_card_filter]
    simp [K]
  have hterm : ∀ i, (∫⁻ ω : unitary (E →L[ℝ] E) × E,
      if ((T i).rigidMove ω.1 ω.2).carrier ⊆ K.carrier then (1 : ENNReal) else 0
      ∂(rigidMeasure E)) = rigidMeasure E (P i) := by
    intro i
    rw [show (fun ω : unitary (E →L[ℝ] E) × E =>
      if ((T i).rigidMove ω.1 ω.2).carrier ⊆ K.carrier then (1 : ENNReal) else 0)
        = (P i).indicator (fun _ : unitary (E →L[ℝ] E) × E => (1 : ENNReal)) by
        funext ω
        rfl]
    exact lintegral_indicator_one (μ := rigidMeasure E) (s := P i) (hP_meas i)
  have hbound : ∀ i, rigidMeasure E (P i) ≤
      C₀ * (δ : ENNReal) ^ (2 * (Module.finrank ℝ E - 1)) := by
    intro i
    calc
      rigidMeasure E (P i)
          = rigidMeasure E {ω : unitary (E →L[ℝ] E) × E |
              ((T i).rigidMove ω.1 ω.2).carrier ⊆ K.carrier} := rfl
      _ = rigidMeasure E {ω : unitary (E →L[ℝ] E) × E |
              ((T i).rigidMove ω.1 ω.2).carrier
                ⊆ Metric.cthickening (99 * (δ : ℝ)) T₀.carrier} := rfl
      _ ≤ C₀ * (δ : ENNReal) ^ (2 * (Module.finrank ℝ E - 1)) :=
            hKey hδ hδ_le (T i) T₀
  calc
    ∫⁻ ω, (edBadCount s T T₀ ω : ENNReal) ∂(rigidMeasure E)
        = ∫⁻ ω, ∑ i ∈ s,
        (if ((T i).rigidMove ω.1 ω.2).carrier ⊆ K.carrier then (1 : ENNReal) else 0)
        ∂(rigidMeasure E) := by
          apply lintegral_congr
          intro ω
          exact hcount ω
    _ = ∑ i ∈ s, ∫⁻ ω,
          (if ((T i).rigidMove ω.1 ω.2).carrier ⊆ K.carrier then (1 : ENNReal) else 0)
          ∂(rigidMeasure E) := by
          exact lintegral_finsetSum' (μ := rigidMeasure E) (s := s)
            (f := fun (i : ι) (ω : unitary (E →L[ℝ] E) × E) =>
              if ((T i).rigidMove ω.1 ω.2).carrier ⊆ K.carrier then (1 : ENNReal) else 0)
            (hf := fun i hi => (hmeas i).aemeasurable)
    _ ≤ ∑ i ∈ s, C₀ * (δ : ENNReal) ^ (2 * (Module.finrank ℝ E - 1)) := by
          exact Finset.sum_le_sum (fun i _ => (hterm i).trans_le (hbound i))
    _ = (s.card : ENNReal) * (C₀ * (δ : ENNReal) ^ (2 * (Module.finrank ℝ E - 1))) := by
          simp [Finset.sum_const, nsmul_eq_mul]
    _ = C₀ * (s.card : ENNReal) * (δ : ENNReal) ^ (2 * (Module.finrank ℝ E - 1)) := by
          ring

end

end Kakeya

end
