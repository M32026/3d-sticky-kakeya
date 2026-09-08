import MyLeanRepo.Kakeya.Streamlined.Families
import MyLeanRepo.Kakeya.Streamlined.Basic
import MyLeanRepo.Kakeya.Streamlined.StickyInput
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Final iteration from the two Main Lemmas

Paper references:
- `reference/streamlined_kakeya_2601.14411/03-partial-kakeya-estimates.md`,
  the final iteration after `lemmain1` and `lemmain2`;
- `reference/streamlined_kakeya_2601.14411/01-introduction-to-the-kakeya-problem.md`,
  theorem `thmkak`.

This file derives `GeneralKakeyaStatement` from the sticky hypothesis,
VeryNotSticky, and the two Main Lemmas. It does not prove those inputs.

Contains:
- Tube volume equalities and lower bounds
- `realRpowENN` helper lemmas
- Card bound from the Katz–Tao condition
- `katz_tao_one` and `katz_tao_mono`
- Finite iteration bootstrap
- Final derivation assembling all pieces
- The target theorem `sticky_implies_general`
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Streamlined

/-!
## Tube volume equalities and lower bounds
-/

/-- An isometry equivalence maps closed thickenings to closed thickenings. -/
lemma IsometryEquiv.cthickening_image {α β : Type*} [PseudoEMetricSpace α] [PseudoEMetricSpace β]
    (e : α ≃ᵢ β) (δ : ℝ) (s : Set α) :
    e '' (Metric.cthickening δ s) = Metric.cthickening δ (e '' s) := by
  ext y
  simp only [Metric.mem_cthickening_iff, Set.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have h : Metric.infEDist (e x) (e '' s) = Metric.infEDist x s :=
      Metric.infEDist_image e.isometry
    rw [h]
    exact hx
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    have h_img : e.symm '' (e '' s) = s := by
      rw [← Set.image_comp]
      simp
    have h : Metric.infEDist (e.symm y) s = Metric.infEDist y (e '' s) := by
      have h' := Metric.infEDist_image e.symm.isometry (x := y) (t := e '' s)
      rw [h_img] at h'
      exact h'
    rw [h]
    exact hy

theorem deltaTube_volume_eq {δ : ℝ} (T : Kakeya.DeltaTube δ) :
    T.volume = Kakeya.deltaTubeVolume δ := by
  let e₀ : Point3 := EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
  have hdir : ‖T.direction‖ = 1 := T.direction_unit
  have he₀ : ‖e₀‖ = 1 := by
    simp [e₀]
  have hnorm : ‖T.direction‖ = ‖e₀‖ := by
    rw [hdir, he₀]
  let A : Point3 ≃ₗᵢ[ℝ] Point3 :=
    Submodule.reflection (ℝ ∙ (T.direction - e₀))ᗮ
  have hA : A T.direction = e₀ := Submodule.reflection_sub hnorm
  let τ : Point3 ≃ᵢ Point3 :=
    { toFun := fun x => x - T.base
      invFun := fun y => y + T.base
      left_inv := by intro x; simp
      right_inv := by intro y; simp
      isometry_toFun := by
        intro x y
        simp [edist_dist, dist_eq_norm] }
  let f : Point3 ≃ᵢ Point3 := τ.trans A
  have hf_apply : ∀ x, f x = A (x - T.base) := by
    intro x; rfl
  have hseg : f '' (Kakeya.unitSegment T.base T.direction) =
      Kakeya.unitSegment 0 e₀ := by
    ext y
    simp only [Kakeya.unitSegment, Set.mem_image]
    constructor
    · rintro ⟨x, ⟨t, ht, rfl⟩, rfl⟩
      refine ⟨t, ht, ?_⟩
      simp [hf_apply, hA, A.map_smul]
    · rintro ⟨t, ht, rfl⟩
      refine ⟨T.base + t • T.direction, ⟨t, ht, rfl⟩, ?_⟩
      simp [hf_apply, hA, A.map_smul]
  have hcarrier : f '' T.carrier =
      Metric.cthickening δ (Kakeya.unitSegment 0 e₀) := by
    rw [DeltaTube.carrier, IsometryEquiv.cthickening_image f δ (Kakeya.unitSegment T.base T.direction), hseg]
  have hA_mp : MeasurePreserving A volume volume := A.measurePreserving
  have hτ_mp : MeasurePreserving τ volume volume :=
    measurePreserving_sub_right volume T.base
  have hmp : MeasurePreserving f volume volume := hA_mp.comp hτ_mp
  let f_meas : Point3 ≃ᵐ Point3 :=
    { toFun := f
      invFun := f.symm
      left_inv := f.left_inv
      right_inv := f.right_inv
      measurable_toFun := f.continuous.measurable
      measurable_invFun := f.symm.continuous.measurable }
  have hmp_symm : MeasurePreserving f.symm volume volume := hmp.symm f_meas
  have h_eq : f '' T.carrier = f.symm ⁻¹' T.carrier := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hz
      exact ⟨f.symm z, hz, f.apply_symm_apply z⟩
  have hvol : volume (f '' T.carrier) = volume T.carrier := by
    rw [h_eq]
    exact MeasurePreserving.measure_preimage_equiv (f := f_meas.symm) hmp_symm T.carrier
  rw [DeltaTube.volume, ← hvol, hcarrier]
  rfl

theorem deltaTube_volume_lower_bound {δ : ℝ} (hδ : 0 < δ) :
    Kakeya.deltaTubeVolume δ ≥ ENNReal.ofReal (Real.pi / 6 * δ^3) := by
  let e₀ : Point3 := EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
  let midpoint : Point3 := (1 / 2 : ℝ) • e₀
  have hmid : midpoint ∈ Kakeya.unitSegment 0 e₀ := by
    refine ⟨1 / 2, by norm_num, ?_⟩
    simp [midpoint]
  have hball : Metric.closedBall midpoint (δ / 2) ⊆
      Metric.cthickening δ (Kakeya.unitSegment 0 e₀) := by
    intro x hx
    have hdist : dist x midpoint ≤ δ / 2 := hx
    have h2 : dist x midpoint ≤ δ := by linarith
    have h3 : Metric.infEDist x (Kakeya.unitSegment 0 e₀) ≤ edist x midpoint :=
      Metric.infEDist_le_edist_of_mem hmid
    have h4 : edist x midpoint ≤ ENNReal.ofReal δ := by
      rw [edist_dist]
      exact ENNReal.ofReal_le_ofReal h2
    exact le_trans h3 h4
  have hvol : volume (Metric.closedBall midpoint (δ / 2)) ≤
      Kakeya.deltaTubeVolume δ :=
    measure_mono hball
  have hballvol : volume (Metric.closedBall midpoint (δ / 2)) =
      ENNReal.ofReal (δ / 2) ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3) :=
    EuclideanSpace.volume_closedBall_fin_three midpoint (δ / 2)
  rw [hballvol] at hvol
  have h4 : 0 ≤ δ := by linarith
  have h5 : 0 ≤ δ / 2 := by linarith
  have h6 : ENNReal.ofReal (δ / 2) ^ 3 = ENNReal.ofReal ((δ / 2) ^ 3) := by
    rw [ENNReal.ofReal_pow h5]
  have h3 : ENNReal.ofReal (δ / 2) ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3) =
      ENNReal.ofReal (Real.pi / 6 * δ^3) := by
    rw [h6, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  rw [h3] at hvol
  exact hvol

theorem family_mass_eq_nominal {δ : ℝ} (F : TubeFamily δ) :
    F.toBodyFamily.mass = F.nominalMass := by
  have h : ∀ i : Fin F.card, (F.toBodyFamily.body i).volume = Kakeya.deltaTubeVolume δ := by
    intro i
    exact deltaTube_volume_eq (F.tube i)
  calc
    F.toBodyFamily.mass
      = ∑ i : Fin F.card, (F.toBodyFamily.body i).volume := by rfl
    _ = ∑ i : Fin F.card, Kakeya.deltaTubeVolume δ := by
      apply Finset.sum_congr rfl
      intro i _
      exact h i
    _ = (F.card : ENNReal) * Kakeya.deltaTubeVolume δ := by
      simp [Finset.sum_const]
    _ = F.enncard * Kakeya.deltaTubeVolume δ := by rfl
    _ = F.nominalMass := by rfl

/-!
## Helper lemmas for the final derivation
-/

/-- Monotonicity of `realRpowENN δ` in the exponent for `0 < δ ≤ 1`:
larger exponent gives smaller value. -/
lemma realRpowENN_antitone {δ a b : ℝ} (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1)
    (h : a ≤ b) : Kakeya.realRpowENN δ b ≤ Kakeya.realRpowENN δ a := by
  simp only [Kakeya.realRpowENN]
  apply ENNReal.ofReal_le_ofReal
  exact Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_le_one h

/-- Multiplication-addition identity for `realRpowENN`. -/
lemma realRpowENN_add {δ a b : ℝ} (hδ_pos : 0 < δ) :
    Kakeya.realRpowENN δ (a + b) =
      Kakeya.realRpowENN δ a * Kakeya.realRpowENN δ b := by
  simp only [Kakeya.realRpowENN]
  have h1 : Real.rpow δ (a + b) = Real.rpow δ a * Real.rpow δ b :=
    Real.rpow_add (by linarith) a b
  rw [h1]
  have ha : 0 ≤ Real.rpow δ a := Real.rpow_nonneg (by linarith) a
  have hb : 0 ≤ Real.rpow δ b := Real.rpow_nonneg (by linarith) b
  have h_mul : ENNReal.ofReal (Real.rpow δ a * Real.rpow δ b) =
      ENNReal.ofReal (Real.rpow δ a) * ENNReal.ofReal (Real.rpow δ b) := by
    rw [← ENNReal.ofReal_mul ha]
  exact h_mul

/-- For any finite `D` and `γ > 0`, there exists `δ₀ > 0` such that
`D ≤ realRpowENN δ (-γ)` for all `0 < δ ≤ δ₀`. -/
lemma exists_delta_pow_bound (D : ENNReal) (hD : D ≠ ⊤) {γ : ℝ} (hγ : 0 < γ) :
    ∃ (δ₀ : ℝ), 0 < δ₀ ∧ ∀ (δ : ℝ), 0 < δ → δ ≤ δ₀ →
      D ≤ Kakeya.realRpowENN δ (-γ) := by
  by_cases hD0 : D = 0
  · refine ⟨1, by norm_num, fun δ _ _ => ?_⟩
    rw [hD0]
    simp [Kakeya.realRpowENN]
  · have hD_pos : 0 < D := Ne.bot_lt hD0
    have hD_real_pos : 0 < D.toReal :=
      ENNReal.toReal_pos hD0 hD
    let δ₀ : ℝ := (D.toReal)⁻¹ ^ (γ⁻¹)
    have hδ₀_pos : 0 < δ₀ := by positivity
    refine ⟨δ₀, hδ₀_pos, fun δ hδ hδle => ?_⟩
    have h1 : δ ^ γ ≤ D.toReal⁻¹ := by
      have h4 : δ ^ γ ≤ δ₀ ^ γ := by gcongr
      have h5 : δ₀ ^ γ = D.toReal⁻¹ := by
        dsimp only [δ₀]
        rw [← Real.rpow_mul (by positivity)]
        have h6 : γ⁻¹ * γ = 1 := by field_simp
        rw [h6] <;> simp
      rw [h5] at h4
      exact h4
    have h2 : D.toReal ≤ δ ^ (-γ) := by
      have h3 : δ ^ (-γ) = (δ ^ γ)⁻¹ := by
        rw [Real.rpow_neg (by linarith)]
      rw [h3]
      have h4 : 0 < δ ^ γ := by positivity
      have h5 : (δ ^ γ)⁻¹ ≥ (D.toReal⁻¹)⁻¹ := by gcongr
      have h6 : (D.toReal⁻¹)⁻¹ = D.toReal := by
        field_simp [hD_real_pos.ne']
      rw [h6] at h5
      exact h5
    have h5 : D ≤ ENNReal.ofReal (δ ^ (-γ)) := by
      have h_nonneg : 0 ≤ δ ^ (-γ) := by positivity
      rw [ENNReal.le_ofReal_iff_toReal_le hD h_nonneg]
      exact h2
    simpa [Kakeya.realRpowENN] using h5

/-- If KT estimate works with η₀, it works with any η ≤ η₀. -/
lemma katz_tao_shrink_eta {α ε η η₀ δ : ℝ}
    (hη : η ≤ η₀) (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1)
    (hKT : ∀ (F : TubeFamily δ), F.Nonempty → F.IsInUnitBall →
      F.IsEssentiallyDistinct →
      F.toBodyFamily.IsCKatzTao (Kakeya.realRpowENN δ (-η₀)) →
      ∀ (Y : TubeShading F),
        Y.IsLambdaDense (Kakeya.realRpowENN δ η₀) →
        Y.HasAverageMultiplicityAtMost
          (Kakeya.realRpowENN δ (-ε) * ENNReal.rpow F.enncard α))
    {F : TubeFamily δ} (hF_ne : F.Nonempty)
    (hF_ball : F.IsInUnitBall) (hF_distinct : F.IsEssentiallyDistinct)
    (hKT_eta : F.toBodyFamily.IsCKatzTao (Kakeya.realRpowENN δ (-η)))
    {Y : TubeShading F}
    (hY_eta : Y.IsLambdaDense (Kakeya.realRpowENN δ η)) :
    Y.HasAverageMultiplicityAtMost
      (Kakeya.realRpowENN δ (-ε) * ENNReal.rpow F.enncard α) := by
  have h1 : Kakeya.realRpowENN δ (-η) ≤ Kakeya.realRpowENN δ (-η₀) :=
    realRpowENN_antitone hδ_pos hδ_le_one (by linarith)
  have h2 : Kakeya.realRpowENN δ η₀ ≤ Kakeya.realRpowENN δ η :=
    realRpowENN_antitone hδ_pos hδ_le_one (by linarith)
  have hKT₀ : F.toBodyFamily.IsCKatzTao (Kakeya.realRpowENN δ (-η₀)) :=
    le_trans hKT_eta h1
  have hY₀ : Y.IsLambdaDense (Kakeya.realRpowENN δ η₀) := by
    have h : Kakeya.realRpowENN δ η₀ * F.toBodyFamily.mass ≤
        Kakeya.realRpowENN δ η * F.toBodyFamily.mass := by gcongr
    exact le_trans h hY_eta
  exact hKT F hF_ne hF_ball hF_distinct hKT₀ Y hY₀

/-- The unit ball has positive, finite volume. -/
lemma unitBall_volume_pos_and_lt_top :
    0 < volume unitBall.carrier ∧ volume unitBall.carrier ≠ ⊤ := by
  have h8 : unitBall.carrier = Metric.closedBall (0 : Point3) 1 := by
    simp [unitBall, Kakeya.DeltaTube.unitBall]
  have h9 : volume unitBall.carrier ≠ ⊤ := by
    rw [h8]
    have h10 : Bornology.IsBounded (Metric.closedBall (0 : Point3) 1) :=
      Metric.isBounded_closedBall
    have h11 : volume (Metric.closedBall (0 : Point3) 1) < ⊤ :=
      h10.measure_lt_top
    exact h11.ne
  have h_open : IsOpen (Metric.ball (0 : Point3) 1) := Metric.isOpen_ball
  have h_nonempty : Set.Nonempty (Metric.ball (0 : Point3) 1) := by
    refine ⟨0, by simp⟩
  have h2 : (Metric.ball (0 : Point3) 1) ⊆ unitBall.carrier := by
    rw [h8]
    intro x hx
    exact Metric.ball_subset_closedBall hx
  have h3 : 0 < volume (Metric.ball (0 : Point3) 1) :=
    h_open.measure_pos volume h_nonempty
  have h4 : 0 < volume unitBall.carrier :=
    lt_of_lt_of_le h3 (MeasureTheory.measure_mono h2)
  exact ⟨h4, h9⟩

/-!
## Card bound from Katz-Tao condition
-/

/-- Bound on the number of tubes from the Katz-Tao condition. -/
lemma card_bound_from_kt {δ η : ℝ} (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1)
    {F : TubeFamily δ} (hF_ball : F.IsInUnitBall)
    (hKT : F.toBodyFamily.IsCKatzTao (Kakeya.realRpowENN δ (-η))) :
    F.enncard ≤
      (volume unitBall.carrier) * (ENNReal.ofReal (Real.pi / 6))⁻¹ *
      Kakeya.realRpowENN δ (-(3 + η)) := by
  classical
  have h_mass_eq : F.toBodyFamily.mass = F.nominalMass :=
    family_mass_eq_nominal F
  have h_unitBall_convex : Convex ℝ unitBall.carrier :=
    convex_closedBall (0 : Point3) 1
  have h_density_in : F.toBodyFamily.density unitBall.carrier ∈
      {d : ENNReal | ∃ (K : Set Point3), Convex ℝ K ∧ d = F.toBodyFamily.density K} :=
    ⟨unitBall.carrier, h_unitBall_convex, rfl⟩
  have h_density : F.toBodyFamily.density unitBall.carrier ≤ F.toBodyFamily.deltaMax :=
    have h_bdd : BddAbove {d : ENNReal | ∃ (K : Set Point3), Convex ℝ K ∧ d = F.toBodyFamily.density K} := by
      use ⊤
      intro x _
      exact le_top
    le_csSup h_bdd h_density_in
  have h_all_contained : F.toBodyFamily.containedMass unitBall.carrier = F.toBodyFamily.mass := by
    have h_indices : F.toBodyFamily.containedIndices unitBall.carrier = Finset.univ := by
      apply Finset.filter_true_of_mem
      intro i _
      have h : (F.toBodyFamily.body i).carrier ⊆ unitBall.carrier := by
        have h' : (F.tube i).carrier ⊆ Kakeya.DeltaTube.unitBall := hF_ball i
        have h_eq1 : (F.toBodyFamily.body i).carrier = (F.tube i).carrier := by rfl
        have h_eq2 : unitBall.carrier = Kakeya.DeltaTube.unitBall := by rfl
        rw [h_eq1, h_eq2]
        exact h'
      exact h
    rw [BodyFamily.containedMass, h_indices]
    <;> rfl
  have h1 : F.toBodyFamily.density unitBall.carrier =
      F.toBodyFamily.mass / volume unitBall.carrier := by
    rw [BodyFamily.density, h_all_contained]
  have h2 : F.toBodyFamily.mass / volume unitBall.carrier ≤
      Kakeya.realRpowENN δ (-η) := by
    rw [h1] at h_density
    exact le_trans h_density hKT
  have hvol_pos : 0 < volume unitBall.carrier := unitBall_volume_pos_and_lt_top.1
  have hvol_ne_top : volume unitBall.carrier ≠ ⊤ := unitBall_volume_pos_and_lt_top.2
  have h3 : F.toBodyFamily.mass ≤
      Kakeya.realRpowENN δ (-η) * volume unitBall.carrier := by
    have h4 : F.toBodyFamily.mass / volume unitBall.carrier ≤ Kakeya.realRpowENN δ (-η) := h2
    have h5 : F.toBodyFamily.mass =
        (F.toBodyFamily.mass / volume unitBall.carrier) * volume unitBall.carrier := by
      rw [ENNReal.div_mul_cancel hvol_pos.ne' hvol_ne_top]
    rw [h5]
    exact mul_le_mul_of_nonneg_right h4 (by simp)
  have h4 : F.enncard * Kakeya.deltaTubeVolume δ ≤
      Kakeya.realRpowENN δ (-η) * volume unitBall.carrier := by
    have h41 : F.nominalMass = F.enncard * Kakeya.deltaTubeVolume δ := by rfl
    rw [←h41, ←h_mass_eq]
    exact h3
  have h6 : Kakeya.deltaTubeVolume δ ≥
      ENNReal.ofReal (Real.pi / 6) * Kakeya.realRpowENN δ 3 := by
    have h7 := deltaTube_volume_lower_bound hδ_pos
    have hpi_pos : 0 ≤ Real.pi / 6 := by positivity
    have h9 : Kakeya.realRpowENN δ 3 = ENNReal.ofReal (δ ^ 3) := by
      simp [Kakeya.realRpowENN] <;> rfl
    have h8 : ENNReal.ofReal (Real.pi / 6 * δ^3) =
        ENNReal.ofReal (Real.pi / 6) * Kakeya.realRpowENN δ 3 := by
      rw [h9, ← ENNReal.ofReal_mul hpi_pos] <;> rfl
    rw [h8] at h7
    exact h7
  set A : ENNReal := ENNReal.ofReal (Real.pi / 6) with hA_def
  set B : ENNReal := Kakeya.realRpowENN δ 3 with hB_def
  have hA_pos : 0 < A := by simp [hA_def] <;> positivity
  have hA_ne_top : A ≠ ⊤ := by simp [hA_def] <;> exact ENNReal.ofReal_ne_top
  have hB_pos : 0 < B := by simp [hB_def, Kakeya.realRpowENN, hδ_pos] <;> positivity
  have hB_ne_top : B ≠ ⊤ := by simp [hB_def] <;> exact ENNReal.ofReal_ne_top
  have h9 : F.enncard * (A * B) ≤ Kakeya.realRpowENN δ (-η) * volume unitBall.carrier := by
    have h91 : F.enncard * (A * B) ≤ F.enncard * Kakeya.deltaTubeVolume δ :=
      mul_le_mul_of_nonneg_left h6 (by simp)
    exact le_trans h91 h4
  have hAB_ne_zero : A * B ≠ 0 := mul_ne_zero hA_pos.ne' hB_pos.ne'
  have hAB_ne_top : A * B ≠ ⊤ := ENNReal.mul_ne_top hA_ne_top hB_ne_top
  have h_rearr4 : ∀ (a b c d : ENNReal), (a * b) * (c * d) = (a * c) * (b * d) := by
    intro a b c d
    have h1 : (a * b) * (c * d) = a * (b * (c * d)) := by rw [mul_assoc]
    have h2 : b * (c * d) = (b * c) * d := by rw [←mul_assoc]
    have h3 : (c * b) * d = c * (b * d) := by rw [mul_assoc]
    calc (a * b) * (c * d)
         = a * (b * (c * d)) := h1
       _ = a * ((b * c) * d) := by rw [h2]
       _ = a * ((c * b) * d) := by rw [mul_comm b c]
       _ = a * (c * (b * d)) := by rw [h3]
       _ = (a * c) * (b * d) := by rw [←mul_assoc]
  have h11 : (A * B) * (A⁻¹ * B⁻¹) = 1 := by
    have h := h_rearr4 A B A⁻¹ B⁻¹
    rw [h]
    rw [ENNReal.mul_inv_cancel hA_pos.ne' hA_ne_top,
        ENNReal.mul_inv_cancel hB_pos.ne' hB_ne_top]
    <;> simp
  have h10 : (F.enncard * (A * B)) * (A⁻¹ * B⁻¹) = F.enncard := by
    calc (F.enncard * (A * B)) * (A⁻¹ * B⁻¹)
         = F.enncard * ((A * B) * (A⁻¹ * B⁻¹)) := by rw [mul_assoc]
       _ = F.enncard * 1 := by rw [h11]
       _ = F.enncard := by simp
  have h12 : B⁻¹ * Kakeya.realRpowENN δ (-η) = Kakeya.realRpowENN δ (-(3 + η)) := by
    have hpos3 : 0 < δ ^ 3 := by positivity
    have h14 : δ ^ (-3 : ℝ) = (δ ^ 3)⁻¹ := by
      have h141 : δ ^ (-3 : ℝ) = (δ ^ (3 : ℝ))⁻¹ := by
        rw [Real.rpow_neg (by linarith)]
      have h142 : δ ^ (3 : ℝ) = δ ^ 3 := by simp
      rw [h141, h142]
    have h15 : ENNReal.ofReal (δ ^ (-3 : ℝ)) = (ENNReal.ofReal (δ ^ 3))⁻¹ := by
      rw [h14, ENNReal.ofReal_inv_of_pos hpos3]
    have h13 : B⁻¹ = Kakeya.realRpowENN δ (-3) := by
      simpa [hB_def, Kakeya.realRpowENN] using h15.symm
    rw [h13]
    have h14' : (-3 : ℝ) + (-η) = -(3 + η) := by ring
    rw [← realRpowENN_add hδ_pos, h14']
  have h_rearrange : (Kakeya.realRpowENN δ (-η) * volume unitBall.carrier) * (A⁻¹ * B⁻¹) =
      volume unitBall.carrier * A⁻¹ * (B⁻¹ * Kakeya.realRpowENN δ (-η)) := by
    set d_eta : ENNReal := Kakeya.realRpowENN δ (-η) with hd_eta_def
    set V : ENNReal := volume unitBall.carrier with hV_def
    have h1 : (d_eta * V) * (A⁻¹ * B⁻¹) = (V * A⁻¹) * (d_eta * B⁻¹) := by
      have h2 : (d_eta * V) * (A⁻¹ * B⁻¹) = (V * d_eta) * (A⁻¹ * B⁻¹) := by
        rw [mul_comm d_eta V]
      rw [h2]
      exact h_rearr4 V d_eta A⁻¹ B⁻¹
    have h_main : (d_eta * V) * (A⁻¹ * B⁻¹) = V * A⁻¹ * (B⁻¹ * d_eta) := by
      rw [h1]
      have h3 : d_eta * B⁻¹ = B⁻¹ * d_eta := mul_comm d_eta B⁻¹
      rw [h3] <;> rfl
    exact h_main
  calc F.enncard
       = (F.enncard * (A * B)) * (A⁻¹ * B⁻¹) := h10.symm
   _ ≤ (Kakeya.realRpowENN δ (-η) * volume unitBall.carrier) * (A⁻¹ * B⁻¹) := by gcongr
   _ = volume unitBall.carrier * A⁻¹ * (B⁻¹ * Kakeya.realRpowENN δ (-η)) := h_rearrange
   _ = volume unitBall.carrier * A⁻¹ * Kakeya.realRpowENN δ (-(3 + η)) := by rw [h12]

/-!
## Katz-Tao estimate at exponent 1 and monotonicity
-/

theorem katz_tao_one : KatzTaoEstimate 1 := by
  have h₁ : 0 ≤ (1 : ℝ) := by norm_num
  have h₂ : (1 : ℝ) ≤ 1 := by norm_num
  refine ⟨h₁, h₂, fun ε hε => ?_⟩
  use 1, 1
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  intro δ hδ hδ₀ F hFnonempty hFball hFdistinct hFkt Y hYdense
  have h3 : ∀ (i : Fin F.card), MeasureTheory.volume (Y.carrier i) ≤ MeasureTheory.volume Y.union := by
    intro i
    apply MeasureTheory.measure_mono
    intro x hx
    exact ⟨i, hx⟩
  have h4 : Y.mass ≤ F.enncard * MeasureTheory.volume Y.union := by
    calc Y.mass
      = ∑ i : Fin F.card, MeasureTheory.volume (Y.carrier i) := by rfl
    _ ≤ ∑ i : Fin F.card, MeasureTheory.volume Y.union := by
        apply Finset.sum_le_sum
        intro i _
        exact h3 i
    _ = (F.card : ENNReal) * MeasureTheory.volume Y.union := by
        rw [Finset.sum_const, Finset.card_fin]
        ring
    _ = F.enncard * MeasureTheory.volume Y.union := by rfl
  have h5 : ENNReal.rpow F.enncard 1 = F.enncard := ENNReal.rpow_one F.enncard
  have h61 : (1 : ℝ) ≤ Real.rpow δ (-ε) := by
    have h_pos : 0 < δ := hδ
    have h_le1 : δ ≤ 1 := hδ₀
    have h_rpow_le1 : Real.rpow δ ε ≤ 1 := by
      apply Real.rpow_le_one <;> linarith
    have h_rpow_pos : 0 < Real.rpow δ ε := Real.rpow_pos_of_pos h_pos ε
    have h_neg_rpow : Real.rpow δ (-ε) = (Real.rpow δ ε)⁻¹ := by
      simp [Real.rpow_neg h_pos.le]
    rw [h_neg_rpow]
    have h : (1 : ℝ) ≤ (Real.rpow δ ε)⁻¹ := by
      calc (Real.rpow δ ε)⁻¹
        ≥ (1 : ℝ)⁻¹ := by gcongr
      _ = 1 := by norm_num
    exact h
  have h6 : (1 : ENNReal) ≤ Kakeya.realRpowENN δ (-ε) := by
    have h62 : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal (Real.rpow δ (-ε)) :=
      ENNReal.ofReal_le_ofReal h61
    simp [Kakeya.realRpowENN] at h62 ⊢
    exact h62
  rw [h5]
  have h7 : F.enncard * MeasureTheory.volume Y.union ≤
      (Kakeya.realRpowENN δ (-ε)) * (F.enncard * MeasureTheory.volume Y.union) := by
    have h8 : (1 : ENNReal) ≤ Kakeya.realRpowENN δ (-ε) := h6
    have h9 : (1 : ENNReal) * (F.enncard * MeasureTheory.volume Y.union) ≤
        (Kakeya.realRpowENN δ (-ε)) * (F.enncard * MeasureTheory.volume Y.union) := by
      gcongr
    simp at h9
    exact h9
  have h10 : (Kakeya.realRpowENN δ (-ε)) * (F.enncard * MeasureTheory.volume Y.union) =
      (Kakeya.realRpowENN δ (-ε) * F.enncard) * MeasureTheory.volume Y.union := by
    ring
  rw [h10] at h7
  exact le_trans h4 h7

/-- Monotonicity of KatzTaoEstimate in the exponent: larger exponent gives weaker bound. -/
theorem katz_tao_mono {β α : ℝ} (h : KatzTaoEstimate β) (hβα : β ≤ α) (hα1 : α ≤ 1) :
    KatzTaoEstimate α := by
  have hβ0 : 0 ≤ β := h.1
  have hα0 : 0 ≤ α := by linarith
  refine ⟨hα0, hα1, fun ε hε => ?_⟩
  rcases h.2.2 ε hε with ⟨η, δ₀, hη, hδ₀, hδ₀1, h_main⟩
  refine ⟨η, δ₀, hη, hδ₀, hδ₀1, fun δ hδ hδle F hFnonempty hFball hFdistinct hFkt Y hYdense => ?_⟩
  have h_prev : Y.HasAverageMultiplicityAtMost
      (Kakeya.realRpowENN δ (-ε) * ENNReal.rpow F.enncard β) :=
    h_main δ hδ hδle F hFnonempty hFball hFdistinct hFkt Y hYdense
  have h_card1 : (1 : ENNReal) ≤ F.enncard := by
    exact Nat.one_le_cast.mpr hFnonempty
  have h_rpow_mono : ENNReal.rpow F.enncard β ≤ ENNReal.rpow F.enncard α :=
    ENNReal.rpow_le_rpow_of_exponent_le h_card1 hβα
  have h_mul_mono : Kakeya.realRpowENN δ (-ε) * ENNReal.rpow F.enncard β ≤
      Kakeya.realRpowENN δ (-ε) * ENNReal.rpow F.enncard α := by
    gcongr
  have h_prev' : Y.mass ≤ (Kakeya.realRpowENN δ (-ε) * ENNReal.rpow F.enncard β) * MeasureTheory.volume Y.union := h_prev
  have h_final : Y.mass ≤ (Kakeya.realRpowENN δ (-ε) * ENNReal.rpow F.enncard α) * MeasureTheory.volume Y.union := by
    calc Y.mass
      ≤ (Kakeya.realRpowENN δ (-ε) * ENNReal.rpow F.enncard β) * MeasureTheory.volume Y.union := h_prev'
    _ ≤ (Kakeya.realRpowENN δ (-ε) * ENNReal.rpow F.enncard α) * MeasureTheory.volume Y.union := by gcongr
  exact h_final

/-!
## Finite iteration lemma
-/

/-- Sequence `β_0 = 1`, `β_{n+1} = β_n - ν(β_n)`. -/
private def iterationSeq (ν : ℝ → ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => iterationSeq ν n - ν (iterationSeq ν n)

/-- The trivial Katz--Tao estimate at exponent 1: average multiplicity is at
most `#F`, and `δ^{-ε} ≥ 1` absorbs the extra factor. -/
lemma katz_tao_estimate_one : KatzTaoEstimate 1 := by
  refine' ⟨by norm_num, by norm_num, _⟩
  intro epsilon hepsilon
  refine' ⟨1, 1, by norm_num, by norm_num, by norm_num, _⟩
  intro delta hdelta hdelta0 F _ _ _ _ Y _
  have h1 : ∀ (i : Fin F.card), MeasureTheory.volume (Y.carrier i) ≤
        MeasureTheory.volume Y.union := by
    intro i
    apply MeasureTheory.measure_mono
    intro x hx
    exact ⟨i, hx⟩
  have h2 : Y.mass ≤ ∑ i : Fin F.card, MeasureTheory.volume Y.union := by
    apply Finset.sum_le_sum
    intro i _
    exact h1 i
  have h3 : ∑ i : Fin F.card, MeasureTheory.volume Y.union =
        F.enncard * MeasureTheory.volume Y.union := by
    simp [TubeFamily.enncard, Finset.sum_const]
  have h_mass_le : Y.mass ≤ F.enncard * MeasureTheory.volume Y.union :=
    h2.trans_eq h3
  have h_rpow_one : ENNReal.rpow F.enncard 1 = F.enncard := by simp
  have h5 : Real.rpow delta (-epsilon) ≥ 1 := by
    have h6 : 0 < Real.rpow delta epsilon := Real.rpow_pos_of_pos hdelta _
    have h7 : Real.rpow delta epsilon ≤ 1 :=
      Real.rpow_le_one (by linarith) (by linarith) (by linarith)
    have h_prod : Real.rpow delta (-epsilon) * Real.rpow delta epsilon = 1 := by
      have h_add : Real.rpow delta (-epsilon) * Real.rpow delta epsilon =
            Real.rpow delta ((-epsilon) + epsilon) :=
        (Real.rpow_add (by linarith) (-epsilon) epsilon).symm
      rw [h_add]
      have h_zero : (-epsilon : ℝ) + epsilon = 0 := by ring
      rw [h_zero]
      simp
    have h_inv : Real.rpow delta (-epsilon) = (Real.rpow delta epsilon)⁻¹ := by
      field_simp [h6.ne'] at h_prod ⊢
      exact h_prod
    rw [h_inv]
    exact (one_le_inv₀ h6).mpr h7
  have h10 : (1 : ENNReal) ≤ Kakeya.realRpowENN delta (-epsilon) := by
    have h11 : (1 : ENNReal) ≤ ENNReal.ofReal (Real.rpow delta (-epsilon)) :=
      ENNReal.one_le_ofReal.mpr h5
    simpa [Kakeya.realRpowENN] using h11
  have h13 : F.enncard ≤ Kakeya.realRpowENN delta (-epsilon) * F.enncard :=
    le_mul_of_one_le_left' h10
  have h14 : F.enncard * MeasureTheory.volume Y.union ≤
        (Kakeya.realRpowENN delta (-epsilon) * F.enncard) *
          MeasureTheory.volume Y.union := by
    have h15 : F.enncard * MeasureTheory.volume Y.union ≤
          (Kakeya.realRpowENN delta (-epsilon) * F.enncard) *
            MeasureTheory.volume Y.union := by
      apply mul_le_mul_of_nonneg_right h13
      positivity
    exact h15
  rw [h_rpow_one]
  exact h_mass_le.trans h14

/-- Finite iteration: for any `β₀ > 0`, there exists `0 ≤ β < β₀` with
`KatzTaoEstimate β`. -/
theorem iteration_lemma (hML1 : MainLemma1Statement)
    (hML2 : MainLemma2Statement)
    (hSticky : GWZStickyVolumeSocket)
    (hVNS : VeryNotStickyStatement) :
    ∀ (β0 : ℝ), 0 < β0 → ∃ (β : ℝ), 0 ≤ β ∧ β < β0 ∧ KatzTaoEstimate β := by
  rcases hML2 hSticky hVNS with ⟨ν, hν_mono, hν_prop⟩
  have hKT1 : KatzTaoEstimate 1 := katz_tao_estimate_one
  let β := iterationSeq ν
  have hβ_zero : β 0 = 1 := by simp [β, iterationSeq]
  have hβ_succ : ∀ n, β (n + 1) = β n - ν (β n) := by
    intro n
    simp [β, iterationSeq]
  have h_inv : ∀ n, 0 < β n ∧ β n ≤ 1 ∧ KatzTaoEstimate (β n) := by
    intro n
    induction n with
    | zero =>
      rw [hβ_zero]
      exact ⟨by norm_num, by norm_num, hKT1⟩
    | succ n ih =>
      have hpos : 0 < β n := ih.1
      have hle : β n ≤ 1 := ih.2.1
      have hkt : KatzTaoEstimate (β n) := ih.2.2
      have hfr : FrostmanEstimate (β n) :=
        hML1 hSticky (β n) (by linarith) (by linarith) hkt
      have hν_pos : 0 < ν (β n) := (hν_prop (β n) hpos hle).1
      have hν_lt : ν (β n) < β n := (hν_prop (β n) hpos hle).2.1
      have h_next : KatzTaoEstimate (β n - ν (β n)) :=
        (hν_prop (β n) hpos hle).2.2 hkt hfr
      have h_eq : β (n + 1) = β n - ν (β n) := hβ_succ n
      rw [h_eq]
      exact ⟨by linarith, by linarith, h_next⟩
  intro β0 hβ0
  by_cases h_big : β0 > 1
  · exact ⟨1, by norm_num, by linarith, hKT1⟩
  · have hβ0_le : β0 ≤ 1 := by linarith
    have hνβ0_pos : 0 < ν β0 := (hν_prop β0 hβ0 hβ0_le).1
    have h_exists : ∃ n : ℕ, β n < β0 := by
      by_contra h
      push Not at h
      have h_ge : ∀ n, β n ≥ β0 := h
      have hν_ge : ∀ n, ν (β n) ≥ ν β0 := by
        intro n
        have h1 : β0 ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
        have h2 : β n ∈ Set.Icc (0 : ℝ) 1 :=
          ⟨by linarith [(h_inv n).1], (h_inv n).2.1⟩
        have h3 : β0 ≤ β n := h_ge n
        exact hν_mono h1 h2 h3
      have h_step : ∀ n, β (n + 1) ≤ β n - ν β0 := by
        intro n
        have h_eq : β (n + 1) = β n - ν (β n) := hβ_succ n
        rw [h_eq]
        linarith [hν_ge n]
      have h_bound : ∀ n : ℕ, β n ≤ 1 - (n : ℝ) * ν β0 := by
        intro n
        induction n with
        | zero =>
          rw [hβ_zero]
          ; norm_num
        | succ n ih =>
          calc
            β (n + 1) ≤ β n - ν β0 := h_step n
            _ ≤ 1 - (n : ℝ) * ν β0 - ν β0 := by linarith
            _ = 1 - ((n + 1 : ℕ) : ℝ) * ν β0 := by
              simp [Nat.cast_add, Nat.cast_one]
              ring
      have h_arch : ∃ n : ℕ, 1 < (n : ℝ) * ν β0 := by
        have h_pos : 0 < ν β0 := hνβ0_pos
        obtain ⟨n, hn⟩ := exists_nat_gt (1 / ν β0)
        refine' ⟨n, _⟩
        have h : (n : ℝ) > 1 / ν β0 := hn
        calc
          (n : ℝ) * ν β0 > (1 / ν β0) * ν β0 := by gcongr
          _ = 1 := by
            field_simp [h_pos.ne']
      rcases h_arch with ⟨n, hn⟩
      have h_neg : β n < 0 := by linarith [h_bound n]
      have h_pos : 0 < β n := (h_inv n).1
      linarith
    rcases h_exists with ⟨n, hn⟩
    exact ⟨β n, by linarith [(h_inv n).1], hn, (h_inv n).2.2⟩

/-!
## Final derivation
-/

/-- K_KT at all positive exponents implies GeneralKakeya. -/
theorem final_derivation (h : ∀ (α : ℝ), 0 < α → α ≤ 1 → KatzTaoEstimate α) :
    GeneralKakeyaStatement := by
  intro β_target hβ_target
  set β : ℝ := min β_target 1 with hβ_def
  have hβ_pos : 0 < β := by
    simp [hβ_def, hβ_target] <;> norm_num <;> linarith
  have hβ_le_one : β ≤ 1 := by
    simp [hβ_def] <;> norm_num
  set α : ℝ := β / 8 with hα_def
  set ε : ℝ := β / 8 with hε_def
  have hα_pos : 0 < α := by positivity
  have hα_le_one : α ≤ 1 := by linarith
  have hε_pos : 0 < ε := by positivity
  have hKα : KatzTaoEstimate α := h α hα_pos hα_le_one
  rcases hKα.2.2 ε hε_pos with ⟨η₀, δ₀_kt, hη₀_pos, hδ₀_kt_pos, hδ₀_kt_le_one, hKT_main⟩
  set η : ℝ := min η₀ (β / 4) with hη_def
  have hη_pos : 0 < η := by
    simp [hη_def, hη₀_pos, hβ_pos] <;> linarith
  have hη_le_η₀ : η ≤ η₀ := by
    simp [hη_def] <;> exact min_le_left _ _
  have hη_le_β4 : η ≤ β / 4 := by
    simp [hη_def] <;> exact min_le_right _ _
  set γ : ℝ := β - η - ε - α * (3 + η) with hγ_def
  have hγ_pos : 0 < γ := by
    rw [hγ_def, hα_def, hε_def]
    have h1 : η ≤ β / 4 := hη_le_β4
    nlinarith [sq_nonneg (β - 1)]
  let C : ENNReal :=
    (volume unitBall.carrier) * (ENNReal.ofReal (Real.pi / 6))⁻¹
  have hvol_ne_top : volume unitBall.carrier ≠ ⊤ := unitBall_volume_pos_and_lt_top.2
  have hpi_pos : 0 < Real.pi / 6 := by positivity
  have hA_ne_zero : ENNReal.ofReal (Real.pi / 6) ≠ 0 := by
    have h : 0 < ENNReal.ofReal (Real.pi / 6) := ENNReal.ofReal_pos.mpr hpi_pos
    exact h.ne'
  have hpi_ne_top : (ENNReal.ofReal (Real.pi / 6))⁻¹ ≠ ⊤ := by
    exact ENNReal.inv_ne_top.mpr hA_ne_zero
  have hC_ne_top : C ≠ ⊤ := ENNReal.mul_ne_top hvol_ne_top hpi_ne_top
  set C_pow : ENNReal := ENNReal.rpow C α with hC_pow_def
  have hC_pow_ne_top : C_pow ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by linarith) hC_ne_top
  rcases exists_delta_pow_bound C_pow hC_pow_ne_top hγ_pos with
    ⟨δ₀_const, hδ₀_const_pos, hδ_const⟩
  set δ₀ : ℝ := min (min δ₀_kt δ₀_const) (1 / 2) with hδ₀_def
  have hδ₀_pos : 0 < δ₀ := by
    simp [hδ₀_def, hδ₀_kt_pos, hδ₀_const_pos] <;> positivity
  have hδ₀_le_one : δ₀ ≤ 1 := by
    simp [hδ₀_def] <;> norm_num
  refine ⟨η, δ₀, hη_pos, hδ₀_pos, hδ₀_le_one, ?_⟩
  intro δ hδ_pos hδ_le
  intro F hF_ball hF_distinct hKT_cond
  intro Y hY_dense
  by_cases hF_empty : F.card = 0
  · have h_nom : F.nominalMass = 0 := by
      simp [TubeFamily.nominalMass, TubeFamily.enncard, hF_empty] <;> simp
    rw [h_nom] <;> simp
  · have hF_nonempty : F.Nonempty := by
      simp [TubeFamily.Nonempty] <;> omega
    have hδ_le_kt : δ ≤ δ₀_kt := by
      have h1 : δ ≤ δ₀ := hδ_le
      have h2 : δ₀ ≤ min δ₀_kt δ₀_const := min_le_left _ _
      have h3 : δ ≤ min δ₀_kt δ₀_const := le_trans h1 h2
      exact le_trans h3 (min_le_left _ _)
    have hδ_le_const : δ ≤ δ₀_const := by
      have h1 : δ ≤ δ₀ := hδ_le
      have h2 : δ₀ ≤ min δ₀_kt δ₀_const := min_le_left _ _
      have h3 : δ ≤ min δ₀_kt δ₀_const := le_trans h1 h2
      exact le_trans h3 (min_le_right _ _)
    have hδ_le_one' : δ ≤ 1 := by linarith
    have h_mult : Y.HasAverageMultiplicityAtMost
        (Kakeya.realRpowENN δ (-ε) * ENNReal.rpow F.enncard α) :=
      katz_tao_shrink_eta hη_le_η₀ hδ_pos hδ_le_one'
        (hKT_main δ hδ_pos hδ_le_kt) hF_nonempty hF_ball hF_distinct hKT_cond hY_dense
    have h_card : F.enncard ≤ C * Kakeya.realRpowENN δ (-(3 + η)) :=
      card_bound_from_kt hδ_pos hδ_le_one' hF_ball hKT_cond
    have hα_nonneg : 0 ≤ α := by linarith
    have h_rpow1 : ENNReal.rpow (C * Kakeya.realRpowENN δ (-(3 + η))) α =
        C_pow * ENNReal.rpow (Kakeya.realRpowENN δ (-(3 + η))) α := by
      have h : (C * Kakeya.realRpowENN δ (-(3 + η))) ^ α =
          C ^ α * (Kakeya.realRpowENN δ (-(3 + η))) ^ α :=
        ENNReal.mul_rpow_of_nonneg C (Kakeya.realRpowENN δ (-(3 + η))) hα_nonneg
      have h_eq1 : ENNReal.rpow (C * Kakeya.realRpowENN δ (-(3 + η))) α =
          (C * Kakeya.realRpowENN δ (-(3 + η))) ^ α := ENNReal.rpow_eq_pow _ _
      have h_eq2 : ENNReal.rpow (Kakeya.realRpowENN δ (-(3 + η))) α =
          (Kakeya.realRpowENN δ (-(3 + η))) ^ α := ENNReal.rpow_eq_pow _ _
      have hC_pow_eq : C ^ α = C_pow := by rw [hC_pow_def] <;> rfl
      rw [h_eq1, h_eq2, h, hC_pow_eq]
    have hpos_exp : 0 ≤ δ ^ (-(3 + η)) := by positivity
    have h_rpow2 : ENNReal.rpow (Kakeya.realRpowENN δ (-(3 + η))) α =
        Kakeya.realRpowENN δ (-α * (3 + η)) := by
      have h : (ENNReal.ofReal (δ ^ (-(3 + η)))) ^ α =
          ENNReal.ofReal ((δ ^ (-(3 + η))) ^ α) :=
        ENNReal.ofReal_rpow_of_nonneg hpos_exp hα_nonneg
      have hδ_nonneg : 0 ≤ δ := by linarith
      have hmul : (δ ^ (-(3 + η))) ^ α = δ ^ ((-(3 + η)) * α) :=
        (Real.rpow_mul (x := δ) hδ_nonneg (-(3 + η)) α).symm
      have hcomm : (-(3 + η)) * α = -α * (3 + η) := by ring
      have h_eq : ENNReal.rpow (Kakeya.realRpowENN δ (-(3 + η))) α =
          (Kakeya.realRpowENN δ (-(3 + η))) ^ α := ENNReal.rpow_eq_pow _ _
      have h_def : Kakeya.realRpowENN δ (-(3 + η)) = ENNReal.ofReal (δ ^ (-(3 + η))) := by
        simp [Kakeya.realRpowENN] <;> rfl
      have h_goal : ENNReal.ofReal (δ ^ (-α * (3 + η))) = Kakeya.realRpowENN δ (-α * (3 + η)) := by
        simp [Kakeya.realRpowENN] <;> rfl
      rw [h_eq, h_def, h, hmul, hcomm, h_goal]
    have h_card_pow : ENNReal.rpow F.enncard α ≤
        C_pow * Kakeya.realRpowENN δ (-α * (3 + η)) := by
      have h_rpow_mono : ENNReal.rpow F.enncard α ≤
          ENNReal.rpow (C * Kakeya.realRpowENN δ (-(3 + η))) α :=
        ENNReal.rpow_le_rpow h_card hα_nonneg
      rw [h_rpow1, h_rpow2] at h_rpow_mono
      exact h_rpow_mono
    have h_const : C_pow ≤ Kakeya.realRpowENN δ (-γ) :=
      hδ_const δ hδ_pos hδ_le_const
    have h_main_ineq : ENNReal.rpow F.enncard α ≤
        Kakeya.realRpowENN δ (η + ε - β) := by
      calc ENNReal.rpow F.enncard α
           ≤ C_pow * Kakeya.realRpowENN δ (-α * (3 + η)) := h_card_pow
         _ ≤ Kakeya.realRpowENN δ (-γ) * Kakeya.realRpowENN δ (-α * (3 + η)) := by gcongr
         _ = Kakeya.realRpowENN δ (η + ε - β) := by
             have hsum : -γ + (-α * (3 + η)) = η + ε - β := by
               rw [hγ_def] <;> ring
             rw [← realRpowENN_add hδ_pos, hsum]
    have h_mass_eq : F.toBodyFamily.mass = F.nominalMass :=
      family_mass_eq_nominal F
    set P : ENNReal := ENNReal.rpow F.enncard α with hP_def
    have hF_enncard_pos : 0 < F.enncard := by
      have h : 0 < F.card := Nat.pos_of_ne_zero hF_empty
      have h' : (F.card : ENNReal) > 0 := by exact_mod_cast h
      simpa [TubeFamily.enncard] using h'
    have hF_enncard_ne_top : F.enncard ≠ ⊤ := by
      simp [TubeFamily.enncard]
    have hP_pos : 0 < P := by
      exact ENNReal.rpow_pos (hx_pos := hF_enncard_pos) (hx_ne_top := hF_enncard_ne_top)
    have hP_ne_top : P ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg (by linarith) hF_enncard_ne_top
    have hprod : Kakeya.realRpowENN δ β * P ≤ Kakeya.realRpowENN δ (η + ε) := by
      calc Kakeya.realRpowENN δ β * P
           ≤ Kakeya.realRpowENN δ β * Kakeya.realRpowENN δ (η + ε - β) := by gcongr
         _ = Kakeya.realRpowENN δ (β + (η + ε - β)) := by
             rw [← realRpowENN_add hδ_pos]
         _ = Kakeya.realRpowENN δ (η + ε) := by
             have hsum : β + (η + ε - β) = η + ε := by ring
             rw [hsum]
    have hY1 : Kakeya.realRpowENN δ η * F.toBodyFamily.mass ≤ Y.mass := hY_dense
    have hY2 : Y.mass ≤
        Kakeya.realRpowENN δ (-ε) * P * volume Y.union := h_mult
    have hY3 : Kakeya.realRpowENN δ η * F.nominalMass ≤
        Kakeya.realRpowENN δ (-ε) * P * volume Y.union := by
      rw [h_mass_eq] at hY1
      exact le_trans hY1 hY2
    have h_eps_inv : Kakeya.realRpowENN δ ε * Kakeya.realRpowENN δ (-ε) = 1 := by
      have h : Kakeya.realRpowENN δ ε * Kakeya.realRpowENN δ (-ε) =
          Kakeya.realRpowENN δ (ε + (-ε)) := by
        rw [← realRpowENN_add hδ_pos]
      rw [h]
      have h2 : ε + (-ε) = 0 := by ring
      rw [h2]
      simp [Kakeya.realRpowENN] <;> norm_num
    have hY4 : Kakeya.realRpowENN δ (η + ε) * F.nominalMass ≤ P * volume Y.union := by
      calc Kakeya.realRpowENN δ (η + ε) * F.nominalMass
           = Kakeya.realRpowENN δ ε * (Kakeya.realRpowENN δ η * F.nominalMass) := by
             have h : Kakeya.realRpowENN δ (η + ε) =
                 Kakeya.realRpowENN δ ε * Kakeya.realRpowENN δ η := by
               rw [← realRpowENN_add hδ_pos] <;> ring_nf
             rw [h] <;> simp [mul_assoc]
         _ ≤ Kakeya.realRpowENN δ ε * (Kakeya.realRpowENN δ (-ε) * P * volume Y.union) := by
             gcongr
         _ = P * volume Y.union := by
             have h_assoc : Kakeya.realRpowENN δ ε * (Kakeya.realRpowENN δ (-ε) * P * volume Y.union) =
                 (Kakeya.realRpowENN δ ε * Kakeya.realRpowENN δ (-ε)) * (P * volume Y.union) := by
               simp [mul_assoc, mul_comm, mul_left_comm]
               <;> rfl
             rw [h_assoc, h_eps_inv] <;> simp
    have h5 : Kakeya.realRpowENN δ β * P * F.nominalMass ≤ P * volume Y.union := by
      calc Kakeya.realRpowENN δ β * P * F.nominalMass
           = (Kakeya.realRpowENN δ β * P) * F.nominalMass := by rw [mul_assoc]
         _ ≤ Kakeya.realRpowENN δ (η + ε) * F.nominalMass := by gcongr
         _ ≤ P * volume Y.union := hY4
    have h6 : Kakeya.realRpowENN δ β * F.nominalMass ≤ volume Y.union := by
      have h7 : Kakeya.realRpowENN δ β * F.nominalMass * P ≤ volume Y.union * P := by
        have h71 : Kakeya.realRpowENN δ β * F.nominalMass * P = Kakeya.realRpowENN δ β * P * F.nominalMass := by
          calc Kakeya.realRpowENN δ β * F.nominalMass * P
               = Kakeya.realRpowENN δ β * (F.nominalMass * P) := by rw [mul_assoc]
             _ = Kakeya.realRpowENN δ β * (P * F.nominalMass) := by rw [mul_comm F.nominalMass P]
             _ = Kakeya.realRpowENN δ β * P * F.nominalMass := by rw [←mul_assoc]
        have h72 : P * volume Y.union = volume Y.union * P := mul_comm P (volume Y.union)
        rw [h71]
        have h : Kakeya.realRpowENN δ β * P * F.nominalMass ≤ P * volume Y.union := h5
        rw [h72] at h
        exact h
      have h8 : Kakeya.realRpowENN δ β * F.nominalMass ≤ volume Y.union := by
        exact (ENNReal.mul_le_mul_iff_left hP_pos.ne' hP_ne_top).mp h7
      exact h8
    by_cases h_case : β_target ≤ 1
    · have hβ_eq : β = β_target := by
        simp [hβ_def, h_case] <;> linarith
      rw [hβ_eq] at h6
      exact h6
    · have hβ_eq : β = 1 := by
        simp [hβ_def, h_case] <;> linarith
      have h_le : Kakeya.realRpowENN δ β_target ≤ Kakeya.realRpowENN δ β := by
        rw [hβ_eq]
        exact realRpowENN_antitone hδ_pos hδ_le_one' (by linarith)
      calc Kakeya.realRpowENN δ β_target * F.nominalMass
           ≤ Kakeya.realRpowENN δ β * F.nominalMass := by gcongr
         _ ≤ volume Y.union := h6

/-!
## Target theorem
-/

theorem sticky_implies_general : StickyImpliesGeneralStatement := by
  intro hSticky hVNS hML1 hML2
  have h_iter : ∀ (β₀ : ℝ), 0 < β₀ → ∃ (β : ℝ), 0 ≤ β ∧ β < β₀ ∧ KatzTaoEstimate β :=
    iteration_lemma hML1 hML2 hSticky hVNS
  have h_all : ∀ (α : ℝ), 0 < α → α ≤ 1 → KatzTaoEstimate α := by
    intro α hα_pos hα_le1
    rcases h_iter α hα_pos with ⟨β, hβ_ge0, hβ_lt, hKβ⟩
    exact katz_tao_mono hKβ (by linarith) hα_le1
  exact final_derivation h_all

end Kakeya.Streamlined
