import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushTwoBroadLeaves
import MyLeanRepo.Kakeya.Assouad.TubeVolumeScaling
import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.TubeReversal
import MyLeanRepo.Kakeya.Hairbrush.Basic

/-!
# Orientation infrastructure for Raw-B

Reversing a tube preserves its carrier. This allows converting an acute-angle
hairbrush into an ordinary-angle hairbrush by choosing, for each band hair, the
orientation that makes the angle with the stem at most `π/2`.
-/

noncomputable section

open MeasureTheory Metric Set Finset Real

attribute [local instance] Classical.propDecidable

namespace Kakeya.Assouad

variable {δ : ℝ}

/-- Angle between T and the reverse of U. -/
lemma angleBetween_reverse (T U : DeltaTube δ) :
    angleBetween T (reverseTube U) = Real.pi - angleBetween T U := by
  have h1 : inner ℝ T.direction (reverseTube U).direction =
           -inner ℝ T.direction U.direction := by
    unfold reverseTube
    simp [inner_neg_right]
  rw [angleBetween, angleBetween, h1]
  exact Real.arccos_neg (inner ℝ T.direction U.direction)

/-- The acute angle equals the ordinary angle when it is at most π/2. -/
lemma acuteAngle_eq_angleBetween_le_pi2 (T U : DeltaTube δ)
    (h : angleBetween T U ≤ Real.pi / 2) :
    hairbrushAcuteAngle T U = angleBetween T U := by
  have h3 : angleBetween T U ≤ Real.pi - angleBetween T U := by linarith
  have h_def : hairbrushAcuteAngle T U =
      min (angleBetween T U) (Real.pi - angleBetween T U) := by
    simp [hairbrushAcuteAngle, hairbrushAcuteDirectionAngle, angleBetween]
    <;> rfl
  rw [h_def, min_eq_left h3]

/-- The acute angle equals π minus the ordinary angle when it exceeds π/2. -/
lemma acuteAngle_eq_angleBetween_reverse_gt_pi2 (T U : DeltaTube δ)
    (h : angleBetween T U > Real.pi / 2) :
    hairbrushAcuteAngle T U = angleBetween T (reverseTube U) := by
  have h4 : Real.pi - angleBetween T U ≤ angleBetween T U := by linarith
  have h_def : hairbrushAcuteAngle T U =
      min (angleBetween T U) (Real.pi - angleBetween T U) := by
    simp [hairbrushAcuteAngle, hairbrushAcuteDirectionAngle, angleBetween]
    <;> rfl
  have h5 : hairbrushAcuteAngle T U = Real.pi - angleBetween T U := by
    rw [h_def, min_eq_right h4]
  rw [h5, angleBetween_reverse]

/--
For any tube U, choose the orientation (U or reverseTube U) that makes the
ordinary angle with T equal to the acute angle.
-/
def orientTube (T U : DeltaTube δ) : DeltaTube δ :=
  if angleBetween T U ≤ Real.pi / 2 then U else reverseTube U

lemma orientTube_carrier (T U : DeltaTube δ) :
    (orientTube T U).carrier = U.carrier := by
  dsimp only [orientTube]
  by_cases h : angleBetween T U ≤ Real.pi / 2
  · rw [if_pos h]
  · rw [if_neg h]
    exact reverseTube_carrier U

lemma orientTube_volume (T U : DeltaTube δ) :
    (orientTube T U).volume = U.volume := by
  unfold DeltaTube.volume
  rw [orientTube_carrier]

lemma orientTube_angle (T U : DeltaTube δ) :
    angleBetween T (orientTube T U) = hairbrushAcuteAngle T U := by
  dsimp only [orientTube]
  by_cases h : angleBetween T U ≤ Real.pi / 2
  · rw [if_pos h]
    exact (acuteAngle_eq_angleBetween_le_pi2 T U h).symm
  · rw [if_neg h]
    exact (acuteAngle_eq_angleBetween_reverse_gt_pi2 T U (by linarith)).symm

lemma orientTube_angle_le_pi2 (T U : DeltaTube δ) :
    angleBetween T (orientTube T U) ≤ Real.pi / 2 := by
  rw [orientTube_angle]
  have h_def : hairbrushAcuteAngle T U =
      min (angleBetween T U) (Real.pi - angleBetween T U) := by
    simp [hairbrushAcuteAngle, hairbrushAcuteDirectionAngle, angleBetween] <;> rfl
  rw [h_def]
  by_cases h4 : angleBetween T U ≤ Real.pi / 2
  · have h5 : min (angleBetween T U) (Real.pi - angleBetween T U) = angleBetween T U := by
      apply min_eq_left
      linarith
    rw [h5] <;> linarith
  · have h5 : min (angleBetween T U) (Real.pi - angleBetween T U) = Real.pi - angleBetween T U := by
      apply min_eq_right
      linarith
    rw [h5] <;> linarith

/--
The band of tubes in F3 at acute angle [σ, 2σ] from the stem, excluding the
stem itself, and whose carrier intersects the stem.
-/
def acuteBandFamily
    {F : TubeFamily δ} {Y : Shading F}
    {eta theta aCore zetaEnds bTube : ℝ}
    (core : HairbrushMultiplicityDenseTwoEndsCoreData Y eta theta aCore zetaEnds bTube)
    (transverse : HairbrushAcuteRobustTransverseData core) :
    TubeFamily δ :=
  core.F3.filter fun U =>
    U ≠ transverse.stem ∧
    transverse.sigma ≤ hairbrushAcuteAngle transverse.stem U ∧
    hairbrushAcuteAngle transverse.stem U ≤ 2 * transverse.sigma ∧
    (transverse.stem.carrier ∩ U.carrier).Nonempty

/--
The oriented version of the acute band family. Each tube is oriented so that
its ordinary angle with the stem is in [σ, 2σ] and at most π/2.
-/
def orientedBandFamily
    {F : TubeFamily δ} {Y : Shading F}
    {eta theta aCore zetaEnds bTube : ℝ}
    (core : HairbrushMultiplicityDenseTwoEndsCoreData Y eta theta aCore zetaEnds bTube)
    (transverse : HairbrushAcuteRobustTransverseData core) :
    TubeFamily δ :=
  (acuteBandFamily core transverse).image (orientTube transverse.stem)

lemma orientedBandFamily_injOn
    {F : TubeFamily δ} {Y : Shading F}
    {eta theta aCore zetaEnds bTube : ℝ}
    (core : HairbrushMultiplicityDenseTwoEndsCoreData Y eta theta aCore zetaEnds bTube)
    (transverse : HairbrushAcuteRobustTransverseData core)
    (hδ : 0 < δ)
    (h_ed : F.IsEssentiallyDistinct) :
    Set.InjOn (orientTube transverse.stem) (acuteBandFamily core transverse) := by
  intro U hU V hV h
  have hcar : (orientTube transverse.stem U).carrier =
              (orientTube transverse.stem V).carrier := by rw [h]
  have hUcar : (orientTube transverse.stem U).carrier = U.carrier :=
    orientTube_carrier transverse.stem U
  have hVcar : (orientTube transverse.stem V).carrier = V.carrier :=
    orientTube_carrier transverse.stem V
  rw [hUcar, hVcar] at hcar
  have h_inter : U.carrier ∩ V.carrier = U.carrier := by
    rw [hcar] <;> simp
  by_cases hne : U ≠ V
  · have hU_F3 : U ∈ core.F3 := (Finset.mem_filter.mp hU).1
    have hV_F3 : V ∈ core.F3 := (Finset.mem_filter.mp hV).1
    have h_ed' : U.EssentiallyDistinct V :=
      h_ed (core.F3_subset hU_F3) (core.F3_subset hV_F3) hne
    have hvol_int : volume (U.carrier ∩ V.carrier) = U.volume := by
      rw [h_inter] <;> rfl
    have hvol_eq : U.volume = V.volume := by
      unfold DeltaTube.volume
      congr
    have hmax : max U.volume V.volume = U.volume := by
      rw [hvol_eq] <;> simp
    rw [DeltaTube.EssentiallyDistinct, hvol_int, hmax] at h_ed'
    have hvol : TubeVolumeScalingStatement := tube_volume_scaling
    have hT : U.volume = Kakeya.deltaTubeVolume δ := hvol.1 δ U
    have hδ_le_one : δ ≤ 1 := by
      linarith [transverse.delta_le_sigma, transverse.sigma_le_one]
    have h_fin : 0 < Kakeya.deltaTubeVolume δ ∧ Kakeya.deltaTubeVolume δ ≠ ⊤ :=
      hvol.2.1 δ hδ hδ_le_one
    have h_ne_zero : U.volume ≠ 0 := by
      rw [hT] <;> exact h_fin.1.ne'
    have h_ne_top : U.volume ≠ ⊤ := by
      rw [hT] <;> exact h_fin.2
    have h9 : U.volume / 2 < U.volume := ENNReal.half_lt_self h_ne_zero h_ne_top
    have h10 : (2 : ENNReal)⁻¹ * U.volume = U.volume / 2 := by
      rw [div_eq_mul_inv] <;> ring
    rw [h10] at h_ed'
    exact False.elim (not_le.mpr h9 h_ed')
  · simpa using hne

lemma orientedBandFamily_card
    {F : TubeFamily δ} {Y : Shading F}
    {eta theta aCore zetaEnds bTube : ℝ}
    (core : HairbrushMultiplicityDenseTwoEndsCoreData Y eta theta aCore zetaEnds bTube)
    (transverse : HairbrushAcuteRobustTransverseData core)
    (hδ : 0 < δ)
    (h_ed : F.IsEssentiallyDistinct) :
    (orientedBandFamily core transverse).card =
    (acuteBandFamily core transverse).card := by
  have h_inj := orientedBandFamily_injOn core transverse hδ h_ed
  exact Finset.card_image_of_injOn h_inj

lemma orientedBandFamily_angle
    {F : TubeFamily δ} {Y : Shading F}
    {eta theta aCore zetaEnds bTube : ℝ}
    (core : HairbrushMultiplicityDenseTwoEndsCoreData Y eta theta aCore zetaEnds bTube)
    (transverse : HairbrushAcuteRobustTransverseData core)
    {U' : DeltaTube δ}
    (hU' : U' ∈ orientedBandFamily core transverse) :
    transverse.sigma ≤ angleBetween transverse.stem U' ∧
    angleBetween transverse.stem U' ≤ 2 * transverse.sigma := by
  rcases Finset.mem_image.mp hU' with ⟨U, hU, rfl⟩
  have h_band := (Finset.mem_filter.mp hU).2
  have h_angle : angleBetween transverse.stem (orientTube transverse.stem U) =
      hairbrushAcuteAngle transverse.stem U :=
    orientTube_angle transverse.stem U
  rw [h_angle]
  exact ⟨h_band.2.1, h_band.2.2.1⟩

lemma orientedBandFamily_intersects_stem
    {F : TubeFamily δ} {Y : Shading F}
    {eta theta aCore zetaEnds bTube : ℝ}
    (core : HairbrushMultiplicityDenseTwoEndsCoreData Y eta theta aCore zetaEnds bTube)
    (transverse : HairbrushAcuteRobustTransverseData core)
    {U' : DeltaTube δ}
    (hU' : U' ∈ orientedBandFamily core transverse) :
    (transverse.stem.carrier ∩ U'.carrier).Nonempty := by
  rcases Finset.mem_image.mp hU' with ⟨U, hU, rfl⟩
  have h_band := (Finset.mem_filter.mp hU).2
  have hcar : (orientTube transverse.stem U).carrier = U.carrier :=
    orientTube_carrier transverse.stem U
  rw [hcar]
  exact h_band.2.2.2

/-- Transport shading from the original band to the oriented band.

For each oriented tube U', the shading carrier is the union of Z(U) over all
band tubes U that orient to U'. By injectivity, there is at most one such U. -/
def orientedShading
    {F : TubeFamily δ} {Y : Shading F}
    {eta theta aCore zetaEnds bTube : ℝ}
    (core : HairbrushMultiplicityDenseTwoEndsCoreData Y eta theta aCore zetaEnds bTube)
    (transverse : HairbrushAcuteRobustTransverseData core) :
    Shading (orientedBandFamily core transverse) where
  carrier U' :=
    ⋃ U ∈ acuteBandFamily core transverse,
      if orientTube transverse.stem U = U'
      then core.Z.carrier U
      else (∅ : Set Point3)
  measurable_carrier := by
    intro U' hU'
    have h : ∀ U ∈ acuteBandFamily core transverse,
        MeasurableSet (if orientTube transverse.stem U = U'
          then core.Z.carrier U else (∅ : Set Point3)) := by
      intro U hU
      by_cases h_eq : orientTube transverse.stem U = U'
      · rw [if_pos h_eq]
        have hU_F3 : U ∈ core.F3 := (Finset.mem_filter.mp hU).1
        exact core.Z.measurable_carrier hU_F3
      · rw [if_neg h_eq]
        exact MeasurableSet.empty
    exact MeasurableSet.biUnion (acuteBandFamily core transverse).finite_toSet.countable h
  subset_tube := by
    intro U' hU'
    apply iUnion₂_subset
    intro U hU
    by_cases h : orientTube transverse.stem U = U'
    · rw [if_pos h]
      have hcar : U'.carrier = U.carrier := by
        rw [←h]
        exact orientTube_carrier transverse.stem U
      rw [hcar]
      have hU_F3 : U ∈ core.F3 := (Finset.mem_filter.mp hU).1
      exact core.Z.subset_tube hU_F3
    · rw [if_neg h]
      exact empty_subset _

lemma orientedShading_carrier
    {F : TubeFamily δ} {Y : Shading F}
    {eta theta aCore zetaEnds bTube : ℝ}
    (core : HairbrushMultiplicityDenseTwoEndsCoreData Y eta theta aCore zetaEnds bTube)
    (transverse : HairbrushAcuteRobustTransverseData core)
    (hδ : 0 < δ)
    (h_ed : F.IsEssentiallyDistinct)
    {U : DeltaTube δ}
    (hU : U ∈ acuteBandFamily core transverse) :
    (orientedShading core transverse).carrier (orientTube transverse.stem U) =
    core.Z.carrier U := by
  let U' := orientTube transverse.stem U
  have h_injOn : Set.InjOn (orientTube transverse.stem) (acuteBandFamily core transverse) :=
    orientedBandFamily_injOn core transverse hδ h_ed
  have h_main : (orientedShading core transverse).carrier U' = core.Z.carrier U := by
    apply Set.Subset.antisymm
    · apply iUnion₂_subset
      intro V hV
      by_cases h : orientTube transverse.stem V = U'
      · rw [if_pos h]
        have h_eq : V = U := h_injOn hV hU h
        rw [h_eq]
      · rw [if_neg h]
        exact empty_subset _
    · intro x hx
      have hcond : orientTube transverse.stem U = U' := rfl
      have hx' : x ∈ (if orientTube transverse.stem U = U' then core.Z.carrier U else (∅ : Set Point3)) := by
        rw [if_pos hcond] <;> exact hx
      exact Set.mem_biUnion hU hx'
  exact h_main

/--
`orientTube stem` is injective on any subfamily of an essentially distinct family.

Equal oriented tubes have equal carriers, so the original tubes have identical
carriers.  Essential distinctness then forces the intersection volume to be at
most half the tube volume, contradicting the full intersection.
-/
lemma orientTube_injOn {B source : Kakeya.TubeFamily δ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (h_ed : B.IsEssentiallyDistinct) (h_sub : source ⊆ B)
    (stem : Kakeya.DeltaTube δ) :
    Set.InjOn (orientTube stem) source := by
  intro U hU V hV h
  have hcar : (orientTube stem U).carrier = (orientTube stem V).carrier := by rw [h]
  have hUcar : (orientTube stem U).carrier = U.carrier := orientTube_carrier stem U
  have hVcar : (orientTube stem V).carrier = V.carrier := orientTube_carrier stem V
  rw [hUcar, hVcar] at hcar
  have h_inter : U.carrier ∩ V.carrier = U.carrier := by
    rw [hcar] <;> simp
  by_cases hne : U ≠ V
  · have hU_B : U ∈ B := h_sub hU
    have hV_B : V ∈ B := h_sub hV
    have h_ed' : U.EssentiallyDistinct V := h_ed hU_B hV_B hne
    have hvol_int : volume (U.carrier ∩ V.carrier) = U.volume := by
      rw [h_inter] <;> rfl
    have hvol_eq : U.volume = V.volume := by
      unfold Kakeya.DeltaTube.volume
      congr
    have hmax : max U.volume V.volume = U.volume := by
      rw [hvol_eq] <;> simp
    rw [Kakeya.DeltaTube.EssentiallyDistinct, hvol_int, hmax] at h_ed'
    have hvol : TubeVolumeScalingStatement := tube_volume_scaling
    have hT : U.volume = Kakeya.deltaTubeVolume δ := hvol.1 δ U
    have h_fin : 0 < Kakeya.deltaTubeVolume δ ∧ Kakeya.deltaTubeVolume δ ≠ ⊤ :=
      hvol.2.1 δ hδ hδ1
    have h_ne_zero : U.volume ≠ 0 := by
      rw [hT] <;> exact h_fin.1.ne'
    have h_ne_top : U.volume ≠ ⊤ := by
      rw [hT] <;> exact h_fin.2
    have h9 : U.volume / 2 < U.volume := ENNReal.half_lt_self h_ne_zero h_ne_top
    have h10 : (2 : ENNReal)⁻¹ * U.volume = U.volume / 2 := by
      rw [div_eq_mul_inv] <;> ring
    rw [h10] at h_ed'
    exact False.elim (not_le.mpr h9 h_ed')
  · simpa using hne

/--
Transport a shading from a source family to its oriented image.

For each oriented tube `U'`, the shading carrier is the union of `Z.carrier U`
over all source tubes `U` that orient to `U'`.  By injectivity there is at most
one such `U`.
-/
def transportedShading {B source : Kakeya.TubeFamily δ}
    (Z : Kakeya.Shading B) (stem : Kakeya.DeltaTube δ)
    (h_sub : source ⊆ B) :
    Kakeya.Shading (source.image (orientTube stem)) where
  carrier U' :=
    ⋃ U ∈ source,
      if orientTube stem U = U'
      then Z.carrier U
      else (∅ : Set Point3)
  measurable_carrier := by
    intro U' hU'
    have h : ∀ U ∈ source,
        MeasurableSet (if orientTube stem U = U'
          then Z.carrier U else (∅ : Set Point3)) := by
      intro U hU
      by_cases h_eq : orientTube stem U = U'
      · rw [if_pos h_eq]
        exact Z.measurable_carrier (h_sub hU)
      · rw [if_neg h_eq]
        exact MeasurableSet.empty
    exact MeasurableSet.biUnion source.finite_toSet.countable h
  subset_tube := by
    intro U' hU'
    apply iUnion₂_subset
    intro U hU
    by_cases h : orientTube stem U = U'
    · rw [if_pos h]
      have hcar : U'.carrier = U.carrier := by
        rw [←h]
        exact orientTube_carrier stem U
      rw [hcar]
      exact Z.subset_tube (h_sub hU)
    · rw [if_neg h]
      exact empty_subset _

lemma transportedShading_carrier {B source : Kakeya.TubeFamily δ}
    (Z : Kakeya.Shading B) (stem : Kakeya.DeltaTube δ)
    (h_sub : source ⊆ B)
    (h_inj : Set.InjOn (orientTube stem) source)
    {U : Kakeya.DeltaTube δ} (hU : U ∈ source) :
    (transportedShading Z stem h_sub).carrier (orientTube stem U) = Z.carrier U := by
  let U' := orientTube stem U
  have h_main : (transportedShading Z stem h_sub).carrier U' = Z.carrier U := by
    apply Set.Subset.antisymm
    · apply iUnion₂_subset
      intro V hV
      by_cases h : orientTube stem V = U'
      · rw [if_pos h]
        have h_eq : V = U := h_inj hV hU h
        rw [h_eq]
      · rw [if_neg h]
        exact empty_subset _
    · intro x hx
      have hcond : orientTube stem U = U' := rfl
      have hx' : x ∈ (if orientTube stem U = U' then Z.carrier U else (∅ : Set Point3)) := by
        rw [if_pos hcond] <;> exact hx
      exact Set.mem_biUnion hU hx'
  exact h_main

end Kakeya.Assouad
