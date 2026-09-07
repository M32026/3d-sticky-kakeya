import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.FamilyShadingAssembly
import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.VolumeScaling
import MyLeanRepo.Kakeya.Assouad.MultiplicityRefinement
import MyLeanRepo.Kakeya.Assouad.Statements

/-!
# Bounded family assembly for anisotropic rescaling

Flatten a source-indexed three-tube image cover while preserving its explicit
basepoint window, then construct the corresponding target shading.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Flatten a three-tube image cover without discarding indexed copies. -/
def flattenThreeTubeImageCover
    {delta rho : ℝ}
    (F : Kakeya.Streamlined.TubeFamily delta)
    (Phi : Point3 → Point3)
    (source : Fin F.card → Set Point3)
    (W : ThreeTubeImageCover (rho := rho) F Phi source) :
    Kakeya.Streamlined.TubeFamily rho where
  card := F.card * 3
  tube j :=
    let pair := finProdFinEquiv.symm j
    W.tube pair.1 pair.2

@[simp] lemma flattenThreeTubeImageCover_card
    {delta rho : ℝ}
    (F : Kakeya.Streamlined.TubeFamily delta)
    (Phi : Point3 → Point3)
    (source : Fin F.card → Set Point3)
    (W : ThreeTubeImageCover (rho := rho) F Phi source) :
    (flattenThreeTubeImageCover F Phi source W).card = F.card * 3 := rfl

lemma flattenThreeTubeImageCover_tube
    {delta rho : ℝ}
    (F : Kakeya.Streamlined.TubeFamily delta)
    (Phi : Point3 → Point3)
    (source : Fin F.card → Set Point3)
    (W : ThreeTubeImageCover (rho := rho) F Phi source)
    (i : Fin F.card) (k : Fin 3) :
    (flattenThreeTubeImageCover F Phi source W).tube
        (finProdFinEquiv (i, k)) =
      W.tube i k := by
  simp [flattenThreeTubeImageCover]

lemma flattenThreeTubeImageCover_covered
    {delta rho : ℝ}
    (F : Kakeya.Streamlined.TubeFamily delta)
    (Phi : Point3 → Point3)
    (source : Fin F.card → Set Point3)
    (W : ThreeTubeImageCover (rho := rho) F Phi source) :
    ∀ i,
      Phi '' source i ⊆
        (flattenThreeTubeImageCover F Phi source W).toBodyFamily.union := by
  intro i point hpoint
  have hcovered := W.covered i hpoint
  rcases Set.mem_iUnion.mp hcovered with ⟨k, hk⟩
  refine ⟨finProdFinEquiv (i, k), ?_⟩
  change
    point ∈
      ((flattenThreeTubeImageCover F Phi source W).tube
        (finProdFinEquiv (i, k))).carrier
  rw [flattenThreeTubeImageCover_tube]
  exact hk

lemma flattenThreeTubeImageCover_isInVerticalChart
    {delta rho : ℝ}
    (F : Kakeya.Streamlined.TubeFamily delta)
    (Phi : Point3 → Point3)
    (source : Fin F.card → Set Point3)
    (W : ThreeTubeImageCover (rho := rho) F Phi source) :
    IsInVerticalChart (flattenThreeTubeImageCover F Phi source W) := by
  intro j
  let pair := finProdFinEquiv.symm j
  change
    (1 / 2 : ℝ) ≤
      |(W.tube pair.1 pair.2).direction (2 : Fin 3)|
  exact W.vertical pair.1 pair.2

lemma flattenThreeTubeImageCover_hasBoundedBase
    {delta rho R : ℝ}
    (F : Kakeya.Streamlined.TubeFamily delta)
    (Phi : Point3 → Point3)
    (source : Fin F.card → Set Point3)
    (W : ThreeTubeImageCover (rho := rho) F Phi source)
    (hbase : ∀ i k, ‖(W.tube i k).base‖ ≤ R) :
    HasBoundedBase (flattenThreeTubeImageCover F Phi source W) R := by
  intro j
  let pair := finProdFinEquiv.symm j
  change ‖(W.tube pair.1 pair.2).base‖ ≤ R
  exact hbase pair.1 pair.2

/--
Construct the target shading tube-by-tube from the image of the corresponding
source shaded piece.  Unlike the global construction, this retains the source
index needed for later weighted deduplication.
-/
def sourceIndexedAnisotropicTargetShading
    {delta rho c d m : ℝ}
    (F : Kakeya.Streamlined.TubeFamily delta)
    (Y : Kakeya.Streamlined.TubeShading F)
    (g : SlopeFunction)
    (W : ThreeTubeImageCover (rho := rho) F
      (anisotropicRescalingMap g c d m)
      (fun i => (F.tube i).carrier ∩ horizontalSlab c d)) :
    Kakeya.Streamlined.TubeShading
      (flattenThreeTubeImageCover F
        (anisotropicRescalingMap g c d m)
        (fun i => (F.tube i).carrier ∩ horizontalSlab c d) W) where
  carrier q :=
    let pair := finProdFinEquiv.symm q
    ((W.tube pair.1 pair.2).carrier ∩
      Metric.cthickening rho
        (anisotropicRescalingMap g c d m ''
          (Y.carrier pair.1 ∩ horizontalSlab c d))) ∩
      horizontalSlab (-1) 1
  measurable_carrier q := by
    exact ((Metric.isClosed_cthickening.measurableSet.inter
      Metric.isClosed_cthickening.measurableSet).inter
        (measurableSet_horizontalSlab (-1) 1))
  subset_body q := by
    intro point hpoint
    exact hpoint.1.1

lemma sourceIndexedAnisotropicTargetShading_carrier
    {delta rho c d m : ℝ}
    (F : Kakeya.Streamlined.TubeFamily delta)
    (Y : Kakeya.Streamlined.TubeShading F)
    (g : SlopeFunction)
    (W : ThreeTubeImageCover (rho := rho) F
      (anisotropicRescalingMap g c d m)
      (fun i => (F.tube i).carrier ∩ horizontalSlab c d))
    (i : Fin F.card) (k : Fin 3) :
    (sourceIndexedAnisotropicTargetShading F Y g W).carrier
        (finProdFinEquiv (i, k)) =
      ((W.tube i k).carrier ∩
        Metric.cthickening rho
          (anisotropicRescalingMap g c d m ''
            (Y.carrier i ∩ horizontalSlab c d))) ∩
        horizontalSlab (-1) 1 := by
  have hpair :
      finProdFinEquiv.symm (finProdFinEquiv (i, k)) = (i, k) :=
    finProdFinEquiv.left_inv (i, k)
  change
    ((W.tube (finProdFinEquiv.symm
        (finProdFinEquiv (i, k))).1
        (finProdFinEquiv.symm
          (finProdFinEquiv (i, k))).2).carrier ∩
      Metric.cthickening rho
        (anisotropicRescalingMap g c d m ''
          (Y.carrier (finProdFinEquiv.symm
            (finProdFinEquiv (i, k))).1 ∩ horizontalSlab c d))) ∩
      horizontalSlab (-1) 1 = _
  rw [hpair]

/--
One raw target shaded carrier only uses the affine image of its underlying
source shaded piece.
-/
lemma sourceIndexedAnisotropicTargetShading_carrier_subset_local
    {delta rho c d m : ℝ}
    (F : Kakeya.Streamlined.TubeFamily delta)
    (Y : Kakeya.Streamlined.TubeShading F)
    (g : SlopeFunction)
    (W : ThreeTubeImageCover (rho := rho) F
      (anisotropicRescalingMap g c d m)
      (fun i => (F.tube i).carrier ∩ horizontalSlab c d))
    (q : Fin (F.card * 3)) :
    (sourceIndexedAnisotropicTargetShading F Y g W).carrier q ⊆
      Metric.cthickening rho
        (anisotropicRescalingMap g c d m ''
          (Y.carrier (finProdFinEquiv.symm q).1 ∩
            horizontalSlab c d)) := by
  let pair := finProdFinEquiv.symm q
  have hq : q = finProdFinEquiv pair :=
    (finProdFinEquiv.apply_symm_apply q).symm
  intro point hpoint
  rw [hq, sourceIndexedAnisotropicTargetShading_carrier] at hpoint
  change point ∈ Metric.cthickening rho
    (anisotropicRescalingMap g c d m ''
      (Y.carrier (finProdFinEquiv.symm q).1 ∩ horizontalSlab c d))
  have hindex : (finProdFinEquiv.symm q).1 = pair.1 := by
    rfl
  rw [hindex]
  exact hpoint.1.2

/--
The source-indexed raw target shading stays inside the target-radius
thickening of the full affine image.
-/
lemma sourceIndexedAnisotropicTargetShading_union_subset_thickening
    {delta rho c d m : ℝ}
    (F : Kakeya.Streamlined.TubeFamily delta)
    (Y : Kakeya.Streamlined.TubeShading F)
    (g : SlopeFunction)
    (W : ThreeTubeImageCover (rho := rho) F
      (anisotropicRescalingMap g c d m)
      (fun i => (F.tube i).carrier ∩ horizontalSlab c d)) :
    (sourceIndexedAnisotropicTargetShading F Y g W).union ⊆
      Metric.cthickening rho
        (anisotropicRescalingMap g c d m ''
          (Y.union ∩ horizontalSlab c d)) := by
  rintro point ⟨q, hq⟩
  let pair := finProdFinEquiv.symm q
  have hlocal :
      point ∈ Metric.cthickening rho
        (anisotropicRescalingMap g c d m ''
          (Y.carrier pair.1 ∩ horizontalSlab c d)) :=
    hq.1.2
  apply Metric.cthickening_subset_of_subset rho _ hlocal
  rintro imagePoint ⟨sourcePoint, ⟨hi, hslab⟩, rfl⟩
  exact ⟨sourcePoint, ⟨⟨pair.1, hi⟩, hslab⟩, rfl⟩

/-- The source-indexed raw target shading is clipped to `z ∈ [-1,1]`. -/
lemma sourceIndexedAnisotropicTargetShading_isInSlopeWindow
    {delta rho c d m : ℝ}
    (F : Kakeya.Streamlined.TubeFamily delta)
    (Y : Kakeya.Streamlined.TubeShading F)
    (g : SlopeFunction)
    (W : ThreeTubeImageCover (rho := rho) F
      (anisotropicRescalingMap g c d m)
      (fun i => (F.tube i).carrier ∩ horizontalSlab c d)) :
    IsInSlopeWindow (sourceIndexedAnisotropicTargetShading F Y g W) := by
  rintro point ⟨q, hq⟩
  exact hq.2

/--
The source-indexed target shading has the same global image, thickening, and
slope-window containments as the former global construction.
-/
lemma construct_source_indexed_anisotropic_target_shading
    {delta rho c d m : ℝ}
    (hcd : c < d)
    (F : Kakeya.Streamlined.TubeFamily delta)
    (Y : Kakeya.Streamlined.TubeShading F)
    (g : SlopeFunction)
    (W : ThreeTubeImageCover (rho := rho) F
      (anisotropicRescalingMap g c d m)
      (fun i => (F.tube i).carrier ∩ horizontalSlab c d)) :
    let coarse :=
      flattenThreeTubeImageCover F
        (anisotropicRescalingMap g c d m)
        (fun i => (F.tube i).carrier ∩ horizontalSlab c d) W
    ∃ Y' : Kakeya.Streamlined.TubeShading coarse,
      anisotropicRescalingMap g c d m ''
          (Y.union ∩ horizontalSlab c d) ⊆
        Y'.union ∧
      Y'.union ⊆
        Metric.cthickening rho
          (anisotropicRescalingMap g c d m ''
            (Y.union ∩ horizontalSlab c d)) ∧
      IsInSlopeWindow Y' := by
  let coarse :=
    flattenThreeTubeImageCover F
      (anisotropicRescalingMap g c d m)
      (fun i => (F.tube i).carrier ∩ horizontalSlab c d) W
  let Y' := sourceIndexedAnisotropicTargetShading F Y g W
  have himage_window :
      anisotropicRescalingMap g c d m ''
          (Y.union ∩ horizontalSlab c d) ⊆
        horizontalSlab (-1) 1 :=
    anisotropicImage_in_slopeWindow hcd Set.inter_subset_right
  refine ⟨Y', ?_, ?_, ?_⟩
  · rintro point ⟨sourcePoint, ⟨⟨i, hi⟩, hslab⟩, rfl⟩
    have hcovered :=
      W.covered i
        ⟨sourcePoint, ⟨Y.subset_body i hi, hslab⟩, rfl⟩
    rcases Set.mem_iUnion.mp hcovered with ⟨k, hk⟩
    refine ⟨finProdFinEquiv (i, k), ?_⟩
    rw [sourceIndexedAnisotropicTargetShading_carrier]
    let localImage : Set Point3 :=
      anisotropicRescalingMap g c d m ''
        (Y.carrier i ∩ horizontalSlab c d)
    have hlocal_mem :
        anisotropicRescalingMap g c d m sourcePoint ∈ localImage :=
      ⟨sourcePoint, ⟨hi, hslab⟩, rfl⟩
    have hlocal_thick :
        anisotropicRescalingMap g c d m sourcePoint ∈
          Metric.cthickening rho localImage :=
      Metric.self_subset_cthickening
        (δ := rho) (E := localImage) hlocal_mem
    exact
      ⟨⟨hk, hlocal_thick⟩,
        himage_window ⟨sourcePoint, ⟨⟨i, hi⟩, hslab⟩, rfl⟩⟩
  · rintro point ⟨q, hq⟩
    let pair := finProdFinEquiv.symm q
    have hlocal :
        point ∈ Metric.cthickening rho
          (anisotropicRescalingMap g c d m ''
            (Y.carrier pair.1 ∩ horizontalSlab c d)) :=
      hq.1.2
    apply Metric.cthickening_subset_of_subset rho _ hlocal
    rintro imagePoint ⟨sourcePoint, ⟨hi, hslab⟩, rfl⟩
    exact ⟨sourcePoint, ⟨⟨pair.1, hi⟩, hslab⟩, rfl⟩
  · rintro point ⟨q, hq⟩
    exact hq.2

/--
For one source tube, its shaded slab image is covered by the three target
shaded pieces carrying that same source index.
-/
lemma source_image_volume_le_target_fiber_mass
    {delta rho c d m : ℝ}
    (hcd : c < d)
    (F : Kakeya.Streamlined.TubeFamily delta)
    (Y : Kakeya.Streamlined.TubeShading F)
    (g : SlopeFunction)
    (W : ThreeTubeImageCover (rho := rho) F
      (anisotropicRescalingMap g c d m)
      (fun i => (F.tube i).carrier ∩ horizontalSlab c d))
    (i : Fin F.card) :
    MeasureTheory.volume
        (anisotropicRescalingMap g c d m ''
          (Y.carrier i ∩ horizontalSlab c d)) ≤
      ∑ k : Fin 3,
        MeasureTheory.volume
          ((sourceIndexedAnisotropicTargetShading F Y g W).carrier
            (finProdFinEquiv (i, k))) := by
  let imagePiece : Set Point3 :=
    anisotropicRescalingMap g c d m ''
      (Y.carrier i ∩ horizontalSlab c d)
  have himage_window : imagePiece ⊆ horizontalSlab (-1) 1 := by
    exact anisotropicImage_in_slopeWindow hcd (by
      intro point hpoint
      exact hpoint.2)
  have hcover :
      imagePiece ⊆
        ⋃ k : Fin 3,
          (sourceIndexedAnisotropicTargetShading F Y g W).carrier
            (finProdFinEquiv (i, k)) := by
    intro point hpoint
    rcases hpoint with ⟨sourcePoint, ⟨hi, hslab⟩, rfl⟩
    have hcovered :=
      W.covered i
        ⟨sourcePoint, ⟨Y.subset_body i hi, hslab⟩, rfl⟩
    rcases Set.mem_iUnion.mp hcovered with ⟨k, hk⟩
    refine Set.mem_iUnion.mpr ⟨k, ?_⟩
    rw [sourceIndexedAnisotropicTargetShading_carrier]
    let localImage : Set Point3 :=
      anisotropicRescalingMap g c d m ''
        (Y.carrier i ∩ horizontalSlab c d)
    have hlocal :
        anisotropicRescalingMap g c d m sourcePoint ∈ localImage :=
      ⟨sourcePoint, ⟨hi, hslab⟩, rfl⟩
    exact
      ⟨⟨hk, Metric.self_subset_cthickening
        (δ := rho) (E := localImage) hlocal⟩,
        himage_window ⟨sourcePoint, ⟨hi, hslab⟩, rfl⟩⟩
  exact (MeasureTheory.measure_mono hcover).trans
    (MeasureTheory.measure_iUnion_fintype_le MeasureTheory.volume _)

/--
The source-indexed target shading retains the full affine-scaled aggregate
mass of the original shading inside the selected slab.
-/
lemma sourceIndexedAnisotropicTargetShading_mass_lower
    {delta rho c d m : ℝ}
    (hcd : c < d) (hm : 0 < m)
    (F : Kakeya.Streamlined.TubeFamily delta)
    (Y : Kakeya.Streamlined.TubeShading F)
    (g : SlopeFunction)
    (W : ThreeTubeImageCover (rho := rho) F
      (anisotropicRescalingMap g c d m)
      (fun i => (F.tube i).carrier ∩ horizontalSlab c d)) :
    ENNReal.ofReal m * shadedMassInSlab Y c d ≤
      (sourceIndexedAnisotropicTargetShading F Y g W).mass := by
  let targetWeight : Fin F.card × Fin 3 → ENNReal :=
    fun pair =>
      MeasureTheory.volume
        ((sourceIndexedAnisotropicTargetShading F Y g W).carrier
          (finProdFinEquiv pair))
  have hsource :
      ∀ i : Fin F.card,
        ENNReal.ofReal m *
            MeasureTheory.volume
              (Y.carrier i ∩ horizontalSlab c d) ≤
          ∑ k : Fin 3, targetWeight (i, k) := by
    intro i
    rw [← volume_image_anisotropicRescalingMap g hcd hm
      (Y.carrier i ∩ horizontalSlab c d)
      ((Y.measurable_carrier i).inter
        (measurableSet_horizontalSlab c d))]
    exact source_image_volume_le_target_fiber_mass hcd F Y g W i
  calc
    ENNReal.ofReal m * shadedMassInSlab Y c d
        = ∑ i : Fin F.card,
            ENNReal.ofReal m *
              MeasureTheory.volume
                (Y.carrier i ∩ horizontalSlab c d) := by
          rw [shadedMassInSlab, Finset.mul_sum]
          rfl
    _ ≤ ∑ i : Fin F.card, ∑ k : Fin 3, targetWeight (i, k) :=
      Finset.sum_le_sum fun i _ => hsource i
    _ = ∑ pair : Fin F.card × Fin 3, targetWeight pair := by
      rw [Fintype.sum_prod_type]
    _ = ∑ q : Fin (F.card * 3),
          MeasureTheory.volume
            ((sourceIndexedAnisotropicTargetShading F Y g W).carrier q) := by
      exact Equiv.sum_comp finProdFinEquiv
        (fun q =>
          MeasureTheory.volume
            ((sourceIndexedAnisotropicTargetShading F Y g W).carrier q))
    _ = (sourceIndexedAnisotropicTargetShading F Y g W).mass := rfl

/--
Assemble a bounded raw anisotropic target family and its image-induced
shading.  This stops before essential-distinctness cleanup.
-/
lemma bounded_anisotropic_target_family_shading
    (hsegment : BoundedThreeSegmentCoverStatement)
    (hbounded : BoundedThreeTubeImageCoverStatement)
    (delta c d m rho : ℝ)
    (hdelta : 0 < delta) (hcd : c < d)
    (h_dc : d - c ≤ 1 / 25)
    (hdelta_small : delta ≤ 1 / 100)
    (hrho_small : 2 * delta / (d - c) ≤ 1 / 4)
    (hrho_eq : rho = 2 * delta / (d - c))
    (hm_pos : 0 < m) (hm_one : m ≤ 1)
    (hsub : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1)
    (F : Kakeya.Streamlined.TubeFamily delta)
    (hF_ball : F.IsInUnitBall)
    (hvertical : IsInVerticalChart F)
    (Y : Kakeya.Streamlined.TubeShading F)
    (g : SlopeFunction) (hg : g.IsNormalized) :
    ∃ coarse : Kakeya.Streamlined.TubeFamily rho,
      ∃ Y' : Kakeya.Streamlined.TubeShading coarse,
        coarse.card = F.card * 3 ∧
        HasBoundedBase coarse 3 ∧
        IsInVerticalChart coarse ∧
        anisotropicRescalingMap g c d m ''
            (Y.union ∩ horizontalSlab c d) ⊆
          Y'.union ∧
        Y'.union ⊆
          Metric.cthickening rho
            (anisotropicRescalingMap g c d m ''
              (Y.union ∩ horizontalSlab c d)) ∧
        IsInSlopeWindow Y' := by
  rcases hbounded hsegment delta c d m rho hdelta hcd h_dc hdelta_small
      hrho_small hrho_eq hm_pos hm_one hsub F hF_ball hvertical g hg with
    ⟨W, hW_base⟩
  let source : Fin F.card → Set Point3 :=
    fun i => (F.tube i).carrier ∩ horizontalSlab c d
  let coarse : Kakeya.Streamlined.TubeFamily rho :=
    flattenThreeTubeImageCover F
      (anisotropicRescalingMap g c d m) source W
  have hbase : HasBoundedBase coarse 3 :=
    flattenThreeTubeImageCover_hasBoundedBase F
      (anisotropicRescalingMap g c d m) source W hW_base
  have hvert : IsInVerticalChart coarse :=
    flattenThreeTubeImageCover_isInVerticalChart F
      (anisotropicRescalingMap g c d m) source W
  rcases construct_source_indexed_anisotropic_target_shading hcd
      F Y g W with
    ⟨Y', himage, hthick, hwindow⟩
  exact ⟨coarse, Y', rfl, hbase, hvert, himage, hthick, hwindow⟩

end Kakeya.Assouad
