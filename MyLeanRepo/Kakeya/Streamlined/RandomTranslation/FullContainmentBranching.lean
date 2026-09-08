import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.DilatedUniformTubeStructure
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.FixedBallGeometricLemmas
import MyLeanRepo.Kakeya.Streamlined.IndependentCoverGeometry.DilatedTubeDimensions
import MyLeanRepo.Kakeya.Streamlined.TubePacking.Proof
import MyLeanRepo.Kakeya.Streamlined.GeneralizedFrostman.RigidMotionNormalizationSelection.GeometryHelpers

/-!
# Full-containment branching from assigned bookkeeping

At one fixed scale the auxiliary parent map partitions the fine indices, but
the paper branching number is the cardinality of the complete geometric
containment fiber.  A full fiber is covered by the assigned fibers of the
parents that own one of its children.  Fixed-ball phase-space packing bounds
the number of such owner parents by a constant depending only on the fixed
cover dilation and support radius.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Streamlined

namespace RandomTranslation

/--
A fine tube contained in the `A`-dilation of a radius-`rho` tube lies in a
ball about that parent's midpoint whose radius depends only on `A`, provided
`rho ≤ 1`.
-/
lemma fine_carrier_subset_parent_midpoint_ball
    {delta rho A : ℝ}
    (hA : 1 ≤ A) (hrho : 0 ≤ rho) (hrhoOne : rho ≤ 1)
    (fine : Kakeya.DeltaTube delta)
    (parent : Kakeya.DeltaTube rho)
    (hcontained :
      fine.carrier ⊆ dilatedTubeCarrier A parent) :
    fine.carrier ⊆
      Metric.closedBall
        (GeometricLemmas.tubeMidpoint parent) (3 * A / 2) := by
  intro x hx
  rcases hcontained hx with ⟨y, hy, rfl⟩
  have hyMid :
      dist y (GeometricLemmas.tubeMidpoint parent) ≤
        rho + 1 / 2 :=
    GeometricLemmas.tube_carrier_subset_closedBall_midpoint
      hrho parent hy
  rw [Metric.mem_closedBall]
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hdist :
      dist
          (AffineMap.homothety
            (GeometricLemmas.tubeMidpoint parent) A y)
          (GeometricLemmas.tubeMidpoint parent) =
        A * dist y (GeometricLemmas.tubeMidpoint parent) := by
    rw [dist_eq_norm, dist_eq_norm, AffineMap.homothety_apply]
    simp only [vsub_eq_sub, vadd_eq_add]
    have heq :
        A •
              (y -
                GeometricLemmas.tubeMidpoint parent) +
              GeometricLemmas.tubeMidpoint parent -
            GeometricLemmas.tubeMidpoint parent =
          A •
            (y - GeometricLemmas.tubeMidpoint parent) := by
      module
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hApos]
  change
    dist
        (AffineMap.homothety
          (GeometricLemmas.tubeMidpoint parent) A y)
        (GeometricLemmas.tubeMidpoint parent) ≤
      3 * A / 2
  rw [hdist]
  calc
    A * dist y (GeometricLemmas.tubeMidpoint parent)
        ≤ A * (rho + 1 / 2) := by gcongr
    _ ≤ A * (1 + 1 / 2) := by gcongr
    _ = 3 * A / 2 := by ring

/--
Same-scale common-child geometry is support-free after translating to the
target parent's midpoint.  The resulting dilation depends only on the cover
dilation `A`, not on an ambient support ball.
-/
lemma common_child_parent_containment_support_free
    {delta rho A : ℝ}
    (hA : 1 ≤ A) (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (fine : Kakeya.DeltaTube delta)
    (owner target : Kakeya.DeltaTube rho)
    (howner :
      fine.carrier ⊆ dilatedTubeCarrier A owner)
    (htarget :
      fine.carrier ⊆ dilatedTubeCarrier A target) :
    owner.carrier ⊆
      dilatedTubeCarrier
        (GeometricLemmas.fixedBallParentDilation A (3 * A / 2))
        target := by
  let v : Point3 := -GeometricLemmas.tubeMidpoint target
  let fine' := translateTube fine v
  let owner' := translateTube owner v
  let target' := translateTube target v
  have hlocal :
      fine.carrier ⊆
        Metric.closedBall
          (GeometricLemmas.tubeMidpoint target) (3 * A / 2) :=
    fine_carrier_subset_parent_midpoint_ball
      hA hrho.le hrhoOne fine target htarget
  have hfineSupport :
      fine'.carrier ⊆
        Metric.closedBall (0 : Point3) (3 * A / 2) := by
    rw [translateTube_carrier]
    rintro _ ⟨x, hx, rfl⟩
    have hx' := hlocal hx
    change
      dist x (GeometricLemmas.tubeMidpoint target) ≤
        3 * A / 2 at hx'
    change dist (x + v) 0 ≤ 3 * A / 2
    calc
      dist (x + v) 0 =
          dist x (GeometricLemmas.tubeMidpoint target) := by
        rw [dist_eq_norm, dist_eq_norm]
        congr 1
        dsimp only [v]
        abel
      _ ≤ 3 * A / 2 := hx'
  have howner' :
      fine'.carrier ⊆ dilatedTubeCarrier A owner' := by
    rw [translateTube_carrier,
      GeneralizedFrostman.dilatedTubeCarrier_translate]
    exact Set.image_mono howner
  have htarget' :
      fine'.carrier ⊆ dilatedTubeCarrier A target' := by
    rw [translateTube_carrier,
      GeneralizedFrostman.dilatedTubeCarrier_translate]
    exact Set.image_mono htarget
  have htranslated :
      owner'.carrier ⊆
        dilatedTubeCarrier
          (GeometricLemmas.fixedBallParentDilation A (3 * A / 2))
          target' :=
    GeometricLemmas.common_child_parent_containment_R
      hA hrho hrhoOne le_rfl (by nlinarith [hA])
      fine' hfineSupport owner' target' howner' htarget'
  rw [translateTube_carrier,
    GeneralizedFrostman.dilatedTubeCarrier_translate] at htranslated
  intro x hx
  have hx' :
      x + v ∈ translateSet owner.carrier v :=
    ⟨x, hx, by abel⟩
  rcases htranslated hx' with ⟨y, hy, hxy⟩
  have hyx : y = x := by
    simpa [add_left_inj] using hxy
  rwa [hyx] at hy

/--
For fixed cover dilation, the number of assigned owner parents contributing
to one complete same-scale containment fiber is uniformly bounded without any
ambient support assumption.
-/
theorem full_containment_owner_count
    (A : ℝ) (hA : 1 ≤ A) :
    ∃ M : ENNReal,
      1 ≤ M ∧ M ≠ ⊤ ∧
      ∀ {delta rho : ℝ},
        0 < rho →
        rho ≤ 1 →
        ∀ {fine : TubeFamily delta},
        ∀ {coarse : TubeFamily rho},
          coarse.IsEssentiallyDistinct →
        ∀ P : DilatedTubeCover A fine coarse,
        ∀ parent : Fin coarse.card,
          ((P.fullContainmentOwnerParents parent).card : ENNReal) ≤ M := by
  let D :=
    GeometricLemmas.fixedBallParentDilation A (3 * A / 2)
  have hD : 1 ≤ D := by
    dsimp only [D, GeometricLemmas.fixedBallParentDilation]
    nlinarith [sq_nonneg A]
  have hThreeD : 1 ≤ 3 * D := by nlinarith
  rcases tube_packing_in_plank (3 * D) hThreeD with
    ⟨C, hC, hPacking⟩
  let M : ENNReal := max 1 (ENNReal.ofReal C)
  have hMOne : 1 ≤ M := le_max_left _ _
  have hMTop : M ≠ ⊤ := by
    dsimp only [M]
    exact max_ne_top (by simp) ENNReal.ofReal_ne_top
  refine ⟨M, hMOne, hMTop, ?_⟩
  intro delta rho hrho hrhoOne fine coarse hCoarseED P parent
  let owners := P.fullContainmentOwnerParents parent
  let ownerFamily := TubeSubfamily.fromFinset coarse owners
  have hOwnerED : ownerFamily.family.IsEssentiallyDistinct :=
    ownerFamily.isEssentiallyDistinct hCoarseED
  rcases
      IndependentCoverGeometry.exists_dilatedTube_outer_plank_general
        hD hrho hrhoOne (coarse.tube parent) with
    ⟨plank, frame, hDimensions, hOuter⟩
  have hOwnerContainment :
      ∀ index : Fin ownerFamily.family.card,
        (ownerFamily.family.tube index).carrier ⊆ plank.carrier := by
    intro index
    let owner : Fin coarse.card := ownerFamily.embedding index
    have hOwnerMem : owner ∈ owners :=
      Finset.orderEmbOfFin_mem owners rfl index
    rcases Finset.mem_image.mp hOwnerMem with
      ⟨fineIndex, hFineFull, hOwnerEq⟩
    have hFineOwner :
        (fine.tube fineIndex).carrier ⊆
          dilatedTubeCarrier A (coarse.tube owner) := by
      have hNested := P.nested fineIndex
      simpa [hOwnerEq] using hNested
    have hFineTarget :
        (fine.tube fineIndex).carrier ⊆
          dilatedTubeCarrier A (coarse.tube parent) :=
      (P.mem_fullContainmentFiberIndices_iff parent fineIndex).mp
        hFineFull
    have hOwnerTarget :
        (coarse.tube owner).carrier ⊆
          dilatedTubeCarrier D (coarse.tube parent) := by
      simpa [D] using
        common_child_parent_containment_support_free
          hA hrho hrhoOne
          (fine.tube fineIndex) (coarse.tube owner)
          (coarse.tube parent) hFineOwner hFineTarget
    rw [ownerFamily.tube_eq index]
    exact hOwnerTarget.trans hOuter
  have hPackingBound :
      ownerFamily.family.enncard ≤
        ENNReal.ofReal
          (C * (rho * rho / rho ^ 2) ^ 2) :=
    hPacking rho rho rho
      hrho le_rfl le_rfl hrhoOne
      plank frame hDimensions ownerFamily.family
      hOwnerED hOwnerContainment
  have hRatio :
      C * (rho * rho / rho ^ 2) ^ 2 = C := by
    field_simp [hrho.ne']
  have hOwnerCard :
      ((owners.card : ℕ) : ENNReal) ≤ ENNReal.ofReal C := by
    simpa [ownerFamily, TubeSubfamily.fromFinset,
      TubeFamily.enncard, hRatio] using hPackingBound
  exact hOwnerCard.trans (le_max_right _ _)

/-- The canonical support-free branching loss attached to a fixed dilation. -/
noncomputable def fullContainmentBranchingLoss
    (A : ℝ) (hA : 1 ≤ A) : ENNReal :=
  Classical.choose (full_containment_owner_count A hA)

lemma one_le_fullContainmentBranchingLoss
    (A : ℝ) (hA : 1 ≤ A) :
    1 ≤ fullContainmentBranchingLoss A hA :=
  (Classical.choose_spec
    (full_containment_owner_count A hA)).1

lemma fullContainmentBranchingLoss_ne_top
    (A : ℝ) (hA : 1 ≤ A) :
    fullContainmentBranchingLoss A hA ≠ ⊤ :=
  (Classical.choose_spec
    (full_containment_owner_count A hA)).2.1

lemma fullContainmentOwnerCount_le_branchingLoss
    (A : ℝ) (hA : 1 ≤ A)
    {delta rho : ℝ} (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (hCoarseED : coarse.IsEssentiallyDistinct)
    (P : DilatedTubeCover A fine coarse)
    (parent : Fin coarse.card) :
    ((P.fullContainmentOwnerParents parent).card : ENNReal) ≤
      fullContainmentBranchingLoss A hA :=
  (Classical.choose_spec
    (full_containment_owner_count A hA)).2.2
      hrho hrhoOne hCoarseED P parent

/--
Assigned bookkeeping uniformity upgrades canonically to paper-facing
full-containment branching at every real scale, with a support-free fixed
geometric loss.
-/
theorem full_containment_uniformity_of_assigned
    {delta A : ℝ} {F : TubeFamily delta}
    (hdelta : 0 < delta) (hA : 1 ≤ A)
    (U : AssignedDilatedUniformTubeStructure (A := A) F) :
    U.FullContainmentIsCUniformAtEveryScale
      (fullContainmentBranchingLoss A hA *
        U.assignedUniformity) := by
  intro rho
  exact
    (U.cover rho).fullContainmentFibersAreCUniform_of_ownerCount
      (one_le_fullContainmentBranchingLoss A hA)
      (U.assignedUniform rho)
      (fun parent =>
        fullContainmentOwnerCount_le_branchingLoss
          A hA (hdelta.trans_le rho.property.1)
          rho.property.2 (U.coarse_distinct rho)
          (U.cover rho) parent)

/--
For fixed cover dilation and support radius, the number of assigned owner
parents contributing to one complete geometric fiber is uniformly bounded.
-/
theorem fixed_ball_full_containment_owner_count
    (A R : ℝ) (hA : 1 ≤ A) (hR : 1 ≤ R) :
    ∃ M : ENNReal,
      1 ≤ M ∧ M ≠ ⊤ ∧
      ∀ {delta rho : ℝ},
        0 < delta →
        0 < rho →
        rho ≤ 1 →
        ∀ {fine : TubeFamily delta},
          (∀ index,
            (fine.tube index).carrier ⊆
              Metric.closedBall (0 : Point3) R) →
        ∀ {coarse : TubeFamily rho},
          coarse.IsEssentiallyDistinct →
        ∀ P : DilatedTubeCover A fine coarse,
        ∀ parent : Fin coarse.card,
          ((P.fullContainmentOwnerParents parent).card : ENNReal) ≤ M := by
  let D := GeometricLemmas.fixedBallParentDilation A R
  have hD : 1 ≤ D := by
    dsimp only [D, GeometricLemmas.fixedBallParentDilation]
    nlinarith [sq_nonneg A]
  have hThreeD : 1 ≤ 3 * D := by nlinarith
  rcases tube_packing_in_plank (3 * D) hThreeD with
    ⟨C, hC, hPacking⟩
  let M : ENNReal := max 1 (ENNReal.ofReal C)
  have hMOne : 1 ≤ M := le_max_left _ _
  have hMTop : M ≠ ⊤ := by
    dsimp only [M]
    exact max_ne_top (by simp) ENNReal.ofReal_ne_top
  refine ⟨M, hMOne, hMTop, ?_⟩
  intro delta rho hdelta hrho hrhoOne fine hFineSupport
    coarse hCoarseED P parent
  let owners := P.fullContainmentOwnerParents parent
  let ownerFamily := TubeSubfamily.fromFinset coarse owners
  have hOwnerED : ownerFamily.family.IsEssentiallyDistinct :=
    ownerFamily.isEssentiallyDistinct hCoarseED
  rcases
      IndependentCoverGeometry.exists_dilatedTube_outer_plank_general
        hD hrho hrhoOne (coarse.tube parent) with
    ⟨plank, frame, hDimensions, hOuter⟩
  have hOwnerContainment :
      ∀ index : Fin ownerFamily.family.card,
        (ownerFamily.family.tube index).carrier ⊆ plank.carrier := by
    intro index
    let owner : Fin coarse.card := ownerFamily.embedding index
    have hOwnerMem : owner ∈ owners := by
      exact Finset.orderEmbOfFin_mem owners rfl index
    rcases Finset.mem_image.mp hOwnerMem with
      ⟨fineIndex, hFineFull, hOwnerEq⟩
    have hFineParent :
        (fine.tube fineIndex).carrier ⊆
          dilatedTubeCarrier A (coarse.tube owner) := by
      have hNested := P.nested fineIndex
      simpa [hOwnerEq] using hNested
    have hFineTarget :
        (fine.tube fineIndex).carrier ⊆
          dilatedTubeCarrier A (coarse.tube parent) :=
      (P.mem_fullContainmentFiberIndices_iff parent fineIndex).mp
        hFineFull
    have hOwnerTarget :
        (coarse.tube owner).carrier ⊆
          dilatedTubeCarrier D (coarse.tube parent) := by
      exact GeometricLemmas.common_child_parent_containment_R
        hA hrho hrhoOne le_rfl (le_trans zero_le_one hR)
        (fine.tube fineIndex) (hFineSupport fineIndex)
        (coarse.tube owner) (coarse.tube parent)
        hFineParent hFineTarget
    rw [ownerFamily.tube_eq index]
    exact hOwnerTarget.trans hOuter
  have hPackingBound :
      ownerFamily.family.enncard ≤
        ENNReal.ofReal
          (C * (rho * rho / rho ^ 2) ^ 2) :=
    hPacking rho rho rho
      hrho le_rfl le_rfl hrhoOne
      plank frame hDimensions ownerFamily.family
      hOwnerED hOwnerContainment
  have hRatio :
      C * (rho * rho / rho ^ 2) ^ 2 = C := by
    field_simp [hrho.ne']
  have hOwnerCard :
      ((owners.card : ℕ) : ENNReal) ≤ ENNReal.ofReal C := by
    simpa [ownerFamily, TubeSubfamily.fromFinset,
      TubeFamily.enncard, hRatio] using hPackingBound
  exact hOwnerCard.trans (le_max_right _ _)

/--
Assigned-fiber uniformity upgrades to full-containment branching uniformity
with one fixed geometric loss.
-/
theorem fixed_ball_full_containment_uniformity
    (A R : ℝ) (hA : 1 ≤ A) (hR : 1 ≤ R) :
    ∃ M : ENNReal,
      1 ≤ M ∧ M ≠ ⊤ ∧
      ∀ {delta : ℝ},
        0 < delta →
        ∀ {F : TubeFamily delta},
          (∀ index,
            (F.tube index).carrier ⊆
              Metric.closedBall (0 : Point3) R) →
        ∀ U : AssignedDilatedUniformTubeStructure (A := A) F,
          U.FullContainmentIsCUniformAtEveryScale
            (M * U.assignedUniformity) := by
  rcases fixed_ball_full_containment_owner_count A R hA hR with
    ⟨M, hMOne, hMTop, hOwner⟩
  refine ⟨M, hMOne, hMTop, ?_⟩
  intro delta hdelta F hFSupport U rho
  exact
    (U.cover rho).fullContainmentFibersAreCUniform_of_ownerCount
      hMOne (U.assignedUniform rho)
      (fun parent =>
        hOwner hdelta (hdelta.trans_le rho.property.1)
          rho.property.2 hFSupport
          (U.coarse_distinct rho) (U.cover rho) parent)

end RandomTranslation

end Kakeya.Streamlined

end
