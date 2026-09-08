import MyLeanRepo.Kakeya.Streamlined.IndependentDilatedCoverGeometry
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.DeterministicHelpers
import MyLeanRepo.Kakeya.Streamlined.RogersShephard

/-!
# Uniform convex envelopes for parents of tubes in a convex set

The parent selected by a dilated cover need not have midpoint close to its
fine child.  Nevertheless, common-child geometry puts every such parent in a
homothetic image of the fine child's radius-enlargement.  If the fine child
lies in a convex set `K`, all those homothetic images fit in one translate of
a scaled difference body of `N_rho(K)`.  Rogers--Shephard controls the volume
of this common envelope by an absolute factor depending only on the fixed
cover dilation.
-/

noncomputable section

open MeasureTheory Set
open scoped Pointwise

namespace Kakeya.Streamlined

/--
A translate of a scaled difference body containing every `D`-homothetic
image of `S` whose center lies in `S`.
-/
def parentEnvelope (D : ℝ) (p : Point3) (S : Set Point3) :
    Set Point3 :=
  translateSet p ((2 * D - 1) • minkowskiDiff S S)

/-- The universal volume loss for the common parent envelope. -/
def parentEnvelopeVolumeFactor (A : ℝ) : ENNReal :=
  64 * ENNReal.ofReal
    ((2 * independentCoverParentDilation A - 1) ^ 3)

/--
Every `D`-homothetic image of a convex set about one of its points lies in a
single difference-body envelope based at any other point of the set.
-/
lemma homothety_image_subset_parentEnvelope
    {S : Set Point3} (hS : Convex ℝ S)
    {p m : Point3} (hp : p ∈ S) (hm : m ∈ S)
    {D : ℝ} (hD : 1 ≤ D) :
    AffineMap.homothety m D '' S ⊆ parentEnvelope D p S := by
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  let c := 2 * D - 1
  have hc : 0 < c := by
    dsimp only [c]
    linarith
  let a := D / c
  let b := (D - 1) / c
  have ha : 0 ≤ a := by
    dsimp only [a]
    positivity
  have hb : 0 ≤ b := by
    dsimp only [b]
    positivity
  have hab : a + b = 1 := by
    dsimp only [a, b]
    rw [← add_div]
    have hnum : D + (D - 1) = c := by
      dsimp only [c]
      ring
    rw [hnum, div_self hc.ne']
  let dx := x - p
  let dm := p - m
  have hdx : dx ∈ minkowskiDiff S S :=
    Set.mem_image2.mpr ⟨x, hx, p, hp, rfl⟩
  have hdm : dm ∈ minkowskiDiff S S :=
    Set.mem_image2.mpr ⟨p, hp, m, hm, rfl⟩
  let q := a • dx + b • dm
  have hq : q ∈ minkowskiDiff S S :=
    (convex_minkowskiDiff hS hS) hdx hdm ha hb hab
  have hscaled : c • q ∈ c • minkowskiDiff S S :=
    Set.smul_mem_smul_set hq
  change AffineMap.homothety m D x ∈
    (fun z : Point3 => p + z) '' (c • minkowskiDiff S S)
  refine ⟨c • q, hscaled, ?_⟩
  have hca : c * a = D := by
    dsimp only [a]
    field_simp [hc.ne']
  have hcb : c * b = D - 1 := by
    dsimp only [b]
    field_simp [hc.ne']
  rw [AffineMap.homothety_apply]
  dsimp only [q, dx, dm]
  rw [smul_add, smul_smul, smul_smul, hca, hcb]
  change p + (D • (x - p) + (D - 1) • (p - m)) =
    D • (x - m) + m
  module

/-- The common parent envelope is convex. -/
lemma parentEnvelope_convex
    {S : Set Point3} (hS : Convex ℝ S)
    (D : ℝ) (p : Point3) :
    Convex ℝ (parentEnvelope D p S) := by
  have hdiff : Convex ℝ (minkowskiDiff S S) :=
    convex_minkowskiDiff hS hS
  have hscaled :
      Convex ℝ ((2 * D - 1) • minkowskiDiff S S) :=
    hdiff.smul (2 * D - 1)
  simpa [parentEnvelope, translateSet, one_smul] using
    hscaled.affinity p 1

/--
The parent envelope has volume at most
`64 * (2D - 1)^3 * volume(S)`.
-/
lemma parentEnvelope_volume_le
    {S : Set Point3} (hS : Convex ℝ S)
    (hS_pos : 0 < volume S) (hS_top : volume S ≠ ⊤)
    {D : ℝ} (hD : 1 ≤ D) (p : Point3) :
    volume (parentEnvelope D p S) ≤
      ENNReal.ofReal ((2 * D - 1) ^ 3) * (64 * volume S) := by
  let c := 2 * D - 1
  have hc : 0 < c := by
    dsimp only [c]
    linarith
  have htranslate :
      volume (parentEnvelope D p S) =
        volume (c • minkowskiDiff S S) := by
    have h := volume_translation (-p) (c • minkowskiDiff S S)
    simpa [parentEnvelope, c, translateSet] using h
  rw [htranslate, volume_dilateSet c hc.ne', abs_of_pos hc]
  gcongr
  exact rogers_shephard_single_pos hS hS_pos hS_top

namespace GeometricLemmas

/--
If a fine tube lies in `K`, then its radius-`rho` enlargement lies in the
closed `rho`-neighborhood of `K`.
-/
lemma withRadius_carrier_subset_cthickening
    {delta rho : ℝ} (T : Kakeya.DeltaTube delta)
    {K : Set Point3} (hTK : T.carrier ⊆ K) :
    (withRadius rho T).carrier ⊆ Metric.cthickening rho K := by
  rw [withRadius_carrier]
  apply Metric.cthickening_subset_of_subset
  intro x hx
  exact hTK (Metric.self_subset_cthickening
    (Kakeya.unitSegment T.base T.direction) hx)

end GeometricLemmas

namespace DilatedDiscreteUniformTubeStructure

variable {delta A : ℝ} {F : TubeFamily delta}
variable {hdelta_le_one : delta ≤ 1}
variable (U : DilatedDiscreteUniformTubeStructure
  (A := A) F hdelta_le_one)

/--
All selected scale-`r` parents of fine tubes lying in `K` fit in one common
convex envelope based at any point of `N_rho(K)`.
-/
lemma assigned_parent_subset_parentEnvelope
    (hA : 1 ≤ A) (hdelta : 0 < delta)
    (hF_ball : F.IsInUnitBall)
    (r : UniformScaleIndex delta)
    {K : Set Point3}
    (hK : Convex ℝ K)
    (p : Point3) (hp : p ∈ Metric.cthickening
      (uniformScale delta hdelta_le_one r).1 K)
    (i : Fin F.card) (hiK : (F.tube i).carrier ⊆ K) :
    ((U.coarse r).tube ((U.cover r).parent i)).carrier ⊆
      parentEnvelope (independentCoverParentDilation A) p
        (Metric.cthickening
          (uniformScale delta hdelta_le_one r).1 K) := by
  let rho := (uniformScale delta hdelta_le_one r).1
  let fine := F.tube i
  let parent := (U.coarse r).tube ((U.cover r).parent i)
  let enlargedFine := GeometricLemmas.withRadius rho fine
  have hrho : 0 < rho :=
    lt_of_lt_of_le hdelta
      (uniformScale delta hdelta_le_one r).property.1
  have hrho_one : rho ≤ 1 :=
    (uniformScale delta hdelta_le_one r).property.2
  have hdelta_rho : delta ≤ rho :=
    (uniformScale delta hdelta_le_one r).property.1
  have hfine_parent :
      fine.carrier ⊆ dilatedTubeCarrier A parent :=
    (U.cover r).nested i
  have hfine_enlarged :
      fine.carrier ⊆ dilatedTubeCarrier A enlargedFine := by
    exact (GeometricLemmas.carrier_subset_withRadius
      hdelta_rho fine).trans
        (GeometricLemmas.self_dilated_containment
          A hA enlargedFine)
  have hparent_enlarged :
      parent.carrier ⊆
        dilatedTubeCarrier
          (independentCoverParentDilation A) enlargedFine := by
    exact common_child_parent_containment hA
      hrho hrho_one le_rfl fine (hF_ball i)
      parent enlargedFine hfine_parent hfine_enlarged
  let S := Metric.cthickening rho K
  have hS_convex :
      Convex ℝ S :=
    hK.cthickening rho
  have henlarged_S : enlargedFine.carrier ⊆ S := by
    exact GeometricLemmas.withRadius_carrier_subset_cthickening
      fine hiK
  have hmid_enlarged :
      GeometricLemmas.tubeMidpoint enlargedFine ∈
        enlargedFine.carrier :=
    GeometricLemmas.tubeMidpoint_mem_carrier enlargedFine
  have hmid_S :
      GeometricLemmas.tubeMidpoint enlargedFine ∈ S :=
    henlarged_S hmid_enlarged
  let D := independentCoverParentDilation A
  have hD : 1 ≤ D := by
    dsimp only [D, independentCoverParentDilation]
    nlinarith [sq_nonneg A]
  have hdilated_S :
      dilatedTubeCarrier D enlargedFine ⊆
        AffineMap.homothety
          (GeometricLemmas.tubeMidpoint enlargedFine) D '' S := by
    exact Set.image_mono henlarged_S
  exact hparent_enlarged.trans <|
    hdilated_S.trans <|
      homothety_image_subset_parentEnvelope
        hS_convex hp hmid_S hD

/--
All assigned scale-`r` parents of fine tubes contained in one convex set fit
in a common convex envelope.  When the `rho`-neighborhood of the set has
finite volume, the envelope loses only `parentEnvelopeVolumeFactor A`.
-/
lemma exists_assigned_parent_envelope
    (hA : 1 ≤ A) (hdelta : 0 < delta)
    (hF_ball : F.IsInUnitBall)
    (r : UniformScaleIndex delta)
    {K : Set Point3} (hK : Convex ℝ K)
    (i₀ : Fin F.card) (hi₀K : (F.tube i₀).carrier ⊆ K)
    (hne_top :
      volume (Metric.cthickening
        (uniformScale delta hdelta_le_one r).1 K) ≠ ⊤) :
    ∃ W : Set Point3,
      Convex ℝ W ∧
      (∀ i : Fin F.card, (F.tube i).carrier ⊆ K →
        ((U.coarse r).tube ((U.cover r).parent i)).carrier ⊆ W) ∧
      volume W ≤
        parentEnvelopeVolumeFactor A *
          volume (Metric.cthickening
            (uniformScale delta hdelta_le_one r).1 K) := by
  let rho := (uniformScale delta hdelta_le_one r).1
  let S := Metric.cthickening rho K
  let p :=
    GeometricLemmas.tubeMidpoint
      (GeometricLemmas.withRadius rho (F.tube i₀))
  let D := independentCoverParentDilation A
  let W := parentEnvelope D p S
  have hrho : 0 < rho :=
    lt_of_lt_of_le hdelta
      (uniformScale delta hdelta_le_one r).property.1
  have hS_convex : Convex ℝ S :=
    hK.cthickening rho
  have henlarged_S :
      (GeometricLemmas.withRadius rho (F.tube i₀)).carrier ⊆ S :=
    GeometricLemmas.withRadius_carrier_subset_cthickening
      (F.tube i₀) hi₀K
  have hp : p ∈ S :=
    henlarged_S
      (GeometricLemmas.tubeMidpoint_mem_carrier
        (GeometricLemmas.withRadius rho (F.tube i₀)))
  have hS_pos : 0 < volume S := by
    have htube :
        0 <
          (GeometricLemmas.withRadius rho (F.tube i₀)).volume := by
      rw [RandomTranslation.tube_volume_eq_deltaTubeVolume]
      exact RandomTranslation.deltaTubeVolume_pos hrho
    exact htube.trans_le (measure_mono henlarged_S)
  have hD : 1 ≤ D := by
    dsimp only [D, independentCoverParentDilation]
    nlinarith [sq_nonneg A]
  refine ⟨W, parentEnvelope_convex hS_convex D p, ?_, ?_⟩
  · intro i hiK
    exact U.assigned_parent_subset_parentEnvelope
      hA hdelta hF_ball r hK p hp i hiK
  · have hvolume :=
      parentEnvelope_volume_le hS_convex hS_pos
        (show volume S ≠ ⊤ by simpa [S, rho] using hne_top)
        hD p
    calc
      volume W
          ≤ ENNReal.ofReal ((2 * D - 1) ^ 3) *
              (64 * volume S) := hvolume
      _ = parentEnvelopeVolumeFactor A * volume S := by
        dsimp only [parentEnvelopeVolumeFactor, D]
        ring
      _ = parentEnvelopeVolumeFactor A *
          volume (Metric.cthickening
            (uniformScale delta hdelta_le_one r).1 K) := by
        rfl

end DilatedDiscreteUniformTubeStructure

end Kakeya.Streamlined
