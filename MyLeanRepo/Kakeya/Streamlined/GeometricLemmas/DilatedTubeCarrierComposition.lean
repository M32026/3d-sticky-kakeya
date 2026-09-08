import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.SelfDilatedContainment
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.TubeOrientation

/-!
# Composing homothetic tube containments

Tube carriers are centrally symmetric about their segment midpoint.  Hence a
homothetic dilation of a tube already contained in a homothetic dilation of a
second tube remains in one fixed larger homothetic dilation of the second
tube.
-/

noncomputable section

namespace Kakeya.Streamlined

namespace GeometricLemmas

/-- Reflection in the segment midpoint preserves a tube carrier. -/
lemma pointReflection_mem_carrier
    {rho : ℝ} (T : Kakeya.DeltaTube rho)
    {x : Point3} (hx : x ∈ T.carrier) :
    (2 : ℝ) • tubeMidpoint T - x ∈ T.carrier := by
  let reflection : Point3 ≃ᵃⁱ[ℝ] Point3 :=
    AffineIsometryEquiv.pointReflection ℝ (tubeMidpoint T)
  have hsegment :
      reflection ''
          Kakeya.unitSegment T.base T.direction =
        Kakeya.unitSegment T.base T.direction := by
    ext y
    constructor
    · rintro ⟨z, ⟨t, ht, rfl⟩, rfl⟩
      refine
        ⟨1 - t,
          ⟨by linarith [ht.2], by linarith [ht.1]⟩,
          ?_⟩
      rw [AffineIsometryEquiv.pointReflection_apply]
      simp [tubeMidpoint, vsub_eq_sub, vadd_eq_add]
      module
    · rintro ⟨t, ht, rfl⟩
      let z := T.base + (1 - t) • T.direction
      have hz :
          z ∈ Kakeya.unitSegment T.base T.direction := by
        exact
          ⟨1 - t,
            ⟨by linarith [ht.2], by linarith [ht.1]⟩,
            rfl⟩
      refine ⟨z, hz, ?_⟩
      rw [AffineIsometryEquiv.pointReflection_apply]
      simp [z, tubeMidpoint, vsub_eq_sub, vadd_eq_add]
      module
  have hreflection :
      reflection '' T.carrier = T.carrier := by
    rw [Kakeya.DeltaTube.carrier]
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hdist :
          Metric.infEDist
              (reflection z)
              (reflection ''
                Kakeya.unitSegment T.base T.direction) =
            Metric.infEDist z
              (Kakeya.unitSegment T.base T.direction) :=
        Metric.infEDist_image reflection.isometry
      rw [hsegment] at hdist
      change
        Metric.infEDist
            (reflection z)
            (Kakeya.unitSegment T.base T.direction) ≤
          ENNReal.ofReal rho
      change
        Metric.infEDist z
            (Kakeya.unitSegment T.base T.direction) ≤
          ENNReal.ofReal rho at hz
      rw [hdist]
      exact hz
    · intro hy
      let z := reflection y
      have hz :
          z ∈
            Metric.cthickening rho
              (Kakeya.unitSegment T.base T.direction) := by
        have hdist :
            Metric.infEDist
                (reflection y)
                (reflection ''
                  Kakeya.unitSegment T.base T.direction) =
              Metric.infEDist y
                (Kakeya.unitSegment T.base T.direction) :=
          Metric.infEDist_image reflection.isometry
        rw [hsegment] at hdist
        change
          Metric.infEDist z
              (Kakeya.unitSegment T.base T.direction) ≤
            ENNReal.ofReal rho
        change
          Metric.infEDist y
              (Kakeya.unitSegment T.base T.direction) ≤
            ENNReal.ofReal rho at hy
        dsimp only [z]
        rw [hdist]
        exact hy
      refine ⟨z, hz, ?_⟩
      exact
        (AffineIsometryEquiv.pointReflection_involutive
          (𝕜 := ℝ) (tubeMidpoint T) y)
  have hmem :
      reflection x ∈ T.carrier := by
    rw [← hreflection]
    exact ⟨x, hx, rfl⟩
  rw [show
    (2 : ℝ) • tubeMidpoint T - x =
      tubeMidpoint T - x + tubeMidpoint T by module]
  simpa [reflection,
    AffineIsometryEquiv.pointReflection_apply,
    vsub_eq_sub, vadd_eq_add] using hmem

/--
If `T` lies in the `D`-dilation of `U`, then the `A`-dilation of `T` lies
in the `((2A-1)D)`-dilation of `U`.
-/
lemma dilatedTubeCarrier_comp_of_subset
    {rho sigma A D : ℝ}
    (hA : 1 ≤ A) (hD : 0 < D)
    (T : Kakeya.DeltaTube rho)
    (U : Kakeya.DeltaTube sigma)
    (hTU :
      T.carrier ⊆ dilatedTubeCarrier D U) :
    dilatedTubeCarrier A T ⊆
      dilatedTubeCarrier ((2 * A - 1) * D) U := by
  let mT := tubeMidpoint T
  let mU := tubeMidpoint U
  have hc : 0 < 2 * A - 1 := by linarith
  intro z hz
  rcases hz with ⟨y, hy, rfl⟩
  have hmT : mT ∈ T.carrier :=
    tubeMidpoint_mem_carrier T
  rcases hTU hmT with ⟨a, ha, haMap⟩
  rcases hTU hy with ⟨b, hb, hbMap⟩
  let reflectedA : Point3 := (2 : ℝ) • mU - a
  have hreflectedA : reflectedA ∈ U.carrier := by
    exact pointReflection_mem_carrier U ha
  let alpha : ℝ := A / (2 * A - 1)
  let beta : ℝ := (A - 1) / (2 * A - 1)
  have halpha : 0 ≤ alpha := by
    dsimp only [alpha]
    positivity
  have hbeta : 0 ≤ beta := by
    dsimp only [beta]
    positivity
  have hab : alpha + beta = 1 := by
    dsimp only [alpha, beta]
    rw [← add_div]
    have hnumerator :
        A + (A - 1) = 2 * A - 1 := by
      ring
    rw [hnumerator, div_self hc.ne']
  let q : Point3 := alpha • b + beta • reflectedA
  have hq : q ∈ U.carrier :=
    (deltaTube_carrier_convex' U)
      hb hreflectedA halpha hbeta hab
  have hcalpha :
      (2 * A - 1) * alpha = A := by
    dsimp only [alpha]
    field_simp [hc.ne']
  have hcbeta :
      (2 * A - 1) * beta = A - 1 := by
    dsimp only [beta]
    field_simp [hc.ne']
  have hqSub :
      q - mU =
        alpha • (b - mU) -
          beta • (a - mU) := by
    dsimp only [q, reflectedA]
    have hbetaAlpha : beta = 1 - alpha := by
      linarith [hab]
    rw [hbetaAlpha]
    module
  have hcoefficientAlpha :
      ((2 * A - 1) * D) * alpha = A * D := by
    calc
      ((2 * A - 1) * D) * alpha =
          D * ((2 * A - 1) * alpha) := by ring
      _ = D * A := by rw [hcalpha]
      _ = A * D := by ring
  have hcoefficientBeta :
      ((2 * A - 1) * D) * beta =
        (A - 1) * D := by
    calc
      ((2 * A - 1) * D) * beta =
          D * ((2 * A - 1) * beta) := by ring
      _ = D * (A - 1) := by rw [hcbeta]
      _ = (A - 1) * D := by ring
  refine ⟨q, hq, ?_⟩
  change
    ((2 * A - 1) * D) • (q - mU) + mU =
      A • (y - mT) + mT
  change D • (a - mU) + mU = mT at haMap
  change D • (b - mU) + mU = y at hbMap
  rw [← haMap, ← hbMap]
  rw [hqSub, smul_sub, smul_smul, smul_smul,
    hcoefficientAlpha, hcoefficientBeta]
  module

lemma dilatedTubeCarrier_comp_subset
    {sourceScale targetScale A B : ℝ}
    (_htargetScale : 0 ≤ targetScale)
    (hA : 1 ≤ A)
    (hB : 1 ≤ B)
    (source : Kakeya.DeltaTube sourceScale)
    (target : Kakeya.DeltaTube targetScale)
    (hsource :
      source.carrier ⊆ dilatedTubeCarrier A target) :
    dilatedTubeCarrier B source ⊆
      dilatedTubeCarrier (A * (2 * B - 1)) target := by
  have hcontainment :
      dilatedTubeCarrier B source ⊆
        dilatedTubeCarrier ((2 * B - 1) * A) target :=
    dilatedTubeCarrier_comp_of_subset
      hB (zero_lt_one.trans_le hA) source target hsource
  have hcoefficient :
      (2 * B - 1) * A = A * (2 * B - 1) := by
    ring
  rw [← hcoefficient]
  exact hcontainment

end GeometricLemmas

end Kakeya.Streamlined
