/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.Rescaling.Hybrid
public import Kakeya.DimensionThree.MainLemma1.Cases

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology
open scoped NNReal ENNReal

namespace Kakeya.ml1Boot

/-- The source/output scale ratios agree under the fine normalization
`sigma = rho * theta`, `dt = tau / theta`. -/
theorem sourceScale_div_eq {tau theta dt rho : NNReal}
    (htau : 0 < tau) (htheta : 0 < theta) (hdt : dt = tau / theta) :
    rho * theta / tau = rho / dt := by
  subst dt
  field_simp

/-- The lower endpoint of the source window is the normalized lower endpoint,
multiplied by the ambient scale. -/
theorem sourceWindow_lower_eq {tau theta : NNReal} (htau : 0 < tau) (htheta : 0 < theta)
    (w : Real) :
    tau * (theta / tau) ^ w = (tau / theta) ^ (1 - w) * theta := by
  apply NNReal.eq
  simp only [NNReal.coe_mul, NNReal.coe_rpow]
  have htauR : (0 : Real) < tau := by exact_mod_cast htau
  have hthetaR : (0 : Real) < theta := by exact_mod_cast htheta
  rw [NNReal.coe_div, NNReal.coe_div]
  rw [Real.div_rpow (le_of_lt hthetaR) (le_of_lt htauR)]
  rw [Real.div_rpow (le_of_lt htauR) (le_of_lt hthetaR)]
  rw [Real.rpow_sub htauR, Real.rpow_sub hthetaR]
  simp only [Real.rpow_one]
  field_simp [Real.rpow_pos_of_pos htauR, Real.rpow_pos_of_pos hthetaR]

/-- A normalized scale in the output window gives a source scale in the
corresponding source window. -/
theorem sourceScale_mem_window {eps : Real} {tau theta dt rho : NNReal}
    (htau : 0 < tau) (htheta : 0 < theta) (hdt : dt = tau / theta)
    (hlo : dt ^ (1 - 5 * eps) <= rho) (hhi : rho <= dt ^ (5 * eps)) :
    tau * (theta / tau) ^ (5 * eps) <= rho * theta /\
      rho * theta <= theta * (tau / theta) ^ (5 * eps) := by
  subst dt
  constructor
  · rw [sourceWindow_lower_eq htau htheta (5 * eps)]
    exact mul_le_mul_right' hlo theta
  · rw [mul_comm theta]
    exact mul_le_mul_right' hhi theta

/-- Instantiate a source lower-Frostman witness at the source scale corresponding
to an output scale. This is the exact arithmetic/quantifier prefix needed by
the lower-normalization clause; the geometric transport of the witness is
separate. -/
theorem source_lower_witness_at_outputScale
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {eps e n : Real} {delta tau theta dt rho : NNReal}
    (htau : 0 < tau) (htheta : 0 < theta) (hdt : dt = tau / theta)
    (hlo : dt ^ (1 - 5 * eps) ≤ rho) (hhi : rho ≤ dt ^ (5 * eps))
    {ι : Type*} {u u' un : Finset ι} (hu'u : u' ⊆ u)
    (Ttheta : Tube theta E) (U : ι → ShadedTube tau E)
    (hFb : ∀ sigma : NNReal,
      tau * (theta / tau) ^ (5 * eps) ≤ sigma →
      sigma ≤ theta * (tau / theta) ^ (5 * eps) →
      ∀ k ∈ u,
        ∃ Tsigma : Tube sigma E,
          Tsigma.toConvexSpaceBody ≤ Ttheta.toConvexSpaceBody ∧
          (U k).toConvexSpaceBody ≤ Tsigma.toConvexSpaceBody ∧
          (delta : ENNReal) ^ e * ((sigma / tau : NNReal) : ENNReal) ^ n ≤
            frostmanConstIn
              (familyIn un (fun k' => (U k').toConvexSpaceBody) Tsigma.toConvexSpaceBody)
              (fun k' => (U k').toConvexSpaceBody) Tsigma.toConvexSpaceBody) :
    ∀ k ∈ u',
      ∃ Tsigma : Tube (rho * theta) E,
        Tsigma.toConvexSpaceBody ≤ Ttheta.toConvexSpaceBody ∧
        (U k).toConvexSpaceBody ≤ Tsigma.toConvexSpaceBody ∧
        (delta : ENNReal) ^ e * ((rho / dt : NNReal) : ENNReal) ^ n ≤
          frostmanConstIn
            (familyIn un (fun k' => (U k').toConvexSpaceBody) Tsigma.toConvexSpaceBody)
            (fun k' => (U k').toConvexSpaceBody) Tsigma.toConvexSpaceBody := by
  have hwin := sourceScale_mem_window htau htheta hdt hlo hhi
  intro k hk
  obtain ⟨Tsigma, hTsigmaSelf, hU, hlower⟩ :=
    hFb (rho * theta) hwin.1 hwin.2 k (hu'u hk)
  refine ⟨Tsigma, hTsigmaSelf, hU, ?_⟩
  have hratio : rho * theta / tau = rho / dt := sourceScale_div_eq htau htheta hdt
  simpa [hratio] using hlower

/-- The source lower bound after an arbitrary invertible affine change of variables. Both the
ambient family selector and the Frostman constant are transported exactly. -/
theorem source_lower_witness_affineImage
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E]
    {eps e n : Real} {delta tau theta dt rho : NNReal}
    (htau : 0 < tau) (htheta : 0 < theta) (hdt : dt = tau / theta)
    (hlo : dt ^ (1 - 5 * eps) ≤ rho) (hhi : rho ≤ dt ^ (5 * eps))
    {ι : Type*} {u u' un : Finset ι} (hu'u : u' ⊆ u)
    (Ttheta : Tube theta E) (U : ι → ShadedTube tau E)
    (hFb : ∀ sigma : NNReal,
      tau * (theta / tau) ^ (5 * eps) ≤ sigma →
      sigma ≤ theta * (tau / theta) ^ (5 * eps) →
      ∀ k ∈ u,
        ∃ Tsigma : Tube sigma E,
          Tsigma.toConvexSpaceBody ≤ Ttheta.toConvexSpaceBody ∧
          (U k).toConvexSpaceBody ≤ Tsigma.toConvexSpaceBody ∧
          (delta : ENNReal) ^ e * ((sigma / tau : NNReal) : ENNReal) ^ n ≤
            frostmanConstIn
              (familyIn un (fun k' => (U k').toConvexSpaceBody) Tsigma.toConvexSpaceBody)
              (fun k' => (U k').toConvexSpaceBody) Tsigma.toConvexSpaceBody)
    (L : E ≃ᵃ[Real] E) (hcont : Continuous L) :
    ∀ k ∈ u',
      ∃ Tsigma : Tube (rho * theta) E,
        Tsigma.toConvexSpaceBody ≤ Ttheta.toConvexSpaceBody ∧
        (U k).toConvexSpaceBody ≤ Tsigma.toConvexSpaceBody ∧
        (delta : ENNReal) ^ e * ((rho / dt : NNReal) : ENNReal) ^ n ≤
          frostmanConstIn
            (familyIn un
              (fun k' => (U k').toConvexSpaceBody.affineImage L.toAffineMap hcont)
              (Tsigma.toConvexSpaceBody.affineImage L.toAffineMap hcont))
            (fun k' => (U k').toConvexSpaceBody.affineImage L.toAffineMap hcont)
            (Tsigma.toConvexSpaceBody.affineImage L.toAffineMap hcont) := by
  intro k hk
  obtain ⟨Tsigma, hTsigma, hUk, hlower⟩ :=
    source_lower_witness_at_outputScale htau htheta hdt hlo hhi hu'u Ttheta U hFb k hk
  refine ⟨Tsigma, hTsigma, hUk, ?_⟩
  rw [Kakeya.familyIn_affineImage]
  rw [ConvexSpaceBody.frostmanConstIn_affineImage]
  exact hlower

/-- An honest output-scale tube containing the rescaled source container. The extra hypothesis
`rho ≤ 1 / 4` is exactly the truncation required by `Tube.rescale_outer_tube`; it is not implied
by the window hypotheses of `exists_fineNormalization_lower`. -/
theorem exists_rescaled_source_container
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
    (hdim : Module.finrank Real E = 3)
    {theta rho : NNReal} (htheta : 0 < theta) (htheta1 : theta ≤ 1)
    (hrho : 0 < rho) (hrho4 : (rho : Real) ≤ 1 / 4)
    (Ttheta : Tube theta E) (Tsigma : Tube (rho * theta) E)
    (hTsigma : Tsigma.toConvexSpaceBody ≤ Ttheta.toConvexSpaceBody) :
    ∃ Trho : Tube rho E,
      Ttheta.rescaleMap ((_root_.Tube.normalization.C 3 : NNReal) : Real) '' Tsigma.carrier
          ⊆ Trho.carrier ∧
      Trho.carrier ⊆ Metric.closedBall (0 : E) 1 ∧
      volume Trho.carrier ≤
        ENNReal.ofReal
            ((4 * ((_root_.Tube.normalization.C 3 : NNReal) : Real)) ^ 6) *
          volume
            (Ttheta.rescaleMap ((_root_.Tube.normalization.C 3 : NNReal) : Real) ''
              Tsigma.carrier) ∧
      Trho.center = midpoint Real
          (Ttheta.rescaleMap ((_root_.Tube.normalization.C 3 : NNReal) : Real) Tsigma.x)
          (Ttheta.rescaleMap ((_root_.Tube.normalization.C 3 : NNReal) : Real) Tsigma.y) ∧
      Trho.direction
        = ‖Ttheta.normalizationLinear Tsigma.direction‖⁻¹
            • Ttheta.normalizationLinear Tsigma.direction := by
  let R : Real := ((_root_.Tube.normalization.C 3 : NNReal) : Real)
  have hC1 : (1 : NNReal) ≤ _root_.Tube.normalization.C 3 :=
    _root_.Tube.normalization.one_le_C 3
  have hR1 : (1 : Real) ≤ R := by
    dsimp [R]
    exact NNReal.coe_le_coe.mpr hC1
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  have hrho1 : rho ≤ 1 := by
    rw [← NNReal.coe_le_coe]
    exact le_trans hrho4 (by norm_num)
  have hinter : rho * theta ≤ theta := by
    simpa using mul_le_mul_right' hrho1 theta
  have hratio : ((rho * theta : NNReal) : Real) / (theta : Real) = rho := by
    rw [NNReal.coe_mul]
    field_simp
  have hsit : _root_.Tube.IsRescalingSituation theta (rho * theta) rho R 3 :=
    { pos_ambient := htheta
      inner_le_ambient := hinter
      ambient_le_one := htheta1
      pos_out := hrho
      out_le_quarter := hrho4
      out_le_ratio := by rw [hratio]
      normalizationConst_le_radius := by simp [R] }
  obtain ⟨L, hL⟩ := _root_.Tube.exists_rescaleEquiv htheta hR Ttheta
  have hxy : Ttheta.rescaleMap R Tsigma.x ≠ Ttheta.rescaleMap R Tsigma.y := by
    intro h
    rw [← hL] at h
    have hxy' : Tsigma.x = Tsigma.y := L.injective h
    have hone := Tsigma.dist_eq_one
    rw [hxy'] at hone
    simp at hone
  let Trho : Tube rho E := _root_.Tube.centredExtension rho hxy
  have hdist : _root_.Tube.IsNormalizationDistortion Ttheta Tsigma :=
    _root_.Tube.normalization_distortion htheta hinter htheta1 Ttheta Tsigma hTsigma
  have hball0 :
      Ttheta.normalization '' Ttheta.carrier ⊆ Metric.closedBall Ttheta.x R := by
    have h := _root_.Tube.normalization_image_ambient_subset_closedBall
      htheta htheta1 Ttheta
    rw [hdim] at h
    simpa [R] using h
  have hball :
      Ttheta.normalization '' Tsigma.carrier ⊆ Metric.closedBall Ttheta.x R :=
    (Set.image_mono hTsigma).trans hball0
  have hratio4 :
      ((rho * theta : NNReal) : Real) / (theta : Real) ≤ 4 * (rho : Real) := by
    rw [hratio]
    have hrho0 : (0 : Real) ≤ rho := by positivity
    linarith
  have hout := _root_.Tube.rescale_outer_tube
    (hsit := hsit) (hn := hdim) (hR := hR) (hρσ := hratio4)
    (T₀ := Ttheta) (T := Tsigma) (hdist := hdist) (hball := hball) (hxy := hxy)
  refine ⟨Trho, hout.1, hout.2.1, hout.2.2, ?_, ?_⟩
  · exact _root_.Tube.center_centredExtension hxy
  · have h := centredExtension_rescaleMap_direction (R := R) hR Ttheta (s := rho) hxy
    have hdirdef : Tsigma.direction = Tsigma.y - Tsigma.x := rfl
    rw [hdirdef]
    exact h

/-- Choose the source witness, transport its Frostman lower bound exactly through the rescaling
equivalence, and place its image in an honest output-scale tube. What remains after this lemma is
comparison with the separately constructed normalized replacement family. -/
theorem exists_affine_lower_rescaled_container
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
    (hdim : Module.finrank Real E = 3)
    {eps e n : Real} {delta tau theta dt rho : NNReal}
    (htau : 0 < tau) (htheta : 0 < theta) (htheta1 : theta ≤ 1)
    (hdt : dt = tau / theta)
    (hlo : dt ^ (1 - 5 * eps) ≤ rho) (hhi : rho ≤ dt ^ (5 * eps))
    (hrho4 : (rho : Real) ≤ 1 / 4)
    {ι : Type*} {u u' un : Finset ι} (hu'u : u' ⊆ u)
    (Ttheta : Tube theta E) (U : ι → ShadedTube tau E)
    (hFb : ∀ sigma : NNReal,
      tau * (theta / tau) ^ (5 * eps) ≤ sigma →
      sigma ≤ theta * (tau / theta) ^ (5 * eps) →
      ∀ k ∈ u,
        ∃ Tsigma : Tube sigma E,
          Tsigma.toConvexSpaceBody ≤ Ttheta.toConvexSpaceBody ∧
          (U k).toConvexSpaceBody ≤ Tsigma.toConvexSpaceBody ∧
          (delta : ENNReal) ^ e * ((sigma / tau : NNReal) : ENNReal) ^ n ≤
            frostmanConstIn
              (familyIn un (fun k' => (U k').toConvexSpaceBody) Tsigma.toConvexSpaceBody)
              (fun k' => (U k').toConvexSpaceBody) Tsigma.toConvexSpaceBody) :
    ∀ k ∈ u',
      ∃ (Tsigma : Tube (rho * theta) E) (Trho : Tube rho E) (L : E ≃ᵃ[Real] E),
        L.toAffineMap =
            Ttheta.rescaleMap ((_root_.Tube.normalization.C 3 : NNReal) : Real) ∧
        Tsigma.toConvexSpaceBody ≤ Ttheta.toConvexSpaceBody ∧
        (U k).toConvexSpaceBody ≤ Tsigma.toConvexSpaceBody ∧
        Tsigma.toConvexSpaceBody.affineImage L.toAffineMap
              (AffineEquiv.continuous_of_finiteDimensional L) ≤
            Trho.toConvexSpaceBody ∧
        Trho.carrier ⊆ Metric.closedBall (0 : E) 1 ∧
        volume Trho.carrier ≤
          ENNReal.ofReal
              ((4 * ((_root_.Tube.normalization.C 3 : NNReal) : Real)) ^ 6) *
            volume (L '' Tsigma.carrier) ∧
        (delta : ENNReal) ^ e * ((rho / dt : NNReal) : ENNReal) ^ n ≤
          frostmanConstIn
            (familyIn un
              (fun k' => (U k').toConvexSpaceBody.affineImage L.toAffineMap
                (AffineEquiv.continuous_of_finiteDimensional L))
              (Tsigma.toConvexSpaceBody.affineImage L.toAffineMap
                (AffineEquiv.continuous_of_finiteDimensional L)))
            (fun k' => (U k').toConvexSpaceBody.affineImage L.toAffineMap
              (AffineEquiv.continuous_of_finiteDimensional L))
            (Tsigma.toConvexSpaceBody.affineImage L.toAffineMap
              (AffineEquiv.continuous_of_finiteDimensional L)) := by
  intro k hk
  obtain ⟨Tsigma, hTsigma, hUk, hlower⟩ :=
    source_lower_witness_at_outputScale htau htheta hdt hlo hhi hu'u Ttheta U hFb k hk
  have hrho : 0 < rho := by
    have hlo0 : 0 < dt ^ (1 - 5 * eps) := by
      apply Real.rpow_pos_of_pos
      rw [hdt]
      exact div_pos htau htheta
    exact lt_of_lt_of_le hlo0 hlo
  obtain ⟨Trho, himage, hball, hvolume, -, -⟩ :=
    exists_rescaled_source_container hdim htheta htheta1 hrho hrho4
      Ttheta Tsigma hTsigma
  let R : Real := ((_root_.Tube.normalization.C 3 : NNReal) : Real)
  have hC1 : (1 : NNReal) ≤ _root_.Tube.normalization.C 3 :=
    _root_.Tube.normalization.one_le_C 3
  have hR : 0 < R := by
    have : (1 : Real) ≤ R := by
      dsimp [R]
      exact NNReal.coe_le_coe.mpr hC1
    linarith
  obtain ⟨L, hL⟩ := _root_.Tube.exists_rescaleEquiv htheta hR Ttheta
  let hcont : Continuous L := AffineEquiv.continuous_of_finiteDimensional L
  have hLfun : (L : E → E) = (Ttheta.rescaleMap R : E → E) :=
    congrArg (fun f : E →ᵃ[Real] E => (f : E → E)) hL
  have himage' :
      Tsigma.toConvexSpaceBody.affineImage L.toAffineMap hcont ≤
        Trho.toConvexSpaceBody := by
    change L '' Tsigma.carrier ⊆ Trho.carrier
    rw [hLfun]
    simpa [R] using himage
  have hvolume' :
      volume Trho.carrier ≤
        ENNReal.ofReal
            ((4 * ((_root_.Tube.normalization.C 3 : NNReal) : Real)) ^ 6) *
          volume (L '' Tsigma.carrier) := by
    rw [hLfun]
    simpa [R] using hvolume
  have hlower' :
      (delta : ENNReal) ^ e * ((rho / dt : NNReal) : ENNReal) ^ n ≤
        frostmanConstIn
          (familyIn un
            (fun k' => (U k').toConvexSpaceBody.affineImage L.toAffineMap hcont)
            (Tsigma.toConvexSpaceBody.affineImage L.toAffineMap hcont))
          (fun k' => (U k').toConvexSpaceBody.affineImage L.toAffineMap hcont)
          (Tsigma.toConvexSpaceBody.affineImage L.toAffineMap hcont) := by
    rw [Kakeya.familyIn_affineImage]
    rw [ConvexSpaceBody.frostmanConstIn_affineImage]
    exact hlower
  exact ⟨Tsigma, Trho, L, by simpa [R] using hL, hTsigma, hUk,
    himage', hball, hvolume', hlower'⟩

end Kakeya.ml1Boot
