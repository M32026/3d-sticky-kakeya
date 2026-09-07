import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23Theorem22Threshold

/-!
# Theorem 22-ready actual graph for WZ1 Lemma 23

This module packages the final finite inputs to
`WZ1ProjectionDichotomyConclusion`:

* nonempty vertex classes;
* unit-ball support;
* separation at the final graph scale;
* one-dimensional Katz--Tao bounds with the theorem's power constant;
* actual edge support; and
* the required edge-cardinality threshold.

The graph remains the common `/5` image of the faithful actual Lemma 23
four-cycle graph.
-/

namespace Kakeya.Assouad

noncomputable section

/--
At sufficiently small source scale, the final graph-scale Katz--Tao power
constant dominates the absolute constant four.
-/
theorem wz1_lemma23_katzTao_constant_absorption
    (theoremEta : ℝ) (htheoremEta : 0 < theoremEta) :
    ∃ rho₀ : ℝ, 0 < rho₀ ∧ rho₀ ≤ 1 ∧
      ∀ rho : ℝ, 0 < rho → rho ≤ rho₀ →
        (4 : ENNReal) ≤
          Kakeya.realRpowENN
            (wz1Lemma23Theorem22Scale rho) (-theoremEta) := by
  let A : ENNReal :=
    Kakeya.realRpowENN
      (5 * Real.sqrt 3) theoremEta
  have hdenom : 0 < 5 * Real.sqrt 3 := by positivity
  have hApos : A ≠ 0 := by
    apply ne_of_gt
    exact ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos hdenom theoremEta)
  have hAtop : A ≠ ⊤ := by
    simp [A, Kakeya.realRpowENN, ENNReal.ofReal_ne_top]
  let D : ENNReal :=
    4 * A⁻¹
  have hD : D ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by norm_num)
      (ENNReal.inv_ne_top.mpr hApos)
  have hgap : (0 : ℝ) < theoremEta / 2 := by linarith
  rcases exists_scale_absorb_constant
      D hD (c := 0) (c' := theoremEta / 2)
      (by norm_num) hgap with
    ⟨rho₀, hrho₀, hrho₀One, habsorb⟩
  refine ⟨rho₀, hrho₀, hrho₀One, ?_⟩
  intro rho hrho hrhoSmall
  have hraw := habsorb rho hrho hrhoSmall
  have hzero :
      Kakeya.realRpowENN rho (-(0 : ℝ)) = 1 := by
    simp [Kakeya.realRpowENN]
  rw [hzero, mul_one] at hraw
  have hscale :
      Kakeya.realRpowENN
          (wz1Lemma23Theorem22Scale rho) (-theoremEta) =
        A *
          Kakeya.realRpowENN rho (-(theoremEta / 2)) := by
    have hsqrt :
        Real.sqrt rho = Real.rpow rho (1 / 2 : ℝ) :=
      Real.sqrt_eq_rpow rho
    have hreal :
        Real.rpow (wz1Lemma23Theorem22Scale rho) (-theoremEta) =
          Real.rpow (5 * Real.sqrt 3) theoremEta *
            Real.rpow rho (-(theoremEta / 2)) := by
      dsimp only [wz1Lemma23Theorem22Scale]
      rw [hsqrt]
      have hdiv :=
        Real.div_rpow
          (Real.rpow_nonneg hrho.le (1 / 2 : ℝ))
          hdenom.le (-theoremEta)
      have hnum :
          Real.rpow (Real.rpow rho (1 / 2 : ℝ)) (-theoremEta) =
            Real.rpow rho ((1 / 2 : ℝ) * (-theoremEta)) := by
        exact
          (Real.rpow_mul hrho.le (1 / 2 : ℝ)
            (-theoremEta)).symm
      have hden :
          Real.rpow (5 * Real.sqrt 3) (-theoremEta) =
            (Real.rpow (5 * Real.sqrt 3) theoremEta)⁻¹ :=
        Real.rpow_neg hdenom.le theoremEta
      calc
        Real.rpow
            (Real.rpow rho (1 / 2 : ℝ) /
              (5 * Real.sqrt 3)) (-theoremEta)
            = Real.rpow (Real.rpow rho (1 / 2 : ℝ))
                (-theoremEta) /
              Real.rpow (5 * Real.sqrt 3)
                (-theoremEta) := hdiv
        _ = Real.rpow rho ((1 / 2 : ℝ) * (-theoremEta)) /
              (Real.rpow (5 * Real.sqrt 3) theoremEta)⁻¹ := by
          rw [hnum, hden]
        _ = Real.rpow (5 * Real.sqrt 3) theoremEta *
              Real.rpow rho (-(theoremEta / 2)) := by
          have hdenPos :
              0 < Real.rpow (5 * Real.sqrt 3) theoremEta :=
            Real.rpow_pos_of_pos hdenom _
          field_simp [hdenPos.ne']
    simp only [A, Kakeya.realRpowENN, hreal]
    exact ENNReal.ofReal_mul
      (Real.rpow_nonneg hdenom.le theoremEta)
  rw [hscale]
  have hraw' :
      4 * A⁻¹ ≤
        Kakeya.realRpowENN rho (-(theoremEta / 2)) := by
    simpa [D] using hraw
  calc
    (4 : ENNReal) = 4 * 1 := by simp
    _ = 4 * (A⁻¹ * A) := by
      rw [ENNReal.inv_mul_cancel hApos hAtop]
    _ = A * (4 * A⁻¹) := by ac_rfl
    _ ≤ A * Kakeya.realRpowENN rho (-(theoremEta / 2)) := by
      gcongr

/-- A Katz--Tao bound may be weakened by increasing its constant. -/
lemma DiscreteSet.IsKatzTao.mono_const
    {n : ℕ} {A : DiscreteSet n}
    {delta s : ℝ} {C C' : ENNReal}
    (h : A.IsKatzTao delta s C)
    (hCC' : C ≤ C') :
    A.IsKatzTao delta s C' := by
  intro x r hdelta_r hr_one
  exact
    (h x r hdelta_r hr_one).trans
      (by gcongr)

/--
The final unit-ball graph together with all hypotheses of the final Theorem
22 interface at `deltaGraph = sqrt rho / (5 * sqrt 3)`.
-/
structure WZ1Lemma23Theorem22ReadyGraph
    (rho theoremEta : ℝ)
    {sourceF sourceG₁ sourceG₂ : DiscreteSet 2}
    {sourceH : Finset (Point2 × Point2 × Point2)}
    (unitBall :
      WZ1Lemma23UnitBallGraph
        rho sourceF sourceG₁ sourceG₂ sourceH) where
  deltaGraph : ℝ := wz1Lemma23Theorem22Scale rho
  deltaGraph_eq :
    deltaGraph = wz1Lemma23Theorem22Scale rho
  deltaGraph_pos : 0 < deltaGraph
  F_nonempty : unitBall.F.Nonempty
  G₁_nonempty : unitBall.G₁.Nonempty
  G₂_nonempty : unitBall.G₂.Nonempty
  H_nonempty : unitBall.H.Nonempty
  F_katzTao :
    unitBall.F.IsKatzTao deltaGraph 1
      (Kakeya.realRpowENN deltaGraph (-theoremEta))
  G₁_katzTao :
    unitBall.G₁.IsKatzTao deltaGraph 1
      (Kakeya.realRpowENN deltaGraph (-theoremEta))
  G₂_katzTao :
    unitBall.G₂.IsKatzTao deltaGraph 1
      (Kakeya.realRpowENN deltaGraph (-theoremEta))
  edge_threshold :
    Kakeya.realRpowENN deltaGraph (theoremEta - 3) ≤
      (unitBall.H.card : ENNReal)

/--
Construct the final Theorem 22-ready package from the sharp localized
geometry, its edge threshold, and the harmless small-scale absorption
`4 ≤ deltaGraph^(-theoremEta)`.
-/
theorem WZ1Lemma23LocalizedPreparedGeometry.toTheorem22ReadyGraph
    {delta rho sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C : ENNReal}
    {windowed :
      WZ1Lemma23WindowedGlobalSlicePackage
        (delta := delta) (rho := rho) (sigma := sigma) Y C}
    {localized :
      WZ1Lemma23LocalizedGlobalBinPackage windowed.global}
    {residue :
      WZ1Lemma23YResiduePackage windowed.global}
    {localBins :
      WZ1Lemma23LocalBinPackage
        (rho := rho) (sigma := sigma) C windowed.global.cells}
    {prepared :
      WZ1Lemma23LocalizedPreparedPackage
        windowed localized residue localBins}
    (geometry :
      WZ1Lemma23LocalizedPreparedGeometry prepared)
    (theoremEta : ℝ)
    (hedge :
      Kakeya.realRpowENN
          (wz1Lemma23Theorem22Scale rho)
          (theoremEta - 3) ≤
        (geometry.unitBall.H.card : ENNReal))
    (hKatzTaoConstant :
      (4 : ENNReal) ≤
        Kakeya.realRpowENN
          (wz1Lemma23Theorem22Scale rho) (-theoremEta)) :
    Nonempty
      (WZ1Lemma23Theorem22ReadyGraph
        rho theoremEta geometry.unitBall) := by
  let deltaGraph := wz1Lemma23Theorem22Scale rho
  have hdeltaGraph : 0 < deltaGraph := by
    dsimp only [deltaGraph, wz1Lemma23Theorem22Scale]
    exact div_pos
      (Real.sqrt_pos.mpr windowed.global.rho_pos)
      (by positivity)
  have hthresholdPos :
      0 <
        Kakeya.realRpowENN deltaGraph (theoremEta - 3) := by
    apply ENNReal.ofReal_pos.mpr
    exact Real.rpow_pos_of_pos hdeltaGraph _
  have hHcardPos :
      0 < (geometry.unitBall.H.card : ENNReal) :=
    hthresholdPos.trans_le hedge
  have hHnonempty : geometry.unitBall.H.Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast hHcardPos
  rcases hHnonempty with ⟨edge, hedgeMem⟩
  have hsupport :=
    geometry.unitBall.edge_support edge hedgeMem
  have hFnonempty : geometry.unitBall.F.Nonempty :=
    ⟨edge.1, hsupport.1⟩
  have hG₁nonempty : geometry.unitBall.G₁.Nonempty :=
    ⟨edge.2.1, hsupport.2.1⟩
  have hG₂nonempty : geometry.unitBall.G₂.Nonempty :=
    ⟨edge.2.2, hsupport.2.2⟩
  exact
    ⟨{ deltaGraph := deltaGraph
       deltaGraph_eq := rfl
       deltaGraph_pos := hdeltaGraph
       F_nonempty := hFnonempty
       G₁_nonempty := hG₁nonempty
       G₂_nonempty := hG₂nonempty
       H_nonempty := ⟨edge, hedgeMem⟩
       F_katzTao :=
         geometry.unitBall.F_katzTao.mono_const
           hKatzTaoConstant
       G₁_katzTao :=
         geometry.unitBall.G₁_katzTao.mono_const
           hKatzTaoConstant
       G₂_katzTao :=
         geometry.unitBall.G₂_katzTao.mono_const
           hKatzTaoConstant
       edge_threshold := hedge }⟩

end

end Kakeya.Assouad
