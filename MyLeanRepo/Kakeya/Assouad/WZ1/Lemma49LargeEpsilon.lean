import MyLeanRepo.Kakeya.Assouad.WZ1.ProjectionTheoremLocalizationStatements

/-!
# The large-epsilon branch of WZ1 Lemma 49

When `epsilon ≥ 1`, the exponent `1 - epsilon` in the long-projection
conclusion is nonpositive.  A single dot-difference value therefore gives the
required covering lower bound after choosing the interval radius to satisfy
the length condition exactly.
-/

namespace Kakeya.Assouad

noncomputable section

/--
For `epsilon ≥ 1`, every nonempty tripartite graph satisfies the long
dot-difference projection alternative.
-/
theorem wz1_lemma49_large_epsilon_long_projection
    {delta epsilon eta : ℝ}
    {H : Finset (Point2 × Point2 × Point2)}
    (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    (heta : 0 < eta) (hepsilon : 1 ≤ epsilon)
    (hH : H.Nonempty) :
    WZ1StripLocalizationLongProjection delta epsilon eta H := by
  let rho : ℝ := delta
  let radius : ℝ :=
    Real.rpow delta (-eta) * delta / 2
  let edge := Classical.choose hH
  let center : ℝ :=
    inner ℝ edge.1 (edge.2.1 - edge.2.2)
  have hedge : edge ∈ H := Classical.choose_spec hH
  have hrho : 0 < rho := hdelta
  have hradius : 0 < radius := by
    dsimp only [radius]
    have hpow : 0 < Real.rpow delta (-eta) :=
      Real.rpow_pos_of_pos hdelta _
    exact div_pos (mul_pos hpow hdelta) (by norm_num)
  have hcenter :
      center ∈
        wz1DotDifferenceSet H ∩
          Metric.closedBall center radius := by
    constructor
    · change center ∈
        H.image fun current =>
          inner ℝ current.1 (current.2.1 - current.2.2)
      exact Finset.mem_image.mpr ⟨edge, hedge, rfl⟩
    · simp [Metric.mem_closedBall, hradius.le]
  have honeCover :
      (1 : ENNReal) ≤
        (Metric.externalCoveringNumber
          (Real.toNNReal rho)
          (wz1DotDifferenceSet H ∩
            Metric.closedBall center radius) : ENNReal) := by
    have hmono :
        Metric.externalCoveringNumber
            (Real.toNNReal rho) ({center} : Set ℝ) ≤
          Metric.externalCoveringNumber
            (Real.toNNReal rho)
            (wz1DotDifferenceSet H ∩
              Metric.closedBall center radius) :=
      Metric.externalCoveringNumber_mono_set
        (by
          intro value hvalue
          have hvalueEq : value = center := by
            simpa using hvalue
          rw [hvalueEq]
          exact hcenter)
    rw [Metric.externalCoveringNumber_singleton] at hmono
    exact_mod_cast hmono
  have hbase :
      1 ≤ 2 * radius / rho := by
    have hpow :
        1 ≤ Real.rpow delta (-eta) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos
        hdelta hdelta_one (by linarith)
    have heq :
        2 * radius / rho =
          Real.rpow delta (-eta) := by
      dsimp only [radius, rho]
      field_simp [hdelta.ne']
    rw [heq]
    exact hpow
  have hpower :
      Kakeya.realRpowENN
          (2 * radius / rho) (1 - epsilon) ≤ 1 := by
    apply ENNReal.ofReal_le_one.mpr
    exact Real.rpow_le_one_of_one_le_of_nonpos
      hbase (by linarith)
  refine
    ⟨rho, center, radius, le_rfl, hdelta_one,
      hradius, ?_, hpower.trans honeCover⟩
  dsimp only [rho, radius]
  ring_nf
  exact le_rfl

end

end Kakeya.Assouad
