import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition45TwoEndsStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.ProjectionTheoremLocalizationStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.ProjectionTransport
import Mathlib.Topology.MetricSpace.CoveringNumbers

/-!
# Projection helpers for the wide branch of WZ1 Proposition 8.9

This module isolates two mechanical bridges used after anisotropic
normalization:

* a global dot-difference covering bound gives a localized long projection;
* weighted raw strip nonconcentration, together with a retention loss, gives
  the standard line-nonconcentration predicate.
-/

namespace Kakeya.Assouad

noncomputable section

open scoped ENNReal

/-- Inverting the positive base negates the real-rpow exponent. -/
private lemma realRpowENN_one_div
    {base exponent : ℝ} (hbase : 0 < base) :
    Kakeya.realRpowENN (1 / base) exponent =
      Kakeya.realRpowENN base (-exponent) := by
  simp only [Kakeya.realRpowENN]
  congr 1
  calc
    Real.rpow (1 / base) exponent =
        Real.rpow 1 exponent / Real.rpow base exponent :=
      Real.div_rpow (by norm_num) hbase.le exponent
    _ = (Real.rpow base exponent)⁻¹ := by simp
    _ = Real.rpow base (-exponent) :=
      (Real.rpow_neg hbase.le exponent).symm

/--
The elementary exponent comparison used when localizing a global covering
bound to the radius-two ball.
-/
lemma wide_branch_covering_exponent
    {tau epsilon : ℝ}
    (htau : 0 < tau)
    (hreal :
      Real.rpow 4 (1 - epsilon) ≤
        Real.rpow tau (-epsilon / 2)) :
    Kakeya.realRpowENN (4 / tau) (1 - epsilon) ≤
      Kakeya.realRpowENN tau (epsilon / 2 - 1) := by
  have hfour :
      Kakeya.realRpowENN 4 (1 - epsilon) ≤
        Kakeya.realRpowENN tau (-epsilon / 2) := by
    exact ENNReal.ofReal_mono hreal
  have hquotient :
      Kakeya.realRpowENN (4 / tau) (1 - epsilon) =
        Kakeya.realRpowENN 4 (1 - epsilon) *
          Kakeya.realRpowENN tau (-(1 - epsilon)) := by
    calc
      Kakeya.realRpowENN (4 / tau) (1 - epsilon) =
          Kakeya.realRpowENN (4 * (1 / tau)) (1 - epsilon) := by
        congr 2
        ring
      _ =
          Kakeya.realRpowENN 4 (1 - epsilon) *
            Kakeya.realRpowENN (1 / tau) (1 - epsilon) :=
        realRpowENN_mul (by norm_num) (by positivity) _
      _ =
          Kakeya.realRpowENN 4 (1 - epsilon) *
            Kakeya.realRpowENN tau (-(1 - epsilon)) := by
        rw [realRpowENN_one_div htau]
  have htarget :
      Kakeya.realRpowENN tau (epsilon / 2 - 1) =
        Kakeya.realRpowENN tau (-epsilon / 2) *
          Kakeya.realRpowENN tau (-(1 - epsilon)) := by
    have hexponent :
        epsilon / 2 - 1 =
          (-epsilon / 2) + (-(1 - epsilon)) := by
      ring
    rw [hexponent]
    exact realRpowENN_add htau _ _
  rw [hquotient, htarget]
  gcongr

/--
Convert a global normalized dot-difference covering bound at scale `tau` to
the long-projection conclusion on the original graph.

All normalized dot differences are assumed to lie in `[-2, 2]`; the same
covering set is therefore the intersection with the radius-two ball.
-/
lemma global_covering_to_long_projection
    {delta epsilon eta tau : ℝ}
    {H : Finset (Point2 × Point2 × Point2)}
    (hdelta : 0 < delta)
    (htau : 0 < tau)
    (hdeltaTau : delta ≤ tau)
    (htauOne : tau ≤ 1)
    (hthin : Real.rpow delta (-eta) * tau ≤ 4)
    (hexponent :
      Real.rpow 4 (1 - epsilon) ≤
        Real.rpow tau (-epsilon / 2))
    (hball :
      ∀ value ∈ wz1DotDifferenceSet H, |value| ≤ 2)
    (hcover :
      Kakeya.realRpowENN tau (epsilon / 2 - 1) ≤
        (↑(Metric.externalCoveringNumber
          (Real.toNNReal tau)
          (wz1DotDifferenceSet H)) : ENNReal)) :
    WZ1StripLocalizationLongProjection
      delta epsilon eta H := by
  let center : ℝ := 0
  let radius : ℝ := 2
  have hradius : 0 < radius := by norm_num
  have hlength :
      Real.rpow delta (-eta) * tau ≤ 2 * radius := by
    calc
      Real.rpow delta (-eta) * tau ≤ 4 := hthin
      _ = 2 * radius := by norm_num [radius]
  have hsubset :
      wz1DotDifferenceSet H ⊆
        Metric.closedBall center radius := by
    intro value hvalue
    simpa [center, radius, Metric.mem_closedBall, Real.dist_eq] using
      hball value hvalue
  have hintersection :
      wz1DotDifferenceSet H ∩ Metric.closedBall center radius =
        wz1DotDifferenceSet H :=
    Set.inter_eq_left.mpr hsubset
  have hpower :=
    wide_branch_covering_exponent htau hexponent
  refine
    ⟨tau, center, radius, hdeltaTau, htauOne, hradius,
      hlength, ?_⟩
  rw [hintersection]
  have hratio : 2 * radius / tau = 4 / tau := by
    dsimp only [radius]
    ring
  rw [hratio]
  exact hpower.trans hcover

/--
Rewrite the weighted raw strip factor in the multiplicative
`realRpowENN` convention.
-/
private lemma weighted_raw_power_identity
    {width radius zeta : ℝ}
    (hwidth : 0 < width) (hradius : 0 < radius) :
    ENNReal.ofReal
        ((Real.rpow width zeta)⁻¹ *
          Real.rpow radius zeta) =
      Kakeya.realRpowENN width (-zeta) *
        Kakeya.realRpowENN radius zeta := by
  have hnegative :
      (Real.rpow width zeta)⁻¹ =
        Real.rpow width (-zeta) :=
    (Real.rpow_neg hwidth.le zeta).symm
  rw [hnegative]
  exact ENNReal.ofReal_mul (Real.rpow_nonneg hwidth.le _)

/-- Power identity matching `WZ1LineNonConcentration`. -/
private lemma line_nonconcentration_power_identity
    {tau radius lambda zeta : ℝ}
    (htau : 0 < tau) (hradius : 0 < radius) :
    Kakeya.realRpowENN tau (-lambda * zeta) *
        Kakeya.realRpowENN radius zeta =
      Kakeya.realRpowENN
        (Real.rpow tau (-lambda) * radius) zeta := by
  have hbase : 0 < Real.rpow tau (-lambda) :=
    Real.rpow_pos_of_pos htau _
  have hiterated :
      Kakeya.realRpowENN tau (-lambda * zeta) =
        Kakeya.realRpowENN
          (Real.rpow tau (-lambda)) zeta := by
    simp only [Kakeya.realRpowENN]
    congr 1
    exact Real.rpow_mul htau.le (-lambda) zeta
  rw [hiterated]
  exact
    (realRpowENN_mul hbase hradius zeta).symm

/--
Transfer weighted raw strip nonconcentration to the standard
line-nonconcentration predicate on a retained subset.

`retentionInv` is an explicit reciprocal retention loss.  The hypothesis
`hconstant` absorbs this loss and converts the original strip width to the
target scale `tau`.
-/
lemma WZ1WeightedRawStripNonconcentration.toLineNonconcentration
    {delta tau rawWidth zeta lambda : ℝ}
    {constant retentionInv : ENNReal}
    {ambient selected : DiscreteSet 2}
    (hraw :
      WZ1WeightedRawStripNonconcentration
        delta zeta rawWidth constant ambient)
    (hselected : selected ⊆ ambient)
    (hretention :
      ambient.enncard ≤ retentionInv * selected.enncard)
    (hconstant :
      constant *
          Kakeya.realRpowENN rawWidth (-zeta) *
          retentionInv ≤
        Kakeya.realRpowENN tau (-lambda * zeta))
    (hdeltaTau : delta ≤ tau)
    (htau : 0 < tau)
    (hrawWidth : 0 < rawWidth) :
    WZ1LineNonConcentration tau lambda zeta selected := by
  intro normal hnormal level radius htauRadius hradiusOne
  have hradius : 0 < radius := htau.trans_le htauRadius
  have hdeltaRadius : delta ≤ radius :=
    hdeltaTau.trans htauRadius
  let strip : Point2 → Prop :=
    fun point => |inner ℝ point normal - level| ≤ radius
  have hcount :
      ((selected.filter strip).card : ENNReal) ≤
        ((ambient.filter strip).card : ENNReal) := by
    exact_mod_cast
      Finset.card_le_card
        (Finset.filter_subset_filter strip hselected)
  have hambient :
      ((ambient.filter strip).card : ENNReal) ≤
        constant *
          Kakeya.realRpowENN rawWidth (-zeta) *
          Kakeya.realRpowENN radius zeta *
          ambient.enncard := by
    have hrawAt :=
      hraw normal hnormal level radius hdeltaRadius
    rw [weighted_raw_power_identity hrawWidth hradius] at hrawAt
    simpa [strip, mul_assoc] using hrawAt
  calc
    ((selected.filter strip).card : ENNReal)
        ≤ constant *
            Kakeya.realRpowENN rawWidth (-zeta) *
            Kakeya.realRpowENN radius zeta *
            ambient.enncard :=
      hcount.trans hambient
    _ ≤
        constant *
          Kakeya.realRpowENN rawWidth (-zeta) *
          Kakeya.realRpowENN radius zeta *
          (retentionInv * selected.enncard) := by
      gcongr
    _ =
        (constant *
            Kakeya.realRpowENN rawWidth (-zeta) *
            retentionInv) *
          Kakeya.realRpowENN radius zeta *
          selected.enncard := by
      ring
    _ ≤
        Kakeya.realRpowENN tau (-lambda * zeta) *
          Kakeya.realRpowENN radius zeta *
          selected.enncard := by
      gcongr
    _ =
        Kakeya.realRpowENN
            (Real.rpow tau (-lambda) * radius) zeta *
          selected.enncard := by
      rw [line_nonconcentration_power_identity htau hradius]

end

/--
Weaken a line-nonconcentration exponent.  For a base scale at most one,
increasing `lambda` only enlarges the permitted strip count.
-/
lemma WZ1LineNonConcentration.mono_lambda
    {tau smallerLambda largerLambda zeta : ℝ}
    {set : DiscreteSet 2}
    (h : WZ1LineNonConcentration
      tau smallerLambda zeta set)
    (htau : 0 < tau) (htauOne : tau ≤ 1)
    (hlambda : smallerLambda ≤ largerLambda)
    (hzeta : 0 ≤ zeta) :
    WZ1LineNonConcentration
      tau largerLambda zeta set := by
  intro normal hnormal level radius htauRadius hradiusOne
  have hradius : 0 < radius := htau.trans_le htauRadius
  have hpower :
      Real.rpow tau (-smallerLambda) ≤
        Real.rpow tau (-largerLambda) :=
    Real.rpow_le_rpow_of_exponent_ge htau htauOne
      (by linarith)
  have hbase :
      Real.rpow tau (-smallerLambda) * radius ≤
        Real.rpow tau (-largerLambda) * radius := by
    gcongr
  have hcoefficient :
      Kakeya.realRpowENN
          (Real.rpow tau (-smallerLambda) * radius) zeta ≤
        Kakeya.realRpowENN
          (Real.rpow tau (-largerLambda) * radius) zeta := by
    simp only [Kakeya.realRpowENN]
    exact ENNReal.ofReal_mono
      (Real.rpow_le_rpow
        (mul_nonneg
          (Real.rpow_nonneg htau.le _) hradius.le)
        hbase hzeta)
  exact
    (h normal hnormal level radius
      htauRadius hradiusOne).trans (by gcongr)

/--
Transport a normalized dot-difference covering bound to a long projection
on the original graph.

The chain is:
1. `sourceDot = width * normalizedDot` (exact scaling identity);
2. scale covering by `width`;
3. use the normalized radius-two bound;
4. enlarge from the literal source subgraph to the original graph.

This is a conditional transport helper.  A coarse snapped graph must first
be related to a literal normalized source graph; closeness to snapped cell
centers alone does not establish `h_dot_eq`.
-/
lemma wide_normalized_covering_transport
    {delta epsilon eta width scale : ℝ}
    {H sourceH normalizedH : Finset (Point2 × Point2 × Point2)}
    (hdelta : 0 < delta)
    (hdelta_one : delta ≤ 1)
    (_heta : 0 < eta)
    (_hepsilon : 0 < epsilon)
    (hscale_pos : 0 < scale)
    (_hscale_one : scale ≤ 1)
    (hwidth_pos : 0 < width)
    (hscale_eq : width * scale = delta)
    (hsource_subset : sourceH ⊆ H)
    (h_dot_eq : wz1DotDifferenceSet sourceH =
        (fun x : ℝ => width * x) '' wz1DotDifferenceSet normalizedH)
    (hnormalized_ball :
      ∀ value ∈ wz1DotDifferenceSet normalizedH, |value| ≤ 2)
    (hthin : Real.rpow delta (-eta) * scale ≤ 4)
    (hexponent :
      Real.rpow 4 (1 - epsilon) ≤
        Real.rpow scale (-epsilon / 2)) :
    (Kakeya.realRpowENN scale (epsilon / 2 - 1) ≤
      (↑(Metric.externalCoveringNumber (Real.toNNReal scale)
        (wz1DotDifferenceSet normalizedH)) : ENNReal)) →
    WZ1StripLocalizationLongProjection delta epsilon eta H := by
  intro hcover
  set rho : ℝ := delta with hrho_def
  set radius : ℝ := 2 * width with hradius_def
  have hradius_pos : 0 < radius := by positivity
  have hthin' :
      Real.rpow delta (-eta) * rho ≤ 2 * radius := by
    simp only [hrho_def, hradius_def]
    have hscaled :
        Real.rpow delta (-eta) * (width * scale) ≤
          4 * width := by
      calc
        Real.rpow delta (-eta) * (width * scale)
            = width *
                (Real.rpow delta (-eta) * scale) := by ring
        _ ≤ width * 4 := by gcongr
        _ = 4 * width := by ring
    rw [hscale_eq] at hscaled
    linarith
  have hsource_ball :
      ∀ value ∈ wz1DotDifferenceSet sourceH,
        |value| ≤ radius := by
    intro value hvalue
    rw [h_dot_eq] at hvalue
    rcases hvalue with ⟨normalizedValue, hnormalizedValue, rfl⟩
    have hbound :=
      hnormalized_ball normalizedValue hnormalizedValue
    calc
      |width * normalizedValue| = width * |normalizedValue| := by
        rw [abs_mul, abs_of_pos hwidth_pos]
      _ ≤ width * 2 := by gcongr
      _ = radius := by simp [hradius_def] <;> ring
  have hsource_subset_ball :
      wz1DotDifferenceSet sourceH ⊆
        Metric.closedBall (0 : ℝ) radius := by
    intro value hvalue
    simpa [Metric.mem_closedBall, Real.dist_eq] using
      hsource_ball value hvalue
  have h_cover_scaled :
      Metric.externalCoveringNumber (Real.toNNReal delta)
          (wz1DotDifferenceSet sourceH) =
        Metric.externalCoveringNumber (Real.toNNReal scale)
          (wz1DotDifferenceSet normalizedH) := by
    rw [h_dot_eq, ← hrho_def, ← hscale_eq]
    exact real_covering_number_scaling hwidth_pos (by linarith)
  have hcover_source :
      Kakeya.realRpowENN scale (epsilon / 2 - 1) ≤
        (↑(Metric.externalCoveringNumber (Real.toNNReal delta)
          (wz1DotDifferenceSet sourceH)) : ENNReal) := by
    rw [h_cover_scaled]
    exact hcover
  have hpower :
      Kakeya.realRpowENN (2 * radius / rho) (1 - epsilon) ≤
        Kakeya.realRpowENN scale (epsilon / 2 - 1) := by
    have hratio : 2 * radius / rho = 4 / scale := by
      calc
        2 * radius / rho = 4 * width / rho := by
          simp [hradius_def] <;> ring
        _ = 4 * width / (width * scale) := by rw [hscale_eq]
        _ = 4 / scale := by field_simp [hwidth_pos.ne']
    rw [hratio]
    exact wide_branch_covering_exponent hscale_pos hexponent
  have hsource_dot_subset :
      wz1DotDifferenceSet sourceH ⊆ wz1DotDifferenceSet H := by
    intro value hvalue
    simp only [wz1DotDifferenceSet] at hvalue ⊢
    rcases Finset.mem_image.mp hvalue with
      ⟨edge, hedge, rfl⟩
    exact Finset.mem_image.mpr
      ⟨edge, hsource_subset hedge, rfl⟩
  have hsource_inter_subset :
      wz1DotDifferenceSet sourceH ⊆
        wz1DotDifferenceSet H ∩
          Metric.closedBall (0 : ℝ) radius := by
    intro value hvalue
    exact
      ⟨hsource_dot_subset hvalue,
        hsource_subset_ball hvalue⟩
  have hcover_mono :
      (Metric.externalCoveringNumber (Real.toNNReal rho)
          (wz1DotDifferenceSet sourceH) : ENNReal) ≤
        (Metric.externalCoveringNumber (Real.toNNReal rho)
          (wz1DotDifferenceSet H ∩
            Metric.closedBall (0 : ℝ) radius) : ENNReal) := by
    exact_mod_cast
      Metric.externalCoveringNumber_mono_set
        hsource_inter_subset
  have hH_cover :
      Kakeya.realRpowENN (2 * radius / rho) (1 - epsilon) ≤
        (↑(Metric.externalCoveringNumber (Real.toNNReal rho)
          (wz1DotDifferenceSet H ∩
            Metric.closedBall (0 : ℝ) radius)) : ENNReal) := by
    calc
      Kakeya.realRpowENN (2 * radius / rho) (1 - epsilon)
          ≤ Kakeya.realRpowENN scale (epsilon / 2 - 1) :=
        hpower
      _ ≤
          (↑(Metric.externalCoveringNumber (Real.toNNReal rho)
            (wz1DotDifferenceSet sourceH)) : ENNReal) := by
        simpa [hrho_def] using hcover_source
      _ ≤
          (↑(Metric.externalCoveringNumber (Real.toNNReal rho)
            (wz1DotDifferenceSet H ∩
              Metric.closedBall (0 : ℝ) radius)) : ENNReal) :=
        hcover_mono
  exact
    ⟨rho, (0 : ℝ), radius, by linarith [hrho_def],
      hdelta_one, hradius_pos, hthin', hH_cover⟩

end Kakeya.Assouad
