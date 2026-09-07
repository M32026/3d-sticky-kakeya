import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma40Absorption
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma49ActiveWidthGeometry
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma49LargeEpsilon
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma49OutsideActiveStrip

/-!
# Outer assembly of WZ1 Lemma 49

This module performs only the elementary case split and parameter
monotonicity around the two genuine projection leaves:

* the graph-active outside-orthogonal-strip covering argument; and
* the residual anisotropic-rescaling/radial-projection/Kaufman argument.

It never replaces the graph-active common width by an ambient maximum.
-/

namespace Kakeya.Assouad

noncomputable section

private lemma wz1Lemma49_rpow_neg_mono
    {delta first second : ℝ}
    (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    (hfirstSecond : first ≤ second) :
    Kakeya.realRpowENN delta (-first) ≤
      Kakeya.realRpowENN delta (-second) := by
  apply ENNReal.ofReal_mono
  exact Real.rpow_le_rpow_of_exponent_ge
    hdelta hdelta_one (by linarith)

private lemma wz1Lemma49_rpow_pos_antitone
    {delta first second : ℝ}
    (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    (hfirstSecond : first ≤ second) :
    Kakeya.realRpowENN delta second ≤
      Kakeya.realRpowENN delta first := by
  apply ENNReal.ofReal_mono
  exact Real.rpow_le_rpow_of_exponent_ge
    hdelta hdelta_one hfirstSecond

/--
The long-projection conclusion weakens when its loss exponent decreases.
-/
lemma wz1Lemma49_longProjection_mono_eta
    {delta epsilon eta eta' : ℝ}
    {H : Finset (Point2 × Point2 × Point2)}
    (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    (heta : eta ≤ eta')
    (h :
      WZ1StripLocalizationLongProjection
        delta epsilon eta' H) :
    WZ1StripLocalizationLongProjection
      delta epsilon eta H := by
  rcases h with
    ⟨rho, center, radius, hdeltaRho, hrhoOne,
      hradius, hlength, hcover⟩
  have hrho : 0 ≤ rho := by
    linarith
  have hpower :
      Real.rpow delta (-eta) ≤
        Real.rpow delta (-eta') := by
    exact Real.rpow_le_rpow_of_exponent_ge
      hdelta hdelta_one (by linarith)
  refine
    ⟨rho, center, radius, hdeltaRho, hrhoOne,
      hradius, ?_, hcover⟩
  calc
    Real.rpow delta (-eta) * rho
        ≤ Real.rpow delta (-eta') * rho := by
      gcongr
    _ ≤ 2 * radius := hlength

/--
Assemble the complete Lemma 49 dichotomy from its two non-elementary leaves.
-/
theorem wz1_lemma49_outer_assembly
    (hOutside : WZ1Lemma49OutsideActiveStripStatement)
    (hKaufman : WZ1StripLocalizationKaufmanCaseStatement) :
    WZ1StripLocalizationDichotomyStatement := by
  intro epsilon hepsilon
  by_cases hepsilonOne : epsilon < 1
  · let epsilonAux := wz1Lemma49AuxiliaryEpsilon epsilon
    have hepsilonAux : 0 ≤ epsilonAux := by
      dsimp only [epsilonAux, wz1Lemma49AuxiliaryEpsilon]
      positivity
    rcases hOutside epsilon hepsilon hepsilonOne with
      ⟨etaOutside, deltaOutside,
        hetaOutside, hetaOutsideBudget,
        hdeltaOutside, hdeltaOutsideOne,
        hOutsideTail⟩
    rcases hKaufman epsilon hepsilon hepsilonOne with
      ⟨etaKaufman, deltaKaufman,
        hetaKaufman, hdeltaKaufman,
        hdeltaKaufmanOne, hKaufmanTail⟩
    let eta := min etaOutside etaKaufman
    let delta₀ := min deltaOutside deltaKaufman
    have heta : 0 < eta := by
      simp [eta, hetaOutside, hetaKaufman]
    have hetaOutsideLe : eta ≤ etaOutside := by
      exact min_le_left _ _
    have hetaKaufmanLe : eta ≤ etaKaufman := by
      exact min_le_right _ _
    have hdelta₀ : 0 < delta₀ := by
      simp [delta₀, hdeltaOutside, hdeltaKaufman]
    have hdelta₀One : delta₀ ≤ 1 := by
      exact (min_le_left _ _).trans hdeltaOutsideOne
    refine
      ⟨eta, delta₀, heta, hdelta₀, hdelta₀One, ?_⟩
    intro delta hdelta hdeltaLe
    have hdeltaOne : delta ≤ 1 :=
      hdeltaLe.trans hdelta₀One
    have hdeltaOutsideLe : delta ≤ deltaOutside :=
      hdeltaLe.trans (min_le_left _ _)
    have hdeltaKaufmanLe : delta ≤ deltaKaufman :=
      hdeltaLe.trans (min_le_right _ _)
    intro F G₁ G₂ hF hG₁ hG₂
      hFball hG₁ball hG₂ball
      hFsep hG₁sep hG₂sep
      hFfrost hG₁frost hG₂frost hstandard
      H hDensity base direction hdirection w hw hwDelta hG₁strip
    have hFfrostOutside :
        F.IsFrostman delta 1
          (Kakeya.realRpowENN delta (-etaOutside)) :=
      hFfrost.mono_const
        (wz1Lemma49_rpow_neg_mono
          hdelta hdeltaOne hetaOutsideLe)
    have hG₁frostOutside :
        G₁.IsFrostman delta 1
          (Kakeya.realRpowENN delta (-etaOutside)) :=
      hG₁frost.mono_const
        (wz1Lemma49_rpow_neg_mono
          hdelta hdeltaOne hetaOutsideLe)
    have hG₂frostOutside :
        G₂.IsFrostman delta 1
          (Kakeya.realRpowENN delta (-etaOutside)) :=
      hG₂frost.mono_const
        (wz1Lemma49_rpow_neg_mono
          hdelta hdeltaOne hetaOutsideLe)
    have hDensityOutside :
        WZ1UniformTripleDensity
          (Kakeya.realRpowENN delta etaOutside)
          F G₁ G₂ H :=
      uniform_triple_density_mono hDensity
        (wz1Lemma49_rpow_pos_antitone
          hdelta hdeltaOne hetaOutsideLe)
    have hFfrostKaufman :
        F.IsFrostman delta 1
          (Kakeya.realRpowENN delta (-etaKaufman)) :=
      hFfrost.mono_const
        (wz1Lemma49_rpow_neg_mono
          hdelta hdeltaOne hetaKaufmanLe)
    have hG₁frostKaufman :
        G₁.IsFrostman delta 1
          (Kakeya.realRpowENN delta (-etaKaufman)) :=
      hG₁frost.mono_const
        (wz1Lemma49_rpow_neg_mono
          hdelta hdeltaOne hetaKaufmanLe)
    have hG₂frostKaufman :
        G₂.IsFrostman delta 1
          (Kakeya.realRpowENN delta (-etaKaufman)) :=
      hG₂frost.mono_const
        (wz1Lemma49_rpow_neg_mono
          hdelta hdeltaOne hetaKaufmanLe)
    have hDensityKaufman :
        WZ1UniformTripleDensity
          (Kakeya.realRpowENN delta etaKaufman)
          F G₁ G₂ H :=
      uniform_triple_density_mono hDensity
        (wz1Lemma49_rpow_pos_antitone
          hdelta hdeltaOne hetaKaufmanLe)
    let t :=
      wz1ActiveCommonWidth
        delta H hDensity.1 base direction
    by_cases hEscape :
        ∃ edge ∈ H,
          edge.1 ∉
            wz1LineNeighborhood 0
              (wz1Perp2 direction)
              (Real.rpow delta (-epsilonAux) * t)
    · have hlong :
          WZ1StripLocalizationLongProjection
            delta epsilon etaOutside H := by
        exact
          hOutsideTail delta hdelta hdeltaOutsideLe
            F G₁ G₂ hF hG₁ hG₂
            hFball hG₁ball hG₂ball
            hFsep hG₁sep hG₂sep
            hFfrostOutside hG₁frostOutside hG₂frostOutside
            hstandard H hDensityOutside base direction
            hdirection hEscape
      exact Or.inr
        (wz1Lemma49_longProjection_mono_eta
          hdelta hdeltaOne hetaOutsideLe hlong)
    · have hfirst :
          ∀ edge ∈ H,
            edge.1 ∈
              wz1LineNeighborhood 0
                (wz1Perp2 direction)
                (Real.rpow delta (-epsilonAux) * t) := by
        push Not at hEscape
        exact hEscape
      by_cases hsmall :
          t ≤
            Real.rpow delta (-epsilon + epsilonAux) * w
      · exact Or.inl
          (wz1_lemma49_small_active_width_localization
            hDensity.1 hdelta hdeltaOne hepsilon hepsilonAux
            base direction hw.le hfirst hsmall)
      · have hlarge :
            Real.rpow delta (-epsilon + epsilonAux) * w < t :=
          lt_of_not_ge hsmall
        have hlong :
            WZ1StripLocalizationLongProjection
              delta epsilon etaKaufman H := by
          exact
            hKaufmanTail delta hdelta hdeltaKaufmanLe
              F G₁ G₂ hF hG₁ hG₂
              hFball hG₁ball hG₂ball
              hFsep hG₁sep hG₂sep
              hFfrostKaufman hG₁frostKaufman hG₂frostKaufman
              hstandard H hDensityKaufman
              base direction hdirection w hw hwDelta hG₁strip
              hfirst hlarge
        exact Or.inr
          (wz1Lemma49_longProjection_mono_eta
            hdelta hdeltaOne hetaKaufmanLe hlong)
  · have hepsilonLarge : 1 ≤ epsilon :=
      le_of_not_gt hepsilonOne
    let eta := epsilon / 100
    let delta₀ : ℝ := 1
    have heta : 0 < eta := by
      dsimp only [eta]
      positivity
    refine
      ⟨eta, delta₀, heta, by norm_num, by norm_num, ?_⟩
    intro delta hdelta hdeltaOne
    intro F G₁ G₂ hF hG₁ hG₂
      hFball hG₁ball hG₂ball
      hFsep hG₁sep hG₂sep
      hFfrost hG₁frost hG₂frost hstandard
      H hDensity base direction hdirection w hw hwDelta hG₁strip
    exact Or.inr
      (wz1_lemma49_large_epsilon_long_projection
        hdelta hdeltaOne heta hepsilonLarge hDensity.1)

/--
The complete Lemma 49 dichotomy now depends only on its genuine residual
anisotropic-rescaling/radial-projection/Kaufman branch.
-/
theorem wz1_strip_localization_dichotomy_from_kaufman :
    WZ1StripLocalizationDichotomyFromKaufmanStatement := by
  intro hKaufman
  exact
    wz1_lemma49_outer_assembly
      wz1_lemma49_outside_active_strip hKaufman

end

end Kakeya.Assouad
