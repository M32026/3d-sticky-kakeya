import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma49LargeEpsilon
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition8_9ParameterSelection
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition8_9WideFromNormalized
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition8_9NarrowUnion

/-!
# Faithful union-valued assembly of WZ1 Proposition 8.9
-/

namespace Kakeya.Assouad

private lemma proposition8_9_long_projection_mono_epsilon
    {delta epsilon epsilon' eta : ℝ}
    {H : Finset (Point2 × Point2 × Point2)}
    (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    (hepsilon : epsilon' ≤ epsilon) (heta : 0 < eta)
    (h : WZ1StripLocalizationLongProjection delta epsilon' eta H) :
    WZ1StripLocalizationLongProjection delta epsilon eta H := by
  rcases h with
    ⟨rho, center, radius, hdeltaRho, hrhoOne, hradius, hlength, hcover⟩
  have hrho : 0 < rho := hdelta.trans_le hdeltaRho
  have hpowerOne : 1 ≤ Real.rpow delta (-eta) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos
      hdelta hdelta_one (by linarith)
  have hrhoLe : rho ≤ 2 * radius := by
    calc
      rho = 1 * rho := by ring
      _ ≤ Real.rpow delta (-eta) * rho := by gcongr
      _ ≤ 2 * radius := hlength
  have hratio : 1 ≤ 2 * radius / rho := by
    exact (le_div_iff₀ hrho).2 (by simpa using hrhoLe)
  have hcoverPower :
      Kakeya.realRpowENN (2 * radius / rho) (1 - epsilon) ≤
        Kakeya.realRpowENN (2 * radius / rho) (1 - epsilon') := by
    apply ENNReal.ofReal_mono
    exact Real.rpow_le_rpow_of_exponent_le hratio (by linarith)
  exact ⟨rho, center, radius, hdeltaRho, hrhoOne, hradius, hlength,
    hcoverPower.trans hcover⟩

theorem wz1_proposition8_9_union_split_assembly :
    WZ1Proposition8_9UnionSplitAssemblyStatement := by
  intro hParameters hCommon hNarrow hWide hHypergraph hAnisotropic
    hProjection hStrip hOSW
  intro epsilon hepsilon
  let epsilonWork := min epsilon (1 / 10 : ℝ)
  have hepsilonWork : 0 < epsilonWork := by
    dsimp only [epsilonWork]
    positivity
  have hepsilonWorkTenth : epsilonWork ≤ 1 / 10 := min_le_right _ _
  have hepsilonWorkOne : epsilonWork < 1 :=
    hepsilonWorkTenth.trans_lt (by norm_num)
  have hepsilonWorkLe : epsilonWork ≤ epsilon := min_le_left _ _
  rcases hParameters hProjection hOSW hStrip
      epsilonWork hepsilonWork hepsilonWorkTenth with
    ⟨parameters⟩
  rcases hNarrow epsilonWork parameters hepsilonWork hepsilonWorkOne with
    ⟨narrowEtaCap, narrowDelta₀, hnarrowEtaCap, hnarrowDelta₀,
      hnarrowDelta₀One, hnarrow⟩
  rcases hWide hHypergraph hAnisotropic epsilonWork parameters
      hepsilonWork hepsilonWorkOne with
    ⟨wideEtaCap, hwideEtaCap, hwideTail⟩
  let etaCap := min narrowEtaCap wideEtaCap
  let deltaCap := narrowDelta₀
  rcases hCommon epsilonWork parameters etaCap deltaCap
      hepsilonWork hepsilonWorkOne (by positivity) hnarrowDelta₀ with
    ⟨eta, delta₀, heta, hetaCap, hdelta₀, hdeltaCap,
      hdelta₀One, hcommon⟩
  have hetaNarrow : eta ≤ narrowEtaCap :=
    hetaCap.trans (min_le_left _ _)
  have hetaWide : eta ≤ wideEtaCap :=
    hetaCap.trans (min_le_right _ _)
  rcases hwideTail eta heta hetaWide with
    ⟨wideDelta₀, hwideDelta₀, hwideDelta₀One, hwide⟩
  let finalDelta₀ := min delta₀ wideDelta₀
  refine ⟨eta, finalDelta₀, heta, by positivity,
    (min_le_left _ _).trans hdelta₀One, ?_⟩
  intro delta hdelta hdeltaSmall F G₁ G₂ hF hG₁ hG₂
    hFball hG₁ball hG₂ball hFsep hG₁sep hG₂sep
    hFfrost hG₁frost hG₂frost hstandard H huniform
  have hdeltaCommon : delta ≤ delta₀ :=
    hdeltaSmall.trans (min_le_left _ _)
  have hdeltaWide : delta ≤ wideDelta₀ :=
    hdeltaSmall.trans (min_le_right _ _)
  have hdeltaOne : delta ≤ 1 := hdeltaCommon.trans hdelta₀One
  have liftLong :
      WZ1StripLocalizationLongProjection delta epsilonWork eta H →
        WZ1StripLocalizationLongProjection delta epsilon eta H := by
    intro hlong
    exact proposition8_9_long_projection_mono_epsilon
      hdelta hdeltaOne hepsilonWorkLe heta hlong
  have liftAlternative :
      WZ1Proposition8_9AlternativeAUnion
          delta epsilonWork F G₁ G₂ →
        (∃ base direction : Point2,
          ‖direction‖ = 1 ∧
          Kakeya.realRpowENN delta (epsilon - 1) ≤
            wz1DiscreteLineCount F 0 (wz1Perp2 direction) delta ∧
          (Kakeya.realRpowENN delta (epsilon - 1) ≤
              wz1DiscreteLineCount G₁ base direction delta ∨
            Kakeya.realRpowENN delta (epsilon - 1) ≤
              wz1DiscreteLineCount G₂ base direction delta)) := by
    rintro ⟨base, direction, hdirection, hFline, hGline⟩
    have hpower :
        Kakeya.realRpowENN delta (epsilon - 1) ≤
          Kakeya.realRpowENN delta (epsilonWork - 1) := by
      apply ENNReal.ofReal_mono
      exact Real.rpow_le_rpow_of_exponent_ge
        hdelta hdeltaOne (by linarith)
    exact ⟨base, direction, hdirection, hpower.trans hFline,
      hGline.imp (fun h => hpower.trans h) (fun h => hpower.trans h)⟩
  rcases hcommon delta hdelta hdeltaCommon F G₁ G₂ hF hG₁ hG₂
      hFball hG₁ball hG₂ball hFsep hG₁sep hG₂sep
      hFfrost hG₁frost hG₂frost hstandard H huniform with
    hlong | hdata
  · exact Or.inr (liftLong hlong)
  · rcases hdata with ⟨data⟩
    by_cases hnarrowWidth :
        data.width ≤ Real.rpow delta (1 - epsilonWork / 10)
    · rcases hnarrow hdelta (hdeltaCommon.trans hdeltaCap)
          heta hetaNarrow data hnarrowWidth with hA | hlong
      · exact Or.inl (liftAlternative hA)
      · exact Or.inr (liftLong hlong)
    · exact Or.inr
        (liftLong (hwide hdelta hdeltaWide data (lt_of_not_ge hnarrowWidth)))

end Kakeya.Assouad
