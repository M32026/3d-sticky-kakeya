import MyLeanRepo.Kakeya.Cinematic.Section5.UniformC2GlobalizationArithmetic
import MyLeanRepo.Kakeya.Cinematic.Section5.UniformC2GlobalizationMeasure
import MyLeanRepo.Kakeya.Cinematic.Section5.TaylorGlobalizationGeometry
import MyLeanRepo.Kakeya.Cinematic.Section5.LocalAssembly.LogAbsorption

/-!
# Uniform centered Taylor globalization

This module combines the logarithmic centered-sixteenth cover, same-witness
quadratic Taylor transport, the uniform controlled-interval estimate, and the
two endpoint-stub bounds. It does not infer `IsControlled` for a physical
short interval: the controlled interval exists only after Taylor transport.
-/

namespace Kakeya.Cinematic

open MeasureTheory Set

theorem wz2_uniformC2_local_level_set_from_taylor_globalization :
    WZ2UniformC2LocalLevelSetFromTaylorGlobalizationStatement := by
  intro hCover hGraph hStub hStubAbsorption hQuadratic hFinite hShort
  intro K D C_KT lambda M hK hD hC_KT hlambda hM epsilon hepsilon
  have hK_pos : 0 < K := by linarith
  have hlambda_pos : 0 < lambda := by linarith
  have hK_transport : 1 ≤ 12 * K := by nlinarith
  have hC_transport : 1 ≤ 2 * C_KT := by nlinarith
  have hlambda_transport : 1 ≤ 3 * K * lambda := by nlinarith
  have hM_transport : 0 ≤ 2 * M := by positivity
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg hD
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hexponent : 0 ≤ Real.log D / Real.log 2 :=
    div_nonneg hlogD hlog2.le
  have hbase :
      1 ≤ D * Real.rpow (6 * K) (Real.log D / Real.log 2) := by
    have h6K : 1 ≤ 6 * K := by nlinarith
    have hrpow :
        1 ≤ Real.rpow (6 * K) (Real.log D / Real.log 2) :=
      Real.one_le_rpow h6K hexponent
    nlinarith
  have hD_transport :
      1 ≤ (D * Real.rpow (6 * K) (Real.log D / Real.log 2)) ^ 3 :=
    one_le_pow₀ hbase
  rcases hShort
      (12 * K)
      ((D * Real.rpow (6 * K) (Real.log D / Real.log 2)) ^ 3)
      (2 * C_KT) (3 * K * lambda) (2 * M)
      hK_transport hD_transport hC_transport hlambda_transport hM_transport
      (epsilon / 4) (by positivity) with
    ⟨delta_short, hdelta_short_pos, hdelta_short_lambda, hshort⟩
  rcases hCover (K := 12 * K) hK_transport with
    ⟨C_cover, hC_cover_pos, hcover⟩
  rcases hStubAbsorption hGraph hStub
      hC_KT hlambda hM (show 0 < epsilon / 2 by positivity) with
    ⟨delta_stub, hdelta_stub_pos, hdelta_stub_lambda, hstub⟩
  let scaleConstant : ℝ := Real.rpow (3 * K) (epsilon / 4)
  have hscaleConstant_pos : 0 < scaleConstant := by
    dsimp only [scaleConstant]
    exact Real.rpow_pos_of_pos (by positivity) _
  rcases localAssembly_log_absorption_general
      scaleConstant 1 (epsilon / 4)
      hscaleConstant_pos (by norm_num) (by positivity) with
    ⟨delta_scale, hdelta_scale_pos, hdelta_scale_one, hscale_absorb⟩
  have hcoverConstant_pos : 0 < C_cover + 2 := by linarith
  rcases localAssembly_log_absorption_general
      (C_cover + 2) 1 (epsilon / 2)
      hcoverConstant_pos (by norm_num) (by positivity) with
    ⟨delta_card, hdelta_card_pos, hdelta_card_one, hcard_absorb⟩
  let delta_geometry : ℝ := (288 * K * lambda)⁻¹
  have hdelta_geometry_pos : 0 < delta_geometry := by
    dsimp only [delta_geometry]
    positivity
  let delta₀ : ℝ :=
    min delta_short
      (min delta_stub
        (min delta_scale
          (min delta_card (min delta_geometry 1))))
  have hdelta₀_pos : 0 < delta₀ := by
    dsimp only [delta₀]
    positivity
  have hdelta₀_lambda : delta₀ ≤ 1 / lambda := by
    have hle : delta₀ ≤ delta_stub := by simp [delta₀]
    exact hle.trans hdelta_stub_lambda
  refine ⟨delta₀, hdelta₀_pos, hdelta₀_lambda, ?_⟩
  intro delta hdelta hdelta₀ family hfamily hbound
    F hF_family hF_separated hF_KT c mu hmu E₀ hE₀ hE₀_strip hE₀_level
  have hdelta_short : delta ≤ delta_short :=
    hdelta₀.trans (by simp [delta₀])
  have hdelta_stub : delta ≤ delta_stub :=
    hdelta₀.trans (by simp [delta₀])
  have hdelta_scale : delta ≤ delta_scale :=
    hdelta₀.trans (by simp [delta₀])
  have hdelta_card : delta ≤ delta_card :=
    hdelta₀.trans (by simp [delta₀])
  have hdelta_geometry : delta ≤ delta_geometry :=
    hdelta₀.trans (by simp [delta₀])
  have hdelta_one : delta ≤ 1 :=
    hdelta₀.trans (by simp [delta₀])
  let rho : ℝ := lambda * delta
  have hrho_pos : 0 < rho := by
    dsimp only [rho]
    positivity
  have hrho_one : rho ≤ 1 := by
    have hdelta_lambda : delta ≤ 1 / lambda :=
      hdelta_stub.trans hdelta_stub_lambda
    dsimp only [rho]
    simpa [mul_comm] using
      (le_div_iff₀ hlambda_pos).mp hdelta_lambda
  have hrho_cover : rho ≤ (24 * (12 * K))⁻¹ := by
    have hmul :
        lambda * delta ≤ lambda * delta_geometry :=
      mul_le_mul_of_nonneg_left hdelta_geometry hlambda_pos.le
    have heq :
        lambda * delta_geometry = (24 * (12 * K))⁻¹ := by
      dsimp only [delta_geometry]
      field_simp [hK_pos.ne', hlambda_pos.ne']
      ring
    simpa [rho, heq] using hmul
  rcases hcover hrho_pos hrho_cover with
    ⟨intervals, hintervals_card, hintervals, hcard, hcover_middle⟩
  let leftStub : Set (ℝ × ℝ) :=
    E₀ ∩ (Set.Icc 0 (2 * rho) ×ˢ (Set.univ : Set ℝ))
  let rightStub : Set (ℝ × ℝ) :=
    E₀ ∩ (Set.Icc (1 - 2 * rho) 1 ×ˢ (Set.univ : Set ℝ))
  let pieces : Fin intervals.card → Set (ℝ × ℝ) := fun i =>
    E₀ ∩
      ((intervals.interval i).realCenteredCarrier (1 / 16) ×ˢ
        Set.Icc c (c + 1))
  have htwo_rho : 2 * rho ≤ 1 := by
    have hsmall : rho ≤ 1 / 288 := by
      have hK288 : (288 * K)⁻¹ ≤ (288 : ℝ)⁻¹ := by
        gcongr
        nlinarith
      have hcover_eq : (24 * (12 * K))⁻¹ = (288 * K)⁻¹ := by ring_nf
      rw [hcover_eq] at hrho_cover
      exact hrho_cover.trans (hK288.trans (by norm_num))
    linarith
  have hcover_E :
      E₀ ⊆ leftStub ∪ rightStub ∪ ⋃ i, pieces i := by
    intro p hp
    by_cases hleft : p.1 ≤ 2 * rho
    · exact Or.inl <| Or.inl
        ⟨hp, ⟨(hE₀_strip hp).1.1, hleft⟩, trivial⟩
    by_cases hright : 1 - 2 * rho ≤ p.1
    · exact Or.inl <| Or.inr
        ⟨hp, ⟨hright, (hE₀_strip hp).1.2⟩, trivial⟩
    · have hmiddle : p.1 ∈ Set.Icc (2 * rho) (1 - 2 * rho) := by
        exact ⟨le_of_not_ge hleft, le_of_not_ge hright⟩
      rcases Set.mem_iUnion.mp (hcover_middle hmiddle) with ⟨i, hi⟩
      exact Or.inr <|
        Set.mem_iUnion.mpr ⟨i, ⟨hp, hi, (hE₀_strip hp).2⟩⟩
  let B : ENNReal :=
    ENNReal.ofReal
      (Real.rpow delta (-(epsilon / 2)) *
        Real.rpow (mu : ℝ) (-3 / 2 : ℝ))
  have hleft_volume : volume leftStub ≤ B := by
    by_cases hne : leftStub.Nonempty
    · exact hstub (delta := delta) (F := F) (mu := mu)
        (E := leftStub) (a := 0) (b := 2 * rho)
        hdelta hdelta_stub hF_KT hmu hne
        (by
          dsimp only [leftStub]
          exact hE₀.inter
            (measurableSet_Icc.prod MeasurableSet.univ))
        (by linarith)
        (by
          intro x hx
          exact ⟨hx.1, hx.2.trans htwo_rho⟩)
        (by
          dsimp only [rho]
          ring_nf
          exact le_rfl)
        (fun f hf x =>
          HasUniformC2Bound.firstDerivative hbound (hF_family hf) x)
        (by
          intro p hp
          exact hp.2)
        (by
          intro p hp
          exact (hE₀_level p hp.1).1)
    · have hempty : leftStub = ∅ :=
        Set.not_nonempty_iff_eq_empty.mp hne
      rw [hempty, measure_empty]
      exact bot_le
  have hright_volume : volume rightStub ≤ B := by
    by_cases hne : rightStub.Nonempty
    · exact hstub (delta := delta) (F := F) (mu := mu)
        (E := rightStub) (a := 1 - 2 * rho) (b := 1)
        hdelta hdelta_stub hF_KT hmu hne
        (by
          dsimp only [rightStub]
          exact hE₀.inter
            (measurableSet_Icc.prod MeasurableSet.univ))
        (by linarith)
        (by
          intro x hx
          have hleft_nonneg : 0 ≤ 1 - 2 * rho := by linarith
          exact ⟨hleft_nonneg.trans hx.1, hx.2⟩)
        (by
          dsimp only [rho]
          ring_nf
          exact le_rfl)
        (fun f hf x =>
          HasUniformC2Bound.firstDerivative hbound (hF_family hf) x)
        (by
          intro p hp
          exact hp.2)
        (by
          intro p hp
          exact (hE₀_level p hp.1).1)
    · have hempty : rightStub = ∅ :=
        Set.not_nonempty_iff_eq_empty.mp hne
      rw [hempty, measure_empty]
      exact bot_le
  have hscale_log :=
    hscale_absorb delta hdelta hdelta_scale
  have hlog_delta_nonpos : Real.log delta ≤ 0 :=
    Real.log_nonpos hdelta.le hdelta_one
  have hlog_term : 1 ≤ Real.log (1 / delta) + 1 := by
    rw [one_div, Real.log_inv]
    linarith
  have hscale_loss :
      Real.rpow (3 * K) (epsilon / 4) ≤
        Real.rpow delta (-(epsilon / 4)) := by
    have hfirst :
        scaleConstant ≤
          scaleConstant * (Real.log (1 / delta) + 1) := by
      nlinarith [mul_le_mul_of_nonneg_left hlog_term
        hscaleConstant_pos.le]
    exact hfirst.trans hscale_log
  have hpiece_volume : ∀ i, volume (pieces i) ≤ B := by
    intro i
    have hI_data := hintervals i
    have hI_len : 0 < (intervals.interval i).length :=
      lt_of_lt_of_le (mul_pos (by norm_num) hrho_pos) hI_data.1
    rcases hFinite hQuadratic K D C_KT lambda M
        hK hD hC_KT hlambda hM family hfamily hbound
        (intervals.interval i) hI_len hI_data.2
        delta hdelta hI_data.1 F hF_family hF_separated hF_KT with
      ⟨transport, htransport, htransport_bound, _hquadratic⟩
    dsimp [CenteredTaylorFiniteGraphTransportData] at htransport
    rcases htransport with
      ⟨_hinj, htransport_family, htransport_sub, _hcard_eq,
        htransport_sep, htransport_KT, _hjet, _hmetric, _hgraph,
        htransport_mult⟩
    let transportedF := F.transportImage transport
    let transportedFamily := transport '' family
    let delta' : ℝ := delta / (3 * K)
    let lambda' : ℝ := 3 * K * lambda
    let controlI := centeredTaylorControlInterval K hK
    let imagePiece : Set (ℝ × ℝ) :=
      centeredHorizontalPoint (intervals.interval i) '' pieces i
    have hdelta'_pos : 0 < delta' := by
      dsimp only [delta']
      positivity
    have hdelta'_le_delta : delta' ≤ delta := by
      dsimp only [delta']
      exact div_le_self hdelta.le (by nlinarith : 1 ≤ 3 * K)
    have hdelta'_short : delta' ≤ delta_short :=
      hdelta'_le_delta.trans hdelta_short
    have hcontrol : controlI.IsControlled (12 * K) := by
      exact centeredTaylorControlInterval_isControlled K hK
    have hpiece_meas : MeasurableSet (pieces i) := by
      have hcenter_meas :
          MeasurableSet
            ((intervals.interval i).realCenteredCarrier (1 / 16)) := by
        unfold ParameterInterval.realCenteredCarrier
        exact measurableSet_Icc.inter
          ((continuous_abs.comp
            (continuous_id.sub continuous_const)).measurable
              measurableSet_Iic)
      exact hE₀.inter (hcenter_meas.prod measurableSet_Icc)
    have himage_meas : MeasurableSet imagePiece := by
      exact measurableSet_centeredHorizontalPoint_image
        (intervals.interval i) hpiece_meas
    have himage_sub :
        imagePiece ⊆
          controlI.realCenteredCarrier (1 / 16) ×ˢ
            Set.Icc c (c + 1) := by
      exact centeredHorizontalPoint_image_subset_controlStrip
        hK hI_data.2 (by intro p hp; exact hp.2)
    have hscale_eq : lambda' * delta' = lambda * delta := by
      dsimp only [lambda', delta']
      field_simp [hK_pos.ne']
    have himage_level :
        ∀ p ∈ imagePiece,
          (mu : ℝ) ≤ multiplicity transportedF (lambda' * delta') p ∧
            multiplicity transportedF (lambda' * delta') p < 2 * mu := by
      rintro p ⟨q, hq, rfl⟩
      have hq_center :
          q.1 ∈ (intervals.interval i).realCenteredCarrier (1 / 16) :=
        hq.2.1
      have hmult_eq :=
        htransport_mult q hq_center
      have hlevel := hE₀_level q hq.1
      simpa [transportedF, hscale_eq] using
        And.imp (fun h => hmult_eq ▸ h) (fun h => hmult_eq ▸ h) hlevel
    have hshort_piece :=
      hshort delta' hdelta'_pos hdelta'_short
        transportedFamily htransport_family htransport_bound
        controlI hcontrol transportedF htransport_sub
        htransport_sep htransport_KT c mu hmu imagePiece
        himage_meas himage_sub himage_level
    have hdelta_rpow :
        Real.rpow delta' (-(epsilon / 4)) ≤
          Real.rpow delta (-(epsilon / 2)) := by
      exact centeredTaylor_transported_delta_rpow_le
        hK hdelta hepsilon hscale_loss
    have hreal_bound :
        Real.rpow delta' (-(epsilon / 4)) *
            Real.rpow (mu : ℝ) (-3 / 2 : ℝ) ≤
          Real.rpow delta (-(epsilon / 2)) *
            Real.rpow (mu : ℝ) (-3 / 2 : ℝ) := by
      exact mul_le_mul_of_nonneg_right hdelta_rpow
        (Real.rpow_nonneg (by positivity) _)
    calc
      volume (pieces i) = volume imagePiece := by
        exact
          (volume_centeredHorizontalPoint_image
            (intervals.interval i) hpiece_meas).symm
      _ ≤ ENNReal.ofReal
          (Real.rpow delta' (-(epsilon / 4)) *
            Real.rpow (mu : ℝ) (-3 / 2 : ℝ)) := hshort_piece
      _ ≤ B := by
        exact ENNReal.ofReal_le_ofReal hreal_bound
  have htotal :=
    volume_le_card_add_two_mul_of_cover hcover_E
      hleft_volume hright_volume hpiece_volume
  have hcard_log :=
    hcard_absorb delta hdelta hdelta_card
  have hcard_loss :
      (intervals.card + 2 : ℕ) ≤
        Real.rpow delta (-(epsilon / 2)) := by
    exact centeredTaylor_cover_card_add_two_le
      hC_cover_pos hlambda hdelta hdelta_one hrho_one hepsilon
      hcard hcard_log
  have hcard_loss_ennreal :
      ((intervals.card + 2 : ℕ) : ENNReal) ≤
        ENNReal.ofReal (Real.rpow delta (-(epsilon / 2))) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hcard_loss
  have htotal' :
      volume E₀ ≤ ((intervals.card + 2 : ℕ) : ENNReal) * B := by
    simpa using htotal
  have hhalf_nonneg :
      0 ≤ Real.rpow delta (-(epsilon / 2)) :=
    Real.rpow_nonneg hdelta.le _
  have hmu_nonneg :
      0 ≤ Real.rpow (mu : ℝ) (-3 / 2 : ℝ) :=
    Real.rpow_nonneg (by positivity) _
  have hpower :
      Real.rpow delta (-(epsilon / 2)) *
          Real.rpow delta (-(epsilon / 2)) =
        Real.rpow delta (-epsilon) := by
    have h :=
      Real.rpow_add hdelta (-(epsilon / 2)) (-(epsilon / 2))
    have hexp : -(epsilon / 2) + -(epsilon / 2) = -epsilon := by ring
    rw [hexp] at h
    exact h.symm
  calc
    volume E₀ ≤ ((intervals.card + 2 : ℕ) : ENNReal) * B := htotal'
    _ ≤ ENNReal.ofReal (Real.rpow delta (-(epsilon / 2))) * B := by
      exact mul_le_mul_right' hcard_loss_ennreal B
    _ = ENNReal.ofReal
        (Real.rpow delta (-(epsilon / 2)) *
          (Real.rpow delta (-(epsilon / 2)) *
            Real.rpow (mu : ℝ) (-3 / 2 : ℝ))) := by
      rw [show B = ENNReal.ofReal
        (Real.rpow delta (-(epsilon / 2)) *
          Real.rpow (mu : ℝ) (-3 / 2 : ℝ)) by rfl]
      rw [← ENNReal.ofReal_mul hhalf_nonneg]
    _ = ENNReal.ofReal
        (Real.rpow delta (-epsilon) *
          Real.rpow (mu : ℝ) (-3 / 2 : ℝ)) := by
      congr 1
      rw [← mul_assoc, hpower]

end Kakeya.Cinematic
