import MyLeanRepo.Kakeya.Assouad.WZ1.CommonEndpointActiveFrostman
import MyLeanRepo.Kakeya.Assouad.ExponentArithmetic

/-!
# Paper power budget for the final common-endpoint reduction

For the input Katz--Tao loss `eta`, the paper uses the bad-edge radius
`delta^(5*eta)`, the grid radius `delta^(6*eta)`, and a hypergraph
refinement loss `delta^(20*eta)`.  The four inequalities below absorb the
only fixed constants needed by these steps.
-/

namespace Kakeya.Assouad

noncomputable section

open scoped ENNReal

/-- Finite ENNReal half-retention arithmetic used after deleting the two
bad edge families. -/
lemma ennreal_half_le_good_of_bad_bound
    {threshold total good bad : ENNReal}
    (hthresholdTop : threshold ≠ ⊤)
    (htotalTop : total ≠ ⊤) (hgoodTop : good ≠ ⊤) (hbadTop : bad ≠ ⊤)
    (hthreshold : threshold ≤ total)
    (htotal : total ≤ good + bad + bad)
    (hbad : 4 * bad ≤ threshold) :
    threshold / 2 ≤ good := by
  have hthresholdReal :=
    (ENNReal.toReal_le_toReal hthresholdTop htotalTop).2 hthreshold
  have htotalSumTop : good + bad + bad ≠ ⊤ := by
    exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.add_ne_top.mpr ⟨hgoodTop, hbadTop⟩, hbadTop⟩
  have htotalReal :=
    (ENNReal.toReal_le_toReal htotalTop htotalSumTop).2 htotal
  have hfourBadTop : 4 * bad ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) hbadTop
  have hbadReal :=
    (ENNReal.toReal_le_toReal hfourBadTop hthresholdTop).2 hbad
  have hfourBadReal : (4 * bad).toReal = 4 * bad.toReal := by
    rw [ENNReal.toReal_mul]
    norm_num
  rw [hfourBadReal] at hbadReal
  have hthresholdNonneg : 0 ≤ threshold.toReal := ENNReal.toReal_nonneg
  have hsumReal :
      (good + bad + bad).toReal =
        good.toReal + bad.toReal + bad.toReal := by
    rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hgoodTop, hbadTop⟩)
      hbadTop, ENNReal.toReal_add hgoodTop hbadTop]
  have hreal : threshold.toReal / 2 ≤ good.toReal := by
    rw [hsumReal] at htotalReal
    linarith
  have hhalfTop : threshold / 2 ≠ ⊤ :=
    ENNReal.div_ne_top hthresholdTop (by norm_num)
  apply (ENNReal.toReal_le_toReal hhalfTop hgoodTop).1
  simpa using hreal

/-- One-dimensional power at exponent one. -/
lemma common_endpoint_realRpowENN_one (x : ℝ) :
    Kakeya.realRpowENN x 1 = ENNReal.ofReal x := by
  exact congr_arg ENNReal.ofReal (Real.rpow_one x)

/-- `delta^(a)` squared is `delta^(2a)`. -/
lemma realRpowENN_sq
    {delta exponent : ℝ} (hdelta : 0 < delta) :
    Kakeya.realRpowENN delta exponent ^ 2 =
      Kakeya.realRpowENN delta (2 * exponent) := by
  rw [pow_two, ← realRpowENN_add hdelta]
  congr 2
  ring

/-- Exact bad-edge power appearing twice in the final reduction. -/
lemma common_endpoint_bad_power_identity
    {delta eta : ℝ} (hdelta : 0 < delta) :
    let C := Kakeya.realRpowENN delta (-eta)
    let threshold := Real.rpow delta (5 * eta)
    (C * Kakeya.realRpowENN (threshold / delta) 1) *
        (C * Kakeya.realRpowENN (1 / delta) 1) ^ 2 =
      Kakeya.realRpowENN delta (2 * eta - 3) := by
  dsimp only
  have hthreshold :
      Real.rpow delta (5 * eta) / delta =
        Real.rpow delta (5 * eta - 1) := by
    calc
      Real.rpow delta (5 * eta) / delta =
          Real.rpow delta (5 * eta) / Real.rpow delta 1 := by
            rw [show Real.rpow delta 1 = delta from Real.rpow_one delta]
      _ = Real.rpow delta (5 * eta - 1) :=
        (Real.rpow_sub hdelta (5 * eta) 1).symm
  have hinv : (1 / delta : ℝ) = Real.rpow delta (-1) := by
    rw [one_div]
    exact (Real.rpow_neg_one delta).symm
  have hthresholdENN :
      Kakeya.realRpowENN
          (Real.rpow delta (5 * eta) / delta) 1 =
        Kakeya.realRpowENN delta (5 * eta - 1) := by
    rw [common_endpoint_realRpowENN_one, hthreshold]
    rfl
  have hinvENN :
      Kakeya.realRpowENN (1 / delta) 1 =
        Kakeya.realRpowENN delta (-1) := by
    rw [common_endpoint_realRpowENN_one, hinv]
    rfl
  rw [hthresholdENN, hinvENN]
  have hfirst :
      Kakeya.realRpowENN delta (-eta) *
          Kakeya.realRpowENN delta (5 * eta - 1) =
        Kakeya.realRpowENN delta (4 * eta - 1) := by
    calc
      Kakeya.realRpowENN delta (-eta) *
            Kakeya.realRpowENN delta (5 * eta - 1) =
          Kakeya.realRpowENN delta (-eta + (5 * eta - 1)) :=
        (realRpowENN_add hdelta _ _).symm
      _ = Kakeya.realRpowENN delta (4 * eta - 1) := by
        apply congr_arg (Kakeya.realRpowENN delta)
        ring
  have hother :
      Kakeya.realRpowENN delta (-eta) *
          Kakeya.realRpowENN delta (-1) =
        Kakeya.realRpowENN delta (-eta - 1) := by
    calc
      Kakeya.realRpowENN delta (-eta) *
            Kakeya.realRpowENN delta (-1) =
          Kakeya.realRpowENN delta (-eta + (-1)) :=
        (realRpowENN_add hdelta _ _).symm
      _ = Kakeya.realRpowENN delta (-eta - 1) := by ring_nf
  calc
    (Kakeya.realRpowENN delta (-eta) *
        Kakeya.realRpowENN delta (5 * eta - 1)) *
          (Kakeya.realRpowENN delta (-eta) *
            Kakeya.realRpowENN delta (-1)) ^ 2 =
      Kakeya.realRpowENN delta (4 * eta - 1) *
        Kakeya.realRpowENN delta (2 * (-eta - 1)) := by
          rw [hfirst, hother, realRpowENN_sq hdelta]
    _ = Kakeya.realRpowENN delta
        ((4 * eta - 1) + 2 * (-eta - 1)) :=
      (realRpowENN_add hdelta _ _).symm
    _ = Kakeya.realRpowENN delta (2 * eta - 3) := by
      apply congr_arg (Kakeya.realRpowENN delta)
      ring

/-- Simultaneous small-scale inequalities for the paper's final reduction. -/
structure WZ1CommonEndpointParameterBudget (eta delta : ℝ) where
  delta_pos : 0 < delta
  delta_half : delta ≤ 1 / 2
  geometry_absorb :
    (100 : ENNReal) * Kakeya.realRpowENN delta (6 * eta) ≤
      Kakeya.realRpowENN delta (5 * eta)
  bad_edge_absorb :
    (4 : ENNReal) * Kakeya.realRpowENN delta (2 * eta - 3) ≤
      Kakeya.realRpowENN delta (eta - 3)
  grid_loss_absorb :
    (2000000 : ENNReal) *
        Kakeya.realRpowENN delta (38 * eta - 3) ≤
      Kakeya.realRpowENN delta (37 * eta - 3)
  density_loss_absorb :
    (64 : ENNReal) * Kakeya.realRpowENN delta (100 * eta) ≤
      Kakeya.realRpowENN delta (61 * eta)
  refinement_loss_absorb :
    (2 : ENNReal) * Kakeya.realRpowENN delta (20 * eta) ≤ 1
  frostman_loss_absorb :
    (8 : ENNReal) * Kakeya.realRpowENN delta (59 * eta) ≤ 1

namespace WZ1CommonEndpointParameterBudget

lemma geometry_absorb_real
    {eta delta : ℝ}
    (budget : WZ1CommonEndpointParameterBudget eta delta) :
    100 * Real.rpow delta (6 * eta) ≤
      Real.rpow delta (5 * eta) := by
  have hleftTop :
      (100 : ENNReal) * Kakeya.realRpowENN delta (6 * eta) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num)
      (by simp [Kakeya.realRpowENN])
  have hrightTop :
      Kakeya.realRpowENN delta (5 * eta) ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  have h := (ENNReal.toReal_le_toReal hleftTop hrightTop).2
    budget.geometry_absorb
  simpa [Kakeya.realRpowENN, ENNReal.toReal_ofReal,
    Real.rpow_nonneg budget.delta_pos.le] using h

lemma density_loss_absorb_real
    {eta delta : ℝ}
    (budget : WZ1CommonEndpointParameterBudget eta delta) :
    64 * Real.rpow delta (100 * eta) ≤
      Real.rpow delta (61 * eta) := by
  have hleftTop :
      (64 : ENNReal) * Kakeya.realRpowENN delta (100 * eta) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num)
      (by simp [Kakeya.realRpowENN])
  have hrightTop :
      Kakeya.realRpowENN delta (61 * eta) ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  have h := (ENNReal.toReal_le_toReal hleftTop hrightTop).2
    budget.density_loss_absorb
  simpa [Kakeya.realRpowENN, ENNReal.toReal_ofReal,
    Real.rpow_nonneg budget.delta_pos.le] using h

lemma frostman_loss_absorb_real
    {eta delta : ℝ}
    (budget : WZ1CommonEndpointParameterBudget eta delta) :
    8 * Real.rpow delta (59 * eta) ≤ 1 := by
  have hleftTop :
      (8 : ENNReal) * Kakeya.realRpowENN delta (59 * eta) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num)
      (by simp [Kakeya.realRpowENN])
  have h := (ENNReal.toReal_le_toReal hleftTop (by norm_num)).2
    budget.frostman_loss_absorb
  simpa [Kakeya.realRpowENN, ENNReal.toReal_ofReal,
    Real.rpow_nonneg budget.delta_pos.le] using h

private lemma common_endpoint_card_upper_real_eq
    {eta delta : ℝ} (hdelta : 0 < delta) :
    Real.rpow delta (-eta) * (1 / (delta / 2)) =
      2 * Real.rpow delta (-eta - 1) := by
  have hinv : 1 / (delta / 2) = 2 * Real.rpow delta (-1) := by
    calc
      1 / (delta / 2) = 2 * delta⁻¹ := by
        field_simp [hdelta.ne']
      _ = 2 * Real.rpow delta (-1) := by
        exact congr_arg (fun value : ℝ => 2 * value)
          (Real.rpow_neg_one delta).symm
  have hadd :
      Real.rpow delta (-eta) * Real.rpow delta (-1) =
        Real.rpow delta (-eta - 1) := by
    calc
      Real.rpow delta (-eta) * Real.rpow delta (-1) =
          Real.rpow delta (-eta + (-1)) :=
        (Real.rpow_add hdelta _ _).symm
      _ = Real.rpow delta (-eta - 1) := by ring_nf
  calc
    Real.rpow delta (-eta) * (1 / (delta / 2)) =
        Real.rpow delta (-eta) *
          (2 * Real.rpow delta (-1)) := by rw [hinv]
    _ = 2 * (Real.rpow delta (-eta) * Real.rpow delta (-1)) := by ring
    _ = 2 * Real.rpow delta (-eta - 1) := by rw [hadd]

/-- Real cubic inequality behind active-class Frostman normalization. -/
lemma frostman_cubic_real
    {eta delta : ℝ}
    (budget : WZ1CommonEndpointParameterBudget eta delta)
    (heta : 0 < eta) :
    (Real.rpow delta (-eta) * (1 / (delta / 2))) ^ 3 ≤
      Real.rpow (delta / 2) (-100 * eta) *
        Real.rpow delta (38 * eta - 3) := by
  have hdelta := budget.delta_pos
  have hdelta' : 0 < delta / 2 := by positivity
  have hbaseMono :
      Real.rpow delta (-100 * eta) ≤
        Real.rpow (delta / 2) (-100 * eta) :=
    Real.rpow_le_rpow_of_nonpos hdelta' (by linarith) (by linarith)
  have hupperCube :
      (Real.rpow delta (-eta) * (1 / (delta / 2))) ^ 3 =
        8 * Real.rpow delta (-3 * eta - 3) := by
    calc
      (Real.rpow delta (-eta) * (1 / (delta / 2))) ^ 3 =
          (2 * Real.rpow delta (-eta - 1)) ^ 3 := by
        rw [common_endpoint_card_upper_real_eq hdelta]
      _ = 8 * (Real.rpow delta (-eta - 1)) ^ 3 := by ring
      _ = 8 * Real.rpow delta ((3 : ℝ) * (-eta - 1)) := by
        congr 1
        simpa using rpow_nat_pow hdelta (-eta - 1) 3
      _ = 8 * Real.rpow delta (-3 * eta - 3) := by
        congr 1
        apply congr_arg (Real.rpow delta)
        ring
  have htarget :
      Real.rpow delta (-100 * eta) *
          Real.rpow delta (38 * eta - 3) =
        Real.rpow delta (-62 * eta - 3) := by
    calc
      Real.rpow delta (-100 * eta) *
          Real.rpow delta (38 * eta - 3) =
        Real.rpow delta ((-100 * eta) + (38 * eta - 3)) :=
          (Real.rpow_add hdelta _ _).symm
      _ = Real.rpow delta (-62 * eta - 3) := by
        apply congr_arg (Real.rpow delta)
        ring
  have hgap :
      Real.rpow delta (59 * eta) *
          Real.rpow delta (-62 * eta - 3) =
        Real.rpow delta (-3 * eta - 3) := by
    calc
      Real.rpow delta (59 * eta) *
          Real.rpow delta (-62 * eta - 3) =
        Real.rpow delta ((59 * eta) + (-62 * eta - 3)) :=
          (Real.rpow_add hdelta _ _).symm
      _ = Real.rpow delta (-3 * eta - 3) := by
        apply congr_arg (Real.rpow delta)
        ring
  have hcore :
      8 * Real.rpow delta (-3 * eta - 3) ≤
        Real.rpow delta (-62 * eta - 3) := by
    calc
      8 * Real.rpow delta (-3 * eta - 3) =
          8 * (Real.rpow delta (59 * eta) *
            Real.rpow delta (-62 * eta - 3)) := by rw [hgap]
      _ = (8 * Real.rpow delta (59 * eta)) *
            Real.rpow delta (-62 * eta - 3) := by ring
      _ ≤ 1 * Real.rpow delta (-62 * eta - 3) := by
        exact mul_le_mul_of_nonneg_right budget.frostman_loss_absorb_real
          (Real.rpow_nonneg hdelta.le _)
      _ = Real.rpow delta (-62 * eta - 3) := by ring
  calc
    (Real.rpow delta (-eta) * (1 / (delta / 2))) ^ 3 =
        8 * Real.rpow delta (-3 * eta - 3) := hupperCube
    _ ≤ Real.rpow delta (-62 * eta - 3) := hcore
    _ = Real.rpow delta (-100 * eta) *
          Real.rpow delta (38 * eta - 3) := htarget.symm
    _ ≤ Real.rpow (delta / 2) (-100 * eta) *
          Real.rpow delta (38 * eta - 3) := by
      exact mul_le_mul_of_nonneg_right hbaseMono
        (Real.rpow_nonneg hdelta.le _)

/-- Real power inequality behind the refined uniform-density bound. -/
lemma density_refinement_real
    {eta delta : ℝ}
    (budget : WZ1CommonEndpointParameterBudget eta delta)
    (heta : 0 < eta) :
    8 * Real.rpow (delta / 2) (100 * eta) *
        (Real.rpow delta (-eta) * (1 / (delta / 2))) ^ 3 ≤
      Real.rpow delta (20 * eta) *
        Real.rpow delta (38 * eta - 3) := by
  have hdelta := budget.delta_pos
  have hdelta' : 0 < delta / 2 := by positivity
  have hbaseMono :
      Real.rpow (delta / 2) (100 * eta) ≤
        Real.rpow delta (100 * eta) :=
    Real.rpow_le_rpow hdelta'.le (by linarith) (by positivity)
  have hupperCube :
      (Real.rpow delta (-eta) * (1 / (delta / 2))) ^ 3 =
        8 * Real.rpow delta (-3 * eta - 3) := by
    calc
      (Real.rpow delta (-eta) * (1 / (delta / 2))) ^ 3 =
          (2 * Real.rpow delta (-eta - 1)) ^ 3 := by
        rw [common_endpoint_card_upper_real_eq hdelta]
      _ = 8 * (Real.rpow delta (-eta - 1)) ^ 3 := by ring
      _ = 8 * Real.rpow delta ((3 : ℝ) * (-eta - 1)) := by
        congr 1
        simpa using rpow_nat_pow hdelta (-eta - 1) 3
      _ = 8 * Real.rpow delta (-3 * eta - 3) := by
        congr 1
        apply congr_arg (Real.rpow delta)
        ring
  have hleftPower :
      Real.rpow delta (100 * eta) *
          Real.rpow delta (-3 * eta - 3) =
        Real.rpow delta (97 * eta - 3) := by
    calc
      Real.rpow delta (100 * eta) *
          Real.rpow delta (-3 * eta - 3) =
        Real.rpow delta ((100 * eta) + (-3 * eta - 3)) :=
          (Real.rpow_add hdelta _ _).symm
      _ = Real.rpow delta (97 * eta - 3) := by
        apply congr_arg (Real.rpow delta)
        ring
  have hrightPower :
      Real.rpow delta (20 * eta) *
          Real.rpow delta (38 * eta - 3) =
        Real.rpow delta (58 * eta - 3) := by
    calc
      Real.rpow delta (20 * eta) *
          Real.rpow delta (38 * eta - 3) =
        Real.rpow delta ((20 * eta) + (38 * eta - 3)) :=
          (Real.rpow_add hdelta _ _).symm
      _ = Real.rpow delta (58 * eta - 3) := by
        apply congr_arg (Real.rpow delta)
        ring
  have hgap :
      Real.rpow delta (61 * eta) *
          Real.rpow delta (-3 * eta - 3) =
        Real.rpow delta (58 * eta - 3) := by
    calc
      Real.rpow delta (61 * eta) *
          Real.rpow delta (-3 * eta - 3) =
        Real.rpow delta ((61 * eta) + (-3 * eta - 3)) :=
          (Real.rpow_add hdelta _ _).symm
      _ = Real.rpow delta (58 * eta - 3) := by
        apply congr_arg (Real.rpow delta)
        ring
  have hcore :
      64 * Real.rpow delta (97 * eta - 3) ≤
        Real.rpow delta (58 * eta - 3) := by
    calc
      64 * Real.rpow delta (97 * eta - 3) =
          64 * (Real.rpow delta (100 * eta) *
            Real.rpow delta (-3 * eta - 3)) := by rw [hleftPower]
      _ = (64 * Real.rpow delta (100 * eta)) *
            Real.rpow delta (-3 * eta - 3) := by ring
      _ ≤ Real.rpow delta (61 * eta) *
            Real.rpow delta (-3 * eta - 3) := by
        exact mul_le_mul_of_nonneg_right budget.density_loss_absorb_real
          (Real.rpow_nonneg hdelta.le _)
      _ = Real.rpow delta (58 * eta - 3) := hgap
  calc
    8 * Real.rpow (delta / 2) (100 * eta) *
          (Real.rpow delta (-eta) * (1 / (delta / 2))) ^ 3 =
        8 * Real.rpow (delta / 2) (100 * eta) *
          (8 * Real.rpow delta (-3 * eta - 3)) := by rw [hupperCube]
    _
        ≤ 8 * Real.rpow delta (100 * eta) *
          (8 * Real.rpow delta (-3 * eta - 3)) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hbaseMono (by norm_num))
              (mul_nonneg (by norm_num) (Real.rpow_nonneg hdelta.le _))
    _ = 64 * Real.rpow delta (97 * eta - 3) := by
      rw [← hleftPower]
      ring
    _ ≤ Real.rpow delta (58 * eta - 3) := hcore
    _ = Real.rpow delta (20 * eta) *
          Real.rpow delta (38 * eta - 3) := hrightPower.symm

end WZ1CommonEndpointParameterBudget

/-- One source-scale cap realizes all four paper losses. -/
theorem exists_common_endpoint_parameter_budget
    (eta : ℝ) (heta : 0 < eta) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 / 2 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        Nonempty (WZ1CommonEndpointParameterBudget eta delta) := by
  rcases exists_delta₀_const_mul_rpow_le
      100 (by norm_num) (5 * eta) (6 * eta) (by linarith) with
    ⟨deltaGeometry, hdeltaGeometry, hdeltaGeometryOne, hgeometry⟩
  rcases exists_delta₀_const_mul_rpow_le
      4 (by norm_num) (eta - 3) (2 * eta - 3) (by linarith) with
    ⟨deltaBad, hdeltaBad, hdeltaBadOne, hbad⟩
  rcases exists_delta₀_const_mul_rpow_le
      2000000 (by norm_num) (37 * eta - 3) (38 * eta - 3)
      (by linarith) with
    ⟨deltaGrid, hdeltaGrid, hdeltaGridOne, hgrid⟩
  rcases exists_delta₀_const_mul_rpow_le
      64 (by norm_num) (61 * eta) (100 * eta) (by linarith) with
    ⟨deltaDensity, hdeltaDensity, hdeltaDensityOne, hdensity⟩
  rcases exists_delta₀_const_mul_rpow_le
      2 (by norm_num) 0 (20 * eta) (by linarith) with
    ⟨deltaRefinement, hdeltaRefinement, hdeltaRefinementOne, hrefinement⟩
  rcases exists_delta₀_const_mul_rpow_le
      8 (by norm_num) 0 (59 * eta) (by linarith) with
    ⟨deltaFrostman, hdeltaFrostman, hdeltaFrostmanOne, hfrostman⟩
  let delta₀ :=
    min (1 / 2 : ℝ)
      (min deltaGeometry
        (min deltaBad
          (min deltaGrid
            (min deltaDensity (min deltaRefinement deltaFrostman)))))
  have hdelta₀ : 0 < delta₀ := by
    dsimp only [delta₀]
    positivity
  have hdelta₀Half : delta₀ ≤ 1 / 2 := min_le_left _ _
  refine ⟨delta₀, hdelta₀, hdelta₀Half, ?_⟩
  intro delta hdelta hdeltaSmall
  have htail :
      delta ≤
        min deltaGeometry
          (min deltaBad
            (min deltaGrid
              (min deltaDensity (min deltaRefinement deltaFrostman)))) :=
    hdeltaSmall.trans (min_le_right _ _)
  have hgeometrySmall : delta ≤ deltaGeometry :=
    htail.trans (min_le_left _ _)
  have hbadSmall : delta ≤ deltaBad :=
    htail.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hgridSmall : delta ≤ deltaGrid :=
    htail.trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _)))
  have hdensitySmall : delta ≤ deltaDensity :=
    htail.trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans (min_le_left _ _))))
  have hfrostmanSmall : delta ≤ deltaFrostman :=
    htail.trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans
            ((min_le_right _ _).trans (min_le_right _ _)))))
  have hrefinementSmall : delta ≤ deltaRefinement :=
    htail.trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans
            ((min_le_right _ _).trans (min_le_left _ _)))))
  exact ⟨{
    delta_pos := hdelta
    delta_half := hdeltaSmall.trans hdelta₀Half
    geometry_absorb := by
      simpa using hgeometry delta hdelta hgeometrySmall
    bad_edge_absorb := by
      simpa using hbad delta hdelta hbadSmall
    grid_loss_absorb := by
      simpa using hgrid delta hdelta hgridSmall
    density_loss_absorb := by
      simpa using hdensity delta hdelta hdensitySmall
    refinement_loss_absorb := by
      have h := hrefinement delta hdelta hrefinementSmall
      simpa [Kakeya.realRpowENN] using h
    frostman_loss_absorb := by
      have h := hfrostman delta hdelta hfrostmanSmall
      simpa [Kakeya.realRpowENN] using h
  }⟩

end

end Kakeya.Assouad
