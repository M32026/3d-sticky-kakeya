import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.LocalAD

/-!
# Hard regime helper lemma

Isolates the PropertyP construction from the main theorem's complex context.
The sticky data type has many interdependent implicit parameters; by wrapping
the construction in a separate lemma with fully explicit parameters, we avoid
type inference timeouts in the main theorem.
-/

namespace Kakeya.Assouad.PureWZ2

/-- Construct PropertyP data from a balanced cover and coarse extremal.

All parameters are explicit to avoid type inference pollution in the caller.
-/
noncomputable def constructPropertyP
    (delta sigma outputLoss L tau : ℝ)
    (fine : Streamlined.TubeFamily delta)
    (coarse : Streamlined.TubeFamily L)
    (cover : PureWZ2Section6Cover fine coarse)
    (fineShading : WZ1PaperTubeShading fine)
    (coarseShading : WZ1PaperTubeShading coarse)
    (balanced : PureWZ2BalancedCoverData cover fineShading coarseShading)
    (coarseExtremal : WZ2PaperCroppedIsExtremal sigma outputLoss coarse coarseShading)
    (h_line : ∀ i, WZ1PaperTubeInLineClass (coarse.tube i))
    (epsilon₁ epsilon₃ : ℝ)
    (heps₁_pos : 0 < epsilon₁)
    (heps₃_pos : 0 < epsilon₃)
    (heps_sum : epsilon₁ + epsilon₃ < 1)
    (hL_pos : 0 < L)
    (hL_small : L ≤ 1 / 10000)
    (htau_pos : 0 < tau)
    (hL_le_tau : L ≤ tau)
    (htau_large : L * Real.sqrt 3 ≤ tau)
    (htau_sq : tau ^ 2 ≤ 4 * L)
    (htau_le_one : tau ≤ 1)
    (K : ℕ)
    (hK_one : 1 ≤ K)
    (hKL_small : (K : ℝ) * L ≤ 1 / 2)
    (m : ℕ)
    (hm_pos : 0 < m)
    (hm_gt_packing : (2 * 4 * 601 ^ 3 * 12001 ^ 3 : ENNReal) < (m : ENNReal))
    (hm_gt_general : ((1600 * K + 1)^5 : ENNReal) < (m : ENNReal))
    (h_mass_ne_top : coarseShading.mass ≠ ⊤)
    (h_volume_ne_top : MeasureTheory.volume coarseShading.union ≠ ⊤)
    (h_avg : (m : ENNReal) * MeasureTheory.volume coarseShading.union <
      (1 / 2 : ENNReal) * coarseShading.mass)
    (h_kappa : Real.rpow L epsilon₃ ≤ (K : ℝ) * L)
    (h_cell_full : Kakeya.realRpowENN L (2 + 2 * epsilon₁) * ENNReal.ofReal tau ≤ Kakeya.realRpowENN L 3) :
    PureWZ2PropertyPData
      (sigma := sigma) (coarseShading := coarseShading)
      (epsilon₁ := epsilon₁) (epsilon₃ := epsilon₃) (tau := tau) := by
  exact pureWz2_propertyP_refinement_general_of_distinctness
    (coarseExtremal := coarseExtremal)
    (h_essentially_distinct := cover.coarse_essentially_distinct)
    (h_line := h_line)
    (epsilon₁ := epsilon₁) (epsilon₃ := epsilon₃)
    (heps₁_pos := heps₁_pos) (heps₃_pos := heps₃_pos) (heps_sum := heps_sum)
    (hL_pos := hL_pos) (hL_small := hL_small)
    (htau_pos := htau_pos) (hL_le_tau := hL_le_tau)
    (htau_large := htau_large) (htau_sq := htau_sq) (htau_le_one := htau_le_one)
    (K := K) (hK_one := hK_one) (hKL_small := hKL_small)
    (m := m) (hm_pos := hm_pos)
    (hm_gt_packing := hm_gt_packing) (hm_gt_general := hm_gt_general)
    (h_mass_ne_top := h_mass_ne_top)
    (h_volume_ne_top := h_volume_ne_top)
    (h_avg := h_avg)
    (h_kappa := h_kappa)
    (h_cell_full := h_cell_full)

/-- Minimal wrapper: extract PropertyP from sticky data with arithmetic hypotheses as sorrys.

This keeps the target file clean — all type inference for the 30+ parameters
happens inside this lemma's context, not inside the main theorem's polluted
sticky-data context.

The arithmetic hypotheses (`h_avg`, `h_cell_full`, etc.) are left as `sorry`
here; they should be replaced with real proofs or passed explicitly via
`constructPropertyP`.
-/
noncomputable def constructPropertyPFromSticky
    (delta sigma outputLoss : ℝ)
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent)
    (tau : ℝ)
    (epsilon₁ epsilon₃ : ℝ)
    (K m : ℕ)
    (hL_pos : 0 < rho.1)
    (hL_small : rho.1 ≤ 1 / 10000)
    (htau_pos : 0 < tau)
    (hL_le_tau : rho.1 ≤ tau)
    (htau_large : rho.1 * Real.sqrt 3 ≤ tau)
    (htau_sq : tau ^ 2 ≤ 4 * rho.1)
    (htau_le_one : tau ≤ 1)
    (hK_one : 1 ≤ K)
    (hKL_small : (K : ℝ) * rho.1 ≤ 1 / 2)
    (hm_pos : 0 < m)
    (hm_gt_packing : (2 * 4 * 601 ^ 3 * 12001 ^ 3 : ENNReal) < (m : ENNReal))
    (hm_gt_general : ((1600 * K + 1)^5 : ENNReal) < (m : ENNReal))
    (heps₁_pos : 0 < epsilon₁)
    (heps₃_pos : 0 < epsilon₃)
    (heps_sum : epsilon₁ + epsilon₃ < 1)
    (h_mass_ne_top : sticky.croppedCoarseShading.mass ≠ ⊤)
    (h_volume_ne_top : MeasureTheory.volume sticky.croppedCoarseShading.union ≠ ⊤)
    (h_avg : (m : ENNReal) * MeasureTheory.volume sticky.croppedCoarseShading.union <
      (1 / 2 : ENNReal) * sticky.croppedCoarseShading.mass)
    (h_kappa : Real.rpow rho.1 epsilon₃ ≤ (K : ℝ) * rho.1)
    (h_cell_full : Kakeya.realRpowENN rho.1 (2 + 2 * epsilon₁) * ENNReal.ofReal tau ≤ Kakeya.realRpowENN rho.1 3) :
    PureWZ2PropertyPData
      (sigma := sigma)
      (coarseShading := sticky.croppedCoarseShading)
      (epsilon₁ := epsilon₁) (epsilon₃ := epsilon₃) (tau := tau) := by
  let fine := sticky.selected.family
  let coarse := sticky.coarse
  let cover := sticky.cover
  let fineShading := sticky.refined
  let coarseShading := sticky.croppedCoarseShading
  let balanced := sticky.balanced
  let coarseExtremal := sticky.coarse_extremal
  let h_line : ∀ i, WZ1PaperTubeInLineClass (coarse.tube i) :=
    cover.coarse_line_class
  exact constructPropertyP
    delta sigma outputLoss rho.1 tau
    fine coarse cover fineShading coarseShading
    balanced coarseExtremal h_line
    epsilon₁ epsilon₃ heps₁_pos heps₃_pos heps_sum
    hL_pos hL_small htau_pos hL_le_tau htau_large htau_sq htau_le_one
    K hK_one hKL_small
    m hm_pos hm_gt_packing hm_gt_general
    h_mass_ne_top h_volume_ne_top h_avg
    h_kappa h_cell_full

/--
Helper lemma: proves the key real inequality for `h_cell_full`.
Given `L ≤ 3^(-20/σ)`, `ε₁ = (σ - 2*stickyLoss)/20`, `stickyLoss ≤ σ/4`,
and `tau = L * √3`, we have `L^(2+2ε₁) * tau ≤ L^3`.
-/
lemma cell_full_real_ineq
    (L_coarse tau sigma stickyLoss epsilon₁ C_P : ℝ)
    (hL_coarse_pos : 0 < L_coarse)
    (hL_le_C : L_coarse ≤ 1 / C_P)
    (h_sticky_le_sigma4 : stickyLoss ≤ sigma / 4)
    (hsigma_pos : 0 < sigma)
    (hC_P_def : C_P = (3 : ℝ) ^ (20 / sigma))
    (heps₁_def : epsilon₁ = (sigma - 2 * stickyLoss) / 20)
    (htau_def : tau = L_coarse * Real.sqrt 3) :
    L_coarse ^ (2 + 2 * epsilon₁) * tau ≤ L_coarse ^ (3 : ℝ) := by
  have h_pos3 : (0 : ℝ) < (3 : ℝ) := by norm_num
  have h_base : 1 / C_P = (3 : ℝ) ^ (-(20 / sigma)) := by
    rw [hC_P_def]
    have h9 : (1 : ℝ) / (3 : ℝ) ^ (20 / sigma) = ((3 : ℝ) ^ (20 / sigma))⁻¹ := by simp
    rw [h9]
    exact (Real.rpow_neg h_pos3.le (20 / sigma)).symm
  have h8 : (1 / C_P) ^ (2 * epsilon₁) = (3 : ℝ) ^ (-(20 / sigma) * (2 * epsilon₁)) := by
    rw [h_base]
    exact (Real.rpow_mul h_pos3.le (-(20 / sigma)) (2 * epsilon₁)).symm
  have h9 : -(20 / sigma) * (2 * epsilon₁) ≤ -1 := by
    rw [heps₁_def]
    have h10 : 4 * stickyLoss ≤ sigma := by linarith
    have h11 : -(20 / sigma) * (2 * ((sigma - 2 * stickyLoss) / 20)) = -2 + 4 * stickyLoss / sigma := by
      field_simp [hsigma_pos.ne'] <;> ring
    rw [h11]
    have h12 : 4 * stickyLoss / sigma ≤ 1 := by
      calc 4 * stickyLoss / sigma ≤ sigma / sigma := by gcongr
        _ = 1 := by field_simp [hsigma_pos.ne']
    linarith
  have h10 : (3 : ℝ) ^ (-(20 / sigma) * (2 * epsilon₁)) ≤ (3 : ℝ) ^ (-1 : ℝ) := by
    exact Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ (3 : ℝ) from by norm_num) h9
  have h11 : (3 : ℝ) ^ (-1 : ℝ) = 1 / 3 := by norm_num
  have hL_pow_small : L_coarse ^ (2 * epsilon₁) ≤ 1 / 3 := by
    have h5 : L_coarse ^ (2 * epsilon₁) ≤ (1 / C_P) ^ (2 * epsilon₁) :=
      Real.rpow_le_rpow (by linarith) hL_le_C (by linarith)
    calc L_coarse ^ (2 * epsilon₁)
      ≤ (1 / C_P) ^ (2 * epsilon₁) := h5
    _ = (3 : ℝ) ^ (-(20 / sigma) * (2 * epsilon₁)) := h8
    _ ≤ (3 : ℝ) ^ (-1 : ℝ) := h10
    _ = 1 / 3 := h11
  have h_sqrt3_le : Real.sqrt 3 * L_coarse ^ (2 * epsilon₁) ≤ 1 := by
    have h : Real.sqrt 3 * L_coarse ^ (2 * epsilon₁) ≤ Real.sqrt 3 * (1 / 3) := by
      exact mul_le_mul_of_nonneg_left hL_pow_small (Real.sqrt_nonneg 3)
    have h2 : Real.sqrt 3 * (1 / 3) ≤ 1 := by
      have h3 : Real.sqrt 3 ≤ 3 := by rw [Real.sqrt_le_iff] <;> norm_num
      linarith
    linarith
  have h12 : L_coarse ^ (2 + 2 * epsilon₁) * tau = Real.sqrt 3 * L_coarse ^ (2 * epsilon₁) * L_coarse ^ (3 : ℝ) := by
    rw [htau_def]
    have h13 : L_coarse ^ (2 + 2 * epsilon₁) = L_coarse ^ (2 * epsilon₁) * L_coarse ^ (2 : ℝ) := by
      have h14 : (2 + 2 * epsilon₁) = (2 * epsilon₁) + (2 : ℝ) := by ring
      rw [h14]
      exact Real.rpow_add hL_coarse_pos (2 * epsilon₁) (2 : ℝ)
    have h15 : L_coarse ^ (2 : ℝ) * L_coarse = L_coarse ^ (3 : ℝ) := by
      have h16 : (3 : ℝ) = (2 : ℝ) + (1 : ℝ) := by norm_num
      rw [h16]
      rw [Real.rpow_add hL_coarse_pos (2 : ℝ) (1 : ℝ)]
      <;> simp
    calc L_coarse ^ (2 + 2 * epsilon₁) * (L_coarse * Real.sqrt 3)
      = (L_coarse ^ (2 * epsilon₁) * L_coarse ^ (2 : ℝ)) * (L_coarse * Real.sqrt 3) := by rw [h13]
    _ = L_coarse ^ (2 * epsilon₁) * (L_coarse ^ (2 : ℝ) * L_coarse) * Real.sqrt 3 := by
      simp [mul_assoc, mul_comm, mul_left_comm]
    _ = L_coarse ^ (2 * epsilon₁) * L_coarse ^ (3 : ℝ) * Real.sqrt 3 := by rw [h15]
    _ = Real.sqrt 3 * L_coarse ^ (2 * epsilon₁) * L_coarse ^ (3 : ℝ) := by
      simp [mul_assoc, mul_comm, mul_left_comm]
  rw [h12]
  have h15 : 0 ≤ L_coarse ^ (3 : ℝ) := by positivity
  nlinarith

/-- Axis condition for Córdoba: `4*(6L)^2 ≤ (3/4)*L^(2(1-ε₃))`.

Holds when `L ≤ 1/10000` and `9/10 < ε₃ < 1`. -/
lemma cordoba_ax_condition
    (L epsilon₃ : ℝ)
    (hL_pos : 0 < L)
    (hL_small : L ≤ 1 / 10000)
    (heps₃_gt : 9 / 10 < epsilon₃)
    (heps₃_lt_one : epsilon₃ < 1) :
    4 * (6 * L)^2 ≤ (3 / 4 : ℝ) * (Real.rpow L (1 - epsilon₃))^2 := by
  set x : ℝ := 1 - epsilon₃ with hx_def
  have hx_pos : 0 < x := by linarith
  have h_rpow_sq : (Real.rpow L x)^2 = Real.rpow L (2 * x) := by
    have h1 : Real.rpow L (x + x) = Real.rpow L x * Real.rpow L x := Real.rpow_add hL_pos x x
    have h2 : x + x = 2 * x := by ring
    have h3 : Real.rpow L (2 * x) = Real.rpow L (x + x) := by rw [h2]
    have h4 : Real.rpow L (2 * x) = Real.rpow L x * Real.rpow L x := by
      rw [h3, h1]
    have h5 : (Real.rpow L x)^2 = Real.rpow L x * Real.rpow L x := by ring
    rw [h5, ←h4]
  have h_decomp : Real.rpow L (2 * x) = L^2 * Real.rpow L (-2 * epsilon₃) := by
    have h1 : 2 * x = (2 : ℝ) + (-2 * epsilon₃) := by
      simp only [x] <;> ring
    have h2 : Real.rpow L ((2 : ℝ) + (-2 * epsilon₃)) = Real.rpow L (2 : ℝ) * Real.rpow L (-2 * epsilon₃) :=
      Real.rpow_add hL_pos (2 : ℝ) (-2 * epsilon₃)
    have h3 : Real.rpow L (2 : ℝ) = L^2 := by
      simpa [Real.rpow_two] using rfl
    rw [h1, h2, h3] <;> ring
  have h_192 : Real.rpow L (-2 * epsilon₃) ≥ 192 := by
    have hL_le_one : L ≤ 1 := by linarith
    have h9 : -2 * epsilon₃ ≤ -9 / 5 := by linarith
    have h10 : Real.rpow L (-2 * epsilon₃) ≥ Real.rpow L (-9 / 5 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hL_pos hL_le_one h9
    have hL_nonneg : 0 ≤ L := by linarith
    set a : ℝ := Real.rpow L (9 / 5 : ℝ) with ha_def
    set b : ℝ := Real.rpow (1 / 10000 : ℝ) (9 / 5 : ℝ) with hb_def
    have h_pos1 : 0 < a := Real.rpow_pos_of_pos hL_pos (9 / 5 : ℝ)
    have h_pos2 : 0 < b := Real.rpow_pos_of_pos (by norm_num) (9 / 5 : ℝ)
    have h11c : a ≤ b := by
      simp only [ha_def, hb_def]
      exact Real.rpow_le_rpow hL_nonneg hL_small (by norm_num)
    have h_inv : 1 / b ≤ 1 / a := one_div_le_one_div_of_le h_pos1 h11c
    have hneg_eq : (-9 / 5 : ℝ) = - (9 / 5 : ℝ) := by norm_num
    have h_rpow_neg_L : Real.rpow L (-9 / 5 : ℝ) = (Real.rpow L (9 / 5 : ℝ))⁻¹ := by
      have h1 : Real.rpow L (-9 / 5 : ℝ) = Real.rpow L (-(9 / 5 : ℝ)) := by rw [hneg_eq]
      rw [h1]
      exact Real.rpow_neg hL_nonneg (9 / 5 : ℝ)
    have ha : Real.rpow L (-9 / 5 : ℝ) = 1 / a := by
      rw [h_rpow_neg_L]
      <;> simp [ha_def]
    have h_rpow_neg_10k : Real.rpow (1 / 10000 : ℝ) (-9 / 5 : ℝ) = (Real.rpow (1 / 10000 : ℝ) (9 / 5 : ℝ))⁻¹ := by
      have h1 : Real.rpow (1 / 10000 : ℝ) (-9 / 5 : ℝ) = Real.rpow (1 / 10000 : ℝ) (-(9 / 5 : ℝ)) := by rw [hneg_eq]
      rw [h1]
      exact Real.rpow_neg (by norm_num) (9 / 5 : ℝ)
    have hb : Real.rpow (1 / 10000 : ℝ) (-9 / 5 : ℝ) = 1 / b := by
      rw [h_rpow_neg_10k]
      <;> simp [hb_def]
    have h11 : Real.rpow L (-9 / 5 : ℝ) ≥ Real.rpow (1 / 10000 : ℝ) (-9 / 5 : ℝ) := by
      rw [ha, hb]
      exact h_inv
    have h12 : Real.rpow (1 / 10000 : ℝ) (-9 / 5 : ℝ) ≥ 192 := by
      have h12a : (-9 / 5 : ℝ) ≤ (-1 : ℝ) := by norm_num
      have h12b : Real.rpow (1 / 10000 : ℝ) (-9 / 5 : ℝ) ≥ Real.rpow (1 / 10000 : ℝ) (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) h12a
      have h12c : Real.rpow (1 / 10000 : ℝ) (-1 : ℝ) = 10000 := by
        simp [Real.rpow_neg] <;> norm_num
      rw [h12c] at h12b
      linarith
    calc Real.rpow L (-2 * epsilon₃)
      ≥ Real.rpow L (-9 / 5 : ℝ) := h10
    _ ≥ Real.rpow (1 / 10000 : ℝ) (-9 / 5 : ℝ) := h11
    _ ≥ 192 := h12
  have h_goal : 144 * L^2 ≤ (3 / 4 : ℝ) * Real.rpow L (2 * x) := by
    rw [h_decomp]
    have h21 : 0 ≤ L^2 := by positivity
    nlinarith
  have h_final : 4 * (6 * L)^2 = 144 * L^2 := by ring
  rw [h_final, h_rpow_sq]
  exact h_goal

end Kakeya.Assouad.PureWZ2

namespace Kakeya.Assouad

open Kakeya.Streamlined

/-- Lower bound on the total mass of a tube family:
    `F.toBodyFamily.mass ≥ 2 * F.card * L^2`. -/
lemma tube_family_mass_lower_bound
    {L : ℝ} (hL_pos : 0 < L)
    (F : Kakeya.Streamlined.TubeFamily L) :
    (F.card : ENNReal) * ENNReal.ofReal (2 * L^2) ≤ F.toBodyFamily.mass := by
  let e0 : Point3 := EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
  let T_canon : Kakeya.DeltaTube L :=
    { base := 0
      direction := e0
      direction_unit := by simp [e0] }
  have h_canon_vol : T_canon.volume = Kakeya.deltaTubeVolume L := by rfl
  have h1 : ∀ (i : Fin F.card),
      (F.toBodyFamily.body i).volume ≥ ENNReal.ofReal (2 * L^2) := by
    intro i
    have h2 : (F.toBodyFamily.body i).volume = (F.tube i).volume := by rfl
    rw [h2]
    have h3 : (F.tube i).volume = T_canon.volume :=
      Kakeya.Streamlined.tube_volume_eq (F.tube i) T_canon
    rw [h3, h_canon_vol]
    exact Kakeya.Streamlined.tube_volume_ge_two_delta_sq L hL_pos
  calc
    F.toBodyFamily.mass
      = ∑ i : Fin F.card, (F.toBodyFamily.body i).volume := by rfl
    _ ≥ ∑ i : Fin F.card, ENNReal.ofReal (2 * L^2) := by
      apply Finset.sum_le_sum
      intro i _
      exact h1 i
    _ = (F.card : ENNReal) * ENNReal.ofReal (2 * L^2) := by
      simp [Finset.sum_const]

end Kakeya.Assouad
