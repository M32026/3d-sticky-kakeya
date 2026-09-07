import MyLeanRepo.Kakeya.CV.MultilinearKakeya.VisibilityProductBound

/-!
# Polynomial visibility to lattice factorization

Final finite normalization in CV Section 4.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace Kakeya.CV

private lemma scaled_weight_cube_sum
    {Cube : Type*} [Fintype Cube]
    (M : Cube → NNReal) (scale : NNReal)
    (hM : (∑ q, M q ^ 3) = 1) :
    ∑ q, ((scale * M q : NNReal) : ℝ) ^ 3 = (scale : ℝ) ^ 3 := by
  have hM_real : ∑ q, (M q : ℝ) ^ 3 = 1 := by
    exact_mod_cast hM
  simp_rw [NNReal.coe_mul, mul_pow]
  rw [← Finset.mul_sum, hM_real, mul_one]

private lemma cube_rpow_one_third (scale : NNReal) :
    Real.rpow ((scale : ℝ) ^ 3) (1 / 3 : ℝ) = scale := by
  rw [show (1 / 3 : ℝ) = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
  exact Real.pow_rpow_inv_natCast scale.2 (by norm_num)

private lemma factor_normalization_algebra
    (Cvis Cdir D scale tv M vis s₁ s₂ s₃ : ℝ)
    (hCvis : 0 < Cvis) (hCdir : 0 < Cdir)
    (hD : 0 < D) (hscale : 0 < scale)
    (htv : 0 ≤ tv) (hM : 0 ≤ M)
    (hvis : Cvis * (scale * M) ≤ vis)
    (hproduct :
      tv * vis ^ 3 ≤ Cdir ^ 3 * (s₁ * s₂ * s₃)) :
    (((Cdir * D) / Cvis) ^ 3)⁻¹ * tv * M ^ 3 ≤
      (D⁻¹ * scale⁻¹ * s₁) *
        (D⁻¹ * scale⁻¹ * s₂) *
          (D⁻¹ * scale⁻¹ * s₃) := by
  have hvis_pow : (Cvis * (scale * M)) ^ 3 ≤ vis ^ 3 :=
    pow_le_pow_left₀ (by positivity) hvis 3
  have hcore :
      Cvis ^ 3 * scale ^ 3 * tv * M ^ 3 ≤
        Cdir ^ 3 * (s₁ * s₂ * s₃) := by
    calc
      Cvis ^ 3 * scale ^ 3 * tv * M ^ 3 =
          tv * (Cvis * (scale * M)) ^ 3 := by ring
      _ ≤ tv * vis ^ 3 :=
        mul_le_mul_of_nonneg_left hvis_pow htv
      _ ≤ Cdir ^ 3 * (s₁ * s₂ * s₃) := hproduct
  field_simp [hCvis.ne', hCdir.ne', hD.ne', hscale.ne']
  nlinarith [hcore]

private lemma mollifiedColumnConstant_toReal
    (offsets : Finset (Point 3)) (k : ℕ) :
    (8 * (offsets.card : ENNReal) *
      (12 * planeConstant * ENNReal.ofReal Real.pi *
        (k : ENNReal))).toReal =
      (8 * (offsets.card : ENNReal) *
        (12 * planeConstant * ENNReal.ofReal Real.pi)).toReal *
        (k : ℝ) := by
  have heq :
      8 * (offsets.card : ENNReal) *
          (12 * planeConstant * ENNReal.ofReal Real.pi *
            (k : ENNReal)) =
        (8 * (offsets.card : ENNReal) *
          (12 * planeConstant * ENNReal.ofReal Real.pi)) *
            (k : ENNReal) := by ring
  rw [heq, ENNReal.toReal_mul]
  simp

private lemma incidenceFactor_sum_le
    {ι : Type*} [DecidableEq ι]
    (cubes : Finset ι) (p : ι → Prop) [DecidablePred p]
    (f : ι → ℝ) (N D scale : ℝ)
    (hf : ∀ q ∈ cubes, 0 ≤ f q)
    (hN : 0 ≤ N) (hD : 0 < D) (hscale : 0 < scale)
    (hN_def : N = D⁻¹ * scale⁻¹)
    (hsum : ∑ q ∈ cubes.filter p, (1 + f q) ≤ D * scale) :
    (∑ q : cubes,
      if p q.1 then Real.toNNReal (N * (1 + f q.1)) else 0) ≤ 1 := by
  rw [← NNReal.coe_le_coe]
  calc
    ((↑(∑ q : cubes,
        if p q.1 then Real.toNNReal (N * (1 + f q.1)) else 0) : NNReal) : ℝ) =
        ∑ q : cubes,
          if p q.1 then N * (1 + f q.1) else 0 := by
            push_cast
            apply Finset.sum_congr rfl
            intro q _
            by_cases hq : p q.1
            · simp only [hq, if_true]
              rw [Real.coe_toNNReal _]
              exact mul_nonneg hN (add_nonneg zero_le_one (hf q.1 q.2))
            · simp [hq]
    _ = ∑ q ∈ cubes,
          if p q then N * (1 + f q) else 0 := by
      rw [← cubes.sum_attach
        (fun q => if p q then N * (1 + f q) else 0),
        Finset.attach_eq_univ]
    _ = ∑ q ∈ cubes.filter p, N * (1 + f q) := by
      rw [Finset.sum_filter]
    _ = N * ∑ q ∈ cubes.filter p, (1 + f q) := by
      rw [Finset.mul_sum]
    _ ≤ N * (D * scale) :=
      mul_le_mul_of_nonneg_left hsum hN
    _ = 1 := by
      rw [hN_def]
      field_simp [hD.ne', hscale.ne']

/--
The completed polynomial visibility theorem and the mollified directional
estimates give the normalized finite lattice-cube factorization.
-/
theorem polynomial_visibility_to_lattice_factorization_closed :
    PolynomialVisibilityToLatticeFactorizationStatement := by
  classical
  intro hVisibility hSurface hBody _hCylinder hDirectional _hDegree
  rcases hVisibility with
    ⟨Cdeg, Cvis, hCdeg, hCvis, hVisibility⟩
  rcases exists_mollified_visibility_product_bound hBody hDirectional with
    ⟨Cdir, hCdir, hProduct⟩
  rcases exists_finite_unitTube_cover_threeTube with
    ⟨offsets, hoffsets⟩
  let B : ℝ :=
    (8 * (offsets.card : ENNReal) *
      (12 * planeConstant * ENNReal.ofReal Real.pi)).toReal
  let D : ℝ := 1 + B * Cdeg
  have hB : 0 ≤ B := ENNReal.toReal_nonneg
  have hD : 0 < D := by
    dsimp only [D]
    positivity
  let α : ℝ := (Cdir * D) / Cvis
  have hα : 0 < α := div_pos (mul_pos hCdir hD) hCvis
  let A : NNReal := (Real.toNNReal α) ^ 3
  have hA : 0 < A := by
    dsimp only [A]
    exact pow_pos (Real.toNNReal_pos.mpr hα) _
  refine ⟨A, hA, ?_⟩
  intro F₁ F₂ F₃ cubes M hM
  let scale : NNReal := (cubes.card + 1 : ℕ)
  have hscale : 0 < (scale : ℝ) := by
    dsimp only [scale]
    positivity
  let scaledM : cubes → NNReal := fun q => scale * M q
  rcases hVisibility cubes (fun q => latticeCubeCenter q.1) scaledM with
    ⟨k, P, ε, x, hε, _hx, hk, hvis⟩
  have hscaled_sum :
      ∑ q, ((scaledM q : NNReal) : ℝ) ^ 3 = (scale : ℝ) ^ 3 := by
    exact scaled_weight_cube_sum M scale hM
  have hk_bound : (k : ℝ) ≤ Cdeg * (scale : ℝ) := by
    calc
      (k : ℝ) ≤
          Cdeg *
            Real.rpow (∑ q, ((scaledM q : NNReal) : ℝ) ^ 3)
              (1 / 3 : ℝ) := hk
      _ = Cdeg * (scale : ℝ) := by
        rw [hscaled_sum, cube_rpow_one_third]
  let area₁ : UnitLatticeCube → Fin F₁.card → ℝ := fun q i =>
    concreteMollifiedDirectionalArea P ε x (F₁.direction i)
      (unitCube (latticeCubeCenter q))
  let area₂ : UnitLatticeCube → Fin F₂.card → ℝ := fun q j =>
    concreteMollifiedDirectionalArea P ε x (F₂.direction j)
      (unitCube (latticeCubeCenter q))
  let area₃ : UnitLatticeCube → Fin F₃.card → ℝ := fun q l =>
    concreteMollifiedDirectionalArea P ε x (F₃.direction l)
      (unitCube (latticeCubeCenter q))
  let N : ℝ := D⁻¹ * (scale : ℝ)⁻¹
  have hN : 0 ≤ N := by
    dsimp only [N]
    positivity
  let S₁ : cubes → Fin F₁.card → NNReal := fun q i =>
    if unitLineMeetsLatticeCube F₁ i q.1 then
      Real.toNNReal (N * (1 + area₁ q.1 i))
    else 0
  let S₂ : cubes → Fin F₂.card → NNReal := fun q j =>
    if unitLineMeetsLatticeCube F₂ j q.1 then
      Real.toNNReal (N * (1 + area₂ q.1 j))
    else 0
  let S₃ : cubes → Fin F₃.card → NNReal := fun q l =>
    if unitLineMeetsLatticeCube F₃ l q.1 then
      Real.toNNReal (N * (1 + area₃ q.1 l))
    else 0
  refine ⟨S₁, S₂, S₃, ?_, ?_, ?_, ?_⟩
  · intro q i j l
    by_cases hi : unitLineMeetsLatticeCube F₁ i q.1
    · by_cases hj : unitLineMeetsLatticeCube F₂ j q.1
      · by_cases hl : unitLineMeetsLatticeCube F₃ l q.1
        · have harea₁ : 0 ≤ area₁ q.1 i :=
            concreteMollifiedDirectionalArea_nonneg P ε x
              (F₁.direction i) (unitCube (latticeCubeCenter q.1))
          have harea₂ : 0 ≤ area₂ q.1 j :=
            concreteMollifiedDirectionalArea_nonneg P ε x
              (F₂.direction j) (unitCube (latticeCubeCenter q.1))
          have harea₃ : 0 ≤ area₃ q.1 l :=
            concreteMollifiedDirectionalArea_nonneg P ε x
              (F₃.direction l) (unitCube (latticeCubeCenter q.1))
          have hvis_q :
              Cvis * ((scale : ℝ) * (M q : ℝ)) ≤
                concreteMollifiedVisibility P ε x
                  (unitCube (latticeCubeCenter q.1)) := by
            simpa [scaledM, NNReal.coe_mul] using hvis q
          have hprod :=
            hProduct P (unitCube (latticeCubeCenter q.1))
              (latticeCubeCenter q.1) ε x
              ![F₁.direction i, F₂.direction j, F₃.direction l]
              (unitCube_measurableSet (latticeCubeCenter q.1))
              (unitCube_subset_closedBall (latticeCubeCenter q.1))
              hε (by
                intro m
                fin_cases m
                · exact F₁.direction_unit i
                · exact F₂.direction_unit j
                · exact F₃.direction_unit l)
          have hprod' :
              tripleVolume
                    ![F₁.direction i, F₂.direction j, F₃.direction l] *
                  concreteMollifiedVisibility P ε x
                    (unitCube (latticeCubeCenter q.1)) ^ 3 ≤
                Cdir ^ 3 *
                  ((1 + area₁ q.1 i) * (1 + area₂ q.1 j) *
                    (1 + area₃ q.1 l)) := by
            simpa [area₁, area₂, area₃, Fin.prod_univ_succ, mul_assoc] using hprod
          have hreal :
              (α ^ 3)⁻¹ *
                    tripleVolume
                      ![F₁.direction i, F₂.direction j, F₃.direction l] *
                    (M q : ℝ) ^ 3 ≤
                (N * (1 + area₁ q.1 i)) *
                  (N * (1 + area₂ q.1 j)) *
                    (N * (1 + area₃ q.1 l)) := by
            simpa [α, N, area₁, area₂, area₃, mul_assoc] using
              factor_normalization_algebra Cvis Cdir D (scale : ℝ)
                (tripleVolume
                  ![F₁.direction i, F₂.direction j, F₃.direction l])
                (M q : ℝ)
                (concreteMollifiedVisibility P ε x
                  (unitCube (latticeCubeCenter q.1)))
                (1 + area₁ q.1 i) (1 + area₂ q.1 j)
                (1 + area₃ q.1 l)
                hCvis hCdir hD hscale (abs_nonneg _) (M q).2
                hvis_q hprod'
          rw [← NNReal.coe_le_coe]
          simp only [S₁, S₂, S₃, hi, hj, hl, if_true,
            A, unitScaleCubeWeight, and_self, tripleVolumeNNReal,
            NNReal.coe_mul, NNReal.coe_inv, NNReal.coe_pow]
          rw [Real.coe_toNNReal α hα.le]
          rw [Real.coe_toNNReal _
            (mul_nonneg hN (add_nonneg zero_le_one harea₁))]
          rw [Real.coe_toNNReal _
            (mul_nonneg hN (add_nonneg zero_le_one harea₂))]
          rw [Real.coe_toNNReal _
            (mul_nonneg hN (add_nonneg zero_le_one harea₃))]
          rw [Real.coe_toNNReal _
            (show 0 ≤ tripleVolume
              ![F₁.direction i, F₂.direction j, F₃.direction l] from
                abs_nonneg _)]
          exact hreal
        · simp [S₁, S₂, S₃, unitScaleCubeWeight, hl]
      · simp [S₁, S₂, S₃, unitScaleCubeWeight, hj]
    · simp [S₁, S₂, S₃, unitScaleCubeWeight, hi]
  · intro i
    let active := cubes.filter fun q =>
      unitLineMeetsLatticeCube F₁ i q
    have hcolumn :=
      concreteMollifiedDirectionalArea_column_le P hSurface offsets
        hoffsets ε x hε F₁ i active (by
          intro q hq
          exact (Finset.mem_filter.mp hq).2)
    have hcolumn' :
        ∑ q ∈ active, area₁ q i ≤ B * (k : ℝ) := by
      calc
        ∑ q ∈ active, area₁ q i ≤
            (8 * (offsets.card : ENNReal) *
              (12 * planeConstant * ENNReal.ofReal Real.pi *
                (k : ENNReal))).toReal := by
                  simpa [area₁] using hcolumn
        _ = B * (k : ℝ) := by
          rw [mollifiedColumnConstant_toReal]
    have hactive_card : (active.card : ℝ) ≤ (scale : ℝ) := by
      dsimp only [scale, active]
      exact_mod_cast
        (Nat.le_succ_of_le (Finset.card_filter_le cubes _))
    have hsum_raw :
        ∑ q ∈ active, (1 + area₁ q i) ≤ D * (scale : ℝ) := by
      calc
        ∑ q ∈ active, (1 + area₁ q i) =
            (active.card : ℝ) + ∑ q ∈ active, area₁ q i := by
              simp [Finset.sum_add_distrib]
        _ ≤ (scale : ℝ) + B * (k : ℝ) := add_le_add hactive_card hcolumn'
        _ ≤ (scale : ℝ) + B * (Cdeg * (scale : ℝ)) := by
          gcongr
        _ = D * (scale : ℝ) := by
          dsimp only [D]
          ring
    exact incidenceFactor_sum_le cubes
      (unitLineMeetsLatticeCube F₁ i) (fun q => area₁ q i)
      N D (scale : ℝ) (by
        intro q _
        exact concreteMollifiedDirectionalArea_nonneg P ε x
          (F₁.direction i) (unitCube (latticeCubeCenter q)))
      hN hD hscale (by rfl) (by simpa [active] using hsum_raw)
  · intro j
    let active := cubes.filter fun q =>
      unitLineMeetsLatticeCube F₂ j q
    have hcolumn :=
      concreteMollifiedDirectionalArea_column_le P hSurface offsets
        hoffsets ε x hε F₂ j active (by
          intro q hq
          exact (Finset.mem_filter.mp hq).2)
    have hcolumn' :
        ∑ q ∈ active, area₂ q j ≤ B * (k : ℝ) := by
      calc
        ∑ q ∈ active, area₂ q j ≤
            (8 * (offsets.card : ENNReal) *
              (12 * planeConstant * ENNReal.ofReal Real.pi *
                (k : ENNReal))).toReal := by
                  simpa [area₂] using hcolumn
        _ = B * (k : ℝ) := by
          rw [mollifiedColumnConstant_toReal]
    have hactive_card : (active.card : ℝ) ≤ (scale : ℝ) := by
      dsimp only [scale, active]
      exact_mod_cast
        (Nat.le_succ_of_le (Finset.card_filter_le cubes _))
    have hsum_raw :
        ∑ q ∈ active, (1 + area₂ q j) ≤ D * (scale : ℝ) := by
      calc
        ∑ q ∈ active, (1 + area₂ q j) =
            (active.card : ℝ) + ∑ q ∈ active, area₂ q j := by
              simp [Finset.sum_add_distrib]
        _ ≤ (scale : ℝ) + B * (k : ℝ) := add_le_add hactive_card hcolumn'
        _ ≤ (scale : ℝ) + B * (Cdeg * (scale : ℝ)) := by
          gcongr
        _ = D * (scale : ℝ) := by
          dsimp only [D]
          ring
    exact incidenceFactor_sum_le cubes
      (unitLineMeetsLatticeCube F₂ j) (fun q => area₂ q j)
      N D (scale : ℝ) (by
        intro q _
        exact concreteMollifiedDirectionalArea_nonneg P ε x
          (F₂.direction j) (unitCube (latticeCubeCenter q)))
      hN hD hscale (by rfl) (by simpa [active] using hsum_raw)
  · intro l
    let active := cubes.filter fun q =>
      unitLineMeetsLatticeCube F₃ l q
    have hcolumn :=
      concreteMollifiedDirectionalArea_column_le P hSurface offsets
        hoffsets ε x hε F₃ l active (by
          intro q hq
          exact (Finset.mem_filter.mp hq).2)
    have hcolumn' :
        ∑ q ∈ active, area₃ q l ≤ B * (k : ℝ) := by
      calc
        ∑ q ∈ active, area₃ q l ≤
            (8 * (offsets.card : ENNReal) *
              (12 * planeConstant * ENNReal.ofReal Real.pi *
                (k : ENNReal))).toReal := by
                  simpa [area₃] using hcolumn
        _ = B * (k : ℝ) := by
          rw [mollifiedColumnConstant_toReal]
    have hactive_card : (active.card : ℝ) ≤ (scale : ℝ) := by
      dsimp only [scale, active]
      exact_mod_cast
        (Nat.le_succ_of_le (Finset.card_filter_le cubes _))
    have hsum_raw :
        ∑ q ∈ active, (1 + area₃ q l) ≤ D * (scale : ℝ) := by
      calc
        ∑ q ∈ active, (1 + area₃ q l) =
            (active.card : ℝ) + ∑ q ∈ active, area₃ q l := by
              simp [Finset.sum_add_distrib]
        _ ≤ (scale : ℝ) + B * (k : ℝ) := add_le_add hactive_card hcolumn'
        _ ≤ (scale : ℝ) + B * (Cdeg * (scale : ℝ)) := by
          gcongr
        _ = D * (scale : ℝ) := by
          dsimp only [D]
          ring
    exact incidenceFactor_sum_le cubes
      (unitLineMeetsLatticeCube F₃ l) (fun q => area₃ q l)
      N D (scale : ℝ) (by
        intro q _
        exact concreteMollifiedDirectionalArea_nonneg P ε x
          (F₃.direction l) (unitCube (latticeCubeCenter q)))
      hN hD hscale (by rfl) (by simpa [active] using hsum_raw)

end Kakeya.CV
