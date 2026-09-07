import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23PlanarProjectionFullnessStatements

/-!
# Planar projection fullness in WZ1 Lemma 23

For a planar slice in one `sqrt rho` square and one width-`rho` strip, either
the two projection directions have small determinant, or the global projection
fills a definite fraction of its determinant-controlled interval.
-/

namespace Kakeya.Assouad

open MeasureTheory

theorem wz1_lemma23_planar_projection_fullness_core :
    WZ1Lemma23PlanarProjectionFullnessCoreStatement := by
  intro rho eta hrho hrho_one heta h32 slice sliceCenter stripCenter normal slope
    hmeas hnorm hvert hsquare hstrip
  dsimp only
  intro hslice
  let tilt : ℝ := normal 1 - slope * normal 0
  by_cases htilt_le : |tilt| ≤ Real.sqrt rho
  · exact Or.inl htilt_le
  · have htilt_gt : |tilt| > Real.sqrt rho := by
      exact lt_of_not_ge htilt_le
    have hsqrt_pos : 0 < Real.sqrt rho :=
      Real.sqrt_pos.mpr hrho
    have htilt_pos : 0 < |tilt| := hsqrt_pos.trans htilt_gt
    have htilt_ne_zero : tilt ≠ 0 := by
      simpa [abs_pos] using htilt_pos
    let M : Matrix (Fin 2) (Fin 2) ℝ :=
      !![1, slope; normal 0, normal 1]
    let L : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) :=
      Matrix.toLin' M
    have hL0 :
        ∀ p : Fin 2 → ℝ,
          L p 0 = p 0 + slope * p 1 := by
      intro p
      have h3 : L p = M.mulVec p := by rfl
      rw [h3]
      have h4 :
          (M.mulVec p) 0 =
            M 0 0 * p 0 + M 0 1 * p 1 := by
        have h5 :
            (M.mulVec p) 0 =
              ∑ j : Fin 2, M 0 j * p j := by
          rfl
        rw [h5, Fin.sum_univ_two]
      rw [h4]
      have h6 : M 0 0 = 1 := by simp [M]
      have h7 : M 0 1 = slope := by simp [M]
      rw [h6, h7]
      ring
    have hL1 :
        ∀ p : Fin 2 → ℝ,
          L p 1 = normal 0 * p 0 + normal 1 * p 1 := by
      intro p
      have h3 : L p = M.mulVec p := by rfl
      rw [h3]
      have h4 :
          (M.mulVec p) 1 =
            M 1 0 * p 0 + M 1 1 * p 1 := by
        have h5 :
            (M.mulVec p) 1 =
              ∑ j : Fin 2, M 1 j * p j := by
          rfl
        rw [h5, Fin.sum_univ_two]
      rw [h4]
      have h6 : M 1 0 = normal 0 := by simp [M]
      have h7 : M 1 1 = normal 1 := by simp [M]
      rw [h6, h7] <;> ring
    have hdet : LinearMap.det L = tilt := by
      have h :
          LinearMap.det L = Matrix.det M :=
        LinearMap.det_toLin' M
      rw [h]
      simp [M, Matrix.det_fin_two]
      ring
    let globalProjection : Set ℝ :=
      (fun point : Fin 2 → ℝ =>
        point 0 + slope * point 1) '' slice
    let s : Fin 2 → Set ℝ :=
      ![globalProjection,
        Set.Icc (-rho + stripCenter) (rho + stripCenter)]
    let S : Set (Fin 2 → ℝ) := Set.univ.pi s
    have hcontain : L '' slice ⊆ S := by
      intro y hy
      rcases hy with ⟨point, hpoint, rfl⟩
      have h1 : L point 0 ∈ s 0 := by
        rw [hL0]
        exact ⟨point, hpoint, rfl⟩
      let localVal : ℝ :=
        normal 0 * point 0 + normal 1 * point 1 -
          stripCenter
      have hstrip' : |localVal| ≤ rho :=
        hstrip point hpoint
      have h_eq : L point 1 - stripCenter = localVal := by
        dsimp only [localVal]
        rw [hL1]
      have h2 : L point 1 ∈ s 1 := by
        have h3 : -rho ≤ L point 1 - stripCenter := by
          rw [h_eq]
          exact (abs_le.mp hstrip').1
        have h4 : L point 1 - stripCenter ≤ rho := by
          rw [h_eq]
          exact (abs_le.mp hstrip').2
        have h5 : -rho + stripCenter ≤ L point 1 := by
          linarith
        have h6 : L point 1 ≤ rho + stripCenter := by
          linarith
        exact ⟨h5, h6⟩
      intro i hi
      fin_cases i <;> assumption
    have hvol :
        volume (L '' slice) =
          ENNReal.ofReal |tilt| * volume slice := by
      have h :=
        MeasureTheory.Measure.addHaar_image_linearMap
          volume L slice
      rw [hdet] at h
      exact h
    have hprod :
        volume S = volume (s 0) * volume (s 1) := by
      have h :
          volume S = ∏ i : Fin 2, volume (s i) :=
        MeasureTheory.volume_pi_pi s
      rw [h, Fin.prod_univ_two]
    have hs1 :
        s 1 =
          Set.Icc (-rho + stripCenter)
            (rho + stripCenter) := by
      simp [s]
    have hIcc :
        volume (s 1) = ENNReal.ofReal (2 * rho) := by
      rw [hs1]
      have h :
          volume
              (Set.Icc (-rho + stripCenter)
                (rho + stripCenter)) =
            ENNReal.ofReal
              ((rho + stripCenter) -
                (-rho + stripCenter)) :=
        Real.volume_Icc
      rw [h]
      have h2 :
          (rho + stripCenter) -
              (-rho + stripCenter) =
            2 * rho := by
        ring
      rw [h2]
    rw [hIcc] at hprod
    have hmain :
        ENNReal.ofReal |tilt| * volume slice ≤
          volume globalProjection *
            ENNReal.ofReal (2 * rho) := by
      calc
        ENNReal.ofReal |tilt| * volume slice
            = volume (L '' slice) := hvol.symm
        _ ≤ volume S := measure_mono hcontain
        _ = volume (s 0) * ENNReal.ofReal (2 * rho) :=
          hprod
        _ =
            volume globalProjection *
              ENNReal.ofReal (2 * rho) := by
          congr 1 <;> simp [s]
    have hmain2 :
        ENNReal.ofReal |tilt| *
            Kakeya.realRpowENN rho (3 / 2 + 2 * eta) ≤
          volume globalProjection *
            ENNReal.ofReal (2 * rho) := by
      calc
        ENNReal.ofReal |tilt| *
              Kakeya.realRpowENN rho (3 / 2 + 2 * eta)
            ≤ ENNReal.ofReal |tilt| * volume slice := by
          gcongr
        _ ≤
            volume globalProjection *
              ENNReal.ofReal (2 * rho) :=
          hmain
    let projectionRadius : ℝ :=
      4 * rho + 4 * Real.sqrt rho * |tilt|
    have hrho_le :
        rho ≤ Real.sqrt rho * |tilt| := by
      have hsq :
          Real.sqrt rho ^ 2 = rho :=
        Real.sq_sqrt (by linarith)
      have h :
          rho = Real.sqrt rho * Real.sqrt rho := by
        nlinarith [Real.sqrt_nonneg rho]
      rw [h]
      gcongr
      linarith
    have hradius :
        projectionRadius ≤
          8 * Real.sqrt rho * |tilt| := by
      dsimp only [projectionRadius]
      linarith [hrho_le]
    have harith :
        Real.rpow rho (3 * eta) *
              (2 * projectionRadius) * (2 * rho) ≤
          |tilt| *
            Real.rpow rho (3 / 2 + 2 * eta) := by
      have hsqrt :
          Real.sqrt rho =
            Real.rpow rho (1 / 2 : ℝ) :=
        Real.sqrt_eq_rpow rho
      have hstep1 :
          Real.rpow rho (1 / 2 : ℝ) *
                Real.rpow rho (3 * eta) =
            Real.rpow rho ((1 / 2 : ℝ) + 3 * eta) :=
        (Real.rpow_add hrho (1 / 2 : ℝ) (3 * eta)).symm
      have hstep2 :
          Real.rpow rho ((1 / 2 : ℝ) + 3 * eta) *
                Real.rpow rho 1 =
            Real.rpow rho
              (((1 / 2 : ℝ) + 3 * eta) + 1) :=
        (Real.rpow_add hrho
          ((1 / 2 : ℝ) + 3 * eta) 1).symm
      have hrho1 : rho = Real.rpow rho 1 := by simp
      have hpow32 :
          Real.rpow rho (1 / 2 : ℝ) *
                Real.rpow rho (3 * eta) * rho =
            Real.rpow rho (3 / 2 + 3 * eta) := by
        calc
          Real.rpow rho (1 / 2 : ℝ) *
                Real.rpow rho (3 * eta) * rho
              =
                (Real.rpow rho (1 / 2 : ℝ) *
                    Real.rpow rho (3 * eta)) * rho := by
                  rw [mul_assoc]
          _ =
              Real.rpow rho ((1 / 2 : ℝ) + 3 * eta) *
                rho := by
                  rw [hstep1]
          _ =
              Real.rpow rho ((1 / 2 : ℝ) + 3 * eta) *
                Real.rpow rho 1 := by
                  congr 1 <;> exact hrho1
          _ =
              Real.rpow rho
                (((1 / 2 : ℝ) + 3 * eta) + 1) :=
            hstep2
          _ = Real.rpow rho (3 / 2 + 3 * eta) := by
            ring_nf
      have hsum :
          (3 / 2 + 2 * eta) + eta =
            3 / 2 + 3 * eta := by
        ring
      have h5 :
          Real.rpow rho (3 / 2 + 3 * eta) =
            Real.rpow rho (3 / 2 + 2 * eta) *
              Real.rpow rho eta := by
        have h :
            Real.rpow rho ((3 / 2 + 2 * eta) + eta) =
              Real.rpow rho (3 / 2 + 2 * eta) *
                Real.rpow rho eta :=
          Real.rpow_add hrho (3 / 2 + 2 * eta) eta
        rw [hsum] at h
        exact h
      have h4 : 32 * Real.rpow rho eta ≤ 1 := h32
      have h6 : 0 ≤ |tilt| := by positivity
      have h7 :
          0 ≤ Real.rpow rho (3 / 2 + 2 * eta) :=
        Real.rpow_nonneg hrho.le _
      calc
        Real.rpow rho (3 * eta) *
              (2 * projectionRadius) * (2 * rho)
            ≤
              Real.rpow rho (3 * eta) *
                (2 * (8 * Real.sqrt rho * |tilt|)) *
                  (2 * rho) := by
            have hpos :
                0 ≤ Real.rpow rho (3 * eta) :=
              Real.rpow_nonneg hrho.le _
            have hpr :
                2 * projectionRadius ≤
                  2 * (8 * Real.sqrt rho * |tilt|) := by
              gcongr
            gcongr <;> positivity
        _ =
            32 * |tilt| *
              Real.rpow rho (3 / 2 + 3 * eta) := by
          calc
            Real.rpow rho (3 * eta) *
                  (2 * (8 * Real.sqrt rho * |tilt|)) *
                    (2 * rho)
                =
                  32 * |tilt| *
                    (Real.sqrt rho *
                      Real.rpow rho (3 * eta) * rho) := by
                    ring
            _ =
                32 * |tilt| *
                  (Real.rpow rho (1 / 2 : ℝ) *
                    Real.rpow rho (3 * eta) * rho) := by
                  rw [hsqrt]
            _ =
                32 * |tilt| *
                  Real.rpow rho (3 / 2 + 3 * eta) := by
                  rw [hpow32]
        _ =
            |tilt| *
              Real.rpow rho (3 / 2 + 2 * eta) *
                (32 * Real.rpow rho eta) := by
          rw [h5]
          ring
        _ ≤
            |tilt| *
              Real.rpow rho (3 / 2 + 2 * eta) := by
          have hpos :
              0 ≤
                |tilt| *
                  Real.rpow rho (3 / 2 + 2 * eta) := by
            positivity
          nlinarith [h4]
    have h_pos1 :
        0 ≤ Real.rpow rho (3 * eta) :=
      Real.rpow_nonneg hrho.le _
    have h_pos2 : 0 ≤ 2 * projectionRadius := by
      positivity
    have h_pos4 : 0 ≤ |tilt| := by positivity
    have h_lhs :
        Kakeya.realRpowENN rho (3 * eta) *
              ENNReal.ofReal (2 * projectionRadius) *
                ENNReal.ofReal (2 * rho) =
          ENNReal.ofReal
            (Real.rpow rho (3 * eta) *
              (2 * projectionRadius) * (2 * rho)) := by
      simp only [Kakeya.realRpowENN]
      have h1 :
          ENNReal.ofReal (Real.rpow rho (3 * eta)) *
                ENNReal.ofReal (2 * projectionRadius) =
            ENNReal.ofReal
              (Real.rpow rho (3 * eta) *
                (2 * projectionRadius)) := by
        rw [ENNReal.ofReal_mul h_pos1]
      rw [h1,
        ENNReal.ofReal_mul (mul_nonneg h_pos1 h_pos2)]
    have h_rhs :
        ENNReal.ofReal |tilt| *
              Kakeya.realRpowENN rho (3 / 2 + 2 * eta) =
          ENNReal.ofReal
            (|tilt| *
              Real.rpow rho (3 / 2 + 2 * eta)) := by
      simp only [Kakeya.realRpowENN]
      rw [ENNReal.ofReal_mul h_pos4]
    have henn :
        Kakeya.realRpowENN rho (3 * eta) *
              ENNReal.ofReal (2 * projectionRadius) *
                ENNReal.ofReal (2 * rho) ≤
          ENNReal.ofReal |tilt| *
            Kakeya.realRpowENN rho (3 / 2 + 2 * eta) := by
      rw [h_lhs, h_rhs]
      exact ENNReal.ofReal_le_ofReal harith
    let density := Kakeya.realRpowENN rho (3 * eta)
    let radius := ENNReal.ofReal (2 * projectionRadius)
    let c := ENNReal.ofReal (2 * rho)
    have hcancel :
        density * radius * c ≤
          volume globalProjection * c :=
      henn.trans hmain2
    have hc_ne_top : c ≠ ⊤ := ENNReal.ofReal_ne_top
    have hfinal :
        density * radius ≤ volume globalProjection := by
      by_cases htop : volume globalProjection = ⊤
      · rw [htop]
        exact le_top
      · have hfin : volume globalProjection ≠ ⊤ := htop
        have htop_vol :
            volume globalProjection * c ≠ ⊤ :=
          ENNReal.mul_ne_top hfin hc_ne_top
        have htop_dr :
            density * radius ≠ ⊤ :=
          ENNReal.mul_ne_top
            ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
        have hreal :
            (density * radius * c).toReal ≤
              (volume globalProjection * c).toReal :=
          ENNReal.toReal_mono htop_vol hcancel
        have hcr : 0 < c.toReal := by
          have h :
              c.toReal = 2 * rho :=
            ENNReal.toReal_ofReal (by positivity)
          rw [h]
          positivity
        have hreal2 :
            (density * radius).toReal ≤
              (volume globalProjection).toReal := by
          have hreal3 :
              (density * radius * c).toReal =
                (density * radius).toReal * c.toReal := by
            rw [ENNReal.toReal_mul]
          have hreal4 :
              (volume globalProjection * c).toReal =
                (volume globalProjection).toReal *
                  c.toReal := by
            rw [ENNReal.toReal_mul]
          rw [hreal3, hreal4] at hreal
          have hcr' : c.toReal ≠ 0 := hcr.ne'
          calc
            (density * radius).toReal
                =
                  ((density * radius).toReal * c.toReal) /
                    c.toReal := by
                      field_simp [hcr']
            _ ≤
                ((volume globalProjection).toReal * c.toReal) /
                  c.toReal := by
                    gcongr
            _ = (volume globalProjection).toReal := by
              field_simp [hcr']
        exact
          (ENNReal.toReal_le_toReal htop_dr hfin).mp hreal2
    exact
      Or.inr
        ⟨Kakeya.realRpowENN rho (3 * eta),
          by simp, hfinal⟩

/-- Compatibility wrapper for the original slope-`1/10` interface. -/
theorem wz1_lemma23_planar_projection_fullness :
    WZ1Lemma23PlanarProjectionFullnessStatement := by
  intro rho eta hrho hrho_one heta hsmall
    slice sliceCenter stripCenter normal slope hsliceMeas
    hnormal hvertical _hslope hsquare hstrip
  exact
    wz1_lemma23_planar_projection_fullness_core
      rho eta hrho hrho_one heta hsmall
      slice sliceCenter stripCenter normal slope hsliceMeas
      hnormal hvertical hsquare hstrip

/-- Wrapper for the source-package slope bound `3`. -/
theorem wz1_lemma23_planar_projection_fullness_generalized :
    WZ1Lemma23PlanarProjectionFullnessStatementGeneralized := by
  intro rho eta hrho hrho_one heta hsmall
    slice sliceCenter stripCenter normal slope hsliceMeas
    hnormal hvertical _hslope hsquare hstrip
  exact
    wz1_lemma23_planar_projection_fullness_core
      rho eta hrho hrho_one heta hsmall
      slice sliceCenter stripCenter normal slope hsliceMeas
      hnormal hvertical hsquare hstrip

end Kakeya.Assouad
