import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.Algebra

/-!
# Constant comparison for the robust bipartite reduction

This module packages the logarithmic lower bound and the polynomial
comparison constant used by the arbitrary-tangency reduction.
-/

namespace Kakeya.Cinematic

lemma normalized_rpow_log_ge_one {N : ℝ} (hN : 2 ≤ N) :
    1 ≤ Real.rpow N (3 / 2 : ℝ) * Real.log N := by
  have hN_le :
      N ≤ 2 * (Real.rpow N (3 / 2 : ℝ) * Real.log N) := by
    simpa [mul_assoc] using normalized_count_le_rpow_log hN
  linarith

lemma robust_comparison_bound
    {C_ct C_core tangency A : ℝ}
    (hC_ct : 1 ≤ C_ct)
    (hC_core : 100 ≤ C_core)
    (htangency : 1 ≤ tangency)
    (hA : 1 ≤ A) :
    let center := C_ct * Real.rpow tangency C_ct + 6
    let needed :=
      C_core * Real.rpow (2 * A * tangency) C_core
    let base :=
      100 + C_ct + 6 + C_core * Real.rpow 2 C_core
    let exponent := max C_ct C_core
    max 100 (max center needed) ≤
      base * Real.rpow tangency exponent *
        Real.rpow A exponent := by
  dsimp only
  have hC_ct_pos : 0 < C_ct := lt_of_lt_of_le (by norm_num) hC_ct
  have hC_core_pos : 0 < C_core :=
    lt_of_lt_of_le (by norm_num) hC_core
  have htangency_pos : 0 < tangency :=
    lt_of_lt_of_le (by norm_num) htangency
  have hA_pos : 0 < A := lt_of_lt_of_le (by norm_num) hA
  let exponent : ℝ := max C_ct C_core
  let base : ℝ :=
    100 + C_ct + 6 + C_core * Real.rpow 2 C_core
  let target : ℝ :=
    base * Real.rpow tangency exponent *
      Real.rpow A exponent
  have hexponent_nonneg : 0 ≤ exponent := by
    dsimp only [exponent]
    exact hC_ct_pos.le.trans (le_max_left _ _)
  have hbase_pos : 0 < base := by
    dsimp only [base]
    have hpower : 0 < Real.rpow 2 C_core :=
      Real.rpow_pos_of_pos (by norm_num) C_core
    have hterm :
        0 < C_core * Real.rpow 2 C_core :=
      mul_pos hC_core_pos hpower
    linarith
  have htangency_power :
      1 ≤ Real.rpow tangency exponent :=
    Real.one_le_rpow htangency hexponent_nonneg
  have hA_power :
      1 ≤ Real.rpow A exponent :=
    Real.one_le_rpow hA hexponent_nonneg
  have hbase_target : base ≤ target := by
    dsimp only [target]
    have hbase_power_nonneg :
        0 ≤ base * Real.rpow tangency exponent :=
      mul_nonneg hbase_pos.le
        (Real.rpow_nonneg htangency_pos.le exponent)
    exact
      (le_mul_of_one_le_right hbase_pos.le htangency_power).trans
        (le_mul_of_one_le_right hbase_power_nonneg hA_power)
  have h100_base : (100 : ℝ) ≤ base := by
    dsimp only [base]
    have hterm :
        0 ≤ C_core * Real.rpow 2 C_core :=
      mul_nonneg hC_core_pos.le
        (Real.rpow_nonneg (by norm_num) C_core)
    linarith
  have hcenter_base_power :
      C_ct * Real.rpow tangency C_ct + 6 ≤
        base * Real.rpow tangency exponent := by
    have hC_ct_exponent : C_ct ≤ exponent := by
      dsimp only [exponent]
      exact le_max_left _ _
    have hpower :
        Real.rpow tangency C_ct ≤
          Real.rpow tangency exponent :=
      Real.rpow_le_rpow_of_exponent_le
        htangency hC_ct_exponent
    have hsix :
        6 ≤ 6 * Real.rpow tangency exponent := by
      nlinarith
    have hcoefficient : C_ct + 6 ≤ base := by
      dsimp only [base]
      have hterm :
          0 ≤ C_core * Real.rpow 2 C_core :=
        mul_nonneg hC_core_pos.le
          (Real.rpow_nonneg (by norm_num) C_core)
      linarith
    calc
      C_ct * Real.rpow tangency C_ct + 6
          ≤ C_ct * Real.rpow tangency exponent +
              6 * Real.rpow tangency exponent := by
        gcongr
      _ = (C_ct + 6) * Real.rpow tangency exponent := by
        ring
      _ ≤ base * Real.rpow tangency exponent := by
        gcongr
  have hcenter_target :
      C_ct * Real.rpow tangency C_ct + 6 ≤ target := by
    have hbase_power_nonneg :
        0 ≤ base * Real.rpow tangency exponent :=
      mul_nonneg hbase_pos.le
        (Real.rpow_nonneg htangency_pos.le exponent)
    exact hcenter_base_power.trans
      (le_mul_of_one_le_right hbase_power_nonneg hA_power)
  have htwoA :
      Real.rpow (2 * A * tangency) C_core =
        Real.rpow 2 C_core * Real.rpow A C_core *
          Real.rpow tangency C_core := by
    calc
      Real.rpow (2 * A * tangency) C_core =
          Real.rpow (2 * A) C_core *
            Real.rpow tangency C_core :=
        Real.mul_rpow (by positivity) htangency_pos.le
      _ = (Real.rpow 2 C_core * Real.rpow A C_core) *
            Real.rpow tangency C_core := by
        congr 1
        exact Real.mul_rpow (by norm_num) hA_pos.le
  have hC_core_exponent : C_core ≤ exponent := by
    dsimp only [exponent]
    exact le_max_right _ _
  have htangency_mono :
      Real.rpow tangency C_core ≤
        Real.rpow tangency exponent :=
    Real.rpow_le_rpow_of_exponent_le
      htangency hC_core_exponent
  have hA_mono :
      Real.rpow A C_core ≤ Real.rpow A exponent :=
    Real.rpow_le_rpow_of_exponent_le hA hC_core_exponent
  have hcoefficient :
      C_core * Real.rpow 2 C_core ≤ base := by
    dsimp only [base]
    linarith
  have hneeded_target :
      C_core * Real.rpow (2 * A * tangency) C_core ≤
        target := by
    rw [htwoA]
    dsimp only [target]
    have hpowers :
        Real.rpow A C_core * Real.rpow tangency C_core ≤
          Real.rpow A exponent *
            Real.rpow tangency exponent :=
      mul_le_mul hA_mono htangency_mono
        (Real.rpow_nonneg htangency_pos.le C_core)
        (Real.rpow_nonneg hA_pos.le exponent)
    have hcoefficient_nonneg :
        0 ≤ C_core * Real.rpow 2 C_core :=
      mul_nonneg hC_core_pos.le
        (Real.rpow_nonneg (by norm_num) C_core)
    have htarget_powers_nonneg :
        0 ≤ Real.rpow A exponent *
          Real.rpow tangency exponent :=
      mul_nonneg
        (Real.rpow_nonneg hA_pos.le exponent)
        (Real.rpow_nonneg htangency_pos.le exponent)
    calc
      C_core *
          (Real.rpow 2 C_core * Real.rpow A C_core *
            Real.rpow tangency C_core) =
          (C_core * Real.rpow 2 C_core) *
            (Real.rpow A C_core *
              Real.rpow tangency C_core) := by ring
      _ ≤ (C_core * Real.rpow 2 C_core) *
            (Real.rpow A exponent *
              Real.rpow tangency exponent) := by
        exact mul_le_mul_of_nonneg_left hpowers hcoefficient_nonneg
      _ ≤ base *
            (Real.rpow A exponent *
              Real.rpow tangency exponent) := by
        exact mul_le_mul_of_nonneg_right
          hcoefficient htarget_powers_nonneg
      _ = base * Real.rpow tangency exponent *
            Real.rpow A exponent := by ring
  apply max_le
  · exact h100_base.trans hbase_target
  · apply max_le
    · exact hcenter_target
    · exact hneeded_target

lemma robust_refined_product_bound
    {C_poly B_base B_exp C_core comparison tangency A : ℝ}
    (hC_poly : 0 ≤ C_poly)
    (hB_base : 0 < B_base)
    (hC_core : 0 ≤ C_core)
    (hcomparison : 0 ≤ comparison)
    (htangency : 1 ≤ tangency)
    (hA : 1 ≤ A)
    (hcomparison_bound :
      comparison ≤
        B_base * Real.rpow tangency B_exp *
          Real.rpow A B_exp) :
    C_poly * Real.rpow comparison C_poly *
        C_core * Real.rpow (2 * A * tangency) C_core ≤
      (C_poly * Real.rpow B_base C_poly *
          C_core * Real.rpow 2 C_core) *
        Real.rpow tangency (B_exp * C_poly + C_core) *
        Real.rpow A (B_exp * C_poly + C_core) := by
  have htangency_pos : 0 < tangency :=
    lt_of_lt_of_le (by norm_num) htangency
  have hA_pos : 0 < A := lt_of_lt_of_le (by norm_num) hA
  have hcomparison_power :
      Real.rpow comparison C_poly ≤
        Real.rpow B_base C_poly *
          Real.rpow tangency (B_exp * C_poly) *
          Real.rpow A (B_exp * C_poly) := by
    have hmono :
        Real.rpow comparison C_poly ≤
          Real.rpow
            (B_base * Real.rpow tangency B_exp *
              Real.rpow A B_exp)
            C_poly :=
      Real.rpow_le_rpow hcomparison hcomparison_bound hC_poly
    calc
      Real.rpow comparison C_poly
          ≤ Real.rpow
              (B_base * Real.rpow tangency B_exp *
                Real.rpow A B_exp)
              C_poly := hmono
      _ = Real.rpow B_base C_poly *
            Real.rpow
              (Real.rpow tangency B_exp) C_poly *
            Real.rpow
              (Real.rpow A B_exp) C_poly := by
        have houter :
            Real.rpow
                ((B_base * Real.rpow tangency B_exp) *
                  Real.rpow A B_exp) C_poly =
              Real.rpow
                  (B_base * Real.rpow tangency B_exp) C_poly *
                Real.rpow (Real.rpow A B_exp) C_poly :=
          Real.mul_rpow
            (mul_nonneg hB_base.le
              (Real.rpow_nonneg htangency_pos.le B_exp))
            (Real.rpow_nonneg hA_pos.le B_exp)
        have hinner :
            Real.rpow
                (B_base * Real.rpow tangency B_exp) C_poly =
              Real.rpow B_base C_poly *
                Real.rpow (Real.rpow tangency B_exp) C_poly :=
          Real.mul_rpow hB_base.le
            (Real.rpow_nonneg htangency_pos.le B_exp)
        calc
          Real.rpow
              (B_base * Real.rpow tangency B_exp *
                Real.rpow A B_exp) C_poly =
              Real.rpow
                  (B_base * Real.rpow tangency B_exp) C_poly *
                Real.rpow (Real.rpow A B_exp) C_poly := houter
          _ = Real.rpow B_base C_poly *
                Real.rpow (Real.rpow tangency B_exp) C_poly *
                Real.rpow (Real.rpow A B_exp) C_poly := by
            rw [hinner]
      _ = Real.rpow B_base C_poly *
            Real.rpow tangency (B_exp * C_poly) *
            Real.rpow A (B_exp * C_poly) := by
        have htangency_flat :
            Real.rpow (Real.rpow tangency B_exp) C_poly =
              Real.rpow tangency (B_exp * C_poly) :=
          (Real.rpow_mul htangency_pos.le B_exp C_poly).symm
        have hA_flat :
            Real.rpow (Real.rpow A B_exp) C_poly =
              Real.rpow A (B_exp * C_poly) :=
          (Real.rpow_mul hA_pos.le B_exp C_poly).symm
        rw [htangency_flat, hA_flat]
  have hscaled_comparison :
      C_poly * Real.rpow comparison C_poly ≤
        C_poly *
          (Real.rpow B_base C_poly *
            Real.rpow tangency (B_exp * C_poly) *
            Real.rpow A (B_exp * C_poly)) :=
    mul_le_mul_of_nonneg_left hcomparison_power hC_poly
  have hcore_expand :
      C_core * Real.rpow (2 * A * tangency) C_core =
        C_core *
          (Real.rpow 2 C_core *
            Real.rpow A C_core *
            Real.rpow tangency C_core) := by
    have hexpand :
        Real.rpow (2 * A * tangency) C_core =
          Real.rpow 2 C_core *
            Real.rpow A C_core *
            Real.rpow tangency C_core := by
      calc
        Real.rpow (2 * A * tangency) C_core =
            Real.rpow (2 * A) C_core *
              Real.rpow tangency C_core :=
          Real.mul_rpow (by positivity) htangency_pos.le
        _ = (Real.rpow 2 C_core *
              Real.rpow A C_core) *
              Real.rpow tangency C_core := by
          have htwoA :
              Real.rpow (2 * A) C_core =
                Real.rpow 2 C_core *
                  Real.rpow A C_core :=
            Real.mul_rpow (by norm_num) hA_pos.le
          rw [htwoA]
    rw [hexpand]
  have hleft_nonneg :
      0 ≤ C_poly * Real.rpow comparison C_poly :=
    mul_nonneg hC_poly
      (Real.rpow_nonneg hcomparison C_poly)
  have hright_nonneg :
      0 ≤ C_core * Real.rpow (2 * A * tangency) C_core :=
    mul_nonneg hC_core
      (Real.rpow_nonneg (by positivity) C_core)
  have hproduct :
      (C_poly * Real.rpow comparison C_poly) *
          (C_core * Real.rpow (2 * A * tangency) C_core) ≤
        (C_poly *
          (Real.rpow B_base C_poly *
            Real.rpow tangency (B_exp * C_poly) *
            Real.rpow A (B_exp * C_poly))) *
          (C_core *
            (Real.rpow 2 C_core *
              Real.rpow A C_core *
              Real.rpow tangency C_core)) := by
    rw [hcore_expand]
    exact mul_le_mul_of_nonneg_right
      hscaled_comparison
      (mul_nonneg hC_core
        (mul_nonneg
          (mul_nonneg
            (Real.rpow_nonneg (by norm_num) C_core)
            (Real.rpow_nonneg hA_pos.le C_core))
          (Real.rpow_nonneg htangency_pos.le C_core)))
  have htangency_add :
      Real.rpow tangency (B_exp * C_poly) *
          Real.rpow tangency C_core =
        Real.rpow tangency (B_exp * C_poly + C_core) :=
    (Real.rpow_add htangency_pos
      (B_exp * C_poly) C_core).symm
  have hA_add :
      Real.rpow A (B_exp * C_poly) *
          Real.rpow A C_core =
        Real.rpow A (B_exp * C_poly + C_core) :=
    (Real.rpow_add hA_pos
      (B_exp * C_poly) C_core).symm
  calc
    C_poly * Real.rpow comparison C_poly *
        C_core * Real.rpow (2 * A * tangency) C_core =
      (C_poly * Real.rpow comparison C_poly) *
        (C_core * Real.rpow (2 * A * tangency) C_core) := by
      ring
    _ ≤
      (C_poly *
        (Real.rpow B_base C_poly *
          Real.rpow tangency (B_exp * C_poly) *
          Real.rpow A (B_exp * C_poly))) *
        (C_core *
          (Real.rpow 2 C_core *
            Real.rpow A C_core *
            Real.rpow tangency C_core)) := hproduct
    _ =
      (C_poly * Real.rpow B_base C_poly *
          C_core * Real.rpow 2 C_core) *
        Real.rpow tangency (B_exp * C_poly + C_core) *
        Real.rpow A (B_exp * C_poly + C_core) := by
      rw [← htangency_add, ← hA_add]
      ring

end Kakeya.Cinematic
