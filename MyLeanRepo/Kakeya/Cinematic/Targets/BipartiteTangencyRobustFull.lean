import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyInputs
import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.Algebra
import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.ScaleTransfer
import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.CenterDistance
import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.ComparisonBound
import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.CrudePacking

/-!
# Full robust bipartite tangency estimate

Generalizes the fixed-tangency reduction to an arbitrary input tangency
constant.  Starting from `BipartiteTangencyRobustCoreStatement`, derives the
full `t/A`-separated estimate with loss polynomial in both tangency and A.

**Proof structure:**

1. Extract constants from `hPolyRefine`, `hCore`, `uniform_doubling`, `hCommon`.
2. Pick `w₀ ∈ W` and establish a center-distance bound using `hCommon` at the
   arbitrary input tangency.
3. Define the core tangency after rescaling: `T' := 2 * A * tangency`.
4. Branch on the robust core scale condition `T'^C_core * delta ≤ c₂ * t / 2`:

   **Small-ratio branch** (condition holds):
   - If `comparison * delta > t`, fall back to `robust_crude_packing_bound`.
   - Otherwise, polynomial refinement → rescale by `2A` → robust core with
     tangency `T'`.

   **Large-ratio branch** (condition fails):
   - Use `robust_crude_packing_bound` with the ratio bound derived from the
     negated scale condition.

5. Absorb all polynomial factors into a single final constant `C`.
-/

namespace Kakeya.Cinematic

theorem bipartite_tangency_robust_full
    (hTangency : TangencyGeometryCompletionStatement)
    (hComparable : ComparableRectanglesStatement)
    (hPacking : RectanglePackingStatement)
    (hRefinement : RectangleRefinementStatement)
    (hPolyRefine : PolynomialRectangleRefinementStatement)
    (hCommon : CommonTangentRectangleRobustStatement)
    (hCore : BipartiteTangencyRobustCoreStatement) :
    BipartiteTangencyRobustFullStatement := by
  intro K hK
  rcases hPolyRefine K hK with ⟨C_poly, hC_poly_1, hPolyRefineMain⟩
  rcases hCore K hK with ⟨c₂, C_core, hc₂_pos, hC_core_100, hRobustCoreMain⟩

  -- Uniform doubling constant D depends only on K
  rcases uniform_doubling K hK with ⟨D, hD1, hDoublingFamily⟩
  rcases hCommon K D hK hD1 with ⟨C_ct, hC_ct1, hCT⟩

  let alpha : ℝ := Real.log D / Real.log 2
  let centerScale : ℝ := C_ct + 6
  let centerExponent : ℝ := C_ct

  let B_base : ℝ := 100 + C_ct + 6 + C_core * Real.rpow 2 C_core
  let B_exp : ℝ := max C_ct C_core

  -- Fallback 1 constants (comparison * delta > t)
  let ratioScale_fb1 : ℝ := B_base
  let ratioExponent_fb1 : ℝ := B_exp
  let D_fb1 : ℝ := D * Real.rpow (centerScale / 3) alpha *
      (42 * 103 ^ 2 * Real.rpow ratioScale_fb1 (5 / 2 : ℝ))
  let E_tang_fb1 : ℝ := centerExponent * alpha + ratioExponent_fb1 * (5 / 2 : ℝ)
  let E_A_fb1 : ℝ := ratioExponent_fb1 * (5 / 2 : ℝ)

  -- Fallback 2 constants (large ratio)
  let ratioScale_fb2 : ℝ := 2 * Real.rpow 2 C_core / c₂
  let ratioExponent_fb2 : ℝ := C_core
  let D_fb2 : ℝ := D * Real.rpow (centerScale / 3) alpha *
      (42 * 103 ^ 2 * Real.rpow ratioScale_fb2 (5 / 2 : ℝ))
  let E_tang_fb2 : ℝ := centerExponent * alpha + ratioExponent_fb2 * (5 / 2 : ℝ)
  let E_A_fb2 : ℝ := ratioExponent_fb2 * (5 / 2 : ℝ)

  -- Main case constants
  let D_small : ℝ := C_poly * Real.rpow B_base C_poly * C_core * Real.rpow 2 C_core
  let E_small : ℝ := B_exp * C_poly + C_core

  let C : ℝ := |D_fb1| + |E_tang_fb1| + |E_A_fb1| +
      |D_fb2| + |E_tang_fb2| + |E_A_fb2| +
      |D_small| + |E_small| + 1

  have hC_pos : 1 ≤ C := by
    dsimp only [C]
    have h : 0 ≤ |D_fb1| + |E_tang_fb1| + |E_A_fb1| +
        |D_fb2| + |E_tang_fb2| + |E_A_fb2| +
        |D_small| + |E_small| := by positivity
    linarith

  have hD_fb1_le : D_fb1 ≤ C := by
    dsimp only [C]; have h : D_fb1 ≤ |D_fb1| := le_abs_self D_fb1
    linarith [abs_nonneg E_tang_fb1, abs_nonneg E_A_fb1,
      abs_nonneg D_fb2, abs_nonneg E_tang_fb2, abs_nonneg E_A_fb2,
      abs_nonneg D_small, abs_nonneg E_small]
  have hE_tang_fb1_le : E_tang_fb1 ≤ C := by
    dsimp only [C]; have h : E_tang_fb1 ≤ |E_tang_fb1| := le_abs_self E_tang_fb1
    linarith [abs_nonneg D_fb1, abs_nonneg E_A_fb1,
      abs_nonneg D_fb2, abs_nonneg E_tang_fb2, abs_nonneg E_A_fb2,
      abs_nonneg D_small, abs_nonneg E_small]
  have hE_A_fb1_le : E_A_fb1 ≤ C := by
    dsimp only [C]; have h : E_A_fb1 ≤ |E_A_fb1| := le_abs_self E_A_fb1
    linarith [abs_nonneg D_fb1, abs_nonneg E_tang_fb1,
      abs_nonneg D_fb2, abs_nonneg E_tang_fb2, abs_nonneg E_A_fb2,
      abs_nonneg D_small, abs_nonneg E_small]
  have hD_fb2_le : D_fb2 ≤ C := by
    dsimp only [C]; have h : D_fb2 ≤ |D_fb2| := le_abs_self D_fb2
    linarith [abs_nonneg D_fb1, abs_nonneg E_tang_fb1, abs_nonneg E_A_fb1,
      abs_nonneg E_tang_fb2, abs_nonneg E_A_fb2,
      abs_nonneg D_small, abs_nonneg E_small]
  have hE_tang_fb2_le : E_tang_fb2 ≤ C := by
    dsimp only [C]; have h : E_tang_fb2 ≤ |E_tang_fb2| := le_abs_self E_tang_fb2
    linarith [abs_nonneg D_fb1, abs_nonneg E_tang_fb1, abs_nonneg E_A_fb1,
      abs_nonneg D_fb2, abs_nonneg E_A_fb2,
      abs_nonneg D_small, abs_nonneg E_small]
  have hE_A_fb2_le : E_A_fb2 ≤ C := by
    dsimp only [C]; have h : E_A_fb2 ≤ |E_A_fb2| := le_abs_self E_A_fb2
    linarith [abs_nonneg D_fb1, abs_nonneg E_tang_fb1, abs_nonneg E_A_fb1,
      abs_nonneg D_fb2, abs_nonneg E_tang_fb2,
      abs_nonneg D_small, abs_nonneg E_small]
  have hD_small_le : D_small ≤ C := by
    dsimp only [C]; have h : D_small ≤ |D_small| := le_abs_self D_small
    linarith [abs_nonneg D_fb1, abs_nonneg E_tang_fb1, abs_nonneg E_A_fb1,
      abs_nonneg D_fb2, abs_nonneg E_tang_fb2, abs_nonneg E_A_fb2,
      abs_nonneg E_small]
  have hE_small_le : E_small ≤ C := by
    dsimp only [C]; have h : E_small ≤ |E_small| := le_abs_self E_small
    linarith [abs_nonneg D_fb1, abs_nonneg E_tang_fb1, abs_nonneg E_A_fb1,
      abs_nonneg D_fb2, abs_nonneg E_tang_fb2, abs_nonneg E_A_fb2,
      abs_nonneg D_small]

  refine ⟨C, hC_pos, ?_⟩
  intro tangency htangency family hCurv I hI A delta t hA hdelta ht hdt ht1 hdat
    W B hW hB hdiam hsep
    R hRin hRquarter hR100 hRnonempty mu nu hmu hnu hcounts

  classical

  have hfamily : IsCinematicFamily family K D := hDoublingFamily family hCurv
  have htangency1 : 1 ≤ tangency := by linarith
  have htangency_nonneg : 0 ≤ tangency := zero_le_one.trans htangency1
  have hA_pos0 : 0 ≤ A := by linarith
  have ht_pos : 0 < t := lt_of_lt_of_le hdelta hdt
  have hC_core_pos : 0 < C_core := by linarith
  have hC_ct_pos : 0 < C_ct := by linarith [hC_ct1]

  let N := RectangleFamily.bipartiteNormalizedCount W B mu nu
  have hN2 : 2 ≤ N :=
    RectangleFamily.two_le_bipartiteNormalizedCount_of_tangentCounts
      hRnonempty hmu hnu hcounts
  set P : ℝ := Real.rpow N (3 / 2 : ℝ) * Real.log N with hP_def
  have hN_pos : 0 < N := by linarith
  have hP_nonneg : 0 ≤ P :=
    mul_nonneg (Real.rpow_nonneg hN_pos.le _) (Real.log_nonneg (by linarith))
  have hP_ge1 : 1 ≤ P := by
    simpa [hP_def] using normalized_rpow_log_ge_one hN2

  -- Pick w₀ ∈ W
  have hW_nonempty : W.carrier.Nonempty := by
    let i : Fin R.card := ⟨0, hRnonempty⟩
    have h_pos : 0 < RectangleFamily.tangentCount (R.rectangle i) W tangency :=
      lt_of_lt_of_le hmu ((hcounts i).1)
    have h_nonempty : (W.toFinset.filter fun w => (R.rectangle i).IsLambdaTangent w tangency).Nonempty :=
      Finset.card_pos.mp h_pos
    rcases h_nonempty with ⟨w, hw⟩
    have hwW : w ∈ W.carrier := W.finite.mem_toFinset.mp (Finset.mem_filter.mp hw).1
    exact ⟨w, hwW⟩
  rcases hW_nonempty with ⟨w₀, hw₀⟩

  -- Restricted diameter for W only
  have hdiam_W : ∀ ⦃f : C2Function⦄, f ∈ W.carrier → ∀ ⦃g : C2Function⦄, g ∈ W.carrier → dist f g ≤ 6 * t := by
    intro f hf g hg
    exact hdiam (Or.inl hf) (Or.inl hg)

  let C_center : ℝ := C_ct * Real.rpow tangency C_ct + 6

  -- Center distance bound using hCommon at arbitrary tangency
  have hcenter_bound : ∀ i, c2Distance (R.rectangle i).function w₀ ≤ C_center * t := by
    intro i
    have h_pos : 0 < RectangleFamily.tangentCount (R.rectangle i) W tangency :=
      lt_of_lt_of_le hmu ((hcounts i).1)
    have h_nonempty : (W.toFinset.filter fun w => (R.rectangle i).IsLambdaTangent w tangency).Nonempty :=
      Finset.card_pos.mp h_pos
    rcases h_nonempty with ⟨w_i, hwi⟩
    have hwiW : w_i ∈ W.carrier := W.finite.mem_toFinset.mp (Finset.mem_filter.mp hwi).1
    have hwi_tan : (R.rectangle i).IsLambdaTangent w_i tangency := (Finset.mem_filter.mp hwi).2
    by_cases h_eq : (R.rectangle i).function = w_i
    · have hdist_wi : dist w_i w₀ ≤ 6 * t := hdiam_W hwiW hw₀
      have h_c2dist : c2Distance w_i w₀ ≤ 6 * t := hdist_wi
      have hC6 : 6 ≤ C_center := by
        dsimp only [C_center]
        have h : 0 < C_ct * Real.rpow tangency C_ct :=
          mul_pos hC_ct_pos (Real.rpow_pos_of_pos (by linarith) _)
        linarith
      have h6 : 6 * t ≤ C_center * t := mul_le_mul_of_nonneg_right hC6 ht_pos.le
      rw [h_eq]
      exact h_c2dist.trans h6
    · have hRt_self : (R.rectangle i).IsLambdaTangent (R.rectangle i).function tangency := by
        intro p hp
        have h : |p.2 - (R.rectangle i).function p.1| ≤ delta := hp.2
        have h2 : delta ≤ tangency * delta := by
          have h3 : 1 ≤ tangency := htangency1
          calc
            delta = 1 * delta := by ring
            _ ≤ tangency * delta := by gcongr
        exact h.trans h2
      have hbound :
          (tangencyParameterOn I (R.rectangle i).function w_i + delta) *
            c2Distance (R.rectangle i).function w_i ≤
          C_ct * Real.rpow tangency C_ct * delta * t :=
        hCT tangency htangency1 family hfamily I hI delta t hdelta hdt ht1
          (R.rectangle i) (hRin i) (hRquarter i)
          (R.rectangle i).function (hRin i) w_i (hW hwiW) h_eq
          hRt_self hwi_tan
      have htp_nonneg : 0 ≤ tangencyParameterOn I (R.rectangle i).function w_i :=
        tangencyParameterOn_nonneg
      have hnonneg : 0 ≤ c2Distance (R.rectangle i).function w_i := dist_nonneg
      have h1 : c2Distance (R.rectangle i).function w_i ≤ C_ct * Real.rpow tangency C_ct * t := by
        have h2 : delta * c2Distance (R.rectangle i).function w_i ≤
            (tangencyParameterOn I (R.rectangle i).function w_i + delta) *
              c2Distance (R.rectangle i).function w_i := by
          have h3 : delta ≤ tangencyParameterOn I (R.rectangle i).function w_i + delta := by linarith [htp_nonneg]
          exact mul_le_mul_of_nonneg_right h3 hnonneg
        have h3 : delta * c2Distance (R.rectangle i).function w_i ≤
            C_ct * Real.rpow tangency C_ct * delta * t := h2.trans hbound
        calc
          c2Distance (R.rectangle i).function w_i
            = (delta * c2Distance (R.rectangle i).function w_i) / delta := by
              field_simp [hdelta.ne'] <;> ring
          _ ≤ (C_ct * Real.rpow tangency C_ct * delta * t) / delta := by gcongr
          _ = C_ct * Real.rpow tangency C_ct * t := by
              field_simp [hdelta.ne'] <;> ring
      have hdist_wi : dist w_i w₀ ≤ 6 * t := hdiam_W hwiW hw₀
      have h_c2dist : c2Distance w_i w₀ ≤ 6 * t := hdist_wi
      calc
        c2Distance (R.rectangle i).function w₀ ≤
            c2Distance (R.rectangle i).function w_i + c2Distance w_i w₀ :=
          dist_triangle _ _ _
        _ ≤ C_ct * Real.rpow tangency C_ct * t + 6 * t := by gcongr
        _ = C_center * t := by
          dsimp only [C_center] <;> ring

  -- Center bound in the form needed by robust_crude_packing_bound
  have hcenter_bound_poly : ∀ i,
      c2Distance w₀ (R.rectangle i).function ≤
        centerScale * Real.rpow tangency centerExponent * t := by
    intro i
    have hsymm : c2Distance w₀ (R.rectangle i).function = c2Distance (R.rectangle i).function w₀ :=
      dist_comm _ _
    rw [hsymm]
    have h : c2Distance (R.rectangle i).function w₀ ≤ C_center * t := hcenter_bound i
    have hCcenter_le : C_center ≤ centerScale * Real.rpow tangency centerExponent := by
      dsimp only [C_center, centerScale, centerExponent]
      have h1 : 6 ≤ 6 * Real.rpow tangency C_ct := by
        have h2 : 1 ≤ Real.rpow tangency C_ct := Real.one_le_rpow htangency1 (by linarith)
        linarith
      linarith
    have h3 : C_center * t ≤ (centerScale * Real.rpow tangency centerExponent) * t :=
      mul_le_mul_of_nonneg_right hCcenter_le ht_pos.le
    exact h.trans h3

  have hcenterScale3 : 3 ≤ centerScale := by
    dsimp only [centerScale]
    linarith [hC_ct1]
  have hcenterExponent_nonneg : 0 ≤ centerExponent := by
    dsimp only [centerExponent]
    linarith [hC_ct1]

  let T' : ℝ := 2 * A * tangency
  let comparison_needed : ℝ := C_core * Real.rpow T' C_core
  let comparison : ℝ := max 100 (max C_center comparison_needed)

  have hT'_pos : 0 < T' := by positivity
  have hT'_5 : 5 ≤ T' := by
    dsimp only [T']
    have h1 : 1 ≤ A := hA
    have h2 : 5 ≤ tangency := htangency
    nlinarith
  have hT'_1 : 1 ≤ T' := by linarith

  have hcomparison_100 : 100 ≤ comparison := by
    dsimp only [comparison]
    exact le_max_left _ _
  have hcomparison_C_center : C_center ≤ comparison := by
    dsimp only [comparison]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hcomparison_needed : comparison_needed ≤ comparison := by
    dsimp only [comparison]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hcomparison_nonneg : 0 ≤ comparison := by linarith
  have hcomparison1 : 1 ≤ comparison := by linarith

  -- Bound comparison ≤ B_base * tangency^B_exp * A^B_exp
  have hBbase_pos : 0 < B_base := by
    dsimp only [B_base]
    have h : 0 < C_core * Real.rpow 2 C_core :=
      mul_pos hC_core_pos (Real.rpow_pos_of_pos (by norm_num) C_core)
    linarith
  have hBexp_nonneg : 0 ≤ B_exp := by
    dsimp only [B_exp]
    have h1 : 0 ≤ C_ct := by linarith [hC_ct1]
    have h2 : C_ct ≤ max C_ct C_core := le_max_left _ _
    exact h1.trans h2

  have hcomparison_bound : comparison ≤ B_base * Real.rpow tangency B_exp * Real.rpow A B_exp := by
    simpa [comparison, C_center, comparison_needed, T', B_base, B_exp] using
      robust_comparison_bound hC_ct1 hC_core_100 htangency1 hA

  by_cases hScale : Real.rpow T' C_core * delta ≤ c₂ * t / 2
  · -- SMALL-RATIO BRANCH
    by_cases hfb : comparison * delta > t
    · -- FALLBACK: comparison too large for admissibility
      have h_ratio : t / delta < comparison := by
        have h : comparison * delta > t := hfb
        calc
          t / delta < (comparison * delta) / delta := by gcongr
          _ = comparison := by field_simp [hdelta.ne'] <;> ring
      have hratio_fb1 : t / delta ≤
          ratioScale_fb1 * Real.rpow tangency ratioExponent_fb1 * Real.rpow A ratioExponent_fb1 := by
        dsimp only [ratioScale_fb1, ratioExponent_fb1]
        exact h_ratio.le.trans hcomparison_bound
      have hratioScale_fb1_pos : 0 < ratioScale_fb1 := by
        dsimp only [ratioScale_fb1, B_base]
        positivity
      have hratioExponent_fb1_nonneg : 0 ≤ ratioExponent_fb1 := by
        dsimp only [ratioExponent_fb1]
        exact hBexp_nonneg
      have hbound : (R.card : ℝ) ≤ D_fb1 *
          Real.rpow tangency E_tang_fb1 * Real.rpow A E_A_fb1 :=
        robust_crude_packing_bound hK hD1 hfamily hI htangency1 hA hdelta ht hdt ht1
          hcenterScale3 hcenterExponent_nonneg hratioScale_fb1_pos hratioExponent_fb1_nonneg
          (hW hw₀) hRin hRquarter hR100 hcenter_bound_poly hratio_fb1
      have h_tang_nonneg : 0 ≤ Real.rpow tangency E_tang_fb1 :=
        Real.rpow_nonneg (by linarith) _
      have h_A_nonneg : 0 ≤ Real.rpow A E_A_fb1 :=
        Real.rpow_nonneg (by linarith) _
      have h_product_nonneg : 0 ≤ Real.rpow tangency E_tang_fb1 * Real.rpow A E_A_fb1 :=
        mul_nonneg h_tang_nonneg h_A_nonneg
      have h1 : D_fb1 * (Real.rpow tangency E_tang_fb1 * Real.rpow A E_A_fb1) ≤
          C * (Real.rpow tangency C * Real.rpow A C) := by
        have h1a : D_fb1 ≤ C := hD_fb1_le
        have h1b : Real.rpow tangency E_tang_fb1 * Real.rpow A E_A_fb1 ≤
            Real.rpow tangency C * Real.rpow A C := by
          have h1b1 : Real.rpow tangency E_tang_fb1 ≤ Real.rpow tangency C :=
            Real.rpow_le_rpow_of_exponent_le htangency1 hE_tang_fb1_le
          have h1b2 : Real.rpow A E_A_fb1 ≤ Real.rpow A C :=
            Real.rpow_le_rpow_of_exponent_le hA hE_A_fb1_le
          calc
            Real.rpow tangency E_tang_fb1 * Real.rpow A E_A_fb1
              ≤ Real.rpow tangency C * Real.rpow A E_A_fb1 :=
                mul_le_mul_of_nonneg_right h1b1 h_A_nonneg
            _ ≤ Real.rpow tangency C * Real.rpow A C :=
                mul_le_mul_of_nonneg_left h1b2 (Real.rpow_nonneg (by linarith) _)
        exact mul_le_mul h1a h1b h_product_nonneg (by linarith)
      have h1' : D_fb1 * Real.rpow tangency E_tang_fb1 * Real.rpow A E_A_fb1 ≤
          C * Real.rpow tangency C * Real.rpow A C := by
        have h_assoc1 : D_fb1 * Real.rpow tangency E_tang_fb1 * Real.rpow A E_A_fb1 =
            D_fb1 * (Real.rpow tangency E_tang_fb1 * Real.rpow A E_A_fb1) := by ring
        have h_assoc2 : C * Real.rpow tangency C * Real.rpow A C =
            C * (Real.rpow tangency C * Real.rpow A C) := by ring
        rw [h_assoc1, h_assoc2]
        exact h1
      have h7 : (R.card : ℝ) ≤ C * Real.rpow tangency C * Real.rpow A C :=
        hbound.trans h1'
      have hC_nonneg2 : 0 ≤ C := by linarith
      have h_tanC_nonneg : 0 ≤ Real.rpow tangency C := Real.rpow_nonneg (by linarith) _
      have h_AC_nonneg : 0 ≤ Real.rpow A C := Real.rpow_nonneg (by linarith) _
      have h_pos_C : 0 ≤ C * Real.rpow tangency C * Real.rpow A C :=
        mul_nonneg (mul_nonneg hC_nonneg2 h_tanC_nonneg) h_AC_nonneg
      have h8 : C * Real.rpow tangency C * Real.rpow A C ≤
          C * Real.rpow tangency C * Real.rpow A C * P :=
        calc
          C * Real.rpow tangency C * Real.rpow A C
            = (C * Real.rpow tangency C * Real.rpow A C) * 1 := by ring
          _ ≤ (C * Real.rpow tangency C * Real.rpow A C) * P := by
            exact mul_le_mul_of_nonneg_left hP_ge1 h_pos_C
      have h_final : (R.card : ℝ) ≤ C * Real.rpow tangency C * Real.rpow A C * P :=
        h7.trans h8
      have h9 : C * Real.rpow tangency C * Real.rpow A C * P =
          C * Real.rpow tangency C * Real.rpow A C * Real.rpow N (3 / 2 : ℝ) * Real.log N := by
        have hP_eq : P = Real.rpow N (3 / 2 : ℝ) * Real.log N := hP_def
        rw [hP_eq] <;> ring
      rw [h9] at h_final
      exact h_final

    · -- MAIN SUBCASE: admissibility holds
      have hadm : comparison * delta ≤ t := by linarith
      have hadm_orig : IsAdmissibleComparisonScale delta t comparison :=
        ⟨hcomparison1, hadm⟩

      have hcenter_poly : ∀ i, c2Distance w₀ (R.rectangle i).function ≤ comparison * t := by
        intro i
        have hsymm : c2Distance w₀ (R.rectangle i).function = c2Distance (R.rectangle i).function w₀ :=
          dist_comm _ _
        rw [hsymm]
        have h : c2Distance (R.rectangle i).function w₀ ≤ C_center * t := hcenter_bound i
        have h2 : C_center * t ≤ comparison * t :=
          mul_le_mul_of_nonneg_right hcomparison_C_center (by linarith)
        exact h.trans h2

      -- Apply polynomial refinement
      rcases hPolyRefineMain comparison hcomparison_100 family hCurv I hI delta t hdelta hdt
          hadm_orig w₀ R hRin hRquarter hR100 hcenter_poly with
        ⟨S, hS_incomp, hS_bound⟩

      have hS_nonempty : 0 < S.card := by
        by_contra h
        have h0 : S.card = 0 := by omega
        have hR0 : R.card = 0 := by simpa [h0] using hS_bound
        have h_cont : ¬(0 < R.card) := by rw [hR0] <;> norm_num
        exact h_cont hRnonempty

      -- Rescale S to (delta', r)
      let delta' : ℝ := delta / (2 * A)
      let r : ℝ := t / (2 * A)
      have hdelta'_pos : 0 < delta' := by positivity
      have hr_pos : 0 < r := by positivity
      have hdelta'_le : delta' ≤ delta := by
        dsimp only [delta']
        have hA2 : 1 ≤ 2 * A := by linarith
        calc
          delta / (2 * A) ≤ delta / 1 := by gcongr
          _ = delta := by ring
      have hratio : delta' / r = delta / t := by
        dsimp only [delta', r]
        have hA_ne_zero : A ≠ 0 := by linarith
        have hdelta_ne_zero : delta ≠ 0 := by linarith
        have ht_ne_zero : t ≠ 0 := by linarith
        field_simp [hA_ne_zero, hdelta_ne_zero, ht_ne_zero] <;> ring
      have hdt' : delta' ≤ r := by
        dsimp only [delta', r]
        gcongr
      have hr1 : r ≤ 1 := by
        dsimp only [r]
        have hA2 : 1 ≤ 2 * A := by linarith
        have h : t / (2 * A) ≤ t := by
          calc
            t / (2 * A) ≤ t / 1 := by gcongr
            _ = t := by ring
        exact h.trans ht1

      let S' : RectangleFamily delta' r := S.family.rescale hratio

      have hS'_incomp : S'.IsPairwiseIncomparable family comparison :=
        RectangleFamily.IsPairwiseIncomparable.rescale
          hdelta hdelta'_pos hdelta'_le hratio hcomparison1 hS_incomp

      have hadm_rescaled : IsAdmissibleComparisonScale delta' r comparison :=
        CurvilinearRectangle.admissible_comparison_scale_rescale hratio ht_pos hr_pos hadm_orig

      have hS'_incomp_needed : S'.IsPairwiseIncomparable family comparison_needed :=
        IsPairwiseIncomparable.mono hcomparison_needed hdelta'_pos hr_pos
          hadm_rescaled hS'_incomp

      have hS_quarter : S.family.IsOverCentralQuarterOf I := by
        intro j; exact hRquarter (S.embedding j)
      have hS_in : S.family.CentersIn family := by
        intro j; exact hRin (S.embedding j)
      have hS'_quarter : S'.IsOverCentralQuarterOf I :=
        RectangleFamily.IsOverCentralQuarterOf.rescale hS_quarter hratio
      have hS'_in : S'.CentersIn family :=
        RectangleFamily.CentersIn.rescale hS_in hratio
      have hS_family_nonempty : S.family.Nonempty := hS_nonempty
      have hS'_nonempty : S'.Nonempty :=
        RectangleFamily.Nonempty.rescale hS_family_nonempty hratio

      -- Tangent count transfer: input tangency → T' = 2*A*tangency
      have h_tan_transfer : ∀ (j : Fin S'.card),
          mu ≤ RectangleFamily.tangentCount (S'.rectangle j) W T' ∧
          nu ≤ RectangleFamily.tangentCount (S'.rectangle j) B T' := by
        intro j
        let i : Fin R.card := S.embedding j
        have h_eq1 : S'.rectangle j = (R.rectangle i).rescale hratio := by
          dsimp only [S']
          unfold RectangleFamily.rescale <;> rfl
        have hW : mu ≤ RectangleFamily.tangentCount (R.rectangle i) W tangency := (hcounts i).1
        have hB : nu ≤ RectangleFamily.tangentCount (R.rectangle i) B tangency := (hcounts i).2
        have hA_ne_zero : A ≠ 0 := by linarith
        have hbound : tangency * delta ≤ T' * delta' := by
          dsimp only [T', delta']
          have h : (2 * A * tangency) * (delta / (2 * A)) = tangency * delta := by
            field_simp [hA_ne_zero] <;> ring
          rw [h] <;> linarith
        have hW' : RectangleFamily.tangentCount (R.rectangle i) W tangency ≤
                   RectangleFamily.tangentCount ((R.rectangle i).rescale hratio) W T' :=
          RectangleFamily.tangentCount_rescale_le hdelta'_le hbound hratio
        have hB' : RectangleFamily.tangentCount (R.rectangle i) B tangency ≤
                   RectangleFamily.tangentCount ((R.rectangle i).rescale hratio) B T' :=
          RectangleFamily.tangentCount_rescale_le hdelta'_le hbound hratio
        have hW_final : mu ≤ RectangleFamily.tangentCount (S'.rectangle j) W T' := by
          simpa [h_eq1] using hW.trans hW'
        have hB_final : nu ≤ RectangleFamily.tangentCount (S'.rectangle j) B T' := by
          simpa [h_eq1] using hB.trans hB'
        exact ⟨hW_final, hB_final⟩

      -- Separation transfer
      have hsep' : W.AreSeparated B (2 * r) := by
        have h : W.AreSeparated B (2 * r) ↔ W.AreSeparated B (t / A) :=
          FiniteFunctionFamily.AreSeparated.scale_transfer (rfl)
        exact h.mpr hsep

      -- Ratio condition for robust core
      have hratio_core : Real.rpow T' C_core * delta' ≤ c₂ * r / 2 := by
        dsimp only [T', delta', r]
        have h_pos2 : 0 < 2 * A := by positivity
        have h2 : (Real.rpow (2 * A * tangency) C_core * delta) / (2 * A) ≤
            (c₂ * t / 2) / (2 * A) := div_le_div_of_nonneg_right hScale (by positivity)
        have h3 : Real.rpow (2 * A * tangency) C_core * (delta / (2 * A)) =
                 (Real.rpow (2 * A * tangency) C_core * delta) / (2 * A) := by ring
        have h4 : (c₂ * t / 2) / (2 * A) = c₂ * (t / (2 * A)) / 2 := by ring
        rw [h3]
        rw [h4] at h2
        exact h2

      -- Admissibility for robust core
      have hadm_core : IsAdmissibleComparisonScale delta' r comparison_needed := by
        have h1 : comparison_needed * delta' ≤ r := by
          dsimp only [delta', r]
          have h2 : comparison_needed * delta ≤ t := by
            have h3 : comparison_needed ≤ comparison := hcomparison_needed
            have h4 : comparison_needed * delta ≤ comparison * delta :=
              mul_le_mul_of_nonneg_right h3 (by linarith)
            exact h4.trans hadm
          have h_pos2 : 0 < 2 * A := by positivity
          have h3 : (comparison_needed * delta) / (2 * A) ≤ t / (2 * A) :=
            div_le_div_of_nonneg_right h2 (by positivity)
          have h4 : comparison_needed * (delta / (2 * A)) = (comparison_needed * delta) / (2 * A) := by ring
          rw [h4]
          exact h3
        have h_cn1 : 1 ≤ comparison_needed := by
          dsimp only [comparison_needed]
          have h1 : 1 ≤ C_core := by linarith [hC_core_100]
          have h2 : 1 ≤ Real.rpow T' C_core := Real.one_le_rpow hT'_1 (by linarith)
          have h_pos1 : 0 < C_core := by linarith
          have h_pos2 : 0 < Real.rpow T' C_core := Real.rpow_pos_of_pos hT'_pos C_core
          have h_mul : 1 ≤ C_core * Real.rpow T' C_core := by
            calc
              1 = 1 * 1 := by ring
              _ ≤ C_core * Real.rpow T' C_core := by gcongr <;> linarith
          exact h_mul
        exact ⟨h_cn1, h1⟩

      -- Apply robust core
      have hrobust_bound : (S'.card : ℝ) ≤
          C_core * Real.rpow T' C_core * Real.rpow N (3 / 2 : ℝ) * Real.log N :=
        hRobustCoreMain T' hT'_5 family hCurv I hI delta' r
          hdelta'_pos hr_pos hdt' hr1 hratio_core hadm_core W B hW hB hsep'
          S' hS'_in hS'_quarter hS'_incomp_needed hS'_nonempty mu nu hmu hnu h_tan_transfer
      have hrobust_bound' : (S'.card : ℝ) ≤ C_core * Real.rpow T' C_core * P := by
        have h_rhs_eq : C_core * Real.rpow T' C_core * Real.rpow N (3 / 2 : ℝ) * Real.log N =
            C_core * Real.rpow T' C_core * P := by
          dsimp only [P]
          <;> ring_nf
        exact hrobust_bound.trans (le_of_eq h_rhs_eq)

      have hScard_eq : (S'.card : ℝ) = (S.card : ℝ) := by
        dsimp only [S'] <;> rfl

      have hstep1 : (R.card : ℝ) ≤ C_poly * Real.rpow comparison C_poly * (S'.card : ℝ) := by
        calc
          (R.card : ℝ) ≤ C_poly * Real.rpow comparison C_poly * (S.card : ℝ) := hS_bound
          _ = C_poly * Real.rpow comparison C_poly * (S'.card : ℝ) := by rw [hScard_eq] <;> ring

      have hstep2 : C_poly * Real.rpow comparison C_poly * (S'.card : ℝ) ≤
          C_poly * Real.rpow comparison C_poly * C_core * Real.rpow T' C_core * P := by
        have h : (S'.card : ℝ) ≤ C_core * Real.rpow T' C_core * P := hrobust_bound'
        have hpos : 0 ≤ C_poly * Real.rpow comparison C_poly :=
          mul_nonneg (by linarith) (Real.rpow_nonneg hcomparison_nonneg C_poly)
        calc
          C_poly * Real.rpow comparison C_poly * (S'.card : ℝ)
            ≤ C_poly * Real.rpow comparison C_poly * (C_core * Real.rpow T' C_core * P) :=
              mul_le_mul_of_nonneg_left h hpos
          _ = C_poly * Real.rpow comparison C_poly * C_core * Real.rpow T' C_core * P := by ring

      have hstep3_core :
          C_poly * Real.rpow comparison C_poly * C_core * Real.rpow T' C_core ≤
          D_small * Real.rpow tangency E_small * Real.rpow A E_small := by
        simpa [T', D_small, E_small] using
          robust_refined_product_bound
            (show 0 ≤ C_poly by linarith)
            hBbase_pos
            (show 0 ≤ C_core by linarith)
            hcomparison_nonneg
            htangency1
            hA
            hcomparison_bound

      have hstep3 : C_poly * Real.rpow comparison C_poly * C_core * Real.rpow T' C_core * P ≤
          D_small * Real.rpow tangency E_small * Real.rpow A E_small * P :=
        mul_le_mul_of_nonneg_right hstep3_core hP_nonneg
      have hstep4 : D_small * Real.rpow tangency E_small * Real.rpow A E_small * P ≤
          C * Real.rpow tangency C * Real.rpow A C * P := by
        have hEsmall_le1 : Real.rpow tangency E_small ≤ Real.rpow tangency C :=
          Real.rpow_le_rpow_of_exponent_le htangency1 hE_small_le
        have hEsmall_le2 : Real.rpow A E_small ≤ Real.rpow A C :=
          Real.rpow_le_rpow_of_exponent_le hA hE_small_le
        have h9 : D_small * Real.rpow tangency E_small * Real.rpow A E_small ≤
            C * Real.rpow tangency C * Real.rpow A C := by
          have h10 : D_small ≤ C := hD_small_le
          have h11 : 0 ≤ Real.rpow tangency E_small := Real.rpow_nonneg htangency_nonneg _
          have h12 : 0 ≤ Real.rpow A E_small := Real.rpow_nonneg hA_pos0 _
          have h13 : 0 ≤ Real.rpow tangency C := Real.rpow_nonneg htangency_nonneg _
          have hC_nonneg2 : 0 ≤ C := by linarith
          have hCT_nonneg : 0 ≤ C * Real.rpow tangency C := mul_nonneg hC_nonneg2 h13
          calc
            D_small * Real.rpow tangency E_small * Real.rpow A E_small
              ≤ C * Real.rpow tangency E_small * Real.rpow A E_small :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h10 h11) h12
            _ ≤ C * Real.rpow tangency C * Real.rpow A E_small :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hEsmall_le1 hC_nonneg2) h12
            _ ≤ C * Real.rpow tangency C * Real.rpow A C :=
                mul_le_mul_of_nonneg_left hEsmall_le2 hCT_nonneg
        exact mul_le_mul_of_nonneg_right h9 hP_nonneg

      have h_final : (R.card : ℝ) ≤ C * Real.rpow tangency C * Real.rpow A C * P :=
        hstep1.trans (hstep2.trans (hstep3.trans hstep4))
      let X := C * Real.rpow tangency C * Real.rpow A C
      have hP_eq : P = Real.rpow N (3 / 2 : ℝ) * Real.log N := hP_def
      have h_eq1 : X * P = X * (Real.rpow N (3 / 2 : ℝ) * Real.log N) :=
        congrArg (fun y : ℝ => X * y) hP_eq
      have h_eq2 : X * (Real.rpow N (3 / 2 : ℝ) * Real.log N) =
          X * Real.rpow N (3 / 2 : ℝ) * Real.log N :=
        (mul_assoc X (Real.rpow N (3 / 2 : ℝ)) (Real.log N)).symm
      have h_final' : (R.card : ℝ) ≤ X * Real.rpow N (3 / 2 : ℝ) * Real.log N :=
        h_final.trans (le_of_eq (h_eq1.trans h_eq2))
      exact h_final'
  · -- LARGE-RATIO BRANCH: scale condition fails
    have hScale' : c₂ * t / 2 < Real.rpow T' C_core * delta :=
      lt_of_not_ge hScale
    have h_ratio : t / delta < 2 * Real.rpow T' C_core / c₂ := by
      have hc2_pos' : 0 < c₂ := hc₂_pos
      calc
        t / delta = (c₂ * t / 2) / (c₂ * delta / 2) := by
          field_simp [hdelta.ne', hc2_pos'.ne']
        _ < (Real.rpow T' C_core * delta) / (c₂ * delta / 2) := by gcongr
        _ = 2 * Real.rpow T' C_core / c₂ := by
          field_simp [hdelta.ne', hc2_pos'.ne']
    have hT'_expand : Real.rpow T' C_core =
        Real.rpow 2 C_core * Real.rpow tangency C_core * Real.rpow A C_core := by
      dsimp only [T']
      have h1 : Real.rpow (2 * A * tangency) C_core =
          Real.rpow (2 * A) C_core * Real.rpow tangency C_core :=
        Real.mul_rpow (by positivity) (by linarith)
      rw [h1]
      have h2 : Real.rpow (2 * A) C_core = Real.rpow 2 C_core * Real.rpow A C_core :=
        Real.mul_rpow (by norm_num) hA_pos0
      rw [h2] <;> ring
    have hratio_fb2 : t / delta ≤
        ratioScale_fb2 * Real.rpow tangency ratioExponent_fb2 * Real.rpow A ratioExponent_fb2 := by
      dsimp only [ratioScale_fb2, ratioExponent_fb2]
      rw [hT'_expand] at h_ratio
      have h : (2 * (Real.rpow 2 C_core * Real.rpow tangency C_core * Real.rpow A C_core) / c₂) =
          (2 * Real.rpow 2 C_core / c₂) * Real.rpow tangency C_core * Real.rpow A C_core := by
        ring
      rw [h] at h_ratio
      exact h_ratio.le
    have hratioScale_fb2_pos : 0 < ratioScale_fb2 := by
      dsimp only [ratioScale_fb2]
      have h1 : 0 < Real.rpow 2 C_core := Real.rpow_pos_of_pos (by norm_num) C_core
      have h2 : 0 < 2 * Real.rpow 2 C_core := mul_pos (by norm_num) h1
      exact div_pos h2 hc₂_pos
    have hratioExponent_fb2_nonneg : 0 ≤ ratioExponent_fb2 :=
      le_trans (show (0 : ℝ) ≤ 100 by norm_num) hC_core_100
    have hbound : (R.card : ℝ) ≤ D_fb2 *
        Real.rpow tangency E_tang_fb2 * Real.rpow A E_A_fb2 :=
      robust_crude_packing_bound hK hD1 hfamily hI htangency1 hA hdelta ht hdt ht1
        hcenterScale3 hcenterExponent_nonneg hratioScale_fb2_pos hratioExponent_fb2_nonneg
        (hW hw₀) hRin hRquarter hR100 hcenter_bound_poly hratio_fb2
    have h_final : (R.card : ℝ) ≤ C * Real.rpow tangency C * Real.rpow A C * P := by
      have h2 : D_fb2 ≤ C := hD_fb2_le
      have h3 : Real.rpow tangency E_tang_fb2 ≤ Real.rpow tangency C :=
        Real.rpow_le_rpow_of_exponent_le htangency1 hE_tang_fb2_le
      have h4 : Real.rpow A E_A_fb2 ≤ Real.rpow A C :=
        Real.rpow_le_rpow_of_exponent_le hA hE_A_fb2_le
      have h5 : 0 ≤ Real.rpow tangency E_tang_fb2 := Real.rpow_nonneg htangency_nonneg _
      have h6 : 0 ≤ Real.rpow A E_A_fb2 := Real.rpow_nonneg hA_pos0 _
      have hC_nonneg3 : 0 ≤ C := zero_le_one.trans hC_pos
      have h13 : 0 ≤ Real.rpow tangency C := Real.rpow_nonneg htangency_nonneg _
      have hCT_nonneg2 : 0 ≤ C * Real.rpow tangency C := mul_nonneg hC_nonneg3 h13
      have h1 : D_fb2 * Real.rpow tangency E_tang_fb2 * Real.rpow A E_A_fb2 ≤
          C * Real.rpow tangency C * Real.rpow A C := by
        calc
          D_fb2 * Real.rpow tangency E_tang_fb2 * Real.rpow A E_A_fb2
            ≤ C * Real.rpow tangency E_tang_fb2 * Real.rpow A E_A_fb2 :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 h5) h6
          _ ≤ C * Real.rpow tangency C * Real.rpow A E_A_fb2 :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hC_nonneg3) h6
          _ ≤ C * Real.rpow tangency C * Real.rpow A C :=
              mul_le_mul_of_nonneg_left h4 hCT_nonneg2
      have h7 : (R.card : ℝ) ≤ C * Real.rpow tangency C * Real.rpow A C :=
        hbound.trans h1
      have hCAT_nonneg : 0 ≤ C * Real.rpow tangency C * Real.rpow A C :=
        mul_nonneg hCT_nonneg2 (Real.rpow_nonneg hA_pos0 _)
      have h8 : C * Real.rpow tangency C * Real.rpow A C ≤
          C * Real.rpow tangency C * Real.rpow A C * P :=
        le_mul_of_one_le_right hCAT_nonneg hP_ge1
      exact h7.trans h8
    have h9 : C * Real.rpow tangency C * Real.rpow A C * P =
        C * Real.rpow tangency C * Real.rpow A C *
          Real.rpow N (3 / 2 : ℝ) * Real.log N := by
      have hP : P = Real.rpow N (3 / 2 : ℝ) * Real.log N := hP_def
      calc
        C * Real.rpow tangency C * Real.rpow A C * P
          = C * Real.rpow tangency C * Real.rpow A C * (Real.rpow N (3 / 2 : ℝ) * Real.log N) := by rw [hP]
        _ = C * Real.rpow tangency C * Real.rpow A C * Real.rpow N (3 / 2 : ℝ) * Real.log N := by ring
    rw [h9] at h_final
    exact h_final

end Kakeya.Cinematic
