import MyLeanRepo.Kakeya.CV.Statements
import MyLeanRepo.Kakeya.CV.Targets.AntipodalSignSeparation.TopologicalTools
import MyLeanRepo.Kakeya.CV.Targets.AntipodalSignSeparation.MeasureContinuity

/-!
# Separation of antipodal polynomial sign classes

Establishes the closure-separation condition needed by the Borsuk--Ulam
covering lemma in the final polynomial visibility argument.

## Proof outline (direct contradiction)

Assume `z` lies in both `positiveSignClass` and the closure of its antipodal
image.  Extract a sequence `zseq m = -xseq m` from the antipodal image
converging to `z`, where `xseq m ∈ positiveSignClass`.  By sequential local
constancy of `selectedRegion`, the regions agree eventually.  Since
`xseq m → -z`, the parameter polynomials converge pointwise to
`parameterPolynomial P (-z) = -parameterPolynomial P z`.  Sign-volume
continuity then transports the strict inequality at each `xseq m` to a
non-strict inequality at the limit, contradicting `z ∈ positiveSignClass`.
-/

noncomputable section

open MeasureTheory Filter

namespace Kakeya.CV

theorem antipodal_sign_separation :
    AntipodalSignSeparationStatement := by
  intro k P selectedRegion D hD_antipodal hRegion_antipodal hRegion_meas
        hRegion_finite hPoly_nonzero hNoBisect hLocalConst
  rw [← Set.not_nonempty_iff_eq_empty]
  intro hne
  rcases hne with ⟨z, hz⟩
  have hz_pos : z ∈ positiveSignClass P selectedRegion D := hz.1
  have hz_closure : z ∈ closure ((fun x => -x) '' positiveSignClass P selectedRegion D) := hz.2
  have hz_D : z ∈ D := hz_pos.1

  -- Step 1: extract a sequence from the closure
  have hseq : ∃ (zseq : ℕ → CoefficientSpace P.dim),
      (∀ m, zseq m ∈ (fun x => -x) '' positiveSignClass P selectedRegion D) ∧
      Tendsto zseq atTop (nhds z) :=
    exists_seq_in_closure_tendsto hz_closure
  rcases hseq with ⟨zseq, hzseq_in_image, hzseq_tendsto⟩

  -- Step 2: write zseq m = -xseq m with xseq m ∈ positiveSignClass
  choose xseq hxseq_pos hxseq_eq using fun m => hzseq_in_image m
  have h_xseq_eq : ∀ m, -xseq m = zseq m := hxseq_eq
  have h_xseq_pos : ∀ m, xseq m ∈ positiveSignClass P selectedRegion D := hxseq_pos
  have h_xseq_D : ∀ m, xseq m ∈ D := fun m => (h_xseq_pos m).1
  have h_zseq_D : ∀ m, zseq m ∈ D := by
    intro m
    have h_eq : zseq m = -xseq m := (h_xseq_eq m).symm
    rw [h_eq]
    exact hD_antipodal (xseq m) (h_xseq_D m)

  -- Step 3: local constancy gives selectedRegion (zseq m) = selectedRegion z eventually
  have h_local : ∀ᶠ m in atTop, selectedRegion (zseq m) = selectedRegion z :=
    hLocalConst zseq z h_zseq_D hz_D hzseq_tendsto

  -- Step 4: hence selectedRegion (xseq m) = selectedRegion z eventually
  have h_region_eventually : ∀ᶠ m in atTop, selectedRegion (xseq m) = selectedRegion z := by
    filter_upwards [h_local] with m hm
    have h1 : selectedRegion (xseq m) = selectedRegion (-(xseq m)) :=
      (hRegion_antipodal (xseq m) (h_xseq_D m)).symm
    rw [h1, h_xseq_eq m]
    exact hm

  -- Step 5: xseq m → -z
  have h_xseq_tendsto : Tendsto xseq atTop (nhds (-z)) := by
    have h1 : Tendsto (fun m => -zseq m) atTop (nhds (-z)) :=
      hzseq_tendsto.neg
    have h2 : (fun m => -zseq m) = xseq := by
      funext m
      have h3 : -xseq m = zseq m := h_xseq_eq m
      have h4 : -zseq m = xseq m := by
        calc
          -zseq m = -(-xseq m) := by rw [h3]
          _ = xseq m := by simp
      exact h4
    rw [h2] at h1
    exact h1

  -- Step 6: apply sign-volume continuity at limit -z
  let R := selectedRegion z
  let p := parameterPolynomial P z
  have h_p_nonzero : p ≠ 0 := hPoly_nonzero z hz_D
  have h_neg_p_nonzero : parameterPolynomial P (-z) ≠ 0 := by
    rw [parameterPolynomial_neg P z]
    simpa using h_p_nonzero

  let pseq := fun m => parameterPolynomial P (xseq m)
  let p_limit := parameterPolynomial P (-z)

  -- Pointwise convergence of polynomial values:
  -- x ↦ polynomialValue (parameterPolynomial P x) y is linear in x, hence continuous
  have hconv : ∀ (y : Point 3),
      Tendsto (fun m => polynomialValue (pseq m) y) atTop (nhds (polynomialValue p_limit y)) := by
    intro y
    let f : CoefficientSpace P.dim →ₗ[ℝ] ℝ :=
      { toFun := fun x => polynomialValue (parameterPolynomial P x) y
        map_add' := by
          intro x1 x2
          have h1 : parameterPolynomial P (x1 + x2) = parameterPolynomial P x1 + parameterPolynomial P x2 := by
            dsimp only [parameterPolynomial]
            exact congr_arg (fun p : degreeLESubmodule k => (p : MvPolynomial (Fin 3) ℝ))
              (map_add P.equiv x1 x2)
          rw [h1]
          simp [polynomialValue, MvPolynomial.eval_add]
        map_smul' := by
          intro c x
          have h1 : parameterPolynomial P (c • x) = c • parameterPolynomial P x := by
            dsimp only [parameterPolynomial]
            exact congr_arg (fun p : degreeLESubmodule k => (p : MvPolynomial (Fin 3) ℝ))
              (map_smul P.equiv c x)
          rw [h1]
          dsimp only [polynomialValue]
          have h2 : MvPolynomial.eval (fun i : Fin 3 => y i) (c • parameterPolynomial P x) =
              c * MvPolynomial.eval (fun i : Fin 3 => y i) (parameterPolynomial P x) := by
            have h3 : c • parameterPolynomial P x = MvPolynomial.C c * parameterPolynomial P x := by
              exact MvPolynomial.smul_eq_C_mul (parameterPolynomial P x) c
            rw [h3, MvPolynomial.eval_mul, MvPolynomial.eval_C] <;> ring
          exact h2 }
    have h_cont : Continuous f :=
      LinearMap.continuous_of_finiteDimensional f
    exact h_cont.tendsto (-z) |>.comp h_xseq_tendsto

  have h_svc1 := sign_volume_pos_continuity R
    (hRegion_meas z hz_D) (hRegion_finite z hz_D) pseq p_limit h_neg_p_nonzero hconv
  have h_svc2 := sign_volume_neg_continuity R
    (hRegion_meas z hz_D) (hRegion_finite z hz_D) pseq p_limit h_neg_p_nonzero hconv

  -- Step 7: identify the limit volumes using parameterPolynomial_neg
  have h_set1 : {y : Point 3 | 0 < polynomialValue (parameterPolynomial P (-z)) y} =
      {y : Point 3 | polynomialValue p y < 0} := by
    ext y
    have h1 : polynomialValue (parameterPolynomial P (-z)) y = -polynomialValue (parameterPolynomial P z) y := by
      have h2 : parameterPolynomial P (-z) = -(parameterPolynomial P z) := parameterPolynomial_neg P z
      rw [h2]
      exact polynomialValue_neg (parameterPolynomial P z) y
    have h3 : (0 < polynomialValue (parameterPolynomial P (-z)) y) ↔ (polynomialValue (parameterPolynomial P z) y < 0) := by
      rw [h1]
      constructor <;> intro h4 <;> linarith
    exact h3
  have h_limit_pos : volume (R ∩ {y | 0 < polynomialValue (parameterPolynomial P (-z)) y}) =
      volume (R ∩ {y | polynomialValue p y < 0}) := by
    rw [h_set1]

  have h_set2 : {y : Point 3 | polynomialValue (parameterPolynomial P (-z)) y < 0} =
      {y : Point 3 | 0 < polynomialValue p y} := by
    ext y
    have h1 : polynomialValue (parameterPolynomial P (-z)) y = -polynomialValue (parameterPolynomial P z) y := by
      have h2 : parameterPolynomial P (-z) = -(parameterPolynomial P z) := parameterPolynomial_neg P z
      rw [h2]
      exact polynomialValue_neg (parameterPolynomial P z) y
    have h3 : (polynomialValue (parameterPolynomial P (-z)) y < 0) ↔ (0 < polynomialValue (parameterPolynomial P z) y) := by
      rw [h1]
      constructor <;> intro h4 <;> linarith
    exact h3
  have h_limit_neg : volume (R ∩ {y | polynomialValue (parameterPolynomial P (-z)) y < 0}) =
      volume (R ∩ {y | 0 < polynomialValue p y}) := by
    rw [h_set2]

  -- Step 8: from xseq m ∈ positiveSignClass, get strict inequality eventually
  have h_strict_eventually : ∀ᶠ m in atTop,
      volume (R ∩ {y | polynomialValue (parameterPolynomial P (xseq m)) y < 0}) <
      volume (R ∩ {y | 0 < polynomialValue (parameterPolynomial P (xseq m)) y}) := by
    filter_upwards [h_region_eventually] with m hm
    have h_pos : xseq m ∈ positiveSignClass P selectedRegion D := h_xseq_pos m
    have h_def : positiveSignClass P selectedRegion D =
        {x | x ∈ D ∧ volume (selectedRegion x ∩ {y | 0 < polynomialValue (parameterPolynomial P x) y}) >
            volume (selectedRegion x ∩ {y | polynomialValue (parameterPolynomial P x) y < 0})} := by
      rfl
    rw [h_def] at h_pos
    rcases h_pos with ⟨_, h_ineq⟩
    rw [hm] at h_ineq
    exact h_ineq

  -- Step 9: take limits to derive non-strict inequality at z
  rw [h_limit_pos] at h_svc1
  rw [h_limit_neg] at h_svc2
  have h_contra : volume (R ∩ {y | 0 < polynomialValue p y}) ≤
      volume (R ∩ {y | polynomialValue p y < 0}) :=
    le_of_tendsto_of_tendsto h_svc2 h_svc1
      (h_strict_eventually.mono fun _ h => h.le)

  -- Step 10: contradict z ∈ positiveSignClass
  have h_z_ineq : volume (R ∩ {y | 0 < polynomialValue p y}) >
      volume (R ∩ {y | polynomialValue p y < 0}) := by
    have h_def : positiveSignClass P selectedRegion D =
        {x | x ∈ D ∧ volume (selectedRegion x ∩ {y | 0 < polynomialValue (parameterPolynomial P x) y}) >
            volume (selectedRegion x ∩ {y | polynomialValue (parameterPolynomial P x) y < 0})} := by
      rfl
    rw [h_def] at hz_pos
    exact hz_pos.2
  exact lt_irrefl _ (lt_of_le_of_lt h_contra h_z_ineq)

end Kakeya.CV
