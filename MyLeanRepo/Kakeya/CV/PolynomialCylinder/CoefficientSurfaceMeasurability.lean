import MyLeanRepo.Kakeya.CV.PolynomialCylinder.SinglePatchContribution
import MyLeanRepo.Kakeya.CV.PolynomialCylinder.GraphPatchIntegralMeasurability
import MyLeanRepo.Kakeya.CV.PolynomialMollification

/-!
# Coefficient measurability of directional surface area

The regular zero set is covered by countably many jointly measurable graph
patches. After disjointifying those patches in coefficient-space times
physical-space, each contribution is measurable by
`single_patch_contribution_measurable`. The singular part contributes zero
because `polynomialUnitNormal` is defined to vanish when the gradient does.
-/

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal Real Classical

namespace Kakeya.CV

variable {k : ℕ} {P : PolynomialParameterization k}

def coefficientRegularZeroSet (P : PolynomialParameterization k) :
    Set (CoefficientSpace P.dim × Point 3) :=
  {p | polynomialValue (parameterPolynomial P p.1) p.2 = 0 ∧
    polynomialGradient (parameterPolynomial P p.1) p.2 ≠ 0}

lemma coefficientRegularZeroSet_measurable
    (P : PolynomialParameterization k) :
    MeasurableSet (coefficientRegularZeroSet P) := by
  have hvalue :
      Measurable
        (fun p : CoefficientSpace P.dim × Point 3 =>
          polynomialValue (parameterPolynomial P p.1) p.2) :=
    family_polynomialValue_continuous.measurable
  have hgrad :
      Measurable
        (fun p : CoefficientSpace P.dim × Point 3 =>
          polynomialGradient (parameterPolynomial P p.1) p.2) :=
    family_polynomialGradient_continuous.measurable
  exact (hvalue (MeasurableSet.singleton 0)).inter
    (hgrad (MeasurableSet.singleton 0) |>.compl)

lemma coverPatchImage_subset_regular
    (patch : CoverPatch k P) :
    coverPatchImage patch ⊆ coefficientRegularZeroSet P := by
  rintro ⟨x, z⟩ ⟨hxV, y, hyA, heq⟩
  have hzero := patch.h_zero x hxV y hyA
  have hreg := patch.h_reg x hxV y hyA
  change polynomialValue (parameterPolynomial P x) z = 0 ∧
    polynomialGradient (parameterPolynomial P x) z ≠ 0
  refine ⟨by simpa only [heq] using hzero, ?_⟩
  intro hgrad
  apply hreg
  rw [heq]
  exact congrArg (fun v : Point 3 => v patch.dir) hgrad

lemma iUnion_coverPatchImage_eq_regular
    (patches : ℕ → CoverPatch k P)
    (hcover : ∀ (x : CoefficientSpace P.dim) (z : Point 3),
      polynomialValue (parameterPolynomial P x) z = 0 →
      polynomialGradient (parameterPolynomial P x) z ≠ 0 →
      ∃ n : ℕ, x ∈ (patches n).V ∧
        ∃ y ∈ (patches n).A,
          z = dirGraphMap (patches n).dir ((patches n).g x) y) :
    (⋃ n, coverPatchImage (patches n)) = coefficientRegularZeroSet P := by
  ext p
  rcases p with ⟨x, z⟩
  constructor
  · intro hp
    rcases Set.mem_iUnion.mp hp with ⟨n, hn⟩
    exact coverPatchImage_subset_regular (patches n) hn
  · rintro ⟨hzero, hgrad⟩
    rcases hcover x z hzero hgrad with ⟨n, hxV, y, hyA, heq⟩
    exact Set.mem_iUnion.mpr ⟨n, hxV, y, hyA, heq.symm⟩

def localizedDisjointPatch
    (patches : ℕ → CoverPatch k P) (U : Set (Point 3)) (n : ℕ) :
    Set (CoefficientSpace P.dim × Point 3) :=
  disjointed (fun m => coverPatchImage (patches m)) n ∩
    (Set.univ ×ˢ U)

lemma localizedDisjointPatch_measurable
    (patches : ℕ → CoverPatch k P)
    {U : Set (Point 3)} (hU : MeasurableSet U)
    (n : ℕ) :
    MeasurableSet (localizedDisjointPatch patches U n) := by
  exact (MeasurableSet.disjointed
      (fun m => coverPatchImage_measurable (patches m)) n).inter
    (MeasurableSet.univ.prod hU)

lemma localizedDisjointPatch_subset
    (patches : ℕ → CoverPatch k P) (U : Set (Point 3)) (n : ℕ) :
    localizedDisjointPatch patches U n ⊆
      coverPatchImage (patches n) := by
  exact fun _ h => disjointed_subset
    (fun m => coverPatchImage (patches m)) n h.1

lemma localizedDisjointPatch_pairwise
    (patches : ℕ → CoverPatch k P) (U : Set (Point 3)) :
    Pairwise (fun i j =>
      Disjoint (localizedDisjointPatch patches U i)
        (localizedDisjointPatch patches U j)) := by
  exact (disjoint_disjointed
    (fun m => coverPatchImage (patches m))).mono fun _ _ h =>
      h.mono inter_subset_left inter_subset_left

lemma iUnion_localizedDisjointPatch
    (patches : ℕ → CoverPatch k P)
    (hcover : ∀ (x : CoefficientSpace P.dim) (z : Point 3),
      polynomialValue (parameterPolynomial P x) z = 0 →
      polynomialGradient (parameterPolynomial P x) z ≠ 0 →
      ∃ n : ℕ, x ∈ (patches n).V ∧
        ∃ y ∈ (patches n).A,
          z = dirGraphMap (patches n).dir ((patches n).g x) y)
    (U : Set (Point 3)) :
    (⋃ n, localizedDisjointPatch patches U n) =
      coefficientRegularZeroSet P ∩ (Set.univ ×ˢ U) := by
  ext p
  constructor
  · intro hp
    rcases Set.mem_iUnion.mp hp with ⟨n, hn⟩
    refine ⟨?_, hn.2⟩
    have hsub := disjointed_subset
      (fun m => coverPatchImage (patches m)) n hn.1
    exact coverPatchImage_subset_regular (patches n) hsub
  · rintro ⟨hreg, hU⟩
    have hcover_union :
        p ∈ ⋃ n, coverPatchImage (patches n) := by
      rw [iUnion_coverPatchImage_eq_regular patches hcover]
      exact hreg
    have hdisj_union :
        p ∈ ⋃ n, disjointed
          (fun m => coverPatchImage (patches m)) n := by
      rw [iUnion_disjointed]
      exact hcover_union
    rcases Set.mem_iUnion.mp hdisj_union with ⟨n, hn⟩
    exact Set.mem_iUnion.mpr ⟨n, hn, hU⟩

lemma singular_integrand_zero
    (p : MvPolynomial (Fin 3) ℝ) (u z : Point 3)
    (hgrad : polynomialGradient p z = 0) :
    ENNReal.ofReal ‖inner ℝ u (polynomialUnitNormal p z)‖ = 0 := by
  have hnorm : ‖polynomialGradient p z‖ = 0 := by rw [hgrad, norm_zero]
  rw [polynomialUnitNormal, dif_pos hnorm]
  simp

/-- Directional surface area over a measurable region is measurable as a
function of polynomial coefficients. -/
theorem coefficient_directionalSurfaceArea_measurable
    (P : PolynomialParameterization k)
    {U : Set (Point 3)} (hU : MeasurableSet U)
    (u : Point 3) :
    Measurable (fun x : CoefficientSpace P.dim =>
      directionalSurfaceArea u (parameterPolynomial P x)
        (polynomialZeroSet (parameterPolynomial P x) ∩ U)) := by
  let Coeff := CoefficientSpace P.dim
  rcases exists_countable_regular_cover P with ⟨patches, hcover⟩
  let E : ℕ → Set (Coeff × Point 3) :=
    localizedDisjointPatch patches U
  have hE_meas : ∀ n, MeasurableSet (E n) :=
    fun n => localizedDisjointPatch_measurable patches hU n
  have hE_sub : ∀ n, E n ⊆ coverPatchImage (patches n) :=
    fun n => localizedDisjointPatch_subset patches U n
  let contribution : ℕ → Coeff → ENNReal := fun n x =>
    ∫⁻ z : Point 3,
      {z : Point 3 | (x, z) ∈ E n}.indicator
          (1 : Point 3 → ENNReal) z *
        Set.univ.indicator (1 : Point 3 → ENNReal) z *
        ENNReal.ofReal ‖inner ℝ u
          (polynomialUnitNormal (parameterPolynomial P x) z)‖
    ∂μH[2]
  have hcontribution : ∀ n, Measurable (contribution n) := by
    intro n
    exact single_patch_contribution_measurable
      (patches n) MeasurableSet.univ u (E n) (hE_meas n) (hE_sub n)
  have hsum : Measurable (fun x => ∑' n, contribution n x) :=
    graph_patch_tsum_measurable hcontribution
  have hpointwise : ∀ x : Coeff,
      directionalSurfaceArea u (parameterPolynomial P x)
          (polynomialZeroSet (parameterPolynomial P x) ∩ U) =
        ∑' n, contribution n x := by
    intro x
    let p := parameterPolynomial P x
    let F : Point 3 → ENNReal := fun z =>
      ENNReal.ofReal ‖inner ℝ u (polynomialUnitNormal p z)‖
    let S : ℕ → Set (Point 3) := fun n => {z | (x, z) ∈ E n}
    let R : Set (Point 3) :=
      {z | polynomialValue p z = 0 ∧ polynomialGradient p z ≠ 0 ∧ z ∈ U}
    let Z : Set (Point 3) :=
      {z | polynomialValue p z = 0 ∧ polynomialGradient p z = 0 ∧ z ∈ U}
    have hS_meas : ∀ n, MeasurableSet (S n) := by
      intro n
      exact (hE_meas n).preimage
        (measurable_const.prodMk measurable_id)
    have hS_pairwise :
        Pairwise (fun i j => Disjoint (S i) (S j)) := by
      intro i j hij
      have hdisj := localizedDisjointPatch_pairwise patches U hij
      exact Set.disjoint_left.mpr fun z hzi hzj =>
        Set.disjoint_left.mp hdisj hzi hzj
    have hS_union : (⋃ n, S n) = R := by
      have hjoint := iUnion_localizedDisjointPatch patches hcover U
      ext z
      have hmem :
          (x, z) ∈ ⋃ n, E n ↔
            (x, z) ∈ coefficientRegularZeroSet P ∩ (Set.univ ×ˢ U) := by
        rw [hjoint]
      constructor
      · intro hz
        have hz' : (x, z) ∈ ⋃ n, E n := by
          rcases Set.mem_iUnion.mp hz with ⟨n, hn⟩
          exact Set.mem_iUnion.mpr ⟨n, hn⟩
        rcases hmem.mp hz' with ⟨hreg, _hxuniv, hzU⟩
        exact ⟨hreg.1, hreg.2, hzU⟩
      · rintro ⟨hzero, hgrad, hzU⟩
        have hz' :
            (x, z) ∈ coefficientRegularZeroSet P ∩
              (Set.univ ×ˢ U) :=
          ⟨⟨hzero, hgrad⟩, Set.mem_univ x, hzU⟩
        rcases Set.mem_iUnion.mp (hmem.mpr hz') with ⟨n, hn⟩
        exact Set.mem_iUnion.mpr ⟨n, hn⟩
    have hF_meas : Measurable F := by
      exact ENNReal.measurable_ofReal.comp
        (measurable_const.inner
          (measurable_polynomialUnitNormal p)).norm
    have hcontribution_set : ∀ n,
        contribution n x = ∫⁻ z in S n, F z ∂μH[2] := by
      intro n
      rw [← MeasureTheory.lintegral_indicator (hS_meas n)]
      apply MeasureTheory.lintegral_congr
      intro z
      by_cases hz : z ∈ S n <;>
        simp [contribution, S, F, p, hz]
    have hregular :
        (∫⁻ z in R, F z ∂μH[2]) = ∑' n, contribution n x := by
      calc
        (∫⁻ z in R, F z ∂μH[2])
            = ∫⁻ z in ⋃ n, S n, F z ∂μH[2] := by rw [hS_union]
        _ = ∑' n, ∫⁻ z in S n, F z ∂μH[2] :=
          MeasureTheory.lintegral_iUnion hS_meas hS_pairwise F
        _ = ∑' n, contribution n x := by
          apply tsum_congr
          intro n
          exact (hcontribution_set n).symm
    have hzero_meas : MeasurableSet (polynomialZeroSet p) :=
      measurableSet_polynomialZeroSet p
    have hgradzero_meas :
        MeasurableSet {z : Point 3 | polynomialGradient p z = 0} :=
      (polynomialGradient_continuous p).measurable (MeasurableSet.singleton 0)
    have hR_meas : MeasurableSet R := by
      have hmeas :=
        (hzero_meas.inter hgradzero_meas.compl).inter hU
      convert hmeas using 1
      ext z
      simp only [R, polynomialZeroSet, Set.mem_setOf_eq, Set.mem_inter_iff,
        Set.mem_compl_iff]
      tauto
    have hZ_meas : MeasurableSet Z := by
      have hmeas :=
        (hzero_meas.inter hgradzero_meas).inter hU
      convert hmeas using 1
      ext z
      simp only [Z, polynomialZeroSet, Set.mem_setOf_eq, Set.mem_inter_iff]
      tauto
    have hfull : polynomialZeroSet p ∩ U = R ∪ Z := by
      ext z
      by_cases hgrad : polynomialGradient p z = 0 <;>
        simp [R, Z, polynomialZeroSet, hgrad]
    have hRZ : Disjoint R Z := by
      exact Set.disjoint_left.mpr fun _ hr hz => hr.2.1 hz.2.1
    have hsingular : (∫⁻ z in Z, F z ∂μH[2]) = 0 := by
      rw [MeasureTheory.setLIntegral_eq_zero_iff hZ_meas hF_meas]
      filter_upwards with z
      intro hz
      exact singular_integrand_zero p u z hz.2.1
    change (∫⁻ z in polynomialZeroSet p ∩ U, F z ∂μH[2]) =
      ∑' n, contribution n x
    rw [hfull, MeasureTheory.lintegral_union hZ_meas hRZ, hsingular,
      add_zero, hregular]
  rw [show (fun x : Coeff =>
      directionalSurfaceArea u (parameterPolynomial P x)
        (polynomialZeroSet (parameterPolynomial P x) ∩ U)) =
      (fun x => ∑' n, contribution n x) by
        funext x
        exact hpointwise x]
  exact hsum

/-- The frozen coefficient-surface measurability statement. The boundedness
hypothesis is not needed for measurability itself. -/
theorem coefficientSurfaceFunctional_aeMeasurable_proof :
    CoefficientSurfaceFunctionalAEMeasurabilityStatement := by
  intro k P U _c hU _hUball u
  exact (coefficient_directionalSurfaceArea_measurable P hU u).ennreal_toReal
    |>.aemeasurable

end Kakeya.CV
