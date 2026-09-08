import MyLeanRepo.Kakeya.Streamlined.Estimates
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.Submultiplicativity

/-!
# Inequality form of the Frostman constant

The definition of `BodyFamily.frostmanConstantIn` is a supremum of density
ratios.  The Section 7 submultiplicativity argument needs the equivalent
pointwise inequality

`density K ≤ C * density U`

for every convex `K ⊆ U`.  This module supplies both directions with the
necessary nonzero and finiteness assumptions on the reference density.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Streamlined

namespace BodyFamily

/-- Every admissible density ratio is bounded by the Frostman constant. -/
lemma density_div_density_le_frostmanConstantIn
    (F : BodyFamily) {U K : Set Point3}
    (hK : Convex ℝ K) (hKU : K ⊆ U) :
    F.density K / F.density U ≤ F.frostmanConstantIn U := by
  apply le_csSup
  · exact ⟨⊤, fun _ _ => le_top⟩
  · exact ⟨K, hK, hKU, rfl⟩

/--
An upper bound for the Frostman constant gives the corresponding pointwise
density inequality.
-/
lemma density_le_mul_of_frostmanConstantIn_le
    (F : BodyFamily) {U K : Set Point3} {C : ENNReal}
    (hU_zero : F.density U ≠ 0)
    (hU_top : F.density U ≠ ⊤)
    (hC : F.frostmanConstantIn U ≤ C)
    (hK : Convex ℝ K) (hKU : K ⊆ U) :
    F.density K ≤ C * F.density U := by
  have hratio :
      F.density K / F.density U ≤ C :=
    (F.density_div_density_le_frostmanConstantIn hK hKU).trans hC
  exact (ENNReal.div_le_iff hU_zero hU_top).mp hratio

/--
Pointwise density control on all convex subsets gives an upper bound for the
Frostman constant.
-/
lemma frostmanConstantIn_le_of_density_le_mul
    (F : BodyFamily) {U : Set Point3} {C : ENNReal}
    (hU_zero : F.density U ≠ 0)
    (hU_top : F.density U ≠ ⊤)
    (hcontrol :
      ∀ K : Set Point3, Convex ℝ K → K ⊆ U →
        F.density K ≤ C * F.density U) :
    F.frostmanConstantIn U ≤ C := by
  let S : Set ENNReal :=
    {c | ∃ K : Set Point3, Convex ℝ K ∧ K ⊆ U ∧
      c = F.density K / F.density U}
  have hS_nonempty : S.Nonempty := by
    have hempty : F.containedMass (∅ : Set Point3) = 0 := by
      classical
      dsimp only [BodyFamily.containedMass]
      apply Finset.sum_eq_zero
      intro i hi
      have hsub :
          (F.body i).carrier ⊆ (∅ : Set Point3) :=
        (Finset.mem_filter.mp hi).2
      have heq : (F.body i).carrier = ∅ := by
        simpa using hsub
      simp [Body.volume, heq]
    refine ⟨0, ∅, convex_empty, Set.empty_subset U, ?_⟩
    simp [BodyFamily.density, hempty]
  change sSup S ≤ C
  apply csSup_le hS_nonempty
  rintro c ⟨K, hK, hKU, rfl⟩
  exact (ENNReal.div_le_iff hU_zero hU_top).mpr
    (hcontrol K hK hKU)

/--
For positive finite reference density, `IsCFrostmanIn` is equivalent to the
pointwise density inequality on convex subsets.
-/
lemma isCFrostmanIn_iff_density_le_mul
    (F : BodyFamily) {U : Set Point3} {C : ENNReal}
    (hU_zero : F.density U ≠ 0)
    (hU_top : F.density U ≠ ⊤) :
    F.IsCFrostmanIn U C ↔
      ∀ K : Set Point3, Convex ℝ K → K ⊆ U →
        F.density K ≤ C * F.density U := by
  constructor
  · intro h K hK hKU
    exact F.density_le_mul_of_frostmanConstantIn_le
      hU_zero hU_top h hK hKU
  · intro h
    exact F.frostmanConstantIn_le_of_density_le_mul
      hU_zero hU_top h

/--
If every body of `F` lies in a convex reference set `U`, then maximal density
is bounded by the Frostman constant in `U` times the reference density.
-/
lemma deltaMax_le_frostmanConstantIn_mul_density
    (F : BodyFamily) {U : Set Point3}
    (hU : Convex ℝ U)
    (hall : ∀ i, (F.body i).carrier ⊆ U)
    (hU_zero : F.density U ≠ 0)
    (hU_top : F.density U ≠ ⊤) :
    F.deltaMax ≤ F.frostmanConstantIn U * F.density U := by
  dsimp only [BodyFamily.deltaMax]
  apply csSup_le
    (by
      exact ⟨0, Set.univ, convex_univ,
        by simp [BodyFamily.density]⟩)
  rintro d ⟨K, hK, rfl⟩
  let L := K ∩ U
  have hL : Convex ℝ L := hK.inter hU
  have hLU : L ⊆ U := Set.inter_subset_right
  have hindices :
      F.containedIndices K = F.containedIndices L := by
    ext i
    simp only [BodyFamily.containedIndices, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · intro hi
      exact fun x hx => ⟨hi hx, hall i hx⟩
    · intro hi
      exact hi.trans Set.inter_subset_left
  have hmass :
      F.containedMass K = F.containedMass L := by
    dsimp only [BodyFamily.containedMass]
    rw [hindices]
  have hvolume :
      volume L ≤ volume K :=
    measure_mono Set.inter_subset_left
  have hdensity :
      F.density K ≤ F.density L := by
    dsimp only [BodyFamily.density]
    rw [hmass]
    exact ENNReal.div_le_div le_rfl hvolume
  exact hdensity.trans <|
    F.density_le_mul_of_frostmanConstantIn_le
      hU_zero hU_top le_rfl hL hLU

/--
Cross-multiplied Frostman mass inequality.  The test set may have zero
volume; finiteness follows from `K ⊆ U`.
-/
lemma containedMass_mul_volume_le_of_frostmanConstantIn_le
    (F : BodyFamily) {U K : Set Point3} {C : ENNReal}
    (hU_zero : volume U ≠ 0)
    (hU_top : volume U ≠ ⊤)
    (hMassU_zero : F.containedMass U ≠ 0)
    (hMassU_top : F.containedMass U ≠ ⊤)
    (hC : F.frostmanConstantIn U ≤ C)
    (hK : Convex ℝ K) (hKU : K ⊆ U) :
    F.containedMass K * volume U ≤
      C * F.containedMass U * volume K := by
  classical
  have hDensityU_zero : F.density U ≠ 0 := by
    exact ENNReal.div_ne_zero.mpr ⟨hMassU_zero, hU_top⟩
  have hDensityU_top : F.density U ≠ ⊤ := by
    exact ENNReal.div_ne_top hMassU_top hU_zero
  have hdensity :
      F.density K ≤ C * F.density U :=
    F.density_le_mul_of_frostmanConstantIn_le
      hDensityU_zero hDensityU_top hC hK hKU
  by_cases hK_zero : volume K = 0
  · have hMassK_zero : F.containedMass K = 0 := by
      dsimp only [BodyFamily.containedMass]
      apply Finset.sum_eq_zero
      intro i hi
      have hsub :
          (F.body i).carrier ⊆ K :=
        (Finset.mem_filter.mp hi).2
      have hvolume :
          (F.body i).volume ≤ volume K :=
        measure_mono hsub
      rw [hK_zero] at hvolume
      simpa using hvolume
    simp [hMassK_zero, hK_zero]
  · have hK_top : volume K ≠ ⊤ :=
      ne_top_of_le_ne_top hU_top (measure_mono hKU)
    dsimp only [BodyFamily.density] at hdensity
    have hmass :
        F.containedMass K ≤
          (C * (F.containedMass U / volume U)) * volume K :=
      (ENNReal.div_le_iff hK_zero hK_top).mp hdensity
    have hmul :
        F.containedMass K * volume U ≤
          ((C * (F.containedMass U / volume U)) * volume K) *
            volume U :=
      mul_le_mul_right' hmass _
    calc
      F.containedMass K * volume U
          ≤ ((C * (F.containedMass U / volume U)) * volume K) *
              volume U := hmul
      _ = C * F.containedMass U * volume K := by
        have hcancel :
            F.containedMass U / volume U * volume U =
              F.containedMass U :=
          ENNReal.div_mul_cancel hU_zero hU_top
        calc
          ((C * (F.containedMass U / volume U)) * volume K) *
                volume U
              = C * (F.containedMass U / volume U * volume U) *
                  volume K := by
                ring
          _ = C * F.containedMass U * volume K := by
            rw [hcancel]

/--
The cross-multiplied pointwise inequalities recover an upper bound for the
Frostman constant.
-/
lemma frostmanConstantIn_le_of_containedMass_mul_volume_le
    (F : BodyFamily) {U : Set Point3} {C : ENNReal}
    (hU_zero : volume U ≠ 0)
    (hU_top : volume U ≠ ⊤)
    (hMassU_zero : F.containedMass U ≠ 0)
    (hMassU_top : F.containedMass U ≠ ⊤)
    (hcontrol :
      ∀ K : Set Point3, Convex ℝ K → K ⊆ U →
        F.containedMass K * volume U ≤
          C * F.containedMass U * volume K) :
    F.frostmanConstantIn U ≤ C := by
  classical
  have hDensityU_zero : F.density U ≠ 0 :=
    ENNReal.div_ne_zero.mpr ⟨hMassU_zero, hU_top⟩
  have hDensityU_top : F.density U ≠ ⊤ :=
    ENNReal.div_ne_top hMassU_top hU_zero
  apply F.frostmanConstantIn_le_of_density_le_mul
    hDensityU_zero hDensityU_top
  intro K hK hKU
  by_cases hK_zero : volume K = 0
  · have hMassK_zero : F.containedMass K = 0 := by
      dsimp only [BodyFamily.containedMass]
      apply Finset.sum_eq_zero
      intro i hi
      have hsub :
          (F.body i).carrier ⊆ K :=
        (Finset.mem_filter.mp hi).2
      have hvolume :
          (F.body i).volume ≤ volume K :=
        measure_mono hsub
      rw [hK_zero] at hvolume
      simpa using hvolume
    simp [BodyFamily.density, hMassK_zero, hK_zero]
  · have hK_top : volume K ≠ ⊤ :=
      ne_top_of_le_ne_top hU_top (measure_mono hKU)
    have hcross := hcontrol K hK hKU
    have hdivide :
        F.containedMass K ≤
          (C * F.containedMass U * volume K) / volume U := by
      exact
        (ENNReal.le_div_iff_mul_le
          (Or.inl hU_zero) (Or.inl hU_top)).2 hcross
    dsimp only [BodyFamily.density]
    apply (ENNReal.div_le_iff hK_zero hK_top).2
    calc
      F.containedMass K
          ≤ (C * F.containedMass U * volume K) /
              volume U := hdivide
      _ = (C * (F.containedMass U / volume U)) *
            volume K := by
        simp [div_eq_mul_inv]
        ring

/--
Transfer a cross-multiplied Frostman estimate from an ambient reference
family and container to a local family and container.

The hypotheses isolate the two quantities that a multiscale argument must
pay:

* `volume V ≤ q * volume U`;
* `q * C * ambientMass ≤ D * localMass`.
-/
lemma frostmanConstantIn_le_of_cross_container
    (F G : BodyFamily) {U V : Set Point3}
    {C q D : ENNReal}
    (hV_zero : volume V ≠ 0)
    (hV_top : volume V ≠ ⊤)
    (hMassV_zero : G.containedMass V ≠ 0)
    (hMassV_top : G.containedMass V ≠ ⊤)
    (hvolume : volume V ≤ q * volume U)
    (hreference :
      q * C * F.containedMass U ≤
        D * G.containedMass V)
    (hambient :
      ∀ K : Set Point3, Convex ℝ K → K ⊆ V →
        G.containedMass K * volume U ≤
          C * F.containedMass U * volume K) :
    G.frostmanConstantIn V ≤ D := by
  apply G.frostmanConstantIn_le_of_containedMass_mul_volume_le
    hV_zero hV_top hMassV_zero hMassV_top
  intro K hK hKV
  have hambientK := hambient K hK hKV
  calc
    G.containedMass K * volume V
        ≤ G.containedMass K * (q * volume U) := by
      exact mul_le_mul_left' hvolume _
    _ = q * (G.containedMass K * volume U) := by
      ring
    _ ≤ q * (C * F.containedMass U * volume K) := by
      exact mul_le_mul_left' hambientK _
    _ = (q * C * F.containedMass U) * volume K := by
      ring
    _ ≤ (D * G.containedMass V) * volume K := by
      exact mul_le_mul_right' hreference _
    _ = D * G.containedMass V * volume K := by
      ring

/--
Enlarging the reference container costs at most its volume ratio, provided
all family members already lie in the smaller container.
-/
lemma frostmanConstantIn_mono_container
    (F : BodyFamily) {U V : Set Point3}
    (hU_convex : Convex ℝ U)
    (hV_convex : Convex ℝ V)
    (hUV : U ⊆ V)
    (hall : ∀ i, (F.body i).carrier ⊆ U)
    (hU_zero : volume U ≠ 0)
    (hU_top : volume U ≠ ⊤)
    (hV_zero : volume V ≠ 0)
    (hV_top : volume V ≠ ⊤)
    (hMass_zero : F.mass ≠ 0)
    (hMass_top : F.mass ≠ ⊤) :
    F.frostmanConstantIn V ≤
      (volume V / volume U) * F.frostmanConstantIn U := by
  classical
  have hMassU :
      F.containedMass U = F.mass := by
    have hindices : F.containedIndices U = Finset.univ := by
      ext i
      simp [BodyFamily.containedIndices, hall i]
    dsimp only [BodyFamily.containedMass, BodyFamily.mass]
    rw [hindices]
  have hMassV :
      F.containedMass V = F.mass := by
    have hindices : F.containedIndices V = Finset.univ := by
      ext i
      simp [BodyFamily.containedIndices, (hall i).trans hUV]
    dsimp only [BodyFamily.containedMass, BodyFamily.mass]
    rw [hindices]
  apply F.frostmanConstantIn_le_of_containedMass_mul_volume_le
    hV_zero hV_top
    (by simpa [hMassV] using hMass_zero)
    (by simpa [hMassV] using hMass_top)
  intro K hK hKV
  let L := K ∩ U
  have hL : Convex ℝ L :=
    hK.inter hU_convex
  have hLU : L ⊆ U :=
    Set.inter_subset_right
  have hindices :
      F.containedIndices K = F.containedIndices L := by
    ext i
    simp only [BodyFamily.containedIndices, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · intro hi
      exact fun x hx => ⟨hi hx, hall i hx⟩
    · intro hi
      exact hi.trans Set.inter_subset_left
  have hmass :
      F.containedMass K = F.containedMass L := by
    dsimp only [BodyFamily.containedMass]
    rw [hindices]
  have hsmall :=
    F.containedMass_mul_volume_le_of_frostmanConstantIn_le
      hU_zero hU_top
      (by simpa [hMassU] using hMass_zero)
      (by simpa [hMassU] using hMass_top)
      le_rfl hL hLU
  have hL_volume : volume L ≤ volume K :=
    measure_mono Set.inter_subset_left
  rw [hmass]
  calc
    F.containedMass L * volume V
        = (F.containedMass L * volume U) *
            (volume V / volume U) := by
      rw [mul_assoc]
      rw [ENNReal.mul_div_cancel hU_zero hU_top]
    _ ≤ (F.frostmanConstantIn U * F.containedMass U *
            volume L) *
          (volume V / volume U) := by
      exact mul_le_mul_right' hsmall _
    _ ≤ (F.frostmanConstantIn U * F.containedMass U *
            volume K) *
          (volume V / volume U) := by
      exact mul_le_mul_right'
        (mul_le_mul_left' hL_volume
          (F.frostmanConstantIn U * F.containedMass U)) _
    _ = ((volume V / volume U) *
            F.frostmanConstantIn U) *
          F.containedMass V * volume K := by
      rw [hMassU, hMassV]
      ring

/--
Quantitative transfer of a Frostman constant to a subfamily.

If `G` is a subfamily of `F` and its reference mass in `U` is at least the
fraction `m` of the ambient reference mass, then
`C_F(G,U) ≤ C_F(F,U) / m`.
-/
lemma subfamily_frostmanConstantIn_le_div
    {F G : BodyFamily} {embed : Fin G.card → Fin F.card}
    (hinj : Function.Injective embed)
    (hcarrier :
      ∀ i, (G.body i).carrier = (F.body (embed i)).carrier)
    {U : Set Point3} {m : ENNReal}
    (hm_zero : m ≠ 0) (hm_top : m ≠ ⊤)
    (hFU_zero : F.density U ≠ 0)
    (hFU_top : F.density U ≠ ⊤)
    (hGU_zero : G.density U ≠ 0)
    (hGU_top : G.density U ≠ ⊤)
    (hmass :
      m * F.containedMass U ≤ G.containedMass U) :
    G.frostmanConstantIn U ≤ F.frostmanConstantIn U / m := by
  apply G.frostmanConstantIn_le_of_density_le_mul
    hGU_zero hGU_top
  intro K hK _hKU
  have hcontained :
      G.containedMass K ≤ F.containedMass K :=
    BodyFamily.subfamily_containedMass_le
      hinj hcarrier K
  have hFcontrol :
      F.density K ≤
        F.frostmanConstantIn U * F.density U :=
    F.density_le_mul_of_frostmanConstantIn_le
      hFU_zero hFU_top le_rfl hK _hKU
  have hmass_density :
      m * F.density U ≤ G.density U := by
    dsimp only [BodyFamily.density]
    calc
      m * (F.containedMass U / volume U)
          = (m * F.containedMass U) / volume U := by
        simp [div_eq_mul_inv]
        ring
      _ ≤ G.containedMass U / volume U := by
        exact ENNReal.div_le_div hmass le_rfl
  have hscale :
      F.density U ≤ G.density U / m := by
    exact
      (ENNReal.le_div_iff_mul_le
        (Or.inl hm_zero) (Or.inl hm_top)).2
        (by simpa [mul_comm] using hmass_density)
  calc
    G.density K
        ≤ F.density K := by
      dsimp only [BodyFamily.density]
      exact ENNReal.div_le_div hcontained le_rfl
    _ ≤ F.frostmanConstantIn U * F.density U := hFcontrol
    _ ≤ F.frostmanConstantIn U * (G.density U / m) := by
      gcongr
    _ = (F.frostmanConstantIn U / m) * G.density U := by
      simp [div_eq_mul_inv]
      ring

end BodyFamily

end Kakeya.Streamlined
