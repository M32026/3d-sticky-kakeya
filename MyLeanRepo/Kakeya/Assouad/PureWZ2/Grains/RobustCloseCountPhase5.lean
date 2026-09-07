import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.RobustCloseCountPhase2
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.LocalAD

/-!
# Phase 5: High-multiplicity subshading extraction

Given a paper tube shading with average multiplicity ≥ A, extract a subshading
where every point has multiplicity ≥ A/2, retaining at least half the mass.

This is the reverse Markov argument: the low-multiplicity region contributes at
most half the mass, so the high-multiplicity region retains at least half.

This provides the fine multiplicity lower bound needed for the transverse
condition (Phase 4) and ultimately the plane map construction.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set ENNReal

attribute [local instance] Classical.propDecidable

/-- Extract a high-multiplicity subshading.

Given `A * volume(S.union) ≤ S.mass` (i.e., average multiplicity ≥ A),
there exists a measurable set `good` where multiplicity ≥ A/2, and
the restricted shading on `good` retains at least half the mass.

Proof: low-multiplicity region {mult < A/2} contributes at most
(A/2) * volume(union) ≤ S.mass / 2, so the high-multiplicity region
contributes at least S.mass / 2.
-/
lemma high_multiplicity_subshading
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    (A : ENNReal)
    (hA_ne_top : A ≠ ⊤)
    (h_vol_ne_top : volume S.union ≠ ⊤)
    (h_mass_ne_top : S.mass ≠ ⊤)
    (h_mass : A * volume S.union ≤ S.mass) :
    ∃ (S' : WZ1PaperTubeShading F),
      PaperIsSubshading S' S ∧
      (∀ p ∈ S'.union, (A / 2) ≤ (S'.pointMultiplicity p : ENNReal)) ∧
      (1 / 2 : ENNReal) * S.mass ≤ S'.mass := by
  classical
  let mult : Point3 → ENNReal := fun p => (S.pointMultiplicity p : ENNReal)
  have h_mult_meas : Measurable mult := pointMultiplicity_measurable S

  have h_union_meas : MeasurableSet S.union := by
    have h : S.union = ⋃ i : Fin F.card, S.carrier i := by
      ext x
      simp [Kakeya.Streamlined.Shading.union]
      <;> tauto
    rw [h]
    exact MeasurableSet.iUnion (fun i => S.measurable_carrier i)

  have h_mult_zero_outside : ∀ p ∉ S.union, mult p = 0 := by
    intro p hp
    have h1 : ∀ i : Fin F.card, p ∉ S.carrier i := by
      intro i
      intro h2
      exact hp ⟨i, h2⟩
    simp [mult, Kakeya.Streamlined.Shading.pointMultiplicity, h1, Finset.filter_false]
    <;> norm_num

  let good : Set Point3 := {p | A / 2 ≤ mult p}
  have h_good_meas : MeasurableSet good := h_mult_meas measurableSet_Ici
  let low : Set Point3 := {p | mult p < A / 2}
  have h_low_meas : MeasurableSet low := h_mult_meas measurableSet_Iio
  let low_eff := low ∩ S.union
  have h_low_eff_meas : MeasurableSet low_eff := h_low_meas.inter h_union_meas

  -- mult = 0 outside S.union, so lintegral over low = lintegral over low_eff
  have h_eq_low : ∫⁻ p in low, mult p = ∫⁻ p in low_eff, mult p := by
    have h_disj : Disjoint low_eff (low \ S.union) := by
      rw [Set.disjoint_left]
      intro x hx1 hx2
      exact hx2.2 hx1.2
    have h_union : low = low_eff ∪ (low \ S.union) := by
      ext x
      simp [low_eff] <;> tauto
    have h_low_diff_meas : MeasurableSet (low \ S.union) := h_low_meas.diff h_union_meas
    have h_zero : ∫⁻ p in (low \ S.union), mult p = 0 := by
      have h1 : ∀ p ∈ (low \ S.union), mult p = 0 := by
        intro p hp
        exact h_mult_zero_outside p hp.2
      have h2 : Set.indicator (low \ S.union) mult = fun (_ : Point3) => (0 : ENNReal) := by
        funext p
        by_cases hp : p ∈ (low \ S.union)
        · have hmp : mult p = 0 := h1 p hp
          simp [hp, hmp]
        · simp [hp]
      rw [←lintegral_indicator h_low_diff_meas, h2]
      simp
    rw [h_union]
    rw [lintegral_union h_low_diff_meas h_disj, h_zero, add_zero]

  -- Low region contributes at most (A/2) * volume(low_eff)
  have h_mass_low : ∫⁻ p in low_eff, mult p ≤ (A / 2) * volume low_eff := by
    have h1 : ∀ p ∈ low_eff, mult p ≤ A / 2 := by
      intro p hp
      exact le_of_lt hp.1
    have h_ind : ∀ p, Set.indicator low_eff mult p ≤ Set.indicator low_eff (fun _ => A / 2) p := by
      intro p
      by_cases hp : p ∈ low_eff
      · simpa [hp] using h1 p hp
      · simp [hp]
    have h2 : ∫⁻ p, Set.indicator low_eff mult p ≤ ∫⁻ p, Set.indicator low_eff (fun _ => A / 2) p :=
      lintegral_mono h_ind
    have h4 : ∫⁻ p in low_eff, mult p = ∫⁻ p, Set.indicator low_eff mult p := by
      rw [lintegral_indicator h_low_eff_meas]
    have h5 : ∫⁻ p in low_eff, (A / 2) = ∫⁻ p, Set.indicator low_eff (fun _ => A / 2) p := by
      rw [lintegral_indicator h_low_eff_meas]
    have h6 : ∫⁻ p in low_eff, (A / 2) = (A / 2) * volume low_eff := setLIntegral_const low_eff (A / 2)
    rw [h4]
    have h7 : ∫⁻ p, Set.indicator low_eff (fun _ => A / 2) p = (A / 2) * volume low_eff := by
      rw [←h5, h6]
    exact h7 ▸ h2

  -- Low region contributes at most S.mass / 2
  have h_mass_low2 : ∫⁻ p in low, mult p ≤ (1 / 2 : ENNReal) * S.mass := by
    calc
      ∫⁻ p in low, mult p = ∫⁻ p in low_eff, mult p := h_eq_low
      _ ≤ (A / 2) * volume low_eff := h_mass_low
      _ ≤ (A / 2) * volume S.union := by
        have hsub : low_eff ⊆ S.union := by
          intro p hp
          exact hp.2
        have hvol : volume low_eff ≤ volume S.union := measure_mono hsub
        have h' : volume low_eff * (A / 2) ≤ volume S.union * (A / 2) := mul_le_mul_right' hvol (A / 2)
        simpa [mul_comm] using h'
      _ = (1 / 2 : ENNReal) * (A * volume S.union) := by
        have hdiv : A / 2 = A * (1 / 2 : ENNReal) := by
          simp [div_eq_mul_inv] <;> ring
        rw [hdiv]
        have h_assoc : A * (1 / 2 : ENNReal) * volume S.union =
                       A * ((1 / 2 : ENNReal) * volume S.union) := by rw [mul_assoc]
        rw [h_assoc]
        have h : A * ((1 / 2 : ENNReal) * volume S.union) =
                   (1 / 2 : ENNReal) * (A * volume S.union) := by
          rw [←mul_assoc, mul_comm A (1 / 2 : ENNReal), mul_assoc]
        exact h
      _ ≤ (1 / 2 : ENNReal) * S.mass := by
        gcongr

  let mass_good : ENNReal := ∫⁻ p in good, mult p
  let mass_low : ENNReal := ∫⁻ p in low, mult p

  -- 2 * mass_low ≤ S.mass
  have h2c : 2 * mass_low ≤ S.mass := by
    have h_half : (2 : ENNReal) * (1 / 2 : ENNReal) = 1 := by
      have h1 : (1 / 2 : ENNReal) = (2 : ENNReal)⁻¹ := by
        simp [one_div]
      rw [h1]
      exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
    have h_mul2 : 2 * ((1 / 2 : ENNReal) * S.mass) = S.mass := by
      rw [←mul_assoc, h_half, one_mul]
    have h : 2 * mass_low ≤ 2 * ((1 / 2 : ENNReal) * S.mass) := by
      gcongr
    rw [h_mul2] at h
    exact h

  -- good and low partition univ
  have h_disj : Disjoint good low := by
    rw [Set.disjoint_left]
    intro p hpg hpl
    have h3 : A / 2 ≤ mult p := by simpa [good] using hpg
    have h4 : mult p < A / 2 := by simpa [low] using hpl
    exact not_le.mpr h4 h3
  have h_univ : (good ∪ low : Set Point3) = Set.univ := by
    ext p
    simp only [good, low, Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    by_cases h : A / 2 ≤ mult p
    · exact Or.inl h
    · exact Or.inr (lt_of_not_ge h)

  -- S.mass = mass_good + mass_low
  have h_mass_split : S.mass = mass_good + mass_low := by
    have h1 : (∫⁻ p, mult p) = S.mass := lintegral_pointMultiplicity_eq_mass S
    have h4 : ∫⁻ p in (good ∪ low), mult p = mass_good + mass_low :=
      lintegral_union h_low_meas h_disj
    have h5 : ∫⁻ p, mult p = ∫⁻ p in (Set.univ), mult p := by simp
    have h6 : ∫⁻ p in (Set.univ), mult p = ∫⁻ p in (good ∪ low), mult p := by
      rw [h_univ]
    rw [h1.symm, h5, h6, h4]

  -- S.mass ≤ 2 * mass_good
  have h_final : S.mass ≤ 2 * mass_good := by
    have h : S.mass + S.mass ≤ S.mass + 2 * mass_good := by
      have h_eq2 : S.mass + S.mass = 2 * mass_good + 2 * mass_low := by
        have h1 : S.mass + S.mass = 2 * S.mass := by rw [←two_mul]
        rw [h1, h_mass_split, mul_add]
        <;> rfl
      rw [h_eq2]
      rw [add_comm (2 * mass_good) (2 * mass_low)]
      exact add_le_add_left h2c (2 * mass_good)
    exact (ENNReal.add_le_add_iff_left h_mass_ne_top).mp h

  let S' : WZ1PaperTubeShading F :=
    paperRestrictShadingToSet S good h_good_meas
  have hsub : PaperIsSubshading S' S := by
    intro i p hp
    exact hp.1

  have h_mult_eq : ∀ p ∈ good, (S'.pointMultiplicity p : ENNReal) = mult p := by
    intro p hp
    have h1 : ∀ i : Fin F.card, p ∈ S'.carrier i ↔ p ∈ S.carrier i := by
      intro i
      simp [S', paperRestrictShadingToSet, hp] <;> tauto
    have h2 : (Finset.univ.filter fun j : Fin F.card => p ∈ S'.carrier j) =
             (Finset.univ.filter fun j : Fin F.card => p ∈ S.carrier j) := by
      apply Finset.ext
      intro j
      simpa using h1 j
    have h3 : S'.pointMultiplicity p = S.pointMultiplicity p := by
      dsimp only [Kakeya.Streamlined.Shading.pointMultiplicity]
      exact congr_arg Finset.card h2
    have h4 : (S'.pointMultiplicity p : ENNReal) = (S.pointMultiplicity p : ENNReal) := by
      exact_mod_cast h3
    have h5 : (S.pointMultiplicity p : ENNReal) = mult p := by rfl
    rw [h4, h5]

  have h_high_mult : ∀ p ∈ S'.union, (A / 2) ≤ (S'.pointMultiplicity p : ENNReal) := by
    intro p hp
    have hpg : p ∈ good := by
      rcases hp with ⟨i, hi⟩
      simpa [S', paperRestrictShadingToSet] using hi.2
    have h3 : (A / 2) ≤ mult p := by simpa [good] using hpg
    rw [h_mult_eq p hpg]
    exact h3

  have h_mass_S' : S'.mass = mass_good := by
    have h1 : (∫⁻ p, (S'.pointMultiplicity p : ENNReal)) = S'.mass :=
      lintegral_pointMultiplicity_eq_mass S'
    have h1' : S'.mass = ∫⁻ p, (S'.pointMultiplicity p : ENNReal) := h1.symm
    rw [h1']
    have h2 : (fun p : Point3 => (S'.pointMultiplicity p : ENNReal)) =
        fun p => if p ∈ good then mult p else 0 := by
      funext p
      by_cases hpg : p ∈ good
      · rw [if_pos hpg, h_mult_eq p hpg]
      · rw [if_neg hpg]
        have h3 : p ∉ S'.union := by
          intro h4
          rcases h4 with ⟨i, hi⟩
          exact hpg (by simpa [S', paperRestrictShadingToSet] using hi.2)
        have h4 : S'.pointMultiplicity p = 0 := by
          have h5 : ∀ i : Fin F.card, p ∉ S'.carrier i := by
            intro i
            intro h6
            have h7 : p ∈ S'.union := ⟨i, h6⟩
            exact h3 h7
          simp [Kakeya.Streamlined.Shading.pointMultiplicity, h5]
        exact_mod_cast h4
    rw [h2]
    have h3 : (fun p : Point3 => (if p ∈ good then mult p else 0)) =
        Set.indicator good mult := by
      funext p
      simp [Set.indicator_apply] <;> split_ifs <;> tauto
    rw [h3]
    rw [lintegral_indicator h_good_meas] <;> rfl

  have h_final2 : (1 / 2 : ENNReal) * S.mass ≤ mass_good := by
    have h : S.mass ≤ 2 * mass_good := h_final
    have h' : (1 / 2 : ENNReal) * S.mass ≤ (1 / 2 : ENNReal) * (2 * mass_good) := by
      gcongr
    have h'' : (1 / 2 : ENNReal) * (2 * mass_good) = mass_good := by
      have h3 : (1 / 2 : ENNReal) * (2 * mass_good) = ((1 / 2 : ENNReal) * 2) * mass_good := by
        rw [mul_assoc]
      rw [h3]
      have h4 : (1 / 2 : ENNReal) * 2 = 1 := by
        have h5 : (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2 : ℝ) := by simp
        rw [h5]
        have h6 : ENNReal.ofReal (1 / 2 : ℝ) * (2 : ENNReal) = ENNReal.ofReal ((1 / 2 : ℝ) * 2) := by
          rw [ENNReal.ofReal_mul (by norm_num)] <;> norm_cast
        rw [h6] <;> norm_num
      rw [h4, one_mul]
    rw [h''] at h'
    exact h'

  exact ⟨S', hsub, h_high_mult, by
    rw [h_mass_S']
    exact h_final2⟩

end Kakeya.Assouad.PureWZ2
