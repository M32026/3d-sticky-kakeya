import MyLeanRepo.Kakeya.Assouad.PureWZ2.PropSticky
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2PaperStatements
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.RobustCloseCountPhase1

/-!
# Phase 2: Markov fiber cap

Given a balanced cover with cellMass, restrict the fine shading to a "good" set
where fiber point multiplicity is bounded by 2 * average.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set Finset

attribute [local instance] Classical.propDecidable

/-- Fiber point multiplicity: number of fine tubes in parent's fiber containing p. -/
def fiberPointMultiplicity
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : PureWZ2Section6Cover fine coarse)
    (fineShading : WZ1PaperTubeShading fine)
    (parent : Fin coarse.card)
    (p : Point3) : ℕ :=
  (univ.filter fun i : Fin fine.card =>
    selectParent cover i = parent ∧ p ∈ fineShading.carrier i).card

/-- Fiber multiplicity ≤ total point multiplicity. -/
lemma fiberMultiplicity_le_total
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {parent : Fin coarse.card}
    {p : Point3} :
    (fiberPointMultiplicity cover fineShading parent p : ENNReal) ≤
      (fineShading.pointMultiplicity p : ENNReal) := by
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro i hi
  have h := mem_filter.mp hi
  exact mem_filter.mpr ⟨mem_univ i, h.2.2⟩

/-- The indicator function as ENNReal. -/
private def ennrealIndicator (s : Set Point3) (p : Point3) : ENNReal :=
  Set.indicator s (fun _ => (1 : ENNReal)) p

/-- Point multiplicity is measurable. -/
lemma pointMultiplicity_measurable
    {F : Kakeya.Streamlined.BodyFamily}
    (Y : Kakeya.Streamlined.Shading F) :
    Measurable fun p : Point3 => (Y.pointMultiplicity p : ENNReal) := by
  have h1 : (fun p : Point3 => (Y.pointMultiplicity p : ENNReal)) =
      fun p => ∑ i : Fin F.card, ennrealIndicator (Y.carrier i) p := by
    funext p
    simp [Kakeya.Streamlined.Shading.pointMultiplicity, ennrealIndicator, Set.indicator_apply]
    <;> norm_cast
  rw [h1]
  apply Finset.measurable_sum
  intro i _
  have h_ind : Measurable (ennrealIndicator (Y.carrier i)) := by
    unfold ennrealIndicator
    exact (measurable_const).indicator (Y.measurable_carrier i)
  exact h_ind

/-- Lintegral of point multiplicity equals shading mass. -/
lemma lintegral_pointMultiplicity_eq_mass
    {F : Kakeya.Streamlined.BodyFamily}
    (Y : Kakeya.Streamlined.Shading F) :
    ∫⁻ p, (Y.pointMultiplicity p : ENNReal) = Y.mass := by
  have h1 : (fun p : Point3 => (Y.pointMultiplicity p : ENNReal)) =
      fun p => ∑ i : Fin F.card, ennrealIndicator (Y.carrier i) p := by
    funext p
    simp [Kakeya.Streamlined.Shading.pointMultiplicity, ennrealIndicator, Set.indicator_apply]
    <;> norm_cast
  rw [h1]
  have h_meas : ∀ i ∈ Finset.univ, Measurable (ennrealIndicator (Y.carrier i)) := by
    intro i _
    unfold ennrealIndicator
    exact (measurable_const).indicator (Y.measurable_carrier i)
  rw [MeasureTheory.lintegral_finsetSum Finset.univ h_meas]
  have h2 : ∑ i : Fin F.card, ∫⁻ p, ennrealIndicator (Y.carrier i) p =
      ∑ i : Fin F.card, volume (Y.carrier i) := by
    apply Finset.sum_congr rfl
    intro i _
    have h3 : ∫⁻ p, ennrealIndicator (Y.carrier i) p = volume (Y.carrier i) := by
      unfold ennrealIndicator
      rw [lintegral_indicator (Y.measurable_carrier i)]
      <;> simp
    exact h3
  rw [h2]
  rfl

/-- Markov restriction: restrict shading to points where point multiplicity ≤ 2*A. -/
lemma markov_multiplicity_restriction
    {F : Kakeya.Streamlined.BodyFamily}
    (Y : Kakeya.Streamlined.Shading F)
    (V A : ENNReal)
    (hV_ne_top : V ≠ ⊤)
    (hA_pos : 0 < A)
    (hA_ne_top : A ≠ ⊤)
    (h_mass : Y.mass ≤ A * V) :
    ∃ (bad : Set Point3),
      MeasurableSet bad ∧
      volume bad ≤ V / 2 ∧
      (∀ p ∉ bad, (Y.pointMultiplicity p : ENNReal) ≤ 2 * A) := by
  let f : Point3 → ENNReal := fun p => (Y.pointMultiplicity p : ENNReal)
  have hf_meas : Measurable f := pointMultiplicity_measurable Y
  have h_mass' : ∫⁻ p, f p = Y.mass := lintegral_pointMultiplicity_eq_mass Y
  set t : ENNReal := 2 * A with ht
  have ht_ne_zero : t ≠ 0 := by
    simp [ht, hA_pos.ne']
  have ht_ne_top : t ≠ ⊤ := by
    rw [ht]
    exact ENNReal.mul_ne_top (by norm_num) hA_ne_top
  let bad : Set Point3 := {p | t ≤ f p}
  have hbad_meas : MeasurableSet bad := hf_meas measurableSet_Ici
  have h_markov : volume bad ≤ (∫⁻ p, f p) / t :=
    MeasureTheory.meas_ge_le_lintegral_div hf_meas.aemeasurable ht_ne_zero ht_ne_top
  have h_div : (A * V) / t = V / 2 := by
    rw [ht]
    have h10 : (A * V) / (2 * A) = V / 2 := by
      have h11 : (2 * A) = A * 2 := by ring
      rw [h11]
      rw [ENNReal.mul_div_mul_left _ _ hA_pos.ne' hA_ne_top]
      <;> ring
    exact h10
  have h_main : volume bad ≤ V / 2 := by
    calc
      volume bad ≤ Y.mass / t := by rw [h_mass'] at h_markov; exact h_markov
      _ ≤ (A * V) / t := by gcongr
      _ = V / 2 := h_div
  have h_good : ∀ p ∉ bad, f p ≤ 2 * A := by
    intro p hp
    have h : ¬(t ≤ f p) := by simpa [bad] using hp
    have h' : f p < t := lt_of_not_ge h
    rw [ht] at h'
    exact le_of_lt h'
  exact ⟨bad, hbad_meas, h_main, h_good⟩

/-- Construct a restricted shading by removing a bad set from each carrier. -/
def restrictShading
    {F : Kakeya.Streamlined.BodyFamily}
    (Y : Kakeya.Streamlined.Shading F)
    (bad : Set Point3)
    (hbad_meas : MeasurableSet bad) :
    Kakeya.Streamlined.Shading F :=
  { carrier := fun i => Y.carrier i \ bad
    measurable_carrier := fun i =>
      (Y.measurable_carrier i).diff hbad_meas
    subset_body := fun i =>
      Set.sdiff_subset.trans (Y.subset_body i) }

/-- The restricted shading is a subshading. -/
lemma restrictShading_subshading
    {F : Kakeya.Streamlined.BodyFamily}
    (Y : Kakeya.Streamlined.Shading F)
    (bad : Set Point3)
    (hbad_meas : MeasurableSet bad) :
    ∀ i, (restrictShading Y bad hbad_meas).carrier i ⊆ Y.carrier i := by
  intro i
  exact Set.sdiff_subset

/-- Point multiplicity of restricted shading ≤ original. -/
lemma restrictShading_pointMultiplicity_le
    {F : Kakeya.Streamlined.BodyFamily}
    (Y : Kakeya.Streamlined.Shading F)
    (bad : Set Point3)
    (hbad_meas : MeasurableSet bad)
    (p : Point3) :
    (restrictShading Y bad hbad_meas).pointMultiplicity p ≤
      Y.pointMultiplicity p := by
  apply Finset.card_le_card
  intro i hi
  have h := mem_filter.mp hi
  exact mem_filter.mpr ⟨mem_univ i, Set.sdiff_subset (h.2)⟩

/-- On good points, restricted fiber multiplicity ≤ 2*A. -/
lemma markov_fiber_cap
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {V A : ENNReal}
    {bad : Set Point3}
    {hbad_meas : MeasurableSet bad}
    (h_good : ∀ p ∉ bad, (fineShading.pointMultiplicity p : ENNReal) ≤ 2 * A)
    (parent : Fin coarse.card)
    (p : Point3)
    (hp : p ∉ bad) :
    (fiberPointMultiplicity cover
      (restrictShading fineShading bad hbad_meas) parent p : ENNReal) ≤ 2 * A := by
  have h1 : (fiberPointMultiplicity cover
        (restrictShading fineShading bad hbad_meas) parent p : ENNReal) ≤
      ((restrictShading fineShading bad hbad_meas).pointMultiplicity p : ENNReal) :=
    fiberMultiplicity_le_total
  have h2 : ((restrictShading fineShading bad hbad_meas).pointMultiplicity p : ENNReal) ≤
      (fineShading.pointMultiplicity p : ENNReal) := by
    exact_mod_cast restrictShading_pointMultiplicity_le fineShading bad hbad_meas p
  exact le_trans h1 (le_trans h2 (h_good p hp))

end Kakeya.Assouad.PureWZ2
