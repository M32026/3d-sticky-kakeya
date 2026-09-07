import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushStatements
import MyLeanRepo.Kakeya.Assouad.HairbrushBalancedBroadDecomposition.MaxScoreBroadness
import MyLeanRepo.Kakeya.Assouad.HairbrushBalancedBroadDecomposition.DyadicPigeonhole
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Data.ENNReal.Basic

/-!
# Mass retention via dyadic pigeonholing

Partition the shaded union by the exact through-subfamily at each point.
For each nonempty through-subfamily, the max-score lemma gives a local scale.
Dyadically pigeonhole these scales to find a common `theta` retaining at least
`δ^eps` of the total mass, while preserving exact two-broadness.
-/

noncomputable section

open MeasureTheory Set Finset

attribute [local instance] Classical.propDecidable

namespace Kakeya.Assouad

section MassRetention

variable {δ eta eps : ℝ} {F : Kakeya.TubeFamily δ}

/-- The set of points whose through-subfamily is exactly `S`. -/
def throughPattern (Y : Kakeya.Shading F)
    (S : Finset (Kakeya.DeltaTube δ)) : Set Point3 :=
  {x ∈ Y.union | F.filter (fun T => x ∈ Y.carrier T) = S}

lemma throughPattern_measurable (Y : Kakeya.Shading F)
    {S : Finset (Kakeya.DeltaTube δ)} (hS : S ∈ F.powerset) :
    MeasurableSet (throughPattern Y S) := by
  have hS_sub : S ⊆ F := Finset.mem_powerset.mp hS
  have h1 : MeasurableSet Y.union := by
    have h_union_eq : Y.union = ⋃ T ∈ F, Y.carrier T := by
      ext x
      simp [Kakeya.Shading.union]
      <;> tauto
    rw [h_union_eq]
    exact Finset.measurableSet_biUnion F (fun T _ => Y.measurable_carrier (by assumption))
  let S' : Set (Kakeya.DeltaTube δ) := ↑S
  let FS' : Set (Kakeya.DeltaTube δ) := ↑(F \ S)
  have h2 : MeasurableSet {x | F.filter (fun T => x ∈ Y.carrier T) = S} := by
    have h_eq : {x : Point3 | F.filter (fun T => x ∈ Y.carrier T) = S} =
        (⋂ T ∈ S', Y.carrier T) ∩ (⋂ T ∈ FS', (Y.carrier T)ᶜ) := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff, S', FS']
      constructor
      · intro h
        have h4 : F.filter (fun T => x ∈ Y.carrier T) = S := h
        have h5 : ∀ T ∈ S, x ∈ Y.carrier T := by
          intro T hT
          have h6 : T ∈ F.filter (fun T => x ∈ Y.carrier T) := by
            rw [h4] <;> exact hT
          exact (Finset.mem_filter.mp h6).2
        have h6 : ∀ T ∈ F \ S, x ∉ Y.carrier T := by
          intro T hT
          have h7 : T ∈ F := (Finset.mem_sdiff.mp hT).1
          have h8 : T ∉ S := (Finset.mem_sdiff.mp hT).2
          by_contra h9
          have h10 : T ∈ F.filter (fun T => x ∈ Y.carrier T) :=
            Finset.mem_filter.mpr ⟨h7, h9⟩
          rw [h4] at h10
          exact h8 h10
        exact ⟨h5, h6⟩
      · rintro ⟨h5, h6⟩
        apply Finset.ext
        intro T
        constructor
        · intro hT
          have h7 : T ∈ F := (Finset.mem_filter.mp hT).1
          by_cases h8 : T ∈ S
          · exact h8
          · have h9 : T ∈ F \ S := Finset.mem_sdiff.mpr ⟨h7, h8⟩
            exact False.elim (h6 T h9 ((Finset.mem_filter.mp hT).2))
        · intro hT
          exact Finset.mem_filter.mpr ⟨hS_sub hT, h5 T hT⟩
    rw [h_eq]
    have h3 : MeasurableSet (⋂ T ∈ S', Y.carrier T) :=
      MeasurableSet.biInter (Set.Finite.countable (Finset.finite_toSet S))
        (fun T hT => Y.measurable_carrier (hS_sub hT))
    have h4 : MeasurableSet (⋂ T ∈ FS', (Y.carrier T)ᶜ) :=
      MeasurableSet.biInter (Set.Finite.countable (Finset.finite_toSet (F \ S)))
        (fun T hT => (Y.measurable_carrier ((Finset.mem_sdiff.mp hT).1)).compl)
    exact h3.inter h4
  exact h1.inter h2

lemma throughPattern_partition (Y : Kakeya.Shading F) :
    Set.PairwiseDisjoint (F.powerset : Set (Finset (Kakeya.DeltaTube δ))) (throughPattern Y) ∧
    (⋃ S ∈ F.powerset, throughPattern Y S) = Y.union := by
  have h_disj : Set.PairwiseDisjoint (F.powerset : Set (Finset (Kakeya.DeltaTube δ))) (throughPattern Y) := by
    intro S hS T hT hne
    have h : Disjoint (throughPattern Y S) (throughPattern Y T) := by
      rw [Set.disjoint_left]
      intro x hxS hxT
      have h4 : F.filter (fun T' => x ∈ Y.carrier T') = S := hxS.2
      have h5 : F.filter (fun T' => x ∈ Y.carrier T') = T := hxT.2
      have h6 : S = T := h4.symm.trans h5
      exact hne h6
    exact h
  have h_union : (⋃ S ∈ F.powerset, throughPattern Y S) = Y.union := by
    apply Set.Subset.antisymm
    · intro x hx
      rcases Set.mem_iUnion₂.mp hx with ⟨S, _, hxS⟩
      exact hxS.1
    · intro x hx
      let S := F.filter (fun T => x ∈ Y.carrier T)
      have hS : S ∈ F.powerset := Finset.mem_powerset.mpr (Finset.filter_subset _ _)
      have h_xin : x ∈ throughPattern Y S := ⟨hx, rfl⟩
      exact Set.mem_iUnion₂.mpr ⟨S, hS, h_xin⟩
  exact ⟨h_disj, h_union⟩

/-- Local scale for each through-subfamily (δ for empty families). -/
def localScale (hδ : 0 < δ) (hδ_le1 : δ ≤ 1) (heta : 0 < eta)
    (S : Finset (Kakeya.DeltaTube δ)) : ℝ :=
  if h : S.Nonempty then
    Classical.choose (max_score_broadness hδ hδ_le1 heta h)
  else δ

lemma localScale_range (hδ : 0 < δ) (hδ_le1 : δ ≤ 1) (heta : 0 < eta)
    (S : Finset (Kakeya.DeltaTube δ)) :
    δ ≤ localScale hδ hδ_le1 heta S ∧ localScale hδ hδ_le1 heta S ≤ 1 := by
  dsimp only [localScale]
  by_cases h : S.Nonempty
  · rw [dif_pos h]
    let spec := Classical.choose_spec (max_score_broadness hδ hδ_le1 heta h)
    exact ⟨spec.1, spec.2.1⟩
  · rw [dif_neg h]
    exact ⟨le_refl δ, hδ_le1⟩

lemma localScale_broadness (hδ : 0 < δ) (hδ_le1 : δ ≤ 1) (heta : 0 < eta)
    (S : Finset (Kakeya.DeltaTube δ)) (h : S.Nonempty) :
    ∀ (w : Point3), ‖w‖ = 1 → ∀ r : ℝ, δ ≤ r → r ≤ localScale hδ hδ_le1 heta S →
      ((S.filter fun T => hairbrushAcuteDirectionAngle T.direction w ≤ r).card : ℝ) ≤
        Real.rpow (r / localScale hδ hδ_le1 heta S) eta * (S.card : ℝ) := by
  dsimp only [localScale]
  rw [dif_pos h]
  exact (Classical.choose_spec (max_score_broadness hδ hδ_le1 heta h)).2.2

/-- Total volume of the shaded union equals the sum over through-patterns. -/
lemma volume_union_eq_sum_patterns (Y : Kakeya.Shading F) :
    volume Y.union = ∑ S ∈ F.powerset, volume (throughPattern Y S) := by
  have h_part := throughPattern_partition Y
  have h_meas : ∀ S ∈ F.powerset, MeasurableSet (throughPattern Y S) :=
    fun S hS => throughPattern_measurable Y hS
  have h_eq : (⋃ S ∈ F.powerset, throughPattern Y S) = Y.union := h_part.2
  rw [← h_eq]
  rw [MeasureTheory.measure_biUnion_finset h_part.1 h_meas]

/-- Helper: prove broadness inequality from extensional membership facts.
This avoids Decidable-instance matching issues with the let-bound filters
in `IsTwoBroadAtScale`. -/
lemma broadness_by_ext {δ eta : ℝ} {thetaLocal : ℝ} {S : Finset (Kakeya.DeltaTube δ)}
    (hδ : 0 < δ) (hδ_le1 : δ ≤ 1) (heta : 0 < eta)
    (hS_nonempty : S.Nonempty)
    (h_broad : ∀ (w : Point3), ‖w‖ = 1 → ∀ r : ℝ, δ ≤ r → r ≤ thetaLocal →
      ((S.filter fun T => hairbrushAcuteDirectionAngle T.direction w ≤ r).card : ℝ) ≤
        Real.rpow (r / thetaLocal) eta * (S.card : ℝ))
    (w : Point3) (hw : ‖w‖ = 1) (r : ℝ) (hrδ : δ ≤ r) (hr : r ≤ thetaLocal)
    (through near : Finset (Kakeya.DeltaTube δ))
    (hth : ∀ T, T ∈ through ↔ T ∈ S)
    (hnear : ∀ T, T ∈ near ↔ T ∈ through ∧ hairbrushAcuteDirectionAngle T.direction w ≤ r) :
    (near.card : ℝ) ≤ Real.rpow (r / thetaLocal) eta * (through.card : ℝ) := by
  have h1 : through = S := Finset.ext hth
  have h2 : near = through.filter (fun T => hairbrushAcuteDirectionAngle T.direction w ≤ r) := by
    apply Finset.ext
    intro T
    simpa [Finset.mem_filter] using hnear T
  rw [h2, h1]
  exact h_broad w hw r hrδ hr

/-- Mass retention with exact two-broadness.

Given a shading `Y`, partition `Y.union` by through-subfamily, assign each
pattern its max-score local scale, and dyadically pigeonhole to find a common
`theta` retaining at least `δ^eps` of the volume while every retained point
enjoys exact two-broadness at a scale `thetaLocal ∈ [theta/2, theta]`.
-/
theorem mass_retention_broadness
    (hδ : 0 < δ) (hδ_le1 : δ ≤ 1) (heta : 0 < eta) (heps : 0 < eps)
    (Y : Kakeya.Shading F)
    (h_small : (δ ^ eps) * (Real.log (1/δ) / Real.log 2 + 1) ≤ 1) :
    ∃ (theta : ℝ) (Y' : Kakeya.Shading F),
      δ ≤ theta ∧ theta ≤ 1 ∧
      ENNReal.ofReal (δ ^ eps) * volume Y.union ≤ volume Y'.union ∧
      Y'.union ⊆ Y.union ∧
      (∀ T ∈ F, Y'.carrier T ⊆ Y.carrier T) ∧
      IsTwoBroadAtScale Y' theta eta := by
  let N : ℕ := F.powerset.card
  let e : Fin N ≃ {S // S ∈ F.powerset} := (Finset.equivFin F.powerset).symm
  let idx : Fin N → Finset (Kakeya.DeltaTube δ) := fun i => (e i).val
  have hidx_mem : ∀ i, idx i ∈ F.powerset := fun i => (e i).property
  let mass : Fin N → ENNReal := fun i => volume (throughPattern Y (idx i))
  let scale : Fin N → ℝ := fun i => localScale hδ hδ_le1 heta (idx i)
  have h_scales : ∀ i, δ ≤ scale i ∧ scale i ≤ 1 := by
    intro i
    exact localScale_range hδ hδ_le1 heta (idx i)
  have h_total_eq : volume Y.union = ∑ i : Fin N, mass i := by
    let g : {S // S ∈ F.powerset} → ENNReal := fun S => volume (throughPattern Y S.val)
    have h_eq1 : ∑ i : Fin N, mass i = ∑ i : Fin N, g (e i) := by
      apply Finset.sum_congr rfl
      intro i _
      rfl
    have h_sum1 : ∑ i : Fin N, g (e i) = ∑ S : {S // S ∈ F.powerset}, g S :=
      Equiv.sum_comp e g
    have h_sum2 : ∑ S : {S // S ∈ F.powerset}, g S =
        ∑ S ∈ F.powerset, volume (throughPattern Y S) := by
      rw [← Finset.sum_attach (s := F.powerset)]
      <;> rfl
    have h_sum : ∑ i : Fin N, mass i = ∑ S ∈ F.powerset, volume (throughPattern Y S) := by
      rw [h_eq1, h_sum1, h_sum2]
    rw [h_sum]
    exact volume_union_eq_sum_patterns Y
  rcases dyadic_pigeonhole_scale hδ hδ_le1 N mass scale h_scales
      (volume Y.union) (by rw [h_total_eq]) eps heps h_small with
    ⟨theta, h_thetaδ, h_theta1, _h_dyadic, h_retained⟩
  -- Retained set: union of patterns whose scale lies in [theta/2, theta]
  let R : Set Point3 := ⋃ i : Fin N,
    (if theta/2 ≤ scale i ∧ scale i ≤ theta then throughPattern Y (idx i) else ∅)
  have hR_meas : MeasurableSet R := by
    apply MeasurableSet.iUnion
    intro i
    by_cases h : theta/2 ≤ scale i ∧ scale i ≤ theta
    · rw [if_pos h]
      exact throughPattern_measurable Y (hidx_mem i)
    · rw [if_neg h]
      exact MeasurableSet.empty
  have hR_sub : R ⊆ Y.union := by
    intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
    by_cases h : theta/2 ≤ scale i ∧ scale i ≤ theta
    · rw [if_pos h] at hxi
      exact hxi.1
    · rw [if_neg h] at hxi
      simpa using hxi
  -- Define restricted shading
  let Y' : Kakeya.Shading F :=
    { carrier := fun T => Y.carrier T ∩ R
      measurable_carrier := fun T hT =>
        (Y.measurable_carrier hT).inter hR_meas
      subset_tube := fun T hT =>
        Set.inter_subset_left.trans (Y.subset_tube hT) }
  have hY'union_eq : Y'.union = R := by
    apply Set.Subset.antisymm
    · intro x hx
      rcases Set.mem_setOf.mp hx with ⟨T, hT, hxT⟩
      exact hxT.2
    · intro x hx
      have h_xin_Yunion : x ∈ Y.union := hR_sub hx
      rcases Set.mem_setOf.mp h_xin_Yunion with ⟨T, hT, hxT⟩
      have h_xin_Y'carrier : x ∈ Y'.carrier T := ⟨hxT, hx⟩
      exact Set.mem_setOf.mpr ⟨T, hT, h_xin_Y'carrier⟩
  -- Volume retention
  have h_volume_R : volume R = ∑ i : Fin N,
      (if theta/2 ≤ scale i ∧ scale i ≤ theta then mass i else 0) := by
    let f : Fin N → Set Point3 := fun i =>
      if theta/2 ≤ scale i ∧ scale i ≤ theta then throughPattern Y (idx i) else ∅
    have h_disj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin N))) f := by
      intro i _ j _ hne
      by_cases hi : theta/2 ≤ scale i ∧ scale i ≤ theta
      · by_cases hj : theta/2 ≤ scale j ∧ scale j ≤ theta
        · have hfi : f i = throughPattern Y (idx i) := by simp [f, hi]
          have hfj : f j = throughPattern Y (idx j) := by simp [f, hj]
          have h_goal : Disjoint (f i) (f j) := by
            rw [hfi, hfj]
            have h_i_in : idx i ∈ F.powerset := hidx_mem i
            have h_j_in : idx j ∈ F.powerset := hidx_mem j
            have h_ne' : idx i ≠ idx j := by
              intro h
              have h' : i = j := by
                have h_inj : ∀ (a b : Fin N), idx a = idx b → a = b := by
                  intro a b hab
                  exact e.injective (Subtype.ext hab)
                exact h_inj i j h
              exact hne h'
            exact (throughPattern_partition Y).1 h_i_in h_j_in h_ne'
          exact h_goal
        · have hfj : f j = ∅ := by simp [f, hj]
          have h_goal : Disjoint (f i) (f j) := by
            rw [hfj]
            simp
          exact h_goal
      · have hfi : f i = ∅ := by simp [f, hi]
        have h_goal : Disjoint (f i) (f j) := by
          rw [hfi]
          simp
        exact h_goal
    have h_meas : ∀ i : Fin N, MeasurableSet (f i) := by
      intro i
      by_cases h : theta/2 ≤ scale i ∧ scale i ≤ theta
      · rw [show f i = throughPattern Y (idx i) from by simp [f, h]]
        exact throughPattern_measurable Y (hidx_mem i)
      · rw [show f i = ∅ from by simp [f, h]]
        exact MeasurableSet.empty
    have h : volume R = ∑ i : Fin N, volume (f i) := by
      simpa [R, f] using MeasureTheory.measure_biUnion_finset (s := Finset.univ) (f := f) h_disj (fun b _ => h_meas b)
    rw [h]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : theta/2 ≤ scale i ∧ scale i ≤ theta
    · simp [f, h, mass]
    · simp [f, h]
  have h_mass_retention : ENNReal.ofReal (δ ^ eps) * volume Y.union ≤ volume Y'.union := by
    rw [hY'union_eq, h_volume_R]
    exact h_retained
  -- Two-broadness
  have h_broad : IsTwoBroadAtScale Y' theta eta := by
    intro x hx
    have hxR : x ∈ R := by
      rw [hY'union_eq] at hx
      exact hx
    rcases Set.mem_iUnion.mp hxR with ⟨i, hxi⟩
    have h_interval : theta/2 ≤ scale i ∧ scale i ≤ theta := by
      by_cases h : theta/2 ≤ scale i ∧ scale i ≤ theta
      · exact h
      · rw [if_neg h] at hxi
        simpa using hxi
    let S := idx i
    have hS_in : S ∈ F.powerset := hidx_mem i
    have hxS : x ∈ throughPattern Y S := by
      rw [if_pos h_interval] at hxi
      exact hxi
    have h_through : F.filter (fun T => x ∈ Y.carrier T) = S := hxS.2
    have hS_nonempty : S.Nonempty := by
      by_contra h_empty
      have hS_empty : S = ∅ := by simpa using h_empty
      have h_xin_Yunion : x ∈ Y.union := hxS.1
      rcases Set.mem_setOf.mp h_xin_Yunion with ⟨T, hT, hxT⟩
      have hT_in_filter : T ∈ F.filter (fun T' => x ∈ Y.carrier T') :=
        Finset.mem_filter.mpr ⟨hT, hxT⟩
      rw [h_through, hS_empty] at hT_in_filter
      simpa using hT_in_filter
    let thetaLocal : ℝ := scale i
    have h_thetaLocal1 : δ ≤ thetaLocal := (h_scales i).1
    have h_thetaLocal2 : theta / 2 ≤ thetaLocal := h_interval.1
    have h_thetaLocal3 : thetaLocal ≤ theta := h_interval.2
    have h_through' : F.filter (fun T => x ∈ Y'.carrier T) = S := by
      have h_eq1 : ∀ T, x ∈ Y'.carrier T ↔ x ∈ Y.carrier T := by
        intro T
        simp [Y', hxR]
        <;> tauto
      apply Finset.ext
      intro T
      have h_iff : T ∈ F.filter (fun T' => x ∈ Y.carrier T') ↔ T ∈ S := by
        rw [h_through]
        <;> simp
      simpa [Finset.mem_filter, h_eq1 T] using h_iff
    refine ⟨thetaLocal, h_thetaLocal1, h_thetaLocal2, h_thetaLocal3, ?_⟩
    intro w hw r hrδ hr
    dsimp only
    have h_eq1 : ∀ T, x ∈ Y'.carrier T ↔ x ∈ Y.carrier T := by
      intro T
      simp [Y', hxR] <;> tauto
    refine broadness_by_ext hδ hδ_le1 heta hS_nonempty
      (localScale_broadness hδ hδ_le1 heta S hS_nonempty)
      w hw r hrδ hr _ _ ?_ ?_
    · intro T
      have h4 : T ∈ F.filter (fun T => x ∈ Y.carrier T) ↔ T ∈ S := by
        rw [h_through] <;> simp
      have h5 : T ∈ F.filter (fun T => x ∈ Y.carrier T) ↔ T ∈ F ∧ x ∈ Y.carrier T := by
        rw [Finset.mem_filter]
      simpa [h_eq1 T, Finset.mem_filter] using h5.symm.trans h4
    · intro T
      simp [Finset.mem_filter]
      <;> tauto
  have hY'_carrier_sub : ∀ T ∈ F, Y'.carrier T ⊆ Y.carrier T := by
    intro T hT
    dsimp only [Y']
    exact Set.inter_subset_left
  exact ⟨theta, Y', h_thetaδ, h_theta1, h_mass_retention, hY'union_eq.subset.trans hR_sub, hY'_carrier_sub, h_broad⟩

/-!
## Mass identity

Expresses the total shaded mass as a sum over through-patterns,
weighted by the cardinality of each pattern.
-/

/-- For each tube T, its shaded carrier is the disjoint union of all
    through-patterns S that contain T. -/
lemma carrier_eq_union_patterns (Y : Kakeya.Shading F) (T : Kakeya.DeltaTube δ) (hT : T ∈ F) :
    Y.carrier T = ⋃ S ∈ F.powerset.filter (fun S => T ∈ S), throughPattern Y S := by
  apply Set.Subset.antisymm
  · intro x hx
    let S := F.filter (fun T' => x ∈ Y.carrier T')
    have hS_in_powerset : S ∈ F.powerset := Finset.mem_powerset.mpr (Finset.filter_subset _ _)
    have hT_in_S : T ∈ S := Finset.mem_filter.mpr ⟨hT, hx⟩
    have hS_in_filter : S ∈ F.powerset.filter (fun S => T ∈ S) :=
      Finset.mem_filter.mpr ⟨hS_in_powerset, hT_in_S⟩
    have h_xin_union : x ∈ Y.union := ⟨T, hT, hx⟩
    have h_xin_pattern : x ∈ throughPattern Y S := ⟨h_xin_union, rfl⟩
    exact Set.mem_iUnion₂.mpr ⟨S, hS_in_filter, h_xin_pattern⟩
  · intro x hx
    rcases Set.mem_iUnion₂.mp hx with ⟨S, hS_filter, hxS⟩
    have hT_in_S : T ∈ S := (Finset.mem_filter.mp hS_filter).2
    have h_through : F.filter (fun T' => x ∈ Y.carrier T') = S := hxS.2
    have hT_in_filter : T ∈ F.filter (fun T' => x ∈ Y.carrier T') := by
      rw [h_through] <;> exact hT_in_S
    exact (Finset.mem_filter.mp hT_in_filter).2

/-- Volume of a tube's shaded carrier equals the sum of volumes of all
    through-patterns containing that tube. -/
lemma volume_carrier_eq_sum_patterns (Y : Kakeya.Shading F)
    (T : Kakeya.DeltaTube δ) (hT : T ∈ F) :
    volume (Y.carrier T) =
      ∑ S ∈ F.powerset.filter (fun S => T ∈ S), volume (throughPattern Y S) := by
  have h_eq := carrier_eq_union_patterns Y T hT
  rw [h_eq]
  have h_disj : Set.PairwiseDisjoint
      (F.powerset.filter (fun S => T ∈ S) : Set (Finset (Kakeya.DeltaTube δ)))
      (throughPattern Y) := by
    intro S hS T' hT' hne
    have hS_in : S ∈ F.powerset := (Finset.mem_filter.mp hS).1
    have hT'_in : T' ∈ F.powerset := (Finset.mem_filter.mp hT').1
    exact (throughPattern_partition Y).1 hS_in hT'_in hne
  have h_meas : ∀ S ∈ F.powerset.filter (fun S => T ∈ S),
      MeasurableSet (throughPattern Y S) := by
    intro S hS
    have hS_in : S ∈ F.powerset := (Finset.mem_filter.mp hS).1
    exact throughPattern_measurable Y hS_in
  rw [MeasureTheory.measure_biUnion_finset h_disj h_meas]

/-- Sum swap identity for through-pattern weighted sums. -/
private lemma sum_swap_patterns (f : Finset (Kakeya.DeltaTube δ) → ENNReal) :
    ∑ T ∈ F, ∑ S ∈ F.powerset.filter (fun S => T ∈ S), f S =
      ∑ S ∈ F.powerset, (S.card : ENNReal) * f S := by
  have h1 : ∀ T ∈ F, (∑ S ∈ F.powerset.filter (fun S => T ∈ S), f S) =
      ∑ S ∈ F.powerset, if T ∈ S then f S else 0 := by
    intro T _
    rw [Finset.sum_filter]
  calc
    ∑ T ∈ F, ∑ S ∈ F.powerset.filter (fun S => T ∈ S), f S
      = ∑ T ∈ F, ∑ S ∈ F.powerset, (if T ∈ S then f S else 0) := by
        apply Finset.sum_congr rfl
        intro T hT
        exact h1 T hT
    _ = ∑ S ∈ F.powerset, ∑ T ∈ F, (if T ∈ S then f S else 0) := by
        rw [Finset.sum_comm]
    _ = ∑ S ∈ F.powerset, (S.card : ENNReal) * f S := by
        apply Finset.sum_congr rfl
        intro S hS
        have hS_sub : S ⊆ F := Finset.mem_powerset.mp hS
        have h2 : ∑ T ∈ F, (if T ∈ S then f S else 0) = ∑ T ∈ S, f S := by
          rw [Finset.sum_ite]
          <;> simp [hS_sub]
        rw [h2]
        have h3 : ∑ T ∈ S, f S = (S.card : ENNReal) * f S := by
          rw [Finset.sum_const]
          <;> ring
        exact h3

/-- Total shaded mass equals the sum over through-patterns weighted by cardinality. -/
lemma shading_mass_eq_sum_patterns (Y : Kakeya.Shading F) :
    Y.mass = ∑ S ∈ F.powerset, (S.card : ENNReal) * volume (throughPattern Y S) := by
  have h1 : Y.mass = ∑ T ∈ F, volume (Y.carrier T) := by rfl
  rw [h1]
  have h2 : ∀ T ∈ F, volume (Y.carrier T) =
      ∑ S ∈ F.powerset.filter (fun S => T ∈ S), volume (throughPattern Y S) :=
    fun T hT => volume_carrier_eq_sum_patterns Y T hT
  rw [Finset.sum_congr rfl h2]
  exact sum_swap_patterns (fun S => volume (throughPattern Y S))

end MassRetention

end Kakeya.Assouad
