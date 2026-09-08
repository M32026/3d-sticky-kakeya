import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.NonDistinctDilatedContainment
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.CapsuleBounds
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.TubeVolume
import MyLeanRepo.Kakeya.Streamlined.Families
import MyLeanRepo.Kakeya.Streamlined.Estimates
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.FrostmanFromDeltaMax
import MyLeanRepo.Kakeya.Streamlined.RogersShephard
import Mathlib.Analysis.Convex.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Degree bound from deltaMax

For a tube family in the unit ball, the number of non-essentially-distinct
neighbors of each tube is bounded by `1000^3 * deltaMax`.

This uses the key geometric fact that non-ED tubes are contained in a
1000x dilation, and deltaMax controls the contained mass in any convex set.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Streamlined

/-- Volume of a dilated tube carrier scales by A^3. -/
lemma volume_dilatedTubeCarrier_of_pos
    {ρ : ℝ} (_hρ : 0 < ρ) {A : ℝ} (hA : 0 < A)
    (T : Kakeya.DeltaTube ρ) :
    volume (dilatedTubeCarrier A T) =
      ENNReal.ofReal (A ^ 3) * T.volume := by
  let m := GeometricLemmas.tubeMidpoint T
  let scale : Point3 → Point3 := fun x => A • x
  let pre : Point3 → Point3 := fun x => x - m
  let post : Point3 → Point3 := fun x => m + x
  let hmap : Point3 → Point3 := AffineMap.homothety m A

  have h_hmap : hmap = post ∘ scale ∘ pre := by
    funext x
    simp [hmap, post, scale, pre, AffineMap.homothety_apply]
    <;> abel

  have h_main_eq : dilatedTubeCarrier A T = hmap '' T.carrier := by
    have h1 : dilatedTubeCarrier A T =
        (AffineMap.homothety (T.base + (1 / 2 : ℝ) • T.direction) A) '' T.carrier := by rfl
    rw [h1]
    have h2 : (AffineMap.homothety (T.base + (1 / 2 : ℝ) • T.direction) A) = hmap := by
      congr
    rw [h2]

  rw [h_main_eq, h_hmap]
  have h_img : (post ∘ scale ∘ pre) '' T.carrier = post '' (scale '' (pre '' T.carrier)) := by
    rw [Set.image_comp, Set.image_comp]
  rw [h_img]

  have h_fn_post : (fun x : Point3 => -(-m) + x) = post := by
    funext x; simp [post]
  have h_vol_post : volume (post '' (scale '' (pre '' T.carrier))) =
      volume (scale '' (pre '' T.carrier)) := by
    have h := volume_translation (-m) (scale '' (pre '' T.carrier))
    rw [h_fn_post] at h
    exact h
  rw [h_vol_post]

  have h_vol_scale : volume (scale '' (pre '' T.carrier)) =
      ENNReal.ofReal (A ^ 3) * volume (pre '' T.carrier) :=
    GeometricLemmas.volume_smul3 hA
  rw [h_vol_scale]

  have h_fn_pre : (fun x : Point3 => -m + x) = pre := by
    funext x; simp [pre] <;> abel
  have h_vol_pre : volume (pre '' T.carrier) = volume T.carrier := by
    have h := volume_translation m T.carrier
    rw [h_fn_pre] at h
    exact h
  rw [h_vol_pre]

  have h_final : volume T.carrier = T.volume := by
    rw [Kakeya.DeltaTube.volume]
  rw [h_final]

/-- The dilated tube carrier is convex. -/
lemma convex_dilatedTubeCarrier {ρ : ℝ} {A : ℝ} (_hA : 0 < A) (_hρ : 0 ≤ ρ)
    (T : Kakeya.DeltaTube ρ) :
    Convex ℝ (dilatedTubeCarrier A T) := by
  let m := GeometricLemmas.tubeMidpoint T
  let hmap : Point3 →ᵃ[ℝ] Point3 := AffineMap.homothety m A
  have h_set_eq : dilatedTubeCarrier A T = hmap '' T.carrier := by
    have h1 : dilatedTubeCarrier A T =
        (AffineMap.homothety (T.base + (1 / 2 : ℝ) • T.direction) A) '' T.carrier := by rfl
    rw [h1]
    have h2 : (AffineMap.homothety (T.base + (1 / 2 : ℝ) • T.direction) A) = hmap := by
      rfl
    rw [h2]
  rw [h_set_eq]
  have h_conv : Convex ℝ T.carrier := GeometricLemmas.deltaTube_carrier_convex T
  exact Convex.affine_image hmap h_conv

/--
For a tube family in the unit ball, the number of non-essentially-distinct
neighbors of each tube is bounded by `1000^3 * deltaMax`.

This is the key degree bound for the essentially-distinct subfamily extraction.
-/
lemma deltaMax_bounds_non_ed_degree {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {T : TubeFamily δ} (hT_ball : T.IsInUnitBall)
    {D : ENNReal} (hD : T.toBodyFamily.deltaMax ≤ D) :
    ∀ j : Fin T.card,
      ∃ neighbors : Finset (Fin T.card),
        (neighbors.card : ENNReal) ≤ 1000^3 * D ∧
        ∀ i, i ≠ j → ¬(T.tube i).EssentiallyDistinct (T.tube j) → i ∈ neighbors := by
  classical
  let V := Kakeya.deltaTubeVolume δ
  have hV_pos : 0 < V := by
    have h_lower : V ≥ ENNReal.ofReal (Real.pi * δ ^ 2 + (4 / 3 : ℝ) * Real.pi * δ ^ 3) := by
      exact GeometricLemmas.capsule_volume_lower δ hδ
    have h_pos : 0 < Real.pi * δ ^ 2 + (4 / 3 : ℝ) * Real.pi * δ ^ 3 := by positivity
    have h_ennreal_pos : 0 < ENNReal.ofReal (Real.pi * δ ^ 2 + (4 / 3 : ℝ) * Real.pi * δ ^ 3) :=
      ENNReal.ofReal_pos.mpr h_pos
    exact lt_of_lt_of_le h_ennreal_pos h_lower
  have hV_ne_top : V ≠ ⊤ := by
    have h_upper : V ≤ ENNReal.ofReal (Real.pi * δ ^ 2 + (8 / 3 : ℝ) * Real.pi * δ ^ 3) := by
      exact GeometricLemmas.capsule_upper_bound_instantiation δ hδ
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h_upper
  have h_vol_eq : ∀ i, (T.tube i).volume = V := by
    intro i
    exact tube_volume_eq (T.tube i) ⟨0, EuclideanSpace.single 0 1, by simp⟩

  intro j
  let K : Set Point3 := dilatedTubeCarrier 1000 (T.tube j)
  have hK_convex : Convex ℝ K := convex_dilatedTubeCarrier (by norm_num) hδ.le (T.tube j)
  have hK_vol : volume K = (1000 : ENNReal)^3 * V := by
    have h :=
      volume_dilatedTubeCarrier_of_pos
        hδ (A := 1000) (by norm_num) (T.tube j)
    rw [h, h_vol_eq j] <;> norm_cast
  have hK_vol_pos : 0 < volume K := by
    rw [hK_vol] <;> positivity
  have hK_vol_ne_top : volume K ≠ ⊤ := by
    rw [hK_vol]
    exact ENNReal.mul_ne_top (by norm_num) hV_ne_top

  have h_density_le : T.toBodyFamily.density K ≤ D :=
    BodyFamily.density_le_of_deltaMax_le hD hK_convex

  have h_mass_le : T.toBodyFamily.containedMass K ≤ D * volume K := by
    have h_density_eq : T.toBodyFamily.density K =
        T.toBodyFamily.containedMass K / volume K := by rfl
    rw [h_density_eq] at h_density_le
    have h_cancel : (T.toBodyFamily.containedMass K / volume K) * volume K =
        T.toBodyFamily.containedMass K := by
      rw [ENNReal.div_mul_cancel hK_vol_pos.ne' hK_vol_ne_top]
    have h : (T.toBodyFamily.containedMass K / volume K) * volume K ≤ D * volume K := by
      gcongr
    rw [h_cancel] at h
    exact h

  let neighbors : Finset (Fin T.card) :=
    Finset.univ.filter fun i =>
      i ≠ j ∧ ¬(T.tube i).EssentiallyDistinct (T.tube j)

  have h_body_carrier : ∀ i, (T.toBodyFamily.body i).carrier = (T.tube i).carrier := by
    intro i
    rfl

  have h_containment : ∀ i ∈ neighbors, (T.tube i).carrier ⊆ K := by
    intro i hi
    have h_i_ne_j : i ≠ j := (Finset.mem_filter.mp hi).2.1
    have h_non_ed : ¬(T.tube i).EssentiallyDistinct (T.tube j) :=
      (Finset.mem_filter.mp hi).2.2
    have h_m1 : ‖GeometricLemmas.tubeMidpoint (T.tube i)‖ ≤ 3 := by
      have h := GeometricLemmas.tubeMidpoint_norm_le_one (hT_ball i)
      linarith
    have h_m2 : ‖GeometricLemmas.tubeMidpoint (T.tube j)‖ ≤ 3 := by
      have h := GeometricLemmas.tubeMidpoint_norm_le_one (hT_ball j)
      linarith
    exact GeometricLemmas.non_distinct_dilated_containment hδ hδ1 (T.tube i) (T.tube j) h_m1 h_m2 h_non_ed

  have h_mem_contained : ∀ (F : BodyFamily) (K : Set Point3) i,
      (F.body i).carrier ⊆ K → i ∈ F.containedIndices K := by
    intro F K i h
    simpa [BodyFamily.containedIndices, Finset.mem_filter] using h

  have h_neighbors_subset_contained :
      neighbors ⊆ T.toBodyFamily.containedIndices K := by
    intro i hi
    have h1 : (T.tube i).carrier ⊆ K := h_containment i hi
    have h2 : (T.toBodyFamily.body i).carrier ⊆ K := by
      rw [h_body_carrier i] <;> exact h1
    exact h_mem_contained T.toBodyFamily K i h2

  have h_sum_vol : ∑ i ∈ neighbors, (T.tube i).volume = (neighbors.card : ENNReal) * V := by
    have h : ∑ i ∈ neighbors, (T.tube i).volume = ∑ i ∈ neighbors, V := by
      apply Finset.sum_congr rfl
      intro i _
      exact h_vol_eq i
    rw [h]
    simp [Finset.sum_const]

  have h_mass_bound :
      (neighbors.card : ENNReal) * V ≤ T.toBodyFamily.containedMass K := by
    calc
      (neighbors.card : ENNReal) * V
        = ∑ i ∈ neighbors, (T.tube i).volume := h_sum_vol.symm
      _ ≤ ∑ i ∈ T.toBodyFamily.containedIndices K, (T.tube i).volume := by
          apply Finset.sum_le_sum_of_subset_of_nonneg h_neighbors_subset_contained
          intro _ _ _; positivity
      _ = ∑ i ∈ T.toBodyFamily.containedIndices K, (T.toBodyFamily.body i).volume := by
          apply Finset.sum_congr rfl
          intro i _
          rfl
      _ = T.toBodyFamily.containedMass K := by rfl

  have h_main : (neighbors.card : ENNReal) * V ≤ D * volume K := by
    calc
      (neighbors.card : ENNReal) * V
        ≤ T.toBodyFamily.containedMass K := h_mass_bound
      _ ≤ D * volume K := h_mass_le

  rw [hK_vol] at h_main
  have h5 : D * ((1000 : ENNReal)^3 * V) = (1000 : ENNReal)^3 * (D * V) := by
    rw [mul_left_comm]
  rw [h5] at h_main
  have h_final : (neighbors.card : ENNReal) ≤ (1000 : ENNReal)^3 * D := by
    by_contra h
    have h2 : (1000 : ENNReal)^3 * D < (neighbors.card : ENNReal) := by
      exact lt_of_not_ge h
    have h3 : ((1000 : ENNReal)^3 * D) * V < (neighbors.card : ENNReal) * V :=
      ENNReal.mul_lt_mul_left hV_pos.ne' hV_ne_top h2
    have h4 : ((1000 : ENNReal)^3 * D) * V = (1000 : ENNReal)^3 * (D * V) := by
      rw [mul_assoc]
    rw [h4] at h3
    exact lt_irrefl _ (h3.trans_le h_main)

  refine ⟨neighbors, h_final, ?_⟩
  intro i hne hnoned
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne, hnoned⟩

/--
For any positive-radius tube family, `deltaMax ≤ enncard`.

Proof: every convex set containing a tube has volume at least the tube volume `V`,
and total contained mass is at most `|T| · V`, so density is at most `|T|`.
Sets containing no tube have zero contained mass and zero density.
-/
lemma deltaMax_le_enncard_support_free
    {δ : ℝ} (hδ : 0 < δ) {T : TubeFamily δ} :
    T.toBodyFamily.deltaMax ≤ T.toBodyFamily.enncard := by
  classical
  let F := T.toBodyFamily
  let V := Kakeya.deltaTubeVolume δ
  have hV_pos : 0 < V := by
    have h_lower : V ≥ ENNReal.ofReal (Real.pi * δ ^ 2 + (4 / 3 : ℝ) * Real.pi * δ ^ 3) := by
      exact GeometricLemmas.capsule_volume_lower δ hδ
    have h_pos : 0 < Real.pi * δ ^ 2 + (4 / 3 : ℝ) * Real.pi * δ ^ 3 := by positivity
    have h_ennreal_pos : 0 < ENNReal.ofReal (Real.pi * δ ^ 2 + (4 / 3 : ℝ) * Real.pi * δ ^ 3) :=
      ENNReal.ofReal_pos.mpr h_pos
    exact lt_of_lt_of_le h_ennreal_pos h_lower
  have hV_ne_top : V ≠ ⊤ := by
    have h_upper : V ≤ ENNReal.ofReal (Real.pi * δ ^ 2 + (8 / 3 : ℝ) * Real.pi * δ ^ 3) := by
      exact GeometricLemmas.capsule_upper_bound_instantiation δ hδ
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h_upper
  have h_vol_eq : ∀ i, (T.tube i).volume = V := by
    intro i
    exact tube_volume_eq (T.tube i) ⟨0, EuclideanSpace.single 0 1, by simp⟩
  have h_body_vol : ∀ i, (F.body i).volume = V := by
    intro i
    have h_carrier : (F.body i).carrier = (T.tube i).carrier := by
      dsimp only [F, TubeFamily.toBodyFamily] <;> rfl
    have h_vol : (F.body i).volume = (T.tube i).volume := by
      simp [Body.volume, Kakeya.DeltaTube.volume, h_carrier]
    rw [h_vol]
    exact h_vol_eq i

  have h_mass_eq : F.mass = F.enncard * V := by
    simp [BodyFamily.mass, BodyFamily.enncard, h_body_vol]

  have h_density_le : ∀ (K : Set Point3), Convex ℝ K → F.density K ≤ F.enncard := by
    intro K _hK
    by_cases hcm : F.containedMass K = 0
    · have h_density_zero : F.density K = 0 := by
        rw [BodyFamily.density, hcm]
        <;> simp
      rw [h_density_zero]
      exact zero_le
    · have hcm_pos : 0 < F.containedMass K :=
        bot_lt_iff_ne_bot.mpr hcm
      have h_nonempty : (F.containedIndices K).Nonempty := by
        by_contra h
        have h_empty : F.containedIndices K = ∅ := by simpa using h
        have h_cm_zero : F.containedMass K = 0 := by
          simp [BodyFamily.containedMass, h_empty]
        exact hcm h_cm_zero
      rcases h_nonempty with ⟨i, hi⟩
      have h_i_in : (F.body i).carrier ⊆ K := by
        simpa [BodyFamily.containedIndices, Finset.mem_filter] using hi
      have h_vol_K : V ≤ volume K := by
        have h1 : volume (F.body i).carrier ≤ volume K := volume.mono h_i_in
        have h2 : volume (F.body i).carrier = V := h_body_vol i
        rw [h2] at h1
        exact h1
      have hK_pos : 0 < volume K := lt_of_lt_of_le hV_pos h_vol_K
      have hK_ne_zero : volume K ≠ 0 := hK_pos.ne'
      have h_mass_le : F.containedMass K ≤ F.mass := by
        apply Finset.sum_le_sum_of_subset
        exact Finset.filter_subset _ _
      have h_main : F.containedMass K ≤ F.enncard * volume K := by
        calc
          F.containedMass K ≤ F.mass := h_mass_le
          _ = F.enncard * V := h_mass_eq
          _ ≤ F.enncard * volume K := by gcongr
      have h_density_eq : F.density K = F.containedMass K / volume K := by rfl
      rw [h_density_eq]
      by_cases hK_top : volume K = ⊤
      · rw [hK_top]
        simp
      · have h_ineq : F.containedMass K / volume K ≤ F.enncard := by
          have h_mult : F.containedMass K * (volume K)⁻¹ ≤ F.enncard * volume K * (volume K)⁻¹ := by
            gcongr
          have h_cancel : F.enncard * volume K * (volume K)⁻¹ = F.enncard := by
            rw [mul_assoc, ENNReal.mul_inv_cancel hK_ne_zero hK_top, mul_one]
          rw [h_cancel] at h_mult
          exact h_mult
        exact h_ineq

  have h_set : ∀ d ∈ {d : ENNReal | ∃ (K : Set Point3), Convex ℝ K ∧ d = F.density K}, d ≤ F.enncard := by
    intro d hd
    rcases hd with ⟨K, hK, rfl⟩
    exact h_density_le K hK
  have h_deltaMax_le : F.deltaMax ≤ F.enncard := by
    unfold BodyFamily.deltaMax
    exact sSup_le h_set
  exact h_deltaMax_le

/-- Compatibility wrapper retaining the historical redundant support
hypothesis. -/
lemma deltaMax_le_enncard {δ : ℝ} (hδ : 0 < δ) {T : TubeFamily δ}
    (_hT_ball : T.IsInUnitBall) :
    T.toBodyFamily.deltaMax ≤ T.toBodyFamily.enncard :=
  deltaMax_le_enncard_support_free hδ

/-- For any tube family in the unit ball, `deltaMax` is finite (not `⊤`). -/
lemma deltaMax_lt_top {δ : ℝ} (hδ : 0 < δ) {T : TubeFamily δ}
    (hT_ball : T.IsInUnitBall) :
    T.toBodyFamily.deltaMax ≠ ⊤ := by
  let F := T.toBodyFamily
  have h_deltaMax_le : F.deltaMax ≤ F.enncard := deltaMax_le_enncard hδ hT_ball
  have h_enncard_ne_top : F.enncard ≠ ⊤ := ENNReal.natCast_ne_top F.card
  exact ne_top_of_le_ne_top h_enncard_ne_top h_deltaMax_le

end Kakeya.Streamlined
