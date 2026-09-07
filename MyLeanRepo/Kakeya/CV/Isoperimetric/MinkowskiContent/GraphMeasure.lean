import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.InnerStripGraphCover
import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.LipschitzStripBound
import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.LipschitzGraphAreaLower
import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.Tactic

open MeasureTheory Metric Set ENNReal
open scoped MeasureTheory Pointwise
open GraphAreaFormula

namespace Geometry.Isoperimetric

variable {m : ℕ} [Nonempty (Fin m)]

/-- Intersecting graph images of shrinking closed thickenings recovers the original graph image. -/
lemma graph_image_intersection_cthickening
    {g : E m → ℝ} (hg_cont : Continuous (graphMap g))
    {A : Set (E m)} (hA : IsCompact A) :
    (⋂ n : ℕ, graphMap g '' Metric.cthickening (1 / (n + 1 : ℝ)) A) = graphMap g '' A := by
  by_cases hA_empty : A = ∅
  · rw [hA_empty]
    ext y
    simp
  · have hA_nonempty : A.Nonempty := Set.nonempty_iff_ne_empty.mpr hA_empty
    have h_inj : Function.Injective (graphMap g) := graphMap_injective g
    let K : ℕ → Set (E m) := fun n => Metric.cthickening (1 / (n + 1 : ℝ)) A
    have hK_subset : ∀ n : ℕ, A ⊆ K n := by
      intro n x hx
      have h_pos : (0 : ℝ) ≤ 1 / (n + 1 : ℝ) := by positivity
      have h_inf : infEDist x A = 0 := by
        have h3 : infEDist x A ≤ edist x x := Metric.infEDist_le_edist_of_mem hx
        have h4 : edist x x = 0 := edist_self x
        rw [h4] at h3
        exact le_antisymm h3 bot_le
      rw [Metric.mem_cthickening_iff, h_inf]
      simpa using h_pos
    have h1 : ∀ x : E m, (∀ n : ℕ, x ∈ K n) → x ∈ A := by
      intro x hx
      have h_inf : ∀ n : ℕ, infDist x A ≤ 1 / (n + 1 : ℝ) := by
        intro n
        have h2 : infEDist x A ≤ ENNReal.ofReal (1 / (n + 1 : ℝ)) :=
          (Metric.mem_cthickening_iff).mp (hx n)
        have h3 : infEDist x A = ENNReal.ofReal (infDist x A) := by
          have h4 : infEDist x A ≠ ⊤ := Metric.infEDist_ne_top hA_nonempty
          have h5 : (infEDist x A).toReal = infDist x A := by rfl
          rw [← h5, ENNReal.ofReal_toReal h4]
        rw [h3] at h2
        exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h2
      have h_inf_zero : infDist x A = 0 := by
        have h_nonneg : 0 ≤ infDist x A := Metric.infDist_nonneg
        by_cases h_pos : 0 < infDist x A
        · rcases exists_nat_gt (1 / infDist x A) with ⟨n, hn⟩
          have h_gt : (n : ℝ) + 1 > 1 / infDist x A := by linarith
          have h_lt : 1 / ((n : ℝ) + 1) < infDist x A := by
            calc
              1 / ((n : ℝ) + 1) < 1 / (1 / infDist x A) := by gcongr
              _ = infDist x A := by field_simp [h_pos.ne'] <;> ring
          linarith [h_inf n]
        · exact le_antisymm (by linarith) h_nonneg
      have h_iff : x ∈ closure A ↔ infDist x A = 0 :=
        Metric.mem_closure_iff_infDist_zero hA_nonempty
      rw [hA.isClosed.closure_eq] at h_iff
      exact h_iff.mpr h_inf_zero
    have h_main : (⋂ n : ℕ, graphMap g '' K n) = graphMap g '' (⋂ n : ℕ, K n) := by
      ext y
      simp only [Set.mem_iInter, Set.mem_image]
      constructor
      · intro h
        rcases h 0 with ⟨x0, _, rfl⟩
        have h_x_in : ∀ n : ℕ, x0 ∈ K n := by
          intro n
          rcases h n with ⟨x, hx, h_eq⟩
          rw [h_inj h_eq] at hx
          exact hx
        exact ⟨x0, h_x_in, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact fun n => ⟨x, hx n, rfl⟩
    have hK_inter : (⋂ n : ℕ, K n) = A := by
      ext x
      simp only [K, Set.mem_iInter]
      exact ⟨fun hx => h1 x hx, fun hx n => hK_subset n hx⟩
    rw [h_main, hK_inter]

/-- Hausdorff measure of graph images is continuous along shrinking thickenings. -/
lemma graph_image_measure_continuous
    {g : E m → ℝ} {L : NNReal} (hg : LipschitzWith L g)
    {A : Set (E m)} (hA : IsCompact A) (ε : ENNReal) (hε : 0 < ε) :
    ∃ s : ℝ, 0 < s ∧
      μHE[m] (graphMap g '' Metric.thickening s A) ≤
      μHE[m] (graphMap g '' A) + ε := by
  by_cases hA_empty : A = ∅
  · rw [hA_empty]
    exact ⟨1, by norm_num, by simpa using zero_le (α := ENNReal)⟩
  · have hA_nonempty : A.Nonempty := Set.nonempty_iff_ne_empty.mpr hA_empty
    let K' : NNReal := ⟨Real.sqrt (1 + (L : ℝ) ^ 2), by positivity⟩
    have hK' : LipschitzWith K' (graphMap g) := graphMap_lipschitz_global hg
    have hg_cont : Continuous (graphMap g) := hK'.continuous
    have h_ct_bdd : ∀ s : ℝ, 0 ≤ s → Bornology.IsBounded (Metric.cthickening s A) := by
      intro s hs
      by_cases hpos : 0 < s
      · have h1 : Bornology.IsBounded (Metric.thickening s A) := hA.isBounded.thickening
        rw [(closure_thickening hpos A).symm]
        exact h1.closure
      · have h0 : s = 0 := by linarith
        rw [h0, Metric.cthickening_zero, hA.isClosed.closure_eq]
        exact hA.isBounded
    have h_ct_compact : ∀ s : ℝ, 0 ≤ s → IsCompact (Metric.cthickening s A) := by
      intro s hs
      exact Metric.isCompact_of_isClosed_isBounded Metric.isClosed_cthickening (h_ct_bdd s hs)
    let S : ℕ → Set (E (m + 1)) := fun n =>
      graphMap g '' Metric.cthickening (1 / (n + 1 : ℝ)) A
    have hS_compact : ∀ n, IsCompact (S n) := by
      intro n
      exact (h_ct_compact _ (by positivity)).image hg_cont
    have hS_meas : ∀ n, MeasurableSet (S n) := fun n => (hS_compact n).measurableSet
    have hS_nullmeas : ∀ n, NullMeasurableSet (S n) μHE[m] :=
      fun n => (hS_meas n).nullMeasurableSet
    have hS_dec : Antitone S := by
      intro n k hnk
      have h1 : (1 / (k + 1 : ℝ)) ≤ (1 / (n + 1 : ℝ)) := by
        apply one_div_le_one_div_of_le <;> norm_num <;> linarith
      have h2 : Metric.cthickening (1 / (k + 1 : ℝ)) A ⊆
          Metric.cthickening (1 / (n + 1 : ℝ)) A := by
        intro x hx
        have h3 : infEDist x A ≤ ENNReal.ofReal (1 / (k + 1 : ℝ)) :=
          (Metric.mem_cthickening_iff).mp hx
        exact (Metric.mem_cthickening_iff).mpr
          (h3.trans (ENNReal.ofReal_le_ofReal h1))
      rintro z ⟨x, hx, rfl⟩
      exact ⟨x, h2 hx, rfl⟩
    have h_inter : (⋂ n, S n) = graphMap g '' A :=
      graph_image_intersection_cthickening hg_cont hA
    have h_vol_eq : (μHE[m] : Measure (E m)) = volume :=
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume m
    have h_ct1_compact : IsCompact (Metric.cthickening 1 A) :=
      h_ct_compact 1 (by norm_num)
    have h_bdd_vol : μHE[m] (Metric.cthickening 1 A) < ⊤ := by
      rw [h_vol_eq]
      exact h_ct1_compact.measure_lt_top
    have hK_on : LipschitzOnWith K' (graphMap g) (Metric.cthickening 1 A) :=
      hK'.lipschitzOnWith
    have hS0_eq : S 0 = graphMap g '' Metric.cthickening 1 A := by
      simp [S] <;> norm_num
    have h2 : μHE[m] (graphMap g '' Metric.cthickening 1 A) ≤
        (K' : ENNReal) ^ (m : ℝ) * μHE[m] (Metric.cthickening 1 A) :=
      lipschitzOnWith_euclideanHausdorffMeasure_image_le
        (X := E m) (Y := E (m + 1)) (K := K') (f := graphMap g)
        (s := Metric.cthickening 1 A) (d := m) hK_on
    have h2' : μHE[m] (S 0) ≤
        (K' : ENNReal) ^ (m : ℝ) * μHE[m] (Metric.cthickening 1 A) := by
      rw [hS0_eq]
      exact h2
    have h_fin : μHE[m] (S 0) ≠ ⊤ := by
      have h3 : μHE[m] (S 0) < ⊤ := by
        calc
          μHE[m] (S 0) ≤
              (K' : ENNReal) ^ (m : ℝ) * μHE[m] (Metric.cthickening 1 A) := h2'
          _ < ⊤ := ENNReal.mul_lt_top
            (lt_top_iff_ne_top.mpr
              (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.coe_ne_top))
            h_bdd_vol
      exact h3.ne
    have h_tendsto : Filter.Tendsto (fun n => μHE[m] (S n)) Filter.atTop
        (nhds (μHE[m] (graphMap g '' A))) := by
      rw [← h_inter]
      exact tendsto_measure_iInter_atTop hS_nullmeas hS_dec ⟨0, h_fin⟩
    by_cases h_top : μHE[m] (graphMap g '' A) = ⊤
    · have hS0 : S 0 = graphMap g '' Metric.cthickening 1 A := by
        simp [S] <;> norm_num
      have h_image_subset : graphMap g '' Metric.thickening 1 A ⊆ S 0 := by
        rw [hS0]
        exact Set.image_mono (Metric.thickening_subset_cthickening 1 A)
      refine ⟨1, by norm_num, (measure_mono h_image_subset).trans ?_⟩
      rw [h_top]
      simp
    · have h_lt : μHE[m] (graphMap g '' A) < μHE[m] (graphMap g '' A) + ε :=
        ENNReal.lt_add_right h_top hε.ne'
      have h_nhds : Set.Iio (μHE[m] (graphMap g '' A) + ε) ∈
          nhds (μHE[m] (graphMap g '' A)) :=
        Iio_mem_nhds h_lt
      have h_eventually_lt : ∀ᶠ n in Filter.atTop,
          μHE[m] (S n) < μHE[m] (graphMap g '' A) + ε :=
        h_tendsto h_nhds
      have h_eventually : ∀ᶠ n in Filter.atTop,
          μHE[m] (S n) ≤ μHE[m] (graphMap g '' A) + ε :=
        h_eventually_lt.mono fun n hn => hn.le
      rcases Filter.eventually_atTop.mp h_eventually with ⟨N, hN⟩
      let s : ℝ := 1 / (N + 1 : ℝ)
      have hs_pos : 0 < s := by positivity
      have h_image_subset : graphMap g '' Metric.thickening s A ⊆ S N := by
        rintro y ⟨x, hx, rfl⟩
        have h_in : x ∈ Metric.cthickening (1 / (↑N + 1 : ℝ)) A := by
          convert Metric.thickening_subset_cthickening s A hx using 2 <;>
            simp [s] <;> norm_cast
        exact ⟨x, h_in, rfl⟩
      exact ⟨s, hs_pos, (measure_mono h_image_subset).trans (hN N (by rfl))⟩

/-- A continuous graph has zero ambient Lebesgue measure. -/
lemma graph_volume_zero {g : E m → ℝ} (hg : Continuous g) :
    volume (GraphAreaFormula.graph g) = 0 := by
  let e : E (m + 1) ≃ᵐ (E m × ℝ) := eSplit
  have hmp : MeasurePreserving e volume volume := eSplit_measurePreserving
  let S : Set (E m × ℝ) := {p | p.2 = g p.1}
  have h_image : e '' (GraphAreaFormula.graph g) = S := by
    ext ⟨x, y⟩
    simp only [S, GraphAreaFormula.graph, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨p, hp, h_eq⟩
      have h_e_eq : e p = (GraphAreaFormula.proj p, p (Fin.last m)) := eSplit_apply p
      have h_xy : (GraphAreaFormula.proj p, p (Fin.last m)) = (x, y) := by
        rw [← h_e_eq, h_eq]
      have hx : GraphAreaFormula.proj p = x := congrArg Prod.fst h_xy
      have hy : p (Fin.last m) = y := congrArg Prod.snd h_xy
      calc
        y = p (Fin.last m) := hy.symm
        _ = g (GraphAreaFormula.proj p) := hp
        _ = g x := congrArg g hx
    · intro h
      let q := e.symm (x, y)
      have h3 : e q = (x, y) := e.right_inv _
      have h4 : GraphAreaFormula.proj q = x := by
        have h5 : (e q).1 = x := by rw [h3]
        rw [eSplit_apply] at h5
        exact h5
      have h7 : q (Fin.last m) = y := by
        have h8 : (e q).2 = y := by rw [h3]
        rw [eSplit_apply] at h8
        exact h8
      exact ⟨q, by simpa [GraphAreaFormula.graph, h4, h7] using h, h3⟩
  have hS_meas : MeasurableSet S := by
    have h_sub : Continuous (fun p : E m × ℝ => p.2 - g p.1) :=
      continuous_snd.sub (hg.comp continuous_fst)
    have h : S = (fun p : E m × ℝ => p.2 - g p.1) ⁻¹' {0} := by
      ext ⟨x, y⟩
      simp [S, sub_eq_zero]
    rw [h]
    exact (MeasurableSet.singleton (0 : ℝ)).preimage h_sub.measurable
  have h_ae : ∀ᵐ x : E m ∂volume, volume {y : ℝ | (x, y) ∈ S} = 0 := by
    filter_upwards with x
    have h10 : {y : ℝ | (x, y) ∈ S} = {y : ℝ | y = g x} := by
      ext y
      simp [S]
    rw [h10]
    simp
  have h_main : volume S = 0 :=
    (MeasureTheory.Measure.measure_prod_null hS_meas).mpr h_ae
  have hG_meas : MeasurableSet (GraphAreaFormula.graph g) := by
    have h1 : Continuous (fun p : E (m + 1) => p (Fin.last m)) := by fun_prop
    have h2 : Continuous (fun p : E (m + 1) => g (GraphAreaFormula.proj p)) :=
      hg.comp GraphAreaFormula.continuous_proj
    have h_sub : Continuous
        (fun p : E (m + 1) => p (Fin.last m) - g (GraphAreaFormula.proj p)) :=
      h1.sub h2
    have h : GraphAreaFormula.graph g =
        (fun p : E (m + 1) => p (Fin.last m) - g (GraphAreaFormula.proj p)) ⁻¹' {0} := by
      ext p
      simp [GraphAreaFormula.graph, sub_eq_zero]
    rw [h]
    exact (MeasurableSet.singleton (0 : ℝ)).preimage h_sub.measurable
  have h1 : volume (e ⁻¹' S) = volume S :=
    hmp.measure_preimage hS_meas.nullMeasurableSet
  have h2 : e ⁻¹' S = GraphAreaFormula.graph g := by
    rw [← h_image]
    ext z
    simp
  rw [h2] at h1
  have h_eq : volume (GraphAreaFormula.graph g) =
      volume (e '' (GraphAreaFormula.graph g)) := by
    rw [h_image]
    exact h1
  rw [h_eq, h_image]
  exact h_main

end Geometry.Isoperimetric
