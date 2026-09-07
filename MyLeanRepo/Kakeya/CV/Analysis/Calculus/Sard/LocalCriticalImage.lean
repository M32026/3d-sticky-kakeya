module

public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.Defs
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Tactic

@[expose] public section

namespace ForMathlib.Analysis.Calculus.Sard

open MeasureTheory
open scoped ContDiff

/-- Helper lemma: If the critical values of every globally defined smooth function have measure zero,
then the critical values of any smooth function on an open set also have measure zero. -/
lemma local_critical_image_null {m : ℕ}
    (ih : ∀ (g : EuclideanSpace ℝ (Fin m) → ℝ), ContDiff ℝ ∞ g →
      (volume : Measure ℝ) (g '' {x | fderiv ℝ g x = 0}) = 0)
    {U : Set (EuclideanSpace ℝ (Fin m))} (hU_open : IsOpen U)
    (g : EuclideanSpace ℝ (Fin m) → ℝ) (hg : ContDiffOn ℝ ∞ g U) :
    (volume : Measure ℝ) (g '' {x ∈ U | fderiv ℝ g x = 0}) = 0 := by
  let S : Set (EuclideanSpace ℝ (Fin m)) := {x ∈ U | fderiv ℝ g x = 0}
  have h_goal : (volume : Measure ℝ) (g '' S) = 0 := by
    by_cases hS_empty : S = ∅
    · have h : g '' S = ∅ := by
        rw [hS_empty]
        simp
      rw [h]
      simp
    · have hS_nonempty : S.Nonempty := Set.nonempty_iff_ne_empty.mpr hS_empty
      have h_main : ∀ (x : EuclideanSpace ℝ (Fin m)), x ∈ U →
          ∃ (W : Set (EuclideanSpace ℝ (Fin m))), IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧
            (volume : Measure ℝ) (g '' (S ∩ W)) = 0 := by
        intro x hx
        have h_nhds : U ∈ nhds x := hU_open.mem_nhds hx
        rcases Metric.mem_nhds_iff.mp h_nhds with ⟨d, d_pos, hd⟩
        have h_d4_pos : 0 < d / 4 := by linarith
        have h_d4_lt_d2 : d / 4 < d / 2 := by linarith
        let c : ContDiffBump x :=
          { rIn := d / 4
            rOut := d / 2
            rIn_pos := h_d4_pos
            rIn_lt_rOut := h_d4_lt_d2 }
        let b : EuclideanSpace ℝ (Fin m) → ℝ := c
        have hb_tsupp : tsupport b ⊆ U := by
          rw [c.tsupport_eq]
          have h1 : Metric.closedBall x (d / 2) ⊆ Metric.ball x d := by
            apply Metric.closedBall_subset_ball
            linarith
          have h2 : Metric.ball x d ⊆ U := hd
          exact h1.trans h2
        have hb_contDiff : ContDiff ℝ ∞ b := c.contDiff
        let W : Set (EuclideanSpace ℝ (Fin m)) := Metric.ball x (d / 4)
        have hW_open : IsOpen W := Metric.isOpen_ball
        have hW_mem : x ∈ W := Metric.mem_ball_self h_d4_pos
        have hW_sub : W ⊆ U := by
          have h1 : Metric.ball x (d / 4) ⊆ Metric.ball x d := by
            apply Metric.ball_subset_ball
            linarith
          exact h1.trans hd
        have hW_eq1 : ∀ y ∈ W, b y = 1 := by
          intro y hy
          apply c.one_of_mem_closedBall
          exact Metric.ball_subset_closedBall hy
        let g' : EuclideanSpace ℝ (Fin m) → ℝ := fun y => b y * g y
        have hg'_diff : ContDiff ℝ ∞ g' := by
          rw [contDiff_iff_contDiffAt]
          intro y
          by_cases hy : y ∈ tsupport b
          · -- Case 1: y ∈ tsupport b, so y ∈ U
            have hyU : y ∈ U := hb_tsupp hy
            have hU_nhds : U ∈ nhds y := hU_open.mem_nhds hyU
            have h1 : ContDiffOn ℝ ∞ g' U := hb_contDiff.contDiffOn.mul hg
            exact h1.contDiffAt hU_nhds
          · -- Case 2: y ∉ tsupport b, so b =ᶠ[nhds y] 0
            have h2 : b =ᶠ[nhds y] 0 := notMem_tsupport_iff_eventuallyEq.mp hy
            have h3 : g' =ᶠ[nhds y] 0 := by
              filter_upwards [h2] with z hz
              simp [g', hz]
            exact (contDiff_const : ContDiff ℝ ∞ (fun _ : EuclideanSpace ℝ (Fin m) => (0 : ℝ))).contDiffAt.congr_of_eventuallyEq h3
        have h2 : ∀ y ∈ W, fderiv ℝ g' y = fderiv ℝ g y := by
          intro y hy
          have h4 : ∀ᶠ z in nhds y, b z = 1 := by
            have h5 : W ∈ nhds y := hW_open.mem_nhds hy
            filter_upwards [h5] with z hz
            exact hW_eq1 z hz
          have h5 : g' =ᶠ[nhds y] g := by
            filter_upwards [h4] with z hz
            simp [g', hz]
          exact h5.fderiv_eq
        have h6 : S ∩ W ⊆ {x | fderiv ℝ g' x = 0} := by
          intro z hz
          have hz1 : z ∈ S := hz.1
          have hz2 : z ∈ W := hz.2
          have hz3 : fderiv ℝ g z = 0 := hz1.2
          have hz4 : fderiv ℝ g' z = fderiv ℝ g z := h2 z hz2
          have hz5 : fderiv ℝ g' z = 0 := by
            rw [hz4, hz3]
          exact hz5
        have h7 : g '' (S ∩ W) ⊆ g' '' {x | fderiv ℝ g' x = 0} := by
          intro z hz
          rcases hz with ⟨y, hy, rfl⟩
          have hy' : y ∈ {x | fderiv ℝ g' x = 0} := h6 hy
          have h_eq : g y = g' y := by
            have h : g' y = b y * g y := rfl
            rw [h, hW_eq1 y hy.2, one_mul]
          rw [h_eq]
          exact ⟨y, hy', rfl⟩
        have h8 : (volume : Measure ℝ) (g' '' {x | fderiv ℝ g' x = 0}) = 0 := ih g' hg'_diff
        have h9 : (volume : Measure ℝ) (g '' (S ∩ W)) = 0 :=
          measure_mono_null h7 h8
        exact ⟨W, hW_open, hW_mem, hW_sub, h9⟩
      have h_cover : ∀ (x : {x // x ∈ S}), ∃ (W : Set (EuclideanSpace ℝ (Fin m))), IsOpen W ∧ (x : EuclideanSpace ℝ (Fin m)) ∈ W ∧
          (volume : Measure ℝ) (g '' (S ∩ W)) = 0 := by
        intro x
        have hxU : (x : EuclideanSpace ℝ (Fin m)) ∈ U := x.property.1
        rcases h_main (x : EuclideanSpace ℝ (Fin m)) hxU with ⟨W, hW_open, hW_mem, _, hW_null⟩
        exact ⟨W, hW_open, hW_mem, hW_null⟩
      choose W hW_open hW_mem hW_null using h_cover
      have hS_cover : S ⊆ ⋃ x : {x // x ∈ S}, W x := by
        intro y hy
        let y' : {x // x ∈ S} := ⟨y, hy⟩
        have h : y ∈ W y' := hW_mem y'
        exact Set.mem_iUnion_of_mem y' h
      have h_secondCountable : SecondCountableTopology (EuclideanSpace ℝ (Fin m)) := by infer_instance
      have h_all_open : ∀ (i : {x // x ∈ S}), IsOpen (W i) := hW_open
      obtain ⟨T, hT_count, hT_cover⟩ := TopologicalSpace.isOpen_iUnion_countable W h_all_open
      have hT_nonempty : T.Nonempty := by
        by_contra h
        have hT_empty : T = ∅ := by
          simpa [Set.not_nonempty_iff_eq_empty] using h
        rw [hT_empty] at hT_cover
        have h1 : (⋃ t ∈ (∅ : Set {x // x ∈ S}), W t) = ∅ := by simp
        have h2 : (⋃ t ∈ (∅ : Set {x // x ∈ S}), W t) = (⋃ x : {x // x ∈ S}, W x) := hT_cover
        have h3 : (⋃ x : {x // x ∈ S}, W x) = ∅ := by
          rw [←h2, h1]
        have h4 : S ⊆ ∅ := by
          calc S
            ⊆ ⋃ x : {x // x ∈ S}, W x := hS_cover
          _ = ∅ := h3
        have h5 : S = ∅ := by simpa using h4
        exact hS_empty h5
      obtain ⟨g0, h_eq_range⟩ := hT_count.exists_eq_range hT_nonempty
      let W' : ℕ → Set (EuclideanSpace ℝ (Fin m)) := fun n => W (g0 n)
      have h_cover' : S ⊆ ⋃ n, W' n := by
        calc S
          ⊆ ⋃ x : {x // x ∈ S}, W x := hS_cover
        _ = ⋃ t ∈ T, W t := by rw [hT_cover]
        _ = ⋃ n, W' n := by
          rw [h_eq_range]
          ext y
          simp [W']
      have h10 : g '' S ⊆ ⋃ n, g '' (S ∩ W' n) := by
        intro z hz
        rcases hz with ⟨x, hx, rfl⟩
        have hx_in_union : x ∈ ⋃ n, W' n := h_cover' hx
        rcases Set.mem_iUnion.mp hx_in_union with ⟨n, hxn⟩
        have h_x_in_inter : x ∈ S ∩ W' n := ⟨hx, hxn⟩
        have h_z_in_image : g x ∈ g '' (S ∩ W' n) := Set.mem_image_of_mem g h_x_in_inter
        exact Set.mem_iUnion.mpr ⟨n, h_z_in_image⟩
      have h11 : ∀ n, (volume : Measure ℝ) (g '' (S ∩ W' n)) = 0 := by
        intro n
        exact hW_null (g0 n)
      have h12 : (volume : Measure ℝ) (⋃ n, g '' (S ∩ W' n)) = 0 :=
        measure_iUnion_null h11
      exact measure_mono_null h10 h12
  simpa [S] using h_goal


end ForMathlib.Analysis.Calculus.Sard
