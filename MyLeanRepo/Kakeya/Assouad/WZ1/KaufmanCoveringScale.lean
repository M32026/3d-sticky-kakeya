import MyLeanRepo.Kakeya.Assouad.Definitions
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Data.Real.Basic

/-!
# Real-line covering numbers under positive scaling

This is the homothety transport needed by the Kaufman-to-dot-difference step.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

/-- Positive homotheties preserve external covering numbers after scaling the radius. -/
lemma external_covering_number_scaling_real
    {S : Set ℝ} {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) :
    Metric.externalCoveringNumber (Real.toNNReal (c * ε))
        ((fun x : ℝ => c * x) '' S) =
      Metric.externalCoveringNumber (Real.toNNReal ε) S := by
  let f : ℝ → ℝ := fun x => c * x
  let g : ℝ → ℝ := fun y => y / c
  have hfg : ∀ x, g (f x) = x := by
    intro x
    dsimp only [f, g]
    field_simp [hc.ne'] <;> ring
  have hf_inj : Function.Injective f := by
    intro x y h
    simpa [f, hc.ne'] using h
  have hg_inj : Function.Injective g := by
    intro x y h
    simpa [g, hc.ne'] using h
  have h_dist_scale : ∀ (x y : ℝ), dist (f x) (f y) = c * dist x y := by
    intro x y
    have h1 : dist (f x) (f y) = |c * x - c * y| := by
      simp [f, dist_eq_norm, Real.norm_eq_abs] <;> ring
    have h2 : |c * x - c * y| = c * |x - y| := by
      have h21 : c * x - c * y = c * (x - y) := by ring
      rw [h21, abs_mul, abs_of_pos hc]
    have h3 : c * dist x y = c * |x - y| := by
      simp [dist_eq_norm, Real.norm_eq_abs]
    rw [h1, h2, h3]
  have hg_dist : ∀ (a b : ℝ), dist (g a) (g b) = dist a b / c := by
    intro a b
    have h1 : dist (g a) (g b) = |a / c - b / c| := by
      simp [g, dist_eq_norm, Real.norm_eq_abs]
    have h2 : |a / c - b / c| = |a - b| / c := by
      have h3 : a / c - b / c = (a - b) / c := by ring
      rw [h3, abs_div, abs_of_pos hc]
    have h4 : dist a b / c = |a - b| / c := by
      simp [dist_eq_norm, Real.norm_eq_abs]
    rw [h1, h2, h4]
  let ε_nn : NNReal := Real.toNNReal ε
  let cε_nn : NNReal := Real.toNNReal (c * ε)
  have hε_nn_val : (ε_nn : ℝ) = ε := by
    simp [ε_nn, Real.toNNReal_of_nonneg hε.le]
  have hcε_nn_val : (cε_nn : ℝ) = c * ε := by
    simp [cε_nn, Real.toNNReal_of_nonneg (mul_nonneg hc.le hε.le)]
  have h_main1 : ∀ (C : Set ℝ), IsCover ε_nn S C →
      IsCover cε_nn (f '' S) (f '' C) := by
    intro C hC
    intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    rcases hC hx with ⟨y, hy, hdist⟩
    refine ⟨f y, Set.mem_image_of_mem f hy, ?_⟩
    have h1 : dist (f x) (f y) = c * dist x y := h_dist_scale x y
    have h2 : dist x y ≤ (ε_nn : ℝ) := by
      exact_mod_cast hdist
    have h2' : dist x y ≤ ε := by
      rw [← hε_nn_val]
      exact h2
    have h3 : dist (f x) (f y) ≤ (cε_nn : ℝ) := by
      rw [h1, hcε_nn_val]
      gcongr
    exact_mod_cast h3
  have h_main2 : ∀ (C' : Set ℝ), IsCover cε_nn (f '' S) C' →
      IsCover ε_nn S (g '' C') := by
    intro C' hC'
    intro x hx
    have hfx : f x ∈ f '' S := ⟨x, hx, rfl⟩
    rcases hC' hfx with ⟨z, hz, hdist⟩
    refine ⟨g z, Set.mem_image_of_mem g hz, ?_⟩
    have h1 : dist (f x) z ≤ (cε_nn : ℝ) := by
      exact_mod_cast hdist
    have h_eq : x = g (f x) := (hfg x).symm
    have h21 : dist x (g z) = dist (g (f x)) (g z) := by
      exact congr_arg (fun y : ℝ => dist y (g z)) h_eq
    have h2 : dist x (g z) = dist (f x) z / c := by
      rw [h21]
      exact hg_dist (f x) z
    have h3 : dist x (g z) ≤ (ε_nn : ℝ) := by
      rw [h2, hε_nn_val]
      calc
        dist (f x) z / c ≤ (cε_nn : ℝ) / c := by gcongr
        _ = ε := by
          rw [hcε_nn_val]
          field_simp [hc.ne'] <;> ring
    exact_mod_cast h3
  have h_forward :
      Metric.externalCoveringNumber cε_nn (f '' S) ≤
        Metric.externalCoveringNumber ε_nn S := by
    simp only [Metric.externalCoveringNumber, le_iInf_iff]
    intro C hC
    have hcover := h_main1 C hC
    have h4 : Metric.externalCoveringNumber cε_nn (f '' S) ≤ (f '' C).encard :=
      hcover.externalCoveringNumber_le_encard
    have h5 : (f '' C).encard = C.encard := hf_inj.encard_image C
    rw [h5] at h4
    exact h4
  have h_backward :
      Metric.externalCoveringNumber ε_nn S ≤
        Metric.externalCoveringNumber cε_nn (f '' S) := by
    simp only [Metric.externalCoveringNumber, le_iInf_iff]
    intro C' hC'
    have hcover := h_main2 C' hC'
    have h4 : Metric.externalCoveringNumber ε_nn S ≤ (g '' C').encard :=
      hcover.externalCoveringNumber_le_encard
    have h5 : (g '' C').encard = C'.encard := hg_inj.encard_image C'
    rw [h5] at h4
    exact h4
  exact le_antisymm h_forward h_backward

/-- On a finite subset of `ℝ`, doubling the covering radius loses at most a factor two. -/
lemma external_covering_number_double_real
    {S : Set ℝ} {ε : ℝ} (hε : 0 < ε) (hS : Set.Finite S) :
    Metric.externalCoveringNumber (Real.toNNReal ε) S ≤
      2 * Metric.externalCoveringNumber (Real.toNNReal (2 * ε)) S := by
  let ε' : NNReal := ⟨ε, hε.le⟩
  let ε2' : NNReal := ⟨2 * ε, by linarith⟩
  have h_coe2 : (ε2' : ENNReal) = ENNReal.ofReal (2 * ε) := by
    have h1 : (ε2' : ℝ) = 2 * ε := Subtype.coe_mk (2 * ε) _
    have h2 : (ε2' : ENNReal) = ENNReal.ofReal (ε2' : ℝ) :=
      ENNReal.coe_nnreal_eq ε2'
    rw [h2, h1]
  have h_coe1 : (ε' : ENNReal) = ENNReal.ofReal ε := by
    have h1 : (ε' : ℝ) = ε := Subtype.coe_mk ε _
    have h2 : (ε' : ENNReal) = ENNReal.ofReal (ε' : ℝ) :=
      ENNReal.coe_nnreal_eq ε'
    rw [h2, h1]
  have h_main : ∀ (C : Set ℝ), Metric.IsCover ε2' S C →
      Metric.externalCoveringNumber ε' S ≤ 2 * C.encard := by
    intro C hC
    let C' : Set ℝ := (fun c : ℝ => c - ε) '' C ∪ (fun c : ℝ => c + ε) '' C
    have hC'_cover : Metric.IsCover ε' S C' := by
      intro x hx
      obtain ⟨c, hc, hdist⟩ := hC hx
      have h_dist_real : dist x c ≤ 2 * ε := by
        have h : edist x c ≤ (ε2' : ENNReal) := by simpa using hdist
        rw [h_coe2] at h
        have h3 : edist x c = ENNReal.ofReal (dist x c) := edist_dist x c
        rw [h3] at h
        exact ENNReal.ofReal_le_ofReal_iff (by linarith) |>.mp h
      have h_abs : |x - c| ≤ 2 * ε := by
        simpa [dist_eq_norm, Real.norm_eq_abs] using h_dist_real
      by_cases h : x ≤ c
      · have h2 : dist x (c - ε) ≤ ε := by
          simpa [dist_eq_norm, Real.norm_eq_abs] using
            show |x - (c - ε)| ≤ ε by
              have h4 : |x - c + ε| ≤ ε := by
                rw [abs_le]
                constructor <;> linarith [abs_le.mp h_abs]
              have h5 : x - (c - ε) = x - c + ε := by ring
              rw [h5]
              exact h4
        have hmem : c - ε ∈ C' := Or.inl ⟨c, hc, by ring⟩
        have h6 : edist x (c - ε) ≤ (ε' : ENNReal) := by
          rw [h_coe1, edist_dist]
          exact ENNReal.ofReal_le_ofReal h2
        exact ⟨c - ε, hmem, h6⟩
      · have h2 : dist x (c + ε) ≤ ε := by
          simpa [dist_eq_norm, Real.norm_eq_abs] using
            show |x - (c + ε)| ≤ ε by
              have h4 : |x - c - ε| ≤ ε := by
                rw [abs_le]
                constructor <;> linarith [abs_le.mp h_abs]
              have h5 : x - (c + ε) = x - c - ε := by ring
              rw [h5]
              exact h4
        have hmem : c + ε ∈ C' := Or.inr ⟨c, hc, by ring⟩
        have h6 : edist x (c + ε) ≤ (ε' : ENNReal) := by
          rw [h_coe1, edist_dist]
          exact ENNReal.ofReal_le_ofReal h2
        exact ⟨c + ε, hmem, h6⟩
    have h1 : Metric.externalCoveringNumber ε' S ≤ C'.encard :=
      Metric.IsCover.externalCoveringNumber_le_encard hC'_cover
    have h_img1 : ((fun c : ℝ => c - ε) '' C).encard ≤ C.encard :=
      Set.encard_image_le _ _
    have h_img2 : ((fun c : ℝ => c + ε) '' C).encard ≤ C.encard :=
      Set.encard_image_le _ _
    have h_union : C'.encard ≤
        ((fun c : ℝ => c - ε) '' C).encard +
          ((fun c : ℝ => c + ε) '' C).encard :=
      Set.encard_union_le _ _
    have h_sum : ((fun c : ℝ => c - ε) '' C).encard +
          ((fun c : ℝ => c + ε) '' C).encard ≤ C.encard + C.encard :=
      add_le_add h_img1 h_img2
    have h3 : C'.encard ≤ 2 * C.encard := by
      calc
        C'.encard ≤ _ := h_union
        _ ≤ C.encard + C.encard := h_sum
        _ = 2 * C.encard := by ring
    exact h1.trans (h3.trans_eq rfl)
  let Covers : Set (Set ℝ) := {C | Metric.IsCover ε2' S C}
  let I : Set ENat := Set.image (fun C : Set ℝ => C.encard) Covers
  have hI_nonempty : I.Nonempty := by
    refine ⟨S.encard, ?_⟩
    exact ⟨S, by simp [Covers], rfl⟩
  have h_attained : sInf I ∈ I := csInf_mem hI_nonempty
  rcases h_attained with ⟨C, hC_in_Covers, hC_eq⟩
  have hC_cover : Metric.IsCover ε2' S C := hC_in_Covers
  have h_bdd : BddBelow I := ⟨0, fun _ _ => bot_le⟩
  have h_ext_eq : Metric.externalCoveringNumber ε2' S = sInf I := by
    have h1 : Metric.externalCoveringNumber ε2' S ≤ sInf I := by
      apply le_csInf hI_nonempty
      intro x hx
      rcases hx with ⟨C, hC, rfl⟩
      exact Metric.IsCover.externalCoveringNumber_le_encard hC
    have h2 : sInf I ≤ Metric.externalCoveringNumber ε2' S := by
      rw [Metric.externalCoveringNumber]
      apply le_iInf
      intro C
      by_cases hC : Metric.IsCover ε2' S C
      · haveI : Nonempty (Metric.IsCover ε2' S C) := ⟨hC⟩
        have h5 : (⨅ (_ : Metric.IsCover ε2' S C), C.encard) = C.encard :=
          iInf_const
        rw [h5]
        exact csInf_le h_bdd ⟨C, hC, rfl⟩
      · have h_empt : IsEmpty (Metric.IsCover ε2' S C) :=
          ⟨fun h => hC h⟩
        rw [iInf_of_empty]
        simp
    exact le_antisymm h1 h2
  have hC_encard_eq : C.encard = Metric.externalCoveringNumber ε2' S := by
    rw [h_ext_eq]
    exact hC_eq
  have h_final : Metric.externalCoveringNumber ε' S ≤ 2 * C.encard :=
    h_main C hC_cover
  have h_goal : Metric.externalCoveringNumber ε' S ≤
      2 * Metric.externalCoveringNumber ε2' S := by
    rw [hC_encard_eq] at h_final
    exact h_final
  have h_eps' : ε' = Real.toNNReal ε := by
    have h : (ε' : ℝ) = (Real.toNNReal ε : ℝ) := by
      rw [Real.toNNReal_of_nonneg hε.le]
      exact Subtype.coe_mk ε _
    exact Subtype.ext h
  have h_eps2' : ε2' = Real.toNNReal (2 * ε) := by
    have h : (ε2' : ℝ) = (Real.toNNReal (2 * ε) : ℝ) := by
      rw [Real.toNNReal_of_nonneg (by linarith)]
      exact Subtype.coe_mk (2 * ε) _
    exact Subtype.ext h
  rw [h_eps', h_eps2'] at h_goal
  exact h_goal

end Kakeya.Assouad
