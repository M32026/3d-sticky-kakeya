import MyLeanRepo.Kakeya.Assouad.Definitions
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Local Lipschitz thickening containment

Version of `lipschitzWith_image_cthickening` for maps that are only
Lipschitz on a domain containing the thickened set.
-/

noncomputable section

namespace Kakeya.Assouad

open Set Metric

/--
A local version of `lipschitzWith_image_cthickening`.

If `f` is `L`-Lipschitz on `S`, and the `ρ`-thickening of `A` stays within `S`,
then the image of the thickening is contained in the `(L*ρ)`-thickening of the image.
-/
lemma lipschitzOn_image_cthickening
    {X Y : Type _} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {f : X → Y} {S A : Set X} {ρ : ℝ} {L : NNReal}
    (hf : LipschitzOnWith L f S) (hthick : cthickening ρ A ⊆ S)
    (_hr : 0 ≤ ρ) :
    f '' (cthickening ρ A) ⊆ cthickening ((L : ℝ) * ρ) (f '' A) := by
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  have hxs : x ∈ S := hthick hx
  have h1 : infEDist x A ≤ ENNReal.ofReal ρ := by
    simpa [cthickening_eq_preimage_infEDist] using hx
  by_cases hS : A = ∅
  · simp [hS] at h1
  · have hS' : A.Nonempty := Set.nonempty_iff_ne_empty.mpr hS
    letI : Nonempty A := hS'.to_subtype
    have hA_sub_S : A ⊆ S := by
      intro z hz
      have hzin : z ∈ cthickening ρ A := by
        simpa [cthickening_eq_preimage_infEDist] using
          (Metric.infEDist_le_edist_of_mem hz).trans (by simp)
      exact hthick hzin
    have h21 : ∀ (y : A), infEDist (f x) (f '' A) ≤ edist (f x) (f y) := by
      intro y
      apply Metric.infEDist_le_edist_of_mem
      exact ⟨y, y.property, rfl⟩
    have h22 : infEDist (f x) (f '' A) ≤ iInf (fun y : A => edist (f x) (f y)) := by
      exact le_iInf h21
    have h23 : iInf (fun y : A => edist (f x) (f y)) ≤
        iInf (fun y : A => (L : ENNReal) * edist x y) := by
      apply iInf_mono
      intro y
      have hys : y.val ∈ S := hA_sub_S y.property
      have hdist : dist (f x) (f y.val) ≤ (L : ℝ) * dist x y.val :=
        hf.dist_le_mul x hxs y.val hys
      have h_edist : edist (f x) (f y.val) ≤ (L : ENNReal) * edist x y.val := by
        rw [edist_dist, edist_dist]
        have h : ENNReal.ofReal (dist (f x) (f y.val)) ≤
            ENNReal.ofReal ((L : ℝ) * dist x y.val) :=
          ENNReal.ofReal_le_ofReal hdist
        have h2 : ENNReal.ofReal ((L : ℝ) * dist x y.val) =
            (L : ENNReal) * ENNReal.ofReal (dist x y.val) := by
          rw [ENNReal.ofReal_mul (show 0 ≤ (L : ℝ) from by positivity)]
          have h3 : ENNReal.ofReal (L : ℝ) = (L : ENNReal) :=
            ENNReal.ofReal_coe_nnreal
          rw [h3]
        rw [h2] at h
        exact h
      exact h_edist
    have h24 : iInf (fun y : A => (L : ENNReal) * edist x y) =
        (L : ENNReal) * iInf (fun y : A => edist x y) := by
      have h : (iInf (fun y : A => edist x y)) * (L : ENNReal) =
          iInf (fun y : A => (edist x y) * (L : ENNReal)) :=
        ENNReal.iInf_mul' (hinfty := by simp) (h₀ := by intro _; exact inferInstance)
      have h' : iInf (fun y : A => (L : ENNReal) * edist x y) =
          iInf (fun y : A => (edist x y) * (L : ENNReal)) := by
        congr with y; exact mul_comm _ _
      rw [h']
      rw [← h]
      exact mul_comm _ _
    have h25 : infEDist (f x) (f '' A) ≤ (L : ENNReal) * infEDist x A := by
      calc infEDist (f x) (f '' A)
          ≤ iInf (fun y : A => edist (f x) (f y)) := h22
        _ ≤ iInf (fun y : A => (L : ENNReal) * edist x y) := h23
        _ = (L : ENNReal) * iInf (fun y : A => edist x y) := h24
        _ = (L : ENNReal) * infEDist x A := by
          have h_eq : iInf (fun y : A => edist x y) = infEDist x A := by
            simpa [Metric.infEDist] using iInf_subtype'' A (fun y => edist x y)
          rw [h_eq]
    have h6 : (L : ENNReal) * infEDist x A ≤ (L : ENNReal) * ENNReal.ofReal ρ := by
      gcongr
    have h7 : (L : ENNReal) * ENNReal.ofReal ρ = ENNReal.ofReal ((L : ℝ) * ρ) := by
      have h71 : (L : ENNReal) = ENNReal.ofReal (L : ℝ) :=
        ENNReal.ofReal_coe_nnreal.symm
      rw [h71]
      rw [← ENNReal.ofReal_mul (show 0 ≤ (L : ℝ) from by positivity)]
    rw [h7] at h6
    have h8 : infEDist (f x) (f '' A) ≤ ENNReal.ofReal ((L : ℝ) * ρ) := le_trans h25 h6
    simpa [cthickening_eq_preimage_infEDist] using h8

end Kakeya.Assouad
