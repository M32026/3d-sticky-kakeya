import MyLeanRepo.Kakeya.Assouad.WZ1.ProjectionTheoremFirstLayerStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.WellSeparatedRestriction
import MyLeanRepo.Kakeya.Assouad.WZ1.KatzTaoToFrostmanHelpers
import MyLeanRepo.Kakeya.Assouad.WZ1.GridCenter
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Affine normalization for WZ1 removal of standard separation

Implements the paper's "final reduction" (Section 8, proof of Theorem 22'):
given KatzTao sets F, G₁, G₂ and a large tripartite graph H, restrict to
small grid cells, dilate independently, and obtain standard-separated Frostman
sets with a uniformly dense transformed graph.

## Main steps

1. Small-product vacuous B (existing lemma)
2. KatzTao to Frostman conversion (existing lemma)
3. Standard separation from geometric configuration
4. Grid partition and pigeonhole
5. Frostman and graph transport under dilation
6. Conclusion transport back
-/

noncomputable section

namespace Kakeya.Assouad

open scoped ENNReal
open Classical

variable {δ : ℝ}

/-- Scaling a discrete set by `s : ℝ`. -/
def scaleSet {n : ℕ} (s : ℝ) (A : DiscreteSet n) : DiscreteSet n :=
  A.image (fun x => s • x)

/-- Distance scales by `|s|` under scalar multiplication. -/
lemma dist_smul_real {n : ℕ} {s : ℝ} {x y : Point n} :
    dist (s • x) (s • y) = |s| * dist x y := by
  have h1 : s • x - s • y = s • (x - y) := by
    rw [smul_sub]
  rw [dist_eq_norm, dist_eq_norm, h1]
  exact norm_smul s (x - y)

/-- Translation preserves distance. -/
lemma dist_add_right {n : ℕ} {t x y : Point n} :
    dist (x + t) (y + t) = dist x y := by
  simp [dist_eq_norm]

/-! ## Step 1: Standard separation construction -/

/--
Given three small sets with controlled positions, construct dilated/translated
sets satisfying `WZ1StandardSeparation` and contained in the unit ball.

Scaling choices:
- `s_F = 1 / (‖f_center‖ + r_F)`: F points have norm ≤ 1
- `s_G = 2 / (D_G + 2 * r_G)` where `D_G = dist g1_center g2_center`, translate G midpoint to 0: G points have norm ≤ 1

Ratio requirements:
- `‖f_center‖ ≥ 19 * r_F` (ensures F diameter ≤ 1/10 and dist ≥ 1/2)
- `D_G ≥ 38 * r_G` (ensures G diameter ≤ 1/10 and mutual separation ≥ 1/2)
-/
lemma standard_separation_from_geometry
    {F' G1' G2' : DiscreteSet 2}
    {f_center g1_center g2_center : Point2}
    {r_F r_G : ℝ}
    (hF_ball : ∀ x ∈ F', dist x f_center ≤ r_F)
    (hG1_ball : ∀ x ∈ G1', dist x g1_center ≤ r_G)
    (hG2_ball : ∀ x ∈ G2', dist x g2_center ≤ r_G)
    (hF_unit : ∀ x ∈ F', dist x 0 ≤ 1)
    (hG1_unit : ∀ x ∈ G1', dist x 0 ≤ 1)
    (hG2_unit : ∀ x ∈ G2', dist x 0 ≤ 1)
    (hrF_pos : 0 < r_F) (hrG_pos : 0 < r_G)
    (h_ratio_F : 19 * r_F ≤ dist f_center 0)
    (h_ratio_G : 38 * r_G ≤ dist g1_center g2_center) :
    ∃ (s_F s_G : ℝ) (t_G : Point2),
      let F'' := scaleSet s_F F'
      let G1'' := (scaleSet s_G G1').image (fun x => x + t_G)
      let G2'' := (scaleSet s_G G2').image (fun x => x + t_G)
      WZ1StandardSeparation F'' G1'' G2'' ∧
      0 < s_F ∧ 0 < s_G ∧
      (∀ x ∈ F'', dist x 0 ≤ 1) ∧
      (∀ x ∈ G1'', dist x 0 ≤ 1) ∧
      (∀ x ∈ G2'', dist x 0 ≤ 1) := by
  let d_F : ℝ := dist f_center 0
  have hdF_pos : 0 < d_F := by linarith [h_ratio_F]
  let s_F : ℝ := 1 / (d_F + r_F)
  have hsF_pos : 0 < s_F := by positivity
  let D_G : ℝ := dist g1_center g2_center
  have hD_G_pos : 0 < D_G := by linarith [h_ratio_G]
  let s_G : ℝ := 2 / (D_G + 2 * r_G)
  have hsG_pos : 0 < s_G := by positivity
  let midpoint : Point2 := (1 / 2 : ℝ) • (g1_center + g2_center)
  let t_G : Point2 := -s_G • midpoint

  let F'' := scaleSet s_F F'
  let G1'' := (scaleSet s_G G1').image (fun x => x + t_G)
  let G2'' := (scaleSet s_G G2').image (fun x => x + t_G)

  have hF_diam : ∀ x ∈ F'', ∀ y ∈ F'', dist x y ≤ 1 / 10 := by
    intro x hx y hy
    rcases Finset.mem_image.mp hx with ⟨x0, hx0, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨y0, hy0, rfl⟩
    have h : dist x0 y0 ≤ 2 * r_F := by
      have h1 : dist x0 y0 ≤ dist x0 f_center + dist f_center y0 := dist_triangle _ _ _
      have h2 : dist f_center y0 = dist y0 f_center := dist_comm _ _
      rw [h2] at h1
      linarith [hF_ball x0 hx0, hF_ball y0 hy0]
    have h2 : dist (s_F • x0) (s_F • y0) = s_F * dist x0 y0 := by
      rw [dist_smul_real, abs_of_pos hsF_pos]
    rw [h2]
    have h3 : s_F * dist x0 y0 ≤ s_F * (2 * r_F) := by gcongr
    have h4 : s_F * (2 * r_F) ≤ 1 / 10 := by
      dsimp only [s_F]
      have h5 : 2 * r_F ≤ (1 / 10 : ℝ) * (d_F + r_F) := by
        linarith [h_ratio_F]
      have h6 : (1 : ℝ) / (d_F + r_F) * (2 * r_F) ≤ 1 / 10 := by
        calc
          (1 : ℝ) / (d_F + r_F) * (2 * r_F)
            = (2 * r_F) / (d_F + r_F) := by ring
          _ ≤ 1 / 10 := by
            have h7 : 0 < d_F + r_F := by positivity
            have h8 : 2 * r_F ≤ (1 / 10 : ℝ) * (d_F + r_F) := by linarith [h_ratio_F]
            calc
              (2 * r_F) / (d_F + r_F)
                ≤ ((1 / 10 : ℝ) * (d_F + r_F)) / (d_F + r_F) := by gcongr
              _ = 1 / 10 := by field_simp [h7.ne'] <;> ring
      exact h6
    linarith

  have hG1_diam : ∀ x ∈ G1'', ∀ y ∈ G1'', dist x y ≤ 1 / 10 := by
    intro x hx y hy
    rcases Finset.mem_image.mp hx with ⟨x1, hx1, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨y1, hy1, rfl⟩
    rcases Finset.mem_image.mp hx1 with ⟨x0, hx0, rfl⟩
    rcases Finset.mem_image.mp hy1 with ⟨y0, hy0, rfl⟩
    have h : dist x0 y0 ≤ 2 * r_G := by
      have h1 : dist x0 y0 ≤ dist x0 g1_center + dist g1_center y0 := dist_triangle _ _ _
      have h2 : dist g1_center y0 = dist y0 g1_center := dist_comm _ _
      rw [h2] at h1
      linarith [hG1_ball x0 hx0, hG1_ball y0 hy0]
    have h2 : dist (s_G • x0 + t_G) (s_G • y0 + t_G) = s_G * dist x0 y0 := by
      have h3 : dist (s_G • x0 + t_G) (s_G • y0 + t_G) = dist (s_G • x0) (s_G • y0) := by
        exact dist_add_right
      rw [h3, dist_smul_real, abs_of_pos hsG_pos]
    rw [h2]
    have h3 : s_G * dist x0 y0 ≤ s_G * (2 * r_G) := by gcongr
    have h4 : s_G * (2 * r_G) ≤ 1 / 10 := by
      dsimp only [s_G]
      have h5 : 2 * r_G ≤ (1 / 10 : ℝ) * ((D_G + 2 * r_G) / 2) := by
        linarith [h_ratio_G]
      have h6 : (2 : ℝ) / (D_G + 2 * r_G) * (2 * r_G) ≤ 1 / 10 := by
        calc
          (2 : ℝ) / (D_G + 2 * r_G) * (2 * r_G)
            = (4 * r_G) / (D_G + 2 * r_G) := by ring
          _ ≤ 1 / 10 := by
            have h7 : 0 < D_G + 2 * r_G := by positivity
            have h8 : 4 * r_G ≤ (1 / 10 : ℝ) * (D_G + 2 * r_G) := by linarith [h_ratio_G]
            calc
              (4 * r_G) / (D_G + 2 * r_G)
                ≤ ((1 / 10 : ℝ) * (D_G + 2 * r_G)) / (D_G + 2 * r_G) := by gcongr
              _ = 1 / 10 := by field_simp [h7.ne'] <;> ring
      exact h6
    linarith

  have hG2_diam : ∀ x ∈ G2'', ∀ y ∈ G2'', dist x y ≤ 1 / 10 := by
    intro x hx y hy
    rcases Finset.mem_image.mp hx with ⟨x1, hx1, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨y1, hy1, rfl⟩
    rcases Finset.mem_image.mp hx1 with ⟨x0, hx0, rfl⟩
    rcases Finset.mem_image.mp hy1 with ⟨y0, hy0, rfl⟩
    have h : dist x0 y0 ≤ 2 * r_G := by
      have h1 : dist x0 y0 ≤ dist x0 g2_center + dist g2_center y0 := dist_triangle _ _ _
      have h2 : dist g2_center y0 = dist y0 g2_center := dist_comm _ _
      rw [h2] at h1
      linarith [hG2_ball x0 hx0, hG2_ball y0 hy0]
    have h2 : dist (s_G • x0 + t_G) (s_G • y0 + t_G) = s_G * dist x0 y0 := by
      have h3 : dist (s_G • x0 + t_G) (s_G • y0 + t_G) = dist (s_G • x0) (s_G • y0) := by
        exact dist_add_right
      rw [h3, dist_smul_real, abs_of_pos hsG_pos]
    rw [h2]
    have h3 : s_G * dist x0 y0 ≤ s_G * (2 * r_G) := by gcongr
    have h4 : s_G * (2 * r_G) ≤ 1 / 10 := by
      dsimp only [s_G]
      have h6 : (2 : ℝ) / (D_G + 2 * r_G) * (2 * r_G) ≤ 1 / 10 := by
        calc
          (2 : ℝ) / (D_G + 2 * r_G) * (2 * r_G)
            = (4 * r_G) / (D_G + 2 * r_G) := by ring
          _ ≤ 1 / 10 := by
            have h7 : 0 < D_G + 2 * r_G := by positivity
            have h8 : 4 * r_G ≤ (1 / 10 : ℝ) * (D_G + 2 * r_G) := by linarith [h_ratio_G]
            calc
              (4 * r_G) / (D_G + 2 * r_G)
                ≤ ((1 / 10 : ℝ) * (D_G + 2 * r_G)) / (D_G + 2 * r_G) := by gcongr
              _ = 1 / 10 := by field_simp [h7.ne'] <;> ring
      exact h6
    linarith

  have hG_sep : WZ1MutuallySeparated G1'' G2'' (1 / 2) := by
    intro x hx y hy
    rcases Finset.mem_image.mp hx with ⟨x1, hx1, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨y1, hy1, rfl⟩
    rcases Finset.mem_image.mp hx1 with ⟨x0, hx0, rfl⟩
    rcases Finset.mem_image.mp hy1 with ⟨y0, hy0, rfl⟩
    have h_x1 : dist x0 g1_center ≤ r_G := hG1_ball x0 hx0
    have h_y1 : dist y0 g2_center ≤ r_G := hG2_ball y0 hy0
    have h_low : dist x0 y0 ≥ D_G - 2 * r_G := by
      have h1 : dist g1_center g2_center ≤ dist g1_center x0 + dist x0 y0 + dist y0 g2_center :=
        dist_triangle4 _ _ _ _
      have h2 : dist g1_center x0 ≤ r_G := by
        have h21 : dist g1_center x0 = dist x0 g1_center := dist_comm _ _
        rw [h21]
        exact h_x1
      have h3 : dist y0 g2_center ≤ r_G := h_y1
      have h4 : dist g1_center g2_center ≤ dist x0 y0 + 2 * r_G := by
        linarith
      linarith
    have h2 : dist (s_G • x0 + t_G) (s_G • y0 + t_G) = s_G * dist x0 y0 := by
      have h3 : dist (s_G • x0 + t_G) (s_G • y0 + t_G) = dist (s_G • x0) (s_G • y0) := by
        exact dist_add_right
      rw [h3, dist_smul_real, abs_of_pos hsG_pos]
    rw [h2]
    have h3 : s_G * (D_G - 2 * r_G) ≥ 1 / 2 := by
      dsimp only [s_G]
      have h4 : 2 * (D_G - 2 * r_G) ≥ (1 / 2 : ℝ) * (D_G + 2 * r_G) := by
        linarith [h_ratio_G]
      have h5 : 0 < D_G + 2 * r_G := by positivity
      have h6 : (2 : ℝ) / (D_G + 2 * r_G) * (D_G - 2 * r_G) ≥ 1 / 2 := by
        calc
          (2 : ℝ) / (D_G + 2 * r_G) * (D_G - 2 * r_G)
            = (2 * (D_G - 2 * r_G)) / (D_G + 2 * r_G) := by ring
          _ ≥ 1 / 2 := by
            have h7 : 0 < D_G + 2 * r_G := by positivity
            have h8 : 2 * (D_G - 2 * r_G) ≥ (1 / 2 : ℝ) * (D_G + 2 * r_G) := by linarith [h_ratio_G]
            calc
              (2 * (D_G - 2 * r_G)) / (D_G + 2 * r_G)
                ≥ ((1 / 2 : ℝ) * (D_G + 2 * r_G)) / (D_G + 2 * r_G) := by gcongr
              _ = 1 / 2 := by field_simp [h7.ne'] <;> ring
      exact h6
    have h4 : s_G * dist x0 y0 ≥ s_G * (D_G - 2 * r_G) := by gcongr
    have h5 : s_G * dist x0 y0 ≥ 1 / 2 := by linarith
    exact h5

  have hF_dist : ∀ x ∈ F'', 1 / 2 ≤ dist x 0 := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨x0, hx0, rfl⟩
    have h_x : dist x0 f_center ≤ r_F := hF_ball x0 hx0
    have h_low : dist x0 0 ≥ d_F - r_F := by
      have h1 : dist f_center 0 ≤ dist f_center x0 + dist x0 0 := dist_triangle _ _ _
      have h2 : dist f_center x0 ≤ r_F := by
        have h21 : dist f_center x0 = dist x0 f_center := dist_comm _ _
        rw [h21]
        exact h_x
      have h3 : dist f_center 0 ≤ r_F + dist x0 0 := by linarith
      linarith [hdF_pos]
    have h2 : dist (s_F • x0) 0 = s_F * dist x0 0 := by
      have h3 : dist (s_F • x0) 0 = dist (s_F • x0) (s_F • (0 : Point2)) := by simp
      rw [h3, dist_smul_real, abs_of_pos hsF_pos] <;> simp
    rw [h2]
    have h3 : s_F * (d_F - r_F) ≥ 1 / 2 := by
      dsimp only [s_F]
      have h4 : d_F - r_F ≥ (1 / 2 : ℝ) * (d_F + r_F) := by
        linarith [h_ratio_F]
      have h5 : 0 < d_F + r_F := by positivity
      have h6 : (1 : ℝ) / (d_F + r_F) * (d_F - r_F) ≥ 1 / 2 := by
        calc
          (1 : ℝ) / (d_F + r_F) * (d_F - r_F)
            = (d_F - r_F) / (d_F + r_F) := by ring
          _ ≥ 1 / 2 := by
            have h7 : 0 < d_F + r_F := by positivity
            have h8 : d_F - r_F ≥ (1 / 2 : ℝ) * (d_F + r_F) := by linarith [h_ratio_F]
            calc
              (d_F - r_F) / (d_F + r_F)
                ≥ ((1 / 2 : ℝ) * (d_F + r_F)) / (d_F + r_F) := by gcongr
              _ = 1 / 2 := by field_simp [h7.ne'] <;> ring
      exact h6
    have h4 : s_F * dist x0 0 ≥ s_F * (d_F - r_F) := by gcongr
    have h5 : s_F * dist x0 0 ≥ 1 / 2 := by linarith
    exact h5

  have hF_unit' : ∀ x ∈ F'', dist x 0 ≤ 1 := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨x0, hx0, rfl⟩
    have h_x : dist x0 f_center ≤ r_F := hF_ball x0 hx0
    have h_norm : dist x0 0 ≤ d_F + r_F := by
      calc
        dist x0 0 ≤ dist x0 f_center + dist f_center 0 := dist_triangle _ _ _
        _ ≤ r_F + d_F := by gcongr
        _ = d_F + r_F := by ring
    have h2 : dist (s_F • x0) 0 = s_F * dist x0 0 := by
      have h3 : dist (s_F • x0) 0 = dist (s_F • x0) (s_F • (0 : Point2)) := by simp
      rw [h3, dist_smul_real, abs_of_pos hsF_pos] <;> simp
    rw [h2]
    have h3 : s_F * dist x0 0 ≤ s_F * (d_F + r_F) := by gcongr
    have h4 : s_F * (d_F + r_F) = 1 := by
      dsimp only [s_F]
      have hpos : 0 < d_F + r_F := by positivity
      field_simp [hpos.ne'] <;> ring
    rw [h4] at h3
    exact h3

  have hG1_unit' : ∀ x ∈ G1'', dist x 0 ≤ 1 := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨x1, hx1, rfl⟩
    rcases Finset.mem_image.mp hx1 with ⟨x0, hx0, rfl⟩
    have h_x : dist x0 g1_center ≤ r_G := hG1_ball x0 hx0
    have h_c1 : dist (g1_center - midpoint) 0 = dist g1_center g2_center / 2 := by
      have h : g1_center - midpoint = (1 / 2 : ℝ) • (g1_center - g2_center) := by
        ext i
        fin_cases i <;> simp [midpoint, smul_sub, sub_smul] <;> ring
      rw [h]
      have h0 : (0 : Point2) = (1 / 2 : ℝ) • (0 : Point2) := by simp
      rw [h0]
      have h1 : dist ((1 / 2 : ℝ) • (g1_center - g2_center)) ((1 / 2 : ℝ) • (0 : Point2)) =
          (1 / 2 : ℝ) * dist (g1_center - g2_center) 0 := by
        rw [dist_smul_real, abs_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)]
      rw [h1]
      have h2 : dist (g1_center - g2_center) 0 = dist g1_center g2_center := by
        simp [dist_eq_norm]
      rw [h2] <;> ring
    have h_norm : dist (x0 - midpoint) 0 ≤ dist g1_center g2_center / 2 + r_G := by
      calc
        dist (x0 - midpoint) 0
          = dist x0 midpoint := by simp [dist_eq_norm] <;> ring_nf
        _ ≤ dist x0 g1_center + dist g1_center midpoint := dist_triangle _ _ _
        _ ≤ r_G + dist g1_center midpoint := by gcongr
        _ = r_G + dist g1_center g2_center / 2 := by
          have h : dist g1_center midpoint = dist g1_center g2_center / 2 := by
            have h2 : g1_center - midpoint = (1 / 2 : ℝ) • (g1_center - g2_center) := by
              ext i
              fin_cases i <;> simp [midpoint, smul_sub, sub_smul] <;> ring
            have h3 : dist g1_center midpoint = dist (g1_center - midpoint) 0 := by
              simp [dist_eq_norm] <;> ring_nf
            rw [h3, h2]
            have h0 : (0 : Point2) = (1 / 2 : ℝ) • (0 : Point2) := by simp
            rw [h0]
            have h4 : dist ((1 / 2 : ℝ) • (g1_center - g2_center)) ((1 / 2 : ℝ) • (0 : Point2)) =
                (1 / 2 : ℝ) * dist (g1_center - g2_center) 0 := by
              rw [dist_smul_real, abs_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)]
            rw [h4]
            have h5 : dist (g1_center - g2_center) 0 = dist g1_center g2_center := by
              simp [dist_eq_norm]
            rw [h5] <;> ring
          rw [h]
        _ = dist g1_center g2_center / 2 + r_G := by ring
    have h2 : dist (s_G • x0 + t_G) 0 = s_G * dist (x0 - midpoint) 0 := by
      have h_eq : s_G • x0 + t_G = s_G • (x0 - midpoint) := by
        ext i
        fin_cases i <;> simp [t_G, midpoint, smul_sub, sub_smul] <;> ring
      have h_main : dist (s_G • (x0 - midpoint)) 0 = s_G * dist (x0 - midpoint) 0 := by
        have h0 : dist (s_G • (x0 - midpoint)) 0 = ‖s_G • (x0 - midpoint)‖ := by
          rw [dist_eq_norm] <;> simp
        rw [h0]
        have h1 : ‖s_G • (x0 - midpoint)‖ = |s_G| * ‖x0 - midpoint‖ := norm_smul s_G (x0 - midpoint)
        rw [h1]
        have h2 : |s_G| = s_G := abs_of_pos hsG_pos
        rw [h2]
        have h3 : ‖x0 - midpoint‖ = dist (x0 - midpoint) 0 := by
          rw [dist_eq_norm] <;> simp
        rw [h3]
      rw [h_eq]
      exact h_main
    rw [h2]
    have h5 : s_G * dist (x0 - midpoint) 0 ≤ s_G * (dist g1_center g2_center / 2 + r_G) := by gcongr
    have h6 : s_G * (dist g1_center g2_center / 2 + r_G) ≤ 1 := by
      dsimp only [s_G]
      have h7 : dist g1_center g2_center / 2 + r_G = (D_G + 2 * r_G) / 2 := by
        dsimp only [D_G] <;> ring
      have h8 : (2 : ℝ) / (D_G + 2 * r_G) * (dist g1_center g2_center / 2 + r_G) ≤ 1 := by
        rw [h7]
        have hpos : 0 < D_G + 2 * r_G := by positivity
        have h9 : (2 : ℝ) / (D_G + 2 * r_G) * ((D_G + 2 * r_G) / 2) = 1 := by
          field_simp [hpos.ne']
          <;> ring
        rw [h9]
        <;> norm_num
      exact h8
    linarith

  have hG2_unit' : ∀ x ∈ G2'', dist x 0 ≤ 1 := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨x1, hx1, rfl⟩
    rcases Finset.mem_image.mp hx1 with ⟨x0, hx0, rfl⟩
    have h_x : dist x0 g2_center ≤ r_G := hG2_ball x0 hx0
    have h_norm : dist (x0 - midpoint) 0 ≤ dist g1_center g2_center / 2 + r_G := by
      calc
        dist (x0 - midpoint) 0
          = dist x0 midpoint := by simp [dist_eq_norm] <;> ring_nf
        _ ≤ dist x0 g2_center + dist g2_center midpoint := dist_triangle _ _ _
        _ ≤ r_G + dist g2_center midpoint := by gcongr
        _ = r_G + dist g1_center g2_center / 2 := by
          have h : dist g2_center midpoint = dist g1_center g2_center / 2 := by
            have h2 : g2_center - midpoint = (1 / 2 : ℝ) • (g2_center - g1_center) := by
              ext i
              fin_cases i <;> simp [midpoint, smul_sub, sub_smul] <;> ring
            have h3 : dist g2_center midpoint = dist (g2_center - midpoint) 0 := by
              simp [dist_eq_norm] <;> ring_nf
            rw [h3, h2]
            have h0 : (0 : Point2) = (1 / 2 : ℝ) • (0 : Point2) := by simp
            rw [h0]
            have h4 : dist ((1 / 2 : ℝ) • (g2_center - g1_center)) ((1 / 2 : ℝ) • (0 : Point2)) =
                (1 / 2 : ℝ) * dist (g2_center - g1_center) 0 := by
              rw [dist_smul_real, abs_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)]
            rw [h4]
            have h5 : dist (g2_center - g1_center) 0 = dist g2_center g1_center := by
              simp [dist_eq_norm]
            have h6 : dist g2_center g1_center = dist g1_center g2_center := dist_comm _ _
            rw [h5, h6] <;> ring
          rw [h]
        _ = dist g1_center g2_center / 2 + r_G := by ring
    have h2 : dist (s_G • x0 + t_G) 0 = s_G * dist (x0 - midpoint) 0 := by
      have h_eq : s_G • x0 + t_G = s_G • (x0 - midpoint) := by
        ext i
        fin_cases i <;> simp [t_G, midpoint, smul_sub, sub_smul] <;> ring
      have h_main : dist (s_G • (x0 - midpoint)) 0 = s_G * dist (x0 - midpoint) 0 := by
        have h0 : dist (s_G • (x0 - midpoint)) 0 = ‖s_G • (x0 - midpoint)‖ := by
          rw [dist_eq_norm] <;> simp
        rw [h0]
        have h1 : ‖s_G • (x0 - midpoint)‖ = |s_G| * ‖x0 - midpoint‖ := norm_smul s_G (x0 - midpoint)
        rw [h1]
        have h2 : |s_G| = s_G := abs_of_pos hsG_pos
        rw [h2]
        have h3 : ‖x0 - midpoint‖ = dist (x0 - midpoint) 0 := by
          rw [dist_eq_norm] <;> simp
        rw [h3]
      rw [h_eq]
      exact h_main
    rw [h2]
    have h5 : s_G * dist (x0 - midpoint) 0 ≤ s_G * (dist g1_center g2_center / 2 + r_G) := by gcongr
    have h6 : s_G * (dist g1_center g2_center / 2 + r_G) ≤ 1 := by
      dsimp only [s_G]
      have h7 : dist g1_center g2_center / 2 + r_G = (D_G + 2 * r_G) / 2 := by
        dsimp only [D_G] <;> ring
      have h8 : (2 : ℝ) / (D_G + 2 * r_G) * (dist g1_center g2_center / 2 + r_G) ≤ 1 := by
        rw [h7]
        have hpos : 0 < D_G + 2 * r_G := by positivity
        have h9 : (2 : ℝ) / (D_G + 2 * r_G) * ((D_G + 2 * r_G) / 2) = 1 := by
          field_simp [hpos.ne']
          <;> ring
        rw [h9]
        <;> norm_num
      exact h8
    linarith

  have h_std : WZ1StandardSeparation F'' G1'' G2'' := by
    exact ⟨hF_diam, hG1_diam, hG2_diam, hG_sep, hF_dist⟩

  exact ⟨s_F, s_G, t_G, h_std, hsF_pos, hsG_pos, hF_unit', hG1_unit', hG2_unit'⟩

/-! ## Step 2: Grid partition and pigeonhole -/

/--
Pigeonhole lemma for tripartite graphs: partition each vertex set by grid cells
of side `r`, and find a cell triple containing at least an average fraction of edges.

Returns the cell centers and the number of cell triples `N`, with the bound
`|H'| * N ≥ |H|`.
-/
lemma grid_pigeonhole_triple
    {F G1 G2 : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    {r : ℝ} (hr_pos : 0 < r)
    (hH_nonempty : H.Nonempty)
    (hH_support : ∀ h ∈ H, h.1 ∈ F ∧ h.2.1 ∈ G1 ∧ h.2.2 ∈ G2) :
    ∃ (cF cG1 cG2 : Point2) (N : ℕ),
      let H' := H.filter (fun h =>
        gridCenter r h.1 = cF ∧
        gridCenter r h.2.1 = cG1 ∧
        gridCenter r h.2.2 = cG2)
      H'.Nonempty ∧
      (H'.card : ENNReal) * (N : ENNReal) ≥ (H.card : ENNReal) ∧
      (N : ENNReal) ≤ ((F.image (gridCenter r)).card : ENNReal) *
          ((G1.image (gridCenter r)).card : ENNReal) *
          ((G2.image (gridCenter r)).card : ENNReal) := by
  let f : (Point2 × Point2 × Point2) → (Point2 × Point2 × Point2) :=
    fun h => (gridCenter r h.1, gridCenter r h.2.1, gridCenter r h.2.2)
  let centers := H.image f
  have hcenters_nonempty : centers.Nonempty :=
    Finset.Nonempty.image hH_nonempty f
  let fiber_card : (Point2 × Point2 × Point2) → ℕ :=
    fun c => (H.filter (fun h => f h = c)).card
  have h_disj : ∀ c1 ∈ centers, ∀ c2 ∈ centers, c1 ≠ c2 →
      Disjoint (H.filter (fun h => f h = c1)) (H.filter (fun h => f h = c2)) := by
    intro c1 _ c2 _ hne
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    have h1 : f x = c1 := (Finset.mem_filter.mp hx1).2
    have h2 : f x = c2 := (Finset.mem_filter.mp hx2).2
    have h3 : c1 = c2 := by rw [← h1, h2]
    exact hne h3
  have h_union : centers.biUnion (fun c => H.filter (fun h => f h = c)) = H := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_filter]
    constructor
    · rintro ⟨c, _, hx, _⟩
      exact hx
    · intro hx
      exact ⟨f x, Finset.mem_image.mpr ⟨x, hx, rfl⟩, hx, rfl⟩
  have h_sum : ∑ c ∈ centers, fiber_card c = H.card := by
    have h : ∑ c ∈ centers, fiber_card c = (centers.biUnion (fun c => H.filter (fun h => f h = c))).card := by
      rw [Finset.card_biUnion h_disj]
      <;> rfl
    rw [h, h_union]
  have h_main : ∃ c ∈ centers, H.card ≤ centers.card * fiber_card c := by
    by_contra h
    have h' : ∀ c ∈ centers, centers.card * fiber_card c < H.card := by
      simpa [not_exists] using h
    have h_strict : ∑ c ∈ centers, (centers.card * fiber_card c) < ∑ c ∈ centers, H.card :=
      Finset.sum_lt_sum_of_nonempty hcenters_nonempty (fun i hi => h' i hi)
    have h_lhs : ∑ c ∈ centers, (centers.card * fiber_card c) = centers.card * (∑ c ∈ centers, fiber_card c) := by
      rw [Finset.mul_sum]
    have h_rhs : ∑ c ∈ centers, H.card = centers.card * H.card := by
      rw [Finset.sum_const]
      <;> ring
    rw [h_lhs, h_sum, h_rhs] at h_strict
    exact lt_irrefl _ h_strict
  have h_centers_subset : centers ⊆ (F.image (gridCenter r)) ×ˢ (G1.image (gridCenter r)) ×ˢ (G2.image (gridCenter r)) := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨h, hh, rfl⟩
    have h_sup := hH_support h hh
    have h1 : gridCenter r h.1 ∈ F.image (gridCenter r) :=
      Finset.mem_image.mpr ⟨h.1, h_sup.1, rfl⟩
    have h2 : gridCenter r h.2.1 ∈ G1.image (gridCenter r) :=
      Finset.mem_image.mpr ⟨h.2.1, h_sup.2.1, rfl⟩
    have h3 : gridCenter r h.2.2 ∈ G2.image (gridCenter r) :=
      Finset.mem_image.mpr ⟨h.2.2, h_sup.2.2, rfl⟩
    simp only [f, Finset.mem_product]
    exact ⟨h1, h2, h3⟩
  have h_N_bound : (centers.card : ENNReal) ≤
      ((F.image (gridCenter r)).card : ENNReal) *
      ((G1.image (gridCenter r)).card : ENNReal) *
      ((G2.image (gridCenter r)).card : ENNReal) := by
    have h_card : centers.card ≤
        ((F.image (gridCenter r)) ×ˢ (G1.image (gridCenter r)) ×ˢ (G2.image (gridCenter r))).card :=
      Finset.card_le_card h_centers_subset
    have h_prod : ((F.image (gridCenter r)) ×ˢ (G1.image (gridCenter r)) ×ˢ (G2.image (gridCenter r))).card =
        (F.image (gridCenter r)).card * (G1.image (gridCenter r)).card * (G2.image (gridCenter r)).card := by
      rw [Finset.card_product, Finset.card_product] <;> ring
    rw [h_prod] at h_card
    exact_mod_cast h_card
  rcases h_main with ⟨c, hc, h_ineq⟩
  let H' := H.filter (fun h => f h = c)
  have hH'_nonempty : H'.Nonempty := by
    by_contra h_empty
    have h_eq : H'.card = 0 := by
      rw [Finset.not_nonempty_iff_eq_empty.mp h_empty] <;> simp
    have h_contra : H.card ≤ centers.card * 0 := by
      simpa [fiber_card, H', h_eq] using h_ineq
    have h_zero : H.card = 0 := by linarith
    exact hH_nonempty.ne_empty (Finset.card_eq_zero.mp h_zero)
  have h_final : (H.card : ENNReal) ≤ (centers.card : ENNReal) * (H'.card : ENNReal) := by
    exact_mod_cast h_ineq
  have h_filter_eq : (H.filter (fun h =>
      gridCenter r h.1 = c.1 ∧
      gridCenter r h.2.1 = c.2.1 ∧
      gridCenter r h.2.2 = c.2.2)) = H' := by
    ext h
    simp only [Finset.mem_filter, H']
    <;> constructor <;> intro h <;> simp [f, Prod.ext_iff] at * <;> tauto
  have h_goal : (H.filter (fun h =>
      gridCenter r h.1 = c.1 ∧
      gridCenter r h.2.1 = c.2.1 ∧
      gridCenter r h.2.2 = c.2.2)).Nonempty ∧
      ((H.filter (fun h =>
      gridCenter r h.1 = c.1 ∧
      gridCenter r h.2.1 = c.2.1 ∧
      gridCenter r h.2.2 = c.2.2)).card : ENNReal) * (centers.card : ENNReal) ≥ (H.card : ENNReal) := by
    rw [h_filter_eq]
    have h_final' : (H'.card : ENNReal) * (centers.card : ENNReal) ≥ (H.card : ENNReal) := by
      have h_comm : (H'.card : ENNReal) * (centers.card : ENNReal) = (centers.card : ENNReal) * (H'.card : ENNReal) := by
        rw [mul_comm]
      rw [h_comm]
      exact h_final
    exact ⟨hH'_nonempty, h_final'⟩
  exact ⟨c.1, c.2.1, c.2.2, centers.card, h_goal.1, h_goal.2, h_N_bound⟩

/-! ## Good edge majority -/

/--
Edges whose F-coordinate is within distance `t` of origin: at most
`C * t * |F| * |G1| * |G2|`.
-/
lemma bad_near_origin_count
    {delta t : ℝ} {C : ENNReal}
    {F G1 G2 : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    (hdelta_pos : 0 < delta) (ht : delta ≤ t) (ht_one : t ≤ 1)
    (hF_frost : F.IsFrostman delta 1 C)
    (hsupport : ∀ h ∈ H, h.1 ∈ F ∧ h.2.1 ∈ G1 ∧ h.2.2 ∈ G2) :
    ((H.filter fun h => dist h.1 0 < t).card : ENNReal) ≤
      C * Kakeya.realRpowENN t 1 * F.enncard * G1.enncard * G2.enncard := by
  let S : DiscreteSet 2 := F.filter fun f => dist f 0 ≤ t
  have hS_card : S.enncard ≤ C * Kakeya.realRpowENN t 1 * F.enncard :=
    hF_frost 0 t ht ht_one
  let badH := H.filter fun h => dist h.1 0 < t
  have h_bad_subset : badH ⊆ S ×ˢ G1 ×ˢ G2 := by
    intro h hh
    have h1 : dist h.1 0 < t := (Finset.mem_filter.mp hh).2
    have h2 := hsupport h (Finset.mem_filter.mp hh).1
    have h3 : h.1 ∈ S := by
      simp only [S, Finset.mem_filter] <;> exact ⟨h2.1, by linarith⟩
    simp only [Finset.mem_product] <;> exact ⟨h3, h2.2.1, h2.2.2⟩
  have h4 : (badH.card : ENNReal) ≤ ((S ×ˢ G1 ×ˢ G2).card : ENNReal) := by
    exact_mod_cast Finset.card_le_card h_bad_subset
  have h5 : ((S ×ˢ G1 ×ˢ G2).card : ENNReal) = S.enncard * G1.enncard * G2.enncard := by
    simp [Finset.card_product, DiscreteSet.enncard] <;> ring
  rw [h5] at h4
  exact h4.trans (by gcongr)

/--
Edges whose G1-G2 distance is less than `t`: at most
`C * t * |F| * |G1| * |G2|`.
-/
lemma bad_close_pair_count
    {delta t : ℝ} {C : ENNReal}
    {F G1 G2 : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    (hdelta_pos : 0 < delta) (ht : delta ≤ t) (ht_one : t ≤ 1)
    (hG2_frost : G2.IsFrostman delta 1 C)
    (hsupport : ∀ h ∈ H, h.1 ∈ F ∧ h.2.1 ∈ G1 ∧ h.2.2 ∈ G2) :
    ((H.filter fun h => dist h.2.1 h.2.2 < t).card : ENNReal) ≤
      C * Kakeya.realRpowENN t 1 * F.enncard * G1.enncard * G2.enncard := by
  classical
  let badPairs : Finset (Point2 × Point2) :=
    (G1 ×ˢ G2).filter fun p => dist p.1 p.2 < t
  have h_per_g1 : ∀ g1 ∈ G1, ((G2.filter fun g2 => dist g1 g2 < t).card : ENNReal) ≤
        C * Kakeya.realRpowENN t 1 * G2.enncard := by
    intro g1 hg1
    let Sg : DiscreteSet 2 := G2.filter fun g2 => dist g2 g1 ≤ t
    have hSg_eq : Sg.enncard = G2.ballCount g1 t := by rfl
    have h4 : (G2.filter fun g2 => dist g1 g2 < t) ⊆ Sg := by
      intro x hx
      have h_in : x ∈ G2 := (Finset.mem_filter.mp hx).1
      have h_lt : dist g1 x < t := (Finset.mem_filter.mp hx).2
      simp only [Sg, Finset.mem_filter] <;> exact ⟨h_in, by simpa [dist_comm] using h_lt.le⟩
    have h5 : Sg.enncard ≤ C * Kakeya.realRpowENN t 1 * G2.enncard := by
      rw [hSg_eq] <;> exact hG2_frost g1 t ht ht_one
    have h7 : (G2.filter fun g2 => dist g1 g2 < t).card ≤ Sg.card := Finset.card_le_card h4
    have h6 : ((G2.filter fun g2 => dist g1 g2 < t).card : ENNReal) ≤ (Sg.card : ENNReal) := by
      exact_mod_cast h7
    have h6' : ((G2.filter fun g2 => dist g1 g2 < t).card : ENNReal) ≤ Sg.enncard := by
      simpa [DiscreteSet.enncard] using h6
    exact h6'.trans h5
  have h_bad_pairs_card : (badPairs.card : ENNReal) ≤
      G1.enncard * (C * Kakeya.realRpowENN t 1 * G2.enncard) := by
    have h2 : badPairs = Finset.biUnion G1 (fun g1 =>
        (G2.filter fun g2 => dist g1 g2 < t).image (fun g2 => (g1, g2))) := by
      ext ⟨g1, g2⟩
      simp only [badPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion]
      <;> constructor <;> intro h <;> simp_all [Finset.mem_image] <;> tauto
    have h_disj : ∀ (i : Point2), i ∈ G1 → ∀ (j : Point2), j ∈ G1 → i ≠ j →
        Disjoint ((G2.filter fun g2 => dist i g2 < t).image (fun g2 => (i, g2)))
                 ((G2.filter fun g2 => dist j g2 < t).image (fun g2 => (j, g2))) := by
      intro i _ j _ hne
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      rcases Finset.mem_image.mp hp1 with ⟨_, _, rfl⟩
      rcases Finset.mem_image.mp hp2 with ⟨_, _, h_eq⟩
      injection h_eq with h1
      exact hne h1.symm
    have h_inj : ∀ (g1 : Point2), Function.Injective (fun g2 : Point2 => (g1, g2)) := by
      intro g1
      intro a b h
      simpa using h
    have h3 : badPairs.card = ∑ g1 ∈ G1, (G2.filter fun g2 => dist g1 g2 < t).card := by
      rw [h2, Finset.card_biUnion h_disj]
      apply Finset.sum_congr rfl
      intro g1 _
      rw [Finset.card_image_of_injective _ (h_inj g1)]
    rw [h3]
    have h4 : (∑ g1 ∈ G1, ((G2.filter fun g2 => dist g1 g2 < t).card : ENNReal)) ≤
        ∑ g1 ∈ G1, (C * Kakeya.realRpowENN t 1 * G2.enncard) := by
      apply Finset.sum_le_sum
      intro i _
      exact h_per_g1 i ‹_›
    have h5 : (∑ g1 ∈ G1, (C * Kakeya.realRpowENN t 1 * G2.enncard)) =
        (G1.card : ENNReal) * (C * Kakeya.realRpowENN t 1 * G2.enncard) := by
      rw [Finset.sum_const, mul_comm]
      <;> simp
    rw [h5] at h4
    simpa [DiscreteSet.enncard] using h4
  let badH := H.filter fun h => dist h.2.1 h.2.2 < t
  have h_bad_edges_subset : badH ⊆ F ×ˢ badPairs := by
    intro h hh
    have h1 : dist h.2.1 h.2.2 < t := (Finset.mem_filter.mp hh).2
    have h2 := hsupport h (Finset.mem_filter.mp hh).1
    have h3 : (h.2.1, h.2.2) ∈ badPairs := by
      simp only [badPairs, Finset.mem_filter, Finset.mem_product] <;> exact ⟨⟨h2.2.1, h2.2.2⟩, by simpa using h1⟩
    simp only [Finset.mem_product] <;> exact ⟨h2.1, h3⟩
  have h4 : (badH.card : ENNReal) ≤ ((F ×ˢ badPairs).card : ENNReal) := by
    exact_mod_cast Finset.card_le_card h_bad_edges_subset
  have h5 : ((F ×ˢ badPairs).card : ENNReal) = F.enncard * (badPairs.card : ENNReal) := by
    simp [Finset.card_product, DiscreteSet.enncard] <;> ring
  rw [h5] at h4
  have h6 : F.enncard * (badPairs.card : ENNReal) ≤
      F.enncard * (G1.enncard * (C * Kakeya.realRpowENN t 1 * G2.enncard)) := by
    gcongr <;> exact h_bad_pairs_card
  have h7 : F.enncard * (G1.enncard * (C * Kakeya.realRpowENN t 1 * G2.enncard)) =
      C * Kakeya.realRpowENN t 1 * F.enncard * G1.enncard * G2.enncard := by ring
  rw [h7] at h6
  exact h4.trans h6

/--
If `|H| ≥ δ^{η-3}`, Frostman constant `C = δ^{-η}`,
vertex sizes ≤ δ^{-1-η}, and `t = δ^{6η}`, then total bad edges < |H|/2.
Requires `δ^η < 1/4` and `6η ≤ 1`.
-/
lemma good_edge_majority
    {delta eta : ℝ}
    {F G1 G2 : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    (hdelta_pos : 0 < delta) (hdelta_one : delta ≤ 1)
    (heta : 0 < eta) (heta_le : 6 * eta ≤ 1)
    (hF_frost : F.IsFrostman delta 1 (Kakeya.realRpowENN delta (-eta)))
    (hG2_frost : G2.IsFrostman delta 1 (Kakeya.realRpowENN delta (-eta)))
    (hF_upper : F.enncard ≤ Kakeya.realRpowENN delta (-1 - eta))
    (hG1_upper : G1.enncard ≤ Kakeya.realRpowENN delta (-1 - eta))
    (hG2_upper : G2.enncard ≤ Kakeya.realRpowENN delta (-1 - eta))
    (hsupport : ∀ h ∈ H, h.1 ∈ F ∧ h.2.1 ∈ G1 ∧ h.2.2 ∈ G2)
    (hH_card : Kakeya.realRpowENN delta (eta - 3) ≤ (H.card : ENNReal))
    (hdelta_small : Real.rpow delta eta < 1 / 4) :
    let t := Real.rpow delta (6 * eta)
    let badOrigin := H.filter fun h => dist h.1 0 < t
    let badClose := H.filter fun h => dist h.2.1 h.2.2 < t
    (badOrigin.card + badClose.card : ENNReal) < (H.card : ENNReal) / 2 := by
  set t := Real.rpow delta (6 * eta) with ht_def
  have ht_pos : 0 < t := Real.rpow_pos_of_pos hdelta_pos _
  have ht_ge_delta : delta ≤ t := by
    rw [ht_def]
    have h : Real.rpow delta (6 * eta) ≥ Real.rpow delta 1 :=
      Real.rpow_le_rpow_of_exponent_ge hdelta_pos hdelta_one (by linarith)
    have h1 : Real.rpow delta 1 = delta := by simp
    rw [h1] at h
    exact h
  have ht_one : t ≤ 1 := by
    rw [ht_def]
    exact Real.rpow_le_one hdelta_pos.le hdelta_one (by linarith)
  set C := Kakeya.realRpowENN delta (-eta) with hC_def
  have h_bad_origin := bad_near_origin_count hdelta_pos ht_ge_delta ht_one hF_frost hsupport
  have h_bad_close := bad_close_pair_count hdelta_pos ht_ge_delta ht_one hG2_frost hsupport
  have h_rpow_t : Kakeya.realRpowENN t 1 = Kakeya.realRpowENN delta (6 * eta) := by
    simp [Kakeya.realRpowENN, ht_def]
  rw [h_rpow_t] at h_bad_origin h_bad_close
  have h_bound_each : C * Kakeya.realRpowENN delta (6 * eta) * F.enncard * G1.enncard * G2.enncard ≤
      Kakeya.realRpowENN delta (2 * eta - 3) := by
    have h_exp : C * Kakeya.realRpowENN delta (6 * eta) *
          Kakeya.realRpowENN delta (-1 - eta) *
          Kakeya.realRpowENN delta (-1 - eta) *
          Kakeya.realRpowENN delta (-1 - eta) =
        Kakeya.realRpowENN delta (2 * eta - 3) := by
      simp only [hC_def, Kakeya.realRpowENN]
      have h_pos : ∀ (r : ℝ), 0 ≤ Real.rpow delta r := fun _ =>
        Real.rpow_nonneg hdelta_pos.le _
      let a := Real.rpow delta (-eta)
      let b := Real.rpow delta (6 * eta)
      let c := Real.rpow delta (-1 - eta)
      have ha : 0 ≤ a := h_pos (-eta)
      have hb : 0 ≤ b := h_pos (6 * eta)
      have hc : 0 ≤ c := h_pos (-1 - eta)
      have hab : 0 ≤ a * b := mul_nonneg ha hb
      have habc : 0 ≤ a * b * c := mul_nonneg hab hc
      have habcc : 0 ≤ a * b * c * c := mul_nonneg habc hc
      have h9 : ENNReal.ofReal a * ENNReal.ofReal b * ENNReal.ofReal c *
          ENNReal.ofReal c * ENNReal.ofReal c =
          ENNReal.ofReal (a * b * c * c * c) := by
        rw [← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul hab,
            ← ENNReal.ofReal_mul habc, ← ENNReal.ofReal_mul habcc]
        <;> ring
      have h_real2 : a * b * c * c * c = Real.rpow delta (2 * eta - 3) := by
        dsimp only [a, b, c]
        have h1 : Real.rpow delta (-eta) * Real.rpow delta (6 * eta) =
              Real.rpow delta ((-eta) + (6 * eta)) :=
          (Real.rpow_add hdelta_pos (-eta) (6 * eta)).symm
        have h2 : Real.rpow delta (-1 - eta) * Real.rpow delta (-1 - eta) =
              Real.rpow delta ((-1 - eta) + (-1 - eta)) :=
          (Real.rpow_add hdelta_pos (-1 - eta) (-1 - eta)).symm
        have h3 : Real.rpow delta (-eta) * Real.rpow delta (6 * eta) *
              Real.rpow delta (-1 - eta) * Real.rpow delta (-1 - eta) *
              Real.rpow delta (-1 - eta) =
            Real.rpow delta (((-eta) + (6 * eta)) + ((-1 - eta) + (-1 - eta)) + (-1 - eta)) := by
          have h_assoc : Real.rpow delta (-eta) * Real.rpow delta (6 * eta) *
                Real.rpow delta (-1 - eta) * Real.rpow delta (-1 - eta) *
                Real.rpow delta (-1 - eta) =
              (Real.rpow delta (-eta) * Real.rpow delta (6 * eta)) *
              (Real.rpow delta (-1 - eta) * Real.rpow delta (-1 - eta)) *
              Real.rpow delta (-1 - eta) := by ring
          rw [h_assoc, h1, h2]
          have h_step1 : Real.rpow delta ((-eta) + (6 * eta)) * Real.rpow delta ((-1 - eta) + (-1 - eta)) =
                Real.rpow delta (((-eta) + (6 * eta)) + ((-1 - eta) + (-1 - eta))) :=
            (Real.rpow_add hdelta_pos _ _).symm
          have h_step2 : (Real.rpow delta ((-eta) + (6 * eta)) * Real.rpow delta ((-1 - eta) + (-1 - eta))) * Real.rpow delta (-1 - eta) =
                Real.rpow delta ((((-eta) + (6 * eta)) + ((-1 - eta) + (-1 - eta))) + (-1 - eta)) := by
            rw [h_step1]
            exact (Real.rpow_add hdelta_pos _ _).symm
          have h_final : Real.rpow delta ((-eta) + (6 * eta)) * Real.rpow delta ((-1 - eta) + (-1 - eta)) * Real.rpow delta (-1 - eta) =
                Real.rpow delta ((((-eta) + (6 * eta)) + ((-1 - eta) + (-1 - eta))) + (-1 - eta)) := by
            have h_ring : Real.rpow delta ((-eta) + (6 * eta)) * Real.rpow delta ((-1 - eta) + (-1 - eta)) * Real.rpow delta (-1 - eta) =
                (Real.rpow delta ((-eta) + (6 * eta)) * Real.rpow delta ((-1 - eta) + (-1 - eta))) * Real.rpow delta (-1 - eta) := by ring
            rw [h_ring]
            exact h_step2
          exact h_final
        rw [h3]
        have h4 : ((-eta) + (6 * eta)) + ((-1 - eta) + (-1 - eta)) + (-1 - eta) = 2 * eta - 3 := by ring
        rw [h4]
      rw [h9, h_real2]
    calc
      C * Kakeya.realRpowENN delta (6 * eta) * F.enncard * G1.enncard * G2.enncard
        ≤ C * Kakeya.realRpowENN delta (6 * eta) *
            Kakeya.realRpowENN delta (-1 - eta) *
            Kakeya.realRpowENN delta (-1 - eta) *
            Kakeya.realRpowENN delta (-1 - eta) := by gcongr
      _ = Kakeya.realRpowENN delta (2 * eta - 3) := h_exp
  let badOrigin := H.filter fun h => dist h.1 0 < t
  let badClose := H.filter fun h => dist h.2.1 h.2.2 < t
  have h_total_bad : (badOrigin.card + badClose.card : ENNReal) ≤
      2 * Kakeya.realRpowENN delta (2 * eta - 3) := by
    calc
      (badOrigin.card + badClose.card : ENNReal)
        ≤ (C * Kakeya.realRpowENN delta (6 * eta) * F.enncard * G1.enncard * G2.enncard) +
            (C * Kakeya.realRpowENN delta (6 * eta) * F.enncard * G1.enncard * G2.enncard) := by
          gcongr
      _ = 2 * (C * Kakeya.realRpowENN delta (6 * eta) * F.enncard * G1.enncard * G2.enncard) := by ring
      _ ≤ 2 * Kakeya.realRpowENN delta (2 * eta - 3) := by gcongr
  have h_real_ineq : (4 : ℝ) * Real.rpow delta (2 * eta - 3) < Real.rpow delta (eta - 3) := by
    have h_sum : (eta - 3) + eta = 2 * eta - 3 := by ring
    have h7 : Real.rpow delta (2 * eta - 3) = Real.rpow delta (eta - 3) * Real.rpow delta eta := by
      rw [← h_sum]
      exact Real.rpow_add hdelta_pos (eta - 3) eta
    rw [h7]
    have h8 : 0 < Real.rpow delta (eta - 3) := Real.rpow_pos_of_pos hdelta_pos _
    nlinarith [hdelta_small]
  have h5 : (4 : ENNReal) * Kakeya.realRpowENN delta (2 * eta - 3) <
      Kakeya.realRpowENN delta (eta - 3) := by
    set x := Real.rpow delta (2 * eta - 3) with hx_def
    set y := Real.rpow delta (eta - 3) with hy_def
    have hx_nonneg : 0 ≤ x := Real.rpow_nonneg (by linarith) _
    have hy_pos : 0 < y := Real.rpow_pos_of_pos hdelta_pos _
    have h51 : (4 : ENNReal) * ENNReal.ofReal x = ENNReal.ofReal ((4 : ℝ) * x) := by
      have h : ENNReal.ofReal ((4 : ℝ) * x) = ENNReal.ofReal (4 : ℝ) * ENNReal.ofReal x :=
        ENNReal.ofReal_mul (show (0 : ℝ) ≤ 4 by norm_num)
      have h2 : ENNReal.ofReal (4 : ℝ) = (4 : ENNReal) := by simp
      rw [h, h2] <;> ring
    simp only [Kakeya.realRpowENN, hx_def, hy_def]
    rw [h51]
    exact (ENNReal.ofReal_lt_ofReal_iff hy_pos).mpr h_real_ineq
  set X := Kakeya.realRpowENN delta (2 * eta - 3) with hX
  set Y := Kakeya.realRpowENN delta (eta - 3) with hY
  have h6 : (2 : ENNReal) * X < Y / 2 := by
    by_contra h9
    have h10 : Y / 2 ≤ (2 : ENNReal) * X := Std.not_lt.mp h9
    have h12 : (Y / 2) * 2 = Y := by
      rw [div_eq_mul_inv, mul_assoc]
      have h14 : (2⁻¹ : ENNReal) * (2 : ENNReal) = 1 := by
        rw [ENNReal.inv_mul_cancel] <;> norm_num
      rw [h14, mul_one]
    have h13 : Y ≤ (4 : ENNReal) * X := by
      calc
        Y = (Y / 2) * 2 := h12.symm
        _ ≤ ((2 : ENNReal) * X) * 2 := by gcongr
        _ = (4 : ENNReal) * X := by ring
    have h15 : ¬(Y ≤ (4 : ENNReal) * X) := Std.not_le.mpr h5
    exact h15 h13
  have h_H_half : Kakeya.realRpowENN delta (eta - 3) / 2 ≤ (H.card : ENNReal) / 2 := by
    have h9 : Kakeya.realRpowENN delta (eta - 3) ≤ (H.card : ENNReal) := hH_card
    have h10 : Kakeya.realRpowENN delta (eta - 3) / 2 ≤ (H.card : ENNReal) / 2 := by
      gcongr
    exact h10
  dsimp only
  exact h_total_bad.trans_lt (h6.trans_le h_H_half)



/--
Given a majority bound `badOrigin.card + badClose.card < H.card / 2`,
deduce that the set of "good" edges (those whose origin is far from 0 AND
whose G1-G2 pair is far apart) has at least half the cardinality of `H`.
-/
lemma good_edge_card
    {H : Finset (Point2 × Point2 × Point2)} {t : ℝ}
    (h_majority :
      (((H.filter fun h => dist h.1 0 < t).card + (H.filter fun h => dist h.2.1 h.2.2 < t).card : ENNReal)
        < (H.card : ENNReal) / 2)) :
    ((H.filter fun h => dist h.1 0 ≥ t ∧ dist h.2.1 h.2.2 ≥ t).card : ENNReal) ≥ (H.card : ENNReal) / 2 := by
  let badOrigin := H.filter fun h => dist h.1 0 < t
  let badClose := H.filter fun h => dist h.2.1 h.2.2 < t
  let H_good := H.filter fun h => dist h.1 0 ≥ t ∧ dist h.2.1 h.2.2 ≥ t
  let badUnion := badOrigin ∪ badClose
  have h1 : H_good = H \ badUnion := by
    ext z
    have hz : z ∈ H_good ↔ z ∈ H \ badUnion := by
      simp [H_good, badUnion, Finset.mem_filter, Finset.mem_union]
      <;> by_cases h1 : dist z.1 0 < t <;> by_cases h2 : dist z.2.1 z.2.2 < t <;> aesop
    exact hz
  have h2 : badUnion.card ≤ badOrigin.card + badClose.card := Finset.card_union_le _ _
  have h3 : (badUnion.card : ENNReal) ≤ (badOrigin.card + badClose.card : ENNReal) := by exact_mod_cast h2
  have h4 : (badUnion.card : ENNReal) < (H.card : ENNReal) / 2 := h3.trans_lt h_majority
  have h_sub : badUnion ⊆ H := by
    intro x hx
    simp only [badUnion, Finset.mem_union] at hx
    rcases hx with (hx | hx) <;> exact (Finset.mem_filter.mp hx).1
  have h_disj : Disjoint (H \ badUnion) badUnion := by
    simp [Finset.disjoint_left]
  have h_union : (H \ badUnion) ∪ badUnion = H := by
    rw [Finset.sdiff_union_of_subset h_sub]
  have h_card_sum : (H \ badUnion).card + badUnion.card = H.card := by
    have h : (H \ badUnion).card + badUnion.card = ((H \ badUnion) ∪ badUnion).card := by
      rw [Finset.card_union_of_disjoint h_disj]
    rw [h, h_union]
  have h5 : (H.card : ENNReal) = ((H \ badUnion).card : ENNReal) + (badUnion.card : ENNReal) := by
    exact_mod_cast h_card_sum.symm
  have h6 : (H.card : ENNReal) / 2 ≤ ((H \ badUnion).card : ENNReal) := by
    by_contra h7
    have h8 : ((H \ badUnion).card : ENNReal) < (H.card : ENNReal) / 2 := not_le.mp h7
    have h9 : ((H \ badUnion).card : ENNReal) + (badUnion.card : ENNReal) < (H.card : ENNReal) := by
      calc
        ((H \ badUnion).card : ENNReal) + (badUnion.card : ENNReal)
          < (H.card : ENNReal) / 2 + (H.card : ENNReal) / 2 := by gcongr
        _ = (H.card : ENNReal) := by
          have h10 : (H.card : ENNReal) / 2 + (H.card : ENNReal) / 2 = (H.card : ENNReal) := by
            have h11 : (H.card : ENNReal) / 2 + (H.card : ENNReal) / 2 = 2 * ((H.card : ENNReal) / 2) := by ring
            rw [h11]
            have h12 : (2 : ENNReal) * ((H.card : ENNReal) / 2) = (H.card : ENNReal) := by
              exact ENNReal.mul_div_cancel (by norm_num) (by norm_num)
            exact h12
          exact h10
    have h13 : ((H \ badUnion).card : ENNReal) + (badUnion.card : ENNReal) = (H.card : ENNReal) := h5.symm
    rw [h13] at h9
    exact lt_irrefl _ h9
  have h12 : (H_good.card : ENNReal) = ((H \ badUnion).card : ENNReal) := by
    congr
    <;> exact h1
  rw [h12]
  exact h6

/-- Scaling by 1 is the identity. -/
lemma scaleSet_one {n : ℕ} (A : DiscreteSet n) : scaleSet (1 : ℝ) A = A := by
  ext z
  simp only [scaleSet, Finset.mem_image, one_smul]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hz
    exact ⟨z, hz, rfl⟩

/-- Translation by 0 is the identity. -/
lemma image_add_zero {n : ℕ} (A : DiscreteSet n) :
    A.image (fun z : Point n => z + (0 : Point n)) = A := by
  ext z
  simp only [Finset.mem_image, add_zero]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hz
    exact ⟨z, hz, rfl⟩

/-- Scaling by 1 then translating by 0 is the identity. -/
lemma scaled_one_trans_zero {n : ℕ} (A : DiscreteSet n) :
    (scaleSet (1 : ℝ) A).image (fun z : Point n => z + (0 : Point n)) = A := by
  rw [scaleSet_one A]
  exact image_add_zero A

/-- Transfer `WZ1StandardSeparation` along set equalities. -/
lemma transfer_wz1_sep {A B C A' B' C' : DiscreteSet 2}
    (hA : A' = A) (hB : B' = B) (hC : C' = C)
    (h : WZ1StandardSeparation A B C) : WZ1StandardSeparation A' B' C' := by
  rw [hA, hB, hC]
  exact h

/-- Case 4: both scaling factors are already ≥ 1, so use identity scaling. -/
lemma case4_both_unscaled {F' G1' G2' : DiscreteSet 2}
    {f_center g1_center g2_center : Point2} {r_F r_G : ℝ}
    (hF_ball : ∀ x ∈ F', dist x f_center ≤ r_F)
    (hG1_ball : ∀ x ∈ G1', dist x g1_center ≤ r_G)
    (hG2_ball : ∀ x ∈ G2', dist x g2_center ≤ r_G)
    (hF_unit : ∀ x ∈ F', dist x 0 ≤ 1)
    (hG1_unit : ∀ x ∈ G1', dist x 0 ≤ 1)
    (hG2_unit : ∀ x ∈ G2', dist x 0 ≤ 1)
    (hrF_small : 2 * r_F ≤ 1 / 10)
    (hrG_small : 2 * r_G ≤ 1 / 10)
    (h_ratio_F : 19 * r_F ≤ dist f_center 0)
    (h_ratio_G : 38 * r_G ≤ dist g1_center g2_center)
    (hF : ¬(dist f_center 0 + r_F ≤ 1))
    (hG : ¬(dist g1_center g2_center + 2 * r_G ≤ 2)) :
    ∃ (s_F s_G : ℝ) (t_G : Point2),
      1 ≤ s_F ∧ 1 ≤ s_G ∧
      WZ1StandardSeparation (scaleSet s_F F')
        ((scaleSet s_G G1').image (fun x => x + t_G))
        ((scaleSet s_G G2').image (fun x => x + t_G)) ∧
      (∀ x ∈ scaleSet s_F F', dist x 0 ≤ 1) ∧
      (∀ x ∈ (scaleSet s_G G1').image (fun x => x + t_G), dist x 0 ≤ 1) ∧
      (∀ x ∈ (scaleSet s_G G2').image (fun x => x + t_G), dist x 0 ≤ 1) := by
  let d_F := dist f_center 0
  let D_G := dist g1_center g2_center
  have h_rF_le20 : r_F ≤ 1 / 20 := by linarith
  have h_rG_le20 : r_G ≤ 1 / 20 := by linarith
  have h_diam2 : ∀ (A : DiscreteSet 2) (c : Point2) (r : ℝ),
      (∀ x ∈ A, dist x c ≤ r) → ∀ (x y : Point2), x ∈ A → y ∈ A → dist x y ≤ 2 * r := by
    intro A c r hball x y hx hy
    have h1 : dist x y ≤ dist x c + dist c y := dist_triangle _ _ _
    have h2 : dist c y = dist y c := dist_comm _ _
    rw [h2] at h1
    linarith [hball x hx, hball y hy]
  have h_ball_lower : ∀ (A : DiscreteSet 2) (c : Point2) (r : ℝ),
      (∀ x ∈ A, dist x c ≤ r) → ∀ x ∈ A, dist x 0 ≥ dist c 0 - r := by
    intro A c r hball x hx
    have h1 : dist c 0 ≤ dist c x + dist x 0 := dist_triangle _ _ _
    have h2 : dist c x ≤ r := by
      have h3 : dist x c ≤ r := hball x hx
      have h4 : dist c x = dist x c := dist_comm _ _
      rw [h4]; exact h3
    linarith
  have h_sep_lower : ∀ (x0 y0 : Point2), x0 ∈ G1' → y0 ∈ G2' → dist x0 y0 ≥ D_G - 2 * r_G := by
    intro x0 y0 hx0 hy0
    have h1 : dist g1_center g2_center ≤ dist g1_center x0 + dist x0 y0 + dist y0 g2_center := by
      calc dist g1_center g2_center ≤ dist g1_center x0 + dist x0 g2_center := dist_triangle _ _ _
        _ ≤ dist g1_center x0 + dist x0 y0 + dist y0 g2_center := by
          have h2 : dist x0 g2_center ≤ dist x0 y0 + dist y0 g2_center := dist_triangle _ _ _
          linarith
    have h3 : dist g1_center x0 ≤ r_G := by
      have h4 : dist x0 g1_center ≤ r_G := hG1_ball x0 hx0
      have h5 : dist g1_center x0 = dist x0 g1_center := dist_comm _ _
      rw [h5]; exact h4
    have h4 : dist y0 g2_center ≤ r_G := hG2_ball y0 hy0
    linarith
  have h_orig : WZ1StandardSeparation F' G1' G2' := by
    refine' ⟨_, _, _, _, _⟩
    · intro x hx y hy
      have h : dist x y ≤ 2 * r_F := h_diam2 F' f_center r_F hF_ball x y hx hy
      linarith [hrF_small]
    · intro x hx y hy
      have h : dist x y ≤ 2 * r_G := h_diam2 G1' g1_center r_G hG1_ball x y hx hy
      linarith [hrG_small]
    · intro x hx y hy
      have h : dist x y ≤ 2 * r_G := h_diam2 G2' g2_center r_G hG2_ball x y hx hy
      linarith [hrG_small]
    · intro x hx y hy
      have h_dist : dist x y ≥ D_G - 2 * r_G := h_sep_lower x y hx hy
      have h4 : D_G - 2 * r_G ≥ 1 / 2 := by
        have h5 : D_G + 2 * r_G > 2 := by exact not_le.mp hG
        linarith [h_rG_le20]
      linarith
    · intro x hx
      have h1 : dist x 0 ≥ d_F - r_F := h_ball_lower F' f_center r_F hF_ball x hx
      have h4 : d_F - r_F ≥ 1 / 2 := by
        have h5 : d_F + r_F > 1 := by exact not_le.mp hF
        linarith [h_rF_le20]
      linarith
  exact ⟨1, 1, (0 : Point2), by norm_num, by norm_num,
    transfer_wz1_sep (scaleSet_one F') (scaled_one_trans_zero G1') (scaled_one_trans_zero G2') h_orig,
    by rw [scaleSet_one F']; exact hF_unit,
    by rw [scaled_one_trans_zero G1']; exact hG1_unit,
    by rw [scaled_one_trans_zero G2']; exact hG2_unit⟩

/--
Variant of `standard_separation_from_geometry` that guarantees scaling factors `s_F, s_G ≥ 1`.

When the geometry already satisfies the smallness conditions without scaling (cells small enough
and separation large enough), we use scaling factor 1. Otherwise we use the standard scaling.
-/
lemma standard_separation_from_geometry_scaling_ge_one
    {F' G1' G2' : DiscreteSet 2}
    {f_center g1_center g2_center : Point2}
    {r_F r_G : ℝ}
    (hF_ball : ∀ x ∈ F', dist x f_center ≤ r_F)
    (hG1_ball : ∀ x ∈ G1', dist x g1_center ≤ r_G)
    (hG2_ball : ∀ x ∈ G2', dist x g2_center ≤ r_G)
    (hF_unit : ∀ x ∈ F', dist x 0 ≤ 1)
    (hG1_unit : ∀ x ∈ G1', dist x 0 ≤ 1)
    (hG2_unit : ∀ x ∈ G2', dist x 0 ≤ 1)
    (hrF_pos : 0 < r_F) (hrG_pos : 0 < r_G)
    (hrF_small : 2 * r_F ≤ 1 / 10)
    (hrG_small : 2 * r_G ≤ 1 / 10)
    (h_ratio_F : 19 * r_F ≤ dist f_center 0)
    (h_ratio_G : 38 * r_G ≤ dist g1_center g2_center) :
    ∃ (s_F s_G : ℝ) (t_G : Point2),
      1 ≤ s_F ∧ 1 ≤ s_G ∧
      WZ1StandardSeparation (scaleSet s_F F')
        ((scaleSet s_G G1').image (fun x => x + t_G))
        ((scaleSet s_G G2').image (fun x => x + t_G)) ∧
      (∀ x ∈ scaleSet s_F F', dist x 0 ≤ 1) ∧
      (∀ x ∈ (scaleSet s_G G1').image (fun x => x + t_G), dist x 0 ≤ 1) ∧
      (∀ x ∈ (scaleSet s_G G2').image (fun x => x + t_G), dist x 0 ≤ 1) := by
  let d_F := dist f_center 0
  let D_G := dist g1_center g2_center
  let midpoint : Point2 := (1 / 2 : ℝ) • (g1_center + g2_center)
  have hdF_pos : 0 < d_F := by
    have h : 0 < 19 * r_F := by positivity
    linarith [h_ratio_F]
  have hD_G_pos : 0 < D_G := by
    have h : 0 < 38 * r_G := by positivity
    linarith [h_ratio_G]
  have h_rF_le20 : r_F ≤ 1 / 20 := by linarith
  have h_rG_le20 : r_G ≤ 1 / 20 := by linarith

  -- Reusable geometric facts
  have h_diam2 : ∀ (A : DiscreteSet 2) (c : Point2) (r : ℝ),
      (∀ x ∈ A, dist x c ≤ r) → ∀ (x y : Point2), x ∈ A → y ∈ A → dist x y ≤ 2 * r := by
    intro A c r hball x y hx hy
    have h1 : dist x y ≤ dist x c + dist c y := dist_triangle _ _ _
    have h2 : dist c y = dist y c := dist_comm _ _
    rw [h2] at h1
    linarith [hball x hx, hball y hy]

  have h_ball_lower : ∀ (A : DiscreteSet 2) (c : Point2) (r : ℝ),
      (∀ x ∈ A, dist x c ≤ r) → ∀ x ∈ A, dist x 0 ≥ dist c 0 - r := by
    intro A c r hball x hx
    have h1 : dist c 0 ≤ dist c x + dist x 0 := dist_triangle _ _ _
    have h2 : dist c x ≤ r := by
      have h3 : dist x c ≤ r := hball x hx
      have h4 : dist c x = dist x c := dist_comm _ _
      rw [h4]; exact h3
    linarith

  have h_g1_mid : dist g1_center midpoint = D_G / 2 := by
    have h4 : g1_center - midpoint = (1 / 2 : ℝ) • (g1_center - g2_center) := by
      ext i; fin_cases i <;> simp [midpoint, smul_sub] <;> ring
    have h5 : dist g1_center midpoint = ‖g1_center - midpoint‖ := by rw [dist_eq_norm] <;> simp
    rw [h5, h4]
    have h6 : ‖(1 / 2 : ℝ) • (g1_center - g2_center)‖ = (1 / 2 : ℝ) * ‖g1_center - g2_center‖ := by
      rw [norm_smul] <;> norm_num
    rw [h6]
    have h7 : ‖g1_center - g2_center‖ = dist g1_center g2_center := by rw [dist_eq_norm] <;> simp
    rw [h7] <;> ring

  have h_g2_mid : dist g2_center midpoint = D_G / 2 := by
    have h4 : g2_center - midpoint = (1 / 2 : ℝ) • (g2_center - g1_center) := by
      ext i; fin_cases i <;> simp [midpoint, smul_sub] <;> ring
    have h5 : dist g2_center midpoint = ‖g2_center - midpoint‖ := by rw [dist_eq_norm] <;> simp
    rw [h5, h4]
    have h6 : ‖(1 / 2 : ℝ) • (g2_center - g1_center)‖ = (1 / 2 : ℝ) * ‖g2_center - g1_center‖ := by
      rw [norm_smul] <;> norm_num
    rw [h6]
    have h7 : ‖g2_center - g1_center‖ = dist g2_center g1_center := by rw [dist_eq_norm] <;> simp
    have h8 : dist g2_center g1_center = dist g1_center g2_center := dist_comm _ _
    rw [h7, h8] <;> ring

  have h_midpoint_dist : ∀ (x : Point2), x ∈ G1' → dist x midpoint ≤ D_G / 2 + r_G := by
    intro x hx
    have h1 : dist x midpoint ≤ dist x g1_center + dist g1_center midpoint := dist_triangle _ _ _
    linarith [hG1_ball x hx, h_g1_mid]

  have h_midpoint_dist2 : ∀ (x : Point2), x ∈ G2' → dist x midpoint ≤ D_G / 2 + r_G := by
    intro x hx
    have h1 : dist x midpoint ≤ dist x g2_center + dist g2_center midpoint := dist_triangle _ _ _
    linarith [hG2_ball x hx, h_g2_mid]

  have h_sep_lower : ∀ (x0 y0 : Point2), x0 ∈ G1' → y0 ∈ G2' → dist x0 y0 ≥ D_G - 2 * r_G := by
    intro x0 y0 hx0 hy0
    have h1 : dist g1_center g2_center ≤ dist g1_center x0 + dist x0 y0 + dist y0 g2_center := by
      calc dist g1_center g2_center ≤ dist g1_center x0 + dist x0 g2_center := dist_triangle _ _ _
        _ ≤ dist g1_center x0 + dist x0 y0 + dist y0 g2_center := by
          have h2 : dist x0 g2_center ≤ dist x0 y0 + dist y0 g2_center := dist_triangle _ _ _
          linarith
    have h3 : dist g1_center x0 ≤ r_G := by
      have h4 : dist x0 g1_center ≤ r_G := hG1_ball x0 hx0
      have h5 : dist g1_center x0 = dist x0 g1_center := dist_comm _ _
      rw [h5]; exact h4
    have h4 : dist y0 g2_center ≤ r_G := hG2_ball y0 hy0
    linarith

  -- Case analysis
  by_cases hF : d_F + r_F ≤ 1
  · -- hF true
    by_cases hG : D_G + 2 * r_G ≤ 2
    · -- Case 1: both scaled
      let s_F := 1 / (d_F + r_F)
      let s_G := 2 / (D_G + 2 * r_G)
      let t_G : Point2 := -s_G • midpoint
      let F'' := scaleSet s_F F'
      let G1'' := (scaleSet s_G G1').image (fun z => z + t_G)
      let G2'' := (scaleSet s_G G2').image (fun z => z + t_G)
      have hsF_pos : 0 < s_F := by positivity
      have hsG_pos : 0 < s_G := by positivity
      have hsF_ge : 1 ≤ s_F := by
        dsimp only [s_F]; have h_pos : 0 < d_F + r_F := by positivity
        calc 1 = (d_F + r_F) / (d_F + r_F) := by field_simp [h_pos.ne'] <;> ring
          _ ≤ 1 / (d_F + r_F) := by gcongr
      have hsG_ge : 1 ≤ s_G := by
        dsimp only [s_G]; have h_pos : 0 < D_G + 2 * r_G := by positivity
        calc 1 = (D_G + 2 * r_G) / (D_G + 2 * r_G) := by field_simp [h_pos.ne'] <;> ring
          _ ≤ 2 / (D_G + 2 * r_G) := by gcongr
      have hF_diam : ∀ x ∈ F'', ∀ y ∈ F'', dist x y ≤ 1 / 10 := by
        intro x hx y hy
        rcases Finset.mem_image.mp hx with ⟨x0, hx0, rfl⟩
        rcases Finset.mem_image.mp hy with ⟨y0, hy0, rfl⟩
        have h : dist x0 y0 ≤ 2 * r_F := h_diam2 F' f_center r_F hF_ball x0 y0 hx0 hy0
        have h2 : dist (s_F • x0) (s_F • y0) = s_F * dist x0 y0 := by
          rw [dist_smul_real, abs_of_pos hsF_pos]
        rw [h2]
        have h3 : s_F * dist x0 y0 ≤ s_F * (2 * r_F) := by gcongr
        have h4 : s_F * (2 * r_F) ≤ 1 / 10 := by
          dsimp only [s_F]
          have h5 : d_F + r_F ≥ 20 * r_F := by linarith [h_ratio_F]
          calc (1 / (d_F + r_F)) * (2 * r_F) = (2 * r_F) / (d_F + r_F) := by ring
            _ ≤ (2 * r_F) / (20 * r_F) := by gcongr
            _ = 1 / 10 := by field_simp [hrF_pos.ne'] <;> ring
        linarith
      have hF_dist : ∀ x ∈ F'', 1 / 2 ≤ dist x 0 := by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨x0, hx0, rfl⟩
        have h1 : dist x0 0 ≥ d_F - r_F := h_ball_lower F' f_center r_F hF_ball x0 hx0
        have h2 : dist (s_F • x0) 0 = s_F * dist x0 0 := by
          calc dist (s_F • x0) 0 = ‖s_F • x0‖ := by rw [dist_eq_norm] <;> simp
            _ = |s_F| * ‖x0‖ := norm_smul s_F x0
            _ = s_F * ‖x0‖ := by rw [abs_of_pos hsF_pos]
            _ = s_F * dist x0 0 := by rw [dist_eq_norm] <;> simp
        rw [h2]
        have h3 : s_F * dist x0 0 ≥ s_F * (d_F - r_F) := by gcongr
        have h4 : s_F * (d_F - r_F) ≥ 1 / 2 := by
          dsimp only [s_F]
          have h5 : 0 < d_F + r_F := by positivity
          have h6 : 2 * (d_F - r_F) ≥ d_F + r_F := by linarith [h_ratio_F]
          have h7 : (d_F - r_F) / (d_F + r_F) ≥ 1 / 2 := by
            have h8 : (d_F - r_F) / (d_F + r_F) - 1 / 2 ≥ 0 := by
              have h9 : (d_F - r_F) / (d_F + r_F) - 1 / 2 =
                  (2 * (d_F - r_F) - (d_F + r_F)) / (2 * (d_F + r_F)) := by
                field_simp [h5.ne'] <;> ring
              rw [h9]
              apply div_nonneg
              · linarith
              · positivity
            linarith
          calc (1 / (d_F + r_F)) * (d_F - r_F) = (d_F - r_F) / (d_F + r_F) := by ring
            _ ≥ 1 / 2 := h7
        linarith
      have hF_unit' : ∀ x ∈ F'', dist x 0 ≤ 1 := by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨x0, hx0, rfl⟩
        have hball : dist x0 f_center ≤ r_F := hF_ball x0 hx0
        have h1 : dist x0 0 ≤ d_F + r_F := by
          calc dist x0 0 ≤ dist x0 f_center + dist f_center 0 := dist_triangle _ _ _
            _ ≤ r_F + d_F := by linarith [hball]
            _ = d_F + r_F := by ring
        have h2 : dist (s_F • x0) 0 = s_F * dist x0 0 := by
          calc dist (s_F • x0) 0 = ‖s_F • x0‖ := by rw [dist_eq_norm] <;> simp
            _ = |s_F| * ‖x0‖ := norm_smul s_F x0
            _ = s_F * ‖x0‖ := by rw [abs_of_pos hsF_pos]
            _ = s_F * dist x0 0 := by rw [dist_eq_norm] <;> simp
        rw [h2]
        have h3 : s_F * dist x0 0 ≤ s_F * (d_F + r_F) := by gcongr
        have h4 : s_F * (d_F + r_F) = 1 := by
          dsimp only [s_F]; field_simp [show (0 : ℝ) < d_F + r_F by positivity] <;> ring
        linarith
      have hG1_diam : ∀ x ∈ G1'', ∀ y ∈ G1'', dist x y ≤ 1 / 10 := by
        intro x hx y hy
        rcases Finset.mem_image.mp hx with ⟨x1, hx1, rfl⟩
        rcases Finset.mem_image.mp hy with ⟨y1, hy1, rfl⟩
        rcases Finset.mem_image.mp hx1 with ⟨x0, hx0, rfl⟩
        rcases Finset.mem_image.mp hy1 with ⟨y0, hy0, rfl⟩
        have h : dist x0 y0 ≤ 2 * r_G := h_diam2 G1' g1_center r_G hG1_ball x0 y0 hx0 hy0
        have h5 : dist (s_G • x0 + t_G) (s_G • y0 + t_G) = s_G * dist x0 y0 := by
          rw [dist_add_right, dist_smul_real, abs_of_pos hsG_pos]
        rw [h5]
        have h6 : s_G * dist x0 y0 ≤ s_G * (2 * r_G) := by gcongr
        have h7 : s_G * (2 * r_G) ≤ 1 / 10 := by
          dsimp only [s_G]
          have h8 : D_G + 2 * r_G ≥ 40 * r_G := by linarith [h_ratio_G]
          calc (2 / (D_G + 2 * r_G)) * (2 * r_G) = (4 * r_G) / (D_G + 2 * r_G) := by ring
            _ ≤ (4 * r_G) / (40 * r_G) := by gcongr
            _ = 1 / 10 := by field_simp [hrG_pos.ne'] <;> ring
        linarith
      have hG2_diam : ∀ x ∈ G2'', ∀ y ∈ G2'', dist x y ≤ 1 / 10 := by
        intro x hx y hy
        rcases Finset.mem_image.mp hx with ⟨x1, hx1, rfl⟩
        rcases Finset.mem_image.mp hy with ⟨y1, hy1, rfl⟩
        rcases Finset.mem_image.mp hx1 with ⟨x0, hx0, rfl⟩
        rcases Finset.mem_image.mp hy1 with ⟨y0, hy0, rfl⟩
        have h : dist x0 y0 ≤ 2 * r_G := h_diam2 G2' g2_center r_G hG2_ball x0 y0 hx0 hy0
        have h5 : dist (s_G • x0 + t_G) (s_G • y0 + t_G) = s_G * dist x0 y0 := by
          rw [dist_add_right, dist_smul_real, abs_of_pos hsG_pos]
        rw [h5]
        have h6 : s_G * dist x0 y0 ≤ s_G * (2 * r_G) := by gcongr
        have h7 : s_G * (2 * r_G) ≤ 1 / 10 := by
          dsimp only [s_G]
          have h8 : D_G + 2 * r_G ≥ 40 * r_G := by linarith [h_ratio_G]
          calc (2 / (D_G + 2 * r_G)) * (2 * r_G) = (4 * r_G) / (D_G + 2 * r_G) := by ring
            _ ≤ (4 * r_G) / (40 * r_G) := by gcongr
            _ = 1 / 10 := by field_simp [hrG_pos.ne'] <;> ring
        linarith
      have hG_sep : WZ1MutuallySeparated G1'' G2'' (1 / 2) := by
        intro x hx y hy
        rcases Finset.mem_image.mp hx with ⟨x1, hx1, rfl⟩
        rcases Finset.mem_image.mp hy with ⟨y1, hy1, rfl⟩
        rcases Finset.mem_image.mp hx1 with ⟨x0, hx0, rfl⟩
        rcases Finset.mem_image.mp hy1 with ⟨y0, hy0, rfl⟩
        have h_dist : dist x0 y0 ≥ D_G - 2 * r_G := h_sep_lower x0 y0 hx0 hy0
        have h5 : dist (s_G • x0 + t_G) (s_G • y0 + t_G) = s_G * dist x0 y0 := by
          rw [dist_add_right, dist_smul_real, abs_of_pos hsG_pos]
        rw [h5]
        have h6 : s_G * dist x0 y0 ≥ s_G * (D_G - 2 * r_G) := by gcongr
        have h7 : s_G * (D_G - 2 * r_G) ≥ 1 / 2 := by
          dsimp only [s_G]
          have h8 : 0 < D_G + 2 * r_G := by positivity
          have h9 : 2 * (D_G - 2 * r_G) ≥ (1 / 2 : ℝ) * (D_G + 2 * r_G) := by linarith [h_ratio_G]
          calc (2 / (D_G + 2 * r_G)) * (D_G - 2 * r_G)
              = (2 * (D_G - 2 * r_G)) / (D_G + 2 * r_G) := by ring
            _ ≥ ((1 / 2 : ℝ) * (D_G + 2 * r_G)) / (D_G + 2 * r_G) := by gcongr
            _ = 1 / 2 := by field_simp [h8.ne'] <;> ring
        linarith
      have hG1_unit' : ∀ x ∈ G1'', dist x 0 ≤ 1 := by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨x1, hx1, rfl⟩
        rcases Finset.mem_image.mp hx1 with ⟨x0, hx0, rfl⟩
        have h1 : dist x0 midpoint ≤ D_G / 2 + r_G := h_midpoint_dist x0 hx0
        have h2 : dist (s_G • x0 + t_G) 0 = s_G * dist x0 midpoint := by
          have h3 : s_G • x0 + t_G = s_G • (x0 - midpoint) := by
            ext i; fin_cases i <;> simp [t_G, midpoint, smul_sub] <;> ring
          rw [h3, dist_eq_norm]
          have h4 : ‖s_G • (x0 - midpoint) - 0‖ = |s_G| * ‖x0 - midpoint‖ := by
            simpa [sub_zero] using norm_smul s_G (x0 - midpoint)
          rw [h4, abs_of_pos hsG_pos]
          have h5 : ‖x0 - midpoint‖ = dist x0 midpoint := by rw [dist_eq_norm] <;> simp
          rw [h5]
        rw [h2]
        have h6 : s_G * dist x0 midpoint ≤ s_G * (D_G / 2 + r_G) := by gcongr
        have h7 : s_G * (D_G / 2 + r_G) = 1 := by
          dsimp only [s_G]
          have h8 : D_G / 2 + r_G = (D_G + 2 * r_G) / 2 := by ring
          rw [h8]; field_simp [show (0 : ℝ) < D_G + 2 * r_G by positivity] <;> ring
        linarith
      have hG2_unit' : ∀ x ∈ G2'', dist x 0 ≤ 1 := by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨x1, hx1, rfl⟩
        rcases Finset.mem_image.mp hx1 with ⟨x0, hx0, rfl⟩
        have h1 : dist x0 midpoint ≤ D_G / 2 + r_G := h_midpoint_dist2 x0 hx0
        have h2 : dist (s_G • x0 + t_G) 0 = s_G * dist x0 midpoint := by
          have h3 : s_G • x0 + t_G = s_G • (x0 - midpoint) := by
            ext i; fin_cases i <;> simp [t_G, midpoint, smul_sub] <;> ring
          rw [h3, dist_eq_norm]
          have h4 : ‖s_G • (x0 - midpoint) - 0‖ = |s_G| * ‖x0 - midpoint‖ := by
            simpa [sub_zero] using norm_smul s_G (x0 - midpoint)
          rw [h4, abs_of_pos hsG_pos]
          have h5 : ‖x0 - midpoint‖ = dist x0 midpoint := by rw [dist_eq_norm] <;> simp
          rw [h5]
        rw [h2]
        have h6 : s_G * dist x0 midpoint ≤ s_G * (D_G / 2 + r_G) := by gcongr
        have h7 : s_G * (D_G / 2 + r_G) = 1 := by
          dsimp only [s_G]
          have h8 : D_G / 2 + r_G = (D_G + 2 * r_G) / 2 := by ring
          rw [h8]; field_simp [show (0 : ℝ) < D_G + 2 * r_G by positivity] <;> ring
        linarith
      exact ⟨s_F, s_G, t_G, hsF_ge, hsG_ge,
        ⟨hF_diam, hG1_diam, hG2_diam, hG_sep, hF_dist⟩,
        hF_unit', hG1_unit', hG2_unit'⟩

    · -- Case 2: hF true, hG false → F scaled, G unscaled
      let s_F := 1 / (d_F + r_F)
      let t_G : Point2 := 0
      let F'' := scaleSet s_F F'
      let G1'' := (scaleSet (1 : ℝ) G1').image (fun z => z + t_G)
      let G2'' := (scaleSet (1 : ℝ) G2').image (fun z => z + t_G)
      have hsF_pos : 0 < s_F := by positivity
      have hsF_ge : 1 ≤ s_F := by
        dsimp only [s_F]; have h_pos : 0 < d_F + r_F := by positivity
        calc 1 = (d_F + r_F) / (d_F + r_F) := by field_simp [h_pos.ne'] <;> ring
          _ ≤ 1 / (d_F + r_F) := by gcongr
      have hF_diam : ∀ x ∈ F'', ∀ y ∈ F'', dist x y ≤ 1 / 10 := by
        intro x hx y hy
        rcases Finset.mem_image.mp hx with ⟨x0, hx0, rfl⟩
        rcases Finset.mem_image.mp hy with ⟨y0, hy0, rfl⟩
        have h : dist x0 y0 ≤ 2 * r_F := h_diam2 F' f_center r_F hF_ball x0 y0 hx0 hy0
        have h2 : dist (s_F • x0) (s_F • y0) = s_F * dist x0 y0 := by
          rw [dist_smul_real, abs_of_pos hsF_pos]
        rw [h2]
        have h3 : s_F * dist x0 y0 ≤ s_F * (2 * r_F) := by gcongr
        have h4 : s_F * (2 * r_F) ≤ 1 / 10 := by
          dsimp only [s_F]
          have h5 : d_F + r_F ≥ 20 * r_F := by linarith [h_ratio_F]
          calc (1 / (d_F + r_F)) * (2 * r_F) = (2 * r_F) / (d_F + r_F) := by ring
            _ ≤ (2 * r_F) / (20 * r_F) := by gcongr
            _ = 1 / 10 := by field_simp [hrF_pos.ne'] <;> ring
        linarith
      have hF_dist : ∀ x ∈ F'', 1 / 2 ≤ dist x 0 := by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨x0, hx0, rfl⟩
        have h1 : dist x0 0 ≥ d_F - r_F := h_ball_lower F' f_center r_F hF_ball x0 hx0
        have h2 : dist (s_F • x0) 0 = s_F * dist x0 0 := by
          calc dist (s_F • x0) 0 = ‖s_F • x0‖ := by rw [dist_eq_norm] <;> simp
            _ = |s_F| * ‖x0‖ := norm_smul s_F x0
            _ = s_F * ‖x0‖ := by rw [abs_of_pos hsF_pos]
            _ = s_F * dist x0 0 := by rw [dist_eq_norm] <;> simp
        rw [h2]
        have h3 : s_F * dist x0 0 ≥ s_F * (d_F - r_F) := by gcongr
        have h4 : s_F * (d_F - r_F) ≥ 1 / 2 := by
          dsimp only [s_F]
          have h5 : 0 < d_F + r_F := by positivity
          have h6 : 2 * (d_F - r_F) ≥ d_F + r_F := by linarith [h_ratio_F]
          have h7 : (d_F - r_F) / (d_F + r_F) ≥ 1 / 2 := by
            have h8 : 2 * ((d_F - r_F) / (d_F + r_F)) ≥ 1 := by
              have h9 : 2 * ((d_F - r_F) / (d_F + r_F)) = (2 * (d_F - r_F)) / (d_F + r_F) := by ring
              rw [h9]
              have h10 : (2 * (d_F - r_F)) / (d_F + r_F) ≥ (d_F + r_F) / (d_F + r_F) := by gcongr
              have h11 : (d_F + r_F) / (d_F + r_F) = 1 := by field_simp [h5.ne'] <;> ring
              rw [h11] at h10
              exact h10
            linarith
          calc (1 / (d_F + r_F)) * (d_F - r_F) = (d_F - r_F) / (d_F + r_F) := by ring
            _ ≥ 1 / 2 := h7
        linarith
      have hF_unit' : ∀ x ∈ F'', dist x 0 ≤ 1 := by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨x0, hx0, rfl⟩
        have hball : dist x0 f_center ≤ r_F := hF_ball x0 hx0
        have h1 : dist x0 0 ≤ d_F + r_F := by
          calc dist x0 0 ≤ dist x0 f_center + dist f_center 0 := dist_triangle _ _ _
            _ ≤ r_F + d_F := by linarith [hball]
            _ = d_F + r_F := by ring
        have h2 : dist (s_F • x0) 0 = s_F * dist x0 0 := by
          calc dist (s_F • x0) 0 = ‖s_F • x0‖ := by rw [dist_eq_norm] <;> simp
            _ = |s_F| * ‖x0‖ := norm_smul s_F x0
            _ = s_F * ‖x0‖ := by rw [abs_of_pos hsF_pos]
            _ = s_F * dist x0 0 := by rw [dist_eq_norm] <;> simp
        rw [h2]
        have h3 : s_F * dist x0 0 ≤ s_F * (d_F + r_F) := by gcongr
        have h4 : s_F * (d_F + r_F) = 1 := by
          dsimp only [s_F]; field_simp [show (0 : ℝ) < d_F + r_F by positivity] <;> ring
        linarith
      have hG1_diam : ∀ x ∈ G1'', ∀ y ∈ G1'', dist x y ≤ 1 / 10 := by
        intro x hx y hy
        rcases Finset.mem_image.mp hx with ⟨x1, hx1, rfl⟩
        rcases Finset.mem_image.mp hy with ⟨y1, hy1, rfl⟩
        rcases Finset.mem_image.mp hx1 with ⟨x0, hx0, rfl⟩
        rcases Finset.mem_image.mp hy1 with ⟨y0, hy0, rfl⟩
        have h : dist x0 y0 ≤ 2 * r_G := h_diam2 G1' g1_center r_G hG1_ball x0 y0 hx0 hy0
        simpa using h.trans hrG_small
      have hG2_diam : ∀ x ∈ G2'', ∀ y ∈ G2'', dist x y ≤ 1 / 10 := by
        intro x hx y hy
        rcases Finset.mem_image.mp hx with ⟨x1, hx1, rfl⟩
        rcases Finset.mem_image.mp hy with ⟨y1, hy1, rfl⟩
        rcases Finset.mem_image.mp hx1 with ⟨x0, hx0, rfl⟩
        rcases Finset.mem_image.mp hy1 with ⟨y0, hy0, rfl⟩
        have h : dist x0 y0 ≤ 2 * r_G := h_diam2 G2' g2_center r_G hG2_ball x0 y0 hx0 hy0
        simpa using h.trans hrG_small
      have hG_sep : WZ1MutuallySeparated G1'' G2'' (1 / 2) := by
        intro x hx y hy
        rcases Finset.mem_image.mp hx with ⟨x1, hx1, rfl⟩
        rcases Finset.mem_image.mp hy with ⟨y1, hy1, rfl⟩
        rcases Finset.mem_image.mp hx1 with ⟨x0, hx0, rfl⟩
        rcases Finset.mem_image.mp hy1 with ⟨y0, hy0, rfl⟩
        have h_dist : dist x0 y0 ≥ D_G - 2 * r_G := h_sep_lower x0 y0 hx0 hy0
        have h4 : D_G - 2 * r_G ≥ 1 / 2 := by
          have h5 : D_G + 2 * r_G > 2 := by exact not_le.mp hG
          linarith [h_rG_le20]
        have h6 : 1 / 2 ≤ dist x0 y0 := by linarith
        have h7 : dist ((1 : ℝ) • x0 + t_G) ((1 : ℝ) • y0 + t_G) = dist x0 y0 := by
          rw [dist_add_right, dist_smul_real] <;> norm_num
        rw [h7]
        exact h6
      have hG1_unit' : ∀ x ∈ G1'', dist x 0 ≤ 1 := by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨x1, hx1, rfl⟩
        rcases Finset.mem_image.mp hx1 with ⟨x0, hx0, rfl⟩
        have h_tG : t_G = (0 : Point2) := by rfl
        simpa only [h_tG, one_smul, add_zero] using hG1_unit x0 hx0
      have hG2_unit' : ∀ x ∈ G2'', dist x 0 ≤ 1 := by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨x1, hx1, rfl⟩
        rcases Finset.mem_image.mp hx1 with ⟨x0, hx0, rfl⟩
        have h_tG : t_G = (0 : Point2) := by rfl
        simpa only [h_tG, one_smul, add_zero] using hG2_unit x0 hx0
      exact ⟨s_F, 1, t_G, hsF_ge, by norm_num,
        ⟨hF_diam, hG1_diam, hG2_diam, hG_sep, hF_dist⟩,
        hF_unit', hG1_unit', hG2_unit'⟩

  · -- hF false
    by_cases hG : D_G + 2 * r_G ≤ 2
    · -- Case 3: hF false, hG true → F unscaled, G scaled
      let s_G := 2 / (D_G + 2 * r_G)
      let t_G : Point2 := -s_G • midpoint
      let F'' := scaleSet (1 : ℝ) F'
      let G1'' := (scaleSet s_G G1').image (fun z => z + t_G)
      let G2'' := (scaleSet s_G G2').image (fun z => z + t_G)
      have hsG_pos : 0 < s_G := by positivity
      have hsG_ge : 1 ≤ s_G := by
        dsimp only [s_G]; have h_pos : 0 < D_G + 2 * r_G := by positivity
        calc 1 = (D_G + 2 * r_G) / (D_G + 2 * r_G) := by field_simp [h_pos.ne'] <;> ring
          _ ≤ 2 / (D_G + 2 * r_G) := by gcongr
      have hF_diam : ∀ x ∈ F'', ∀ y ∈ F'', dist x y ≤ 1 / 10 := by
        intro x hx y hy
        rcases Finset.mem_image.mp hx with ⟨x0, hx0, rfl⟩
        rcases Finset.mem_image.mp hy with ⟨y0, hy0, rfl⟩
        have h : dist x0 y0 ≤ 2 * r_F := h_diam2 F' f_center r_F hF_ball x0 y0 hx0 hy0
        simpa using h.trans hrF_small
      have hF_dist : ∀ x ∈ F'', 1 / 2 ≤ dist x 0 := by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨x0, hx0, rfl⟩
        have h1 : dist x0 0 ≥ d_F - r_F := h_ball_lower F' f_center r_F hF_ball x0 hx0
        have h4 : d_F - r_F ≥ 1 / 2 := by
          have h5 : d_F + r_F > 1 := by exact not_le.mp hF
          linarith [h_rF_le20]
        have h6 : 1 / 2 ≤ dist x0 0 := by linarith
        simpa using h6
      have hF_unit' : ∀ x ∈ F'', dist x 0 ≤ 1 := by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨x0, hx0, rfl⟩
        simpa using hF_unit x0 hx0
      have hG1_diam : ∀ x ∈ G1'', ∀ y ∈ G1'', dist x y ≤ 1 / 10 := by
        intro x hx y hy
        rcases Finset.mem_image.mp hx with ⟨x1, hx1, rfl⟩
        rcases Finset.mem_image.mp hy with ⟨y1, hy1, rfl⟩
        rcases Finset.mem_image.mp hx1 with ⟨x0, hx0, rfl⟩
        rcases Finset.mem_image.mp hy1 with ⟨y0, hy0, rfl⟩
        have h : dist x0 y0 ≤ 2 * r_G := h_diam2 G1' g1_center r_G hG1_ball x0 y0 hx0 hy0
        have h5 : dist (s_G • x0 + t_G) (s_G • y0 + t_G) = s_G * dist x0 y0 := by
          rw [dist_add_right, dist_smul_real, abs_of_pos hsG_pos]
        rw [h5]
        have h6 : s_G * dist x0 y0 ≤ s_G * (2 * r_G) := by gcongr
        have h7 : s_G * (2 * r_G) ≤ 1 / 10 := by
          dsimp only [s_G]
          have h8 : D_G + 2 * r_G ≥ 40 * r_G := by linarith [h_ratio_G]
          calc (2 / (D_G + 2 * r_G)) * (2 * r_G) = (4 * r_G) / (D_G + 2 * r_G) := by ring
            _ ≤ (4 * r_G) / (40 * r_G) := by gcongr
            _ = 1 / 10 := by field_simp [hrG_pos.ne'] <;> ring
        linarith
      have hG2_diam : ∀ x ∈ G2'', ∀ y ∈ G2'', dist x y ≤ 1 / 10 := by
        intro x hx y hy
        rcases Finset.mem_image.mp hx with ⟨x1, hx1, rfl⟩
        rcases Finset.mem_image.mp hy with ⟨y1, hy1, rfl⟩
        rcases Finset.mem_image.mp hx1 with ⟨x0, hx0, rfl⟩
        rcases Finset.mem_image.mp hy1 with ⟨y0, hy0, rfl⟩
        have h : dist x0 y0 ≤ 2 * r_G := h_diam2 G2' g2_center r_G hG2_ball x0 y0 hx0 hy0
        have h5 : dist (s_G • x0 + t_G) (s_G • y0 + t_G) = s_G * dist x0 y0 := by
          rw [dist_add_right, dist_smul_real, abs_of_pos hsG_pos]
        rw [h5]
        have h6 : s_G * dist x0 y0 ≤ s_G * (2 * r_G) := by gcongr
        have h7 : s_G * (2 * r_G) ≤ 1 / 10 := by
          dsimp only [s_G]
          have h8 : D_G + 2 * r_G ≥ 40 * r_G := by linarith [h_ratio_G]
          calc (2 / (D_G + 2 * r_G)) * (2 * r_G) = (4 * r_G) / (D_G + 2 * r_G) := by ring
            _ ≤ (4 * r_G) / (40 * r_G) := by gcongr
            _ = 1 / 10 := by field_simp [hrG_pos.ne'] <;> ring
        linarith
      have hG_sep : WZ1MutuallySeparated G1'' G2'' (1 / 2) := by
        intro x hx y hy
        rcases Finset.mem_image.mp hx with ⟨x1, hx1, rfl⟩
        rcases Finset.mem_image.mp hy with ⟨y1, hy1, rfl⟩
        rcases Finset.mem_image.mp hx1 with ⟨x0, hx0, rfl⟩
        rcases Finset.mem_image.mp hy1 with ⟨y0, hy0, rfl⟩
        have h_dist : dist x0 y0 ≥ D_G - 2 * r_G := h_sep_lower x0 y0 hx0 hy0
        have h5 : dist (s_G • x0 + t_G) (s_G • y0 + t_G) = s_G * dist x0 y0 := by
          rw [dist_add_right, dist_smul_real, abs_of_pos hsG_pos]
        rw [h5]
        have h6 : s_G * dist x0 y0 ≥ s_G * (D_G - 2 * r_G) := by gcongr
        have h7 : s_G * (D_G - 2 * r_G) ≥ 1 / 2 := by
          dsimp only [s_G]
          have h8 : 0 < D_G + 2 * r_G := by positivity
          have h9 : 2 * (D_G - 2 * r_G) ≥ (1 / 2 : ℝ) * (D_G + 2 * r_G) := by linarith [h_ratio_G]
          calc (2 / (D_G + 2 * r_G)) * (D_G - 2 * r_G)
              = (2 * (D_G - 2 * r_G)) / (D_G + 2 * r_G) := by ring
            _ ≥ ((1 / 2 : ℝ) * (D_G + 2 * r_G)) / (D_G + 2 * r_G) := by gcongr
            _ = 1 / 2 := by field_simp [h8.ne'] <;> ring
        linarith
      have hG1_unit' : ∀ x ∈ G1'', dist x 0 ≤ 1 := by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨x1, hx1, rfl⟩
        rcases Finset.mem_image.mp hx1 with ⟨x0, hx0, rfl⟩
        have h1 : dist x0 midpoint ≤ D_G / 2 + r_G := h_midpoint_dist x0 hx0
        have h2 : dist (s_G • x0 + t_G) 0 = s_G * dist x0 midpoint := by
          have h3 : s_G • x0 + t_G = s_G • (x0 - midpoint) := by
            ext i; fin_cases i <;> simp [t_G, midpoint, smul_sub] <;> ring
          rw [h3, dist_eq_norm]
          have h4 : ‖s_G • (x0 - midpoint) - 0‖ = |s_G| * ‖x0 - midpoint‖ := by
            simpa [sub_zero] using norm_smul s_G (x0 - midpoint)
          rw [h4, abs_of_pos hsG_pos]
          have h5 : ‖x0 - midpoint‖ = dist x0 midpoint := by rw [dist_eq_norm] <;> simp
          rw [h5]
        rw [h2]
        have h6 : s_G * dist x0 midpoint ≤ s_G * (D_G / 2 + r_G) := by gcongr
        have h7 : s_G * (D_G / 2 + r_G) = 1 := by
          dsimp only [s_G]
          have h8 : D_G / 2 + r_G = (D_G + 2 * r_G) / 2 := by ring
          rw [h8]; field_simp [show (0 : ℝ) < D_G + 2 * r_G by positivity] <;> ring
        linarith
      have hG2_unit' : ∀ x ∈ G2'', dist x 0 ≤ 1 := by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨x1, hx1, rfl⟩
        rcases Finset.mem_image.mp hx1 with ⟨x0, hx0, rfl⟩
        have h1 : dist x0 midpoint ≤ D_G / 2 + r_G := h_midpoint_dist2 x0 hx0
        have h2 : dist (s_G • x0 + t_G) 0 = s_G * dist x0 midpoint := by
          have h3 : s_G • x0 + t_G = s_G • (x0 - midpoint) := by
            ext i; fin_cases i <;> simp [t_G, midpoint, smul_sub] <;> ring
          rw [h3, dist_eq_norm]
          have h4 : ‖s_G • (x0 - midpoint) - 0‖ = |s_G| * ‖x0 - midpoint‖ := by
            simpa [sub_zero] using norm_smul s_G (x0 - midpoint)
          rw [h4, abs_of_pos hsG_pos]
          have h5 : ‖x0 - midpoint‖ = dist x0 midpoint := by rw [dist_eq_norm] <;> simp
          rw [h5]
        rw [h2]
        have h6 : s_G * dist x0 midpoint ≤ s_G * (D_G / 2 + r_G) := by gcongr
        have h7 : s_G * (D_G / 2 + r_G) = 1 := by
          dsimp only [s_G]
          have h8 : D_G / 2 + r_G = (D_G + 2 * r_G) / 2 := by ring
          rw [h8]; field_simp [show (0 : ℝ) < D_G + 2 * r_G by positivity] <;> ring
        linarith
      exact ⟨1, s_G, t_G, by norm_num, hsG_ge,
        ⟨hF_diam, hG1_diam, hG2_diam, hG_sep, hF_dist⟩,
        hF_unit', hG1_unit', hG2_unit'⟩

    · -- Case 4: both unscaled
      exact case4_both_unscaled hF_ball hG1_ball hG2_ball hF_unit hG1_unit hG2_unit
        hrF_small hrG_small h_ratio_F h_ratio_G hF hG

end Kakeya.Assouad
