module

/-
  MultiTubeStepBHelpers.lean

  Geometric helpers for the multi-tube Step B construction.

  Main lemma:
  `conditional_tube_containment` — when L is within ρ of a grid line L'
  near x, tube(2r+4ρ, L) ∩ Y_x is contained in tubeLine(17ρ, ℓ')
  for some line ℓ' through x.
-/

public import MyLeanRepo.RadialBootstrapping.Basic
public import MyLeanRepo.RadialBootstrapping.TubeLine
public import MyLeanRepo.RadialBootstrapping.TubeFamilies
public import MyLeanRepo.RadialBootstrapping.TxDeltaSet
public import MyLeanRepo.OSWPrelude

@[expose] public section

open MeasureTheory Metric Set Finset Classical
open scoped ENNReal NNReal


noncomputable section

namespace RadialBootstrapping
namespace B1

/-- Given grid line L, point x with x ∈ tube(d, L), construct line ℓ_x
    through x parallel to L, with tube(w, L) ⊆ tubeLine(w + d, ℓ_x). -/
lemma tube_to_parallel_line
    (L : Line2) (x : Point) (w d : ℝ) (hw : 0 < w) (hd : 0 ≤ d)
    (hx : x ∈ tube d L) :
    ∃ (ℓ_x : AffineSubspace ℝ Point),
      x ∈ (ℓ_x : Set Point) ∧
      Module.finrank ℝ ℓ_x.direction = 1 ∧
      tube w L ⊆ tubeLine (w + d) ℓ_x := by
  let ℓ_x : AffineSubspace ℝ Point :=
    AffineSubspace.mk' x L.toAffine.direction
  have hx_mem : x ∈ (ℓ_x : Set Point) := by
    simp [ℓ_x]
  have hdir : ℓ_x.direction = L.toAffine.direction := by
    simp [ℓ_x]
  have hfin : Module.finrank ℝ ℓ_x.direction = 1 := by
    rw [hdir]; exact L.property
  have h_main : tube w L ⊆ tubeLine (w + d) ℓ_x := by
    intro y hy
    rcases Metric.mem_thickening_iff.mp hy with ⟨z, hzL, hdist_yz⟩
    rcases Metric.mem_thickening_iff.mp hx with ⟨p, hpL, hdist_xp⟩
    let z' : Point := x +ᵥ (z -ᵥ p)
    have h1 : z' -ᵥ x = z -ᵥ p := by simp [z']
    have h2 : z -ᵥ p ∈ L.toAffine.direction :=
      AffineSubspace.vsub_mem_direction hzL hpL
    have h3 : z' -ᵥ x ∈ ℓ_x.direction := by
      have h4 : ℓ_x.direction = L.toAffine.direction := by simp [ℓ_x]
      rw [h4, h1]
      exact h2
    have hz'_mem : z' ∈ (ℓ_x : Set Point) := by
      have h5 : (z' -ᵥ x) +ᵥ x ∈ (ℓ_x : Set Point) := by
        apply AffineSubspace.vadd_mem_mk' x (direction := L.toAffine.direction)
        rw [h1]
        exact h2
      have h6 : (z' -ᵥ x) +ᵥ x = z' := by
        simp [vsub_eq_sub]
      rw [h6] at h5
      exact h5
    have hdist_zz' : dist z z' = dist x p := by
      have h_eq1 : z - z' = p - x := by
        simp [z', vsub_eq_sub] <;> abel
      have h : dist z z' = ‖z - z'‖ := by simp [dist_eq_norm]
      rw [h, h_eq1]
      have h2 : ‖p - x‖ = ‖x - p‖ := by
        rw [show p - x = -(x - p) by abel]
        rw [norm_neg]
      exact h2
    have hdist_yz' : dist y z' < w + d := by
      have h1 : dist y z' ≤ dist y z + dist z z' := dist_triangle y z z'
      rw [hdist_zz'] at h1
      linarith [hdist_yz, hdist_xp]
    exact Metric.mem_thickening_iff.mpr ⟨z', hz'_mem, hdist_yz'⟩
  exact ⟨ℓ_x, hx_mem, hfin, h_main⟩

/-- Conditional wide tube containment: if dist(L, L') ≤ ρ and x ∈ tube(2r, L'),
    then tube(2r+4ρ, L) ∩ Y_x ⊆ tubeLine(17ρ, ℓ') for some ℓ' through x.
    Requires r ≤ ρ and ρ ≤ 1. -/
lemma conditional_tube_containment
    (L L' : Line2) (x : Point) (r ρ : ℝ)
    (hr : 0 < r) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hr_le_rho : r ≤ ρ)
    (h_dist : dist L L' ≤ ρ)
    (hx_tube : x ∈ tube (2 * r) L')
    (Y_x : Set Point) (hY_sub : Y_x ⊆ closedBall (0 : Point) 1) :
    ∃ (ℓ' : AffineSubspace ℝ Point),
      x ∈ (ℓ' : Set Point) ∧
      Module.finrank ℝ ℓ'.direction = 1 ∧
      (tube (2 * r + 4 * ρ) L ∩ Y_x) ⊆ tubeLine (17 * ρ) ℓ' := by
  have h_step1 : tube (2 * r + 4 * ρ) L ∩ Y_x ⊆
      tube (2 * r + 13 * ρ) L' := by
    intro y hy
    have hy_tube : y ∈ tube (2 * r + 4 * ρ) L := hy.1
    have hy_Y : y ∈ Y_x := hy.2
    have hynorm : ‖y‖ ≤ 1 := by
      simpa [Metric.mem_closedBall] using hY_sub hy_Y
    rcases Metric.mem_thickening_iff.mp hy_tube with ⟨z, hzL, hdist_yz⟩
    have hz_norm : ‖z‖ ≤ 7 := by
      have h1 : ‖z‖ ≤ ‖y‖ + ‖z - y‖ := by
        have h_eq : y + (z - y) = z := by abel
        have h : ‖y + (z - y)‖ ≤ ‖y‖ + ‖z - y‖ := norm_add_le y (z - y)
        rw [h_eq] at h
        exact h
      have h2 : ‖z - y‖ = dist y z := by
        simp [dist_eq_norm, norm_sub_rev]
      rw [h2] at h1
      have h4 : dist y z < 2 * r + 4 * ρ := hdist_yz
      have h5 : ‖z‖ < ‖y‖ + (2 * r + 4 * ρ) := by linarith
      have h6 : ‖y‖ + (2 * r + 4 * ρ) ≤ 7 := by
        have h7 : 2 * r + 4 * ρ ≤ 6 * ρ := by linarith
        have h8 : 6 * ρ ≤ 6 := by linarith
        linarith [hynorm]
      linarith
    have hz_in : z ∈ L.toSet ∩ closedBall (0 : Point) 7 :=
      ⟨hzL, by simpa [Metric.mem_closedBall] using hz_norm⟩
    have h_dist' : dist L' L ≤ ρ := by rwa [dist_comm]
    have hz_tube : z ∈ tube (9 * ρ) L' := by
      have h_general := line_ball_to_tube_general L' L ρ 7 hρ (by norm_num) h_dist' hz_in
      have h_eq : (7 + 2) * ρ = 9 * ρ := by ring
      rw [h_eq] at h_general
      exact h_general
    rcases Metric.mem_thickening_iff.mp hz_tube with ⟨w', hw'L', hdist_zw'⟩
    have hdist_yw' : dist y w' < 2 * r + 13 * ρ := by
      have h1 : dist y w' ≤ dist y z + dist z w' := dist_triangle y z w'
      linarith [hdist_yz, hdist_zw']
    exact Metric.mem_thickening_iff.mpr ⟨w', hw'L', hdist_yw'⟩
  rcases tube_to_parallel_line L' x (2 * r + 13 * ρ) (2 * r)
      (by positivity) (by positivity) hx_tube with
    ⟨ℓ', hx_mem, hfin, h_contain2⟩
  have h_width_eq : (2 * r + 13 * ρ) + 2 * r = 4 * r + 13 * ρ := by ring
  have h_final : tube (2 * r + 13 * ρ) L' ⊆ tubeLine (4 * r + 13 * ρ) ℓ' := by
    rw [h_width_eq] at h_contain2
    exact h_contain2
  have h_rho_bound : 4 * r + 13 * ρ ≤ 17 * ρ := by linarith
  have h_contain3 : tubeLine (4 * r + 13 * ρ) ℓ' ⊆ tubeLine (17 * ρ) ℓ' :=
    Metric.thickening_mono h_rho_bound (ℓ' : Set Point)
  have h_main : (tube (2 * r + 4 * ρ) L ∩ Y_x) ⊆ tubeLine (17 * ρ) ℓ' := by
    intro y hy
    have h1 : y ∈ tube (2 * r + 13 * ρ) L' := h_step1 ⟨hy.1, hy.2⟩
    have h2 : y ∈ tubeLine (4 * r + 13 * ρ) ℓ' := h_final h1
    exact h_contain3 h2
  exact ⟨ℓ', hx_mem, hfin, h_main⟩

/-- Conditional mass upper bound: when the ball around L contains some L' ∈ S_x,
    bound ν(tube(2r+4ρ, L) ∩ Y_x) by K * 17^σ * ρ^σ using thin tubes on a
    line through x parallel to L'. -/
lemma conditional_mass_upper_bound
    {ν₂ : Measure Point} [IsProbabilityMeasure ν₂]
    {r σ ρ K : ℝ} (hr : 0 < r) (hσ : 0 ≤ σ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hr_le_rho : r ≤ ρ) (hK : 1 ≤ K)
    (x : Point) (Y_x : Set Point) (hY_sub : Y_x ⊆ closedBall (0 : Point) 1)
    (S_x : Finset Line2) (hS_2r : ∀ L ∈ S_x, x ∈ tube (2 * r) L)
    (L : Line2) (h_nonempty : (S_x.filter (fun L' => L' ∈ Metric.ball L ρ)).Nonempty)
    (h_thin : ∀ (ℓ : AffineSubspace ℝ Point), x ∈ (ℓ : Set Point) →
        Module.finrank ℝ ℓ.direction = 1 → ∀ (w : ℝ), 0 < w →
          ν₂ (tubeLine w ℓ ∩ Y_x) ≤ ENNReal.ofReal (K * Real.rpow w σ)) :
    ν₂ (tube (2 * r + 4 * ρ) L ∩ Y_x) ≤
      ENNReal.ofReal (K * (17 : ℝ)^σ * Real.rpow ρ σ) := by
  rcases h_nonempty with ⟨L', hL'⟩
  have hL'_in_Sx : L' ∈ S_x := (Finset.mem_filter.mp hL').1
  have hL'_in_ball : L' ∈ Metric.ball L ρ := (Finset.mem_filter.mp hL').2
  have h_dist : dist L L' < ρ := by
    have h : dist L' L < ρ := Metric.mem_ball.mp hL'_in_ball
    rwa [dist_comm] at h
  have h_dist_le : dist L L' ≤ ρ := by linarith
  have hx_tube : x ∈ tube (2 * r) L' := hS_2r L' hL'_in_Sx
  rcases conditional_tube_containment L L' x r ρ hr hρ hρ1 hr_le_rho
      h_dist_le hx_tube Y_x hY_sub with
    ⟨ℓ', hx_mem, hfin, h_contain⟩
  have h_contain' : tube (2 * r + 4 * ρ) L ∩ Y_x ⊆ tubeLine (17 * ρ) ℓ' ∩ Y_x := by
    intro y hy
    exact ⟨h_contain hy, hy.2⟩
  have h1 : ν₂ (tube (2 * r + 4 * ρ) L ∩ Y_x) ≤ ν₂ (tubeLine (17 * ρ) ℓ' ∩ Y_x) :=
    measure_mono h_contain'
  have h2 : ν₂ (tubeLine (17 * ρ) ℓ' ∩ Y_x) ≤
      ENNReal.ofReal (K * Real.rpow (17 * ρ) σ) :=
    h_thin ℓ' hx_mem hfin (17 * ρ) (by positivity)
  have h4 : Real.rpow (17 * ρ) σ = Real.rpow (17 : ℝ) σ * Real.rpow ρ σ :=
    Real.mul_rpow (by norm_num) (by linarith)
  have h5 : Real.rpow (17 : ℝ) σ = (17 : ℝ)^σ := by rfl
  have h3 : K * Real.rpow (17 * ρ) σ = K * (17 : ℝ)^σ * Real.rpow ρ σ := by
    calc K * Real.rpow (17 * ρ) σ
      = K * (Real.rpow (17 : ℝ) σ * Real.rpow ρ σ) := by rw [h4]
    _ = K * (17 : ℝ)^σ * Real.rpow ρ σ := by rw [h5] <;> ring
  rw [h3] at h2
  exact le_trans h1 h2

end B1
end RadialBootstrapping
