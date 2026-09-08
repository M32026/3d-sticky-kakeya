import MyLeanRepo.Kakeya.Streamlined.VolumeHelpers

/-!
# Bound on the volume of a thickened framed box

This module provides a volume upper bound for the thickening of a convex body
contained in a framed axis-parallel box.
-/

noncomputable section

open MeasureTheory Metric Kakeya.Streamlined

namespace Kakeya.Streamlined

/-- An affine isometry equivalence preserves infEDist of images. -/
lemma iso_infEDist (e : Point3 ≃ᵃⁱ[ℝ] Point3) (s : Set Point3) (x : Point3) :
    infEDist (e x) (e '' s) = infEDist x s := by
  have h_iso : Isometry (e : Point3 → Point3) := e.isometry
  apply le_antisymm
  · -- Prove infEDist (e x) (e '' s) ≤ infEDist x s
    rw [le_infEDist]
    intro y hy
    have h_ey : e y ∈ e '' s := ⟨y, hy, rfl⟩
    have h_eq : edist (e x) (e y) = edist x y := h_iso.edist_eq x y
    have h : infEDist (e x) (e '' s) ≤ edist (e x) (e y) :=
      infEDist_le_edist_of_mem h_ey
    rw [h_eq] at h
    exact h
  · -- Prove infEDist x s ≤ infEDist (e x) (e '' s)
    rw [le_infEDist]
    intro z hz
    have h_exists : ∃ y, y ∈ s ∧ e y = z := by
      simpa [Set.mem_image] using hz
    rcases h_exists with ⟨y, hy, rfl⟩
    have h_eq : edist (e x) (e y) = edist x y := h_iso.edist_eq x y
    have h : infEDist x s ≤ edist x y := infEDist_le_edist_of_mem hy
    calc infEDist x s ≤ edist x y := h
      _ = edist (e x) (e y) := h_eq.symm

/-- An affine isometry equivalence commutes with closed thickening. -/
lemma AffineIsometryEquiv.cthickening_image
    (e : Point3 ≃ᵃⁱ[ℝ] Point3) (s : Set Point3) (r : ℝ) :
    e '' Metric.cthickening r s = Metric.cthickening r (e '' s) := by
  ext z
  simp only [Set.mem_image, Metric.cthickening, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have h_eq : infEDist (e x) (e '' s) = infEDist x s := iso_infEDist e s x
    rw [h_eq]
    exact hx
  · intro hz
    have h_eq : infEDist (e.symm z) s = infEDist z (e '' s) := by
      have h := iso_infEDist e s (e.symm z)
      simpa using h.symm
    refine ⟨e.symm z, ?_, by simp⟩
    rw [h_eq]
    exact hz

/-- Coordinate bound: each coordinate of a Point3 is bounded by its norm. -/
private lemma coord_le_norm (z : Point3) (i : Fin 3) : |z i| ≤ ‖z‖ := by
  have h2 : ‖z‖ = Real.sqrt (∑ j : Fin 3, |z j| ^ 2) :=
    EuclideanSpace.norm_eq z
  have h_sum_nonneg : 0 ≤ ∑ j : Fin 3, |z j| ^ 2 := by
    apply Finset.sum_nonneg
    intro j _
    exact sq_nonneg (|z j|)
  have h1 : ‖z‖ ^ 2 = ∑ j : Fin 3, |z j| ^ 2 := by
    rw [h2]
    rw [Real.sq_sqrt h_sum_nonneg]
  have h4 : |z i| ^ 2 ≤ ∑ j ∈ Finset.univ, |z j| ^ 2 := by
    exact Finset.single_le_sum (f := fun j : Fin 3 => |z j| ^ 2)
      (fun j _ => sq_nonneg (|z j|)) (Finset.mem_univ i)
  have h5 : (∑ j ∈ Finset.univ, |z j| ^ 2) = ∑ j : Fin 3, |z j| ^ 2 := by simp
  have h3 : |z i| ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [h1]
    rw [←h5]
    exact h4
  have h6 : 0 ≤ |z i| := abs_nonneg _
  have h7 : 0 ≤ ‖z‖ := norm_nonneg _
  nlinarith

/-- Thickening an axis-box by `r` is contained in the expanded axis-box. -/
lemma cthickening_axisBox_subset (a b c r : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hr : 0 ≤ r) :
    Metric.cthickening r (axisBox a b c) ⊆ axisBox (a + 2 * r) (b + 2 * r) (c + 2 * r) := by
  intro x hx
  have h_inf : infEDist x (axisBox a b c) ≤ ENNReal.ofReal r := hx
  have h_main : ∀ (i : Fin 3) (halfside : ℝ), (∀ y ∈ axisBox a b c, |y i| ≤ halfside) →
      |x i| ≤ halfside + r := by
    intro i halfside h_bd
    apply le_of_forall_pos_le_add
    intro ε hε
    have h_r_lt : r < r + ε := by linarith
    have h_ofReal_lt : ENNReal.ofReal r < ENNReal.ofReal (r + ε) := by
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hr).mpr (by linarith)
    have h_lt : infEDist x (axisBox a b c) < ENNReal.ofReal (r + ε) :=
      lt_of_le_of_lt h_inf h_ofReal_lt
    rcases infEDist_lt_iff.mp h_lt with ⟨y, hy, h_edist⟩
    have h_yi : |y i| ≤ halfside := h_bd y hy
    have h1 : edist x y = ENNReal.ofReal (dist x y) := edist_dist x y
    rw [h1] at h_edist
    have h_dist_real : dist x y < r + ε := by
      have h_nonneg1 : 0 ≤ dist x y := dist_nonneg
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg h_nonneg1).mp h_edist
    have h_coord : |x i - y i| ≤ dist x y := by
      have h2 : |(x - y) i| ≤ ‖x - y‖ := coord_le_norm (x - y) i
      simpa [dist_eq_norm] using h2
    have h3 : |x i| ≤ |y i| + |x i - y i| := by
      calc |x i| = |y i + (x i - y i)| := by ring_nf
        _ ≤ |y i| + |x i - y i| := abs_add_le _ _
    calc |x i| ≤ |y i| + |x i - y i| := h3
      _ ≤ halfside + dist x y := by linarith
      _ ≤ halfside + (r + ε) := by linarith
      _ = halfside + r + ε := by ring
  have h_bd0 : ∀ y ∈ axisBox a b c, |y 0| ≤ a / 2 := by
    intro y hy
    exact hy.1
  have h_bd1 : ∀ y ∈ axisBox a b c, |y 1| ≤ b / 2 := by
    intro y hy
    exact hy.2.1
  have h_bd2 : ∀ y ∈ axisBox a b c, |y 2| ≤ c / 2 := by
    intro y hy
    exact hy.2.2
  have h_abs0 : |x 0| ≤ a / 2 + r := h_main 0 (a / 2) h_bd0
  have h_abs1 : |x 1| ≤ b / 2 + r := h_main 1 (b / 2) h_bd1
  have h_abs2 : |x 2| ≤ c / 2 + r := h_main 2 (c / 2) h_bd2
  have h_final0 : |x 0| ≤ (a + 2 * r) / 2 := by
    have h : a / 2 + r = (a + 2 * r) / 2 := by ring
    rw [h] at h_abs0
    exact h_abs0
  have h_final1 : |x 1| ≤ (b + 2 * r) / 2 := by
    have h : b / 2 + r = (b + 2 * r) / 2 := by ring
    rw [h] at h_abs1
    exact h_abs1
  have h_final2 : |x 2| ≤ (c + 2 * r) / 2 := by
    have h : c / 2 + r = (c + 2 * r) / 2 := by ring
    rw [h] at h_abs2
    exact h_abs2
  simpa [axisBox] using ⟨h_final0, h_final1, h_final2⟩

/--
Volume bound for the thickening of a body contained in a framed axis-box.

If `V.carrier` is contained in `Vframe '' axisBox (B*u) (B*v) (B*w)`, then the
volume of its `r`-thickening is at most the volume of the expanded box
`axisBox (B*u + 2*r) (B*v + 2*r) (B*w + 2*r)`.
-/
theorem box_thickening_bound (V : Body) (Vframe : Point3 ≃ᵃⁱ[ℝ] Point3)
    (u v w B r : ℝ) (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (hr : 0 ≤ r) (hB : 1 ≤ B)
    (h : V.carrier ⊆ Vframe '' axisBox (B * u) (B * v) (B * w)) :
    MeasureTheory.volume (Metric.cthickening r V.carrier) ≤
      ENNReal.ofReal ((B * u + 2 * r) * (B * v + 2 * r) * (B * w + 2 * r)) := by
  set a : ℝ := B * u with ha_def
  set b : ℝ := B * v with hb_def
  set c : ℝ := B * w with hc_def
  have ha : 0 < a := by positivity
  have hb : 0 < b := by positivity
  have hc : 0 < c := by positivity
  have h1 : Metric.cthickening r V.carrier ⊆ Metric.cthickening r (Vframe '' axisBox a b c) := by
    intro x hx
    simp only [Metric.cthickening, Set.mem_setOf_eq] at *
    exact le_trans (infEDist_anti h) hx
  have h2 : Metric.cthickening r (Vframe '' axisBox a b c) =
      Vframe '' Metric.cthickening r (axisBox a b c) :=
    (AffineIsometryEquiv.cthickening_image Vframe (axisBox a b c) r).symm
  have h3 : Metric.cthickening r (axisBox a b c) ⊆ axisBox (a + 2 * r) (b + 2 * r) (c + 2 * r) :=
    cthickening_axisBox_subset a b c r ha hb hc hr
  have h4 : Vframe '' Metric.cthickening r (axisBox a b c) ⊆
      Vframe '' axisBox (a + 2 * r) (b + 2 * r) (c + 2 * r) := by
    intro z hz
    have h_exists : ∃ y, y ∈ Metric.cthickening r (axisBox a b c) ∧ Vframe y = z := by
      simpa [Set.mem_image] using hz
    rcases h_exists with ⟨y, hy, rfl⟩
    exact ⟨y, h3 hy, rfl⟩
  rw [h2] at h1
  have h5 : Metric.cthickening r V.carrier ⊆
      Vframe '' axisBox (a + 2 * r) (b + 2 * r) (c + 2 * r) :=
    h1.trans h4
  have h6 : MeasureTheory.volume (Metric.cthickening r V.carrier) ≤
      MeasureTheory.volume (Vframe '' axisBox (a + 2 * r) (b + 2 * r) (c + 2 * r)) :=
    measure_mono h5
  have h7 : MeasureTheory.volume (Vframe '' axisBox (a + 2 * r) (b + 2 * r) (c + 2 * r)) =
      MeasureTheory.volume (axisBox (a + 2 * r) (b + 2 * r) (c + 2 * r)) :=
    AffineIsometryEquiv.volume_image Vframe
      (axisBox (a + 2 * r) (b + 2 * r) (c + 2 * r))
      (measurableSet_axisBox (a + 2 * r) (b + 2 * r) (c + 2 * r))
  have h8 : 0 < a + 2 * r := by linarith
  have h9 : 0 < b + 2 * r := by linarith
  have h10 : 0 < c + 2 * r := by linarith
  have h11 : MeasureTheory.volume (axisBox (a + 2 * r) (b + 2 * r) (c + 2 * r)) =
      ENNReal.ofReal ((a + 2 * r) * (b + 2 * r) * (c + 2 * r)) :=
    volume_axisBox (a + 2 * r) (b + 2 * r) (c + 2 * r) h8 h9 h10
  rw [h7, h11] at h6
  simpa [ha_def, hb_def, hc_def] using h6

end Kakeya.Streamlined
