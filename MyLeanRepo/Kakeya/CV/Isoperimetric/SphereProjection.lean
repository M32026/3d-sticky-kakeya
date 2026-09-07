import MyLeanRepo.Kakeya.CV.Isoperimetric.Statements
import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.BrunnMinkowski.BM
import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.BrunnMinkowski.Isodiametric
import MyLeanRepo.Kakeya.CV.Targets.ProjectionArea
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Sphere projection and normalization helpers

Partitions the unit sphere into six coordinate-dominant regions and develops
isometry, projection, measurability, and quantitative lower-bound lemmas.  The
former disproof theorem is intentionally omitted; these reusable lemmas support
the corrected standard-area target `(π / 4) * μH[2]`.
-/

open MeasureTheory Metric Set Function
open scoped ENNReal

namespace Kakeya.CV

noncomputable section

-- ======================================================================
-- Point helpers
-- ======================================================================

def mkPoint2 (f : Fin 2 → ℝ) : Point 2 :=
  (WithLp.equiv 2 (Fin 2 → ℝ)).symm f

def mkPoint3 (f : Fin 3 → ℝ) : Point 3 :=
  (WithLp.equiv 2 (Fin 3 → ℝ)).symm f

lemma mkPoint2_apply (f : Fin 2 → ℝ) (i : Fin 2) : (mkPoint2 f) i = f i := by
  simp [mkPoint2, WithLp.equiv_symm_apply]

lemma mkPoint3_apply (f : Fin 3 → ℝ) (i : Fin 3) : (mkPoint3 f) i = f i := by
  simp [mkPoint3, WithLp.equiv_symm_apply]

lemma norm_sq_point3 (p : Point 3) : ‖p‖ ^ 2 = (p 0)^2 + (p 1)^2 + (p 2)^2 := by
  have h : ‖p‖ ^ 2 = ∑ i : Fin 3, (p i)^2 := EuclideanSpace.real_norm_sq_eq p
  rw [h]
  have h2 : ∑ i : Fin 3, (p i)^2 = (p 0)^2 + (p 1)^2 + (p 2)^2 := by
    simp [Fin.sum_univ_succ] <;> ring
  exact h2

lemma dist_sq_point3 (x y : Point 3) :
    dist x y ^ 2 = (x 0 - y 0)^2 + (x 1 - y 1)^2 + (x 2 - y 2)^2 := by
  have h : dist x y ^ 2 = ∑ i : Fin 3, dist (x i) (y i)^2 := EuclideanSpace.dist_sq_eq x y
  rw [h]
  have h2 : ∑ i : Fin 3, dist (x i) (y i)^2 = (x 0 - y 0)^2 + (x 1 - y 1)^2 + (x 2 - y 2)^2 := by
    simp [Fin.sum_univ_succ, Real.dist_eq] <;> ring
  exact h2

lemma dist_sq_point2 (x y : Point 2) :
    dist x y ^ 2 = (x 0 - y 0)^2 + (x 1 - y 1)^2 := by
  have h : dist x y ^ 2 = ∑ i : Fin 2, dist (x i) (y i)^2 := EuclideanSpace.dist_sq_eq x y
  rw [h]
  have h2 : ∑ i : Fin 2, dist (x i) (y i)^2 = (x 0 - y 0)^2 + (x 1 - y 1)^2 := by
    simp [Fin.sum_univ_succ, Real.dist_eq] <;> ring
  exact h2

lemma sphere_eq_sq_sum (p : Point 3) (h : p ∈ unitSphere 3) :
    (p 0)^2 + (p 1)^2 + (p 2)^2 = 1 := by
  have h1 : ‖p‖ = 1 := by simpa [unitSphere, Metric.mem_sphere] using h
  have h2 : ‖p‖ ^ 2 = (p 0)^2 + (p 1)^2 + (p 2)^2 := norm_sq_point3 p
  have h3 : ‖p‖ ^ 2 = 1 := by rw [h1] <;> norm_num
  linarith

-- ======================================================================
-- Parametric region definition
-- ======================================================================

/-- Region where coordinate `i` has the largest absolute value and sign `pos`. -/
def dominantRegion (i : Fin 3) (pos : Bool) : Set (Point 3) :=
  {p | p ∈ unitSphere 3 ∧
    (if pos then p i > 0 else p i < 0) ∧
    (∀ j ≠ i, |p i| > |p j|)}

abbrev R0p := dominantRegion 0 true
abbrev R0m := dominantRegion 0 false
abbrev R1p := dominantRegion 1 true
abbrev R1m := dominantRegion 1 false
abbrev R2p := dominantRegion 2 true
abbrev R2m := dominantRegion 2 false

-- ======================================================================
-- Isometries: coordinate flips and swaps
-- ======================================================================

/-- Flip coordinate `i`. -/
def coordFlip (i : Fin 3) (p : Point 3) : Point 3 :=
  mkPoint3 (fun j => if j = i then -(p j) else p j)

/-- Swap coordinates `i` and `j`. -/
def coordSwap (i j : Fin 3) (p : Point 3) : Point 3 :=
  mkPoint3 (fun k => if k = i then p j else if k = j then p i else p k)

lemma coordFlip_apply (i : Fin 3) (p : Point 3) (j : Fin 3) :
    (coordFlip i p) j = if j = i then -(p j) else p j := by
  simp [coordFlip, mkPoint3_apply]

lemma coordSwap_apply (i j k : Fin 3) (p : Point 3) :
    (coordSwap i j p) k = if k = i then p j else if k = j then p i else p k := by
  simp [coordSwap, mkPoint3_apply]

lemma coordFlip_isometry (i : Fin 3) : Isometry (coordFlip i) := by
  intro x y
  have h : dist (coordFlip i x) (coordFlip i y) ^ 2 = dist x y ^ 2 := by
    rw [dist_sq_point3, dist_sq_point3]
    fin_cases i <;> simp [coordFlip_apply, Fin.sum_univ_succ] <;> ring
  have h4 : 0 ≤ dist (coordFlip i x) (coordFlip i y) := by positivity
  have h5 : 0 ≤ dist x y := by positivity
  have h6 : dist (coordFlip i x) (coordFlip i y) = dist x y := by nlinarith
  simpa [edist_dist] using congr_arg ENNReal.ofReal h6

lemma coordSwap_isometry (i j : Fin 3) : Isometry (coordSwap i j) := by
  intro x y
  have h : dist (coordSwap i j x) (coordSwap i j y) ^ 2 = dist x y ^ 2 := by
    rw [dist_sq_point3, dist_sq_point3]
    fin_cases i <;> fin_cases j <;> simp [coordSwap_apply, Fin.sum_univ_succ] <;> ring
  have h4 : 0 ≤ dist (coordSwap i j x) (coordSwap i j y) := by positivity
  have h5 : 0 ≤ dist x y := by positivity
  have h6 : dist (coordSwap i j x) (coordSwap i j y) = dist x y := by nlinarith
  simpa [edist_dist] using congr_arg ENNReal.ofReal h6

-- ======================================================================
-- Helper: prove image equality using an involutive isometry
-- ======================================================================

lemma image_eq_via_invol (f : Point 3 → Point 3)
    (h_invol : ∀ p, f (f p) = p)
    (R : Set (Point 3))
    (h1 : ∀ p, p ∈ R0p → f p ∈ R)
    (h2 : ∀ q, q ∈ R → f q ∈ R0p) :
    f '' R0p = R := by
  apply Set.Subset.antisymm
  · rintro x ⟨p, hp, rfl⟩; exact h1 p hp
  · intro q hq; exact ⟨f q, h2 q hq, h_invol q⟩

-- Helper: check if a point is in R0p
lemma in_R0p_iff (p : Point 3) :
    p ∈ R0p ↔ p ∈ unitSphere 3 ∧ p 0 > 0 ∧ ∀ j ≠ (0 : Fin 3), |p 0| > |p j| := by
  simp [R0p, dominantRegion] <;> tauto

-- Coordinate transformations preserve the sphere
lemma norm_one_of_sq_one {x : ℝ} (hx : x ^ 2 = 1) (hnonneg : 0 ≤ x) : x = 1 := by
  have h : x = Real.sqrt (x ^ 2) := by rw [Real.sqrt_sq hnonneg]
  rw [h, hx] <;> norm_num

lemma sphere_preserve (f : Point 3 → Point 3)
    (h : ∀ p, (f p 0)^2 + (f p 1)^2 + (f p 2)^2 = (p 0)^2 + (p 1)^2 + (p 2)^2)
    {p : Point 3} (hp : p ∈ unitSphere 3) : f p ∈ unitSphere 3 := by
  have h1 : (p 0)^2 + (p 1)^2 + (p 2)^2 = 1 := sphere_eq_sq_sum p hp
  have h2 : (f p 0)^2 + (f p 1)^2 + (f p 2)^2 = 1 := by rw [h p, h1]
  have h3 : ‖f p‖ ^ 2 = (f p 0)^2 + (f p 1)^2 + (f p 2)^2 := norm_sq_point3 (f p)
  have h4 : ‖f p‖ ^ 2 = 1 := by linarith
  have h5 : ‖f p‖ = 1 := norm_one_of_sq_one h4 (by positivity)
  simpa [unitSphere, Metric.mem_sphere] using h5

lemma coordFlip_sphere (i : Fin 3) {p} (hp : p ∈ unitSphere 3) :
    coordFlip i p ∈ unitSphere 3 :=
  sphere_preserve (coordFlip i) (fun p => by
    fin_cases i <;> simp [coordFlip_apply] <;> ring) hp

lemma coordSwap01_sphere {p} (hp : p ∈ unitSphere 3) :
    coordSwap 0 1 p ∈ unitSphere 3 :=
  sphere_preserve (coordSwap 0 1) (fun p => by
    simp [coordSwap_apply] <;> ring) hp

lemma coordSwap02_sphere {p} (hp : p ∈ unitSphere 3) :
    coordSwap 0 2 p ∈ unitSphere 3 :=
  sphere_preserve (coordSwap 0 2) (fun p => by
    simp [coordSwap_apply] <;> ring) hp

-- coordFlip 0 maps R0p to R0m
lemma coordFlip0_image : coordFlip 0 '' R0p = R0m := by
  apply image_eq_via_invol (coordFlip 0) (fun p => by
    ext j; fin_cases j <;> simp [coordFlip_apply] <;> ring) R0m
  · intro p hp
    have h_sphere : p ∈ unitSphere 3 := hp.1
    have h_pos : p 0 > 0 := by simpa using hp.2.1
    have h_abs : ∀ j ≠ (0 : Fin 3), |p 0| > |p j| := hp.2.2
    have h_sphere' := coordFlip_sphere 0 h_sphere
    have h_neg : (coordFlip 0 p) 0 < 0 := by
      have h : (coordFlip 0 p) 0 = -(p 0) := by simp [coordFlip_apply]
      rw [h] <;> linarith
    have h_abs' : ∀ j ≠ (0 : Fin 3), |(coordFlip 0 p) 0| > |(coordFlip 0 p) j| := by
      intro j hj
      have h5 : (coordFlip 0 p) 0 = -(p 0) := by simp [coordFlip_apply]
      have h6 : (coordFlip 0 p) j = p j := by simp [coordFlip_apply, hj] <;> tauto
      rw [h5, h6]; rw [abs_neg]; exact h_abs j hj
    exact ⟨h_sphere', by simpa using h_neg, h_abs'⟩
  · intro q hq
    have h_sphere : q ∈ unitSphere 3 := hq.1
    have h_neg : q 0 < 0 := by simpa using hq.2.1
    have h_abs : ∀ j ≠ (0 : Fin 3), |q 0| > |q j| := hq.2.2
    have h_sphere' := coordFlip_sphere 0 h_sphere
    have h_pos : (coordFlip 0 q) 0 > 0 := by
      have h : (coordFlip 0 q) 0 = -(q 0) := by simp [coordFlip_apply]
      rw [h] <;> linarith
    have h_abs' : ∀ j ≠ (0 : Fin 3), |(coordFlip 0 q) 0| > |(coordFlip 0 q) j| := by
      intro j hj
      have h5 : (coordFlip 0 q) 0 = -(q 0) := by simp [coordFlip_apply]
      have h6 : (coordFlip 0 q) j = q j := by simp [coordFlip_apply, hj] <;> tauto
      rw [h5, h6]; rw [abs_neg]; exact h_abs j hj
    exact ⟨h_sphere', by simpa using h_pos, h_abs'⟩

-- coordSwap 0 1 maps R0p to R1p
lemma coordSwap01_image : coordSwap 0 1 '' R0p = R1p := by
  apply image_eq_via_invol (coordSwap 0 1) (fun p => by
    ext j; fin_cases j <;> simp [coordSwap_apply] <;> ring) R1p
  · intro p hp
    have h_sphere : p ∈ unitSphere 3 := hp.1
    have h_pos : p 0 > 0 := by simpa using hp.2.1
    have h_abs : ∀ j ≠ (0 : Fin 3), |p 0| > |p j| := hp.2.2
    let f := coordSwap 0 1 p
    have h_sphere' := coordSwap01_sphere h_sphere
    have h_pos' : f 1 > 0 := by
      have h5 : f 1 = p 0 := by dsimp only [f]; simp [coordSwap_apply]
      rw [h5]
      exact h_pos
    have h_abs' : ∀ j ≠ (1 : Fin 3), |f 1| > |f j| := by
      intro j hj
      have h_f1 : f 1 = p 0 := by dsimp only [f]; simp [coordSwap_apply]
      have h_f0 : f 0 = p 1 := by dsimp only [f]; simp [coordSwap_apply]
      have h_f2 : f 2 = p 2 := by dsimp only [f]; simp [coordSwap_apply]
      fin_cases j <;> simp [h_f1, h_f0, h_f2, h_abs] <;> tauto
    exact ⟨h_sphere', by simp; exact h_pos', h_abs'⟩
  · intro q hq
    have h_sphere : q ∈ unitSphere 3 := hq.1
    have h_pos : q 1 > 0 := by simpa using hq.2.1
    have h_abs : ∀ j ≠ (1 : Fin 3), |q 1| > |q j| := hq.2.2
    let p := coordSwap 0 1 q
    have h_sphere' := coordSwap01_sphere h_sphere
    have h_pos' : p 0 > 0 := by
      have h5 : p 0 = q 1 := by dsimp only [p]; simp [coordSwap_apply]
      rw [h5]
      exact h_pos
    have h_abs' : ∀ j ≠ (0 : Fin 3), |p 0| > |p j| := by
      intro j hj
      have h_p0 : p 0 = q 1 := by dsimp only [p]; simp [coordSwap_apply]
      have h_p1 : p 1 = q 0 := by dsimp only [p]; simp [coordSwap_apply]
      have h_p2 : p 2 = q 2 := by dsimp only [p]; simp [coordSwap_apply]
      fin_cases j <;> simp [h_p0, h_p1, h_p2, h_abs] <;> tauto
    exact ⟨h_sphere', by simp; exact h_pos', h_abs'⟩

-- coordSwap 0 2 maps R0p to R2p
lemma coordSwap02_image : coordSwap 0 2 '' R0p = R2p := by
  apply image_eq_via_invol (coordSwap 0 2) (fun p => by
    ext j; fin_cases j <;> simp [coordSwap_apply] <;> ring) R2p
  · intro p hp
    have h_sphere : p ∈ unitSphere 3 := hp.1
    have h_pos : p 0 > 0 := by simpa using hp.2.1
    have h_abs : ∀ j ≠ (0 : Fin 3), |p 0| > |p j| := hp.2.2
    let f := coordSwap 0 2 p
    have h_sphere' := coordSwap02_sphere h_sphere
    have h_pos' : f 2 > 0 := by
      have h5 : f 2 = p 0 := by dsimp only [f]; simp [coordSwap_apply]
      rw [h5]
      exact h_pos
    have h_abs' : ∀ j ≠ (2 : Fin 3), |f 2| > |f j| := by
      intro j hj
      have h_f2 : f 2 = p 0 := by dsimp only [f]; simp [coordSwap_apply]
      have h_f0 : f 0 = p 2 := by dsimp only [f]; simp [coordSwap_apply]
      have h_f1 : f 1 = p 1 := by dsimp only [f]; simp [coordSwap_apply]
      fin_cases j <;> simp [h_f2, h_f0, h_f1, h_abs] <;> tauto
    exact ⟨h_sphere', by simp; exact h_pos', h_abs'⟩
  · intro q hq
    have h_sphere : q ∈ unitSphere 3 := hq.1
    have h_pos : q 2 > 0 := by simpa using hq.2.1
    have h_abs : ∀ j ≠ (2 : Fin 3), |q 2| > |q j| := hq.2.2
    let p := coordSwap 0 2 q
    have h_sphere' := coordSwap02_sphere h_sphere
    have h_pos' : p 0 > 0 := by
      have h5 : p 0 = q 2 := by dsimp only [p]; simp [coordSwap_apply]
      rw [h5]
      exact h_pos
    have h_abs' : ∀ j ≠ (0 : Fin 3), |p 0| > |p j| := by
      intro j hj
      have h_p0 : p 0 = q 2 := by dsimp only [p]; simp [coordSwap_apply]
      have h_p1 : p 1 = q 1 := by dsimp only [p]; simp [coordSwap_apply]
      have h_p2 : p 2 = q 0 := by dsimp only [p]; simp [coordSwap_apply]
      fin_cases j <;> simp [h_p0, h_p1, h_p2, h_abs] <;> tauto
    exact ⟨h_sphere', by simp; exact h_pos', h_abs'⟩

-- For R1m and R2m, use composition: swap then flip
-- R1m = (coordSwap 0 1 ∘ coordFlip 0) '' R0p
-- The inverse is (coordFlip 0 ∘ coordSwap 0 1)

lemma R1m_image : (coordSwap 0 1 ∘ coordFlip 0) '' R0p = R1m := by
  let f := coordSwap 0 1 ∘ coordFlip 0
  let g := coordFlip 0 ∘ coordSwap 0 1
  have h_flip_invol : ∀ p, coordFlip 0 (coordFlip 0 p) = p := by
    intro p; ext j; fin_cases j <;> simp [coordFlip_apply] <;> ring
  have h_swap_invol : ∀ p, coordSwap 0 1 (coordSwap 0 1 p) = p := by
    intro p; ext j; fin_cases j <;> simp [coordSwap_apply] <;> ring
  have hfg : ∀ p, f (g p) = p := by
    intro p
    dsimp only [f, g]
    simp [h_flip_invol, h_swap_invol]
  have hgf : ∀ p, g (f p) = p := by
    intro p
    dsimp only [f, g]
    simp [h_flip_invol, h_swap_invol]
  apply Set.Subset.antisymm
  · rintro x ⟨p, hp, rfl⟩
    have h_sphere : p ∈ unitSphere 3 := hp.1
    have h_pos : p 0 > 0 := by simpa using hp.2.1
    have h_abs : ∀ j ≠ (0 : Fin 3), |p 0| > |p j| := hp.2.2
    let q := f p
    have h_sphere' : q ∈ unitSphere 3 := by
      have h1 := coordFlip_sphere 0 h_sphere
      exact coordSwap01_sphere h1
    have h_neg' : q 1 < 0 := by
      have h5 : q 1 = -(p 0) := by dsimp only [q, f]; simp [coordSwap_apply, coordFlip_apply]
      rw [h5] <;> linarith
    have h_abs' : ∀ j ≠ (1 : Fin 3), |q 1| > |q j| := by
      intro j hj
      have h_q1 : q 1 = -(p 0) := by dsimp only [q, f]; simp [coordSwap_apply, coordFlip_apply]
      have h_q0 : q 0 = p 1 := by dsimp only [q, f]; simp [coordSwap_apply, coordFlip_apply]
      have h_q2 : q 2 = p 2 := by dsimp only [q, f]; simp [coordSwap_apply, coordFlip_apply]
      fin_cases j <;> simp [h_q1, h_q0, h_q2, h_abs, abs_neg] <;> tauto
    exact ⟨h_sphere', by simp; exact h_neg', h_abs'⟩
  · intro q hq
    have h_sphere : q ∈ unitSphere 3 := hq.1
    have h_neg : q 1 < 0 := by simpa using hq.2.1
    have h_abs : ∀ j ≠ (1 : Fin 3), |q 1| > |q j| := hq.2.2
    let p := g q
    have h_sphere' : p ∈ unitSphere 3 := by
      have h1 := coordSwap01_sphere h_sphere
      exact coordFlip_sphere 0 h1
    have h_pos' : p 0 > 0 := by
      have h5 : p 0 = -(q 1) := by dsimp only [p, g]; simp [coordSwap_apply, coordFlip_apply]
      rw [h5] <;> linarith
    have h_abs' : ∀ j ≠ (0 : Fin 3), |p 0| > |p j| := by
      intro j hj
      have h_p0 : p 0 = -(q 1) := by dsimp only [p, g]; simp [coordSwap_apply, coordFlip_apply]
      have h_p1 : p 1 = q 0 := by dsimp only [p, g]; simp [coordSwap_apply, coordFlip_apply]
      have h_p2 : p 2 = q 2 := by dsimp only [p, g]; simp [coordSwap_apply, coordFlip_apply]
      fin_cases j <;> simp [h_p0, h_p1, h_p2, h_abs, abs_neg] <;> tauto
    have hp : p ∈ R0p := ⟨h_sphere', by simp; exact h_pos', h_abs'⟩
    have h_eq : f p = q := hfg q
    exact ⟨p, hp, h_eq⟩

lemma R2m_image : (coordSwap 0 2 ∘ coordFlip 0) '' R0p = R2m := by
  let f := coordSwap 0 2 ∘ coordFlip 0
  let g := coordFlip 0 ∘ coordSwap 0 2
  have h_flip_invol : ∀ p, coordFlip 0 (coordFlip 0 p) = p := by
    intro p; ext j; fin_cases j <;> simp [coordFlip_apply] <;> ring
  have h_swap_invol : ∀ p, coordSwap 0 2 (coordSwap 0 2 p) = p := by
    intro p; ext j; fin_cases j <;> simp [coordSwap_apply] <;> ring
  have hfg : ∀ p, f (g p) = p := by
    intro p
    dsimp only [f, g]
    simp [h_flip_invol, h_swap_invol]
  have hgf : ∀ p, g (f p) = p := by
    intro p
    dsimp only [f, g]
    simp [h_flip_invol, h_swap_invol]
  apply Set.Subset.antisymm
  · rintro x ⟨p, hp, rfl⟩
    have h_sphere : p ∈ unitSphere 3 := hp.1
    have h_pos : p 0 > 0 := by simpa using hp.2.1
    have h_abs : ∀ j ≠ (0 : Fin 3), |p 0| > |p j| := hp.2.2
    let q := f p
    have h_sphere' : q ∈ unitSphere 3 := by
      have h1 := coordFlip_sphere 0 h_sphere
      exact coordSwap02_sphere h1
    have h_neg' : q 2 < 0 := by
      have h5 : q 2 = -(p 0) := by dsimp only [q, f]; simp [coordSwap_apply, coordFlip_apply]
      rw [h5] <;> linarith
    have h_abs' : ∀ j ≠ (2 : Fin 3), |q 2| > |q j| := by
      intro j hj
      have h_q2 : q 2 = -(p 0) := by dsimp only [q, f]; simp [coordSwap_apply, coordFlip_apply]
      have h_q0 : q 0 = p 2 := by dsimp only [q, f]; simp [coordSwap_apply, coordFlip_apply]
      have h_q1 : q 1 = p 1 := by dsimp only [q, f]; simp [coordSwap_apply, coordFlip_apply]
      fin_cases j <;> simp [h_q2, h_q0, h_q1, h_abs, abs_neg] <;> tauto
    exact ⟨h_sphere', by simp; exact h_neg', h_abs'⟩
  · intro q hq
    have h_sphere : q ∈ unitSphere 3 := hq.1
    have h_neg : q 2 < 0 := by simpa using hq.2.1
    have h_abs : ∀ j ≠ (2 : Fin 3), |q 2| > |q j| := hq.2.2
    let p := g q
    have h_sphere' : p ∈ unitSphere 3 := by
      have h1 := coordSwap02_sphere h_sphere
      exact coordFlip_sphere 0 h1
    have h_pos' : p 0 > 0 := by
      have h5 : p 0 = -(q 2) := by dsimp only [p, g]; simp [coordSwap_apply, coordFlip_apply]
      rw [h5] <;> linarith
    have h_abs' : ∀ j ≠ (0 : Fin 3), |p 0| > |p j| := by
      intro j hj
      have h_p0 : p 0 = -(q 2) := by dsimp only [p, g]; simp [coordSwap_apply, coordFlip_apply]
      have h_p1 : p 1 = q 1 := by dsimp only [p, g]; simp [coordSwap_apply, coordFlip_apply]
      have h_p2 : p 2 = q 0 := by dsimp only [p, g]; simp [coordSwap_apply, coordFlip_apply]
      fin_cases j <;> simp [h_p0, h_p1, h_p2, h_abs, abs_neg] <;> tauto
    have hp : p ∈ R0p := ⟨h_sphere', by simp; exact h_pos', h_abs'⟩
    have h_eq : f p = q := hfg q
    exact ⟨p, hp, h_eq⟩

-- ======================================================================
-- Projection
-- ======================================================================

def projYZ : Point 3 → Point 2 :=
  fun p => mkPoint2 (fun i : Fin 2 => p i.succ)

def projectedOpenSet : Set (Point 2) :=
  {q | 2 * (q 0)^2 + (q 1)^2 < 1 ∧ (q 0)^2 + 2 * (q 1)^2 < 1}

def projectedSet : Set (Point 2) :=
  {q | 2 * (q 0)^2 + (q 1)^2 ≤ 1 ∧ (q 0)^2 + 2 * (q 1)^2 ≤ 1}

lemma projYZ_lipschitz : LipschitzWith 1 projYZ := by
  have h : ∀ (x y : Point 3), dist (projYZ x) (projYZ y) ≤ dist x y := by
    intro x y
    have h1 : dist (projYZ x) (projYZ y) ^ 2 = (x 1 - y 1)^2 + (x 2 - y 2)^2 := by
      rw [dist_sq_point2]
      have h0 : (projYZ x) 0 = x 1 := by simp [projYZ, mkPoint2_apply]
      have h1 : (projYZ x) 1 = x 2 := by simp [projYZ, mkPoint2_apply]
      have h2 : (projYZ y) 0 = y 1 := by simp [projYZ, mkPoint2_apply]
      have h3 : (projYZ y) 1 = y 2 := by simp [projYZ, mkPoint2_apply]
      rw [h0, h1, h2, h3] <;> ring
    have h2 : dist x y ^ 2 = (x 0 - y 0)^2 + (x 1 - y 1)^2 + (x 2 - y 2)^2 := dist_sq_point3 x y
    have h3 : dist (projYZ x) (projYZ y) ^ 2 ≤ dist x y ^ 2 := by
      rw [h1, h2] <;> nlinarith [sq_nonneg (x 0 - y 0)]
    have h4 : 0 ≤ dist (projYZ x) (projYZ y) := by positivity
    have h5 : 0 ≤ dist x y := by positivity
    nlinarith
  have h' : ∀ (x y : Point 3), edist (projYZ x) (projYZ y) ≤ (1 : ENNReal) * edist x y := by
    intro x y
    have h_dist : dist (projYZ x) (projYZ y) ≤ dist x y := h x y
    have h_edist : edist (projYZ x) (projYZ y) ≤ edist x y := by
      simpa [edist_dist] using ENNReal.ofReal_le_ofReal h_dist
    simpa using h_edist
  exact h'

-- ======================================================================
-- Measure equivalence Point 2 ≃ ℝ × ℝ
-- ======================================================================

/-- Linear equivalence from Point 2 to ℝ × ℝ. -/
def point2EquivProd : Point 2 ≃ₗ[ℝ] (ℝ × ℝ) :=
  { toFun := fun q => (q 0, q 1),
    invFun := fun p : ℝ × ℝ => mkPoint2 ![p.1, p.2],
    left_inv := by
      intro x; ext i; fin_cases i <;> simp [mkPoint2_apply] <;> ring,
    right_inv := by
      intro ⟨x, y⟩
      have h1 : (mkPoint2 ![x, y]) 0 = x := by simp [mkPoint2_apply]
      have h2 : (mkPoint2 ![x, y]) 1 = y := by simp [mkPoint2_apply]
      exact Prod.ext h1 h2,
    map_add' := by
      intro x y; apply Prod.ext <;> simp <;> ring,
    map_smul' := by
      intro c x; apply Prod.ext <;> simp <;> ring }

lemma point2EquivProd_mp : MeasurePreserving point2EquivProd volume volume := by
  have h1 : MeasurePreserving (WithLp.equiv 2 (Fin 2 → ℝ)) volume volume :=
    EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (ι := Fin 2)
  have h2 : MeasurePreserving (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)) volume volume :=
    volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ)
  have h_eq : (point2EquivProd : Point 2 → ℝ × ℝ) =
      (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)) ∘ (WithLp.equiv 2 (Fin 2 → ℝ)) := by
    funext q
    simp [point2EquivProd, WithLp.equiv_symm_apply, MeasurableEquiv.piFinTwo]
    <;> rfl
  rw [h_eq]
  exact h2.comp h1

lemma point2EquivProd_image_open :
    point2EquivProd '' projectedOpenSet = Geometry.ProjectionArea.ellipseSetOpen := by
  ext p
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨hq.1, hq.2⟩
  · rintro ⟨h1, h2⟩
    let q : Point 2 := mkPoint2 ![p.1, p.2]
    have hq0 : q 0 = p.1 := by simp [q, mkPoint2_apply]
    have hq1 : q 1 = p.2 := by simp [q, mkPoint2_apply]
    have hq_mem : q ∈ projectedOpenSet := by
      simp only [projectedOpenSet, Set.mem_setOf_eq, hq0, hq1] <;> exact ⟨h1, h2⟩
    have h_eq : point2EquivProd q = p := by
      apply Prod.ext <;> simp [point2EquivProd, hq0, hq1] <;> ring
    exact ⟨q, hq_mem, h_eq⟩

lemma point2EquivProd_image_closed :
    point2EquivProd '' projectedSet = Geometry.ProjectionArea.ellipseSet := by
  ext p
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨hq.1, hq.2⟩
  · rintro ⟨h1, h2⟩
    let q : Point 2 := mkPoint2 ![p.1, p.2]
    have hq0 : q 0 = p.1 := by simp [q, mkPoint2_apply]
    have hq1 : q 1 = p.2 := by simp [q, mkPoint2_apply]
    have hq_mem : q ∈ projectedSet := by
      simp only [projectedSet, Set.mem_setOf_eq, hq0, hq1] <;> exact ⟨h1, h2⟩
    have h_eq : point2EquivProd q = p := by
      apply Prod.ext <;> simp [point2EquivProd, hq0, hq1] <;> ring
    exact ⟨q, hq_mem, h_eq⟩

-- ======================================================================
-- Key lemmas
-- ======================================================================

lemma hausdorff_ge_area_two_dim {s : Set (Point 2)} :
    ENNReal.ofReal (4 / Real.pi) * volume s ≤ μH[2] s :=
  Geometry.hausdorff_twoDim_ge_volume_scaled s

lemma projectedSet_area :
    volume projectedSet = ENNReal.ofReal (2 * Real.sqrt 2 * Real.arcsin (1 / Real.sqrt 3)) := by
  have h_preimg : projectedSet = point2EquivProd ⁻¹' Geometry.ProjectionArea.ellipseSet := by
    have h : point2EquivProd ⁻¹' (point2EquivProd '' projectedSet) = projectedSet :=
      point2EquivProd.toEquiv.preimage_image projectedSet
    rw [point2EquivProd_image_closed] at h
    exact h.symm
  rw [h_preimg]
  have h_null : MeasureTheory.NullMeasurableSet Geometry.ProjectionArea.ellipseSet volume :=
    Geometry.ProjectionArea.ellipseSet_measurable.nullMeasurableSet
  have h := point2EquivProd_mp.measure_preimage (hs := h_null)
  rw [h, Geometry.ProjectionArea.ellipseSet_volume, Geometry.ProjectionArea.ellipseSetOpen_volume]

lemma projectedOpenSet_area :
    volume projectedOpenSet = volume projectedSet := by
  have h1 : projectedOpenSet = point2EquivProd ⁻¹' Geometry.ProjectionArea.ellipseSetOpen := by
    have h : point2EquivProd ⁻¹' (point2EquivProd '' projectedOpenSet) = projectedOpenSet :=
      point2EquivProd.toEquiv.preimage_image projectedOpenSet
    rw [point2EquivProd_image_open] at h
    exact h.symm
  have h2 : projectedSet = point2EquivProd ⁻¹' Geometry.ProjectionArea.ellipseSet := by
    have h : point2EquivProd ⁻¹' (point2EquivProd '' projectedSet) = projectedSet :=
      point2EquivProd.toEquiv.preimage_image projectedSet
    rw [point2EquivProd_image_closed] at h
    exact h.symm
  rw [h1, h2]
  have h_null1 : MeasureTheory.NullMeasurableSet Geometry.ProjectionArea.ellipseSetOpen volume :=
    Geometry.ProjectionArea.ellipseSetOpen_measurable.nullMeasurableSet
  have h_null2 : MeasureTheory.NullMeasurableSet Geometry.ProjectionArea.ellipseSet volume :=
    Geometry.ProjectionArea.ellipseSet_measurable.nullMeasurableSet
  rw [point2EquivProd_mp.measure_preimage (hs := h_null1),
      point2EquivProd_mp.measure_preimage (hs := h_null2)]
  exact Geometry.ProjectionArea.ellipseSet_volume.symm

lemma numerical_ineq :
    12 * Real.sqrt 2 * Real.arcsin (1 / Real.sqrt 3) > Real.pi ^ 2 := by
  have h1 : Real.sin (3 / 5 : ℝ) < 1 / Real.sqrt 3 := by
    have h_sin_bound : |Real.sin (3 / 5 : ℝ) - ((3 / 5 : ℝ) - (3 / 5 : ℝ)^3 / 6)| ≤
        (3 / 5 : ℝ)^4 * (5 / 96) := by
      have h := Real.sin_bound (show |(3 / 5 : ℝ)| ≤ 1 by norm_num)
      have h' : |(3 / 5 : ℝ)| = (3 / 5 : ℝ) := by
        rw [abs_of_pos] <;> norm_num
      simpa [h'] using h
    have h2 : Real.sin (3 / 5 : ℝ) ≤ (3 / 5 : ℝ) - (3 / 5 : ℝ)^3 / 6 + (3 / 5 : ℝ)^4 * (5 / 96) := by
      linarith [abs_le.mp h_sin_bound]
    have h3 : (3 / 5 : ℝ) - (3 / 5 : ℝ)^3 / 6 + (3 / 5 : ℝ)^4 * (5 / 96) = (2283 : ℝ) / 4000 := by norm_num
    rw [h3] at h2
    have h4 : (2283 : ℝ) / 4000 < 1 / Real.sqrt 3 := by
      have h5 : 0 < (2283 : ℝ) / 4000 := by norm_num
      have h6 : 0 < 1 / Real.sqrt 3 := by positivity
      have h7 : ((2283 : ℝ) / 4000) ^ 2 < (1 / Real.sqrt 3) ^ 2 := by
        have h8 : ((2283 : ℝ) / 4000) ^ 2 < 1 / 3 := by norm_num
        have h9 : (1 / Real.sqrt 3) ^ 2 = 1 / 3 := by
          field_simp <;> rw [Real.sq_sqrt (by norm_num)]
        rw [h9]; exact h8
      have h10 : |(2283 : ℝ) / 4000| < |1 / Real.sqrt 3| := sq_lt_sq.mp h7
      have h11 : |(2283 : ℝ) / 4000| = (2283 : ℝ) / 4000 := by rw [abs_of_pos] <;> norm_num
      have h12 : |1 / Real.sqrt 3| = 1 / Real.sqrt 3 := by rw [abs_of_pos] <;> positivity
      rw [h11, h12] at h10; exact h10
    linarith
  have h_sin35_in : Real.sin (3 / 5 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by
    exact ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
  have h_pi2 : (3 / 5 : ℝ) ≤ Real.pi / 2 := by
    have h : Real.pi > (3 : ℝ) := by linarith [Real.pi_gt_d2]
    linarith
  have h_inv : Real.arcsin (Real.sin (3 / 5 : ℝ)) = (3 / 5 : ℝ) := by
    rw [Real.arcsin_sin] <;> linarith [Real.pi_pos]
  have h_one_over_sqrt3_in : (1 / Real.sqrt 3 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by
    have h7 : 0 < 1 / Real.sqrt 3 := by positivity
    have h8 : 1 / Real.sqrt 3 ≤ 1 := by
      have h9 : Real.sqrt 3 ≥ 1 := Real.le_sqrt_of_sq_le (by norm_num)
      have h10 : 0 < Real.sqrt 3 := by positivity
      apply (div_le_one h10).mpr; exact h9
    exact ⟨by linarith, h8⟩
  have h_strict_mono : StrictMonoOn Real.arcsin (Set.Icc (-1 : ℝ) 1) :=
    Real.strictMonoOn_arcsin
  have h_arcsin : (3 / 5 : ℝ) < Real.arcsin (1 / Real.sqrt 3) := by
    have h9 : Real.arcsin (Real.sin (3 / 5 : ℝ)) < Real.arcsin (1 / Real.sqrt 3) :=
      h_strict_mono h_sin35_in h_one_over_sqrt3_in h1
    rw [h_inv] at h9; exact h9
  have h11 : 12 * Real.sqrt 2 * Real.arcsin (1 / Real.sqrt 3) > (36 / 5 : ℝ) * Real.sqrt 2 := by
    have h : 12 * Real.sqrt 2 * Real.arcsin (1 / Real.sqrt 3) > 12 * Real.sqrt 2 * (3 / 5 : ℝ) := by
      gcongr <;> linarith
    have h2 : 12 * Real.sqrt 2 * (3 / 5 : ℝ) = (36 / 5 : ℝ) * Real.sqrt 2 := by ring
    rw [h2] at h; exact h
  have h_pi4 : Real.pi ^ 4 < ((63 / 20 : ℝ)) ^ 4 := by
    have hpi : Real.pi < (63 / 20 : ℝ) := by
      have h : Real.pi < (3.15 : ℝ) := Real.pi_lt_d2
      norm_num at h ⊢ <;> exact h
    have hpos : 0 < Real.pi := Real.pi_pos
    gcongr <;> linarith
  have h_main : ((36 / 5 : ℝ) * Real.sqrt 2) ^ 2 > Real.pi ^ 4 := by
    have h15 : ((36 / 5 : ℝ) * Real.sqrt 2) ^ 2 = (2592 / 25 : ℝ) := by
      calc
        ((36 / 5 : ℝ) * Real.sqrt 2) ^ 2
          = (36 / 5 : ℝ)^2 * (Real.sqrt 2)^2 := by ring
        _ = (36 / 5 : ℝ)^2 * 2 := by rw [Real.sq_sqrt (by norm_num)]
        _ = (2592 / 25 : ℝ) := by norm_num
    rw [h15]
    have h16 : Real.pi ^ 4 < ((63 / 20 : ℝ)) ^ 4 := h_pi4
    have h17 : ((63 / 20 : ℝ)) ^ 4 < (2592 / 25 : ℝ) := by norm_num
    linarith
  have h18 : (36 / 5 : ℝ) * Real.sqrt 2 > Real.pi ^ 2 := by
    have hpos1 : 0 < (36 / 5 : ℝ) * Real.sqrt 2 := by positivity
    have hpos2 : 0 < Real.pi ^ 2 := by positivity
    nlinarith [h_main]
  linarith

-- ======================================================================
-- Projection image (sorry for now)
-- ======================================================================

lemma projYZ_image : projYZ '' R0p = projectedOpenSet := by
  apply Set.Subset.antisymm
  · -- Forward direction
    rintro q ⟨p, hp, rfl⟩
    have h_sphere : (p 0)^2 + (p 1)^2 + (p 2)^2 = 1 := sphere_eq_sq_sum p hp.1
    have h_pos : p 0 > 0 := by simpa using hp.2.1
    have h_abs1 : |p 0| > |p 1| := hp.2.2 1 (by decide)
    have h_abs2 : |p 0| > |p 2| := hp.2.2 2 (by decide)
    have h_abs0 : |p 0| = p 0 := by
      rw [abs_of_pos] <;> exact h_pos
    have h1 : p 0^2 > p 1^2 := by
      have h : |p 0| > |p 1| := h_abs1
      have h' : |p 0|^2 > |p 1|^2 := by gcongr
      simpa [h_abs0, sq_abs] using h'
    have h2 : p 0^2 > p 2^2 := by
      have h : |p 0| > |p 2| := h_abs2
      have h' : |p 0|^2 > |p 2|^2 := by gcongr
      simpa [h_abs0, sq_abs] using h'
    have hq1 : 2 * (projYZ p 0)^2 + (projYZ p 1)^2 < 1 := by
      have h_eq1 : projYZ p 0 = p 1 := by simp [projYZ, mkPoint2_apply]
      have h_eq2 : projYZ p 1 = p 2 := by simp [projYZ, mkPoint2_apply]
      rw [h_eq1, h_eq2]
      nlinarith
    have hq2 : (projYZ p 0)^2 + 2 * (projYZ p 1)^2 < 1 := by
      have h_eq1 : projYZ p 0 = p 1 := by simp [projYZ, mkPoint2_apply]
      have h_eq2 : projYZ p 1 = p 2 := by simp [projYZ, mkPoint2_apply]
      rw [h_eq1, h_eq2]
      nlinarith
    exact ⟨hq1, hq2⟩
  · -- Backward direction
    intro q hq
    have h1 : 2 * (q 0)^2 + (q 1)^2 < 1 := hq.1
    have h2 : (q 0)^2 + 2 * (q 1)^2 < 1 := hq.2
    have h3 : (q 0)^2 + (q 1)^2 < 1 := by linarith
    have h4 : 0 < 1 - (q 0)^2 - (q 1)^2 := by linarith
    let x0 : ℝ := Real.sqrt (1 - (q 0)^2 - (q 1)^2)
    have hx0_pos : 0 < x0 := Real.sqrt_pos.mpr h4
    have hx0_sq : x0^2 = 1 - (q 0)^2 - (q 1)^2 := by
      rw [Real.sq_sqrt (by linarith)]
    let p : Point 3 := mkPoint3 (fun j => if j = 0 then x0 else if j = 1 then q 0 else q 1)
    have hp0 : p 0 = x0 := by simp [p, mkPoint3_apply]
    have hp1 : p 1 = q 0 := by simp [p, mkPoint3_apply]
    have hp2 : p 2 = q 1 := by simp [p, mkPoint3_apply]
    have h_sphere : p ∈ unitSphere 3 := by
      have h_sum : (p 0)^2 + (p 1)^2 + (p 2)^2 = 1 := by
        rw [hp0, hp1, hp2, hx0_sq] <;> ring
      have h_norm : ‖p‖ ^ 2 = (p 0)^2 + (p 1)^2 + (p 2)^2 := norm_sq_point3 p
      have h_norm1 : ‖p‖ ^ 2 = 1 := by linarith
      have h_norm2 : ‖p‖ = 1 := by
        have h_nonneg : 0 ≤ ‖p‖ := by positivity
        nlinarith
      simpa [unitSphere, Metric.mem_sphere] using h_norm2
    have h_pos' : p 0 > 0 := by
      rw [hp0] <;> exact hx0_pos
    have h_abs1' : |p 0| > |p 1| := by
      rw [hp0, hp1, abs_of_pos hx0_pos]
      have h : x0^2 > (q 0)^2 := by
        rw [hx0_sq] <;> linarith
      have h5 : 0 ≤ |q 0| := by positivity
      nlinarith [sq_abs (q 0)]
    have h_abs2' : |p 0| > |p 2| := by
      rw [hp0, hp2, abs_of_pos hx0_pos]
      have h : x0^2 > (q 1)^2 := by
        rw [hx0_sq] <;> linarith
      have h5 : 0 ≤ |q 1| := by positivity
      nlinarith [sq_abs (q 1)]
    have h_abs' : ∀ j ≠ (0 : Fin 3), |p 0| > |p j| := by
      intro j hj
      fin_cases j <;> simp (config := {decide := true}) [h_abs1', h_abs2'] <;> tauto
    have hpR : p ∈ R0p := ⟨h_sphere, by simp; exact h_pos', h_abs'⟩
    have h_proj : projYZ p = q := by
      ext j
      fin_cases j <;> simp [projYZ, mkPoint2_apply, hp1, hp2] <;> ring
    exact ⟨p, hpR, h_proj⟩

-- ======================================================================
-- Lower bound for R0p
-- ======================================================================

lemma region0p_lower_bound :
    μH[2] R0p ≥ ENNReal.ofReal (8 * Real.sqrt 2 / Real.pi * Real.arcsin (1 / Real.sqrt 3)) := by
  have h1 : μH[2] (projYZ '' R0p) ≤ μH[2] R0p := by
    have h := projYZ_lipschitz.hausdorffMeasure_image_le (d := 2) (by norm_num) R0p
    simpa using h
  rw [projYZ_image] at h1
  have h2 : ENNReal.ofReal (4 / Real.pi) * volume projectedOpenSet ≤ μH[2] projectedOpenSet :=
    hausdorff_ge_area_two_dim (s := projectedOpenSet)
  rw [projectedOpenSet_area, projectedSet_area] at h2
  have h4 : ENNReal.ofReal (4 / Real.pi) *
           ENNReal.ofReal (2 * Real.sqrt 2 * Real.arcsin (1 / Real.sqrt 3)) =
         ENNReal.ofReal (8 * Real.sqrt 2 / Real.pi * Real.arcsin (1 / Real.sqrt 3)) := by
    rw [← ENNReal.ofReal_mul (by positivity)] <;> ring_nf
  rw [h4] at h2
  exact le_trans h2 h1

-- ======================================================================
-- Isometry measure preservation helper
-- ======================================================================

/-- If `f` and `g` are inverse isometries, they preserve Hausdorff measure. -/
lemma isometry_equiv_measure_preserving {f g : Point 3 → Point 3}
    (h_iso_f : Isometry f) (h_iso_g : Isometry g)
    (h_gf : ∀ x, g (f x) = x) (s : Set (Point 3)) :
    μH[2] (f '' s) = μH[2] s := by
  have h_lip_f : LipschitzWith 1 f := h_iso_f.lipschitz
  have h_lip_g : LipschitzWith 1 g := h_iso_g.lipschitz
  have h1 : μH[2] (f '' s) ≤ μH[2] s := by
    simpa using h_lip_f.hausdorffMeasure_image_le (d := 2) (by norm_num) s
  have h2 : μH[2] (g '' (f '' s)) ≤ μH[2] (f '' s) := by
    simpa using h_lip_g.hausdorffMeasure_image_le (d := 2) (by norm_num) (f '' s)
  have h3 : g '' (f '' s) = s := by
    rw [Set.image_image]
    have h4 : (g ∘ f) '' s = s := by
      have h5 : g ∘ f = id := funext h_gf
      rw [h5]
      simp
    exact h4
  rw [h3] at h2
  exact le_antisymm h1 h2

-- ======================================================================
-- All 6 regions have same measure
-- ======================================================================

lemma all_regions_same_measure :
    μH[2] R0m = μH[2] R0p ∧
    μH[2] R1p = μH[2] R0p ∧
    μH[2] R1m = μH[2] R0p ∧
    μH[2] R2p = μH[2] R0p ∧
    μH[2] R2m = μH[2] R0p := by
  have h_flip_invol : ∀ p, coordFlip 0 (coordFlip 0 p) = p := by
    intro p; ext j; fin_cases j <;> simp [coordFlip_apply] <;> ring
  have h_swap01_invol : ∀ p, coordSwap 0 1 (coordSwap 0 1 p) = p := by
    intro p; ext j; fin_cases j <;> simp [coordSwap_apply] <;> ring
  have h_swap02_invol : ∀ p, coordSwap 0 2 (coordSwap 0 2 p) = p := by
    intro p; ext j; fin_cases j <;> simp [coordSwap_apply] <;> ring
  let f1 := coordSwap 0 1 ∘ coordFlip 0
  let g1 := coordFlip 0 ∘ coordSwap 0 1
  let f2 := coordSwap 0 2 ∘ coordFlip 0
  let g2 := coordFlip 0 ∘ coordSwap 0 2
  have h_gf1 : ∀ x, g1 (f1 x) = x := by
    intro x
    calc
      g1 (f1 x)
        = coordFlip 0 (coordSwap 0 1 (coordSwap 0 1 (coordFlip 0 x))) := by rfl
      _ = coordFlip 0 (coordFlip 0 x) := by rw [h_swap01_invol (coordFlip 0 x)]
      _ = x := h_flip_invol x
  have h_gf2 : ∀ x, g2 (f2 x) = x := by
    intro x
    calc
      g2 (f2 x)
        = coordFlip 0 (coordSwap 0 2 (coordSwap 0 2 (coordFlip 0 x))) := by rfl
      _ = coordFlip 0 (coordFlip 0 x) := by rw [h_swap02_invol (coordFlip 0 x)]
      _ = x := h_flip_invol x
  have h0 : μH[2] R0m = μH[2] R0p := by
    have h_img : μH[2] (coordFlip 0 '' R0p) = μH[2] R0p :=
      isometry_equiv_measure_preserving (coordFlip_isometry 0) (coordFlip_isometry 0) h_flip_invol R0p
    rw [coordFlip0_image] at h_img
    exact h_img
  have h1 : μH[2] R1p = μH[2] R0p := by
    have h_img : μH[2] (coordSwap 0 1 '' R0p) = μH[2] R0p :=
      isometry_equiv_measure_preserving (coordSwap_isometry 0 1) (coordSwap_isometry 0 1) h_swap01_invol R0p
    rw [coordSwap01_image] at h_img
    exact h_img
  have h2 : μH[2] R1m = μH[2] R0p := by
    have h_iso_f : Isometry f1 := (coordSwap_isometry 0 1).comp (coordFlip_isometry 0)
    have h_iso_g : Isometry g1 := (coordFlip_isometry 0).comp (coordSwap_isometry 0 1)
    have h_img : μH[2] (f1 '' R0p) = μH[2] R0p :=
      isometry_equiv_measure_preserving h_iso_f h_iso_g h_gf1 R0p
    rw [R1m_image] at h_img
    exact h_img
  have h3 : μH[2] R2p = μH[2] R0p := by
    have h_img : μH[2] (coordSwap 0 2 '' R0p) = μH[2] R0p :=
      isometry_equiv_measure_preserving (coordSwap_isometry 0 2) (coordSwap_isometry 0 2) h_swap02_invol R0p
    rw [coordSwap02_image] at h_img
    exact h_img
  have h4 : μH[2] R2m = μH[2] R0p := by
    have h_iso_f : Isometry f2 := (coordSwap_isometry 0 2).comp (coordFlip_isometry 0)
    have h_iso_g : Isometry g2 := (coordFlip_isometry 0).comp (coordSwap_isometry 0 2)
    have h_img : μH[2] (f2 '' R0p) = μH[2] R0p :=
      isometry_equiv_measure_preserving h_iso_f h_iso_g h_gf2 R0p
    rw [R2m_image] at h_img
    exact h_img
  exact ⟨h0, h1, h2, h3, h4⟩

-- ======================================================================
-- Pairwise disjointness
-- ======================================================================

lemma regions_pairwise_disjoint :
    Pairwise (fun (p : Fin 3 × Bool) (q : Fin 3 × Bool) =>
      Disjoint (dominantRegion p.1 p.2) (dominantRegion q.1 q.2)) := by
  rintro ⟨i, pos⟩ ⟨j, pos'⟩ hne
  rw [Set.disjoint_left]
  intro p hp hp'
  have h_abs1 : ∀ k ≠ i, |p i| > |p k| := hp.2.2
  have h_abs2 : ∀ k ≠ j, |p j| > |p k| := hp'.2.2
  by_cases hij : i = j
  · -- Same coordinate, must have different signs
    subst hij
    have h_posne : pos ≠ pos' := by
      intro h; apply hne; simp [h]
    have hsign1 : (if pos then p i > 0 else p i < 0) := hp.2.1
    have hsign2 : (if pos' then p i > 0 else p i < 0) := hp'.2.1
    fin_cases pos <;> fin_cases pos' <;> simp_all (config := {decide := true}) <;> linarith
  · -- Different coordinates
    have h1' : |p i| > |p j| := h_abs1 j (Ne.symm hij)
    have h2' : |p j| > |p i| := h_abs2 i hij
    linarith

-- ======================================================================
-- All regions are subsets of unit sphere
-- ======================================================================

lemma regions_subset_sphere (i : Fin 3) (pos : Bool) :
    dominantRegion i pos ⊆ unitSphere 3 := by
  intro p hp
  exact hp.1

lemma dominantRegion_measurable (i : Fin 3) (pos : Bool) :
    MeasurableSet (dominantRegion i pos) := by
  have h1 : MeasurableSet (unitSphere 3) := isClosed_sphere.measurableSet
  have h_sign : MeasurableSet {p : Point 3 | (if pos then p i > 0 else p i < 0)} := by
    cases pos
    · have h_cont : Continuous (fun p : Point 3 => p i) := by
        exact PiLp.continuous_apply 2 (fun x => ℝ) i
      have h_iso : IsOpen (Iio (0 : ℝ)) := by exact isOpen_Iio
      have h_pre : IsOpen ((fun p : Point 3 => p i) ⁻¹' (Iio (0 : ℝ))) := h_iso.preimage h_cont
      have h_eq : (fun p : Point 3 => p i) ⁻¹' (Iio (0 : ℝ)) = {p : Point 3 | p i < 0} := by
        ext x; simp
      exact h_eq ▸ h_pre.measurableSet
    · have h_cont : Continuous (fun p : Point 3 => p i) := by
        exact PiLp.continuous_apply 2 (fun x => ℝ) i
      have h_iso : IsOpen (Ioi (0 : ℝ)) := by exact isOpen_Ioi
      have h_pre : IsOpen ((fun p : Point 3 => p i) ⁻¹' (Ioi (0 : ℝ))) := h_iso.preimage h_cont
      have h_eq : (fun p : Point 3 => p i) ⁻¹' (Ioi (0 : ℝ)) = {p : Point 3 | p i > 0} := by
        ext x; simp
      exact h_eq ▸ h_pre.measurableSet
  have h3 : MeasurableSet {p : Point 3 | ∀ j ≠ i, |p i| > |p j|} := by
    have h4 : ∀ (j : Fin 3), MeasurableSet {p : Point 3 | j ≠ i → |p i| > |p j|} := by
      intro j
      by_cases hji : j = i
      · subst hji
        simp
      · have h_cont_j : Continuous (fun p : Point 3 => p j) := by
          exact PiLp.continuous_apply 2 (fun x => ℝ) j
        have h_cont_i : Continuous (fun p : Point 3 => p i) := by
          exact PiLp.continuous_apply 2 (fun x => ℝ) i
        have h_abs_j : Continuous (fun p : Point 3 => |p j|) := by
          exact Continuous.abs h_cont_j
        have h_abs_i : Continuous (fun p : Point 3 => |p i|) := by
          exact Continuous.abs h_cont_i
        have h_cont : Continuous (fun p : Point 3 => |p j| - |p i|) := h_abs_j.sub h_abs_i
        have h_iso : IsOpen (Iio (0 : ℝ)) := by exact isOpen_Iio
        have h_pre : IsOpen ((fun p : Point 3 => |p j| - |p i|) ⁻¹' (Iio (0 : ℝ))) := h_iso.preimage h_cont
        have h_eq : (fun p : Point 3 => |p j| - |p i|) ⁻¹' (Iio (0 : ℝ)) = {p : Point 3 | |p j| < |p i|} := by
          ext x; simp [sub_lt_zero]
        have h5 : MeasurableSet {p : Point 3 | |p j| < |p i|} := h_eq ▸ h_pre.measurableSet
        simpa [hji] using h5
    have h6 : {p : Point 3 | ∀ j ≠ i, |p i| > |p j|} =
        ⋂ j : Fin 3, {p : Point 3 | j ≠ i → |p i| > |p j|} := by
      ext p; simp
    rw [h6]
    exact MeasurableSet.iInter h4
  exact h1.inter (h_sign.inter h3)

end

end Kakeya.CV
