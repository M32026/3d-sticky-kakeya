import MyLeanRepo.Kakeya.CV.HausdorffMeasureSphere.Geometry


open MeasureTheory Metric Set Filter
open scoped ENNReal

namespace Kakeya.CV

noncomputable section

-- ======================================================================
-- Sphere regions and isometry images
-- ======================================================================

/-- A region of the unit sphere where coordinate `i` is at least `thr` in
    absolute value, with sign determined by `pos`. -/
def sphereRegion (i : Fin 3) (pos : Bool) (thr : ℝ) : Set (Point 3) :=
  {p | p ∈ unitSphere 3 ∧ (if pos then p i ≥ thr else p i ≤ -thr)}

/-- The isometry mapping `sphereRegion 0 true thr` to `sphereRegion i pos thr`. -/
def regionIsometry (i : Fin 3) (pos : Bool) : Point 3 → Point 3 :=
  if pos then coordSwap 0 i else (coordFlip i) ∘ (coordSwap 0 i)

/-- The inverse isometry of `regionIsometry i pos`. -/
def regionInverseIsometry (i : Fin 3) (pos : Bool) : Point 3 → Point 3 :=
  if pos then coordSwap 0 i else (coordSwap 0 i) ∘ (coordFlip i)

lemma regionIsometry_isometry (i : Fin 3) (pos : Bool) :
    Isometry (regionIsometry i pos) := by
  unfold regionIsometry
  by_cases h : pos
  · rw [if_pos h]; exact coordSwap_isometry 0 i
  · rw [if_neg h]; exact (coordFlip_isometry i).comp (coordSwap_isometry 0 i)

lemma regionInverseIsometry_isometry (i : Fin 3) (pos : Bool) :
    Isometry (regionInverseIsometry i pos) := by
  unfold regionInverseIsometry
  by_cases h : pos
  · rw [if_pos h]; exact coordSwap_isometry 0 i
  · rw [if_neg h]; exact (coordSwap_isometry 0 i).comp (coordFlip_isometry i)

lemma regionIsometry_left_inv (i : Fin 3) (pos : Bool) :
    ∀ (p : Point 3), regionInverseIsometry i pos (regionIsometry i pos p) = p := by
  unfold regionIsometry regionInverseIsometry
  by_cases h : pos
  · rw [if_pos h, if_pos h]
    intro p; ext j; fin_cases i <;> fin_cases j <;> simp [coordSwap_apply]
  · rw [if_neg h, if_neg h]
    intro p; ext j; fin_cases i <;> fin_cases j <;> simp [coordSwap_apply, coordFlip_apply]

lemma regionIsometry_right_inv (i : Fin 3) (pos : Bool) :
    ∀ (p : Point 3), regionIsometry i pos (regionInverseIsometry i pos p) = p := by
  unfold regionIsometry regionInverseIsometry
  by_cases h : pos
  · rw [if_pos h, if_pos h]
    intro p; ext j; fin_cases i <;> fin_cases j <;> simp [coordSwap_apply]
  · rw [if_neg h, if_neg h]
    intro p; ext j; fin_cases i <;> fin_cases j <;> simp [coordSwap_apply, coordFlip_apply]

lemma regionIsometry_fix_zero (i : Fin 3) (pos : Bool) :
    regionIsometry i pos (0 : Point 3) = 0 := by
  unfold regionIsometry
  by_cases h : pos
  · rw [if_pos h]; ext j; fin_cases j <;> simp [coordSwap_apply]
  · rw [if_neg h]; ext j; fin_cases j <;> simp [coordSwap_apply, coordFlip_apply]

lemma regionIsometry_sphere (i : Fin 3) (pos : Bool) {p : Point 3}
    (hp : p ∈ unitSphere 3) : regionIsometry i pos p ∈ unitSphere 3 := by
  have hf : Isometry (regionIsometry i pos) := regionIsometry_isometry i pos
  have h0 : regionIsometry i pos (0 : Point 3) = 0 := regionIsometry_fix_zero i pos
  have h1 : ‖regionIsometry i pos p‖ = ‖p‖ := by
    have h2 : dist (regionIsometry i pos p) (regionIsometry i pos (0 : Point 3)) = dist p 0 :=
      hf.dist_eq p 0
    rw [h0] at h2
    simpa [dist_zero_right] using h2
  have h3 : ‖p‖ = 1 := by simpa [unitSphere, Metric.mem_sphere, dist_zero_right] using hp
  have h4 : ‖regionIsometry i pos p‖ = 1 := h1.trans h3
  simpa [unitSphere, Metric.mem_sphere, dist_zero_right] using h4

lemma regionInverseIsometry_sphere (i : Fin 3) (pos : Bool) {p : Point 3}
    (hp : p ∈ unitSphere 3) : regionInverseIsometry i pos p ∈ unitSphere 3 := by
  have hf : Isometry (regionInverseIsometry i pos) := regionInverseIsometry_isometry i pos
  have h0 : regionInverseIsometry i pos (0 : Point 3) = 0 := by
    unfold regionInverseIsometry
    by_cases h : pos
    · rw [if_pos h]; ext j; fin_cases j <;> simp [coordSwap_apply]
    · rw [if_neg h]; ext j; fin_cases j <;> simp [coordSwap_apply, coordFlip_apply]
  have h1 : ‖regionInverseIsometry i pos p‖ = ‖p‖ := by
    have h2 : dist (regionInverseIsometry i pos p) (regionInverseIsometry i pos (0 : Point 3)) = dist p 0 :=
      hf.dist_eq p 0
    rw [h0] at h2
    simpa [dist_zero_right] using h2
  have h3 : ‖p‖ = 1 := by simpa [unitSphere, Metric.mem_sphere, dist_zero_right] using hp
  have h4 : ‖regionInverseIsometry i pos p‖ = 1 := h1.trans h3
  simpa [unitSphere, Metric.mem_sphere, dist_zero_right] using h4

lemma regionIsometry_coord (i : Fin 3) (pos : Bool) (q : Point 3) :
    (regionIsometry i pos q) i = if pos then q 0 else -(q 0) := by
  unfold regionIsometry
  cases pos
  · fin_cases i <;> simp [coordSwap_apply] <;> aesop
  · fin_cases i <;> simp [coordFlip_apply, coordSwap_apply] <;> aesop

lemma regionInverseIsometry_coord0 (i : Fin 3) (pos : Bool) (p : Point 3) :
    (regionInverseIsometry i pos p) 0 = if pos then p i else -(p i) := by
  unfold regionInverseIsometry
  cases pos
  · fin_cases i <;> simp [coordSwap_apply] <;> aesop
  · fin_cases i <;> simp [coordSwap_apply, coordFlip_apply] <;> aesop

/-- `sphereRegion i pos thr` is the image of `sphereRegion 0 true thr` under
    the coordinate isometry. -/
lemma sphereRegion_image (i : Fin 3) (pos : Bool) (thr : ℝ) :
    sphereRegion i pos thr = regionIsometry i pos '' sphereRegion 0 true thr := by
  let f := regionIsometry i pos
  let g := regionInverseIsometry i pos
  have hg_left : ∀ p, g (f p) = p := regionIsometry_left_inv i pos
  have hg_right : ∀ p, f (g p) = p := regionIsometry_right_inv i pos
  have hf_sphere : ∀ {p}, p ∈ unitSphere 3 → f p ∈ unitSphere 3 :=
    fun {p} hp => regionIsometry_sphere i pos hp
  have hg_sphere : ∀ {p}, p ∈ unitSphere 3 → g p ∈ unitSphere 3 :=
    fun {p} hp => regionInverseIsometry_sphere i pos hp
  have h_coord_f : ∀ q, (f q) i = if pos then q 0 else -(q 0) :=
    fun q => regionIsometry_coord i pos q
  have h_coord_g : ∀ p, (g p) 0 = if pos then p i else -(p i) :=
    fun p => regionInverseIsometry_coord0 i pos p
  ext p
  simp only [sphereRegion, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨h_sphere, h_cond⟩
    let q := g p
    have hq_sphere : q ∈ unitSphere 3 := hg_sphere h_sphere
    have hq0 : q 0 ≥ thr := by
      have h1 : q 0 = (if pos then p i else -(p i)) := h_coord_g p
      rw [h1]; split_ifs at h_cond ⊢ <;> linarith
    have hqA : q ∈ sphereRegion 0 true thr := by
      simp only [sphereRegion, Set.mem_setOf_eq]
      exact ⟨hq_sphere, by simpa using hq0⟩
    have hfq : f q = p := hg_right p
    exact ⟨q, hqA, hfq⟩
  · rintro ⟨q, hq, rfl⟩
    have hq0 : q 0 ≥ thr := by simpa [sphereRegion] using hq.2
    have hq_sphere : q ∈ unitSphere 3 := hq.1
    have h_sphere : f q ∈ unitSphere 3 := hf_sphere hq_sphere
    have h_cond : (f q) i = if pos then q 0 else -(q 0) := h_coord_f q
    have h3 : (if pos then (f q) i ≥ thr else (f q) i ≤ -thr) := by
      rw [h_cond]; split_ifs <;> linarith
    exact ⟨h_sphere, h3⟩

/-- Finiteness of μHE[2] on a sphere region by isometry invariance. -/
lemma sphereRegion_finite (i : Fin 3) (pos : Bool) (thr : ℝ)
    (hA0_finite : (μHE[2] : Measure (Point 3)) (sphereRegion 0 true thr) < ⊤) :
    (μHE[2] : Measure (Point 3)) (sphereRegion i pos thr) < ⊤ := by
  have h_image : sphereRegion i pos thr =
      regionIsometry i pos '' sphereRegion 0 true thr :=
    sphereRegion_image i pos thr
  rw [h_image]
  have h_iso : Isometry (regionIsometry i pos) := regionIsometry_isometry i pos
  have h_eq : (μHE[2] : Measure (Point 3)) (regionIsometry i pos '' sphereRegion 0 true thr) =
      (μHE[2] : Measure (Point 3)) (sphereRegion 0 true thr) :=
    h_iso.euclideanHausdorffMeasure_image (sphereRegion 0 true thr)
  rw [h_eq]
  exact hA0_finite


end

end Kakeya.CV
