import MyLeanRepo.Kakeya.Streamlined.Geometry

/-!
# Plane and intercept computation for tubes

Given a tube with base `p` and direction `u` in a coordinate frame where
`|u_2| ≥ 1/2`, compute a sign-flipped direction `u'` with `u'_2 > 0`,
an integer plane index `k`, and the intercept parameter `t0 ∈ (0,1)`
and point `q` on the plane `x_2 = k/2`.
-/

noncomputable section

open Kakeya.Streamlined Metric Set

namespace Kakeya.Streamlined.GeometricLemmas

/-! ### Direction normalization -/

/--
If `u_2 < 0`, flip the tube orientation: `p' = p + u`, `u' = -u`.
The underlying segment is unchanged.  If `u_2 ≥ 0`, keep as is.
-/
def normalizeDirection (p u : Point3) : Point3 × Point3 :=
  if u 2 < 0 then (p + u, -u) else (p, u)

lemma normalizeDirection_spec (p u : Point3) (h : |u 2| ≥ 1 / 2) :
    (normalizeDirection p u).2 2 > 0 ∧
    ((normalizeDirection p u).1 = p ∧ (normalizeDirection p u).2 = u ∨
     (normalizeDirection p u).1 = p + u ∧ (normalizeDirection p u).2 = -u) := by
  by_cases hneg : u 2 < 0
  · -- u 2 < 0
    have hif : normalizeDirection p u = (p + u, -u) := by
      rw [normalizeDirection, if_pos hneg]
    rw [hif]
    have h1 : (-u) 2 > 0 := by simpa using hneg
    exact ⟨h1, Or.inr ⟨rfl, rfl⟩⟩
  · -- u 2 ≥ 0
    have hpos : u 2 > 0 := by
      have h' : u 2 ≥ 0 := by linarith
      have h'' : |u 2| = u 2 := abs_of_nonneg h'
      rw [h''] at h
      linarith
    have hif : normalizeDirection p u = (p, u) := by
      rw [normalizeDirection, if_neg hneg]
    rw [hif]
    exact ⟨hpos, Or.inl ⟨rfl, rfl⟩⟩

lemma normalizeDirection_unit (p u : Point3) (hu : ‖u‖ = 1) :
    ‖(normalizeDirection p u).2‖ = 1 := by
  by_cases hneg : u 2 < 0
  · rw [normalizeDirection, if_pos hneg] <;> simp [hu, norm_neg]
  · rw [normalizeDirection, if_neg hneg] <;> simp [hu]

/-! ### Plane index -/

/--
Integer `k` such that `k/2` lies in `(p_2, p_2 + 1/2]`.
When `u_2 ≥ 1/2`, this guarantees `k/2 ∈ (p_2, p_2 + u_2]`.
-/
def planeIndex (p2 : ℝ) : ℤ :=
  Int.floor (2 * p2) + 1

lemma planeIndex_lower (p2 : ℝ) : (planeIndex p2 : ℝ) / 2 > p2 := by
  dsimp only [planeIndex]
  have h_cast : ((Int.floor (2 * p2) + 1 : ℤ) : ℝ) = (Int.floor (2 * p2) : ℝ) + 1 := by
    simp
  rw [h_cast]
  have h2 : (Int.floor (2 * p2) : ℝ) + 1 > 2 * p2 := by
    have h3 : (Int.floor (2 * p2) : ℝ) > 2 * p2 - 1 := Int.sub_one_lt_floor (2 * p2)
    linarith
  linarith

lemma planeIndex_upper (p2 : ℝ) : (planeIndex p2 : ℝ) / 2 ≤ p2 + 1 / 2 := by
  dsimp only [planeIndex]
  have h_cast : ((Int.floor (2 * p2) + 1 : ℤ) : ℝ) = (Int.floor (2 * p2) : ℝ) + 1 := by simp
  rw [h_cast]
  have h1 : (Int.floor (2 * p2) : ℝ) ≤ 2 * p2 := Int.floor_le (2 * p2)
  linarith

lemma planeIndex_in_segment (p2 u2 : ℝ) (hu2 : u2 ≥ 1 / 2) :
    (planeIndex p2 : ℝ) / 2 ≤ p2 + u2 := by
  have h1 : (planeIndex p2 : ℝ) / 2 ≤ p2 + 1 / 2 := planeIndex_upper p2
  linarith

/-- Bound on `k` given `p2 ∈ [-A/2, A/2]`. -/
lemma planeIndex_bound (p2 A : ℝ) (_hA : 0 ≤ A)
    (hlo : -A / 2 ≤ p2) (hhi : p2 ≤ A / 2) :
    -A ≤ (planeIndex p2 : ℝ) ∧ (planeIndex p2 : ℝ) ≤ A + 1 := by
  dsimp only [planeIndex]
  have h1 : -A ≤ 2 * p2 := by linarith
  have h2 : 2 * p2 ≤ A := by linarith
  have h3 : (Int.floor (2 * p2) : ℝ) ≥ 2 * p2 - 1 := (Int.sub_one_lt_floor (2 * p2)).le
  have h4 : (Int.floor (2 * p2) : ℝ) ≤ 2 * p2 := Int.floor_le (2 * p2)
  constructor
  · have h5 : (Int.floor (2 * p2) : ℝ) ≥ -A - 1 := by linarith
    have h6 : ((Int.floor (2 * p2) + 1 : ℤ) : ℝ) ≥ -A := by
      simp [h5] <;> linarith
    exact_mod_cast h6
  · have h7 : (Int.floor (2 * p2) : ℝ) ≤ A := by linarith
    have h8 : ((Int.floor (2 * p2) + 1 : ℤ) : ℝ) ≤ A + 1 := by
      simp [h7] <;> linarith
    exact_mod_cast h8

/-! ### Intercept parameter and point -/

/--
Parameter `t0 ∈ (0,1)` such that `(p + t0 • u)_2 = k/2`,
where `k = planeIndex p_2`.
Requires `u_2 > 0` and `u_2 ≥ 1/2`.
-/
def interceptParam (p2 u2 : ℝ) : ℝ :=
  ((planeIndex p2 : ℝ) / 2 - p2) / u2

lemma interceptParam_pos (p2 u2 : ℝ) (hu2_pos : 0 < u2) :
    0 < interceptParam p2 u2 := by
  dsimp only [interceptParam]
  have h1 : (planeIndex p2 : ℝ) / 2 - p2 > 0 := by
    linarith [planeIndex_lower p2]
  exact div_pos h1 hu2_pos

lemma interceptParam_le_one (p2 u2 : ℝ) (hu2 : u2 ≥ 1 / 2) :
    interceptParam p2 u2 ≤ 1 := by
  dsimp only [interceptParam]
  have h1 : (planeIndex p2 : ℝ) / 2 - p2 ≤ u2 := by
    linarith [planeIndex_upper p2]
  have h2 : 0 < u2 := by linarith
  rw [div_le_one (by linarith)] <;> linarith

lemma interceptParam_coord (p2 u2 : ℝ) (hu2_pos : 0 < u2) :
    p2 + interceptParam p2 u2 * u2 = (planeIndex p2 : ℝ) / 2 := by
  dsimp only [interceptParam]
  field_simp [hu2_pos.ne'] <;> ring

/--
Intercept point `q = p + t0 • u`, where `t0 = interceptParam p_2 u_2`.
Guaranteed `q_2 = k/2`.
-/
def interceptPoint (p u : Point3) (hu2_pos : 0 < u 2) : Point3 :=
  p + interceptParam (p 2) (u 2) • u

lemma interceptPoint_coord2 (p u : Point3) (hu2_pos : 0 < u 2) :
    (interceptPoint p u hu2_pos) 2 = (planeIndex (p 2) : ℝ) / 2 := by
  dsimp only [interceptPoint]
  have h : (p + interceptParam (p 2) (u 2) • u) 2 =
      p 2 + interceptParam (p 2) (u 2) * u 2 := by
    simp [Pi.add_apply, Pi.smul_apply]
  rw [h]
  exact interceptParam_coord (p 2) (u 2) hu2_pos

/-! ### Full pipeline for a tube -/

/--
Full normalized tube data: `(p', u', k, t0, q)` where:
- `u'_2 > 0` and `|u'_2| ≥ 1/2`
- `k = planeIndex p'_2`
- `t0 = interceptParam p'_2 u'_2 ∈ (0,1)`
- `q = p' + t0 • u'`, `q_2 = k/2`
- The segment `[p', p'+u']` equals the original segment `[p, p+u]`
-/
structure TubePlaneData (p u : Point3) where
  p' : Point3
  u' : Point3
  k : ℤ
  t0 : ℝ
  q : Point3
  hu'2_pos : 0 < u' 2
  hu'2_dom : |u' 2| ≥ 1 / 2
  h_segment : Set.image (fun t : ℝ => p' + t • u') (Set.Icc (0 : ℝ) 1) =
                   Set.image (fun t : ℝ => p + t • u) (Set.Icc (0 : ℝ) 1)
  h_p'_eq : p' = p ∨ p' = p + u
  h_u'_eq : u' = u ∨ u' = -u
  h_k_def : (k : ℝ) = (planeIndex (p' 2) : ℝ)
  h_t0_def : t0 = interceptParam (p' 2) (u' 2)
  h_q_def : q = p' + t0 • u'
  h_t0_pos : 0 < t0
  h_t0_le_one : t0 ≤ 1
  h_q2 : q 2 = (k : ℝ) / 2

/-- Construct `TubePlaneData` from a tube with `|u_2| ≥ 1/2`. -/
def computeTubePlaneData (p u : Point3) (h : |u 2| ≥ 1 / 2)
    (hu : ‖u‖ = 1) : TubePlaneData p u := by
  let r := normalizeDirection p u
  let p' := r.1
  let u' := r.2
  have hspec := normalizeDirection_spec p u h
  have hu'2_pos : 0 < u' 2 := hspec.1
  have hcases : (p' = p ∧ u' = u) ∨ (p' = p + u ∧ u' = -u) := hspec.2
  have hp'eq : p' = p ∨ p' = p + u := by
    rcases hcases with (h | h) <;> [left; right] <;> exact h.1
  have hseg : Set.image (fun t : ℝ => p' + t • u') (Set.Icc (0 : ℝ) 1) =
      Set.image (fun t : ℝ => p + t • u) (Set.Icc (0 : ℝ) 1) := by
    rcases hcases with (h | h)
    · rw [h.1, h.2]
    · rw [h.1, h.2]
      ext y
      simp only [Set.mem_image]
      constructor
      · rintro ⟨t, ht, rfl⟩
        have ht0 : 0 ≤ t := ht.1
        have ht1 : t ≤ 1 := ht.2
        have h0 : 0 ≤ 1 - t := by linarith
        have h1 : 1 - t ≤ 1 := by linarith
        refine ⟨1 - t, ⟨h0, h1⟩, ?_⟩
        simp [sub_smul, smul_sub] <;> abel
      · rintro ⟨t, ht, rfl⟩
        have ht0 : 0 ≤ t := ht.1
        have ht1 : t ≤ 1 := ht.2
        have h0 : 0 ≤ 1 - t := by linarith
        have h1 : 1 - t ≤ 1 := by linarith
        refine ⟨1 - t, ⟨h0, h1⟩, ?_⟩
        simp [sub_smul, smul_sub] <;> abel
  have hu'2_dom : |u' 2| ≥ 1 / 2 := by
    rcases hcases with (hcase | hcase)
    · rw [hcase.2] <;> exact h
    · rw [hcase.2] <;> simpa [abs_neg] using h
  let k : ℤ := planeIndex (p' 2)
  let t0 : ℝ := interceptParam (p' 2) (u' 2)
  let q : Point3 := p' + t0 • u'
  have h_t0_pos : 0 < t0 := interceptParam_pos (p' 2) (u' 2) hu'2_pos
  have h_t0_le_one : t0 ≤ 1 := interceptParam_le_one (p' 2) (u' 2) (by
    have h5 : |u' 2| ≥ 1 / 2 := hu'2_dom
    have h6 : u' 2 ≥ 1 / 2 := by
      have h7 : 0 < u' 2 := hu'2_pos
      have h8 : |u' 2| = u' 2 := abs_of_pos h7
      rw [h8] at h5; exact h5
    exact h6)
  have h_q2 : q 2 = (k : ℝ) / 2 := by
    dsimp only [q]
    have h_eq : (p' + t0 • u') 2 = p' 2 + t0 * u' 2 := by
      simp [Pi.add_apply, Pi.smul_apply]
    rw [h_eq]
    exact interceptParam_coord (p' 2) (u' 2) hu'2_pos
  have hu'eq : u' = u ∨ u' = -u := by
    rcases hcases with (h | h) <;> [left; right] <;> exact h.2
  exact ⟨p', u', k, t0, q, hu'2_pos, hu'2_dom, hseg, hp'eq, hu'eq, rfl, rfl, rfl, h_t0_pos, h_t0_le_one, h_q2⟩

end Kakeya.Streamlined.GeometricLemmas
