import MyLeanRepo.Kakeya.Assouad.CinematicFamilyFromSlope.Construction
import MyLeanRepo.Kakeya.Assouad.CinematicFamilyFromSlope.UpperBound
import MyLeanRepo.Kakeya.Assouad.CinematicFamilyFromSlope.LowerBound
import MyLeanRepo.Kakeya.Assouad.CinematicFamilyFromSlope.Doubling
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.CinematicFiniteFamily
import MyLeanRepo.Kakeya.Cinematic.Definitions

/-!
# Extended cinematic family for original tube parameters

Tube parameters satisfy |a| ≤ 12, |b| ≤ 12, |d| ≤ 2. This module proves that
the family of slope curves over this extended box is still an `IsCinematicFamily`,
with constants K = 37500/99 and D = 216^12.

Whiteprint node: `extended_cinematic_family`.
-/

noncomputable section

open Kakeya.Cinematic Set Finset

attribute [local instance] Classical.propDecidable

namespace Kakeya.Assouad

/-- Extended parameter box: |p0| ≤ 12, |p1| ≤ 12, |p2| ≤ 2. -/
def extendedParamBox : Set (Fin 3 → ℝ) :=
  {p | |p 0| ≤ 12 ∧ |p 1| ≤ 12 ∧ |p 2| ≤ 2}

/-- Projection to the extended parameter box. -/
def projExtendedBox (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i =>
    match i with
    | 0 => max (-12) (min 12 (x 0))
    | 1 => max (-12) (min 12 (x 1))
    | 2 => max (-2) (min 2 (x 2))

lemma projExtendedBox_mem (x : Fin 3 → ℝ) :
    projExtendedBox x ∈ extendedParamBox := by
  simp only [extendedParamBox, Set.mem_setOf_eq]
  constructor
  · have h : -12 ≤ max (-12) (min 12 (x 0)) := by apply le_max_left
    have h2 : max (-12) (min 12 (x 0)) ≤ 12 := by
      apply max_le <;> norm_num <;> apply min_le_left
    exact abs_le.mpr ⟨h, h2⟩
  constructor
  · have h : -12 ≤ max (-12) (min 12 (x 1)) := by apply le_max_left
    have h2 : max (-12) (min 12 (x 1)) ≤ 12 := by
      apply max_le <;> norm_num <;> apply min_le_left
    exact abs_le.mpr ⟨h, h2⟩
  · have h : -2 ≤ max (-2) (min 2 (x 2)) := by apply le_max_left
    have h2 : max (-2) (min 2 (x 2)) ≤ 2 := by
      apply max_le <;> norm_num <;> apply min_le_left
    exact abs_le.mpr ⟨h, h2⟩

lemma projExtendedBox_id (x : Fin 3 → ℝ) (hx : x ∈ extendedParamBox) :
    projExtendedBox x = x := by
  funext i
  fin_cases i
  · have h1 : -12 ≤ x 0 := (abs_le.mp hx.1).1
    have h2 : x 0 ≤ 12 := (abs_le.mp hx.1).2
    simp [projExtendedBox, h1, h2] <;> linarith
  · have h1 : -12 ≤ x 1 := (abs_le.mp hx.2.1).1
    have h2 : x 1 ≤ 12 := (abs_le.mp hx.2.1).2
    simp [projExtendedBox, h1, h2] <;> linarith
  · have h1 : -2 ≤ x 2 := (abs_le.mp hx.2.2).1
    have h2 : x 2 ≤ 2 := (abs_le.mp hx.2.2).2
    simp [projExtendedBox, h1, h2] <;> linarith

/-- Clamping to [lo,hi] is 1-Lipschitz. -/
private lemma clamp_lipschitz {x y lo hi : ℝ} (hlo : lo ≤ hi) :
    |max lo (min hi x) - max lo (min hi y)| ≤ |x - y| := by
  have h1 : |min hi x - min hi y| ≤ |x - y| := abs_min_sub_le
  have h2 : |max lo (min hi x) - max lo (min hi y)| ≤ |min hi x - min hi y| := by
    have h21 : max lo (min hi x) = max (min hi x) lo := by rw [max_comm]
    have h22 : max lo (min hi y) = max (min hi y) lo := by rw [max_comm]
    rw [h21, h22]
    exact abs_max_sub_max_le_abs (min hi x) (min hi y) lo
  exact le_trans h2 h1

lemma projExtendedBox_lipschitz (x y : Fin 3 → ℝ) :
    l1Dist (projExtendedBox x) (projExtendedBox y) ≤ l1Dist x y := by
  dsimp only [l1Dist]
  apply Finset.sum_le_sum
  intro i _
  fin_cases i <;> simp [projExtendedBox, clamp_lipschitz] <;>
    exact clamp_lipschitz (by norm_num)

/-- Lower Lipschitz bound without parameter bounds. -/
lemma slopeCurve_lower_lipschitz_general (f : SlopeFunction)
    (h_ns : f.IsNonsingular) (h0 : f 0 = 0)
    (p q : Fin 3 → ℝ) (x : UnitPoint) :
    l1Dist p q ≤ (7500 / 33 : ℝ) *
      c2Distance (slopeCurve f (p 0) (p 1) (p 2))
        (slopeCurve f (q 0) (q 1) (q 2)) := by
  let g1 := slopeCurve f (p 0) (p 1) (p 2)
  let g2 := slopeCurve f (q 0) (q 1) (q 2)
  have hrep1 := slopeCurve_represents f (p 0) (p 1) (p 2)
  have hrep2 := slopeCurve_represents f (q 0) (q 1) (q 2)
  have h_l1_eq : l1Dist p q = |p 0 - q 0| + |p 1 - q 1| + |p 2 - q 2| := by
    simp [l1Dist, Fin.sum_univ_succ] <;> ring
  have h_lower : (99 / 7500 : ℝ) * (|p 0 - q 0| + |p 1 - q 1| + |p 2 - q 2|) ≤
      jetGap g1 g2 x :=
    slopeCurve_jetGap_ge f h_ns h0 g1 g2 (p 0) (p 1) (p 2) (q 0) (q 1) (q 2) hrep1 hrep2 x
  have h_lower' : (99 / 7500 : ℝ) * l1Dist p q ≤ jetGap g1 g2 x := by
    rw [h_l1_eq]; exact h_lower
  have h_jet : jetGap g1 g2 x ≤ 3 * c2Distance g1 g2 :=
    jetGap_le_three_mul_c2Distance g1 g2 x
  have h : (99 / 7500 : ℝ) * l1Dist p q ≤ 3 * c2Distance g1 g2 := by linarith
  have h99 : (0 : ℝ) < 99 / 7500 := by norm_num
  have h_div : l1Dist p q ≤ (3 * c2Distance g1 g2) / (99 / 7500 : ℝ) := by
    calc l1Dist p q
      = ((99 / 7500 : ℝ) * l1Dist p q) / (99 / 7500 : ℝ) := by field_simp [h99.ne'] <;> ring
    _ ≤ (3 * c2Distance g1 g2) / (99 / 7500 : ℝ) := by gcongr
  have h_eq : (3 * c2Distance g1 g2) / (99 / 7500 : ℝ) = (7500 / 33 : ℝ) * c2Distance g1 g2 := by
    field_simp [h99.ne'] <;> ring_nf <;> norm_num
  rw [h_eq] at h_div
  exact h_div

/-- The extended family of slope curves. -/
def extendedSlopeCurveFamily (f : SlopeFunction) : Set C2Function :=
  let φ : (Fin 3 → ℝ) → C2Function := fun p => slopeCurve f (p 0) (p 1) (p 2)
  φ '' extendedParamBox

/-- Extract parameters from a curve in the extended family. -/
lemma extendedSlopeCurveFamily_extract (f : SlopeFunction)
    {g : C2Function} (hg : g ∈ extendedSlopeCurveFamily f) :
    ∃ (a b d : ℝ), |a| ≤ 12 ∧ |b| ≤ 12 ∧ |d| ≤ 2 ∧
      g = slopeCurve f a b d := by
  simp only [extendedSlopeCurveFamily, Set.mem_image] at hg
  rcases hg with ⟨p, hp, rfl⟩
  exact ⟨p 0, p 1, p 2, hp.1, hp.2.1, hp.2.2, rfl⟩

/--
The normalized extended slope-curve family has a uniform absolute two-jet
bound, independent of the concrete slope function.
-/
lemma extendedSlopeCurveFamily_jet_bound
    (f : SlopeFunction) (h_ns : f.IsNonsingular) (h0 : f 0 = 0) :
    ∀ g ∈ extendedSlopeCurveFamily f, ∀ x : UnitPoint,
      |g x| ≤ 40 ∧ |g.firstDeriv x| ≤ 40 ∧ |g.secondDeriv x| ≤ 40 := by
  intro g hg x
  rcases extendedSlopeCurveFamily_extract f hg with
    ⟨a, b, d, ha, hb, hd, rfl⟩
  have hfx : |f x| ≤ 2 :=
    abs_fx_le_two f h_ns h0 x.property
  have hfx' : |deriv f x| ≤ 2 := by
    exact (h_ns x ⟨by linarith [x.property.1], by linarith [x.property.2]⟩).2.1
  have hfx'' : |deriv (deriv f) x| ≤ 1 / 100 := by
    exact (h_ns x ⟨by linarith [x.property.1], by linarith [x.property.2]⟩).2.2
  have hx : |(x : ℝ)| ≤ 1 := by
    rw [abs_of_nonneg x.property.1]
    exact x.property.2
  constructor
  · rw [slopeCurve_value]
    calc
      |a + b * f x + d * (x : ℝ) * f x|
          ≤ |a| + |b * f x| + |d * (x : ℝ) * f x| :=
        abs_add_three _ _ _
      _ = |a| + |b| * |f x| + |d| * |(x : ℝ)| * |f x| := by
        rw [abs_mul, abs_mul, abs_mul]
      _ ≤ 12 + 12 * 2 + 2 * 1 * 2 := by gcongr
      _ = 40 := by norm_num
  constructor
  · rw [slopeCurve_firstDeriv]
    calc
      |b * deriv f x + d * (f x + (x : ℝ) * deriv f x)|
          ≤ |b * deriv f x| +
              |d * (f x + (x : ℝ) * deriv f x)| :=
        abs_add_le _ _
      _ = |b| * |deriv f x| +
            |d| * |f x + (x : ℝ) * deriv f x| := by
        rw [abs_mul, abs_mul]
      _ ≤ 12 * 2 + 2 * (|f x| + |(x : ℝ) * deriv f x|) := by
        gcongr
        exact abs_add_le _ _
      _ = 12 * 2 + 2 * (|f x| + |(x : ℝ)| * |deriv f x|) := by
        rw [abs_mul]
      _ ≤ 12 * 2 + 2 * (2 + 1 * 2) := by gcongr
      _ = 32 := by norm_num
      _ ≤ 40 := by norm_num
  · rw [slopeCurve_secondDeriv]
    calc
      |b * deriv (deriv f) x +
          d * (2 * deriv f x + (x : ℝ) * deriv (deriv f) x)|
          ≤ |b * deriv (deriv f) x| +
              |d * (2 * deriv f x + (x : ℝ) * deriv (deriv f) x)| :=
        abs_add_le _ _
      _ = |b| * |deriv (deriv f) x| +
            |d| *
              |2 * deriv f x + (x : ℝ) * deriv (deriv f) x| := by
        rw [abs_mul, abs_mul]
      _ ≤ 12 * (1 / 100) +
            2 * (|2 * deriv f x| +
              |(x : ℝ) * deriv (deriv f) x|) := by
        gcongr
        exact abs_add_le _ _
      _ = 12 * (1 / 100) +
            2 * (2 * |deriv f x| +
              |(x : ℝ)| * |deriv (deriv f) x|) := by
        rw [abs_mul, abs_mul]
        norm_num
      _ ≤ 12 * (1 / 100) + 2 * (2 * 2 + 1 * (1 / 100)) := by
        gcongr
      _ ≤ 40 := by norm_num

/-- Value-only compatibility projection of the absolute two-jet bound. -/
lemma extendedSlopeCurveFamily_value_bound
    (f : SlopeFunction) (h_ns : f.IsNonsingular) (h0 : f 0 = 0) :
    ∀ g ∈ extendedSlopeCurveFamily f, ∀ x : UnitPoint, |g x| ≤ 40 := by
  intro g hg x
  exact (extendedSlopeCurveFamily_jet_bound f h_ns h0 g hg x).1

/-- Doubling property for the extended slope curve family. -/
theorem extendedSlopeCurve_doubling (f : SlopeFunction)
    (h_ns : f.IsNonsingular) (h0 : f 0 = 0) :
    ∀ ⦃g0 : C2Function⦄, g0 ∈ extendedSlopeCurveFamily f → ∀ r : ℝ, 0 < r →
      ∃ centers : Set C2Function,
        centers.Finite ∧ centers ⊆ extendedSlopeCurveFamily f ∧
        (centers.ncard : ℝ) ≤ (216 ^ 12 : ℝ) ∧
        ∀ ⦃g : C2Function⦄, g ∈ extendedSlopeCurveFamily f → c2Distance g g0 ≤ r →
          ∃ h ∈ centers, c2Distance h g ≤ r / 2 := by
  intro g0 hg0 r hr
  rcases extendedSlopeCurveFamily_extract f hg0 with ⟨a0, b0, d0, ha0, hb0, hd0, hg0_eq⟩
  let p0 : Fin 3 → ℝ := fun i =>
    match i with
    | 0 => a0
    | 1 => b0
    | 2 => d0
  have hp0 : p0 ∈ extendedParamBox := by
    simp only [extendedParamBox, Set.mem_setOf_eq]
    exact ⟨ha0, hb0, hd0⟩

  let A : ℝ := 7500 / 33
  let k : ℕ := 12
  have hA_pos : 0 < A := by norm_num [A]
  have h_k : (2 : ℝ) ^ k ≥ 2 * A * 5 := by norm_num [A, k]

  rcases l1_doubling_iterate k p0 (A * r) (by positivity) with ⟨centers_X, h_card_X, h_cover_X⟩

  classical
  let φ : (Fin 3 → ℝ) → C2Function := fun p => slopeCurve f (p 0) (p 1) (p 2)
  let centers_Y : Finset C2Function :=
    Finset.image (fun c : Fin 3 → ℝ => φ (projExtendedBox c)) centers_X
  let centers : Set C2Function := (centers_Y : Set C2Function)

  have h_finite : centers.Finite := Finset.finite_toSet centers_Y
  have h_card : centers.ncard ≤ 216 ^ k := by
    calc centers.ncard
      = centers_Y.card := by simp [centers]
    _ ≤ centers_X.card := Finset.card_image_le
    _ ≤ 216 ^ k := h_card_X

  have h_subset : centers ⊆ extendedSlopeCurveFamily f := by
    intro h hh
    have h_in_Y : h ∈ centers_Y := hh
    have h_mp : ∃ (c : Fin 3 → ℝ), c ∈ centers_X ∧ φ (projExtendedBox c) = h := by
      simpa [centers_Y, Finset.mem_image] using h_in_Y
    rcases h_mp with ⟨c, hc, h_eq⟩
    let pc := projExtendedBox c
    have hpc : pc ∈ extendedParamBox := projExtendedBox_mem c
    exact h_eq.symm ▸ ⟨pc, hpc, rfl⟩

  refine ⟨centers, h_finite, h_subset, ?_, ?_⟩
  · have h1 : (centers.ncard : ℝ) ≤ (216 ^ k : ℝ) := by exact_mod_cast h_card
    simpa [k] using h1
  · intro g hg hdist
    rcases extendedSlopeCurveFamily_extract f hg with ⟨a, b, d, ha, hb, hd, hg_eq⟩
    let p : Fin 3 → ℝ := fun i =>
      match i with
      | 0 => a
      | 1 => b
      | 2 => d
    have hp : p ∈ extendedParamBox := by
      simp only [extendedParamBox, Set.mem_setOf_eq]
      exact ⟨ha, hb, hd⟩
    have h_lower : l1Dist p p0 ≤ A * c2Distance g g0 := by
      rw [hg_eq, hg0_eq]
      exact slopeCurve_lower_lipschitz_general f h_ns h0 p p0 midpoint
    have h_ball : l1Dist p p0 ≤ A * r := by
      have h2 : A * c2Distance g g0 ≤ A * r := mul_le_mul_of_nonneg_left hdist (by positivity)
      exact h_lower.trans h2
    rcases h_cover_X p h_ball with ⟨c, hc, h_close⟩
    let pc := projExtendedBox c
    let h_center : C2Function := φ pc
    have h_center_in : h_center ∈ centers := by
      have h1 : φ (projExtendedBox c) ∈ centers_Y :=
        Finset.mem_image_of_mem (fun c => φ (projExtendedBox c)) hc
      have h2 : h_center = φ (projExtendedBox c) := by rfl
      rw [h2]; exact h1
    have h_proj : l1Dist p pc ≤ l1Dist p c := by
      have hpid : projExtendedBox p = p := projExtendedBox_id p hp
      have h_eq : l1Dist p pc = l1Dist (projExtendedBox p) pc := by rw [hpid]
      rw [h_eq]
      exact projExtendedBox_lipschitz p c
    have h_upper : c2Distance g h_center ≤ 5 * l1Dist p pc := by
      rw [hg_eq]
      exact slopeCurve_upper_lipschitz f h_ns h0 p pc
    have h_final : c2Distance h_center g ≤ r / 2 := by
      have h_sym : c2Distance h_center g = c2Distance g h_center := dist_comm _ _
      rw [h_sym]
      have h1 : c2Distance g h_center ≤ 5 * l1Dist p pc := h_upper
      have h2 : 5 * l1Dist p pc ≤ 5 * l1Dist p c :=
        mul_le_mul_of_nonneg_left h_proj (by norm_num)
      have h3 : 5 * l1Dist p c ≤ 5 * ((A * r) / (2 ^ k : ℝ)) :=
        mul_le_mul_of_nonneg_left h_close (by norm_num)
      have h4 : 5 * ((A * r) / (2 ^ k : ℝ)) = (5 * A / (2 ^ k : ℝ)) * r := by ring
      have h5 : 5 * A / (2 ^ k : ℝ) ≤ 1 / 2 := by
        have h' : (2 : ℝ) ^ k ≥ 2 * A * 5 := h_k
        have h_pos1 : 0 ≤ 5 * A := by positivity
        have h_denom : 0 < (2 : ℝ) ^ k := by positivity
        have h_other : 0 < 2 * A * 5 := by positivity
        have h_div : 5 * A / (2 ^ k : ℝ) ≤ 5 * A / (2 * A * 5) := by
          exact div_le_div_of_nonneg_left h_pos1 h_other h_k
        have h_eq : 5 * A / (2 * A * 5) = 1 / 2 := by
          field_simp [hA_pos.ne'] <;> ring
        rw [h_eq] at h_div
        exact h_div
      have hr' : 0 ≤ r := by linarith [hr]
      have h7 : (5 * A / (2 ^ k : ℝ)) * r ≤ (1 / 2 : ℝ) * r :=
        mul_le_mul_of_nonneg_right h5 hr'
      have h8 : (1 / 2 : ℝ) * r = r / 2 := by ring
      rw [h8] at h7
      have h6 : (5 * A / (2 ^ k : ℝ)) * r ≤ r / 2 := h7
      linarith
    exact ⟨h_center, h_center_in, h_final⟩

/-- Extended cinematic family theorem. -/
theorem extended_cinematic_family (f : SlopeFunction)
    (h_ns : f.IsNonsingular) (h0 : f 0 = 0) :
    ∃ (family : Set C2Function) (K D : ℝ),
      1 ≤ K ∧ 1 ≤ D ∧
      IsCinematicFamily family K D := by
  let K : ℝ := 37500 / 99
  let D : ℝ := (216 ^ 12 : ℝ)
  have hK1 : 1 ≤ K := by norm_num [K]
  have hD1 : 1 ≤ D := by norm_num [D]
  let family := extendedSlopeCurveFamily f
  have h_doubling := extendedSlopeCurve_doubling f h_ns h0

  have h_diameter : ∀ ⦃g1 : C2Function⦄, g1 ∈ family → ∀ ⦃g2 : C2Function⦄, g2 ∈ family →
      c2Distance g1 g2 ≤ K := by
    intro g1 hg1 g2 hg2
    rcases extendedSlopeCurveFamily_extract f hg1 with ⟨a1, b1, d1, ha1, hb1, hd1, hg1_eq⟩
    rcases extendedSlopeCurveFamily_extract f hg2 with ⟨a2, b2, d2, ha2, hb2, hd2, hg2_eq⟩
    set P : ℝ := |a1 - a2| + |b1 - b2| + |d1 - d2| with hP
    have h1 : |a1 - a2| ≤ 24 := by
      calc |a1 - a2| ≤ |a1| + |a2| := abs_sub a1 a2
        _ ≤ 12 + 12 := by gcongr <;> linarith
        _ = 24 := by norm_num
    have h2 : |b1 - b2| ≤ 24 := by
      calc |b1 - b2| ≤ |b1| + |b2| := abs_sub b1 b2
        _ ≤ 12 + 12 := by gcongr <;> linarith
        _ = 24 := by norm_num
    have h3 : |d1 - d2| ≤ 4 := by
      calc |d1 - d2| ≤ |d1| + |d2| := abs_sub d1 d2
        _ ≤ 2 + 2 := by gcongr <;> linarith
        _ = 4 := by norm_num
    have hP_le : P ≤ 52 := by linarith
    rw [hg1_eq, hg2_eq]
    have h_dist : c2Distance (slopeCurve f a1 b1 d1) (slopeCurve f a2 b2 d2) ≤ 5 * P :=
      slopeCurve_c2Distance_le f h_ns h0 a1 b1 d1 a2 b2 d2
    have h_final : c2Distance (slopeCurve f a1 b1 d1) (slopeCurve f a2 b2 d2) ≤ K := by
      calc c2Distance (slopeCurve f a1 b1 d1) (slopeCurve f a2 b2 d2)
        ≤ 5 * P := h_dist
      _ ≤ 5 * 52 := by gcongr
      _ = 260 := by norm_num
      _ ≤ K := by norm_num [K]
    exact h_final

  have h_lower_bound : ∀ ⦃g1 : C2Function⦄, g1 ∈ family → ∀ ⦃g2 : C2Function⦄, g2 ∈ family →
      ∀ x : UnitPoint, K⁻¹ * c2Distance g1 g2 ≤ jetGap g1 g2 x := by
    intro g1 hg1 g2 hg2 x
    rcases extendedSlopeCurveFamily_extract f hg1 with ⟨a1, b1, d1, ha1, hb1, hd1, hg1_eq⟩
    rcases extendedSlopeCurveFamily_extract f hg2 with ⟨a2, b2, d2, ha2, hb2, hd2, hg2_eq⟩
    set P : ℝ := |a1 - a2| + |b1 - b2| + |d1 - d2| with hP
    rw [hg1_eq, hg2_eq]
    have h_lower : (99 / 7500 : ℝ) * P ≤ jetGap (slopeCurve f a1 b1 d1) (slopeCurve f a2 b2 d2) x :=
      slopeCurve_jetGap_ge f h_ns h0 _ _ a1 b1 d1 a2 b2 d2
        (slopeCurve_represents f a1 b1 d1) (slopeCurve_represents f a2 b2 d2) x
    have h_upper : c2Distance (slopeCurve f a1 b1 d1) (slopeCurve f a2 b2 d2) ≤ 5 * P :=
      slopeCurve_c2Distance_le f h_ns h0 a1 b1 d1 a2 b2 d2
    have h_main : (99 / 37500 : ℝ) * c2Distance (slopeCurve f a1 b1 d1) (slopeCurve f a2 b2 d2) ≤
        jetGap (slopeCurve f a1 b1 d1) (slopeCurve f a2 b2 d2) x := by
      calc (99 / 37500 : ℝ) * c2Distance (slopeCurve f a1 b1 d1) (slopeCurve f a2 b2 d2)
          = (99 / 7500 : ℝ) * (c2Distance (slopeCurve f a1 b1 d1) (slopeCurve f a2 b2 d2) / 5) := by ring
        _ ≤ (99 / 7500 : ℝ) * P := by
          have h : c2Distance (slopeCurve f a1 b1 d1) (slopeCurve f a2 b2 d2) / 5 ≤ P := by linarith
          gcongr
        _ ≤ jetGap (slopeCurve f a1 b1 d1) (slopeCurve f a2 b2 d2) x := h_lower
    have hK_inv : K⁻¹ = (99 / 37500 : ℝ) := by
      simp [K] <;> field_simp <;> norm_num
    rw [hK_inv]
    exact h_main

  have h_doubling' : ∀ ⦃f0 : C2Function⦄, f0 ∈ family → ∀ r : ℝ, 0 < r →
      ∃ centers : Set C2Function,
        centers.Finite ∧ centers ⊆ family ∧
        (centers.ncard : ℝ) ≤ D ∧
        ∀ ⦃g : C2Function⦄, g ∈ family → c2Distance f0 g ≤ r →
          ∃ h ∈ centers, c2Distance h g ≤ r / 2 := by
    intro f0 hf0 r hr
    rcases h_doubling hf0 r hr with ⟨centers, h_finite, h_subset, h_card, h_cover⟩
    have h_D : (centers.ncard : ℝ) ≤ D := by
      have h1 : (centers.ncard : ℝ) ≤ (216 ^ 12 : ℝ) := h_card
      have h2 : D = (216 ^ 12 : ℝ) := by simp [D]
      rw [h2]; exact h1
    refine ⟨centers, h_finite, h_subset, h_D, ?_⟩
    intro g hg hdist
    have hdist' : c2Distance g f0 ≤ r := by
      have h_sym : c2Distance f0 g = c2Distance g f0 := dist_comm _ _
      rw [h_sym] at hdist
      exact hdist
    exact h_cover hg hdist'

  have h_cinematic : IsCinematicFamily family K D :=
    ⟨h_diameter, h_doubling', h_lower_bound⟩
  exact ⟨family, K, D, hK1, hD1, h_cinematic⟩

/-- Explicit version with the concrete family and constants. -/
theorem extended_cinematic_family' (f : SlopeFunction)
    (h_ns : f.IsNonsingular) (h0 : f 0 = 0) :
    IsCinematicFamily (extendedSlopeCurveFamily f) (37500 / 99) (216 ^ 12) := by
  let K : ℝ := 37500 / 99
  let D : ℝ := (216 ^ 12 : ℝ)
  let family := extendedSlopeCurveFamily f
  have h_diameter : ∀ ⦃g1 : C2Function⦄, g1 ∈ family → ∀ ⦃g2 : C2Function⦄, g2 ∈ family →
      c2Distance g1 g2 ≤ K := by
    intro g1 hg1 g2 hg2
    rcases extendedSlopeCurveFamily_extract f hg1 with ⟨a1, b1, d1, ha1, hb1, hd1, rfl⟩
    rcases extendedSlopeCurveFamily_extract f hg2 with ⟨a2, b2, d2, ha2, hb2, hd2, rfl⟩
    set P : ℝ := |a1 - a2| + |b1 - b2| + |d1 - d2| with hP
    have h1 : |a1 - a2| ≤ 24 := by
      calc |a1 - a2| ≤ |a1| + |a2| := abs_sub a1 a2
        _ ≤ 12 + 12 := by gcongr <;> linarith
        _ = 24 := by norm_num
    have h2 : |b1 - b2| ≤ 24 := by
      calc |b1 - b2| ≤ |b1| + |b2| := abs_sub b1 b2
        _ ≤ 12 + 12 := by gcongr <;> linarith
        _ = 24 := by norm_num
    have h3 : |d1 - d2| ≤ 4 := by
      calc |d1 - d2| ≤ |d1| + |d2| := abs_sub d1 d2
        _ ≤ 2 + 2 := by gcongr <;> linarith
        _ = 4 := by norm_num
    have hP_le : P ≤ 52 := by linarith
    have h_dist : c2Distance (slopeCurve f a1 b1 d1) (slopeCurve f a2 b2 d2) ≤ 5 * P :=
      slopeCurve_c2Distance_le f h_ns h0 a1 b1 d1 a2 b2 d2
    have h_final : c2Distance (slopeCurve f a1 b1 d1) (slopeCurve f a2 b2 d2) ≤ K := by
      calc c2Distance (slopeCurve f a1 b1 d1) (slopeCurve f a2 b2 d2)
        ≤ 5 * P := h_dist
      _ ≤ 5 * 52 := by gcongr
      _ = 260 := by norm_num
      _ ≤ K := by norm_num [K]
    exact h_final
  have h_doubling' : ∀ ⦃f0 : C2Function⦄, f0 ∈ family → ∀ r : ℝ, 0 < r →
      ∃ centers : Set C2Function,
        centers.Finite ∧ centers ⊆ family ∧
        (centers.ncard : ℝ) ≤ D ∧
        ∀ ⦃g : C2Function⦄, g ∈ family → c2Distance f0 g ≤ r →
          ∃ h ∈ centers, c2Distance h g ≤ r / 2 := by
    intro f0 hf0 r hr
    rcases extendedSlopeCurve_doubling f h_ns h0 hf0 r hr with ⟨centers, h_finite, h_subset, h_card, h_cover⟩
    have h_D : (centers.ncard : ℝ) ≤ D := by
      have h1 : (centers.ncard : ℝ) ≤ (216 ^ 12 : ℝ) := h_card
      have h2 : D = (216 ^ 12 : ℝ) := by simp [D]
      rw [h2]; exact h1
    refine ⟨centers, h_finite, h_subset, h_D, ?_⟩
    intro g hg hdist
    have hdist' : c2Distance g f0 ≤ r := by
      have h_sym : c2Distance f0 g = c2Distance g f0 := dist_comm _ _
      rw [h_sym] at hdist
      exact hdist
    exact h_cover hg hdist'
  have h_lower_bound : ∀ ⦃g1 : C2Function⦄, g1 ∈ family → ∀ ⦃g2 : C2Function⦄, g2 ∈ family →
      ∀ x : UnitPoint, K⁻¹ * c2Distance g1 g2 ≤ jetGap g1 g2 x := by
    intro g1 hg1 g2 hg2 x
    rcases extendedSlopeCurveFamily_extract f hg1 with ⟨a1, b1, d1, ha1, hb1, hd1, rfl⟩
    rcases extendedSlopeCurveFamily_extract f hg2 with ⟨a2, b2, d2, ha2, hb2, hd2, rfl⟩
    set P : ℝ := |a1 - a2| + |b1 - b2| + |d1 - d2| with hP
    have h_lower : (99 / 7500 : ℝ) * P ≤ jetGap (slopeCurve f a1 b1 d1) (slopeCurve f a2 b2 d2) x :=
      slopeCurve_jetGap_ge f h_ns h0 _ _ a1 b1 d1 a2 b2 d2
        (slopeCurve_represents f a1 b1 d1) (slopeCurve_represents f a2 b2 d2) x
    have h_upper : c2Distance (slopeCurve f a1 b1 d1) (slopeCurve f a2 b2 d2) ≤ 5 * P :=
      slopeCurve_c2Distance_le f h_ns h0 a1 b1 d1 a2 b2 d2
    have h_main : (99 / 37500 : ℝ) * c2Distance (slopeCurve f a1 b1 d1) (slopeCurve f a2 b2 d2) ≤
        jetGap (slopeCurve f a1 b1 d1) (slopeCurve f a2 b2 d2) x := by
      calc (99 / 37500 : ℝ) * c2Distance (slopeCurve f a1 b1 d1) (slopeCurve f a2 b2 d2)
          = (99 / 7500 : ℝ) * (c2Distance (slopeCurve f a1 b1 d1) (slopeCurve f a2 b2 d2) / 5) := by ring
        _ ≤ (99 / 7500 : ℝ) * P := by
          have h : c2Distance (slopeCurve f a1 b1 d1) (slopeCurve f a2 b2 d2) / 5 ≤ P := by linarith
          gcongr
        _ ≤ jetGap (slopeCurve f a1 b1 d1) (slopeCurve f a2 b2 d2) x := h_lower
    have hK_inv : K⁻¹ = (99 / 37500 : ℝ) := by
      simp [K] <;> field_simp <;> norm_num
    rw [hK_inv]
    exact h_main
  exact ⟨h_diameter, h_doubling', h_lower_bound⟩

end Kakeya.Assouad
