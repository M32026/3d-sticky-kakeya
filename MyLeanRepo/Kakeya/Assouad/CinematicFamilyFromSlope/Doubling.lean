import MyLeanRepo.Kakeya.Assouad.CinematicFamilyFromSlope.Construction
import MyLeanRepo.Kakeya.Assouad.CinematicFamilyFromSlope.UpperBound
import MyLeanRepo.Kakeya.Assouad.CinematicFamilyFromSlope.LowerBound
import MyLeanRepo.Kakeya.Assouad.CinematicFamilyFromSlope.Uniqueness
import MyLeanRepo.Kakeya.Cinematic.Definitions
import Mathlib.Data.Finset.Pi
import Mathlib.Data.Real.Basic

/-!
# Doubling property of the slope curve cinematic family

Uses the bi-Lipschitz parameterization and explicit doubling of ℝ³ with ℓ¹ metric.
The parameter cube [-1,1]^3 is doubling; projection onto it is 1-Lipschitz,
so the image under the bi-Lipschitz map φ(p) = slopeCurve f (p0) (p1) (p2) is
also doubling.

Whiteprint node: `slope_curve_doubling`.
-/

noncomputable section

open Kakeya.Cinematic Kakeya.Assouad Set Finset

namespace Kakeya.Assouad

/-- ℓ¹ distance on ℝ³. -/
def l1Dist (x y : Fin 3 → ℝ) : ℝ := ∑ i : Fin 3, |x i - y i|

/-- One-dimensional grid center for interval `[c-R, c+R]` with 6 subintervals. -/
noncomputable def grid1d (c R : ℝ) (k : Fin 6) : ℝ :=
  c - R + (2 * (k : ℝ) + 1) * R / 6

/-- For any `y ∈ [c-R, c+R]`, there is a grid center within `R/6`. -/
lemma grid1d_cover (c R : ℝ) (hR : 0 < R) (y : ℝ) (h : |y - c| ≤ R) :
    ∃ (k : Fin 6), |y - grid1d c R k| ≤ R / 6 := by
  have h1 : c - R ≤ y := by linarith [abs_le.mp h]
  have h2 : y ≤ c + R := by linarith [abs_le.mp h]
  set z : ℝ := y - (c - R) with hz
  have hz1 : 0 ≤ z := by linarith
  have hz2 : z ≤ 2 * R := by linarith
  set t : ℝ := 3 * z / R with ht
  have ht1 : 0 ≤ t := by positivity
  have ht2 : t ≤ 6 := by
    rw [ht]
    calc 3 * z / R ≤ 3 * (2 * R) / R := by gcongr
      _ = 6 := by field_simp [hR.ne'] <;> ring
  let k0 : Int := Int.floor t
  have h_k01 : (k0 : ℝ) ≤ t := Int.floor_le t
  have h_k02 : t < (k0 : ℝ) + 1 := Int.lt_floor_add_one t
  have h_k03 : 0 ≤ k0 := Int.floor_nonneg.mpr ht1
  have h_k04 : k0 ≤ 6 := by
    have h : (k0 : ℝ) ≤ t := h_k01
    have h' : t ≤ 6 := ht2
    exact_mod_cast (show (k0 : ℝ) ≤ 6 from by linarith)
  by_cases h_case : k0 = 6
  · have h6 : (k0 : ℝ) = 6 := by exact_mod_cast h_case
    have ht6 : t = 6 := by linarith
    have hz6 : z = 2 * R := by
      have h_eq : 3 * z / R = 6 := by
        rw [ht] at ht6; exact ht6
      field_simp [hR.ne'] at h_eq
      linarith
    refine ⟨(5 : Fin 6), ?_⟩
    have h_y : y = c + R := by linarith
    have h_goal : y - grid1d c R (5 : Fin 6) = R / 6 := by
      rw [h_y]
      simp [grid1d] <;> ring_nf <;> field_simp <;> ring
    rw [h_goal]
    rw [abs_of_nonneg] <;> linarith
  · have h_k05 : k0 < 6 := by omega
    have h_nat : (k0.toNat : ℤ) = k0 := Int.toNat_of_nonneg h_k03
    let k : Fin 6 := ⟨k0.toNat, by omega⟩
    have hk_val : (k : ℝ) = (k0 : ℝ) := by
      have h1 : (k : ℕ) = k0.toNat := rfl
      have h2 : ((k : ℕ) : ℝ) = (k0.toNat : ℝ) := by rw [h1]
      have h3 : (k0.toNat : ℝ) = (k0 : ℝ) := by exact_mod_cast h_nat
      linarith
    refine ⟨k, ?_⟩
    have h9 : (k : ℝ) * (R / 3) ≤ z := by
      rw [hk_val]
      have h10 : (k0 : ℝ) ≤ t := h_k01
      rw [ht] at h10
      have h : (k0 : ℝ) * (R / 3) ≤ (3 * z / R) * (R / 3) := by gcongr
      have h' : (3 * z / R) * (R / 3) = z := by
        field_simp [hR.ne'] <;> ring
      rw [h'] at h
      exact h
    have h10 : z < ((k : ℝ) + 1) * (R / 3) := by
      rw [hk_val]
      have h11 : t < (k0 : ℝ) + 1 := h_k02
      rw [ht] at h11
      have h : z = (3 * z / R) * (R / 3) := by field_simp [hR.ne'] <;> ring
      rw [h]
      gcongr
    have h12 : |z - ((2 * (k : ℝ) + 1) * R / 6)| ≤ R / 6 := by
      have h13 : (k : ℝ) * (R / 3) ≤ z := h9
      have h14 : z < ((k : ℝ) + 1) * (R / 3) := h10
      have h15 : z - ((2 * (k : ℝ) + 1) * R / 6) ≤ R / 6 := by linarith
      have h16 : -(R / 6) ≤ z - ((2 * (k : ℝ) + 1) * R / 6) := by linarith
      exact abs_le.mpr ⟨h16, h15⟩
    have h17 : y - grid1d c R k = z - ((2 * (k : ℝ) + 1) * R / 6) := by
      have h : y = z + (c - R) := by linarith
      rw [h]
      simp [grid1d] <;> ring
    rw [h17]
    exact h12

/-- Explicit doubling of ℝ³ with ℓ¹ metric. -/
lemma real3_l1_doubling (center : Fin 3 → ℝ) (R : ℝ) (hR : 0 < R) :
    ∃ (centers : Finset (Fin 3 → ℝ)),
      centers.card ≤ 216 ∧
      ∀ (x : Fin 3 → ℝ), l1Dist x center ≤ R →
        ∃ c ∈ centers, l1Dist x c ≤ R / 2 := by
  let f : (Fin 3 → Fin 6) → (Fin 3 → ℝ) :=
    fun k i => grid1d (center i) R (k i)
  let centers : Finset (Fin 3 → ℝ) := Finset.image f Finset.univ
  have h_card : centers.card ≤ 216 := by
    calc centers.card
      ≤ (Finset.univ : Finset (Fin 3 → Fin 6)).card := Finset.card_image_le
    _ = 6 ^ 3 := by simp [Fintype.card_pi]
    _ = 216 := by norm_num
  refine ⟨centers, h_card, ?_⟩
  intro x hx
  have h1 : ∀ i : Fin 3, |x i - center i| ≤ R := by
    intro i
    have h2 : |x i - center i| ≤ ∑ j : Fin 3, |x j - center j| := by
      apply Finset.single_le_sum (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    linarith [show l1Dist x center = ∑ j : Fin 3, |x j - center j| from rfl]
  choose k hk using fun i => grid1d_cover (center i) R hR (x i) (h1 i)
  let k0 : Fin 3 → Fin 6 := fun i => k i
  let c : Fin 3 → ℝ := f k0
  have hc : c ∈ centers := by
    exact Finset.mem_image.mpr ⟨k0, Finset.mem_univ _, rfl⟩
  have h3 : ∀ i : Fin 3, |x i - c i| ≤ R / 6 := by
    intro i
    exact hk i
  have h4 : l1Dist x c ≤ R / 2 := by
    dsimp only [l1Dist]
    calc ∑ i : Fin 3, |x i - c i|
      ≤ ∑ i : Fin 3, R / 6 := by apply Finset.sum_le_sum; intro i _; exact h3 i
    _ = R / 2 := by simp <;> ring
  exact ⟨c, hc, h4⟩

/-- Iterated doubling for ℓ¹ metric on ℝ³. -/
lemma l1_doubling_iterate (k : ℕ) (center : Fin 3 → ℝ) (R : ℝ) (hR : 0 < R) :
    ∃ (centers : Finset (Fin 3 → ℝ)),
      centers.card ≤ 216 ^ k ∧
      ∀ (x : Fin 3 → ℝ), l1Dist x center ≤ R →
        ∃ c ∈ centers, l1Dist x c ≤ R / (2 ^ k : ℝ) := by
  induction k with
  | zero =>
    refine ⟨{center}, by simp, ?_⟩
    intro x hx
    exact ⟨center, by simp, by simpa using hx⟩
  | succ k ih =>
    rcases ih with ⟨centers_k, h_card_k, h_cover_k⟩
    have h_pos : 0 < R / (2 ^ k : ℝ) := by positivity
    have h_step : ∀ (c : Fin 3 → ℝ), ∃ (centers_c : Finset (Fin 3 → ℝ)),
        centers_c.card ≤ 216 ∧
        ∀ y, l1Dist y c ≤ R / (2 ^ k : ℝ) →
          ∃ d ∈ centers_c, l1Dist y d ≤ R / (2 ^ (k + 1) : ℝ) := by
      intro c
      rcases real3_l1_doubling c (R / (2 ^ k : ℝ)) h_pos with ⟨centers_c, h_card_c, h_cover_c⟩
      refine ⟨centers_c, h_card_c, ?_⟩
      intro y hy
      rcases h_cover_c y hy with ⟨d, hd, hdist⟩
      have h_eq : (R / (2 ^ k : ℝ)) / 2 = R / (2 ^ (k + 1) : ℝ) := by
        simp [pow_succ] <;> ring
      exact ⟨d, hd, by rwa [h_eq] at hdist⟩
    choose centers_c h_card_c h_cover_c using h_step
    let centers : Finset (Fin 3 → ℝ) := centers_k.biUnion (fun c => centers_c c)
    have h_card : centers.card ≤ 216 ^ (k + 1) := by
      calc centers.card
        ≤ ∑ c ∈ centers_k, (centers_c c).card := Finset.card_biUnion_le
      _ ≤ ∑ c ∈ centers_k, 216 := by gcongr <;> exact h_card_c c
      _ = centers_k.card * 216 := by simp [Finset.sum_const]
      _ ≤ 216 ^ k * 216 := by gcongr
      _ = 216 ^ (k + 1) := by ring
    refine ⟨centers, h_card, ?_⟩
    intro x hx
    rcases h_cover_k x hx with ⟨c, hc, hdist_c⟩
    rcases h_cover_c c x hdist_c with ⟨d, hd, hdist_d⟩
    have h_in : d ∈ centers := by
      simp only [centers, Finset.mem_biUnion]
      exact ⟨c, hc, hd⟩
    exact ⟨d, h_in, hdist_d⟩

/-- Projection onto [-1,1]^3. -/
def projParamCube (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => max (-1) (min 1 (x i))

lemma projParamCube_mem (x : Fin 3 → ℝ) :
    ∀ i, (projParamCube x) i ∈ Set.Icc (-1 : ℝ) 1 := by
  intro i
  simp only [projParamCube]
  have h1 : -1 ≤ max (-1) (min 1 (x i)) := by apply le_max_left
  have h2 : max (-1) (min 1 (x i)) ≤ 1 := by
    have h21 : min 1 (x i) ≤ 1 := by apply min_le_left
    have h22 : max (-1) (min 1 (x i)) ≤ 1 := by
      exact max_le (by norm_num) h21
    exact h22
  exact ⟨h1, h2⟩

lemma projParamCube_id (x : Fin 3 → ℝ)
    (hx : ∀ i, x i ∈ Set.Icc (-1 : ℝ) 1) :
    projParamCube x = x := by
  funext i
  have hxi1 : -1 ≤ x i := (hx i).1
  have hxi2 : x i ≤ 1 := (hx i).2
  simp [projParamCube, hxi1, hxi2] <;> linarith

lemma abs_min_sub_le {x y a : ℝ} : |min a x - min a y| ≤ |x - y| := by
  have h : ∀ (u v : ℝ), min a u - min a v ≤ |u - v| := by
    intro u v
    by_cases h2 : u ≤ v
    · have h3 : min a u ≤ min a v := by gcongr
      have h4 : min a v - min a u ≤ v - u := by
        simp [min_def, h2] <;> split_ifs <;> linarith
      have h5 : |u - v| = v - u := by rw [abs_of_nonpos] <;> linarith
      linarith
    · have h2' : v ≤ u := by linarith
      have h4 : min a u - min a v ≤ u - v := by
        simp [min_def, h2'] <;> split_ifs <;> linarith
      have h5 : |u - v| = u - v := by rw [abs_of_nonneg] <;> linarith
      linarith
  have h1 : min a x - min a y ≤ |x - y| := h x y
  have h2 : min a y - min a x ≤ |y - x| := h y x
  have h3 : |y - x| = |x - y| := by rw [abs_sub_comm]
  rw [h3] at h2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma abs_max_sub_le {x y a : ℝ} : |max a x - max a y| ≤ |x - y| := by
  have h : ∀ (u v : ℝ), max a u - max a v ≤ |u - v| := by
    intro u v
    by_cases h2 : u ≤ v
    · have h3 : max a u ≤ max a v := by gcongr
      have h4 : max a v - max a u ≤ v - u := by
        simp [max_def, h2] <;> split_ifs <;> linarith
      have h5 : |u - v| = v - u := by rw [abs_of_nonpos] <;> linarith
      linarith
    · have h2' : v ≤ u := by linarith
      have h4 : max a u - max a v ≤ u - v := by
        simp [max_def, h2'] <;> split_ifs <;> linarith
      have h5 : |u - v| = u - v := by rw [abs_of_nonneg] <;> linarith
      linarith
  have h1 : max a x - max a y ≤ |x - y| := h x y
  have h2 : max a y - max a x ≤ |y - x| := h y x
  have h3 : |y - x| = |x - y| := by rw [abs_sub_comm]
  rw [h3] at h2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma abs_proj_sub_le {x y : ℝ} :
    |max (-1) (min 1 x) - max (-1) (min 1 y)| ≤ |x - y| := by
  have h1 : |min 1 x - min 1 y| ≤ |x - y| := abs_min_sub_le
  have h2 : |max (-1) (min 1 x) - max (-1) (min 1 y)| ≤ |min 1 x - min 1 y| :=
    abs_max_sub_le (x := min 1 x) (y := min 1 y) (a := -1)
  exact le_trans h2 h1

lemma projParamCube_lipschitz (x y : Fin 3 → ℝ) :
    l1Dist (projParamCube x) (projParamCube y) ≤ l1Dist x y := by
  dsimp only [l1Dist]
  apply Finset.sum_le_sum
  intro i _
  exact abs_proj_sub_le

/-- Upper Lipschitz bound for slope curve parameterization. -/
lemma slopeCurve_upper_lipschitz (f : SlopeFunction) (h_ns : f.IsNonsingular)
    (h0 : f 0 = 0) (p q : Fin 3 → ℝ) :
    c2Distance (slopeCurve f (p 0) (p 1) (p 2))
        (slopeCurve f (q 0) (q 1) (q 2)) ≤
      5 * l1Dist p q := by
  have h : c2Distance (slopeCurve f (p 0) (p 1) (p 2))
        (slopeCurve f (q 0) (q 1) (q 2)) ≤
      5 * (|p 0 - q 0| + |p 1 - q 1| + |p 2 - q 2|) :=
    slopeCurve_c2Distance_le f h_ns h0 (p 0) (p 1) (p 2) (q 0) (q 1) (q 2)
  have h_eq : l1Dist p q = |p 0 - q 0| + |p 1 - q 1| + |p 2 - q 2| := by
    simp [l1Dist, Fin.sum_univ_succ]
    <;> ring
  rw [h_eq]
  exact h

/-- Lower Lipschitz bound for slope curve parameterization on paramCube. -/
lemma slopeCurve_lower_lipschitz (f : SlopeFunction) (h_ns : f.IsNonsingular)
    (h0 : f 0 = 0) (p q : Fin 3 → ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (-1 : ℝ) 1)
    (hq : ∀ i, q i ∈ Set.Icc (-1 : ℝ) 1)
    (x : UnitPoint) :
    l1Dist p q ≤ (7500 / 33 : ℝ) *
      c2Distance (slopeCurve f (p 0) (p 1) (p 2))
          (slopeCurve f (q 0) (q 1) (q 2)) := by
  let g1 := slopeCurve f (p 0) (p 1) (p 2)
  let g2 := slopeCurve f (q 0) (q 1) (q 2)
  have hrep1 : RepresentsSlopeCurve g1 f (p 0) (p 1) (p 2) :=
    slopeCurve_represents f (p 0) (p 1) (p 2)
  have hrep2 : RepresentsSlopeCurve g2 f (q 0) (q 1) (q 2) :=
    slopeCurve_represents f (q 0) (q 1) (q 2)
  have h_l1_eq : l1Dist p q = |p 0 - q 0| + |p 1 - q 1| + |p 2 - q 2| := by
    simp [l1Dist, Fin.sum_univ_succ] <;> ring
  have h_lower : (99 / 7500 : ℝ) * (|p 0 - q 0| + |p 1 - q 1| + |p 2 - q 2|) ≤ jetGap g1 g2 x :=
    slopeCurve_jetGap_ge f h_ns h0 g1 g2 (p 0) (p 1) (p 2) (q 0) (q 1) (q 2) hrep1 hrep2 x
  have h_lower' : (99 / 7500 : ℝ) * l1Dist p q ≤ jetGap g1 g2 x := by
    rw [h_l1_eq]
    exact h_lower
  have h_jet : jetGap g1 g2 x ≤ 3 * c2Distance g1 g2 :=
    jetGap_le_three_mul_c2Distance g1 g2 x
  have h : (99 / 7500 : ℝ) * l1Dist p q ≤ 3 * c2Distance g1 g2 := by linarith
  have h99 : (0 : ℝ) < 99 / 7500 := by norm_num
  have h_mul : (99 / 7500 : ℝ) * l1Dist p q ≤ 3 * c2Distance g1 g2 := h
  have h_div : l1Dist p q ≤ (3 * c2Distance g1 g2) / (99 / 7500 : ℝ) := by
    have hpos : 0 < (99 / 7500 : ℝ) := h99
    calc l1Dist p q
      = ((99 / 7500 : ℝ) * l1Dist p q) / (99 / 7500 : ℝ) := by field_simp [hpos.ne'] <;> ring
      _ ≤ (3 * c2Distance g1 g2) / (99 / 7500 : ℝ) := by gcongr
  have h_eq : (3 * c2Distance g1 g2) / (99 / 7500 : ℝ) = (7500 / 33 : ℝ) * c2Distance g1 g2 := by
    have h99' : (99 / 7500 : ℝ) ≠ 0 := h99.ne'
    field_simp [h99'] <;> ring_nf <;> norm_num
  have h_final : l1Dist p q ≤ (7500 / 33 : ℝ) * c2Distance g1 g2 := by
    calc l1Dist p q
      ≤ (3 * c2Distance g1 g2) / (99 / 7500 : ℝ) := h_div
    _ = (7500 / 33 : ℝ) * c2Distance g1 g2 := h_eq
  exact h_final

/-- If two C2Functions represent the same parameter triple, they are equal. -/
lemma represents_eq {f : SlopeFunction} {a b d : ℝ} {g1 g2 : C2Function}
    (h1 : RepresentsSlopeCurve g1 f a b d)
    (h2 : RepresentsSlopeCurve g2 f a b d) : g1 = g2 := by
  have h_val : g1.value = g2.value := by
    ext x
    exact (h1 x).1.trans (h2 x).1.symm
  have h_fd : g1.firstDeriv = g2.firstDeriv := by
    ext x
    exact (h1 x).2.1.trans (h2 x).2.1.symm
  have h_sd : g1.secondDeriv = g2.secondDeriv := by
    ext x
    exact (h1 x).2.2.trans (h2 x).2.2.symm
  have h_jet : g1.toJet = g2.toJet := by
    simp [C2Function.toJet, h_val, h_fd, h_sd]
  exact C2Function.toJet_injective h_jet

/-- Doubling property of the slope curve family with constant 216^12. -/
theorem slopeCurve_doubling_core (f : SlopeFunction)
    (h_ns : f.IsNonsingular) (h0 : f 0 = 0)
    (family : Set C2Function) (h_family : IsSlopeCurveFamily family f) :
    ∀ ⦃g0 : C2Function⦄, g0 ∈ family → ∀ r : ℝ, 0 < r →
      ∃ centers : Set C2Function,
        centers.Finite ∧ centers ⊆ family ∧
        (centers.ncard : ℝ) ≤ (216 ^ 12 : ℝ) ∧
        ∀ ⦃g : C2Function⦄, g ∈ family → c2Distance g g0 ≤ r →
          ∃ h ∈ centers, c2Distance h g ≤ r / 2 := by
  intro g0 hg0 r hr
  -- Extract p0 from g0
  rcases (h_family g0).mp hg0 with ⟨a0, ha0, b0, hb0, d0, hd0, hrep0⟩
  let p0 : Fin 3 → ℝ := fun i =>
    match i with
    | 0 => a0
    | 1 => b0
    | 2 => d0
  have hp0 : ∀ i, p0 i ∈ Set.Icc (-1 : ℝ) 1 := by
    intro i
    fin_cases i <;> simp [p0, ha0, hb0, hd0] <;> tauto
  have hg0_eq : g0 = slopeCurve f a0 b0 d0 :=
    represents_eq hrep0 (slopeCurve_represents f a0 b0 d0)

  let A : ℝ := 7500 / 33
  let k : ℕ := 12
  have hA_pos : 0 < A := by norm_num [A]
  have h_k : (2 : ℝ) ^ k ≥ 2 * A * 5 := by norm_num [A, k]

  -- Cover ℓ¹ ball B(p0, A*r) with 216^12 centers
  rcases l1_doubling_iterate k p0 (A * r) (by positivity) with ⟨centers_X, h_card_X, h_cover_X⟩

  -- Project centers and apply φ
  classical
  let φ : (Fin 3 → ℝ) → C2Function := fun p => slopeCurve f (p 0) (p 1) (p 2)
  let centers_Y : Finset C2Function :=
    Finset.image (fun c : Fin 3 → ℝ => φ (projParamCube c)) centers_X
  let centers : Set C2Function := (centers_Y : Set C2Function)

  have h_finite : centers.Finite := by exact Finset.finite_toSet centers_Y
  have h_card : centers.ncard ≤ 216 ^ k := by
    calc centers.ncard
      = centers_Y.card := by simp [centers]
      _ ≤ centers_X.card := by
        exact Finset.card_image_le (f := fun c : Fin 3 → ℝ => φ (projParamCube c))
      _ ≤ 216 ^ k := h_card_X

  have h_subset : centers ⊆ family := by
    intro h hh
    have h_in_Y : h ∈ centers_Y := hh
    have h_mp : ∃ (c : Fin 3 → ℝ), c ∈ centers_X ∧ φ (projParamCube c) = h := by
      simpa [centers_Y, Finset.mem_image] using h_in_Y
    rcases h_mp with ⟨c, hc, h_eq⟩
    let pc := projParamCube c
    have hpc : ∀ i, pc i ∈ Set.Icc (-1 : ℝ) 1 := projParamCube_mem c
    have hrep : RepresentsSlopeCurve (φ pc) f (pc 0) (pc 1) (pc 2) :=
      slopeCurve_represents f (pc 0) (pc 1) (pc 2)
    have h_goal : φ pc ∈ family := (h_family (φ pc)).mpr
      ⟨pc 0, hpc 0, pc 1, hpc 1, pc 2, hpc 2, hrep⟩
    exact h_eq.symm ▸ h_goal

  refine ⟨centers, h_finite, h_subset, ?_, ?_⟩
  · -- ncard bound
    have h1 : (centers.ncard : ℝ) ≤ (216 ^ k : ℝ) := by exact_mod_cast h_card
    simpa [k] using h1
  · -- coverage
    intro g hg hdist
    -- Extract p from g
    rcases (h_family g).mp hg with ⟨a, ha, b, hb, d, hd, hrep⟩
    let p : Fin 3 → ℝ := fun i =>
      match i with
      | 0 => a
      | 1 => b
      | 2 => d
    have hp : ∀ i, p i ∈ Set.Icc (-1 : ℝ) 1 := by
      intro i
      fin_cases i <;> simp [p, ha, hb, hd] <;> tauto
    have hg_eq : g = slopeCurve f a b d :=
      represents_eq hrep (slopeCurve_represents f a b d)

    -- Lower Lipschitz: l1Dist p p0 ≤ A * c2Distance g g0
    have h_l1 : l1Dist p p0 ≤ A * r := by
      let x0 : UnitPoint := ⟨0, by
        simp [Kakeya.Cinematic.unitInterval]
        <;> norm_num⟩
      have h_lip_raw : l1Dist p p0 ≤ A * c2Distance
          (slopeCurve f (p 0) (p 1) (p 2))
          (slopeCurve f (p0 0) (p0 1) (p0 2)) :=
        slopeCurve_lower_lipschitz f h_ns h0 p p0 hp hp0 x0
      have h_lip : l1Dist p p0 ≤ A * c2Distance g g0 := by
        rw [hg_eq, hg0_eq]
        exact h_lip_raw
      calc l1Dist p p0
        ≤ A * c2Distance g g0 := h_lip
        _ ≤ A * r := by gcongr

    -- Find center c ∈ centers_X with l1Dist p c ≤ A * r / 2^k
    rcases h_cover_X p h_l1 with ⟨c, hc, hdist_c⟩
    let pc := projParamCube c
    let h_center : C2Function := φ pc
    have h_center_in : h_center ∈ centers := by
      have h1 : φ (projParamCube c) ∈ centers_Y := by
        exact Finset.mem_image_of_mem (fun c : Fin 3 → ℝ => φ (projParamCube c)) hc
      have h2 : h_center = φ (projParamCube c) := by rfl
      rw [h2]
      exact h1

    -- Projection is 1-Lipschitz
    have h_proj : l1Dist p pc ≤ l1Dist p c := by
      have hpid : projParamCube p = p := projParamCube_id p hp
      have h_eq : l1Dist p pc = l1Dist (projParamCube p) pc := by rw [hpid]
      rw [h_eq]
      exact projParamCube_lipschitz p c

    -- Upper Lipschitz
    have h_upper : c2Distance g h_center ≤ 5 * l1Dist p pc := by
      rw [hg_eq]
      exact slopeCurve_upper_lipschitz f h_ns h0 p pc

    have h_final : c2Distance g h_center ≤ r / 2 := by
      calc c2Distance g h_center
        ≤ 5 * l1Dist p pc := h_upper
        _ ≤ 5 * l1Dist p c := by gcongr
        _ ≤ 5 * (A * r / (2 ^ k : ℝ)) := by gcongr
        _ = (5 * A * r) / (2 ^ k : ℝ) := by ring
        _ ≤ r / 2 := by
          have h_pos2 : 0 < (2 ^ k : ℝ) := by positivity
          have h : 5 * A / (2 ^ k : ℝ) ≤ 1 / 2 := by
            have h' : (2 : ℝ) ^ k ≥ 2 * A * 5 := h_k
            have h'' : 5 * A ≤ (2 ^ k : ℝ) / 2 := by linarith
            calc 5 * A / (2 ^ k : ℝ)
              ≤ ((2 ^ k : ℝ) / 2) / (2 ^ k : ℝ) := by gcongr
              _ = 1 / 2 := by field_simp [h_pos2.ne'] <;> ring
          calc (5 * A * r) / (2 ^ k : ℝ)
            = (5 * A / (2 ^ k : ℝ)) * r := by ring
            _ ≤ (1 / 2 : ℝ) * r := by gcongr
            _ = r / 2 := by ring

    have h_comm : c2Distance h_center g = c2Distance g h_center := by
      simp [c2Distance, dist_comm]
    exact ⟨h_center, h_center_in, by rw [h_comm]; exact h_final⟩

end Kakeya.Assouad
