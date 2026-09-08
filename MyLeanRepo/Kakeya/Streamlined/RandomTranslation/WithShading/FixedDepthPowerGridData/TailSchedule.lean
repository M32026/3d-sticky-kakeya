import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.ScaleInterpolation
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.WithShading.FixedDepthPowerGridData

/-!
# Fixed-depth power-grid tail schedule

For `s_k = δ^(k/N)`, use the positive radius
`(s_k - s_{k+1}) / N` at level `k`.  Every suffix of this schedule fits
inside its adjacent grid gap, and the total radius is at most one.
-/

noncomputable section

open BigOperators Finset
open Kakeya.Streamlined
open Kakeya.Streamlined.RandomTranslation

namespace Kakeya.Streamlined.RandomTranslation.WithShading
namespace FixedDepthPowerGridTail

/-- The real grid point `s_k = δ^(k/N)`. -/
def realScale (δ : ℝ) (N : ℕ) (k : ℕ) : ℝ :=
  Real.rpow δ ((k : ℝ) / (N : ℝ))

/-- The common ratio `r = δ^(1/N)`. -/
def r (δ : ℝ) (N : ℕ) : ℝ :=
  Real.rpow δ (1 / (N : ℝ))

lemma r_pos {δ : ℝ} {N : ℕ} (hδ_pos : 0 < δ) (_hN_pos : 0 < N) :
    0 < r δ N :=
  Real.rpow_pos_of_pos hδ_pos _

lemma r_lt_one {δ : ℝ} {N : ℕ} (hδ_pos : 0 < δ)
    (hδ_lt_one : δ < 1) (hN_pos : 0 < N) :
    r δ N < 1 := by
  have hexponent : (0 : ℝ) < 1 / (N : ℝ) := by
    positivity
  have h :
      Real.rpow δ (1 / (N : ℝ)) < Real.rpow δ 0 :=
    Real.rpow_lt_rpow_of_exponent_gt
      hδ_pos hδ_lt_one hexponent
  simpa [r] using h

/-- The real scale grid is the ordinary power sequence of `r`. -/
lemma realScale_eq_rpow {δ : ℝ} {N : ℕ}
    (hδ_pos : 0 < δ) (hN_pos : 0 < N) (k : ℕ) :
    realScale δ N k = (r δ N) ^ k := by
  induction k with
  | zero =>
      simp [realScale, r]
  | succ k ih =>
      have hN_ne : (N : ℝ) ≠ 0 := by
        exact_mod_cast hN_pos.ne'
      have h_add :
          (((k + 1 : ℕ) : ℝ) / (N : ℝ)) =
            ((k : ℝ) / (N : ℝ)) + 1 / (N : ℝ) := by
        field_simp [hN_ne] <;> norm_cast <;> ring
      have h_main :
          realScale δ N (k + 1) =
            realScale δ N k * r δ N := by
        simp only [realScale, r]
        rw [h_add]
        exact Real.rpow_add hδ_pos _ _
      rw [h_main, ih]
      ring

/-- The adjacent scale gap. -/
def gap (δ : ℝ) (N : ℕ) (k : ℕ) : ℝ :=
  realScale δ N k - realScale δ N (k + 1)

lemma gap_pos {δ : ℝ} {N : ℕ} (hδ_pos : 0 < δ)
    (hδ_lt_one : δ < 1) (hN_pos : 0 < N)
    (k : ℕ) (_hk : k < N) :
    0 < gap δ N k := by
  set rr := r δ N
  have hr_pos : 0 < rr := r_pos hδ_pos hN_pos
  have hr_lt_one : rr < 1 :=
    r_lt_one hδ_pos hδ_lt_one hN_pos
  have hscale :
      realScale δ N (k + 1) < realScale δ N k := by
    rw [realScale_eq_rpow hδ_pos hN_pos (k + 1),
      realScale_eq_rpow hδ_pos hN_pos k]
    have hpow_pos : 0 < rr ^ k := by
      positivity
    rw [pow_succ]
    nlinarith
  exact sub_pos.mpr hscale

/-- One `N`-th of the adjacent scale gap. -/
def radius (δ : ℝ) (N : ℕ) (k : Fin N) : ℝ :=
  gap δ N k.val / (N : ℝ)

lemma radius_pos {δ : ℝ} {N : ℕ} (hδ_pos : 0 < δ)
    (hδ_lt_one : δ < 1) (hN_pos : 0 < N) (k : Fin N) :
    0 < radius δ N k := by
  have hgap :
      0 < gap δ N k.val :=
    gap_pos hδ_pos hδ_lt_one hN_pos k.val k.is_lt
  have hN : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast hN_pos
  exact div_pos hgap hN

/-- Bernoulli's geometric-series bound on `[0, 1]`. -/
lemma one_sub_pow_le (r : ℝ) (hr_pos : 0 < r)
    (hr_lt_one : r < 1) (m : ℕ) :
    1 - r ^ m ≤ (m : ℝ) * (1 - r) := by
  induction m with
  | zero =>
      norm_num
  | succ m ih =>
      have hsplit :
          1 - r ^ (m + 1) =
            (1 - r ^ m) + r ^ m * (1 - r) := by
        ring
      have hr_nonneg : 0 ≤ r := hr_pos.le
      have hr_le_one : r ≤ 1 := hr_lt_one.le
      have hpow : r ^ m ≤ 1 :=
        pow_le_one₀ hr_nonneg hr_le_one
      have hmul :
          r ^ m * (1 - r) ≤ 1 * (1 - r) := by
        gcongr
      rw [hsplit]
      calc
        (1 - r ^ m) + r ^ m * (1 - r)
            ≤ (m : ℝ) * (1 - r) + 1 * (1 - r) := by
              gcongr
        _ = ((m + 1 : ℕ) : ℝ) * (1 - r) := by
              simp [Nat.cast_add]
              ring

/-- The finite sum of adjacent gaps telescopes. -/
lemma sum_gap {δ : ℝ} {N : ℕ} (k : ℕ) (hk : k ≤ N) :
    ∑ j ∈ Finset.Ico k N, gap δ N j =
      realScale δ N k - realScale δ N N := by
  have h_telescoping :
      ∀ m : ℕ, k ≤ m → m ≤ N →
        ∑ j ∈ Finset.Ico k m, gap δ N j =
          realScale δ N k - realScale δ N m := by
    intro m hkm hmn
    induction m with
    | zero =>
        have hk0 : k = 0 := by
          omega
        simp [hk0, gap, realScale]
    | succ m ih =>
        by_cases h : k ≤ m
        · rw [Finset.sum_Ico_succ_top h]
          rw [ih h (by omega)]
          simp [gap] <;> ring
        · have hkm' : k = m + 1 := by
            omega
          simp [hkm', Finset.sum_eq_zero]
  exact h_telescoping N hk le_rfl

/-- Rewrite a filtered sum over `Fin N` as an interval sum over naturals. -/
lemma sum_filter_eq_sum_Ico {N : ℕ} (hN_pos : 0 < N)
    (k : Fin N) (f : ℕ → ℝ) :
    ∑ j ∈ Finset.univ.filter (fun j : Fin N => k.val ≤ j.val),
        f j.val =
      ∑ i ∈ Finset.Ico k.val N, f i := by
  let S :=
    Finset.univ.filter (fun j : Fin N => k.val ≤ j.val)
  have h_image :
      S.image (fun j : Fin N => j.val) =
        Finset.Ico k.val N := by
    ext x
    simp only [S, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, Finset.mem_Ico, true_and]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨hj, j.is_lt⟩
    · rintro ⟨hx1, hx2⟩
      exact ⟨⟨x, hx2⟩, hx1, rfl⟩
  have h_inj :
      Set.InjOn (fun j : Fin N => j.val) S := by
    intro j1 _ j2 _ h
    exact Fin.ext h
  calc
    ∑ j ∈ S, f j.val =
        ∑ x ∈ S.image (fun j => j.val), f x := by
          rw [Finset.sum_image h_inj]
    _ = ∑ i ∈ Finset.Ico k.val N, f i := by
          rw [h_image]

/-- Exact suffix sum of the radius schedule. -/
lemma sum_radius_eq {δ : ℝ} {N : ℕ} (hδ_pos : 0 < δ)
    (hN_pos : 0 < N) (k : Fin N) :
    ∑ j ∈ Finset.univ.filter (fun j : Fin N => k.val ≤ j.val),
        radius δ N j =
      (realScale δ N k.val - realScale δ N N) / (N : ℝ) := by
  rw [show
      (∑ j ∈ Finset.univ.filter
          (fun j : Fin N => k.val ≤ j.val), radius δ N j) =
        ∑ j ∈ Finset.univ.filter
          (fun j : Fin N => k.val ≤ j.val),
            gap δ N j.val / (N : ℝ) by rfl]
  rw [sum_filter_eq_sum_Ico hN_pos k
    (fun i => gap δ N i / (N : ℝ))]
  have h_sum :
      ∑ i ∈ Finset.Ico k.val N, gap δ N i / (N : ℝ) =
        (∑ i ∈ Finset.Ico k.val N, gap δ N i) / (N : ℝ) := by
    rw [Finset.sum_div]
  rw [h_sum, sum_gap k.val (by omega)]

/-- Every suffix fits inside the adjacent gap at its first level. -/
lemma tail_suffix_bound {δ : ℝ} {N : ℕ} (hδ_pos : 0 < δ)
    (hδ_lt_one : δ < 1) (hN_pos : 0 < N) (k : Fin N) :
    (∑ j ∈ Finset.univ.filter
      (fun j : Fin N => k.val ≤ j.val), radius δ N j) ≤
        gap δ N k.val := by
  rw [sum_radius_eq hδ_pos hN_pos k]
  set rr := r δ N
  set m : ℕ := N - k.val
  have hr_pos : 0 < rr := r_pos hδ_pos hN_pos
  have hr_lt_one : rr < 1 :=
    r_lt_one hδ_pos hδ_lt_one hN_pos
  have hkm : k.val + m = N := by
    simp [m] <;> omega
  have hscale_k :
      realScale δ N k.val = rr ^ k.val :=
    realScale_eq_rpow hδ_pos hN_pos k.val
  have hscale_N :
      realScale δ N N = rr ^ N :=
    realScale_eq_rpow hδ_pos hN_pos N
  have hgap :
      gap δ N k.val =
        rr ^ k.val - rr ^ (k.val + 1) := by
    rw [gap, hscale_k,
      realScale_eq_rpow hδ_pos hN_pos (k.val + 1)]
  rw [hgap]
  have hN_pos' : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast hN_pos
  have hseries :
      1 - rr ^ m ≤ (m : ℝ) * (1 - rr) :=
    one_sub_pow_le rr hr_pos hr_lt_one m
  have hm_le_N : (m : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (by omega : m ≤ N)
  have hfactor_nonneg : 0 ≤ 1 - rr := by
    linarith
  have hseries_N :
      1 - rr ^ m ≤ (N : ℝ) * (1 - rr) :=
    hseries.trans (by gcongr)
  have hpow_N : rr ^ N = rr ^ k.val * rr ^ m := by
    have h_eq : rr ^ N = rr ^ (k.val + m) := by
      rw [hkm]
    rw [h_eq, pow_add] <;> ring
  rw [hscale_k, hscale_N, hpow_N]
  calc
    (rr ^ k.val - rr ^ k.val * rr ^ m) / (N : ℝ)
        = (rr ^ k.val * (1 - rr ^ m)) / (N : ℝ) := by
            ring
    _ ≤ (rr ^ k.val * ((N : ℝ) * (1 - rr))) /
          (N : ℝ) := by
            gcongr
    _ = rr ^ k.val * (1 - rr) := by
          field_simp [hN_pos'.ne'] <;> ring
    _ = rr ^ k.val - rr ^ (k.val + 1) := by
          rw [pow_succ]
          ring

/-- The entire radius schedule has total radius at most one. -/
lemma total_radius_le_one {δ : ℝ} {N : ℕ} (hδ_pos : 0 < δ)
    (hδ_lt_one : δ < 1) (hN_pos : 0 < N) :
    multiscaleTotalRadius (radius δ N) ≤ 1 := by
  let k0 : Fin N := ⟨0, hN_pos⟩
  have h_sum :
      multiscaleTotalRadius (radius δ N) =
        (realScale δ N 0 - realScale δ N N) / (N : ℝ) := by
    have h0 :
        (Finset.univ : Finset (Fin N)) =
          Finset.univ.filter
            (fun j : Fin N => (0 : ℕ) ≤ j.val) := by
      ext x
      simp
    rw [multiscaleTotalRadius, h0]
    exact sum_radius_eq hδ_pos hN_pos k0
  rw [h_sum]
  have h_s0 : realScale δ N 0 = 1 := by
    simp [realScale]
  have h_sN : realScale δ N N = δ := by
    simp [realScale]
    have h : (N : ℝ) / (N : ℝ) = 1 := by
      field_simp [hN_pos.ne']
    rw [h]
    simp
  rw [h_s0, h_sN]
  have hN_pos' : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast hN_pos
  have hnum : 1 - δ ≤ (N : ℝ) := by
    have hN_one : (1 : ℝ) ≤ N := by
      exact_mod_cast hN_pos
    linarith
  calc
    (1 - δ) / (N : ℝ) ≤ (N : ℝ) / (N : ℝ) := by
      gcongr
    _ = 1 := by
      field_simp [hN_pos'.ne']

end FixedDepthPowerGridTail
end Kakeya.Streamlined.RandomTranslation.WithShading

end
