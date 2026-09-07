import MyLeanRepo.Kakeya.Assouad.WZ1.MildRescalingBoxPigeonholeHelpers
import Mathlib.Tactic

/-!
# Mass-popular source box for WZ1 Lemma 8
-/

namespace Kakeya.Assouad

open MeasureTheory

theorem wz1_mild_rescaling_box_pigeonhole :
    WZ1MildRescalingBoxPigeonholeStatement := by
  intro F Y hUnion h hh h1
  let n : ℕ := Nat.floor (3 / h)
  have h_pos : 0 ≤ 3 / h := by
    positivity
  have h2 : 3 ≤ 3 / h := by
    calc
      3 = 3 * h / h := by field_simp [hh.ne']
      _ ≤ 3 / h := by
        gcongr
        linarith
  have hn3 : n ≥ 3 := by
    exact (Nat.le_floor_iff h_pos).mpr h2
  have hN : (n : ℝ) ≤ 3 / h :=
    Nat.floor_le h_pos
  have h_nh1 : 3 / h < (n : ℝ) + 1 := by
    simpa [n] using Nat.lt_floor_add_one (3 / h)
  have hnh : (n : ℝ) * h > 2 := by
    have h3 : 3 < ((n : ℝ) + 1) * h := by
      calc
        3 = (3 / h) * h := by field_simp [hh.ne']
        _ < ((n : ℝ) + 1) * h := by gcongr
    have h4 :
        ((n : ℝ) + 1) * h = (n : ℝ) * h + h := by
      ring
    rw [h4] at h3
    linarith
  set d : ℝ := (2 - h) / ((n : ℝ) - 1) with hd_def
  have hnd_pos : 0 < (n : ℝ) - 1 := by
    linarith
  have hd_pos : 0 < d := by
    have htwo_sub : 0 < 2 - h := by
      linarith
    rw [hd_def]
    positivity
  have hd_le_h : d ≤ h := by
    rw [hd_def]
    have h4 : 2 - h ≤ ((n : ℝ) - 1) * h := by
      linarith
    calc
      (2 - h) / ((n : ℝ) - 1)
          ≤ (((n : ℝ) - 1) * h) / ((n : ℝ) - 1) := by
            gcongr
      _ = h := by field_simp [hnd_pos.ne']
  let first : Fin n := ⟨0, by omega⟩
  let last : Fin n := ⟨n - 1, by omega⟩
  let c : Fin n → ℝ :=
    fun k => -1 + h / 2 + (k : ℝ) * d
  have hc0 : c first = -1 + h / 2 := by
    simp [c, first]
  have hc_last : c last = 1 - h / 2 := by
    have h_last_val : (last : ℝ) = (n : ℝ) - 1 := by
      have hlast : (last : ℕ) = n - 1 := by
        simp [last]
      rw [show (last : ℝ) = ↑(last : ℕ) by simp, hlast]
      rw [Nat.cast_sub (show 1 ≤ n by omega)]
      simp
    rw [show c last =
      -1 + h / 2 + (last : ℝ) * d by rfl]
    rw [h_last_val, hd_def]
    field_simp [hnd_pos.ne']
    ring
  have hc_margin :
      ∀ k : Fin n, |c k| ≤ 1 - h / 2 := by
    intro k
    have hk_nonneg : 0 ≤ (k : ℝ) := by
      exact_mod_cast Nat.zero_le k.val
    have hk_le : (k : ℝ) ≤ (n : ℝ) - 1 := by
      have hk : k.val + 1 ≤ n := by
        omega
      have hk' : (k : ℝ) + 1 ≤ (n : ℝ) := by
        exact_mod_cast hk
      linarith
    have hc_lower : -1 + h / 2 ≤ c k := by
      have hnonneg : 0 ≤ (k : ℝ) * d := by
        positivity
      change -1 + h / 2 ≤ -1 + h / 2 + (k : ℝ) * d
      linarith
    have hc_upper : c k ≤ 1 - h / 2 := by
      have hmul :
          (k : ℝ) * d ≤ ((n : ℝ) - 1) * d :=
        mul_le_mul_of_nonneg_right hk_le hd_pos.le
      have htotal :
          ((n : ℝ) - 1) * d = 2 - h := by
        rw [hd_def]
        field_simp [hnd_pos.ne']
      rw [htotal] at hmul
      change -1 + h / 2 + (k : ℝ) * d ≤ 1 - h / 2
      linarith
    exact abs_le.mpr ⟨by linarith, hc_upper⟩
  have hc_mem :
      ∀ k : Fin n, c k ∈ Set.Icc (-1 : ℝ) 1 := by
    intro k
    have hmargin := abs_le.mp (hc_margin k)
    exact ⟨by linarith, by linarith⟩
  have h1D_cover :
      ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 →
        ∃ k : Fin n, |x - c k| ≤ h / 2 := by
    intro x hx
    let S : Finset (Fin n) :=
      Finset.univ.filter (fun k => x ≤ c k + h / 2)
    have hS_nonempty : S.Nonempty := by
      have hx_last : x ≤ c last + h / 2 := by
        rw [hc_last]
        linarith [hx.2]
      exact ⟨last, by simp [S, hx_last]⟩
    let k : Fin n := S.min' hS_nonempty
    have hkS : k ∈ S :=
      Finset.min'_mem S hS_nonempty
    have hk_cond : x ≤ c k + h / 2 := by
      simpa [S, Finset.mem_filter] using hkS
    by_cases hk_zero : k.val = 0
    · have hk_first : k = first := by
        apply Fin.ext
        simp [first, hk_zero]
      rw [hk_first] at hk_cond
      refine ⟨first, ?_⟩
      rw [abs_le]
      have hleft : c first - h / 2 ≤ x := by
        rw [hc0]
        linarith [hx.1]
      constructor <;> linarith
    · have hk_pos : 0 < k.val := by
        omega
      let k' : Fin n := ⟨k.val - 1, by omega⟩
      have hk'_lt : k' < k := by
        simp [k', Fin.lt_def]
        omega
      have hk'_notS : k' ∉ S := by
        intro hk'
        have hle : k ≤ k' :=
          Finset.min'_le S k' hk'
        exact not_le.mpr hk'_lt hle
      have hk'_right : c k' + h / 2 < x := by
        have hnot : ¬x ≤ c k' + h / 2 := by
          simpa [S, Finset.mem_filter] using hk'_notS
        linarith
      have hk_diff : (k : ℝ) = (k' : ℝ) + 1 := by
        have hval : k.val = k'.val + 1 := by
          simp [k']
          omega
        exact_mod_cast hval
      have hc_step : c k = c k' + d := by
        change
          -1 + h / 2 + (k : ℝ) * d =
            (-1 + h / 2 + (k' : ℝ) * d) + d
        rw [hk_diff]
        ring
      have hleft : c k - h / 2 ≤ x := by
        rw [hc_step]
        linarith [hd_le_h]
      refine ⟨k, ?_⟩
      rw [abs_le]
      constructor <;> linarith
  let halfWidth : Point3 :=
    point3 (h / 2) (h / 2) (h / 2)
  let Idx := Fin n × Fin n × Fin n
  let center : Idx → Point3 :=
    fun p => point3 (c p.1) (c p.2.1) (c p.2.2)
  let box : Idx → Set Point3 :=
    fun p =>
      wz1MildRescalingSourceBox (center p) halfWidth
  have h3D_cover :
      wz1MildRescalingSourceWindow ⊆ ⋃ p : Idx, box p := by
    intro x hx
    have hx_coords : ∀ i : Fin 3, |x i| ≤ 1 := by
      simpa [wz1MildRescalingSourceWindow,
        Set.mem_setOf_eq] using hx
    have hcoordinate :
        ∀ j : Fin 3, ∃ k : Fin n, |x j - c k| ≤ h / 2 := by
      intro j
      exact
        h1D_cover (x j)
          (abs_le.mp (hx_coords j))
    choose k0 hk0 using hcoordinate 0
    choose k1 hk1 using hcoordinate 1
    choose k2 hk2 using hcoordinate 2
    let p : Idx := (k0, k1, k2)
    have haxis :
        x ∈ wz1AxisBox (center p) halfWidth := by
      simp only [wz1AxisBox, Set.mem_setOf_eq]
      intro i
      fin_cases i
      · simpa [center, halfWidth, point3_apply] using hk0
      · simpa [center, halfWidth, point3_apply] using hk1
      · simpa [center, halfWidth, point3_apply] using hk2
    have hbox : x ∈ box p := by
      simp only [box, wz1MildRescalingSourceBox,
        Set.mem_inter_iff]
      exact ⟨haxis, hx⟩
    exact Set.mem_iUnion.mpr ⟨p, hbox⟩
  have hcarrier_cover :
      ∀ i : Fin F.card,
        Y.carrier i ⊆ ⋃ p : Idx, box p := by
    intro i
    exact
      subset_trans
        (show Y.carrier i ⊆ Y.union from
          fun x hx => ⟨i, hx⟩)
        (subset_trans hUnion h3D_cover)
  have hvolume :
      ∀ i : Fin F.card,
        volume (Y.carrier i) ≤
          ∑ p : Idx, volume (Y.carrier i ∩ box p) := by
    intro i
    exact measure_cover_le_sum (hcarrier_cover i)
  have hsum :
      Y.mass ≤
        ∑ p : Idx,
          ∑ i : Fin F.card,
            volume (Y.carrier i ∩ box p) := by
    calc
      Y.mass =
          ∑ i : Fin F.card,
            volume (Y.carrier i) := by
        rfl
      _ ≤
          ∑ i : Fin F.card,
            ∑ p : Idx,
              volume (Y.carrier i ∩ box p) :=
        Finset.sum_le_sum (fun i _ => hvolume i)
      _ =
          ∑ p : Idx,
            ∑ i : Fin F.card,
              volume (Y.carrier i ∩ box p) := by
        rw [Finset.sum_comm]
  let captured : Idx → ENNReal :=
    fun p =>
      ∑ i : Fin F.card,
        volume (Y.carrier i ∩ box p)
  let threshold : Idx → ENNReal :=
    fun _ => ENNReal.ofReal (h ^ 3 / 27) * Y.mass
  have hIdx_nonempty : Nonempty Idx :=
    ⟨(first, first, first)⟩
  have hcard : Fintype.card Idx = n ^ 3 := by
    simp [Idx, Fintype.card_prod]
    ring
  have hthreshold_sum :
      ∑ p : Idx, threshold p =
        (Fintype.card Idx : ENNReal) *
          ENNReal.ofReal (h ^ 3 / 27) * Y.mass := by
    simp [threshold, Finset.sum_const, hcard]
    ring
  have hcube :
      (n ^ 3 : ENNReal) *
          ENNReal.ofReal (h ^ 3 / 27) ≤ 1 := by
    simpa [Nat.cast_pow] using cube_mul_le n h hh hN
  have hsum_compare :
      ∑ p : Idx, threshold p ≤
        ∑ p : Idx, captured p := by
    rw [hthreshold_sum, hcard]
    have hcast :
        (↑(n ^ 3) : ENNReal) = (↑n ^ 3 : ENNReal) := by
      rw [Nat.cast_pow]
    rw [hcast]
    exact
      (calc
        (↑n ^ 3 : ENNReal) *
              ENNReal.ofReal (h ^ 3 / 27) * Y.mass
            ≤ 1 * Y.mass := by gcongr
        _ = Y.mass := by ring
        _ ≤ ∑ p : Idx, captured p := hsum)
  have hexists :
      ∃ p : Idx, threshold p ≤ captured p := by
    simpa using
      ENNReal.exists_le_of_sum_le
        (Finset.univ_nonempty : (Finset.univ : Finset Idx).Nonempty)
        hsum_compare
  rcases hexists with ⟨p, hp⟩
  have hcenter :
      center p ∈ wz1MildRescalingSourceWindow := by
    have hcoords : ∀ i : Fin 3, |(center p) i| ≤ 1 := by
      intro i
      fin_cases i
      · simpa [center, point3_apply] using
          abs_le.mpr (hc_mem p.1)
      · simpa [center, point3_apply] using
          abs_le.mpr (hc_mem p.2.1)
      · simpa [center, point3_apply] using
          abs_le.mpr (hc_mem p.2.2)
    simpa [wz1MildRescalingSourceWindow,
      Set.mem_setOf_eq] using hcoords
  have hcenterMargin : ∀ i : Fin 3, |(center p) i| ≤ 1 - h / 2 := by
    intro i
    fin_cases i
    · simpa [center, point3_apply] using hc_margin p.1
    · simpa [center, point3_apply] using hc_margin p.2.1
    · simpa [center, point3_apply] using hc_margin p.2.2
  exact ⟨center p, hcenterMargin, hcenter, by
    simpa [threshold, captured, box, halfWidth] using hp⟩

end Kakeya.Assouad
