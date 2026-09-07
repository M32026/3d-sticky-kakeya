import MyLeanRepo.Kakeya.Cinematic.Section5.NonThinFineRectangleCountInputs
import MyLeanRepo.Kakeya.Cinematic.Targets.GeneralizedPacking

/-!
# Uniform non-thin fine-rectangle count

When `t ≤ 16 * delta`, the fine interval length `L = sqrt(delta / tFine)`
has a uniform lower bound depending only on `C_R`. We partition midpoints
into constantly many clusters, construct an interval hull `J` of length
at most `10L` per cluster, and apply the scale-free
`generalized_packing_bound` with `lambda = 100` using the global center
as the reference function.
-/

noncomputable section

open Finset

namespace Kakeya.Cinematic

theorem non_thin_fine_rectangle_count :
    NonThinFineRectangleCountStatement := by
  intro K C_R hK hCR
  let M : ℕ := Nat.ceil (16 * Real.sqrt C_R / 9) + 1
  let B : ℝ := 42 * (100 : ℝ)^2 * 10
  use (M : ℝ) * B
  constructor
  · have hM_pos : 0 < M := by
      dsimp only [M]
      have h1 : 0 ≤ 16 * Real.sqrt C_R / 9 := by positivity
      omega
    positivity
  · intro delta t Delta hdelta hDelta_delta hDelta_t ht16 family I hI R hCenters hOver hIncomp center hdist
    let tFine : ℝ := C_R * t * Delta / delta
    let L : ℝ := Real.sqrt (delta / tFine)
    have hCR_pos : 0 < C_R := by nlinarith
    have ht_pos : 0 < t := by linarith
    have hDelta_pos : 0 < Delta := by linarith
    have htFine_pos : 0 < tFine := by positivity
    have hL_pos : 0 < L := Real.sqrt_pos.mpr (by positivity)

    -- delta ≤ tFine
    have h_dt : delta ≤ tFine := by
      have h1 : C_R ≥ 1 := by nlinarith
      have h2 : t * Delta ≥ delta * delta := by nlinarith
      have h3 : C_R * t * Delta ≥ delta * delta := by nlinarith
      have h4 : C_R * t * Delta / delta ≥ delta := by
        calc
          C_R * t * Delta / delta ≥ (delta * delta) / delta := by gcongr
          _ = delta := by field_simp [hdelta.ne'] <;> ring
      simpa [show tFine = C_R * t * Delta / delta from rfl] using h4

    -- L ≥ 1 / (16 * sqrt C_R)
    have hL_lower : L ≥ 1 / (16 * Real.sqrt C_R) := by
      have h1 : t * Delta ≤ 256 * delta ^ 2 := by nlinarith
      have h2 : tFine ≤ 256 * C_R * delta := by
        have h31 : C_R * (t * Delta) ≤ C_R * (256 * delta ^ 2) :=
          mul_le_mul_of_nonneg_left h1 (by linarith)
        have h32 : C_R * t * Delta / delta = C_R * (t * Delta) / delta := by ring
        have h33 : C_R * (t * Delta) / delta ≤ C_R * (256 * delta ^ 2) / delta :=
          div_le_div_of_nonneg_right h31 (by positivity)
        have h34 : C_R * (256 * delta ^ 2) / delta = 256 * C_R * delta := by
          field_simp [hdelta.ne'] <;> ring
        have h35 : C_R * t * Delta / delta ≤ 256 * C_R * delta := by
          rw [h32] <;> exact h33.trans (by rw [h34])
        simpa [show tFine = C_R * t * Delta / delta from rfl] using h35
      have h3 : delta / tFine ≥ 1 / (256 * C_R) := by
        calc
          delta / tFine ≥ delta / (256 * C_R * delta) := by gcongr
          _ = 1 / (256 * C_R) := by field_simp [hdelta.ne', hCR_pos.ne'] <;> ring
      have h4 : Real.sqrt (delta / tFine) ≥ Real.sqrt (1 / (256 * C_R)) :=
        Real.sqrt_le_sqrt h3
      have h5 : Real.sqrt (1 / (256 * C_R)) = 1 / (16 * Real.sqrt C_R) := by
        have h6 : Real.sqrt (256 * C_R) = 16 * Real.sqrt C_R := by
          rw [Real.sqrt_mul (by positivity)]
          have h7 : Real.sqrt 256 = 16 := by
            rw [Real.sqrt_eq_cases] <;> norm_num
          rw [h7] <;> ring
        have h8 : Real.sqrt (1 / (256 * C_R)) = 1 / Real.sqrt (256 * C_R) := by
          rw [Real.sqrt_div (by positivity)] <;> norm_num
        rw [h8, h6] <;> ring
      have h9 : L = Real.sqrt (delta / tFine) := by rfl
      rw [h9]
      rw [h5] at h4
      exact h4

    -- 6 * t ≤ 3 * tFine
    have h_dist_conv : 6 * t ≤ 3 * tFine := by
      have h1 : C_R ≥ 2 := by nlinarith
      have h2 : Delta / delta ≥ 1 := by
        have h3 : delta ≤ Delta := hDelta_delta
        have h4 : 0 < delta := hdelta
        calc
          Delta / delta ≥ delta / delta := by gcongr
          _ = 1 := by field_simp [h4.ne'] <;> ring
      have hCR9216 : C_R ≥ 9216 := by
        have hK2 : K ^ 2 ≥ 1 := by nlinarith
        nlinarith
      have h5 : C_R * Delta / delta ≥ 2 := by
        have h6 : C_R * (Delta / delta) ≥ 9216 * (1 : ℝ) := by
          gcongr <;> linarith
        have h7 : C_R * Delta / delta = C_R * (Delta / delta) := by ring
        rw [h7]
        linarith
      have h9 : 3 * tFine = 3 * t * (C_R * Delta / delta) := by
        simp [show tFine = C_R * t * Delta / delta from rfl] <;> ring
      rw [h9]
      nlinarith

    have hM_nat_pos : 0 < M := by
      dsimp only [M]
      have h1 : 0 ≤ 16 * Real.sqrt C_R / 9 := by positivity
      omega

    -- 1/M < 9L
    have h1M_lt : 1 / (M : ℝ) < 9 * L := by
      have h1 : (M : ℝ) > 16 * Real.sqrt C_R / 9 := by
        dsimp only [M]
        have h2 : (Nat.ceil (16 * Real.sqrt C_R / 9) : ℝ) ≥ 16 * Real.sqrt C_R / 9 :=
          Nat.le_ceil _
        have h3 : (M : ℝ) = (Nat.ceil (16 * Real.sqrt C_R / 9) : ℝ) + 1 := by
          simp [M] <;> norm_cast
        rw [h3]
        linarith
      have h3 : 0 < (M : ℝ) := by exact_mod_cast hM_nat_pos
      have h4 : 1 / (M : ℝ) < 1 / (16 * Real.sqrt C_R / 9) :=
        one_div_lt_one_div_of_lt (by positivity) h1
      have h5 : 1 / (16 * Real.sqrt C_R / 9) = 9 / (16 * Real.sqrt C_R) := by
        field_simp [hCR_pos.ne'] <;> ring
      rw [h5] at h4
      have h6 : 9 / (16 * Real.sqrt C_R) ≤ 9 * L := by
        calc
          9 / (16 * Real.sqrt C_R) = 9 * (1 / (16 * Real.sqrt C_R)) := by ring
          _ ≤ 9 * L := by gcongr <;> exact hL_lower
      linarith

    have hI_short : I.IsShort K := hI.2

    -- Cluster index using floor clipped to M-1
    let clusterIdx (i : Fin R.card) : Fin M :=
      let f : ℕ := Nat.floor ((R.rectangle i).interval.midpoint * (M : ℝ))
      ⟨Nat.min f (M - 1), by
        have hMpos : 0 < M := hM_nat_pos
        have h1 : Nat.min f (M - 1) ≤ M - 1 := Nat.min_le_right f (M - 1)
        omega⟩
    let S (k : Fin M) : Finset (Fin R.card) :=
      Finset.univ.filter (fun i => clusterIdx i = k)

    -- Clusters are disjoint
    have h_disj : ∀ (k1 k2 : Fin M), k1 ≠ k2 → Disjoint (S k1) (S k2) := by
      intro k1 k2 hne
      rw [Finset.disjoint_left]
      intro i hi1 hi2
      have h1 : clusterIdx i = k1 := (Finset.mem_filter.mp hi1).2
      have h2 : clusterIdx i = k2 := (Finset.mem_filter.mp hi2).2
      rw [h1] at h2
      exact hne h2

    -- Midpoint in [0,1]
    have h_mid_in : ∀ i : Fin R.card, 0 ≤ (R.rectangle i).interval.midpoint ∧
        (R.rectangle i).interval.midpoint ≤ 1 := by
      intro i
      have h1 : 0 ≤ (R.rectangle i).interval.left := (R.rectangle i).interval.left_mem.1
      have h2 : (R.rectangle i).interval.right ≤ 1 := (R.rectangle i).interval.right_mem.2
      have h3 : (R.rectangle i).interval.left ≤ (R.rectangle i).interval.right :=
        (R.rectangle i).interval.left_le_right
      simp [ParameterInterval.midpoint] <;> constructor <;> linarith

    -- Per-cluster midpoint range: if i ∈ S k, then k/M ≤ m_i ≤ (k+1)/M
    have h_range : ∀ (k : Fin M) (i : Fin R.card), i ∈ S k →
        (k : ℝ) / (M : ℝ) ≤ (R.rectangle i).interval.midpoint ∧
        (R.rectangle i).interval.midpoint ≤ ((k : ℝ) + 1) / (M : ℝ) := by
      intro k i hi
      have h_eq : (clusterIdx i).val = k.val := by
        have h : clusterIdx i = k := (Finset.mem_filter.mp hi).2
        rw [h]
      let m : ℝ := (R.rectangle i).interval.midpoint
      let f : ℕ := Nat.floor (m * (M : ℝ))
      have h_kmin : k.val = Nat.min f (M - 1) := by
        have h1 : (clusterIdx i).val = Nat.min f (M - 1) := by
          simp [clusterIdx] <;> rfl
        have h2 : (clusterIdx i).val = k.val := by rw [h_eq]
        rw [h1] at h2
        exact h2.symm
      have hm0 : 0 ≤ m := (h_mid_in i).1
      have hm1 : m ≤ 1 := (h_mid_in i).2
      have hM_pos' : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM_nat_pos
      by_cases h : f < M - 1
      · -- f < M-1, so k.val = f
        have hk : k.val = f := by
          have hle : f ≤ M - 1 := by omega
          have h_min : Nat.min f (M - 1) = f := by
            simp [Nat.min_def, hle]
          exact h_kmin.trans h_min
        have h1 : (f : ℝ) ≤ m * (M : ℝ) := Nat.floor_le (by positivity)
        have h2 : m * (M : ℝ) < (f : ℝ) + 1 := Nat.lt_floor_add_one (m * (M : ℝ))
        constructor
        · have h3 : (k : ℝ) = (f : ℝ) := by exact_mod_cast hk
          rw [h3, div_le_iff₀ hM_pos']; exact h1
        · have h3 : (k : ℝ) = (f : ℝ) := by exact_mod_cast hk
          rw [h3, le_div_iff₀ hM_pos']; linarith
      · -- f ≥ M-1, so k.val = M-1
        have h' : f ≥ M - 1 := by omega
        have hk : k.val = M - 1 := by
          have h_min : Nat.min f (M - 1) = M - 1 := by
            simp [Nat.min_def, h']
          exact h_kmin.trans h_min
        have h1 : (f : ℝ) ≤ m * (M : ℝ) := Nat.floor_le (by positivity)
        have h2 : (M : ℝ) - 1 ≤ (f : ℝ) := by
          have h21 : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := Nat.cast_pred hM_nat_pos
          have h22 : M - 1 ≤ f := h'
          have h23 : ((M - 1 : ℕ) : ℝ) ≤ (f : ℝ) := by exact_mod_cast h22
          rw [h21] at h23
          exact h23
        have h_cast : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := Nat.cast_pred hM_nat_pos
        have h31 : (M : ℝ) - 1 ≤ m * (M : ℝ) := by linarith
        have h3 : ((M - 1 : ℕ) : ℝ) / (M : ℝ) ≤ m := by
          rw [h_cast]
          exact (div_le_iff₀ hM_pos').mpr h31
        have h4 : m ≤ 1 := hm1
        have h5 : ((k : ℝ) + 1) / (M : ℝ) = 1 := by
          have h6 : (k : ℝ) = ((M - 1 : ℕ) : ℝ) := by exact_mod_cast hk
          rw [h6]
          have h7 : ((M - 1 : ℕ) : ℝ) + 1 = (M : ℝ) := by
            have h71 : 0 < M := hM_nat_pos
            have h : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := Nat.cast_pred hM_nat_pos
            rw [h] <;> linarith
          rw [h7] <;> field_simp [hM_pos'.ne'] <;> ring
        constructor
        · have h6 : (k : ℝ) = ((M - 1 : ℕ) : ℝ) := by exact_mod_cast hk
          rw [h6]; exact_mod_cast h3
        · rw [h5]; exact h4

    -- Midpoint diameter bound
    have h_mid_diam : ∀ (k : Fin M) (i j : Fin R.card),
        i ∈ S k → j ∈ S k →
        |(R.rectangle i).interval.midpoint - (R.rectangle j).interval.midpoint| ≤ 9 * L := by
      intro k i j hi hj
      let mi := (R.rectangle i).interval.midpoint
      let mj := (R.rectangle j).interval.midpoint
      have hri := h_range k i hi
      have hrj := h_range k j hj
      have hM_pos' : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM_nat_pos
      have h6 : ((k : ℝ) + 1) / (M : ℝ) - (k : ℝ) / (M : ℝ) = 1 / (M : ℝ) := by
        field_simp [hM_pos'.ne'] <;> ring
      have h_diff : |mi - mj| ≤ 1 / (M : ℝ) := by
        have h1 : mi - mj ≤ 1 / (M : ℝ) := by
          have h1a : mi ≤ ((k : ℝ) + 1) / (M : ℝ) := hri.2
          have h1b : (k : ℝ) / (M : ℝ) ≤ mj := hrj.1
          linarith [h6]
        have h2 : mj - mi ≤ 1 / (M : ℝ) := by
          have h2a : mj ≤ ((k : ℝ) + 1) / (M : ℝ) := hrj.2
          have h2b : (k : ℝ) / (M : ℝ) ≤ mi := hri.1
          linarith [h6]
        rw [abs_le] <;> constructor <;> linarith
      have h : |mi - mj| ≤ 9 * L := by
        calc
          |mi - mj| ≤ 1 / (M : ℝ) := h_diff
          _ ≤ 9 * L := le_of_lt h1M_lt
      exact h

    -- Per-cluster bound
    have h_cluster : ∀ k : Fin M, (S k).card ≤ B := by
      intro k
      by_cases hS : (S k).Nonempty
      · -- Nonempty cluster
        let lefts : Finset ℝ := Finset.image (fun i => (R.rectangle i).interval.left) (S k)
        let rights : Finset ℝ := Finset.image (fun i => (R.rectangle i).interval.right) (S k)
        have h_lefts_ne : lefts.Nonempty := hS.image _
        have h_rights_ne : rights.Nonempty := hS.image _
        let a : ℝ := Finset.min' lefts h_lefts_ne
        let b : ℝ := Finset.max' rights h_rights_ne

        -- Get witness for a
        rcases Finset.mem_image.mp (Finset.min'_mem lefts h_lefts_ne) with ⟨ia, hia, ha_eq⟩
        rcases Finset.mem_image.mp (Finset.max'_mem rights h_rights_ne) with ⟨ib, hib, hb_eq⟩

        let J : ParameterInterval :=
          { left := a
            right := b
            left_mem := by
              have h5 : a = (R.rectangle ia).interval.left := ha_eq.symm
              rw [h5]
              exact (R.rectangle ia).interval.left_mem
            right_mem := by
              have h5 : b = (R.rectangle ib).interval.right := hb_eq.symm
              rw [h5]
              exact (R.rectangle ib).interval.right_mem
            left_le_right := by
              rcases hS with ⟨i, hi⟩
              have h5 : a ≤ (R.rectangle i).interval.left :=
                Finset.min'_le lefts _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
              have h6 : (R.rectangle i).interval.right ≤ b :=
                Finset.le_max' rights _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
              have h7 : (R.rectangle i).interval.left ≤ (R.rectangle i).interval.right :=
                (R.rectangle i).interval.left_le_right
              linarith }

        have hJ_len : J.length ≤ 10 * L := by
          have ha : a = (R.rectangle ia).interval.left := ha_eq.symm
          have hb : b = (R.rectangle ib).interval.right := hb_eq.symm
          have h_len_a : (R.rectangle ia).interval.length = L := by
            exact (R.rectangle ia).interval_length
          have h_len_b : (R.rectangle ib).interval.length = L := by
            exact (R.rectangle ib).interval_length
          have h_mid : |(R.rectangle ia).interval.midpoint - (R.rectangle ib).interval.midpoint| ≤ 9 * L :=
            h_mid_diam k ia ib hia hib
          have h_left_eq : (R.rectangle ia).interval.left = (R.rectangle ia).interval.midpoint - L / 2 := by
            have hmid : (R.rectangle ia).interval.midpoint = ((R.rectangle ia).interval.left + (R.rectangle ia).interval.right) / 2 := by
              simp [ParameterInterval.midpoint] <;> ring
            have hlen : (R.rectangle ia).interval.right - (R.rectangle ia).interval.left = L := h_len_a
            rw [hmid]
            linarith
          have h_right_eq : (R.rectangle ib).interval.right = (R.rectangle ib).interval.midpoint + L / 2 := by
            have hmid : (R.rectangle ib).interval.midpoint = ((R.rectangle ib).interval.left + (R.rectangle ib).interval.right) / 2 := by
              simp [ParameterInterval.midpoint] <;> ring
            have hlen : (R.rectangle ib).interval.right - (R.rectangle ib).interval.left = L := h_len_b
            rw [hmid]
            linarith
          have h_J_len : J.length = b - a := by rfl
          rw [h_J_len, ha, hb, h_left_eq, h_right_eq]
          have h_abs2 : (R.rectangle ib).interval.midpoint - (R.rectangle ia).interval.midpoint ≤ 9 * L := by
            calc
              (R.rectangle ib).interval.midpoint - (R.rectangle ia).interval.midpoint
                ≤ |(R.rectangle ib).interval.midpoint - (R.rectangle ia).interval.midpoint| := le_abs_self _
              _ = |(R.rectangle ia).interval.midpoint - (R.rectangle ib).interval.midpoint| := by rw [abs_sub_comm]
              _ ≤ 9 * L := h_mid
          linarith [hL_pos]

        -- Subfamily
        let e : Fin (S k).card ↪ Fin R.card :=
          (Finset.orderEmbOfFin (S k) rfl).toEmbedding
        let sub : RectangleSubfamily R := ⟨(S k).card, e⟩
        let R_k := sub.family
        have h_e_mem : ∀ i, e i ∈ S k := Finset.orderEmbOfFin_mem (S k) rfl

        have hCenters_k : R_k.CentersIn family := by
          intro i; exact hCenters (e i)
        have hOver_k : R_k.IsOverCentralQuarterOf I := by
          intro i; exact hOver (e i)
        have hIncomp_k : R_k.IsPairwiseIncomparable family 100 := by
          intro i j hne
          have hne2 : e i ≠ e j := by
            intro h; exact hne (e.inj' h)
          exact hIncomp (e i) (e j) hne2
        have hdist_k : ∀ i, c2Distance center (R_k.rectangle i).function ≤ 3 * tFine := by
          intro i
          have h1 : c2Distance center (R.rectangle (e i)).function ≤ 6 * t := hdist (e i)
          have h2 : (R_k.rectangle i).function = (R.rectangle (e i)).function := by rfl
          rw [h2]
          exact h1.trans h_dist_conv

        -- Containment
        have hcontain_k : ∀ i, (R_k.rectangle i).carrier ⊆
            verticalNeighborhoodOn center (100 * delta) J := by
          intro i p hp
          let j : Fin R.card := e i
          have hj_in : j ∈ S k := h_e_mem i
          have h1 : p.1 ∈ (R.rectangle j).interval.carrier := hp.1
          have h2 : |p.2 - (R.rectangle j).function p.1| ≤ delta := hp.2
          have h3 : p.1 ∈ J.carrier := by
            have h4 : (R.rectangle j).interval.left ≤ (p.1 : ℝ) := h1.1
            have h5 : (p.1 : ℝ) ≤ (R.rectangle j).interval.right := h1.2
            have h6 : a ≤ (R.rectangle j).interval.left :=
              Finset.min'_le lefts _ (Finset.mem_image.mpr ⟨j, hj_in, rfl⟩)
            have h7 : (R.rectangle j).interval.right ≤ b :=
              Finset.le_max' rights _ (Finset.mem_image.mpr ⟨j, hj_in, rfl⟩)
            exact ⟨by linarith, by linarith⟩
          have h4 : |p.2 - center p.1| ≤ 100 * delta := by
            have h5 : |(R.rectangle j).function p.1 - center p.1| ≤
                c2Distance ((R.rectangle j).function) center :=
              abs_value_sub_le_c2Distance ((R.rectangle j).function) center p.1
            have h6 : c2Distance ((R.rectangle j).function) center ≤ 6 * t := by
              have h_sym : c2Distance ((R.rectangle j).function) center =
                  c2Distance center ((R.rectangle j).function) := by
                rw [c2Distance_eq_dist, c2Distance_eq_dist, dist_comm]
              rw [h_sym]; exact hdist j
            calc
              |p.2 - center p.1|
                ≤ |p.2 - (R.rectangle j).function p.1| +
                    |(R.rectangle j).function p.1 - center p.1| := by
                  exact abs_sub_le _ _ _
              _ ≤ delta + c2Distance ((R.rectangle j).function) center := by gcongr
              _ ≤ delta + 6 * t := by gcongr
              _ ≤ delta + 6 * (16 * delta) := by gcongr <;> linarith
              _ = 97 * delta := by ring
              _ ≤ 100 * delta := by linarith
          exact ⟨h3, h4⟩

        have h_bound : (R_k.card : ℝ) ≤ 42 * (100 : ℝ)^2 * J.length / L :=
          generalized_packing_bound
            (hK := hK) (hI := hI_short) (hdelta := hdelta) (hdt := h_dt)
            (hlambda := by norm_num)
            (hCenters := hCenters_k) (hOver := hOver_k)
            (hIncomp := hIncomp_k) (hdist := hdist_k)
            (hcontain := hcontain_k)

        have h_final : (R_k.card : ℝ) ≤ B := by
          calc
            (R_k.card : ℝ)
              ≤ 42 * (100 : ℝ)^2 * J.length / L := h_bound
            _ ≤ 42 * (100 : ℝ)^2 * (10 * L) / L := by gcongr <;> linarith
            _ = B := by
              field_simp [hL_pos.ne'] <;> simp [B] <;> ring
        exact_mod_cast h_final

      · -- Empty cluster
        have h_empty : (S k).card = 0 := by
          simpa [Finset.not_nonempty_iff_eq_empty] using hS
        rw [h_empty] <;> norm_num [B]

    -- Sum over clusters
    have h_univ : Finset.biUnion (Finset.univ : Finset (Fin M)) S =
        (Finset.univ : Finset (Fin R.card)) := by
      ext i
      simp only [S, Finset.mem_biUnion, Finset.mem_univ, true_and]
      constructor
      · intro _; trivial
      · intro _
        refine ⟨clusterIdx i, by simp [S]⟩

    have h_disj' : ((Finset.univ : Finset (Fin M)) : Set (Fin M)).PairwiseDisjoint S := by
      intro k1 _ k2 _ hne
      exact h_disj k1 k2 hne
    have h_card : (Finset.biUnion (Finset.univ : Finset (Fin M)) S).card =
        ∑ k : Fin M, (S k).card :=
      Finset.card_biUnion (h := h_disj')

    have h_sum : (R.card : ℝ) = ∑ k : Fin M, ((S k).card : ℝ) := by
      have h9 : (Finset.biUnion (Finset.univ : Finset (Fin M)) S).card = R.card := by
        rw [h_univ] <;> simp
      rw [h9] at h_card
      exact_mod_cast h_card

    rw [h_sum]
    have h_final : ∑ k : Fin M, ((S k).card : ℝ) ≤ (M : ℝ) * B := by
      calc
        ∑ k : Fin M, ((S k).card : ℝ)
          ≤ ∑ k : Fin M, B := by
            apply Finset.sum_le_sum
            intro k _
            exact h_cluster k
        _ = (M : ℝ) * B := by
          simp [Finset.sum_const] <;> ring
    exact h_final

end Kakeya.Cinematic
