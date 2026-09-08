import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.GridCounting
import MyLeanRepo.Kakeya.Streamlined.Geometry

/-!
# Generic intercept-based phase-space grid packing

A generic grid-packing theorem parameterized by per-tube intercept data.
For each tube, the caller supplies a plane index, two transverse intercept
coordinates, a segment parameter, and two transverse direction coordinates.
The theorem grids all five quantities and proves injectivity via the supplied
closeness lemma.

## Main result

`phase_space_grid_packing_intercept`: generic cardinality bound.
-/

noncomputable section

namespace Kakeya.Streamlined.GeometricLemmas

open Kakeya.Streamlined

/--
Generic intercept-based phase-space packing bound.

The caller supplies per-tube functions `plane_idx`, `q1`, `q2`, `t0`, `du1`,
`du2` and their range bounds.  The theorem grids `q1,q2` and `du1,du2` with
cell size `δ/100`, `t0` with 8 cells of spacing `1/8`, and uses `plane_idx`
directly (bounded by `K`).  Two tubes mapping to the same cell tuple satisfy
all five closeness inequalities, so `h_close` rules out essential distinctness.
-/
theorem phase_space_grid_packing_intercept
    {δ A : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hA : 1 ≤ A)
    {F : TubeFamily δ}
    (hdistinct : F.IsEssentiallyDistinct)
    (R1 R2 D1 D2 : ℝ) (hR1 : 0 < R1) (hR2 : 0 < R2) (hD1 : 0 < D1) (hD2 : 0 < D2)
    (K : ℕ)
    (plane_idx : DeltaTube δ → ℕ)
    (q1 q2 t0 du1 du2 : DeltaTube δ → ℝ)
    (h_plane : ∀ T ∈ F, plane_idx T < K)
    (h_q1 : ∀ T ∈ F, |q1 T| ≤ R1)
    (h_q2 : ∀ T ∈ F, |q2 T| ≤ R2)
    (h_t0 : ∀ T ∈ F, t0 T ∈ Set.Icc 0 1)
    (h_du1 : ∀ T ∈ F, |du1 T| ≤ D1)
    (h_du2 : ∀ T ∈ F, |du2 T| ≤ D2)
    (h_close : ∀ (T1 T2 : DeltaTube δ), T1 ∈ F → T2 ∈ F →
        plane_idx T1 = plane_idx T2 →
        |q1 T1 - q1 T2| ≤ δ / 100 →
        |q2 T1 - q2 T2| ≤ δ / 100 →
        |t0 T1 - t0 T2| ≤ 1 / 8 →
        |du1 T1 - du1 T2| ≤ δ / 100 →
        |du2 T1 - du2 T2| ≤ δ / 100 →
        ¬ T1.EssentiallyDistinct T2)
    : F.enncard ≤ ENNReal.ofReal ((K : ℝ) * (200 * R1 / δ + 2) * (200 * R2 / δ + 2) * 8 * (200 * D1 / δ + 2) * (200 * D2 / δ + 2)) := by
  set s : ℝ := δ / 100 with hs_def
  have hs_pos : 0 < s := by
    dsimp only [s] <;> exact div_pos hδ (by norm_num)

  have hR1' : -R1 ≤ R1 := by linarith
  have hR2' : -R2 ≤ R2 := by linarith
  have hD1' : -D1 ≤ D1 := by linarith
  have hD2' : -D2 ≤ D2 := by linarith

  -- Position grid for (q1, q2): [-R1,R1] × [-R2,R2]
  rcases grid_cover_bound (-R1) R1 (-R2) R2 s hs_pos hR1' hR2'
    with ⟨cells_pos, hcover_pos, hcard_pos⟩

  -- Direction grid for (du1, du2): [-D1,D1] × [-D2,D2]
  rcases grid_cover_bound (-D1) D1 (-D2) D2 s hs_pos hD1' hD2'
    with ⟨cells_dir, hcover_dir, hcard_dir⟩

  -- t0 grid: 8 cells at (2*n+1)/16 for n = 0..7, covering [0,1] within 1/16
  let cells_t0 : Finset ℝ :=
    Finset.image (fun n : ℕ => ((2 * (n : ℝ) + 1) / 16)) (Finset.range 8)

  have hcover_t0 : ∀ (t : ℝ), 0 ≤ t → t ≤ 1 →
      ∃ (c : ℝ), c ∈ cells_t0 ∧ |t - c| ≤ 1 / 16 := by
    intro t ht0 ht1
    by_cases h_t1 : t = 1
    · refine ⟨(15 / 16 : ℝ), ?_, ?_⟩
      · simp only [cells_t0, Finset.mem_image, Finset.mem_range]
        exact ⟨7, by norm_num, by norm_num⟩
      · rw [h_t1] <;> norm_num
    · have h_t_lt1 : t < 1 := lt_of_le_of_ne ht1 h_t1
      have h8t_pos : 0 ≤ 8 * t := by linarith
      set n : ℕ := Nat.floor (8 * t) with hn_def
      have hn_lt8 : n < 8 := by
        have h1 : (n : ℝ) ≤ 8 * t := Nat.floor_le h8t_pos
        have h2 : (n : ℝ) < 8 := by linarith
        exact_mod_cast h2
      have h4 : (n : ℝ) ≤ 8 * t := Nat.floor_le h8t_pos
      have h5 : 8 * t < (n : ℝ) + 1 := by
        simpa [hn_def] using Nat.lt_floor_add_one (8 * t)
      let c : ℝ := (2 * (n : ℝ) + 1) / 16
      have hc_in : c ∈ cells_t0 := by
        simp only [cells_t0, Finset.mem_image, Finset.mem_range]
        exact ⟨n, hn_lt8, by simp [c]⟩
      have h_abs : |t - c| ≤ 1 / 16 := by
        have h8 : t - c ≤ 1 / 16 := by
          dsimp only [c] <;> linarith
        have h9 : -(1 / 16 : ℝ) ≤ t - c := by
          dsimp only [c] <;> linarith
        exact abs_le.mpr ⟨h9, h8⟩
      exact ⟨c, hc_in, h_abs⟩

  have hcard_t0 : (cells_t0.card : ℝ) ≤ 8 := by
    have h : cells_t0.card ≤ 8 := by
      have h' : cells_t0 = Finset.image (fun n : ℕ => ((2 * (n : ℝ) + 1) / 16)) (Finset.range 8) := by rfl
      rw [h']
      simpa using Finset.card_image_le (s := Finset.range 8) (f := _)
    exact_mod_cast h

  classical

  let cells_plane : Finset ℕ := Finset.range K

  let cellPairs : Finset (((ℕ × (ℝ × ℝ)) × ℝ) × (ℝ × ℝ)) :=
    ((cells_plane ×ˢ cells_pos) ×ˢ cells_t0) ×ˢ cells_dir

  -- Helper to choose position cell
  let choose_pos_cell (p : ℝ × ℝ) (h1 : -R1 ≤ p.1) (h2 : p.1 ≤ R1)
      (h3 : -R2 ≤ p.2) (h4 : p.2 ≤ R2) : ℝ × ℝ :=
    Classical.choose (hcover_pos p h1 h2 h3 h4)
  have choose_pos_cell_spec : ∀ p h1 h2 h3 h4,
      choose_pos_cell p h1 h2 h3 h4 ∈ cells_pos ∧
      |p.1 - (choose_pos_cell p h1 h2 h3 h4).1| ≤ s / 2 ∧
      |p.2 - (choose_pos_cell p h1 h2 h3 h4).2| ≤ s / 2 := by
    intro p h1 h2 h3 h4
    exact Classical.choose_spec (hcover_pos p h1 h2 h3 h4)

  -- Helper to choose direction cell
  let choose_dir_cell (p : ℝ × ℝ) (h1 : -D1 ≤ p.1) (h2 : p.1 ≤ D1)
      (h3 : -D2 ≤ p.2) (h4 : p.2 ≤ D2) : ℝ × ℝ :=
    Classical.choose (hcover_dir p h1 h2 h3 h4)
  have choose_dir_cell_spec : ∀ p h1 h2 h3 h4,
      choose_dir_cell p h1 h2 h3 h4 ∈ cells_dir ∧
      |p.1 - (choose_dir_cell p h1 h2 h3 h4).1| ≤ s / 2 ∧
      |p.2 - (choose_dir_cell p h1 h2 h3 h4).2| ≤ s / 2 := by
    intro p h1 h2 h3 h4
    exact Classical.choose_spec (hcover_dir p h1 h2 h3 h4)

  -- Helper to choose t0 cell
  let choose_t0_cell (t : ℝ) (h1 : 0 ≤ t) (h2 : t ≤ 1) : ℝ :=
    Classical.choose (hcover_t0 t h1 h2)
  have choose_t0_cell_spec : ∀ t h1 h2,
      choose_t0_cell t h1 h2 ∈ cells_t0 ∧ |t - choose_t0_cell t h1 h2| ≤ 1 / 16 := by
    intro t h1 h2
    exact Classical.choose_spec (hcover_t0 t h1 h2)

  -- Cell assignment
  let cplane (T : DeltaTube δ) : ℕ := plane_idx T
  let cpos (T : DeltaTube δ) : ℝ × ℝ :=
    if hT : T ∈ F then
      let h1 : -R1 ≤ q1 T := by linarith [abs_le.mp (h_q1 T hT)]
      let h2 : q1 T ≤ R1 := by linarith [abs_le.mp (h_q1 T hT)]
      let h3 : -R2 ≤ q2 T := by linarith [abs_le.mp (h_q2 T hT)]
      let h4 : q2 T ≤ R2 := by linarith [abs_le.mp (h_q2 T hT)]
      choose_pos_cell (q1 T, q2 T) h1 h2 h3 h4
    else (0, 0)
  let cparam (T : DeltaTube δ) : ℝ :=
    if hT : T ∈ F then
      let ht0_0 : 0 ≤ t0 T := (h_t0 T hT).1
      let ht0_1 : t0 T ≤ 1 := (h_t0 T hT).2
      choose_t0_cell (t0 T) ht0_0 ht0_1
    else 0
  let cdir (T : DeltaTube δ) : ℝ × ℝ :=
    if hT : T ∈ F then
      let h1 : -D1 ≤ du1 T := by linarith [abs_le.mp (h_du1 T hT)]
      let h2 : du1 T ≤ D1 := by linarith [abs_le.mp (h_du1 T hT)]
      let h3 : -D2 ≤ du2 T := by linarith [abs_le.mp (h_du2 T hT)]
      let h4 : du2 T ≤ D2 := by linarith [abs_le.mp (h_du2 T hT)]
      choose_dir_cell (du1 T, du2 T) h1 h2 h3 h4
    else (0, 0)

  -- Spec lemmas using equality trick
  have hcpos_spec : ∀ T ∈ F, cpos T ∈ cells_pos ∧
      |q1 T - (cpos T).1| ≤ s / 2 ∧ |q2 T - (cpos T).2| ≤ s / 2 := by
    intro T hT
    have h1 : -R1 ≤ q1 T := by linarith [abs_le.mp (h_q1 T hT)]
    have h2 : q1 T ≤ R1 := by linarith [abs_le.mp (h_q1 T hT)]
    have h3 : -R2 ≤ q2 T := by linarith [abs_le.mp (h_q2 T hT)]
    have h4 : q2 T ≤ R2 := by linarith [abs_le.mp (h_q2 T hT)]
    have h_eq : cpos T = choose_pos_cell (q1 T, q2 T) h1 h2 h3 h4 := by
      dsimp only [cpos]
      rw [dif_pos hT] <;> rfl
    rw [h_eq]
    exact choose_pos_cell_spec (q1 T, q2 T) h1 h2 h3 h4

  have hcparam_spec : ∀ T ∈ F, cparam T ∈ cells_t0 ∧ |t0 T - cparam T| ≤ 1 / 16 := by
    intro T hT
    have ht0_0 : 0 ≤ t0 T := (h_t0 T hT).1
    have ht0_1 : t0 T ≤ 1 := (h_t0 T hT).2
    have h_eq : cparam T = choose_t0_cell (t0 T) ht0_0 ht0_1 := by
      dsimp only [cparam]
      rw [dif_pos hT] <;> rfl
    rw [h_eq]
    exact choose_t0_cell_spec (t0 T) ht0_0 ht0_1

  have hcdir_spec : ∀ T ∈ F, cdir T ∈ cells_dir ∧
      |du1 T - (cdir T).1| ≤ s / 2 ∧ |du2 T - (cdir T).2| ≤ s / 2 := by
    intro T hT
    have h1 : -D1 ≤ du1 T := by linarith [abs_le.mp (h_du1 T hT)]
    have h2 : du1 T ≤ D1 := by linarith [abs_le.mp (h_du1 T hT)]
    have h3 : -D2 ≤ du2 T := by linarith [abs_le.mp (h_du2 T hT)]
    have h4 : du2 T ≤ D2 := by linarith [abs_le.mp (h_du2 T hT)]
    have h_eq : cdir T = choose_dir_cell (du1 T, du2 T) h1 h2 h3 h4 := by
      dsimp only [cdir]
      rw [dif_pos hT] <;> rfl
    rw [h_eq]
    exact choose_dir_cell_spec (du1 T, du2 T) h1 h2 h3 h4

  let f : DeltaTube δ → ((ℕ × (ℝ × ℝ)) × ℝ) × (ℝ × ℝ) :=
    fun T => (((cplane T, cpos T), cparam T), cdir T)

  have h_f_in_cells : ∀ T ∈ F, f T ∈ cellPairs := by
    intro T hT
    have h1 : cplane T ∈ cells_plane := by
      simp only [cells_plane, Finset.mem_range]; exact h_plane T hT
    have h21 : cpos T ∈ cells_pos := (hcpos_spec T hT).1
    have h22 : cparam T ∈ cells_t0 := (hcparam_spec T hT).1
    have h23 : cdir T ∈ cells_dir := (hcdir_spec T hT).1
    have h_inner : (cplane T, cpos T) ∈ cells_plane ×ˢ cells_pos :=
      Finset.mem_product.mpr ⟨h1, h21⟩
    have h_left : ((cplane T, cpos T), cparam T) ∈ (cells_plane ×ˢ cells_pos) ×ˢ cells_t0 :=
      Finset.mem_product.mpr ⟨h_inner, h22⟩
    have h_all : (((cplane T, cpos T), cparam T), cdir T) ∈ cellPairs :=
      Finset.mem_product.mpr ⟨h_left, h23⟩
    simpa [f] using h_all

  have h_inj : Set.InjOn f F := by
    intro T1 hT1 T2 hT2 h_eq
    have h_plane_eq : cplane T1 = cplane T2 := by
      exact congr_arg (fun x : ((ℕ × (ℝ × ℝ)) × ℝ) × (ℝ × ℝ) => x.1.1.1) h_eq
    have h_cpos_eq : cpos T1 = cpos T2 := by
      exact congr_arg (fun x => x.1.1.2) h_eq
    have h_cparam_eq : cparam T1 = cparam T2 := by
      exact congr_arg (fun x => x.1.2) h_eq
    have h_cdir_eq : cdir T1 = cdir T2 := by
      exact congr_arg (fun x => x.2) h_eq

    have h_q1_diff : |q1 T1 - q1 T2| ≤ δ / 100 := by
      have h1 : |q1 T1 - (cpos T1).1| ≤ s / 2 := (hcpos_spec T1 hT1).2.1
      have h2 : |q1 T2 - (cpos T2).1| ≤ s / 2 := (hcpos_spec T2 hT2).2.1
      have h_e : |q1 T1 - q1 T2| ≤ |q1 T1 - (cpos T1).1| + |(cpos T1).1 - q1 T2| := abs_sub_le _ _ _
      have h_rew : |(cpos T1).1 - q1 T2| = |q1 T2 - (cpos T2).1| := by
        calc |(cpos T1).1 - q1 T2|
          = |q1 T2 - (cpos T1).1| := by rw [abs_sub_comm]
        _ = |q1 T2 - (cpos T2).1| := by rw [h_cpos_eq]
      rw [h_rew] at h_e
      have h_sum : |q1 T1 - (cpos T1).1| + |q1 T2 - (cpos T2).1| ≤ s := by
        calc |q1 T1 - (cpos T1).1| + |q1 T2 - (cpos T2).1|
          ≤ s / 2 + s / 2 := by gcongr
        _ = s := by ring
      have h_s : s ≤ δ / 100 := by rw [hs_def] <;> linarith
      linarith

    have h_q2_diff : |q2 T1 - q2 T2| ≤ δ / 100 := by
      have h1 : |q2 T1 - (cpos T1).2| ≤ s / 2 := (hcpos_spec T1 hT1).2.2
      have h2 : |q2 T2 - (cpos T2).2| ≤ s / 2 := (hcpos_spec T2 hT2).2.2
      have h_e : |q2 T1 - q2 T2| ≤ |q2 T1 - (cpos T1).2| + |(cpos T1).2 - q2 T2| := abs_sub_le _ _ _
      have h_rew : |(cpos T1).2 - q2 T2| = |q2 T2 - (cpos T2).2| := by
        calc |(cpos T1).2 - q2 T2|
          = |q2 T2 - (cpos T1).2| := by rw [abs_sub_comm]
        _ = |q2 T2 - (cpos T2).2| := by rw [h_cpos_eq]
      rw [h_rew] at h_e
      have h_sum : |q2 T1 - (cpos T1).2| + |q2 T2 - (cpos T2).2| ≤ s := by
        calc |q2 T1 - (cpos T1).2| + |q2 T2 - (cpos T2).2|
          ≤ s / 2 + s / 2 := by gcongr
        _ = s := by ring
      have h_s : s ≤ δ / 100 := by rw [hs_def] <;> linarith
      linarith

    have h_t0_diff : |t0 T1 - t0 T2| ≤ 1 / 8 := by
      have h1 : |t0 T1 - cparam T1| ≤ 1 / 16 := (hcparam_spec T1 hT1).2
      have h2 : |t0 T2 - cparam T2| ≤ 1 / 16 := (hcparam_spec T2 hT2).2
      have h_e : |t0 T1 - t0 T2| ≤ |t0 T1 - cparam T1| + |cparam T1 - t0 T2| := abs_sub_le _ _ _
      have h_rew : |cparam T1 - t0 T2| = |t0 T2 - cparam T2| := by
        calc |cparam T1 - t0 T2|
          = |t0 T2 - cparam T1| := by rw [abs_sub_comm]
        _ = |t0 T2 - cparam T2| := by rw [h_cparam_eq]
      rw [h_rew] at h_e
      have h_sum : |t0 T1 - cparam T1| + |t0 T2 - cparam T2| ≤ 1 / 8 := by
        have h : |t0 T1 - cparam T1| + |t0 T2 - cparam T2| ≤ 1 / 16 + 1 / 16 := by gcongr
        have h2 : (1 / 16 : ℝ) + (1 / 16 : ℝ) = 1 / 8 := by norm_num
        rw [h2] at h
        exact h
      exact le_trans h_e h_sum

    have h_du1_diff : |du1 T1 - du1 T2| ≤ δ / 100 := by
      have h1 : |du1 T1 - (cdir T1).1| ≤ s / 2 := (hcdir_spec T1 hT1).2.1
      have h2 : |du1 T2 - (cdir T2).1| ≤ s / 2 := (hcdir_spec T2 hT2).2.1
      have h_e : |du1 T1 - du1 T2| ≤ |du1 T1 - (cdir T1).1| + |(cdir T1).1 - du1 T2| := abs_sub_le _ _ _
      have h_rew : |(cdir T1).1 - du1 T2| = |du1 T2 - (cdir T2).1| := by
        calc |(cdir T1).1 - du1 T2|
          = |du1 T2 - (cdir T1).1| := by rw [abs_sub_comm]
        _ = |du1 T2 - (cdir T2).1| := by rw [h_cdir_eq]
      rw [h_rew] at h_e
      have h_sum : |du1 T1 - (cdir T1).1| + |du1 T2 - (cdir T2).1| ≤ s := by
        calc |du1 T1 - (cdir T1).1| + |du1 T2 - (cdir T2).1|
          ≤ s / 2 + s / 2 := by gcongr
        _ = s := by ring
      have h_s : s ≤ δ / 100 := by rw [hs_def] <;> linarith
      linarith

    have h_du2_diff : |du2 T1 - du2 T2| ≤ δ / 100 := by
      have h1 : |du2 T1 - (cdir T1).2| ≤ s / 2 := (hcdir_spec T1 hT1).2.2
      have h2 : |du2 T2 - (cdir T2).2| ≤ s / 2 := (hcdir_spec T2 hT2).2.2
      have h_e : |du2 T1 - du2 T2| ≤ |du2 T1 - (cdir T1).2| + |(cdir T1).2 - du2 T2| := abs_sub_le _ _ _
      have h_rew : |(cdir T1).2 - du2 T2| = |du2 T2 - (cdir T2).2| := by
        calc |(cdir T1).2 - du2 T2|
          = |du2 T2 - (cdir T1).2| := by rw [abs_sub_comm]
        _ = |du2 T2 - (cdir T2).2| := by rw [h_cdir_eq]
      rw [h_rew] at h_e
      have h_sum : |du2 T1 - (cdir T1).2| + |du2 T2 - (cdir T2).2| ≤ s := by
        calc |du2 T1 - (cdir T1).2| + |du2 T2 - (cdir T2).2|
          ≤ s / 2 + s / 2 := by gcongr
        _ = s := by ring
      have h_s : s ≤ δ / 100 := by rw [hs_def] <;> linarith
      linarith

    have h_plane_eq' : plane_idx T1 = plane_idx T2 := h_plane_eq
    have h_not_distinct : ¬ T1.EssentiallyDistinct T2 :=
      h_close T1 T2 hT1 hT2 h_plane_eq' h_q1_diff h_q2_diff h_t0_diff h_du1_diff h_du2_diff
    by_cases h : T1 = T2
    · exact h
    · exfalso
      exact h_not_distinct (hdistinct hT1 hT2 h)

  have h_image_card : (F.image f).card = F.card :=
    Finset.card_image_of_injOn h_inj
  have h_image_subset : F.image f ⊆ cellPairs := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨T, hT, rfl⟩
    exact h_f_in_cells T hT
  have h_card_le : F.card ≤ cellPairs.card := by
    rw [←h_image_card]
    exact Finset.card_le_card h_image_subset

  have h_cellPairs_card : cellPairs.card = K * cells_pos.card * cells_t0.card * cells_dir.card := by
    have h1 : cellPairs.card = ((cells_plane ×ˢ cells_pos) ×ˢ cells_t0).card * cells_dir.card :=
      Finset.card_product _ _
    have h2 : ((cells_plane ×ˢ cells_pos) ×ˢ cells_t0).card =
        (cells_plane ×ˢ cells_pos).card * cells_t0.card := Finset.card_product _ _
    have h3 : (cells_plane ×ˢ cells_pos).card = cells_plane.card * cells_pos.card :=
      Finset.card_product _ _
    have h4 : cells_plane.card = K := by simp [cells_plane]
    rw [h1, h2, h3, h4] <;> ring

  rw [h_cellPairs_card] at h_card_le

  have h_pos_bound : (cells_pos.card : ℝ) ≤ (200 * R1 / δ + 2) * (200 * R2 / δ + 2) := by
    have h : (cells_pos.card : ℝ) ≤ ((R1 - -R1) / s + 2) * ((R2 - -R2) / s + 2) := hcard_pos
    have h1 : (R1 - -R1) / s = 200 * R1 / δ := by
      rw [hs_def]
      rw [div_div_eq_mul_div] <;> ring
    have h2 : (R2 - -R2) / s = 200 * R2 / δ := by
      rw [hs_def]
      rw [div_div_eq_mul_div] <;> ring
    rw [h1, h2] at h
    exact h

  have h_dir_bound : (cells_dir.card : ℝ) ≤ (200 * D1 / δ + 2) * (200 * D2 / δ + 2) := by
    have h : (cells_dir.card : ℝ) ≤ ((D1 - -D1) / s + 2) * ((D2 - -D2) / s + 2) := hcard_dir
    have h1 : (D1 - -D1) / s = 200 * D1 / δ := by
      rw [hs_def]
      rw [div_div_eq_mul_div] <;> ring
    have h2 : (D2 - -D2) / s = 200 * D2 / δ := by
      rw [hs_def]
      rw [div_div_eq_mul_div] <;> ring
    rw [h1, h2] at h
    exact h

  have h_main : (F.card : ℝ) ≤
      (K : ℝ) * (200 * R1 / δ + 2) * (200 * R2 / δ + 2) * 8 * (200 * D1 / δ + 2) * (200 * D2 / δ + 2) := by
    let cp : ℝ := (cells_pos.card : ℝ)
    let ct : ℝ := (cells_t0.card : ℝ)
    let cd : ℝ := (cells_dir.card : ℝ)
    let P : ℝ := (200 * R1 / δ + 2) * (200 * R2 / δ + 2)
    let D : ℝ := (200 * D1 / δ + 2) * (200 * D2 / δ + 2)
    have h6_raw : (F.card : ℝ) ≤ (K : ℝ) * (cells_pos.card : ℝ) * (cells_t0.card : ℝ) * (cells_dir.card : ℝ) := by
      exact_mod_cast h_card_le
    have h6 : (F.card : ℝ) ≤ (K : ℝ) * cp * ct * cd := by
      have hcp : cp = (cells_pos.card : ℝ) := by rfl
      have hct : ct = (cells_t0.card : ℝ) := by rfl
      have hcd : cd = (cells_dir.card : ℝ) := by rfl
      rw [hcp, hct, hcd]
      exact h6_raw
    have h_pos : cp ≤ P := h_pos_bound
    have h_dir : cd ≤ D := h_dir_bound
    have h_t0 : ct ≤ 8 := hcard_t0
    have hK : 0 ≤ (K : ℝ) := by positivity
    calc (F.card : ℝ)
      ≤ (K : ℝ) * cp * ct * cd := h6
    _ ≤ (K : ℝ) * P * ct * cd := by gcongr
    _ ≤ (K : ℝ) * P * 8 * cd := by gcongr
    _ ≤ (K : ℝ) * P * 8 * D := by gcongr
    _ = (K : ℝ) * (200 * R1 / δ + 2) * (200 * R2 / δ + 2) * 8 * (200 * D1 / δ + 2) * (200 * D2 / δ + 2) := by
        simp only [P, D] <;> ring

  set B : ℝ := (K : ℝ) * (200 * R1 / δ + 2) * (200 * R2 / δ + 2) * 8 * (200 * D1 / δ + 2) * (200 * D2 / δ + 2) with hB_def
  have h_nonneg : 0 ≤ B := by positivity
  have h_final : F.enncard ≤ ENNReal.ofReal B := by
    have h1 : F.enncard = (F.card : ENNReal) := by rfl
    rw [h1]
    have h2 : (F.card : ENNReal) ≤ ENNReal.ofReal B := by
      have h3 : (F.card : ℝ) ≤ B := h_main
      have h4 : 0 ≤ (F.card : ℝ) := by positivity
      have h5 : (F.card : ENNReal) = ENNReal.ofReal (F.card : ℝ) := by
        have h6 : ∀ (n : ℕ), (n : ENNReal) = ENNReal.ofReal (n : ℝ) := by
          intro n
          simp
        exact h6 F.card
      rw [h5]
      exact ENNReal.ofReal_le_ofReal h3
    exact h2
  exact h_final

end Kakeya.Streamlined.GeometricLemmas
