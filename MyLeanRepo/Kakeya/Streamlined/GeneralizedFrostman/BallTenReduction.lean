import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.TranslateTubeGeometry
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.DeterministicHelpers
import MyLeanRepo.Kakeya.Streamlined.Estimates
import MyLeanRepo.Kakeya.Streamlined.TubeRefinement
import MyLeanRepo.Kakeya.Streamlined.GeneralizedFrostman.RigidMotion
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option linter.constructorNameAsVariable false

/-!
# Reduction from `B₁₀` to the unit ball via a finite grid partition

Cover `B₁₀` with a finite grid of radius-`1/2` balls. Assign each tube to a
cell by its midpoint, then rigidly translate that cell by `-c` into the unit
ball. Pick the heaviest cell to retain at least `1/41³` of the shading mass.

## Main results

- `ballTen_cellReduction`: extract a unit-ball subfamily with mass retention.
-/

noncomputable section

open Classical MeasureTheory Kakeya.Streamlined Kakeya.Streamlined.RandomTranslation

namespace Kakeya.Streamlined.GeneralizedFrostman

/-! ### Midpoint geometric lemma -/

/-- Midpoint of a δ-tube's unit segment. -/
def tubeMidpoint {δ : ℝ} (T : Kakeya.DeltaTube δ) : Point3 :=
  T.base + (1 / 2 : ℝ) • T.direction

/-- The midpoint of a tube lies in its carrier. -/
lemma tubeMidpoint_in_carrier {δ : ℝ} (T : Kakeya.DeltaTube δ) (hδ : 0 ≤ δ) :
    tubeMidpoint T ∈ T.carrier := by
  have h1 : tubeMidpoint T ∈ unitSegment T.base T.direction := by
    refine ⟨1 / 2, by norm_num, ?_⟩
    simp [tubeMidpoint]
  have h2 : unitSegment T.base T.direction ⊆ T.carrier :=
    Metric.self_subset_cthickening (unitSegment T.base T.direction)
  exact h2 h1

/-- A δ-tube carrier is contained in `Ball(midpoint, 1/2 + δ)`. -/
lemma tube_carrier_subset_ball_midpoint {δ : ℝ} (T : Kakeya.DeltaTube δ)
    (hδ : 0 ≤ δ) :
    T.carrier ⊆ Metric.closedBall (tubeMidpoint T) (1 / 2 + δ) := by
  intro x hx
  let s := unitSegment T.base T.direction
  have hs_compact : IsCompact s := by
    have h_eq : s = (fun t : ℝ => T.base + t • T.direction) '' Set.Icc (0 : ℝ) 1 := by
      ext y; simp [s, unitSegment]
    rw [h_eq]
    exact IsCompact.image isCompact_Icc (by fun_prop)
  have hs_nonempty : s.Nonempty := ⟨T.base, ⟨0, by norm_num, by simp⟩⟩
  have h1 : Metric.infEDist x s ≤ ENNReal.ofReal δ := by
    simpa [DeltaTube.carrier, Metric.mem_cthickening_iff] using hx
  rcases hs_compact.exists_infEDist_eq_edist hs_nonempty x with ⟨y, hy, h_eq⟩
  have h2 : edist x y ≤ ENNReal.ofReal δ := by
    rw [←h_eq]; exact h1
  have h3 : edist x y = ENNReal.ofReal (dist x y) := edist_dist x y
  rw [h3] at h2
  have h_dist : dist x y ≤ δ :=
    (ENNReal.ofReal_le_ofReal_iff hδ).mp h2
  rcases hy with ⟨t, ht, rfl⟩
  have h4 : ‖(T.base + t • T.direction) - tubeMidpoint T‖ ≤ 1 / 2 := by
    have h5 : (T.base + t • T.direction) - tubeMidpoint T =
        (t - 1 / 2 : ℝ) • T.direction := by
      simp [tubeMidpoint, sub_smul] <;> abel
    rw [h5, norm_smul, T.direction_unit]
    have h6 : |t - 1 / 2| ≤ 1 / 2 := by
      rw [abs_le] <;> constructor <;> linarith [ht.1, ht.2]
    have h7 : ‖(t - 1 / 2 : ℝ)‖ = |t - 1 / 2| := by
      simp [Real.norm_eq_abs]
    rw [h7, mul_one]
    exact h6
  have h5 : dist x (tubeMidpoint T) ≤
      dist x (T.base + t • T.direction) + dist (T.base + t • T.direction) (tubeMidpoint T) :=
    dist_triangle _ _ _
  have h6 : dist (T.base + t • T.direction) (tubeMidpoint T) ≤ 1 / 2 := by
    simpa [dist_eq_norm] using h4
  have h7 : dist x (tubeMidpoint T) ≤ 1 / 2 + δ := by linarith
  simpa [Metric.mem_closedBall] using h7

/-! ### Grid covering B₁₀ -/

/-- A grid center from integer indices in `{0, ..., 40}`. -/
def gridCenter (i j k : ℕ) : Point3 :=
  EuclideanSpace.single 0 ((i : ℝ) / 2 - 10) +
  EuclideanSpace.single 1 ((j : ℝ) / 2 - 10) +
  EuclideanSpace.single 2 ((k : ℝ) / 2 - 10)

/-- The finite grid of at most `41³` centers covering `B₁₀`. -/
def ballTenGrid : Finset Point3 :=
  (Finset.univ : Finset (Fin 41 × Fin 41 × Fin 41)).image fun p =>
    gridCenter p.1 p.2.1 p.2.2

/-- Number of grid centers is at most `41³`. -/
lemma ballTenGrid_card_le : ballTenGrid.card ≤ 41 ^ 3 := by
  calc
    ballTenGrid.card ≤ (Finset.univ : Finset (Fin 41 × Fin 41 × Fin 41)).card :=
      Finset.card_image_le
    _ = 41 ^ 3 := by norm_num

/-- Membership helper: any `(i,j,k)` with `i,j,k < 41` gives a grid center. -/
lemma ballTenGrid_mem (i j k : ℕ) (hi : i < 41) (hj : j < 41) (hk : k < 41) :
    gridCenter i j k ∈ ballTenGrid := by
  apply Finset.mem_image.mpr
  exact ⟨(⟨i, hi⟩, ⟨j, hj⟩, ⟨k, hk⟩), Finset.mem_univ _, rfl⟩

/-- Coordinate bound: `|x i| ≤ ‖x‖`. -/
private lemma euclidean_coord_bound (x : Point3) (i : Fin 3) : |x i| ≤ ‖x‖ := by
  have h_norm_sq : ‖x‖ ^ 2 = ∑ j : Fin 3, (x j) ^ 2 :=
    EuclideanSpace.real_norm_sq_eq x
  have h3 : (x i) ^ 2 ≤ ∑ j : Fin 3, (x j) ^ 2 := by
    exact Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
  have h5 : (x i) ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [h_norm_sq]; exact h3
  exact abs_le_of_sq_le_sq h5 (norm_nonneg x)

/-- Every point in `B₁₀` is within `√3/4` of some grid center. -/
lemma ballTenGrid_cover (x : Point3) (hx : x ∈ Metric.closedBall (0 : Point3) 10) :
    ∃ (c : Point3), c ∈ ballTenGrid ∧ ‖x - c‖ ≤ Real.sqrt 3 / 4 := by
  have h_coord : ∀ (i : Fin 3), |x i| ≤ 10 := by
    intro i
    have h1 : |x i| ≤ ‖x‖ := euclidean_coord_bound x i
    have h2 : ‖x‖ ≤ 10 := by simpa [Metric.mem_closedBall] using hx
    linarith
  have h_main : ∀ (i : Fin 3), ∃ (n : ℕ), n < 41 ∧
      |x i - ((n : ℝ) / 2 - 10)| ≤ 1 / 4 := by
    intro i
    have h_i : |x i| ≤ 10 := h_coord i
    set y : ℝ := 2 * (x i + 10) with hy_def
    have hy0 : 0 ≤ y := by rw [hy_def]; linarith [abs_le.mp h_i]
    have hy40 : y ≤ 40 := by rw [hy_def]; linarith [abs_le.mp h_i]
    let k : ℤ := ⌊y + 1 / 2⌋
    have hk1 : (k : ℝ) ≤ y + 1 / 2 := Int.floor_le _
    have hk2 : y + 1 / 2 < (k : ℝ) + 1 := Int.lt_floor_add_one _
    have hk_nonneg : 0 ≤ k := by
      apply Int.floor_nonneg.mpr
      have h_pos : 0 ≤ y + 1 / 2 := by linarith
      exact h_pos
    let n : ℕ := k.toNat
    have hkn : (n : ℝ) = (k : ℝ) := by
      have h : (n : ℤ) = k := Int.toNat_of_nonneg hk_nonneg
      exact_mod_cast h
    have h_n3 : n < 41 := by
      have h : (n : ℝ) ≤ 40 + 1 / 2 := by linarith
      have h' : n ≤ 40 := by
        by_contra h10
        have h11 : n ≥ 41 := by omega
        have h12 : (n : ℝ) ≥ 41 := by exact_mod_cast h11
        linarith
      omega
    have h_final : |x i - ((n : ℝ) / 2 - 10)| ≤ 1 / 4 := by
      have h_eq : x i - ((n : ℝ) / 2 - 10) = (y - (n : ℝ)) / 2 := by
        simp [hy_def] <;> ring
      rw [h_eq]
      have h_abs : |y - (n : ℝ)| ≤ 1 / 2 := by
        rw [abs_le] <;> constructor <;> linarith
      have h : |(y - (n : ℝ)) / 2| = |y - (n : ℝ)| / 2 := by
        rw [abs_div] <;> norm_num
      rw [h]; linarith
    exact ⟨n, h_n3, h_final⟩
  choose n hn using h_main
  let c : Point3 := gridCenter (n 0) (n 1) (n 2)
  have hc_in : c ∈ ballTenGrid :=
    ballTenGrid_mem (n 0) (n 1) (n 2) (hn 0).1 (hn 1).1 (hn 2).1
  have h_dist : ‖x - c‖ ≤ Real.sqrt 3 / 4 := by
    have h1 : ‖x - c‖ ^ 2 = ∑ i : Fin 3, |(x - c) i| ^ 2 := by
      simpa [EuclideanSpace.real_norm_sq_eq] using EuclideanSpace.real_norm_sq_eq (x - c)
    have h2 : ∀ i : Fin 3, |(x - c) i| ≤ 1 / 4 := by
      intro i
      have h_ci : c i = (n i : ℝ) / 2 - 10 := by
        fin_cases i <;> simp [c, gridCenter, EuclideanSpace.single_apply] <;> rfl
      have h_eq : (x - c) i = x i - c i := by rfl
      rw [h_eq, h_ci]
      exact (hn i).2
    have h3 : ∑ i : Fin 3, |(x - c) i| ^ 2 ≤ ∑ i : Fin 3, (1 / 4 : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have h4 : |(x - c) i| ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := by
        gcongr <;> linarith [h2 i]
      exact h4
    have h4 : ∑ i : Fin 3, (1 / 4 : ℝ) ^ 2 = 3 / 16 := by norm_num
    have h5 : ‖x - c‖ ^ 2 ≤ 3 / 16 := by
      rw [h1]; exact h3.trans (by rw [h4])
    have h6 : 0 ≤ ‖x - c‖ := by positivity
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  exact ⟨c, hc_in, h_dist⟩

/-! ### Helper lemmas -/

/-- Shading mass is always finite. -/
lemma shading_mass_ne_top {δ : ℝ} {F : TubeFamily δ} (Y : TubeShading F) :
    Y.mass ≠ ⊤ := by
  dsimp only [Shading.mass]
  rw [ENNReal.sum_ne_top]
  intro i _
  have h : volume (Y.carrier i) ≤ (F.tube i).volume := measure_mono (Y.subset_body i)
  have h' : (F.tube i).volume ≠ ⊤ := by
    have h_eq : (F.tube i).volume = Kakeya.deltaTubeVolume δ :=
      tube_volume_eq_deltaTubeVolume (F.tube i)
    rw [h_eq]
    exact deltaTubeVolume_ne_top
  exact ne_top_of_le_ne_top h' h

/-- Pigeonhole: some element of a nonempty finset has ENNReal value ≥ average. -/
private lemma pigeonhole_ennreal {α : Type*} {s : Finset α} {f : α → ENNReal}
    (hs : s.Nonempty) (hfin : ∑ x ∈ s, f x ≠ ⊤) :
    ∃ x ∈ s, f x ≥ (∑ x ∈ s, f x) / (s.card : ENNReal) := by
  let S := ∑ x ∈ s, f x
  let N := (s.card : ENNReal)
  have hN : N ≠ 0 := by
    have h : 0 < s.card := Finset.card_pos.mpr hs
    simp [N, h.ne'] <;> omega
  have hS : S ≠ ⊤ := hfin
  rcases Finset.exists_max_image s f hs with ⟨x, hx, hmax⟩
  have h1 : S ≤ N * f x := by
    calc S
      = ∑ y ∈ s, f y := by rfl
    _ ≤ ∑ y ∈ s, f x := Finset.sum_le_sum (fun y hy => hmax y hy)
    _ = N * f x := by
      have h_sum : ∑ y ∈ s, f x = (s.card : ENNReal) * f x := by
        rw [Finset.sum_const]
        <;> simp [nsmul_eq_mul] <;> rfl
      rw [h_sum] <;> rfl
  have hfx : f x ≠ ⊤ := by
    have h2 : f x ≤ S := Finset.single_le_sum (fun _ _ => by positivity) hx
    exact ne_top_of_le_ne_top hS h2
  have h_mult : S ≤ f x * N := by
    rw [mul_comm]; exact h1
  have h_final : S / N ≤ f x := ENNReal.div_le_of_le_mul h_mult
  exact ⟨x, hx, h_final⟩

private lemma fiber_partition_cover
    {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]
    (s : Finset β) (f : α → β) (hf : ∀ x, f x ∈ s) :
    Finset.biUnion s (fun c => Finset.univ.filter (fun x => f x = c)) =
      Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro x
  apply Finset.mem_biUnion.mpr
  exact ⟨f x, hf x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩

/-! ### Heavy cell reduction -/

/-- There exists a grid cell whose translated subfamily lies in the unit ball
and retains at least `1/41³` of the shading mass. -/
theorem ballTen_cellReduction {δ : ℝ} {G : TubeFamily δ}
    (hδ_pos : 0 < δ) (hδ_small : δ ≤ 1 / 2 - Real.sqrt 3 / 4)
    (hG_ball : ∀ i, (G.tube i).carrier ⊆ Metric.closedBall (0 : Point3) 10)
    (hG_distinct : G.IsEssentiallyDistinct)
    (Y : TubeShading G) :
    ∃ (S : TubeFamily δ) (Y' : TubeShading S)
      (e : Point3 ≃ₗᵢ[ℝ] Point3) (t : Point3),
      S.IsInUnitBall ∧
      S.IsEssentiallyDistinct ∧
      S.enncard ≤ G.enncard ∧
      Y'.mass ≥ Y.mass / (41 ^ 3 : ENNReal) ∧
      volume Y'.union ≤ volume Y.union ∧
      S.toBodyFamily.deltaMax ≤ G.toBodyFamily.deltaMax := by
  have hδ : 0 ≤ δ := by linarith
  -- Assign each tube to a grid center near its midpoint
  have h_cover : ∀ (i : Fin G.card), ∃ (c : Point3), c ∈ ballTenGrid ∧
      tubeMidpoint (G.tube i) ∈ Metric.closedBall c (1 / 2 - δ) := by
    intro i
    have h_mid_in : tubeMidpoint (G.tube i) ∈ Metric.closedBall (0 : Point3) 10 :=
      (hG_ball i) (tubeMidpoint_in_carrier (G.tube i) hδ)
    rcases ballTenGrid_cover (tubeMidpoint (G.tube i)) h_mid_in with ⟨c, hc_in, h_dist⟩
    have h3 : Real.sqrt 3 / 4 ≤ 1 / 2 - δ := by linarith
    have h4 : dist (tubeMidpoint (G.tube i)) c ≤ 1 / 2 - δ := by
      have h5 : dist (tubeMidpoint (G.tube i)) c = ‖tubeMidpoint (G.tube i) - c‖ := by
        rw [dist_eq_norm]
      rw [h5]; exact le_trans h_dist h3
    exact ⟨c, hc_in, by simpa [Metric.mem_closedBall] using h4⟩
  choose chooseCell hc1 hc2 using h_cover
  let I (c : Point3) : Finset (Fin G.card) :=
    Finset.univ.filter (fun i => chooseCell i = c)
  have hI_mem : ∀ c i, i ∈ I c ↔ chooseCell i = c := by
    intro c i; simp [I]
  have h_disj : ∀ c1 ∈ ballTenGrid, ∀ c2 ∈ ballTenGrid, c1 ≠ c2 → Disjoint (I c1) (I c2) := by
    intro c1 _ c2 _ hne
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    have h3 : chooseCell i = c1 := (hI_mem c1 i).mp hi1
    have h4 : chooseCell i = c2 := (hI_mem c2 i).mp hi2
    rw [h3] at h4
    exact hne h4
  have h_univ : Finset.biUnion ballTenGrid I = (Finset.univ : Finset (Fin G.card)) := by
    exact fiber_partition_cover ballTenGrid chooseCell hc1
  have h_partition : ∑ c ∈ ballTenGrid, ∑ i ∈ I c, volume (Y.carrier i) = Y.mass := by
    rw [←Finset.sum_biUnion h_disj, h_univ]
    <;> rfl
  have h_card_pos : 0 < ballTenGrid.card := by
    have h_nonempty : ballTenGrid.Nonempty := by
      refine ⟨gridCenter 0 0 0, ballTenGrid_mem 0 0 0 (by norm_num) (by norm_num) (by norm_num)⟩
    exact Finset.card_pos.mpr h_nonempty
  have h_mass_fin : Y.mass ≠ ⊤ := shading_mass_ne_top Y
  have h_sum_fin : (∑ c ∈ ballTenGrid, ∑ i ∈ I c, volume (Y.carrier i)) ≠ ⊤ := by
    rw [h_partition]
    exact h_mass_fin
  let cellMass : Point3 → ENNReal := fun c => ∑ i ∈ I c, volume (Y.carrier i)
  have h_pigeon : ∃ c ∈ ballTenGrid, cellMass c ≥ (∑ x ∈ ballTenGrid, cellMass x) / (ballTenGrid.card : ENNReal) :=
    pigeonhole_ennreal (f := cellMass) (Finset.card_pos.mp h_card_pos) h_sum_fin
  rcases h_pigeon with ⟨c, hc_in, h_ge⟩
  have h_sum_eq : (∑ x ∈ ballTenGrid, cellMass x) = Y.mass := h_partition
  have h_main : ∃ c ∈ ballTenGrid, cellMass c ≥ Y.mass / (ballTenGrid.card : ENNReal) := by
    rw [h_sum_eq] at h_ge
    exact ⟨c, hc_in, h_ge⟩
  rcases h_main with ⟨c, hc_in, h_mass_ge⟩
  let I_c := I c
  let S_B10 : TubeSubfamily G := TubeSubfamily.fromFinset G I_c
  -- Translate by -c
  let v : Point3 := -c
  let S : TubeFamily δ := translateTubeFamily S_B10.family v
  let Y_B10 : TubeShading S_B10.family := TubeSubfamily.restrictShading S_B10 Y
  let Y' : TubeShading S :=
    { carrier := fun i => translateSet (Y_B10.carrier i) v
      measurable_carrier := fun i => measurableSet_translateSet (Y_B10.measurable_carrier i) v
      subset_body := fun i => by
        have h_sub : Y_B10.carrier i ⊆ (S_B10.family.tube i).carrier := Y_B10.subset_body i
        have h1 : translateSet (Y_B10.carrier i) v ⊆ translateSet ((S_B10.family.tube i).carrier) v :=
          Set.image_mono h_sub
        have h2 : translateSet ((S_B10.family.tube i).carrier) v = (S.tube i).carrier :=
          (translateTube_carrier (S_B10.family.tube i) v).symm
        rw [h2] at h1
        exact h1 }
  -- Properties
  have hS_unit : S.IsInUnitBall := by
    intro i
    have h5 : S_B10.embedding i ∈ I_c := by
      have h6 : S_B10.embedding = (I_c.orderEmbOfFin rfl).toEmbedding := by rfl
      rw [h6]
      exact Finset.orderEmbOfFin_mem I_c rfl i
    have h7 : chooseCell (S_B10.embedding i) = c := (hI_mem c _).mp h5
    have h_mid_near : tubeMidpoint (S_B10.family.tube i) ∈ Metric.closedBall c (1 / 2 - δ) := by
      have h8 : tubeMidpoint (G.tube (S_B10.embedding i)) ∈ Metric.closedBall (chooseCell (S_B10.embedding i)) (1 / 2 - δ) :=
        hc2 (S_B10.embedding i)
      rw [h7] at h8
      have h9 : S_B10.family.tube i = G.tube (S_B10.embedding i) := S_B10.tube_eq i
      rw [h9]
      exact h8
    have h_tube_sub : (S_B10.family.tube i).carrier ⊆ Metric.closedBall c 1 := by
      have h7 : (S_B10.family.tube i).carrier ⊆
          Metric.closedBall (tubeMidpoint (S_B10.family.tube i)) (1 / 2 + δ) :=
        tube_carrier_subset_ball_midpoint (S_B10.family.tube i) hδ
      intro x hx
      have h8 : dist x (tubeMidpoint (S_B10.family.tube i)) ≤ 1 / 2 + δ := h7 hx
      have h9 : dist (tubeMidpoint (S_B10.family.tube i)) c ≤ 1 / 2 - δ := by
        simpa [Metric.mem_closedBall] using h_mid_near
      have h10 : dist x c ≤ 1 := by
        calc dist x c
          ≤ dist x (tubeMidpoint (S_B10.family.tube i)) + dist (tubeMidpoint (S_B10.family.tube i)) c := dist_triangle _ _ _
        _ ≤ (1 / 2 + δ) + (1 / 2 - δ) := by gcongr
        _ = 1 := by ring
      simpa [Metric.mem_closedBall] using h10
    have h_trans : (S.tube i).carrier = translateSet ((S_B10.family.tube i).carrier) v :=
      translateTube_carrier (S_B10.family.tube i) v
    have h_main : (S.tube i).carrier ⊆ Kakeya.DeltaTube.unitBall := by
      rw [h_trans]
      intro x hx
      rcases hx with ⟨y, hy, rfl⟩
      have h11 : dist y c ≤ 1 := by
        simpa [Metric.mem_closedBall] using h_tube_sub hy
      have h12 : dist (y + v) (0 : Point3) ≤ 1 := by
        have h13 : y + v = y - c := by
          simp [v] <;> abel
        rw [h13]
        simpa [dist_eq_norm] using h11
      simpa [Kakeya.DeltaTube.unitBall, Metric.mem_closedBall] using h12
    simpa [DeltaTube.IsInUnitBall] using h_main
  have hS_distinct : S.IsEssentiallyDistinct := by
    have h1 : S_B10.family.IsEssentiallyDistinct := TubeSubfamily.isEssentiallyDistinct S_B10 hG_distinct
    exact translateFamily_essentiallyDistinct h1
  have hS_card_le : S.enncard ≤ G.enncard := by
    have h1 : S.enncard = S_B10.family.enncard := by rfl
    rw [h1]
    have h2 : S_B10.family.enncard = (I_c.card : ENNReal) := by
      simp [S_B10, TubeSubfamily.fromFinset, TubeFamily.enncard]
    rw [h2]
    have h3 : (I_c.card : ENNReal) ≤ (G.card : ENNReal) := by
      have h4 : I_c.card ≤ G.card := by
        have h5 : I_c ⊆ (Finset.univ : Finset (Fin G.card)) := Finset.subset_univ I_c
        have h6 := Finset.card_le_card h5
        simpa using h6
      exact_mod_cast h4
    simpa [TubeFamily.enncard] using h3
  have hY'_mass_ge : Y'.mass ≥ Y.mass / (41 ^ 3 : ENNReal) := by
    have h_vol_trans : ∀ i, volume (translateSet (Y_B10.carrier i) v) = volume (Y_B10.carrier i) := by
      intro i
      exact volume_translateSet (Y_B10.measurable_carrier i) v
    have h1 : Y'.mass = ∑ i ∈ I_c, volume (Y.carrier i) := by
      dsimp only [Y', Shading.mass]
      have h_step1 : (∑ i : Fin S_B10.family.card, volume (translateSet (Y_B10.carrier i) v)) =
          ∑ i : Fin S_B10.family.card, volume (Y_B10.carrier i) := by
        apply Finset.sum_congr rfl
        intro i _
        exact h_vol_trans i
      have h_step2 : (∑ i : Fin S_B10.family.card, volume (Y_B10.carrier i)) =
          ∑ i : Fin S_B10.family.card, volume (Y.carrier (S_B10.embedding i)) := by
        apply Finset.sum_congr rfl
        intro i _
        rfl
      let e : (Fin S_B10.family.card) ↪ (Fin G.card) := S_B10.embedding
      have h_eq1 : e = (I_c.orderEmbOfFin rfl).toEmbedding := by rfl
      have h_map : Finset.map e (Finset.univ : Finset (Fin S_B10.family.card)) = I_c := by
        rw [h_eq1]
        exact Finset.map_orderEmbOfFin_univ I_c rfl
      have h_sum_map : ∑ j ∈ Finset.map e (Finset.univ : Finset (Fin S_B10.family.card)),
          volume (Y.carrier j) =
          ∑ i : Fin S_B10.family.card, volume (Y.carrier (e i)) :=
        Finset.sum_map (Finset.univ) e (fun j => volume (Y.carrier j))
      have h_step3 : (∑ i : Fin S_B10.family.card, volume (Y.carrier (e i))) =
          ∑ j ∈ I_c, volume (Y.carrier j) := by
        calc
          ∑ i : Fin S_B10.family.card, volume (Y.carrier (e i))
            = ∑ j ∈ Finset.map e (Finset.univ : Finset (Fin S_B10.family.card)),
                volume (Y.carrier j) := h_sum_map.symm
          _ = ∑ j ∈ I_c, volume (Y.carrier j) := by rw [h_map]
      calc
        (∑ i : Fin S_B10.family.card, volume (translateSet (Y_B10.carrier i) v))
          = ∑ i : Fin S_B10.family.card, volume (Y_B10.carrier i) := h_step1
        _ = ∑ i : Fin S_B10.family.card, volume (Y.carrier (S_B10.embedding i)) := h_step2
        _ = ∑ i : Fin S_B10.family.card, volume (Y.carrier (e i)) := by rfl
        _ = ∑ j ∈ I_c, volume (Y.carrier j) := h_step3
    rw [h1]
    have h3 : (∑ i ∈ I_c, volume (Y.carrier i)) ≥ Y.mass / (ballTenGrid.card : ENNReal) := h_mass_ge
    have h4 : (ballTenGrid.card : ENNReal) ≤ (41 ^ 3 : ENNReal) := by
      exact_mod_cast ballTenGrid_card_le
    have h5 : Y.mass / (ballTenGrid.card : ENNReal) ≥ Y.mass / (41 ^ 3 : ENNReal) := by
      gcongr
    exact le_trans h5 h3
  have hY'_union_le : volume Y'.union ≤ volume Y.union := by
    have h1 : Y'.union = translateSet Y_B10.union v := by
      ext x
      simp only [Y', Shading.union, translateSet, Set.mem_image, Set.mem_setOf_eq]
      constructor
      · rintro ⟨i, y, hy, rfl⟩
        exact ⟨y, ⟨i, hy⟩, rfl⟩
      · rintro ⟨y, ⟨i, hy⟩, rfl⟩
        exact ⟨i, y, hy, rfl⟩
    rw [h1]
    have h_meas : MeasurableSet Y_B10.union := by
      have h_union_def : Y_B10.union = ⋃ i : Fin S_B10.family.card, Y_B10.carrier i := by
        ext z
        simp [Shading.union]
        <;> rfl
      rw [h_union_def]
      exact MeasurableSet.iUnion (fun i => Y_B10.measurable_carrier i)
    have h2 : volume (translateSet Y_B10.union v) = volume Y_B10.union :=
      volume_translateSet h_meas v
    rw [h2]
    have h3 : Y_B10.union ⊆ Y.union := by
      intro x hx
      rcases hx with ⟨i, hi⟩
      exact ⟨S_B10.embedding i, hi⟩
    exact measure_mono h3
  have hdeltaMax_le : S.toBodyFamily.deltaMax ≤ G.toBodyFamily.deltaMax := by
    let e_id : Point3 ≃ₗᵢ[ℝ] Point3 := LinearIsometryEquiv.refl ℝ Point3
    have h_body_eq : S.toBodyFamily.body = (rigidMoveBodyFamily S_B10.family.toBodyFamily e_id v).body := by
      funext i
      have h_carrier : (S.toBodyFamily.body i).carrier =
          ((rigidMoveBodyFamily S_B10.family.toBodyFamily e_id v).body i).carrier := by
        have h_a : (S.toBodyFamily.body i).carrier =
            translateSet (S_B10.family.toBodyFamily.body i).carrier v := by
          have h_tube : (S.toBodyFamily.body i).carrier = (translateTube (S_B10.family.tube i) v).carrier := by rfl
          rw [h_tube, translateTube_carrier]
          <;> rfl
        have h_b : ((rigidMoveBodyFamily S_B10.family.toBodyFamily e_id v).body i).carrier =
            translateSet (S_B10.family.toBodyFamily.body i).carrier v := by
          dsimp only [rigidMoveBodyFamily, rigidMoveBody]
          have h_rmap : rigidMoveMap e_id v = fun x : Point3 => x + v := by
            funext x; simp [rigidMoveMap, e_id] <;> abel
          rw [h_rmap]
          <;> rfl
        rw [h_a, h_b]
      exact congr_arg Body.mk h_carrier
    have h_family_eq : S.toBodyFamily = rigidMoveBodyFamily S_B10.family.toBodyFamily e_id v := by
      let B := rigidMoveBodyFamily S_B10.family.toBodyFamily e_id v
      have hb : S.toBodyFamily.body = B.body := h_body_eq
      exact congr_arg (fun b : Fin S.toBodyFamily.card → Body => BodyFamily.mk S.toBodyFamily.card b) hb
    rw [h_family_eq]
    have h2 : (rigidMoveBodyFamily S_B10.family.toBodyFamily e_id v).deltaMax =
        S_B10.family.toBodyFamily.deltaMax :=
      rigidMoveBodyFamily_deltaMax S_B10.family.toBodyFamily e_id v
        (tubeFamily_bodies_measurable S_B10.family)
    rw [h2]
    -- subfamily deltaMax ≤ parent deltaMax
    let B_sub : Subfamily G.toBodyFamily := S_B10.toBodySubfamily
    classical
    have h_sub_mass : ∀ (K : Set Point3),
        B_sub.family.containedMass K ≤ G.toBodyFamily.containedMass K := by
      intro K
      let I_sub := B_sub.family.containedIndices K
      let I_G := G.toBodyFamily.containedIndices K
      have h_inj : ∀ (x y : Fin B_sub.family.card),
          B_sub.embedding x = B_sub.embedding y → x = y :=
        fun x y h => B_sub.embedding.inj' h
      have h_emb : ∀ i ∈ I_sub, B_sub.embedding i ∈ I_G := by
        intro i hi
        have h7 : (B_sub.family.body i).carrier ⊆ K :=
          (Finset.mem_filter.mp hi).2
        have h8 : (G.toBodyFamily.body (B_sub.embedding i)).carrier ⊆ K := by
          rw [←B_sub.carrier_eq i]; exact h7
        have h9 : B_sub.embedding i ∈ I_G := by
          simp only [I_G, BodyFamily.containedIndices, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, h8⟩
        exact h9
      have h_vol : ∀ i ∈ I_sub, (B_sub.family.body i).volume =
          (G.toBodyFamily.body (B_sub.embedding i)).volume := by
        intro i _
        have h10 : (B_sub.family.body i).carrier = (G.toBodyFamily.body (B_sub.embedding i)).carrier :=
          B_sub.carrier_eq i
        rw [Body.volume, Body.volume, h10]
      have h_sum_map : ∑ j ∈ Finset.map B_sub.embedding I_sub,
          (G.toBodyFamily.body j).volume =
          ∑ i ∈ I_sub, (G.toBodyFamily.body (B_sub.embedding i)).volume :=
        Finset.sum_map I_sub B_sub.embedding (fun j => (G.toBodyFamily.body j).volume)
      have h_img_sub : Finset.map B_sub.embedding I_sub ⊆ I_G := by
        intro j hj
        rcases Finset.mem_map.mp hj with ⟨i, hi, rfl⟩
        exact h_emb i hi
      calc
        B_sub.family.containedMass K
          = ∑ i ∈ I_sub, (B_sub.family.body i).volume := by rfl
        _ = ∑ i ∈ I_sub, (G.toBodyFamily.body (B_sub.embedding i)).volume :=
          Finset.sum_congr rfl h_vol
        _ = ∑ j ∈ Finset.map B_sub.embedding I_sub, (G.toBodyFamily.body j).volume :=
          h_sum_map.symm
        _ ≤ ∑ j ∈ I_G, (G.toBodyFamily.body j).volume :=
          Finset.sum_le_sum_of_subset_of_nonneg h_img_sub (fun _ _ _ => by simp)
        _ = G.toBodyFamily.containedMass K := by rfl
    have h_density : ∀ (K : Set Point3),
        B_sub.family.density K ≤ G.toBodyFamily.density K := by
      intro K
      dsimp only [BodyFamily.density]
      gcongr
      exact h_sub_mass K
    have h_bdd : BddAbove {d : ENNReal | ∃ K : Set Point3, Convex ℝ K ∧ d = G.toBodyFamily.density K} :=
      ⟨⊤, fun _ _ => le_top⟩
    apply sSup_le
    intro d hd
    rcases hd with ⟨K, hK_conv, rfl⟩
    have h1 : B_sub.family.density K ≤ G.toBodyFamily.density K := h_density K
    have h2 : G.toBodyFamily.density K ≤ G.toBodyFamily.deltaMax := by
      apply le_csSup h_bdd
      exact ⟨K, hK_conv, rfl⟩
    exact le_trans h1 h2
  refine' ⟨S, Y', LinearIsometryEquiv.refl ℝ Point3, v, hS_unit, hS_distinct, hS_card_le, _⟩
  exact ⟨hY'_mass_ge, hY'_union_le, hdeltaMax_le⟩

end Kakeya.Streamlined.GeneralizedFrostman
