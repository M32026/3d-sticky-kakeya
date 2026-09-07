module

/-
  Translation layer between metric and dyadic definitions (1D case).

  Main results:
  - `external_le_dyadic1`: externalCoveringNumber ≤ dyadicCoveringNumber
  - `dyadic_le_external1`: dyadicCoveringNumber ≤ 3 * externalCoveringNumber
-/
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoveringUtils
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicCubes
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open scoped ENNReal NNReal
open DirecretisedFurstenbergEstimate

namespace DiscretisedFurstenbergEstimate.Translation

/-! ### 1D helpers -/

def mk1 (x : ℝ) : EuclideanSpace ℝ (Fin 1) :=
  WithLp.toLp 2 (fun _ : Fin 1 => x)

lemma mk1_apply (x : ℝ) : (mk1 x) 0 = x := by simp [mk1]

lemma dist1_eq (x y : EuclideanSpace ℝ (Fin 1)) : dist x y = |x 0 - y 0| := by
  have h : ‖x - y‖ ^ 2 = (x 0 - y 0) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq (x - y)]
    <;> simp [Fin.sum_univ_one] <;> ring
  have hpos1 : 0 ≤ ‖x - y‖ := by positivity
  have hpos2 : 0 ≤ |x 0 - y 0| := by positivity
  have h9 : ‖x - y‖ ^ 2 = |x 0 - y 0| ^ 2 := by rw [h, sq_abs]
  have h10 : ‖x - y‖ = |x 0 - y 0| := by nlinarith
  simpa [dist_eq_norm] using h10

def center1 (δ : ℝ) (k : ℤ) : EuclideanSpace ℝ (Fin 1) :=
  mk1 (δ * ((k : ℝ) + 1 / 2))

lemma center1_apply (δ : ℝ) (k : ℤ) : (center1 δ k) 0 = δ * ((k : ℝ) + 1 / 2) := by
  simp [center1, mk1]

lemma dist_to_center1_le {δ : ℝ} (hδ : 0 ≤ δ) {k : ℤ}
    {x : EuclideanSpace ℝ (Fin 1)}
    (hx : x ∈ dyadicCube δ (fun _ : Fin 1 => k)) :
    dist x (center1 δ k) ≤ δ / 2 := by
  have h1 : δ * (k : ℝ) ≤ x 0 := (hx 0).1
  have h2 : x 0 < δ * ((k : ℝ) + 1) := (hx 0).2
  have h3 : |x 0 - (center1 δ k) 0| ≤ δ / 2 := by
    rw [center1_apply]
    have h4 : x 0 - δ * ((k : ℝ) + 1 / 2) ≤ δ / 2 := by linarith
    have h5 : -(δ / 2) ≤ x 0 - δ * ((k : ℝ) + 1 / 2) := by linarith
    exact abs_le.mpr ⟨h5, h4⟩
  rw [dist1_eq]
  exact h3

lemma exists_cube_containing1 {δ : ℝ} (hδ : 0 < δ)
    (x : EuclideanSpace ℝ (Fin 1)) :
    ∃ (k : ℤ), x ∈ dyadicCube δ (fun _ : Fin 1 => k) := by
  let k : ℤ := ⌊x 0 / δ⌋
  have h2 : (k : ℝ) ≤ x 0 / δ := Int.floor_le _
  have h3 : x 0 / δ < (k : ℝ) + 1 := Int.lt_floor_add_one _
  refine ⟨k, ?_⟩
  intro i
  have h4 : δ * (k : ℝ) ≤ x 0 := by
    have h5 : δ * (k : ℝ) ≤ δ * (x 0 / δ) := by gcongr
    have h6 : δ * (x 0 / δ) = x 0 := by field_simp [hδ.ne'] <;> ring
    linarith
  have h5 : x 0 < δ * ((k : ℝ) + 1) := by
    have h6 : x 0 = δ * (x 0 / δ) := by field_simp [hδ.ne'] <;> ring
    rw [h6]
    gcongr <;> linarith
  have h_eq : (fun _ : Fin 1 => k) i = k := by simp
  have h_goal1 : δ * ((fun _ : Fin 1 => k) i) ≤ x i := by
    rw [h_eq]
    have h_xi : x i = x 0 := by fin_cases i <;> rfl
    rw [h_xi]
    exact h4
  have h_goal2 : x i < δ * (((fun _ : Fin 1 => k) i) + 1) := by
    rw [h_eq]
    have h_xi : x i = x 0 := by fin_cases i <;> rfl
    rw [h_xi]
    exact h5
  exact Set.mem_Ico.mpr ⟨h_goal1, h_goal2⟩

lemma cube_injective1 {δ : ℝ} (hδ : 0 < δ) :
    Function.Injective (fun (k : ℤ) => dyadicCube δ (fun _ : Fin 1 => k)) := by
  intro k1 k2 h
  by_cases hlt : k1 < k2
  · -- k1 < k2: pick point in first cube, show it can't be in second
    let x : EuclideanSpace ℝ (Fin 1) := mk1 (δ * (k1 : ℝ) + δ / 2)
    have hx1 : x ∈ dyadicCube δ (fun _ : Fin 1 => k1) := by
      intro i
      have h_eq : (fun _ : Fin 1 => k1) i = k1 := by simp
      rw [h_eq]
      constructor <;> simp [x, mk1] <;> linarith
    have h_eq : dyadicCube δ (fun _ : Fin 1 => k1) = dyadicCube δ (fun _ : Fin 1 => k2) := h
    have hx2 : x ∈ dyadicCube δ (fun _ : Fin 1 => k2) := by
      exact h_eq ▸ hx1
    have h4 : x 0 < δ * ((k1 : ℝ) + 1) := (hx1 0).2
    have h5 : δ * (k2 : ℝ) ≤ x 0 := (hx2 0).1
    have h6 : (k1 : ℝ) + 1 ≤ (k2 : ℝ) := by exact_mod_cast (show k1 + 1 ≤ k2 from by linarith)
    have h7 : δ * ((k1 : ℝ) + 1) ≤ δ * (k2 : ℝ) := by gcongr
    linarith
  · by_cases hlt2 : k2 < k1
    · -- symmetric
      let x : EuclideanSpace ℝ (Fin 1) := mk1 (δ * (k2 : ℝ) + δ / 2)
      have hx2 : x ∈ dyadicCube δ (fun _ : Fin 1 => k2) := by
        intro i
        have h_eq : (fun _ : Fin 1 => k2) i = k2 := by simp
        rw [h_eq]
        constructor <;> simp [x, mk1] <;> linarith
      have h_eq : dyadicCube δ (fun _ : Fin 1 => k1) = dyadicCube δ (fun _ : Fin 1 => k2) := h
      have hx1 : x ∈ dyadicCube δ (fun _ : Fin 1 => k1) := by
        exact h_eq.symm ▸ hx2
      have h4 : x 0 < δ * ((k2 : ℝ) + 1) := (hx2 0).2
      have h5 : δ * (k1 : ℝ) ≤ x 0 := (hx1 0).1
      have h6 : (k2 : ℝ) + 1 ≤ (k1 : ℝ) := by exact_mod_cast (show k2 + 1 ≤ k1 from by linarith)
      have h7 : δ * ((k2 : ℝ) + 1) ≤ δ * (k1 : ℝ) := by gcongr
      linarith
    · have h_eq : k1 = k2 := by omega
      exact h_eq

/-! ### external ≤ dyadic (d=1) -/

lemma external_le_dyadic1 {δ : ℝ} (hδ : 0 < δ)
    {A : Set (EuclideanSpace ℝ (Fin 1))} :
    Metric.externalCoveringNumber δ.toNNReal A ≤ dyadicCoveringNumber δ A := by
  let idxSet := {k : ℤ | (dyadicCube δ (fun _ : Fin 1 => k) ∩ A).Nonempty}
  let centers := (fun k : ℤ => center1 δ k) '' idxSet
  have hcover : Metric.IsCover δ.toNNReal A centers := by
    intro x hx
    rcases exists_cube_containing1 hδ x with ⟨k, hk⟩
    have h_nonempty : (dyadicCube δ (fun _ : Fin 1 => k) ∩ A).Nonempty := ⟨x, hk, hx⟩
    let c := center1 δ k
    have hc_in : c ∈ centers := ⟨k, h_nonempty, rfl⟩
    have hdist : dist x c ≤ δ / 2 := dist_to_center1_le (le_of_lt hδ) hk
    have hdist' : dist x c ≤ δ := by linarith
    have hedist : edist x c ≤ ↑δ.toNNReal := by
      rw [edist_dist]
      exact ENNReal.ofReal_le_ofReal hdist'
    exact ⟨c, hc_in, hedist⟩
  have h1 : Metric.externalCoveringNumber δ.toNNReal A ≤ centers.encard :=
    Metric.IsCover.externalCoveringNumber_le_encard hcover
  have h2 : centers.encard ≤ idxSet.encard := Set.encard_image_le _ _
  let f : ℤ → Set (EuclideanSpace ℝ (Fin 1)) := fun k => dyadicCube δ (fun _ => k)
  have h4 : (dyadicCubesMeeting (d := 1) δ A) = f '' idxSet := by
    ext Q
    simp only [dyadicCubesMeeting, dyadicCubes, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨⟨k, rfl⟩, hQ⟩
      have h_k_eq : (fun _ : Fin 1 => k 0) = k := by
        funext i
        fin_cases i <;> simp
      have h5 : (dyadicCube δ (fun _ : Fin 1 => k 0) ∩ A).Nonempty := by
        rw [h_k_eq] <;> exact hQ
      exact ⟨k 0, h5, by simp [f, h_k_eq]⟩
    · rintro ⟨k, hQ, rfl⟩
      exact ⟨⟨fun _ => k, rfl⟩, hQ⟩
  have h5 : Function.Injective f := by
    intro k1 k2 h
    exact cube_injective1 hδ h
  have h6 : (f '' idxSet).encard = idxSet.encard := h5.encard_image idxSet
  have h7 : dyadicCoveringNumber δ A = idxSet.encard := by
    simp only [dyadicCoveringNumber, h4, h6]
  rw [h7]
  exact h1.trans h2

/-! ### ball intersects ≤ 3 cubes (d=1) -/

lemma ball_cube_bound {δ : ℝ} (hδ : 0 < δ)
    {c : EuclideanSpace ℝ (Fin 1)} :
    Set.Finite {k : ℤ | (dyadicCube δ (fun _ : Fin 1 => k) ∩ Metric.closedBall c δ).Nonempty} := by
  let m : ℤ := ⌊c 0 / δ⌋
  let S : Finset ℤ := Finset.Icc (m - 1) (m + 1)
  have h_subset : {k : ℤ | (dyadicCube δ (fun _ : Fin 1 => k) ∩ Metric.closedBall c δ).Nonempty} ⊆ (S : Set ℤ) := by
    intro k hk
    rcases hk with ⟨x, hx_cube, hx_ball⟩
    have hdist : dist x c ≤ δ := (Metric.mem_closedBall).mp hx_ball
    have h_coord : |x 0 - c 0| ≤ δ := by
      rw [dist1_eq x c] at hdist <;> exact hdist
    have h1 : δ * (k : ℝ) ≤ x 0 := (hx_cube 0).1
    have h2 : x 0 < δ * ((k : ℝ) + 1) := (hx_cube 0).2
    have h3 : c 0 - δ ≤ x 0 := by linarith [abs_le.mp h_coord]
    have h4 : x 0 ≤ c 0 + δ := by linarith [abs_le.mp h_coord]
    have h5 : (k : ℝ) ≤ c 0 / δ + 1 := by
      have h6 : δ * (k : ℝ) ≤ c 0 + δ := by linarith
      have h7 : (k : ℝ) ≤ (c 0 + δ) / δ := by
        calc (k : ℝ)
          = (δ * (k : ℝ)) / δ := by field_simp [hδ.ne'] <;> ring
        _ ≤ (c 0 + δ) / δ := by gcongr
      have h8 : (c 0 + δ) / δ = c 0 / δ + 1 := by field_simp [hδ.ne'] <;> ring
      rw [h8] at h7
      exact h7
    have h9 : c 0 / δ - 2 < (k : ℝ) := by
      have h10 : c 0 - δ < δ * ((k : ℝ) + 1) := by linarith
      have h11 : (c 0 - δ) / δ < (k : ℝ) + 1 := by
        calc (c 0 - δ) / δ
          < (δ * ((k : ℝ) + 1)) / δ := by gcongr
        _ = (k : ℝ) + 1 := by field_simp [hδ.ne'] <;> ring
      have h12 : (c 0 - δ) / δ = c 0 / δ - 1 := by field_simp [hδ.ne'] <;> ring
      rw [h12] at h11
      linarith
    have hm1 : (m : ℝ) ≤ c 0 / δ := Int.floor_le _
    have hm2 : c 0 / δ < (m : ℝ) + 1 := Int.lt_floor_add_one _
    have h13 : (m : ℝ) - 2 < (k : ℝ) := by linarith [hm1, h9]
    have h_k_ge : m - 1 ≤ k := by
      have h14 : m - 2 < k := by exact_mod_cast h13
      omega
    have h15 : (k : ℝ) < (m : ℝ) + 2 := by linarith [hm2, h5]
    have h_k_le : k ≤ m + 1 := by
      have h16 : k < m + 2 := by exact_mod_cast h15
      omega
    exact Finset.mem_Icc.mpr ⟨h_k_ge, h_k_le⟩
  exact Set.Finite.subset S.finite_toSet h_subset

lemma ball_cube_encard_le_3 {δ : ℝ} (hδ : 0 < δ)
    {c : EuclideanSpace ℝ (Fin 1)} :
    ({k : ℤ | (dyadicCube δ (fun _ : Fin 1 => k) ∩ Metric.closedBall c δ).Nonempty}.encard : ENNReal) ≤ 3 := by
  let m : ℤ := ⌊c 0 / δ⌋
  let S : Finset ℤ := Finset.Icc (m - 1) (m + 1)
  have h_card : S.card ≤ 3 := by
    simp [S, Finset.Icc_eq_empty_of_lt] <;> omega
  have h_subset : {k : ℤ | (dyadicCube δ (fun _ : Fin 1 => k) ∩ Metric.closedBall c δ).Nonempty} ⊆ (S : Set ℤ) := by
    intro k hk
    rcases hk with ⟨x, hx_cube, hx_ball⟩
    have hdist : dist x c ≤ δ := (Metric.mem_closedBall).mp hx_ball
    have h_coord : |x 0 - c 0| ≤ δ := by
      rw [dist1_eq x c] at hdist <;> exact hdist
    have h1 : δ * (k : ℝ) ≤ x 0 := (hx_cube 0).1
    have h2 : x 0 < δ * ((k : ℝ) + 1) := (hx_cube 0).2
    have h3 : c 0 - δ ≤ x 0 := by linarith [abs_le.mp h_coord]
    have h4 : x 0 ≤ c 0 + δ := by linarith [abs_le.mp h_coord]
    have h5 : (k : ℝ) ≤ c 0 / δ + 1 := by
      have h6 : δ * (k : ℝ) ≤ c 0 + δ := by linarith
      have h7 : (k : ℝ) ≤ (c 0 + δ) / δ := by
        calc (k : ℝ)
          = (δ * (k : ℝ)) / δ := by field_simp [hδ.ne'] <;> ring
        _ ≤ (c 0 + δ) / δ := by gcongr
      have h8 : (c 0 + δ) / δ = c 0 / δ + 1 := by field_simp [hδ.ne'] <;> ring
      rw [h8] at h7
      exact h7
    have h9 : c 0 / δ - 2 < (k : ℝ) := by
      have h10 : c 0 - δ < δ * ((k : ℝ) + 1) := by linarith
      have h11 : (c 0 - δ) / δ < (k : ℝ) + 1 := by
        calc (c 0 - δ) / δ
          < (δ * ((k : ℝ) + 1)) / δ := by gcongr
        _ = (k : ℝ) + 1 := by field_simp [hδ.ne'] <;> ring
      have h12 : (c 0 - δ) / δ = c 0 / δ - 1 := by field_simp [hδ.ne'] <;> ring
      rw [h12] at h11
      linarith
    have hm1 : (m : ℝ) ≤ c 0 / δ := Int.floor_le _
    have hm2 : c 0 / δ < (m : ℝ) + 1 := Int.lt_floor_add_one _
    have h13 : (m : ℝ) - 2 < (k : ℝ) := by linarith [hm1, h9]
    have h_k_ge : m - 1 ≤ k := by
      have h14 : m - 2 < k := by exact_mod_cast h13
      omega
    have h15 : (k : ℝ) < (m : ℝ) + 2 := by linarith [hm2, h5]
    have h_k_le : k ≤ m + 1 := by
      have h16 : k < m + 2 := by exact_mod_cast h15
      omega
    exact Finset.mem_Icc.mpr ⟨h_k_ge, h_k_le⟩
  have h_encard : ({k : ℤ | (dyadicCube δ (fun _ : Fin 1 => k) ∩ Metric.closedBall c δ).Nonempty}.encard : ENNReal) ≤ (S.card : ENNReal) := by
    exact_mod_cast Set.encard_le_encard h_subset
  have h_final : (S.card : ENNReal) ≤ 3 := by
    exact_mod_cast h_card
  exact h_encard.trans h_final

/-! ### dyadic ≤ 3 * external (d=1) -/

lemma dyadic_le_external1 {δ : ℝ} (hδ : 0 < δ)
    {A : Set (EuclideanSpace ℝ (Fin 1))} :
    dyadicCoveringNumber δ A ≤ 3 * Metric.externalCoveringNumber δ.toNNReal A := by
  let idxSet := {k : ℤ | (dyadicCube δ (fun _ : Fin 1 => k) ∩ A).Nonempty}
  let f : ℤ → Set (EuclideanSpace ℝ (Fin 1)) := fun k => dyadicCube δ (fun _ => k)
  have h3 : dyadicCoveringNumber δ A = idxSet.encard := by
    have h4 : (dyadicCubesMeeting (d := 1) δ A) = f '' idxSet := by
      ext Q
      simp only [dyadicCubesMeeting, dyadicCubes, Set.mem_setOf_eq, Set.mem_image]
      constructor
      · rintro ⟨⟨k, rfl⟩, hQ⟩
        have h_k_eq : (fun _ : Fin 1 => k 0) = k := by
          funext i
          fin_cases i <;> simp
        have h5 : (dyadicCube δ (fun _ : Fin 1 => k 0) ∩ A).Nonempty := by
          rw [h_k_eq] <;> exact hQ
        exact ⟨k 0, h5, by simp [f, h_k_eq]⟩
      · rintro ⟨k, hQ, rfl⟩
        exact ⟨⟨fun _ => k, rfl⟩, hQ⟩
    have h5 : Function.Injective f := by
      intro k1 k2 h
      exact cube_injective1 hδ h
    have h6 : (f '' idxSet).encard = idxSet.encard := h5.encard_image idxSet
    simp only [dyadicCoveringNumber, h4, h6]
  rw [h3]
  by_cases h_top : Metric.externalCoveringNumber δ.toNNReal A = ⊤
  · rw [h_top] <;> simp
  · have h_lt_top : Metric.externalCoveringNumber δ.toNNReal A < ⊤ :=
      lt_top_iff_ne_top.mpr h_top
    rcases DiscretisedFurstenbergEstimate.CoveringUtils.exists_external_cover_eq h_lt_top with ⟨C, hC, hC_eq⟩
    by_cases hCinf : C.encard = ⊤
    · rw [hC_eq] at hCinf
      rw [hCinf] <;> simp
    · have hCfin : Set.Finite C := Set.encard_ne_top_iff.mp hCinf
      let C' := hCfin.toFinset
      let S_c : EuclideanSpace ℝ (Fin 1) → Finset ℤ := fun c =>
        (ball_cube_bound hδ (c := c)).toFinset
      let S_union : Finset ℤ := C'.biUnion (fun c => S_c c)
      have h1 : idxSet ⊆ (S_union : Set ℤ) := by
        intro k hk
        rcases hk with ⟨x, hx_cube, hx_A⟩
        have h_xcovered : ∃ (c : EuclideanSpace ℝ (Fin 1)), c ∈ C ∧ edist x c ≤ ↑δ.toNNReal := hC hx_A
        rcases h_xcovered with ⟨c, hc, hedist⟩
        have hdist : dist x c ≤ δ := by
          rw [edist_dist] at hedist
          have hδ_nonneg : 0 ≤ δ := by linarith
          have h_eq : (↑δ.toNNReal : ENNReal) = ENNReal.ofReal δ := by exact ENNReal.ofNNReal_toNNReal δ
          rw [h_eq] at hedist
          have h' : dist x c ≤ δ := by
            by_contra h_contra
            have h2 : δ < dist x c := by linarith
            have h3 : ENNReal.ofReal δ < ENNReal.ofReal (dist x c) := by exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hδ_nonneg).mpr h2
            exact absurd h3 (not_lt.mpr hedist)
          exact h'
        have hball : x ∈ Metric.closedBall c δ := by
          simpa [Metric.mem_closedBall] using hdist
        have hc' : c ∈ C' := by simpa [C'] using hc
        have hk_sc : k ∈ (S_c c : Set ℤ) := by
          simpa [S_c] using ⟨x, hx_cube, hball⟩
        exact Finset.mem_biUnion.mpr ⟨c, hc', hk_sc⟩
      have h2 : idxSet.encard ≤ (S_union : Set ℤ).encard := Set.encard_le_encard h1
      have h3_card : S_union.card ≤ ∑ c ∈ C', (S_c c).card := Finset.card_biUnion_le
      have h3_eq : (S_union : Set ℤ).encard = ↑S_union.card := by exact Set.encard_coe_eq_coe_finsetCard S_union
      have h3_enreal : ((S_union : Set ℤ).encard : ENNReal) ≤ (↑(∑ c ∈ C', (S_c c).card) : ENNReal) := by
        rw [h3_eq]
        have h : (↑S_union.card : ENNReal) ≤ (↑(∑ c ∈ C', (S_c c).card) : ENNReal) := by
          exact_mod_cast h3_card
        exact h
      have h4 : ∀ c ∈ C', (S_c c).card ≤ 3 := by
        intro c _
        have h5 : (S_c c : Set ℤ) = {k : ℤ | (dyadicCube δ (fun _ : Fin 1 => k) ∩ Metric.closedBall c δ).Nonempty} := by
          ext k
          simp [S_c] <;> rfl
        have h6 : ((S_c c : Set ℤ).encard : ENNReal) ≤ 3 := by
          rw [h5]
          exact ball_cube_encard_le_3 hδ (c := c)
        exact_mod_cast h6
      have h_sum : (∑ c ∈ C', (S_c c).card) ≤ C'.card * 3 := by
        calc ∑ c ∈ C', (S_c c).card
          ≤ ∑ c ∈ C', 3 := Finset.sum_le_sum h4
        _ = C'.card * 3 := by simp [Finset.sum_const] <;> ring
      have h7 : (idxSet.encard : ENNReal) ≤ (3 : ENNReal) * (C.encard : ENNReal) := by
        calc (idxSet.encard : ENNReal)
          ≤ ((S_union : Set ℤ).encard : ENNReal) := by exact_mod_cast h2
        _ = (↑S_union.card : ENNReal) := by exact_mod_cast h3_eq
        _ ≤ (↑(∑ c ∈ C', (S_c c).card) : ENNReal) := by exact_mod_cast h3_card
        _ ≤ (↑(C'.card * 3) : ENNReal) := by exact_mod_cast h_sum
        _ = (3 : ENNReal) * (↑C'.card : ENNReal) := by
          simp [mul_comm] <;> ring
        _ = (3 : ENNReal) * (C.encard : ENNReal) := by
          have h81 : (C' : Set _) = C := hCfin.coe_toFinset
          have h9 : C.encard = ↑C'.card := by
            have h10 : C.encard = ↑C.ncard := Set.Finite.encard_eq_coe hCfin
            have h11 : C.ncard = (C' : Set (EuclideanSpace ℝ (Fin 1))).ncard := by rw [h81]
            have h12 : (C' : Set (EuclideanSpace ℝ (Fin 1))).ncard = C'.card := by exact Set.ncard_coe_finset C'
            rw [h10, h11, h12]
          have h8 : (↑C'.card : ENNReal) = (C.encard : ENNReal) := by
            have h9' : (C.encard : ENNReal) = (↑C'.card : ENNReal) := by exact_mod_cast h9
            exact h9'.symm
          rw [h8] <;> ring
      have h9 : idxSet.encard ≤ (3 : ℕ∞) * C.encard := by
        exact_mod_cast h7
      rw [hC_eq] at h9
      exact h9

/-! ### monotonicity -/

lemma dyadicCoveringNumber_mono {d : ℕ} {δ : ℝ}
    {A B : Set (EuclideanSpace ℝ (Fin d))} (h : A ⊆ B) :
    dyadicCoveringNumber δ A ≤ dyadicCoveringNumber δ B := by
  have h1 : dyadicCubesMeeting δ A ⊆ dyadicCubesMeeting δ B := by
    intro Q hQ
    exact ⟨hQ.1, hQ.2.mono (Set.inter_subset_inter_right Q h)⟩
  exact Set.encard_mono h1

/-! ### IsDeltaSSet → IsDeltaSCSet (d=1) -/

lemma isDeltaSSet_to_isDeltaSCSet1 {δ s C : ℝ}
    {P : Set (EuclideanSpace ℝ (Fin 1))}
    (hP : IsDeltaSSet δ s C P)
    (hδ_dyadic : δ ∈ dyadicScales)
    (hP_bounded : Bornology.IsBounded P)
    (hs_le_one : s ≤ 1) :
    IsDeltaSCSet (d := 1) δ s (3 * C) P := by
  have hP_ne : P.Nonempty := hP.1
  have hδ_pos : 0 < δ := hP.2.1
  have hC_pos : 0 < C := hP.2.2.1
  have hs_nonneg : 0 ≤ s := hP.2.2.2.1
  have h_main : ∀ (x : EuclideanSpace ℝ (Fin 1)) (r : ℝ), δ ≤ r →
      (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) : ℝ≥0∞) ≤
      ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
        (Metric.externalCoveringNumber δ.toNNReal P : ℝ≥0∞) :=
    hP.2.2.2.2
  have hs_le_one' : s ≤ (↑1 : ℕ) := by exact_mod_cast hs_le_one
  have h3C_pos : 0 < 3 * C := by positivity
  refine ⟨hP_bounded, hP_ne, by norm_num, hδ_dyadic, hδ_pos, hs_nonneg, hs_le_one', h3C_pos, ?_⟩
  intro r Q hr_dyadic hQ hδ_le_r hr_le_one
  rcases hQ with ⟨k, rfl⟩
  let k0 : ℤ := k 0
  let c := center1 r k0
  have h_k_eq : (fun _ : Fin 1 => k0) = k := by funext i; fin_cases i <;> rfl
  have hQ_subset : dyadicCube r k ⊆ Metric.closedBall c r := by
    rw [show dyadicCube r k = dyadicCube r (fun _ => k0) from by rw [h_k_eq]]
    intro x hx
    have hdist : dist x c ≤ r / 2 := dist_to_center1_le (by linarith) hx
    exact Metric.mem_closedBall.mpr (by linarith)
  have h_inter : P ∩ dyadicCube r k ⊆ P ∩ Metric.closedBall c r := by
    gcongr
  have h1 : (dyadicCoveringNumber δ (P ∩ dyadicCube r k) : ENNReal) ≤
      (dyadicCoveringNumber δ (P ∩ Metric.closedBall c r) : ENNReal) := by
    exact_mod_cast dyadicCoveringNumber_mono h_inter
  have h2 : (dyadicCoveringNumber δ (P ∩ Metric.closedBall c r) : ENNReal) ≤
      (3 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall c r) : ENNReal) := by
    exact_mod_cast dyadic_le_external1 hδ_pos
  have h3 : (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall c r) : ENNReal) ≤
      ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
        (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) :=
    h_main c r hδ_le_r
  have h4 : (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) ≤
      (dyadicCoveringNumber δ P : ENNReal) := by
    exact_mod_cast external_le_dyadic1 hδ_pos
  have h5 : (dyadicCoveringNumber δ (P ∩ dyadicCube r k) : ENNReal) ≤
      (3 : ENNReal) * ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (dyadicCoveringNumber δ P : ENNReal) := by
    calc (dyadicCoveringNumber δ (P ∩ dyadicCube r k) : ENNReal)
      ≤ (dyadicCoveringNumber δ (P ∩ Metric.closedBall c r) : ENNReal) := h1
    _ ≤ (3 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall c r) : ENNReal) := h2
    _ ≤ (3 : ENNReal) * (ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (Metric.externalCoveringNumber δ.toNNReal P : ENNReal)) := by
      gcongr
    _ = (3 : ENNReal) * ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by ring
    _ ≤ (3 : ENNReal) * ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (dyadicCoveringNumber δ P : ENNReal) := by
      gcongr
  have h6 : ENNReal.ofReal (3 * C) = (3 : ENNReal) * ENNReal.ofReal C := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)] <;> norm_cast
  have h7 : 0 ≤ r := by linarith
  have h8 : ENNReal.ofReal (r ^ s) = (ENNReal.ofReal r) ^ s := by
    rw [ENNReal.ofReal_rpow_of_nonneg h7 hs_nonneg]
  have h9 : (3 : ENNReal) * ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (dyadicCoveringNumber δ P : ENNReal) =
      ENNReal.ofReal (3 * C) * (dyadicCoveringNumber δ P : ENNReal) * ENNReal.ofReal (r ^ s) := by
    rw [h6, h8] <;> ring
  rw [h9] at h5
  exact h5

/-! ### 2D helpers -/

def center2 (δ : ℝ) (k : Fin 2 → ℤ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 (fun i : Fin 2 => δ * ((k i : ℝ) + 1 / 2))

lemma dist_to_center2_le {δ : ℝ} (hδ : 0 ≤ δ) {k : Fin 2 → ℤ}
    {x : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ dyadicCube δ k) :
    dist x (center2 δ k) ≤ δ := by
  have h1 : ∀ i : Fin 2, |x i - (center2 δ k) i| ≤ δ / 2 := by
    intro i
    have h2 : δ * (k i : ℝ) ≤ x i := (hx i).1
    have h3 : x i < δ * ((k i : ℝ) + 1) := (hx i).2
    have h4 : (center2 δ k) i = δ * ((k i : ℝ) + 1 / 2) := by simp [center2]
    rw [h4]
    have h5 : x i - δ * ((k i : ℝ) + 1 / 2) ≤ δ / 2 := by linarith
    have h6 : -(δ / 2) ≤ x i - δ * ((k i : ℝ) + 1 / 2) := by linarith
    exact abs_le.mpr ⟨h6, h5⟩
  have h2 : |x 0 - (center2 δ k) 0| ≤ δ / 2 := h1 0
  have h3 : |x 1 - (center2 δ k) 1| ≤ δ / 2 := h1 1
  have h4 : (x 0 - (center2 δ k) 0) ^ 2 ≤ (δ / 2) ^ 2 := by
    calc (x 0 - (center2 δ k) 0) ^ 2
      = |x 0 - (center2 δ k) 0| ^ 2 := by rw [sq_abs]
    _ ≤ (δ / 2) ^ 2 := by gcongr
  have h5 : (x 1 - (center2 δ k) 1) ^ 2 ≤ (δ / 2) ^ 2 := by
    calc (x 1 - (center2 δ k) 1) ^ 2
      = |x 1 - (center2 δ k) 1| ^ 2 := by rw [sq_abs]
    _ ≤ (δ / 2) ^ 2 := by gcongr
  have h_norm_sq : ‖x - center2 δ k‖ ^ 2 =
      (x 0 - (center2 δ k) 0) ^ 2 + (x 1 - (center2 δ k) 1) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq (x - center2 δ k)]
    <;> simp [Fin.sum_univ_two] <;> ring
  have h6 : ‖x - center2 δ k‖ ^ 2 ≤ δ ^ 2 := by
    rw [h_norm_sq]
    nlinarith
  have h7 : 0 ≤ ‖x - center2 δ k‖ := by positivity
  have h8 : ‖x - center2 δ k‖ ≤ δ := by nlinarith
  simpa [dist_eq_norm] using h8

/-! ### Comparability (d=2) via DyadicCubes infrastructure -/

lemma dyadicScale_eq_delta {δ : ℝ} (hδ_dyadic : δ ∈ dyadicScales) :
    ∃ (n : ℕ), δ = DyadicCubes.dyadicDelta n := by
  rcases hδ_dyadic with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  rw [hn]
  simp [DyadicCubes.dyadicDelta, zpow_neg, zpow_ofNat]
  <;> field_simp
  <;> ring

lemma external_le_dyadic2 {δ : ℝ} (hδ : 0 < δ) (hδ_dyadic : δ ∈ dyadicScales)
    {A : Set (EuclideanSpace ℝ (Fin 2))} (hA : Bornology.IsBounded A) :
    Metric.externalCoveringNumber δ.toNNReal A ≤ dyadicCoveringNumber δ A := by
  rcases dyadicScale_eq_delta hδ_dyadic with ⟨n, hδ_eq⟩
  have h_eq : dyadicCoveringNumber δ A = ↑(DyadicCubes.dyadicCoveringNumber n A hA) := by
    rw [hδ_eq]
    exact DyadicCubes.dyadicCoveringNumber_eq_general n hA
  rw [h_eq, hδ_eq]
  exact DyadicCubes.dyadicCoveringNumber_le_external n hA

lemma dyadic_le_external2 {δ : ℝ} (hδ : 0 < δ) (hδ_dyadic : δ ∈ dyadicScales)
    {A : Set (EuclideanSpace ℝ (Fin 2))} (hA : Bornology.IsBounded A) :
    dyadicCoveringNumber δ A ≤ (9 : ENNReal) * Metric.externalCoveringNumber δ.toNNReal A := by
  rcases dyadicScale_eq_delta hδ_dyadic with ⟨n, hδ_eq⟩
  have h_eq : dyadicCoveringNumber δ A = ↑(DyadicCubes.dyadicCoveringNumber n A hA) := by
    rw [hδ_eq]
    exact DyadicCubes.dyadicCoveringNumber_eq_general n hA
  rw [h_eq, hδ_eq]
  exact_mod_cast DyadicCubes.externalCoveringNumber_le_dyadic n hA

/-! ### IsDeltaSSet → IsDeltaSCSet (d=2) -/

lemma isDeltaSSet_to_isDeltaSCSet2 {δ s C : ℝ}
    {P : Set (EuclideanSpace ℝ (Fin 2))}
    (hP : IsDeltaSSet δ s C P)
    (hδ_dyadic : δ ∈ dyadicScales)
    (hP_bounded : Bornology.IsBounded P)
    (hs_le_two : s ≤ 2) :
    IsDeltaSCSet (d := 2) δ s (9 * C) P := by
  have hP_ne : P.Nonempty := hP.1
  have hδ_pos : 0 < δ := hP.2.1
  have hC_pos : 0 < C := hP.2.2.1
  have hs_nonneg : 0 ≤ s := hP.2.2.2.1
  have h_main : ∀ (x : EuclideanSpace ℝ (Fin 2)) (r : ℝ), δ ≤ r →
      (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) : ℝ≥0∞) ≤
      ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
        (Metric.externalCoveringNumber δ.toNNReal P : ℝ≥0∞) :=
    hP.2.2.2.2
  have hs_le_two' : s ≤ (↑2 : ℕ) := by exact_mod_cast hs_le_two
  have h9C_pos : 0 < 9 * C := by positivity
  refine ⟨hP_bounded, hP_ne, by norm_num, hδ_dyadic, hδ_pos, hs_nonneg, hs_le_two', h9C_pos, ?_⟩
  intro r Q hr_dyadic hQ hδ_le_r hr_le_one
  rcases hQ with ⟨k, rfl⟩
  let c := center2 r k
  have hQ_subset : dyadicCube r k ⊆ Metric.closedBall c r := by
    intro x hx
    have hdist : dist x c ≤ r := dist_to_center2_le (by linarith) hx
    exact Metric.mem_closedBall.mpr hdist
  have h_inter : P ∩ dyadicCube r k ⊆ P ∩ Metric.closedBall c r := by gcongr
  have h_sub : P ∩ Metric.closedBall c r ⊆ Metric.closedBall c r := by
    intro x hx
    exact hx.2
  have h_ball_bdd : Bornology.IsBounded (P ∩ Metric.closedBall c r) :=
    Bornology.IsBounded.subset (Metric.isBounded_closedBall (x := c) (r := r)) h_sub
  have h1 : (dyadicCoveringNumber δ (P ∩ dyadicCube r k) : ENNReal) ≤
      (dyadicCoveringNumber δ (P ∩ Metric.closedBall c r) : ENNReal) := by
    exact_mod_cast dyadicCoveringNumber_mono h_inter
  have h2 : (dyadicCoveringNumber δ (P ∩ Metric.closedBall c r) : ENNReal) ≤
      (9 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall c r) : ENNReal) := by
    exact dyadic_le_external2 hδ_pos hδ_dyadic h_ball_bdd
  have h3 : (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall c r) : ENNReal) ≤
      ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
        (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) :=
    h_main c r hδ_le_r
  have h4 : (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) ≤
      (dyadicCoveringNumber δ P : ENNReal) := by
    exact_mod_cast external_le_dyadic2 hδ_pos hδ_dyadic hP_bounded
  have h5 : (dyadicCoveringNumber δ (P ∩ dyadicCube r k) : ENNReal) ≤
      (9 : ENNReal) * ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (dyadicCoveringNumber δ P : ENNReal) := by
    calc (dyadicCoveringNumber δ (P ∩ dyadicCube r k) : ENNReal)
      ≤ (dyadicCoveringNumber δ (P ∩ Metric.closedBall c r) : ENNReal) := h1
    _ ≤ (9 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall c r) : ENNReal) := h2
    _ ≤ (9 : ENNReal) * (ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (Metric.externalCoveringNumber δ.toNNReal P : ENNReal)) := by gcongr
    _ = (9 : ENNReal) * ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by ring
    _ ≤ (9 : ENNReal) * ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (dyadicCoveringNumber δ P : ENNReal) := by gcongr
  have h6 : ENNReal.ofReal (9 * C) = (9 : ENNReal) * ENNReal.ofReal C := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 9)] <;> norm_cast
  have h7 : 0 ≤ r := by linarith
  have h8 : ENNReal.ofReal (r ^ s) = (ENNReal.ofReal r) ^ s := by
    rw [ENNReal.ofReal_rpow_of_nonneg h7 hs_nonneg]
  have h9 : (9 : ENNReal) * ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (dyadicCoveringNumber δ P : ENNReal) =
      ENNReal.ofReal (9 * C) * (dyadicCoveringNumber δ P : ENNReal) * ENNReal.ofReal (r ^ s) := by
    rw [h6, h8] <;> ring
  rw [h9] at h5
  exact h5

end DiscretisedFurstenbergEstimate.Translation
