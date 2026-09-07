module

/-
  FurstenbergCaller.lean

  Constructs the h_furstenberg_lower hypothesis for the non-concentrated bridge.
-/

public import MyLeanRepo.RadialBootstrapping.Basic
public import MyLeanRepo.RadialBootstrapping.FurstenbergLowerBound

@[expose] public section

open Metric Set Finset
open scoped ENNReal NNReal
open FurstenbergEstimate

noncomputable section

namespace RadialBootstrapping

/-! ============================================================================
   1. Uniform doubling for finite-dimensional normed spaces
   ============================================================================ -/

lemma exists_doubling_constant_normed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    ∃ (D : ℕ), 0 < D ∧ ∀ (x : E) (ε : ℝ), 0 < ε →
      ∃ (S : Finset E), Metric.closedBall x (2 * ε) ⊆ ⋃ y ∈ S, Metric.closedBall y ε ∧ S.card ≤ D := by
  have h_compact : IsCompact (Metric.closedBall (0 : E) 2) := by exact isCompact_closedBall 0 2
  let U : E → Set E := fun y => Metric.ball y (1 : ℝ)
  have hU : ∀ (y : E), IsOpen (U y) := fun _ => Metric.isOpen_ball
  have h_cover : Metric.closedBall (0 : E) 2 ⊆ ⋃ (y : E), U y := by
    intro z hz
    have hball : z ∈ U z := by
      simpa [U, Metric.mem_ball] using by norm_num
    exact Set.mem_iUnion.mpr ⟨z, hball⟩
  rcases h_compact.elim_finite_subcover (U := U) hU h_cover with ⟨S₀, hS₀_cover⟩
  let D := S₀.card
  have hD_pos : 0 < D := by
    by_contra h
    have h' : S₀.card = 0 := by omega
    have hS0_empty : S₀ = ∅ := Finset.card_eq_zero.mp h'
    have h_cont : Metric.closedBall (0 : E) 2 ⊆ (∅ : Set E) := by
      rw [hS0_empty] at hS₀_cover
      simpa using hS₀_cover
    have h0_in : (0 : E) ∈ Metric.closedBall (0 : E) 2 := by simp
    exact False.elim (h_cont h0_in)
  refine' ⟨D, hD_pos, _⟩
  intro x ε hε
  classical
  let S : Finset E := S₀.image (fun y => x + ε • y)
  have hS_card : S.card ≤ D := by
    have h1 : S.card ≤ S₀.card := Finset.card_image_le
    have h2 : S₀.card = D := by rfl
    rw [h2] at h1
    exact h1
  have h_main : Metric.closedBall x (2 * ε) ⊆ ⋃ y ∈ S, Metric.closedBall y ε := by
    intro z hz
    let w : E := ε⁻¹ • (z - x)
    have h9 : ‖z - x‖ ≤ 2 * ε := by simpa [dist_eq_norm] using hz
    have hwnorm : ‖w‖ = ε⁻¹ * ‖z - x‖ := by
      have h : ‖w‖ = ‖ε⁻¹ • (z - x)‖ := by rfl
      rw [h, norm_smul]
      have h_abs : ‖ε⁻¹‖ = ε⁻¹ := by
        have h_pos : 0 < ε⁻¹ := by positivity
        have h1 : ‖(ε⁻¹ : ℝ)‖ = |ε⁻¹| := by exact Real.norm_eq_abs ε⁻¹
        rw [h1, abs_of_pos h_pos]
      rw [h_abs]
    have h10 : ‖w‖ ≤ 2 := by
      rw [hwnorm]
      calc ε⁻¹ * ‖z - x‖ ≤ ε⁻¹ * (2 * ε) := by gcongr
        _ = 2 := by field_simp [hε.ne'] <;> ring
    have h1 : w ∈ Metric.closedBall (0 : E) 2 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using h10
    have h2 : w ∈ ⋃ (y : E) (_ : y ∈ S₀), U y := hS₀_cover h1
    rcases Set.mem_iUnion₂.mp h2 with ⟨y, hy, h3⟩
    let y' : E := x + ε • y
    have hy'_in_S : y' ∈ S := Finset.mem_image.mpr ⟨y, hy, rfl⟩
    have h71 : w ∈ Metric.ball y 1 := h3
    have h7 : ‖w - y‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using h71
    have h61 : ε • w = (z - x) := by
      have h_def : w = ε⁻¹ • (z - x) := by rfl
      have h : ε • (ε⁻¹ • (z - x)) = (ε * ε⁻¹) • (z - x) := by
        rw [smul_smul]
      have h_mul : ε * ε⁻¹ = 1 := by
        field_simp [hε.ne']
      rw [h_def, h, h_mul, one_smul]
    have h6 : ε • (w - y) = (z - x) - ε • y := by
      rw [smul_sub, h61]
    have h5 : ‖z - (x + ε • y)‖ = ε * ‖w - y‖ := by
      have h51 : z - (x + ε • y) = (z - x) - ε • y := by abel
      have h_abs : ‖ε‖ = ε := by
        simp [abs_of_pos hε]
      rw [h51, ←h6, norm_smul, h_abs]
    have h8 : ε * ‖w - y‖ < ε := by
      have h9 : ‖w - y‖ * ε < ε := mul_lt_of_lt_one_left hε h7
      linarith
    have h4 : dist z y' ≤ ε := by
      have h_dist : dist z y' = ‖z - (x + ε • y)‖ := by simp [y', dist_eq_norm]
      rw [h_dist, h5]
      linarith
    exact Set.mem_iUnion₂.mpr ⟨y', hy'_in_S, h4⟩
  exact ⟨S, h_main, hS_card⟩

/-! ============================================================================
   2. Doubling for Point and Line2
   ============================================================================ -/

lemma Point_exists_doubling :
    ∃ (D : ℕ), 0 < D ∧ ∀ (x : Point) (ε : ℝ), 0 < ε →
      ∃ (S : Finset Point), Metric.closedBall x (2 * ε) ⊆ ⋃ y ∈ S, Metric.closedBall y ε ∧ S.card ≤ D :=
  exists_doubling_constant_normed (E := Point)

/-- Line2 embeds into (Point →L Point) × Point. The embedding satisfies:
    dist_E ≤ dist_Line2 ≤ 2 * dist_E (bi-Lipschitz with constant 2). -/
def line2Embed (L : Line2) : (Point →L[ℝ] Point) × Point :=
  (submoduleProj L.toAffine.direction, L.closestPoint)

lemma line2Embed_lipschitz : ∀ (L1 L2 : Line2),
    dist (line2Embed L1) (line2Embed L2) ≤ lineDist L1 L2 := by
  intro L1 L2
  have h1 : 0 ≤ lineDirDist L1 L2 := by
    simp [lineDirDist] <;> exact norm_nonneg _
  have h2 : 0 ≤ lineOffsetDist L1 L2 := by
    simp [lineOffsetDist] <;> exact dist_nonneg
  have h_main : dist (line2Embed L1) (line2Embed L2) =
      max (lineDirDist L1 L2) (lineOffsetDist L1 L2) := by
    simp [line2Embed, lineDirDist, lineOffsetDist, Prod.norm_def, dist_eq_norm] <;> rfl
  rw [h_main]
  have h3 : max (lineDirDist L1 L2) (lineOffsetDist L1 L2) ≤
      lineDirDist L1 L2 + lineOffsetDist L1 L2 := by
    exact max_le (by linarith) (by linarith)
  exact h3

lemma line2Embed_antilipschitz : ∀ (L1 L2 : Line2),
    lineDist L1 L2 ≤ 2 * dist (line2Embed L1) (line2Embed L2) := by
  intro L1 L2
  have h : lineDist L1 L2 = lineDirDist L1 L2 + lineOffsetDist L1 L2 := by rfl
  rw [h]
  have h2 : dist (line2Embed L1) (line2Embed L2) =
      max (lineDirDist L1 L2) (lineOffsetDist L1 L2) := by
    simp [line2Embed, lineDirDist, lineOffsetDist, Prod.norm_def, dist_eq_norm] <;> rfl
  rw [h2]
  have h3 : lineDirDist L1 L2 + lineOffsetDist L1 L2 ≤
      2 * max (lineDirDist L1 L2) (lineOffsetDist L1 L2) := by
    cases' le_total (lineDirDist L1 L2) (lineOffsetDist L1 L2) with h4 h4 <;> simp [h4] <;> linarith
  exact h3

/-- Line2 has uniform doubling via 2-bi-Lipschitz embedding into finite-dimensional normed space. -/
lemma Line2_exists_doubling :
    ∃ (D : ℕ), 0 < D ∧ ∀ (L : Line2) (ε : ℝ), 0 < ε →
      ∃ (S : Finset Line2), Metric.closedBall L (2 * ε) ⊆ ⋃ M ∈ S, Metric.closedBall M ε ∧ S.card ≤ D := by
  let E := (Point →L[ℝ] Point) × Point
  rcases exists_doubling_constant_normed (E := E) with ⟨D0, hD0_pos, hD0⟩
  let D := D0 * D0 * D0
  have hD_pos : 0 < D := by positivity
  refine' ⟨D, hD_pos, _⟩
  intro L ε hε
  let e : Line2 → E := line2Embed
  classical
  -- Cover closedBall(e(L), 2ε) in E with D0^3 balls of radius ε/4
  have h_step1 : ∃ (S1 : Finset E),
      Metric.closedBall (e L) (2 * ε) ⊆ ⋃ z ∈ S1, Metric.closedBall z ε ∧ S1.card ≤ D0 :=
    hD0 (e L) ε hε
  rcases h_step1 with ⟨S1, hS1_cover, hS1_card⟩
  -- Cover each ε-ball with ε/2 balls
  have h_half : ∀ (x : E), ∃ (Sx : Finset E),
      Metric.closedBall x ε ⊆ ⋃ z ∈ Sx, Metric.closedBall z (ε / 2) ∧ Sx.card ≤ D0 := by
    intro x
    have h := hD0 x (ε / 2) (by linarith)
    have h' : 2 * (ε / 2) = ε := by ring
    rcases h with ⟨Sx, hcov, hcard⟩
    rw [h'] at hcov
    exact ⟨Sx, hcov, hcard⟩
  choose Sx hSx_cover hSx_card using h_half
  let S2 : Finset E := S1.biUnion Sx
  have hS2_card : S2.card ≤ D0 * D0 := by
    calc S2.card ≤ ∑ x ∈ S1, (Sx x).card := Finset.card_biUnion_le
      _ ≤ ∑ _ ∈ S1, D0 := by gcongr; exact hSx_card ‹_›
      _ = S1.card * D0 := by simp [Finset.sum_const]
      _ ≤ D0 * D0 := by gcongr
  have hS2_cover : Metric.closedBall (e L) (2 * ε) ⊆ ⋃ z ∈ S2, Metric.closedBall z (ε / 2) := by
    intro w hw
    have h1' : ∃ (x : E), x ∈ (S1 : Set E) ∧ w ∈ Metric.closedBall x ε := by
      simpa [Set.mem_biUnion] using hS1_cover hw
    rcases h1' with ⟨x, hx, hwx⟩
    have h2' : ∃ (z : E), z ∈ (Sx x : Set E) ∧ w ∈ Metric.closedBall z (ε / 2) := by
      simpa [Set.mem_biUnion] using hSx_cover x hwx
    rcases h2' with ⟨z, hz, hwz⟩
    have hz2 : z ∈ S2 := by
      have h : ∃ (i : E), i ∈ S1 ∧ z ∈ Sx i := ⟨x, hx, hz⟩
      exact Finset.mem_biUnion.mpr h
    have h_final : w ∈ (⋃ (z : E) (_ : z ∈ S2), Metric.closedBall z (ε / 2)) := by
      simpa [Set.mem_biUnion] using ⟨z, hz2, hwz⟩
    exact h_final
  -- Cover each ε/2-ball with ε/4 balls
  have h_quarter : ∀ (x : E), ∃ (Sx : Finset E),
      Metric.closedBall x (ε / 2) ⊆ ⋃ z ∈ Sx, Metric.closedBall z (ε / 4) ∧ Sx.card ≤ D0 := by
    intro x
    have h := hD0 x (ε / 4) (by linarith)
    have h' : 2 * (ε / 4) = ε / 2 := by ring
    rcases h with ⟨Sx, hcov, hcard⟩
    rw [h'] at hcov
    exact ⟨Sx, hcov, hcard⟩
  choose Sy hSy_cover hSy_card using h_quarter
  let S3 : Finset E := S2.biUnion Sy
  have hS3_card : S3.card ≤ D := by
    calc S3.card ≤ ∑ x ∈ S2, (Sy x).card := Finset.card_biUnion_le
      _ ≤ ∑ _ ∈ S2, D0 := by gcongr; exact hSy_card ‹_›
      _ = S2.card * D0 := by simp [Finset.sum_const]
      _ ≤ (D0 * D0) * D0 := by gcongr
      _ = D := by ring
  have hS3_cover : Metric.closedBall (e L) (2 * ε) ⊆ ⋃ z ∈ S3, Metric.closedBall z (ε / 4) := by
    intro w hw
    have h1' : ∃ (z : E), z ∈ (S2 : Set E) ∧ w ∈ Metric.closedBall z (ε / 2) := by
      simpa [Set.mem_biUnion] using hS2_cover hw
    rcases h1' with ⟨z, hz, hwz⟩
    have h2' : ∃ (y : E), y ∈ (Sy z : Set E) ∧ w ∈ Metric.closedBall y (ε / 4) := by
      simpa [Set.mem_biUnion] using hSy_cover z hwz
    rcases h2' with ⟨y, hy, hwy⟩
    have hy2 : y ∈ S3 := by
      have h : ∃ (i : E), i ∈ S2 ∧ y ∈ Sy i := ⟨z, hz, hy⟩
      exact Finset.mem_biUnion.mpr h
    have h_final : w ∈ (⋃ (y : E) (_ : y ∈ S3), Metric.closedBall y (ε / 4)) := by
      simpa [Set.mem_biUnion] using ⟨y, hy2, hwy⟩
    exact h_final
  -- Pick Line2 points near each center in S3 that intersects e(Line2)
  let f : E → Finset Line2 := fun z =>
    if h : ∃ (M : Line2), dist (e M) z ≤ ε / 4 then
      ({Classical.choose h} : Finset Line2)
    else
      (∅ : Finset Line2)
  let S_Line2 : Finset Line2 := S3.biUnion f
  have h_f_card : ∀ z ∈ S3, (f z).card ≤ 1 := by
    intro z _
    dsimp only [f]
    split_ifs <;> simp [Finset.card_singleton] <;> omega
  have hS_Line2_card : S_Line2.card ≤ S3.card := by
    calc S_Line2.card ≤ ∑ z ∈ S3, (f z).card := Finset.card_biUnion_le
      _ ≤ ∑ z ∈ S3, 1 := by
        apply Finset.sum_le_sum
        intro i hi
        exact h_f_card i hi
      _ = S3.card := by simp
  have hS_Line2_cover : Metric.closedBall L (2 * ε) ⊆ ⋃ M ∈ S_Line2, Metric.closedBall M ε := by
    intro M hM
    have h_eM : e M ∈ Metric.closedBall (e L) (2 * ε) := by
      have h : dist (e M) (e L) ≤ dist M L := line2Embed_lipschitz M L
      have h' : dist M L ≤ 2 * ε := hM
      exact h.trans h'
    have h3 : ∃ z ∈ S3, e M ∈ Metric.closedBall z (ε / 4) := by
      simpa [Set.mem_iUnion] using hS3_cover h_eM
    rcases h3 with ⟨z, hz, h4⟩
    have h5 : dist (e M) z ≤ ε / 4 := h4
    have h_exists : ∃ (M' : Line2), dist (e M') z ≤ ε / 4 := ⟨M, h5⟩
    let M' : Line2 := Classical.choose h_exists
    have hM'_dist : dist (e M') z ≤ ε / 4 := Classical.choose_spec h_exists
    have hM'_in : M' ∈ S_Line2 := by
      have hz' : z ∈ S3 := hz
      have h_fz : M' ∈ f z := by
        dsimp only [f]
        rw [dif_pos h_exists]
        <;> simp [M']
      exact Finset.mem_biUnion.mpr ⟨z, hz', h_fz⟩
    have h6 : dist M M' ≤ ε := by
      calc dist M M' ≤ 2 * dist (e M) (e M') := line2Embed_antilipschitz M M'
        _ ≤ 2 * (dist (e M) z + dist z (e M')) := by gcongr; exact dist_triangle _ _ _
        _ ≤ 2 * (ε / 4 + ε / 4) := by gcongr; exact dist_comm z (e M') ▸ hM'_dist
        _ = ε := by ring
    exact Set.mem_iUnion₂.mpr ⟨M', hM'_in, h6⟩
  have h_final : S_Line2.card ≤ D := le_trans hS_Line2_card hS3_card
  exact ⟨S_Line2, hS_Line2_cover, h_final⟩

/-! ============================================================================
   3. External covering number doubling bound
   ============================================================================ -/

lemma extCov_doubling {X : Type*} [PseudoMetricSpace X] [DecidableEq X]
    (D : ℕ) (hD_pos : 0 < D)
    (h_double : ∀ (x : X) (ε : ℝ), 0 < ε →
      ∃ (S : Finset X), Metric.closedBall x (2 * ε) ⊆ ⋃ y ∈ S, Metric.closedBall y ε ∧ S.card ≤ D)
    {P : Set X} {ε : NNReal} (hε : 0 < ε) (hP_nonempty : P.Nonempty) :
    Metric.externalCoveringNumber ε P ≤ (D : ENat) * Metric.externalCoveringNumber (2 * ε) P := by
  have h_main : ∀ (C : Set X), Metric.IsCover (2 * ε) P C →
      Metric.externalCoveringNumber ε P ≤ (D : ENat) * C.encard := by
    intro C hC
    by_cases hC_finite : C.Finite
    · let Cfin : Finset X := hC_finite.toFinset
      have hC_coe : (Cfin : Set X) = C := hC_finite.coe_toFinset
      classical
      choose S hS_cover hS_card using fun c => h_double c (ε : ℝ) hε
      let C' : Finset X := Cfin.biUnion S
      have hC'_cover : Metric.IsCover ε P (C' : Set X) := by
        intro z hz
        rcases hC hz with ⟨c, hc, hdist⟩
        have hc' : c ∈ Cfin := by
          have h : c ∈ (Cfin : Set X) := by
            rw [hC_coe] <;> exact hc
          exact h
        have hzc : z ∈ Metric.closedBall c (2 * (ε : ℝ)) := by
          have h_edist : edist z c ≤ ↑(2 * ε) := hdist
          have h_dist : dist z c ≤ (2 * ε : ℝ) := by
            exact edist_le_coe.mp h_edist
          simpa [Metric.mem_closedBall] using h_dist
        have h_in_S : z ∈ ⋃ y ∈ S c, Metric.closedBall y (ε : ℝ) := hS_cover c hzc
        rcases Set.mem_iUnion₂.mp h_in_S with ⟨y, hy, hzy⟩
        have h_dist_y : dist z y ≤ (ε : ℝ) := by
          simpa [Metric.mem_closedBall] using hzy
        have hy' : y ∈ C' := by
          exact Finset.mem_biUnion.mpr ⟨c, hc', hy⟩
        have h_edist2 : edist z y ≤ ↑ε := by
          exact edist_le_coe.mpr h_dist_y
        exact ⟨y, hy', h_edist2⟩
      have h2 : Metric.externalCoveringNumber ε P ≤ (C'.card : ENat) := by
        have h : Metric.externalCoveringNumber ε P ≤ ((C' : Set X).encard) :=
          Metric.IsCover.externalCoveringNumber_le_encard hC'_cover
        have h' : ((C' : Set X).encard) = ↑C'.card := by simp
        rw [h'] at h
        exact h
      have h3 : C'.card ≤ D * Cfin.card := by
        calc C'.card ≤ ∑ c ∈ Cfin, (S c).card := Finset.card_biUnion_le
          _ ≤ ∑ _ ∈ Cfin, D := by gcongr; exact hS_card ‹_›
          _ = Cfin.card * D := by simp [Finset.sum_const]
          _ = D * Cfin.card := by ring
      have h4 : (C'.card : ENat) ≤ (D : ENat) * (C.encard : ENat) := by
        have h6 : C.encard = ↑Cfin.card := by
          rw [←hC_coe] <;> simp
        rw [h6]
        exact_mod_cast h3
      exact le_trans h2 h4
    · have h_top : C.encard = ⊤ := by
        exact Set.encard_eq_top_iff.mpr hC_finite
      rw [h_top]
      have h_mul_top : (D : ENat) * ⊤ = ⊤ := by
        simp [hD_pos.ne']
      rw [h_mul_top]
      exact le_top
  have hD_ne_zero : (D : ENat) ≠ 0 := by exact_mod_cast hD_pos.ne'
  have h_iInf : (⨅ (C : Set X) (_ : Metric.IsCover (2 * ε) P C), (D : ENat) * C.encard) =
      (D : ENat) * Metric.externalCoveringNumber (2 * ε) P := by
    have h1 : ∀ (C : Set X), (⨅ (_ : Metric.IsCover (2 * ε) P C), (D : ENat) * C.encard) =
        (D : ENat) * (⨅ (_ : Metric.IsCover (2 * ε) P C), C.encard) := by
      intro C
      rw [ENat.mul_iInf_of_ne hD_ne_zero]
    calc (⨅ (C : Set X) (_ : Metric.IsCover (2 * ε) P C), (D : ENat) * C.encard)
      = ⨅ (C : Set X), (⨅ (_ : Metric.IsCover (2 * ε) P C), (D : ENat) * C.encard) := by rfl
    _ = ⨅ (C : Set X), (D : ENat) * (⨅ (_ : Metric.IsCover (2 * ε) P C), C.encard) := by
        congr with C; exact h1 C
    _ = (D : ENat) * (⨅ (C : Set X), (⨅ (_ : Metric.IsCover (2 * ε) P C), C.encard)) := by
        rw [ENat.mul_iInf_of_ne hD_ne_zero]
    _ = (D : ENat) * Metric.externalCoveringNumber (2 * ε) P := by
        rw [Metric.externalCoveringNumber]
  have h5 : Metric.externalCoveringNumber ε P ≤ ⨅ (C : Set X) (_ : Metric.IsCover (2 * ε) P C), (D : ENat) * C.encard :=
    le_iInf_iff.mpr (fun C => le_iInf_iff.mpr (fun h => h_main C h))
  exact le_trans h5 (le_of_eq h_iInf)

/-! ============================================================================
   4. IsDeltaSet scale conversion: δ → 2δ
   ============================================================================ -/

lemma IsDeltaSet.scale_up {X : Type*} [PseudoMetricSpace X] [DecidableEq X]
    {P : Set X} {δ s C : ℝ} (hδ : 0 < δ) (hs : 0 ≤ s) (hC : 0 ≤ C)
    (h : IsDeltaSet δ s C hδ hs hC P)
    (D : ℕ) (hD_pos : 0 < D)
    (h_double : ∀ (x : X) (ε : ℝ), 0 < ε →
      ∃ (S : Finset X), Metric.closedBall x (2 * ε) ⊆ ⋃ y ∈ S, Metric.closedBall y ε ∧ S.card ≤ D)
    (hP_nonempty : P.Nonempty) :
    IsDeltaSet (2 * δ) s (C * (D : ℝ)) (by linarith) hs (by positivity) P := by
  let δn : NNReal := ⟨δ, hδ.le⟩
  let δ2n : NNReal := ⟨2 * δ, by linarith⟩
  have hδn_pos : 0 < δn := by exact_mod_cast hδ
  have h_double_bound : Metric.externalCoveringNumber δn P ≤ (D : ENat) * Metric.externalCoveringNumber δ2n P :=
    extCov_doubling D hD_pos h_double hδn_pos hP_nonempty
  intro x r' hr'
  have h1 : δ ≤ r' := by linarith
  have hr'_nonneg : 0 ≤ r' := by linarith
  have h_le : δn ≤ δ2n := by exact_mod_cast (show δ ≤ 2 * δ from by linarith)
  have h_anti : Metric.externalCoveringNumber δ2n (P ∩ ball x r') ≤ Metric.externalCoveringNumber δn (P ∩ ball x r') :=
    Metric.externalCoveringNumber_anti h_le
  have h_anti' : (Metric.externalCoveringNumber δ2n (P ∩ ball x r') : ENNReal) ≤
      (Metric.externalCoveringNumber δn (P ∩ ball x r') : ENNReal) := by
    exact_mod_cast h_anti
  have h_spec : (Metric.externalCoveringNumber δn (P ∩ ball x r') : ENNReal) ≤
      ENNReal.ofReal (C * Real.rpow r' s) * (Metric.externalCoveringNumber δn P : ENNReal) :=
    h.spec x r' h1
  have h_double' : (Metric.externalCoveringNumber δn P : ENNReal) ≤
      (D : ENNReal) * (Metric.externalCoveringNumber δ2n P : ENNReal) := by
    exact_mod_cast h_double_bound
  have h_rpow_nonneg : 0 ≤ Real.rpow r' s := Real.rpow_nonneg hr'_nonneg s
  have hpos1 : 0 ≤ C * Real.rpow r' s := mul_nonneg hC h_rpow_nonneg
  have h_step1 : (Metric.externalCoveringNumber δ2n (P ∩ ball x r') : ENNReal) ≤
      ENNReal.ofReal (C * Real.rpow r' s) * (Metric.externalCoveringNumber δn P : ENNReal) :=
    le_trans h_anti' h_spec
  have h_step2 : (Metric.externalCoveringNumber δ2n (P ∩ ball x r') : ENNReal) ≤
      ENNReal.ofReal (C * Real.rpow r' s) * ((D : ENNReal) * (Metric.externalCoveringNumber δ2n P : ENNReal)) :=
    le_trans h_step1 (by gcongr)
  have h_mul1 : ENNReal.ofReal (C * Real.rpow r' s) * ENNReal.ofReal ((D : ℝ)) =
      ENNReal.ofReal ((C * Real.rpow r' s) * (D : ℝ)) := by
    rw [←ENNReal.ofReal_mul hpos1]
  have h_ofReal_D : ENNReal.ofReal ((D : ℝ)) = (D : ENNReal) := by simp
  have h_mul : ENNReal.ofReal (C * Real.rpow r' s) * (D : ENNReal) =
      ENNReal.ofReal ((C * Real.rpow r' s) * (D : ℝ)) := by
    rw [←h_ofReal_D]
    exact h_mul1
  have h_ring : (C * Real.rpow r' s) * (D : ℝ) = C * (D : ℝ) * Real.rpow r' s := by ring
  have h_final : ENNReal.ofReal (C * Real.rpow r' s) * ((D : ENNReal) * (Metric.externalCoveringNumber δ2n P : ENNReal)) =
      ENNReal.ofReal (C * (D : ℝ) * Real.rpow r' s) * (Metric.externalCoveringNumber δ2n P : ENNReal) := by
    calc ENNReal.ofReal (C * Real.rpow r' s) * ((D : ENNReal) * (Metric.externalCoveringNumber δ2n P : ENNReal))
      = (ENNReal.ofReal (C * Real.rpow r' s) * (D : ENNReal)) * (Metric.externalCoveringNumber δ2n P : ENNReal) := by rw [mul_assoc]
    _ = ENNReal.ofReal ((C * Real.rpow r' s) * (D : ℝ)) * (Metric.externalCoveringNumber δ2n P : ENNReal) := by rw [h_mul]
    _ = ENNReal.ofReal (C * (D : ℝ) * Real.rpow r' s) * (Metric.externalCoveringNumber δ2n P : ENNReal) := by rw [h_ring]
  rw [h_final] at h_step2
  exact h_step2

/-! ============================================================================
   5. Main caller lemma
   ============================================================================ -/

lemma furstenberg_caller_lower_bound
    (σ : ℝ) (hσ : 0 < σ) (hσ_lt_one : σ < 1)
    (r εF : ℝ) (hr : 0 < r) (hr_small : r < 1) (hr2_small : 2 * r < 1)
    (hεF_pos : 0 < εF)
    (D_X D_T : ℕ) (hD_X_pos : 0 < D_X) (hD_T_pos : 0 < D_T)
    (h_double_X : ∀ (x : Point) (ε : ℝ), 0 < ε →
      ∃ (S : Finset Point), Metric.closedBall x (2 * ε) ⊆ ⋃ y ∈ S, Metric.closedBall y ε ∧ S.card ≤ D_X)
    (h_double_T : ∀ (L : Line2) (ε : ℝ), 0 < ε →
      ∃ (S : Finset Line2), Metric.closedBall L (2 * ε) ⊆ ⋃ M ∈ S, Metric.closedBall M ε ∧ S.card ≤ D_T)
    (ε_F δ₀ : ℝ) (hε_F_pos : 0 < ε_F) (hδ₀_pos : 0 < δ₀)
    (hF : ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ δ₀ →
      ∀ (X : Set Point) (T : Point → Set Line2),
        X.Nonempty → X ⊆ closedBall 0 1 →
        IsDeltaSet δ 1 (Real.rpow δ (-ε_F)) hδ (by norm_num) (Real.rpow_nonneg hδ.le _) X →
        (∀ x ∈ X, (T x).Nonempty ∧
          IsDeltaSet δ σ (Real.rpow δ (-ε_F)) hδ hσ.le (Real.rpow_nonneg hδ.le _) (T x) ∧
          ∀ ℓ ∈ T x, x ∈ tube δ ℓ) →
        Set.Finite (⋃ x ∈ X, T x) →
        (⋃ x ∈ X, T x).ncard ≥ Nat.ceil (Real.rpow δ (-2 * σ - ε_F)))
    (hεF_le : εF ≤ ε_F)
    (hδ_le : 2 * r ≤ δ₀)
    (X : Set Point) (T_x : Point → Set Line2)
    (hX_nonempty : X.Nonempty) (hX_ball : X ⊆ closedBall 0 1)
    (C_X : ℝ) (hC_X_nonneg : 0 ≤ C_X)
    (hX_delta : IsDeltaSet r 1 C_X hr (by norm_num) hC_X_nonneg X)
    (hC_X_bound : C_X * (D_X : ℝ) ≤ Real.rpow (2 * r) (-εF))
    (hT : ∀ x ∈ X, (T_x x).Nonempty ∧
      (∃ (C_T : ℝ) (hC_T_nonneg : 0 ≤ C_T),
        IsDeltaSet r σ C_T hr hσ.le hC_T_nonneg (T_x x) ∧
        C_T * (D_T : ℝ) ≤ Real.rpow (2 * r) (-εF)) ∧
      ∀ ℓ ∈ T_x x, x ∈ tube (2 * r) ℓ)
    (hfin : Set.Finite (⋃ x ∈ X, T_x x)) :
    (⋃ x ∈ X, T_x x).ncard ≥ ENNReal.ofReal (Real.rpow (2 * r) (-(2 * σ + εF))) := by
  let δ : ℝ := 2 * r
  have hδ_pos : 0 < δ := by linarith
  have hδ_lt_one : δ < 1 := hr2_small
  have hX_delta2 : IsDeltaSet δ 1 (C_X * (D_X : ℝ)) hδ_pos (by norm_num) (by positivity) X :=
    hX_delta.scale_up hr (by norm_num) hC_X_nonneg D_X hD_X_pos h_double_X hX_nonempty
  have hX_delta_F : IsDeltaSet δ 1 (Real.rpow δ (-εF)) hδ_pos (by norm_num) (Real.rpow_nonneg hδ_pos.le _) X :=
    IsDeltaSet.mono_C hX_delta2 (Real.rpow_nonneg hδ_pos.le _) hC_X_bound
  have hT2 : ∀ x ∈ X, (T_x x).Nonempty ∧
      IsDeltaSet δ σ (Real.rpow δ (-εF)) hδ_pos hσ.le (Real.rpow_nonneg hδ_pos.le _) (T_x x) ∧
      ∀ ℓ ∈ T_x x, x ∈ tube δ ℓ := by
    intro x hx
    have h1 := hT x hx
    rcases h1 with ⟨h_nonempty, ⟨C_T, hC_T_nonneg, hT_delta, h_bound⟩, h_tube⟩
    have h_boundδ : C_T * (D_T : ℝ) ≤ Real.rpow δ (-εF) := by
      have h_eq : Real.rpow δ (-εF) = Real.rpow (2 * r) (-εF) := by rfl
      rw [h_eq]
      exact h_bound
    have hT_delta2 : IsDeltaSet δ σ (C_T * (D_T : ℝ)) hδ_pos hσ.le (by positivity) (T_x x) :=
      hT_delta.scale_up hr hσ.le hC_T_nonneg D_T hD_T_pos h_double_T h_nonempty
    have hT_delta_F : IsDeltaSet δ σ (Real.rpow δ (-εF)) hδ_pos hσ.le (Real.rpow_nonneg hδ_pos.le _) (T_x x) :=
      IsDeltaSet.mono_C hT_delta2 (Real.rpow_nonneg hδ_pos.le _) h_boundδ
    exact ⟨h_nonempty, hT_delta_F, h_tube⟩
  have h_ncard := furstenberg_lower_bound_with_epsilon
    σ 1 hσ hσ_lt_one (by linarith) (by norm_num)
    ε_F δ₀ hε_F_pos hδ₀_pos hF εF hεF_pos hεF_le δ hδ_pos hδ_lt_one hδ_le
    X T_x hX_nonempty hX_ball hX_delta_F hT2 hfin
  have h9 : ((⋃ x ∈ X, T_x x).ncard : ℝ) ≥ Real.rpow δ (-2 * σ - εF) := by
    have h10 : ((⋃ x ∈ X, T_x x).ncard : ℝ) ≥ ↑(Nat.ceil (Real.rpow δ (-2 * σ - εF))) := by
      exact_mod_cast h_ncard
    have h11 : (↑(Nat.ceil (Real.rpow δ (-2 * σ - εF))) : ℝ) ≥ Real.rpow δ (-2 * σ - εF) := Nat.le_ceil _
    linarith
  have h13 : 0 ≤ Real.rpow δ (-2 * σ - εF) := Real.rpow_nonneg (by linarith) _
  have h14 : ENNReal.ofReal (Real.rpow δ (-2 * σ - εF)) ≤ ↑((⋃ x ∈ X, T_x x).ncard) := by
    have h141 : (Real.rpow δ (-2 * σ - εF) : ℝ) ≤ ((⋃ x ∈ X, T_x x).ncard : ℝ) := h9
    have h142 : ENNReal.ofReal (Real.rpow δ (-2 * σ - εF)) ≤ ENNReal.ofReal ((⋃ x ∈ X, T_x x).ncard : ℝ) :=
      ENNReal.ofReal_le_ofReal h141
    have h143 : ENNReal.ofReal ((⋃ x ∈ X, T_x x).ncard : ℝ) = ↑((⋃ x ∈ X, T_x x).ncard) := by
      simp
    rw [h143] at h142
    exact h142
  have h15 : Real.rpow (2 * r) (-(2 * σ + εF)) = Real.rpow δ (-2 * σ - εF) := by
    have h16 : δ = 2 * r := by rfl
    rw [h16]
    have h17 : -(2 * σ + εF) = -2 * σ - εF := by ring
    rw [h17]
  rw [h15]
  exact h14

end RadialBootstrapping

end
