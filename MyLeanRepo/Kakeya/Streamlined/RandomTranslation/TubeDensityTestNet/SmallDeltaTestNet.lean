import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.TubeDensityTestNet.RoundingLemma
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.TubeDensityTestNet.NetConstruction
import MyLeanRepo.Kakeya.Streamlined.JohnToFramedDimensions.FramedDimensions

/-!
# Small δ test net for tube density

For δ < 1/2, construct a finite test family from the grid of parallelepipeds.
The rounding lemma ensures every relevant convex body is contained in a test
set with volume at most `10^7` times the body volume.
-/

noncomputable section

open MeasureTheory Metric Finset
open scoped Pointwise
open Kakeya.Streamlined.GeometricLemmas
open Kakeya.Streamlined.RandomTranslation.TubeDensityTestNet

namespace Kakeya.Streamlined

/-- Grid parameter set for small δ. -/
def smallDeltaGrid (δ : ℝ) (hδ : 0 < δ) :
    Finset ((Point3 × Matrix (Fin 3) (Fin 3) ℝ) × (ℝ × ℝ × ℝ)) :=
  (centerGrid δ hδ ×ˢ frameMatrices (δ / 100) (by positivity)) ×ˢ dimTriples δ hδ

/-- All grid test parallelepipeds (including zero-volume ones). -/
def smallDeltaAllTestSets (δ : ℝ) (hδ : 0 < δ) : Finset (Set Point3) :=
  (smallDeltaGrid δ hδ).image (fun p =>
    testParallelepiped p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2)

/-- The actual test family: grid test sets with nonzero volume. -/
def smallDeltaTestSets (δ : ℝ) (hδ : 0 < δ) : Finset (Set Point3) :=
  (smallDeltaAllTestSets δ hδ).filter (fun K => volume K ≠ 0)

/-- Cardinality bound for the small-δ test family. -/
lemma smallDeltaTestSets_card_bound {δ : ℝ} (hδ : 0 < δ) (hδ_small : δ < 1 / 2) :
    ((smallDeltaTestSets δ hδ).card : ℝ) ≤ (1 / δ) ^ 200 := by
  have h1 : (smallDeltaTestSets δ hδ).card ≤ (smallDeltaAllTestSets δ hδ).card :=
    Finset.card_filter_le _ _
  have h2 : ((smallDeltaAllTestSets δ hδ).card : ℝ) ≤ ((smallDeltaGrid δ hδ).card : ℝ) :=
    Nat.cast_le.mpr Finset.card_image_le
  have h3 : ((smallDeltaGrid δ hδ).card : ℝ) =
      ((centerGrid δ hδ).card : ℝ) *
      ((frameMatrices (δ / 100) (by positivity)).card : ℝ) *
      ((dimTriples δ hδ).card : ℝ) := by
    simp [smallDeltaGrid, Finset.card_product] <;> ring_nf <;> norm_cast <;> ring
  rw [h3] at h2
  exact le_trans (Nat.cast_le.mpr h1) (le_trans h2 (grid_card_bound hδ hδ_small))

/-- For δ < 1/2, the polynomial-size test net. -/
def small_delta_test_net {δ : ℝ} (hδ : 0 < δ) (hδ_le_one : δ ≤ 1)
    (hδ_small : δ < 1 / 2) (L : ENNReal)
    (hL_one : 1 ≤ L) (hL_ne_top : L ≠ ⊤)
    (hL_big : (10^7 : ENNReal) ≤ L) :
    RandomTranslation.TubeDensityTestNet δ := by
  classical
  let allTestSets := smallDeltaAllTestSets δ hδ
  let testSets := smallDeltaTestSets δ hδ

  have h_all_valid : ∀ K ∈ allTestSets,
      Convex ℝ K ∧ MeasurableSet K ∧ volume K ≠ ⊤ ∧ K ⊆ closedBall (0 : Point3) 20 := by
    intro K hK
    simp only [allTestSets, smallDeltaAllTestSets, Finset.mem_image] at hK
    rcases hK with ⟨p, hp, rfl⟩
    have hp' : p.1 ∈ (centerGrid δ hδ ×ˢ frameMatrices (δ / 100) (by positivity)) ∧
        p.2 ∈ dimTriples δ hδ := by
      simpa [smallDeltaGrid, Finset.mem_product] using hp
    have hp1 : p.1.1 ∈ centerGrid δ hδ ∧ p.1.2 ∈ frameMatrices (δ / 100) (by positivity) := by
      simpa [Finset.mem_product] using hp'.1
    exact test_set_valid hδ hδ_le_one p.1.1 hp1.1 p.1.2 hp1.2 p.2.1 p.2.2.1 p.2.2.2 hp'.2

  have h_testSets_convex : ∀ K ∈ testSets, Convex ℝ K := by
    intro K hK
    have hK' : K ∈ allTestSets := (Finset.mem_filter.mp hK).1
    exact (h_all_valid K hK').1

  have h_testSets_measurable : ∀ K ∈ testSets, MeasurableSet K := by
    intro K hK
    have hK' : K ∈ allTestSets := (Finset.mem_filter.mp hK).1
    exact (h_all_valid K hK').2.1

  have h_testSets_volume_pos : ∀ K ∈ testSets, 0 < volume K := by
    intro K hK
    have h_ne_zero : volume K ≠ 0 := (Finset.mem_filter.mp hK).2
    exact bot_lt_iff_ne_bot.mpr h_ne_zero

  have h_testSets_volume_ne_top : ∀ K ∈ testSets, volume K ≠ ⊤ := by
    intro K hK
    have hK' : K ∈ allTestSets := (Finset.mem_filter.mp hK).1
    exact (h_all_valid K hK').2.2.1

  have h_testSets_supported : ∀ K ∈ testSets, K ⊆ closedBall (0 : Point3) 20 := by
    intro K hK
    have hK' : K ∈ allTestSets := (Finset.mem_filter.mp hK).1
    exact (h_all_valid K hK').2.2.2

  have h_testSets_closed : ∀ K ∈ testSets, IsClosed K := by
    intro K hK
    have hK' : K ∈ allTestSets := (Finset.mem_filter.mp hK).1
    simp only [allTestSets, smallDeltaAllTestSets, Finset.mem_image] at hK'
    rcases hK' with ⟨p, _, rfl⟩
    exact testParallelepiped_isClosed p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2

  have h_density_suffices :
      ∀ (G : TubeFamily δ),
        (∀ i, (G.tube i).carrier ⊆ closedBall (0 : Point3) 10) →
        ∀ (C : ENNReal),
          (∀ K ∈ testSets, G.toBodyFamily.density K ≤ C) →
          G.toBodyFamily.deltaMax ≤ L * C := by
    intro G hG C hC
    let F := G.toBodyFamily
    rcases deltaMax_attained F with ⟨W, hW_convex, hW_density⟩

    by_cases h_zero : F.deltaMax = 0
    · rw [h_zero] <;> simp

    have h_density_pos : 0 < F.density W := by
      rw [hW_density]; exact bot_lt_iff_ne_bot.mpr h_zero
    have h_mass_pos : 0 < F.containedMass W := by
      by_contra h
      have h' : F.containedMass W = 0 := by simpa using h
      have h_density_zero : F.density W = 0 := by
        dsimp only [BodyFamily.density]; rw [h'] <;> simp
      rw [h_density_zero] at h_density_pos
      exact False.elim (lt_irrefl 0 h_density_pos)
    have h_indices_nonempty : (F.containedIndices W).Nonempty := by
      by_contra h
      have h' : F.containedIndices W = ∅ := by simpa using h
      have h'' : F.containedMass W = 0 := by
        rw [BodyFamily.containedMass, h'] <;> simp
      exact h_mass_pos.ne' h''
    rcases h_indices_nonempty with ⟨i, hi⟩
    have h_tube_sub_W : (G.tube i).carrier ⊆ W := by
      have h_i_in : i ∈ F.containedIndices W := hi
      have h' : (F.body i).carrier ⊆ W := by
        simpa [BodyFamily.containedIndices, Finset.mem_filter] using h_i_in
      have h_eq : (G.tube i).carrier = (F.body i).carrier := by rfl
      rw [h_eq]; exact h'

    let B10 : Set Point3 := closedBall (0 : Point3) 10
    let V : Set Point3 := W ∩ B10

    have hB10_convex : Convex ℝ B10 := convex_closedBall (0 : Point3) 10
    have hV_convex : Convex ℝ V := Convex.inter hW_convex hB10_convex
    have hV_sub_B10 : V ⊆ B10 := by simp [V]
    have hV_sub_W : V ⊆ W := by simp [V]

    have h_indices_eq : F.containedIndices V = F.containedIndices W := by
      ext j
      simp only [BodyFamily.containedIndices, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h; exact subset_trans h hV_sub_W
      · intro h
        have hB : (F.body j).carrier ⊆ B10 := by
          have h_eq : (G.tube j).carrier = (F.body j).carrier := by rfl
          rw [←h_eq]; exact hG j
        intro x hx; exact ⟨h hx, hB hx⟩
    have h_mass_eq : F.containedMass V = F.containedMass W := by
      dsimp only [BodyFamily.containedMass]
      rw [h_indices_eq]

    have h_vol_V_le_W : volume V ≤ volume W := measure_mono hV_sub_W

    have h_density_V_ge : F.density W ≤ F.density V := by
      dsimp only [BodyFamily.density]
      rw [h_mass_eq]
      exact ENNReal.div_le_div (le_refl _) h_vol_V_le_W

    have h_density_V_le : F.density V ≤ F.deltaMax := by
      apply le_csSup (by simp)
      exact ⟨V, hV_convex, rfl⟩

    have h_density_V_eq : F.density V = F.deltaMax := by
      rw [hW_density] at h_density_V_ge
      exact le_antisymm h_density_V_le h_density_V_ge

    have h_vol_W_pos : 0 < volume W := by
      have h_tube_interior : (interior (G.tube i).carrier).Nonempty :=
        RandomTranslation.deltaTube_nonempty_interior hδ (G.tube i)
      have h : interior (G.tube i).carrier ⊆ interior W := interior_mono h_tube_sub_W
      exact MeasureTheory.Measure.measure_pos_of_nonempty_interior volume (h_tube_interior.mono h)

    have h_vol_W_ne_top : volume W ≠ ⊤ := by
      by_contra h_top
      have h_density_zero : F.density W = 0 := by
        dsimp only [BodyFamily.density]; rw [h_top] <;> simp
      rw [h_density_zero] at h_density_pos
      exact False.elim (lt_irrefl 0 h_density_pos)

    have h_vol_V_pos : 0 < volume V := by
      have h_tube_sub_V : (G.tube i).carrier ⊆ V := by
        intro x hx
        exact ⟨h_tube_sub_W hx, hG i hx⟩
      have h_tube_interior : (interior (G.tube i).carrier).Nonempty :=
        RandomTranslation.deltaTube_nonempty_interior hδ (G.tube i)
      have h : interior (G.tube i).carrier ⊆ interior V := interior_mono h_tube_sub_V
      exact MeasureTheory.Measure.measure_pos_of_nonempty_interior volume (h_tube_interior.mono h)

    have h_vol_V_ne_top : volume V ≠ ⊤ :=
      ne_top_of_le_ne_top (Metric.isBounded_closedBall.measure_lt_top.ne) (measure_mono hV_sub_B10)

    have h_mass_ne_top : F.containedMass W ≠ ⊤ := by
      have h : F.containedMass W ≤ F.mass := by
        dsimp only [BodyFamily.containedMass, BodyFamily.mass]
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro _ _ _; simp
      have hF_mass_ne_top : F.mass ≠ ⊤ := by
        dsimp only [BodyFamily.mass]
        rw [ENNReal.sum_ne_top]
        intro j _
        have h_bdd : Bornology.IsBounded (F.body j).carrier :=
          Metric.isBounded_closedBall.subset (hG j)
        exact h_bdd.measure_lt_top.ne
      exact ne_top_of_le_ne_top hF_mass_ne_top h

    let W' : Set Point3 := closure V

    have hW'_closed : IsClosed W' := isClosed_closure
    have hW'_sub_B10 : W' ⊆ B10 := closure_minimal hV_sub_B10 Metric.isClosed_closedBall
    have hW'_bounded : Bornology.IsBounded W' :=
      Metric.isBounded_closedBall.subset hW'_sub_B10
    have hW'_compact : IsCompact W' :=
      Metric.isCompact_of_isClosed_isBounded hW'_closed hW'_bounded
    have hW'_convex : Convex ℝ W' := Convex.closure hV_convex
    have hW'_interior : (interior W').Nonempty := by
      have h_tube_sub_V : (G.tube i).carrier ⊆ V := by
        intro x hx; exact ⟨h_tube_sub_W hx, hG i hx⟩
      have h_tube_interior : (interior (G.tube i).carrier).Nonempty :=
        RandomTranslation.deltaTube_nonempty_interior hδ (G.tube i)
      have h : interior (G.tube i).carrier ⊆ interior W' :=
        interior_mono (subset_trans h_tube_sub_V subset_closure)
      exact h_tube_interior.mono h

    have h_vol_W'_eq_V : volume W' = volume V := by
      have h_frontier_null : volume (frontier V) = 0 := Convex.addHaar_frontier volume hV_convex
      have h1 : W' = V ∪ frontier V := by
        ext x; simp [W', closure_eq_self_union_frontier]
      rw [h1]
      have h2 : volume (V ∪ frontier V) ≤ volume V + volume (frontier V) := measure_union_le _ _
      have h3 : volume (V ∪ frontier V) ≤ volume V := by
        rw [h_frontier_null] at h2; simpa using h2
      have h4 : volume V ≤ volume (V ∪ frontier V) := measure_mono (by intro x hx; exact Or.inl hx)
      exact le_antisymm h3 h4

    have h_ball : ∃ (p : Point3), ball p δ ⊆ W' := by
      refine ⟨(G.tube i).base, ?_⟩
      have h1 : closedBall (G.tube i).base δ ⊆ (G.tube i).carrier :=
        tube_contains_ball hδ (G.tube i)
      have h2 : ball (G.tube i).base δ ⊆ closedBall (G.tube i).base δ := ball_subset_closedBall
      have h3 : (G.tube i).carrier ⊆ V := by
        intro x hx; exact ⟨h_tube_sub_W hx, hG i hx⟩
      exact subset_trans h2 (subset_trans h1 (subset_trans h3 subset_closure))

    rcases john_to_framed_dimensions_with_bound with ⟨A_john, hA_john_one, hA_john_le, hJohn⟩
    let K_body : Body := ⟨W'⟩
    have hK_body : JohnEllipsoid.IsConvexBody W' :=
      ⟨hW'_convex, hW'_compact, hW'_interior⟩
    rcases hJohn K_body hK_body with ⟨a, b, c_dim, frame, h_dims_frame⟩
    have ha : 0 < a := h_dims_frame.1
    have hab : a ≤ b := h_dims_frame.2.1
    have hbc : b ≤ c_dim := h_dims_frame.2.2.1
    have hA_john_one' : 1 ≤ A_john := h_dims_frame.2.2.2.1
    have h_inner : frame '' axisBox a b c_dim ⊆ W' := h_dims_frame.2.2.2.2.1
    have h_outer : W' ⊆ frame '' axisBox (A_john * a) (A_john * b) (A_john * c_dim) :=
      h_dims_frame.2.2.2.2.2
    have hb : 0 < b := lt_of_lt_of_le ha hab
    have hc : 0 < c_dim := lt_of_lt_of_le hb hbc

    rcases rounding_lemma hδ hδ_le_one W' hW'_convex hW'_compact hW'_interior hW'_sub_B10
        a b c_dim A_john ha hb hc hab hbc hA_john_one' hA_john_le frame h_inner h_outer h_ball
        L hL_ne_top hL_big
      with ⟨center, hc_grid, M, hM, a', b', c', h_dims', h_containment, h_vol_bound⟩

    let T := testParallelepiped center M a' b' c'

    have hT_in_all : T ∈ allTestSets := by
      simp only [allTestSets, smallDeltaAllTestSets, Finset.mem_image]
      refine ⟨((center, M), (a', (b', c'))), ?_, rfl⟩
      simp only [smallDeltaGrid, Finset.mem_product]
      exact ⟨⟨hc_grid, hM⟩, h_dims'⟩

    have hT_vol_pos : 0 < volume T := by
      have h1 : 0 < volume W' := by rw [h_vol_W'_eq_V]; exact h_vol_V_pos
      exact lt_of_lt_of_le h1 (measure_mono h_containment)
    have hT_ne_zero : volume T ≠ 0 := hT_vol_pos.ne'

    have hT_in : T ∈ testSets := by
      simp only [testSets, smallDeltaTestSets, Finset.mem_filter]
      exact ⟨hT_in_all, hT_ne_zero⟩

    have h_mass_le : F.containedMass W ≤ F.containedMass T := by
      dsimp only [BodyFamily.containedMass]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj
        simp only [BodyFamily.containedIndices, Finset.mem_filter] at hj ⊢
        have h_tube_in_W : (F.body j).carrier ⊆ W := hj.2
        have h_tube_in_V : (F.body j).carrier ⊆ V := by
          intro x hx
          exact ⟨h_tube_in_W hx, hG j hx⟩
        exact ⟨hj.1, subset_trans (subset_trans h_tube_in_V subset_closure) h_containment⟩
      · intro _ _ _; simp

    have h_vol_le : volume T ≤ L * volume W := by
      calc volume T
        ≤ L * volume W' := h_vol_bound
      _ = L * volume V := by rw [h_vol_W'_eq_V]
      _ ≤ L * volume W := mul_le_mul_of_nonneg_left h_vol_V_le_W (by positivity)

    have h_density_T : F.density T ≤ C := hC T hT_in

    have hT_vol_ne_top : volume T ≠ ⊤ := (h_all_valid T hT_in_all).2.2.1

    have h_density_le : F.density W ≤ L * F.density T :=
      ennreal_density_ineq
        (F.containedMass W) (volume W) (F.containedMass T) (volume T) L
        hL_one hL_ne_top h_mass_le h_vol_le
        h_vol_W_pos hT_vol_pos h_vol_W_ne_top hT_vol_ne_top

    have h_final : F.deltaMax ≤ L * F.density T := by
      rw [←hW_density]; exact h_density_le

    exact le_trans h_final (mul_le_mul_of_nonneg_left h_density_T (by positivity))

  exact
    { testSets := testSets
      testSets_convex := h_testSets_convex
      testSets_measurable := h_testSets_measurable
      testSets_volume_pos := h_testSets_volume_pos
      testSets_volume_ne_top := h_testSets_volume_ne_top
      testSets_supported := h_testSets_supported
      testSets_closed := h_testSets_closed
      lossFactor := L
      one_le_lossFactor := hL_one
      lossFactor_ne_top := hL_ne_top
      density_suffices := h_density_suffices }

/-- Cardinality bound for the small-δ test net. -/
lemma small_delta_test_net_card_bound {δ : ℝ} (hδ : 0 < δ) (hδ_le_one : δ ≤ 1)
    (hδ_small : δ < 1 / 2) (L : ENNReal)
    (hL_one : 1 ≤ L) (hL_ne_top : L ≠ ⊤)
    (hL_big : (10^7 : ENNReal) ≤ L) :
    ((small_delta_test_net hδ hδ_le_one hδ_small L hL_one hL_ne_top hL_big).testSets.card : ℝ)
    ≤ (1 / δ) ^ 200 := by
  have h_eq : (small_delta_test_net hδ hδ_le_one hδ_small L hL_one hL_ne_top hL_big).testSets =
      smallDeltaTestSets δ hδ := by
    rfl
  rw [h_eq]
  exact smallDeltaTestSets_card_bound hδ hδ_small

end Kakeya.Streamlined
