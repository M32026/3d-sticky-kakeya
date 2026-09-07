module

/-
  Fixed-scale adapter: dyadic configuration at δ_n → Appendix A alternative at δ' = 9δ_n.

  Builds on indigo's helper lemmas in `.scratch/indigo/FixedScaleAdapter.lean`:
  - `incidence_to_affine_line_9δ`
  - `toAffineLine_packing_9δ` (constant 628849)

  Provides:
  1. `toAffineLine_dyadic_card_to_ncover_9δ` — card/RegularIncidence.Ncover bound at 9δ
  2. `toAffineLine_finiteTubeSSet_to_affineSSet_9δ` — IsFiniteTubeSSet → IsDeltaSSet(9δ)
  3. `toAffineLine_tubeSSet_transfer_9δ` — full IsDeltaSSet(δ) → IsDeltaSSet(9δ) chain
  4. `apply_appendix_a_to_dyadic` — main adapter with absorption hypotheses

  Tube transfer constant: `max 1 (10 * C_T) * 628849 * 44^s`.
  The 44 = 2 * 22 comes from the co-Lipschitz bound and triangle inequality.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.DiscretisedFurstenbergEstimate.RegularIncidence.Definitions
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.CarrierTransfer
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicToAffineAdapters
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicCardToNcover
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Bridge_SSetTransfer
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Contracts.AppendixA
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.UniformIncidenceData
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal Classical

noncomputable section

namespace DiscretisedFurstenbergEstimate.FixedScaleAdapter

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.RegularIncidence
open DirecretisedFurstenbergEstimate.CarrierTransfer
open DyadicToAffineAdapters
open DyadicCardToNcover
open DiscretisedFurstenbergEstimate.InductionOnScales

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-! ============================================================================
   0. Packing bound for toAffineLine image at 9δ (from indigo)

   Constant: 628849 = 793^2 = (2*396+1)^2.
   Via 22-co-Lipschitz: diam 18δ → param ball 396δ → 793×793 integer grid.
   ============================================================================ -/

def toAffinePackingConst : ℕ := 628849

/-- At most toAffinePackingConst tubes map into a 9δ-ball. -/
lemma toAffineLine_packing_9δ {n : ℕ} {S : Finset (DyadicTube n)}
    (hm : ∀ T ∈ S, |T.slope| ≤ 1)
    (hb : ∀ T ∈ S, |T.intercept| ≤ 3)
    (c : AffineLine) :
    (S.filter (fun T => toAffineLine T ∈ Metric.closedBall c ((9 * dyadicDelta n).toNNReal))).card ≤
      toAffinePackingConst := by
  classical
  set δ := dyadicDelta n with hδ
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  set δ9 := 9 * δ with hδ9
  have hδ9_pos : 0 < δ9 := by positivity
  have hδ9_nn_coe : ((δ9.toNNReal) : ℝ) = δ9 := by
    simp [hδ9_pos.le]
  let G : Finset (DyadicTube n) :=
    S.filter (fun T => toAffineLine T ∈ Metric.closedBall c ((9 * dyadicDelta n).toNNReal))
  change G.card ≤ toAffinePackingConst
  by_cases hG_nonempty : G.Nonempty
  · rcases hG_nonempty with ⟨T0, hT0⟩
    have hT0_in_S : T0 ∈ S := (Finset.mem_filter.mp hT0).1
    have hT0_ball : toAffineLine T0 ∈ Metric.closedBall c ((9 * dyadicDelta n).toNNReal) :=
      (Finset.mem_filter.mp hT0).2
    have h_dist0 : dist (toAffineLine T0) c ≤ δ9 := by
      have h'' : dist (toAffineLine T0) c ≤ (((9 * dyadicDelta n).toNNReal) : ℝ) := by
        simpa [Metric.mem_closedBall] using hT0_ball
      have h_coe : (((9 * dyadicDelta n).toNNReal) : ℝ) = δ9 := by
        simp [hδ9, hδ, hδ9_pos.le] <;> exact Std.le_of_lt hδ_pos
      rw [h_coe] at h''
      exact h''
    have h_ball : ∀ T ∈ G, paramDistLinf T T0 ≤ 44 * δ9 := by
      intro T hT
      have hT_in_S : T ∈ S := (Finset.mem_filter.mp hT).1
      have hT_ball : toAffineLine T ∈ Metric.closedBall c ((9 * dyadicDelta n).toNNReal) :=
        (Finset.mem_filter.mp hT).2
      have h_distT : dist (toAffineLine T) c ≤ δ9 := by
        have h'' : dist (toAffineLine T) c ≤ (((9 * dyadicDelta n).toNNReal) : ℝ) := by
          simpa [Metric.mem_closedBall] using hT_ball
        have h_coe : (((9 * dyadicDelta n).toNNReal) : ℝ) = δ9 := by
          simp [hδ9, hδ, hδ9_pos.le] <;> exact Std.le_of_lt hδ_pos
        rw [h_coe] at h''
        exact h''
      have h_coLip : paramDistLinf T T0 ≤ 22 * dist (toAffineLine T) (toAffineLine T0) :=
        toAffineLine_co_lipschitz T T0 (hm T hT_in_S) (hm T0 hT0_in_S) (hb T0 hT0_in_S)
      have h_tri : dist (toAffineLine T) (toAffineLine T0) ≤ 2 * δ9 := by
        calc
          dist (toAffineLine T) (toAffineLine T0)
            ≤ dist (toAffineLine T) c + dist c (toAffineLine T0) := dist_triangle _ _ _
          _ = dist (toAffineLine T) c + dist (toAffineLine T0) c := by rw [dist_comm c _]
          _ ≤ δ9 + δ9 := by gcongr
          _ = 2 * δ9 := by ring
      calc paramDistLinf T T0
          ≤ 22 * dist (toAffineLine T) (toAffineLine T0) := h_coLip
        _ ≤ 22 * (2 * δ9) := by gcongr
        _ = 44 * δ9 := by ring
    have h_bound : ∀ T ∈ G, |(T.a : ℤ) - T0.a| ≤ 396 ∧ |(T.b : ℤ) - T0.b| ≤ 396 := by
      intro T hT
      have h_param : paramDistLinf T T0 ≤ 44 * δ9 := h_ball T hT
      have h_slope_diff : |T.slope - T0.slope| ≤ paramDistLinf T T0 := by
        dsimp only [paramDistLinf]; exact le_max_left _ _
      have h_intercept_diff : |T.intercept - T0.intercept| ≤ paramDistLinf T T0 := by
        dsimp only [paramDistLinf]; exact le_max_right _ _
      have h_slope_le : |T.slope - T0.slope| ≤ 44 * δ9 := le_trans h_slope_diff h_param
      have h_intercept_le : |T.intercept - T0.intercept| ≤ 44 * δ9 :=
        le_trans h_intercept_diff h_param
      have h_slope_eq : T.slope - T0.slope = δ * ((T.a : ℝ) - (T0.a : ℝ)) := by
        simp [DyadicTube.slope, hδ] <;> ring
      have h_intercept_eq : T.intercept - T0.intercept = δ * ((T.b : ℝ) - (T0.b : ℝ)) := by
        simp [DyadicTube.intercept, hδ] <;> ring
      have h_a_abs : δ * |(T.a : ℝ) - (T0.a : ℝ)| ≤ 44 * δ9 := by
        have h : |T.slope - T0.slope| = δ * |(T.a : ℝ) - (T0.a : ℝ)| := by
          rw [h_slope_eq, abs_mul, abs_of_pos hδ_pos]
        rw [h] at h_slope_le
        exact h_slope_le
      have h_b_abs : δ * |(T.b : ℝ) - (T0.b : ℝ)| ≤ 44 * δ9 := by
        have h : |T.intercept - T0.intercept| = δ * |(T.b : ℝ) - (T0.b : ℝ)| := by
          rw [h_intercept_eq, abs_mul, abs_of_pos hδ_pos]
        rw [h] at h_intercept_le
        exact h_intercept_le
      have h_a396 : |(T.a : ℝ) - (T0.a : ℝ)| ≤ 396 := by
        have h : 44 * δ9 = 396 * δ := by simp [hδ9, hδ] <;> ring
        rw [h] at h_a_abs
        nlinarith [hδ_pos]
      have h_b396 : |(T.b : ℝ) - (T0.b : ℝ)| ≤ 396 := by
        have h : 44 * δ9 = 396 * δ := by simp [hδ9, hδ] <;> ring
        rw [h] at h_b_abs
        nlinarith [hδ_pos]
      have ha_int : |(T.a - T0.a : ℤ)| ≤ 396 := by exact_mod_cast h_a396
      have hb_int : |(T.b - T0.b : ℤ)| ≤ 396 := by exact_mod_cast h_b396
      exact ⟨ha_int, hb_int⟩
    let G_pairs : Finset (ℤ × ℤ) := G.image (fun T => (T.a, T.b))
    have h_inj : Set.InjOn (fun (T : DyadicTube n) => (T.a, T.b)) (G : Set (DyadicTube n)) := by
      intro T1 hT1 T2 hT2 h
      have ha : T1.a = T2.a := by simp [Prod.ext_iff] at h <;> tauto
      have hb : T1.b = T2.b := by simp [Prod.ext_iff] at h <;> tauto
      cases T1 <;> cases T2 <;> simp_all <;> tauto
    have h_card : G.card = G_pairs.card := by
      rw [← Finset.card_image_of_injOn h_inj]
    let H := Finset.Icc (T0.a - 396) (T0.a + 396) ×ˢ Finset.Icc (T0.b - 396) (T0.b + 396)
    have h_sub : G_pairs ⊆ H := by
      intro p hp
      rcases Finset.mem_image.mp hp with ⟨T, hT, rfl⟩
      have h := h_bound T hT
      have ha1 : -(396 : ℤ) ≤ T.a - T0.a := (abs_le.mp h.1).1
      have ha2 : T.a - T0.a ≤ (396 : ℤ) := (abs_le.mp h.1).2
      have hb1 : -(396 : ℤ) ≤ T.b - T0.b := (abs_le.mp h.2).1
      have hb2 : T.b - T0.b ≤ (396 : ℤ) := (abs_le.mp h.2).2
      have ha : T.a ∈ Finset.Icc (T0.a - 396) (T0.a + 396) := by
        simp only [Finset.mem_Icc] <;> constructor <;> linarith
      have hb : T.b ∈ Finset.Icc (T0.b - 396) (T0.b + 396) := by
        simp only [Finset.mem_Icc] <;> constructor <;> linarith
      simp only [H, Finset.mem_product] <;> exact ⟨ha, hb⟩
    have h_final : G.card ≤ H.card := by
      rw [h_card]
      exact Finset.card_le_card h_sub
    have h_card2 : H.card =
        (Finset.Icc (T0.a - 396) (T0.a + 396)).card *
        (Finset.Icc (T0.b - 396) (T0.b + 396)).card := by
      rw [Finset.card_product]
    rw [h_card2] at h_final
    have h_Icc1 : ∀ (x : ℤ), (Finset.Icc (x - 396) (x + 396)).card = 793 := by
      intro x
      rw [Int.card_Icc] <;> norm_num <;> omega
    rw [h_Icc1 T0.a, h_Icc1 T0.b] at h_final
    have h_goal : G.card ≤ toAffinePackingConst := by
      simpa [toAffinePackingConst] using h_final
    exact h_goal
  · have h_empty : G = ∅ := Finset.not_nonempty_iff_eq_empty.mp hG_nonempty
    have h_goal : G.card ≤ toAffinePackingConst := by
      rw [h_empty] <;> simp [toAffinePackingConst] <;> norm_num
    exact h_goal

/-! ============================================================================
   1. Card-to-RegularIncidence.Ncover at 9δ for toAffineLine image

   Uses toAffineLine_packing_9δ (constant 628849) from indigo.
   ============================================================================ -/

/-- `|S| / 628849 ≤ RegularIncidence.Ncover(9δ, toAffineLine '' S)`. -/
lemma toAffineLine_dyadic_card_to_ncover_9δ {n : ℕ} (S : Finset (DyadicTube n))
    (hm : ∀ T ∈ S, |T.slope| ≤ 1)
    (hb : ∀ T ∈ S, |T.intercept| ≤ 3) :
    ENNReal.ofReal ((S.card : ℝ) / 628849) ≤
      Metric.externalCoveringNumber (9 * dyadicDelta n).toNNReal
        (toAffineLine '' (S : Set (DyadicTube n))) := by
  classical
  set δ := dyadicDelta n with hδ
  set δ9 := 9 * δ with hδ9
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  have hδ9_pos : 0 < δ9 := by positivity
  set δ9_nn := δ9.toNNReal with hδ9_nn
  have hδ9_nn_coe : (δ9_nn : ℝ) = δ9 := by
    simp [hδ9_nn, hδ9_pos.le]
  set A : Set AffineLine := toAffineLine '' (S : Set (DyadicTube n)) with hA_def
  have hA_fin : A.Finite := Set.Finite.image _ (S.finite_toSet)
  have hcover_A : Metric.IsCover δ9_nn A A := by
    intro x hx; exact ⟨x, hx, by simp [Metric.IsCover, edist_dist]⟩
  let ι := {C : Set AffineLine // Metric.IsCover δ9_nn A C}
  have hι_nonempty : Nonempty ι := ⟨⟨A, hcover_A⟩⟩
  let f : ι → ℕ∞ := fun C => (C.val).encard
  have h_exists : ∃ (C : ι), f C = ⨅ (x : ι), f x := ENat.exists_eq_iInf f
  rcases h_exists with ⟨C_min, hC_min_eq⟩
  have h_ext_def : Metric.externalCoveringNumber δ9_nn A = ⨅ (C : ι), f C := by
    have h : Metric.externalCoveringNumber δ9_nn A =
        ⨅ (C : Set AffineLine) (_ : Metric.IsCover δ9_nn A C), C.encard := by rfl
    rw [h]
    have h2 : (⨅ (C : Set AffineLine) (_ : Metric.IsCover δ9_nn A C), C.encard) = ⨅ (C : ι), f C := by
      rw [iInf_subtype] <;> rfl
    rw [h2]
  have h_encard_eq : (C_min.val).encard = Metric.externalCoveringNumber δ9_nn A := by
    have h10 : f C_min = Metric.externalCoveringNumber δ9_nn A := by
      rw [hC_min_eq, h_ext_def]
    simpa [f] using h10
  have h_fin : (C_min.val).Finite := by
    have h1 : Metric.externalCoveringNumber δ9_nn A ≤ A.encard :=
      Metric.externalCoveringNumber_le_encard_self A
    rw [←h_encard_eq] at h1
    exact Set.encard_lt_top_iff.mp (h1.trans_lt (hA_fin.encard_lt_top))
  let C_finset : Finset AffineLine := h_fin.toFinset
  have hC_coe : (C_finset : Set AffineLine) = C_min.val := by exact Set.Finite.coe_toFinset h_fin
  have h_edist_dist : ∀ (x c : AffineLine), edist x c ≤ (δ9_nn : ENNReal) ↔ dist x c ≤ δ9 := by
    intro x c
    simp [edist_dist, hδ9_nn_coe]
  have h_cover : ∀ (x : AffineLine), x ∈ A → ∃ (c : AffineLine), c ∈ C_finset ∧ x ∈ Metric.closedBall c δ9_nn := by
    intro x hx
    have h2 := C_min.property hx
    rcases h2 with ⟨c, hc, hball⟩
    have hball' : x ∈ Metric.closedBall c δ9_nn := by
      simpa [Metric.mem_closedBall, (h_edist_dist x c)] using hball
    have hc' : c ∈ C_finset := by
      have h1 : c ∈ (C_finset : Set AffineLine) := by rw [hC_coe] <;> exact hc
      simpa using h1
    exact ⟨c, hc', hball'⟩
  let S_c : AffineLine → Finset (DyadicTube n) := fun c =>
    S.filter (fun T => toAffineLine T ∈ Metric.closedBall c δ9_nn)
  have h_union : S ⊆ Finset.biUnion C_finset S_c := by
    intro T hT
    have hT_in_A : toAffineLine T ∈ A := by exact ⟨T, hT, rfl⟩
    rcases h_cover (toAffineLine T) hT_in_A with ⟨c, hc, hball⟩
    have h3 : T ∈ S_c c := by
      simp only [S_c, Finset.mem_filter]; exact ⟨hT, hball⟩
    exact Finset.mem_biUnion.mpr ⟨c, hc, h3⟩
  have h_ball_bound : ∀ (c : AffineLine), (S_c c).card ≤ 628849 :=
    toAffineLine_packing_9δ hm hb
  have h_card : S.card ≤ 628849 * C_finset.card := by
    calc
      S.card ≤ (Finset.biUnion C_finset S_c).card := Finset.card_le_card h_union
      _ ≤ ∑ c ∈ C_finset, (S_c c).card := Finset.card_biUnion_le
      _ ≤ ∑ c ∈ C_finset, 628849 := by gcongr <;> exact h_ball_bound c
      _ = 628849 * C_finset.card := by simp [Finset.sum_const] <;> ring
  have h_ncard_eq : (C_finset.card : ℕ∞) = Metric.externalCoveringNumber δ9_nn A := by
    have h5 : (C_finset.card : ℕ∞) = (C_min.val).encard := by
      have h6 : C_finset.card = (C_min.val).ncard := by
        exact Eq.symm (Set.ncard_eq_toFinset_card (C_min.val) h_fin)
      have h7 : ((C_min.val).ncard : ℕ∞) = (C_min.val).encard := by
        letI : Fintype (C_min.val) := Set.Finite.fintype h_fin
        simp
      rw [h6, h7]
    rw [h5, h_encard_eq]
  have h_main : (S.card : ENNReal) ≤ (628849 : ENNReal) * Metric.externalCoveringNumber δ9_nn A := by
    have h_card' : (S.card : ℝ) ≤ 628849 * (C_finset.card : ℝ) := by exact_mod_cast h_card
    have h : (S.card : ENNReal) ≤ (628849 : ENNReal) * (C_finset.card : ENNReal) := by
      exact_mod_cast h_card'
    have h9 : (C_finset.card : ENNReal) = Metric.externalCoveringNumber δ9_nn A := by
      exact_mod_cast h_ncard_eq
    rw [h9] at h
    exact h
  have h_final : ENNReal.ofReal ((S.card : ℝ) / 628849) ≤ Metric.externalCoveringNumber δ9_nn A := by
    have h_pos : (0 : ℝ) < 628849 := by norm_num
    have h_eq : ENNReal.ofReal ((S.card : ℝ) / 628849) = (S.card : ENNReal) / 628849 := by
      have h : (S.card : ℝ) / 628849 = (S.card : ℝ) * (1 / 628849 : ℝ) := by ring
      rw [h]
      have h_mul : ENNReal.ofReal ((S.card : ℝ) * (1 / 628849 : ℝ)) =
          ENNReal.ofReal (S.card : ℝ) * ENNReal.ofReal (1 / 628849 : ℝ) :=
        ENNReal.ofReal_mul (by positivity)
      rw [h_mul]
      have h_inv : ENNReal.ofReal (1 / 628849 : ℝ) = (628849 : ENNReal)⁻¹ := by simp
      rw [h_inv] <;> simp [div_eq_mul_inv]
    rw [h_eq]
    have h_comm : (S.card : ENNReal) ≤ Metric.externalCoveringNumber δ9_nn A * (628849 : ENNReal) := by
      have h' : (S.card : ENNReal) ≤ (628849 : ENNReal) * Metric.externalCoveringNumber δ9_nn A := h_main
      rw [mul_comm] at h'
      exact h'
    simpa [ENNReal.div_le_iff_le_mul] using h_comm
  exact h_final

/-! ============================================================================
   2. IsFiniteTubeSSet → IsDeltaSSet(9δ) on toAffineLine image

   Constant: C * 628849 * 44^s.
   44 = 2 * 22 (co-Lipschitz constant times triangle inequality factor).
   ============================================================================ -/

/-- Transfer IsFiniteTubeSSet to IsDeltaSSet at scale 9δ on toAffineLine image. -/
lemma toAffineLine_finiteTubeSSet_to_affineSSet_9δ {n : ℕ} {s C : ℝ} {F : Finset (DyadicTube n)}
    (hs : 0 ≤ s) (hC_one : 1 ≤ C)
    (hm : ∀ T ∈ F, |T.slope| ≤ 1)
    (hb : ∀ T ∈ F, |T.intercept| ≤ 3)
    (h : IsFiniteTubeSSet s C F) :
    IsDeltaSSet (9 * dyadicDelta n) s (C * 628849 * 44^s)
      (toAffineLine '' (F : Set (DyadicTube n))) := by
  set δ := dyadicDelta n with hδ
  set δ9 := 9 * δ with hδ9
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  have hδ9_pos : 0 < δ9 := by positivity
  have hC_pos : 0 < C := by linarith
  set S' : Set AffineLine := toAffineLine '' (F : Set (DyadicTube n)) with hS'_def
  have hF_nonempty : F.Nonempty := h.1
  have hS'_nonempty : S'.Nonempty := by
    rcases hF_nonempty with ⟨T, hT⟩
    exact ⟨toAffineLine T, ⟨T, hT, rfl⟩⟩
  have h_inj : Set.InjOn toAffineLine (F : Set (DyadicTube n)) := by
    intro T1 hT1 T2 hT2 h
    by_cases hne : T1 = T2
    · exact hne
    · exfalso
      have hsep : δ / 2 ≤ dist (toAffineLine T1) (toAffineLine T2) :=
        dyadic_tube_affine_separated T1 T2 hne (hm T1 hT1) (hm T2 hT2)
      rw [h] at hsep
      have h0 : dist (toAffineLine T2) (toAffineLine T2) = 0 := dist_self _
      rw [h0] at hsep
      have h_pos : 0 < δ / 2 := by linarith [hδ_pos]
      linarith
  refine' ⟨hS'_nonempty, hδ9_pos, by positivity, hs, _⟩
  intro y r hr
  set G : Finset (DyadicTube n) := F.filter (fun T => dist (toAffineLine T) y ≤ r) with hG_def
  set B : Finset AffineLine := G.image toAffineLine with hB_def
  have hB_eq : (B : Set AffineLine) = S' ∩ Metric.closedBall y r := by
    ext ℓ
    simp only [hB_def, hS'_def, Finset.mem_coe, Finset.mem_image, Set.mem_inter_iff,
      Metric.mem_closedBall, Set.mem_image]
    constructor
    · rintro ⟨T, hT, rfl⟩
      have hT_in_F : T ∈ F := (Finset.mem_filter.mp hT).1
      have h_dist : dist (toAffineLine T) y ≤ r := (Finset.mem_filter.mp hT).2
      exact ⟨⟨T, hT_in_F, rfl⟩, h_dist⟩
    · rintro ⟨⟨T, hT, rfl⟩, h_dist⟩
      exact ⟨T, Finset.mem_filter.mpr ⟨hT, h_dist⟩, rfl⟩
  by_cases hG_empty : G.Nonempty
  · rcases hG_empty with ⟨T0, hT0⟩
    have hT0_in_F : T0 ∈ F := (Finset.mem_filter.mp hT0).1
    have h_dist0 : dist (toAffineLine T0) y ≤ r := (Finset.mem_filter.mp hT0).2
    have h_ball : G ⊆ F.filter (fun T => paramDistLinf T T0 ≤ 44 * r) := by
      intro T hT
      have hT_in_F : T ∈ F := (Finset.mem_filter.mp hT).1
      have h_distT : dist (toAffineLine T) y ≤ r := (Finset.mem_filter.mp hT).2
      have h_coLip : paramDistLinf T T0 ≤ 22 * dist (toAffineLine T) (toAffineLine T0) :=
        toAffineLine_co_lipschitz T T0 (hm T hT_in_F) (hm T0 hT0_in_F) (hb T0 hT0_in_F)
      have h_tri : dist (toAffineLine T) (toAffineLine T0) ≤ 2 * r := by
        calc
          dist (toAffineLine T) (toAffineLine T0)
            ≤ dist (toAffineLine T) y + dist y (toAffineLine T0) := dist_triangle _ _ _
          _ = dist (toAffineLine T) y + dist (toAffineLine T0) y := by rw [dist_comm y _]
          _ ≤ r + r := by gcongr
          _ = 2 * r := by ring
      have h_final : paramDistLinf T T0 ≤ 44 * r := by
        calc
          paramDistLinf T T0 ≤ 22 * dist (toAffineLine T) (toAffineLine T0) := h_coLip
          _ ≤ 22 * (2 * r) := by gcongr
          _ = 44 * r := by ring
      exact Finset.mem_filter.mpr ⟨hT_in_F, h_final⟩
    have hG_card_le : (G.card : ℝ) ≤ ((F.filter (fun T => paramDistLinf T T0 ≤ 44 * r)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card h_ball
    have h44r_ge_delta : δ ≤ 44 * r := by
      have h1 : δ9 ≤ r := hr
      have h2 : δ ≤ δ9 := by linarith [hδ_pos]
      linarith
    have h_frost := h.2.2.2.2 T0 (44 * r) h44r_ge_delta
    have h_card_le : (G.card : ℝ) ≤ C * (44 * r)^s * (F.card : ℝ) := by
      calc
        (G.card : ℝ) ≤ (F.filter (fun T => paramDistLinf T T0 ≤ 44 * r)).card := hG_card_le
        _ ≤ C * (44 * r)^s * (F.card : ℝ) := h_frost
    let A : Set AffineLine := S' ∩ Metric.closedBall y r
    have h_ncover_le : (Metric.externalCoveringNumber δ9.toNNReal A : ENNReal) ≤ (B.card : ENNReal) := by
      have h : Metric.externalCoveringNumber δ9.toNNReal A ≤ A.encard :=
        Metric.externalCoveringNumber_le_encard_self A
      have hA : A = S' ∩ Metric.closedBall y r := by rfl
      have h2 : A.encard = (B.card : ℕ∞) := by
        rw [hA, ←hB_eq] <;> simp
      rw [h2] at h
      exact_mod_cast h
    have h_card_image : B.card = G.card := by
      rw [hB_def, Finset.card_image_of_injOn]
      intro T1 _ T2 _ h
      exact h_inj (Finset.mem_filter.mp ‹_›).1 (Finset.mem_filter.mp ‹_›).1 h
    have h_lower : (F.card : ENNReal) ≤ (628849 : ENNReal) *
        Metric.externalCoveringNumber δ9.toNNReal S' := by
      have h_ncov : ENNReal.ofReal ((F.card : ℝ) / 628849) ≤
          Metric.externalCoveringNumber δ9.toNNReal S' :=
        toAffineLine_dyadic_card_to_ncover_9δ F hm hb
      have h_eq : ENNReal.ofReal ((F.card : ℝ) / 628849) = (F.card : ENNReal) / 628849 := by
        have h : (F.card : ℝ) / 628849 = (F.card : ℝ) * (1 / 628849 : ℝ) := by ring
        rw [h]
        have h_mul : ENNReal.ofReal ((F.card : ℝ) * (1 / 628849 : ℝ)) =
            ENNReal.ofReal (F.card : ℝ) * ENNReal.ofReal (1 / 628849 : ℝ) :=
          ENNReal.ofReal_mul (by positivity)
        rw [h_mul]
        have h_inv : ENNReal.ofReal (1 / 628849 : ℝ) = (628849 : ENNReal)⁻¹ := by simp
        rw [h_inv] <;> simp [div_eq_mul_inv]
      rw [h_eq] at h_ncov
      have h : (F.card : ENNReal) ≤ Metric.externalCoveringNumber δ9.toNNReal S' * (628849 : ENNReal) := by
        simpa [ENNReal.div_le_iff_le_mul] using h_ncov
      have h' : Metric.externalCoveringNumber δ9.toNNReal S' * (628849 : ENNReal) =
          (628849 : ENNReal) * Metric.externalCoveringNumber δ9.toNNReal S' := by rw [mul_comm]
      rw [h'] at h
      exact h
    have h_r_nonneg : 0 ≤ r := by linarith [hδ9_pos, hr]
    have h44_pos : 0 < (44 : ℝ) := by norm_num
    have h_B_card_real : (B.card : ℝ) = (G.card : ℝ) := by exact_mod_cast h_card_image
    have h_card_le_B : (B.card : ℝ) ≤ C * (44 * r)^s * (F.card : ℝ) := by
      rw [h_B_card_real]; exact h_card_le
    have h_main : (B.card : ENNReal) ≤
        ENNReal.ofReal (C * 628849 * 44^s) * (ENNReal.ofReal r)^s *
          Metric.externalCoveringNumber δ9.toNNReal S' := by
      have h1 : (B.card : ENNReal) = ENNReal.ofReal (B.card : ℝ) := by simp
      rw [h1]
      have h2 : ENNReal.ofReal (B.card : ℝ) ≤
          ENNReal.ofReal (C * (44 * r)^s * (F.card : ℝ)) :=
        ENNReal.ofReal_le_ofReal h_card_le_B
      have h3 : C * (44 * r)^s * (F.card : ℝ) =
          (C * 628849 * 44^s) * r^s * ((F.card : ℝ) / 628849) := by
        have h4 : (44 * r)^s = 44^s * r^s :=
          Real.mul_rpow (x := (44 : ℝ)) (y := r) (z := s) (by norm_num) h_r_nonneg
        rw [h4] <;> ring
      have h5 : ENNReal.ofReal (C * (44 * r)^s * (F.card : ℝ)) =
          ENNReal.ofReal ((C * 628849 * 44^s) * r^s * ((F.card : ℝ) / 628849)) := by rw [h3]
      rw [h5] at h2
      have h_pos1 : 0 ≤ C * 628849 * 44^s := by positivity
      have h_pos2 : 0 ≤ r^s := by positivity
      have h_pos3 : 0 ≤ (F.card : ℝ) / 628849 := by positivity
      have h6 : ENNReal.ofReal ((C * 628849 * 44^s) * r^s * ((F.card : ℝ) / 628849)) =
          ENNReal.ofReal (C * 628849 * 44^s) * ENNReal.ofReal (r^s) *
            ENNReal.ofReal ((F.card : ℝ) / 628849) := by
        have h_step1 : ENNReal.ofReal (((C * 628849 * 44^s) * r^s) * ((F.card : ℝ) / 628849)) =
            ENNReal.ofReal ((C * 628849 * 44^s) * r^s) * ENNReal.ofReal ((F.card : ℝ) / 628849) :=
          ENNReal.ofReal_mul (by positivity)
        rw [h_step1]
        have h_step2 : ENNReal.ofReal ((C * 628849 * 44^s) * r^s) =
            ENNReal.ofReal (C * 628849 * 44^s) * ENNReal.ofReal (r^s) :=
          ENNReal.ofReal_mul h_pos1
        rw [h_step2] <;> ring
      rw [h6] at h2
      have h7 : ENNReal.ofReal (r^s) = (ENNReal.ofReal r)^s := by exact Eq.symm (ENNReal.ofReal_rpow_of_nonneg h_r_nonneg hs)
      rw [h7] at h2
      have h8 : ENNReal.ofReal ((F.card : ℝ) / 628849) ≤ Metric.externalCoveringNumber δ9.toNNReal S' :=
        toAffineLine_dyadic_card_to_ncover_9δ F hm hb
      have h9 : ENNReal.ofReal (C * 628849 * 44^s) * (ENNReal.ofReal r)^s *
            ENNReal.ofReal ((F.card : ℝ) / 628849) ≤
          ENNReal.ofReal (C * 628849 * 44^s) * (ENNReal.ofReal r)^s *
            Metric.externalCoveringNumber δ9.toNNReal S' := by gcongr <;> ring
      exact le_trans h2 h9
    calc
      (Metric.externalCoveringNumber δ9.toNNReal A : ENNReal)
        ≤ (B.card : ENNReal) := h_ncover_le
      _ ≤ ENNReal.ofReal (C * 628849 * 44^s) * (ENNReal.ofReal r)^s *
            Metric.externalCoveringNumber δ9.toNNReal S' := h_main
  · have hB_empty : B = ∅ := by
      rw [hB_def]
      simpa [hG_def] using hG_empty
    have h_cover : Metric.externalCoveringNumber δ9.toNNReal (S' ∩ Metric.closedBall y r) = 0 := by
      rw [←hB_eq, hB_empty] <;> simp
    rw [h_cover] <;> simp

/-! ============================================================================
   3. Full IsDeltaSSet(δ) → IsDeltaSSet(9δ) transfer chain

   Chain: IsDeltaSSet(δ) → DiscreteFrostmanL1(5C) → IsFiniteTubeSSet(max 1 (10C))
          → IsDeltaSSet(9δ) on toAffineLine image.
   Output constant: `max 1 (10 * C_fine) * 628849 * 44^s`.
   ============================================================================ -/

/-- Full S-set transfer from DyadicTube to toAffineLine image at scale 9δ. -/
lemma toAffineLine_tubeSSet_transfer_9δ {n : ℕ} {s C_fine : ℝ} {F : Finset (DyadicTube n)}
    (hs : 0 ≤ s) (hs_lt_one : s < 1) (hC_one : 1 ≤ C_fine)
    (hm : ∀ T ∈ F, |T.slope| ≤ 1)
    (hb : ∀ T ∈ F, |T.intercept| ≤ 3)
    (h : IsDeltaSSet (dyadicDelta n) s C_fine (F : Set (DyadicTube n))) :
    IsDeltaSSet (9 * dyadicDelta n) s
      (max 1 (10 * C_fine) * 628849 * 44^s)
      (toAffineLine '' (F : Set (DyadicTube n))) := by
  have h1 : DiscreteFrostmanL1 s (5 * C_fine) F :=
    isDeltaSSet_to_discreteFrostmanL1 h
  have h2 : IsFiniteTubeSSet s (max 1 (2 * (5 * C_fine))) F :=
    discreteFrostmanL1_to_isFiniteTubeSSet hs_lt_one.le hs h1
  have h3 : max 1 (2 * (5 * C_fine)) = max 1 (10 * C_fine) := by ring_nf
  rw [h3] at h2
  exact toAffineLine_finiteTubeSSet_to_affineSSet_9δ hs (by exact le_max_left _ _) hm hb h2

/-! ============================================================================
   4. Incidence conversion: point in dyadic square → 9δ-near affine line

   If p ∈ Q.toSet and T.toSet ∩ Q.toSet is nonempty, then p is within
   (1 + √2)δ < 9δ of the representative affine line of T.
   ============================================================================ -/

/-- If p ∈ Q.toSet and T.toSet ∩ Q.toSet is nonempty with |T.slope| ≤ 1,
    then p ∈ Metric.cthickening (9δ) ((toAffineLine T).1). -/
lemma point_in_square_near_affine_line_9δ {n : ℕ}
    (T : DyadicTube n) (Q : DyadicSquare n) (p : Plane)
    (hpQ : p ∈ (Q.toSet : Set Plane))
    (h_inter : (T.toSet ∩ Q.toSet).Nonempty)
    (hm : |T.slope| ≤ 1) :
    p ∈ Metric.cthickening (9 * dyadicDelta n) ((toAffineLine T).1) := by
  set δ := dyadicDelta n with hδ
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  rcases h_inter with ⟨q, hqT, hqQ⟩
  -- Vertical projection of q onto the affine line
  let q' : Plane := TubesAndSlopes.mkPlane (q 0) (T.slope * q 0 + T.intercept)
  have hq'_mem : q' ∈ (toAffineLine T).1 :=
    point_on_lineOfSlopeIntercept T.slope T.intercept (q 0)
  have hdist_qq' : dist q q' ≤ δ := by
    have h_same_x : q 0 = q' 0 := by simp [q', TubesAndSlopes.mkPlane_apply0]
    have h : dist q q' = |q 1 - q' 1| := by
      have h_norm : ‖q - q'‖ = Real.sqrt (((q - q') 0)^2 + ((q - q') 1)^2) := by
        simp [EuclideanSpace.norm_eq, Fin.sum_univ_two]
      rw [dist_eq_norm, h_norm]
      have h0 : (q - q') 0 = 0 := by simp [h_same_x]
      have h_eq1 : Real.sqrt (((q - q') 0)^2 + ((q - q') 1)^2) = Real.sqrt (((q - q') 1)^2) := by
        rw [h0]
        <;> ring_nf
      rw [h_eq1]
      have h_eq2 : Real.sqrt (((q - q') 1)^2) = |(q - q') 1| :=
        Real.sqrt_sq_eq_abs ((q - q') 1)
      rw [h_eq2]
      <;> rfl
    rw [h]
    have h7 : q 1 - q' 1 = q 1 - T.slope * q 0 - T.intercept := by
      simp [q', TubesAndSlopes.mkPlane_apply1] <;> ring
    rw [h7]
    exact hqT
  -- Bound dist p q
  have hside := DyadicSquare.side_length hpQ hqQ
  have h2 : (p 0 - q 0)^2 ≤ δ^2 := by
    have h3 : |p 0 - q 0| ≤ δ := hside.1
    have h4 : (p 0 - q 0)^2 = |p 0 - q 0|^2 := by rw [sq_abs]
    rw [h4]
    gcongr <;> linarith
  have h4 : (p 1 - q 1)^2 ≤ δ^2 := by
    have h5 : |p 1 - q 1| ≤ δ := hside.2
    have h6 : (p 1 - q 1)^2 = |p 1 - q 1|^2 := by rw [sq_abs]
    rw [h6]
    gcongr <;> linarith
  have hdist_pq : dist p q ≤ Real.sqrt 2 * δ := by
    have h1 : dist p q = Real.sqrt ((p 0 - q 0)^2 + (p 1 - q 1)^2) := by
      simp [dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_two]
    rw [h1]
    have h6 : (p 0 - q 0)^2 + (p 1 - q 1)^2 ≤ 2 * δ^2 := by linarith
    have h7 : Real.sqrt ((p 0 - q 0)^2 + (p 1 - q 1)^2) ≤ Real.sqrt (2 * δ^2) := Real.sqrt_le_sqrt h6
    have h8 : Real.sqrt (2 * δ^2) = Real.sqrt 2 * δ := by
      have h9 : 0 ≤ δ := by linarith
      have h10 : 2 * δ^2 = (Real.sqrt 2 * δ)^2 := by
        calc 2 * δ^2 = (Real.sqrt 2)^2 * δ^2 := by rw [Real.sq_sqrt (by norm_num)] <;> ring
          _ = (Real.sqrt 2 * δ)^2 := by ring
      rw [h10]
      rw [Real.sqrt_sq (by positivity)]
    rw [h8] at h7
    exact h7
  have h_main : dist p q' ≤ (1 + Real.sqrt 2) * δ := by
    calc dist p q'
      ≤ dist p q + dist q q' := dist_triangle _ _ _
    _ ≤ Real.sqrt 2 * δ + δ := by gcongr
    _ = (1 + Real.sqrt 2) * δ := by ring
  have h9 : (1 + Real.sqrt 2) * δ ≤ 9 * δ := by
    have h10 : 1 + Real.sqrt 2 ≤ 9 := by
      have h11 : Real.sqrt 2 ≤ 8 := by
        have h12 : Real.sqrt 2 ≤ Real.sqrt 64 := Real.sqrt_le_sqrt (by norm_num)
        have h13 : Real.sqrt 64 = 8 := by
          rw [Real.sqrt_eq_cases] <;> norm_num
        linarith
      linarith
    gcongr <;> linarith
  have h_final : dist p q' ≤ 9 * δ := le_trans h_main h9
  have h_edist : edist p q' ≤ ENNReal.ofReal (9 * δ) := by
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal h_final
  have h_inf : Metric.infEDist p ((toAffineLine T).1) ≤ ENNReal.ofReal (9 * δ) := by
    have h : Metric.infEDist p ((toAffineLine T).1) ≤ edist p q' :=
      Metric.infEDist_le_edist_of_mem hq'_mem
    exact le_trans h h_edist
  exact Metric.mem_cthickening_iff.mpr h_inf

/-! ============================================================================
   5. Apply Appendix A alternative to converted dyadic configuration

   Converts dyadic regularity from δ_n to δ' = 9δ_n and applies
   UniformAppendixAAlternative at scale δ'.
   ============================================================================ -/

/-- Apply Appendix A alternative to a dyadic configuration at scale δ_n.

    Converts:
    - Point S-set: δ_n → 9δ_n via point_sset_scale (factor 361), absorb with h_absorb_point
    - Sqrt covering: √δ_n → √(9δ_n) via anti-monotonicity, absorb with h_absorb_sqrt
    - Tube S-sets: DyadicTube at δ_n → AffineLine at 9δ_n via toAffineLine_tubeSSet_transfer_9δ
    - Incidence: tube-square intersection → 9δ cthickening via incidence_to_affine_line_9δ

    Returns δA from the alternative and a conditional disjunction (when 9δ_n ≤ δA).
-/
lemma apply_appendix_a_to_dyadic
    {n m : ℕ} (hnm : m ≤ n) (h_even : n = 2 * m)
    {s t u : ℝ} (hs_pos : 0 < s) (hs_lt_one : s < 1) (hst : s < t) (hu_t : t ≤ u) (hu_two : u ≤ 2)
    {C_P K_P C_T : ℝ}
    {P : Set DirecretisedFurstenbergEstimate.EuclideanPlane}
    (hP_bdd : P ⊆ Metric.closedBall 0 1)
    (hP_regular : IsSquareRootRegular (dyadicDelta n) u C_P K_P P)
    {tubeFamily : (p : DirecretisedFurstenbergEstimate.EuclideanPlane) → p ∈ P → Finset (DyadicTube n)}
    (hTubes_sset : ∀ p hp, IsDeltaSSet (dyadicDelta n) s C_T (tubeFamily p hp : Set (DyadicTube n)))
    (h_slope_bound : ∀ p hp, ∀ T ∈ tubeFamily p hp, |T.slope| ≤ 1)
    (h_intercept_bound : ∀ p hp, ∀ T ∈ tubeFamily p hp, |T.intercept| ≤ 3)
    (hIncidence : ∀ p hp, ∀ T ∈ tubeFamily p hp,
      ∃ (Q : DyadicSquare n), p ∈ (Q.toSet : Set Plane) ∧ (T.toSet ∩ Q.toSet).Nonempty)
    (hCT_one : 1 ≤ C_T)
    (εA : ℝ) (hεA_pos : 0 < εA)
    (hA : UniformAppendixAAlternative (fun ℓ : AffineLine => ℓ.1) s t εA)
    (h_absorb_point : C_P * 361 ≤ Real.rpow (9 * dyadicDelta n) (-εA))
    (h_absorb_sqrt  : K_P * (9 : ℝ)^(u / 2) ≤ Real.rpow (9 * dyadicDelta n) (-εA))
    (h_absorb_tube  : max 1 (10 * C_T) * 628849 * 44^s ≤ Real.rpow (9 * dyadicDelta n) (-εA)) :
    ∃ (δA : ℝ), 0 < δA ∧ δA ≤ 1 ∧
      (9 * dyadicDelta n ≤ δA →
        (ENNReal.ofReal (Real.rpow (9 * dyadicDelta n) (-(2 * s + εA))) ≤
          RegularIncidence.Ncover (9 * dyadicDelta n)
            (⋃ p, ⋃ hp : p ∈ P, toAffineLine '' (tubeFamily p hp : Set (DyadicTube n))))
        ∨
        (ENNReal.ofReal (Real.rpow (9 * dyadicDelta n) (-(s + εA))) ≤
          RegularIncidence.Ncover (Real.sqrt (9 * dyadicDelta n))
            (⋃ p, ⋃ hp : p ∈ P, toAffineLine '' (tubeFamily p hp : Set (DyadicTube n))))) := by
  set δ := dyadicDelta n with hδ_def
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  set δ' := 9 * δ with hδ'_def
  have hδ'_pos : 0 < δ' := by positivity
  have hP_bdd' : Bornology.IsBounded P := Metric.isBounded_closedBall.subset hP_bdd

  -- Step 1: Convert point S-set from δ to δ'
  have hP_delta : IsDeltaSSet δ u C_P P := hP_regular.to_isDeltaSSet
  have hP_scaled : IsDeltaSSet δ' u (C_P * 361) P :=
    point_sset_scale hδ_pos hP_bdd' hP_delta
  have hP_final : IsDeltaSSet δ' u (Real.rpow δ' (-εA)) P :=
    IsDeltaSSet.weaken_C hP_scaled h_absorb_point

  -- Step 2: Convert sqrt covering bound
  have h_sqrt_orig : RegularIncidence.Ncover (Real.sqrt δ) P ≤
      ENNReal.ofReal (K_P * Real.rpow δ (-u / 2)) := hP_regular.ncover_sqrt_le
  have hδ_leδ' : δ ≤ δ' := by linarith [hδ_pos]
  have hsqrt_le : Real.sqrt δ ≤ Real.sqrt δ' := Real.sqrt_le_sqrt hδ_leδ'
  have h_sqrt_antitone : RegularIncidence.Ncover (Real.sqrt δ') P ≤ RegularIncidence.Ncover (Real.sqrt δ) P := by
    have h_le : (Real.sqrt δ).toNNReal ≤ (Real.sqrt δ').toNNReal := by
      exact Real.toNNReal_mono hsqrt_le
    simpa [RegularIncidence.Ncover] using Metric.externalCoveringNumber_anti h_le
  have h_sqrt_eq : Real.rpow δ (-u / 2) = (9 : ℝ)^(u / 2) * Real.rpow δ' (-u / 2) := by
    have h1 : Real.rpow δ' (-u / 2) = (9 : ℝ)^(-u / 2) * Real.rpow δ (-u / 2) :=
      Real.mul_rpow (by norm_num) (by linarith)
    have h3 : (9 : ℝ)^(u / 2) * (9 : ℝ)^(-u / 2) = (1 : ℝ) := by
      have h4 : (9 : ℝ)^(u / 2) * (9 : ℝ)^(-u / 2) = (9 : ℝ)^((u / 2) + (-u / 2)) :=
        (Real.rpow_add (by norm_num) (u / 2) (-u / 2)).symm
      rw [h4]
      have h5 : (u / 2 : ℝ) + (-u / 2) = 0 := by ring
      rw [h5]
      simp
    have h6 : Real.rpow δ (-u / 2) =
        (9 : ℝ)^(u / 2) * ((9 : ℝ)^(-u / 2) * Real.rpow δ (-u / 2)) := by
      have h7 : (9 : ℝ)^(u / 2) * (9 : ℝ)^(-u / 2) = (1 : ℝ) := h3
      have h8 : (9 : ℝ)^(u / 2) * ((9 : ℝ)^(-u / 2) * Real.rpow δ (-u / 2)) =
          ((9 : ℝ)^(u / 2) * (9 : ℝ)^(-u / 2)) * Real.rpow δ (-u / 2) := by ring
      rw [h8, h7] <;> ring
    rw [h6, ←h1] <;> ring
  have h_sqrt_final : RegularIncidence.Ncover (Real.sqrt δ') P ≤
      ENNReal.ofReal (Real.rpow δ' (-εA) * Real.rpow δ' (-u / 2)) := by
    calc RegularIncidence.Ncover (Real.sqrt δ') P
      ≤ RegularIncidence.Ncover (Real.sqrt δ) P := h_sqrt_antitone
    _ ≤ ENNReal.ofReal (K_P * Real.rpow δ (-u / 2)) := h_sqrt_orig
    _ = ENNReal.ofReal (K_P * (9 : ℝ)^(u / 2) * Real.rpow δ' (-u / 2)) := by
      rw [h_sqrt_eq] <;> ring_nf
    _ ≤ ENNReal.ofReal (Real.rpow δ' (-εA) * Real.rpow δ' (-u / 2)) := by
      have h_pos : 0 ≤ Real.rpow δ' (-u / 2) := Real.rpow_nonneg hδ'_pos.le _
      have h_le : K_P * (9 : ℝ)^(u / 2) * Real.rpow δ' (-u / 2) ≤
          Real.rpow δ' (-εA) * Real.rpow δ' (-u / 2) :=
        mul_le_mul_of_nonneg_right h_absorb_sqrt h_pos
      exact ENNReal.ofReal_le_ofReal h_le

  have hP_regular' : IsSquareRootRegular δ' u (Real.rpow δ' (-εA)) (Real.rpow δ' (-εA)) P :=
    ⟨hP_final, h_sqrt_final⟩

  -- Step 3: Convert tube S-sets from DyadicTube at δ to AffineLine at δ'
  let tubeFamily' : (p : DirecretisedFurstenbergEstimate.EuclideanPlane) → p ∈ P → Set AffineLine :=
    fun p hp => toAffineLine '' (tubeFamily p hp : Set (DyadicTube n))
  have hTubes' : ∀ p hp, IsDeltaSSet δ' s (Real.rpow δ' (-εA)) (tubeFamily' p hp) := by
    intro p hp
    have h_orig : IsDeltaSSet δ s C_T (tubeFamily p hp : Set (DyadicTube n)) := hTubes_sset p hp
    have hm : ∀ T ∈ tubeFamily p hp, |T.slope| ≤ 1 := h_slope_bound p hp
    have hb : ∀ T ∈ tubeFamily p hp, |T.intercept| ≤ 3 := h_intercept_bound p hp
    have h_scaled : IsDeltaSSet δ' s (max 1 (10 * C_T) * 628849 * 44^s) (tubeFamily' p hp) :=
      toAffineLine_tubeSSet_transfer_9δ hs_pos.le hs_lt_one hCT_one hm hb h_orig
    have h_abs : max 1 (10 * C_T) * 628849 * 44^s ≤ Real.rpow δ' (-εA) :=
      h_absorb_tube
    exact IsDeltaSSet.weaken_C h_scaled h_abs

  -- Step 4: Convert incidence to 9δ
  have hInc' : ∀ p hp, ∀ ℓ ∈ tubeFamily' p hp, p ∈ Metric.cthickening δ' (ℓ.1) := by
    intro p hp ℓ hℓ
    rcases hℓ with ⟨T, hT, rfl⟩
    rcases hIncidence p hp T hT with ⟨Q, hpQ, h_intersect⟩
    have h_slope : |T.slope| ≤ 1 := h_slope_bound p hp T hT
    exact point_in_square_near_affine_line_9δ T Q p hpQ h_intersect h_slope

  -- Step 5: Apply the alternative
  rcases hA with ⟨hεA_pos', δA, hδA_pos, hδA_one, h_body⟩
  refine' ⟨δA, hδA_pos, hδA_one, _⟩
  intro hδ'_le
  have h_sqrt_rpow : Real.rpow δ' (-εA) * Real.rpow δ' (-u / 2) =
      Real.rpow δ' (-(u / 2 + εA)) := by
    have h_add : Real.rpow δ' (-εA) * Real.rpow δ' (-u / 2) =
        Real.rpow δ' ((-εA) + (-u / 2)) := (Real.rpow_add hδ'_pos _ _).symm
    rw [h_add]
    have h_sum : (-εA) + (-u / 2) = -(u / 2 + εA) := by ring
    rw [h_sum]
  have h_sqrt_bound : RegularIncidence.Ncover (Real.sqrt δ') P ≤
      ENNReal.ofReal (Real.rpow δ' (-(u / 2 + εA))) := by
    rw [←h_sqrt_rpow]
    exact h_sqrt_final
  have hsu' : t ≤ u := hu_t
  exact h_body u hsu' hu_two hδ'_pos hδ'_le P hP_bdd hP_final h_sqrt_bound
    tubeFamily' hTubes' hInc'

/-- Intercept bound ≤ 3 from incidence with a unit square.

    If q indices are in [0,2^n), T.toSet intersects q.toSet, and |T.slope| ≤ 1,
    then |T.intercept| ≤ 3. -/
lemma intercept_bound_3 {n : ℕ} {T : DyadicTube n} {q : DyadicSquare n}
    (h_inc : (T.toSet ∩ q.toSet).Nonempty)
    (h_slope : |T.slope| ≤ 1)
    (hqi1 : 0 ≤ q.i) (hqi2 : q.i < (2^n : ℤ))
    (hqj1 : 0 ≤ q.j) (hqj2 : q.j < (2^n : ℤ))
    (hδ_le_one : dyadicDelta n ≤ 1) :
    |T.intercept| ≤ 3 := by
  set δ := dyadicDelta n with hδ
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  have hδ_eq : (2^n : ℝ) * δ = 1 := by
    simp [hδ, dyadicDelta] <;> field_simp <;> ring
  have hqi2' : (q.i + 1 : ℤ) ≤ (2^n : ℤ) := by linarith
  have hqi2'' : (q.i + 1 : ℝ) ≤ (2^n : ℝ) := by exact_mod_cast hqi2'
  have hqj2' : (q.j + 1 : ℤ) ≤ (2^n : ℤ) := by linarith
  have hqj2'' : (q.j + 1 : ℝ) ≤ (2^n : ℝ) := by exact_mod_cast hqj2'
  rcases h_inc with ⟨z, hzT, hzq⟩
  have hx1 : 0 ≤ z 0 := by
    have h : (q.i : ℝ) * δ ≤ z 0 := hzq.1
    have h2 : 0 ≤ (q.i : ℝ) * δ := by positivity
    linarith
  have hx2 : z 0 < 1 := by
    have h : z 0 < ((q.i + 1 : ℝ)) * δ := hzq.2.1
    have h3 : ((q.i + 1 : ℝ)) * δ ≤ (2^n : ℝ) * δ := by
      have h31 : (q.i + 1 : ℤ) ≤ (2^n : ℤ) := by linarith
      have h32 : ((q.i + 1 : ℝ)) ≤ (2^n : ℝ) := by exact_mod_cast h31
      gcongr
    have h4 : (2^n : ℝ) * δ = 1 := hδ_eq
    linarith
  have hy1 : 0 ≤ z 1 := by
    have h : (q.j : ℝ) * δ ≤ z 1 := hzq.2.2.1
    have h2 : 0 ≤ (q.j : ℝ) * δ := by positivity
    linarith
  have hy2 : z 1 < 1 := by
    have h : z 1 < ((q.j + 1 : ℝ)) * δ := hzq.2.2.2
    have h3 : ((q.j + 1 : ℝ)) * δ ≤ (2^n : ℝ) * δ := by
      have h31 : (q.j + 1 : ℤ) ≤ (2^n : ℤ) := by linarith
      have h32 : ((q.j + 1 : ℝ)) ≤ (2^n : ℝ) := by exact_mod_cast h31
      gcongr
    have h4 : (2^n : ℝ) * δ = 1 := hδ_eq
    linarith
  have hzT' : |z 1 - T.slope * z 0 - T.intercept| ≤ δ := by
    simpa [DyadicTube.toSet] using hzT
  have h_z0_abs : |z 0| ≤ 1 := by
    rw [abs_le] <;> constructor <;> linarith
  have h_z1_abs : |z 1| ≤ 1 := by
    rw [abs_le] <;> constructor <;> linarith
  set a : ℝ := z 1 - T.slope * z 0 with ha
  set b : ℝ := z 1 - T.slope * z 0 - T.intercept with hb
  have h_ab : a - b = T.intercept := by
    simp [ha, hb] <;> ring
  have h_main : |T.intercept| ≤ |a| + |b| := by
    have h_abs : |a - b| ≤ |a| + |b| := abs_sub a b
    rw [h_ab] at h_abs
    exact h_abs
  have h5 : |a| ≤ |z 1| + |T.slope| * |z 0| := by
    have h_abs2 : |z 1 - T.slope * z 0| ≤ |z 1| + |T.slope * z 0| := abs_sub (z 1) (T.slope * z 0)
    have h_eq : a = z 1 - T.slope * z 0 := by simp [ha]
    rw [h_eq]
    rw [abs_mul] at * <;> exact h_abs2
  have h6 : |b| ≤ δ := by
    have h_eq2 : b = z 1 - T.slope * z 0 - T.intercept := by simp [hb]
    rw [h_eq2]
    exact hzT'
  have h_prod : |T.slope| * |z 0| ≤ 1 := by
    have h7 : |T.slope| ≤ 1 := h_slope
    have h8 : |z 0| ≤ 1 := h_z0_abs
    have h9 : 0 ≤ |T.slope| := abs_nonneg _
    nlinarith
  have h : |T.intercept| ≤ |z 1| + |T.slope| * |z 0| + δ := by
    calc |T.intercept|
      ≤ |a| + |b| := h_main
    _ ≤ (|z 1| + |T.slope| * |z 0|) + |b| := by gcongr
    _ ≤ (|z 1| + |T.slope| * |z 0|) + δ := by gcongr
    _ = |z 1| + |T.slope| * |z 0| + δ := by ring
  have h4 : |T.intercept| ≤ 1 + 1 + δ := by
    have h10 : |z 1| + |T.slope| * |z 0| + δ ≤ 1 + 1 + δ := by
      have h11 : |z 1| ≤ 1 := h_z1_abs
      linarith [h_prod]
    exact le_trans h h10
  have h12 : 1 + 1 + δ ≤ 3 := by
    have h13 : δ ≤ 1 := hδ_le_one
    linarith
  exact le_trans h4 h12

end DiscretisedFurstenbergEstimate.FixedScaleAdapter

end
