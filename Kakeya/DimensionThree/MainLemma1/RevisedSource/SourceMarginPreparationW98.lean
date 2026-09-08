module

public import Kakeya.DimensionThree.MainLemma2.CanonicalCentredCover
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.ActualMarginSelectionW102
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.ActualMarginWeightedSelectionW102
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.ActualMarginParentW102
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceQuotientGridW97
public import Kakeya.Uniform.Tree

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody
open scoped ENNReal NNReal

namespace Kakeya.ml1Boot.TrialRestartW94

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
attribute [local instance] Classical.propDecidable

universe uE uI

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

open RevisedLiteralProfileInterfaceFormalizerW87

/-- Concrete old-core margin at every strict pair of actual levels. It says
nothing about normalized tubes and is built BEFORE all-pair regularization. -/
structure ActualTreeParameterMarginW98
    {iota : Type uI} [DecidableEq iota] {delta : NNReal}
    {A : Finset iota} {T : iota -> Tube delta E} {N : Nat}
    (cov : Tube.GridCoverSystem A T N) (kappa : NNReal) : Prop where
  midpoint : ∀ k l, k < l -> l <= N -> ∀ i ∈ A,
    ‖(cov.tube l (cov.assign l i)).center - (cov.tube k (cov.assign k i)).center‖ <=
      (kappa : Real) * (Tube.gridScale delta N k : Real)
  direction : ∀ k l, k < l -> l <= N -> ∀ i ∈ A,
    min (‖(cov.tube l (cov.assign l i)).direction - (cov.tube k (cov.assign k i)).direction‖)
      (‖(cov.tube l (cov.assign l i)).direction + (cov.tube k (cov.assign k i)).direction‖) <=
      (kappa : Real) * (Tube.gridScale delta N k : Real)

/-- Actual pre-regularization tree. No count/CF band or normalization witness
is supplied here; nesting is the production GridCoverSystem nesting. -/
structure ActualPreparedRawTreeW98
    {iota : Type uI} [DecidableEq iota] {delta : NNReal}
    (A : Finset iota) (T : iota -> Tube delta E) (N : Nat) (kappa Ctw : NNReal) where
  cover : Tube.GridCoverSystem A T N
  margin : ActualTreeParameterMarginW98 cover kappa
  surjective : ∀ k, k <= N -> A.image (cover.assign k) = cover.indexSet k
  bottom_index : cover.indexSet N = A
  bottom_assign : ∀ i ∈ A, cover.assign N i = i
  bottom_tube : ∀ i ∈ A, (cover.tube N i).toConvexSpaceBody = (T i).toConvexSpaceBody
  tube_injective : ∀ k, k <= N -> Set.InjOn (cover.tube k) (cover.indexSet k : Set iota)
  parent_ball : ∀ k, k <= N -> ∀ R ∈ cover.indexSet k,
    (cover.tube k R).carrier ⊆ Metric.closedBall 0 2
  parent_line_ed : ∀ k, k <= N -> lineEssentiallyDistinctW94 (cover.indexSet k) (cover.tube k) Ctw
  tight_overlap : ∀ k, k <= N -> ∀ V : Tube (Tube.gridScale delta N k) E,
    ((cover.indexSet k).filter (fun R => ∃ i ∈ A,
      (T i).toConvexSpaceBody <= (cover.tube k R).toConvexSpaceBody ∧
      (T i).toConvexSpaceBody <= V.toConvexSpaceBody)).card <=
        Tube.overlapConstBOTight (Module.finrank Real E)

/-- New actual small-bin producer. All fixed packing/colour losses are paid
before delta; no arbitrary old regular tower is asserted to have this margin. -/
theorem exists_actual_parameter_margin_raw_tree_w98
    (hdim : Module.finrank Real E = 3) (N : Nat) (hN : 1 <= N)
    (kappa Cbase : NNReal) (hkappa : 0 < kappa) (hkappaSmall : kappa <= 1 / 100)
    (hCbase : 1 <= Cbase) :
    ∃ (Ctw Cprepare : NNReal) (delta0 : NNReal),
      1 <= Ctw ∧ 1 <= Cprepare ∧ 0 < delta0 ∧ delta0 < 1 ∧
      ∀ {delta : NNReal}, 0 < delta -> delta < delta0 ->
      ∀ {iota : Type uI} [DecidableEq iota] (F : Finset iota) (Y : iota -> ShadedTube delta E),
        (∀ i ∈ F, (Y i).carrier ⊆ Metric.closedBall 0 1) ->
        (∀ i ∈ F, centredTubeW94 (Y i).toTube) ->
        lineEssentiallyDistinctW94 F (fun i => (Y i).toTube) Cbase ->
        (0 < ∑ i ∈ F, volume (Y i).shade) ->
        ∃ A : Finset iota, A.Nonempty ∧ A ⊆ F ∧
          (Cprepare : ENNReal)⁻¹ * (∑ i ∈ F, volume (Y i).shade) <=
            ∑ i ∈ A, volume (Y i).shade ∧
          Nonempty (ActualPreparedRawTreeW98 A (fun i => (Y i).toTube) N kappa Ctw) := by

  have hlineCover {delta : NNReal} (hd : 0 < delta) {iota : Type uI}
      {A : Finset iota} {T : iota -> Tube delta E} {M : Nat} {C : NNReal}
      (G : Tube.GridCoverSystem A T M)
      (hoverlap : ∀ k, k <= M -> ∀ V : Tube (Tube.gridScale delta M k) E,
        (((G.indexSet k).filter (fun j => ∃ i ∈ A,
          (T i).toConvexSpaceBody <= (G.tube k j).toConvexSpaceBody ∧
          (T i).toConvexSpaceBody <= V.toConvexSpaceBody)).card : NNReal) <= C)
      (hcen : ∀ i ∈ A, (T i).IsCentred) {R0 : Real} (hR0 : 0 <= R0)
      (hmid : ∀ i ∈ A, ‖(T i).midpoint‖ <= R0) {k : Nat} (hk : k <= M)
      (h4 : 4 * (delta : Real) <= Tube.gridScale delta M k)
      (o d : E) (hdirection : ‖d‖ = 1) :
      (((G.activeIndexSet k).filter (fun j => (G.tube k j).carrier ⊆
        Metric.cthickening (5 * (Tube.gridScale delta M k : Real))
          (Set.range (fun t : Real => o + t • d)))).card : Real) <=
        (C : Real) * Tube.activeLineConstant (Module.finrank Real E) R0 := by
    exact (open _root_.Tube in by
      classical
      set ρ : NNReal := gridScale delta M k with hρdef
      have hρ : 0 < ρ := gridScale_pos hd M k
      have hρr : (0 : ℝ) < ρ := by exact_mod_cast hρ
      have hdeltaReal : (0 : ℝ) < delta := by exact_mod_cast hd
      set L : Set E := Set.range fun t : ℝ ↦ o + t • d with hL
      set B := (G.activeIndexSet k).filter fun j ↦ (G.tube k j).carrier ⊆
        Metric.cthickening (5 * (ρ : ℝ)) L with hB
      have hC0 : (0 : ℝ) ≤ C := C.coe_nonneg
      have hconst0 : 0 ≤ activeLineConstant (Module.finrank ℝ E) R0 := by
        unfold activeLineConstant; positivity
      rcases B.eq_empty_or_nonempty with hBe | ⟨j₀, hj₀⟩
      · rw [hBe]; simp only [Finset.card_empty, Nat.cast_zero]; positivity
      -- a member in each active node
      have hpick : ∀ j ∈ B, ∃ i ∈ A, G.assign k i = j :=
        fun j hj ↦ ((G.mem_activeIndexSet).mp (Finset.mem_filter.mp hj).1).2
      obtain ⟨i₀, -, -⟩ := hpick j₀ hj₀
      haveI : Nonempty iota := ⟨i₀⟩
      choose! pick hpick_mem hpick_eq using hpick
      have hmemT : ∀ j ∈ B, (T (pick j)).carrier ⊆ Metric.cthickening (5 * (ρ : ℝ)) L := by
        intro j hj
        have h1 := G.le_tube_assign k hk (pick j) (hpick_mem j hj)
        rw [hpick_eq j hj] at h1
        exact fun x hx ↦ (Finset.mem_filter.mp hj).2 (h1 hx)
      -- the centred net at spacing `ρ/8`
      obtain ⟨G₀, hG₀cen, hG₀mid, hG₀sep, hG₀cover⟩ :=
        exists_centred_net (E := E) ρ R0 (ε := (ρ : ℝ) / 8) (by positivity)
      have hnode : ∀ j ∈ B, ∃ V ∈ G₀, ‖(T (pick j)).midpoint - V.midpoint‖ ≤ 2 * ((ρ : ℝ) / 8) ∧
          ‖(T (pick j)).direction - V.direction‖ ≤ 2 * ((ρ : ℝ) / 8) :=
        fun j hj ↦ hG₀cover _ _ (hcen _ (hpick_mem j hj)) (T _).norm_direction (hmid _ (hpick_mem j hj))
      haveI : Nonempty (Tube ρ E) := ⟨ofMidpointDirection ρ 0 d hdirection⟩
      choose! Vmap hV_mem hV_mid hV_dir using hnode
      -- the member lies inside its net node
      have hle : ∀ j ∈ B, (T (pick j)).toConvexSpaceBody ≤ (Vmap j).toConvexSpaceBody := by
        intro j hj
        refine le_of_params_close _ _ (hV_mid j hj) (hV_dir j hj) ?_
        linarith
      -- the net node's parameters are in the two boxes
      set Rx : ℝ := 5 * ρ * (1 + 4 * R0) + ρ / 4 with hRx
      set Ry : ℝ := 20 * ρ + ρ / 4 with hRy
      have hRx0 : 0 ≤ Rx := by rw [hRx]; positivity
      have hRy0 : 0 ≤ Ry := by rw [hRy]; positivity
      have hbox : ∀ j ∈ B, ‖(Vmap j).midpoint - lineFoot o d‖ ≤ Rx ∧
          (‖(Vmap j).direction - (1 : ℝ) • d‖ ≤ Ry ∨ ‖(Vmap j).direction - (-1 : ℝ) • d‖ ≤ Ry) := by
        intro j hj
        have hK : (1 : ℝ) ≤ 5 * ρ / delta := by rw [le_div_iff₀ hdeltaReal]; linarith
        have hKdelta : (5 * (ρ : ℝ) / delta) * delta = 5 * ρ := by field_simp
        have hKm : (5 * (ρ : ℝ) / delta - 1) * delta = 5 * ρ - delta := by field_simp
        obtain ⟨sgn, hsgn, hdir, hmidc⟩ := params_close_of_carrier_subset_line (T (pick j))
          (hcen _ (hpick_mem j hj)) (hmid _ (hpick_mem j hj)) hdirection hK (by rw [hKdelta]; exact hmemT j hj)
        rw [hKm] at hdir hmidc
        have hmid' : ‖(Vmap j).midpoint - (T (pick j)).midpoint‖ ≤ 2 * ((ρ : ℝ) / 8) := by
          rw [norm_sub_rev]; exact hV_mid j hj
        have hdir' : ‖(Vmap j).direction - (T (pick j)).direction‖ ≤ 2 * ((ρ : ℝ) / 8) := by
          rw [norm_sub_rev]; exact hV_dir j hj
        refine ⟨?_, ?_⟩
        · calc ‖(Vmap j).midpoint - lineFoot o d‖
              ≤ ‖(Vmap j).midpoint - (T (pick j)).midpoint‖ +
                ‖(T (pick j)).midpoint - lineFoot o d‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
            _ ≤ 2 * ((ρ : ℝ) / 8) + (5 * ρ - delta) * (1 + 4 * R0) := add_le_add hmid' hmidc
            _ ≤ Rx := by rw [hRx]; nlinarith [hdeltaReal.le, hR0]
        · have hcalc : ‖(Vmap j).direction - sgn • d‖ ≤ Ry := by
            calc ‖(Vmap j).direction - sgn • d‖
                ≤ ‖(Vmap j).direction - (T (pick j)).direction‖ +
                  ‖(T (pick j)).direction - sgn • d‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
              _ ≤ 2 * ((ρ : ℝ) / 8) + 4 * (5 * ρ - delta) := add_le_add hdir' hdir
              _ ≤ Ry := by rw [hRy]; linarith
          rcases hsgn with rfl | rfl
          · exact Or.inl hcalc
          · exact Or.inr hcalc
      -- the image of `A` in the net lies in the box-filtered net
      set G₁ := G₀.filter fun V ↦ ‖V.midpoint - lineFoot o d‖ ≤ Rx ∧
        (‖V.direction - (1 : ℝ) • d‖ ≤ Ry ∨ ‖V.direction - (-1 : ℝ) • d‖ ≤ Ry) with hG₁
      have himg : B.image Vmap ⊆ G₁ := by
        intro V hV
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hV
        exact Finset.mem_filter.mpr ⟨hV_mem j hj, hbox j hj⟩
      -- each fibre of `Vmap` is bounded by `C` through `boundedOverlap`
      have hfibre : ∀ V ∈ B.image Vmap, ((B.filter fun j ↦ Vmap j = V).card : ℝ) ≤ C := by
        intro V _
        have hsub : B.filter (fun j ↦ Vmap j = V) ⊆
            (G.indexSet k).filter (fun j ↦ ∃ i ∈ A,
              (T i).toConvexSpaceBody ≤ (G.tube k j).toConvexSpaceBody ∧
              (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody) := by
          intro j hj
          obtain ⟨hjA, hjV⟩ := Finset.mem_filter.mp hj
          refine Finset.mem_filter.mpr ⟨G.activeIndexSet_subset k (Finset.mem_filter.mp hjA).1,
            pick j, hpick_mem j hjA, ?_, ?_⟩
          · have h1 := G.le_tube_assign k hk (pick j) (hpick_mem j hjA)
            rwa [hpick_eq j hjA] at h1
          · rw [← hjV]; exact hle j hjA
        have h := hoverlap k hk V
        calc ((B.filter fun j ↦ Vmap j = V).card : ℝ)
            ≤ (((G.indexSet k).filter (fun j ↦ ∃ i ∈ A,
              (T i).toConvexSpaceBody ≤ (G.tube k j).toConvexSpaceBody ∧
              (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody)).card : ℝ) := by
              exact_mod_cast Finset.card_le_card hsub
          _ ≤ C := by exact_mod_cast h
      have hcardA : (B.card : ℝ) ≤ ((B.image Vmap).card : ℝ) * C := by
        rw [Finset.card_eq_sum_card_image Vmap B]
        push_cast
        calc ∑ V ∈ B.image Vmap, ((B.filter fun j ↦ Vmap j = V).card : ℝ)
            ≤ ∑ V ∈ B.image Vmap, (C : ℝ) := Finset.sum_le_sum hfibre
          _ = ((B.image Vmap).card : ℝ) * C := by rw [Finset.sum_const, nsmul_eq_mul]
      have hG₁card : ((B.image Vmap).card : ℝ) ≤ (G₁.card : ℝ) := by
        exact_mod_cast Finset.card_le_card himg
      -- the box packing of the net
      have hpack : (G₁.card : ℝ) ≤ activeLineConstant (Module.finrank ℝ E) R0 := by
        have h := card_filter_boxes_le_of_sep G₀ (fun V : Tube ρ E ↦ V) (ε := (ρ : ℝ) / 8)
          (by positivity) hG₀sep (lineFoot o d) d hRx0 hRy0
        have hx : (Rx + (ρ : ℝ) / 8 / 4) / ((ρ : ℝ) / 8 / 4) = 160 * (1 + 4 * R0) + 9 := by
          rw [hRx]; field_simp; ring
        have hy : (Ry + (ρ : ℝ) / 8 / 4) / ((ρ : ℝ) / 8 / 4) = 649 := by
          rw [hRy]; field_simp; ring
        rw [hx, hy] at h
        exact h
      calc (B.card : ℝ) ≤ ((B.image Vmap).card : ℝ) * C := hcardA
        _ ≤ (G₁.card : ℝ) * C := by gcongr
        _ ≤ activeLineConstant (Module.finrank ℝ E) R0 * C := by gcongr
        _ = (C : ℝ) * activeLineConstant (Module.finrank ℝ E) R0 := mul_comm _ _)
  classical
  let alpha : NNReal := kappa / 4
  have halpha : 0 < alpha := div_pos hkappa (by norm_num)
  have halphaSmall : alpha <= 1 / 400 := by
    apply NNReal.coe_le_coe.mp
    have hh : (kappa : Real) <= 1 / 100 := by exact_mod_cast hkappaSmall
    change (kappa : Real) / 4 <= (1 : NNReal) / 400
    norm_num
    linarith
  have halpha1 : alpha <= 1 := halphaSmall.trans
    ((div_le_iff₀ (by norm_num : (0 : NNReal) < 400)).mpr (by norm_num))
  let Kbottom := lineSelectionMultiplicityW95 3 1 (Nat.floor (Cbase : Real))
  let Croot : Nat := Nat.ceil ((640 / (alpha : Real) + 1) ^ (6 : Nat)) + 1
  let D : Nat := 2 * (cpackW102 alpha * 3 + 1) ^ (6 : Nat) + 1
  let Cprepare : NNReal := max 1 ((Kbottom : NNReal) * Croot * (D : NNReal) ^ N)
  let Cline : NNReal := ⟨(Tube.overlapConstBOTight 3 : Real) *
      Tube.activeLineConstant 3 1, by
    apply mul_nonneg (Nat.cast_nonneg _)
    unfold Tube.activeLineConstant
    positivity⟩
  let Ctw : NNReal := max 1 (max Cbase Cline)
  let qcut : NNReal := min (alpha / 2) (1 / 16)
  have hqcut : 0 < qcut := lt_min (div_pos halpha (by norm_num)) (by norm_num)
  let delta0 : NNReal := min (qcut ^ (N : Real)) (1 / 2)
  have hdelta0 : 0 < delta0 := lt_min (NNReal.rpow_pos hqcut) (by norm_num)
  have hdelta01 : delta0 < 1 := (min_le_right _ _).trans_lt (by norm_num)
  refine ⟨Ctw, Cprepare, delta0, le_max_left _ _, le_max_left _ _, hdelta0, hdelta01, ?_⟩
  intro delta hd hd0 iota inst F Y hball hcen hline hmass
  have hd1 : delta < 1 := hd0.trans hdelta01
  have hNpos : 0 < N := by omega
  let rho : Nat -> NNReal := Tube.gridScale delta N
  have hrho (k : Nat) : 0 < rho k := Tube.gridScale_pos hd N k
  have hrho1 (k : Nat) : rho k <= 1 := Tube.gridScale_le_one hd1.le N k
  have hq : delta ^ (1 / (N : Real)) <= qcut := by
    calc
      _ <= (qcut ^ (N : Real)) ^ (1 / (N : Real)) := NNReal.rpow_le_rpow
        (hd0.le.trans (min_le_left _ _)) (by positivity)
      _ = qcut := by
        rw [← NNReal.rpow_mul]
        rw [mul_one_div_cancel (show (N : Real) ≠ 0 by exact_mod_cast hNpos.ne'), NNReal.rpow_one]
  have hsucc (k : Nat) : rho (k + 1) = rho k * delta ^ (1 / (N : Real)) := by
    dsimp [rho, Tube.gridScale]
    rw [← NNReal.rpow_add hd.ne']
    congr 1
    push_cast
    ring
  have hsmallgap (k : Nat) : 2 * (rho (k + 1) : Real) <= (alpha * rho k : NNReal) := by
    rw [hsucc, NNReal.coe_mul, NNReal.coe_mul]
    have hh : (delta ^ (1 / (N : Real)) : NNReal) <= alpha / 2 := hq.trans (min_le_left _ _)
    have hhR : ((delta ^ (1 / (N : Real)) : NNReal) : Real) <= (alpha : Real) / 2 := by exact_mod_cast hh
    nlinarith [(rho k).coe_nonneg]
  have hgap (k : Nat) : 2 * (rho (k + 1) : Real) <= (rho k : Real) :=
    (hsmallgap k).trans (by exact_mod_cast mul_le_of_le_one_left (rho k).coe_nonneg halpha1)
  have hrhoSmall (k : Nat) (hk : 1 <= k) : (rho k : Real) <= 1 / 16 := by
    have hh : rho 1 <= 1 / 16 := by
      simpa only [rho, Tube.gridScale, Nat.cast_one] using hq.trans (min_le_right _ _)
    exact_mod_cast (Tube.gridScale_antitone hd hd1.le N hk).trans hh
  have hF : F.Nonempty := by
    by_contra hh
    simpa [Finset.not_nonempty_iff_eq_empty.mp hh] using hmass
  have hfloor : 1 <= Nat.floor (Cbase : Real) := by
    exact (Nat.le_floor_iff Cbase.coe_nonneg).mpr (by exact_mod_cast hCbase)
  have hcenter : ∀ i ∈ F, ‖(Y i).center‖ <= (1 : Real) := by
    intro i hi
    have heq : (Y i).center = (Y i).toTube.midpoint := by
      change midpoint Real (Y i).x (Y i).y = (1 / 2 : Real) • ((Y i).x + (Y i).y)
      rw [midpoint_eq_smul_add]
      norm_num
    rw [heq]
    exact Tube.norm_midpoint_le_of_subset_ball hd (Y i).toTube (hball i hi)
  obtain ⟨A0, hA0F, hA0, hA0ED, hA0mass, _⟩ :=
    exists_pairwise_lineED_paid_w95 hd hd1.le F Y hF 1 (by norm_num)
      hcenter (Nat.floor (Cbase : Real)) hfloor
      ((pointwise_lineED_iff_library_floor_w95 F (fun i => (Y i).toTube) Cbase).mp hline)
      ConvexSpaceBody.closedUnitBall (fun i hi => SetLike.coe_subset_coe.mpr (hball i hi)) hmass
  have hpaid0 : (∑ i ∈ F, volume (Y i).shade) <=
      (Kbottom : ENNReal) * ∑ i ∈ A0, volume (Y i).shade := by simpa only [hdim] using hA0mass
  have hmass0 : 0 < ∑ i ∈ A0, volume (Y i).shade := by
    by_contra hh
    have hz := le_antisymm (not_lt.mp hh) bot_le
    rw [hz, mul_zero] at hpaid0
    exact (not_le_of_gt hmass) hpaid0
  obtain ⟨i0, hi0⟩ := hA0
  choose G hGcover hGsep hGball hGmid using (fun k : Fin N =>
    exists_scaled_grid_net_with_midpoint_w102 (E := E) (hrho k.val) (hrho1 k.val) halpha halpha1)
  let P : (k : Fin (N + 1)) -> Finset (Tube (rho k.val) E) := fun k =>
    if hk : k.val < N then (G ⟨k.val, hk⟩).image (fun W => W.rescale (rho k.val))
    else A0.image (fun i => (Y i).toTube.rescale (rho k.val))
  have hPmid (k : Fin (N + 1)) (W : Tube (rho k.val) E) (hW : W ∈ P k) :
      W.midpoint ∈ Metric.closedBall (0 : E) 3 := by
    by_cases hk : k.val < N
    · simp only [P, dif_pos hk] at hW
      obtain ⟨V, hV, rfl⟩ := Finset.mem_image.mp hW
      exact hGmid ⟨k.val, hk⟩ V hV
    · simp only [P, dif_neg hk] at hW
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hW
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (Tube.norm_midpoint_le_of_subset_ball hd (Y i).toTube (hball i (hA0F hi))).trans
        (by norm_num)
  have hchoose (k : Fin N) (W : {V : Tube (rho k.succ.val) E // V ∈ P k.succ}) :
      ∃ V ∈ G k, W.val.toConvexSpaceBody <= V.toConvexSpaceBody ∧
        ‖W.val.midpoint - V.midpoint‖ <= (alpha * rho k.val : Real) / 32 ∧
        ‖W.val.direction - V.direction‖ <= (alpha * rho k.val : Real) / 16 :=
    hGcover k W.val (hsmallgap k.val) (hPmid k.succ W.val W.property)
  let smallStep (k : Fin N) (W : {V : Tube (rho k.succ.val) E // V ∈ P k.succ}) :=
    (hchoose k W).choose
  have hstepSpec (k : Fin N) (W : {V : Tube (rho k.succ.val) E // V ∈ P k.succ}) :=
    (hchoose k W).choose_spec
  let leaf (i : iota) : {W : Tube (rho (Fin.last N).val) E // W ∈ P (Fin.last N)} :=
    if hi : i ∈ A0 then ⟨(Y i).toTube.rescale (rho N), by
      simp only [P, Fin.val_last, lt_self_iff_false, ↓reduceDIte]
      exact Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩ else
      ⟨(Y i0).toTube.rescale (rho N), by
        simp only [P, Fin.val_last, lt_self_iff_false, ↓reduceDIte]
        exact Finset.mem_image.mpr ⟨i0, hi0, rfl⟩⟩
  let parentStep (k : Fin N) (W : {V : Tube (rho k.succ.val) E // V ∈ P k.succ}) :
      {V : Tube (rho k.castSucc.val) E // V ∈ P k.castSucc} :=
    ⟨(smallStep k W).rescale (rho k.val), by
      simp only [P, Fin.coe_castSucc, dif_pos k.isLt]
      exact Finset.mem_image.mpr ⟨smallStep k W, (hstepSpec k W).1, rfl⟩⟩
  let anc : (k : Fin (N + 1)) -> iota -> {W : Tube (rho k.val) E // W ∈ P k} :=
    fun k i => Fin.reverseInduction (leaf i) parentStep k
  have hancStep (k : Fin N) (i : iota) :
      (anc k.castSucc i).val = (smallStep k (anc k.succ i)).rescale (rho k.val) := by
    dsimp only [anc]
    rw [Fin.reverseInduction_castSucc]
  have hancLast (i : iota) (hi : i ∈ A0) :
      (anc (Fin.last N) i).val = (Y i).toTube.rescale (rho N) := by
    simp only [anc, Fin.reverseInduction_last, leaf, dif_pos hi]
  have hparentBody (k : Fin N) (W : {V : Tube (rho k.succ.val) E // V ∈ P k.succ}) :
      (smallStep k W).toConvexSpaceBody <= ((smallStep k W).rescale (rho k.val)).toConvexSpaceBody := by
    simpa only [Tube.toConvexSpaceBody_rescale_self] using Tube.rescale_le_rescale_of_radius_le
      (smallStep k W) (mul_le_of_le_one_left (rho k.val).coe_nonneg halpha1)
  have hancBounds (k : Fin (N + 1)) (i : iota) (hi : i ∈ A0) :
      (Y i).toConvexSpaceBody <= (anc k i).val.toConvexSpaceBody ∧
      ‖(Y i).toTube.midpoint - (anc k i).val.midpoint‖ <= (alpha : Real) * (rho k.val : Real) / 16 ∧
      ‖(Y i).toTube.direction - (anc k i).val.direction‖ <= (alpha : Real) * (rho k.val : Real) / 8 := by
    induction k using Fin.reverseInduction with
    | last =>
      rw [hancLast i hi]
      refine ⟨?_, ?_, ?_⟩
      · change (Y i).toConvexSpaceBody <= ((Y i).toTube.rescale (Tube.gridScale delta N N)).toConvexSpaceBody
        rw [Tube.gridScale_self delta hNpos, Tube.toConvexSpaceBody_rescale_self]
      · change ‖(Y i).toTube.midpoint - (Y i).toTube.midpoint‖ <= _
        rw [sub_self, norm_zero]
        positivity
      · change ‖(Y i).toTube.direction - (Y i).toTube.direction‖ <= _
        rw [sub_self, norm_zero]
        positivity
    | cast k ih =>
      rw [hancStep]
      have hs := hstepSpec k (anc k.succ i)
      refine ⟨ih.1.trans (hs.2.1.trans (hparentBody k (anc k.succ i))), ?_, ?_⟩
      · have ht := norm_sub_le_norm_sub_add_norm_sub (Y i).toTube.midpoint
          (anc k.succ i).val.midpoint (smallStep k (anc k.succ i)).midpoint
        have hgapPaid := mul_le_mul_of_nonneg_left (hgap k.val) alpha.coe_nonneg
        have hmid := hs.2.2.1
        change ‖(Y i).toTube.midpoint - (smallStep k (anc k.succ i)).midpoint‖ <= _
        dsimp only [Fin.val_succ, Fin.coe_castSucc] at *
        linarith [ih.2.1]
      · have ht := norm_sub_le_norm_sub_add_norm_sub (Y i).toTube.direction
          (anc k.succ i).val.direction (smallStep k (anc k.succ i)).direction
        have hgapPaid := mul_le_mul_of_nonneg_left (hgap k.val) alpha.coe_nonneg
        have hdir := hs.2.2.2
        change ‖(Y i).toTube.direction - (smallStep k (anc k.succ i)).direction‖ <= _
        dsimp only [Fin.val_succ, Fin.coe_castSucc] at *
        linarith [ih.2.2]
  have hancNested (k : Fin N) (i j : iota)
      (hij : (anc k.succ i).val = (anc k.succ j).val) :
      (anc k.castSucc i).val = (anc k.castSucc j).val := by
    rw [hancStep, hancStep, show anc k.succ i = anc k.succ j from Subtype.ext hij]
  have hancBodyStep (k : Fin N) (i : iota) :
      (anc k.succ i).val.toConvexSpaceBody <= (anc k.castSucc i).val.toConvexSpaceBody := by
    rw [hancStep]
    exact (hstepSpec k (anc k.succ i)).2.1.trans (hparentBody k (anc k.succ i))
  let smallAnc (k : Fin N) (i : iota) := smallStep k (anc k.succ i)
  have hsmallAncMem (k : Fin N) (i : iota) : smallAnc k i ∈ G k := (hstepSpec k (anc k.succ i)).1
  have hsmallAncBody (k : Fin N) (i : iota) (hi : i ∈ A0) :
      (Y i).toConvexSpaceBody <= (smallAnc k i).toConvexSpaceBody :=
    (hancBounds k.succ i hi).1.trans (hstepSpec k (anc k.succ i)).2.1
  have hnearby (k : Fin N) (W V : Tube (alpha * rho k.val) E)
      (hclose : ‖W.x - V.x‖ + ‖W.y - V.y‖ < (rho k.val : Real) / 32) :
      W.toConvexSpaceBody <= (V.rescale (rho k.val)).toConvexSpaceBody := by
    have hmid : ‖W.midpoint - V.midpoint‖ <= (rho k.val : Real) / 64 := by
      have heq : W.midpoint - V.midpoint =
          (1 / 2 : Real) • ((W.x - V.x) + (W.y - V.y)) := by
        dsimp only [Tube.midpoint]
        module
      rw [heq, norm_smul]
      norm_num only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : Real) < 1 / 2)]
      have hh := norm_add_le (W.x - V.x) (W.y - V.y)
      linarith
    have hdir : ‖W.direction - V.direction‖ <= (rho k.val : Real) / 32 := by
      have heq : W.direction - V.direction = (W.y - V.y) - (W.x - V.x) := by
        dsimp only [Tube.direction]
        abel
      rw [heq]
      have hh := norm_sub_le (W.y - V.y) (W.x - V.x)
      linarith
    apply Tube.le_of_params_close W (V.rescale (rho k.val)) hmid hdir
    have haR : (alpha : Real) <= 1 / 400 := by exact_mod_cast halphaSmall
    change (rho k.val : Real) / 64 + (rho k.val : Real) / 32 / 2 +
      (alpha * rho k.val : NNReal) <= (rho k.val : Real)
    rw [NNReal.coe_mul]
    nlinarith [(rho k.val).coe_nonneg]
  have hpruneStep (S : Finset iota) (hSA0 : S ⊆ A0)
      (hSpos : 0 < ∑ i ∈ S, volume (Y i).shade) (k : Fin N) :
      ∃ B ⊆ S, (0 < ∑ i ∈ B, volume (Y i).shade) ∧
        (∑ i ∈ S, volume (Y i).shade) <= (D : ENNReal) * ∑ i ∈ B, volume (Y i).shade ∧
        (∀ W ∈ B.image (smallAnc k), ∀ V ∈ B.image (smallAnc k), W ≠ V ->
          (rho k.val : Real) / 32 <= ‖W.x - V.x‖ + ‖W.y - V.y‖) := by
    let H := S.image (smallAnc k)
    let w (W : Tube (alpha * rho k.val) E) :=
      ∑ i ∈ S.filter (fun i => smallAnc k i = W), volume (Y i).shade
    have hdegree (V : Tube (alpha * rho k.val) E) (hV : V ∈ H) :
        {W ∈ (H : Set (Tube (alpha * rho k.val) E)) |
          ‖W.x - V.x‖ + ‖W.y - V.y‖ < (rho k.val : Real) / 32}.ncard <=
          2 * (cpackW102 alpha * 3 + 1) ^ (6 : Nat) := by
      let B := H.filter (fun W => ‖W.x - V.x‖ + ‖W.y - V.y‖ < (rho k.val : Real) / 32)
      have heq : {W ∈ (H : Set (Tube (alpha * rho k.val) E)) |
          ‖W.x - V.x‖ + ‖W.y - V.y‖ < (rho k.val : Real) / 32} = (B : Set _) := by
        ext W
        simp only [B, Finset.mem_coe, Finset.mem_filter, Set.mem_setOf_eq]
      rw [heq, Set.ncard_coe_finset]
      have hsubset : B ⊆ (G k).filter (fun W => ∃ U : Tube delta E,
          U.carrier ⊆ Metric.closedBall (0 : E) 1 ∧
          U.toConvexSpaceBody <= (W.rescale (rho k.val)).toConvexSpaceBody ∧
          U.toConvexSpaceBody <= (V.rescale (rho k.val)).toConvexSpaceBody) := by
        intro W hW
        obtain ⟨hWH, hWV⟩ := Finset.mem_filter.mp hW
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hWH
        refine Finset.mem_filter.mpr ⟨hsmallAncMem k i, (Y i).toTube,
          hball i (hA0F (hSA0 hi)), ?_, ?_⟩
        · exact (hsmallAncBody k i (hSA0 hi)).trans (hparentBody k (anc k.succ i))
        · exact (hsmallAncBody k i (hSA0 hi)).trans (hnearby k _ V hWV)
      have hpack := scaled_grid_overlap_target_cpack_w102 (delta := delta)
        (hrho k.val) halpha halpha1 (G k) (hGsep k) (V.rescale (rho k.val))
      exact (Finset.card_le_card hsubset).trans (by simpa only [hdim] using hpack)
    obtain ⟨J, hJH, hJsep, hpaidJ⟩ := exists_weighted_separated_subset_w102 H
      (fun W V => ‖W.x - V.x‖ + ‖W.y - V.y‖) ((rho k.val : Real) / 32)
      (div_pos (by exact_mod_cast hrho k.val) (by norm_num))
      (fun W V => by rw [norm_sub_rev W.x V.x, norm_sub_rev W.y V.y])
      (fun W => by simp only [sub_self, norm_zero, add_zero]) hdegree w
    let B := S.filter (fun i => smallAnc k i ∈ J)
    have hBpaid : (∑ i ∈ S, volume (Y i).shade) <= (D : ENNReal) * ∑ i ∈ B, volume (Y i).shade := by
      have hsumH : (∑ W ∈ H, w W) = ∑ i ∈ S, volume (Y i).shade :=
        Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image.mpr ⟨i, hi, rfl⟩) _
      have hsumJ : (∑ W ∈ J, w W) = ∑ i ∈ B, volume (Y i).shade :=
        Finset.sum_fiberwise_eq_sum_filter S J (smallAnc k) _
      rw [hsumH, hsumJ] at hpaidJ
      exact hpaidJ
    have hBpos : 0 < ∑ i ∈ B, volume (Y i).shade := by
      by_contra hh
      rw [le_antisymm (not_lt.mp hh) bot_le, mul_zero] at hBpaid
      exact (not_le_of_gt hSpos) hBpaid
    refine ⟨B, Finset.filter_subset _ _, hBpos, hBpaid, ?_⟩
    intro W hW V hV hWV
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hW
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hV
    exact hJsep _ (Finset.mem_filter.mp hi).2 _ (Finset.mem_filter.mp hj).2 hWV
  let zeroLevel : Fin N := ⟨0, hNpos⟩
  have hGzero : (G zeroLevel).Nonempty := ⟨smallAnc zeroLevel i0, hsmallAncMem zeroLevel i0⟩
  have hrootCard : (G zeroLevel).card <= Croot := by
    have hloc (W : Tube (alpha * rho zeroLevel.val) E) (hW : W ∈ G zeroLevel) :
        ‖W.x - (0 : E)‖ <= 5 ∧ ‖W.y - (0 : E)‖ <= 5 := by
      constructor
      · have hh := hGball zeroLevel W hW
          (W.carrier_eq ▸ Set.mem_iUnion₂.mpr ⟨W.x, left_mem_segment Real W.x W.y,
            Metric.mem_closedBall_self (by positivity)⟩)
        simpa only [Metric.mem_closedBall, dist_zero_right, sub_zero] using hh
      · have hh := hGball zeroLevel W hW
          (W.carrier_eq ▸ Set.mem_iUnion₂.mpr ⟨W.y, right_mem_segment Real W.x W.y,
            Metric.mem_closedBall_self (by positivity)⟩)
        simpa only [Metric.mem_closedBall, dist_zero_right, sub_zero] using hh
    have hsep0 : ∀ W ∈ G zeroLevel, ∀ V ∈ G zeroLevel, W ≠ V ->
        (alpha : Real) / 32 <= ‖W.x - V.x‖ + ‖W.y - V.y‖ := by
      simpa only [zeroLevel, rho, Tube.gridScale_zero, NNReal.coe_one, mul_one] using hGsep zeroLevel
    have hpack := Tube.card_le_of_L1_separated_in_box (G zeroLevel)
      (fun W => W.x) (fun W => W.y) (0 : E) (0 : E)
      (show (0 : Real) < (alpha : Real) / 32 by positivity) hsep0
      (fun W hW => (hloc W hW).1) (fun W hW => (hloc W hW).2)
    have heq : ((5 : Real) + ((alpha : Real) / 32) / 4) / (((alpha : Real) / 32) / 4) =
        640 / (alpha : Real) + 1 := by field_simp; ring
    rw [heq, hdim] at hpack
    have hceil : ((G zeroLevel).card : Real) <= (Croot : Real) :=
      hpack.trans ((Nat.le_ceil _).trans (by dsimp only [Croot]; push_cast; linarith))
    exact_mod_cast hceil
  let rootWeight (W : Tube (alpha * rho zeroLevel.val) E) :=
    ∑ i ∈ A0.filter (fun i => smallAnc zeroLevel i = W), volume (Y i).shade
  obtain ⟨rootNode, hrootMem, hrootMax⟩ := (G zeroLevel).exists_max_image rootWeight hGzero
  let Aroot := A0.filter (fun i => smallAnc zeroLevel i = rootNode)
  have hArootA0 : Aroot ⊆ A0 := Finset.filter_subset _ _
  have hrootPaid : (∑ i ∈ A0, volume (Y i).shade) <=
      (Croot : ENNReal) * ∑ i ∈ Aroot, volume (Y i).shade := by
    calc
      _ = ∑ W ∈ G zeroLevel, rootWeight W :=
        (Finset.sum_fiberwise_of_maps_to (fun i hi => hsmallAncMem zeroLevel i) _).symm
      _ <= ∑ W ∈ G zeroLevel, rootWeight rootNode := Finset.sum_le_sum (fun W hW => hrootMax W hW)
      _ = ((G zeroLevel).card : ENNReal) * ∑ i ∈ Aroot, volume (Y i).shade := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ <= _ := mul_le_mul_right' (by exact_mod_cast hrootCard) _
  have hrootPos : 0 < ∑ i ∈ Aroot, volume (Y i).shade := by
    by_contra hh
    rw [le_antisymm (not_lt.mp hh) bot_le, mul_zero] at hrootPaid
    exact (not_le_of_gt hmass0) hrootPaid
  have hpruning (n : Nat) (hn : n <= N) :
      ∃ A ⊆ Aroot, (0 < ∑ i ∈ A, volume (Y i).shade) ∧
        (∑ i ∈ Aroot, volume (Y i).shade) <= (D : ENNReal) ^ n * ∑ i ∈ A, volume (Y i).shade ∧
        (∀ k : Fin N, k.val < n -> ∀ W ∈ A.image (smallAnc k), ∀ V ∈ A.image (smallAnc k), W ≠ V ->
          (rho k.val : Real) / 32 <= ‖W.x - V.x‖ + ‖W.y - V.y‖) := by
    induction n with
    | zero =>
      exact ⟨Aroot, Finset.Subset.refl _, hrootPos, by simp only [pow_zero, one_mul, le_refl], by omega⟩
    | succ n ih =>
      obtain ⟨S, hSAroot, hSpos, hSpaid, hSsep⟩ := ih (by omega)
      obtain ⟨B, hBS, hBpos, hBpaid, hBsep⟩ := hpruneStep S (hSAroot.trans hArootA0) hSpos ⟨n, by omega⟩
      refine ⟨B, hBS.trans hSAroot, hBpos, ?_, ?_⟩
      · calc
          _ <= (D : ENNReal) ^ n * ((D : ENNReal) * ∑ i ∈ B, volume (Y i).shade) :=
            hSpaid.trans (mul_le_mul_left' hBpaid _)
          _ = _ := by rw [pow_succ]; ring
      · intro k hk W hW V hV hWV
        by_cases hkn : k.val < n
        · exact hSsep k hkn W (Finset.image_subset_image hBS hW) V (Finset.image_subset_image hBS hV) hWV
        · have hkEq : k = (⟨n, by omega⟩ : Fin N) := Fin.ext (show k.val = n by omega)
          have hsepK := hBsep
          rw [← hkEq] at hsepK
          exact hsepK W hW V hV hWV
  obtain ⟨A, hAAroot, hApos, hApaid, hAsep⟩ := hpruning N le_rfl
  have hAA0 : A ⊆ A0 := hAAroot.trans hArootA0
  have hAF : A ⊆ F := hAA0.trans hA0F
  have hA : A.Nonempty := by
    by_contra hh
    simpa only [Finset.not_nonempty_iff_eq_empty.mp hh, Finset.sum_empty, lt_self_iff_false] using hApos
  have hpaid : (∑ i ∈ F, volume (Y i).shade) <= (Cprepare : ENNReal) * ∑ i ∈ A, volume (Y i).shade := by
    calc
      _ <= (Kbottom : ENNReal) * ((Croot : ENNReal) *
          ((D : ENNReal) ^ N * ∑ i ∈ A, volume (Y i).shade)) :=
        hpaid0.trans (mul_le_mul_left' (hrootPaid.trans (mul_le_mul_left' hApaid _)) _)
      _ = ((Kbottom : ENNReal) * Croot * (D : ENNReal) ^ N) * ∑ i ∈ A, volume (Y i).shade := by ring
      _ <= _ := mul_le_mul_right' (by
        dsimp only [Cprepare]
        exact_mod_cast (le_max_right (1 : NNReal) ((Kbottom : NNReal) * Croot * (D : NNReal) ^ N))) _
  obtain ⟨j0, hj0⟩ := hA
  have hA : A.Nonempty := ⟨j0, hj0⟩
  have hrootSame (i : iota) (hi : i ∈ A) : smallAnc zeroLevel i = smallAnc zeroLevel j0 :=
    (Finset.mem_filter.mp (hAAroot hi)).2.trans (Finset.mem_filter.mp (hAAroot hj0)).2.symm
  have hrescaleInj {r s : NNReal} : Function.Injective (fun T : Tube r E => T.rescale s) := by
    intro V W hVW
    have hx : V.x = W.x := congrArg (fun T : Tube s E => T.x) hVW
    have hy : V.y = W.y := congrArg (fun T : Tube s E => T.y) hVW
    apply Tube.ext _ hx hy
    rw [V.carrier_eq, W.carrier_eq, hx, hy]
  have hrootAnc (i : iota) (hi : i ∈ A) :
      (anc zeroLevel.castSucc i).val = (anc zeroLevel.castSucc j0).val := by
    rw [hancStep, hancStep]
    change (smallAnc zeroLevel i).rescale _ = (smallAnc zeroLevel j0).rescale _
    rw [hrootSame i hi]
  have hrootPair (i : iota) (hi : i ∈ A) :
      ‖(Y i).toTube.midpoint - (Y j0).toTube.midpoint‖ <= (alpha : Real) / 8 ∧
      ‖(Y i).toTube.direction - (Y j0).toTube.direction‖ <= (alpha : Real) / 4 := by
    have hI := hancBounds zeroLevel.castSucc i (hAA0 hi)
    have hJ := hancBounds zeroLevel.castSucc j0 (hAA0 hj0)
    rw [hrootAnc i hi] at hI
    have hm := norm_sub_le_norm_sub_add_norm_sub (Y i).toTube.midpoint
      (anc zeroLevel.castSucc j0).val.midpoint (Y j0).toTube.midpoint
    have hv := norm_sub_le_norm_sub_add_norm_sub (Y i).toTube.direction
      (anc zeroLevel.castSucc j0).val.direction (Y j0).toTube.direction
    rw [norm_sub_rev (anc zeroLevel.castSucc j0).val.midpoint] at hm
    rw [norm_sub_rev (anc zeroLevel.castSucc j0).val.direction] at hv
    simp only [zeroLevel, Fin.val_castSucc, rho, Tube.gridScale_zero, NNReal.coe_one, mul_one] at hI hJ
    constructor <;> linarith [hI.2.1, hI.2.2, hJ.2.1, hJ.2.2]
  have hrootBounds (k : Fin (N + 1)) (i : iota) (hi : i ∈ A) :
      ‖(anc k i).val.midpoint - (Y j0).toTube.midpoint‖ <=
        (alpha : Real) * (rho k.val : Real) / 16 + (alpha : Real) / 8 ∧
      ‖(anc k i).val.direction - (Y j0).toTube.direction‖ <=
        (alpha : Real) * (rho k.val : Real) / 8 + (alpha : Real) / 4 := by
    have hbound := hancBounds k i (hAA0 hi)
    have hpair := hrootPair i hi
    have hm := norm_sub_le_norm_sub_add_norm_sub (anc k i).val.midpoint (Y i).toTube.midpoint (Y j0).toTube.midpoint
    have hv := norm_sub_le_norm_sub_add_norm_sub (anc k i).val.direction (Y i).toTube.direction (Y j0).toTube.direction
    rw [norm_sub_rev (anc k i).val.midpoint (Y i).toTube.midpoint] at hm
    rw [norm_sub_rev (anc k i).val.direction (Y i).toTube.direction] at hv
    constructor <;> linarith [hbound.2.1, hbound.2.2, hpair.1, hpair.2]
  let kf (k : Nat) : Fin (N + 1) := if hk : k <= N then ⟨k, by omega⟩ else Fin.last N
  have hkf (k : Nat) (hk : k <= N) : (kf k).val = k := by simp only [kf, dif_pos hk]
  have hkfLast : kf N = Fin.last N := Fin.ext (hkf N le_rfl)
  have hkfCast (k : Nat) (hk : k < N) : kf k = (⟨k, hk⟩ : Fin N).castSucc :=
    Fin.ext (hkf k hk.le)
  have hkfSucc (k : Nat) (hk : k < N) : kf (k + 1) = (⟨k, hk⟩ : Fin N).succ :=
    Fin.ext (hkf (k + 1) (by omega))
  have hfirstRoot (i : iota) (hi : i ∈ A) :
      (anc (kf 1) i).val.toConvexSpaceBody <= ((Y j0).toTube.rescale 1).toConvexSpaceBody := by
    have hbounds := hrootBounds (kf 1) i hi
    apply Tube.le_of_params_close (anc (kf 1) i).val ((Y j0).toTube.rescale 1) hbounds.1 hbounds.2
    have hr := hrhoSmall 1 (by omega)
    have ha : (alpha : Real) <= 1 := by exact_mod_cast halpha1
    have hprod := mul_le_mul_of_nonneg_right ha (rho 1).coe_nonneg
    simp only [hkf 1 hN] at *
    norm_num only [NNReal.coe_one] at *
    nlinarith
  let rep (k : Fin (N + 1)) (V : Tube (rho k.val) E) : iota :=
    if hv : ∃ i ∈ A, (anc k i).val = V then hv.choose else j0
  have hrepMem (k : Fin (N + 1)) (V : Tube (rho k.val) E) : rep k V ∈ A := by
    dsimp only [rep]
    split
    · rename_i h
      exact h.choose_spec.1
    · exact hj0
  have hrepAnc (k : Fin (N + 1)) (i : iota) (hi : i ∈ A) :
      (anc k (rep k (anc k i).val)).val = (anc k i).val := by
    have hh : ∃ j ∈ A, (anc k j).val = (anc k i).val := ⟨i, hi, rfl⟩
    simp only [rep, dif_pos hh]
    exact hh.choose_spec.2
  let assign (k : Nat) (i : iota) := if k = 0 then j0 else if k = N then i else rep (kf k) (anc (kf k) i).val
  let W (k : Nat) (R : iota) : Tube (rho k) E :=
    if k = 0 then (Y j0).toTube.rescale (rho k) else (anc (kf k) R).val.rescale (rho k)
  have hassignMem (k : Nat) (i : iota) (hi : i ∈ A) : assign k i ∈ A := by
    dsimp only [assign]
    split
    · exact hj0
    · split
      · exact hi
      · exact hrepMem _ _
  have hassignBottom (i : iota) : assign N i = i := by
    simp [assign, hNpos.ne']
  have hassignAnc (k : Nat) (hk0 : k ≠ 0) (i : iota) (hi : i ∈ A) :
      (anc (kf k) (assign k i)).val = (anc (kf k) i).val := by
    by_cases hkN : k = N
    · simp only [assign, if_neg hk0, if_pos hkN]
    · simpa only [assign, if_neg hk0, if_neg hkN] using hrepAnc (kf k) i hi
  have hWbody (k : Nat) (hk : k <= N) (hk0 : k ≠ 0) (R : iota) :
      (W k R).toConvexSpaceBody = (anc (kf k) R).val.toConvexSpaceBody := by
    simp only [W, if_neg hk0]
    rw [show rho k = rho (kf k).val from congrArg rho (hkf k hk).symm,
      Tube.toConvexSpaceBody_rescale_self]
  have hWmid (k : Nat) (hk0 : k ≠ 0) (R : iota) : (W k R).midpoint = (anc (kf k) R).val.midpoint := by
    simp only [W, if_neg hk0]
    rfl
  have hWdir (k : Nat) (hk0 : k ≠ 0) (R : iota) : (W k R).direction = (anc (kf k) R).val.direction := by
    simp only [W, if_neg hk0]
    rfl
  have hWassigned (k : Nat) (hk : k <= N) (hk0 : k ≠ 0) (i : iota) (hi : i ∈ A) :
      (W k (assign k i)).toConvexSpaceBody = (anc (kf k) i).val.toConvexSpaceBody := by
    rw [hWbody k hk hk0, hassignAnc k hk0 i hi]
  have hWzero (R : iota) : (W 0 R).toConvexSpaceBody = ((Y j0).toTube.rescale 1).toConvexSpaceBody := by
    change ((Y j0).toTube.rescale (rho 0)).toConvexSpaceBody = _
    exact congrArg (fun r : NNReal => ((Y j0).toTube.rescale r).toConvexSpaceBody)
      (Tube.gridScale_zero delta N)
  have hWbottom (i : iota) (hi : i ∈ A) : (W N i).toConvexSpaceBody = (Y i).toConvexSpaceBody := by
    rw [hWbody N le_rfl hNpos.ne', hkfLast, hancLast i (hAA0 hi)]
    change ((Y i).toTube.rescale (Tube.gridScale delta N N)).toConvexSpaceBody = _
    rw [Tube.gridScale_self delta hNpos, Tube.toConvexSpaceBody_rescale_self]
  have hclasses (k : Nat) (hk : k + 1 <= N) (i : iota) (hi : i ∈ A) (j : iota) (hj : j ∈ A)
      (hij : assign (k + 1) i = assign (k + 1) j) : assign k i = assign k j := by
    by_cases hk0 : k = 0
    · simp only [assign, if_pos hk0]
    · have hnext : (anc (kf (k + 1)) i).val = (anc (kf (k + 1)) j).val := by
        rw [← hassignAnc (k + 1) (by omega) i hi, ← hassignAnc (k + 1) (by omega) j hj, hij]
      rw [hkfSucc k (by omega)] at hnext
      have hprev := hancNested ⟨k, by omega⟩ i j hnext
      rw [← hkfCast k (by omega)] at hprev
      simp only [assign, if_neg hk0, if_neg (by omega : k ≠ N), hprev]
  let cov : Tube.GridCoverSystem A (fun i => (Y i).toTube) N := {
    indexSet := fun k => A.image (assign k)
    assign := assign
    tube := W
    assign_mem := fun k hk i hi => Finset.mem_image.mpr ⟨i, hi, rfl⟩
    le_tube_assign := by
      intro k hk i hi
      by_cases hk0 : k = 0
      · subst k
        rw [hWzero]
        exact (hancBounds (kf 1) i (hAA0 hi)).1.trans (hfirstRoot i hi)
      · rw [hWassigned k hk hk0 i hi]
        exact (hancBounds (kf k) i (hAA0 hi)).1
    nested := hclasses
    tube_nested := by
      intro k hk i hi
      by_cases hk0 : k = 0
      · subst k
        rw [hWzero, hWassigned 1 hN (by omega) i hi]
        exact hfirstRoot i hi
      · rw [hWassigned (k + 1) hk (by omega) i hi, hWassigned k (by omega) hk0 i hi,
          hkfSucc k (by omega), hkfCast k (by omega)]
        exact hancBodyStep ⟨k, by omega⟩ i
  }
  have hbottomIndex : cov.indexSet N = A := by
    change A.image (assign N) = A
    calc
      _ = A.image id := Finset.image_congr (fun i hi => hassignBottom i)
      _ = A := Finset.image_id
  have hindexSub (k : Nat) : cov.indexSet k ⊆ A := by
    intro R hR
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hR
    exact hassignMem k i hi
  have hcarrierInj : Set.InjOn (fun i => (Y i).carrier) (A : Set iota) := by
    intro i hi j hj hij
    by_contra hne
    have hh := hA0ED (hAA0 hi) (hAA0 hj) hne
    change (Y i).carrier = (Y j).carrier at hij
    change IsEssentiallyDistinct (Y i).carrier (Y j).carrier at hh
    rw [hij] at hh
    obtain ⟨hp, ht⟩ := Tube.volume_pos_and_lt_top hd hd1.le (Y j).toTube
    exact not_isEssentiallyDistinct_self hp.ne' ht.ne hh
  have hnodeRep (k : Nat) (hk0 : k ≠ 0) (hkN : k ≠ N) (R : iota) (hR : R ∈ cov.indexSet k) :
      R = rep (kf k) (anc (kf k) R).val := by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hR
    rw [hassignAnc k hk0 i hi]
    simp only [assign, if_neg hk0, if_neg hkN]
  have hWinj (k : Nat) (hk : k <= N) : Set.InjOn (cov.tube k) (cov.indexSet k : Set iota) := by
    intro R hR S hS hRS
    by_cases hk0 : k = 0
    · obtain ⟨i, hi, hir⟩ := Finset.mem_image.mp hR
      obtain ⟨j, hj, hjs⟩ := Finset.mem_image.mp hS
      simp only [assign, if_pos hk0] at hir hjs
      exact hir.symm.trans hjs
    · by_cases hkN : k = N
      · subst k
        apply hcarrierInj (hindexSub N hR) (hindexSub N hS)
        have hh := congrArg (fun T : Tube (rho N) E => T.toConvexSpaceBody) hRS
        rw [hWbottom R (hindexSub N hR), hWbottom S (hindexSub N hS)] at hh
        exact congrArg ConvexSpaceBody.carrier hh
      · have heq : (anc (kf k) R).val = (anc (kf k) S).val := by
          apply hrescaleInj (s := rho k)
          simpa only [cov, W, if_neg hk0] using hRS
        rw [hnodeRep k hk0 hkN R hR, hnodeRep k hk0 hkN S hS, heq]
  have hcenterMid {r : NNReal} (T : Tube r E) : T.center = T.midpoint := by
    dsimp only [Tube.center, Tube.midpoint]
    rw [midpoint_eq_smul_add]
    norm_num
  have hmargin : ActualTreeParameterMarginW98 cov kappa := by
    have halphaEq : (kappa : Real) = 4 * (alpha : Real) := by dsimp only [alpha]; push_cast; ring
    constructor
    · intro k l hkl hl i hi
      change ‖(W l (assign l i)).center - (W k (assign k i)).center‖ <= _
      rw [hcenterMid, hcenterMid, hWmid l (by omega), hassignAnc l (by omega) i hi]
      by_cases hk0 : k = 0
      · subst k
        have hh := (hrootBounds (kf l) i hi).1
        have hr : (rho (kf l).val : Real) <= 1 := by exact_mod_cast hrho1 (kf l).val
        have hm := mul_le_mul_of_nonneg_left hr alpha.coe_nonneg
        change ‖(anc (kf l) i).val.midpoint - (Y j0).toTube.midpoint‖ <= _
        rw [Tube.gridScale_zero, NNReal.coe_one, mul_one, halphaEq]
        linarith [alpha.coe_nonneg]
      · rw [hWmid k hk0, hassignAnc k hk0 i hi]
        have hI := (hancBounds (kf l) i (hAA0 hi)).2.1
        have hJ := (hancBounds (kf k) i (hAA0 hi)).2.1
        have ht := norm_sub_le_norm_sub_add_norm_sub (anc (kf l) i).val.midpoint
          (Y i).toTube.midpoint (anc (kf k) i).val.midpoint
        rw [norm_sub_rev (anc (kf l) i).val.midpoint (Y i).toTube.midpoint] at ht
        have hr : (rho l : Real) <= rho k := by exact_mod_cast Tube.gridScale_antitone hd hd1.le N hkl.le
        have hm := mul_le_mul_of_nonneg_left hr alpha.coe_nonneg
        simp only [hkf l hl, hkf k (hkl.le.trans hl)] at hI hJ
        rw [halphaEq]
        change ‖(anc (kf l) i).val.midpoint - (anc (kf k) i).val.midpoint‖ <= 4 * (alpha : Real) * (rho k : Real)
        nlinarith [(rho k).coe_nonneg, alpha.coe_nonneg]
    · intro k l hkl hl i hi
      apply (min_le_left _ _).trans
      change ‖(W l (assign l i)).direction - (W k (assign k i)).direction‖ <= _
      rw [hWdir l (by omega), hassignAnc l (by omega) i hi]
      by_cases hk0 : k = 0
      · subst k
        have hh := (hrootBounds (kf l) i hi).2
        have hr : (rho (kf l).val : Real) <= 1 := by exact_mod_cast hrho1 (kf l).val
        have hm := mul_le_mul_of_nonneg_left hr alpha.coe_nonneg
        change ‖(anc (kf l) i).val.direction - (Y j0).toTube.direction‖ <= _
        rw [Tube.gridScale_zero, NNReal.coe_one, mul_one, halphaEq]
        linarith [alpha.coe_nonneg]
      · rw [hWdir k hk0, hassignAnc k hk0 i hi]
        have hI := (hancBounds (kf l) i (hAA0 hi)).2.2
        have hJ := (hancBounds (kf k) i (hAA0 hi)).2.2
        have ht := norm_sub_le_norm_sub_add_norm_sub (anc (kf l) i).val.direction
          (Y i).toTube.direction (anc (kf k) i).val.direction
        rw [norm_sub_rev (anc (kf l) i).val.direction (Y i).toTube.direction] at ht
        have hr : (rho l : Real) <= rho k := by exact_mod_cast Tube.gridScale_antitone hd hd1.le N hkl.le
        have hm := mul_le_mul_of_nonneg_left hr alpha.coe_nonneg
        simp only [hkf l hl, hkf k (hkl.le.trans hl)] at hI hJ
        rw [halphaEq]
        change ‖(anc (kf l) i).val.direction - (anc (kf k) i).val.direction‖ <= 4 * (alpha : Real) * (rho k : Real)
        nlinarith [(rho k).coe_nonneg, alpha.coe_nonneg]
  have hsmallBall {r : NNReal} (T : Tube r E) (hr : (r : Real) <= 1 / 16)
      (hm : ‖T.midpoint‖ <= 1 + (r : Real) / 16) : T.carrier ⊆ Metric.closedBall (0 : E) 2 := by
    intro x hx
    obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.mp (T.carrier_eq ▸ hx)
    obtain ⟨t, ht, hzt⟩ := T.exists_param_of_mem_segment hz
    have hznorm : ‖z‖ <= 1 + (r : Real) / 16 + 1 / 2 := by
      rw [hzt]
      have hh := norm_add_le T.midpoint (t • T.direction)
      have hs : ‖t • T.direction‖ = |t| := by
        rw [norm_smul, Real.norm_eq_abs, T.norm_direction, mul_one]
      rw [hs] at hh
      linarith
    have htri := dist_triangle x z 0
    rw [dist_zero_right, dist_zero_right] at htri
    have hdist := Metric.mem_closedBall.mp hxz
    rw [Metric.mem_closedBall, dist_zero_right]
    linarith
  have hparentBall (k : Nat) (hk : k <= N) (R : iota) (hR : R ∈ cov.indexSet k) :
      (cov.tube k R).carrier ⊆ Metric.closedBall (0 : E) 2 := by
    by_cases hk0 : k = 0
    · subst k
      change (W 0 R).carrier ⊆ _
      rw [congrArg ConvexSpaceBody.carrier (hWzero R)]
      intro x hx
      obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.mp (((Y j0).toTube.rescale 1).carrier_eq ▸ hx)
      have hzT : z ∈ (Y j0).carrier := by
        rw [(Y j0).toTube.carrier_eq]
        exact Set.mem_iUnion₂.mpr ⟨z, hz, Metric.mem_closedBall_self delta.coe_nonneg⟩
      have hzNorm := Metric.mem_closedBall.mp (hball j0 (hAF hj0) hzT)
      have hdist := Metric.mem_closedBall.mp hxz
      have htri := dist_triangle x z 0
      rw [Metric.mem_closedBall]
      norm_num only [NNReal.coe_one] at hdist
      linarith
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hR
      apply hsmallBall (W k (assign k i)) (hrhoSmall k (by omega))
      rw [hWmid k hk0, hassignAnc k hk0 i hi]
      have hbound := (hancBounds (kf k) i (hAA0 hi)).2.1
      simp only [hkf k hk] at hbound
      have hmidNorm := Tube.norm_midpoint_le_of_subset_ball hd (Y i).toTube (hball i (hAF hi))
      have ht := norm_sub_le_norm_sub_add_norm_sub (anc (kf k) i).val.midpoint (Y i).toTube.midpoint 0
      rw [sub_zero, sub_zero, norm_sub_rev (anc (kf k) i).val.midpoint (Y i).toTube.midpoint] at ht
      have ha : (alpha : Real) <= 1 := by exact_mod_cast halpha1
      have hprod := mul_le_mul_of_nonneg_right ha (rho k).coe_nonneg
      linarith
  have hWsmall (k : Nat) (hk0 : k ≠ 0) (hkN : k < N) (R : iota) :
      W k R = (smallAnc ⟨k, hkN⟩ R).rescale (rho k) := by
    simp only [W, if_neg hk0]
    rw [hkfCast k hkN, hancStep]
    rfl
  have hoverlap (k : Nat) (hk : k <= N) (V : Tube (Tube.gridScale delta N k) E) :
      ((cov.indexSet k).filter (fun R => ∃ i ∈ A,
        (Y i).toConvexSpaceBody <= (cov.tube k R).toConvexSpaceBody ∧
        (Y i).toConvexSpaceBody <= V.toConvexSpaceBody)).card <=
          Tube.overlapConstBOTight (Module.finrank Real E) := by
    have hOne : 1 <= Tube.overlapConstBOTight (Module.finrank Real E) := by
      norm_num [Tube.overlapConstBOTight, hdim]
    by_cases hk0 : k = 0
    · have hcard : (cov.indexSet k).card <= 1 := by
        simp only [cov, assign, if_pos hk0]
        rw [Finset.image_const hA, Finset.card_singleton]
      exact (Finset.card_filter_le _ _).trans (hcard.trans hOne)
    · by_cases hkN : k = N
      · subst k
        apply (Finset.card_le_one.mpr ?_).trans hOne
        intro R hR S hS
        obtain ⟨hRA, i, hi, hiR, hiV⟩ := Finset.mem_filter.mp hR
        obtain ⟨hSA, j, hj, hjS, hjV⟩ := Finset.mem_filter.mp hS
        have hscale : delta = rho N := (Tube.gridScale_self delta hNpos).symm
        have hRV : (Y R).carrier = V.carrier := by
          calc
            _ = (W N R).carrier := (congrArg ConvexSpaceBody.carrier (hWbottom R (hindexSub N hRA))).symm
            _ = (Y i).carrier := (Tube.carrier_eq_of_subset' hscale (Y i).toTube (W N R) hiR).symm
            _ = V.carrier := Tube.carrier_eq_of_subset' hscale (Y i).toTube V hiV
        have hSV : (Y S).carrier = V.carrier := by
          calc
            _ = (W N S).carrier := (congrArg ConvexSpaceBody.carrier (hWbottom S (hindexSub N hSA))).symm
            _ = (Y j).carrier := (Tube.carrier_eq_of_subset' hscale (Y j).toTube (W N S) hjS).symm
            _ = V.carrier := Tube.carrier_eq_of_subset' hscale (Y j).toTube V hjV
        exact hcarrierInj (hindexSub N hRA) (hindexSub N hSA) (hRV.trans hSV.symm)
      · have hklt : k < N := lt_of_le_of_ne hk hkN
        let H := (cov.indexSet k).image (cov.tube k)
        have hsepH : ∀ Q ∈ H, ∀ Q' ∈ H, Q ≠ Q' ->
            (rho k : Real) / 32 <= ‖Q.x - Q'.x‖ + ‖Q.y - Q'.y‖ := by
          intro Q hQ Q' hQ' hne
          obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp hQ
          obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hQ'
          have hneSmall : smallAnc ⟨k, hklt⟩ R ≠ smallAnc ⟨k, hklt⟩ S := by
            intro heq
            apply hne
            change W k R = W k S
            rw [hWsmall k hk0 hklt, hWsmall k hk0 hklt, heq]
          have hh := hAsep ⟨k, hklt⟩ hklt _ (Finset.mem_image.mpr ⟨R, hindexSub k hR, rfl⟩)
            _ (Finset.mem_image.mpr ⟨S, hindexSub k hS, rfl⟩) hneSmall
          change (rho k : Real) / 32 <= ‖(W k R).x - (W k S).x‖ + ‖(W k R).y - (W k S).y‖
          rw [hWsmall k hk0 hklt, hWsmall k hk0 hklt]
          exact hh
        let B := (cov.indexSet k).filter (fun R => ∃ i ∈ A,
          (Y i).toConvexSpaceBody <= (cov.tube k R).toConvexSpaceBody ∧
          (Y i).toConvexSpaceBody <= V.toConvexSpaceBody)
        have hsub : B.image (cov.tube k) ⊆ H.filter (fun Q => ∃ U : Tube delta E,
            U.carrier ⊆ Metric.closedBall (0 : E) 1 ∧
            U.toConvexSpaceBody <= Q.toConvexSpaceBody ∧ U.toConvexSpaceBody <= V.toConvexSpaceBody) := by
          intro Q hQ
          obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp hQ
          obtain ⟨hRidx, i, hi, hiR, hiV⟩ := Finset.mem_filter.mp hR
          exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨R, hRidx, rfl⟩,
            (Y i).toTube, hball i (hAF hi), hiR, hiV⟩
        have hcard : (B.image (cov.tube k)).card = B.card :=
          Finset.card_image_of_injOn (fun R hR S hS => hWinj k hk
            (Finset.mem_filter.mp hR).1 (Finset.mem_filter.mp hS).1)
        calc
          B.card = (B.image (cov.tube k)).card := hcard.symm
          _ <= _ := Finset.card_le_card hsub
          _ <= _ := by
            simpa only [Tube.overlapConstBOTight] using Tube.grid_overlap_tight (δ := delta) (hrho k) H hsepH V
  have hlineLevels (k : Nat) (hk : k <= N) : lineEssentiallyDistinctW94 (cov.indexSet k) (cov.tube k) Ctw := by
    intro o v hv
    by_cases hkN : k = N
    · subst k
      have hsub : (cov.indexSet N).filter (fun i => liesInFiveDeltaLineTubeW94 (cov.tube N i) o v) ⊆
          F.filter (fun i => liesInFiveDeltaLineTubeW94 (Y i).toTube o v) := by
        intro i hi
        obtain ⟨hiA, hitest⟩ := Finset.mem_filter.mp hi
        have hiA' := hindexSub N hiA
        refine Finset.mem_filter.mpr ⟨hAF hiA', ?_⟩
        have hcarrier := congrArg ConvexSpaceBody.carrier (hWbottom i hiA')
        change liesInFiveDeltaLineTubeW94 (W N i) o v at hitest
        dsimp only [liesInFiveDeltaLineTubeW94] at hitest ⊢
        rw [hcarrier] at hitest
        simpa only [rho, Tube.gridScale_self delta hNpos] using hitest
      exact (show (((cov.indexSet N).filter (fun i => liesInFiveDeltaLineTubeW94 (cov.tube N i) o v)).card : NNReal) <=
        (F.filter (fun i => liesInFiveDeltaLineTubeW94 (Y i).toTube o v)).card by exact_mod_cast Finset.card_le_card hsub).trans
        ((hline o v hv).trans ((le_max_left Cbase Cline).trans (le_max_right 1 _)))
    · have hklt : k < N := lt_of_le_of_ne hk hkN
      have h4 : 4 * (delta : Real) <= Tube.gridScale delta N k := by
        have hqsmall : ((delta ^ (1 / (N : Real)) : NNReal) : Real) <= 1 / 16 := by
          exact_mod_cast hq.trans (min_le_right _ _)
        have hdle : delta <= rho (k + 1) := by
          calc
            _ = rho N := (Tube.gridScale_self delta hNpos).symm
            _ <= _ := Tube.gridScale_antitone hd hd1.le N (by omega)
        have hh := mul_le_mul_of_nonneg_left hqsmall (rho k).coe_nonneg
        have hsu := hsucc k
        have hsuR := congrArg (fun x : NNReal => (x : Real)) hsu
        rw [NNReal.coe_mul] at hsuR
        change 4 * (delta : Real) <= (rho k : Real)
        have hdleR : (delta : Real) <= rho (k + 1) := by exact_mod_cast hdle
        nlinarith
      have hcenA (i : iota) (hi : i ∈ A) : (Y i).toTube.IsCentred := by
        dsimp only [Tube.IsCentred]
        rw [← hcenterMid]
        exact hcen i (hAF hi)
      have hlineBound := hlineCover hd cov
        (C := (Tube.overlapConstBOTight (Module.finrank Real E) : NNReal))
        (fun l hl V => by exact_mod_cast hoverlap l hl V) hcenA (by norm_num : (0 : Real) <= 1)
        (fun i hi => Tube.norm_midpoint_le_of_subset_ball hd (Y i).toTube (hball i (hAF hi))) hk h4 o v hv
      have hactive : cov.activeIndexSet k = cov.indexSet k := by
        apply Finset.Subset.antisymm (cov.activeIndexSet_subset k)
        intro R hR
        exact cov.mem_activeIndexSet.mpr ⟨hR, Finset.mem_image.mp hR⟩
      rw [hactive] at hlineBound
      have hfilter : (cov.indexSet k).filter (fun i => liesInFiveDeltaLineTubeW94 (cov.tube k i) o v) =
          (cov.indexSet k).filter (fun i => (cov.tube k i).carrier ⊆
            Metric.cthickening (5 * (Tube.gridScale delta N k : Real))
              (Set.range (fun t : Real => o + t • v))) := by
        apply Finset.filter_congr
        intro i hi
        simpa only [VeryNotSticky.lineNbhd_eq_cthickening_range] using pointwise_line_neighbourhood_iff_w95 (cov.tube k i) o v hv
      rw [hfilter]
      have hb : (((cov.indexSet k).filter (fun i => (cov.tube k i).carrier ⊆
          Metric.cthickening (5 * (Tube.gridScale delta N k : Real))
            (Set.range (fun t : Real => o + t • v)))).card : NNReal) <= Cline := by
        apply NNReal.coe_le_coe.mp
        change _ <= (Tube.overlapConstBOTight 3 : Real) * Tube.activeLineConstant 3 1
        simpa only [hdim, NNReal.coe_natCast] using hlineBound
      exact hb.trans ((le_max_right Cbase Cline).trans (le_max_right 1 _))
  refine ⟨A, hA, hAF, ?_, ⟨{
    cover := cov
    margin := hmargin
    surjective := fun k hk => rfl
    bottom_index := hbottomIndex
    bottom_assign := fun i hi => hassignBottom i
    bottom_tube := hWbottom
    tube_injective := hWinj
    parent_ball := hparentBall
    parent_line_ed := hlineLevels
    tight_overlap := hoverlap }⟩⟩
  calc
    _ <= (Cprepare : ENNReal)⁻¹ * ((Cprepare : ENNReal) * ∑ i ∈ A, volume (Y i).shade) :=
      mul_le_mul_left' hpaid _
    _ = _ := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel
        (ENNReal.coe_pos.mpr (zero_lt_one.trans_le (le_max_left _ _))).ne' ENNReal.coe_ne_top, one_mul]

/-- Actual P2 band selection on the same prepared tree. Parent tubes and
assignments survive literally, so the old parameter margin is inherited. -/
theorem exists_actual_regularization_of_prepared_raw_tree_w98
    (hdim : Module.finrank Real E = 3) (N : Nat) (hN : 1 <= N)
    (kappa Ctw : NNReal) (hkappa : 0 < kappa) (hkappaSmall : kappa <= 1 / 100)
    (hCtw : 1 <= Ctw) :
    ∃ (Ccan Ccell Cprepare : NNReal) (Kprepare : Nat) (delta0 : NNReal),
      1 <= Ccan ∧ 1 <= Ccell ∧ 1 <= Cprepare ∧ 1 <= Kprepare ∧
      0 < delta0 ∧ delta0 < 1 ∧
      ∀ {delta : NNReal}, 0 < delta -> delta < delta0 ->
      ∀ {iota : Type uI} [DecidableEq iota] (F : Finset iota) (Y : iota -> ShadedTube delta E)
        (raw : ActualPreparedRawTreeW98 F (fun i => (Y i).toTube) N kappa Ctw),
        (∀ i ∈ F, (Y i).carrier ⊆ Metric.closedBall 0 1) ->
        (0 < ∑ i ∈ F, volume (Y i).shade) ->
        ∃ (A : Finset iota) (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) N Ccan),
          A.Nonempty ∧ A ⊆ F ∧
          towerPreparationRetainedW95 delta Cprepare Kprepare * (∑ i ∈ F, volume (Y i).shade) <=
            ∑ i ∈ A, volume (Y i).shade ∧
          Nonempty (SourceRegularizedWorkingTowerW95 U Ctw Ccell) ∧
          ActualTreeParameterMarginW98 U.cover kappa ∧
          (∀ k, k <= N -> U.cover.assign k = raw.cover.assign k) ∧
          (∀ k, k <= N -> U.cover.tube k = raw.cover.tube k) ∧
          (∀ k, k <= N -> U.cover.indexSet k = A.image (raw.cover.assign k)) := by
  have hfibre_filter {delta : NNReal} {iota : Type uI} [DecidableEq iota]
      (S B : Finset iota) (T : iota -> Tube delta E)
      (G : Tube.GridCoverSystem S T N) (hBS : B ⊆ S)
      (h k : Nat) (hhk : h <= k) (hkM : k <= N) (kept : Finset iota) :
      ∀ R ∈ (B.filter (fun i => G.assign h i ∈ kept)).image (G.assign k),
        completeFibreW94 (B.filter (fun i => G.assign h i ∈ kept)) (G.assign k) R =
          completeFibreW94 B (G.assign k) R := by
    intro R hR
    obtain ⟨i, hi, hiR⟩ := Finset.mem_image.mp hR
    obtain ⟨hiB, hikept⟩ := Finset.mem_filter.mp hi
    ext j
    simp only [completeFibreW94, Finset.mem_filter]
    constructor
    · intro hj
      exact ⟨hj.1.1, hj.2⟩
    · rintro ⟨hjB, hjR⟩
      have heq : G.assign h j = G.assign h i :=
        G.assign_eq_of_le hhk hkM (hBS hjB) (hBS hiB) (hjR.trans hiR.symm)
      exact ⟨⟨hjB, heq ▸ hikept⟩, hjR⟩
  have hmass_finite {delta : NNReal} {iota : Type uI}
      (F : Finset iota) (Y : iota -> ShadedTube delta E) :
      (∑ i ∈ F, volume (Y i).shade) < ⊤ := by
    apply ENNReal.sum_lt_top.mpr
    intro i hi
    exact (measure_mono (Y i).shade_subset).trans_lt (Y i).toTube.isCompact.measure_lt_top
  have hstage {delta : NNReal} {iota : Type uI} [DecidableEq iota]
      (S : Finset iota) (Y : iota -> ShadedTube delta E)
      (G : Tube.GridCoverSystem S (fun i => (Y i).toTube) N)
      (H : ENNReal) (hH : 1 <= H) (hHt : H < ⊤)
      (hrange : ∀ B ⊆ S, ∀ k l, k < l -> l <= N -> ∀ R ∈ B.image (G.assign k),
        1 <= (actualDescendantsW95 B G.assign k l R).card ∧
        ((actualDescendantsW95 B G.assign k l R).card : ENNReal) <= H ∧
        1 <= actualRelativeFrostmanW95 B G.assign G.tube k l R ∧
        actualRelativeFrostmanW95 B G.assign G.tube k l R <= H)
      (B : Finset iota) (hBS : B ⊆ S) (hmass : 0 < ∑ i ∈ B, volume (Y i).shade)
      (k : Nat) (hkM : k < N) :
      ∃ (A : Finset iota) (a b : Nat -> Nat),
        A ⊆ B ∧ (0 < ∑ i ∈ A, volume (Y i).shade) ∧
        (∑ i ∈ B, volume (Y i).shade) <=
          (dyadicRangeLengthW95 H : ENNReal) ^ (2 * N) * ∑ i ∈ A, volume (Y i).shade ∧
        (∀ q, k <= q -> q <= N -> ∀ R ∈ A.image (G.assign q),
          completeFibreW94 A (G.assign q) R = completeFibreW94 B (G.assign q) R) ∧
        (∀ l, k < l -> l <= N -> ∀ R ∈ A.image (G.assign k),
          (2 : ENNReal) ^ a l <= (actualDescendantsW95 A G.assign k l R).card ∧
          ((actualDescendantsW95 A G.assign k l R).card : ENNReal) < 2 ^ (a l + 1) ∧
          (2 : ENNReal) ^ b l <= actualRelativeFrostmanW95 A G.assign G.tube k l R ∧
          actualRelativeFrostmanW95 A G.assign G.tube k l R < 2 ^ (b l + 1)) := by
    let L : ENNReal := dyadicRangeLengthW95 H
    have hLone : 1 <= L := by
      dsimp [L, dyadicRangeLengthW95]
      exact_mod_cast (show 1 <= Nat.floor (Real.log H.toReal / Real.log 2) + 1 by omega)
    have hLzero : L ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hLone)
    have hLtop : L ≠ ⊤ := by simp [L]
    have hsteps : ∀ n, n <= N ->
        ∃ (A : Finset iota) (a b : Nat -> Nat),
          A ⊆ B ∧ (0 < ∑ i ∈ A, volume (Y i).shade) ∧
          (∑ i ∈ B, volume (Y i).shade) <= L ^ (2 * n) * ∑ i ∈ A, volume (Y i).shade ∧
          (∀ q, k <= q -> q <= N -> ∀ R ∈ A.image (G.assign q),
            completeFibreW94 A (G.assign q) R = completeFibreW94 B (G.assign q) R) ∧
          (∀ l, k < l -> l <= n -> ∀ R ∈ A.image (G.assign k),
            (2 : ENNReal) ^ a l <= (actualDescendantsW95 A G.assign k l R).card ∧
            ((actualDescendantsW95 A G.assign k l R).card : ENNReal) < 2 ^ (a l + 1) ∧
            (2 : ENNReal) ^ b l <= actualRelativeFrostmanW95 A G.assign G.tube k l R ∧
            actualRelativeFrostmanW95 A G.assign G.tube k l R < 2 ^ (b l + 1)) := by
      intro n
      induction n with
      | zero =>
          intro hn
          refine ⟨B, fun _ => 0, fun _ => 0, Finset.Subset.refl _, hmass, ?_, ?_, ?_⟩
          · simp
          · intro q hq hqM R hR
            rfl
          · intro l hkl hl
            omega
      | succ n ih =>
          intro hnM
          obtain ⟨A, a, b, hAB, hAmass, hpay, hfibres, hbands⟩ := ih (by omega)
          by_cases hkn : k < n + 1
          · have hAS : A ⊆ S := hAB.trans hBS
            have hr := hrange A hAS k (n + 1) hkn hnM
            obtain ⟨aNew, bNew, A', kept, haNew, hbNew, hkept, hA', hkeptne,
                hA'ne, hA'A, himage, hfibre, hdesc, hCF, hpaid⟩ :=
              exists_actual_count_relative_frostman_band_w95 A Y G.assign G.tube
                k (n + 1) H hH hHt (fun R hR => (hr R hR).1)
                (fun R hR => (hr R hR).2.1) (fun R hR => (hr R hR).2.2.1)
                (fun R hR => (hr R hR).2.2.2) hAmass (hmass_finite A Y)
            have hmassStep : (∑ i ∈ A, volume (Y i).shade) <=
                L ^ 2 * ∑ i ∈ A', volume (Y i).shade :=
              (ENNReal.inv_mul_le_iff (pow_ne_zero _ hLzero) (by finiteness)).mp hpaid
            have hA'pos : 0 < ∑ i ∈ A', volume (Y i).shade := by
              by_contra hnpos
              have hz : (∑ i ∈ A', volume (Y i).shade) = 0 := le_antisymm (not_lt.mp hnpos) bot_le
              rw [hz, mul_zero] at hmassStep
              exact (not_le_of_gt hAmass) hmassStep
            have hkeep : ∀ q, k <= q -> q <= N -> ∀ R ∈ A'.image (G.assign q),
                completeFibreW94 A' (G.assign q) R = completeFibreW94 A (G.assign q) R := by
              intro q hkq hqM R hR
              rw [hA'] at hR ⊢
              exact hfibre_filter S A (fun i => (Y i).toTube) G hAS k q hkq hqM kept R hR
            refine ⟨A', (fun l => if l = n + 1 then aNew else a l),
              (fun l => if l = n + 1 then bNew else b l), hA'A.trans hAB, hA'pos, ?_, ?_, ?_⟩
            · calc
                (∑ i ∈ B, volume (Y i).shade) <= L ^ (2 * n) *
                    (L ^ 2 * ∑ i ∈ A', volume (Y i).shade) :=
                  hpay.trans (mul_le_mul_left' hmassStep _)
                _ = L ^ (2 * (n + 1)) * ∑ i ∈ A', volume (Y i).shade := by
                  rw [← mul_assoc, ← pow_add]
                  congr 2
            · intro q hkq hqM R hR
              exact (hkeep q hkq hqM R hR).trans
                (hfibres q hkq hqM R (Finset.image_subset_image hA'A hR))
            · intro l hkl hl R hR
              have hRA : R ∈ A.image (G.assign k) := Finset.image_subset_image hA'A hR
              have hFibreEq := hkeep k le_rfl hkM.le R hR
              have hDEq : actualDescendantsW95 A' G.assign k l R =
                  actualDescendantsW95 A G.assign k l R := by
                simp only [actualDescendantsW95, hFibreEq]
              have hFEq : actualRelativeFrostmanW95 A' G.assign G.tube k l R =
                  actualRelativeFrostmanW95 A G.assign G.tube k l R := by
                simp only [actualRelativeFrostmanW95, hDEq]
              by_cases hln : l = n + 1
              · subst l
                have hRkept : R ∈ kept := himage ▸ hR
                have hbnd := (Finset.mem_filter.mp (hkept ▸ hRkept)).2
                simpa only [ite_true, hDEq, hFEq] using hbnd
              · have hbnd := hbands l hkl (by omega) R hRA
                simpa only [if_neg hln, hDEq, hFEq] using hbnd
          · refine ⟨A, a, b, hAB, hAmass, ?_, hfibres, ?_⟩
            · exact hpay.trans (mul_le_mul_right'
                (pow_le_pow_right₀ hLone (by omega : 2 * n <= 2 * (n + 1))) _)
            · intro l hkl hl
              exact hbands l hkl (by omega)
    exact hsteps N le_rfl
  have hregularize {delta : NNReal} {iota : Type uI} [DecidableEq iota]
      (S : Finset iota) (Y : iota -> ShadedTube delta E)
      (G : Tube.GridCoverSystem S (fun i => (Y i).toTube) N)
      (H : ENNReal) (hH : 1 <= H) (hHt : H < ⊤)
      (hrange : ∀ B ⊆ S, ∀ k l, k < l -> l <= N -> ∀ R ∈ B.image (G.assign k),
        1 <= (actualDescendantsW95 B G.assign k l R).card ∧
        ((actualDescendantsW95 B G.assign k l R).card : ENNReal) <= H ∧
        1 <= actualRelativeFrostmanW95 B G.assign G.tube k l R ∧
        actualRelativeFrostmanW95 B G.assign G.tube k l R <= H)
      (hmass : 0 < ∑ i ∈ S, volume (Y i).shade) :
      ∃ (A : Finset iota) (a b : Nat -> Nat -> Nat),
        A ⊆ S ∧ (0 < ∑ i ∈ A, volume (Y i).shade) ∧
        (∑ i ∈ S, volume (Y i).shade) <=
          (dyadicRangeLengthW95 H : ENNReal) ^ (2 * N * N) * ∑ i ∈ A, volume (Y i).shade ∧
        (∀ k l, k < l -> l <= N -> ∀ R ∈ A.image (G.assign k),
          (2 : ENNReal) ^ a k l <= (actualDescendantsW95 A G.assign k l R).card ∧
          ((actualDescendantsW95 A G.assign k l R).card : ENNReal) < 2 ^ (a k l + 1) ∧
          (2 : ENNReal) ^ b k l <= actualRelativeFrostmanW95 A G.assign G.tube k l R ∧
          actualRelativeFrostmanW95 A G.assign G.tube k l R < 2 ^ (b k l + 1)) := by
    let L : ENNReal := dyadicRangeLengthW95 H
    have hsteps : ∀ r, r <= N ->
        ∃ (A : Finset iota) (a b : Nat -> Nat -> Nat),
          A ⊆ S ∧ (0 < ∑ i ∈ A, volume (Y i).shade) ∧
          (∑ i ∈ S, volume (Y i).shade) <=
            L ^ (2 * N * r) * ∑ i ∈ A, volume (Y i).shade ∧
          (∀ k l, N - r <= k -> k < l -> l <= N -> ∀ R ∈ A.image (G.assign k),
            (2 : ENNReal) ^ a k l <= (actualDescendantsW95 A G.assign k l R).card ∧
            ((actualDescendantsW95 A G.assign k l R).card : ENNReal) < 2 ^ (a k l + 1) ∧
            (2 : ENNReal) ^ b k l <= actualRelativeFrostmanW95 A G.assign G.tube k l R ∧
            actualRelativeFrostmanW95 A G.assign G.tube k l R < 2 ^ (b k l + 1)) := by
      intro r
      induction r with
      | zero =>
          intro hr
          refine ⟨S, fun _ _ => 0, fun _ _ => 0, Finset.Subset.refl _, hmass, ?_, ?_⟩
          · simp
          · intro k l hk hkl hl
            omega
      | succ r ih =>
          intro hrM
          obtain ⟨A, a, b, hAS, hApos, hpaid, hbands⟩ := ih (by omega)
          let k := N - (r + 1)
          have hkM : k < N := by dsimp [k]; omega
          obtain ⟨A', aNew, bNew, hA'A, hA'pos, hstepPay, hkeep, hnew⟩ :=
            hstage S Y G H hH hHt hrange A hAS hApos k hkM
          refine ⟨A', (fun q l => if q = k then aNew l else a q l),
            (fun q l => if q = k then bNew l else b q l), hA'A.trans hAS, hA'pos, ?_, ?_⟩
          · calc
              (∑ i ∈ S, volume (Y i).shade) <=
                  L ^ (2 * N * r) * (L ^ (2 * N) * ∑ i ∈ A', volume (Y i).shade) :=
                hpaid.trans (mul_le_mul_left' hstepPay _)
              _ = L ^ (2 * N * (r + 1)) * ∑ i ∈ A', volume (Y i).shade := by
                rw [← mul_assoc, ← pow_add]
                congr 2 <;> ring
          · intro q l hq hql hl R hR
            by_cases hqk : q = k
            · subst q
              simpa only [ite_true] using hnew l hql hl R hR
            · have hkq : k <= q := hq
              have hqM : q <= N := by omega
              have hqold : N - r <= q := by dsimp [k] at hqk; omega
              have hRold : R ∈ A.image (G.assign q) := Finset.image_subset_image hA'A hR
              have hFibreEq := hkeep q hkq hqM R hR
              have hDEq : actualDescendantsW95 A' G.assign q l R =
                  actualDescendantsW95 A G.assign q l R := by
                simp only [actualDescendantsW95, hFibreEq]
              have hFEq : actualRelativeFrostmanW95 A' G.assign G.tube q l R =
                  actualRelativeFrostmanW95 A G.assign G.tube q l R := by
                simp only [actualRelativeFrostmanW95, hDEq]
              simpa only [if_neg hqk, hDEq, hFEq] using hbands q l hqold hql hl R hRold
    obtain ⟨A, a, b, hAS, hApos, hpaid, hbands⟩ := hsteps N le_rfl
    exact ⟨A, a, b, hAS, hApos, hpaid, fun k l hkl hl =>
      hbands k l (by omega) hkl hl⟩
  have hfrostman_equal_volume {iota : Type uI} (D : Finset iota)
      (V : iota -> ConvexSpaceBody E) (P : ConvexSpaceBody E) (v : ENNReal)
      (hD : D.Nonempty) (hvol : ∀ i ∈ D, volume (V i).carrier = v)
      (hv0 : v ≠ 0) (hvt : v ≠ ⊤)
      (hP0 : volume P.carrier ≠ 0) (hPt : volume P.carrier ≠ ⊤)
      (hle : ∀ i ∈ D, V i <= P) :
      1 <= frostmanConstIn D V P ∧ frostmanConstIn D V P <= volume P.carrier / v := by
    have hdensity : Kakeya.densityIn D V P = (D.card : ENNReal) * v / volume P.carrier := by
      rw [Kakeya.densityIn_of_all_le hle]
      congr 1
      calc
        (∑ i ∈ D, volume (V i).carrier) = ∑ i ∈ D, v := Finset.sum_congr rfl hvol
        _ = (D.card : ENNReal) * v := by rw [Finset.sum_const, nsmul_eq_mul]
    have hdensity_pos : 0 < Kakeya.densityIn D V P := by
      rw [hdensity]
      exact ENNReal.div_pos (mul_ne_zero (by exact_mod_cast hD.card_ne_zero) hv0) hPt
    refine ⟨(isFrostmanIn_frostmanConstIn D V P).one_le hdensity_pos, ?_⟩
    apply frostmanConstIn_le
    intro Q hQP
    have hcancel : volume P.carrier / v * Kakeya.densityIn D V P = (D.card : ENNReal) := by
      rw [hdensity, div_eq_mul_inv, div_eq_mul_inv]
      calc
        volume P.carrier * v⁻¹ * ((D.card : ENNReal) * v * (volume P.carrier)⁻¹) =
            (D.card : ENNReal) * (v * v⁻¹) * (volume P.carrier * (volume P.carrier)⁻¹) := by ring
        _ = (D.card : ENNReal) := by
          rw [ENNReal.mul_inv_cancel hv0 hvt, ENNReal.mul_inv_cancel hP0 hPt]
          simp
    rw [hcancel]
    exact Kakeya.densityIn_le_card D V Q
  have hinput_card {delta : NNReal} (hdelta : 0 < delta) (hdelta1 : delta <= 1)
      {iota : Type uI} [DecidableEq iota]
      (F : Finset iota) (T : iota -> Tube delta E)
      (hball : ∀ i ∈ F, (T i).carrier ⊆ Metric.closedBall (0 : E) 1)
      (hline : lineEssentiallyDistinctW94 F T Ctw) :
      (F.card : Real) <= (5 : Real) ^ (6 : Nat) * (Ctw : Real) *
        (delta : Real) ^ (-(6 : Real)) := by
    have hd : (0 : Real) < delta := by exact_mod_cast hdelta
    have hd1 : (delta : Real) <= 1 := by exact_mod_cast hdelta1
    obtain ⟨P, hPF, hsep, hcover⟩ := exists_maximal_separated_finset F
      (fun i j => ‖(T i).midpoint - (T j).midpoint‖ + ‖(T i).direction - (T j).direction‖)
      (ε := (delta : Real)) (fun i => by simpa using hd)
      (fun i j => by rw [norm_sub_rev (T i).midpoint, norm_sub_rev (T i).direction])
    let assign : iota -> iota := fun i => if hi : i ∈ F then (hcover i hi).choose else i
    have hass : ∀ i ∈ F, assign i ∈ P ∧
        ‖(T i).midpoint - (T (assign i)).midpoint‖ +
          ‖(T i).direction - (T (assign i)).direction‖ < (delta : Real) := by
      intro i hi
      simpa only [assign, dif_pos hi] using (hcover i hi).choose_spec
    have hcluster : ∀ i ∈ F,
        liesInFiveDeltaLineTubeW94 (T i) (T (assign i)).midpoint (T (assign i)).direction := by
      intro i hi x hx
      obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.mp ((T i).carrier_eq ▸ hx)
      rw [segment_eq_image'] at hz
      obtain ⟨theta, htheta, hthetaZ⟩ := hz
      let t : Real := theta - 1 / 2
      have ht : |t| <= 1 / 2 := by
        rw [abs_le]
        dsimp [t]
        constructor <;> linarith [htheta.1, htheta.2]
      have hzt : z = (T i).midpoint + t • (T i).direction := by
        rw [← hthetaZ]
        dsimp [t, Tube.midpoint, Tube.direction]
        module
      let j := assign i
      have hzclose : dist z ((T j).midpoint + t • (T j).direction) <= (delta : Real) := by
        rw [hzt, dist_eq_norm]
        have heq : (T i).midpoint + t • (T i).direction -
            ((T j).midpoint + t • (T j).direction) =
            ((T i).midpoint - (T j).midpoint) + t • ((T i).direction - (T j).direction) := by module
        rw [heq]
        calc
          _ <= ‖(T i).midpoint - (T j).midpoint‖ +
              |t| * ‖(T i).direction - (T j).direction‖ := by
            simpa only [norm_smul, Real.norm_eq_abs] using norm_add_le
              ((T i).midpoint - (T j).midpoint) (t • ((T i).direction - (T j).direction))
          _ <= (delta : Real) := by
            have hdist := (hass i hi).2
            change ‖(T i).midpoint - (T j).midpoint‖ +
              ‖(T i).direction - (T j).direction‖ < (delta : Real) at hdist
            nlinarith [norm_nonneg ((T i).direction - (T j).direction)]
      refine ⟨t, ?_⟩
      have htri := dist_triangle x z ((T j).midpoint + t • (T j).direction)
      have hxz' := Metric.mem_closedBall.mp hxz
      change dist x ((T j).midpoint + t • (T j).direction) <= 5 * (delta : Real)
      linarith
    have hfibrecard : ∀ j ∈ P, ((F.filter (fun i => assign i = j)).card : Real) <= Ctw := by
      intro j hj
      have hsub : F.filter (fun i => assign i = j) ⊆
          F.filter (fun i => liesInFiveDeltaLineTubeW94 (T i) (T j).midpoint (T j).direction) := by
        intro i hi
        obtain ⟨hiF, hij⟩ := Finset.mem_filter.mp hi
        exact Finset.mem_filter.mpr ⟨hiF, hij ▸ hcluster i hiF⟩
      have hcap := hline (T j).midpoint (T j).direction (T j).norm_direction
      have hcapR : ((F.filter (fun i => liesInFiveDeltaLineTubeW94
          (T i) (T j).midpoint (T j).direction)).card : Real) <= Ctw := by exact_mod_cast hcap
      exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans hcapR
    have hcardFP : (F.card : Real) <= (P.card : Real) * Ctw := by
      calc
        (F.card : Real) = ∑ j ∈ P, ((F.filter (fun i => assign i = j)).card : Real) := by
          simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using
            (Finset.sum_fiberwise_of_maps_to (fun i hi => (hass i hi).1) (fun _ => (1 : Real))).symm
        _ <= ∑ j ∈ P, (Ctw : Real) := Finset.sum_le_sum hfibrecard
        _ = (P.card : Real) * Ctw := by rw [Finset.sum_const, nsmul_eq_mul]
    have hcardP : (P.card : Real) <= ((5 : Real) / delta) ^ (6 : Nat) := by
      have hpack := Tube.card_le_of_L1_separated_in_box P
        (fun i => (T i).midpoint) (fun i => (T i).direction) (0 : E) (0 : E)
        (R := (1 : Real)) hd hsep
        (fun i hi => by simpa using Tube.norm_midpoint_le_of_subset_ball hdelta (T i) (hball i (hPF hi)))
        (fun i hi => by simpa using (T i).norm_direction.le)
      rw [hdim] at hpack
      have hratio : ((1 : Real) + (delta : Real) / 4) / ((delta : Real) / 4) <= 5 / (delta : Real) := by
        apply (div_le_div_iff₀ (by positivity) hd).mpr
        nlinarith
      exact hpack.trans (pow_le_pow_left₀ (by positivity) hratio 6)
    calc
      (F.card : Real) <= ((5 : Real) / delta) ^ (6 : Nat) * Ctw :=
        hcardFP.trans (mul_le_mul_of_nonneg_right hcardP Ctw.coe_nonneg)
      _ = (5 : Real) ^ (6 : Nat) * (Ctw : Real) * (delta : Real) ^ (-(6 : Real)) := by
        rw [div_pow, Real.rpow_neg hd.le]
        norm_num only [Real.rpow_ofNat]
        ring
  have hgrid_nested {delta : NNReal} {iota : Type uI} [DecidableEq iota]
      (S : Finset iota) (Y : iota -> ShadedTube delta E)
      (G : Tube.GridCoverSystem S (fun i => (Y i).toTube) N)
      (k l : Nat) (hkl : k <= l) (hl : l <= N) (i : iota) (hi : i ∈ S) :
      (G.tube l (G.assign l i)).toConvexSpaceBody <=
        (G.tube k (G.assign k i)).toConvexSpaceBody := by
    revert hl
    induction l, hkl using Nat.le_induction with
    | base => exact fun _ => le_rfl
    | succ l hkl ih =>
        intro hl
        exact (G.tube_nested l hl i hi).trans (ih (by omega))
  have hrange_tubes {delta : NNReal} (hdelta : 0 < delta) (hdelta1 : delta <= 1)
      {iota : Type uI} [DecidableEq iota]
      (S : Finset iota) (Y : iota -> ShadedTube delta E)
      (G : Tube.GridCoverSystem S (fun i => (Y i).toTube) N)
      (B : Finset iota) (hBS : B ⊆ S) (k l : Nat) (hkl : k < l) (hl : l <= N)
      (R : iota) (hR : R ∈ B.image (G.assign k)) :
      1 <= (actualDescendantsW95 B G.assign k l R).card ∧
      (actualDescendantsW95 B G.assign k l R).card <= S.card ∧
      1 <= actualRelativeFrostmanW95 B G.assign G.tube k l R ∧
      actualRelativeFrostmanW95 B G.assign G.tube k l R <=
        ((Tube.volume_le.C 3 : ENNReal) / (Tube.le_volume.c 3 : ENNReal)) *
          ((delta : ENNReal) ^ (2 : Nat))⁻¹ := by
    let D := actualDescendantsW95 B G.assign k l R
    obtain ⟨i0, hi0, hi0R⟩ := Finset.mem_image.mp hR
    have hD : D.Nonempty := by
      exact ⟨G.assign l i0, Finset.mem_image.mpr
        ⟨i0, Finset.mem_filter.mpr ⟨hi0, hi0R⟩, rfl⟩⟩
    have hDcard : D.card <= S.card :=
      Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans (Finset.card_le_card hBS))
    have hcontained : ∀ Q ∈ D,
        (G.tube l Q).toConvexSpaceBody <= (G.tube k R).toConvexSpaceBody := by
      intro Q hQ
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQ
      obtain ⟨hiB, hiR⟩ := Finset.mem_filter.mp hi
      have h := hgrid_nested S Y G k l hkl.le hl i (hBS hiB)
      rwa [hiR] at h
    obtain ⟨Q0, hQ0⟩ := hD
    let v := volume (G.tube l Q0).carrier
    have hvol : ∀ Q ∈ D, volume (G.tube l Q).carrier = v := by
      intro Q hQ
      exact Tube.volume_carrier_eq_volume_carrier (G.tube l Q) (G.tube l Q0)
    have hvl := Tube.volume_pos_and_lt_top (Tube.gridScale_pos hdelta N l)
      (Tube.gridScale_le_one hdelta1 N l) (G.tube l Q0)
    have hvk := Tube.volume_pos_and_lt_top (Tube.gridScale_pos hdelta N k)
      (Tube.gridScale_le_one hdelta1 N k) (G.tube k R)
    obtain ⟨hCFone, hCFvol⟩ := hfrostman_equal_volume D
      (fun Q => (G.tube l Q).toConvexSpaceBody) (G.tube k R).toConvexSpaceBody v
      ⟨Q0, hQ0⟩ hvol hvl.1.ne' hvl.2.ne hvk.1.ne' hvk.2.ne hcontained
    refine ⟨Finset.card_pos.mpr ⟨Q0, hQ0⟩, hDcard, hCFone, ?_⟩
    have hparentVolume : volume (G.tube k R).carrier <= (Tube.volume_le.C 3 : ENNReal) := by
      have hvolk := Tube.volume_le (Tube.gridScale_le_one hdelta1 N k) (G.tube k R)
      have hscale : ((Tube.gridScale delta N k : NNReal) : ENNReal) <= 1 := by
        exact_mod_cast Tube.gridScale_le_one hdelta1 N k
      have hpow : (((Tube.gridScale delta N k : NNReal) : ENNReal) ^ (2 : Nat)) <= 1 :=
        pow_le_one₀ bot_le hscale
      have hk : volume (G.tube k R).carrier <= (Tube.volume_le.C 3 : ENNReal) *
          (((Tube.gridScale delta N k : NNReal) : ENNReal) ^ (2 : Nat)) := by
        simpa only [hdim, Nat.reduceSub] using hvolk
      exact hk.trans (by simpa only [mul_one] using mul_le_mul_left' hpow (Tube.volume_le.C 3 : ENNReal))
    have hchildVolume : (Tube.le_volume.c 3 : ENNReal) * ((delta : ENNReal) ^ (2 : Nat)) <= v := by
      have hdeltascale : delta <= Tube.gridScale delta N l := by
        simpa only [Tube.gridScale_self delta (by omega : 0 < N)] using
          Tube.gridScale_antitone hdelta hdelta1 N hl
      have hscaleE : (delta : ENNReal) <= ((Tube.gridScale delta N l : NNReal) : ENNReal) := by
        exact_mod_cast hdeltascale
      have hvolmin := Tube.le_volume (G.tube l Q0)
      have hmin : (Tube.le_volume.c 3 : ENNReal) *
          (((Tube.gridScale delta N l : NNReal) : ENNReal) ^ (2 : Nat)) <= v := by
        simpa only [hdim, Nat.reduceSub] using hvolmin
      exact (mul_le_mul_left' (pow_le_pow_left' hscaleE 2) _).trans hmin
    have hc0 : (Tube.le_volume.c 3 : ENNReal) ≠ 0 :=
      (ENNReal.coe_pos.mpr (Tube.le_volume.c_pos 3)).ne'
    calc
      actualRelativeFrostmanW95 B G.assign G.tube k l R <= volume (G.tube k R).carrier / v := hCFvol
      _ <= (Tube.volume_le.C 3 : ENNReal) /
          ((Tube.le_volume.c 3 : ENNReal) * (delta : ENNReal) ^ (2 : Nat)) :=
        ENNReal.div_le_div hparentVolume hchildVolume
      _ = ((Tube.volume_le.C 3 : ENNReal) / (Tube.le_volume.c 3 : ENNReal)) *
          ((delta : ENNReal) ^ (2 : Nat))⁻¹ := by
        simp only [div_eq_mul_inv, ENNReal.mul_inv (Or.inl hc0) (Or.inl ENNReal.coe_ne_top), mul_assoc]
  let Ccan := Tube.uniformConst 3
  have hCtwo : 2 <= Ccan := le_max_left _ _
  have hCone : 1 <= Ccan := (by norm_num : (1 : NNReal) <= 2).trans hCtwo
  have hbundle {delta : NNReal} (hdelta : 0 < delta) (hdelta1 : delta <= 1)
      {iota : Type uI} [DecidableEq iota]
      (S A : Finset iota) (Y : iota -> ShadedTube delta E)
      (G : Tube.GridCoverSystem S (fun i => (Y i).toTube) N)
      (hAS : A ⊆ S)
      (hsurj : ∀ k, k <= N -> S.image (G.assign k) = G.indexSet k)
      (hbottom : ∀ i ∈ S, G.assign N i = i)
      (htubeBottom : ∀ i ∈ S, (G.tube N i).toConvexSpaceBody = (Y i).toConvexSpaceBody)
      (hinj : ∀ k, k <= N -> Set.InjOn (G.tube k) (G.indexSet k : Set iota))
      (hnice : ∀ k, k <= N -> ∀ V : Tube (Tube.gridScale delta N k) E,
        ((G.indexSet k).filter (fun R => ∃ i ∈ S,
          (Y i).toConvexSpaceBody <= (G.tube k R).toConvexSpaceBody ∧
          (Y i).toConvexSpaceBody <= V.toConvexSpaceBody)).card <= Tube.overlapConstBOTight 3)
      (hball : ∀ k, k <= N -> ∀ R ∈ G.indexSet k, (G.tube k R).carrier ⊆ Metric.closedBall 0 2)
      (hbottomBall : ∀ i ∈ A, (Y i).carrier ⊆ Metric.closedBall 0 1)
      (hlineRaw : ∀ k, k <= N -> lineEssentiallyDistinctW94 (G.indexSet k) (G.tube k) Ctw)
      (a b : Nat -> Nat -> Nat)
      (hbands : ∀ k l, k < l -> l <= N -> ∀ R ∈ A.image (G.assign k),
        (2 : ENNReal) ^ a k l <= (actualDescendantsW95 A G.assign k l R).card ∧
        ((actualDescendantsW95 A G.assign k l R).card : ENNReal) < 2 ^ (a k l + 1) ∧
        (2 : ENNReal) ^ b k l <= actualRelativeFrostmanW95 A G.assign G.tube k l R ∧
        actualRelativeFrostmanW95 A G.assign G.tube k l R < 2 ^ (b k l + 1)) :
      ∃ U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) N Ccan,
        Nonempty (SourceRegularizedWorkingTowerW95 U Ctw (Ccan ^ 3)) ∧
        U.cover.assign = G.assign ∧ U.cover.tube = G.tube ∧
        (∀ k, U.cover.indexSet k = A.image (G.assign k)) := by
    let GA : Tube.GridCoverSystem A (fun i => (Y i).toTube) N := {
      indexSet := fun k => A.image (G.assign k)
      assign := G.assign
      tube := G.tube
      assign_mem := fun k hk i hi => Finset.mem_image.mpr ⟨i, hi, rfl⟩
      le_tube_assign := fun k hk i hi => G.le_tube_assign k hk i (hAS hi)
      nested := fun k hk i hi j hj hij => G.nested k hk i (hAS hi) j (hAS hj) hij
      tube_nested := fun k hk i hi => G.tube_nested k hk i (hAS hi)
    }
    have hmem : ∀ k, k <= N -> GA.indexSet k ⊆ G.indexSet k := by
      intro k hk
      rw [← hsurj k hk]
      exact Finset.image_subset_image hAS
    have hniceA : ∀ k, k <= N -> ∀ V : Tube (Tube.gridScale delta N k) E,
        ((GA.indexSet k).filter (fun R => ∃ i ∈ A,
          (Y i).toConvexSpaceBody <= (GA.tube k R).toConvexSpaceBody ∧
          (Y i).toConvexSpaceBody <= V.toConvexSpaceBody)).card <= Tube.overlapConstBOTight 3 := by
      intro k hk V
      apply (Finset.card_le_card ?_).trans (hnice k hk V)
      intro R hR
      obtain ⟨hR, i, hi, hiR, hiV⟩ := Finset.mem_filter.mp hR
      exact Finset.mem_filter.mpr ⟨hmem k hk hR, i, hAS hi, hiR, hiV⟩
    have hbottomIndex : GA.indexSet N = A := by
      change A.image (G.assign N) = A
      calc
        A.image (G.assign N) = A.image id := Finset.image_congr (fun i hi => hbottom i (hAS hi))
        _ = A := Finset.image_id
    have hfibreCover : ∀ k R, completeFibreW94 A (G.assign k) R = Tube.coverClass A (G.assign k) R := by
      intro k R
      ext i
      simp only [completeFibreW94, Tube.coverClass, Finset.mem_filter]
    have hbottomClass : ∀ R ∈ GA.indexSet N, Tube.coverClass A (GA.assign N) R = {R} := by
      intro R hR
      have hRA : R ∈ A := hbottomIndex ▸ hR
      ext i
      simp only [Tube.coverClass, Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hi, hir⟩
        exact (hbottom i (hAS hi)).symm.trans hir
      · intro hir
        subst i
        exact ⟨hRA, hbottom R (hAS hRA)⟩
    have hdescBottom : ∀ k R,
        actualDescendantsW95 A G.assign k N R = Tube.coverClass A (G.assign k) R := by
      intro k R
      have hclsSub : Tube.coverClass A (G.assign k) R ⊆ A := by
        letI : DecidablePred (fun i => G.assign k i = R) := fun _ => Classical.propDecidable _
        exact Finset.filter_subset _ _
      unfold actualDescendantsW95
      rw [hfibreCover]
      calc
        (Tube.coverClass A (G.assign k) R).image (G.assign N) =
            (Tube.coverClass A (G.assign k) R).image id := by
          apply Finset.image_congr
          intro i hi
          exact hbottom i (hAS (hclsSub hi))
        _ = _ := Finset.image_id
    let U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) N Ccan := {
      cover := GA
      branchingN := fun k => if k < N then (2 : NNReal) ^ a k N else 1
      tube_injOn := fun k hk => (hinj k hk).mono (hmem k hk)
      boundedOverlap := by
        intro k hk V
        have hb : (((GA.indexSet k).filter (fun R => ∃ i ∈ A,
            (Y i).toConvexSpaceBody <= (GA.tube k R).toConvexSpaceBody ∧
            (Y i).toConvexSpaceBody <= V.toConvexSpaceBody)).card : NNReal) <=
            (Tube.overlapConstBOTight 3 : NNReal) := by exact_mod_cast hniceA k hk V
        exact hb.trans (le_max_right _ _)
      card_class_le := by
        intro k hk R hR
        by_cases hkM : k < N
        · have hb := (hbands k N hkM le_rfl R hR).2.1
          rw [hdescBottom] at hb
          have hb' : ((Tube.coverClass A (G.assign k) R).card : NNReal) <
              2 * (2 : NNReal) ^ a k N := by
            exact_mod_cast (show ((Tube.coverClass A (G.assign k) R).card : ENNReal) <
              2 * (2 : ENNReal) ^ a k N by simpa only [pow_succ, mul_comm] using hb)
          simpa only [if_pos hkM] using hb'.le.trans (mul_le_mul_right' hCtwo _)
        · have hkeq : k = N := by omega
          subst k
          simp only [hbottomClass R hR, Finset.card_singleton, Nat.cast_one, lt_self_iff_false,
            if_false, mul_one]
          exact hCone
      le_card_class := by
        intro k hk R hR
        by_cases hkM : k < N
        · have hb := (hbands k N hkM le_rfl R hR).1
          rw [hdescBottom] at hb
          have hb' : (2 : NNReal) ^ a k N <= (Tube.coverClass A (G.assign k) R).card := by
            exact_mod_cast hb
          simpa only [if_pos hkM, one_mul] using
            hb'.trans (show ((Tube.coverClass A (G.assign k) R).card : NNReal) <=
              Ccan * ((Tube.coverClass A (G.assign k) R).card : NNReal) by
                simpa only [one_mul] using mul_le_mul_right' hCone ((Tube.coverClass A (G.assign k) R).card : NNReal))
        · have hkeq : k = N := by omega
          subst k
          simp only [hbottomClass R hR, Finset.card_singleton, Nat.cast_one, lt_self_iff_false,
            if_false, mul_one]
          exact hCone
    }
    have hparentLine : ∀ k, k <= N ->
        lineEssentiallyDistinctW94 (U.cover.indexSet k) (U.cover.tube k) Ctw := by
      intro k hk o v hv
      apply le_trans ?_ (hlineRaw k hk o v hv)
      exact_mod_cast Finset.card_le_card
        (Finset.filter_subset_filter _ (hmem k hk))
    refine ⟨U, ?_, rfl, rfl, fun k => rfl⟩
    refine ⟨{
      surjective := fun k hk => rfl
      bottom_index := hbottomIndex
      bottom_assign := fun i hi => hbottom i (hAS hi)
      bottom_tube := fun i hi => htubeBottom i (hAS hi)
      nice := by simpa only [Tube.UniformTubeSet.Nice, hdim] using hniceA
      parent_ball := fun k hk R hR => hball k hk R (hmem k hk hR)
      parent_line_ed := hparentLine
      geometric_count := by
        intro k hk R hR
        calc
          ((exactTubeCellW87 A (fun i => (Y i).toTube) (U.cover.tube k R)).card : NNReal) <=
              Ccan ^ 2 * U.branchingN k := U.card_familyIn_le hk R
          _ <= Ccan ^ 2 * (Ccan * ((Tube.coverClass A (U.cover.assign k) R).card : NNReal)) :=
            mul_le_mul_left' (U.le_card_class k hk R hR) _
          _ = Ccan ^ 3 * ((completeFibreW94 A (U.cover.assign k) R).card : NNReal) := by
            change Ccan ^ 2 * (Ccan * ((Tube.coverClass A (G.assign k) R).card : NNReal)) =
              Ccan ^ 3 * ((completeFibreW94 A (G.assign k) R).card : NNReal)
            rw [hfibreCover]
            ring
      countBand := fun k l => (2 : NNReal) ^ a k l
      countBand_pos := fun k l hkl hl => pow_pos (by norm_num) _
      count_lower := by
        intro k l hkl hl R hR
        exact_mod_cast (hbands k l hkl hl R hR).1
      count_upper := by
        intro k l hkl hl R hR
        have h := (hbands k l hkl hl R hR).2.1
        exact_mod_cast (show ((actualDescendantsW95 A G.assign k l R).card : ENNReal) <
          2 * (2 : ENNReal) ^ a k l by simpa only [pow_succ, mul_comm] using h)
      frostmanBand := fun k l => (2 : ENNReal) ^ b k l
      frostmanBand_pos := fun k l hkl hl => by positivity
      frostmanBand_finite := fun k l hkl hl => by finiteness
      frostman_lower := fun k l hkl hl R hR => (hbands k l hkl hl R hR).2.2.1
      frostman_upper := by
        intro k l hkl hl R hR
        simpa only [pow_succ, mul_comm] using (hbands k l hkl hl R hR).2.2.2
    }⟩
  let N0 : NNReal := 5 ^ (6 : Nat) * Ctw
  let Hc : NNReal := Tube.volume_le.C 3 / Tube.le_volume.c 3
  let Ccut : NNReal := max 1 (max N0 Hc)
  let Q : Nat := 2 * N * N
  let Ctower : NNReal := 7 ^ Q
  let delta0 : NNReal := min (1 / 2) Ccut⁻¹
  have hcut1 : 1 <= Ccut := le_max_left _ _
  have hcutpos : 0 < Ccut := zero_lt_one.trans_le hcut1
  have hdelta0pos : 0 < delta0 := lt_min (by norm_num) (inv_pos.mpr hcutpos)
  have hdelta0half : delta0 <= 1 / 2 := min_le_left _ _
  have hdelta01 : delta0 < 1 := hdelta0half.trans_lt (by norm_num)
  refine ⟨Ccan, Ccan ^ 3, Ctower, Q, delta0, hCone,
    one_le_pow₀ hCone, one_le_pow₀ (by norm_num), by dsimp [Q]; nlinarith,
    hdelta0pos, hdelta01, ?_⟩
  intro delta hdelta hsmall iota inst F Y raw hball hmass
  have hd0 : 0 < (delta : Real) := hdelta
  have hd1 : delta < 1 := hsmall.trans hdelta01
  have hd1r : (delta : Real) <= 1 := hd1.le
  have hdcut : delta <= Ccut⁻¹ := hsmall.le.trans (min_le_right _ _)
  have hline : lineEssentiallyDistinctW94 F (fun i => (Y i).toTube) Ctw := by
    intro o v hv
    have h := raw.parent_line_ed N le_rfl o v hv
    have hfilter : (raw.cover.indexSet N).filter
        (fun R => liesInFiveDeltaLineTubeW94 (raw.cover.tube N R) o v) =
        F.filter (fun R => liesInFiveDeltaLineTubeW94 (Y R).toTube o v) := by
      rw [raw.bottom_index]
      apply Finset.filter_congr
      intro R hR
      unfold liesInFiveDeltaLineTubeW94
      have hb := congrArg ConvexSpaceBody.carrier (raw.bottom_tube R hR)
      change (raw.cover.tube N R).carrier = (Y R).carrier at hb
      rw [hb, Tube.gridScale_self delta (by omega : 0 < N)]
    rwa [hfilter] at h
  have hcoeff : (Ccut : Real) <= (delta : Real)⁻¹ := by
    have hc0 : 0 < (Ccut : Real) := hcutpos
    have hd : (delta : Real) <= 1 / (Ccut : Real) := by
      simpa only [one_div] using (show (delta : Real) <= (Ccut : Real)⁻¹ by exact_mod_cast hdcut)
    have hprod := (le_div_iff₀ hc0).mp hd
    rw [← one_div, le_div_iff₀ hd0]
    nlinarith
  have hN0 : (N0 : Real) <= (delta : Real) ^ (-(1 : Real)) := by
    have hN : N0 <= Ccut := (le_max_left _ _).trans (le_max_right _ _)
    simpa only [Real.rpow_neg_one] using (show (N0 : Real) <= (delta : Real)⁻¹ from
      (show (N0 : Real) <= Ccut by exact_mod_cast hN).trans hcoeff)
  have hHc : (Hc : Real) <= (delta : Real) ^ (-(1 : Real)) := by
    have hH : Hc <= Ccut := (le_max_right _ _).trans (le_max_right _ _)
    simpa only [Real.rpow_neg_one] using (show (Hc : Real) <= (delta : Real)⁻¹ from
      (show (Hc : Real) <= Ccut by exact_mod_cast hH).trans hcoeff)
  have hcard7 : (F.card : Real) <= (delta : Real) ^ (-(7 : Real)) := by
    calc
      (F.card : Real) <= (N0 : Real) * (delta : Real) ^ (-(6 : Real)) :=
        hinput_card hdelta hd1.le F (fun i => (Y i).toTube) hball hline
      _ <= (delta : Real) ^ (-(1 : Real)) * (delta : Real) ^ (-(6 : Real)) :=
        mul_le_mul_of_nonneg_right hN0 (Real.rpow_nonneg delta.2 _)
      _ = (delta : Real) ^ (-(7 : Real)) := by rw [← Real.rpow_add hd0]; norm_num
  have hCFreal : (Hc : Real) * ((delta : Real) ^ (2 : Nat))⁻¹ <=
      (delta : Real) ^ (-(7 : Real)) := by
    calc
      (Hc : Real) * ((delta : Real) ^ (2 : Nat))⁻¹ =
          (Hc : Real) * (delta : Real) ^ (-(2 : Real)) := by
        exact congrArg (fun x : Real => (Hc : Real) * x)
          (by simpa only [Real.rpow_two] using (Real.rpow_neg hd0.le 2).symm)
      _ <= (delta : Real) ^ (-(1 : Real)) * (delta : Real) ^ (-(2 : Real)) :=
        mul_le_mul_of_nonneg_right hHc (Real.rpow_nonneg delta.2 _)
      _ = (delta : Real) ^ (-(3 : Real)) := by rw [← Real.rpow_add hd0]; norm_num
      _ <= (delta : Real) ^ (-(7 : Real)) :=
        Real.rpow_le_rpow_of_exponent_ge hd0 hd1r (by norm_num)
  let H : ENNReal := ENNReal.ofReal ((delta : Real) ^ (-(7 : Real)))
  have hHreal : 1 <= (delta : Real) ^ (-(7 : Real)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hd0 hd1r (by norm_num)
  have hHone : 1 <= H := by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hHreal
  have hHt : H < ⊤ := ENNReal.ofReal_lt_top
  have hcardH : (F.card : ENNReal) <= H := by
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hcard7
  have hc0 : Tube.le_volume.c 3 ≠ 0 := (Tube.le_volume.c_pos 3).ne'
  have hdE0 : (delta : ENNReal) ≠ 0 := (ENNReal.coe_pos.mpr hdelta).ne'
  have hCFH : ((Tube.volume_le.C 3 : ENNReal) / (Tube.le_volume.c 3 : ENNReal)) *
      ((delta : ENNReal) ^ (2 : Nat))⁻¹ <= H := by
    rw [← ENNReal.coe_div hc0]
    change (Hc : ENNReal) * ((delta : ENNReal) ^ (2 : Nat))⁻¹ <= H
    apply (ENNReal.toReal_le_toReal (by simp [ENNReal.mul_ne_top, hdE0]) hHt.ne).mp
    simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_inv,
      ENNReal.toReal_pow, H, ENNReal.toReal_ofReal (zero_le_one.trans hHreal)] using hCFreal
  let G := raw.cover
  have hrange : ∀ B ⊆ F, ∀ k l, k < l -> l <= N -> ∀ R ∈ B.image (G.assign k),
      1 <= (actualDescendantsW95 B G.assign k l R).card ∧
      ((actualDescendantsW95 B G.assign k l R).card : ENNReal) <= H ∧
      1 <= actualRelativeFrostmanW95 B G.assign G.tube k l R ∧
      actualRelativeFrostmanW95 B G.assign G.tube k l R <= H := by
    intro B hBF k l hkl hl R hR
    obtain ⟨hcount1, hcountF, hCF1, hCFmax⟩ :=
      hrange_tubes hdelta hd1.le F Y G B hBF k l hkl hl R hR
    refine ⟨hcount1, ?_, hCF1, hCFmax.trans hCFH⟩
    exact (show ((actualDescendantsW95 B G.assign k l R).card : ENNReal) <= F.card by
      exact_mod_cast hcountF).trans hcardH
  obtain ⟨A, a, b, hAF, hAmass, hpayA, hbands⟩ :=
    hregularize F Y G H hHone hHt hrange hmass
  obtain ⟨U, hU, hassign, htube, hindex⟩ :=
    hbundle hdelta hd1.le F A Y G hAF raw.surjective raw.bottom_assign raw.bottom_tube
      raw.tube_injective (by simpa only [hdim] using raw.tight_overlap)
      raw.parent_ball (fun i hi => hball i (hAF hi)) raw.parent_line_ed a b hbands
  have hAnonempty : A.Nonempty := by
    by_contra h
    simpa only [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty,
      lt_self_iff_false] using hAmass
  have hmargin : ActualTreeParameterMarginW98 U.cover kappa := {
    midpoint := by
      intro k l hkl hl i hi
      rw [hassign, htube]
      exact raw.margin.midpoint k l hkl hl i (hAF hi)
    direction := by
      intro k l hkl hl i hi
      rw [hassign, htube]
      exact raw.margin.direction k l hkl hl i (hAF hi)
  }
  refine ⟨A, U, hAnonempty, hAF, ?_, hU, hmargin,
    fun k hk => congrFun hassign k, fun k hk => congrFun htube k,
    fun k hk => hindex k⟩
  let t : Real := Real.log (1 / (delta : Real)) / Real.log 2
  let L : Real := 2 + t
  have ht0 : 0 <= t := by
    apply div_nonneg (Real.log_nonneg ?_) (Real.log_nonneg (by norm_num))
    exact (le_div_iff₀ hd0).mpr (by simpa only [one_mul] using hd1r)
  have hLpos : 0 < L := by dsimp [L]; linarith
  have hlogH : Real.log H.toReal / Real.log 2 = 7 * t := by
    rw [show H.toReal = (delta : Real) ^ (-(7 : Real)) from ENNReal.toReal_ofReal (zero_le_one.trans hHreal),
      Real.log_rpow hd0]
    dsimp [t]
    rw [Real.log_div one_ne_zero hd0.ne', Real.log_one]
    ring
  have hlenReal : (dyadicRangeLengthW95 H : Real) <= 7 * L := by
    have hfloor := Nat.floor_le (show 0 <= Real.log H.toReal / Real.log 2 by rw [hlogH]; positivity)
    dsimp only [dyadicRangeLengthW95]
    push_cast
    rw [hlogH] at hfloor
    rw [hlogH]
    dsimp [L]
    linarith
  have hlen : (dyadicRangeLengthW95 H : ENNReal) <= 7 * ENNReal.ofReal L := by
    have h := ENNReal.ofReal_le_ofReal hlenReal
    simpa only [ENNReal.ofReal_natCast, ENNReal.ofReal_mul (by norm_num : (0 : Real) <= 7),
      ENNReal.ofReal_ofNat] using h
  have hcoeffpay : (dyadicRangeLengthW95 H : ENNReal) ^ Q <=
      (Ctower : ENNReal) * ENNReal.ofReal (L ^ Q) := by
    calc
      (dyadicRangeLengthW95 H : ENNReal) ^ Q <= (7 * ENNReal.ofReal L) ^ Q :=
        pow_le_pow_left' hlen Q
      _ = (Ctower : ENNReal) * ENNReal.ofReal (L ^ Q) := by
        rw [mul_pow, ENNReal.ofReal_pow hLpos.le]
        simp only [Ctower, ENNReal.coe_pow, ENNReal.coe_ofNat]
  have hpaid : (∑ i ∈ F, volume (Y i).shade) <=
      ((Ctower : ENNReal) * ENNReal.ofReal (L ^ Q)) * ∑ i ∈ A, volume (Y i).shade :=
    hpayA.trans (mul_le_mul_right' hcoeffpay _)
  have hCtower0 : (Ctower : ENNReal) ≠ 0 := by
    exact (ENNReal.coe_pos.mpr (pow_pos (by norm_num : (0 : NNReal) < 7) Q)).ne'
  have hdenom0 : (Ctower : ENNReal) * ENNReal.ofReal (L ^ Q) ≠ 0 :=
    mul_ne_zero hCtower0 (ENNReal.ofReal_pos.mpr (pow_pos hLpos _)).ne'
  exact (ENNReal.inv_mul_le_iff hdenom0 (by finiteness)).mpr hpaid

/-- Source caller bridge: construct the prepared M*M tree and stop only
after its all-pair bands on the same final A. Outer source inputs unchanged. -/
theorem exists_prepared_extended_regularized_stopping_w98
    (hdim : Module.finrank Real E = 3)
    {p : Params} {beta gammaZero xiMin : Real} {xi : Fin (p.N + 1) -> Real}
    {M : Nat} (hp : SourcePassNumericsW95 p beta gammaZero xi xiMin M)
    (kappa : NNReal) (hkappa : 0 < kappa) (hkappaSmall : kappa <= 1 / 100)
    (Cbase : NNReal) (hCbase : 1 <= Cbase) :
    ∃ (Ccan Ctw Ccell BF Cprep : NNReal) (Kprep : Nat) (ePrep : Real) (delta0 : NNReal),
      1 <= Ccan ∧ 1 <= Ctw ∧ 1 <= Ccell ∧ 1 <= BF ∧ 1 <= Cprep ∧ 1 <= Kprep ∧
      0 < ePrep ∧ ePrep < p.η 0 / 100 ∧ 0 < delta0 ∧ delta0 < 1 ∧
      ∀ {delta : NNReal}, 0 < delta -> delta < delta0 ->
      ∀ {iota : Type uI} [DecidableEq iota] (F : Finset iota) (Y : iota -> ShadedTube delta E),
        F.Nonempty -> (∀ i ∈ F, (Y i).carrier ⊆ Metric.closedBall 0 1) ->
        (∀ i ∈ F, centredTubeW94 (Y i).toTube) ->
        lineEssentiallyDistinctW94 F (fun i => (Y i).toTube) Cbase ->
        (delta : ENNReal) ^ ePrep <= fullness' F (fun i => (Y i).toShadedBody) ->
        frostmanConstIn F (fun i => (Y i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall <=
          (delta : ENNReal) ^ (-ePrep) ->
        ∃ (A : Finset iota)
          (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan)
          (Uext : CanonicalProfileNetW87 A (fun i => (Y i).toTube) (M * M) Ccan),
          A.Nonempty ∧ A ⊆ F ∧
          towerPreparationRetainedW95 delta Cprep Kprep * (∑ i ∈ F, volume (Y i).shade) <=
            ∑ i ∈ A, volume (Y i).shade ∧
          Nonempty (SourceRegularizedWorkingTowerW95 U Ctw Ccell) ∧
          Nonempty (SourceRegularizedWorkingTowerW95 Uext Ctw Ccell) ∧
          VisibleExtendedRestrictionW97 U Uext ∧ ActualTreeParameterMarginW98 Uext.cover kappa ∧
          (actualEveryScaleW95 U p.ε p.N BF ∨ Nonempty (ActualSourceDividingBlockW95 U p BF)) := by
  have hgrid (delta : NNReal) (k : Nat) :
      Tube.gridScale delta (M * M) (k * M) = Tube.gridScale delta M k := by
    unfold Tube.gridScale
    congr 1
    push_cast
    have hM0 : (M : Real) ≠ 0 := by exact_mod_cast (show M ≠ 0 by have := hp.M_pos; omega)
    field_simp
  have hcastBody {r s : NNReal} (h : r = s) (T : Tube r E) :
      (h ▸ T : Tube s E).toConvexSpaceBody = T.toConvexSpaceBody := by
    cases h
    rfl
  have hcastHEq {r s : NNReal} (h : r = s) (T : Tube r E) :
      HEq (h ▸ T : Tube s E) T := by
    cases h
    rfl
  have hcastInj {r s : NNReal} (h : r = s) (T V : Tube r E) :
      (h ▸ T : Tube s E) = (h ▸ V : Tube s E) -> T = V := by
    cases h
    exact id
  have hrestrict {delta : NNReal} {iota : Type uI} [DecidableEq iota]
      (A : Finset iota) (Y : iota -> ShadedTube delta E) (Ccan Ctw Ccell : NNReal)
      (Uext : CanonicalProfileNetW87 A (fun i => (Y i).toTube) (M * M) Ccan)
      (hext : SourceRegularizedWorkingTowerW95 Uext Ctw Ccell) :
      ∃ U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan,
        Nonempty (SourceRegularizedWorkingTowerW95 U Ctw Ccell) ∧
        (∀ k, k <= M -> U.cover.indexSet k = Uext.cover.indexSet (k * M)) ∧
        (∀ k, k <= M -> U.cover.assign k = Uext.cover.assign (k * M)) ∧
        (∀ k, k <= M -> Tube.gridScale delta M k = Tube.gridScale delta (M * M) (k * M)) ∧
        (∀ k, k <= M -> ∀ R, HEq (U.cover.tube k R) (Uext.cover.tube (k * M) R)) := by
    have hm (k : Nat) (hk : k <= M) : k * M <= M * M := Nat.mul_le_mul_right M hk
    have hlt (k l : Nat) (hkl : k < l) : k * M < l * M :=
      Nat.mul_lt_mul_of_pos_right hkl (by have := hp.M_pos; omega)
    let tubes (k : Nat) (R : iota) : Tube (Tube.gridScale delta M k) E :=
      hgrid delta k ▸ Uext.cover.tube (k * M) R
    have htube (k : Nat) (R : iota) :
        (tubes k R).toConvexSpaceBody = (Uext.cover.tube (k * M) R).toConvexSpaceBody :=
      hcastBody (hgrid delta k) _
    have hcarrier (k : Nat) (R : iota) :
        (tubes k R).carrier = (Uext.cover.tube (k * M) R).carrier :=
      congrArg (fun V : ConvexSpaceBody E => V.carrier) (htube k R)
    let G : Tube.GridCoverSystem A (fun i => (Y i).toTube) M := {
      indexSet := fun k => Uext.cover.indexSet (k * M)
      assign := fun k => Uext.cover.assign (k * M)
      tube := tubes
      assign_mem := fun k hk i hi => Uext.cover.assign_mem (k * M) (hm k hk) i hi
      le_tube_assign := by
        intro k hk i hi
        rw [htube]
        exact Uext.cover.le_tube_assign (k * M) (hm k hk) i hi
      nested := by
        intro k hk i hi j hj hij
        exact Uext.cover.assign_eq_of_le (Nat.mul_le_mul_right M (Nat.le_succ k))
          (hm (k + 1) hk) hi hj hij
      tube_nested := by
        intro k hk i hi
        rw [htube, htube]
        exact Uext.cover.toChain.tube_assign_le (Nat.mul_le_mul_right M (Nat.le_succ k))
          (hm (k + 1) hk) hi }
    let U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan := {
      cover := G
      branchingN := fun k => Uext.branchingN (k * M)
      tube_injOn := by
        intro k hk R hR S hS hRS
        apply Uext.tube_injOn (k * M) (hm k hk) hR hS
        exact hcastInj (hgrid delta k) _ _ hRS
      boundedOverlap := by
        intro k hk V
        let Vext : Tube (Tube.gridScale delta (M * M) (k * M)) E := (hgrid delta k).symm ▸ V
        have hV : Vext.toConvexSpaceBody = V.toConvexSpaceBody := hcastBody (hgrid delta k).symm V
        have h := Uext.boundedOverlap (k * M) (hm k hk) Vext
        change (((Uext.cover.indexSet (k * M)).filter (fun R => ∃ i ∈ A,
          (Y i).toConvexSpaceBody <= (tubes k R).toConvexSpaceBody ∧
          (Y i).toConvexSpaceBody <= V.toConvexSpaceBody)).card : NNReal) <= Ccan
        simpa only [htube, hV] using h
      card_class_le := fun k hk R hR => Uext.card_class_le (k * M) (hm k hk) R hR
      le_card_class := fun k hk R hR => Uext.le_card_class (k * M) (hm k hk) R hR }
    have hrel (k l : Nat) (R : iota) :
        actualRelativeFrostmanW95 A U.cover.assign U.cover.tube k l R =
          actualRelativeFrostmanW95 A Uext.cover.assign Uext.cover.tube (k * M) (l * M) R := by
      simp only [actualRelativeFrostmanW95, actualDescendantsW95, U, G, htube]
    have hreg : SourceRegularizedWorkingTowerW95 U Ctw Ccell := {
      surjective := fun k hk => hext.surjective (k * M) (hm k hk)
      bottom_index := hext.bottom_index
      bottom_assign := hext.bottom_assign
      bottom_tube := by
        intro i hi
        change (tubes M i).toConvexSpaceBody = (Y i).toConvexSpaceBody
        rw [htube]
        exact hext.bottom_tube i hi
      nice := by
        intro k hk V
        let Vext : Tube (Tube.gridScale delta (M * M) (k * M)) E := (hgrid delta k).symm ▸ V
        have hV : Vext.toConvexSpaceBody = V.toConvexSpaceBody := hcastBody (hgrid delta k).symm V
        have h := hext.nice (k * M) (hm k hk) Vext
        change ((Uext.cover.indexSet (k * M)).filter (fun R => ∃ i ∈ A,
          (Y i).toConvexSpaceBody <= (tubes k R).toConvexSpaceBody ∧
          (Y i).toConvexSpaceBody <= V.toConvexSpaceBody)).card <= _
        simpa only [htube, hV] using h
      parent_ball := by
        intro k hk R hR
        change (tubes k R).carrier ⊆ Metric.closedBall 0 2
        rw [hcarrier]
        exact hext.parent_ball (k * M) (hm k hk) R hR
      parent_line_ed := by
        intro k hk
        have h := hext.parent_line_ed (k * M) (hm k hk)
        simpa only [lineEssentiallyDistinctW94, liesInFiveDeltaLineTubeW94, U, G, hcarrier, hgrid] using h
      geometric_count := by
        intro k hk R hR
        have h := hext.geometric_count (k * M) (hm k hk) R hR
        simpa only [exactTubeCellW87, U, G, htube] using h
      countBand := fun k l => hext.countBand (k * M) (l * M)
      countBand_pos := fun k l hkl hl => hext.countBand_pos _ _ (hlt k l hkl) (hm l hl)
      count_lower := fun k l hkl hl R hR => hext.count_lower _ _ (hlt k l hkl) (hm l hl) R hR
      count_upper := fun k l hkl hl R hR => hext.count_upper _ _ (hlt k l hkl) (hm l hl) R hR
      frostmanBand := fun k l => hext.frostmanBand (k * M) (l * M)
      frostmanBand_pos := fun k l hkl hl => hext.frostmanBand_pos _ _ (hlt k l hkl) (hm l hl)
      frostmanBand_finite := fun k l hkl hl => hext.frostmanBand_finite _ _ (hlt k l hkl) (hm l hl)
      frostman_lower := by
        intro k l hkl hl R hR
        rw [hrel]
        exact hext.frostman_lower _ _ (hlt k l hkl) (hm l hl) R hR
      frostman_upper := by
        intro k l hkl hl R hR
        rw [hrel]
        exact hext.frostman_upper _ _ (hlt k l hkl) (hm l hl) R hR }
    exact ⟨U, ⟨hreg⟩, fun _ _ => rfl, fun _ _ => rfl, fun k _ => (hgrid delta k).symm,
      fun k _ R => hcastHEq (hgrid delta k) _⟩
  have hMM : 1 <= M * M := by
    have hM := hp.M_pos
    nlinarith
  obtain ⟨Ctw, Craw, deltaRaw, hCtw, hCraw, hdeltaRaw, hdeltaRaw1, hraw⟩ :=
    exists_actual_parameter_margin_raw_tree_w98.{uE,uI} hdim (M * M) hMM
      kappa Cbase hkappa hkappaSmall hCbase
  obtain ⟨Ccan, Ccell, Creg, Kprep, deltaReg, hCcan, hCcell, hCreg, hKprep,
      hdeltaReg, hdeltaReg1, hregularize⟩ :=
    exists_actual_regularization_of_prepared_raw_tree_w98.{uE,uI} hdim (M * M) hMM
      kappa Ctw hkappa hkappaSmall hCtw
  let Cprep : NNReal := Craw * Creg
  have hCprep : 1 <= Cprep := one_le_mul hCraw hCreg
  let deltaPrep : NNReal := min deltaRaw deltaReg
  have hdeltaPrep : 0 < deltaPrep := lt_min hdeltaRaw hdeltaReg
  have hdeltaPrep1 : deltaPrep < 1 := (min_le_left _ _).trans_lt hdeltaRaw1
  have htower {delta : NNReal} (hd : 0 < delta) (hdPrep : delta < deltaPrep)
      {iota : Type uI} [DecidableEq iota] (F : Finset iota) (Y : iota -> ShadedTube delta E)
      (hball : ∀ i ∈ F, (Y i).carrier ⊆ Metric.closedBall 0 1)
      (hcen : ∀ i ∈ F, centredTubeW94 (Y i).toTube)
      (hline : lineEssentiallyDistinctW94 F (fun i => (Y i).toTube) Cbase)
      (hmass : 0 < ∑ i ∈ F, volume (Y i).shade) :
      ∃ (A : Finset iota)
        (Uext : CanonicalProfileNetW87 A (fun i => (Y i).toTube) (M * M) Ccan),
        A.Nonempty ∧ A ⊆ F ∧
        towerPreparationRetainedW95 delta Cprep Kprep * (∑ i ∈ F, volume (Y i).shade) <=
          ∑ i ∈ A, volume (Y i).shade ∧
        Nonempty (SourceRegularizedWorkingTowerW95 Uext Ctw Ccell) ∧
        ActualTreeParameterMarginW98 Uext.cover kappa := by
    obtain ⟨I, hI, hIF, hpaidI, ⟨raw⟩⟩ :=
      hraw hd (hdPrep.trans_le (min_le_left _ _)) F Y hball hcen hline hmass
    have hIpos : 0 < ∑ i ∈ I, volume (Y i).shade :=
      (ENNReal.mul_pos (ENNReal.inv_ne_zero.mpr ENNReal.coe_ne_top) hmass.ne').trans_le hpaidI
    obtain ⟨A, Uext, hA, hAI, hpaidA, hreg, hmargin, _, _, _⟩ :=
      hregularize hd (hdPrep.trans_le (min_le_right _ _)) I Y raw
        (fun i hi => hball i (hIF hi)) hIpos
    refine ⟨A, Uext, hA, hAI.trans hIF, ?_, hreg, hmargin⟩
    have hraw0 : (Craw : ENNReal) ≠ 0 :=
      (ENNReal.coe_pos.mpr (zero_lt_one.trans_le hCraw)).ne'
    have hfactor : towerPreparationRetainedW95 delta Cprep Kprep =
        towerPreparationRetainedW95 delta Creg Kprep * (Craw : ENNReal)⁻¹ := by
      unfold towerPreparationRetainedW95 Cprep
      rw [ENNReal.coe_mul, mul_assoc, ENNReal.mul_inv (Or.inl hraw0) (Or.inl ENNReal.coe_ne_top)]
      exact mul_comm _ _
    rw [hfactor, mul_assoc]
    exact (mul_le_mul_left' hpaidI _).trans hpaidA
  obtain ⟨Ctwo, hCtwo, htwo⟩ := actual_relative_cf_composition_w97.{uE,uI} (E := E)
  obtain ⟨Cvol, hCvol, hcrude⟩ := actual_relative_cf_crude_and_prefix_w97.{uE,uI} hdim
  obtain ⟨Croot, hCroot, hroot⟩ := actual_top_relative_cf_w97.{uE,uI} hdim
  let BF : NNReal := max Cvol (2 * Ctwo ^ 2)
  have hBF : 1 <= BF := hCvol.trans (le_max_left _ _)
  let ePrep : Real := p.η 0 / 200
  have hePrep : 0 < ePrep := div_pos (hp.zeta_pos 0 (Nat.zero_le _)) (by norm_num)
  have hePrepSmall : ePrep < p.η 0 / 100 := by
    dsimp [ePrep]
    linarith [hp.zeta_pos 0 (Nat.zero_le _)]
  have hprepCost : Filter.Eventually (fun delta : NNReal => (delta : ENNReal) ^ ePrep <=
      towerPreparationRetainedW95 delta Cprep Kprep) (nhdsWithin 0 (Set.Ioi 0)) := by
    filter_upwards [ENNReal.eventually_ofReal_one_add_logb_pow_le_rpow_neg (half_pos hePrep) Kprep,
      eventually_finite_const_le_rpow_neg (c := (Cprep : ENNReal) * 2 ^ Kprep)
        (by finiteness) (half_pos hePrep),
      eventually_le_nhdsGT (c := (1 : NNReal)) one_pos,
      self_mem_nhdsWithin] with delta hpoly hconst hd1 hd0
    have hdpos : 0 < delta := hd0
    have hdR : (0 : Real) < delta := hdpos
    let t : Real := Real.logb 2 (1 / (delta : Real))
    have ht0 : 0 <= t := by
      apply div_nonneg (Real.log_nonneg ?_) (Real.log_nonneg (by norm_num))
      exact (le_div_iff₀ hdR).mpr (by simpa only [one_mul] using (show (delta : Real) <= 1 from hd1))
    have hbase : ENNReal.ofReal (2 + t) <= 2 * ENNReal.ofReal (1 + t) := by
      have h : 2 + t <= 2 * (1 + t) := by linarith
      simpa only [ENNReal.ofReal_mul (by norm_num : (0 : Real) <= 2), ENNReal.ofReal_ofNat] using
        ENNReal.ofReal_le_ofReal h
    have hden : (Cprep : ENNReal) * ENNReal.ofReal ((2 + t) ^ Kprep) <=
        (delta : ENNReal) ^ (-ePrep) := by
      rw [ENNReal.ofReal_pow (by linarith : 0 <= 2 + t)]
      calc
        (Cprep : ENNReal) * ENNReal.ofReal (2 + t) ^ Kprep <=
            (Cprep : ENNReal) * (2 * ENNReal.ofReal (1 + t)) ^ Kprep := by gcongr
        _ = ((Cprep : ENNReal) * 2 ^ Kprep) * ENNReal.ofReal (1 + t) ^ Kprep := by
          rw [mul_pow]; ring
        _ <= (delta : ENNReal) ^ (-(ePrep / 2)) * (delta : ENNReal) ^ (-(ePrep / 2)) :=
          mul_le_mul' hconst hpoly
        _ = (delta : ENNReal) ^ (-ePrep) := by
          rw [← ENNReal.rpow_add _ _ (ENNReal.coe_pos.mpr hdpos).ne' ENNReal.coe_ne_top]
          congr 1
          ring
    change (delta : ENNReal) ^ ePrep <= ((Cprep : ENNReal) * ENNReal.ofReal ((2 + t) ^ Kprep))⁻¹
    calc
      (delta : ENNReal) ^ ePrep = ((delta : ENNReal) ^ (-ePrep))⁻¹ := by rw [ENNReal.rpow_neg, inv_inv]
      _ <= _ := ENNReal.inv_le_inv.mpr hden
  have hstop {delta : NNReal} (hd : 0 < delta) (hd1 : delta < 1)
      (hgridGap : delta <= (16 : NNReal) ^ (-(M : Real)))
      (hcal : (4 : ENNReal) <= (delta : ENNReal) ^ (-p.ε ^ (2 : Nat) * p.η 0 / 2))
      {iota : Type uI} [DecidableEq iota]
      (A : Finset iota) (Y : iota -> ShadedTube delta E)
      (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan)
      (hA : A.Nonempty) (hreg : SourceRegularizedWorkingTowerW95 U Ctw Ccell)
      (hball : ∀ i ∈ A, (Y i).carrier ⊆ Metric.closedBall 0 1)
      (hCFtop : actualRelativeCFArrayW97 U 0 M <= (delta : ENNReal) ^ (-p.η 0)) :
      actualEveryScaleW95 U p.ε p.N BF ∨ Nonempty (ActualSourceDividingBlockW95 U p BF) := by
    have hMpos : 0 < M := by have := hp.M_pos; omega
    let rho := Tube.gridScale delta M
    let X := actualRelativeCFArrayW97 U
    have hrho (k : Nat) : 0 < rho k := Tube.gridScale_pos hd M k
    have hrhoE (k : Nat) : (0 : ENNReal) < rho k := ENNReal.coe_pos.mpr (hrho k)
    have hratioPos (k l : Nat) : 0 < (rho l : ENNReal) / (rho k : ENNReal) :=
      ENNReal.div_pos (hrhoE l).ne' ENNReal.coe_ne_top
    have hratioFinite (k l : Nat) : (rho l : ENNReal) / (rho k : ENNReal) < ⊤ :=
      ENNReal.div_lt_top ENNReal.coe_ne_top (hrhoE k).ne'
    have hinverse (k l : Nat) (q : Real) :
        ((rho l : ENNReal) / (rho k : ENNReal)) ^ (-q) =
          ((rho k : ENNReal) / (rho l : ENNReal)) ^ q := by
      rw [ENNReal.rpow_neg, ← ENNReal.inv_rpow,
        ENNReal.inv_div (Or.inl ENNReal.coe_ne_top) (Or.inl (hrhoE k).ne')]
    obtain ⟨hcrudeU, hprefixU⟩ := hcrude hd hd1.le U hA hreg
    have hXcrude (k l : Nat) (hkl : k < l) (hl : l <= M) :
        X k l <= (Cvol : ENNReal) * ((rho k : ENNReal) / (rho l : ENNReal)) ^ (2 : Nat) :=
      Finset.sup_le (fun R hR => hcrudeU k l hkl hl R hR)
    have hXfinite (k l : Nat) (hkl : k < l) (hl : l <= M) : X k l < ⊤ := by
      apply (hXcrude k l hkl hl).trans_lt
      exact ENNReal.mul_lt_top (by simp) (by
        exact lt_top_iff_ne_top.mpr (ENNReal.pow_ne_top (hratioFinite l k).ne))
    have hXone (k l : Nat) (hkl : k < l) (hl : l <= M) : 1 <= X k l := by
      obtain ⟨i, hi⟩ := hA
      let R := U.cover.assign k i
      let Q := U.cover.assign l i
      have hR : R ∈ U.cover.indexSet k := U.cover.assign_mem k (hkl.le.trans hl) i hi
      have hQ : Q ∈ actualDescendantsW95 A U.cover.assign k l R :=
        Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, rfl⟩, rfl⟩
      have hcontained : (U.cover.tube l Q).toConvexSpaceBody <=
          (U.cover.tube k R).toConvexSpaceBody :=
        U.cover.toChain.tube_assign_le hkl.le hl hi
      have hdensity : 0 < Kakeya.densityIn (actualDescendantsW95 A U.cover.assign k l R)
          (fun Q => (U.cover.tube l Q).toConvexSpaceBody) (U.cover.tube k R).toConvexSpaceBody :=
        (Kakeya.densityIn_pos_iff _ _ _).mpr ⟨Q, hQ,
          (Tube.volume_pos_and_lt_top (hrho l) (Tube.gridScale_le_one hd1.le M l)
            (U.cover.tube l Q)).1, hcontained⟩
      exact ((isFrostmanIn_frostmanConstIn _ _ _).one_le hdensity).trans
        (Finset.le_sup (f := actualRelativeFrostmanW95 A U.cover.assign U.cover.tube k l) hR)
    have hH1 (k l m : Nat) (hkl : k < l) (hlm : l < m) (hm : m <= M) :
        X k m <= (BF : ENNReal) * X k l * X l m := by
      have hgap : 4 * Tube.gridScale delta M m <= Tube.gridScale delta M l := by
        calc 4 * Tube.gridScale delta M m <= 16 * Tube.gridScale delta M m := by gcongr <;> norm_num
             _ <= _ := Tube.sixteen_mul_gridScale_le hd hd1.le hgridGap hlm hm
      have h := (htwo hd hd1.le U hA hreg hball k l m hkl hlm hm hgap).2
      refine h.trans (mul_le_mul' (mul_le_mul' ?_ le_rfl) le_rfl)
      exact_mod_cast (show 2 * Ctwo ^ (2 : Nat) <= BF from le_max_right _ _)
    have hH2 (k l : Nat) (hkl : k < l) (hl : l <= M) :
        X k l <= (BF : ENNReal) * ((rho l : ENNReal) / (rho k : ENNReal)) ^ (-2 : Real) := by
      rw [hinverse, ENNReal.rpow_two]
      exact (hXcrude k l hkl hl).trans (mul_le_mul'
        (by exact_mod_cast (show Cvol <= BF from le_max_left _ _)) le_rfl)
    have hNlarge : p.ε ^ (-2 : Real) <= (p.N : Real) := by
      rw [hp.epsilon_eq, ← Real.rpow_mul (Nat.cast_nonneg _)]
      norm_num
    have hspanUpper : rho M / rho 0 <= delta ^ (p.ε ^ (2 : Nat)) := by
      rw [show rho M = delta from Tube.gridScale_self delta (by have := hp.M_pos; omega),
        show rho 0 = 1 from Tube.gridScale_zero delta M, div_one]
      calc delta = delta ^ (1 : Real) := (NNReal.rpow_one _).symm
           _ <= _ := NNReal.rpow_le_rpow_of_exponent_ge hd hd1.le
              (by nlinarith [hp.epsilon_pos, hp.epsilon_small])
    have hH3 : X 0 M <= ((rho M : ENNReal) / (rho 0 : ENNReal)) ^ (-p.η 0) := by
      simpa only [rho, Tube.gridScale_self delta (N := M) hMpos,
        Tube.gridScale_zero, ENNReal.coe_one, div_one] using hCFtop
    have hbottom (k : Nat) (R : iota) :
        actualRelativeFrostmanW95 A U.cover.assign U.cover.tube k M R =
          frostmanConstIn (completeFibreW94 A (U.cover.assign k) R)
            (fun i => (Y i).toConvexSpaceBody) (U.cover.tube k R).toConvexSpaceBody := by
      have hD : actualDescendantsW95 A U.cover.assign k M R =
          completeFibreW94 A (U.cover.assign k) R := by
        calc actualDescendantsW95 A U.cover.assign k M R =
            (completeFibreW94 A (U.cover.assign k) R).image id :=
              Finset.image_congr (fun i hi => hreg.bottom_assign i (Finset.mem_filter.mp hi).1)
             _ = _ := Finset.image_id
      unfold actualRelativeFrostmanW95
      rw [hD]
      exact frostmanConstIn_congr _ (fun i hi => hreg.bottom_tube i (Finset.mem_filter.mp hi).1) _
    obtain hall | ⟨a, b, J, hab, hb, hJ, hJN, hlong, hmiddle, htail, hlow⟩ :=
      exists_same_array_stopping_w97 M p.N hp.M_pos (by have := hp.N_large; omega)
        BF 4 hBF (by norm_num) 2 p.ε (by norm_num) hp.epsilon_pos
        (by linarith [hp.epsilon_small]) hNlarge delta hd hd1 rho (fun k hk => hrho k)
        (fun k l hkl hl => Tube.gridScale_lt_gridScale hd hd1 (by have := hp.M_pos; omega) hkl)
        p.η hp.zeta_pos hp.zeta_mono (by linarith [hp.zeta_top, hp.epsilon_pos])
        (fun j hj => by
          have h := hp.rung_next j hj
          have hpos := mul_pos hp.epsilon_pos (hp.zeta_pos (j + 1) (by omega))
          nlinarith only [h, hpos])
        (by simp only [rho, Tube.gridScale_self delta (N := M) hMpos,
          Tube.gridScale_zero, div_one, le_refl]) hspanUpper X hXone hXfinite hH1 hH2 hH3
        (fun a m b ham hmb hb => (hprefixU a m b ham hmb hb).2) hcal
    · left
      intro k hk R hR
      by_cases hkM : k < M
      · rw [← hbottom k R]
        have h := (Finset.le_sup (f := actualRelativeFrostmanW95 A U.cover.assign U.cover.tube k M) hR).trans
          (hall k hkM)
        norm_num only at h
        exact h
      · have he : k = M := by omega
        subst k
        have hRA : R ∈ A := hreg.bottom_index ▸ hR
        have hfibre : completeFibreW94 A (U.cover.assign M) R = {R} := by
          ext i
          simp only [completeFibreW94, Finset.mem_filter, Finset.mem_singleton]
          constructor
          · rintro ⟨hi, hieq⟩
            rwa [hreg.bottom_assign i hi] at hieq
          · intro hei
            subst i
            exact ⟨hRA, hreg.bottom_assign R hRA⟩
        rw [hfibre, hreg.bottom_tube R hRA]
        have hsingleton : IsFrostmanIn {R} (fun i => (Y i).toConvexSpaceBody)
            (Y R).toConvexSpaceBody 1 := by
          apply IsFrostmanIn.of_maxDensity_mul_volume_le
            (fun i hi => by rw [Finset.mem_singleton.mp hi])
            (Tube.volume_pos_and_lt_top hd hd1.le (Y R).toTube).1.ne'
          have hmax : Kakeya.maxDensity {R} (fun i => (Y i).toConvexSpaceBody) <= 1 := by
            simpa only [Finset.card_singleton, Nat.cast_one] using
              Kakeya.maxDensity_le_card {R} (fun i => (Y i).toConvexSpaceBody)
          simpa only [Finset.sum_singleton, one_mul] using
            mul_le_mul_right' hmax (volume (Y R).carrier)
        refine (frostmanConstIn_le hsingleton).trans ?_
        have hpow : (1 : ENNReal) <= (delta : ENNReal) ^ (-3 * p.ε) := by
          simpa only [ENNReal.rpow_zero] using ENNReal.rpow_le_rpow_of_exponent_ge
            (x := (delta : ENNReal)) (by exact_mod_cast hd1.le)
            (show -3 * p.ε <= 0 by linarith [hp.epsilon_pos])
        exact one_le_mul (one_le_pow₀ (by exact_mod_cast hBF)) hpow
    · right
      refine ⟨{
        a := ⟨a, by omega⟩
        b := ⟨b, by omega⟩
        a_lt_b := hab
        label := ⟨J - 1, by omega⟩
        label_active := by change J - 1 < p.N; omega
        block_long := hlong
        middle_upper := by
          intro R hR
          have h := (Finset.le_sup (f := actualRelativeFrostmanW95 A U.cover.assign U.cover.tube a b) hR).trans hmiddle
          simpa only [hinverse] using h
        tail_upper := by
          intro hbM R hR
          rw [← hbottom b R]
          have h := (Finset.le_sup (f := actualRelativeFrostmanW95 A U.cover.assign U.cover.tube b M) hR).trans
            (htail hbM)
          rw [hinverse b M (p.η (J - 1))] at h
          simpa only [rho, Tube.gridScale_self delta (N := M) hMpos] using h
        intermediate_lower := by
          intro l hal hlb hwinL hwinU R hR
          have hl : l <= M := hlb.le.trans hb
          let rab : ENNReal := (rho b : ENNReal) / (rho a : ENNReal)
          let ral : ENNReal := (rho l : ENNReal) / (rho a : ENNReal)
          let rlb : ENNReal := (rho b : ENNReal) / (rho l : ENNReal)
          have hrab : 0 < rab := hratioPos a b
          have hral : 0 < ral := hratioPos a l
          have hrlb : 0 < rlb := hratioPos l b
          have hrabfin : rab < ⊤ := hratioFinite a b
          have hralfin : ral < ⊤ := hratioFinite a l
          have hrlbfin : rlb < ⊤ := hratioFinite l b
          have hprod : ral * rlb = rab := by
            dsimp [ral, rlb, rab]
            simp only [div_eq_mul_inv]
            calc (rho l : ENNReal) * (rho a : ENNReal)⁻¹ *
                ((rho b : ENNReal) * (rho l : ENNReal)⁻¹) =
                  ((rho l : ENNReal) * (rho l : ENNReal)⁻¹) *
                    ((rho b : ENNReal) * (rho a : ENNReal)⁻¹) := by ring
                 _ = _ := by rw [ENNReal.mul_inv_cancel (hrhoE l).ne' ENNReal.coe_ne_top, one_mul]
          have hpowprod : rab ^ (1 - p.ε) * rab ^ p.ε = rab := by
            rw [← ENNReal.rpow_add _ _ hrab.ne' hrabfin.ne]
            simp only [sub_add_cancel, ENNReal.rpow_one]
          have hwindowL : rab ^ (1 - p.ε) <= ral := by
            apply (ENNReal.mul_le_mul_iff_left hrlb.ne' hrlbfin.ne).mp
            calc rab ^ (1 - p.ε) * rlb <= rab ^ (1 - p.ε) * rab ^ p.ε :=
                   mul_le_mul_left' hwinU _
                 _ = ral * rlb := hpowprod.trans hprod.symm
          have hwindowU : ral <= rab ^ p.ε := by
            apply (ENNReal.mul_le_mul_iff_left
              (ENNReal.rpow_pos hrab hrabfin.ne).ne'
              (ENNReal.rpow_ne_top_of_ne_zero hrab.ne' hrabfin.ne)).mp
            calc ral * rab ^ (1 - p.ε) <= ral * rlb := mul_le_mul_left' hwinL _
                 _ = rab ^ p.ε * rab ^ (1 - p.ε) := by rw [hprod, mul_comm, hpowprod]
          have hstrict : rlb ^ (-p.η J) < X l b := hlow l hal hlb hwindowL hwindowU
          have hband : X l b <= 2 * hreg.frostmanBand l b :=
            Finset.sup_le (fun Q hQ => (hreg.frostman_upper l b hlb hb Q hQ).le)
          have hparent := hreg.frostman_lower l b hlb hb R hR
          have hbound : rlb ^ (-p.η J) <
              2 * actualRelativeFrostmanW95 A U.cover.assign U.cover.tube l b R :=
            hstrict.trans_le (hband.trans (mul_le_mul_left' hparent 2))
          have hhalf := ENNReal.mul_lt_mul_right (a := (2 : ENNReal)⁻¹)
            (by norm_num) (by finiteness) hbound
          rw [← mul_assoc, ENNReal.inv_mul_cancel (by norm_num : (2 : ENNReal) ≠ 0)
            (by simp), one_mul] at hhalf
          simpa only [Nat.sub_add_cancel hJ, one_div, rlb, hinverse] using hhalf }⟩
  have hsmall : Filter.Eventually (fun delta : NNReal =>
      (delta : ENNReal) ^ ePrep <= towerPreparationRetainedW95 delta Cprep Kprep ∧
      (Croot : ENNReal) * Ctw <= (delta : ENNReal) ^ (-ePrep) ∧
      (4 : ENNReal) <= (delta : ENNReal) ^ (-p.ε ^ (2 : Nat) * p.η 0 / 2) ∧
      delta <= (16 : NNReal) ^ (-(M : Real))) (nhdsWithin 0 (Set.Ioi 0)) := by
    filter_upwards [hprepCost,
      eventually_finite_const_le_rpow_neg (c := (Croot : ENNReal) * Ctw) (by finiteness) hePrep,
      eventually_finite_const_le_rpow_neg (c := (4 : ENNReal)) (by finiteness)
        (show 0 < p.ε ^ (2 : Nat) * p.η 0 / 2 by
          exact div_pos (mul_pos (pow_pos hp.epsilon_pos _) (hp.zeta_pos 0 (Nat.zero_le _))) (by norm_num)),
      eventually_le_nhdsGT (c := (16 : NNReal) ^ (-(M : Real))) (NNReal.rpow_pos (by norm_num))]
      with delta hprep hroot hfour hgap
    exact ⟨hprep, hroot, by simpa only [neg_div, neg_mul] using hfour, hgap⟩
  obtain ⟨deltaCut, hdeltaCut, hcut⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hsmall
  let delta0 := min deltaPrep deltaCut
  have hdelta0 : 0 < delta0 := lt_min hdeltaPrep hdeltaCut
  have hdelta01 : delta0 < 1 := (min_le_left _ _).trans_lt hdeltaPrep1
  refine ⟨Ccan, Ctw, Ccell, BF, Cprep, Kprep, ePrep, delta0,
    hCcan, hCtw, hCcell, hBF, hCprep, hKprep, hePrep, hePrepSmall, hdelta0, hdelta01, ?_⟩
  intro delta hd hd0 iota inst F Y hF hball hcen hline hfull hCF
  have hd1 : delta < 1 := hd0.trans hdelta01
  have hdPrep : delta < deltaPrep := hd0.trans_le (min_le_left _ _)
  obtain ⟨hprepPaid, hrootPaid, hfourPaid, hgridGap⟩ :=
    hcut ⟨hd, hd0.trans_le (min_le_right _ _)⟩
  have hdEpos : (0 : ENNReal) < delta := ENNReal.coe_pos.mpr hd
  have hfullpos : 0 < fullness' F (fun i => (Y i).toShadedBody) :=
    (ENNReal.rpow_pos hdEpos ENNReal.coe_ne_top).trans_le hfull
  have hmass : 0 < ∑ i ∈ F, volume (Y i).shade := by
    by_contra h
    have hz : (∑ i ∈ F, volume (Y i).shade) = 0 := le_antisymm (not_lt.mp h) bot_le
    simp only [fullness', hz, ENNReal.zero_div, lt_self_iff_false] at hfullpos
  obtain ⟨A, Uext, hA, hAF, hpaid, ⟨hext⟩, hmargin⟩ := htower hd hdPrep F Y hball hcen hline hmass
  obtain ⟨U, hU, hindex, hassign, hscale, htubes⟩ := hrestrict A Y Ccan Ctw Ccell Uext hext
  obtain ⟨hreg⟩ := hU
  have hLpos : 0 < 2 + Real.log (1 / (delta : Real)) / Real.log 2 := by
    have hlog : 0 <= Real.log (1 / (delta : Real)) / Real.log 2 := by
      apply div_nonneg (Real.log_nonneg ?_) (Real.log_nonneg (by norm_num))
      exact (le_div_iff₀ (show (0 : Real) < delta from hd)).mpr
        (by simpa only [one_mul] using (show (delta : Real) <= 1 from hd1.le))
    linarith
  have hdenompos : 0 < (Cprep : ENNReal) * ENNReal.ofReal
      ((2 + Real.log (1 / (delta : Real)) / Real.log 2) ^ Kprep) :=
    ENNReal.mul_pos (ENNReal.coe_pos.mpr (zero_lt_one.trans_le hCprep)).ne'
      (ENNReal.ofReal_pos.mpr (pow_pos hLpos _)).ne'
  have hrpos : 0 < towerPreparationRetainedW95 delta Cprep Kprep := by
    apply ENNReal.inv_pos.mpr
    finiteness
  have hrfin : towerPreparationRetainedW95 delta Cprep Kprep < ⊤ :=
    ENNReal.inv_lt_top.mpr hdenompos
  obtain ⟨i0, hi0⟩ := hF
  obtain ⟨hvpos, hvfin⟩ := Tube.volume_pos_and_lt_top hd hd1.le (Y i0).toTube
  obtain ⟨_, _, _, hCFA⟩ := retained_state_fullness_card_frostman_w94
    F A (fun i => (Y i).toShadedBody) (fun i => (Y i).toShadedBody)
    ConvexSpaceBody.closedUnitBall (volume (Y i0).carrier) ((delta : ENNReal) ^ ePrep)
    ((delta : ENNReal) ^ (-ePrep)) (towerPreparationRetainedW95 delta Cprep Kprep)
    ⟨i0, hi0⟩ hAF hvpos hvfin
    (fun i hi => Tube.volume_carrier_eq_volume_carrier (Y i).toTube (Y i0).toTube)
    (fun i hi => hball i hi) ConvexSpaceBody.closedUnitBall_volume_pos
    ConvexSpaceBody.closedUnitBall.isCompact.measure_lt_top
    (fun i hi => rfl) (fun i hi => Set.Subset.refl _)
    (ENNReal.rpow_pos hdEpos ENNReal.coe_ne_top)
    (ENNReal.rpow_lt_top_of_nonneg hePrep.le ENNReal.coe_ne_top) hfull hCF
    ((ENNReal.rpow_ne_top_of_ne_zero hdEpos.ne' ENNReal.coe_ne_top).lt_top)
    hrpos hrfin hpaid
  have htop : actualRelativeCFArrayW97 U 0 M <= (delta : ENNReal) ^ (-p.η 0) := by
    have h := (hroot hd hd1.le U hp.M_pos hA hreg (fun i hi => hball i (hAF hi)) _ hCFA).2
    calc actualRelativeCFArrayW97 U 0 M <=
        (Croot : ENNReal) * Ctw * ((towerPreparationRetainedW95 delta Cprep Kprep *
          (delta : ENNReal) ^ ePrep)⁻¹ * (delta : ENNReal) ^ (-ePrep)) := h
      _ <= (delta : ENNReal) ^ (-ePrep) *
          (((delta : ENNReal) ^ ePrep * (delta : ENNReal) ^ ePrep)⁻¹ *
            (delta : ENNReal) ^ (-ePrep)) :=
        mul_le_mul' hrootPaid (mul_le_mul' (ENNReal.inv_le_inv.mpr
          (mul_le_mul' hprepPaid le_rfl)) le_rfl)
      _ = (delta : ENNReal) ^ (-4 * ePrep) := by
        rw [← ENNReal.rpow_add _ _ hdEpos.ne' ENNReal.coe_ne_top, ← ENNReal.rpow_neg,
          ← ENNReal.rpow_add _ _ hdEpos.ne' ENNReal.coe_ne_top,
          ← ENNReal.rpow_add _ _ hdEpos.ne' ENNReal.coe_ne_top]
        congr 1
        ring
      _ <= (delta : ENNReal) ^ (-p.η 0) :=
        ENNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hd1.le)
          (by dsimp [ePrep]; linarith [hp.zeta_pos 0 (Nat.zero_le _)])
  exact ⟨A, U, Uext, hA, hAF, hpaid, ⟨hreg⟩, ⟨hext⟩,
    ⟨hindex, hassign, hscale, htubes⟩, hmargin,
    hstop hd hd1 hgridGap hfourPaid A Y U hA hreg (fun i hi => hball i (hAF hi)) htop⟩

end

end Kakeya.ml1Boot.TrialRestartW94
