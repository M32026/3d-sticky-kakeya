module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.PreparedAxisFootCoreW103
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.AxisFootNormalizationGeometryW103

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

private theorem quotient_tube_fields_of_heq_w103 {r s : NNReal} (T : Tube r E) (V : Tube s E)
    (hrs : r = s) (hTV : HEq T V) :
    T.toConvexSpaceBody = V.toConvexSpaceBody ∧ T.center = V.center ∧ T.direction = V.direction := by
  subst s
  have h := eq_of_heq hTV
  subst V
  exact ⟨rfl, rfl, rfl⟩

private theorem quotient_axisFoot_body_of_heq_w103 {r s t u : NNReal}
    (L : E ≃ᵃ[Real] E) (T : Tube r E) (V : Tube s E)
    (hrs : r = s) (htu : t = u) (hTV : HEq T V) :
    (axisFootTubeW103 t L T).toConvexSpaceBody = (axisFootTubeW103 u L V).toConvexSpaceBody := by
  subst s
  subst u
  have h := eq_of_heq hTV
  subst V
  rfl

private theorem quotient_tube_nested_w103
    {iota : Type uI} [DecidableEq iota] {delta : NNReal}
    {A : Finset iota} {T : iota -> Tube delta E} {N : Nat}
    (cov : Tube.GridCoverSystem A T N) {a b : Nat} (hab : a <= b) (hb : b <= N)
    (i : iota) (hi : i ∈ A) :
    (cov.tube b (cov.assign b i)).toConvexSpaceBody <=
      (cov.tube a (cov.assign a i)).toConvexSpaceBody := by
  revert hb
  induction b, hab using Nat.le_induction with
  | base => exact fun _ => le_rfl
  | succ b hab ih =>
    intro hb
    exact (cov.tube_nested b hb i hi).trans (ih (by omega))

theorem exists_axisFoot_quotient_geometry_w103
    (hdim : Module.finrank Real E = 3) (M : Nat) (hM : 1 <= M) :
    ∃ Rmin : NNReal, 1 <= Rmin ∧
      ∀ Rnorm : NNReal, Rmin <= Rnorm ->
      ∀ {delta : NNReal}, 0 < delta -> delta < 1 ->
        16 * Tube.gridScale delta (M * M) 1 <= 1 ->
      ∀ {iota : Type uI} [DecidableEq iota]
        {A : Finset iota} {Y : iota -> ShadedTube delta E}
        {Ccan Ctw Ccell : NNReal}
        (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan)
        (Uext : CanonicalProfileNetW87 A (fun i => (Y i).toTube) (M * M) Ccan),
        A.Nonempty -> VisibleExtendedRestrictionW97 U Uext ->
        SourceRegularizedWorkingTowerW95 U Ctw Ccell ->
        SourceRegularizedWorkingTowerW95 Uext Ctw Ccell ->
        ActualTreeParameterMarginW98 Uext.cover normalizationParameterMarginW98 ->
      ∀ (a b : Nat), a < b -> b <= M ->
      ∀ (R : iota), R ∈ U.cover.indexSet a ->
      ∀ (L : E ≃ᵃ[Real] E), L.toAffineMap = (U.cover.tube a R).rescaleMap (Rnorm : Real) ->
        let F := actualDescendantsW95 A U.cover.assign a b R
        let d := Tube.gridScale delta M b / Tube.gridScale delta M a
        let c := quotientGridIndexW97 M a b
        let parent := fun l => Kakeya.ML2Reduction.coarseNode Uext.cover.toChain (c l) (b * M)
        (∀ Q ∈ F, (U.cover.tube b Q).toConvexSpaceBody <= (U.cover.tube a R).toConvexSpaceBody) ∧
        (∀ l, l <= M -> ∀ S ∈ F.image (parent l),
          S ∈ Uext.cover.indexSet (c l) ∧
          (Uext.cover.tube (c l) S).toConvexSpaceBody <= (U.cover.tube a R).toConvexSpaceBody) ∧
        (∀ l, l <= M -> Tube.gridScale d M l =
          Tube.gridScale delta (M * M) (c l) / Tube.gridScale delta M a) ∧
        (∀ l, l <= M -> ∀ Q ∈ F,
          (axisFootTubeW103 d L (U.cover.tube b Q)).toConvexSpaceBody <=
            (axisFootTubeW103 (Tube.gridScale d M l) L
              (Uext.cover.tube (c l) (parent l Q))).toConvexSpaceBody) := by
  obtain ⟨Rmin, hRmin, hpair⟩ := exists_axis_foot_unit_containment_margin_w98 (E := E) hdim
  refine ⟨Rmin, hRmin, ?_⟩
  intro Rnorm hRnorm delta hd hd1 hgap iota inst A Y Ccan Ctw Ccell U Uext
    hA restriction reg regext margin a b hab hb R hR L hL
  let F := actualDescendantsW95 A U.cover.assign a b R
  let d := Tube.gridScale delta M b / Tube.gridScale delta M a
  let c := quotientGridIndexW97 M a b
  let parent := fun l => Kakeya.ML2Reduction.coarseNode Uext.cover.toChain (c l) (b * M)
  have ha : a <= M := hab.le.trans hb
  have hbM : b * M <= M * M := Nat.mul_le_mul_right M hb
  have htheta : 0 < Tube.gridScale delta M a := Tube.gridScale_pos hd M a
  obtain ⟨hzero, hend, hbounds, hstrict, hscales⟩ :=
    quotient_grid_index_w97 M a b hM hab hb delta hd hd1
  have hfields (k : Nat) (hk : k <= M) (Q : iota) :=
    quotient_tube_fields_of_heq_w103 (U.cover.tube k Q) (Uext.cover.tube (k * M) Q)
      (restriction.radius k hk) (restriction.tube k hk Q)
  have hparent : ∀ l, l <= M -> ∀ i ∈ A,
      parent l (U.cover.assign b i) = Uext.cover.assign (c l) i := by
    intro l hl i hi
    rw [restriction.assign b hb]
    have hclass : (Tube.coverClass A (Uext.cover.toChain.assign (b * M))
        (Uext.cover.assign (b * M) i)).Nonempty :=
      ⟨i, by simp only [Tube.coverClass, Finset.mem_filter]; exact ⟨hi, rfl⟩⟩
    dsimp only [parent]
    rw [Kakeya.ML2Reduction.coarseNode, dif_pos hclass]
    have hmem := hclass.choose_spec
    simp only [Tube.coverClass, Finset.mem_filter] at hmem
    exact Uext.cover.assign_eq_of_le (hbounds l hl).2.1 hbM hmem.1 hi hmem.2
  have hfineTop : ∀ Q ∈ F,
      (U.cover.tube b Q).toConvexSpaceBody <= (U.cover.tube a R).toConvexSpaceBody := by
    intro Q hQ
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQ
    obtain ⟨hiA, hiR⟩ := Finset.mem_filter.mp hi
    simpa only [hiR] using quotient_tube_nested_w103 U.cover hab.le hb i hiA
  have hphysical : ∀ l, l <= M -> ∀ S ∈ F.image (parent l),
      S ∈ Uext.cover.indexSet (c l) ∧
        (Uext.cover.tube (c l) S).toConvexSpaceBody <= (U.cover.tube a R).toConvexSpaceBody := by
    intro l hl S hS
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQ
    obtain ⟨hiA, hiR⟩ := Finset.mem_filter.mp hi
    rw [hparent l hl i hiA]
    refine ⟨Uext.cover.assign_mem (c l) (hbounds l hl).2.2 i hiA, ?_⟩
    have hiRext : Uext.cover.assign (a * M) i = R := by
      rw [← restriction.assign a ha]
      exact hiR
    rw [(hfields a ha R).1]
    simpa only [hiRext] using
      quotient_tube_nested_w103 Uext.cover (hbounds l hl).1 (hbounds l hl).2.2 i hiA
  have hradius : ∀ l, l <= M -> Tube.gridScale d M l =
      Tube.gridScale delta (M * M) (c l) / Tube.gridScale delta M a := by
    intro l hl
    rw [hscales l hl]
    change Tube.gridScale d M l = Tube.gridScale delta M a * Tube.gridScale d M l /
      Tube.gridScale delta M a
    rw [mul_div_cancel_left₀ _ htheta.ne']
  refine ⟨hfineTop, hphysical, hradius, ?_⟩
  intro l hl Q hQ
  by_cases hlM : l = M
  · subst l
    have hlast := (extended_middle_fibres_w97 U Uext restriction regext hM a b hab hb R hR).2.2.2.2.2.2 Q hQ
    have hP : parent M Q = Q := hlast.1
    change (axisFootTubeW103 d L (U.cover.tube b Q)).toConvexSpaceBody <=
      (axisFootTubeW103 (Tube.gridScale d M M) L (Uext.cover.tube (c M) (parent M Q))).toConvexSpaceBody
    apply Eq.le
    apply quotient_axisFoot_body_of_heq_w103 L (U.cover.tube b Q)
      (Uext.cover.tube (c M) (parent M Q))
    · change Tube.gridScale delta M b = Tube.gridScale delta (M * M) (quotientGridIndexW97 M a b M)
      rw [hend]
      exact restriction.radius b hb
    · exact (Tube.gridScale_self d hM).symm
    · have hindex {j k : Nat} (hjk : j = k) :
          HEq (Uext.cover.tube j Q) (Uext.cover.tube k Q) := by
        subst k
        rfl
      apply (restriction.tube b hb Q).trans
      rw [hP]
      exact hindex hend.symm
  · have hlLt : l < M := lt_of_le_of_ne hl hlM
    have hcLt : c l < b * M := by
      simpa only [hend] using hstrict l M hlLt le_rfl
    have hstep (k : Nat) : 16 * Tube.gridScale delta (M * M) (k + 1) <=
        Tube.gridScale delta (M * M) k := by
      have hfactor : Tube.gridScale delta (M * M) (k + 1) =
          Tube.gridScale delta (M * M) k * Tube.gridScale delta (M * M) 1 := by
        unfold Tube.gridScale
        rw [show ((k + 1 : Nat) : Real) / (M * M : Nat) =
          (k : Real) / (M * M : Nat) + (1 : Real) / (M * M : Nat) by push_cast; ring]
        simpa only [Nat.cast_one] using NNReal.rpow_add hd.ne'
          ((k : Real) / (M * M : Nat)) ((1 : Real) / (M * M : Nat))
      rw [hfactor, mul_left_comm]
      exact (mul_le_mul_of_nonneg_left hgap (Tube.gridScale delta (M * M) k).coe_nonneg).trans_eq
        (mul_one _)
    have hsep : 16 * Tube.gridScale delta M b <= Tube.gridScale delta (M * M) (c l) := by
      rw [restriction.radius b hb]
      exact (mul_le_mul_of_nonneg_left
        (Tube.gridScale_antitone hd hd1.le (M * M) (Nat.succ_le_iff.mpr hcLt)) (by norm_num)).trans
          (hstep (c l))
    have hsigmatheta : Tube.gridScale delta (M * M) (c l) <= Tube.gridScale delta M a := by
      rw [restriction.radius a ha]
      exact Tube.gridScale_antitone hd hd1.le (M * M) (hbounds l hl).1
    obtain ⟨i, hi, hiQ⟩ := Finset.mem_image.mp hQ
    obtain ⟨hiA, hiR⟩ := Finset.mem_filter.mp hi
    have hfineParent : (U.cover.tube b Q).toConvexSpaceBody <=
        (Uext.cover.tube (c l) (parent l Q)).toConvexSpaceBody := by
      rw [(hfields b hb Q).1, ← hiQ, hparent l hl i hiA, restriction.assign b hb]
      exact quotient_tube_nested_w103 Uext.cover hcLt.le hbM i hiA
    have hcentre : ‖(U.cover.tube b Q).center - (Uext.cover.tube (c l) (parent l Q)).center‖ <=
        (normalizationParameterMarginW98 : Real) * (Tube.gridScale delta (M * M) (c l) : Real) := by
      rw [(hfields b hb Q).2.1, ← hiQ, hparent l hl i hiA, restriction.assign b hb]
      exact margin.midpoint (c l) (b * M) hcLt hbM i hiA
    have hdir : min
        (‖(U.cover.tube b Q).direction - (Uext.cover.tube (c l) (parent l Q)).direction‖)
        (‖(U.cover.tube b Q).direction + (Uext.cover.tube (c l) (parent l Q)).direction‖) <=
        (normalizationParameterMarginW98 : Real) * (Tube.gridScale delta (M * M) (c l) : Real) := by
      rw [(hfields b hb Q).2.2, ← hiQ, hparent l hl i hiA, restriction.assign b hb]
      exact margin.direction (c l) (b * M) hcLt hbM i hiA
    obtain ⟨W, P, hWP, _, _, _, _, hWdir, hPdir, hWcentre, hPcentre⟩ :=
      hpair Rnorm hRnorm (Tube.gridScale_pos hd M b) hsep hsigmatheta
        (Tube.gridScale_le_one hd1.le M a) (U.cover.tube a R)
        (Uext.cover.tube (c l) (parent l Q)) (U.cover.tube b Q)
        (hphysical l hl _ (Finset.mem_image_of_mem _ hQ)).2 hfineParent hcentre hdir
    have hW : W = axisFootTubeW103 d L (U.cover.tube b Q) := by
      apply axisFootTube_unique_w103 L (U.cover.tube b Q) W
      · change W.direction = ‖L.toAffineMap.linear (U.cover.tube b Q).direction‖⁻¹ •
          L.toAffineMap.linear (U.cover.tube b Q).direction
        rw [hL]
        exact hWdir
      · change W.center = L.toAffineMap (U.cover.tube b Q).center -
          inner Real (L.toAffineMap (U.cover.tube b Q).center) W.direction • W.direction
        rw [hL]
        exact hWcentre
    have hP : P = axisFootTubeW103
        (Tube.gridScale delta (M * M) (c l) / Tube.gridScale delta M a) L
        (Uext.cover.tube (c l) (parent l Q)) := by
      apply axisFootTube_unique_w103 L (Uext.cover.tube (c l) (parent l Q)) P
      · change P.direction = ‖L.toAffineMap.linear (Uext.cover.tube (c l) (parent l Q)).direction‖⁻¹ •
          L.toAffineMap.linear (Uext.cover.tube (c l) (parent l Q)).direction
        rw [hL]
        exact hPdir
      · change P.center = L.toAffineMap (Uext.cover.tube (c l) (parent l Q)).center -
          inner Real (L.toAffineMap (Uext.cover.tube (c l) (parent l Q)).center) P.direction • P.direction
        rw [hL]
        exact hPcentre
    change (axisFootTubeW103 d L (U.cover.tube b Q)).toConvexSpaceBody <=
      (axisFootTubeW103 (Tube.gridScale d M l) L (Uext.cover.tube (c l) (parent l Q))).toConvexSpaceBody
    rw [hradius l hl, ← hW, ← hP]
    exact hWP

end

end Kakeya.ml1Boot.TrialRestartW94
