module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceEligibleCallsW97
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceConstructionRawCutsW97

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody
open scoped ENNReal NNReal

namespace Kakeya.ml1Boot.TrialRestartW94

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

universe uE uI

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

open RevisedLiteralProfileInterfaceFormalizerW87

/-- D1: edges are actual common fine members, not intersecting parent carriers. -/
theorem actual_working_canonical_incidence_w97
    (CbaseTw CworkTw : NNReal) (hbase : 1 <= CbaseTw) (hwork : 1 <= CworkTw) :
    ∃ Cdegree : NNReal, 1 <= Cdegree ∧
      ∀ {delta : NNReal}, 0 < delta -> delta <= 1 ->
      ∀ {iota : Type uI} [DecidableEq iota]
        {B : Finset iota} {V : iota -> ShadedTube delta E} {M : Nat}
        {Ccan Cwork CbaseCell CworkCell : NNReal}
        (U0 : CanonicalProfileNetW87 B (fun i => (V i).toTube) M Ccan)
        (current : RetainedStateW94 B V) (A : Finset iota)
        (U : CanonicalProfileNetW87 A (fun i => (current.shading i).toTube) M Cwork),
        A ⊆ current.active -> SourceRegularizedWorkingTowerW95 U0 CbaseTw CbaseCell ->
        SourceRegularizedWorkingTowerW95 U CworkTw CworkCell ->
      ∀ q : Fin (M + 1),
        let edges := A.image (fun i => (U.cover.assign q.val i, U0.cover.assign q.val i))
        let edgeFine := fun e : iota × iota =>
          A.filter (fun i => U.cover.assign q.val i = e.1 ∧ U0.cover.assign q.val i = e.2)
        (∀ Q ∈ U.cover.indexSet q.val,
          ((edges.filter (fun e => e.1 = Q)).card : NNReal) <= Cdegree) ∧
        (∀ w ∈ canonicalAncestorFamilyW87 U0 current.active q,
          ((edges.filter (fun e => e.2 = w)).card : NNReal) <= Cdegree) ∧
        (∀ e ∈ edges, (edgeFine e).Nonempty ∧
          ∀ i ∈ edgeFine e,
            (current.shading i).toConvexSpaceBody <= (U.cover.tube q.val e.1).toConvexSpaceBody ∧
            (current.shading i).toConvexSpaceBody <= (U0.cover.tube q.val e.2).toConvexSpaceBody) ∧
        A = edges.biUnion edgeFine ∧
        (edges : Set (iota × iota)).Pairwise (fun e f => Disjoint (edgeFine e) (edgeFine f)) ∧
        (∑ e ∈ edges, ∑ i ∈ edgeFine e, volume (current.shading i).shade) =
          ∑ i ∈ A, volume (current.shading i).shade := by
  let K := lineAmplificationBoundW95 (Module.finrank Real E) 2 32
  let Cdegree : NNReal := max 1 ((K : NNReal) * max CbaseTw CworkTw)
  have hcount : ∀ {iota : Type uI} [DecidableEq iota] {rho : NNReal}, 0 < rho -> rho <= 1 ->
      ∀ (J H : Finset iota) (T : iota -> Tube rho E) (C : NNReal) (W : Tube rho E),
        H ⊆ J -> lineEssentiallyDistinctW94 J T C ->
        (∀ i ∈ J, (T i).carrier ⊆ Metric.closedBall 0 2) ->
        (∀ i ∈ H, ∃ p q : E, dist p q = 1 ∧ p ∈ W.carrier ∧ q ∈ W.carrier ∧
          p ∈ (T i).carrier ∧ q ∈ (T i).carrier) ->
        (H.card : NNReal) <= (K : NNReal) * C := by
    intro iota inst rho hr hr1 J H T C W hHJ hline hball hwitness
    have hcenter : ∀ i ∈ J, ‖(T i).center‖ <= 2 := by
      intro i hi
      have hmid := Tube.midpoint_mem_closedBall_of_subset hr (T i) (hball i hi)
      simpa only [Tube.center, Tube.midpoint, midpoint_eq_smul_add, invOf_eq_inv,
        one_div, Metric.mem_closedBall, dist_zero_right] using hmid
    have hnear : H ⊆ nearLineFamilyW95 J T W.center W.direction 32 := by
      intro i hi
      obtain ⟨p, q, hpq, hpW, hqW, hpT, hqT⟩ := hwitness i hi
      have hp2 := Tube.subset_dilate (T i) (by norm_num : (1 : Real) <= 2) hpT
      have hq2 := Tube.subset_dilate (T i) (by norm_num : (1 : Real) <= 2) hqT
      have hdir := Tube.norm_perp_direction_le_of_chord W (T i) (d := 1)
        (by norm_num) hpq.ge hpW hqW hp2 hq2
      have hsmall : ‖(T i).direction - inner Real W.direction (T i).direction • W.direction‖ <=
          15 * (1 : Real) * rho := by
        norm_num only [div_one] at hdir
        nlinarith only [hdir, rho.coe_nonneg]
      have hdilate := Tube.subset_dilate_of_norm_perp_direction_le W (T i) (K := 1)
        le_rfl (by exact_mod_cast hr1) (by norm_num) hpW hp2 hsmall
      refine Finset.mem_filter.mpr ⟨hHJ hi, ?_⟩
      intro x hx
      obtain ⟨s, hs, hdist⟩ := Kakeya.Tube.exists_axis_repr_of_mem_dilate W
        (c := 32 * 1) (by norm_num) (hdilate hx)
      apply VeryNotSticky.mem_lineNbhd_of_dist_le s
      simpa only [dist_eq_norm, mul_one] using hdist
    obtain ⟨G, assign, hG, hGcard, hassign, hcover⟩ :=
      exists_radius_five_line_bins_w95 hr hr1 J T 2 32 (by norm_num) (by norm_num)
        hcenter W.center W.direction W.norm_direction
    let fibres := fun k => J.filter (fun i => liesInFiveDeltaLineTubeW94 (T i) (T k).center (T k).direction)
    have hfibres : ∀ k, ((fibres k).card : NNReal) <= C := fun k =>
      hline (T k).center (T k).direction (T k).norm_direction
    have hcovered : H ⊆ G.biUnion fibres := by
      intro i hi
      have hni := hnear hi
      refine Finset.mem_biUnion.mpr ⟨assign i, hassign i hni, Finset.mem_filter.mpr ⟨hHJ hi, ?_⟩⟩
      exact (pointwise_line_neighbourhood_iff_w95 (T i) (T (assign i)).center
        (T (assign i)).direction (T (assign i)).norm_direction).mpr (hcover i hni)
    calc
      (H.card : NNReal) <= ((G.biUnion fibres).card : NNReal) := by exact_mod_cast Finset.card_le_card hcovered
      _ <= ∑ k ∈ G, ((fibres k).card : NNReal) := by exact_mod_cast Finset.card_biUnion_le
      _ <= ∑ _k ∈ G, C := Finset.sum_le_sum (fun k hk => hfibres k)
      _ = (G.card : NNReal) * C := by rw [Finset.sum_const, nsmul_eq_mul]
      _ <= (K : NNReal) * C := by
        apply mul_le_mul_right'
        exact_mod_cast hGcard
  refine ⟨Cdegree, le_max_left _ _, ?_⟩
  intro delta hd hd1 iota inst B V M Ccan Cwork CbaseCell CworkCell U0 current A U
    hA reg0 reg q
  dsimp only
  let edges := A.image (fun i => (U.cover.assign q.val i, U0.cover.assign q.val i))
  let edgeFine := fun e : iota × iota =>
    A.filter (fun i => U.cover.assign q.val i = e.1 ∧ U0.cover.assign q.val i = e.2)
  have hq : q.val <= M := Nat.le_of_lt_succ q.isLt
  have hcontained : ∀ i ∈ A,
      (current.shading i).toConvexSpaceBody <= (U.cover.tube q.val (U.cover.assign q.val i)).toConvexSpaceBody ∧
      (current.shading i).toConvexSpaceBody <= (U0.cover.tube q.val (U0.cover.assign q.val i)).toConvexSpaceBody := by
    intro i hi
    refine ⟨U.cover.le_tube_assign q.val hq i hi, ?_⟩
    rw [show (current.shading i).toConvexSpaceBody = (V i).toConvexSpaceBody from
      congrArg Tube.toConvexSpaceBody (current.same_tube i (hA hi))]
    exact U0.cover.le_tube_assign q.val hq i (current.active_subset (hA hi))
  have hmem : ∀ e ∈ edges, (edgeFine e).Nonempty ∧
      ∀ i ∈ edgeFine e,
        (current.shading i).toConvexSpaceBody <= (U.cover.tube q.val e.1).toConvexSpaceBody ∧
        (current.shading i).toConvexSpaceBody <= (U0.cover.tube q.val e.2).toConvexSpaceBody := by
    intro e he
    obtain ⟨i, hi, hei⟩ := Finset.mem_image.mp he
    refine ⟨⟨i, Finset.mem_filter.mpr ⟨hi, congrArg Prod.fst hei, congrArg Prod.snd hei⟩⟩, ?_⟩
    intro j hj
    obtain ⟨hjA, hj1, hj2⟩ := Finset.mem_filter.mp hj
    simpa only [hj1, hj2] using hcontained j hjA
  have hpartition : A = edges.biUnion edgeFine := by
    ext i
    constructor
    · intro hi
      exact Finset.mem_biUnion.mpr ⟨(U.cover.assign q.val i, U0.cover.assign q.val i),
        Finset.mem_image_of_mem _ hi, Finset.mem_filter.mpr ⟨hi, rfl, rfl⟩⟩
    · intro hi
      obtain ⟨e, he, hie⟩ := Finset.mem_biUnion.mp hi
      exact (Finset.mem_filter.mp hie).1
  have hdisjoint : (edges : Set (iota × iota)).Pairwise
      (fun e f => Disjoint (edgeFine e) (edgeFine f)) := by
    intro e he f hf hef
    apply Finset.disjoint_left.mpr
    intro i hie hif
    obtain ⟨_, hi1, hi2⟩ := Finset.mem_filter.mp hie
    obtain ⟨_, hj1, hj2⟩ := Finset.mem_filter.mp hif
    exact hef (Prod.ext (hi1.symm.trans hj1) (hi2.symm.trans hj2))
  refine ⟨?_, ?_, hmem, hpartition, hdisjoint, ?_⟩
  · intro Q hQ
    let es := edges.filter (fun e => e.1 = Q)
    let H := es.image Prod.snd
    have hinj : Set.InjOn (Prod.snd : iota × iota -> iota) es := by
      intro e he f hf hef
      exact Prod.ext ((Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp hf).2.symm) hef
    have hH : H ⊆ U0.cover.indexSet q.val := by
      intro w hw
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨i, hi, hei⟩ := Finset.mem_image.mp (Finset.mem_filter.mp he).1
      exact congrArg Prod.snd hei ▸ U0.cover.assign_mem q.val hq i (current.active_subset (hA hi))
    have hwit : ∀ w ∈ H, ∃ p q' : E, dist p q' = 1 ∧
        p ∈ (U.cover.tube q.val Q).carrier ∧ q' ∈ (U.cover.tube q.val Q).carrier ∧
        p ∈ (U0.cover.tube q.val w).carrier ∧ q' ∈ (U0.cover.tube q.val w).carrier := by
      intro w hw
      obtain ⟨e, he, hew⟩ := Finset.mem_image.mp hw
      obtain ⟨heE, heQ⟩ := Finset.mem_filter.mp he
      obtain ⟨i, hi⟩ := (hmem e heE).1
      obtain ⟨hiU, hiU0⟩ := (hmem e heE).2 i hi
      rw [heQ] at hiU
      rw [hew] at hiU0
      exact ⟨(current.shading i).toTube.x, (current.shading i).toTube.y,
        (current.shading i).toTube.dist_eq_one,
        hiU (Tube.x_mem_carrier _), hiU (Tube.y_mem_carrier _),
        hiU0 (Tube.x_mem_carrier _), hiU0 (Tube.y_mem_carrier _)⟩
    have hcard := hcount (Tube.gridScale_pos hd M q.val) (Tube.gridScale_le_one hd1 M q.val)
      (U0.cover.indexSet q.val) H (U0.cover.tube q.val) CbaseTw (U.cover.tube q.val Q)
      hH (reg0.parent_line_ed q.val hq) (reg0.parent_ball q.val hq) hwit
    rw [Finset.card_image_of_injOn hinj] at hcard
    exact hcard.trans ((mul_le_mul_left' (le_max_left CbaseTw CworkTw) (K : NNReal)).trans (le_max_right _ _))
  · intro w hw
    let es := edges.filter (fun e => e.2 = w)
    let H := es.image Prod.fst
    have hinj : Set.InjOn (Prod.fst : iota × iota -> iota) es := by
      intro e he f hf hef
      exact Prod.ext hef ((Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp hf).2.symm)
    have hH : H ⊆ U.cover.indexSet q.val := by
      intro Q hQ
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hQ
      obtain ⟨i, hi, hei⟩ := Finset.mem_image.mp (Finset.mem_filter.mp he).1
      exact congrArg Prod.fst hei ▸ U.cover.assign_mem q.val hq i hi
    have hwit : ∀ Q ∈ H, ∃ p q' : E, dist p q' = 1 ∧
        p ∈ (U0.cover.tube q.val w).carrier ∧ q' ∈ (U0.cover.tube q.val w).carrier ∧
        p ∈ (U.cover.tube q.val Q).carrier ∧ q' ∈ (U.cover.tube q.val Q).carrier := by
      intro Q hQ
      obtain ⟨e, he, heQ⟩ := Finset.mem_image.mp hQ
      obtain ⟨heE, hew⟩ := Finset.mem_filter.mp he
      obtain ⟨i, hi⟩ := (hmem e heE).1
      obtain ⟨hiU, hiU0⟩ := (hmem e heE).2 i hi
      rw [heQ] at hiU
      rw [hew] at hiU0
      exact ⟨(current.shading i).toTube.x, (current.shading i).toTube.y,
        (current.shading i).toTube.dist_eq_one,
        hiU0 (Tube.x_mem_carrier _), hiU0 (Tube.y_mem_carrier _),
        hiU (Tube.x_mem_carrier _), hiU (Tube.y_mem_carrier _)⟩
    have hcard := hcount (Tube.gridScale_pos hd M q.val) (Tube.gridScale_le_one hd1 M q.val)
      (U.cover.indexSet q.val) H (U.cover.tube q.val) CworkTw (U0.cover.tube q.val w)
      hH (reg.parent_line_ed q.val hq) (reg.parent_ball q.val hq) hwit
    rw [Finset.card_image_of_injOn hinj] at hcard
    exact hcard.trans ((mul_le_mul_left' (le_max_right CbaseTw CworkTw) (K : NNReal)).trans (le_max_right _ _))
  · exact (Finset.sum_biUnion hdisjoint).symm.trans
      (Finset.sum_congr hpartition.symm (fun _ _ => rfl))

/-- D2a jointly constructs both actual canonical shadings from the two fine
families. The upper shading is allowed to depend on the prescribed lower cut. -/
theorem exists_actual_canonical_induced_shadings_w97
    {iota : Type uI} [DecidableEq iota] {delta : NNReal} (hd : 0 < delta)
    {B : Finset iota} {V : iota -> ShadedTube delta E} {M : Nat} {Ccan : NNReal}
    (U0 : CanonicalProfileNetW87 B (fun i => (V i).toTube) M Ccan)
    (current : RetainedStateW94 B V) (q : Fin (M + 1))
    (F G : Finset iota) (Y Z : iota -> ShadedTube delta E)
    (hF : F ⊆ current.active) (hG : G ⊆ F)
    (hY : ∀ i ∈ F, (Y i).toTube = (current.shading i).toTube)
    (hZ : ∀ i ∈ G, (Z i).toTube = (Y i).toTube ∧ (Z i).shade ⊆ (Y i).shade)
    (hpos : 0 < ∑ i ∈ G, volume (Z i).shade) :
    ∃ (c : NNReal)
      (W Wplus : CanonicalQNodeW87 U0 current.active q ->
        ShadedTube (Tube.gridScale delta M q.val) E),
      0 < c ∧
      (∀ w, (W w).toTube = U0.cover.tube q.val w.val ∧
        (Wplus w).toTube = U0.cover.tube q.val w.val ∧ (Wplus w).shade ⊆ (W w).shade) ∧
      (∀ w, (W w).shade ⊆ ⋃ i ∈ completeFibreW94 F (U0.cover.assign q.val) w.val, (Y i).shade) ∧
      (∀ w, (Wplus w).shade ⊆ ⋃ i ∈ completeFibreW94 G (U0.cover.assign q.val) w.val, (Z i).shade) ∧
      (∀ w, volume (W w).shade = (c : ENNReal) *
        ∑ i ∈ completeFibreW94 F (U0.cover.assign q.val) w.val, volume (Y i).shade) ∧
      (∀ w, volume (Wplus w).shade = (c : ENNReal) *
        ∑ i ∈ completeFibreW94 G (U0.cover.assign q.val) w.val, volume (Z i).shade) ∧
      (0 < ∑ w ∈ canonicalQNodeFinsetW87 U0 current.active q, volume (Wplus w).shade) := by
  let n : NNReal := F.card + 1
  let c : NNReal := n⁻¹
  have hn : 0 < n := by dsimp only [n]; positivity
  have hc : 0 < c := inv_pos.mpr hn
  have hcE : (c : ENNReal) ≠ 0 := (ENNReal.coe_pos.mpr hc).ne'
  let f := fun w : CanonicalQNodeW87 U0 current.active q => completeFibreW94 F (U0.cover.assign q.val) w.val
  let g := fun w : CanonicalQNodeW87 U0 current.active q => completeFibreW94 G (U0.cover.assign q.val) w.val
  let upper := fun w : CanonicalQNodeW87 U0 current.active q => ⋃ i ∈ f w, (Y i).shade
  let lower := fun w : CanonicalQNodeW87 U0 current.active q => ⋃ i ∈ g w, (Z i).shade
  let massF := fun w : CanonicalQNodeW87 U0 current.active q => ∑ i ∈ f w, volume (Y i).shade
  let massG := fun w : CanonicalQNodeW87 U0 current.active q => ∑ i ∈ g w, volume (Z i).shade
  have hgf : ∀ w, g w ⊆ f w := by
    intro w i hi
    exact Finset.mem_filter.mpr ⟨hG (Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2⟩
  have hlowerUpper : ∀ w, lower w ⊆ upper w := by
    intro w x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    exact Set.mem_iUnion₂.mpr ⟨i, hgf w hi, (hZ i (Finset.mem_filter.mp hi).1).2 hxi⟩
  have hupperCarrier : ∀ w, upper w ⊆ (U0.cover.tube q.val w.val).carrier := by
    intro w x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨hiF, hiw⟩ := Finset.mem_filter.mp hi
    have hiB := current.active_subset (hF hiF)
    have hbody : (Y i).toConvexSpaceBody = (V i).toConvexSpaceBody :=
      congrArg Tube.toConvexSpaceBody ((hY i hiF).trans (current.same_tube i (hF hiF)))
    have hbase := U0.cover.le_tube_assign q.val (by omega) i hiB
    have hxY := (Y i).shade_subset hxi
    rw [hbody] at hxY
    exact hiw ▸ hbase hxY
  have hupperMeas : ∀ w, MeasurableSet (upper w) := by
    intro w
    exact Finset.measurableSet_biUnion _ (fun i hi => (Y i).measurableSet_shade)
  have hlowerMeas : ∀ w, MeasurableSet (lower w) := by
    intro w
    exact Finset.measurableSet_biUnion _ (fun i hi => (Z i).measurableSet_shade)
  have hupperFinite : ∀ w, volume (upper w) < ⊤ := by
    intro w
    exact (measure_mono (hupperCarrier w)).trans_lt (U0.cover.tube q.val w.val).toConvexSpaceBody.isCompact.measure_lt_top
  have hlowerFinite : ∀ w, volume (lower w) < ⊤ := fun w =>
    (measure_mono (hlowerUpper w)).trans_lt (hupperFinite w)
  have hmassGF : ∀ w, massG w <= massF w := by
    intro w
    apply le_trans (Finset.sum_le_sum (s := g w) (fun i hi =>
      measure_mono (hZ i (Finset.mem_filter.mp hi).1).2))
    exact Finset.sum_le_sum_of_subset_of_nonneg (hgf w) (fun _ _ _ => bot_le)
  have hbudget : ∀ (H : Finset iota) (T : iota -> ShadedTube delta E), H ⊆ F ->
      (c : ENNReal) * (∑ i ∈ H, volume (T i).shade) <= volume (⋃ i ∈ H, (T i).shade) := by
    intro H T hHF
    let v := volume (⋃ i ∈ H, (T i).shade)
    have hsum : (∑ i ∈ H, volume (T i).shade) <= (n : ENNReal) * v := by
      calc
        _ <= ∑ i ∈ H, v := Finset.sum_le_sum (fun i hi =>
          measure_mono (Set.subset_iUnion₂_of_subset i hi Set.Subset.rfl))
        _ = (H.card : ENNReal) * v := by rw [Finset.sum_const, nsmul_eq_mul]
        _ <= (n : ENNReal) * v := by
          apply mul_le_mul_right'
          change (H.card : ENNReal) <= ((F.card : NNReal) + 1 : NNReal)
          norm_cast
          exact (Finset.card_le_card hHF).trans (Nat.le_succ _)
    calc
      _ <= (c : ENNReal) * ((n : ENNReal) * v) := mul_le_mul_left' hsum _
      _ = v := by
        dsimp only [c]
        rw [ENNReal.coe_inv hn.ne', ← mul_assoc,
          ENNReal.inv_mul_cancel (ENNReal.coe_pos.mpr hn).ne' ENNReal.coe_ne_top, one_mul]
  have hcut : ∀ w : CanonicalQNodeW87 U0 current.active q,
      ∃ S T : Set E, S ⊆ upper w ∧ T ⊆ lower w ∧ T ⊆ S ∧
        MeasurableSet S ∧ MeasurableSet T ∧ volume S = (c : ENNReal) * massF w ∧
          volume T = (c : ENNReal) * massG w := by
    intro w
    have hGbudget : (c : ENNReal) * massG w <= volume (lower w) :=
      hbudget (g w) Z (fun i hi => hG (Finset.mem_filter.mp hi).1)
    have hFbudget : (c : ENNReal) * massF w <= volume (upper w) :=
      hbudget (f w) Y (Finset.filter_subset _ _)
    obtain ⟨T, hTlower, hTmeas, hTvol⟩ :=
      exists_volume_cut_w97 (lower w) (hlowerMeas w) (hlowerFinite w) _ hGbudget
    have hTupper : T ⊆ upper w := hTlower.trans (hlowerUpper w)
    have hTfinite : volume T ≠ ⊤ := ((measure_mono hTupper).trans_lt (hupperFinite w)).ne
    have hGF : (c : ENNReal) * massG w <= (c : ENNReal) * massF w := mul_le_mul_left' (hmassGF w) _
    have hdiff : (c : ENNReal) * massF w - (c : ENNReal) * massG w <= volume (upper w \ T) := by
      rw [measure_sdiff hTupper hTmeas.nullMeasurableSet hTfinite, hTvol]
      exact tsub_le_tsub_right hFbudget _
    obtain ⟨D, hDsub, hDmeas, hDvol⟩ := exists_volume_cut_w97 (upper w \ T)
      ((hupperMeas w).diff hTmeas) ((measure_mono Set.diff_subset).trans_lt (hupperFinite w)) _ hdiff
    refine ⟨T ∪ D, T, Set.union_subset hTupper (hDsub.trans Set.diff_subset), hTlower,
      Set.subset_union_left, hTmeas.union hDmeas, hTmeas, ?_, hTvol⟩
    have hdisj : Disjoint T D := Set.disjoint_left.mpr (fun x hxT hxD => (hDsub hxD).2 hxT)
    rw [measure_union hdisj hDmeas, hTvol, hDvol, add_comm, tsub_add_cancel_of_le hGF]
  choose S T hS hT hTS hSmeas hTmeas hSvol hTvol using hcut
  let W : CanonicalQNodeW87 U0 current.active q -> ShadedTube (Tube.gridScale delta M q.val) E :=
    fun w => { toTube := U0.cover.tube q.val w.val
               shade := S w
               measurableSet_shade := hSmeas w
               shade_subset := (hS w).trans (hupperCarrier w) }
  let Wplus : CanonicalQNodeW87 U0 current.active q -> ShadedTube (Tube.gridScale delta M q.val) E :=
    fun w => { toTube := U0.cover.tube q.val w.val
               shade := T w
               measurableSet_shade := hTmeas w
               shade_subset := ((hT w).trans (hlowerUpper w)).trans (hupperCarrier w) }
  refine ⟨c, W, Wplus, hc, fun w => ⟨rfl, rfl, hTS w⟩, hS, hT, hSvol, hTvol, ?_⟩
  have hmaps : ∀ i ∈ G, U0.cover.assign q.val i ∈ canonicalAncestorFamilyW87 U0 current.active q := by
    intro i hi
    exact Finset.mem_image_of_mem _ (hF (hG hi))
  have htotal : (∑ w ∈ canonicalQNodeFinsetW87 U0 current.active q, volume (Wplus w).shade) =
      (c : ENNReal) * ∑ i ∈ G, volume (Z i).shade := by
    calc
      _ = ∑ w ∈ canonicalQNodeFinsetW87 U0 current.active q, (c : ENNReal) * massG w :=
        Finset.sum_congr rfl (fun w hw => hTvol w)
      _ = (c : ENNReal) * ∑ w ∈ canonicalQNodeFinsetW87 U0 current.active q, massG w := by
        rw [Finset.mul_sum]
      _ = _ := by
        congr 1
        dsimp only [canonicalQNodeFinsetW87, massG, g, completeFibreW94]
        change (∑ w ∈ (canonicalAncestorFamilyW87 U0 current.active q).attach,
          ∑ i ∈ G.filter (fun i => U0.cover.assign q.val i = w.val), volume (Z i).shade) = _
        exact (Finset.sum_attach (canonicalAncestorFamilyW87 U0 current.active q)
          (fun w => ∑ i ∈ G.filter (fun i => U0.cover.assign q.val i = w), volume (Z i).shade)).trans
          (Finset.sum_fiberwise_of_maps_to hmaps (fun i => volume (Z i).shade))
  rw [htotal]
  exact ENNReal.mul_pos hcE hpos.ne'

/-- D2b: exact affine pullback of every actual Drop shading, followed by one
shared proportional fine cut. No representative deletion changes the old geometry. -/
theorem exists_actual_trial_drop_fine_lift_w97
    {iota : Type uI} [DecidableEq iota] {delta : NNReal}
    {A : Finset iota} {Y : iota -> ShadedTube delta E} {M : Nat} {Ccan Ctw Ccell : NNReal}
    {U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan}
    (Uext : CanonicalProfileNetW87 A (fun i => (Y i).toTube) (M * M) Ccan)
    {p : Params} {BF loss : NNReal} (block : ActualSourceDividingBlockW95 U p BF)
    (selections : ActualSameMassSelectionsW95 block loss)
    (xi : Fin (p.N + 1) -> Real) (gamma : Real)
    (Rnorm Cext Cnorm CtwNorm CcellNorm : NNReal)
    (aux : AuxiliaryHalfEtaThresholdsW97.{uE, uI} (E := E) p xi gamma CtwNorm CcellNorm M)
    (calls : ActualEligibleTrialCallsW97 Uext block selections xi gamma
      Rnorm Cext Cnorm CtwNorm CcellNorm aux)
    (drops : ∀ R (hR : R ∈ actualEligibleThetaParentsW97 selections Cext (aux.inner block.label)),
      DetailedTrialDropW94 (calls.normalization R hR).cells p.ε
        (p.η (block.label.val + 1) / 2) (aux.Ktr block.label))
    (hd : 0 < delta) (hd1 : delta < 1)
    (hM : 1 <= M) (hA : A.Nonempty)
    (reg : SourceRegularizedWorkingTowerW95 U Ctw Ccell)
    (hpos : 0 < ∑ i ∈ selections.fineFamily, volume (selections.fineShading i).shade) :
    ∃ (middlePlus Fdagger : Finset iota)
      (Zplus : iota -> ShadedTube (Tube.gridScale delta M block.b.val) E)
      (Ydagger : iota -> ShadedTube delta E),
      middlePlus.Nonempty ∧ middlePlus ⊆ selections.secondFamily ∧
      (∀ Q ∈ middlePlus, (Zplus Q).toTube = U.cover.tube block.b.val Q ∧
        (Zplus Q).shade ⊆ (selections.secondShading Q).shade) ∧
      (∀ R (hR : R ∈ actualEligibleThetaParentsW97 selections Cext (aux.inner block.label)),
        ∀ Q ∈ (drops R hR).Fplus,
          0 < volume ((drops R hR).Yplus Q).shade -> Q ∈ middlePlus ∧
          (Zplus Q).shade = (actualSecondAmbientW97 selections Q).shade ∩
            ((U.cover.tube block.a.val R).rescaleMap (Rnorm : Real)) ⁻¹'
              ((drops R hR).Yplus Q).shade) ∧
      (∀ Q ∈ middlePlus, ∃ R,
        ∃ hR : R ∈ actualEligibleThetaParentsW97 selections Cext (aux.inner block.label),
          Q ∈ (drops R hR).Fplus ∧ 0 < volume ((drops R hR).Yplus Q).shade ∧
          volume (Zplus Q).shade = ((calls.normalization R hR).jacobian : ENNReal)⁻¹ *
            volume ((drops R hR).Yplus Q).shade) ∧
      Fdagger = selections.fineFamily.filter (fun i => U.cover.assign block.b.val i ∈ middlePlus) ∧
      Fdagger.Nonempty ∧ Fdagger ⊆ selections.fineFamily ∧
      Fdagger.image (U.cover.assign block.b.val) = middlePlus ∧
      (∀ i ∈ Fdagger, (Ydagger i).toTube = (selections.fineShading i).toTube ∧
        (Ydagger i).shade ⊆ (selections.fineShading i).shade) ∧
      (∀ Q ∈ middlePlus,
        (∑ i ∈ completeFibreW94 Fdagger (U.cover.assign block.b.val) Q, volume (Ydagger i).shade) =
          (selections.commonMass : ENNReal)⁻¹ * volume (Zplus Q).shade) ∧
      (1 / 2 : ENNReal) * trialRetainedFractionW94
          (Tube.gridScale delta M block.b.val / Tube.gridScale delta M block.a.val) (aux.Ktr block.label) *
        (∑ i ∈ selections.fineFamily, volume (selections.fineShading i).shade) <=
          ∑ i ∈ Fdagger, volume (Ydagger i).shade := by
  let J := actualEligibleThetaParentsW97 selections Cext (aux.inner block.label)
  let ambient := actualSecondAmbientW97 selections
  let Fibre := fun R => actualDescendantsW95 A U.cover.assign block.a.val block.b.val R
  let kappa := {R : iota // R ∈ J}
  let norm := fun k : kappa => calls.normalization k.val k.property
  let D := fun k : kappa => drops k.val k.property
  let phi := fun k : kappa => (U.cover.tube block.a.val k.val).rescaleMap (Rnorm : Real)
  let positive := fun k : kappa => (D k).Fplus.filter (fun Q => 0 < volume ((D k).Yplus Q).shade)
  let middlePlus := J.attach.biUnion positive
  let cut := fun (k : kappa) Q => (ambient Q).shade ∩ (phi k) ⁻¹' ((D k).Yplus Q).shade
  have ha : block.a.val <= M := Nat.le_of_lt_succ block.a.isLt
  have hb : block.b.val <= M := Nat.le_of_lt_succ block.b.isLt
  have hsecondSubset : selections.secondFamily ⊆ U.cover.indexSet block.b.val :=
    selections.second.child_subset.trans selections.second.active_subset
  have hsecondTube : ∀ Q ∈ selections.secondFamily,
      (selections.secondShading Q).toTube = U.cover.tube block.b.val Q := by
    intro Q hQ
    exact (selections.second.child_shade Q hQ).1.trans
      (zeroExtend_toTube selections.middle_tube Q)
  have hambientTube : ∀ Q, (ambient Q).toTube = U.cover.tube block.b.val Q :=
    zeroExtend_toTube hsecondTube
  have hparent : ∀ R, ∀ Q ∈ Fibre R, selections.coarseAssign Q = R := by
    intro R Q hQ
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQ
    obtain ⟨hiA, hiR⟩ := Finset.mem_filter.mp hi
    exact (selections.parent_compatibility i hiA).trans hiR
  have hpositiveFibre : ∀ k : kappa, positive k ⊆ Fibre k.val := fun k =>
    (Finset.filter_subset _ _).trans (D k).Fplus_subset
  have hcutMeas : ∀ (k : kappa) Q, MeasurableSet (cut k Q) := by
    intro k Q
    have hcontinuous : Continuous (phi k) := by
      rw [← AffineMap.continuous_linear_iff]
      exact (phi k).linear.continuous_of_finiteDimensional
    exact (ambient Q).measurableSet_shade.inter
      (((D k).Yplus Q).measurableSet_shade.preimage hcontinuous.measurable)
  have hcutImage : ∀ (k : kappa) Q, Q ∈ (D k).Fplus ->
      phi k '' cut k Q = ((D k).Yplus Q).shade := by
    intro k Q hQ
    have hsub := (D k).subshade Q hQ
    rw [(norm k).image_shade Q ((D k).Fplus_subset hQ)] at hsub
    exact (Set.image_inter_preimage _ _ _).trans (Set.inter_eq_right.mpr hsub)
  have hcutVolume : ∀ (k : kappa) Q, Q ∈ (D k).Fplus ->
      volume (cut k Q) = ((norm k).jacobian : ENNReal)⁻¹ * volume ((D k).Yplus Q).shade := by
    intro k Q hQ
    have heq := (norm k).volume_image (cut k Q) (hcutMeas k Q)
    rw [hcutImage k Q hQ] at heq
    rw [heq, ← mul_assoc, ENNReal.inv_mul_cancel
      (ENNReal.coe_pos.mpr (norm k).jacobian_pos).ne' ENNReal.coe_ne_top, one_mul]
  have hpositiveSecond : ∀ k : kappa, positive k ⊆ selections.secondFamily := by
    intro k Q hQ
    obtain ⟨hQD, hQpos⟩ := Finset.mem_filter.mp hQ
    by_contra hQsecond
    have hzero : (ambient Q).shade = ∅ := zeroExtend_shade_of_not_mem hQsecond
    have hnormzero := (norm k).image_shade Q ((D k).Fplus_subset hQD)
    rw [hzero, Set.image_empty] at hnormzero
    have hdropzero : ((D k).Yplus Q).shade = ∅ := Set.eq_empty_iff_forall_notMem.mpr
      (fun x hx => by
        have hh : x ∈ ((norm k).normalized Q).shade := (D k).subshade Q hQD hx
        rw [hnormzero] at hh
        exact hh)
    simpa only [hdropzero, measure_empty, lt_self_iff_false] using hQpos
  have hmiddleSubset : middlePlus ⊆ selections.secondFamily := by
    intro Q hQ
    obtain ⟨k, hk, hQk⟩ := Finset.mem_biUnion.mp hQ
    exact hpositiveSecond k hQk
  have hwitness : ∀ Q ∈ middlePlus, ∃ k : kappa, Q ∈ positive k := by
    intro Q hQ
    obtain ⟨k, hk, hQk⟩ := Finset.mem_biUnion.mp hQ
    exact ⟨k, hQk⟩
  let owner := fun Q (hQ : Q ∈ middlePlus) => (hwitness Q hQ).choose
  have howner : ∀ Q (hQ : Q ∈ middlePlus), Q ∈ positive (owner Q hQ) :=
    fun Q hQ => (hwitness Q hQ).choose_spec
  have hunique : ∀ (k k' : kappa) Q, Q ∈ positive k -> Q ∈ positive k' -> k = k' := by
    intro k k' Q hQ hQ'
    apply Subtype.ext
    exact (hparent k.val Q (hpositiveFibre k hQ)).symm.trans
      (hparent k'.val Q (hpositiveFibre k' hQ'))
  let Zplus : iota -> ShadedTube (Tube.gridScale delta M block.b.val) E := fun Q =>
    { toTube := U.cover.tube block.b.val Q
      shade := if hQ : Q ∈ middlePlus then cut (owner Q hQ) Q else ∅
      measurableSet_shade := by
        split
        · exact hcutMeas _ _
        · exact MeasurableSet.empty
      shade_subset := by
        split
        · intro x hx
          have hcarrier := (ambient Q).shade_subset hx.1
          simpa only [show (ambient Q).carrier = (U.cover.tube block.b.val Q).carrier from
            congrArg (fun T => T.carrier) (hambientTube Q)] using hcarrier
        · exact Set.empty_subset _ }
  have hZcut : ∀ (k : kappa) Q, Q ∈ positive k -> (Zplus Q).shade = cut k Q := by
    intro k Q hQ
    have hQmiddle : Q ∈ middlePlus := Finset.mem_biUnion.mpr ⟨k, Finset.mem_attach _ k, hQ⟩
    dsimp only [Zplus]
    rw [dif_pos hQmiddle, hunique (owner Q hQmiddle) k Q (howner Q hQmiddle) hQ]
  have hZsub : ∀ Q ∈ middlePlus, (Zplus Q).toTube = U.cover.tube block.b.val Q ∧
      (Zplus Q).shade ⊆ (selections.secondShading Q).shade := by
    intro Q hQ
    refine ⟨rfl, ?_⟩
    rw [hZcut (owner Q hQ) Q (howner Q hQ)]
    intro x hx
    have hshade : (ambient Q).shade = (selections.secondShading Q).shade :=
      zeroExtend_shade_of_mem (hmiddleSubset hQ)
    exact hshade ▸ hx.1
  have hZvolume : ∀ (k : kappa) Q, Q ∈ positive k ->
      volume (Zplus Q).shade = ((norm k).jacobian : ENNReal)⁻¹ * volume ((D k).Yplus Q).shade := by
    intro k Q hQ
    rw [hZcut k Q hQ]
    exact hcutVolume k Q (Finset.mem_filter.mp hQ).1
  have hdisjoint : (J.attach : Set kappa).Pairwise (fun k k' => Disjoint (positive k) (positive k')) := by
    intro k hk k' hk' hkk'
    exact Finset.disjoint_left.mpr (fun Q hQ hQ' => hkk' (hunique k k' Q hQ hQ'))
  let d := Tube.gridScale delta M block.b.val / Tube.gridScale delta M block.a.val
  let retained := trialRetainedFractionW94 d (aux.Ktr block.label)
  have hdpos : 0 < d := div_pos (Tube.gridScale_pos hd M block.b.val) (Tube.gridScale_pos hd M block.a.val)
  have hdle : d <= 1 := (div_le_one (Tube.gridScale_pos hd M block.a.val)).mpr
    (Tube.gridScale_antitone hd hd1.le M block.a_lt_b.le)
  have hretainedPos : 0 < retained := by
    apply ENNReal.ofReal_pos.mpr
    apply Real.rpow_pos_of_pos
    have hlog : 0 <= Real.log (1 / (d : Real)) := Real.log_nonneg
      ((one_le_div (show (0 : Real) < d by exact_mod_cast hdpos)).mpr (by exact_mod_cast hdle))
    linarith only [hlog]
  have hlocalMass : ∀ k : kappa,
      retained * (∑ Q ∈ Fibre k.val, volume (ambient Q).shade) <=
        ∑ Q ∈ positive k, volume (Zplus Q).shade := by
    intro k
    have himageMass : (∑ Q ∈ Fibre k.val, volume ((norm k).normalized Q).shade) =
        ((norm k).jacobian : ENNReal) * ∑ Q ∈ Fibre k.val, volume (ambient Q).shade := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro Q hQ
      rw [(norm k).image_shade Q hQ]
      exact (norm k).volume_image _ (ambient Q).measurableSet_shade
    have hsumDrop : (∑ Q ∈ positive k, volume ((D k).Yplus Q).shade) =
        ∑ Q ∈ (D k).Fplus, volume ((D k).Yplus Q).shade := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro Q hQ hQnot
      have hn : ¬ 0 < volume ((D k).Yplus Q).shade := by
        intro hh
        exact hQnot (Finset.mem_filter.mpr ⟨hQ, hh⟩)
      exact le_antisymm (not_lt.mp hn) bot_le
    have hdrop := (D k).mass_retention
    rw [himageMass] at hdrop
    calc
      _ = ((norm k).jacobian : ENNReal)⁻¹ *
          (retained * (((norm k).jacobian : ENNReal) * ∑ Q ∈ Fibre k.val, volume (ambient Q).shade)) := by
        rw [mul_left_comm retained, ← mul_assoc, ENNReal.inv_mul_cancel
          (ENNReal.coe_pos.mpr (norm k).jacobian_pos).ne' ENNReal.coe_ne_top, one_mul]
      _ <= ((norm k).jacobian : ENNReal)⁻¹ * ∑ Q ∈ (D k).Fplus, volume ((D k).Yplus Q).shade :=
        mul_le_mul_left' hdrop _
      _ = ((norm k).jacobian : ENNReal)⁻¹ * ∑ Q ∈ positive k, volume ((D k).Yplus Q).shade := by rw [hsumDrop]
      _ = ∑ Q ∈ positive k, volume (Zplus Q).shade := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun Q hQ => (hZvolume k Q hQ).symm)
  have hmiddleMass : (1 / 2 : ENNReal) * retained *
      (∑ Q ∈ U.cover.indexSet block.b.val, volume (ambient Q).shade) <=
        ∑ Q ∈ middlePlus, volume (Zplus Q).shade := by
    calc
      _ = retained * ((1 / 2 : ENNReal) * ∑ Q ∈ U.cover.indexSet block.b.val, volume (ambient Q).shade) := by ring
      _ <= retained * ∑ R ∈ J, ∑ Q ∈ Fibre R, volume (ambient Q).shade := mul_le_mul_left' calls.mass_retention _
      _ = ∑ k ∈ J.attach, retained * ∑ Q ∈ Fibre k.val, volume (ambient Q).shade := by
        rw [Finset.mul_sum]
        exact (Finset.sum_attach J (fun R => retained * ∑ Q ∈ Fibre R, volume (ambient Q).shade)).symm
      _ <= ∑ k ∈ J.attach, ∑ Q ∈ positive k, volume (Zplus Q).shade :=
        Finset.sum_le_sum (fun k hk => hlocalMass k)
      _ = _ := (Finset.sum_biUnion hdisjoint).symm
  have hcommon0 : (selections.commonMass : ENNReal) ≠ 0 :=
    (ENNReal.coe_pos.mpr selections.commonMass_pos).ne'
  have hinduced : ∀ Q ∈ selections.secondFamily,
      volume (selections.secondShading Q).shade = (selections.commonMass : ENNReal) *
        ∑ i ∈ completeFibreW94 selections.fineFamily (U.cover.assign block.b.val) Q,
          volume (selections.fineShading i).shade := by
    intro Q hQ
    rw [selections.weighted_cut Q hQ, ← mul_assoc,
      ENNReal.mul_inv_cancel hcommon0 ENNReal.coe_ne_top, one_mul]
  have hfineMaps : ∀ i ∈ selections.fineFamily, U.cover.assign block.b.val i ∈ selections.secondFamily := by
    intro i hi
    rw [← selections.fine_image]
    exact Finset.mem_image_of_mem _ hi
  have hsecondMass : (∑ Q ∈ selections.secondFamily, volume (selections.secondShading Q).shade) =
      (selections.commonMass : ENNReal) * ∑ i ∈ selections.fineFamily, volume (selections.fineShading i).shade := by
    calc
      _ = ∑ Q ∈ selections.secondFamily, (selections.commonMass : ENNReal) *
          ∑ i ∈ completeFibreW94 selections.fineFamily (U.cover.assign block.b.val) Q,
            volume (selections.fineShading i).shade := Finset.sum_congr rfl hinduced
      _ = _ := by
        rw [← Finset.mul_sum]
        congr 1
        exact Finset.sum_fiberwise_of_maps_to hfineMaps (fun i => volume (selections.fineShading i).shade)
  have hambientMass : (∑ Q ∈ U.cover.indexSet block.b.val, volume (ambient Q).shade) =
      ∑ Q ∈ selections.secondFamily, volume (selections.secondShading Q).shade := by
    exact sum_volume_shade_zeroExtend_of_subset hsecondSubset _ _
  have hmassPos : 0 < ∑ Q ∈ middlePlus, volume (Zplus Q).shade := by
    apply lt_of_lt_of_le _ hmiddleMass
    rw [hambientMass, hsecondMass]
    exact ENNReal.mul_pos (ENNReal.mul_pos (by norm_num : (1 / 2 : ENNReal) ≠ 0)
      hretainedPos.ne').ne' (ENNReal.mul_pos hcommon0 hpos.ne').ne'
  have hmiddleNonempty : middlePlus.Nonempty := by
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.sum_empty] at hmassPos
    exact (lt_irrefl _ hmassPos)
  obtain ⟨Fdagger, Ydagger, hFdagger, hFnonempty, hFsubset, hFimage, hYdagger,
      hFfibres, hcutMass, hcutEach⟩ := exists_same_proportional_fine_cut_w97
        selections.fineFamily selections.fineShading selections.secondFamily middlePlus
        selections.secondShading Zplus (U.cover.assign block.b.val)
        hmiddleNonempty hmiddleSubset selections.fine_image selections.commonMass selections.commonMass_pos
        hinduced (fun Q hQ => ⟨(hZsub Q hQ).1.trans (hsecondTube Q (hmiddleSubset hQ)).symm, (hZsub Q hQ).2⟩)
  have hfinalMass : (∑ i ∈ Fdagger, volume (Ydagger i).shade) =
      (selections.commonMass : ENNReal)⁻¹ * ∑ Q ∈ middlePlus, volume (Zplus Q).shade := by
    have hmaps : ∀ i ∈ Fdagger, U.cover.assign block.b.val i ∈ middlePlus := by
      intro i hi
      rw [← hFimage]
      exact Finset.mem_image_of_mem _ hi
    calc
      _ = ∑ Q ∈ middlePlus, ∑ i ∈ completeFibreW94 Fdagger (U.cover.assign block.b.val) Q,
          volume (Ydagger i).shade := (Finset.sum_fiberwise_of_maps_to hmaps (fun i => volume (Ydagger i).shade)).symm
      _ = ∑ Q ∈ middlePlus, (selections.commonMass : ENNReal)⁻¹ * volume (Zplus Q).shade :=
        Finset.sum_congr rfl hcutMass
      _ = _ := (Finset.mul_sum ..).symm
  refine ⟨middlePlus, Fdagger, Zplus, Ydagger, hmiddleNonempty, hmiddleSubset, hZsub,
    ?_, ?_, hFdagger, hFnonempty, hFsubset, hFimage, hYdagger, hcutMass, ?_⟩
  · intro R hR Q hQ hQpos
    let k : kappa := ⟨R, hR⟩
    have hQpositive : Q ∈ positive k := Finset.mem_filter.mpr ⟨hQ, hQpos⟩
    exact ⟨Finset.mem_biUnion.mpr ⟨k, Finset.mem_attach _ k, hQpositive⟩, hZcut k Q hQpositive⟩
  · intro Q hQ
    let k := owner Q hQ
    have hQk := howner Q hQ
    exact ⟨k.val, k.property, (Finset.mem_filter.mp hQk).1,
      (Finset.mem_filter.mp hQk).2, hZvolume k Q hQk⟩
  · rw [hfinalMass]
    have hpaid := mul_le_mul_left' hmiddleMass (selections.commonMass : ENNReal)⁻¹
    rw [hambientMass, hsecondMass] at hpaid
    calc
      _ = (selections.commonMass : ENNReal)⁻¹ *
          ((1 / 2 : ENNReal) * retained * ((selections.commonMass : ENNReal) *
            ∑ i ∈ selections.fineFamily, volume (selections.fineShading i).shade)) := by
        calc
          _ = ((selections.commonMass : ENNReal)⁻¹ * selections.commonMass) *
              ((1 / 2 : ENNReal) * retained * ∑ i ∈ selections.fineFamily, volume (selections.fineShading i).shade) := by
            rw [ENNReal.inv_mul_cancel hcommon0 ENNReal.coe_ne_top, one_mul]
          _ = _ := by ring
      _ <= _ := hpaid

end

end Kakeya.ml1Boot.TrialRestartW94
