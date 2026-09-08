module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceWindowTrialW98
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceCanonicalTransportW97
public import Kakeya.ConvexBody.DilateWitness

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

/-- Full finite segments and round caps, not merely infinite-axis proximity. -/
theorem exists_common_fine_finite_segment_lift_w101 :
    ∃ Lgeom : NNReal, 2 <= Lgeom ∧
      ∀ {delta tau sigma : NNReal}, 0 < delta -> delta <= tau -> tau <= sigma -> sigma <= 1 ->
      ∀ (fine : Tube delta E) (old canonical : Tube tau E) (parent : Tube sigma E),
        fine.toConvexSpaceBody <= old.toConvexSpaceBody ->
        fine.toConvexSpaceBody <= canonical.toConvexSpaceBody ->
        old.toConvexSpaceBody <= parent.toConvexSpaceBody ->
        canonical.toConvexSpaceBody <= (parent.rescale (Lgeom * sigma)).toConvexSpaceBody := by
  refine ⟨5, by norm_num, ?_⟩
  intro delta tau sigma hd hdt hts hs fine old canonical parent hfo hfc hop
  have hreverse := Tube.le_rescale_of_subset fine canonical hfc
  have hfp : fine.toConvexSpaceBody <= parent.toConvexSpaceBody := hfo.trans hop
  intro x hx
  have hxFine := hreverse hx
  change x ∈ (fine.rescale (4 * tau)).carrier at hxFine
  rw [(fine.rescale (4 * tau)).carrier_eq] at hxFine
  obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp hxFine
  have hpFine : p ∈ fine.carrier := by
    rw [fine.carrier_eq]
    exact Set.mem_iUnion₂.mpr ⟨p, hp, Metric.mem_closedBall_self delta.coe_nonneg⟩
  have hpParent : p ∈ parent.carrier := hfp hpFine
  rw [parent.carrier_eq] at hpParent
  obtain ⟨q, hq, hpq⟩ := Set.mem_iUnion₂.mp hpParent
  change x ∈ (parent.rescale (5 * sigma)).carrier
  rw [(parent.rescale (5 * sigma)).carrier_eq]
  refine Set.mem_iUnion₂.mpr ⟨q, hq, Metric.mem_closedBall.mpr ?_⟩
  have ht : (tau : Real) <= sigma := by exact_mod_cast hts
  have hxp' := Metric.mem_closedBall.mp hxp
  have hpq' := Metric.mem_closedBall.mp hpq
  push_cast at hxp' ⊢
  calc
    dist x q <= dist x p + dist p q := dist_triangle x p q
    _ <= 4 * (tau : Real) + sigma := add_le_add hxp' hpq'
    _ <= 5 * (sigma : Real) := by linarith

/-- The normalized old-parent assignment is the actual extended-tree
ancestor of every fine witness. -/
theorem actual_normalized_old_parent_thread_w101
    {iota : Type uI} [DecidableEq iota] {delta : NNReal}
    {A : Finset iota} {Y : iota -> ShadedTube delta E} {M : Nat} {Ccan : NNReal}
    (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan)
    (Uext : CanonicalProfileNetW87 A (fun i => (Y i).toTube) (M * M) Ccan)
    (restriction : VisibleExtendedRestrictionW97 U Uext)
    (a b : Nat) (hab : a < b) (hb : b <= M)
    (R : iota) (Z : iota -> ShadedTube (Tube.gridScale delta M b) E)
    {Rnorm Cext Cnorm CtwNorm CcellNorm : NNReal}
    (normalization : ActualAssignedUnitNormalizationW97 U Uext a b R Z
      Rnorm Cext Cnorm CtwNorm CcellNorm)
    (l : Nat) (hl : l <= M) :
    ∀ i ∈ A,
      normalization.cells.assign l (U.cover.assign b i) =
        Uext.cover.assign (quotientGridIndexW97 M a b l) i ∧
      (Y i).toConvexSpaceBody <=
        (Uext.cover.tube (quotientGridIndexW97 M a b l)
          (normalization.cells.assign l (U.cover.assign b i))).toConvexSpaceBody := by
  have hcb : quotientGridIndexW97 M a b l <= b * M := by
    unfold quotientGridIndexW97
    calc
      _ <= a * M + (b - a) * M := Nat.add_le_add_left (Nat.mul_le_mul_left _ hl) _
      _ = b * M := by rw [← Nat.add_mul, Nat.add_sub_of_le hab.le]
  have hbM : b * M <= M * M := Nat.mul_le_mul_right M hb
  intro i hi
  have hassign : normalization.cells.assign l (U.cover.assign b i) =
      Uext.cover.assign (quotientGridIndexW97 M a b l) i := by
    rw [normalization.assign_eq l hl, restriction.assign b hb]
    have hclass : (Tube.coverClass A (Uext.cover.toChain.assign (b * M))
        (Uext.cover.assign (b * M) i)).Nonempty :=
      ⟨i, by simp only [Tube.coverClass, Finset.mem_filter]; exact ⟨hi, rfl⟩⟩
    rw [Kakeya.ML2Reduction.coarseNode, dif_pos hclass]
    have hmem := hclass.choose_spec
    simp only [Tube.coverClass, Finset.mem_filter] at hmem
    exact Uext.cover.assign_eq_of_le hcb hbM hmem.1 hi hmem.2
  refine ⟨hassign, ?_⟩
  rw [hassign]
  exact Uext.cover.le_tube_assign _ (hcb.trans hbM) i hi

/-- An actual Window level supplies the physical parent tube and its full
canonical containment at the source working scale. -/
theorem actual_window_canonical_parent_containment_w101
    {iota : Type uI} [DecidableEq iota] {delta : NNReal}
    {B : Finset iota} {V : iota -> ShadedTube delta E} {M : Nat} {Ccan Cwork : NNReal}
    (U0 : CanonicalProfileNetW87 B (fun i => (V i).toTube) M Ccan)
    (current : RetainedStateW94 B V) (A : Finset iota)
    (U : CanonicalProfileNetW87 A (fun i => (current.shading i).toTube) M Cwork)
    (Uext : CanonicalProfileNetW87 A (fun i => (current.shading i).toTube) (M * M) Cwork)
    (restriction : VisibleExtendedRestrictionW97 U Uext)
    (hA : A ⊆ current.active) (hM : 1 <= M) (hd : 0 < delta) (hd1 : delta < 1)
    (a b : Fin (M + 1)) (hab : a.val < b.val)
    (R : iota) (Z : iota -> ShadedTube (Tube.gridScale delta M b.val) E)
    {Rnorm Cext Cnorm CtwNorm CcellNorm : NNReal}
    (normalization : ActualAssignedUnitNormalizationW97 U Uext a.val b.val R Z
      Rnorm Cext Cnorm CtwNorm CcellNorm)
    {epsilon zeta : Real} {Ktr : Nat}
    (drop : WindowDetailedTrialDropW98 normalization.cells epsilon zeta Ktr) :
    ∀ i ∈ A,
      (U0.cover.tube b.val (U0.cover.assign b.val i)).toConvexSpaceBody <=
        ((Uext.cover.tube (quotientGridIndexW97 M a.val b.val drop.level.val)
          (normalization.cells.assign drop.level.val (U.cover.assign b.val i))).rescale
            (5 * (Tube.gridScale delta M a.val *
              Tube.gridScale (Tube.gridScale delta M b.val / Tube.gridScale delta M a.val)
                M drop.level.val))).toConvexSpaceBody := by
  have hb : b.val <= M := Nat.le_of_lt_succ b.isLt
  have hl : drop.level.val <= M := Nat.le_of_lt_succ drop.level.isLt
  obtain ⟨_, _, hbounds, _, hscales⟩ := quotient_grid_index_w97 M a.val b.val hM hab hb delta hd hd1
  have hscale := hscales drop.level.val hl
  change Tube.gridScale delta (M * M) (quotientGridIndexW97 M a.val b.val drop.level.val) =
    Tube.gridScale delta M a.val *
      Tube.gridScale (Tube.gridScale delta M b.val / Tube.gridScale delta M a.val) M drop.level.val
    at hscale
  have htausigma : Tube.gridScale delta M b.val <=
      Tube.gridScale delta (M * M) (quotientGridIndexW97 M a.val b.val drop.level.val) := by
    exact (restriction.radius b.val hb).le.trans
      (Tube.gridScale_antitone hd hd1.le (M * M) (hbounds drop.level.val hl).2.1)
  have hdtau : delta <= Tube.gridScale delta M b.val := by
    simpa only [Tube.gridScale_self delta hM] using Tube.gridScale_antitone hd hd1.le M hb
  intro i hi
  have hparent := (actual_normalized_old_parent_thread_w101 U Uext restriction
    a.val b.val hab hb R Z normalization drop.level.val hl i hi).2
  have hcanonical : (current.shading i).toConvexSpaceBody <=
      (U0.cover.tube b.val (U0.cover.assign b.val i)).toConvexSpaceBody := by
    rw [show (current.shading i).toConvexSpaceBody = (V i).toConvexSpaceBody from
      congrArg Tube.toConvexSpaceBody (current.same_tube i (hA hi))]
    exact U0.cover.le_tube_assign b.val hb i (current.active_subset (hA hi))
  apply (Tube.le_rescale_of_subset (current.shading i).toTube _ hcanonical).trans
  apply Tube.rescale_le_rescale_of_body_le (current.shading i).toTube _ _ _ hparent
  · exact hdtau.trans (by nlinarith)
  · rw [← hscale]
    nlinarith

/-- Conflicts quantify over ALL original U0 nodes, independently of shading. -/
def canonicalParentConflictW101
    {iota : Type uI} [DecidableEq iota] {delta sigma : NNReal}
    {B current : Finset iota} {T : iota -> Tube delta E} {M : Nat} {Ccan : NNReal}
    (U0 : CanonicalProfileNetW87 B T M Ccan) (q : Fin (M + 1))
    (parent : iota -> Tube sigma E) (Lgeom : NNReal) (P Q : iota) : Prop :=
  P ≠ Q ∧ ∃ test : Tube (Lgeom * sigma) E,
    (∃ w ∈ canonicalQNodeFinsetW87 U0 current q,
      (U0.cover.tube q.val w.val).toConvexSpaceBody <= (parent P |>.rescale (Lgeom * sigma)).toConvexSpaceBody ∧
      (U0.cover.tube q.val w.val).toConvexSpaceBody <= test.toConvexSpaceBody) ∧
    (∃ w ∈ canonicalQNodeFinsetW87 U0 current q,
      (U0.cover.tube q.val w.val).toConvexSpaceBody <= (parent Q |>.rescale (Lgeom * sigma)).toConvexSpaceBody ∧
      (U0.cover.tube q.val w.val).toConvexSpaceBody <= test.toConvexSpaceBody)

/-- Actual finite conflict degree and weighted selection. Its overlap is ONE
against the full original canonical family, hence fits the original Ccan. -/
theorem exists_full_canonical_conflict_colour_w101
    (Ctw Lgeom : NNReal) (hCtw : 1 <= Ctw) (hLgeom : 1 <= Lgeom) :
    ∃ Dgeom : Nat, 1 <= Dgeom ∧
      ∀ {delta sigma : NNReal}, 0 < delta -> delta <= 1 ->
      ∀ {iota : Type uI} [DecidableEq iota]
        {B : Finset iota} {T : iota -> Tube delta E} {M : Nat} {Ccan : NNReal}
        (U0 : CanonicalProfileNetW87 B T M Ccan) (current : Finset iota) (q : Fin (M + 1)),
        current ⊆ B -> Tube.gridScale delta M q.val <= sigma -> Lgeom * sigma <= 1 ->
      ∀ (parents : Finset iota) (parent : iota -> Tube sigma E) (weight : iota -> ENNReal),
        (∀ P ∈ parents, (parent P).carrier ⊆ Metric.closedBall 0 2) ->
        lineEssentiallyDistinctW94 parents parent Ctw ->
        (∀ P ∈ parents, weight P < ⊤) -> (0 < ∑ P ∈ parents, weight P) ->
        (∀ P ∈ parents,
          ((parents.filter (canonicalParentConflictW101 (current := current) U0 q parent Lgeom P)).card <= Dgeom)) ∧
        ∃ colour : Finset iota, colour.Nonempty ∧ colour ⊆ parents ∧
          ((Dgeom + 1 : Nat) : ENNReal)⁻¹ * (∑ P ∈ parents, weight P) <= ∑ P ∈ colour, weight P ∧
          (colour : Set iota).Pairwise (fun P Q =>
            ¬canonicalParentConflictW101 (current := current) U0 q parent Lgeom P Q) ∧
          Tube.HasBoundedOverlap (canonicalQNodeFinsetW87 U0 current q)
            (fun w => U0.cover.tube q.val w.val) colour (fun P => (parent P).rescale (Lgeom * sigma)) 1 := by
  have hcommon {d r s : NNReal} (f : Tube d E) (T : Tube r E) (V : Tube s E)
      (hfT : f.toConvexSpaceBody <= T.toConvexSpaceBody)
      (hfV : f.toConvexSpaceBody <= V.toConvexSpaceBody) :
      V.toConvexSpaceBody <= (T.rescale (r + 4 * s)).toConvexSpaceBody := by
    intro x hx
    have hxFine := Tube.le_rescale_of_subset f V hfV hx
    change x ∈ (f.rescale (4 * s)).carrier at hxFine
    rw [(f.rescale (4 * s)).carrier_eq] at hxFine
    obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp hxFine
    have hpFine : p ∈ f.carrier := by
      rw [f.carrier_eq]
      exact Set.mem_iUnion₂.mpr ⟨p, hp, Metric.mem_closedBall_self d.coe_nonneg⟩
    have hpT : p ∈ T.carrier := hfT hpFine
    rw [T.carrier_eq] at hpT
    obtain ⟨q, hq, hpq⟩ := Set.mem_iUnion₂.mp hpT
    change x ∈ (T.rescale (r + 4 * s)).carrier
    rw [(T.rescale (r + 4 * s)).carrier_eq]
    refine Set.mem_iUnion₂.mpr ⟨q, hq, Metric.mem_closedBall.mpr ?_⟩
    have hxp' := Metric.mem_closedBall.mp hxp
    have hpq' := Metric.mem_closedBall.mp hpq
    push_cast at hxp' ⊢
    calc dist x q <= dist x p + dist p q := dist_triangle x p q
      _ <= 4 * (s : Real) + r := add_le_add hxp' hpq'
      _ = _ := by ring
  let K : Real := 9 * (Lgeom : Real)
  let N : Nat := lineAmplificationBoundW95 (Module.finrank Real E) 2 K
  let D : Nat := max 1 (Nat.ceil ((N : Real) * (Ctw : Real)))
  have hK : 1 <= K := by
    have hL : (1 : Real) <= Lgeom := by exact_mod_cast hLgeom
    dsimp [K]
    linarith
  refine ⟨D, Nat.le_max_left _ _, ?_⟩
  intro delta sigma hd hd1 iota inst B T M Ccan U0 current q hcurrent hscale hwide
    parents parent weight hball hline hfinite hmass
  let conflict := canonicalParentConflictW101 (current := current) U0 q parent Lgeom
  have hs : 0 < sigma := (Tube.gridScale_pos hd M q.val).trans_le hscale
  have hs1 : sigma <= 1 := (le_mul_of_one_le_left sigma.coe_nonneg hLgeom).trans hwide
  have hσL : sigma <= Lgeom * sigma := le_mul_of_one_le_left sigma.coe_nonneg hLgeom
  have hsymm : ∀ P Q, conflict P Q -> conflict Q P := by
    rintro P Q ⟨hPQ, test, hP, hQ⟩
    exact ⟨hPQ.symm, test, hQ, hP⟩
  have hirr : ∀ P, ¬conflict P P := by
    intro P h
    exact h.1 rfl
  have hcentre : ∀ P ∈ parents, ‖(parent P).center‖ <= 2 := by
    intro P hP
    have hmid := Tube.midpoint_mem_closedBall_of_subset hs (parent P) (hball P hP)
    simpa only [Tube.center, Tube.midpoint, midpoint_eq_smul_add, invOf_eq_inv,
      one_div, Metric.mem_closedBall, dist_zero_right] using hmid
  have hnear : ∀ P, parents.filter (conflict P) ⊆
      nearLineFamilyW95 parents parent (parent P).center (parent P).direction K := by
    intro P Q hQ
    obtain ⟨hQmem, hPQ⟩ := Finset.mem_filter.mp hQ
    obtain ⟨_, test, ⟨wP, hwP, hwPP, hwPt⟩, ⟨wQ, hwQ, hwQQ, hwQt⟩⟩ := hPQ
    have htest := hcommon (U0.cover.tube q.val wP.val)
      ((parent P).rescale (Lgeom * sigma)) test hwPP hwPt
    have hQparent := hcommon (U0.cover.tube q.val wQ.val)
      ((parent P).rescale (Lgeom * sigma + 4 * (Lgeom * sigma)))
      ((parent Q).rescale (Lgeom * sigma)) (hwQt.trans htest) hwQQ
    have hbody : (parent Q).toConvexSpaceBody <=
        ((parent P).rescale (9 * Lgeom * sigma)).toConvexSpaceBody := by
      have h := (Tube.le_rescale (parent Q) hσL).trans hQparent
      change (parent Q).toConvexSpaceBody <= ((parent P).rescale
        (Lgeom * sigma + 4 * (Lgeom * sigma) + 4 * (Lgeom * sigma))).toConvexSpaceBody at h
      exact h.trans (Tube.rescale_le_rescale_of_radius_le (parent P) (by ring_nf; exact le_rfl))
    refine Finset.mem_filter.mpr ⟨hQmem, ?_⟩
    intro x hx
    have hxP := hbody hx
    change x ∈ ((parent P).rescale (9 * Lgeom * sigma)).carrier at hxP
    rw [((parent P).rescale (9 * Lgeom * sigma)).carrier_eq] at hxP
    obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.mp hxP
    rcases hz with ⟨a, b, ha, hb, hab, rfl⟩
    apply VeryNotSticky.mem_lineNbhd_of_dist_le (b - 1 / 2)
    have heq : a • (parent P).x + b • (parent P).y =
        (parent P).center + (b - 1 / 2 : Real) • (parent P).direction := by
      rw [Tube.x_eq_center_sub, Tube.y_eq_center_add, show a = 1 - b by linarith]
      module
    have hdist := Metric.mem_closedBall.mp hxz
    change dist x (a • (parent P).x + b • (parent P).y) <= (9 * Lgeom * sigma : NNReal) at hdist
    rw [heq] at hdist
    simpa only [K, NNReal.coe_mul, NNReal.coe_ofNat] using hdist
  have hdegree : ∀ P ∈ parents, (parents.filter (conflict P)).card <= D := by
    intro P hP
    obtain ⟨G, assign, hG, hGcard, hassign, hcover⟩ :=
      exists_radius_five_line_bins_w95 hs hs1 parents parent 2 K (by norm_num) hK
        hcentre (parent P).center (parent P).direction (parent P).norm_direction
    let fibres := fun R => parents.filter (fun Q =>
      liesInFiveDeltaLineTubeW94 (parent Q) (parent R).center (parent R).direction)
    have hfibres : ∀ R, ((fibres R).card : NNReal) <= Ctw := fun R =>
      hline (parent R).center (parent R).direction (parent R).norm_direction
    have hcovered : parents.filter (conflict P) ⊆ G.biUnion fibres := by
      intro Q hQ
      have hn := hnear P hQ
      refine Finset.mem_biUnion.mpr ⟨assign Q, hassign Q hn, Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hQ).1, ?_⟩⟩
      exact (pointwise_line_neighbourhood_iff_w95 (parent Q) (parent (assign Q)).center
        (parent (assign Q)).direction (parent (assign Q)).norm_direction).mpr (hcover Q hn)
    have hcount : ((parents.filter (conflict P)).card : NNReal) <= (N : NNReal) * Ctw := by
      calc
        ((parents.filter (conflict P)).card : NNReal) <= ((G.biUnion fibres).card : NNReal) := by
          exact_mod_cast Finset.card_le_card hcovered
        _ <= ∑ R ∈ G, ((fibres R).card : NNReal) := by exact_mod_cast Finset.card_biUnion_le
        _ <= ∑ _R ∈ G, Ctw := Finset.sum_le_sum (fun R hR => hfibres R)
        _ = (G.card : NNReal) * Ctw := by rw [Finset.sum_const, nsmul_eq_mul]
        _ <= (N : NNReal) * Ctw := by
          apply mul_le_mul_right'
          exact_mod_cast hGcard
    have hreal : ((parents.filter (conflict P)).card : Real) <= (N : Real) * Ctw := by
      exact_mod_cast hcount
    have hceil : (parents.filter (conflict P)).card <= Nat.ceil ((N : Real) * Ctw) := by
      exact_mod_cast hreal.trans (Nat.le_ceil _)
    exact hceil.trans (Nat.le_max_right _ _)
  have hdegreeSet : ∀ P ∈ parents, {Q ∈ (parents : Set iota) | conflict Q P}.ncard <= D := by
    intro P hP
    have heq : {Q ∈ (parents : Set iota) | conflict Q P} =
        ((parents.filter (conflict P)) : Set iota) := by
      ext Q
      simp only [Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter]
      exact and_congr_right (fun _ => ⟨hsymm Q P, hsymm P Q⟩)
    rw [heq]
    simpa only [Set.ncard_coe_finset] using hdegree P hP
  obtain ⟨colour, hcolour, hpair, hpay⟩ :=
    Kakeya.exists_pairwise_not_of_degree_le parents conflict hsymm hirr hdegreeSet weight
  have hnonempty : colour.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty, mul_zero] at hpay
    exact (not_le_of_gt hmass) hpay
  refine ⟨hdegree, colour, hnonempty, hcolour, ?_, hpair, ?_⟩
  · exact (ENNReal.inv_mul_le_iff (by norm_num) (by finiteness)).mpr hpay
  · intro test
    have hcard : (colour.filter (fun P => ∃ w ∈ canonicalQNodeFinsetW87 U0 current q,
        (U0.cover.tube q.val w.val).toConvexSpaceBody <=
          ((parent P).rescale (Lgeom * sigma)).toConvexSpaceBody ∧
        (U0.cover.tube q.val w.val).toConvexSpaceBody <= test.toConvexSpaceBody)).card <= 1 := by
      apply Finset.card_le_one.mpr
      intro P hP Q hQ
      obtain ⟨hPc, hpw⟩ := Finset.mem_filter.mp hP
      obtain ⟨hQc, hqw⟩ := Finset.mem_filter.mp hQ
      by_contra hPQ
      exact hpair hPc hQc hPQ ⟨hPQ, test, hpw, hqw⟩
    exact_mod_cast hcard

/-- Weighted canonical conflict selection lifted to the actual fine family.
The returned parent family has overlap one against every original node. -/
theorem exists_fine_refinement_full_canonical_overlap_w101
    (Ctw Lgeom : NNReal) (hCtw : 1 <= Ctw) (hLgeom : 1 <= Lgeom) :
    ∃ Dgeom : Nat, 1 <= Dgeom ∧
      ∀ {delta sigma : NNReal}, 0 < delta -> delta <= 1 ->
      ∀ {iota : Type uI} [DecidableEq iota]
        {B : Finset iota} {T : iota -> Tube delta E} {M : Nat} {Ccan : NNReal}
        (U0 : CanonicalProfileNetW87 B T M Ccan) (current : Finset iota) (q : Fin (M + 1)),
        current ⊆ B -> Tube.gridScale delta M q.val <= sigma -> Lgeom * sigma <= 1 ->
      ∀ (G : Finset iota) (Z : iota -> ShadedTube delta E)
        (assignment : iota -> iota) (parent : iota -> Tube sigma E),
        (∀ P ∈ G.image assignment, (parent P).carrier ⊆ Metric.closedBall 0 2) ->
        lineEssentiallyDistinctW94 (G.image assignment) parent Ctw ->
        (0 < ∑ i ∈ G, volume (Z i).shade) ->
        ∃ H : Finset iota, H.Nonempty ∧ H ⊆ G ∧
          ((Dgeom + 1 : Nat) : ENNReal)⁻¹ * (∑ i ∈ G, volume (Z i).shade) <=
            ∑ i ∈ H, volume (Z i).shade ∧
          Tube.HasBoundedOverlap (canonicalQNodeFinsetW87 U0 current q)
            (fun w => U0.cover.tube q.val w.val) (H.image assignment)
              (fun P => (parent P).rescale (Lgeom * sigma)) 1 := by
  obtain ⟨Dgeom, hDgeom, hcolour⟩ :=
    exists_full_canonical_conflict_colour_w101 (E := E) Ctw Lgeom hCtw hLgeom
  refine ⟨Dgeom, hDgeom, ?_⟩
  intro delta sigma hd hd1 iota inst B T M Ccan U0 current q hcurrent hscale hwide
    G Z assignment parent hball hline hmass
  let parents := G.image assignment
  let weight := fun P => ∑ i ∈ completeFibreW94 G assignment P, volume (Z i).shade
  have hfinite : ∀ P ∈ parents, weight P < ⊤ := by
    intro P hP
    apply ENNReal.sum_lt_top.mpr
    intro i hi
    exact (measure_mono (Z i).shade_subset).trans_lt (Z i).isCompact.measure_lt_top
  have hsum : (∑ P ∈ parents, weight P) = ∑ i ∈ G, volume (Z i).shade :=
    Finset.sum_fiberwise_of_maps_to
      (fun i (hi : i ∈ G) => Finset.mem_image_of_mem assignment hi) (fun i => volume (Z i).shade)
  obtain ⟨_, colour, hcolourNe, hcolourSub, hpay, _, hoverlap⟩ :=
    hcolour hd hd1 U0 current q hcurrent hscale hwide parents parent weight hball hline
      hfinite (by rwa [hsum])
  let H := G.filter (fun i => assignment i ∈ colour)
  have hHG : H ⊆ G := Finset.filter_subset _ _
  have himage : H.image assignment = colour := by
    apply Finset.Subset.antisymm
    · intro P hP
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hP
      exact (Finset.mem_filter.mp hi).2
    · intro P hP
      obtain ⟨i, hi, hiP⟩ := Finset.mem_image.mp (hcolourSub hP)
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hiP ▸ hP⟩, hiP⟩
  have hsumH : (∑ P ∈ colour, weight P) = ∑ i ∈ H, volume (Z i).shade := by
    have hsumH' := Finset.sum_fiberwise_of_maps_to
      (fun i (hi : i ∈ H) => (Finset.mem_filter.mp hi).2) (fun i => volume (Z i).shade)
    rw [← hsumH']
    apply Finset.sum_congr rfl
    intro P hP
    have hfibre : completeFibreW94 G assignment P = completeFibreW94 H assignment P := by
      ext i
      simp only [completeFibreW94, H, Finset.mem_filter]
      constructor
      · rintro ⟨hi, hiP⟩
        exact ⟨⟨hi, hiP ▸ hP⟩, hiP⟩
      · exact fun hi => ⟨hi.1.1, hi.2⟩
    change (∑ i ∈ completeFibreW94 G assignment P, volume (Z i).shade) = _
    rw [hfibre]
    rfl
  refine ⟨H, Finset.image_nonempty.mp (himage ▸ hcolourNe), hHG, ?_, ?_⟩
  · rwa [hsum, hsumH] at hpay
  · rwa [himage]

/-- The approved selected max-density comparison, separated from the
unreviewed exact-unit-tube comparison. -/
theorem exists_actual_canonical_selected_density_comparison_w101
    (hdim : Module.finrank Real E = 3)
    (CbaseTw Ctw Ccell Rnorm Cext Cnorm CtwNorm CcellNorm : NNReal)
    (hCbaseTw : 1 <= CbaseTw) (hCtw : 1 <= Ctw) (hCcell : 1 <= Ccell)
    (hRnorm : 1 <= Rnorm) (hCext : 1 <= Cext) (hCnorm : 1 <= Cnorm) :
    ∃ Cden : NNReal, 1 <= Cden ∧
      ∀ {delta : NNReal}, 0 < delta -> delta < 1 ->
      ∀ {iota : Type uI} [DecidableEq iota]
        {B : Finset iota} {V : iota -> ShadedTube delta E} {M : Nat}
        {Ccan CbaseCell Cwork : NNReal}
        (U0 : CanonicalProfileNetW87 B (fun i => (V i).toTube) M Ccan)
        (current : RetainedStateW94 B V) (A : Finset iota)
        (U : CanonicalProfileNetW87 A (fun i => (current.shading i).toTube) M Cwork)
        (Uext : CanonicalProfileNetW87 A (fun i => (current.shading i).toTube) (M * M) Cwork),
        1 <= M -> A.Nonempty -> A ⊆ current.active ->
        (∀ i ∈ B, (V i).carrier ⊆ Metric.closedBall 0 1) ->
        SourceRegularizedWorkingTowerW95 U0 CbaseTw CbaseCell ->
        SourceRegularizedWorkingTowerW95 U Ctw Ccell ->
        SourceRegularizedWorkingTowerW95 Uext Ctw Ccell ->
        VisibleExtendedRestrictionW97 U Uext ->
        ActualTreeParameterMarginW98 Uext.cover normalizationParameterMarginW98 ->
      ∀ (a b : Fin (M + 1)), a.val < b.val ->
      ∀ (R : iota), R ∈ U.cover.indexSet a.val ->
      ∀ (Z : iota -> ShadedTube (Tube.gridScale delta M b.val) E)
        (normalization : ActualAssignedUnitNormalizationW97 U Uext a.val b.val R Z
          Rnorm Cext Cnorm CtwNorm CcellNorm),
        let F := actualDescendantsW95 A U.cover.assign a.val b.val R
        ∀ (selected : Finset iota) (part : Finset (CanonicalQNodeW87 U0 current.active b)),
          selected ⊆ F ->
          (∀ w ∈ part, ∃ i ∈ A, U0.cover.assign b.val i = w.val ∧ U.cover.assign b.val i ∈ selected) ->
          Kakeya.maxDensity part (fun w => (U0.cover.tube b.val w.val).toConvexSpaceBody) <=
            (Cden : ENNReal) * Kakeya.maxDensity selected
              (fun Q => (normalization.normalized Q).toConvexSpaceBody) := by
  classical
  have htransport {alpha beta : Type uI} [DecidableEq alpha] [DecidableEq beta]
      (s : Finset alpha) (t : Finset beta) (W : alpha -> ConvexSpaceBody E)
      (V : beta -> ConvexSpaceBody E) (f : alpha -> beta) (p q k : ENNReal)
      (hf : ∀ i ∈ s, f i ∈ t)
      (hcount : ∀ j ∈ t, ((s.filter (fun i => f i = j)).card : ENNReal) <= k)
      (hvol : ∀ i ∈ s, volume (W i).carrier <= p * volume (V (f i)).carrier)
      (htest : ∀ K : ConvexSpaceBody E, ∃ D : ConvexSpaceBody E,
        volume D.carrier <= q * volume K.carrier ∧
        ∀ i ∈ s, W i <= K -> V (f i) <= D) :
      maxDensity s W <= (p * k * q) * maxDensity t V := by
    apply maxDensity_le_of_forall_sum_le
    intro K
    obtain ⟨D, hDvol, hD⟩ := htest K
    let sK := s.filter (fun i => W i <= K)
    let tD := t.filter (fun j => V j <= D)
    have hmap : ∀ i ∈ sK, f i ∈ tD := by
      intro i hi
      obtain ⟨his, hiK⟩ := Finset.mem_filter.mp hi
      exact Finset.mem_filter.mpr ⟨hf i his, hD i his hiK⟩
    have hsum : (∑ i ∈ sK, volume (V (f i)).carrier) <=
        k * ∑ j ∈ tD, volume (V j).carrier := by
      rw [← Finset.sum_fiberwise_of_maps_to hmap (fun i => volume (V (f i)).carrier)]
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j hj
      have hcard : ((sK.filter (fun i => f i = j)).card : ENNReal) <= k := by
        calc
          _ <= ((s.filter (fun i => f i = j)).card : ENNReal) := by
            exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ (Finset.filter_subset _ _))
          _ <= k := hcount j (Finset.mem_filter.mp hj).1
      calc
        _ = ∑ _i ∈ sK.filter (fun i => f i = j), volume (V j).carrier := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [(Finset.mem_filter.mp hi).2]
        _ = ((sK.filter (fun i => f i = j)).card : ENNReal) * volume (V j).carrier := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ <= k * volume (V j).carrier := mul_le_mul_right' hcard _
    calc
      _ <= ∑ i ∈ sK, p * volume (V (f i)).carrier := by
        exact Finset.sum_le_sum (fun i hi => hvol i (Finset.mem_filter.mp hi).1)
      _ = p * ∑ i ∈ sK, volume (V (f i)).carrier := (Finset.mul_sum _ _ _).symm
      _ <= p * (k * ∑ j ∈ tD, volume (V j).carrier) := mul_le_mul_left' hsum p
      _ <= p * (k * (maxDensity t V * volume D.carrier)) := by
        exact mul_le_mul_left' (mul_le_mul_left'
          (sum_volume_le_maxDensity_mul_volume t V D) k) p
      _ <= p * (k * (maxDensity t V * (q * volume K.carrier))) := by
        exact mul_le_mul_left' (mul_le_mul_left' (mul_le_mul_left' hDvol _) k) p
      _ = ((p * k * q) * maxDensity t V) * volume K.carrier := by ring
  have hcommonHom {delta tau : NNReal} (fine : Tube delta E) (T V : Tube tau E)
      (hfT : fine.toConvexSpaceBody <= T.toConvexSpaceBody)
      (hfV : fine.toConvexSpaceBody <= V.toConvexSpaceBody) :
      V.carrier ⊆ (fun x => (5 : Real) • (x - T.center) + T.center) '' T.carrier := by
    intro x hx
    have hxf := Tube.le_rescale_of_subset fine V hfV hx
    change x ∈ (fine.rescale (4 * tau)).carrier at hxf
    rw [(fine.rescale (4 * tau)).carrier_eq] at hxf
    obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp hxf
    have hpFine : p ∈ fine.carrier := by
      rw [fine.carrier_eq]
      exact Set.mem_iUnion₂.mpr ⟨p, hp, Metric.mem_closedBall_self delta.coe_nonneg⟩
    have hpT : p ∈ T.carrier := hfT hpFine
    rw [T.carrier_eq] at hpT
    obtain ⟨q, hq, hpq⟩ := Set.mem_iUnion₂.mp hpT
    rcases hq with ⟨a, b, ha, hb, hab, rfl⟩
    have hcore : a • T.x + b • T.y = T.center + (b - 1 / 2 : Real) • T.direction := by
      rw [Tube.x_eq_center_sub, Tube.y_eq_center_add, show a = 1 - b by linarith]
      module
    have hs : |b - (1 / 2 : Real)| <= 5 / 2 := by
      rw [abs_le]
      constructor <;> linarith only [ha, hb, hab]
    have hdist : dist x (T.center + (b - 1 / 2 : Real) • T.direction) <= 5 * (tau : Real) := by
      rw [← hcore]
      have hxp' := Metric.mem_closedBall.mp hxp
      have hpq' := Metric.mem_closedBall.mp hpq
      push_cast at hxp'
      calc
        dist x (a • T.x + b • T.y) <= dist x p + dist p (a • T.x + b • T.y) :=
          dist_triangle _ _ _
        _ <= 4 * (tau : Real) + tau := add_le_add hxp' hpq'
        _ = 5 * (tau : Real) := by ring
    have hxD := Kakeya.Tube.mem_dilate_of_dist_axis_le T (by norm_num : (0 : Real) < 5) hs hdist
    simpa only [Kakeya.Tube.dilate_carrier, AffineMap.homothety_apply,
      vsub_eq_sub, vadd_eq_add] using hxD
  have hgeometric {alpha beta : Type uI} [DecidableEq alpha] [DecidableEq beta]
      {delta tau : NNReal} (htau : 0 < tau) (htau1 : tau <= 1)
      (s : Finset alpha) (t : Finset beta) (W : alpha -> Tube tau E)
      (V : beta -> Tube tau E) (f : alpha -> beta) (k : ENNReal)
      (hf : ∀ i ∈ s, f i ∈ t)
      (hcount : ∀ j ∈ t, ((s.filter (fun i => f i = j)).card : ENNReal) <= k)
      (hcommon : ∀ i ∈ s, ∃ fine : Tube delta E,
        fine.toConvexSpaceBody <= (W i).toConvexSpaceBody ∧
        fine.toConvexSpaceBody <= (V (f i)).toConvexSpaceBody) :
      maxDensity s (fun i => (W i).toConvexSpaceBody) <=
        (48000 * k) * maxDensity t (fun j => (V j).toConvexSpaceBody) := by
    have h := htransport s t (fun i => (W i).toConvexSpaceBody)
      (fun j => (V j).toConvexSpaceBody) f 1 48000 k hf hcount (fun i hi => ?_) (fun K => ?_)
    · simpa only [one_mul, mul_comm k] using h
    · rw [one_mul]
      exact (Tube.volume_carrier_eq_volume_carrier (W i) (V (f i))).le
    · have hhom : ∀ i ∈ s, ∃ p ∈ (W i).carrier,
          (V (f i)).carrier ⊆ (fun x => (5 : Real) • (x - p) + p) '' (W i).carrier := by
        intro i hi
        obtain ⟨fine, hfW, hfV⟩ := hcommon i hi
        refine ⟨(W i).center, ?_, ?_⟩
        · simpa only [Tube.center, Tube.midpoint, midpoint_eq_smul_add, invOf_eq_inv, one_div]
            using Tube.midpoint_mem_carrier htau (W i)
        exact hcommonHom fine (W i) (V (f i)) hfW hfV
      obtain ⟨D, _, hDvol, hD⟩ := ConvexSpaceBody.exists_enlargement_of_homothety
        (s := s) (W := fun i => (W i).toConvexSpaceBody)
        (V := fun i => (V (f i)).toConvexSpaceBody) (lam := 5) (by norm_num)
        (fun i hi => (Tube.volume_pos_and_lt_top htau htau1 (W i)).1.ne') hhom K
      refine ⟨D, ?_, hD⟩
      norm_num [hdim] at hDvol ⊢
      exact hDvol
  obtain ⟨Cdegree, hCdegree, hincidence⟩ :=
    actual_working_canonical_incidence_w97.{uE, uI} (E := E) CbaseTw Ctw hCbaseTw hCtw
  let Cden : NNReal := 48000 * Cdegree * Cext ^ 2
  let Lgeom : NNReal := 1000000 * Rnorm
  have hCden : 1 <= Cden := by
    dsimp only [Cden]
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (by norm_num) hCdegree)
      (one_le_pow₀ hCext)
  have hLgeom : 2 <= Lgeom := by
    calc
      (2 : NNReal) <= 1000000 := by norm_num
      _ <= 1000000 * Rnorm := le_mul_of_one_le_right (by positivity) hRnorm
  refine ⟨Cden, hCden, ?_⟩
  intro delta hd hd1 iota inst B V M Ccan CbaseCell Cwork U0 current A U Uext
    hM hAnonempty hA hball reg0 reg regext restriction margin a b hab R hR Z normalization
  dsimp only
  let F := actualDescendantsW95 A U.cover.assign a.val b.val R
  let old := fun Q => (U.cover.tube b.val Q).toConvexSpaceBody
  let new := fun Q => (normalization.normalized Q).toConvexSpaceBody
  let jac : ENNReal := normalization.jacobian
  have hjac0 : jac ≠ 0 := by
    dsimp only [jac]
    exact_mod_cast normalization.jacobian_pos.ne'
  have hjacTop : jac ≠ ⊤ := ENNReal.coe_ne_top
  have hnormForward : ∀ s : Finset iota, s ⊆ F ->
      maxDensity s old <= (Cext : ENNReal) * maxDensity s new := by
    intro s hs
    have h := htransport s s old new id jac⁻¹ ((Cext : ENNReal) * jac) 1
      (fun i hi => hi) (fun j hj => by
        exact_mod_cast (Finset.card_le_one.mpr (by
          intro x hx y hy
          exact (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm)))
      (fun i hi => ?_) (fun K => ?_)
    · simpa only [mul_one, mul_left_comm jac⁻¹, ENNReal.inv_mul_cancel hjac0 hjacTop,
        mul_one] using h
    · have hiVol := (normalization.carrier_volume i (hs hi)).1
      change jac * volume (old i).carrier <= volume (new i).carrier at hiVol
      simpa only [id_eq, ← mul_assoc, ENNReal.inv_mul_cancel hjac0 hjacTop, one_mul]
        using mul_le_mul_left' hiVol jac⁻¹
    · obtain ⟨D, hD, hsub⟩ := normalization.forward_test K
      exact ⟨D, hD, fun i hi => hsub i (hs hi)⟩
  have hnormBackward : ∀ s : Finset iota, s ⊆ F ->
      maxDensity s new <= (Cext : ENNReal) ^ 2 * maxDensity s old := by
    intro s hs
    have h := htransport s s new old id ((Cext : ENNReal) * jac)
      ((Cext : ENNReal) * jac⁻¹) 1 (fun i hi => hi) (fun j hj => by
        exact_mod_cast (Finset.card_le_one.mpr (by
          intro x hx y hy
          exact (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm)))
      (fun i hi => (normalization.carrier_volume i (hs hi)).2) (fun K => ?_)
    · convert h using 1
      congr 1
      rw [mul_one, show ((Cext : ENNReal) * jac) * ((Cext : ENNReal) * jac⁻¹) =
        (Cext : ENNReal) ^ 2 * (jac * jac⁻¹) by ring,
        ENNReal.mul_inv_cancel hjac0 hjacTop, mul_one]
    · obtain ⟨D, hD, hsub⟩ := normalization.backward_test K
      exact ⟨D, hD, fun i hi => hsub i (hs hi)⟩
  have hb : b.val <= M := Nat.le_of_lt_succ b.isLt
  have htau : 0 < Tube.gridScale delta M b.val := Tube.gridScale_pos hd M b.val
  let edges := A.image (fun i => (U.cover.assign b.val i, U0.cover.assign b.val i))
  have hinc := hincidence hd hd1.le U0 current A U hA reg0 reg b
  have hleft : ∀ Q ∈ U.cover.indexSet b.val,
      ((edges.filter (fun e => e.1 = Q)).card : NNReal) <= Cdegree := hinc.1
  have hright : ∀ w ∈ canonicalAncestorFamilyW87 U0 current.active b,
      ((edges.filter (fun e => e.2 = w)).card : NNReal) <= Cdegree := hinc.2.1
  have hcommon : ∀ i ∈ A,
      (current.shading i).toConvexSpaceBody <= (U.cover.tube b.val (U.cover.assign b.val i)).toConvexSpaceBody ∧
      (current.shading i).toConvexSpaceBody <= (U0.cover.tube b.val (U0.cover.assign b.val i)).toConvexSpaceBody := by
    intro i hi
    refine ⟨U.cover.le_tube_assign b.val hb i hi, ?_⟩
    rw [show (current.shading i).toConvexSpaceBody = (V i).toConvexSpaceBody from
      congrArg Tube.toConvexSpaceBody (current.same_tube i (hA hi))]
    exact U0.cover.le_tube_assign b.val hb i (current.active_subset (hA hi))
  have hF : F ⊆ U.cover.indexSet b.val := by
    intro Q hQ
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQ
    exact U.cover.assign_mem b.val hb i (Finset.mem_filter.mp hi).1
  have hCextSq : (Cext : ENNReal) <= (Cext : ENNReal) ^ 2 := by
    rw [pow_two]
    exact le_mul_of_one_le_right (by positivity) (by exact_mod_cast hCext)
  exact (by
    intro selected part hselected hpart
    obtain ⟨i0, hi0⟩ := hAnonempty
    have hex : ∀ w : CanonicalQNodeW87 U0 current.active b, ∃ i : iota,
        w ∈ part -> i ∈ A ∧ U0.cover.assign b.val i = w.val ∧ U.cover.assign b.val i ∈ selected := by
      intro w
      by_cases hw : w ∈ part
      · obtain ⟨i, hi, hi0, hiU⟩ := hpart w hw
        exact ⟨i, fun _ => ⟨hi, hi0, hiU⟩⟩
      · exact ⟨i0, fun h => (hw h).elim⟩
    choose leaf hleaf using hex
    let f := fun w : CanonicalQNodeW87 U0 current.active b => U.cover.assign b.val (leaf w)
    have hf : ∀ w ∈ part, f w ∈ selected := fun w hw => (hleaf w hw).2.2
    have hcount : ∀ Q ∈ selected, ((part.filter (fun w => f w = Q)).card : ENNReal) <= Cdegree := by
      intro Q hQ
      let fibre := part.filter (fun w => f w = Q)
      let edge : CanonicalQNodeW87 U0 current.active b -> iota × iota := fun w => (Q, w.val)
      have hinj : Set.InjOn edge fibre := by
        intro w hw v hv heq
        exact Subtype.ext (congrArg Prod.snd heq)
      have hmap : fibre.image edge ⊆ edges.filter (fun e => e.1 = Q) := by
        intro e he
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp he
        obtain ⟨hwpart, hwQ⟩ := Finset.mem_filter.mp hw
        obtain ⟨hi, hi0, hiU⟩ := hleaf w hwpart
        refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨leaf w, hi, ?_⟩, rfl⟩
        exact Prod.ext hwQ hi0
      have hcard : (fibre.card : NNReal) <= Cdegree := by
        calc
          _ = ((fibre.image edge).card : NNReal) := by rw [Finset.card_image_of_injOn hinj]
          _ <= ((edges.filter (fun e => e.1 = Q)).card : NNReal) := by
            exact_mod_cast Finset.card_le_card hmap
          _ <= Cdegree := hleft Q (hF (hselected hQ))
      exact_mod_cast hcard
    have hcompare := hgeometric (delta := delta) (tau := Tube.gridScale delta M b.val) htau
      (Tube.gridScale_le_one (by exact_mod_cast hd1.le) _ _) part selected
      (fun w : CanonicalQNodeW87 U0 current.active b => U0.cover.tube b.val w.val)
      (U.cover.tube b.val) f (Cdegree : ENNReal) hf hcount (fun w hw => ?_)
    · calc
        _ <= (48000 * (Cdegree : ENNReal)) * maxDensity selected old := hcompare
        _ <= (48000 * (Cdegree : ENNReal)) * ((Cext : ENNReal) * maxDensity selected new) :=
          mul_le_mul_left' (hnormForward selected hselected) _
        _ <= (48000 * (Cdegree : ENNReal)) * ((Cext : ENNReal) ^ 2 * maxDensity selected new) :=
          mul_le_mul_left' (mul_le_mul_right' hCextSq _) _
        _ = (Cden : ENNReal) * maxDensity selected new := by
          simp only [Cden, ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_ofNat, mul_assoc]
    · obtain ⟨hi, hi0, hiU⟩ := hleaf w hw
      refine ⟨(current.shading (leaf w)).toTube, ?_, (hcommon (leaf w) hi).1⟩
      simpa only [hi0] using (hcommon (leaf w) hi).2
    )

end

end Kakeya.ml1Boot.TrialRestartW94
