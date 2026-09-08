module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceWindowTrialW98
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceCanonicalTransportW97
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceSameMassFullnessW98
public import Kakeya.ConvexBody.DilateWitness

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

/-- Revised detailed GWZ 4851-4905, 5065-5097. This is only the rejected
exact-Ns arm, with original centring sourced from the paid-pass input.
The axis-foot normalization and parameter-margin inputs are unchanged. -/
theorem exists_centred_actual_canonical_exact_ns_comparison_w101
    (hdim : Module.finrank Real E = 3)
    (CbaseTw Ctw Ccell Rnorm Cext Cnorm CtwNorm CcellNorm : NNReal)
    (hCbaseTw : 1 <= CbaseTw) (hCtw : 1 <= Ctw) (hCcell : 1 <= Ccell)
    (hRnorm : 1 <= Rnorm) (hCext : 1 <= Cext) (hCnorm : 1 <= Cnorm) :
    ∃ Cden Lgeom : NNReal, 1 <= Cden ∧ 2 <= Lgeom ∧
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
        (∀ i ∈ B, centredTubeW94 (V i).toTube) ->
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
        let d := Tube.gridScale delta M b.val / Tube.gridScale delta M a.val
        ∀ r : NNReal, 16 * d <= r -> r <= 1 ->
          Lgeom * Tube.gridScale delta M a.val * r <= 1 ->
          allExactTubeNsW87 F (fun Q => (normalization.normalized Q).toTube) r <=
            (Cden : ENNReal) * allExactTubeNsW87 (canonicalQNodeFinsetW87 U0 current.active b)
              (fun w => U0.cover.tube b.val w.val) (Lgeom * Tube.gridScale delta M a.val * r) := by
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
  have hcentredCore {delta : NNReal} {iota : Type uI} [DecidableEq iota]
      (s : Finset iota) (T : iota -> Tube delta E) (i0 : iota) (hi0 : i0 ∈ s)
      (hcen : ∀ i ∈ s, (T i).IsCentred)
      (hmid : ∀ i ∈ s, ‖(T i).midpoint‖ <= 1)
      (o u : E) (hu : ‖u‖ = 1) (rho : Real) (hrho : 0 <= rho)
      (hcore : ∀ i ∈ s, ∀ z ∈ segment Real (T i).x (T i).y,
        Tube.lineDist o u z <= rho)
      (sigma target : NNReal) (hscale : 14 * rho + (sigma : Real) <= target) :
      ∀ i ∈ s, ((T i).rescale sigma).toConvexSpaceBody <=
        ((T i0).rescale target).toConvexSpaceBody := by
    have hparams : ∀ i ∈ s, ∃ sign : Real, (sign = 1 ∨ sign = -1) ∧
        ‖(T i).direction - sign • u‖ <= 4 * rho ∧
        ‖(T i).midpoint - Tube.lineFoot o u‖ <= 5 * rho := by
      intro i hi
      obtain ⟨sign, hsign, hdir⟩ := Tube.exists_sign_norm_direction_sub_le (T i) hu
        (hcore i hi _ (left_mem_segment _ _ _)) (hcore i hi _ (right_mem_segment _ _ _))
      have hmidmem : (T i).midpoint ∈ segment Real (T i).x (T i).y := by
        simpa using (T i).midpoint_add_smul_mem_segment (t := 0) (by norm_num)
      have hm := Tube.norm_midpoint_sub_lineFoot_le_of_isCentred (T i) (hcen i hi)
        hu (hcore i hi _ hmidmem) hsign hdir
      exact ⟨sign, hsign, hdir, by nlinarith [hmid i hi]⟩
    obtain ⟨s0, hs0, hd0, hm0⟩ := hparams i0 hi0
    intro i hi z hz
    obtain ⟨si, hsi, hdi, hmi⟩ := hparams i hi
    have hsiAbs : |si| = 1 := by rcases hsi with rfl | rfl <;> norm_num
    have hs0Abs : |s0| = 1 := by rcases hs0 with rfl | rfl <;> norm_num
    have hsigAbs : |si * s0| = 1 := by rw [abs_mul, hsiAbs, hs0Abs, one_mul]
    have hmiddist : ‖(T i).midpoint - (T i0).midpoint‖ <= 10 * rho := by
      calc
        _ <= ‖(T i).midpoint - Tube.lineFoot o u‖ +
            ‖(T i0).midpoint - Tube.lineFoot o u‖ := by
          simpa only [norm_sub_rev (Tube.lineFoot o u) (T i0).midpoint] using
            norm_sub_le_norm_sub_add_norm_sub (T i).midpoint (Tube.lineFoot o u) (T i0).midpoint
        _ <= _ := by linarith
    have hdirdist : ‖(T i).direction - (si * s0) • (T i0).direction‖ <= 8 * rho := by
      have hid : (T i).direction - (si * s0) • (T i0).direction =
          ((T i).direction - si • u) - (si * s0) • ((T i0).direction - s0 • u) := by
        rcases hs0 with rfl | rfl <;> simp <;> module
      rw [hid]
      calc
        _ <= ‖(T i).direction - si • u‖ + ‖(si * s0) • ((T i0).direction - s0 • u)‖ :=
          norm_sub_le _ _
        _ <= _ := by rw [norm_smul, Real.norm_eq_abs, hsigAbs, one_mul]; linarith
    change z ∈ ((T i).rescale sigma).carrier at hz
    change z ∈ ((T i0).rescale target).carrier
    rw [((T i).rescale sigma).carrier_eq] at hz
    obtain ⟨x, hx, hzx⟩ := Set.mem_iUnion₂.mp hz
    obtain ⟨t, ht, rfl⟩ := (T i).exists_param_of_mem_segment hx
    let y := (T i0).midpoint + (t * (si * s0)) • (T i0).direction
    have hy : y ∈ segment Real (T i0).x (T i0).y := by
      apply (T i0).midpoint_add_smul_mem_segment
      rw [abs_mul, hsigAbs, mul_one]
      exact ht
    have hxy : dist ((T i).midpoint + t • (T i).direction) y <= 14 * rho := by
      rw [dist_eq_norm]
      have hid : (T i).midpoint + t • (T i).direction - y =
          ((T i).midpoint - (T i0).midpoint) +
            t • ((T i).direction - (si * s0) • (T i0).direction) := by dsimp [y]; module
      rw [hid]
      calc
        _ <= ‖(T i).midpoint - (T i0).midpoint‖ +
            ‖t • ((T i).direction - (si * s0) • (T i0).direction)‖ := norm_add_le _ _
        _ <= _ := by
          rw [norm_smul, Real.norm_eq_abs]
          nlinarith [norm_nonneg ((T i).direction - (si * s0) • (T i0).direction)]
    rw [((T i0).rescale target).carrier_eq]
    apply Set.mem_iUnion₂.mpr ⟨y, hy, ?_⟩
    exact Metric.mem_closedBall.mpr ((dist_triangle z ((T i).midpoint + t • (T i).direction) y).trans
      ((add_le_add (Metric.mem_closedBall.mp hzx) hxy).trans (by linarith)))
  have haxisPull {theta tau d r : NNReal} (htheta : 0 < theta) (htheta1 : theta <= 1)
      (R : Real) (hR : 0 < R) (parent : Tube theta E) (old : Tube tau E) (new : Tube d E)
      (hperp : ‖old.direction - inner Real parent.direction old.direction • parent.direction‖ <=
        2 * (theta : Real))
      (hdir : new.direction = ‖(parent.rescaleMap R).linear old.direction‖⁻¹ •
        (parent.rescaleMap R).linear old.direction)
      (hcen : new.center = parent.rescaleMap R old.center -
        inner Real (parent.rescaleMap R old.center) new.direction • new.direction)
      (z : E) (hz : parent.rescaleMap R z ∈ (new.rescale (4 * r)).carrier) :
      Tube.lineDist old.center old.direction z <= 48 * R * (theta : Real) * r := by
    let Psi := parent.rescaleMap R
    rw [(new.rescale (4 * r)).carrier_eq] at hz
    obtain ⟨x, hx, hzx⟩ := Set.mem_iUnion₂.mp hz
    obtain ⟨t, ht, rfl⟩ := new.exists_param_of_mem_segment hx
    let alpha := t - inner Real (Psi old.center) new.direction
    obtain ⟨alpha', halphaBound, halpha⟩ :=
      Tube.rescale_symm_apply_add_smul htheta htheta1 hR parent old alpha old.center
    have hD : Psi old.y - Psi old.x = Psi.linear old.direction := by
      simpa only [Tube.direction, vsub_eq_sub] using
        (AffineMap.linearMap_vsub Psi old.y old.x).symm
    change Psi (old.center + alpha' • old.direction) =
      Psi old.center + (alpha * ‖Psi old.y - Psi old.x‖⁻¹) • (Psi old.y - Psi old.x) at halpha
    rw [hD, ← smul_smul, ← hdir] at halpha
    have hmid : new.midpoint = new.center := by
      simp only [Tube.midpoint, Tube.center, midpoint_eq_smul_add, invOf_eq_inv, one_div]
    let w := old.center + alpha' • old.direction
    have hpoint : Psi w = new.midpoint + t • new.direction := by
      rw [show Psi w = Psi old.center + alpha • new.direction from halpha, hmid, hcen]
      dsimp [alpha, Psi]
      module
    have hv : ‖Psi z - Psi w‖ <= 4 * (r : Real) := by
      rw [hpoint, ← dist_eq_norm]
      simpa only [NNReal.coe_mul, NNReal.coe_ofNat] using Metric.mem_closedBall.mp hzx
    have hvec := Tube.norm_rescale_symm_vector_le htheta htheta1 hR parent old
      (by norm_num : (0 : Real) <= 2) (by positivity : (0 : Real) <= 4 * r) hperp
      (z := w) (u := z - w) (v := Psi z - Psi w) (by simp [Psi]) hv
    have he : inner Real old.direction old.direction = 1 := by
      rw [real_inner_self_eq_norm_sq, old.norm_direction]
      norm_num
    have hinner : inner Real old.direction (z - w) =
        inner Real (z - old.center) old.direction - alpha' := by
      change inner Real old.direction (z - (old.center + alpha' • old.direction)) = _
      rw [inner_sub_right, inner_add_right, real_inner_smul_right, he, mul_one,
        ← real_inner_comm old.direction z, ← real_inner_comm old.direction old.center, inner_sub_left]
      ring
    have hproj : (z - w) - inner Real old.direction (z - w) • old.direction =
        (z - old.center) - inner Real (z - old.center) old.direction • old.direction := by
      rw [hinner]
      dsimp [w]
      module
    rw [hproj] at hvec
    change ‖(z - old.center) - inner Real (z - old.center) old.direction • old.direction‖ <= _
    convert hvec.2 using 1 <;> ring
  obtain ⟨Cdegree, hCdegree, hincidence⟩ :=
    actual_working_canonical_incidence_w97.{uE, uI} (E := E) CbaseTw Ctw hCbaseTw hCtw
  let Cden : NNReal := 48000 * Cdegree * Cext ^ 2
  let Lgeom : NNReal := 1000000 * Rnorm
  refine ⟨Cden, Lgeom, ?_, ?_, ?_⟩
  · exact one_le_mul (one_le_mul (by norm_num) hCdegree) (one_le_pow₀ hCext)
  · dsimp [Lgeom]
    nlinarith
  intro delta hd hd1 iota inst B V M Ccan CbaseCell Cwork U0 current A U Uext
    hM hAnonempty hA hball hcentred reg0 reg regext restriction margin a b hab R hR Z normalization
  dsimp only
  intro r hdr hr1 hlr
  let theta := Tube.gridScale delta M a.val
  let tau := Tube.gridScale delta M b.val
  let F := actualDescendantsW95 A U.cover.assign a.val b.val R
  let old := fun Q => (U.cover.tube b.val Q).toConvexSpaceBody
  let new := fun Q => (normalization.normalized Q).toConvexSpaceBody
  let jac : ENNReal := normalization.jacobian
  have hjac0 : jac ≠ 0 := by
    dsimp only [jac]
    exact_mod_cast normalization.jacobian_pos.ne'
  have hjacTop : jac ≠ ⊤ := ENNReal.coe_ne_top
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
  have htheta : 0 < theta := Tube.gridScale_pos hd M a.val
  have htheta1 : theta <= 1 := Tube.gridScale_le_one hd1.le M a.val
  have htau : 0 < tau := Tube.gridScale_pos hd M b.val
  have htau1 : tau <= 1 := Tube.gridScale_le_one hd1.le M b.val
  have htauSmall : 16 * tau <= theta * r := by
    change 16 * (tau / theta) <= r at hdr
    rw [← mul_div_assoc] at hdr
    simpa only [mul_comm theta r] using (div_le_iff₀ htheta).mp hdr
  have hRpos : (0 : Real) < Rnorm := by exact_mod_cast zero_lt_one.trans_le hRnorm
  have hFleaf : ∀ Q ∈ F, ∃ i ∈ A,
      U.cover.assign b.val i = Q ∧ U.cover.assign a.val i = R := by
    intro Q hQ
    obtain ⟨i, hi, hiQ⟩ := Finset.mem_image.mp hQ
    exact ⟨i, (Finset.mem_filter.mp hi).1, hiQ, (Finset.mem_filter.mp hi).2⟩
  obtain ⟨iDefault, hiDefault⟩ := hAnonempty
  let leaf : iota -> iota := fun Q => if hQ : Q ∈ F then (hFleaf Q hQ).choose else iDefault
  have hleaf : ∀ Q ∈ F, leaf Q ∈ A ∧
      U.cover.assign b.val (leaf Q) = Q ∧ U.cover.assign a.val (leaf Q) = R := by
    intro Q hQ
    simpa only [leaf, dif_pos hQ] using (hFleaf Q hQ).choose_spec
  have hleafA : ∀ Q, leaf Q ∈ A := by
    intro Q
    by_cases hQ : Q ∈ F
    · exact (hleaf Q hQ).1
    · simpa only [leaf, dif_neg hQ] using hiDefault
  let fine : iota -> Tube delta E := fun Q => (current.shading (leaf Q)).toTube
  let f : iota -> CanonicalQNodeW87 U0 current.active b := fun Q =>
    ⟨U0.cover.assign b.val (leaf Q), Finset.mem_image.mpr ⟨leaf Q, hA (hleafA Q), rfl⟩⟩
  have hfineOld : ∀ Q ∈ F, (fine Q).toConvexSpaceBody <= old Q := by
    intro Q hQ
    have h := U.cover.le_tube_assign b.val hb (leaf Q) (hleaf Q hQ).1
    simpa only [(hleaf Q hQ).2.1] using h
  have hfineCanonical : ∀ Q, (fine Q).toConvexSpaceBody <=
      (U0.cover.tube b.val (f Q).val).toConvexSpaceBody := by
    intro Q
    have h := U0.cover.le_tube_assign b.val hb (leaf Q) (current.active_subset (hA (hleafA Q)))
    simpa only [← current.same_tube (leaf Q) (hA (hleafA Q))] using h
  have hfineCentred : ∀ Q, (fine Q).IsCentred := by
    intro Q
    have h := hcentred (leaf Q) (current.active_subset (hA (hleafA Q)))
    rw [← current.same_tube (leaf Q) (hA (hleafA Q))] at h
    change centredTubeW94 (fine Q) at h
    simpa only [centredTubeW94, Tube.IsCentred, Tube.center, Tube.midpoint,
      midpoint_eq_smul_add, invOf_eq_inv, one_div] using h
  have hfineBall : ∀ Q, (fine Q).carrier ⊆ Metric.closedBall 0 1 := by
    intro Q
    have h := hball (leaf Q) (current.active_subset (hA (hleafA Q)))
    simpa only [← current.same_tube (leaf Q) (hA (hleafA Q))] using h
  have hfineMid : ∀ Q, ‖(fine Q).midpoint‖ <= 1 := by
    intro Q
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      hfineBall Q (Tube.midpoint_mem_carrier hd (fine Q))
  let edges := A.image (fun i => (U.cover.assign b.val i, U0.cover.assign b.val i))
  have hright := (hincidence hd hd1.le U0 current A U hA reg0 reg b).2.1
  apply allExactTubeNs_le_w87
  intro test htestNonempty
  let s := exactTubeCellW87 F (fun Q => (normalization.normalized Q).toTube) test
  have hsF : s ⊆ F := Finset.filter_subset _ _
  obtain ⟨Q0, hQ0⟩ := htestNonempty
  have hQ0F := hsF hQ0
  have htestRef := Tube.le_rescale_of_subset (normalization.normalized Q0).toTube test
    (Finset.mem_filter.mp hQ0).2
  have hparent : (U.cover.tube b.val Q0).toConvexSpaceBody <=
      (U.cover.tube a.val R).toConvexSpaceBody := by
    have h := U.cover.toChain.tube_assign_le hab.le hb (hleaf Q0 hQ0F).1
    change (U.cover.tube b.val (U.cover.assign b.val (leaf Q0))).toConvexSpaceBody <=
      (U.cover.tube a.val (U.cover.assign a.val (leaf Q0))).toConvexSpaceBody at h
    simpa only [(hleaf Q0 hQ0F).2.1, (hleaf Q0 hQ0F).2.2] using h
  let rho : Real := 48 * (Rnorm : Real) * (theta : Real) * r
  have hrho : 0 <= rho := by positivity
  have hcoreLine : ∀ Q ∈ s, ∀ z ∈ segment Real (fine Q).x (fine Q).y,
      Tube.lineDist (U.cover.tube b.val Q0).center (U.cover.tube b.val Q0).direction z <= rho := by
    intro Q hQ z hz
    have hnorm : (U.cover.tube a.val R).rescaleMap (Rnorm : Real) z ∈
        ((normalization.normalized Q0).toTube.rescale (4 * r)).carrier := by
      apply htestRef
      apply (Finset.mem_filter.mp hQ).2
      exact normalization.image_carrier Q (hsF hQ)
        ⟨z, hfineOld Q (hsF hQ) ((fine Q).mem_carrier_of_mem_segment hz), rfl⟩
    exact haxisPull htheta htheta1 (Rnorm : Real) hRpos (U.cover.tube a.val R)
      (U.cover.tube b.val Q0) (normalization.normalized Q0).toTube
      (Tube.perp_norm_direction_le_of_subset _ _ hparent)
      (normalization.fine_direction Q0 hQ0F) (normalization.fine_centre Q0 hQ0F) z hnorm
  let target := Lgeom * theta * r
  let carrier : Tube target E := (fine Q0).rescale target
  have hscale : 14 * rho + (4 * tau : NNReal) <= (target : Real) := by
    have hsmall : 16 * (tau : Real) <= (theta : Real) * r := by exact_mod_cast htauSmall
    have hR : (1 : Real) <= Rnorm := hRnorm
    dsimp only [rho, target, Lgeom]
    push_cast
    nlinarith [mul_nonneg (sub_nonneg.mpr hR) (mul_nonneg theta.coe_nonneg r.coe_nonneg)]
  have hfiniteCover := hcentredCore s fine Q0 hQ0 (fun Q hQ => hfineCentred Q)
    (fun Q hQ => hfineMid Q) (U.cover.tube b.val Q0).center
    (U.cover.tube b.val Q0).direction (U.cover.tube b.val Q0).norm_direction rho hrho
    hcoreLine (4 * tau) target hscale
  let part := exactTubeCellW87 (canonicalQNodeFinsetW87 U0 current.active b)
    (fun w => U0.cover.tube b.val w.val) carrier
  have hfpart : ∀ Q ∈ s, f Q ∈ part := by
    intro Q hQ
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_attach _ _, ?_⟩
    exact (Tube.le_rescale_of_subset (fine Q) (U0.cover.tube b.val (f Q).val)
      (hfineCanonical Q)).trans (hfiniteCover Q hQ)
  have hcount : ∀ w ∈ part, ((s.filter (fun Q => f Q = w)).card : ENNReal) <= Cdegree := by
    intro w hw
    let fibre := s.filter (fun Q => f Q = w)
    let edge : iota -> iota × iota := fun Q => (Q, w.val)
    have hinj : Set.InjOn edge (fibre : Set iota) := fun x hx y hy h => congrArg Prod.fst h
    have hmap : fibre.image edge ⊆ edges.filter (fun e => e.2 = w.val) := by
      intro e he
      obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨hQs, hQw⟩ := Finset.mem_filter.mp hQ
      refine Finset.mem_filter.mpr ⟨?_, rfl⟩
      refine Finset.mem_image.mpr ⟨leaf Q, hleafA Q, ?_⟩
      have hv := congrArg Subtype.val hQw
      exact Prod.ext (hleaf Q (hsF hQs)).2.1 hv
    have hc : (fibre.card : NNReal) <= Cdegree := by
      calc
        _ = ((fibre.image edge).card : NNReal) := by rw [Finset.card_image_of_injOn hinj]
        _ <= ((edges.filter (fun e => e.2 = w.val)).card : NNReal) := by
          exact_mod_cast Finset.card_le_card hmap
        _ <= _ := hright w.val w.property
    exact_mod_cast hc
  have hgeo := hgeometric (delta := delta) (tau := tau) htau htau1 s part (U.cover.tube b.val)
    (fun w : CanonicalQNodeW87 U0 current.active b => U0.cover.tube b.val w.val) f
    (Cdegree : ENNReal) hfpart hcount (fun Q hQ => ⟨fine Q, hfineOld Q (hsF hQ), hfineCanonical Q⟩)
  have hpartNs := maxDensity_exactTubeCell_le_allExactTubeNs_w87 carrier ⟨f Q0, hfpart Q0 hQ0⟩
  calc
    _ <= (Cext : ENNReal) ^ 2 * maxDensity s old := hnormBackward s hsF
    _ <= (Cext : ENNReal) ^ 2 * ((48000 * (Cdegree : ENNReal)) *
        maxDensity part (fun w => (U0.cover.tube b.val w.val).toConvexSpaceBody)) :=
      mul_le_mul_right hgeo _
    _ <= (Cext : ENNReal) ^ 2 * ((48000 * (Cdegree : ENNReal)) *
        allExactTubeNsW87 (canonicalQNodeFinsetW87 U0 current.active b)
          (fun w => U0.cover.tube b.val w.val) target) :=
      mul_le_mul_right (mul_le_mul_right hpartNs _) _
    _ = _ := by simp only [Cden, target, theta, ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_ofNat]; ring

end

end Kakeya.ml1Boot.TrialRestartW94
