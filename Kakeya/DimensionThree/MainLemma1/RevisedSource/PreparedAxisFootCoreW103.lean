module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceMarginPreparationW98
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceAssignedNormalizationW97

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

/-- Fixed internal bin width, independent of packing constants and running scales. -/
def normalizationParameterMarginW98 : NNReal := (2 : NNReal)⁻¹ ^ (20 : Nat)

/-- Quantitative repair of the rejected exact-containment step. Both old
cores have actual parameter slack; both new cores are the literal axis feet. -/
theorem exists_axis_foot_unit_containment_margin_w98 (hdim : Module.finrank Real E = 3) :
    ∃ Rmin : NNReal, 1 <= Rmin ∧
      ∀ Rnorm : NNReal, Rmin <= Rnorm ->
      ∀ {tau sigma theta : NNReal}, 0 < tau -> 16 * tau <= sigma -> sigma <= theta -> theta <= 1 ->
      ∀ (top : Tube theta E) (parent : Tube sigma E) (fine : Tube tau E),
        parent.toConvexSpaceBody <= top.toConvexSpaceBody ->
        fine.toConvexSpaceBody <= parent.toConvexSpaceBody ->
        ‖fine.center - parent.center‖ <= (normalizationParameterMarginW98 : Real) * (sigma : Real) ->
        min (‖fine.direction - parent.direction‖) (‖fine.direction + parent.direction‖) <=
          (normalizationParameterMarginW98 : Real) * (sigma : Real) ->
        ∃ (W : Tube (tau / theta) E) (P : Tube (sigma / theta) E),
          W.toConvexSpaceBody <= P.toConvexSpaceBody ∧
          top.rescaleMap (Rnorm : Real) '' fine.carrier ⊆ W.carrier ∧
          top.rescaleMap (Rnorm : Real) '' parent.carrier ⊆ P.carrier ∧
          W.carrier ⊆ Metric.closedBall 0 1 ∧ P.carrier ⊆ Metric.closedBall 0 2 ∧
          W.direction = ‖(top.rescaleMap (Rnorm : Real)).linear fine.direction‖⁻¹ •
            (top.rescaleMap (Rnorm : Real)).linear fine.direction ∧
          P.direction = ‖(top.rescaleMap (Rnorm : Real)).linear parent.direction‖⁻¹ •
            (top.rescaleMap (Rnorm : Real)).linear parent.direction ∧
          W.center = top.rescaleMap (Rnorm : Real) fine.center -
            inner Real (top.rescaleMap (Rnorm : Real) fine.center) W.direction • W.direction ∧
          P.center = top.rescaleMap (Rnorm : Real) parent.center -
            inner Real (top.rescaleMap (Rnorm : Real) parent.center) P.direction • P.direction := by
  let Rmin : NNReal := max 1 (Tube.normalization.C 3)
  refine ⟨Rmin, le_max_left _ _, ?_⟩
  intro Rnorm hRmin tau sigma theta ht hgap hst ht1 top parent fine hpTop hfParent hcentre hdir
  have hR1 : (1 : Real) <= Rnorm := by
    exact_mod_cast (show (1 : NNReal) <= Rnorm from (le_max_left _ _).trans hRmin)
  have hR : (0 : Real) < Rnorm := zero_lt_one.trans_le hR1
  have hs : 0 < sigma := (mul_pos (by norm_num) ht).trans_le hgap
  have htheta : 0 < theta := hs.trans_le hst
  have hts : tau <= sigma := by nlinarith
  have httheta : tau <= theta := hts.trans hst
  let Phi := top.rescaleMap (Rnorm : Real)
  have hPhiBall : Phi '' top.carrier ⊆ Metric.closedBall 0 (1 / 4 : Real) := by
    apply Tube.rescale_image_ambient_subset_closedBall htheta ht1 hR
    simpa only [hdim] using
      (show (Tube.normalization.C 3 : Real) <= Rnorm by
        exact_mod_cast ((le_max_right _ _).trans hRmin : Tube.normalization.C 3 <= Rnorm))
  have hlinear (v : E) : Phi.linear v = Phi v - Phi 0 := by
    simpa only [vsub_eq_sub, sub_zero] using Phi.linearMap_vsub v 0
  have hupper (x y : E) :
      dist (Phi x) (Phi y) <= (theta : Real)⁻¹ * dist x y / (4 * (Rnorm : Real)) := by
    rw [Tube.dist_rescaleMap top hR]
    exact div_le_div_of_nonneg_right (Tube.dist_normalization_le htheta ht1 top x y)
      (by positivity)
  have hlower (v : E) : ‖v‖ / (4 * (Rnorm : Real)) <= ‖Phi.linear v‖ := by
    rw [hlinear, ← dist_eq_norm, Tube.dist_rescaleMap top hR]
    exact div_le_div_of_nonneg_right
      (by simpa only [dist_zero_right] using Tube.dist_le_dist_normalization htheta ht1 top v 0)
      (by positivity)
  have hnonzero {r : NNReal} (V : Tube r E) : Phi.linear V.direction ≠ 0 := by
    intro hz
    have h := hlower V.direction
    rw [hz, norm_zero, V.norm_direction] at h
    exact (not_le_of_gt (by positivity : (0 : Real) < 1 / (4 * (Rnorm : Real)))) h
  have hmidpoint {r : NNReal} (V : Tube r E) : V.midpoint = V.center := by
    simp only [Tube.midpoint, Tube.center, midpoint_eq_smul_add]
    norm_num
  have hbuild {r : NNReal} (hr : 0 < r) (hrt : r <= theta) (V : Tube r E)
      (hV : V.toConvexSpaceBody <= top.toConvexSpaceBody) :
      ∃ W : Tube (r / theta) E,
        Phi '' V.carrier ⊆ W.carrier ∧
        W.direction = ‖Phi.linear V.direction‖⁻¹ • Phi.linear V.direction ∧
        W.center = Phi V.center - inner Real (Phi V.center) W.direction • W.direction ∧
        ‖W.center‖ <= 1 / 4 := by
    let v := Phi.linear V.direction
    let u := ‖v‖⁻¹ • v
    let x := Phi V.center
    let m := x - inner Real x u • u
    have hv : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr (hnonzero V)
    have hu : ‖u‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hv]
    have hvu : ‖v‖ • u = v := by
      simp only [u, smul_smul, mul_inv_cancel₀ hv, one_smul]
    let W : Tube (r / theta) E := Tube.ofMidpointDirection (r / theta) m u hu
    have hWdir : W.direction = u := Tube.direction_ofMidpointDirection' m u hu
    have hWmid : W.midpoint = m := Tube.midpoint_ofMidpointDirection' m u hu
    have hWcentre : W.center = m := (hmidpoint W).symm.trans hWmid
    have hxNorm : ‖x‖ <= 1 / 4 := by
      have hvc : V.center ∈ V.carrier := hmidpoint V ▸ Tube.midpoint_mem_carrier hr V
      have h := hPhiBall ⟨V.center, hV hvc, rfl⟩
      simpa only [Metric.mem_closedBall, dist_zero_right] using h
    have hmNorm : ‖m‖ <= 1 / 4 := by
      have h := Tube.norm_perp_le W x
      rw [hWdir, real_inner_comm] at h
      exact h.trans hxNorm
    have haxis : ∀ p ∈ segment Real V.x V.y,
        Phi p = m + inner Real (Phi p) u • u := by
      rintro p ⟨a, b, ha, hb, hab, rfl⟩
      have hpoint : a • V.x + b • V.y = V.center + (b - 1 / 2 : Real) • V.direction := by
        rw [Tube.x_eq_center_sub, Tube.y_eq_center_add, show a = 1 - b by linarith]
        module
      have himage : Phi (a • V.x + b • V.y) = x + ((b - 1 / 2) * ‖v‖) • u := by
        rw [hpoint, show V.center + (b - 1 / 2 : Real) • V.direction =
          (b - 1 / 2 : Real) • V.direction + V.center from add_comm _ _, show
          Phi ((b - 1 / 2 : Real) • V.direction + V.center) =
            Phi.linear ((b - 1 / 2 : Real) • V.direction) + Phi V.center from
              Phi.map_vadd V.center ((b - 1 / 2 : Real) • V.direction),
          map_smul]
        change (b - 1 / 2 : Real) • v + x = x + ((b - 1 / 2) * ‖v‖) • u
        conv_lhs => rw [← hvu]
        rw [smul_smul, add_comm]
      rw [himage]
      have huu : inner Real u u = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
      simp only [inner_add_left, real_inner_smul_left, huu, mul_one]
      dsimp [m]
      module
    have hcore : ∀ p ∈ segment Real V.x V.y, Phi p ∈ segment Real W.x W.y := by
      intro p hp
      have hpV : p ∈ V.carrier := by
        rw [V.carrier_eq]
        exact Set.mem_iUnion₂.mpr ⟨p, hp, Metric.mem_closedBall_self r.coe_nonneg⟩
      have hpNorm : ‖Phi p‖ <= 1 / 4 := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hPhiBall ⟨p, hV hpV, rfl⟩
      have hcoord : |inner Real (Phi p) u| <= 1 / 4 := by
        calc |inner Real (Phi p) u| <= ‖Phi p‖ * ‖u‖ := abs_real_inner_le_norm _ _
          _ <= 1 / 4 := by rw [hu, mul_one]; exact hpNorm
      have hseg := W.midpoint_add_smul_direction_mem_segment
        (s := inner Real (Phi p) u) (by linarith [(abs_le.mp hcoord).1])
          (by linarith [(abs_le.mp hcoord).2])
      rw [hWmid, hWdir, ← haxis p hp] at hseg
      exact hseg
    refine ⟨W, ?_, hWdir, ?_, hWcentre ▸ hmNorm⟩
    · rintro z ⟨y, hy, rfl⟩
      rw [V.carrier_eq] at hy
      obtain ⟨p, hp, hyp⟩ := Set.mem_iUnion₂.mp hy
      rw [W.carrier_eq]
      refine Set.mem_iUnion₂.mpr ⟨Phi p, hcore p hp, Metric.mem_closedBall.mpr ?_⟩
      have hdist := Metric.mem_closedBall.mp hyp
      calc
        dist (Phi y) (Phi p) <= (theta : Real)⁻¹ * dist y p / (4 * (Rnorm : Real)) := hupper y p
        _ <= (theta : Real)⁻¹ * r / (4 * (Rnorm : Real)) := by gcongr
        _ <= (theta : Real)⁻¹ * r := by
          apply div_le_self (by positivity)
          nlinarith
        _ = ((r / theta : NNReal) : Real) := by push_cast; ring
    · rw [hWcentre, hWdir]
  obtain ⟨W, hWimage, hWdir, hWcentre, hWnorm⟩ := hbuild ht httheta fine (hfParent.trans hpTop)
  obtain ⟨P, hPimage, hPdir, hPcentre, hPnorm⟩ := hbuild hs hst parent hpTop
  have hball {r : NNReal} (V : Tube r E) (hV : ‖V.center‖ <= 1 / 4) :
      V.carrier ⊆ Metric.closedBall 0 (3 / 4 + (r : Real)) := by
    intro z hz
    rw [V.carrier_eq] at hz
    obtain ⟨p, hp, hzp⟩ := Set.mem_iUnion₂.mp hz
    have hpBall : p ∈ Metric.closedBall V.center (1 / 2 : Real) := by
      apply (convex_closedBall V.center (1 / 2 : Real)).segment_subset ?_ ?_ hp
      · rw [Metric.mem_closedBall, dist_eq_norm, Tube.x_eq_center_sub]
        simp only [sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, V.norm_direction]
        norm_num
      · rw [Metric.mem_closedBall, dist_eq_norm, Tube.y_eq_center_add]
        simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, V.norm_direction]
        norm_num
    have hdist : dist z V.center <= 1 / 2 + (r : Real) := by
      have htri := dist_triangle z p V.center
      have hp' := Metric.mem_closedBall.mp hpBall
      have hzp' := Metric.mem_closedBall.mp hzp
      linarith
    have htri := norm_add_le (z - V.center) V.center
    rw [sub_add_cancel] at htri
    rw [dist_eq_norm] at hdist
    rw [Metric.mem_closedBall, dist_zero_right]
    linarith
  have hWball : W.carrier ⊆ Metric.closedBall 0 1 := by
    refine (hball W hWnorm).trans (Metric.closedBall_subset_closedBall ?_)
    have hratio : (tau : Real) / theta <= 1 / 16 := by
      apply (div_le_iff₀ (show (0 : Real) < theta from htheta)).mpr
      have hg : 16 * (tau : Real) <= sigma := by exact_mod_cast hgap
      have hs' : (sigma : Real) <= theta := hst
      linarith
    push_cast
    linarith
  have hPball : P.carrier ⊆ Metric.closedBall 0 2 := by
    refine (hball P hPnorm).trans (Metric.closedBall_subset_closedBall ?_)
    have hratio : (sigma : Real) / theta <= 1 := (div_le_one (show (0 : Real) < theta from htheta)).mpr hst
    push_cast
    linarith
  refine ⟨W, P, ?_, hWimage, hPimage, hWball, hPball, hWdir, hPdir, hWcentre, hPcentre⟩
  let c : Real := 1 / (4 * (Rnorm : Real))
  let k : Real := (normalizationParameterMarginW98 : Real) * sigma / theta
  have hc : 0 < c := by dsimp [c]; positivity
  have hc1 : c <= 1 := by
    dsimp [c]
    apply (div_le_one (by positivity : (0 : Real) < 4 * (Rnorm : Real))).mpr
    nlinarith
  have hk : 0 <= k := by dsimp [k]; positivity
  have hupperLinear (v : E) : ‖Phi.linear v‖ <= c * (theta : Real)⁻¹ * ‖v‖ := by
    rw [hlinear, ← dist_eq_norm]
    convert hupper v 0 using 1 <;> simp only [dist_zero_right, c] <;> ring
  have hnormalization (v w u t : E) (hu : ‖u‖ = 1) (ht : ‖t‖ = 1)
      (hv : v = ‖v‖ • u) (hw : w = ‖w‖ • t) :
      ‖v‖ * ‖u - t‖ <= 2 * ‖v - w‖ := by
    calc
      ‖v‖ * ‖u - t‖ = ‖‖v‖ • (u - t)‖ := by rw [norm_smul, norm_norm]
      _ = ‖v - w + (‖w‖ - ‖v‖) • t‖ := by
        congr 1
        conv_rhs => lhs; rw [hv, hw]
        module
      _ <= ‖v - w‖ + ‖(‖w‖ - ‖v‖) • t‖ := norm_add_le _ _
      _ = ‖v - w‖ + |‖w‖ - ‖v‖| := by rw [norm_smul, Real.norm_eq_abs, ht, mul_one]
      _ <= 2 * ‖v - w‖ := by
        have h := abs_norm_sub_norm_le w v
        rw [norm_sub_rev w v] at h
        linarith
  obtain ⟨s, hsSign, hsource⟩ : ∃ s : Real, (s = 1 ∨ s = -1) ∧
      ‖fine.direction - s • parent.direction‖ <=
        (normalizationParameterMarginW98 : Real) * sigma := by
    rcases le_total ‖fine.direction - parent.direction‖ ‖fine.direction + parent.direction‖ with h | h
    · refine ⟨1, Or.inl rfl, ?_⟩
      simpa only [one_smul, min_eq_left h] using hdir
    · refine ⟨-1, Or.inr rfl, ?_⟩
      simpa only [neg_one_smul, sub_neg_eq_add, min_eq_right h] using hdir
  have hsabs : |s| = 1 := by rcases hsSign with rfl | rfl <;> norm_num
  have hsNorm : ‖s • P.direction‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, hsabs, P.norm_direction, mul_one]
  have hvFine : Phi.linear fine.direction = ‖Phi.linear fine.direction‖ • W.direction := by
    rw [hWdir, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr (hnonzero fine)), one_smul]
  have hvParent : s • Phi.linear parent.direction =
      ‖s • Phi.linear parent.direction‖ • (s • P.direction) := by
    rw [norm_smul, Real.norm_eq_abs, hsabs, one_mul, hPdir]
    simp only [smul_smul]
    have hn : ‖Phi.linear parent.direction‖ ≠ 0 := norm_ne_zero_iff.mpr (hnonzero parent)
    congr 1
    field_simp
  have hlinearDiff : ‖Phi.linear fine.direction - s • Phi.linear parent.direction‖ <= c * k := by
    rw [← map_smul, ← map_sub]
    calc
      ‖Phi.linear (fine.direction - s • parent.direction)‖ <=
          c * (theta : Real)⁻¹ * ‖fine.direction - s • parent.direction‖ := hupperLinear _
      _ <= c * (theta : Real)⁻¹ * ((normalizationParameterMarginW98 : Real) * sigma) := by gcongr
      _ = c * k := by dsimp [k]; ring
  have hunitDiff : ‖W.direction - s • P.direction‖ <= 2 * k := by
    have h := hnormalization (Phi.linear fine.direction) (s • Phi.linear parent.direction)
      W.direction (s • P.direction) W.norm_direction hsNorm hvFine hvParent
    have hlow : c <= ‖Phi.linear fine.direction‖ := by
      simpa only [fine.norm_direction] using hlower fine.direction
    have hprod := mul_le_mul_of_nonneg_right hlow (norm_nonneg (W.direction - s • P.direction))
    nlinarith [hlinearDiff]
  let x := Phi fine.center
  let y := Phi parent.center
  have hy : ‖y‖ <= 1 / 4 := by
    have hpc : parent.center ∈ parent.carrier := hmidpoint parent ▸ Tube.midpoint_mem_carrier hs parent
    simpa only [Metric.mem_closedBall, dist_zero_right] using hPhiBall ⟨parent.center, hpTop hpc, rfl⟩
  have hxy : ‖x - y‖ <= k := by
    have h := hupper fine.center parent.center
    rw [dist_eq_norm, dist_eq_norm] at h
    calc
      ‖x - y‖ <= (theta : Real)⁻¹ * ‖fine.center - parent.center‖ / (4 * (Rnorm : Real)) := h
      _ <= (theta : Real)⁻¹ * ((normalizationParameterMarginW98 : Real) * sigma) /
          (4 * (Rnorm : Real)) := by gcongr
      _ = c * k := by dsimp [c, k]; ring
      _ <= k := by nlinarith
  let u := W.direction
  let v := s • P.direction
  have hPfoot : P.center = y - inner Real y v • v := by
    rw [hPcentre]
    rcases hsSign with rfl | rfl
    · simp only [v, one_smul, y]
    · simp only [v, neg_one_smul, inner_neg_right, neg_smul, smul_neg, neg_neg, one_smul, y]
  have hfootDiff : ‖W.center - P.center‖ <= 2 * k := by
    have hu : ‖u‖ = 1 := W.norm_direction
    have hv : ‖v‖ = 1 := hsNorm
    have hdecomp : W.center - P.center =
        ((x - y) - inner Real u (x - y) • u) +
        (inner Real y v • (v - u) + inner Real y (v - u) • u) := by
      rw [hWcentre, hPfoot]
      simp only [u, inner_sub_left, inner_sub_right, real_inner_comm]
      module
    have hperp := Tube.norm_perp_le W (x - y)
    have hproj : ‖inner Real y v • (v - u) + inner Real y (v - u) • u‖ <=
        2 * ‖y‖ * ‖v - u‖ := by
      calc
        _ <= ‖inner Real y v • (v - u)‖ + ‖inner Real y (v - u) • u‖ := norm_add_le _ _
        _ = |inner Real y v| * ‖v - u‖ + |inner Real y (v - u)| := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, hu, mul_one]
        _ <= (‖y‖ * ‖v‖) * ‖v - u‖ + ‖y‖ * ‖v - u‖ := by
          gcongr
          · exact abs_real_inner_le_norm _ _
          · exact abs_real_inner_le_norm _ _
        _ = 2 * ‖y‖ * ‖v - u‖ := by rw [hv]; ring
    have hdiff : ‖v - u‖ <= 2 * k := by
      rw [norm_sub_rev]
      exact hunitDiff
    calc
      ‖W.center - P.center‖ <= ‖(x - y) - inner Real u (x - y) • u‖ +
          ‖inner Real y v • (v - u) + inner Real y (v - u) • u‖ := by
        rw [hdecomp]
        exact norm_add_le _ _
      _ <= ‖x - y‖ + 2 * ‖y‖ * ‖v - u‖ := add_le_add hperp hproj
      _ <= 2 * k := by nlinarith [norm_nonneg y, norm_nonneg (v - u)]
  have hcoreClose : ∀ z ∈ segment Real W.x W.y,
      ∃ p ∈ segment Real P.x P.y, dist z p <= 3 * k := by
    rintro z ⟨a, b, ha, hb, hab, rfl⟩
    let t : Real := b - 1 / 2
    have ht : |t| <= 1 / 2 := by dsimp [t]; rw [abs_le]; constructor <;> linarith
    have hst : |s * t| <= 1 / 2 := by rw [abs_mul, hsabs, one_mul]; exact ht
    let p := P.center + (s * t) • P.direction
    have hp : p ∈ segment Real P.x P.y := by
      have h := P.midpoint_add_smul_direction_mem_segment (s := s * t)
        (abs_le.mp hst).1 (abs_le.mp hst).2
      rwa [hmidpoint P] at h
    refine ⟨p, hp, ?_⟩
    have hvec : (a • W.x + b • W.y) - p =
        (W.center - P.center) + t • (W.direction - s • P.direction) := by
      rw [Tube.x_eq_center_sub, Tube.y_eq_center_add, show a = 1 - b by linarith]
      dsimp [p, t]
      module
    rw [dist_eq_norm, hvec]
    calc
      _ <= ‖W.center - P.center‖ + ‖t • (W.direction - s • P.direction)‖ := norm_add_le _ _
      _ = ‖W.center - P.center‖ + |t| * ‖W.direction - s • P.direction‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      _ <= 3 * k := by nlinarith [norm_nonneg (W.direction - s • P.direction)]
  intro z hz
  change z ∈ W.carrier at hz
  rw [W.carrier_eq] at hz
  obtain ⟨w, hw, hzw⟩ := Set.mem_iUnion₂.mp hz
  obtain ⟨p, hp, hwp⟩ := hcoreClose w hw
  change z ∈ P.carrier
  rw [P.carrier_eq]
  refine Set.mem_iUnion₂.mpr ⟨p, hp, Metric.mem_closedBall.mpr ?_⟩
  have hzw' := Metric.mem_closedBall.mp hzw
  have hgapReal : 16 * (tau : Real) <= sigma := by exact_mod_cast hgap
  have hκ : (normalizationParameterMarginW98 : Real) <= 1 / 100 := by
    norm_num [normalizationParameterMarginW98]
  have hsmall : (tau : Real) / theta + 3 * k <= (sigma : Real) / theta := by
    apply (le_div_iff₀ (show (0 : Real) < theta from htheta)).mpr
    dsimp [k]
    field_simp
    nlinarith [mul_le_mul_of_nonneg_right hκ sigma.coe_nonneg]
  calc
    dist z p <= dist z w + dist w p := dist_triangle z w p
    _ <= ((tau / theta : NNReal) : Real) + 3 * k := add_le_add hzw' hwp
    _ <= ((sigma / theta : NNReal) : Real) := by simpa only [NNReal.coe_div] using hsmall

end

end Kakeya.ml1Boot.TrialRestartW94
