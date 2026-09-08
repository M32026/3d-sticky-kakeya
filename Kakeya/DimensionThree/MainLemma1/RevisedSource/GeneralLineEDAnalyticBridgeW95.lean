module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.DetailedTrialDefinitionsW95
public import Kakeya.DimensionThree.MainLemma2.CanonicalCentredCover
public import Kakeya.DimensionThree.Plank.FlatPrismInnerEstimate

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology
open scoped ENNReal NNReal

namespace Kakeya.ml1Boot.TrialRestartW94

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

universe uE uI

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]

/-- Perpendicular axis coordinate only; the tube and shading are unchanged. -/
def axisFootW95 {delta : NNReal} (T : Tube delta E) : E :=
  Tube.lineFoot T.center T.direction

/-- Delta-independent cardinality bound for the two sign boxes of line parameters. -/
def lineAmplificationBoundW95 (n : Nat) (R K : Real) : Nat :=
  Nat.ceil (2 * (4 * (R + 1) * (K - 1) * (1 + 8 * R) + 1) ^ n *
    (16 * (R + 1) * (K - 1) + 1) ^ n)

def nearLineFamilyW95 {iota : Type uI} {delta : NNReal}
    (F : Finset iota) (T : iota -> Tube delta E) (o v : E) (K : Real) : Finset iota :=
  F.filter (fun i => (T i).carrier ⊆ VeryNotSticky.lineNbhd o v (K * (delta : Real)))

/-- E1: finite actual representatives for arbitrary, possibly noncentred
tubes. Assignment uses the representatives' complete axes; no tube moves. -/
theorem exists_radius_five_line_bins_w95
    {iota : Type uI} {delta : NNReal} (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (F : Finset iota) (T : iota -> Tube delta E)
    (R K : Real) (hR : 0 <= R) (hK : 1 <= K)
    (hcenter : ∀ i ∈ F, ‖(T i).center‖ <= R)
    (o v : E) (hv : ‖v‖ = 1) :
    ∃ (G : Finset iota) (assign : iota -> iota),
      G ⊆ nearLineFamilyW95 F T o v K ∧
      G.card <= lineAmplificationBoundW95 (Module.finrank Real E) R K ∧
      (∀ i ∈ nearLineFamilyW95 F T o v K, assign i ∈ G) ∧
      (∀ i ∈ nearLineFamilyW95 F T o v K,
        (T i).carrier ⊆ VeryNotSticky.lineNbhd
          (T (assign i)).center (T (assign i)).direction (5 * (delta : Real))) := by
  classical
  have hd : (0 : Real) < delta := by exact_mod_cast hdelta
  have hRp : 0 < R + 1 := by linarith
  have hKm : 0 <= K - 1 := sub_nonneg.mpr hK
  have hmid : ∀ i, (T i).midpoint = (T i).center := by
    intro i
    simp only [Tube.center, midpoint_eq_smul_add, Tube.midpoint]
    norm_num
  let H := nearLineFamilyW95 F T o v K
  let r : Real := (delta : Real) / (R + 1)
  let Rx : Real := (K - 1) * (delta : Real) * (1 + 8 * R)
  let Ry : Real := 4 * ((K - 1) * (delta : Real))
  have hr : 0 < r := div_pos hd hRp
  have hRx : 0 <= Rx := by dsimp [Rx]; positivity
  have hRy : 0 <= Ry := by dsimp [Ry]; positivity
  have hHF : H ⊆ F := Finset.filter_subset _ _
  have hparams : ∀ i ∈ H,
      (∃ s : Real, (s = 1 ∨ s = -1) ∧ ‖(T i).direction - s • v‖ <= Ry) ∧
        ‖axisFootW95 (T i) - Tube.lineFoot o v‖ <= Rx := by
    intro i hi
    have hline : (T i).carrier ⊆ Metric.cthickening (K * (delta : Real))
        (Set.range fun t : Real => o + t • v) := by
      simpa only [VeryNotSticky.lineNbhd_eq_cthickening_range] using
        (Finset.mem_filter.mp hi).2
    have hcore : ∀ z ∈ segment Real (T i).x (T i).y,
        Tube.lineDist o v z <= (K - 1) * (delta : Real) := by
      intro z hz
      have hzdist := Tube.lineDist_le_of_carrier_subset (T i) hv
        (show (delta : Real) <= K * (delta : Real) by nlinarith) hline hz
      linarith
    obtain ⟨s, hs, hdir⟩ := Tube.exists_sign_norm_direction_sub_le (T i) hv
      (hcore _ (left_mem_segment Real _ _)) (hcore _ (right_mem_segment Real _ _))
    refine ⟨⟨s, hs, hdir⟩, ?_⟩
    have hw : ‖s • v‖ = 1 := by rcases hs with rfl | rfl <;> simp [hv]
    have hprojection : inner Real (T i).center v • v =
        inner Real (T i).center (s • v) • (s • v) := by
      rcases hs with rfl | rfl <;> simp
    have hproj : ‖inner Real (T i).center v • v -
        inner Real (T i).center (T i).direction • (T i).direction‖ <=
          2 * ‖(T i).center‖ * ‖(T i).direction - s • v‖ := by
      rw [hprojection]
      have hsplit : inner Real (T i).center (s • v) • (s • v) -
          inner Real (T i).center (T i).direction • (T i).direction =
            inner Real (T i).center (s • v) • (s • v - (T i).direction) +
              inner Real (T i).center (s • v - (T i).direction) • (T i).direction := by
        simp only [inner_sub_right]
        module
      rw [hsplit]
      calc
        _ <= ‖inner Real (T i).center (s • v) • (s • v - (T i).direction)‖ +
            ‖inner Real (T i).center (s • v - (T i).direction) • (T i).direction‖ :=
          norm_add_le _ _
        _ = |inner Real (T i).center (s • v)| * ‖s • v - (T i).direction‖ +
            |inner Real (T i).center (s • v - (T i).direction)| := by
          simp only [norm_smul, Real.norm_eq_abs, (T i).norm_direction, mul_one]
        _ <= (‖(T i).center‖ * ‖s • v‖) * ‖s • v - (T i).direction‖ +
            ‖(T i).center‖ * ‖s • v - (T i).direction‖ := by
          gcongr <;> exact abs_real_inner_le_norm _ _
        _ = 2 * ‖(T i).center‖ * ‖(T i).direction - s • v‖ := by
          rw [hw, norm_sub_rev (s • v)]
          ring
    have hcentre : Tube.lineDist o v (T i).center <= (K - 1) * (delta : Real) :=
      hcore _ (midpoint_mem_segment (𝕜 := Real) _ _)
    have hfoot : axisFootW95 (T i) - Tube.lineFoot o v =
        (((T i).center - o) - inner Real ((T i).center - o) v • v) +
          (inner Real (T i).center v • v -
            inner Real (T i).center (T i).direction • (T i).direction) := by
      dsimp [axisFootW95, Tube.lineFoot]
      rw [inner_sub_left]
      module
    rw [hfoot]
    calc
      _ <= Tube.lineDist o v (T i).center +
          ‖inner Real (T i).center v • v -
            inner Real (T i).center (T i).direction • (T i).direction‖ := norm_add_le _ _
      _ <= (K - 1) * (delta : Real) +
          2 * ‖(T i).center‖ * ‖(T i).direction - s • v‖ := add_le_add hcentre hproj
      _ <= (K - 1) * (delta : Real) + 2 * R * Ry := by
        gcongr
        · exact hcenter i (hHF hi)
      _ = Rx := by dsimp [Rx, Ry]; ring
  obtain ⟨G, hGH, hsep, hcover⟩ := exists_maximal_separated_finset H
    (fun i j => ‖axisFootW95 (T i) - axisFootW95 (T j)‖ +
      ‖(T i).direction - (T j).direction‖) (ε := r)
    (fun _ => by simpa using hr)
    (fun i j => by rw [norm_sub_rev (axisFootW95 (T i)), norm_sub_rev (T i).direction])
  let Gp := G.filter (fun i => ‖(T i).direction - (1 : Real) • v‖ <= Ry)
  let Gm := G.filter (fun i => ‖(T i).direction - (-1 : Real) • v‖ <= Ry)
  have hsplit : G ⊆ Gp ∪ Gm := by
    intro i hi
    obtain ⟨s, hs, hdir⟩ := (hparams i (hGH hi)).1
    rcases hs with rfl | rfl
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hi, hdir⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hi, hdir⟩))
  have hbox : ∀ (s : Real) (J : Finset iota), J ⊆ G ->
      (∀ i ∈ J, ‖(T i).direction - s • v‖ <= Ry) ->
      (J.card : Real) <= ((Rx + r / 4) / (r / 4)) ^ Module.finrank Real E *
        ((Ry + r / 4) / (r / 4)) ^ Module.finrank Real E := by
    intro s J hJG hJdir
    exact Tube.card_le_of_L1_separated_in_rectangle J (fun i => axisFootW95 (T i))
      (fun i => (T i).direction) (Tube.lineFoot o v) (s • v) hr hRx hRy
      (fun i hi j hj hij => hsep i (hJG hi) j (hJG hj) hij)
      (fun i hi => (hparams i (hGH (hJG hi))).2) hJdir
  have hp := hbox 1 Gp (Finset.filter_subset _ _) (fun i hi => (Finset.mem_filter.mp hi).2)
  have hm := hbox (-1) Gm (Finset.filter_subset _ _) (fun i hi => (Finset.mem_filter.mp hi).2)
  have hcard : (G.card : Real) <= (Gp.card : Real) + (Gm.card : Real) := by
    exact_mod_cast (Finset.card_le_card hsplit).trans (Finset.card_union_le _ _)
  have hxratio : (Rx + r / 4) / (r / 4) = 4 * (R + 1) * (K - 1) * (1 + 8 * R) + 1 := by
    dsimp [Rx, r]
    field_simp
  have hyratio : (Ry + r / 4) / (r / 4) = 16 * (R + 1) * (K - 1) + 1 := by
    dsimp [Ry, r]
    field_simp
    ring
  rw [hxratio, hyratio] at hp hm
  have hGcard : G.card <= lineAmplificationBoundW95 (Module.finrank Real E) R K := by
    have hreal : (G.card : Real) <=
        2 * (4 * (R + 1) * (K - 1) * (1 + 8 * R) + 1) ^ Module.finrank Real E *
          (16 * (R + 1) * (K - 1) + 1) ^ Module.finrank Real E := by
      nlinarith only [hcard, hp, hm]
    exact_mod_cast hreal.trans (Nat.le_ceil _)
  let assign : iota -> iota := fun i => if hi : i ∈ H then (hcover i hi).choose else i
  have hass : ∀ i (hi : i ∈ H), assign i ∈ G ∧
      ‖axisFootW95 (T i) - axisFootW95 (T (assign i))‖ +
        ‖(T i).direction - (T (assign i)).direction‖ < r := by
    intro i hi
    simpa only [assign, dif_pos hi] using (hcover i hi).choose_spec
  refine ⟨G, assign, hGH, hGcard, fun i hi => (hass i hi).1, ?_⟩
  intro i hi x hx
  obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.mp ((T i).carrier_eq ▸ hx)
  obtain ⟨t, ht, hzt⟩ := (T i).exists_param_of_mem_segment hz
  rw [hmid] at hzt
  let c : Real := inner Real (T i).center (T i).direction + t
  have hc : |c| <= R + 1 := by
    calc
      |c| <= |inner Real (T i).center (T i).direction| + |t| := abs_add_le _ _
      _ <= ‖(T i).center‖ * ‖(T i).direction‖ + (1 / 2 : Real) :=
        add_le_add (abs_real_inner_le_norm _ _) ht
      _ <= R + 1 := by rw [(T i).norm_direction, mul_one]; linarith [hcenter i (hHF hi)]
  let j := assign i
  have hzaxis : z - ((T j).center +
      (c - inner Real (T j).center (T j).direction) • (T j).direction) =
        (axisFootW95 (T i) - axisFootW95 (T j)) + c • ((T i).direction - (T j).direction) := by
    rw [hzt]
    dsimp [axisFootW95, Tube.lineFoot, c]
    module
  have hzclose : dist z ((T j).center +
      (c - inner Real (T j).center (T j).direction) • (T j).direction) <= (delta : Real) := by
    rw [dist_eq_norm, hzaxis]
    calc
      _ <= ‖axisFootW95 (T i) - axisFootW95 (T j)‖ +
          |c| * ‖(T i).direction - (T j).direction‖ := by
        simpa only [norm_smul, Real.norm_eq_abs] using norm_add_le
          (axisFootW95 (T i) - axisFootW95 (T j)) (c • ((T i).direction - (T j).direction))
      _ <= (R + 1) * (‖axisFootW95 (T i) - axisFootW95 (T j)‖ +
          ‖(T i).direction - (T j).direction‖) := by
        nlinarith [norm_nonneg (axisFootW95 (T i) - axisFootW95 (T j)),
          norm_nonneg ((T i).direction - (T j).direction)]
      _ <= (R + 1) * r := mul_le_mul_of_nonneg_left (hass i hi).2.le hRp.le
      _ = delta := by dsimp [r]; field_simp
  apply VeryNotSticky.mem_lineNbhd_of_dist_le
    (c - inner Real (T j).center (T j).direction)
  have hxz' := Metric.mem_closedBall.mp hxz
  have htriangle := dist_triangle x z ((T j).center +
    (c - inner Real (T j).center (T j).direction) • (T j).direction)
  linarith

/-- E1 counting corollary on the same unmodified family. -/
theorem lineED_five_implies_lineEDAt_w95
    {iota : Type uI} {delta : NNReal} (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (F : Finset iota) (T : iota -> Tube delta E) (A : Nat)
    (hline : VeryNotSticky.IsLineEssDistinct A F T)
    (R K : Real) (hR : 0 <= R) (hK : 1 <= K)
    (hcenter : ∀ i ∈ F, ‖(T i).center‖ <= R) :
    VeryNotSticky.IsLineEssDistinctAt K
      (lineAmplificationBoundW95 (Module.finrank Real E) R K * A) F T := by
  classical
  intro o v hv
  obtain ⟨G, assign, hG, hcard, hassign, hcover⟩ :=
    exists_radius_five_line_bins_w95 hdelta hdelta_one F T R K hR hK hcenter o v hv
  let B : iota -> Finset iota := fun j => F.filter (fun i =>
    (T i).carrier ⊆ VeryNotSticky.lineNbhd (T j).center (T j).direction
      (5 * (delta : Real)))
  have hBcard : ∀ j, (B j).card <= A :=
    fun j => hline (T j).center (T j).direction (T j).norm_direction
  have hcovered : nearLineFamilyW95 F T o v K ⊆ G.biUnion B := by
    intro i hi
    exact Finset.mem_biUnion.mpr ⟨assign i, hassign i hi,
      Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).1, hcover i hi⟩⟩
  calc
    (nearLineFamilyW95 F T o v K).card <= (G.biUnion B).card :=
      Finset.card_le_card hcovered
    _ <= ∑ j ∈ G, (B j).card := Finset.card_biUnion_le
    _ <= ∑ _j ∈ G, A := Finset.sum_le_sum (fun j _ => hBcard j)
    _ = G.card * A := by simp
    _ <= lineAmplificationBoundW95 (Module.finrank Real E) R K * A :=
      Nat.mul_le_mul_right A hcard

/-- P1's pointwise distance predicate is the same closed line neighbourhood. -/
theorem pointwise_line_neighbourhood_iff_w95
    {delta : NNReal} (T : Tube delta E) (o v : E) (hv : ‖v‖ = 1) :
    liesInFiveDeltaLineTubeW94 T o v ↔
      T.carrier ⊆ VeryNotSticky.lineNbhd o v (5 * (delta : Real)) := by
  constructor
  · intro h x hx
    obtain ⟨t, ht⟩ := h x hx
    exact VeryNotSticky.mem_lineNbhd_of_dist_le t ht
  · intro h x hx
    have hd : 0 <= 5 * (delta : Real) := by positivity
    have hdist := (Tube.mem_cthickening_line_iff hv hd).mp
      (show x ∈ Metric.cthickening (5 * (delta : Real))
        (Set.range fun t : Real => o + t • v) from by
          simpa only [VeryNotSticky.lineNbhd_eq_cthickening_range] using h hx)
    refine ⟨inner Real (x - o) v, ?_⟩
    simpa only [dist_eq_norm, Tube.norm_sub_foot_eq o v x hv] using hdist

/-- Integer counting against a real cap uses its floor, without a radius change. -/
theorem pointwise_lineED_iff_library_floor_w95
    {iota : Type uI} {delta : NNReal} (F : Finset iota) (T : iota -> Tube delta E)
    (C : NNReal) :
    lineEssentiallyDistinctW94 F T C ↔
      VeryNotSticky.IsLineEssDistinct (Nat.floor (C : Real)) F T := by
  have hfilter : ∀ o v, ‖v‖ = 1 ->
      F.filter (fun i => liesInFiveDeltaLineTubeW94 (T i) o v) =
        F.filter (fun i => (T i).carrier ⊆
          VeryNotSticky.lineNbhd o v (5 * (delta : Real))) := by
    intro o v hv
    exact Finset.filter_congr (fun i _ => pointwise_line_neighbourhood_iff_w95 (T i) o v hv)
  constructor
  · intro h o v hv
    apply (Nat.le_floor_iff C.coe_nonneg).mpr
    have hc := h o v hv
    rw [hfilter o v hv] at hc
    exact_mod_cast hc
  · intro h o v hv
    rw [hfilter o v hv]
    exact_mod_cast (Nat.le_floor_iff C.coe_nonneg).mp (h o v hv)

def lineSelectionMultiplicityW95 (n : Nat) (R : Real) (A : Nat) : Nat :=
  lineAmplificationBoundW95 n R (Kakeya.Tube.tubeOverlapCoreClose.C n) * A

/-- E2: the same actual pairwise family simultaneously retains mass and
cardinality and pays every analytic transport back to the original family. -/
theorem exists_pairwise_lineED_paid_w95
    {iota : Type uI} {delta : NNReal} (hdelta : 0 < delta) (hdelta_one : delta <= 1)
    (F : Finset iota) (Y : iota -> ShadedTube delta E) (hF : F.Nonempty)
    (R : Real) (hR : 0 <= R) (hcenter : ∀ i ∈ F, ‖(Y i).center‖ <= R)
    (A : Nat) (hA : 1 <= A)
    (hline : VeryNotSticky.IsLineEssDistinct A F (fun i => (Y i).toTube))
    (K0 : ConvexSpaceBody E) (hcontained : ∀ i ∈ F, (Y i).toConvexSpaceBody <= K0)
    (hmass : 0 < ∑ i ∈ F, volume (Y i).shade) :
    let M := lineSelectionMultiplicityW95 (Module.finrank Real E) R A
    ∃ q ⊆ F, q.Nonempty ∧
      (q : Set iota).Pairwise (fun i j => IsEssentiallyDistinct (Y i).carrier (Y j).carrier) ∧
      (∑ i ∈ F, volume (Y i).shade) <= (M : ENNReal) * (∑ i ∈ q, volume (Y i).shade) ∧
      F.card <= M * q.card ∧
      fullness' F (fun i => (Y i).toShadedBody) <=
        (M : ENNReal) * fullness' q (fun i => (Y i).toShadedBody) ∧
      frostmanConstIn q (fun i => (Y i).toConvexSpaceBody) K0 <=
        (M : ENNReal) * frostmanConstIn F (fun i => (Y i).toConvexSpaceBody) K0 ∧
      Kakeya.maxDensity q (fun i => (Y i).toConvexSpaceBody) <=
        Kakeya.maxDensity F (fun i => (Y i).toConvexSpaceBody) ∧
      ShadedBody.multiplicity F (fun i => (Y i).toShadedBody) <=
        (M : ENNReal) * ShadedBody.multiplicity q (fun i => (Y i).toShadedBody) := by
  classical
  let n := Module.finrank Real E
  let K := Kakeya.Tube.tubeOverlapCoreClose.C n
  let M := lineSelectionMultiplicityW95 n R A
  have hK : 1 <= K := (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C n).le
  have hB : 0 < lineAmplificationBoundW95 n R K := by
    apply Nat.ceil_pos.mpr
    have hKm : 0 <= K - 1 := sub_nonneg.mpr hK
    positivity
  have hM : 1 <= M := Nat.mul_pos hB (by omega)
  have hMzero : (M : ENNReal) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  have hline' := lineED_five_implies_lineEDAt_w95 hdelta hdelta_one F
    (fun i => (Y i).toTube) A hline R K hR hK hcenter
  obtain ⟨q, hqF, hqED, hqmass, hqcard⟩ :=
    VeryNotSticky.exists_pairwise_of_isLineEssDistinctAt hdelta hdelta_one hline'
      (fun i => volume (Y i).shade)
  change (∑ i ∈ F, volume (Y i).shade) <= ((M - 1 + 1 : Nat) : ENNReal) *
    (∑ i ∈ q, volume (Y i).shade) at hqmass
  change F.card <= (M - 1 + 1) * q.card at hqcard
  rw [Nat.sub_add_cancel hM] at hqmass hqcard
  have hq : q.Nonempty := by
    by_contra hn
    have hqe : q = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simpa [hqe, hF.card_ne_zero] using hqcard
  have hsum : (∑ i ∈ q, volume (Y i).carrier) <=
      ∑ i ∈ F, volume (Y i).carrier := Finset.sum_le_sum_of_subset hqF
  have hfull : fullness' F (fun i => (Y i).toShadedBody) <=
      (M : ENNReal) * fullness' q (fun i => (Y i).toShadedBody) := by
    unfold fullness'
    rw [← mul_div_assoc]
    exact ENNReal.div_le_div hqmass hsum
  obtain ⟨i0, hi0⟩ := hF
  have hvol : ∀ i ∈ F, volume (Y i).carrier = volume (Y i0).carrier := by
    intro i hi
    exact Tube.volume_carrier_eq_volume_carrier (Y i).toTube (Y i0).toTube
  have hretain : (M : ENNReal)⁻¹ * (F.card : ENNReal) <= (q.card : ENNReal) := by
    apply (ENNReal.inv_mul_le_iff hMzero (by simp)).mpr
    exact_mod_cast hqcard
  have hCF : frostmanConstIn q (fun i => (Y i).toConvexSpaceBody) K0 <=
      (M : ENNReal) * frostmanConstIn F (fun i => (Y i).toConvexSpaceBody) K0 := by
    simpa only [inv_inv] using frostmanConstIn_subfamily_le ⟨i0, hi0⟩ hvol hcontained
      hqF (show (M : ENNReal)⁻¹ ≠ 0 by simp) hretain
  refine ⟨q, hqF, hq, hqED, hqmass, hqcard, hfull, hCF,
    Kakeya.maxDensity_mono _ hqF, ?_⟩
  apply ShadedBody.multiplicity_le_mul_of_sum_shade_le_of_biUnion_subset F
    (fun i => (Y i).toShadedBody) q (fun i => (Y i).toShadedBody) M _ hqmass
  intro x hx
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
  exact Set.mem_iUnion₂.mpr ⟨i, hqF hi, hxi⟩

/-- E3: derive source line-ED KF from the existing project KF estimate.
The final multiplicity bound concerns the original family and shading. -/
theorem frostmanEstimate_lineED_version_w95
    (hdim : Module.finrank Real E = 3) (gamma : Real)
    (hgamma0 : 0 <= gamma) (hgamma1 : gamma <= 1)
    (hKF : FrostmanEstimate.{uI} E gamma) :
    ∀ e > (0 : Real), ∃ eta > (0 : Real),
      ∀ᶠ delta : NNReal in nhdsWithin 0 (Set.Ioi 0),
        ∀ {iota : Type uI} (F : Finset iota) (Y : iota -> ShadedTube delta E),
          (∀ i ∈ F, (Y i).carrier ⊆ Metric.closedBall 0 1) ->
          lineEssentiallyDistinctW94 F (fun i => (Y i).toTube) (delta ^ (-eta)) ->
          frostmanConstIn F (fun i => (Y i).toConvexSpaceBody)
            ConvexSpaceBody.closedUnitBall <= (delta : ENNReal) ^ (-eta) ->
          (delta : ENNReal) ^ eta <= fullness' F (fun i => (Y i).toShadedBody) ->
          ShadedBody.multiplicity F (fun i => (Y i).toShadedBody) <=
            (delta : ENNReal) ^ (-e - 2 * gamma) *
              ((F.card : ENNReal) * (delta : ENNReal) ^ (2 : Nat)) ^ (1 - gamma / 2) := by
  classical
  intro e he
  obtain ⟨eta0, heta0, hKFscale⟩ := hKF (e / 2) (by positivity)
  let eta : Real := min (eta0 / 4) (e / 8)
  have heta : 0 < eta := lt_min (by positivity) (by positivity)
  have heta0' : 3 * eta <= eta0 := by
    have := min_le_left (eta0 / 4) (e / 8)
    dsimp [eta]
    linarith
  have hetae : 2 * eta <= e / 2 := by
    have := min_le_right (eta0 / 4) (e / 8)
    dsimp [eta]
    linarith
  let B := lineAmplificationBoundW95 (Module.finrank Real E) 1
    (Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank Real E))
  have hBpos : 0 < B := by
    apply Nat.ceil_pos.mpr
    have hKm : 0 <= Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank Real E) - 1 :=
      sub_nonneg.mpr (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C _).le
    positivity
  obtain ⟨d0, hd0, hBscale⟩ := exists_threshold_ofReal_le_rpow
    (C := (B : Real)) (by exact_mod_cast hBpos) heta
  refine ⟨eta, heta, ?_⟩
  filter_upwards [hKFscale,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : NNReal) < 1 by norm_num)),
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hd0), self_mem_nhdsWithin] with
      delta hKFdelta hdelta_lt_one hdeltad0 hdelta
  intro iota F Y hball hline hCF hfull
  have hdelta1 : delta <= 1 := hdelta_lt_one.le
  have hd : (0 : NNReal) < delta := hdelta
  have hdE : (0 : ENNReal) < delta := by exact_mod_cast hd
  have hdE1 : (delta : ENNReal) <= 1 := by exact_mod_cast hdelta1
  have hpzero : ∀ t : Real, (delta : ENNReal) ^ t ≠ 0 :=
    fun _ => (ENNReal.rpow_pos hdE (by simp)).ne'
  have hpfinite : ∀ t : Real, (delta : ENNReal) ^ t ≠ ⊤ :=
    fun _ => ENNReal.rpow_ne_top_of_ne_zero hdE.ne' (by simp)
  by_cases hmass0 : (∑ i ∈ F, volume (Y i).shade) = 0
  · rw [ShadedBody.multiplicity_eq_div, hmass0, ENNReal.zero_div]
    exact zero_le
  have hmass : 0 < ∑ i ∈ F, volume (Y i).shade := bot_lt_iff_ne_bot.mpr hmass0
  have hF : F.Nonempty := by
    by_contra hn
    simpa [Finset.not_nonempty_iff_eq_empty.mp hn] using hmass0
  have hcenter : ∀ i ∈ F, ‖(Y i).center‖ <= (1 : Real) := by
    intro i hi
    have hmem := (Y i).toTube.mem_carrier_of_mem_segment
      (midpoint_mem_segment (𝕜 := Real) (Y i).x (Y i).y)
    simpa only [Metric.mem_closedBall, dist_zero_right] using hball i hi hmem
  let A := Nat.floor ((delta ^ (-eta) : NNReal) : Real)
  have hA : 1 <= A := by
    apply (Nat.one_le_floor_iff _).mpr
    exact_mod_cast NNReal.one_le_rpow_of_pos_of_le_one_of_nonpos hd hdelta1 (by linarith : -eta <= 0)
  have hlineA := (pointwise_lineED_iff_library_floor_w95 F
    (fun i => (Y i).toTube) (delta ^ (-eta))).mp hline
  let M := lineSelectionMultiplicityW95 (Module.finrank Real E) 1 A
  obtain ⟨q, hqF, hq, hqED, hqmass, hqcard, hqfull, hqCF, hqmax, hqmult⟩ :=
    exists_pairwise_lineED_paid_w95 hd hdelta1 F Y hF 1 (by norm_num) hcenter A hA
      hlineA ConvexSpaceBody.closedUnitBall hball hmass
  change fullness' F (fun i => (Y i).toShadedBody) <=
    (M : ENNReal) * fullness' q (fun i => (Y i).toShadedBody) at hqfull
  change frostmanConstIn q (fun i => (Y i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall <=
    (M : ENNReal) * frostmanConstIn F (fun i => (Y i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall at hqCF
  change ShadedBody.multiplicity F (fun i => (Y i).toShadedBody) <=
    (M : ENNReal) * ShadedBody.multiplicity q (fun i => (Y i).toShadedBody) at hqmult
  have hBE : (B : ENNReal) <= (delta : ENNReal) ^ (-eta) := by
    simpa only [ENNReal.ofReal_natCast] using hBscale delta hd hdeltad0
  have hAE : (A : ENNReal) <= (delta : ENNReal) ^ (-eta) := by
    rw [← ENNReal.coe_rpow_of_ne_zero hd.ne']
    apply ENNReal.coe_le_coe.mpr
    exact_mod_cast Nat.floor_le (delta ^ (-eta) : NNReal).coe_nonneg
  have hME : (M : ENNReal) <= (delta : ENNReal) ^ (-2 * eta) := by
    calc
      (M : ENNReal) = (B : ENNReal) * (A : ENNReal) := by
        simp only [M, B, lineSelectionMultiplicityW95, Nat.cast_mul]
      _ <= (delta : ENNReal) ^ (-eta) * (delta : ENNReal) ^ (-eta) := mul_le_mul' hBE hAE
      _ = (delta : ENNReal) ^ (-2 * eta) := by
        rw [← ENNReal.rpow_add _ _ hdE.ne' (by simp)]
        congr 1
        ring
  have hCFq : IsFrostmanIn q (fun i => (Y i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall ((delta : ENNReal) ^ (-eta0)) := by
    apply (isFrostmanIn_frostmanConstIn q (fun i => (Y i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall).mono
    calc
      _ <= (M : ENNReal) * frostmanConstIn F (fun i => (Y i).toConvexSpaceBody)
          ConvexSpaceBody.closedUnitBall := hqCF
      _ <= (delta : ENNReal) ^ (-2 * eta) * (delta : ENNReal) ^ (-eta) := mul_le_mul' hME hCF
      _ = (delta : ENNReal) ^ (-3 * eta) := by
        rw [← ENNReal.rpow_add _ _ hdE.ne' (by simp)]
        congr 1
        ring
      _ <= (delta : ENNReal) ^ (-eta0) :=
        ENNReal.rpow_le_rpow_of_exponent_ge hdE1 (by linarith)
  have hfullq : delta ^ eta0 <= ShadedBody.fullness q (fun i => (Y i).toShadedBody) := by
    apply ENNReal.coe_le_coe.mp
    rw [ENNReal.coe_rpow_of_ne_zero hd.ne', ShadedBody.coe_fullness]
    apply (ENNReal.rpow_le_rpow_of_exponent_ge hdE1 heta0').trans
    apply (ENNReal.mul_le_mul_iff_right (hpzero (-2 * eta)) (hpfinite (-2 * eta))).mp
    calc
      (delta : ENNReal) ^ (-2 * eta) * (delta : ENNReal) ^ (3 * eta) =
          (delta : ENNReal) ^ eta := by
        rw [← ENNReal.rpow_add _ _ hdE.ne' (by simp)]
        congr 1
        ring
      _ <= fullness' F (fun i => (Y i).toShadedBody) := hfull
      _ <= (M : ENNReal) * fullness' q (fun i => (Y i).toShadedBody) := hqfull
      _ <= (delta : ENNReal) ^ (-2 * eta) * fullness' q (fun i => (Y i).toShadedBody) :=
        mul_le_mul' hME le_rfl
  have hKFq := hKFdelta q Y (fun i hi => hball i (hqF hi)) hqED hCFq hfullq
  rw [hdim] at hKFq
  norm_num only [Nat.reduceSub] at hKFq
  have hcardpow : ((q.card : ENNReal) * (delta : ENNReal) ^ (2 : Nat)) ^ (1 - gamma / 2) <=
      ((F.card : ENNReal) * (delta : ENNReal) ^ (2 : Nat)) ^ (1 - gamma / 2) := by
    apply ENNReal.rpow_le_rpow _ (by linarith)
    exact mul_le_mul' (by exact_mod_cast Finset.card_le_card hqF) le_rfl
  calc
    _ <= (M : ENNReal) * ShadedBody.multiplicity q (fun i => (Y i).toShadedBody) := hqmult
    _ <= (delta : ENNReal) ^ (-2 * eta) *
        ((delta : ENNReal) ^ (-(e / 2) - 2 * gamma) *
          ((q.card : ENNReal) * (delta : ENNReal) ^ (2 : Nat)) ^ (1 - gamma / 2)) :=
      mul_le_mul' hME hKFq
    _ = (delta : ENNReal) ^ (-2 * eta - e / 2 - 2 * gamma) *
        ((q.card : ENNReal) * (delta : ENNReal) ^ (2 : Nat)) ^ (1 - gamma / 2) := by
      rw [← mul_assoc, ← ENNReal.rpow_add _ _ hdE.ne' (by simp)]
      congr 2
      ring
    _ <= (delta : ENNReal) ^ (-e - 2 * gamma) *
        ((F.card : ENNReal) * (delta : ENNReal) ^ (2 : Nat)) ^ (1 - gamma / 2) :=
      mul_le_mul' (ENNReal.rpow_le_rpow_of_exponent_ge hdE1 (by linarith)) hcardpow

/-! E4 is a local analytic construction in the already chosen original
plank. It does not refactor the selected subfamily or change W's dimensions. -/

theorem exists_inner_ED_family_of_lineED_fineTubes_w95
    (C_NC : NNReal) (hC_NC : 1 <= C_NC) :
    ∃ (Cnorm : NNReal) (dED : Nat) (Cinner bGeom : NNReal) (delta0 : Real),
      1 <= Cnorm ∧ 0 < dED ∧ 1 <= Cinner ∧ 0 < bGeom ∧
      0 < delta0 ∧ delta0 <= 1 ∧
      ∀ {iota : Type uI} [DecidableEq iota]
        {delta a b : NNReal} {hab : a <= b} {hb1 : b <= 1}
        (hdelta : 0 < delta) (ha : 0 < a) (hdelta_a : delta <= a)
        (hdelta_conf : (delta : Real) <= delta0)
        (a0 b0 : NNReal) (hsmall_a : delta <= a0 * b) (hsmall_b : delta <= b0 * a)
        (hgeom : delta <= bGeom * a)
        (W : Plank a b hab hb1) (q : Finset iota)
        (T : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
        (R : Real) (hR : 0 <= R) (A : Nat) (hA : 1 <= A),
        q.Nonempty ->
        (∀ i ∈ q, (T i).carrier ⊆ W.carrier) ->
        (∀ i ∈ q, ‖(T i).center‖ <= R) ->
        VeryNotSticky.IsLineEssDistinct A q (fun i => (T i).toTube) ->
        let M := lineSelectionMultiplicityW95 3 R A
        ∃ (a' b' : NNReal) (ha'b' : a' <= b') (hb'1 : b' <= 1) (iotaJ : Type)
          (qj : Finset iotaJ) (P : iotaJ -> ShadedPlank a' b' ha'b' hb'1),
          qj.Nonempty ∧ a' = delta / b ∧ b' = delta / a ∧
          0 < a' ∧ delta <= a' ∧ a' <= a0 ∧ b' <= b0 ∧
          a' / b' = a / b ∧
          ((a' : ENNReal) / (b' : ENNReal) = (a : ENNReal) / (b : ENNReal)) ∧
          (∀ i ∈ qj, (P i).carrier ⊆ Metric.closedBall 0 (plankWindowRadius : Real)) ∧
          (qj : Set iotaJ).Pairwise
            (fun i j => IsEssentiallyDistinct (P i).carrier (P j).carrier) ∧
          q.card <= M * (dED + 1) * qj.card ∧ qj.card <= q.card ∧
          ShadedBody.fullness q (fun i => (T i).toShadedBody) <=
            (M : NNReal) * Cnorm * ((dED : NNReal) + 1) *
              ShadedBody.fullness qj (fun i => (P i).toShadedBody) ∧
          Kakeya.maxDensity qj (fun i => (P i).toConvexSpaceBody) <=
            (Cnorm : ENNReal) * Kakeya.maxDensity q (fun i => (T i).toConvexSpaceBody) ∧
          frostmanConstIn qj (fun i => (P i).toConvexSpaceBody) plankWindow <=
            (Cnorm : ENNReal) * (M : ENNReal) * ((dED : ENNReal) + 1) *
              frostmanConstIn q (fun i => (T i).toConvexSpaceBody) W.toConvexSpaceBody *
                volume plankWindow.carrier ∧
          (∀ (phi : NNReal) (hphi : phi <= Rslab), a' / b' <= phi ->
            ∀ S : Prism3D phi Rslab Rslab hphi le_rfl,
              ((Plank.inWideSlabFamily qj (fun i => (P i).toPrism3D) S).card : NNReal) <=
                ((dED : NNReal) + 1) * (b / a) ^ (2 : Nat) *
                  phi ^ (1 : Real) * (qj.card : NNReal)) ∧
          Plank.IsThickeningNonconcentrated qj (fun i => (P i).toPrism3D) C_NC
            (Cinner * (b / a) ^ (2 : Nat)) ∧
          ShadedBody.multiplicity q (fun i => (T i).toShadedBody) <=
            (M : ENNReal) * ((dED : ENNReal) + 1) *
              ShadedBody.multiplicity qj (fun i => (P i).toShadedBody) := by
  classical
  obtain ⟨Cnorm, dED, Cinner, bGeom, delta0, hCnorm, hdED, hCinner, hbGeom,
      hdelta0, hdelta01, hconstruct⟩ := exists_inner_ED_family_of_fineTubes C_NC hC_NC
  refine ⟨Cnorm, dED, Cinner, bGeom, delta0, hCnorm, hdED, hCinner, hbGeom,
    hdelta0, hdelta01, ?_⟩
  intro iota _ delta a b hab hb1 hdelta ha hdelta_a hdelta_conf a0 b0
    hsmall_a hsmall_b hgeom W q T R hR A hA hq hcontained hcenter hline
  let M := lineSelectionMultiplicityW95 3 R A
  have hdim : Module.finrank Real (EuclideanSpace Real (Fin 3)) = 3 := by simp
  let K := Kakeya.Tube.tubeOverlapCoreClose.C 3
  have hK : 1 <= K := (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C 3).le
  have hB : 0 < lineAmplificationBoundW95 3 R K := by
    apply Nat.ceil_pos.mpr
    have hKm : 0 <= K - 1 := sub_nonneg.mpr hK
    positivity
  have hM : 1 <= M := Nat.mul_pos hB (by omega)
  have hMzero : (M : ENNReal) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  have hdelta1 : delta <= 1 := hdelta_a.trans (hab.trans hb1)
  have hline' := lineED_five_implies_lineEDAt_w95 hdelta hdelta1 q
    (fun i => (T i).toTube) A hline R K hR hK hcenter
  rw [hdim] at hline'
  have hline'' : VeryNotSticky.IsLineEssDistinctAt
      (Kakeya.Tube.tubeOverlapCoreClose.C
        (Module.finrank Real (EuclideanSpace Real (Fin 3)))) M q (fun i => (T i).toTube) := by
    simpa only [hdim, M, K, lineSelectionMultiplicityW95,
      VeryNotSticky.IsLineEssDistinctAt] using hline'
  obtain ⟨qE, hqEq, hqEED, hmass, hcard⟩ :=
    VeryNotSticky.exists_pairwise_of_isLineEssDistinctAt hdelta hdelta1 hline''
      (fun i => volume (T i).shade)
  rw [Nat.sub_add_cancel hM] at hmass hcard
  have hqE : qE.Nonempty := by
    by_contra hn
    have hqe : qE = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simpa [hqe, hq.card_ne_zero] using hcard
  have hcontainE : ∀ i ∈ qE, (T i).carrier ⊆ W.carrier :=
    fun i hi => hcontained i (hqEq hi)
  have hfullE : ShadedBody.fullness q (fun i => (T i).toShadedBody) <=
      (M : NNReal) * ShadedBody.fullness qE (fun i => (T i).toShadedBody) := by
    apply ENNReal.coe_le_coe.mp
    push_cast
    rw [ShadedBody.coe_fullness, ShadedBody.coe_fullness, fullness', fullness', ← mul_div_assoc]
    exact ENNReal.div_le_div hmass (Finset.sum_le_sum_of_subset hqEq)
  have hmaxE := Kakeya.maxDensity_mono (fun i => (T i).toConvexSpaceBody) hqEq
  have hmultE : ShadedBody.multiplicity q (fun i => (T i).toShadedBody) <=
      (M : ENNReal) * ShadedBody.multiplicity qE (fun i => (T i).toShadedBody) := by
    apply ShadedBody.multiplicity_le_mul_of_sum_shade_le_of_biUnion_subset q
      (fun i => (T i).toShadedBody) qE (fun i => (T i).toShadedBody) M _ hmass
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    exact Set.mem_iUnion₂.mpr ⟨i, hqEq hi, hxi⟩
  obtain ⟨i0, hi0⟩ := hq
  have hvol : ∀ i ∈ q, volume (T i).carrier = volume (T i0).carrier :=
    fun i _ => Tube.volume_carrier_eq_volume_carrier (T i).toTube (T i0).toTube
  have hretain : (M : ENNReal)⁻¹ * (q.card : ENNReal) <= (qE.card : ENNReal) := by
    apply (ENNReal.inv_mul_le_iff hMzero (by simp)).mpr
    exact_mod_cast hcard
  have hCFE : frostmanConstIn qE (fun i => (T i).toConvexSpaceBody) W.toConvexSpaceBody <=
      (M : ENNReal) * frostmanConstIn q (fun i => (T i).toConvexSpaceBody) W.toConvexSpaceBody := by
    simpa only [inv_inv] using frostmanConstIn_subfamily_le ⟨i0, hi0⟩ hvol hcontained
      hqEq (show (M : ENNReal)⁻¹ ≠ 0 by simp) hretain
  obtain ⟨a', b', ha'b', hb'1, iotaJ, qj, P, ha'def, hb'def, ha'pos,
      hdelta_a', hb'b0, hratioNN, hratioENN, hwindow, hED, hcardJ, hcardJ',
      hfullJ, hmaxJ, hslab, hNC, hmultJ⟩ := hconstruct hdelta ha hdelta_a hdelta_conf
        a0 b0 hsmall_a hsmall_b hgeom W qE T hqE hcontainE hqEED
  have hqj : qj.Nonempty := by
    by_contra hn
    have hqe : qj = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simpa [hqe, hqE.card_ne_zero] using hcardJ
  have hCFJ := innerNormalised_isFrostmanIn hdelta ha hdelta_a W qE T hcontainE
    ((isFrostmanIn_frostmanConstIn qE (fun i => (T i).toConvexSpaceBody)
      W.toConvexSpaceBody).mono hCFE) ha'def hb'def Cnorm dED qj P hwindow hcardJ hmaxJ
  refine ⟨a', b', ha'b', hb'1, iotaJ, qj, P, hqj, ha'def, hb'def, ha'pos,
    hdelta_a', ?_, hb'b0, hratioNN, hratioENN, hwindow, hED, ?_,
    hcardJ'.trans (Finset.card_le_card hqEq), ?_, ?_, ?_, hslab, hNC, ?_⟩
  · rw [ha'def]
    exact (div_le_iff₀ (ha.trans_le hab)).mpr hsmall_a
  · calc
      q.card <= M * qE.card := hcard
      _ <= M * ((dED + 1) * qj.card) := Nat.mul_le_mul_left _ hcardJ
      _ = _ := by ring
  · calc
      _ <= (M : NNReal) * ShadedBody.fullness qE (fun i => (T i).toShadedBody) := hfullE
      _ <= (M : NNReal) * (Cnorm * ((dED : NNReal) + 1) *
          ShadedBody.fullness qj (fun i => (P i).toShadedBody)) := mul_le_mul' le_rfl hfullJ
      _ = _ := by ring
  · exact hmaxJ.trans (mul_le_mul' le_rfl hmaxE)
  · convert frostmanConstIn_le hCFJ using 1
    dsimp [flatPrismInnerNormalisedFrostman.C]
    ring
  · calc
      _ <= (M : ENNReal) * ShadedBody.multiplicity qE (fun i => (T i).toShadedBody) := hmultE
      _ <= (M : ENNReal) * (((dED : ENNReal) + 1) *
          ShadedBody.multiplicity qj (fun i => (P i).toShadedBody)) := mul_le_mul' le_rfl hmultJ
      _ = _ := by ring

/-- The local ED selection costs one M in multiplicity and M^(1-gamma/2)
in the Frostman factor; it does not add M to the NC output. -/
theorem line_selection_power_cost_w95 (M : Nat) (hM : 1 <= M)
    (gamma : Real) (hgamma0 : 0 <= gamma) (hgamma1 : gamma <= 1) :
    (M : ENNReal) * (M : ENNReal) ^ (1 - gamma / 2) =
        (M : ENNReal) ^ (2 - gamma / 2) ∧
      (M : ENNReal) ^ (2 - gamma / 2) <= (M : ENNReal) ^ (2 : Nat) := by
  have hMreal : (1 : ENNReal) <= M := by exact_mod_cast hM
  have hMzero : (M : ENNReal) ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hMreal)
  constructor
  · rw [show 2 - gamma / 2 = 1 + (1 - gamma / 2) by ring,
      ENNReal.rpow_add _ _ hMzero (by simp), ENNReal.rpow_one]
  · convert ENNReal.rpow_le_rpow_of_exponent_le hMreal
      (show 2 - gamma / 2 <= (2 : Real) by linarith) using 1
    norm_num

end

end Kakeya.ml1Boot.TrialRestartW94
