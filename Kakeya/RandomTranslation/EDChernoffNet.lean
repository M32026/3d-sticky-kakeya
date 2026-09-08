/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.RandomTranslation.EssDistinct
public import Kakeya.Density
public import Kakeya.Discretization
public import Kakeya.Mathlib.Analysis.EuclideanNet
public import Kakeya.Tube.Volume

/-!
# ED Chernoff testing net ([GWZ], §9)

Structural skeleton for the ED-tolerance testing net used in GWZ §9.
The full mathematical content is deferred to later refinement passes;
this file provides the external interfaces (signatures) so that
downstream files can `import` and reference these lemmas.

Two principal interfaces are exposed (thin variants):

* `exists_ed_tube_net_thin` — existence of a `δ^{-O(1)}`-sized "ED tolerance"
  net of `δ`-tubes covering all tubes with carrier in `B(0, 2)`, with the
  thin per-member volume bound `vol(cthickening 99·δ T₀'.carrier) ≤
  netVolThinConstantM E · δ^(n-1)`.
* `exists_chernoff_tube_net_with_ed_approx_thin` — joint ED Chernoff testing
  net combining the ED-tolerance approximation with the union-bound
  Chernoff input (`productEdFailCountSet_chernoff_tail`).
-/

@[expose] public section

open MeasureTheory Metric

namespace Kakeya

section EDChernoffNet

universe u v

variable
  (E : Type*)
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Multiplicative constant in the covering-net cardinality bound supplied by
`exists_localized_finite_test_family_maxDensity` at radius `2`, namely
`C n · 2 ^ M n` with `C`, `M` the constants of
`exists_volume_bounded_prism_discretization`. Extracted as a top-level constant so
that the size hypothesis `hδ_small` of `exists_frostman_translations` can
quantify it. Inflated by the product of the brick constants
`EuclideanNet.exists_sphere_net` × `EuclideanNet.exists_ball_net` (gated on
`0 < n`) so that the assembled `exists_thin_tube_net` cardinality bound
goes through. -/
noncomputable def netGeomConstantC : ℝ :=
  (exists_volume_bounded_prism_discretization.C (Module.finrank ℝ E) : ℝ) *
      2 ^ exists_volume_bounded_prism_discretization.M (Module.finrank ℝ E) +
    (if h : 0 < Module.finrank ℝ E then
      haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) h
      Kakeya.EuclideanNet.sphereNetConstant E *
        Kakeya.EuclideanNet.ballNetConstant E
    else 0)

/-- Raw `δ`-exponent in the covering-net cardinality bound, i.e. the exponent
`exists_volume_bounded_prism_discretization.M` of the underlying discretization.
Exposed as a top-level constant so that downstream lemmas can reason about
the **strict slack** between this raw exponent and the padded
`netGeomConstantM E`. -/
noncomputable def netGeomConstantMRaw : ℝ :=
  exists_volume_bounded_prism_discretization.M (Module.finrank ℝ E)

/-- Power-of-`δ` exponent in the covering-net cardinality bound. Defined as the
maximum of `netGeomConstantMRaw E + 1` and `2·(n−1)+1`. The `+1` shift over
the raw exponent guarantees **strict slack**
`netGeomConstantMRaw E < netGeomConstantM E`, which is required by the
`(C2.hNetF_smallness)` δ-smallness conjunct in `randCF_smallness_envelope`
(`KTest.card · exp(−⌈M_geom·log(1/δ)⌉₊) ≤ C · δ^(M_geom − M_raw)` is only
δ-vanishing under strict slack). The max-wrap also guarantees
`netGeomConstantM E ≥ 2·(n−1)+1`, which is required by the thin tube net
construction (`exists_thin_tube_net`): a direction × position grid on
`S^(n−1) × B(0,2)` naturally has cardinality `Θ(δ^{-2(n−1)})`, and we need
the statement's exponent to dominate this geometric reality. Since `δ^{−M}`
is **increasing** in `M` for `δ ∈ (0,1]`, enlarging `M` only **weakens** the
cardinality bound, so all existing consumers of `netGeomConstantM` (which use
it as an arbitrary dim-only positive constant) remain sound. -/
noncomputable def netGeomConstantM : ℝ :=
  max (netGeomConstantMRaw E + 1)
      (2 * ((Module.finrank ℝ E : ℝ) - 1) + 1)

omit [MeasurableSpace E] [BorelSpace E] in
lemma netGeomConstantC_pos : 0 < netGeomConstantC E := by
  unfold netGeomConstantC
  have h1 : (0 : ℝ) <
      (exists_volume_bounded_prism_discretization.C (Module.finrank ℝ E) : ℝ) *
        2 ^ exists_volume_bounded_prism_discretization.M (Module.finrank ℝ E) := by
    have := exists_volume_bounded_prism_discretization.C_pos (Module.finrank ℝ E)
    have hC : (0 : ℝ) < (exists_volume_bounded_prism_discretization.C (Module.finrank ℝ E) : ℝ) :=
      NNReal.coe_pos.mpr this
    positivity
  split_ifs with hn
  · haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) hn
    have h2 : 0 < Kakeya.EuclideanNet.sphereNetConstant E :=
      Kakeya.EuclideanNet.sphereNetConstant_pos E
    have h3 : 0 < Kakeya.EuclideanNet.ballNetConstant E :=
      Kakeya.EuclideanNet.ballNetConstant_pos E
    have hprod : 0 <
        Kakeya.EuclideanNet.sphereNetConstant E *
          Kakeya.EuclideanNet.ballNetConstant E :=
      mul_pos h2 h3
    linarith
  · linarith

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma netGeomConstantMRaw_pos : 0 < netGeomConstantMRaw E :=
  exists_volume_bounded_prism_discretization.M_pos (Module.finrank ℝ E)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma netGeomConstantM_pos : 0 < netGeomConstantM E := by
  unfold netGeomConstantM
  exact lt_max_of_lt_left
    (by linarith [netGeomConstantMRaw_pos E])

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The raw discretization exponent is `<` `netGeomConstantM E`,
i.e. there is **strict** slack of at least `1`. -/
lemma netGeomConstantM_gt_raw :
    netGeomConstantMRaw E < netGeomConstantM E := by
  unfold netGeomConstantM
  exact lt_max_of_lt_left (by linarith)

omit [MeasurableSpace E] [BorelSpace E] in
/-- The radius-`2` discretization constant `C n · 2 ^ M n` is the leading summand of
`netGeomConstantC E`, hence bounded by it. -/
lemma prismNetConstant_le_netGeomConstantC :
    (exists_volume_bounded_prism_discretization.C (Module.finrank ℝ E) : ℝ) *
        2 ^ exists_volume_bounded_prism_discretization.M (Module.finrank ℝ E)
      ≤ netGeomConstantC E := by
  unfold netGeomConstantC
  have hbricks_nn : (0 : ℝ) ≤
      (if h : 0 < Module.finrank ℝ E then
        haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) h
        Kakeya.EuclideanNet.sphereNetConstant E *
          Kakeya.EuclideanNet.ballNetConstant E
      else 0) := by
    by_cases hn : 0 < Module.finrank ℝ E
    · haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) hn
      rw [dif_pos hn]
      exact mul_nonneg
        (Kakeya.EuclideanNet.sphereNetConstant_pos E).le
        (Kakeya.EuclideanNet.ballNetConstant_pos E).le
    · rw [dif_neg hn]
  linarith

omit [MeasurableSpace E] [BorelSpace E] in
/-- The bare discretization constant `C n` is bounded by `netGeomConstantC E`, since the extra
factor `2 ^ M n` is at least `1`. -/
lemma prismDiscretizationC_le_netGeomConstantC :
    (exists_volume_bounded_prism_discretization.C (Module.finrank ℝ E) : ℝ)
      ≤ netGeomConstantC E := by
  refine le_trans ?_ (prismNetConstant_le_netGeomConstantC E)
  have h2 : (1 : ℝ) ≤ 2 ^ exists_volume_bounded_prism_discretization.M (Module.finrank ℝ E) := by
    calc (1 : ℝ) = (2 : ℝ) ^ (0 : ℝ) := (Real.rpow_zero 2).symm
      _ ≤ (2 : ℝ) ^ exists_volume_bounded_prism_discretization.M (Module.finrank ℝ E) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (exists_volume_bounded_prism_discretization.M_pos _).le
  have hC : (0 : ℝ) ≤ (exists_volume_bounded_prism_discretization.C (Module.finrank ℝ E) : ℝ) :=
    NNReal.coe_nonneg _
  nlinarith

/-- **Radius-`2` density test family, packaged against `netGeomConstantC` /
`netGeomConstantMRaw`.**

Repackaging of `Kakeya.exists_localized_finite_test_family_maxDensity` at radius `2`: at every
scale `0 < δ ≤ 1` there is a finite family `NetF` of convex bodies inside `B(0,2)`, of cardinality
at most `netGeomConstantC E · δ ^ (-netGeomConstantMRaw E)`, such that the maximal density of any
finite family of `δ`-thick convex bodies in `B(0,2)` is at most `netGeomConstantC E` times its
density in some member of `NetF`.

`NetF` is produced from `δ` alone, before the index type and the family are quantified; this is
what lets a single `NetF` serve a *randomly moved* family whose translations are only chosen
afterwards. The index universe is the explicit parameter `v`, so callers pin it, e.g.
`exists_netF_test_family.{u, _}`. -/
lemma exists_netF_test_family [Nontrivial E] {δ : NNReal} (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1) :
    ∃ NetF : Finset (ConvexSpaceBody E),
      (∀ K ∈ NetF, K.carrier ⊆ Metric.closedBall (0 : E) 2) ∧
      ((NetF.card : ℝ) ≤ netGeomConstantC E * (δ : ℝ) ^ (-netGeomConstantMRaw E)) ∧
      ∀ {ι : Type v} (s : Finset ι) (W : ι → ConvexSpaceBody E),
        (∀ i ∈ s, (W i).carrier ⊆ Metric.closedBall (0 : E) 2) →
        (∀ i ∈ s, (δ : ENNReal) ≤ Metric.ethickness.scale ℝ (W i).carrier) →
        ∃ K ∈ NetF, Kakeya.maxDensity s W ≤
          ENNReal.ofReal (netGeomConstantC E) * Kakeya.densityIn s W K := by
  obtain ⟨NetF, hsub, hcard, hmain⟩ :=
    Kakeya.exists_localized_finite_test_family_maxDensity.{v, _} (E := E)
      (r := δ) (R := 2) hδ_pos hδ_le_one (by norm_num)
  have hCle : (exists_volume_bounded_prism_discretization.C (Module.finrank ℝ E) : ENNReal) ≤
      ENNReal.ofReal (netGeomConstantC E) := by
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal (prismDiscretizationC_le_netGeomConstantC E)
  refine ⟨NetF, fun K hK => by simpa using hsub K hK, ?_, ?_⟩
  · have hreal : (NetF.card : ℝ) ≤
        (exists_volume_bounded_prism_discretization.C (Module.finrank ℝ E) : ℝ) *
          2 ^ exists_volume_bounded_prism_discretization.M (Module.finrank ℝ E) *
          (δ : ℝ) ^ (-exists_volume_bounded_prism_discretization.M (Module.finrank ℝ E)) := by
      have h := NNReal.coe_le_coe.mpr hcard
      rwa [NNReal.coe_mul, NNReal.coe_mul, NNReal.coe_rpow, NNReal.coe_rpow,
        NNReal.coe_natCast, NNReal.coe_ofNat] at h
    refine hreal.trans ?_
    unfold netGeomConstantMRaw
    exact mul_le_mul_of_nonneg_right (prismNetConstant_le_netGeomConstantC E)
      (Real.rpow_nonneg δ.coe_nonneg _)
  · intro ι s W hball hthick
    obtain ⟨K, hK, hle⟩ := hmain s W (fun i hi => by simpa using hball i hi) hthick
    exact ⟨K, hK, hle.trans (mul_le_mul' hCle le_rfl)⟩

/-- Uniform per-member volume constant for the **thin** ED tube net.
Every member `T₀'` of `(exists_ed_tube_net_thin...).choose` satisfies
`vol(cthickening (99·δ) T₀'.carrier) ≤ netVolThinConstantM E · δ^(n-1)`.

Inflated to absorb the brick constant from
`volume_cthickening_unit_segment_le` (rescaled by `100 ^ n` to convert
`r ∈ (0,1]` to `100·δ`), plus a crude `volume(closedBall 0 200) * 100 ^ n`
term for the `δ > 1/100` case where the brick is not applicable.
Downstream users only require positivity, so the exact value is not
consumed. -/
noncomputable def netVolThinConstantM (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] : ℝ :=
  MeasureTheory.volume.real (Metric.closedBall (0 : E) 200) *
      100 ^ Module.finrank ℝ E +
    (if h : 0 < Module.finrank ℝ E then
      haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) h
      (Kakeya.Tube.unitSegmentCthickeningVolumeConstant E : ℝ) *
        100 ^ Module.finrank ℝ E
    else 0) + 1

lemma netVolThinConstantM_pos : 0 < netVolThinConstantM E := by
  unfold netVolThinConstantM
  have h_nn1 : (0 : ℝ) ≤ MeasureTheory.volume.real (Metric.closedBall (0 : E) 200) *
      100 ^ Module.finrank ℝ E := by
    apply mul_nonneg MeasureTheory.measureReal_nonneg
    positivity
  split_ifs with hn
  · haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) hn
    have h_pos : 0 < Kakeya.Tube.unitSegmentCthickeningVolumeConstant E :=
      Kakeya.Tube.unitSegmentCthickeningVolumeConstant_pos E
    have h_nn2 : (0 : ℝ) ≤
        (Kakeya.Tube.unitSegmentCthickeningVolumeConstant E : ℝ) *
          100 ^ Module.finrank ℝ E := by
      apply mul_nonneg (NNReal.coe_nonneg _); positivity
    linarith
  · linarith

set_option maxHeartbeats 800000 in
-- The body performs heavy `module`/segment elaboration over `tube_of` outputs.
/-- **Thin tube net constructor.** Produces a finite set of `Tube δ E` whose
members are in `B(0, 2)`, have `99·δ`-cthickening volume bounded by
`netVolThinConstantM E · δ^(n-1)`, and whose `99·δ`-cthickenings cover all
tubes in `B(0, 2)`.

The body is assembled from the three independent geometric "bricks"
in `Kakeya.Mathlib.Analysis.EuclideanNet` and `Kakeya.Tube.Volume`:

* `EuclideanNet.exists_sphere_net` — direction ε-net on `S^(n-1)` with
  cardinality `≤ C_dir · ε^(-(n-1))`.

* `EuclideanNet.exists_ball_net` — midpoint ε-net on `B(0, 5/2)` with
  cardinality `≤ C_pos · ε^(-n)`.

* `volume_cthickening_unit_segment_le` — uniform thin volume bound
  `vol(cthickening r segment) ≤ C_vol · r^(n-1)` for `r ∈ (0, 1]`.

The product `U × P` (with the canonical `Tube.ofMidpointDirection` constructor)
gives a candidate net of size
`≤ C_dir · C_pos · δ^(-(2n-1))`. Since `netGeomConstantM E ≥ 2n - 1`
by construction (`max(_, 2(n-1) + 1)`), the cardinality bound fits.
The covering property follows from the triangle inequality with slack
`(5/2)·δ ≤ 99·δ`; the thin volume property follows from
`Brick 3` applied to the unit segment of each net tube, case split
on `δ ≤ 1/100` (use brick) vs `δ > 1/100` (crude ball bound). -/
lemma exists_thin_tube_net [Nontrivial E]
    {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ NetT : Finset (Tube δ E),
      (NetT.card : ℝ) ≤ netGeomConstantC E * (δ : ℝ) ^ (-(netGeomConstantM E)) ∧
      (∀ T₀' ∈ NetT, T₀'.carrier ⊆ Metric.closedBall (0 : E) (7 / 2)) ∧
      (∀ T₀' ∈ NetT, volume (Metric.cthickening (99 * (δ : ℝ)) T₀'.carrier)
          ≤ ENNReal.ofReal (netVolThinConstantM E) *
            (δ : ENNReal) ^ (Module.finrank ℝ E - 1)) ∧
      ∀ (T₀ : Tube δ E), T₀.carrier ⊆ Metric.closedBall (0 : E) 2 →
        ∃ T₀' ∈ NetT,
          T₀.carrier ⊆ Metric.cthickening (99 * (δ : ℝ)) T₀'.carrier := by
  classical
  haveI : ProperSpace E := FiniteDimensional.proper_real E
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  have hδR1 : (δ : ℝ) < 1 := by exact_mod_cast hδ1
  set n := Module.finrank ℝ E with hn_def
  have _hn : 0 < Module.finrank ℝ E := Module.finrank_pos
  have hn_pos : 0 < n := _hn
  have hn_real_pos : (0 : ℝ) < n := by exact_mod_cast hn_pos
  have hn_real_ge_one : (1 : ℝ) ≤ n := by exact_mod_cast hn_pos
  -- Brick 1: direction net.
  set C_dir : ℝ := Kakeya.EuclideanNet.sphereNetConstant E with hC_dir_def
  have hC_dir_pos : 0 < C_dir := by
    rw [hC_dir_def]
    exact Kakeya.EuclideanNet.sphereNetConstant_pos E
  obtain ⟨U, hU_unit, hU_card, hU_cover⟩ :=
    Kakeya.EuclideanNet.exists_sphere_net (E := E) hδR hδR1.le
  -- Brick 2: midpoint grid.
  set C_pos : ℝ := Kakeya.EuclideanNet.ballNetConstant E with hC_pos_def
  have hC_pos_pos : 0 < C_pos := by
    rw [hC_pos_def]
    exact Kakeya.EuclideanNet.ballNetConstant_pos E
  obtain ⟨P, hP_card, hP_sub, hP_cover⟩ :=
    Kakeya.EuclideanNet.exists_ball_net (E := E) hδR hδR1.le
  -- Brick 3: volume bound on unit segments.
  set C_vol : ℝ := (Kakeya.Tube.unitSegmentCthickeningVolumeConstant E : ℝ)
    with hC_vol_def
  have hC_vol_pos : 0 < C_vol := by
    rw [hC_vol_def]
    exact NNReal.coe_pos.mpr (Kakeya.Tube.unitSegmentCthickeningVolumeConstant_pos E)
  have hvol : ∀ (x y : E), dist x y = 1 →
      ∀ r : ℝ, 0 < r → r ≤ 1 →
        volume.real (Metric.cthickening r (segment ℝ x y)) ≤
          C_vol * r ^ (Module.finrank ℝ E - 1) := by
    intro x y hxy r hr hr1
    have hr_coe : ((r.toNNReal : NNReal) : ℝ) = r := Real.coe_toNNReal r hr.le
    have hrN_le_one : r.toNNReal ≤ 1 := by
      rw [← NNReal.coe_le_coe, hr_coe]; exact hr1
    have h := Kakeya.Tube.volume_cthickening_unit_segment_le
      E x y hxy r.toNNReal hrN_le_one
    have hRHS_fin :
        (Kakeya.Tube.unitSegmentCthickeningVolumeConstant E : ENNReal) *
            (r.toNNReal : ENNReal) ^ (Module.finrank ℝ E - 1) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
    have hreal := ENNReal.toReal_mono hRHS_fin h
    simpa [Measure.real, hC_vol_def, hr_coe, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.coe_toReal] using hreal
  -- Tube constructor: for each (u, m), get a tube with midpoint m and direction u.
  let tube_of : (u : E) → ‖u‖ = 1 → (m : E) → Tube δ E := fun u hu m =>
    Tube.ofMidpointDirection δ m u hu
  have tube_of_x : ∀ (u : E) (hu : ‖u‖ = 1) (m : E),
      (tube_of u hu m).x = m - (1/2 : ℝ) • u := by
    simp [tube_of]
  have tube_of_y : ∀ (u : E) (hu : ‖u‖ = 1) (m : E),
      (tube_of u hu m).y = m + (1/2 : ℝ) • u := by
    simp [tube_of]
  have tube_of_mid : ∀ (u : E) (hu : ‖u‖ = 1) (m : E),
      (tube_of u hu m).midpoint = m := by
    intro u hu m
    simp only [tube_of, Tube.midpoint, Tube.ofMidpointDirection_x,
      Tube.ofMidpointDirection_y]
    module
  have tube_of_dir : ∀ (u : E) (hu : ‖u‖ = 1) (m : E),
      (tube_of u hu m).direction = u := by
    intro u hu m
    simp only [tube_of, Tube.direction, Tube.ofMidpointDirection_x,
      Tube.ofMidpointDirection_y]
    module
  -- Define the product net using `U.attach` to carry the unit hypothesis.
  set NetT_full : Finset (Tube δ E) :=
    (U.attach ×ˢ P).image (fun (umpair : {u // u ∈ U} × E) =>
      tube_of umpair.1.val (hU_unit umpair.1.val umpair.1.2) umpair.2)
    with hNetT_full_def
  -- Filter to keep tubes with midpoint norm ≤ 2.
  set NetT : Finset (Tube δ E) :=
    NetT_full.filter (fun T => ‖T.midpoint‖ ≤ 2) with hNetT_def
  -- Structure helper: each net member arises from some (u, m) with u ∈ U, m ∈ P.
  have h_NetT_origin :
      ∀ T ∈ NetT, ∃ u m : E, ∃ hu : ‖u‖ = 1,
        u ∈ U ∧ m ∈ P ∧ T = tube_of u hu m := by
    intro T hT
    rw [hNetT_def, Finset.mem_filter] at hT
    obtain ⟨hT_full, _hmid_le⟩ := hT
    rw [hNetT_full_def, Finset.mem_image] at hT_full
    obtain ⟨umpair, hum, hT_eq⟩ := hT_full
    rw [Finset.mem_product] at hum
    refine ⟨umpair.1.val, umpair.2, hU_unit umpair.1.val umpair.1.2,
      umpair.1.2, hum.2, hT_eq.symm⟩
  have h_NetT_struct : ∀ T ∈ NetT, ‖T.midpoint‖ ≤ 2 ∧ ‖T.direction‖ = 1 := by
    intro T hT
    have hmid : ‖T.midpoint‖ ≤ 2 := by
      rw [hNetT_def, Finset.mem_filter] at hT; exact hT.2
    refine ⟨hmid, ?_⟩
    obtain ⟨u, m, hu_unit, _, _, hT_eq⟩ := h_NetT_origin T hT
    rw [hT_eq, tube_of_dir u hu_unit m]
    exact hu_unit
  -- Subset-to-B(0,7/2) helper.
  have h_subset_helper :
      ∀ T : Tube δ E, ‖T.midpoint‖ ≤ 2 →
        T.carrier ⊆ Metric.closedBall (0 : E) (7/2) := by
    intro T hmid p hp
    rw [T.carrier_eq] at hp
    obtain ⟨z, hz_seg, hpz⟩ := Set.mem_iUnion₂.mp hp
    obtain ⟨a, b, ha, hb, hab, hz_eq⟩ := hz_seg
    rw [Metric.mem_closedBall, dist_zero_right]
    have h_dir_norm : ‖T.direction‖ = 1 := by
      have := T.dist_eq_one
      rwa [dist_eq_norm, ← neg_sub, norm_neg] at this
    have hz_alt : z = T.midpoint + (b - 1/2) • T.direction := by
      rw [← hz_eq]
      simp only [Tube.midpoint, Tube.direction]
      have hab' : a = 1 - b := by linarith
      rw [hab']
      module
    have hz_norm : ‖z‖ ≤ ‖T.midpoint‖ + 1/2 := by
      rw [hz_alt]
      have h1 : ‖T.midpoint + (b - 1/2) • T.direction‖
          ≤ ‖T.midpoint‖ + ‖(b - 1/2) • T.direction‖ := norm_add_le _ _
      have h2 : ‖(b - 1/2) • T.direction‖ = |b - 1/2| * 1 := by
        rw [norm_smul, h_dir_norm, Real.norm_eq_abs]
      have h3 : |b - 1/2| ≤ 1/2 := by
        rw [abs_le]; constructor <;> nlinarith
      have h4 : ‖(b - 1/2) • T.direction‖ ≤ 1/2 := by rw [h2]; linarith
      linarith
    have hpz_norm : ‖p - z‖ ≤ δ := by
      rw [← dist_eq_norm]; exact hpz
    have hp_norm : ‖p‖ ≤ ‖z‖ + δ := by
      calc ‖p‖ = ‖z + (p - z)‖ := by rw [add_sub_cancel]
        _ ≤ ‖z‖ + ‖p - z‖ := norm_add_le _ _
        _ ≤ ‖z‖ + δ := by linarith
    linarith
  refine ⟨NetT, ?_, ?_, ?_, ?_⟩
  · -- Cardinality bound.
    have hNetT_le_full : (NetT.card : ℝ) ≤ (NetT_full.card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
    have hNetT_full_le : (NetT_full.card : ℝ) ≤ ((U.attach ×ˢ P).card : ℝ) := by
      exact_mod_cast Finset.card_image_le
    have hUP_card : ((U.attach ×ˢ P).card : ℝ) = (U.card : ℝ) * (P.card : ℝ) := by
      rw [Finset.card_product, U.card_attach]; push_cast; ring
    have hδ_pos : 0 < δ := hδ
    have hδ_nn : 0 ≤ δ := hδ.le
    have h_powdir_nn : 0 ≤ δ ^ (-((n : ℝ) - 1)) := Real.rpow_nonneg hδ_nn _
    have h_powpos_nn : 0 ≤ δ ^ (-(n : ℝ)) := Real.rpow_nonneg hδ_nn _
    have h_UPbound : (U.card : ℝ) * (P.card : ℝ) ≤
        (C_dir * δ ^ (-((n : ℝ) - 1))) * (C_pos * δ ^ (-(n : ℝ))) := by
      apply mul_le_mul hU_card hP_card (Nat.cast_nonneg _)
      positivity
    have h_pow_combine :
        (C_dir * (δ : ℝ) ^ (-((n : ℝ) - 1))) * (C_pos * (δ : ℝ) ^ (-(n : ℝ))) =
          (C_dir * C_pos) * (δ : ℝ) ^ (-(2 * (n : ℝ) - 1)) := by
      have hr : (δ : ℝ) ^ (-((n : ℝ) - 1)) * (δ : ℝ) ^ (-(n : ℝ)) =
          (δ : ℝ) ^ (-(2 * (n : ℝ) - 1)) := by
        rw [← Real.rpow_add hδR]
        congr 1; ring
      calc (C_dir * (δ : ℝ) ^ (-((n : ℝ) - 1))) * (C_pos * (δ : ℝ) ^ (-(n : ℝ)))
          = (C_dir * C_pos) * ((δ : ℝ) ^ (-((n : ℝ) - 1)) * (δ : ℝ) ^ (-(n : ℝ))) := by ring
        _ = (C_dir * C_pos) * (δ : ℝ) ^ (-(2 * (n : ℝ) - 1)) := by rw [hr]
    have h_UPbound' : (U.card : ℝ) * (P.card : ℝ) ≤
        (C_dir * C_pos) * δ ^ (-(2 * (n : ℝ) - 1)) := by
      rw [← h_pow_combine]; exact h_UPbound
    have hM_ge : 2 * (n : ℝ) - 1 ≤ netGeomConstantM E := by
      unfold netGeomConstantM
      have hineq : 2 * (n : ℝ) - 1 ≤ 2 * ((n : ℝ) - 1) + 1 := by linarith
      exact hineq.trans (le_max_right _ _)
    have h_pow_le : δ ^ (-(2 * (n : ℝ) - 1)) ≤ δ ^ (-(netGeomConstantM E)) := by
      apply Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ1.le
      linarith
    have h_C_le : C_dir * C_pos ≤ netGeomConstantC E := by
      unfold netGeomConstantC
      rw [dif_pos _hn]
      have h_old_pos : (0 : ℝ) ≤
          (exists_volume_bounded_prism_discretization.C (Module.finrank ℝ E) : ℝ) *
            2 ^ exists_volume_bounded_prism_discretization.M (Module.finrank ℝ E) := by
        positivity
      change C_dir * C_pos ≤
        (exists_volume_bounded_prism_discretization.C (Module.finrank ℝ E) : ℝ) *
            2 ^ exists_volume_bounded_prism_discretization.M (Module.finrank ℝ E) +
          Kakeya.EuclideanNet.sphereNetConstant E *
            Kakeya.EuclideanNet.ballNetConstant E
      rw [← hC_dir_def, ← hC_pos_def]
      linarith
    have h_CprodPos : 0 ≤ C_dir * C_pos := by
      apply mul_nonneg hC_dir_pos.le hC_pos_pos.le
    have h_PowNN : 0 ≤ δ ^ (-(netGeomConstantM E)) := Real.rpow_nonneg hδ_nn _
    have h_combine :
        (C_dir * C_pos) * δ ^ (-(2 * (n : ℝ) - 1)) ≤
          netGeomConstantC E * δ ^ (-(netGeomConstantM E)) := by
      have step1 : (C_dir * C_pos) * δ ^ (-(2 * (n : ℝ) - 1)) ≤
          (C_dir * C_pos) * δ ^ (-(netGeomConstantM E)) :=
        mul_le_mul_of_nonneg_left h_pow_le h_CprodPos
      have step2 : (C_dir * C_pos) * δ ^ (-(netGeomConstantM E)) ≤
          netGeomConstantC E * δ ^ (-(netGeomConstantM E)) :=
        mul_le_mul_of_nonneg_right h_C_le h_PowNN
      linarith
    calc (NetT.card : ℝ) ≤ (NetT_full.card : ℝ) := hNetT_le_full
      _ ≤ ((U.attach ×ˢ P).card : ℝ) := hNetT_full_le
      _ = (U.card : ℝ) * (P.card : ℝ) := hUP_card
      _ ≤ (C_dir * C_pos) * δ ^ (-(2 * (n : ℝ) - 1)) := h_UPbound'
      _ ≤ netGeomConstantC E * δ ^ (-(netGeomConstantM E)) := h_combine
  · -- Each net member has carrier ⊆ B(0, 7/2).
    intro T hT
    exact h_subset_helper T (h_NetT_struct T hT).1
  · -- Each net member has thin volume bound.
    intro T hT
    obtain ⟨u, m, hu_unit, _hu_in, hm_in, hT_eq⟩ := h_NetT_origin T hT
    have hmid_le : ‖T.midpoint‖ ≤ 2 := (h_NetT_struct T hT).1
    have hTx : T.x = m - (1/2 : ℝ) • u := by rw [hT_eq]; exact tube_of_x u hu_unit m
    have hTy : T.y = m + (1/2 : ℝ) • u := by rw [hT_eq]; exact tube_of_y u hu_unit m
    have hTdist : dist T.x T.y = 1 := T.dist_eq_one
    have hT_carrier_cth : T.carrier = Metric.cthickening (δ : ℝ) (segment ℝ T.x T.y) := by
      rw [T.carrier_eq]
      have hseg_closed : IsClosed (segment ℝ T.x T.y) := by
        rw [segment_eq_image']
        exact (isCompact_Icc.image (by fun_prop)).isClosed
      rw [hseg_closed.cthickening_eq_biUnion_closedBall hδR.le]
    have h99_nn : (0 : ℝ) ≤ 99 * (δ : ℝ) := by positivity
    have h_subset_cth :
        Metric.cthickening (99 * (δ : ℝ)) T.carrier ⊆
          Metric.cthickening (100 * (δ : ℝ)) (segment ℝ T.x T.y) := by
      rw [hT_carrier_cth]
      have h1 : Metric.cthickening (99 * (δ : ℝ))
            (Metric.cthickening (δ : ℝ) (segment ℝ T.x T.y)) ⊆
          Metric.cthickening (99 * (δ : ℝ) + (δ : ℝ)) (segment ℝ T.x T.y) :=
        Metric.cthickening_cthickening_subset h99_nn hδR.le _
      have h_eq : (99 * (δ : ℝ) + (δ : ℝ)) = 100 * (δ : ℝ) := by ring
      rw [h_eq] at h1; exact h1
    have hseg_compact : IsCompact (segment ℝ T.x T.y) := by
      rw [segment_eq_image']
      exact isCompact_Icc.image (by fun_prop)
    have h_cth_fin : volume (Metric.cthickening (100 * δ) (segment ℝ T.x T.y)) ≠ ⊤ :=
      hseg_compact.cthickening.measure_lt_top.ne
    have h_meas_mono : volume.real (Metric.cthickening (99 * (δ : ℝ)) T.carrier) ≤
        volume.real (Metric.cthickening (100 * (δ : ℝ)) (segment ℝ T.x T.y)) :=
      measureReal_mono h_subset_cth h_cth_fin
    have hvol_seg_bd :
        volume.real (Metric.cthickening (100 * (δ : ℝ)) (segment ℝ T.x T.y)) ≤
          netVolThinConstantM E * (δ : ℝ) ^ (n - 1) := by
      by_cases hδ_small : (δ : ℝ) ≤ 1 / 100
      · have h100δ_pos : 0 < 100 * (δ : ℝ) := by positivity
        have h100δ_le : 100 * (δ : ℝ) ≤ 1 := by linarith
        have hvol_brick : volume.real (Metric.cthickening (100 * (δ : ℝ)) (segment ℝ T.x T.y))
            ≤ C_vol * (100 * (δ : ℝ)) ^ (n - 1) :=
          hvol T.x T.y hTdist (100 * (δ : ℝ)) h100δ_pos h100δ_le
        have h_split : (100 * (δ : ℝ)) ^ (n - 1) = 100 ^ (n - 1) * (δ : ℝ) ^ (n - 1) :=
          mul_pow _ _ _
        have h100_nn : (0 : ℝ) ≤ 100 ^ (n - 1) := by positivity
        have hδpow_nn : (0 : ℝ) ≤ (δ : ℝ) ^ (n - 1) := by positivity
        have h100_n_pow_ge : (100 : ℝ) ^ (n - 1) ≤ 100 ^ n := by
          apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 100)
          omega
        have h_C_vol_pos : 0 ≤ C_vol := hC_vol_pos.le
        have hstep1 : C_vol * (100 * (δ : ℝ)) ^ (n - 1) ≤
            C_vol * 100 ^ n * (δ : ℝ) ^ (n - 1) := by
          rw [h_split]
          calc C_vol * (100 ^ (n - 1) * (δ : ℝ) ^ (n - 1))
              = (C_vol * 100 ^ (n - 1)) * (δ : ℝ) ^ (n - 1) := by ring
            _ ≤ (C_vol * 100 ^ n) * (δ : ℝ) ^ (n - 1) := by
                apply mul_le_mul_of_nonneg_right _ hδpow_nn
                exact mul_le_mul_of_nonneg_left h100_n_pow_ge h_C_vol_pos
        have h_C_vol_le : C_vol * 100 ^ n ≤ netVolThinConstantM E := by
          unfold netVolThinConstantM
          rw [dif_pos _hn]
          have h_vol_ball_nn : 0 ≤ MeasureTheory.volume.real (Metric.closedBall (0 : E) 200) *
              100 ^ Module.finrank ℝ E := by
            apply mul_nonneg MeasureTheory.measureReal_nonneg; positivity
          change C_vol * 100 ^ n ≤
            MeasureTheory.volume.real (Metric.closedBall (0 : E) 200) *
                100 ^ Module.finrank ℝ E +
              (Kakeya.Tube.unitSegmentCthickeningVolumeConstant E : ℝ) *
                100 ^ Module.finrank ℝ E + 1
          rw [← hC_vol_def]
          have hn_eq : (n : ℕ) = Module.finrank ℝ E := hn_def
          rw [hn_eq]
          linarith
        have h_C_vol_le' : C_vol * 100 ^ n * (δ : ℝ) ^ (n - 1) ≤
            netVolThinConstantM E * (δ : ℝ) ^ (n - 1) :=
          mul_le_mul_of_nonneg_right h_C_vol_le hδpow_nn
        linarith
      · push Not at hδ_small
        have hseg_in_ball :
            segment ℝ T.x T.y ⊆ Metric.closedBall (T.midpoint : E) (1/2) := by
          intro z hz
          obtain ⟨a, b, ha, hb, hab, hz_eq⟩ := hz
          have h_dir_norm : ‖T.direction‖ = 1 := by
            have := T.dist_eq_one
            rwa [dist_eq_norm, ← neg_sub, norm_neg] at this
          have hz_alt : z = T.midpoint + (b - 1/2) • T.direction := by
            rw [← hz_eq]
            simp only [Tube.midpoint, Tube.direction]
            have hab' : a = 1 - b := by linarith
            rw [hab']
            module
          rw [Metric.mem_closedBall, dist_eq_norm, hz_alt]
          have h_dist : z - T.midpoint = (b - 1/2) • T.direction := by
            rw [hz_alt]; abel
          have h_dist_norm : ‖(b - 1/2) • T.direction‖ = |b - 1/2| := by
            rw [norm_smul, h_dir_norm, mul_one, Real.norm_eq_abs]
          have h_abs : |b - 1/2| ≤ 1/2 := by
            rw [abs_le]; constructor <;> nlinarith
          have h_simp : T.midpoint + (b - 1/2) • T.direction - T.midpoint
              = (b - 1/2) • T.direction := by abel
          calc ‖T.midpoint + (b - 1/2) • T.direction - T.midpoint‖
              = ‖(b - 1/2) • T.direction‖ := by rw [h_simp]
            _ = |b - 1/2| := h_dist_norm
            _ ≤ 1/2 := h_abs
        have h_cth_in_ball :
            Metric.cthickening (100 * (δ : ℝ)) (segment ℝ T.x T.y) ⊆
              Metric.cthickening (100 * (δ : ℝ)) (Metric.closedBall (T.midpoint : E) (1/2)) :=
          Metric.cthickening_subset_of_subset _ hseg_in_ball
        have h_cth_ball :
            Metric.cthickening (100 * (δ : ℝ)) (Metric.closedBall (T.midpoint : E) (1/2))
              = Metric.closedBall T.midpoint (100 * (δ : ℝ) + 1/2) := by
          rw [cthickening_closedBall (by positivity) (by norm_num)]
        have h100δ_le : 100 * (δ : ℝ) ≤ 100 := by linarith
        have h_radius_le : (100 * (δ : ℝ) + 1/2) ≤ 100 + 1/2 := by linarith
        have h_ball_in_big :
            Metric.closedBall (T.midpoint : E) (100 * (δ : ℝ) + 1/2) ⊆
              Metric.closedBall (0 : E) 200 := by
          intro x hx
          rw [Metric.mem_closedBall] at hx ⊢
          calc dist x (0 : E)
              ≤ dist x T.midpoint + dist T.midpoint 0 := dist_triangle _ _ _
            _ ≤ (100 * (δ : ℝ) + 1/2) + ‖T.midpoint‖ := by
                rw [dist_zero_right]; linarith
            _ ≤ 100 + 1/2 + 2 := by linarith
            _ ≤ 200 := by norm_num
        have h_full_sub :
            Metric.cthickening (100 * (δ : ℝ)) (segment ℝ T.x T.y)
              ⊆ Metric.closedBall (0 : E) 200 := by
          calc Metric.cthickening (100 * (δ : ℝ)) (segment ℝ T.x T.y)
              ⊆ Metric.cthickening (100 * (δ : ℝ))
                  (Metric.closedBall (T.midpoint : E) (1/2)) := h_cth_in_ball
            _ = Metric.closedBall (T.midpoint : E) (100 * (δ : ℝ) + 1/2) := h_cth_ball
            _ ⊆ Metric.closedBall (0 : E) 200 := h_ball_in_big
        have hfin : volume (Metric.closedBall (0 : E) 200) ≠ ⊤ :=
          MeasureTheory.measure_closedBall_lt_top.ne
        have h_vol_le_ball :
            volume.real (Metric.cthickening (100 * (δ : ℝ)) (segment ℝ T.x T.y)) ≤
              volume.real (Metric.closedBall (0 : E) 200) :=
          measureReal_mono h_full_sub hfin
        have h_vol_ball_nn : 0 ≤ volume.real (Metric.closedBall (0 : E) 200) :=
          MeasureTheory.measureReal_nonneg
        have hδ_inv : (1 : ℝ) / 100 < (δ : ℝ) := hδ_small
        have h100δ_ge : (100 * (δ : ℝ) : ℝ) > 1 := by linarith
        have h_pow_ge : (100 * (δ : ℝ)) ^ (n - 1) ≥ 1 := by
          apply one_le_pow₀
          linarith
        have h_pow_eq : (100 * (δ : ℝ)) ^ (n - 1) = 100 ^ (n - 1) * (δ : ℝ) ^ (n - 1) :=
          mul_pow _ _ _
        have hδpow_nn : 0 ≤ (δ : ℝ) ^ (n - 1) := by positivity
        have h100pow_nn : 0 ≤ (100 : ℝ) ^ (n - 1) := by positivity
        have h_factor :
            (1 : ℝ) ≤ 100 ^ n * (δ : ℝ) ^ (n - 1) := by
          have h_step : (100 : ℝ) ^ n * (δ : ℝ) ^ (n - 1) =
              100 * (100 ^ (n - 1) * (δ : ℝ) ^ (n - 1)) := by
            rw [show (100 : ℝ) ^ n = 100 * 100 ^ (n - 1) from by
              rw [mul_comm, ← pow_succ, Nat.sub_add_cancel _hn]]
            ring
          rw [h_step]
          have h100ge1 : (1 : ℝ) ≤ 100 := by norm_num
          have h_prod : (1 : ℝ) ≤ 100 ^ (n - 1) * (δ : ℝ) ^ (n - 1) := by
            rw [← h_pow_eq]; exact h_pow_ge
          nlinarith
        have h_main :
            volume.real (Metric.closedBall (0 : E) 200) ≤
              volume.real (Metric.closedBall (0 : E) 200) * 100 ^ n * (δ : ℝ) ^ (n - 1) := by
          have hmul : volume.real (Metric.closedBall (0 : E) 200) * 1 ≤
              volume.real (Metric.closedBall (0 : E) 200) * (100 ^ n * (δ : ℝ) ^ (n - 1)) :=
            mul_le_mul_of_nonneg_left h_factor h_vol_ball_nn
          rw [mul_one] at hmul
          calc volume.real (Metric.closedBall (0 : E) 200) ≤ _ := hmul
            _ = volume.real (Metric.closedBall (0 : E) 200) * 100 ^ n
                  * (δ : ℝ) ^ (n - 1) := by ring
        have h_ball_le : volume.real (Metric.closedBall (0 : E) 200) * 100 ^ n ≤
            netVolThinConstantM E := by
          unfold netVolThinConstantM
          rw [dif_pos _hn]
          have h_other_nn : 0 ≤
              (Kakeya.Tube.unitSegmentCthickeningVolumeConstant E : ℝ) *
                100 ^ Module.finrank ℝ E := by
            apply mul_nonneg
            · exact NNReal.coe_nonneg _
            · positivity
          change volume.real (Metric.closedBall (0 : E) 200) * 100 ^ n ≤
            volume.real (Metric.closedBall (0 : E) 200) * 100 ^ Module.finrank ℝ E +
              (Kakeya.Tube.unitSegmentCthickeningVolumeConstant E : ℝ) *
                100 ^ Module.finrank ℝ E + 1
          have hn_eq : (n : ℕ) = Module.finrank ℝ E := hn_def
          rw [hn_eq]
          linarith
        calc volume.real (Metric.cthickening (100 * (δ : ℝ)) (segment ℝ T.x T.y))
            ≤ volume.real (Metric.closedBall (0 : E) 200) := h_vol_le_ball
          _ ≤ volume.real (Metric.closedBall (0 : E) 200) * 100 ^ n
                * (δ : ℝ) ^ (n - 1) := h_main
          _ ≤ netVolThinConstantM E * (δ : ℝ) ^ (n - 1) := by
              apply mul_le_mul_of_nonneg_right h_ball_le hδpow_nn
    have hreal_final :
        volume.real (Metric.cthickening (99 * (δ : ℝ)) T.carrier) ≤
          netVolThinConstantM E * (δ : ℝ) ^ (n - 1) :=
      h_meas_mono.trans hvol_seg_bd
    have hLHS_fin : volume (Metric.cthickening (99 * (δ : ℝ)) T.carrier) ≠ ⊤ :=
      ne_top_of_le_ne_top h_cth_fin (measure_mono h_subset_cth)
    have hRHS_fin : ENNReal.ofReal (netVolThinConstantM E) *
        (δ : ENNReal) ^ (Module.finrank ℝ E - 1) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
    refine (ENNReal.toReal_le_toReal hLHS_fin hRHS_fin).mp ?_
    simpa [Measure.real, hn_def, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (netVolThinConstantM_pos (E := E)).le,
      ENNReal.coe_toReal] using hreal_final
  · -- Covering property.
    intro T₀ hT₀_in_B2
    set m₀ : E := T₀.midpoint with hm₀_def
    set d₀ : E := T₀.direction with hd₀_def
    have hd₀_norm : ‖d₀‖ = 1 := by
      have h := T₀.dist_eq_one
      rw [dist_eq_norm] at h
      have hdir_eq : d₀ = -(T₀.x - T₀.y) := by
        rw [hd₀_def, Tube.direction]; abel
      rw [hdir_eq, norm_neg]; exact h
    have hmid_in_seg : m₀ ∈ segment ℝ T₀.x T₀.y := by
      refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
      simp only [hm₀_def, Tube.midpoint, smul_add]
    have h_cball_in_carrier : Metric.closedBall m₀ δ ⊆ T₀.carrier := by
      intro p hp
      rw [T₀.carrier_eq]
      exact Set.mem_iUnion₂.mpr ⟨m₀, hmid_in_seg, hp⟩
    have h_cball_in_B2 : Metric.closedBall m₀ δ ⊆ Metric.closedBall (0 : E) 2 :=
      h_cball_in_carrier.trans hT₀_in_B2
    have hm₀_norm_le : ‖m₀‖ ≤ 2 - δ := by
      by_cases hm0 : m₀ = (0 : E)
      · rw [hm0]; simp; linarith
      · have hm0_norm_pos : 0 < ‖m₀‖ := norm_pos_iff.mpr hm0
        set q : E := m₀ + (δ / ‖m₀‖) • m₀ with hq_def
        have hq_mem : q ∈ Metric.closedBall m₀ δ := by
          rw [Metric.mem_closedBall, hq_def, dist_eq_norm]
          have h_simp : m₀ + (δ / ‖m₀‖) • m₀ - m₀ = (δ / ‖m₀‖) • m₀ := by abel
          rw [h_simp, norm_smul, Real.norm_of_nonneg (by positivity)]
          rw [show δ / ‖m₀‖ * ‖m₀‖ = δ from by field_simp]
        have hq_in_B2 : ‖q‖ ≤ 2 := by
          have hq_in := h_cball_in_B2 hq_mem
          rw [Metric.mem_closedBall, dist_zero_right] at hq_in; exact hq_in
        have hq_eq : q = (1 + δ / ‖m₀‖) • m₀ := by
          rw [hq_def]; rw [add_smul, one_smul]
        rw [hq_eq, norm_smul] at hq_in_B2
        have h_coef_pos : 0 < (1 + δ / ‖m₀‖) := by
          have hdiv_pos : 0 < δ / ‖m₀‖ := div_pos hδ hm0_norm_pos
          linarith
        rw [Real.norm_of_nonneg h_coef_pos.le] at hq_in_B2
        have h_expand : (1 + δ / ‖m₀‖) * ‖m₀‖ = ‖m₀‖ + δ := by
          field_simp
        rw [h_expand] at hq_in_B2
        linarith
    have hm₀_in_5_2 : m₀ ∈ Metric.closedBall (0 : E) (5/2) := by
      rw [Metric.mem_closedBall, dist_zero_right]
      linarith
    obtain ⟨u', hu'_in_U, hu'_close⟩ := hU_cover d₀ hd₀_norm
    have hu'_unit : ‖u'‖ = 1 := hU_unit u' hu'_in_U
    obtain ⟨m', hm'_in_P, hm'_close⟩ := hP_cover m₀ hm₀_in_5_2
    have hm'_norm : ‖m'‖ ≤ 2 := by
      calc ‖m'‖ ≤ ‖m₀‖ + ‖m' - m₀‖ := by
            calc ‖m'‖ = ‖m₀ + (m' - m₀)‖ := by congr 1; abel
              _ ≤ ‖m₀‖ + ‖m' - m₀‖ := norm_add_le _ _
        _ ≤ ‖m₀‖ + δ := by
            have hsub_eq : ‖m' - m₀‖ = ‖m₀ - m'‖ := by rw [norm_sub_rev]
            linarith
        _ ≤ 2 := by linarith
    -- Build T' via existential to ensure it's opaque (avoids `tube_of` unfolding).
    obtain ⟨T', hT'_x, hT'_y, hT'_mid, hT'_dir, hT'_in_NetT⟩ :
        ∃ T' : Tube δ E,
          T'.x = m' - (1/2 : ℝ) • u' ∧
          T'.y = m' + (1/2 : ℝ) • u' ∧
          T'.midpoint = m' ∧
          T'.direction = u' ∧
          T' ∈ NetT := by
      refine ⟨tube_of u' hu'_unit m', tube_of_x u' hu'_unit m', tube_of_y u' hu'_unit m',
        tube_of_mid u' hu'_unit m', tube_of_dir u' hu'_unit m', ?_⟩
      rw [hNetT_def, Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [hNetT_full_def, Finset.mem_image]
        refine ⟨(⟨u', hu'_in_U⟩, m'), ?_, ?_⟩
        · rw [Finset.mem_product]
          refine ⟨Finset.mem_attach _ _, hm'_in_P⟩
        · rfl
      · rw [tube_of_mid u' hu'_unit m']; exact hm'_norm
    refine ⟨T', hT'_in_NetT, ?_⟩
    intro z hz
    rw [T₀.carrier_eq] at hz
    obtain ⟨z₀, hz₀_seg, hzz₀⟩ := Set.mem_iUnion₂.mp hz
    obtain ⟨a, b, ha, hb, hab, hz₀_eq⟩ := hz₀_seg
    have hz₀_alt : z₀ = m₀ + (b - 1/2) • d₀ := by
      rw [← hz₀_eq, hm₀_def, hd₀_def]
      simp only [Tube.midpoint, Tube.direction]
      have hab' : a = 1 - b := by linarith
      rw [hab']
      module
    have hz'₀_in_seg : (m' + (b - 1/2) • u') ∈ segment ℝ T'.x T'.y := by
      refine ⟨1 - b, b, by linarith, hb, by linarith, ?_⟩
      have hgoal : (1 - b) • (m' - (1/2 : ℝ) • u') + b • (m' + (1/2 : ℝ) • u') =
          m' + (b - 1/2) • u' := by module
      rw [hT'_x, hT'_y]; exact hgoal
    have hz'₀_in_carrier : (m' + (b - 1/2) • u') ∈ T'.carrier := by
      rw [T'.carrier_eq]
      exact Set.mem_iUnion₂.mpr ⟨_, hz'₀_in_seg, Metric.mem_closedBall_self hδ.le⟩
    have h_z₀z'₀ : z₀ - (m' + (b - 1/2) • u') = (m₀ - m') + (b - 1/2) • (d₀ - u') := by
      rw [hz₀_alt]
      show (m₀ + (b - 1/2) • d₀) - (m' + (b - 1/2) • u') =
        (m₀ - m') + (b - 1/2) • (d₀ - u')
      simp only [smul_sub]
      module
    have h_z₀z'₀_norm : ‖z₀ - (m' + (b - 1/2) • u')‖ ≤ (3/2) * δ := by
      rw [h_z₀z'₀]
      have h1 : ‖(m₀ - m') + (b - 1/2) • (d₀ - u')‖ ≤
          ‖m₀ - m'‖ + ‖(b - 1/2) • (d₀ - u')‖ := norm_add_le _ _
      have h2 : ‖(b - 1/2) • (d₀ - u')‖ = |b - 1/2| * ‖d₀ - u'‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      have h3 : |b - 1/2| ≤ 1/2 := by rw [abs_le]; constructor <;> nlinarith
      have h4 : ‖d₀ - u'‖ ≤ δ := by
        have hud : ‖u' - d₀‖ ≤ δ := hu'_close
        rwa [norm_sub_rev] at hud
      have h5 : |b - 1/2| * ‖d₀ - u'‖ ≤ (1/2) * δ := by
        apply mul_le_mul h3 h4 (norm_nonneg _) (by linarith)
      have h6 : ‖m₀ - m'‖ ≤ δ := hm'_close
      linarith
    have hzz₀_norm : ‖z - z₀‖ ≤ δ := by
      rw [← dist_eq_norm]
      rw [Metric.mem_closedBall] at hzz₀
      exact hzz₀
    have h_zz'₀_norm : ‖z - (m' + (b - 1/2) • u')‖ ≤ (5/2) * δ := by
      calc ‖z - (m' + (b - 1/2) • u')‖
          = ‖(z - z₀) + (z₀ - (m' + (b - 1/2) • u'))‖ := by congr 1; abel
        _ ≤ ‖z - z₀‖ + ‖z₀ - (m' + (b - 1/2) • u')‖ := norm_add_le _ _
        _ ≤ δ + (3/2) * δ := by linarith
        _ = (5/2) * δ := by ring
    have hz_in_cball : z ∈ Metric.closedBall (m' + (b - 1/2) • u') (99 * δ) := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      linarith
    have h_singleton_sub : ({(m' + (b - 1/2) • u')} : Set E) ⊆ T'.carrier := by
      intro x hx; rw [Set.mem_singleton_iff] at hx; rw [hx]; exact hz'₀_in_carrier
    have h_cth_sub : Metric.cthickening (99 * δ) ({(m' + (b - 1/2) • u')} : Set E) ⊆
        Metric.cthickening (99 * δ) T'.carrier :=
      Metric.cthickening_subset_of_subset _ h_singleton_sub
    have h_singleton_cth : Metric.cthickening (99 * δ) ({(m' + (b - 1/2) • u')} : Set E) =
        Metric.closedBall (m' + (b - 1/2) • u') (99 * δ) := by
      have h99_nn : (0 : ℝ) ≤ 99 * δ := by positivity
      rw [Metric.cthickening_singleton _ h99_nn]
    rw [← h_singleton_cth] at hz_in_cball
    exact h_cth_sub hz_in_cball

/-- **Thin** variant of `exists_ed_tube_net`. Same covering property, plus a
per-member volume bound `vol(cthickening 99·δ T₀'.carrier) ≤ netVolThinConstantM E · δ^(n-1)`. -/
lemma exists_ed_tube_net_thin [Nontrivial E]
    {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ NetT : Finset (Tube δ E),
      (NetT.card : ℝ) ≤ netGeomConstantC E * (δ : ℝ) ^ (-(netGeomConstantM E)) ∧
      (∀ T₀' ∈ NetT, MeasurableSet T₀'.carrier) ∧
      (∀ T₀' ∈ NetT, T₀'.carrier ⊆ Metric.closedBall (0 : E) (7 / 2)) ∧
      (∀ T₀' ∈ NetT, volume (Metric.cthickening (99 * (δ : ℝ)) T₀'.carrier)
          ≤ ENNReal.ofReal (netVolThinConstantM E) *
            (δ : ENNReal) ^ (Module.finrank ℝ E - 1)) ∧
      ∀ (T₀ : Tube δ E), T₀.carrier ⊆ Metric.closedBall (0 : E) 2 →
        ∃ T₀' ∈ NetT,
          T₀.carrier ⊆ Metric.cthickening (99 * (δ : ℝ)) T₀'.carrier := by
  classical
  -- Directly expose the tube net from `exists_thin_tube_net`; the previous
  -- `.image Tube.toConvexBody` cast is dropped to preserve the long-axis
  -- structure needed downstream by `badAgainstSet_count_le_of_ED_thinBox`.
  obtain ⟨Net_tubes, hcard_tubes, hsub_tubes, hvol_tubes, hcover_tubes⟩ :=
    exists_thin_tube_net E hδ hδ1
  refine ⟨Net_tubes, hcard_tubes, ?_, hsub_tubes, hvol_tubes, hcover_tubes⟩
  intro T _hT_mem
  exact T.isCompact.measurableSet

/-- **Thin** variant of `exists_chernoff_tube_net_with_ed_approx`. Same joint
testing-net statement, but each net member also satisfies the per-member volume
bound `vol(cthickening (99·δ) T₀'.carrier) ≤ netVolThinConstantM E · δ^(n-1)`. -/
lemma exists_chernoff_tube_net_with_ed_approx_thin
    [ProperSpace E] [Nontrivial E]
    {δ : NNReal} {c : ℝ} (_hc : 0 < c) (_hδ : 0 < δ) (_hδ1 : δ < 1)
    (_hn : 1 < Module.finrank ℝ E)
    {ι : Type u} (s : Finset ι)
    (T : ι → ShadedTube δ E)
    (_hB : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1)
    (_hT_ED : (s : Set ι).Pairwise
      (fun i j => IsEssentiallyDistinct
        ((T i).toTube.carrier) ((T j).toTube.carrier)))
    (Ω : Type*) [MeasurableSpace Ω] [HasUniformTranslation Ω E]
    (J : ℕ) [NeZero J]
    (M_dim : ℕ) (_hM_dim_pos : 0 < M_dim)
    (ρ : ℝ) (_hρ_pos : 0 < ρ)
    -- (A') refactor: the consolidated input is the *integral-form*
    -- Frostman/slice bound (in the `ρ`-scaled form consumed by
    -- `productEdFailCountSet_chernoff_tail`), universally quantified over
    -- every candidate net member `T₀'_t` satisfying the standard B(0,7/2)
    -- containment and thin-volume bound. The previous pointwise
    -- `C_pack`-shape inputs are subsumed by this single hypothesis.
    -- Callers with a pointwise `C_pack`-bound can derive the integral form
    -- by `integral_mono` over `uniformBallMeasure E` (the unit-mass measure).
    -- For the Frostman caller (`ρ := 1`) this collapses to the previous
    -- `∫... v dv` shape via `one_smul`.
    (_hM_dim_ge_integral :
      ∀ (T₀'_t : Tube δ E),
        T₀'_t.carrier ⊆ Metric.closedBall (0 : E) (7 / 2) →
        volume (Metric.cthickening (99 * (δ : ℝ)) T₀'_t.carrier)
          ≤ ENNReal.ofReal (netVolThinConstantM E) *
            (δ : ENNReal) ^ (Module.finrank ℝ E - 1) →
        (J : ℝ) *
          (∫ v : E,
            edFailCountSet s (fun i => (T i).toTube)
              (Metric.cthickening (99 * (δ : ℝ)) T₀'_t.carrier) c (ρ • v)
              ∂(uniformBallMeasure E))
            < (M_dim : ℝ))
    (M_inner : ℕ) (_hM_inner_pos : 0 < M_inner)
    (_hδ_small_ed :
      (netGeomConstantC E) * (δ : ℝ) ^ (-(netGeomConstantM E)) *
        Real.exp (10 * Real.exp 1 - (M_inner : ℝ)) ≤ 1 / 3) :
    ∃ NetED : Finset (Tube δ E),
      ((NetED.card : ℝ) * Real.exp (10 * Real.exp 1 - (M_inner : ℝ)) ≤ 1/3) ∧
      (∀ T₀' ∈ NetED, MeasurableSet T₀'.carrier) ∧
      (∀ T₀' ∈ NetED, T₀'.carrier ⊆ Metric.closedBall (0 : E) (7 / 2)) ∧
      (∀ T₀' ∈ NetED, volume (Metric.cthickening (99 * (δ : ℝ)) T₀'.carrier)
          ≤ ENNReal.ofReal (netVolThinConstantM E) *
            (δ : ENNReal) ^ (Module.finrank ℝ E - 1)) ∧
      (∀ (ω : Fin J → Ω)
          (_hBdd : ∀ j, HasUniformTranslation.shift (Ω := Ω) (E := E) (ω j) (0 : E)
            ∈ Metric.closedBall (0 : E) 1)
          (p : ι × Fin J),
          p.1 ∈ s →
          ∃ T₀' ∈ NetED,
            (((HasUniformTranslation.shift (Ω := Ω) (E := E) (ω p.2)).actShadedTube
                (T p.1)).carrier)
              ⊆ Metric.cthickening (99 * (δ : ℝ)) T₀'.carrier) ∧
      (∀ T₀' ∈ NetED,
        (J : ℝ) *
          (∫ v : E,
            edFailCountSet s (fun i => (T i).toTube)
              (Metric.cthickening (99 * (δ : ℝ)) T₀'.carrier) c (ρ • v)
              ∂(uniformBallMeasure E))
            < (M_dim : ℝ)) := by
  obtain ⟨NetT, hcard, hmeas, hsub, hvol, hcover⟩ :=
    exists_ed_tube_net_thin E _hδ _hδ1
  have hP1 :
      (NetT.card : ℝ) * Real.exp (10 * Real.exp 1 - (M_inner : ℝ)) ≤ 1/3 := by
    have hexp_nn : 0 ≤ Real.exp (10 * Real.exp 1 - (M_inner : ℝ)) :=
      (Real.exp_pos _).le
    have hcard' :
        (NetT.card : ℝ) * Real.exp (10 * Real.exp 1 - (M_inner : ℝ))
          ≤ (netGeomConstantC E) * δ ^ (-(netGeomConstantM E)) *
              Real.exp (10 * Real.exp 1 - (M_inner : ℝ)) :=
      mul_le_mul_of_nonneg_right hcard hexp_nn
    exact hcard'.trans _hδ_small_ed
  refine ⟨NetT, hP1, hmeas, hsub, hvol, ?_, ?_⟩
  · intro ω hBdd p hp
    set Rp : Translation E := HasUniformTranslation.shift (Ω := Ω) (E := E) (ω p.2)
    set Tp_acted : Tube δ E := Rp.actTube (T p.1).toTube with hTp_acted_def
    have hTp_carrier_eq :
        Tp_acted.carrier
          = (Rp.actShadedTube (T p.1)).carrier := by
      rw [hTp_acted_def, Translation.actShadedTube_toTube]
    have hT_p_in_B1 : (T p.1).carrier ⊆ Metric.closedBall (0 : E) 1 := _hB p.1 hp
    have hRp0 : Rp 0 ∈ Metric.closedBall (0 : E) 1 := by
      simpa [Rp] using hBdd p.2
    have hActed_in_B2 :
        (Rp.actShadedTube (T p.1)).carrier ⊆ Metric.closedBall (0 : E) 2 := by
      rw [Translation.actShadedTube_carrier]
      intro x hx
      rcases hx with ⟨y, hy_mem, hxy⟩
      subst hxy
      have hdist_y0 : dist y (0 : E) ≤ 1 := by
        rcases hy_mem with hy_mem
        simpa [Metric.mem_closedBall] using hT_p_in_B1 hy_mem
      have hdist_Ry_R0 : dist (Rp y) (Rp 0) = dist y (0 : E) := Rp.dist_map y 0
      have hdist_R0_0 : dist (Rp 0) (0 : E) ≤ 1 := by
        simpa [Metric.mem_closedBall] using hRp0
      have hdist : dist (Rp y) (0 : E) ≤ 2 := by
        calc dist (Rp y) (0 : E)
            ≤ dist (Rp y) (Rp 0) + dist (Rp 0) (0 : E) := dist_triangle _ _ _
          _ = dist y (0 : E) + dist (Rp 0) (0 : E) := by rw [hdist_Ry_R0]
          _ ≤ 1 + 1 := add_le_add hdist_y0 hdist_R0_0
          _ = 2 := by norm_num
      exact Metric.mem_closedBall.mpr hdist
    have hTp_acted_in_B2 : Tp_acted.carrier ⊆ Metric.closedBall (0 : E) 2 := by
      rw [hTp_carrier_eq]; exact hActed_in_B2
    obtain ⟨T₀', hT₀'_mem, hsubT₀⟩ := hcover Tp_acted hTp_acted_in_B2
    refine ⟨T₀', hT₀'_mem, ?_⟩
    have h_goal_eq :
        (Rp.actShadedTube (T p.1)).carrier = Tp_acted.carrier := hTp_carrier_eq.symm
    rw [h_goal_eq]
    exact hsubT₀
  · intro T₀' _hT₀'_mem
    exact _hM_dim_ge_integral T₀' (hsub T₀' _hT₀'_mem) (hvol T₀' _hT₀'_mem)

end EDChernoffNet

end Kakeya
