import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.ClusterDefinitions
import MyLeanRepo.Kakeya.Cinematic.Targets.RectangleRefinement.DoublingLemma
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Finite cluster covers

The cinematic curvature hypothesis supplies an explicit doubling constant.
Iterating the doubling cover yields the polynomial-in-`A` cluster cover used
in the separation reduction.
-/

noncomputable section

namespace Kakeya.Cinematic

open Classical Set Finset

lemma doubling_cover_finset
    {family : Set C2Function} {K D : ℝ}
    (hfamily : IsCinematicFamily family K D)
    {center : C2Function} (hcenter : center ∈ family)
    {radius : ℝ} (hradius : 0 < radius) :
    ∃ centers : Finset C2Function,
      (centers : Set C2Function) ⊆ family ∧
      {f | f ∈ family ∧ c2Distance center f ≤ radius} ⊆
        ⋃ c ∈ centers, Metric.closedBall c (radius / 2) ∧
      (centers.card : ℝ) ≤ D := by
  obtain ⟨centers, hfinite, hsub, hcard, hcover⟩ :=
    hfamily.2.1 hcenter radius hradius
  let centersFinset := hfinite.toFinset
  refine ⟨centersFinset, ?_, ?_, ?_⟩
  · simpa [centersFinset] using hsub
  · intro f hf
    obtain ⟨c, hc, hcf⟩ := hcover hf.1 hf.2
    exact Set.mem_iUnion₂.mpr ⟨c, by simpa [centersFinset] using hc,
      by simpa [Metric.mem_closedBall, c2Distance, dist_comm] using hcf⟩
  · have hcard_eq : centersFinset.card = centers.ncard :=
      (Set.ncard_eq_toFinset_card centers hfinite).symm
    rw [hcard_eq]
    exact hcard

lemma iterated_doubling_cover
    {family : Set C2Function} {K D : ℝ}
    (hfamily : IsCinematicFamily family K D)
    (center : C2Function) (hcenter : center ∈ family)
    (radius : ℝ) (hradius : 0 < radius) :
    ∀ depth : ℕ, ∃ centers : Finset C2Function,
      (centers : Set C2Function) ⊆ family ∧
      {f | f ∈ family ∧ c2Distance center f ≤ radius} ⊆
        ⋃ c ∈ centers,
          Metric.closedBall c (radius / 2 ^ depth) ∧
      (centers.card : ℝ) ≤ D ^ depth := by
  intro depth
  induction depth with
  | zero =>
      refine ⟨{center}, by simpa, ?_, by simp⟩
      intro f hf
      exact Set.mem_iUnion₂.mpr ⟨center, by simp,
        by simpa [Metric.mem_closedBall, c2Distance, dist_comm] using hf.2⟩
  | succ depth ih =>
      obtain ⟨coarse, hcoarse_sub, hcoarse_cover, hcoarse_card⟩ := ih
      let coarseRadius := radius / 2 ^ depth
      have hcoarse_radius : 0 < coarseRadius := by positivity
      let children (c : C2Function) : Finset C2Function :=
        if hc : c ∈ coarse then
          Classical.choose
            (doubling_cover_finset hfamily
              (hcoarse_sub hc) hcoarse_radius)
        else ∅
      have hchildren : ∀ c ∈ coarse,
          ((children c : Set C2Function) ⊆ family) ∧
          {f | f ∈ family ∧
              c2Distance c f ≤ coarseRadius} ⊆
            ⋃ d ∈ children c,
              Metric.closedBall d (coarseRadius / 2) ∧
          ((children c).card : ℝ) ≤ D := by
        intro c hc
        dsimp only [children]
        rw [dif_pos hc]
        exact Classical.choose_spec
          (doubling_cover_finset hfamily
            (hcoarse_sub hc) hcoarse_radius)
      let refined := coarse.biUnion children
      refine ⟨refined, ?_, ?_, ?_⟩
      · intro d hd
        obtain ⟨c, hc, hd⟩ := Finset.mem_biUnion.mp hd
        exact (hchildren c hc).1 hd
      · intro f hf
        obtain ⟨c, hc, hfc⟩ :=
          Set.mem_iUnion₂.mp (hcoarse_cover hf)
        have hdist : c2Distance c f ≤ coarseRadius := by
          simpa [Metric.mem_closedBall, c2Distance, dist_comm] using hfc
        obtain ⟨d, hd, hfd⟩ :=
          Set.mem_iUnion₂.mp ((hchildren c hc).2.1 ⟨hf.1, hdist⟩)
        have hdrefined : d ∈ refined :=
          Finset.mem_biUnion.mpr ⟨c, hc, hd⟩
        have hradius_eq :
            coarseRadius / 2 = radius / 2 ^ (depth + 1) := by
          dsimp only [coarseRadius]
          rw [pow_succ]
          ring
        exact Set.mem_iUnion₂.mpr ⟨d, hdrefined, by
          rwa [hradius_eq] at hfd⟩
      · have hcard_nat :
            refined.card ≤ ∑ c ∈ coarse, (children c).card :=
          Finset.card_biUnion_le
        have hD_nonneg : 0 ≤ D := by
          have hcenters_nonempty :
              ∃ centers : Set C2Function,
                centers.Finite ∧ centers ⊆ family ∧
                (centers.ncard : ℝ) ≤ D ∧
                ∀ ⦃g⦄, g ∈ family →
                  c2Distance center g ≤ 1 →
                    ∃ h ∈ centers,
                      c2Distance h g ≤ 1 / 2 :=
            hfamily.2.1 hcenter 1 (by norm_num)
          obtain ⟨centers, hfinite, _, hcard, hcover⟩ :=
            hcenters_nonempty
          have hnonempty_centers : centers.Nonempty := by
            obtain ⟨h, hh, _⟩ :=
              hcover hcenter (by simp [c2Distance])
            exact ⟨h, hh⟩
          have : 0 < (centers.ncard : ℝ) := by
            exact_mod_cast
              (Set.ncard_pos hfinite |>.2 hnonempty_centers)
          linarith
        calc
          (refined.card : ℝ) ≤
              (∑ c ∈ coarse, (children c).card : ℕ) := by
            exact_mod_cast hcard_nat
          _ = ∑ c ∈ coarse, ((children c).card : ℝ) := by simp
          _ ≤ ∑ _c ∈ coarse, D := by
            apply Finset.sum_le_sum
            intro c hc
            exact (hchildren c hc).2.2
          _ = D * (coarse.card : ℝ) := by
            simp [mul_comm]
          _ ≤ D * D ^ depth := by
            gcongr
          _ = D ^ (depth + 1) := by
            rw [pow_succ]
            ring

lemma exists_dyadic_depth
    (large small : ℝ) (hlarge : 0 < large) (hsmall : 0 < small) :
    ∃ depth : ℕ, large / 2 ^ depth ≤ small := by
  obtain ⟨depth, hdepth⟩ := exists_nat_gt (large / small)
  have hpow_bound : ∀ n : ℕ, (n : ℝ) + 1 ≤ 2 ^ n := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
        rw [pow_succ]
        norm_num at ih ⊢
        linarith
  have hpow : (large / small) < (2 ^ (depth + 1) : ℝ) := by
    have hdepth_real : (large / small) < (depth : ℝ) := by
      exact_mod_cast hdepth
    have hbound := hpow_bound (depth + 1)
    norm_num at hbound
    linarith
  have hquotient :
      large / (2 ^ (depth + 1) : ℝ) < small := by
    calc
      large / (2 ^ (depth + 1) : ℝ) <
          large / (large / small) := by gcongr
      _ = small := by field_simp [hlarge.ne', hsmall.ne']
  exact ⟨depth + 1, hquotient.le⟩

lemma exists_dyadic_depth_with_polynomial_bound
    (D large small : ℝ)
    (hD : 1 ≤ D)
    (hlarge : 0 < large)
    (hsmall : 0 < small) :
    ∃ depth : ℕ,
      large / 2 ^ depth ≤ small ∧
      D ^ depth ≤
        D *
          Real.rpow
            (max large small / small)
            (Real.log D / Real.log 2) := by
  let radius := max large small
  have hradius : 0 < radius := by
    dsimp only [radius]
    positivity
  have hsmall_radius : small ≤ radius := by
    dsimp only [radius]
    exact le_max_right _ _
  have hratio : 1 ≤ radius / small := by
    exact (le_div_iff₀ hsmall).2 <| by simpa using hsmall_radius
  have hratio_pos : 0 < radius / small := lt_of_lt_of_le zero_lt_one hratio
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let alpha : ℝ := Real.log (radius / small) / Real.log 2
  have halpha : 0 ≤ alpha := by
    dsimp only [alpha]
    exact div_nonneg (Real.log_nonneg hratio) hlog2.le
  let depth : ℕ := Nat.ceil alpha
  have hdepth_lower : alpha ≤ (depth : ℝ) := Nat.le_ceil _
  have hdepth_upper : (depth : ℝ) < alpha + 1 :=
    Nat.ceil_lt_add_one halpha
  have htwo_alpha : Real.rpow 2 alpha = radius / small := by
    simpa [alpha, Real.logb] using
      (Real.rpow_logb
        (show (0 : ℝ) < 2 by norm_num)
        (show (2 : ℝ) ≠ 1 by norm_num)
        hratio_pos)
  have htwo_depth :
      radius / small ≤ (2 : ℝ) ^ depth := by
    calc
      radius / small = Real.rpow 2 alpha := htwo_alpha.symm
      _ ≤ Real.rpow 2 (depth : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hdepth_lower
      _ = (2 : ℝ) ^ depth := Real.rpow_natCast 2 depth
  have hradius_scale :
      radius / (2 : ℝ) ^ depth ≤ small := by
    calc
      radius / (2 : ℝ) ^ depth ≤ radius / (radius / small) := by
        gcongr
      _ = small := by
        field_simp [hradius.ne', hsmall.ne']
  have hlarge_radius : large ≤ radius := by
    dsimp only [radius]
    exact le_max_left _ _
  have hlarge_scale :
      large / (2 : ℝ) ^ depth ≤ small := by
    exact
      (div_le_div_of_nonneg_right hlarge_radius <| by positivity).trans
        hradius_scale
  have hD_pos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hD_depth :
      D ^ depth ≤ Real.rpow D (alpha + 1) := by
    calc
      D ^ depth = Real.rpow D (depth : ℝ) := by
        simp [Real.rpow_natCast]
      _ ≤ Real.rpow D (alpha + 1) :=
        Real.rpow_le_rpow_of_exponent_le hD hdepth_upper.le
  have hD_alpha :
      Real.rpow D alpha =
        Real.rpow (radius / small) (Real.log D / Real.log 2) := by
    calc
      Real.rpow D alpha =
          Real.exp (Real.log D * alpha) :=
        Real.rpow_def_of_pos hD_pos alpha
      _ =
          Real.exp
            (Real.log (radius / small) *
              (Real.log D / Real.log 2)) := by
        congr 1
        dsimp only [alpha]
        ring
      _ =
          Real.rpow (radius / small)
            (Real.log D / Real.log 2) :=
        (Real.rpow_def_of_pos hratio_pos
          (Real.log D / Real.log 2)).symm
  have hD_bound :
      Real.rpow D (alpha + 1) =
        D *
          Real.rpow (radius / small)
            (Real.log D / Real.log 2) := by
    calc
      Real.rpow D (alpha + 1) =
          Real.rpow D alpha * Real.rpow D 1 :=
        Real.rpow_add hD_pos alpha 1
      _ =
          D *
            Real.rpow (radius / small)
              (Real.log D / Real.log 2) := by
        rw [hD_alpha]
        have hone : Real.rpow D 1 = D := Real.rpow_one D
        rw [hone]
        ring
  refine ⟨depth, hlarge_scale, ?_⟩
  rw [hD_bound] at hD_depth
  simpa [radius] using hD_depth

lemma finite_family_cluster_cover_polynomial
    {family : Set C2Function} {K D : ℝ}
    (hfamily : IsCinematicFamily family K D)
    (hD : 1 ≤ D)
    {F : FiniteFunctionFamily} (hF : F.carrier ⊆ family)
    {diameter radius : ℝ} (hdiameter : 0 < diameter)
    (hradius : 0 < radius)
    (hdiam : ∀ f ∈ F.carrier, ∀ g ∈ F.carrier,
      c2Distance f g ≤ diameter) :
    ∃ centers : Finset C2Function,
      (centers : Set C2Function) ⊆ family ∧
      F.carrier ⊆ ⋃ c ∈ centers, Metric.closedBall c radius ∧
      ∃ depth : ℕ,
        diameter / 2 ^ depth ≤ radius ∧
        (centers.card : ℝ) ≤ D ^ depth ∧
        (centers.card : ℝ) ≤
          D *
            Real.rpow
              (max diameter radius / radius)
              (Real.log D / Real.log 2) := by
  let outerRadius := max diameter radius
  have houter : 0 < outerRadius := by
    dsimp only [outerRadius]
    positivity
  have hdiameter_outer : diameter ≤ outerRadius := by
    dsimp only [outerRadius]
    exact le_max_left _ _
  obtain ⟨depth, hscaleOuter, hpolynomial⟩ :=
    exists_dyadic_depth_with_polynomial_bound
      D outerRadius radius hD houter hradius
  have houter_radius : max outerRadius radius = outerRadius := by
    apply max_eq_left
    dsimp only [outerRadius]
    exact le_max_right _ _
  rw [houter_radius] at hpolynomial
  have hscale :
      diameter / (2 : ℝ) ^ depth ≤ radius := by
    exact
      (div_le_div_of_nonneg_right hdiameter_outer <| by positivity).trans
        hscaleOuter
  by_cases hFempty : F.carrier = ∅
  · refine ⟨∅, by simp, by simp [hFempty], depth, hscale, ?_, ?_⟩
    · simp
      exact pow_nonneg (by linarith) _
    · simp
      exact mul_nonneg (by linarith) <|
        Real.rpow_nonneg (by positivity) _
  · obtain ⟨center, hcenterF⟩ :=
      Set.nonempty_iff_ne_empty.mpr hFempty
    have hcenter : center ∈ family := hF hcenterF
    obtain ⟨centers, hcenters, hcover, hcard⟩ :=
      iterated_doubling_cover hfamily center hcenter
        outerRadius houter depth
    refine ⟨centers, hcenters, ?_, depth, hscale, hcard, ?_⟩
    · intro f hf
      obtain ⟨c, hc, hfc⟩ :=
        Set.mem_iUnion₂.mp
          (hcover ⟨hF hf, (hdiam center hcenterF f hf).trans
            hdiameter_outer⟩)
      exact Set.mem_iUnion₂.mpr ⟨c, hc, by
        have hdist :
            c2Distance f c ≤ outerRadius / 2 ^ depth := by
          simpa [Metric.mem_closedBall, c2Distance] using hfc
        exact (show dist f c ≤ radius from hdist.trans hscaleOuter)⟩
    · simpa [outerRadius] using hcard.trans hpolynomial

lemma finite_family_cluster_cover
    {family : Set C2Function} {K D : ℝ}
    (hfamily : IsCinematicFamily family K D)
    (hD : 1 ≤ D)
    {F : FiniteFunctionFamily} (hF : F.carrier ⊆ family)
    {diameter radius : ℝ} (hdiameter : 0 < diameter)
    (hradius : 0 < radius)
    (hdiam : ∀ f ∈ F.carrier, ∀ g ∈ F.carrier,
      c2Distance f g ≤ diameter) :
    ∃ centers : Finset C2Function,
      (centers : Set C2Function) ⊆ family ∧
      F.carrier ⊆ ⋃ c ∈ centers, Metric.closedBall c radius ∧
      ∃ depth : ℕ,
        diameter / 2 ^ depth ≤ radius ∧
        (centers.card : ℝ) ≤ D ^ depth := by
  by_cases hFempty : F.carrier = ∅
  · obtain ⟨depth, hdepth⟩ :=
      exists_dyadic_depth diameter radius hdiameter hradius
    refine ⟨∅, by simp, by simp [hFempty], depth, hdepth, ?_⟩
    simp only [Finset.card_empty, Nat.cast_zero]
    exact pow_nonneg (by linarith) _
  · obtain ⟨center, hcenterF⟩ :=
      Set.nonempty_iff_ne_empty.mpr hFempty
    have hcenter : center ∈ family := hF hcenterF
    obtain ⟨depth, hdepth⟩ :=
      exists_dyadic_depth diameter radius hdiameter hradius
    obtain ⟨centers, hcenters, hcover, hcard⟩ :=
      iterated_doubling_cover hfamily center hcenter
        diameter hdiameter depth
    refine ⟨centers, hcenters, ?_, depth, hdepth, hcard⟩
    intro f hf
    obtain ⟨c, hc, hfc⟩ :=
      Set.mem_iUnion₂.mp (hcover ⟨hF hf, hdiam center hcenterF f hf⟩)
    exact Set.mem_iUnion₂.mpr ⟨c, hc, by
      have hdist : c2Distance f c ≤ diameter / 2 ^ depth := by
        simpa [Metric.mem_closedBall, c2Distance] using hfc
      exact (show dist f c ≤ radius from hdist.trans hdepth)⟩

end Kakeya.Cinematic
