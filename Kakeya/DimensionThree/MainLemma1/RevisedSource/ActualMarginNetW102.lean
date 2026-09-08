module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.GeneralLineEDAnalyticBridgeW95
public import Kakeya.Uniform.GridNet

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody
open scoped ENNReal NNReal

namespace Kakeya.ml1Boot.TrialRestartW94

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

universe uE

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-- A grid net at a parameterized fraction of the target parent radius.  The
covering and separation statements are inherited from the existing tight net;
the target-radius parent is obtained by rescaling its endpoints. -/
theorem exists_scaled_grid_net_w102
    {rho alpha : NNReal} (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (halpha : 0 < alpha) (halpha1 : alpha ≤ 1) :
    ∃ G : Finset (Tube (alpha * rho) E),
      (∀ {sigma : NNReal} (U : Tube sigma E),
        2 * (sigma : Real) ≤ (alpha * rho : Real) ->
        U.midpoint ∈ Metric.closedBall (0 : E) 3 ->
        ∃ W ∈ G, U.toConvexSpaceBody ≤ W.toConvexSpaceBody ∧
          ‖U.midpoint - W.midpoint‖ ≤ (alpha * rho : Real) / 32 ∧
          ‖U.direction - W.direction‖ ≤ (alpha * rho : Real) / 16) ∧
      (∀ a ∈ G, ∀ b ∈ G, a ≠ b ->
        (alpha * rho : Real) / 32 ≤ ‖a.x - b.x‖ + ‖a.y - b.y‖) ∧
      (∀ W ∈ G, W.carrier ⊆ Metric.closedBall (0 : E) 5) := by
  have hprod : 0 < alpha * rho := mul_pos halpha hrho
  have hprod1 : (alpha * rho : Real) ≤ 1 := by
    exact_mod_cast (mul_le_one₀ halpha1 (by positivity) hrho1)
  obtain ⟨G, hcover, hsep, hball, hmid⟩ :=
    Tube.grid_net_tight (E := E) hprod hprod1
  exact ⟨G, hcover, hsep, hball⟩

/-- Rescaling a scaled-net node changes only its radius, not its parameter
coordinates.  This is the transport used by a prospective small-bin tree. -/
theorem scaled_grid_node_rescale_w102
    {rho alpha : NNReal} (W : Tube (alpha * rho) E) :
    (W.rescale rho).x = W.x ∧ (W.rescale rho).y = W.y ∧
      (W.rescale rho).midpoint = W.midpoint ∧
      (W.rescale rho).direction = W.direction := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/- The existing tight packing proof is scale-parametric once both the net and
  the test tube have the same radius.  This wrapper keeps that fact explicit
  for the small-bin radius used by the prospective weighted selector. -/
theorem scaled_grid_overlap_w102
    {delta rho alpha : NNReal} (hrho : 0 < rho)
    (halpha : 0 < alpha) (G : Finset (Tube (alpha * rho) E))
    (hsep : ∀ a ∈ G, ∀ b ∈ G, a ≠ b ->
      (alpha * rho : Real) / 32 ≤ ‖a.x - b.x‖ + ‖a.y - b.y‖)
    (V : Tube (alpha * rho) E) :
    (G.filter (fun W => ∃ (U : Tube delta E),
        U.carrier ⊆ Metric.closedBall (0 : E) 1 ∧
        U.toConvexSpaceBody ≤ W.toConvexSpaceBody ∧
        U.toConvexSpaceBody ≤ V.toConvexSpaceBody)).card ≤
      2 * (3073 * (Module.finrank Real E) + 1) ^
        (2 * Module.finrank Real E) := by
  exact Tube.grid_overlap_tight (δ := delta) (ρ := alpha * rho)
    (mul_pos halpha hrho) G hsep V

/- Target-radius packing for a small-bin net.  The caller supplies the
   parameter-dependent packing base; this is the honest constant change needed
   when the target tube is wider than the net nodes. -/
theorem scaled_grid_overlap_target_w102
    {delta rho alpha : NNReal} (hrho : 0 < rho)
    (halpha : 0 < alpha) (halpha1 : alpha ≤ 1)
    (G : Finset (Tube (alpha * rho) E))
    (hsep : ∀ a ∈ G, ∀ b ∈ G, a ≠ b ->
      (alpha * rho : Real) / 32 ≤ ‖a.x - b.x‖ + ‖a.y - b.y‖)
    (V : Tube rho E) (Cpack : Nat)
    (hCpack : (24 * (rho : Real) + ((alpha * rho : NNReal) : Real) / 128) /
        (((alpha * rho : NNReal) : Real) / 128) ≤
      (Cpack : Real) * Module.finrank Real E + 1) :
    (G.filter (fun W => ∃ (U : Tube delta E),
        U.carrier ⊆ Metric.closedBall (0 : E) 1 ∧
        U.toConvexSpaceBody ≤ (W.rescale rho).toConvexSpaceBody ∧
        U.toConvexSpaceBody ≤ V.toConvexSpaceBody)).card ≤
      2 * (Cpack * Module.finrank Real E + 1) ^
        (2 * Module.finrank Real E) := by
  classical
  set n : Nat := Module.finrank Real E with hn_def
  have hn_pos : 0 < n := Module.finrank_pos
  set r : Real := (rho : Real) with hr_def
  have hr_pos : 0 < r := by rw [hr_def]; exact_mod_cast hrho
  have hrα_pos : 0 < ((alpha * rho : NNReal) : Real) := by
    exact_mod_cast mul_pos halpha hrho
  have hrα_le : ((alpha * rho : NNReal) : Real) ≤ r := by
    rw [NNReal.coe_mul, hr_def]
    exact mul_le_of_le_one_left (by exact_mod_cast hrho.le) (by exact_mod_cast halpha1)
  set F := G.filter (fun W => ∃ (U : Tube delta E),
      U.carrier ⊆ Metric.closedBall (0 : E) 1 ∧
      U.toConvexSpaceBody ≤ (W.rescale rho).toConvexSpaceBody ∧
      U.toConvexSpaceBody ≤ V.toConvexSpaceBody) with hF
  have hFG : ∀ W ∈ F, W ∈ G := fun W hW => (Finset.mem_filter.mp hW).1
  have hsep_endpoints : ∀ W ∈ F, ∀ W' ∈ F, W ≠ W' →
      ((alpha * rho : NNReal) : Real) / 32 ≤ ‖W.x - W'.x‖ + ‖W.y - W'.y‖ :=
    fun W hW W' hW' hne => hsep W (hFG W hW) W' (hFG W' hW') hne
  have hloc24 : ∀ W ∈ F,
      (‖W.x - V.x‖ ≤ 24 * r ∧ ‖W.y - V.y‖ ≤ 24 * r) ∨
      (‖W.x - V.y‖ ≤ 24 * r ∧ ‖W.y - V.x‖ ≤ 24 * r) := by
    intro W hW
    obtain ⟨_, U, _hU1, hUW, hUV⟩ := Finset.mem_filter.mp hW
    have hWr : W.toConvexSpaceBody ≤ (W.rescale rho).toConvexSpaceBody := by
      simpa only [Tube.toConvexSpaceBody_rescale_self] using
        (Tube.rescale_le_rescale_of_radius_le W hrα_le)
    have hW0 : W.toConvexSpaceBody ≤
        (U.rescale (4 * rho)).toConvexSpaceBody := by
      exact hWr.trans (Tube.rescale_le_of_le U (W.rescale rho) hUW)
    have hV0 : V.toConvexSpaceBody ≤
        (U.rescale (4 * rho)).toConvexSpaceBody :=
      Tube.rescale_le_of_le U V hUV
    have hWend := Tube.endpoints_close_of_body_le W
      (U.rescale (4 * rho)) hW0
    have hVend := Tube.endpoints_close_of_body_le V
      (U.rescale (4 * rho)) hV0
    have hVscale : ((4 * rho : NNReal) : Real) = 4 * r := by
      rw [hr_def, NNReal.coe_mul]; norm_num
    simp only [Tube.rescale, Tube.mk'_x, Tube.mk'_y, hVscale] at hWend
    simp only [Tube.rescale, Tube.mk'_x, Tube.mk'_y, hVscale] at hVend
    ring_nf at hWend hVend
    rcases hWend with ⟨hWx, hWy⟩ | ⟨hWx, hWy⟩ <;>
      rcases hVend with ⟨hVx, hVy⟩ | ⟨hVx, hVy⟩
    · left; refine ⟨?_, ?_⟩
      · have ht := norm_sub_le_norm_sub_add_norm_sub W.x U.x V.x
        have hu : ‖U.x - V.x‖ ≤ 12 * r := by simpa [norm_sub_rev, mul_comm] using hVx
        have hw : ‖W.x - U.x‖ ≤ 12 * r := by simpa [mul_comm] using hWx
        linarith [ht, hw, hu]
      · have ht := norm_sub_le_norm_sub_add_norm_sub W.y U.y V.y
        have hu : ‖U.y - V.y‖ ≤ 12 * r := by simpa [norm_sub_rev, mul_comm] using hVy
        have hw : ‖W.y - U.y‖ ≤ 12 * r := by simpa [mul_comm] using hWy
        linarith [ht, hw, hu]
    · right; refine ⟨?_, ?_⟩
      · have ht := norm_sub_le_norm_sub_add_norm_sub W.x U.x V.y
        have hu : ‖U.x - V.y‖ ≤ 12 * r := by simpa [norm_sub_rev, mul_comm] using hVy
        have hw : ‖W.x - U.x‖ ≤ 12 * r := by simpa [mul_comm] using hWx
        linarith [ht, hw, hu]
      · have ht := norm_sub_le_norm_sub_add_norm_sub W.y U.y V.x
        have hu : ‖U.y - V.x‖ ≤ 12 * r := by simpa [norm_sub_rev, mul_comm] using hVx
        have hw : ‖W.y - U.y‖ ≤ 12 * r := by simpa [mul_comm] using hWy
        linarith [ht, hw, hu]
    · right; refine ⟨?_, ?_⟩
      · have ht := norm_sub_le_norm_sub_add_norm_sub W.x U.y V.y
        have hu : ‖U.y - V.y‖ ≤ 12 * r := by simpa [norm_sub_rev, mul_comm] using hVy
        have hw : ‖W.x - U.y‖ ≤ 12 * r := by simpa [mul_comm] using hWx
        linarith [ht, hw, hu]
      · have ht := norm_sub_le_norm_sub_add_norm_sub W.y U.x V.x
        have hu : ‖U.x - V.x‖ ≤ 12 * r := by simpa [norm_sub_rev, mul_comm] using hVx
        have hw : ‖W.y - U.x‖ ≤ 12 * r := by simpa [mul_comm] using hWy
        linarith [ht, hw, hu]
    · left; refine ⟨?_, ?_⟩
      · have ht := norm_sub_le_norm_sub_add_norm_sub W.x U.y V.x
        have hu : ‖U.y - V.x‖ ≤ 12 * r := by simpa [norm_sub_rev, mul_comm] using hVx
        have hw : ‖W.x - U.y‖ ≤ 12 * r := by simpa [mul_comm] using hWx
        linarith [ht, hw, hu]
      · have ht := norm_sub_le_norm_sub_add_norm_sub W.y U.x V.y
        have hu : ‖U.x - V.y‖ ≤ 12 * r := by simpa [norm_sub_rev, mul_comm] using hVy
        have hw : ‖W.y - U.x‖ ≤ 12 * r := by simpa [mul_comm] using hWy
        linarith [ht, hw, hu]
  set Fp : Finset (Tube (alpha * rho) E) :=
    F.filter (fun W => ‖W.x - V.x‖ ≤ 24 * r ∧ ‖W.y - V.y‖ ≤ 24 * r) with hFp
  set Fm : Finset (Tube (alpha * rho) E) := F \ Fp with hFm
  have hsep_pos : (0 : Real) < ((alpha * rho : NNReal) : Real) / 32 := by positivity
  have hratio : (24 * r + (((alpha * rho : NNReal) : Real) / 32) / 4) /
      ((((alpha * rho : NNReal) : Real) / 32) / 4) ≤
      (Cpack : Real) * n + 1 := by
    convert hCpack using 1 <;> ring
  have hpart_bound : ∀ (Gp : Finset (Tube (alpha * rho) E)) (cx cy : E),
      (∀ W ∈ Gp, W ∈ F) →
      (∀ W ∈ Gp, ‖W.x - cx‖ ≤ 24 * r) →
      (∀ W ∈ Gp, ‖W.y - cy‖ ≤ 24 * r) →
      Gp.card ≤ (Cpack * n + 1) ^ (2 * n) := by
    intro Gp cx cy hGF hGx hGy
    have hsepG : ∀ a ∈ Gp, ∀ b ∈ Gp, a ≠ b →
        ((alpha * rho : NNReal) : Real) / 32 ≤ ‖a.x - b.x‖ + ‖a.y - b.y‖ :=
      fun a ha b hb hab => hsep_endpoints a (hGF a ha) b (hGF b hb) hab
    have hpack := Tube.card_le_of_L1_separated_in_box (E := E) Gp
      (fun W => W.x) (fun W => W.y) cx cy hsep_pos hsepG hGx hGy
    have hbase : 0 ≤ (24 * r + (((alpha * rho : NNReal) : Real) / 32) / 4) /
        ((((alpha * rho : NNReal) : Real) / 32) / 4) := by positivity
    have hmono := pow_le_pow_left₀ hbase hratio (2 * n)
    have hcardR : (Gp.card : Real) ≤ ((Cpack : Real) * n + 1) ^ (2 * n) :=
      le_trans hpack hmono
    exact_mod_cast hcardR
  have hFpF : ∀ W ∈ Fp, W ∈ F := fun W hW => (Finset.mem_filter.mp hW).1
  have hFpx : ∀ W ∈ Fp, ‖W.x - V.x‖ ≤ 24 * r :=
    fun W hW => (Finset.mem_filter.mp hW).2.1
  have hFpy : ∀ W ∈ Fp, ‖W.y - V.y‖ ≤ 24 * r :=
    fun W hW => (Finset.mem_filter.mp hW).2.2
  have hFp_card := hpart_bound Fp V.x V.y hFpF hFpx hFpy
  have hFmF : ∀ W ∈ Fm, W ∈ F := fun W hW => (Finset.mem_sdiff.mp hW).1
  have hFmx : ∀ W ∈ Fm, ‖W.x - V.y‖ ≤ 24 * r := by
    intro W hW
    obtain ⟨hWF, hWnp⟩ := Finset.mem_sdiff.mp hW
    rcases hloc24 W hWF with hpos | hneg
    · exact absurd (Finset.mem_filter.mpr ⟨hWF, hpos⟩) hWnp
    · exact hneg.1
  have hFmy : ∀ W ∈ Fm, ‖W.y - V.x‖ ≤ 24 * r := by
    intro W hW
    obtain ⟨hWF, hWnp⟩ := Finset.mem_sdiff.mp hW
    rcases hloc24 W hWF with hpos | hneg
    · exact absurd (Finset.mem_filter.mpr ⟨hWF, hpos⟩) hWnp
    · exact hneg.2
  have hFm_card := hpart_bound Fm V.y V.x hFmF hFmx hFmy
  have hFsplit : F.card ≤ Fp.card + Fm.card := by
    have hFeq : F.card = (Fp ∪ Fm).card := by
      congr 1
      rw [hFm, Finset.union_sdiff_of_subset (Finset.filter_subset _ _)]
    rw [hFeq]; exact Finset.card_union_le _ _
  change F.card ≤ 2 * (Cpack * n + 1) ^ (2 * n)
  calc F.card ≤ Fp.card + Fm.card := hFsplit
    _ ≤ (Cpack * n + 1) ^ (2 * n) + (Cpack * n + 1) ^ (2 * n) :=
      Nat.add_le_add hFp_card hFm_card
    _ = 2 * (Cpack * n + 1) ^ (2 * n) := by ring

end
end Kakeya.ml1Boot.TrialRestartW94
