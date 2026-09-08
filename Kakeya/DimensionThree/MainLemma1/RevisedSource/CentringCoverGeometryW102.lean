module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceConstructionDefinitionsW97
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.CentringGeometryPrefixW112
public import Kakeya.Tube.CylinderApprox

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

open Kakeya.VeryNotSticky

theorem exists_small_ball_centred_cover_w102
    (hdim : Module.finrank Real E = 3)
    {delta : NNReal} (hd : 0 < delta) (hdsmall : delta <= 1 / 200)
    {iota : Type uI} (F : Finset iota) (T : iota -> Tube delta E)
    (hball : ∀ i ∈ F, (T i).carrier ⊆ Metric.closedBall 0 1) :
    ∃ (H : Finset (Tube (delta / 2) E)) (pi : iota -> Tube (delta / 2) E),
      (∀ i ∈ F, pi i ∈ H) ∧
      (∀ W ∈ H, ∃ i ∈ F, pi i = W) ∧
      (∀ i ∈ F, (fun x : E => (1 / 8 : Real) • x) '' (T i).carrier ⊆ (pi i).carrier) ∧
      (∀ W ∈ H, W.IsCentred) ∧
      (∀ W ∈ H, W.carrier ⊆ Metric.closedBall 0 (3 / 4 : Real)) ∧
      (∀ o v : E, ‖v‖ = 1 ->
        ((H.filter (fun W => W.carrier ⊆ Metric.cthickening
          (5 * ((delta / 2 : NNReal) : Real))
            (Set.range (fun t : Real => o + t • v)))).card : Real) <=
          2 * (223 : Real) ^ (6 : Nat)) := by
  classical
  let rho : NNReal := delta / 2
  have hrho : 0 < rho := by dsimp [rho]; positivity
  have hdR : (0 : Real) < delta := hd
  have hdRsmall : (delta : Real) <= 1 / 200 := by exact_mod_cast hdsmall
  have hrhoR : (rho : Real) = (delta : Real) / 2 := by simp [rho]
  let X : iota -> Set E := fun i => centringDilate '' (T i).carrier
  let p : iota -> E := fun i => centringDilate (T i).midpoint
  let d : iota -> E := fun i => (T i).direction
  have hXline : ∀ i, X i ⊆ Metric.cthickening ((rho : Real) / 4)
      (Set.range fun t : Real => p i + t • d i) := by
    intro i
    have h := centringDilate_image_subset_lineNbhd (T i)
    simpa only [X, p, d, hrhoR,
      show (delta : Real) / 2 / 4 = (delta : Real) / 8 by ring] using h
  have hXnorm : ∀ i ∈ F, ∀ z ∈ X i, ‖z‖ <= 1 / 8 := by
    intro i hi z hz
    obtain ⟨x, hx, rfl⟩ := hz
    have hxnorm : ‖x‖ <= 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hball i hi hx
    dsimp [centringDilate]
    rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
    linarith
  have hXne : ∀ i, (X i).Nonempty := fun i =>
    ⟨centringDilate (T i).midpoint, (T i).midpoint,
      Tube.midpoint_mem_carrier hd (T i), rfl⟩
  have hfoot : ∀ i, inner Real (Tube.lineFoot (p i) (d i)) (d i) = 0 :=
    fun i => inner_lineFoot_eq_zero _ _ (T i).norm_direction
  have hfootnorm : ∀ i ∈ F, ‖Tube.lineFoot (p i) (d i)‖ <= 1 / 6 := by
    intro i hi
    obtain ⟨z, hz⟩ := hXne i
    have h := norm_lineFoot_le (T i).norm_direction
      (show 0 <= (rho : Real) / 4 by positivity) (hXline i hz) (hXnorm i hi z hz)
    rw [hrhoR] at h
    linarith
  obtain ⟨H0, hcen, hmid, hsep, hcover⟩ :=
    Tube.exists_centred_net (E := E) rho (1 / 6) (ε := (rho : Real) / 4) (by positivity)
  have hchoice : ∀ i, ∃ W : Tube rho E, i ∈ F ->
      W ∈ H0 ∧ ‖Tube.lineFoot (p i) (d i) - W.midpoint‖ <= (rho : Real) / 2 ∧
        ‖d i - W.direction‖ <= (rho : Real) / 2 := by
    intro i
    by_cases hi : i ∈ F
    · obtain ⟨W, hW, hp, hd'⟩ := hcover (Tube.lineFoot (p i) (d i)) (d i)
        (hfoot i) (T i).norm_direction (hfootnorm i hi)
      refine ⟨W, fun _ => ⟨hW, ?_, ?_⟩⟩ <;> linarith
    · exact ⟨Tube.ofMidpointDirection rho 0 (T i).direction (T i).norm_direction,
        fun h => (hi h).elim⟩
  choose pi hpi using hchoice
  let H := F.image pi
  have hHsub : H ⊆ H0 := by
    intro W hW
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hW
    exact (hpi i hi).1
  refine ⟨H, pi, fun i hi => Finset.mem_image_of_mem _ hi, ?_, ?_,
    fun W hW => hcen W (hHsub hW), ?_, ?_⟩
  · intro W hW
    exact Finset.mem_image.mp hW
  · intro i hi z hz
    have hz : z ∈ X i := by simpa only [X, centringDilate, one_div] using hz
    obtain ⟨_, hp, hd'⟩ := hpi i hi
    let f := Tube.lineFoot (p i) (d i)
    have hzline : z ∈ Metric.cthickening ((rho : Real) / 4)
        (Set.range fun t : Real => f + t • d i) := by
      rw [range_line_lineFoot]
      exact hXline i hz
    let t : Real := inner Real (z - f) (d i)
    have herror : ‖z - (f + t • d i)‖ <= (rho : Real) / 4 := by
      rw [show t = inner Real (z - f) (d i) from rfl,
        Tube.norm_sub_foot_eq f (d i) z (T i).norm_direction]
      exact (Tube.mem_cthickening_line_iff (T i).norm_direction (by positivity)).mp hzline
    have htnorm : |t| <= 1 / 6 := by
      have heq : inner Real (f + t • d i) (d i) = t := by
        rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
          (T i).norm_direction, hfoot i]
        ring
      have htle : |t| <= ‖f + t • d i‖ := by
        calc
          _ = |inner Real (f + t • d i) (d i)| := by rw [heq]
          _ <= ‖f + t • d i‖ * ‖d i‖ := abs_real_inner_le_norm _ _
          _ = _ := by rw [(T i).norm_direction, mul_one]
      have hn := norm_sub_le z (z - (f + t • d i))
      rw [sub_sub_cancel] at hn
      have hzNorm := hXnorm i hi z hz
      rw [hrhoR] at herror
      linarith
    refine (pi i).mem_carrier_of_dist_le
      ((pi i).midpoint_add_smul_mem_segment (htnorm.trans (by norm_num))) ?_
    rw [dist_eq_norm]
    have heq : z - ((pi i).midpoint + t • (pi i).direction) =
        (z - (f + t • d i)) + ((f - (pi i).midpoint) + t • (d i - (pi i).direction)) := by
      module
    rw [heq]
    have hm := mul_le_mul htnorm hd' (norm_nonneg _) (by norm_num : (0 : Real) <= 1 / 6)
    calc
      _ <= ‖z - (f + t • d i)‖ +
          (‖f - (pi i).midpoint‖ + ‖t • (d i - (pi i).direction)‖) :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
      _ = ‖z - (f + t • d i)‖ +
          (‖f - (pi i).midpoint‖ + |t| * ‖d i - (pi i).direction‖) := by
        rw [norm_smul, Real.norm_eq_abs]
      _ <= (rho : Real) := by linarith
  · intro W hW z hz
    obtain ⟨t, g, ht, hg, rfl⟩ := W.exists_decomp_of_mem_carrier hz
    rw [Metric.mem_closedBall, dist_zero_right]
    have hm := hmid W (hHsub hW)
    have hn := (norm_add_le (W.midpoint + t • W.direction) g).trans
      (add_le_add (norm_add_le W.midpoint (t • W.direction)) le_rfl)
    have hs : ‖t • W.direction‖ = |t| := by
      rw [norm_smul, Real.norm_eq_abs, W.norm_direction, mul_one]
    rw [hs] at hn
    rw [hrhoR] at hg
    linarith
  · intro o v hv
    have h := Tube.card_filter_line_le_of_centred_sep H hrho (fun W => W)
      (fun W hW => hcen W (hHsub hW)) (by norm_num : (0 : Real) <= 1 / 6)
      (fun W hW => hmid W (hHsub hW)) (m := 4) (by norm_num)
      (fun W hW W' hW' hne => hsep W (hHsub hW) W' (hHsub hW') hne)
      (K := 5) (by norm_num) o v hv
    refine h.trans ?_
    norm_num [Tube.linePackingConstant, hdim]

end
end Kakeya.ml1Boot.TrialRestartW94
