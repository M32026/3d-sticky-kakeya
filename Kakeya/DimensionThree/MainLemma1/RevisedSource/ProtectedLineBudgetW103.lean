module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceCentringReductionProofW102
public import Kakeya.Tube.EDPacking.DirectionCapCount

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology Metric
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

theorem eventually_source_line_budget_of_protected_ED_w103
    (hdim : Module.finrank Real E = 3) :
    ∃ Cline : NNReal, 1 <= Cline ∧
      ∀ᶠ delta : NNReal in 𝓝[>] 0,
        ∀ {iota : Type uI} (F : Finset iota) (T : iota -> Tube delta E),
          (∀ i ∈ F, (T i).carrier ⊆ Metric.closedBall 0 1) ->
          (F : Set iota).Pairwise
            (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) ->
          lineEssentiallyDistinctW94 F T Cline := by
  classical
  obtain ⟨D, d0, hD, hd0, hd01, hcount⟩ :=
    Kakeya.exists_ED_directionCap_card_bound (E := E)
      (by rw [hdim]; norm_num) (A := 16) (by norm_num)
  let M : Real := 50 * Real.pi
  have hM : 0 < M := by dsimp [M]; positivity
  let Cline : NNReal := ⟨max 1 ((D : Real) * M), le_trans (by norm_num) (le_max_left _ _)⟩
  refine ⟨Cline, ?_, ?_⟩
  · exact_mod_cast (le_max_left 1 ((D : Real) * M))
  · filter_upwards [eventually_le_nhdsGT (c := (⟨d0, hd0.le⟩ : NNReal)) hd0,
      self_mem_nhdsWithin] with delta hdsmall hd
    intro iota F T hball hED o v hv
    have hdR : (0 : Real) < delta := hd
    have hdRsmall : (delta : Real) <= d0 := hdsmall
    let H := F.filter (fun i => liesInFiveDeltaLineTubeW94 (T i) o v)
    let K : Set E := Metric.closedBall 0 1 ∩ Metric.cthickening
      (5 * (delta : Real)) (Set.range fun t : Real => o + t • v)
    let f := Tube.lineFoot o v
    have hf : inner Real f v = 0 := inner_lineFoot_eq_zero o v hv
    have hHsub : H ⊆ F := Finset.filter_subset _ _
    have hline : ∀ i ∈ H, (T i).carrier ⊆ Metric.cthickening
        (5 * (delta : Real)) (Set.range fun t : Real => o + t • v) := by
      intro i hi x hx
      obtain ⟨t, ht⟩ := (Finset.mem_filter.mp hi).2 x hx
      exact Metric.mem_cthickening_of_dist_le x (o + t • v) _ _ ⟨t, rfl⟩ ht
    have hKsub : K ⊆ cylinder f v (-1) 1 (5 * (delta : Real)) := by
      intro x hx
      have hnorm : ‖x‖ <= 1 := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hx.1
      have hinner : inner Real (x - f) v = inner Real x v := by
        rw [inner_sub_left, hf, sub_zero]
      have ha : |inner Real (x - f) v| <= 1 := by
        rw [hinner]
        calc
          _ <= ‖x‖ * ‖v‖ := abs_real_inner_le_norm _ _
          _ <= 1 := by rw [hv, mul_one]; exact hnorm
      refine ⟨abs_le.mp ha, ?_⟩
      have hxline : x ∈ Metric.cthickening (5 * (delta : Real))
          (Set.range fun t : Real => f + t • v) := by
        rw [range_line_lineFoot]
        exact hx.2
      exact (Tube.mem_cthickening_line_iff hv (by positivity)).mp hxline
    have hKvol : volume K <= ENNReal.ofReal M *
        (delta : ENNReal) ^ (Module.finrank Real E - 1) := by
      refine (measure_mono hKsub).trans_eq ?_
      rw [volume_cylinder_three_w102 hdim hv]
      have h5 : ENNReal.ofReal (5 * (delta : Real)) = 5 * (delta : ENNReal) := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_coe_nnreal]
        norm_num
      have h50 : ENNReal.ofReal M = 50 * ENNReal.ofReal Real.pi := by
        dsimp only [M]
        rw [ENNReal.ofReal_mul (by norm_num)]
        norm_num
      rw [h5, h50, hdim]
      norm_num
      ring
    have hKclosed : IsClosed K :=
      (isClosed_closedBall : IsClosed (Metric.closedBall (0 : E) 1)).inter Metric.isClosed_cthickening
    have hKcompact : IsCompact K := (isCompact_closedBall (0 : E) 1).of_isClosed_subset
      hKclosed Set.inter_subset_left
    have hcap : ∀ i ∈ H,
        min ‖(T i).direction - v‖ ‖(T i).direction + v‖ <= 16 * (delta : Real) := by
      intro i hi
      have hcore : ∀ z ∈ segment Real (T i).x (T i).y,
          Tube.lineDist o v z <= 4 * (delta : Real) := by
        intro z hz
        have h := Tube.lineDist_le_of_carrier_subset (T i) hv
          (show (delta : Real) <= 5 * delta by linarith only [hdR]) (hline i hi) hz
        linarith only [h]
      obtain ⟨sgn, hsgn, hdir⟩ := Tube.exists_sign_norm_direction_sub_le (T i) hv
        (hcore _ (left_mem_segment Real _ _)) (hcore _ (right_mem_segment Real _ _))
      rw [show (4 : Real) * (4 * delta) = 16 * delta by ring] at hdir
      rcases hsgn with rfl | rfl
      · exact (min_le_left _ _).trans (by simpa only [one_smul] using hdir)
      · exact (min_le_right _ _).trans
          (by simpa only [neg_smul, one_smul, sub_neg_eq_add] using hdir)
    have hbad : ∀ i ∈ H, ENNReal.ofReal (1 : Real) * volume (T i).carrier <=
        volume ((T i).carrier ∩ K) := by
      intro i hi
      have hsub : (T i).carrier ⊆ K := fun x hx => ⟨hball i (hHsub hi) hx, hline i hi hx⟩
      rw [Set.inter_eq_self_of_subset_left hsub, ENNReal.ofReal_one, one_mul]
    have hreal := hcount hd hdRsmall H T
      (hED.mono (Finset.coe_subset.mpr hHsub)) hv hcap
      hKclosed.measurableSet hKcompact hM hKvol (by norm_num : (0 : Real) < 1) hbad
    have hdcount : (H.card : Real) <= (D : Real) * M := by
      simpa only [div_one] using hreal
    have hle : (H.card : Real) <= max 1 ((D : Real) * M) :=
      hdcount.trans (le_max_right _ _)
    exact_mod_cast hle

end
end Kakeya.ml1Boot.TrialRestartW94
