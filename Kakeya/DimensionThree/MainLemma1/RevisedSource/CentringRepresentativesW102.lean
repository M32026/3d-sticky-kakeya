module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.CentringCoverGeometryW102

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

theorem source_line_of_scaled_carrier_subset_w102
    {delta : NNReal} (T : Tube delta E) (W : Tube (delta / 2) E)
    (hcov : (fun x : E => (1 / 8 : Real) • x) '' T.carrier ⊆ W.carrier) :
    liesInFiveDeltaLineTubeW94 T ((8 : Real) • W.midpoint) W.direction := by
  intro x hx
  obtain ⟨t, g, ht, hg, heq⟩ := W.exists_decomp_of_mem_carrier (hcov ⟨x, hx, rfl⟩)
  refine ⟨8 * t, ?_⟩
  have heq' : x = (8 : Real) • (W.midpoint + t • W.direction + g) := by
    calc
      x = (8 : Real) • ((1 / 8 : Real) • x) := by module
      _ = _ := congrArg (fun z : E => (8 : Real) • z) heq
  have heq'' : x - ((8 : Real) • W.midpoint + (8 * t) • W.direction) =
      (8 : Real) • g := by rw [heq']; module
  rw [dist_eq_norm, heq'', norm_smul, Real.norm_of_nonneg (by norm_num)]
  have hd : (0 : Real) <= delta := delta.coe_nonneg
  simp only [NNReal.coe_div, NNReal.coe_ofNat] at hg
  linarith only [hg, hd]

theorem exists_source_centred_representatives_w102
    (hdim : Module.finrank Real E = 3)
    {delta : NNReal} (hd : 0 < delta) (hdsmall : delta <= 1 / 200)
    {iota : Type uI} [DecidableEq iota]
    (F : Finset iota) (T : iota -> Tube delta E) (Cline : NNReal)
    (hF : F.Nonempty)
    (hball : ∀ i ∈ F, (T i).carrier ⊆ Metric.closedBall 0 1)
    (hline : lineEssentiallyDistinctW94 F T Cline) :
    ∃ (G : Finset iota) (parent : iota -> iota) (W : iota -> Tube (delta / 2) E),
      G.Nonempty ∧ G ⊆ F ∧ F.image parent = G ∧
      (∀ j ∈ G, parent j = j) ∧
      (∀ j ∈ G, (W j).carrier ⊆ Metric.closedBall 0 (3 / 4 : Real)) ∧
      (∀ j ∈ G, centredTubeW94 (W j)) ∧
      lineEssentiallyDistinctW94 G W (2 * (223 : NNReal) ^ (6 : Nat)) ∧
      (∀ i ∈ F, (fun x : E => (1 / 8 : Real) • x) '' (T i).carrier ⊆
        (W (parent i)).carrier) ∧
      (∀ j ∈ G, ((completeFibreW94 F parent j).card : NNReal) <= Cline) := by
  classical
  obtain ⟨H, pi, hpi, hsurj, hcov, hcen, hball', hpack⟩ :=
    exists_small_ball_centred_cover_w102 hdim hd hdsmall F T hball
  obtain ⟨i0, hi0⟩ := hF
  have hchoice : ∀ U : Tube (delta / 2) E, ∃ i : iota,
      U ∈ H -> i ∈ F ∧ pi i = U := by
    intro U
    by_cases hU : U ∈ H
    · obtain ⟨i, hi, heq⟩ := hsurj U hU
      exact ⟨i, fun _ => ⟨hi, heq⟩⟩
    · exact ⟨i0, fun h => (hU h).elim⟩
  choose rep hrep using hchoice
  let G := H.image rep
  let parent : iota -> iota := fun i => rep (pi i)
  have hG : ∀ j ∈ G, j ∈ F ∧ rep (pi j) = j ∧ pi j ∈ H := by
    intro j hj
    obtain ⟨U, hU, rfl⟩ := Finset.mem_image.mp hj
    have h := hrep U hU
    exact ⟨h.1, by rw [h.2], by rw [h.2]; exact hU⟩
  have himage : F.image parent = G := by
    ext j
    constructor
    · intro hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      exact Finset.mem_image_of_mem rep (hpi i hi)
    · intro hj
      obtain ⟨U, hU, rfl⟩ := Finset.mem_image.mp hj
      obtain ⟨i, hi, heq⟩ := hsurj U hU
      exact Finset.mem_image.mpr ⟨i, hi, by dsimp [parent]; rw [heq]⟩
  have hparPi : ∀ i ∈ F, pi (parent i) = pi i := by
    intro i hi
    exact (hrep (pi i) (hpi i hi)).2
  refine ⟨G, parent, pi, ?_, fun j hj => (hG j hj).1, himage,
    fun j hj => (hG j hj).2.1, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← himage]
    exact ⟨parent i0, Finset.mem_image_of_mem _ hi0⟩
  · intro j hj
    exact hball' (pi j) (hG j hj).2.2
  · intro j hj
    simpa only [centredTubeW94, Tube.IsCentred, Tube.center, midpoint_eq_smul_add,
      Tube.midpoint, invOf_eq_inv, one_div] using hcen (pi j) (hG j hj).2.2
  · intro o v hv
    let Q := G.filter (fun j => liesInFiveDeltaLineTubeW94 (pi j) o v)
    have hQinj : Set.InjOn pi Q := by
      intro i hi j hj heq
      have hiG := (Finset.mem_filter.mp hi).1
      have hjG := (Finset.mem_filter.mp hj).1
      calc
        i = rep (pi i) := ((hG i hiG).2.1).symm
        _ = rep (pi j) := congrArg rep heq
        _ = j := (hG j hjG).2.1
    have hQsub : Q.image pi ⊆ H.filter (fun U => U.carrier ⊆
        Metric.cthickening (5 * ((delta / 2 : NNReal) : Real))
          (Set.range fun t : Real => o + t • v)) := by
      intro U hU
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hU
      obtain ⟨hjG, hjline⟩ := Finset.mem_filter.mp hj
      refine Finset.mem_filter.mpr ⟨(hG j hjG).2.2, ?_⟩
      intro x hx
      obtain ⟨t, ht⟩ := hjline x hx
      exact Metric.mem_cthickening_of_dist_le x (o + t • v) _ _ ⟨t, rfl⟩ ht
    have hcard : Q.card <= (H.filter (fun U => U.carrier ⊆
        Metric.cthickening (5 * ((delta / 2 : NNReal) : Real))
          (Set.range fun t : Real => o + t • v))).card := by
      rw [← Finset.card_image_of_injOn hQinj]
      exact Finset.card_le_card hQsub
    have hreal := (Nat.cast_le (α := Real).mpr hcard).trans (hpack o v hv)
    exact_mod_cast hreal
  · intro i hi
    rw [hparPi i hi]
    exact hcov i hi
  · intro j hj
    have hsub : completeFibreW94 F parent j ⊆ F.filter (fun i =>
        liesInFiveDeltaLineTubeW94 (T i) ((8 : Real) • (pi j).midpoint)
          (pi j).direction) := by
      intro i hi
      obtain ⟨hiF, hij⟩ := Finset.mem_filter.mp hi
      refine Finset.mem_filter.mpr ⟨hiF, ?_⟩
      apply source_line_of_scaled_carrier_subset_w102
      rw [← hij, hparPi i hiF]
      exact hcov i hiF
    exact (Nat.cast_le (α := NNReal).mpr (Finset.card_le_card hsub)).trans
      (hline _ _ (pi j).norm_direction)

end
end Kakeya.ml1Boot.TrialRestartW94
