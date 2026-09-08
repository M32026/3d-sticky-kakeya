module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.CentringShadingW102

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody
open scoped ENNReal NNReal

namespace Kakeya.ml1Boot.TrialRestartW94

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

universe uE uI
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

theorem source_centring_maxDensity_w102 (hdim : Module.finrank Real E = 3)
    {delta : NNReal} (hdsmall : delta <= 1 / 200)
    {iota : Type uI} (F G : Finset iota) (T : iota -> Tube delta E)
    (W : iota -> Tube (delta / 2) E) (hGF : G ⊆ F)
    (hcov : ∀ j ∈ G, (fun x : E => (1 / 8 : Real) • x) '' (T j).carrier ⊆
      (W j).carrier) :
    maxDensity G (fun j => (W j).toConvexSpaceBody) <=
      384 * maxDensity F (fun i => (T i).toConvexSpaceBody) := by
  classical
  let N : iota -> ConvexSpaceBody E := fun i =>
    (T i).toConvexSpaceBody.homothety 0 (1 / 8 : Real)
  have hNcar : ∀ i, (N i).carrier =
      (fun x : E => (1 / 8 : Real) • x) '' (T i).carrier := by
    intro i
    change AffineMap.homothety (0 : E) (1 / 8 : Real) '' (T i).carrier = _
    apply Set.image_congr
    intro x hx
    simp [AffineMap.homothety_apply]
  have hNvol : ∀ i, volume (N i).carrier =
      (1 / 512 : ENNReal) * volume (T i).carrier := by
    intro i
    rw [hNcar, volume_source_centring_image_w102 hdim]
  have hvol : ∀ i, volume (W i).carrier <= 384 * volume (N i).carrier := by
    intro i
    rw [hNvol, ← mul_assoc]
    exact half_radius_carrier_volume_w102 hdim hdsmall (T i) (W i)
  refine Kakeya.maxDensity_le_of_forall_sum_le ?_
  intro K
  have hstep : G.filter (fun i => (W i).toConvexSpaceBody <= K) ⊆
      F.filter (fun i => N i <= K) := by
    intro i hi
    obtain ⟨hiG, hiK⟩ := Finset.mem_filter.mp hi
    refine Finset.mem_filter.mpr ⟨hGF hiG, ?_⟩
    rw [← SetLike.coe_subset_coe] at hiK ⊢
    change (N i).carrier ⊆ K.carrier
    rw [hNcar]
    exact (hcov i hiG).trans hiK
  calc
    _ <= ∑ i ∈ G.filter (fun i => (W i).toConvexSpaceBody <= K),
        384 * volume (N i).carrier := Finset.sum_le_sum fun i hi => hvol i
    _ = 384 * ∑ i ∈ G.filter (fun i => (W i).toConvexSpaceBody <= K),
        volume (N i).carrier := by rw [Finset.mul_sum]
    _ <= 384 * ∑ i ∈ F.filter (fun i => N i <= K), volume (N i).carrier :=
      mul_le_mul' le_rfl (Finset.sum_le_sum_of_subset hstep)
    _ <= 384 * (maxDensity F N * volume K.carrier) :=
      mul_le_mul' le_rfl (Kakeya.sum_volume_le_maxDensity_mul_volume F N K)
    _ = _ := by
      rw [show maxDensity F N = maxDensity F (fun i => (T i).toConvexSpaceBody) from
        Kakeya.maxDensity_homothety F _ 0 (by norm_num), mul_assoc]

end
end Kakeya.ml1Boot.TrialRestartW94
