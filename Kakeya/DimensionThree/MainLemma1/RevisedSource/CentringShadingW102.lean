module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.CentringRepresentativesW102
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.CentringVolumeW102
public import Kakeya.Homothety

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

theorem volume_source_centring_image_w102 (hdim : Module.finrank Real E = 3)
    (A : Set E) : volume ((fun x : E => (1 / 8 : Real) • x) '' A) =
      (1 / 512 : ENNReal) * volume A := by
  rw [Kakeya.VeryNotSticky.volume_smul_image, hdim]
  rw [show |(1 / 8 : Real) ^ 3| = 1 / 512 by norm_num,
    ENNReal.ofReal_div_of_pos (by norm_num)]
  norm_num

def sourceCentringShadingW102 {delta : NNReal} {iota : Type uI} [DecidableEq iota]
    (F : Finset iota) (Y : iota -> ShadedTube delta E)
    (parent : iota -> iota) (W : iota -> Tube (delta / 2) E)
    (hcov : ∀ i ∈ F, (fun x : E => (1 / 8 : Real) • x) '' (Y i).carrier ⊆
      (W (parent i)).carrier) (j : iota) : ShadedTube (delta / 2) E where
  toTube := W j
  shade := ⋃ i ∈ completeFibreW94 F parent j,
    (fun x : E => (1 / 8 : Real) • x) '' (Y i).shade
  measurableSet_shade := by
    apply Finset.measurableSet_biUnion
    intro i hi
    have hL : (fun x : E => (1 / 8 : Real) • x) =
        AffineMap.homothety (0 : E) (1 / 8 : Real) := by
      ext x
      simp [AffineMap.homothety_apply]
    rw [hL]
    exact (Kakeya.measurableEmbedding_homothety (0 : E)
      (by norm_num : (1 / 8 : Real) ≠ 0)).measurableSet_image' (Y i).measurableSet_shade
  shade_subset := by
    intro x hx
    obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨hiF, hij⟩ := Finset.mem_filter.mp hi
    rw [← hij]
    exact hcov i hiF (Set.image_mono (Y i).shade_subset hx)

theorem fibre_union_measure_bounds_w102
    {iota : Type uI} [DecidableEq iota] (F G : Finset iota)
    (parent : iota -> iota) (A : iota -> Set E) (B : ENNReal)
    (hmap : ∀ i ∈ F, parent i ∈ G)
    (hcard : ∀ j ∈ G, ((completeFibreW94 F parent j).card : ENNReal) <= B) :
    (∑ j ∈ G, volume (⋃ i ∈ completeFibreW94 F parent j, A i)) <=
      ∑ i ∈ F, volume (A i) ∧
    (∑ i ∈ F, volume (A i)) <=
      B * ∑ j ∈ G, volume (⋃ i ∈ completeFibreW94 F parent j, A i) := by
  classical
  have hsum : (∑ i ∈ F, volume (A i)) =
      ∑ j ∈ G, ∑ i ∈ completeFibreW94 F parent j, volume (A i) :=
    (Finset.sum_fiberwise_of_maps_to hmap _).symm
  constructor
  · rw [hsum]
    exact Finset.sum_le_sum fun j hj => measure_biUnion_finset_le _ _
  · rw [hsum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    calc
      _ <= ∑ i ∈ completeFibreW94 F parent j,
          volume (⋃ i ∈ completeFibreW94 F parent j, A i) := by
        apply Finset.sum_le_sum
        intro i hi
        apply measure_mono
        exact Set.subset_biUnion_of_mem hi
      _ = ((completeFibreW94 F parent j).card : ENNReal) *
          volume (⋃ i ∈ completeFibreW94 F parent j, A i) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ <= _ := mul_le_mul_right' (hcard j hj) _

theorem source_centring_shaded_union_w102
    {delta : NNReal} {iota : Type uI} [DecidableEq iota]
    (F G : Finset iota) (Y : iota -> ShadedTube delta E)
    (parent : iota -> iota) (W : iota -> Tube (delta / 2) E)
    (hcov : ∀ i ∈ F, (fun x : E => (1 / 8 : Real) • x) '' (Y i).carrier ⊆
      (W (parent i)).carrier)
    (hmap : ∀ i ∈ F, parent i ∈ G) :
    (⋃ j ∈ G, (sourceCentringShadingW102 F Y parent W hcov j).shade) =
      (fun x : E => (1 / 8 : Real) • x) '' (⋃ i ∈ F, (Y i).shade) := by
  ext x
  constructor
  · intro hx
    obtain ⟨j, hj, hx⟩ := Set.mem_iUnion₂.mp hx
    change x ∈ ⋃ i ∈ completeFibreW94 F parent j,
      (fun x : E => (1 / 8 : Real) • x) '' (Y i).shade at hx
    obtain ⟨i, hi, y, hy, rfl⟩ := Set.mem_iUnion₂.mp hx
    exact ⟨y, Set.mem_iUnion₂.mpr ⟨i, (Finset.mem_filter.mp hi).1, hy⟩, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨i, hi, hy⟩ := Set.mem_iUnion₂.mp hy
    apply Set.mem_iUnion₂.mpr
    refine ⟨parent i, hmap i hi, ?_⟩
    exact Set.mem_iUnion₂.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, rfl⟩, y, hy, rfl⟩

end
end Kakeya.ml1Boot.TrialRestartW94
