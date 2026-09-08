module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceCentringReductionProofW102

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
  [FiniteDimensional Real E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]

/-- A hereditary band survives the actual centring on the larger original
family. The new band is its parent image, with the exact fixed loss 384. -/
theorem centred_image_hereditary_fullness_w103
    (hdim : Module.finrank Real E = 3)
    {iota : Type uI} [DecidableEq iota] {delta : NNReal}
    (hd : 0 < delta) (hd1 : delta <= 1)
    (b : Finset iota) (Y : iota -> ShadedTube delta E)
    (parent : iota -> iota) (Z : iota -> ShadedTube (delta / 2) E)
    (lam : ENNReal)
    (hfull : ∀ i ∈ b, lam * volume (Y i).carrier <= volume (Y i).shade)
    (hshade : ∀ i ∈ b,
      (fun x : E => (1 / 8 : Real) • x) '' (Y i).shade ⊆ (Z (parent i)).shade)
    (hvolume : ∀ i ∈ b, volume (Z (parent i)).carrier <=
      (384 : ENNReal) * (1 / 512 : ENNReal) * volume (Y i).carrier) :
    ∀ t ⊆ b.image parent, t.Nonempty ->
      lam / 384 <= fullness' t (fun j => (Z j).toShadedBody) := by
  intro t ht htne
  have hpoint : ∀ j ∈ t, lam * volume (Z j).carrier <=
      (384 : ENNReal) * volume (Z j).shade := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (ht hj)
    have himage : (1 / 512 : ENNReal) * volume (Y i).shade <= volume (Z (parent i)).shade := by
      rw [← volume_source_centring_image_w102 hdim]
      exact measure_mono (hshade i hi)
    calc
      _ <= lam * ((384 : ENNReal) * (1 / 512 : ENNReal) * volume (Y i).carrier) :=
        mul_le_mul' le_rfl (hvolume i hi)
      _ = (384 : ENNReal) * ((1 / 512 : ENNReal) * (lam * volume (Y i).carrier)) := by ring
      _ <= (384 : ENNReal) * ((1 / 512 : ENNReal) * volume (Y i).shade) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl (hfull i hi))
      _ <= _ := mul_le_mul' le_rfl himage
  have hr : 0 < delta / 2 := by positivity
  have hr1 : delta / 2 <= 1 := by
    have : delta / 2 <= delta := div_le_self (show (0 : NNReal) <= delta from zero_le) (by norm_num)
    exact this.trans hd1
  have hcar0 : (∑ j ∈ t, volume (Z j).carrier) ≠ 0 := by
    obtain ⟨j, hj⟩ := htne
    exact ne_of_gt (Finset.sum_pos_iff.mpr ⟨j, hj, (Tube.volume_pos_and_lt_top hr hr1 (Z j).toTube).1⟩)
  have hcartop : (∑ j ∈ t, volume (Z j).carrier) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun j _ => (Z j).isCompact.measure_ne_top
  have hsum : lam * (∑ j ∈ t, volume (Z j).carrier) <=
      (384 : ENNReal) * (∑ j ∈ t, volume (Z j).shade) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum hpoint
  have h : lam <= (384 : ENNReal) * fullness' t (fun j => (Z j).toShadedBody) := by
    change lam <= (384 : ENNReal) *
      ((∑ j ∈ t, volume (Z j).shade) / (∑ j ∈ t, volume (Z j).carrier))
    rw [← mul_div_assoc]
    exact (ENNReal.le_div_iff_mul_le (Or.inl hcar0) (Or.inl hcartop)).mpr hsum
  apply (ENNReal.div_le_iff (by norm_num : (384 : ENNReal) ≠ 0)
    (by norm_num : (384 : ENNReal) ≠ ⊤)).mpr
  simpa only [mul_comm] using h

end
end Kakeya.ml1Boot.TrialRestartW94
