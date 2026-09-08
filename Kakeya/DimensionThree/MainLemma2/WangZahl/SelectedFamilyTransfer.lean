module

public import Kakeya.DimensionThree.MainLemma2.WangZahl.EToD

@[expose] public section

open MeasureTheory Convexity

namespace Kakeya.WangZahl

noncomputable section

universe u

/-- A shade-heavy subfamily inherits density, with the exact inverse of the
shade-selection loss. -/
theorem selected_dense_of_shade_mass
    {delta : NNReal} {iota : Type u} {s t : Finset iota}
    (T : iota -> ShadedTube delta Space3) (ht : t ⊆ s)
    {lambda L : ENNReal} (hL0 : L ≠ 0) (hLtop : L ≠ ⊤)
    (hdense : lambda * (∑ i ∈ s, volume (T i).carrier) <=
      ∑ i ∈ s, volume (T i).shade)
    (hshade : (∑ i ∈ s, volume (T i).shade) <=
      L * ∑ i ∈ t, volume (T i).shade) :
    (lambda * L⁻¹) * (∑ i ∈ t, volume (T i).carrier) <=
      ∑ i ∈ t, volume (T i).shade := by
  have hcarrier : (∑ i ∈ t, volume (T i).carrier) <=
      ∑ i ∈ s, volume (T i).carrier :=
    Finset.sum_le_sum_of_subset_of_nonneg ht fun _ _ _ => bot_le
  have hmul : L * ((lambda * L⁻¹) *
      (∑ i ∈ t, volume (T i).carrier)) <=
      L * (∑ i ∈ t, volume (T i).shade) := by
    calc
      L * ((lambda * L⁻¹) * (∑ i ∈ t, volume (T i).carrier)) =
          lambda * (∑ i ∈ t, volume (T i).carrier) := by
        rw [show L * ((lambda * L⁻¹) *
            (∑ i ∈ t, volume (T i).carrier)) =
          (L * L⁻¹) * lambda *
            (∑ i ∈ t, volume (T i).carrier) by ring,
          ENNReal.mul_inv_cancel hL0 hLtop, one_mul]
      _ <= lambda * (∑ i ∈ s, volume (T i).carrier) := by gcongr
      _ <= ∑ i ∈ s, volume (T i).shade := hdense
      _ <= L * ∑ i ∈ t, volume (T i).shade := hshade
  have hcomm :
      ((lambda * L⁻¹) * (∑ i ∈ t, volume (T i).carrier)) * L <=
        (∑ i ∈ t, volume (T i).shade) * L := by
    simpa [mul_comm] using hmul
  exact (ENNReal.mul_le_mul_iff_left hL0 hLtop).mp hcomm

/-- The same two inequalities control the carrier-mass ratio needed by
`IsFrostmanIn.of_le_of_subset`. -/
theorem carrier_mass_le_of_dense_shade_mass
    {delta : NNReal} {iota : Type u} {s t : Finset iota}
    (T : iota -> ShadedTube delta Space3)
    {lambda L : ENNReal} (hlambda0 : lambda ≠ 0) (hlambdatop : lambda ≠ ⊤)
    (hdense : lambda * (∑ i ∈ s, volume (T i).carrier) <=
      ∑ i ∈ s, volume (T i).shade)
    (hshade : (∑ i ∈ s, volume (T i).shade) <=
      L * ∑ i ∈ t, volume (T i).shade) :
    (∑ i ∈ s, volume (T i).carrier) <=
      (lambda⁻¹ * L) * ∑ i ∈ t, volume (T i).carrier := by
  have hshadeCarrier : (∑ i ∈ t, volume (T i).shade) <=
      ∑ i ∈ t, volume (T i).carrier :=
    Finset.sum_le_sum fun i hi => measure_mono (T i).shade_subset
  have hmul : lambda * (∑ i ∈ s, volume (T i).carrier) <=
      lambda * ((lambda⁻¹ * L) *
        ∑ i ∈ t, volume (T i).carrier) := by
    calc
      lambda * (∑ i ∈ s, volume (T i).carrier) <=
          ∑ i ∈ s, volume (T i).shade := hdense
      _ <= L * ∑ i ∈ t, volume (T i).shade := hshade
      _ <= L * ∑ i ∈ t, volume (T i).carrier := by gcongr
      _ = lambda * ((lambda⁻¹ * L) *
          ∑ i ∈ t, volume (T i).carrier) := by
        rw [show lambda * ((lambda⁻¹ * L) *
            ∑ i ∈ t, volume (T i).carrier) =
          (lambda * lambda⁻¹) * L *
            ∑ i ∈ t, volume (T i).carrier by ring,
          ENNReal.mul_inv_cancel hlambda0 hlambdatop, one_mul]
  have hcomm :
      (∑ i ∈ s, volume (T i).carrier) * lambda <=
        ((lambda⁻¹ * L) * ∑ i ∈ t, volume (T i).carrier) * lambda := by
    simpa [mul_comm] using hmul
  exact (ENNReal.mul_le_mul_iff_left hlambda0 hlambdatop).mp hcomm

/-- A heavy shade selection simultaneously preserves density and transfers the
ambient Frostman property with its explicit loss. -/
theorem selected_dense_and_frostman
    {delta : NNReal} {iota : Type u} {s t : Finset iota}
    (T : iota -> ShadedTube delta Space3) (ht : t ⊆ s)
    (B : ConvexSpaceBody Space3) {C lambda L : ENNReal}
    (hlambda0 : lambda ≠ 0) (hlambdatop : lambda ≠ ⊤)
    (hL0 : L ≠ 0) (hLtop : L ≠ ⊤)
    (hTB : ∀ i ∈ s, (T i).toConvexSpaceBody <= B)
    (hF : ConvexSpaceBody.IsFrostmanIn s
      (fun i => (T i).toConvexSpaceBody) B C)
    (hdense : lambda * (∑ i ∈ s, volume (T i).carrier) <=
      ∑ i ∈ s, volume (T i).shade)
    (hshade : (∑ i ∈ s, volume (T i).shade) <=
      L * ∑ i ∈ t, volume (T i).shade) :
    (lambda * L⁻¹) * (∑ i ∈ t, volume (T i).carrier) <=
        ∑ i ∈ t, volume (T i).shade ∧
      ConvexSpaceBody.IsFrostmanIn t
        (fun i => (T i).toConvexSpaceBody) B (C * (lambda⁻¹ * L)) := by
  constructor
  · exact selected_dense_of_shade_mass T ht hL0 hLtop hdense hshade
  · apply hF.of_le_of_subset hTB ht
    exact carrier_mass_le_of_dense_shade_mass T hlambda0 hlambdatop hdense hshade

end

end Kakeya.WangZahl

#print axioms Kakeya.WangZahl.selected_dense_of_shade_mass
#print axioms Kakeya.WangZahl.carrier_mass_le_of_dense_shade_mass
#print axioms Kakeya.WangZahl.selected_dense_and_frostman
