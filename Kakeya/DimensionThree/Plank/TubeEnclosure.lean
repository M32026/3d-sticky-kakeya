/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.Geometry
public import Kakeya.DimensionThree.Plank.EDParentCount
public import Kakeya.DimensionThree.IsometryTransport
public import Kakeya.Tube.IntersectionVolume

/-!
# Enclosing a thickened plank in a dilated tube

This file supplies the low-level bridge used by Proposition 6.6(A): a fixed dilation of a
thickened `a × b × 1` plank lies in a fixed dilation of a `ρ`-tube when `b ≲ ρ`.  The long axis
of `Plank.thickened` is coordinate `2`, so the more usual coordinate-`0` prism-to-tube lemma is
not directly applicable.
-/

@[expose] public section

open Metric Set
open scoped NNReal

noncomputable section

namespace Kakeya

namespace Tube

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  [Nontrivial E] [Nontrivial F]

/-- Dilating a tube about its centre commutes with a linear isometry equivalence. -/
@[simp]
theorem mapLinearIsometryEquiv_dilate {δ : NNReal} (T : Tube δ E)
    (f : E ≃ₗᵢ[ℝ] F) (C : ℝ) :
    (Tube.dilate T C).mapLinearIsometryEquiv f =
      Tube.dilate (T.mapLinearIsometryEquiv f) C := by
  apply ConvexSpaceBody.ext
  change f '' (Tube.dilate T C).carrier =
    (Tube.dilate (T.mapLinearIsometryEquiv f) C).carrier
  rw [Tube.dilate_carrier, Tube.dilate_carrier, Tube.mapLinearIsometryEquiv_carrier,
    Tube.mapLinearIsometryEquiv_center]
  ext z
  constructor
  · rintro ⟨w, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨f v, ⟨v, hv, rfl⟩, ?_⟩
    simp [AffineMap.homothety_apply, map_sub]
  · rintro ⟨w, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨AffineMap.homothety T.center C v,
      ⟨v, hv, rfl⟩, ?_⟩
    simp [AffineMap.homothety_apply, map_sub]

end Tube

namespace prismTubeEnclosure

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Distance from a point in a prism to the line through its centre in a chosen basis
direction, bounded by the sum of all transverse half-widths. -/
theorem dist_transverse_le {n : ℕ} (P : PrismNDim (n + 1) E E) (i₀ : Fin (n + 1)) {x : E}
    (hx : x ∈ P.carrier) :
    dist x (P.center + P.basis.repr (x - P.center) i₀ • P.basis i₀)
      ≤ ∑ i ∈ Finset.univ.erase i₀, (P.thicknesses i : ℝ) := by
  set t := fun i : Fin (n + 1) ↦ P.basis.repr (x - P.center) i with ht
  have ht_sum : x - P.center = ∑ i : Fin (n + 1), t i • P.basis i := by
    calc
      x - P.center = ∑ i, P.basis.repr (x - P.center) i • P.basis i := by
        symm
        exact P.basis.sum_repr (x - P.center)
      _ = ∑ i, t i • P.basis i := by simp [t]
  have hx' : ∀ i, |t i| ≤ (P.thicknesses i : ℝ) := by
    intro i
    simpa [t] using (P.mem_carrier_iff x).mp hx i
  calc
    dist x (P.center + t i₀ • P.basis i₀)
        = ‖(x - P.center) - t i₀ • P.basis i₀‖ := by
          rw [dist_eq_norm]
          congr 1
          abel
    _ = ‖∑ i ∈ Finset.univ.erase i₀, t i • P.basis i‖ := by
      congr 1
      calc
        (x - P.center) - t i₀ • P.basis i₀
            = (∑ i : Fin (n + 1), t i • P.basis i) - t i₀ • P.basis i₀ := by rw [ht_sum]
        _ = ∑ i ∈ Finset.univ.erase i₀, t i • P.basis i := by
          simp [Finset.sum_erase_eq_sub (Finset.mem_univ i₀)]
    _ ≤ ∑ i ∈ Finset.univ.erase i₀, ‖t i • P.basis i‖ :=
      norm_sum_le _ _
    _ = ∑ i ∈ Finset.univ.erase i₀, |t i| := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [norm_smul, P.basis.orthonormal.norm_eq_one]
    _ ≤ ∑ i ∈ Finset.univ.erase i₀, (P.thicknesses i : ℝ) :=
      Finset.sum_le_sum fun i _ ↦ hx' i

/-- The unit segment through `c` in a unit direction contains all points with axial
coordinate of absolute value at most `1 / 2`. -/
theorem unitSegment (c : E) {e : E} (he : ‖e‖ = 1) :
    dist (c - (2⁻¹ : ℝ) • e) (c + (2⁻¹ : ℝ) • e) = 1 ∧
      ∀ t : ℝ, |t| ≤ 2⁻¹ →
        c + t • e ∈ segment ℝ (c - (2⁻¹ : ℝ) • e) (c + (2⁻¹ : ℝ) • e) := by
  constructor
  · have hsub : (c - (2⁻¹ : ℝ) • e) - (c + (2⁻¹ : ℝ) • e) = -e := by module
    rw [dist_eq_norm, hsub, norm_neg, he]
  · intro t ht
    rw [segment]
    refine ⟨2⁻¹ - t, 2⁻¹ + t, ?_, ?_, ?_, ?_⟩
    · linarith [(abs_le.mp ht).1, (abs_le.mp ht).2]
    · linarith [(abs_le.mp ht).1, (abs_le.mp ht).2]
    · linarith
    · module

/-- The `s`-tube whose core is the unit segment through the centre of a prism in the
chosen basis direction. -/
def axisTube {n : ℕ} (P : PrismNDim (n + 1) E E) (i₀ : Fin (n + 1)) (s : NNReal) : Tube s E :=
  Tube.mk' s (unitSegment P.center (P.basis.orthonormal.norm_eq_one i₀)).1

/-- A prism with bounded longitudinal half-width and bounded total transverse half-width
lies in a fixed dilation of its axis tube. -/
theorem carrier_subset_axisTube_dilate {n : ℕ} (P : PrismNDim (n + 1) E E)
    (i₀ : Fin (n + 1)) {Λ : ℝ} (hΛ : 1 ≤ Λ) (hlong : (P.thicknesses i₀ : ℝ) ≤ Λ)
    (s : NNReal)
    (htrans : ∑ i ∈ Finset.univ.erase i₀, (P.thicknesses i : ℝ) ≤ 2 * Λ * (s : ℝ)) :
    (P.carrier : Set E) ⊆ (Tube.dilate (axisTube P i₀ s) (2 * Λ)).carrier := by
  intro x hx
  let t : ℝ := P.basis.repr (x - P.center) i₀
  have ht : |t| ≤ (P.thicknesses i₀ : ℝ) := by
    simpa [t] using (P.mem_carrier_iff x).mp hx i₀
  have hcenter : (axisTube P i₀ s).center = P.center := by
    simp [axisTube, Tube.center, midpoint_eq_smul_add]
    module
  have hdirection : (axisTube P i₀ s).direction = P.basis i₀ := by
    simp [axisTube, Tube.direction]
    module
  have hdist : dist x ((axisTube P i₀ s).center + t • (axisTube P i₀ s).direction)
      ≤ (2 * Λ) * (s : ℝ) := by
    rw [hcenter, hdirection]
    exact (dist_transverse_le P i₀ hx).trans htrans
  have ht' : |t| ≤ (2 * Λ) / 2 := by
    have htwo : (2 * Λ) / 2 = Λ := by ring
    rw [htwo]
    exact ht.trans hlong
  exact Tube.mem_dilate_of_dist_axis_le (axisTube P i₀ s) (by linarith) ht' hdist

variable {a b : NNReal} {hab : a ≤ b} {hb1 : b ≤ 1}

/-- The long half-width of a dilated thickened plank is bounded by `CD` when `C,D ≥ 1`. -/
theorem thickened_dilation_long_le (P : Plank a b hab hb1)
    (θ : NNReal) (hθ1 : θ ≤ 1) (C D : NNReal) (hD : 1 ≤ D) :
    (((P.thickened θ hθ1).toPrismNDim.dilation C).thicknesses 2 : ℝ)
      ≤ (C : ℝ) * (D : ℝ) := by
  rw [PrismNDim.dilation_thicknesses, (P.thickened θ hθ1).thicknesses_eq]
  simp [Matrix.cons_val_two]
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hC0 : 0 ≤ (C : ℝ) := NNReal.coe_nonneg C
  nlinarith

/-- The two transverse half-widths of a dilated thickened plank fit the radius budget of
the `(2CD)`-dilation of a `ρ`-tube when `b ≤ Dρ`. -/
theorem thickened_dilation_transverse_le (P : Plank a b hab hb1)
    (θ : NNReal) (hθ1 : θ ≤ 1) (C D ρ : NNReal) (hbρ : b ≤ D * ρ) :
    ∑ i ∈ Finset.univ.erase (2 : Fin 3),
        ((((P.thickened θ hθ1).toPrismNDim.dilation C).thicknesses i : NNReal) : ℝ)
      ≤ 2 * ((C : ℝ) * (D : ℝ)) * (ρ : ℝ) := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ (2 : Fin 3)), Fin.sum_univ_three]
  simp only [PrismNDim.dilation_thicknesses,
    (P.thickened θ hθ1).thicknesses_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, NNReal.coe_mul]
  have hθ1' : (θ : ℝ) ≤ 1 := by exact_mod_cast hθ1
  have hbρ' : (b : ℝ) ≤ (D : ℝ) * (ρ : ℝ) := by exact_mod_cast hbρ
  have hC0 : 0 ≤ (C : ℝ) := NNReal.coe_nonneg C
  have hb0 : 0 ≤ (b : ℝ) := NNReal.coe_nonneg b
  have hθb : (θ : ℝ) * (b : ℝ) ≤ (b : ℝ) := by nlinarith
  have hCθb := mul_le_mul_of_nonneg_left hθb hC0
  have hCbρ := mul_le_mul_of_nonneg_left hbρ' hC0
  ring_nf at *
  nlinarith

/-- After a fixed enlargement by `A`, the long half-width of the plank test body is at most
`A C D`. -/
theorem homothetic_thickened_dilation_long_le (P : Plank a b hab hb1)
    (θ : NNReal) (hθ1 : θ ≤ 1) (A C D : NNReal) (hD : 1 ≤ D) :
    (((((P.thickened θ hθ1).toPrismNDim.dilation C).homothety 0 A).thicknesses 2 :
        NNReal) : ℝ) ≤ (A : ℝ) * (C : ℝ) * (D : ℝ) := by
  rw [PrismNDim.homothety_thicknesses]
  have h := thickened_dilation_long_le P θ hθ1 C D hD
  push_cast
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h (NNReal.coe_nonneg A)

/-- After a fixed enlargement by `A`, the two transverse half-widths still fit the radius budget
of the `2ACD`-dilate of a `ρ`-tube. -/
theorem homothetic_thickened_dilation_transverse_le (P : Plank a b hab hb1)
    (θ : NNReal) (hθ1 : θ ≤ 1) (A C D ρ : NNReal) (hbρ : b ≤ D * ρ) :
    ∑ i ∈ Finset.univ.erase (2 : Fin 3),
        (((((P.thickened θ hθ1).toPrismNDim.dilation C).homothety 0 A).thicknesses i :
          NNReal) : ℝ)
      ≤ 2 * ((A : ℝ) * (C : ℝ) * (D : ℝ)) * (ρ : ℝ) := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ (2 : Fin 3)), Fin.sum_univ_three]
  simp only [PrismNDim.homothety_thicknesses, NNReal.coe_mul]
  have h := thickened_dilation_transverse_le P θ hθ1 C D ρ hbρ
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ (2 : Fin 3)), Fin.sum_univ_three] at h
  nlinarith [NNReal.coe_nonneg A]

end prismTubeEnclosure

namespace edParentCount

/-- A pairwise essentially-distinct `ρ`-parent family has uniformly bounded occupancy in every
fixed dilation of a thickened `a × b × 1` plank, provided `b` is at most a fixed multiple of
`ρ`.  The plank-shaped test body is enclosed in its long-axis `ρ`-tube and the assigned-parent
packing theorem is then applied to that tube. -/
theorem card_assignedParents_le_dilatedThickenedPlank
    {ι κ : Type*} [DecidableEq κ] {δ ρ D a b C : NNReal}
    {hab : a ≤ b} {hb1 : b ≤ 1}
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hD : 1 ≤ D) (hC : 1 ≤ C)
    (hbρ : b ≤ D * ρ)
    (q : Finset ι) (T : ι → Tube δ (EuclideanSpace ℝ (Fin 3)))
    (r : Finset κ) (R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))) (assign : ι → κ)
    (hED : (↑r : Set κ).Pairwise fun k l ↦
      IsEssentiallyDistinct (R k).carrier (R l).carrier)
    (hassign : ∀ i ∈ q, assign i ∈ r ∧
      (T i).toConvexSpaceBody ≤ Tube.dilate (R (assign i)) (D : ℝ))
    (P : Plank a b hab hb1) (θ : NNReal) (hθ1 : θ ≤ 1) :
    (((r.filter fun k ↦ ∃ i ∈ q, assign i = k ∧
        (T i).toConvexSpaceBody ≤
          ((P.thickened θ hθ1).toPrismNDim.dilation C).toConvexSpaceBody).card : ENNReal))
      ≤ (COfTestDilate 3 D 1 (2 * (C * D)) : ENNReal) := by
  classical
  let Q := (P.thickened θ hθ1).toPrismNDim.dilation C
  let Vtest : Tube (1 * ρ) (EuclideanSpace ℝ (Fin 3)) :=
    prismTubeEnclosure.axisTube Q (2 : Fin 3) (1 * ρ)
  let L : NNReal := ⟨2 * ((C : ℝ) * (D : ℝ)), by positivity⟩
  have hL_eq : L = 2 * (C * D) := by
    apply NNReal.eq
    rfl
  have hCD : 1 ≤ C * D := by
    calc
      1 = 1 * 1 := by norm_num
      _ ≤ C * D := mul_le_mul hC hD (by positivity) (by positivity)
  have hL : 1 ≤ L := by
    rw [hL_eq]
    exact hCD.trans <| by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (show (1 : NNReal) ≤ 2 by norm_num) (C * D).2
  have hLcoe : (L : ℝ) = 2 * ((C * D : NNReal) : ℝ) := by
    rw [hL_eq]
    norm_num
  have htest : (Q.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
      (Tube.dilate Vtest (L : ℝ)).carrier := by
    have hlong := prismTubeEnclosure.thickened_dilation_long_le P θ hθ1 C D hD
    have htransρ :=
      prismTubeEnclosure.thickened_dilation_transverse_le P θ hθ1 C D ρ hbρ
    have htrans : ∑ i ∈ Finset.univ.erase (2 : Fin 3),
        ((Q.thicknesses i : NNReal) : ℝ) ≤ 2 * ((C : ℝ) * (D : ℝ)) * ((1 * ρ : NNReal) : ℝ) := by
      simpa only [Q, one_mul] using htransρ
    have hmain :=
      prismTubeEnclosure.carrier_subset_axisTube_dilate Q (2 : Fin 3) hCD hlong
        (1 * ρ) htrans
    change Q.carrier ⊆ (Tube.dilate Vtest (L : ℝ)).carrier
    rw [hLcoe]
    convert hmain using 1 <;> rfl
  have hsub :
      r.filter (fun k ↦ ∃ i ∈ q, assign i = k ∧
        (T i).toConvexSpaceBody ≤ Q.toConvexSpaceBody) ⊆
      r.filter (fun k ↦ ∃ i ∈ q, assign i = k ∧
        (T i).toConvexSpaceBody ≤ Tube.dilate Vtest (L : ℝ)) := by
    intro k hk
    rcases Finset.mem_filter.mp hk with ⟨hkr, i, hiq, hik, hiQ⟩
    exact Finset.mem_filter.mpr ⟨hkr, i, hiq, hik, hiQ.trans htest⟩
  calc
    (((r.filter fun k ↦ ∃ i ∈ q, assign i = k ∧
        (T i).toConvexSpaceBody ≤ Q.toConvexSpaceBody).card : ENNReal))
        ≤ ((r.filter fun k ↦ ∃ i ∈ q, assign i = k ∧
          (T i).toConvexSpaceBody ≤ Tube.dilate Vtest (L : ℝ)).card : ENNReal) := by
            exact_mod_cast Finset.card_le_card hsub
    _ ≤ (COfTestDilate 3 D 1 L : ENNReal) := by
      simpa only [one_mul, finrank_euclideanSpace_fin] using
        card_assignedParents_le_of_subset_dilate (Ctest := 1) hρ0 hρ1 hD
          (by norm_num) hL q T r R assign hED hassign Vtest
    _ = (COfTestDilate 3 D 1 (2 * (C * D)) : ENNReal) := by rw [hL_eq]

/-- The assigned-parent count remains absolute after applying a common fixed enlargement `A` to
the plank test body.  This is the inverse-image form needed when the output family has first been
shrunk by a common homothety. -/
theorem card_assignedParents_le_homotheticDilatedThickenedPlank
    {ι κ : Type*} [DecidableEq κ] {δ ρ D a b A C : NNReal}
    {hab : a ≤ b} {hb1 : b ≤ 1}
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hD : 1 ≤ D) (hA : 1 ≤ A) (hC : 1 ≤ C)
    (hbρ : b ≤ D * ρ)
    (q : Finset ι) (T : ι → Tube δ (EuclideanSpace ℝ (Fin 3)))
    (r : Finset κ) (R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))) (assign : ι → κ)
    (hED : (↑r : Set κ).Pairwise fun k l ↦
      IsEssentiallyDistinct (R k).carrier (R l).carrier)
    (hassign : ∀ i ∈ q, assign i ∈ r ∧
      (T i).toConvexSpaceBody ≤ Tube.dilate (R (assign i)) (D : ℝ))
    (P : Plank a b hab hb1) (θ : NNReal) (hθ1 : θ ≤ 1) :
    (((r.filter fun k ↦ ∃ i ∈ q, assign i = k ∧
        (T i).toConvexSpaceBody ≤
          (((P.thickened θ hθ1).toPrismNDim.dilation C).homothety 0 A).toConvexSpaceBody).card :
        ENNReal))
      ≤ (COfTestDilate 3 D 1 (2 * (A * C * D)) : ENNReal) := by
  classical
  let Q := (((P.thickened θ hθ1).toPrismNDim.dilation C).homothety 0 A)
  let Vtest : Tube (1 * ρ) (EuclideanSpace ℝ (Fin 3)) :=
    prismTubeEnclosure.axisTube Q (2 : Fin 3) (1 * ρ)
  let L : NNReal := ⟨2 * ((A : ℝ) * (C : ℝ) * (D : ℝ)), by positivity⟩
  have hL_eq : L = 2 * (A * C * D) := by
    apply NNReal.eq
    rfl
  have hACD : 1 ≤ A * C * D := by
    calc
      1 = 1 * 1 * 1 := by norm_num
      _ ≤ A * C * D := mul_le_mul (mul_le_mul hA hC (by positivity) (by positivity)) hD
        (by positivity) (by positivity)
  have hL : 1 ≤ L := by
    rw [hL_eq]
    exact hACD.trans <| by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (show (1 : NNReal) ≤ 2 by norm_num) (A * C * D).2
  have hLcoe : (L : ℝ) = 2 * (((A * C * D : NNReal) : ℝ)) := by
    rw [hL_eq]
    norm_num
  have htest : (Q.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
      (Tube.dilate Vtest (L : ℝ)).carrier := by
    have hlong :=
      prismTubeEnclosure.homothetic_thickened_dilation_long_le P θ hθ1 A C D hD
    have htransρ :=
      prismTubeEnclosure.homothetic_thickened_dilation_transverse_le P θ hθ1 A C D ρ hbρ
    have htrans : ∑ i ∈ Finset.univ.erase (2 : Fin 3),
        ((Q.thicknesses i : NNReal) : ℝ) ≤
          2 * ((A : ℝ) * (C : ℝ) * (D : ℝ)) * ((1 * ρ : NNReal) : ℝ) := by
      simpa only [Q, one_mul] using htransρ
    have hmain :=
      prismTubeEnclosure.carrier_subset_axisTube_dilate Q (2 : Fin 3) hACD hlong
        (1 * ρ) htrans
    change Q.carrier ⊆ (Tube.dilate Vtest (L : ℝ)).carrier
    rw [hLcoe]
    convert hmain using 1 <;> rfl
  have hsub :
      r.filter (fun k ↦ ∃ i ∈ q, assign i = k ∧
        (T i).toConvexSpaceBody ≤ Q.toConvexSpaceBody) ⊆
      r.filter (fun k ↦ ∃ i ∈ q, assign i = k ∧
        (T i).toConvexSpaceBody ≤ Tube.dilate Vtest (L : ℝ)) := by
    intro k hk
    rcases Finset.mem_filter.mp hk with ⟨hkr, i, hiq, hik, hiQ⟩
    exact Finset.mem_filter.mpr ⟨hkr, i, hiq, hik, hiQ.trans htest⟩
  calc
    (((r.filter fun k ↦ ∃ i ∈ q, assign i = k ∧
        (T i).toConvexSpaceBody ≤ Q.toConvexSpaceBody).card : ENNReal))
        ≤ ((r.filter fun k ↦ ∃ i ∈ q, assign i = k ∧
          (T i).toConvexSpaceBody ≤ Tube.dilate Vtest (L : ℝ)).card : ENNReal) := by
            exact_mod_cast Finset.card_le_card hsub
    _ ≤ (COfTestDilate 3 D 1 L : ENNReal) := by
      simpa only [one_mul, finrank_euclideanSpace_fin] using
        card_assignedParents_le_of_subset_dilate (Ctest := 1) hρ0 hρ1 hD
          (by norm_num) hL q T r R assign hED hassign Vtest
    _ = (COfTestDilate 3 D 1 (2 * (A * C * D)) : ENNReal) := by rw [hL_eq]

end edParentCount

end Kakeya

end

end
