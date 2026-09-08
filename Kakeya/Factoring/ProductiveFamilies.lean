/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Factoring.Productive
public import Kakeya.Shading

/-! # Counting and thick families after productive restriction -/

@[expose] public section

open MeasureTheory Convexity Kakeya

namespace ShadedBody

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {ι κ : Type*}

/-- The exact counting body over one productive block. -/
noncomputable def productiveCountingBody (F : FactorFamily E ι κ)
    (G : ShadedFactorFamily E ι κ)
    (hcarrier : ∀ i, (G.innerBody i).toConvexSpaceBody =
      (F.innerBody i).toConvexSpaceBody) (j : κ) : ShadedBody E where
  toConvexSpaceBody := (F.outerBody j).cthickening (F.outerBody j).scale
  shade := iUnionShade (productiveFiber F G j) (zeroExtendedInnerBody F G)
  measurableSet_shade := measurableSet_iUnion_shade _ _
  shade_subset := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    have hi' := (mem_productiveFiber_iff F G j i).mp hi
    have hxc := (zeroExtendedInnerBody F G i).shade_subset hxi
    rw [zeroExtendedInnerBody_toConvexSpaceBody F G hcarrier] at hxc
    have hxparent := F.inner_le_parent i hi'.1 hxc
    apply ConvexSpaceBody.self_le_cthickening (F.outerBody j) (F.outerBody j).scale
    simpa [hi'.2.2] using hxparent

/-- The counting body shade is exactly the final zero-extended fiber union. -/
@[simp]
theorem productiveCountingBody_shade (F : FactorFamily E ι κ)
    (G : ShadedFactorFamily E ι κ)
    (hcarrier : ∀ i, (G.innerBody i).toConvexSpaceBody =
      (F.innerBody i).toConvexSpaceBody) (j : κ) :
    (productiveCountingBody F G hcarrier j).shade =
      iUnionShade (productiveFiber F G j) (zeroExtendedInnerBody F G) := rfl

/-- The thick induced body over one productive block. -/
noncomputable def productiveThickBody (F : FactorFamily E ι κ)
    (G : ShadedFactorFamily E ι κ) (j : κ) : ShadedBody E :=
  inducedShading (productiveFiber F G j) (zeroExtendedInnerBody F G) (F.outerBody j)

open Classical in
/-- The exact counting family associated to a preliminary pipeline family. -/
noncomputable def productiveCountingFamily (F : FactorFamily E ι κ)
    (G : ShadedFactorFamily E ι κ)
    (hcarrier : ∀ i, (G.innerBody i).toConvexSpaceBody = (F.innerBody i).toConvexSpaceBody)
    (_hparent : G.parent = F.parent) : ShadedFactorFamily E ι κ where
  innerSet := productiveFinalInnerSet F G
  innerBody := zeroExtendedInnerBody F G
  outerSet := productiveOuterSet G
  outerBody := productiveCountingBody F G hcarrier
  parent := F.parent
  parent_mem := fun i hi ↦ (mem_productiveFinalInnerSet_iff F G i).mp hi |>.2
  inner_le_parent := by
    intro i hi
    rw [zeroExtendedInnerBody_toConvexSpaceBody F G hcarrier]
    exact (F.inner_le_parent i ((mem_productiveFinalInnerSet_iff F G i).mp hi).1).trans
      (ConvexSpaceBody.self_le_cthickening (F.outerBody (F.parent i))
        (F.outerBody (F.parent i)).scale)
  shade_subset_parent := by
    intro i hi
    have hi' := (mem_productiveFinalInnerSet_iff F G i).mp hi
    have hip : i ∈ productiveFiber F G (F.parent i) :=
      (mem_productiveFiber_iff F G (F.parent i) i).mpr ⟨hi'.1, hi'.2, rfl⟩
    exact Set.subset_iUnion₂_of_subset i hip (Set.Subset.refl _)

open Classical in
/-- The thick induced family associated to a preliminary pipeline family. -/
noncomputable def productiveThickFamily (F : FactorFamily E ι κ)
    (G : ShadedFactorFamily E ι κ)
    (hcarrier : ∀ i, (G.innerBody i).toConvexSpaceBody = (F.innerBody i).toConvexSpaceBody)
    (_hparent : G.parent = F.parent) : ShadedFactorFamily E ι κ where
  innerSet := productiveFinalInnerSet F G
  innerBody := zeroExtendedInnerBody F G
  outerSet := productiveOuterSet G
  outerBody := productiveThickBody F G
  parent := F.parent
  parent_mem := fun i hi ↦ (mem_productiveFinalInnerSet_iff F G i).mp hi |>.2
  inner_le_parent := by
    intro i hi
    rw [zeroExtendedInnerBody_toConvexSpaceBody F G hcarrier]
    exact (F.inner_le_parent i ((mem_productiveFinalInnerSet_iff F G i).mp hi).1).trans
      (ConvexSpaceBody.self_le_cthickening (F.outerBody (F.parent i))
        (F.outerBody (F.parent i)).scale)
  shade_subset_parent := by
    intro i hi x hxi
    apply cthickening_scale_iUnionShade_subset_shade_inducedShading
      (s := productiveFiber F G (F.parent i)) (V := zeroExtendedInnerBody F G)
    · intro q hq
      have hq' := (mem_productiveFiber_iff F G (F.parent i) q).mp hq
      rw [zeroExtendedInnerBody_toConvexSpaceBody F G hcarrier]
      simpa [hq'.2.2] using F.inner_le_parent q hq'.1
    · apply Metric.self_subset_cthickening
      have hi' := (mem_productiveFinalInnerSet_iff F G i).mp hi
      exact Set.mem_iUnion₂.mpr ⟨i,
        (mem_productiveFiber_iff F G (F.parent i) i).mpr ⟨hi'.1, hi'.2, rfl⟩, hxi⟩

@[simp]
theorem productiveCountingFamily_outerSet (F : FactorFamily E ι κ)
    (G : ShadedFactorFamily E ι κ)
    (hcarrier : ∀ i, (G.innerBody i).toConvexSpaceBody =
      (F.innerBody i).toConvexSpaceBody) (hparent : G.parent = F.parent) :
    (productiveCountingFamily F G hcarrier hparent).outerSet = productiveOuterSet G := rfl

/-- A counting-family outer shade is the corresponding final zero-extended fiber union. -/
@[simp]
theorem productiveCountingFamily_outerBody_shade (F : FactorFamily E ι κ)
    (G : ShadedFactorFamily E ι κ)
    (hcarrier : ∀ i, (G.innerBody i).toConvexSpaceBody =
      (F.innerBody i).toConvexSpaceBody) (hparent : G.parent = F.parent) (j : κ) :
    ((productiveCountingFamily F G hcarrier hparent).outerBody j).shade =
      iUnionShade (productiveFiber F G j) (zeroExtendedInnerBody F G) := rfl

@[simp]
theorem productiveThickFamily_outerSet (F : FactorFamily E ι κ)
    (G : ShadedFactorFamily E ι κ)
    (hcarrier : ∀ i, (G.innerBody i).toConvexSpaceBody =
      (F.innerBody i).toConvexSpaceBody) (hparent : G.parent = F.parent) :
    (productiveThickFamily F G hcarrier hparent).outerSet = productiveOuterSet G := rfl

/-- A thick-family outer carrier is the original outer carrier enlarged by its own shortest
scale. -/
@[simp]
theorem productiveThickFamily_outerBody_toConvexSpaceBody (F : FactorFamily E ι κ)
    (G : ShadedFactorFamily E ι κ)
    (hcarrier : ∀ i, (G.innerBody i).toConvexSpaceBody =
      (F.innerBody i).toConvexSpaceBody) (hparent : G.parent = F.parent) (j : κ) :
    ((productiveThickFamily F G hcarrier hparent).outerBody j).toConvexSpaceBody =
      (F.outerBody j).cthickening (F.outerBody j).scale := by
  rfl

@[simp]
theorem productiveCountingFamily_innerSet (F : FactorFamily E ι κ)
    (G : ShadedFactorFamily E ι κ)
    (hcarrier : ∀ i, (G.innerBody i).toConvexSpaceBody =
      (F.innerBody i).toConvexSpaceBody) (hparent : G.parent = F.parent) :
    (productiveCountingFamily F G hcarrier hparent).innerSet =
      productiveFinalInnerSet F G := rfl

@[simp]
theorem productiveThickFamily_innerSet (F : FactorFamily E ι κ)
    (G : ShadedFactorFamily E ι κ)
    (hcarrier : ∀ i, (G.innerBody i).toConvexSpaceBody =
      (F.innerBody i).toConvexSpaceBody) (hparent : G.parent = F.parent) :
    (productiveThickFamily F G hcarrier hparent).innerSet =
      productiveFinalInnerSet F G := rfl

@[simp]
theorem productiveCountingFamily_innerBody (F : FactorFamily E ι κ)
    (G : ShadedFactorFamily E ι κ)
    (hcarrier : ∀ i, (G.innerBody i).toConvexSpaceBody =
      (F.innerBody i).toConvexSpaceBody) (hparent : G.parent = F.parent) :
    (productiveCountingFamily F G hcarrier hparent).innerBody =
      zeroExtendedInnerBody F G := rfl

@[simp]
theorem productiveThickFamily_innerBody (F : FactorFamily E ι κ)
    (G : ShadedFactorFamily E ι κ)
    (hcarrier : ∀ i, (G.innerBody i).toConvexSpaceBody =
      (F.innerBody i).toConvexSpaceBody) (hparent : G.parent = F.parent) :
    (productiveThickFamily F G hcarrier hparent).innerBody =
      zeroExtendedInnerBody F G := rfl

open Classical in
/-- A final productive-family fiber is the complete original fiber over its productive block. -/
theorem productiveCountingFamily_fiber_eq (F : FactorFamily E ι κ)
    (G : ShadedFactorFamily E ι κ)
    (hcarrier : ∀ i, (G.innerBody i).toConvexSpaceBody =
      (F.innerBody i).toConvexSpaceBody) (hparent : G.parent = F.parent) (j : κ) :
    (productiveCountingFamily F G hcarrier hparent).fiber j = productiveFiber F G j := by
  ext i
  simp only [ShadedFactorFamily.fiber, Finset.mem_filter,
    productiveCountingFamily_innerSet, mem_productiveFinalInnerSet_iff,
    mem_productiveFiber_iff]
  constructor
  · rintro ⟨⟨hi, hj⟩, hp⟩
    exact ⟨hi, hj, hp⟩
  · rintro ⟨hi, hj, hp⟩
    exact ⟨⟨hi, hj⟩, hp⟩

open Classical in
/-- The thick productive family has the same complete productive fibers as the counting family. -/
theorem productiveThickFamily_fiber_eq (F : FactorFamily E ι κ)
    (G : ShadedFactorFamily E ι κ)
    (hcarrier : ∀ i, (G.innerBody i).toConvexSpaceBody =
      (F.innerBody i).toConvexSpaceBody) (hparent : G.parent = F.parent) (j : κ) :
    (productiveThickFamily F G hcarrier hparent).fiber j = productiveFiber F G j := by
  ext i
  simp only [ShadedFactorFamily.fiber, Finset.mem_filter,
    productiveThickFamily_innerSet, mem_productiveFinalInnerSet_iff,
    mem_productiveFiber_iff]
  constructor
  · rintro ⟨⟨hi, hj⟩, hp⟩
    exact ⟨hi, hj, hp⟩
  · rintro ⟨hi, hj, hp⟩
    exact ⟨⟨hi, hj⟩, hp⟩

/-- Counting and thick productive families have the same outer carrier. -/
theorem productiveCountingFamily_carrier_eq_productiveThickFamily
    (F : FactorFamily E ι κ) (G : ShadedFactorFamily E ι κ)
    (hcarrier : ∀ i, (G.innerBody i).toConvexSpaceBody = (F.innerBody i).toConvexSpaceBody)
    (hparent : G.parent = F.parent) (j : κ) :
    ((productiveCountingFamily F G hcarrier hparent).outerBody j).toConvexSpaceBody =
      ((productiveThickFamily F G hcarrier hparent).outerBody j).toConvexSpaceBody := rfl

/-- The exact counting shading is contained in the thick induced shading. -/
theorem productiveCountingFamily_shade_subset_productiveThickFamily
    (F : FactorFamily E ι κ) (G : ShadedFactorFamily E ι κ)
    (hcarrier : ∀ i, (G.innerBody i).toConvexSpaceBody = (F.innerBody i).toConvexSpaceBody)
    (hparent : G.parent = F.parent) (j : κ) :
    ((productiveCountingFamily F G hcarrier hparent).outerBody j).shade ⊆
      ((productiveThickFamily F G hcarrier hparent).outerBody j).shade := by
  intro x hx
  apply cthickening_scale_iUnionShade_subset_shade_inducedShading
    (s := productiveFiber F G j) (V := zeroExtendedInnerBody F G)
  · intro i hi
    have hi' := (mem_productiveFiber_iff F G j i).mp hi
    rw [zeroExtendedInnerBody_toConvexSpaceBody F G hcarrier]
    simpa [hi'.2.2] using F.inner_le_parent i hi'.1
  · exact Metric.self_subset_cthickening _ hx

open Classical in
/-- The counting outer union is exactly the zero-extended productive inner union. -/
theorem iUnionShade_productiveCountingFamily_eq_inner
    (F : FactorFamily E ι κ) (G : ShadedFactorFamily E ι κ)
    (hcarrier : ∀ i, (G.innerBody i).toConvexSpaceBody = (F.innerBody i).toConvexSpaceBody)
    (hparent : G.parent = F.parent) :
    iUnionShade (productiveCountingFamily F G hcarrier hparent).outerSet
        (productiveCountingFamily F G hcarrier hparent).outerBody =
      iUnionShade (productiveCountingFamily F G hcarrier hparent).innerSet
        (productiveCountingFamily F G hcarrier hparent).innerBody := by
  ext x
  constructor
  · rintro hx
    change x ∈ ⋃ j ∈ productiveOuterSet G,
      iUnionShade (productiveFiber F G j) (zeroExtendedInnerBody F G) at hx
    obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hxj
    have hi' := (mem_productiveFiber_iff F G j i).mp hi
    have hiFinal : i ∈ productiveFinalInnerSet F G :=
      (mem_productiveFinalInnerSet_iff F G i).mpr
        ⟨hi'.1, by simpa [hi'.2.2] using hj⟩
    exact Set.mem_iUnion₂.mpr ⟨i, hiFinal, hxi⟩
  · intro hx
    change x ∈ iUnionShade (productiveFinalInnerSet F G)
      (zeroExtendedInnerBody F G) at hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    have hi' := (mem_productiveFinalInnerSet_iff F G i).mp hi
    exact Set.mem_iUnion₂.mpr ⟨F.parent i, hi'.2,
      Set.mem_iUnion₂.mpr ⟨i,
        (mem_productiveFiber_iff F G (F.parent i) i).mpr ⟨hi'.1, hi'.2, rfl⟩, hxi⟩⟩

end ShadedBody
