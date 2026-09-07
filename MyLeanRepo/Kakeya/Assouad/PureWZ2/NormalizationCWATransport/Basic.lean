import MyLeanRepo.Kakeya.Assouad.PureWZ2.PropSticky
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12PureCWAReindex
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12NestedJohnCWATransport
import MyLeanRepo.Kakeya.Geometry.JohnEllipsoid.Transport
import MyLeanRepo.Kakeya.Assouad.PureWZ2.AffineMapVolumeTransport

/-!
# Pure CWA transport through rigid isometries

Given an affine isometry `e` and two tube families whose carriers are
related by `e`, transport the pure Definition 2.12 nearby-scale CWA.

## Submodules

- `Basic`: image constructions, geometric and cover transport
- `John`: John ellipsoid transport through affine isometries
- `Fiber`: unit-rescaled full fiber data transport
-/

noncomputable section

open MeasureTheory JohnEllipsoid

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

variable (e : Point3 ≃ᵃⁱ[ℝ] Point3)

/-! ### Helper lemmas -/

/-- An affine isometry distributes over addition with its linear part. -/
lemma affine_isometry_map_add (c v : Point3) :
    e (c + v) = e c + e.linearIsometryEquiv v := by
  have h := e.map_vadd c v
  have h1 : (v +ᵥ c) = c + v := by simp [vadd_eq_add, add_comm]
  have h2 : (e.linearIsometryEquiv v +ᵥ e c) = e c + e.linearIsometryEquiv v := by
    simp [vadd_eq_add, add_comm]
  rw [h1, h2] at h
  exact h

/-- Coerce an affine isometry to an affine equivalence. -/
abbrev affineIsometryToEquiv : Point3 ≃ᵃ[ℝ] Point3 := e

/-- The coercion agrees with the original map. -/
lemma affineIsometryToEquiv_apply (x : Point3) :
    affineIsometryToEquiv e x = e x := by rfl

/-- General helper: a measure-preserving equiv preserves volume of all sets. -/
lemma equiv_volume_image {f : Point3 ≃ Point3}
    (hpres : MeasurePreserving f volume volume)
    (hpres_symm : MeasurePreserving f.symm volume volume)
    (t : Set Point3) : volume (f '' t) = volume t := by
  have h_le1 : volume (f '' t) ≤ volume t := by
    have h : volume (f.symm ⁻¹' t) ≤ volume t := hpres_symm.measure_preimage_le t
    have h_eq : f.symm ⁻¹' t = f '' t := by
      ext x
      simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · intro hx
        exact ⟨f.symm x, hx, f.apply_symm_apply x⟩
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
    rw [h_eq] at h
    exact h
  have h_le2 : volume t ≤ volume (f '' t) := by
    have h : volume (f ⁻¹' (f '' t)) ≤ volume (f '' t) := hpres.measure_preimage_le (f '' t)
    have h_eq : f ⁻¹' (f '' t) = t := by
      ext x
      simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · intro hx
        rcases hx with ⟨y, hy, hxy⟩
        have : f x = f y := hxy.symm
        have : x = y := f.injective this
        rw [this]
        exact hy
      · intro hx
        exact ⟨x, hx, rfl⟩
    rw [h_eq] at h
    exact h
  exact le_antisymm h_le1 h_le2

/-- An affine isometry preserves Lebesgue volume. -/
lemma isometry_volume_image (s : Set Point3) :
    volume (e '' s) = volume s := by
  let v := e 0
  let f : Point3 ≃ₗᵢ[ℝ] Point3 := e.linearIsometryEquiv
  let f' : Point3 ≃ Point3 := f.toEquiv
  let g' : Point3 ≃ Point3 := Equiv.addLeft v
  have h_decomp : e '' s = g' '' (f' '' s) := by
    ext z
    simp only [Set.mem_image, Equiv.coe_addLeft]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h1 : e (0 + x) = e 0 + e.linearIsometryEquiv x := affine_isometry_map_add e 0 x
      have h_eq : e x = v + f x := by simpa [v, f] using h1
      exact ⟨f x, ⟨x, hx, rfl⟩, h_eq.symm⟩
    · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
      have h1 : e (0 + x) = e 0 + e.linearIsometryEquiv x := affine_isometry_map_add e 0 x
      have h_eq : e x = v + f x := by simpa [v, f] using h1
      exact ⟨x, hx, h_eq⟩
  rw [h_decomp]
  have hpres_g : MeasurePreserving g' volume volume :=
    MeasureTheory.measurePreserving_add_left volume v
  have hpres_g_symm : MeasurePreserving g'.symm volume volume :=
    MeasureTheory.measurePreserving_add_left volume (-v)
  have h_g : volume (g' '' (f' '' s)) = volume (f' '' s) :=
    equiv_volume_image hpres_g hpres_g_symm (f' '' s)
  rw [h_g]
  have hpres_f : MeasurePreserving f' volume volume :=
    LinearIsometryEquiv.measurePreserving f
  have hpres_f_symm : MeasurePreserving f'.symm volume volume :=
    LinearIsometryEquiv.measurePreserving f.symm
  exact equiv_volume_image hpres_f hpres_f_symm s

/-- `e.symm '' (e '' s) = s` for an affine isometry. -/
lemma symm_image_image (s : Set Point3) : e.symm '' (e '' s) = s := by
  ext z
  simp only [Set.mem_image]
  constructor
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    simpa [e.left_inv] using hx
  · intro hx
    exact ⟨e z, ⟨z, hx, rfl⟩, by simp⟩

/-! ### 1. Basic image constructions -/

/-- The image of a `DeltaTube` under an affine isometry. -/
def imageDeltaTube {δ : ℝ} (T : Kakeya.DeltaTube δ) : Kakeya.DeltaTube δ where
  base := e T.base
  direction := e.linearIsometryEquiv T.direction
  direction_unit := by
    have h : ‖e.linearIsometryEquiv T.direction‖ = ‖T.direction‖ :=
      e.linearIsometryEquiv.norm_map T.direction
    rw [h, T.direction_unit]

/-- The carrier of the image tube is the isometric image of the carrier. -/
theorem imageDeltaTube_carrier {δ : ℝ} (T : Kakeya.DeltaTube δ) :
    (imageDeltaTube e T).carrier = e '' T.carrier := by
  simp only [imageDeltaTube, Kakeya.DeltaTube.carrier]
  have hseg : e '' (Kakeya.unitSegment T.base T.direction) =
      Kakeya.unitSegment (e T.base) (e.linearIsometryEquiv T.direction) := by
    ext y
    simp only [Kakeya.unitSegment, Set.mem_image]
    constructor
    · rintro ⟨x, ⟨t, ht, rfl⟩, rfl⟩
      refine ⟨t, ht, ?_⟩
      have h : e (T.base + t • T.direction) =
          e T.base + t • e.linearIsometryEquiv T.direction :=
        (affine_isometry_map_add e T.base (t • T.direction)).trans
          (by rw [e.linearIsometryEquiv.map_smul])
      exact h.symm
    · rintro ⟨t, ht, rfl⟩
      refine ⟨T.base + t • T.direction, ⟨t, ht, rfl⟩, ?_⟩
      exact (affine_isometry_map_add e T.base (t • T.direction)).trans
        (by rw [e.linearIsometryEquiv.map_smul])
  have hcthick : e '' (Metric.cthickening δ (Kakeya.unitSegment T.base T.direction)) =
      Metric.cthickening δ (e '' (Kakeya.unitSegment T.base T.direction)) := by
    ext y
    simp only [Metric.mem_cthickening_iff, Set.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h : Metric.infEDist (e x) (e '' (Kakeya.unitSegment T.base T.direction)) =
          Metric.infEDist x (Kakeya.unitSegment T.base T.direction) :=
        Metric.infEDist_image e.isometry
      rw [h] <;> exact hx
    · intro hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      have h' : Metric.infEDist y (e '' (Kakeya.unitSegment T.base T.direction)) =
          Metric.infEDist (e.symm y) (Kakeya.unitSegment T.base T.direction) := by
        have h_i := Metric.infEDist_image e.isometry (x := e.symm y)
          (t := Kakeya.unitSegment T.base T.direction)
        simpa [e.apply_symm_apply] using h_i
      exact h'.symm ▸ hy
  rw [hcthick, hseg]

/-- The image of a tube family under an affine isometry. -/
abbrev imageTubeFamily {δ : ℝ} (F : Kakeya.Streamlined.TubeFamily δ) :
    Kakeya.Streamlined.TubeFamily δ where
  card := F.card
  tube i := imageDeltaTube e (F.tube i)

theorem imageTubeFamily_carrier {δ : ℝ} (F : Kakeya.Streamlined.TubeFamily δ)
    (i : Fin F.card) :
    ((imageTubeFamily e F).tube i).carrier = e '' (F.tube i).carrier :=
  imageDeltaTube_carrier e (F.tube i)

/-! ### 2. Geometric transport -/

/-- Centered dilation carrier transports through isometries. -/
theorem centeredDilatedCarrier_image {ρ : ℝ} (factor : ℝ)
    (T : Kakeya.DeltaTube ρ) :
    e '' (wz2PaperCenteredDilatedCarrier factor T) =
      wz2PaperCenteredDilatedCarrier factor (imageDeltaTube e T) := by
  simp only [wz2PaperCenteredDilatedCarrier]
  have hmid : e (wz2PaperTubeMidpoint T) =
      wz2PaperTubeMidpoint (imageDeltaTube e T) := by
    simp only [wz2PaperTubeMidpoint, imageDeltaTube]
    exact (affine_isometry_map_add e T.base ((1 / 2 : ℝ) • T.direction)).trans
      (by rw [e.linearIsometryEquiv.map_smul])
  have hcomm : ∀ (c : Point3),
      e '' (AffineMap.homothety c factor '' T.carrier) =
        AffineMap.homothety (e c) factor '' (e '' T.carrier) := by
    intro c
    have h_eq : ∀ (x : Point3), e (AffineMap.homothety c factor x) =
        AffineMap.homothety (e c) factor (e x) := by
      intro x
      simp only [AffineMap.homothety_apply]
      have h1 := e.map_vadd c (factor • (x -ᵥ c))
      rw [h1]
      have h2 : e.linearIsometryEquiv (factor • (x -ᵥ c)) =
          factor • (e x -ᵥ e c) := by
        rw [e.linearIsometryEquiv.map_smul]
        have h3 : e.linearIsometryEquiv (x -ᵥ c) = e x -ᵥ e c :=
          e.map_vsub x c
        rw [h3]
      rw [h2]
    ext z
    simp only [Set.mem_image]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rcases hy with ⟨x, hx, rfl⟩
      exact ⟨e x, ⟨x, hx, rfl⟩, (h_eq x).symm⟩
    · rintro ⟨w, hw, rfl⟩
      rcases hw with ⟨x, hx, rfl⟩
      refine ⟨AffineMap.homothety c factor x, ⟨x, hx, rfl⟩, ?_⟩
      exact h_eq x
  rw [hcomm (wz2PaperTubeMidpoint T), hmid]
  rw [imageDeltaTube_carrier e T]

/-- Full fiber index sets are preserved by isometric imaging. -/
theorem fullFiberIndices_image
    {δ ρ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    {G : Kakeya.Streamlined.TubeFamily ρ} (parent : Fin G.card) :
    wz2PaperOrdinaryFullFiberIndices (imageTubeFamily e F) (imageTubeFamily e G) parent =
    wz2PaperOrdinaryFullFiberIndices F G parent := by
  ext i
  rw [mem_wz2PaperOrdinaryFullFiberIndices_iff, mem_wz2PaperOrdinaryFullFiberIndices_iff]
  rw [imageTubeFamily_carrier e F i, imageTubeFamily_carrier e G parent]
  exact Set.image_subset_image_iff e.toEquiv.injective

/-- Dilated fiber index sets are preserved by isometric imaging. -/
theorem dilatedFiberIndices_image
    {δ ρ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    {G : Kakeya.Streamlined.TubeFamily ρ} (factor : ℝ) (parent : Fin G.card) :
    wz2PaperOrdinaryDilatedFiberIndices factor (imageTubeFamily e F) (imageTubeFamily e G) parent =
    wz2PaperOrdinaryDilatedFiberIndices factor F G parent := by
  ext i
  rw [mem_wz2PaperOrdinaryDilatedFiberIndices_iff, mem_wz2PaperOrdinaryDilatedFiberIndices_iff]
  rw [imageTubeFamily_carrier e F i]
  rw [← centeredDilatedCarrier_image e factor (G.tube parent)]
  exact Set.image_subset_image_iff e.toEquiv.injective

/-- Ordinary essential distinctness transports through isometries. -/
theorem essentialDistinct_image
    {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    (h : WZ2PaperOrdinaryIsEssentiallyDistinct F) :
    WZ2PaperOrdinaryIsEssentiallyDistinct (imageTubeFamily e F) := by
  let F' := imageTubeFamily e F
  intro first second hne
  have h1 := h first second hne
  constructor
  · by_contra h2
    have h3 : e.symm '' (F'.tube first).carrier ⊆
        e.symm '' (wz2PaperCenteredDilatedCarrier 2 (F'.tube second)) := by
      intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      exact ⟨x, h2 hx, rfl⟩
    have h4 : e.symm '' (F'.tube first).carrier = (F.tube first).carrier := by
      rw [imageTubeFamily_carrier e F first]
      exact symm_image_image e _
    have h5 : e.symm '' (wz2PaperCenteredDilatedCarrier 2 (F'.tube second)) =
        wz2PaperCenteredDilatedCarrier 2 (F.tube second) := by
      rw [← centeredDilatedCarrier_image e 2 (F.tube second)]
      exact symm_image_image e _
    rw [h4, h5] at h3
    exact h1.1 h3
  · by_contra h2
    have h3 : e.symm '' (F'.tube second).carrier ⊆
        e.symm '' (wz2PaperCenteredDilatedCarrier 2 (F'.tube first)) := by
      intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      exact ⟨x, h2 hx, rfl⟩
    have h4 : e.symm '' (F'.tube second).carrier = (F.tube second).carrier := by
      rw [imageTubeFamily_carrier e F second]
      exact symm_image_image e _
    have h5 : e.symm '' (wz2PaperCenteredDilatedCarrier 2 (F'.tube first)) =
        wz2PaperCenteredDilatedCarrier 2 (F.tube first) := by
      rw [← centeredDilatedCarrier_image e 2 (F.tube first)]
      exact symm_image_image e _
    rw [h4, h5] at h3
    exact h1.2 h3

/-! ### 3. Cover transport -/

/-- Pure partitioning cover transports through isometries. -/
theorem purePartitioningCover_image
    {δ ρ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    {G : Kakeya.Streamlined.TubeFamily ρ}
    (cover : WZ2PaperPurePartitioningCover F G) :
    WZ2PaperPurePartitioningCover (imageTubeFamily e F) (imageTubeFamily e G) where
  covers source := by
    rcases cover.covers source with ⟨parent, hparent⟩
    refine ⟨parent, ?_⟩
    rw [mem_wz2PaperOrdinaryFullFiberIndices_iff] at hparent ⊢
    rw [imageTubeFamily_carrier e F source, imageTubeFamily_carrier e G parent]
    have himg : e '' (F.tube source).carrier ⊆ e '' (G.tube parent).carrier := by
      intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      exact ⟨x, hparent hx, rfl⟩
    exact himg
  doubled_fibers_disjoint first second hne := by
    have h1 := cover.doubled_fibers_disjoint first second hne
    have h_eq1 : wz2PaperOrdinaryDilatedFiberIndices 2 (imageTubeFamily e F) (imageTubeFamily e G) first =
        wz2PaperOrdinaryDilatedFiberIndices 2 F G first := by
      exact dilatedFiberIndices_image (G := G) e 2 first
    have h_eq2 : wz2PaperOrdinaryDilatedFiberIndices 2 (imageTubeFamily e F) (imageTubeFamily e G) second =
        wz2PaperOrdinaryDilatedFiberIndices 2 F G second := by
      exact dilatedFiberIndices_image (G := G) e 2 second
    rw [h_eq1, h_eq2]
    exact h1

/-- Full fiber uniformity transports through isometries. -/
theorem fullFiberUniform_image
    {δ ρ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    {G : Kakeya.Streamlined.TubeFamily ρ} {C : ENNReal}
    (h : WZ2PaperPureFullFibersAreCUniform F G C) :
    WZ2PaperPureFullFibersAreCUniform (imageTubeFamily e F) (imageTubeFamily e G) C := by
  intro first second
  have h_eq1 : wz2PaperOrdinaryFullFiberIndices (imageTubeFamily e F) (imageTubeFamily e G) first =
      wz2PaperOrdinaryFullFiberIndices F G first := by
    exact fullFiberIndices_image (G := G) e first
  have h_eq2 : wz2PaperOrdinaryFullFiberIndices (imageTubeFamily e F) (imageTubeFamily e G) second =
      wz2PaperOrdinaryFullFiberIndices F G second := by
    exact fullFiberIndices_image (G := G) e second
  have h_count1 : wz2PaperOrdinaryFullFiberCount (imageTubeFamily e F) (imageTubeFamily e G) first =
      wz2PaperOrdinaryFullFiberCount F G first := by
    unfold wz2PaperOrdinaryFullFiberCount
    rw [h_eq1]
  have h_count2 : wz2PaperOrdinaryFullFiberCount (imageTubeFamily e F) (imageTubeFamily e G) second =
      wz2PaperOrdinaryFullFiberCount F G second := by
    unfold wz2PaperOrdinaryFullFiberCount
    rw [h_eq2]
  rw [h_count1, h_count2]
  exact h first second

end Kakeya.Assouad

end
