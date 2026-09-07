import MyLeanRepo.Kakeya.Assouad.PropStickyFullFiberHelpers

/-!
# Weakening lemmas for WZ2 `prop: sticky`

Increasing the allowed CWA constant or the extremal loss preserves the
corresponding cropped-paper predicates.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

private theorem realRpowENN_antitone
    {delta first second : ℝ}
    (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    (h : first ≤ second) :
    Kakeya.realRpowENN delta second ≤
      Kakeya.realRpowENN delta first := by
  apply ENNReal.ofReal_mono
  exact Real.rpow_le_rpow_of_exponent_ge
    hdelta hdelta_one h

noncomputable def WZ2PaperUnitRescaledFamilyData.mono
    {delta rho C₁ C₂ : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {parent : Fin coarse.card}
    {hrho : 0 < rho}
    (data :
      WZ2PaperUnitRescaledFamilyData
        cover parent hrho (ENNReal.ofReal C₁))
    (hC : ENNReal.ofReal C₁ ≤ ENNReal.ofReal C₂) :
    WZ2PaperUnitRescaledFamilyData
      cover parent hrho (ENNReal.ofReal C₂) where
  targetFamily := data.targetFamily
  sourceIndex := data.sourceIndex
  sourceIndex_mem := data.sourceIndex_mem
  sourceIndex_injective := data.sourceIndex_injective
  sourceIndex_surjective := data.sourceIndex_surjective
  target_axis := data.target_axis
  target_line_class := data.target_line_class
  convex_wolff := fun convexSet hconvex =>
    (data.convex_wolff convexSet hconvex).trans (by
      gcongr)

theorem WZ2PaperCWAAtEveryScale.mono
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {C₁ C₂ : ENNReal}
    (hC : C₁ ≤ C₂)
    (h : WZ2PaperCWAAtEveryScale family C₁) :
    WZ2PaperCWAAtEveryScale family C₂ := by
  refine ⟨h.1.trans hC, h.2.1, h.2.2.1, ?_⟩
  intro rho
  rcases h.2.2.2 rho with ⟨data⟩
  refine ⟨{
    rho_pos := data.rho_pos
    coarse := data.coarse
    cover := data.cover
    coarse_line_class := data.coarse_line_class
    coarse_essentially_distinct :=
      data.coarse_essentially_distinct
    full_fiber_uniform := ?_
    rescaledFiber := ?_ }⟩
  · intro first second
    exact (data.full_fiber_uniform first second).trans (by
      gcongr)
  · intro parent
    rcases data.rescaledFiber parent with ⟨fiber⟩
    refine ⟨{
      targetFamily := fiber.targetFamily
      sourceIndex := fiber.sourceIndex
      sourceIndex_mem := fiber.sourceIndex_mem
      sourceIndex_injective := fiber.sourceIndex_injective
      sourceIndex_surjective := fiber.sourceIndex_surjective
      target_axis := fiber.target_axis
      target_line_class := fiber.target_line_class
      convex_wolff := fun convexSet hconvex =>
        (fiber.convex_wolff convexSet hconvex).trans (by
          gcongr) }⟩

/-- Increase the constant in one exact-scale cover witness. -/
noncomputable def WZ2PaperScaleCoverData.mono
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    {C₁ C₂ : ENNReal}
    (data : WZ2PaperScaleCoverData family rho C₁)
    (hC : C₁ ≤ C₂) :
    WZ2PaperScaleCoverData family rho C₂ where
  rho_pos := data.rho_pos
  coarse := data.coarse
  cover := data.cover
  coarse_line_class := data.coarse_line_class
  coarse_essentially_distinct :=
    data.coarse_essentially_distinct
  full_fiber_uniform first second :=
    (data.full_fiber_uniform first second).trans (by
      gcongr)
  rescaledFiber parent := by
    rcases data.rescaledFiber parent with ⟨fiber⟩
    exact
      ⟨{
        targetFamily := fiber.targetFamily
        sourceIndex := fiber.sourceIndex
        sourceIndex_mem := fiber.sourceIndex_mem
        sourceIndex_injective := fiber.sourceIndex_injective
        sourceIndex_surjective := fiber.sourceIndex_surjective
        target_axis := fiber.target_axis
        target_line_class := fiber.target_line_class
        convex_wolff := fun convexSet hconvex =>
          (fiber.convex_wolff convexSet hconvex).trans (by
            gcongr) }⟩

/-- Increase the constant in one assigned dilated unit-rescaled fiber. -/
noncomputable def WZ2PaperDilatedUnitRescaledFamilyData.mono
    {factor delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperDilatedTubeCover factor fine coarse}
    {parent : Fin coarse.card}
    {hrho : 0 < rho}
    {C₁ C₂ : ENNReal}
    (data :
      WZ2PaperDilatedUnitRescaledFamilyData
        cover parent hrho C₁)
    (hC : C₁ ≤ C₂) :
    WZ2PaperDilatedUnitRescaledFamilyData
      cover parent hrho C₂ where
  targetFamily := data.targetFamily
  sourceIndex := data.sourceIndex
  sourceIndex_mem := data.sourceIndex_mem
  sourceIndex_injective := data.sourceIndex_injective
  sourceIndex_surjective := data.sourceIndex_surjective
  target_axis := data.target_axis
  target_line_class := data.target_line_class
  convex_wolff convexSet hconvex :=
    (data.convex_wolff convexSet hconvex).trans (by
      gcongr)

/-- Increase the constant in one recursive dilated scale witness. -/
noncomputable def WZ2PaperDilatedScaleCoverData.mono
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {rho : ℝ}
    {C₁ C₂ : ENNReal}
    (data : WZ2PaperDilatedScaleCoverData family rho C₁)
    (hC : C₁ ≤ C₂) :
    WZ2PaperDilatedScaleCoverData family rho C₂ where
  rho_pos := data.rho_pos
  coarse := data.coarse
  cover := data.cover
  coarse_line_class := data.coarse_line_class
  coarse_essentially_distinct :=
    data.coarse_essentially_distinct
  assigned_fiber_uniform first second :=
    (data.assigned_fiber_uniform first second).trans (by
      gcongr)
  rescaledFiber parent := by
    rcases data.rescaledFiber parent with ⟨fiber⟩
    exact ⟨fiber.mono hC⟩

/-- Increase the constant in one literal strict full-fiber rescaling. -/
noncomputable def WZ2PaperLiteralFullFiberRescaledFamilyData.mono
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperLiteralDilatedPartitioningCover fine coarse}
    {parent : Fin coarse.card}
    {hrho : 0 < rho}
    {C₁ C₂ : ENNReal}
    (data :
      WZ2PaperLiteralFullFiberRescaledFamilyData
        cover parent hrho C₁)
    (hC : C₁ ≤ C₂) :
    WZ2PaperLiteralFullFiberRescaledFamilyData
      cover parent hrho C₂ where
  targetFamily := data.targetFamily
  sourceIndex := data.sourceIndex
  sourceIndex_mem := data.sourceIndex_mem
  sourceIndex_injective := data.sourceIndex_injective
  sourceIndex_surjective := data.sourceIndex_surjective
  target_axis := data.target_axis
  target_line_class := data.target_line_class
  convex_wolff convexSet hconvex :=
    (data.convex_wolff convexSet hconvex).trans (by gcongr)

/--
Forget the literal provenance of one complete strict full-fiber rescaling.

This adapter is safe because `literalFullFiberIndices_eq` proves that the
auxiliary assigned fiber of a carrier-faithful literal cover is exactly its
paper strict full fiber.
-/
noncomputable def
    WZ2PaperLiteralFullFiberRescaledFamilyData.toAssigned
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperLiteralDilatedPartitioningCover fine coarse}
    {parent : Fin coarse.card}
    {hrho : 0 < rho}
    {C : ENNReal}
    (data :
      WZ2PaperLiteralFullFiberRescaledFamilyData
        cover parent hrho C) :
    WZ2PaperDilatedUnitRescaledFamilyData
      cover.toWZ2PaperDilatedTubeCover parent hrho C where
  targetFamily := data.targetFamily
  sourceIndex := data.sourceIndex
  sourceIndex_mem target := by
    change
      data.sourceIndex target ∈
        WZ2PaperLiteralDilatedPartitioningCover.fiberIndices
          cover parent
    rw [← cover.literalFullFiberIndices_eq parent]
    exact data.sourceIndex_mem target
  sourceIndex_injective := data.sourceIndex_injective
  sourceIndex_surjective source hsource := by
    change
      source ∈
        WZ2PaperLiteralDilatedPartitioningCover.fiberIndices
          cover parent at hsource
    rw [← cover.literalFullFiberIndices_eq parent] at hsource
    exact data.sourceIndex_surjective source hsource
  target_axis := data.target_axis
  target_line_class := data.target_line_class
  convex_wolff := data.convex_wolff

/-- Increase the constant in one carrier-faithful literal scale witness. -/
noncomputable def WZ2PaperLiteralScaleCoverData.mono
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {rho : ℝ}
    {C₁ C₂ : ENNReal}
    (data : WZ2PaperLiteralScaleCoverData family rho C₁)
    (hC : C₁ ≤ C₂) :
    WZ2PaperLiteralScaleCoverData family rho C₂ where
  rho_pos := data.rho_pos
  coarse := data.coarse
  cover := data.cover
  coarse_line_class := data.coarse_line_class
  coarse_essentially_distinct :=
    data.coarse_essentially_distinct
  full_fiber_uniform first second :=
    (data.full_fiber_uniform first second).trans (by gcongr)
  rescaledFiber parent := by
    rcases data.rescaledFiber parent with ⟨fiber⟩
    exact ⟨fiber.mono hC⟩

/-- A strict partitioning cover is in particular a factor-two assigned cover. -/
noncomputable def WZ2PaperPartitioningCover.toDilatedTwo
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (hrho : 0 < rho) :
    WZ2PaperDilatedTubeCover 2 fine coarse where
  parent := cover.parent
  parent_surjective := cover.parent_surjective
  parent_covers index := by
    have hcover := cover.parent_covers index
    unfold WZ1PaperTubeCovers at hcover
    unfold WZ2PaperDilatedTubeCovers
    exact hcover.trans (by linarith)

/-- Assigned factor-two fibers coincide with strict full geometric fibers. -/
theorem WZ2PaperPartitioningCover.toDilatedTwo_fiberIndices
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (hrho : 0 < rho)
    (parent : Fin coarse.card) :
    (cover.toDilatedTwo hrho).fiberIndices parent =
      wz2PaperFullFiberIndices fine coarse parent := by
  ext source
  constructor
  · intro hsource
    have hparent :
        cover.parent source = parent :=
      (Finset.mem_filter.mp hsource).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ source, ?_⟩
    rw [← hparent]
    exact cover.parent_covers source
  · intro hsource
    have hcovers :
        WZ1PaperTubeCovers
          (fine.tube source) (coarse.tube parent) :=
      (Finset.mem_filter.mp hsource).2
    have hparent :
        parent = cover.parent source :=
      cover.parent_unique source parent hcovers
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ source, hparent.symm⟩

/-- A strict partitioning cover is a carrier-faithful recursive cover with
the same parent assignment. -/
noncomputable def WZ2PaperPartitioningCover.toLiteralDilated
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (hrho : 0 < rho) :
    WZ2PaperLiteralDilatedPartitioningCover fine coarse where
  toWZ2PaperDilatedTubeCover := cover.toDilatedTwo hrho
  parent_carrier_covers := cover.parent_carrier_covers
  literal_parent_unique := cover.literal_parent_unique
  literal_doubled_fibers_disjoint :=
    cover.literal_doubled_fibers_disjoint

/-- Assigned fibers of the strict-to-literal adapter are exactly the literal
strict full fibers. -/
theorem WZ2PaperPartitioningCover.toLiteralDilated_fiberIndices
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (hrho : 0 < rho)
    (parent : Fin coarse.card) :
    (cover.toLiteralDilated hrho).fiberIndices parent =
      wz2PaperLiteralFullFiberIndices fine coarse parent := by
  change (cover.toDilatedTwo hrho).fiberIndices parent =
    wz2PaperLiteralFullFiberIndices fine coarse parent
  rw [cover.toDilatedTwo_fiberIndices hrho parent,
    ← cover.literalFullFiber_eq_fullFiber parent]

/-- Convert one strict full-fiber rescaling to the literal recursive API. -/
noncomputable def WZ2PaperUnitRescaledFamilyData.toLiteralDilated
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {parent : Fin coarse.card}
    {hrho : 0 < rho}
    {C₁ C₂ : ENNReal}
    (fiber :
      WZ2PaperUnitRescaledFamilyData cover parent hrho C₁)
    (hC : C₁ ≤ C₂) :
    WZ2PaperLiteralFullFiberRescaledFamilyData
      (cover.toLiteralDilated hrho) parent hrho C₂ where
  targetFamily := fiber.targetFamily
  sourceIndex := fiber.sourceIndex
  sourceIndex_mem target := by
    rw [cover.literalFullFiber_eq_fullFiber parent]
    exact fiber.sourceIndex_mem target
  sourceIndex_injective := fiber.sourceIndex_injective
  sourceIndex_surjective source hsource := by
    rw [cover.literalFullFiber_eq_fullFiber parent] at hsource
    exact fiber.sourceIndex_surjective source hsource
  target_axis := fiber.target_axis
  target_line_class := fiber.target_line_class
  convex_wolff convexSet hconvex :=
    (fiber.convex_wolff convexSet hconvex).trans (by gcongr)

/-- Convert one strict scale witness to the literal recursive API. -/
noncomputable def WZ2PaperScaleCoverData.toLiteralScale
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    {C₁ C₂ : ENNReal}
    (data : WZ2PaperScaleCoverData family rho C₁)
    (hC : C₁ ≤ C₂) :
    WZ2PaperLiteralScaleCoverData family rho C₂ where
  rho_pos := data.rho_pos
  coarse := data.coarse
  cover := data.cover.toLiteralDilated data.rho_pos
  coarse_line_class := data.coarse_line_class
  coarse_essentially_distinct :=
    data.coarse_essentially_distinct
  full_fiber_uniform first second := by
    rw [data.cover.literalFullFiberCount_eq first,
      data.cover.literalFullFiberCount_eq second]
    exact (data.full_fiber_uniform first second).trans (by gcongr)
  rescaledFiber parent := by
    rcases data.rescaledFiber parent with ⟨fiber⟩
    exact ⟨fiber.toLiteralDilated hC⟩

/-- View one strict full-fiber rescaling in the assigned dilated semantics. -/
noncomputable def WZ2PaperUnitRescaledFamilyData.toDilatedTwo
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {parent : Fin coarse.card}
    {hrho : 0 < rho}
    {C₁ C₂ : ENNReal}
    (fiber :
      WZ2PaperUnitRescaledFamilyData
        cover parent hrho C₁)
    (hC : C₁ ≤ C₂) :
    WZ2PaperDilatedUnitRescaledFamilyData
      (cover.toDilatedTwo hrho) parent hrho C₂ where
  targetFamily := fiber.targetFamily
  sourceIndex := fiber.sourceIndex
  sourceIndex_mem target := by
    rw [cover.toDilatedTwo_fiberIndices hrho parent]
    exact fiber.sourceIndex_mem target
  sourceIndex_injective := fiber.sourceIndex_injective
  sourceIndex_surjective source hsource := by
    rw [cover.toDilatedTwo_fiberIndices hrho parent] at hsource
    exact fiber.sourceIndex_surjective source hsource
  target_axis := fiber.target_axis
  target_line_class := fiber.target_line_class
  convex_wolff convexSet hconvex :=
    (fiber.convex_wolff convexSet hconvex).trans (by
      gcongr)

/-- Convert one strict exact-scale witness to the recursive dilated semantics. -/
noncomputable def WZ2PaperScaleCoverData.toDilatedTwo
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    {C₁ C₂ : ENNReal}
    (data : WZ2PaperScaleCoverData family rho C₁)
    (hC : C₁ ≤ C₂) :
    WZ2PaperDilatedScaleCoverData family rho.1 C₂ where
  rho_pos := data.rho_pos
  coarse := data.coarse
  cover := data.cover.toDilatedTwo data.rho_pos
  coarse_line_class := data.coarse_line_class
  coarse_essentially_distinct :=
    data.coarse_essentially_distinct
  assigned_fiber_uniform first second := by
    unfold WZ2PaperDilatedTubeCover.fiberCount
    rw [
      data.cover.toDilatedTwo_fiberIndices data.rho_pos first,
      data.cover.toDilatedTwo_fiberIndices data.rho_pos second]
    have huniform := data.full_fiber_uniform first second
    simp only [wz2PaperFullFiberCount] at huniform
    exact huniform.trans (mul_le_mul_right' hC _)
  rescaledFiber parent := by
    rcases data.rescaledFiber parent with ⟨fiber⟩
    exact ⟨fiber.toDilatedTwo hC⟩

/--
The stronger exact-scale convention implies the literal nearby-scale paper
condition after a strict enlargement of the allowed constant.
-/
theorem WZ2PaperCWAAtEveryScale.toNearbyScales
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {C₁ C₂ : ENNReal}
    (hC : C₁ < C₂)
    (data : WZ2PaperCWAAtEveryScale family C₁) :
    WZ2PaperCWAAtNearbyScales family C₂ := by
  have hone : 1 < C₂ := data.1.trans_lt hC
  refine ⟨data.1.trans hC.le, data.2.1, data.2.2.1, ?_⟩
  intro rho₀
  rcases data.2.2.2 rho₀ with ⟨scaleData⟩
  have hrho_pos : 0 < ENNReal.ofReal rho₀.1 := by
    exact ENNReal.ofReal_pos.mpr scaleData.rho_pos
  have hrho_top : ENNReal.ofReal rho₀.1 ≠ ⊤ := by
    simp
  refine
    ⟨{
      rho := rho₀.1
      rho_pos := scaleData.rho_pos
      requested_le := le_rfl
      within_factor := ?_
      scaleData := scaleData.toLiteralScale hC.le }⟩
  calc
    ENNReal.ofReal rho₀.1 =
        1 * ENNReal.ofReal rho₀.1 := by simp
    _ < C₂ * ENNReal.ofReal rho₀.1 :=
      by
        simpa [mul_comm] using
          ENNReal.mul_lt_mul_right hrho_pos.ne' hrho_top hone

/-- Increasing the allowed constant preserves nearby-scale paper CWA. -/
theorem WZ2PaperCWAAtNearbyScales.mono
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {C₁ C₂ : ENNReal}
    (hC : C₁ ≤ C₂)
    (data : WZ2PaperCWAAtNearbyScales family C₁) :
    WZ2PaperCWAAtNearbyScales family C₂ := by
  refine ⟨data.1.trans hC, data.2.1, data.2.2.1, ?_⟩
  intro rho₀
  rcases data.2.2.2 rho₀ with ⟨nearby⟩
  refine
    ⟨{
      rho := nearby.rho
      rho_pos := nearby.rho_pos
      requested_le := nearby.requested_le
      within_factor := nearby.within_factor.trans_le (by
        gcongr)
      scaleData := nearby.scaleData.mono hC }⟩

/-- Forget top-level essential distinctness and retain all every-scale data. -/
theorem WZ2PaperCWAAtEveryScale.toCoversAtEveryScale
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    (data : WZ2PaperCWAAtEveryScale family C) :
    WZ2PaperCWACoversAtEveryScale family C :=
  ⟨data.1, data.2.1, data.2.2.2⟩

/-- Forget top-level distinctness in the nearby-scale paper condition. -/
theorem WZ2PaperCWAAtNearbyScales.toCoversAtNearbyScales
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    (data : WZ2PaperCWAAtNearbyScales family C) :
    WZ2PaperCWACoversAtNearbyScales family C :=
  ⟨data.1, data.2.1, data.2.2.2⟩

/-- Increasing the allowed constant preserves raw every-scale cover data. -/
theorem WZ2PaperCWACoversAtEveryScale.mono
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {C₁ C₂ : ENNReal}
    (hC : C₁ ≤ C₂)
    (data : WZ2PaperCWACoversAtEveryScale family C₁) :
    WZ2PaperCWACoversAtEveryScale family C₂ := by
  refine ⟨data.1.trans hC, data.2.1, ?_⟩
  intro rho
  rcases data.2.2 rho with ⟨scaleData⟩
  refine
    ⟨{
      rho_pos := scaleData.rho_pos
      coarse := scaleData.coarse
      cover := scaleData.cover
      coarse_line_class := scaleData.coarse_line_class
      coarse_essentially_distinct :=
        scaleData.coarse_essentially_distinct
      full_fiber_uniform := ?_
      rescaledFiber := ?_ }⟩
  · intro first second
    exact (scaleData.full_fiber_uniform first second).trans (by
      gcongr)
  · intro parent
    rcases scaleData.rescaledFiber parent with ⟨fiber⟩
    refine
      ⟨{
        targetFamily := fiber.targetFamily
        sourceIndex := fiber.sourceIndex
        sourceIndex_mem := fiber.sourceIndex_mem
        sourceIndex_injective := fiber.sourceIndex_injective
        sourceIndex_surjective := fiber.sourceIndex_surjective
        target_axis := fiber.target_axis
        target_line_class := fiber.target_line_class
        convex_wolff := fun convexSet hconvex =>
          (fiber.convex_wolff convexSet hconvex).trans (by
            gcongr) }⟩

/-- Increasing the constant preserves hereditary nearby-scale covers. -/
theorem WZ2PaperCWACoversAtNearbyScales.mono
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {C₁ C₂ : ENNReal}
    (hC : C₁ ≤ C₂)
    (data : WZ2PaperCWACoversAtNearbyScales family C₁) :
    WZ2PaperCWACoversAtNearbyScales family C₂ := by
  refine ⟨data.1.trans hC, data.2.1, ?_⟩
  intro rho₀
  rcases data.2.2 rho₀ with ⟨nearby⟩
  refine
    ⟨{
      rho := nearby.rho
      rho_pos := nearby.rho_pos
      requested_le := nearby.requested_le
      within_factor := nearby.within_factor.trans_le (by
        gcongr)
      scaleData := nearby.scaleData.mono hC }⟩

theorem WZ2PaperIsExtremal.mono_loss
    {delta sigma firstLoss secondLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (data :
      WZ2PaperIsExtremal
        sigma firstLoss family shading)
    (hloss : firstLoss ≤ secondLoss) :
    WZ2PaperIsExtremal
      sigma secondLoss family shading := by
  have hcwaPower :
      Kakeya.realRpowENN delta (-firstLoss) ≤
        Kakeya.realRpowENN delta (-secondLoss) :=
    realRpowENN_antitone data.delta_pos data.delta_le_one
      (by linarith)
  have hdensePower :
      Kakeya.realRpowENN delta secondLoss ≤
        Kakeya.realRpowENN delta firstLoss :=
    realRpowENN_antitone data.delta_pos data.delta_le_one hloss
  have hvolumePower :
      Kakeya.realRpowENN delta (sigma - firstLoss) ≤
        Kakeya.realRpowENN delta (sigma - secondLoss) :=
    realRpowENN_antitone data.delta_pos data.delta_le_one
      (by linarith)
  exact
    { delta_pos := data.delta_pos
      delta_le_one := data.delta_le_one
      nonempty := data.nonempty
      cwa_nearby_scales :=
        data.cwa_nearby_scales.mono hcwaPower
      cubical := data.cubical
      dense :=
        (mul_le_mul_right'
          hdensePower
          (wz1PaperBodyFamily family).mass).trans
          data.dense
      volume_upper := data.volume_upper.trans hvolumePower }

end Kakeya.Assouad
