import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23ActualEdgeDotContainmentStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23SnappedFourCycleDotContainment

/-!
# Actual-edge dot containment in WZ1 Lemma 23
-/

namespace Kakeya.Assouad

theorem wz1_lemma23_actual_edge_dot_containment :
    WZ1Lemma23ActualEdgeDotContainmentStatement := by
  intro rho f g cells baseHeightIndex baseGlobalBin hrho
  dsimp only
  let baseCycles :=
    wz1Lemma23SnappedBaseCycles
      rho f g cells baseHeightIndex baseGlobalBin
  let edge :=
    wz1Lemma23SnappedTripartiteEdge
      rho f g baseHeightIndex
  let edges := baseCycles.image edge
  intro value hvalue
  change value ∈
    edges.image
      (fun h =>
        inner ℝ h.1 (h.2.1 - h.2.2)) at hvalue
  have hvalue' :
      value ∈
        edges.image
          (fun h =>
            inner ℝ h.1 (h.2.1 - h.2.2)) :=
    Finset.mem_coe.mp hvalue
  rcases Finset.mem_image.mp hvalue' with
    ⟨edgeValue, hedgeValue, rfl⟩
  rcases Finset.mem_image.mp hedgeValue with
    ⟨path, hpath, hedge⟩
  have hpath_all :
      path ∈ wz1Lemma23SnappedFourCycles rho f g cells :=
    (Finset.mem_filter.mp hpath).1
  have hbaseHeight :
      wz1Lemma23SnappedHeight path.1 = baseHeightIndex :=
    (Finset.mem_filter.mp hpath).2.1
  have hbaseBin :
      wz1Lemma23SnappedGlobalBin rho f path.1 =
        baseGlobalBin :=
    (Finset.mem_filter.mp hpath).2.2
  have hrelations :
      (path.1 ∈ cells ∧ path.2.1 ∈ cells ∧
        path.2.2.1 ∈ cells ∧ path.2.2.2 ∈ cells) ∧
      wz1Lemma23SameSnappedLocalGrain rho g
          path.1 path.2.1 ∧
      wz1Lemma23SameSnappedLocalGrain rho g
          path.2.2.2 path.2.2.1 ∧
      wz1Lemma23SnappedHeight path.1 =
          wz1Lemma23SnappedHeight path.2.2.2 ∧
      wz1Lemma23SnappedHeight path.2.1 =
          wz1Lemma23SnappedHeight path.2.2.1 ∧
      wz1Lemma23SnappedGlobalBin rho f path.2.1 =
          wz1Lemma23SnappedGlobalBin rho f path.2.2.1 := by
    simpa [wz1Lemma23SnappedFourCycles,
      wz1Lemma23FourCycles] using hpath_all
  let baseValue :=
    wz1Lemma23GlobalCoordinate f
      (wz1Lemma23SnappedPoint rho path.1)
  have hbaseValue :
      |baseValue - (baseGlobalBin : ℝ) * rho| < rho := by
    have hfloor :
        Int.floor (baseValue / rho) = baseGlobalBin := by
      simpa [baseValue, wz1Lemma23SnappedGlobalBin] using hbaseBin
    have hlower :
        (baseGlobalBin : ℝ) ≤ baseValue / rho := by
      simpa [hfloor] using Int.floor_le (baseValue / rho)
    have hupper :
        baseValue / rho < (baseGlobalBin : ℝ) + 1 := by
      simpa [hfloor] using Int.lt_floor_add_one (baseValue / rho)
    rw [abs_lt]
    constructor <;>
      field_simp [hrho.ne'] at hlower hupper ⊢ <;>
      nlinarith
  have hfourHeight :
      wz1Lemma23SnappedHeight path.2.2.2 =
        baseHeightIndex := by
    exact hrelations.2.2.2.1.symm.trans hbaseHeight
  have hbaseHeightIndex :
      path.1.2.2 = baseHeightIndex := by
    simpa [wz1Lemma23SnappedHeight] using hbaseHeight
  have hfourHeightIndex :
      path.2.2.2.2.2 = baseHeightIndex := by
    simpa [wz1Lemma23SnappedHeight] using hfourHeight
  have hbaseHeightReal :
      (wz1Lemma23SnappedPoint rho path.1) 2 =
        wz1Lemma23SnappedBaseHeight rho baseHeightIndex := by
    simp [wz1Lemma23SnappedPoint, wz1Lemma23CellCenter,
      wz1Lemma23SnappedBaseHeight, point3, hbaseHeightIndex]
  have hfourHeightReal :
      (wz1Lemma23SnappedPoint rho path.2.2.2) 2 =
        wz1Lemma23SnappedBaseHeight rho baseHeightIndex := by
    simp [wz1Lemma23SnappedPoint, wz1Lemma23CellCenter,
      wz1Lemma23SnappedBaseHeight, point3, hfourHeightIndex]
  let B := wz1Lemma23SnappedBaseHeight rho baseHeightIndex
  let q1 := wz1Lemma23SnappedPoint rho path.1
  let q2 := wz1Lemma23SnappedPoint rho path.2.1
  let q3 := wz1Lemma23SnappedPoint rho path.2.2.1
  let q4 := wz1Lemma23SnappedPoint rho path.2.2.2
  have hskew2 :
      (wz1Lemma23SkewPoint B f g q2) 2 = q2 2 - B := by
    simp [wz1Lemma23SkewPoint, point3]
  have hskew1_first :
      (wz1Lemma23SkewPoint B f g q1) 1 = q1 1 := by
    simp [wz1Lemma23SkewPoint, point3]
  have hskew1_third :
      (wz1Lemma23SkewPoint B f g q3) 1 = q3 1 := by
    simp [wz1Lemma23SkewPoint, point3]
  have hskew0_fourth :
      (wz1Lemma23SkewPoint B f g q4) 0 =
        wz1Lemma23GlobalCoordinate f q4 := by
    simp [wz1Lemma23SkewPoint, wz1Lemma23GlobalCoordinate,
      point3, q4, B, hfourHeightReal]
  have hdot :
      |inner ℝ
          (wz1Lemma23SnappedHeightPoint
            rho f baseHeightIndex path.2.1)
          (wz1Lemma23SnappedLocalPoint rho g path.1 -
            wz1Lemma23SnappedLocalPoint rho g path.2.2.1) -
        (wz1Lemma23GlobalCoordinate f
          (wz1Lemma23SnappedPoint rho path.2.2.2) -
            (baseGlobalBin : ℝ) * rho)| ≤
        4 * rho := by
    have h :=
      wz1_lemma23_snapped_four_cycle_dot_containment
        rho ((baseGlobalBin : ℝ) * rho) f g cells path
        hrho hpath_all (le_of_lt hbaseValue)
    dsimp only at h
    rw [hbaseHeightReal] at h
    rw [hskew2, hskew1_first, hskew1_third,
      hskew0_fourth] at h
    simpa [B, q1, q2, q3, q4,
      wz1Lemma23SnappedHeightPoint,
      wz1Lemma23SnappedLocalPoint] using h
  have hfourCell : path.2.2.2 ∈ cells :=
    hrelations.1.2.2.2
  have hbaseMember :
      wz1Lemma23GlobalCoordinate f
          (wz1Lemma23SnappedPoint rho path.2.2.2) -
            (baseGlobalBin : ℝ) * rho ∈
        wz1Lemma23SnappedBaseSliceValues
          rho f cells baseHeightIndex baseGlobalBin := by
    exact Finset.mem_image.mpr
      ⟨path.2.2.2,
        Finset.mem_filter.mpr ⟨hfourCell, hfourHeight⟩,
        rfl⟩
  have hedgeValue :
      edgeValue =
        wz1Lemma23SnappedTripartiteEdge
          rho f g baseHeightIndex path := hedge.symm
  rw [hedgeValue]
  exact Metric.mem_cthickening_of_dist_le
    (inner ℝ
      (wz1Lemma23SnappedHeightPoint
        rho f baseHeightIndex path.2.1)
      (wz1Lemma23SnappedLocalPoint rho g path.1 -
        wz1Lemma23SnappedLocalPoint rho g path.2.2.1))
    (wz1Lemma23GlobalCoordinate f
      (wz1Lemma23SnappedPoint rho path.2.2.2) -
        (baseGlobalBin : ℝ) * rho)
    (4 * rho)
    (wz1Lemma23SnappedBaseSliceValues
      rho f cells baseHeightIndex baseGlobalBin : Set ℝ)
    hbaseMember
    (by
      rw [Real.dist_eq]
      simpa [sub_eq_add_neg, add_assoc, add_left_comm,
        add_comm] using hdot)

end Kakeya.Assouad
