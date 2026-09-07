import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.ADTransfer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.PaperADFiniteUnion

/-!
# Paper AD transfer from centered pieces and nearby normals

If a spatial piece lies in a ball centered at `center`, changing its scalar
projection normal from `normal` to a nearby `targetNormal` differs, after the
unique translation aligning the two projections of `center`, by at most the
ball radius times the distance between the normals.  This file records that
centered estimate, its paper-AD consequence, and the corresponding finite-union
wrapper for pieces with different source normals.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

/-- After translating the source projection so that the two projections of
`center` agree, changing from `normal` to `targetNormal` moves every projected
point by at most `R * K`. -/
lemma pureWZ2_centeredNormalProjection_nearby_witness
    {E : Set Point3} {center normal targetNormal : Point3} {R K : ℝ}
    (hE : E ⊆ Metric.closedBall center R)
    (hnormal : dist normal targetNormal ≤ K)
    (hR : 0 ≤ R) :
    ∀ value ∈ scalarProjection targetNormal E,
      ∃ sourceValue ∈
          (fun source : ℝ =>
            source + inner ℝ center (targetNormal - normal)) ''
            scalarProjection normal E,
        dist value sourceValue ≤ R * K := by
  intro value hvalue
  rcases hvalue with ⟨point, hpoint, rfl⟩
  let sourceValue :=
    inner ℝ point normal + inner ℝ center (targetNormal - normal)
  refine ⟨sourceValue, ?_, ?_⟩
  · exact ⟨inner ℝ point normal, ⟨point, hpoint, rfl⟩, rfl⟩
  rw [Real.dist_eq]
  have hidentity :
      inner ℝ point targetNormal - sourceValue =
        inner ℝ (point - center) (targetNormal - normal) := by
    dsimp only [sourceValue]
    simp only [inner_sub_left, inner_sub_right]
    ring
  rw [hidentity]
  have hpointRadius : ‖point - center‖ ≤ R := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hE hpoint
  have hnormalNorm : ‖targetNormal - normal‖ ≤ K := by
    simpa [dist_eq_norm, norm_sub_rev] using hnormal
  calc
    |inner ℝ (point - center) (targetNormal - normal)| ≤
        ‖point - center‖ * ‖targetNormal - normal‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ R * K :=
      mul_le_mul hpointRadius hnormalNorm (norm_nonneg _) hR

/-- Set-theoretic form of the centered estimate: after aligning the source
projection at `center`, the target projection lies in its closed
`R * K`-thickening. -/
lemma pureWZ2_centeredNormalProjection_subset_cthickening
    {E : Set Point3} {center normal targetNormal : Point3} {R K : ℝ}
    (hE : E ⊆ Metric.closedBall center R)
    (hnormal : dist normal targetNormal ≤ K)
    (hR : 0 ≤ R) :
    scalarProjection targetNormal E ⊆
      Metric.cthickening (R * K)
        ((fun source : ℝ =>
          source + inner ℝ center (targetNormal - normal)) ''
          scalarProjection normal E) := by
  intro value hvalue
  rcases pureWZ2_centeredNormalProjection_nearby_witness
      (E := E) (center := center) (normal := normal)
      (targetNormal := targetNormal) hE hnormal hR value hvalue with
    ⟨sourceValue, hsourceValue, hdist⟩
  exact Metric.mem_cthickening_of_dist_le value sourceValue (R * K) _
    hsourceValue hdist

/-- A paper AD projection along `normal` transfers to a nearby target normal
on a radius-`R` centered piece.  The source projection is first translated to
align the projection of the center, and `R * K ≤ delta` then gives the explicit
thickening loss `6`. -/
lemma PureWZ2PaperADSet1.centered_normal_projection
    {E : Set Point3} {center normal targetNormal : Point3}
    {R K delta alpha : ℝ} {C : ENNReal}
    (hAD : PureWZ2PaperADSet1
      (scalarProjection normal E) delta alpha C)
    (hE : E ⊆ Metric.closedBall center R)
    (hnormal : dist normal targetNormal ≤ K)
    (hR : 0 ≤ R)
    (hRK : R * K ≤ delta) :
    PureWZ2PaperADSet1
      (scalarProjection targetNormal E) delta alpha (6 * C) := by
  let shift := inner ℝ center (targetNormal - normal)
  let shiftedProjection : Set ℝ :=
    (fun source : ℝ => source + shift) '' scalarProjection normal E
  have hshifted :
      PureWZ2PaperADSet1 shiftedProjection delta alpha C := by
    simpa only [one_mul] using
      (hAD.affine_transfer (a := (1 : ℝ)) (b := shift) (by norm_num))
  apply hshifted.of_subset_cthickening
      (D := R * K) (T := scalarProjection targetNormal E)
  · simpa only [shift, shiftedProjection] using
      (pureWZ2_centeredNormalProjection_nearby_witness
        (E := E) (center := center) (normal := normal)
        (targetNormal := targetNormal) hE hnormal hR)
  · have hK : 0 ≤ K := (dist_nonneg.trans hnormal)
    exact mul_nonneg hR hK
  · exact hRK

/-- General-radius version of centered normal transfer.  The geometric error
`R * K` may be larger than the paper base scale, provided it is bounded by a
positive comparison radius `epsilon`.  The constant is the explicit loss from
`PureWZ2PaperADSet1.of_subset_cthickening_general`. -/
lemma PureWZ2PaperADSet1.centered_normal_projection_general
    {E : Set Point3} {center normal targetNormal : Point3}
    {R K epsilon delta alpha : ℝ} {C : ENNReal}
    (hAD : PureWZ2PaperADSet1
      (scalarProjection normal E) delta alpha C)
    (hE : E ⊆ Metric.closedBall center R)
    (hnormal : dist normal targetNormal ≤ K)
    (hR : 0 ≤ R)
    (hepsilon : 0 < epsilon)
    (hRK : R * K ≤ epsilon) :
    PureWZ2PaperADSet1
      (scalarProjection targetNormal E) delta alpha
      ((2 * (Nat.ceil (epsilon / delta) + 1) : ENNReal) ^ 3 * C) := by
  let shift := inner ℝ center (targetNormal - normal)
  let shiftedProjection : Set ℝ :=
    (fun source : ℝ => source + shift) '' scalarProjection normal E
  have hshifted :
      PureWZ2PaperADSet1 shiftedProjection delta alpha C := by
    simpa only [one_mul] using
      (hAD.affine_transfer (a := (1 : ℝ)) (b := shift) (by norm_num))
  apply hshifted.of_subset_cthickening_general
      (epsilon := epsilon) (target := scalarProjection targetNormal E)
  · intro value hvalue
    rcases pureWZ2_centeredNormalProjection_nearby_witness
        (E := E) (center := center) (normal := normal)
        (targetNormal := targetNormal) hE hnormal hR value hvalue with
      ⟨sourceValue, hsourceValue, hdist⟩
    exact ⟨sourceValue, by simpa only [shift, shiftedProjection] using hsourceValue,
      hdist.trans hRK⟩
  · exact hepsilon

/-- Finite-union form of centered normal transfer.  Each spatial piece may
have its own center and source normal; all source normals are `K`-close to one
common target normal.  The paper AD constant loses exactly a factor `6` per
piece and then the cardinality factor from finite union. -/
lemma PureWZ2PaperADSet1.centered_normal_finite_iUnion
    {ι : Type*} {indices : Finset ι}
    {pieces : ι → Set Point3} {centers normals : ι → Point3}
    {targetNormal : Point3} {R K delta alpha : ℝ} {C : ENNReal}
    (hindices : indices.Nonempty)
    (hAD : ∀ index ∈ indices,
      PureWZ2PaperADSet1
        (scalarProjection (normals index) (pieces index)) delta alpha C)
    (hpieces : ∀ index ∈ indices,
      pieces index ⊆ Metric.closedBall (centers index) R)
    (hnormals : ∀ index ∈ indices,
      dist (normals index) targetNormal ≤ K)
    (hR : 0 ≤ R)
    (hRK : R * K ≤ delta) :
    PureWZ2PaperADSet1
      (scalarProjection targetNormal
        (⋃ index ∈ indices, pieces index))
      delta alpha ((indices.card : ENNReal) * (6 * C)) := by
  classical
  have hpieceTransfer : ∀ index ∈ indices,
      PureWZ2PaperADSet1
        (scalarProjection targetNormal (pieces index))
        delta alpha (6 * C) := by
    intro index hindex
    exact (hAD index hindex).centered_normal_projection
      (hpieces index hindex) (hnormals index hindex) hR hRK
  have hunion := PureWZ2PaperADSet1.finite_iUnion
    (pieces := fun index => scalarProjection targetNormal (pieces index))
    hindices hpieceTransfer
  have hprojectionUnion :
      scalarProjection targetNormal (⋃ index ∈ indices, pieces index) =
        ⋃ index ∈ indices, scalarProjection targetNormal (pieces index) := by
    unfold scalarProjection
    rw [Set.image_iUnion]
    congr with index
    rw [Set.image_iUnion]
  rwa [hprojectionUnion]

/-- General-radius finite-union form of centered normal transfer.  Every piece
may have a different center and source normal, while the common geometric
error `R * K` is bounded by the positive radius `epsilon`. -/
lemma PureWZ2PaperADSet1.centered_normal_finite_iUnion_general
    {ι : Type*} {indices : Finset ι}
    {pieces : ι → Set Point3} {centers normals : ι → Point3}
    {targetNormal : Point3} {R K epsilon delta alpha : ℝ} {C : ENNReal}
    (hindices : indices.Nonempty)
    (hAD : ∀ index ∈ indices,
      PureWZ2PaperADSet1
        (scalarProjection (normals index) (pieces index)) delta alpha C)
    (hpieces : ∀ index ∈ indices,
      pieces index ⊆ Metric.closedBall (centers index) R)
    (hnormals : ∀ index ∈ indices,
      dist (normals index) targetNormal ≤ K)
    (hR : 0 ≤ R)
    (hepsilon : 0 < epsilon)
    (hRK : R * K ≤ epsilon) :
    PureWZ2PaperADSet1
      (scalarProjection targetNormal
        (⋃ index ∈ indices, pieces index))
      delta alpha
      ((indices.card : ENNReal) *
        ((2 * (Nat.ceil (epsilon / delta) + 1) : ENNReal) ^ 3 * C)) := by
  classical
  have hpieceTransfer : ∀ index ∈ indices,
      PureWZ2PaperADSet1
        (scalarProjection targetNormal (pieces index)) delta alpha
        ((2 * (Nat.ceil (epsilon / delta) + 1) : ENNReal) ^ 3 * C) := by
    intro index hindex
    exact (hAD index hindex).centered_normal_projection_general
      (hpieces index hindex) (hnormals index hindex) hR hepsilon hRK
  have hunion := PureWZ2PaperADSet1.finite_iUnion
    (pieces := fun index => scalarProjection targetNormal (pieces index))
    hindices hpieceTransfer
  have hprojectionUnion :
      scalarProjection targetNormal (⋃ index ∈ indices, pieces index) =
        ⋃ index ∈ indices, scalarProjection targetNormal (pieces index) := by
    unfold scalarProjection
    rw [Set.image_iUnion]
    congr with index
    rw [Set.image_iUnion]
  rwa [hprojectionUnion]

end Kakeya.Assouad

end
