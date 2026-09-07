import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.CenteredNormalPaperAD
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicADTransfer

/-!
# Local paper AD from a finite spatial cover

This file packages the target-side glue needed when a normal field is defined
only on the target set.  Local paper AD at one occupied anchor of each bounded
piece is transferred to the normal at a fixed occupied target anchor, combined
over the finite cover, and then restricted back to the target.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

/-- A finite cover by radius-`R` pieces with local paper AD along a
`1`-Lipschitz normal field gives paper AD along the normal at any fixed target
anchor.  The target radius `R0` controls the distance between every piece
normal and the fixed normal.  The explicit constant is the product of the
finite-union loss and the general centered-normal thickening loss. -/
lemma PureWZ2PaperADSet1.finite_cover_local_lipschitz_field
    {target : Set Point3} (anchor0 : target)
    (field : target → Point3)
    {ι : Type*} {indices : Finset ι}
    {pieces : ι → Set Point3} (pieceAnchor : ι → target)
    {R R0 epsilon delta alpha : ℝ} {C : ENNReal}
    (hfield : LipschitzWith 1 field)
    (hcover : target ⊆ ⋃ index ∈ indices, pieces index)
    (hpieces : ∀ index ∈ indices,
      pieces index ⊆ Metric.closedBall (pieceAnchor index : Point3) R)
    (hAD : ∀ index ∈ indices,
      PureWZ2PaperADSet1
        (scalarProjection (field (pieceAnchor index)) (pieces index))
        delta alpha C)
    (htarget : target ⊆ Metric.closedBall (anchor0 : Point3) R0)
    (hR : 0 ≤ R)
    (hepsilon : 0 < epsilon)
    (herror : R * R0 ≤ epsilon) :
    PureWZ2PaperADSet1
      (scalarProjection (field anchor0) target) delta alpha
      ((indices.card : ENNReal) *
        ((2 * (Nat.ceil (epsilon / delta) + 1) : ENNReal) ^ 3 * C)) := by
  classical
  have hindices : indices.Nonempty := by
    rcases Set.mem_iUnion.mp (hcover anchor0.property) with
      ⟨index, hindex⟩
    rcases Set.mem_iUnion.mp hindex with ⟨hindex, _⟩
    exact ⟨index, hindex⟩
  have hnormal : ∀ index ∈ indices,
      dist (field (pieceAnchor index)) (field anchor0) ≤ R0 := by
    intro index _
    calc
      dist (field (pieceAnchor index)) (field anchor0) ≤
          dist (pieceAnchor index) anchor0 := by
        simpa only [NNReal.coe_one, one_mul] using
          hfield.dist_le_mul (pieceAnchor index) anchor0
      _ ≤ R0 := by
        simpa only [Metric.mem_closedBall, Subtype.dist_eq] using
          htarget (pieceAnchor index).property
  have hunion : PureWZ2PaperADSet1
      (scalarProjection (field anchor0)
        (⋃ index ∈ indices, pieces index)) delta alpha
      ((indices.card : ENNReal) *
        ((2 * (Nat.ceil (epsilon / delta) + 1) : ENNReal) ^ 3 * C)) :=
    PureWZ2PaperADSet1.centered_normal_finite_iUnion_general
      hindices hAD hpieces hnormal hR hepsilon herror
  exact hunion.weaken_subset (Set.image_mono hcover)

end Kakeya.Assouad

end
