import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23SnappedCellStatements
import Mathlib.Combinatorics.Pigeonhole

/-!
# Select separated y-layers for WZ1 Lemma 23

The paper keeps one congruence class of fine y-layers so that the surviving
cube centers have y-coordinates in a translate of `sqrt rho * ℤ`.  This loses
only `O(rho^(-1/2))`, and points in one later local-grain class have exactly
the same snapped y-coordinate.

The finite statement below is weighted: the weight may record the number of
popular incidences carried by one active spatial cell.  It therefore supports
the later local-pair count rather than merely selecting a nonempty wrapper.
-/

namespace Kakeya.Assouad

noncomputable section

/-- Number of fine y-layers skipped between retained layers. -/
def wz1Lemma23YStride (rho : ℝ) : ℕ :=
  Nat.ceil
    (Real.sqrt rho / gridSide (rho / 2))

/-- Active indices in one residue class of the fine y-coordinate. -/
def wz1Lemma23YResidueCells
    (rho : ℝ) (cells : Finset (ℤ × ℤ × ℤ))
    (residue : Fin (wz1Lemma23YStride rho)) :
    Finset (ℤ × ℤ × ℤ) :=
  cells.filter fun idx =>
    idx.2.1 % (wz1Lemma23YStride rho : ℤ) =
      ((residue : ℕ) : ℤ)

/--
One residue class retains its weighted share of the cells.  Distinct retained
y-indices give snapped centers separated by at least `sqrt rho`.
-/
def WZ1Lemma23YLayerSelectionStatement : Prop :=
  ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
    0 < wz1Lemma23YStride rho ∧
    (wz1Lemma23YStride rho : ℝ) ≤
      2 * Real.sqrt 3 / Real.sqrt rho ∧
    ∀ (cells : Finset (ℤ × ℤ × ℤ))
      (weight : (ℤ × ℤ × ℤ) → ℕ),
      ∃ residue : Fin (wz1Lemma23YStride rho),
        let selected :=
          wz1Lemma23YResidueCells rho cells residue
        (∑ idx ∈ cells, weight idx) ≤
            wz1Lemma23YStride rho *
              ∑ idx ∈ selected, weight idx ∧
          selected ⊆ cells ∧
          (∀ idx ∈ selected,
            idx.2.1 % (wz1Lemma23YStride rho : ℤ) =
              ((residue : ℕ) : ℤ)) ∧
          ∀ first ∈ selected, ∀ second ∈ selected,
            first.2.1 = second.2.1 ∨
              Real.sqrt rho ≤
                |(wz1Lemma23CellCenter rho first) 1 -
                  (wz1Lemma23CellCenter rho second) 1|

end

end Kakeya.Assouad
