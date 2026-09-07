import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23CoordinateLabels

/-!
# Snapped spatial-cell centers for WZ1 Lemma 23

The paper works with centers of axis-parallel `rho`-cubes.  The final
Proposition 9 shading in the repository is an arbitrary measurable shading,
so `Lemma23SpatialGrid` chooses genuine shaded representatives instead.

For the combinatorial incidence graph we additionally need canonical lattice
points.  Snapping an active cell to its geometric center has three roles:

* the genuine representative stays within `rho / 2`;
* equal y- or z-indices give exact coordinate equality at the snapped centers;
* the local and global grain scalar coordinates change by only `O(rho)`.

This prevents the invalid replacement of approximate label equality by
definitional equality in the four-cycle telescope.
-/

namespace Kakeya.Assouad

noncomputable section

/-- Center of one spatial cell used by `wz1Lemma23CellIndex`. -/
def wz1Lemma23CellCenter
    (rho : ℝ) (idx : ℤ × ℤ × ℤ) : Point3 :=
  let side := gridSide (rho / 2)
  point3
    (((idx.1 : ℝ) + 1 / 2) * side)
    (((idx.2.1 : ℝ) + 1 / 2) * side)
    (((idx.2.2 : ℝ) + 1 / 2) * side)

/-- Snap a point to the center of its Lemma 23 spatial cell. -/
def wz1Lemma23Snap (rho : ℝ) (p : Point3) : Point3 :=
  wz1Lemma23CellCenter rho (wz1Lemma23CellIndex rho p)

/--
Canonical cell centers recover their index, stay close to every point in the
cell, and preserve the local/global scalar coordinates up to fixed multiples
of `rho`.

The bounds `|f| ≤ 3`, `|g| ≤ 5`, and Lipschitz constants `1`, `4` are the
paper-normalized bounds at the locally-linear stage.
-/
def WZ1Lemma23SnappedCellGeometryStatement : Prop :=
  ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
    (∀ idx : ℤ × ℤ × ℤ,
      wz1Lemma23CellIndex rho
          (wz1Lemma23CellCenter rho idx) = idx) ∧
    (∀ (idx : ℤ × ℤ × ℤ) (p : Point3),
      wz1Lemma23CellIndex rho p = idx →
        (∀ i : Fin 3,
          |p i - (wz1Lemma23CellCenter rho idx) i| ≤ rho / 2) ∧
        dist p (wz1Lemma23CellCenter rho idx) ≤ rho / 2) ∧
    (∀ first second : ℤ × ℤ × ℤ,
      first.2.1 = second.2.1 →
        (wz1Lemma23CellCenter rho first) 1 =
          (wz1Lemma23CellCenter rho second) 1) ∧
    (∀ first second : ℤ × ℤ × ℤ,
      first.2.2 = second.2.2 →
        (wz1Lemma23CellCenter rho first) 2 =
          (wz1Lemma23CellCenter rho second) 2) ∧
    ∀ (f g : ℝ → ℝ),
      LipschitzOnWith 1 f Set.univ →
      LipschitzOnWith 4 g Set.univ →
      (∀ z, |f z| ≤ 3) →
      (∀ y, |g y| ≤ 5) →
      ∀ p : Point3, ‖p‖ ≤ 1 →
        |wz1Lemma23GlobalCoordinate f p -
            wz1Lemma23GlobalCoordinate f
              (wz1Lemma23Snap rho p)| ≤
          4 * rho ∧
        |wz1Lemma23LocalCoordinate g p -
            wz1Lemma23LocalCoordinate g
              (wz1Lemma23Snap rho p)| ≤
          8 * rho

end

end Kakeya.Assouad
