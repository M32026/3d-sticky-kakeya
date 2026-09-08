import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.MultiscaleShifts
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.HierarchicalPrefixGrouping.Proof

/-!
# Multiscale shift data package

Holds the complete multiscale shift construction: per-level copy counts,
shifts, radius budgets, and the derived flat composed shift.

This is the foundation for assembling per-scale label maps at every grid cut
in the shading-aware random translation construction.
-/

noncomputable section

open BigOperators

namespace Kakeya.Streamlined.RandomTranslation.WithShading

/-- Complete multiscale shift data: per-level scales, copy counts, shifts,
and radius budget. The flat total copy count and composed shift are derived
via `totalJ` and `shift`. -/
structure MultiscaleShiftData (δ : ℝ) (M : ℕ) where
  sigma : Fin M → AdmissibleScale δ
  J : Fin M → ℕ
  hJ_pos : ∀ k, 0 < J k
  shiftAt : (k : Fin M) → Fin (J k) → Point3
  radius : Fin M → ℝ
  hradius_nonneg : ∀ k, 0 ≤ radius k
  hshift_norm : ∀ k j, ‖shiftAt k j‖ ≤ radius k
  h_total_radius : multiscaleTotalRadius radius ≤ 9

namespace MultiscaleShiftData

/-- Total flat copy count. -/
abbrev totalJ {δ M} (data : MultiscaleShiftData δ M) : ℕ :=
  multiscaleTotalJ data.J

/-- Composed flat shift function. -/
def shift {δ M} (data : MultiscaleShiftData δ M) :
    Fin data.totalJ → Point3 :=
  multiscaleShiftFun data.shiftAt

/-- Norm bound on every composed shift. -/
lemma hshift_bound {δ M} (data : MultiscaleShiftData δ M) :
    ∀ i : Fin data.totalJ, ‖data.shift i‖ ≤ 9 := by
  intro i
  have h1 : ‖multiscaleShiftFun data.shiftAt i‖ ≤
      multiscaleTotalRadius data.radius :=
    multiscaleShiftFun_norm_le data.shiftAt data.hshift_norm i
  exact le_trans h1 data.h_total_radius

/-- Apply hierarchical prefix grouping at a given cut. -/
theorem prefixGrouping {δ M} (data : MultiscaleShiftData δ M)
    (cut : Fin (M + 1)) :
    ∃ (groupCount : ℕ)
      (group : Fin data.totalJ → Fin groupCount)
      (cumulative : Fin groupCount → Point3)
      (residual : Fin data.totalJ → Point3),
      0 < groupCount ∧
      Function.Surjective group ∧
      (∀ g h,
        (Finset.univ.filter fun i => group i = g).card =
          (Finset.univ.filter fun i => group i = h).card) ∧
      (∀ g, 0 < (Finset.univ.filter fun i => group i = g).card) ∧
      (∀ i j,
        group i = group j ↔
          ∀ k : Fin M, k.val < cut.val →
            (finPiFinEquiv.symm i) k = (finPiFinEquiv.symm j) k) ∧
      (∀ i, data.shift i = cumulative (group i) + residual i) ∧
      ∀ i, ‖residual i‖ ≤
        ∑ k ∈ (Finset.univ.filter fun k : Fin M => cut.val ≤ k.val),
          data.radius k :=
  hierarchical_prefix_grouping data.J data.hJ_pos data.radius
    data.hradius_nonneg data.shiftAt data.hshift_norm cut

end MultiscaleShiftData

end Kakeya.Streamlined.RandomTranslation.WithShading

end
