import MyLeanRepo.Kakeya.Assouad.PropStickyStatements

/-!
# Counting for induced recursive covers

When a coarser source fiber is partitioned into finer source fibers, the
number of finer parents is controlled by the ratio of the two source-fiber
cardinalities.  One `C` is spent on coarse-fiber uniformity and one on the
size range of the finer fibers.
-/

noncomputable section

namespace Kakeya.Assouad

open scoped ENNReal

/--
If every child has mass in `[m, C*m]` and the total masses of two parent
blocks are `C`-comparable, then their child counts are `C^2`-comparable.
-/
theorem induced_parent_count_uniform_square
    {α : Type*} [DecidableEq α]
    (children : α → ENNReal)
    (first second : Finset α)
    (C m : ENNReal)
    (hm_pos : 0 < m) (hm_top : m ≠ ⊤)
    (hchild_lower : ∀ index ∈ first ∪ second, m ≤ children index)
    (hchild_upper :
      ∀ index ∈ first ∪ second, children index ≤ C * m)
    (htotal :
      ∑ index ∈ first, children index ≤
        C * ∑ index ∈ second, children index) :
    (first.card : ENNReal) ≤
      C * C * (second.card : ENNReal) := by
  have hfirst_lower :
      (first.card : ENNReal) * m ≤
        ∑ index ∈ first, children index := by
    calc
      (first.card : ENNReal) * m =
          ∑ _index ∈ first, m := by
            simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ index ∈ first, children index := by
        exact Finset.sum_le_sum fun index hindex =>
          hchild_lower index (Finset.mem_union_left second hindex)
  have hsecond_upper :
      ∑ index ∈ second, children index ≤
        (second.card : ENNReal) * (C * m) := by
    calc
      ∑ index ∈ second, children index ≤
          ∑ _index ∈ second, C * m := by
            exact Finset.sum_le_sum fun index hindex =>
              hchild_upper index (Finset.mem_union_right first hindex)
      _ = (second.card : ENNReal) * (C * m) := by
        simp [Finset.sum_const, nsmul_eq_mul]
  have hwith_m :
      (first.card : ENNReal) * m ≤
        (C * C * (second.card : ENNReal)) * m := by
    calc
      (first.card : ENNReal) * m ≤
          ∑ index ∈ first, children index :=
        hfirst_lower
      _ ≤ C * ∑ index ∈ second, children index := htotal
      _ ≤ C * ((second.card : ENNReal) * (C * m)) := by
        gcongr
      _ = (C * C * (second.card : ENNReal)) * m := by
        ac_rfl
  exact (ENNReal.mul_le_mul_iff_left hm_pos.ne' hm_top).mp hwith_m

end Kakeya.Assouad
