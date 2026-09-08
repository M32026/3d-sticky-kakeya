module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.ActualMarginNetW102

@[expose] public section

open scoped NNReal

namespace Kakeya.ml1Boot.TrialRestartW94

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

universe uE

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-- The fixed-before-delta packing base forced by a small-bin fraction. -/
def cpackW102 (alpha : NNReal) : Nat :=
  Nat.ceil (3072 / (alpha : Real))

theorem cpackW102_spec {alpha rho : NNReal} {n : Nat}
    (halpha : 0 < alpha) (hrho : 0 < rho) (hn : 1 ≤ n) :
    (24 * (rho : Real) + ((alpha * rho : NNReal) : Real) / 128) /
        (((alpha * rho : NNReal) : Real) / 128) ≤
      (cpackW102 alpha : Real) * n + 1 := by
  have ha : (0 : Real) < (alpha : Real) := by exact_mod_cast halpha
  have hr : (0 : Real) < (rho : Real) := by exact_mod_cast hrho
  have hratio :
      (24 * (rho : Real) + ((alpha * rho : NNReal) : Real) / 128) /
          (((alpha * rho : NNReal) : Real) / 128) =
        3072 / (alpha : Real) + 1 := by
    rw [NNReal.coe_mul]
    field_simp
    ring
  rw [hratio]
  have hceil : 3072 / (alpha : Real) ≤ (cpackW102 alpha : Real) := by
    exact Nat.le_ceil _
  have hmul : (cpackW102 alpha : Real) ≤
      (cpackW102 alpha : Real) * n := by
    have hnat : cpackW102 alpha ≤ cpackW102 alpha * n := by
      simpa using Nat.mul_le_mul_left (cpackW102 alpha) hn
    exact_mod_cast hnat
  linarith

theorem scaled_grid_overlap_target_cpack_w102
    {delta rho alpha : NNReal} (hrho : 0 < rho)
    (halpha : 0 < alpha) (halpha1 : alpha ≤ 1)
    (G : Finset (Tube (alpha * rho) E))
    (hsep : ∀ a ∈ G, ∀ b ∈ G, a ≠ b ->
      (alpha * rho : Real) / 32 ≤ ‖a.x - b.x‖ + ‖a.y - b.y‖)
    (V : Tube rho E) :
    (G.filter (fun W : Tube (alpha * rho) E => ∃ (U : Tube delta E),
        U.carrier ⊆ Metric.closedBall (0 : E) 1 ∧
        U.toConvexSpaceBody ≤ (W.rescale rho).toConvexSpaceBody ∧
        U.toConvexSpaceBody ≤ V.toConvexSpaceBody)).card ≤
      2 * (cpackW102 alpha * Module.finrank Real E + 1) ^
        (2 * Module.finrank Real E) := by
  apply scaled_grid_overlap_target_w102 hrho halpha halpha1 G hsep V
    (cpackW102 alpha)
  exact cpackW102_spec halpha hrho (Nat.succ_le_iff.mpr Module.finrank_pos)

theorem rescaled_child_le_parent_w102
    {alpha child parent : NNReal} (halpha : alpha ≤ 1 / 4)
    (hgap : child ≤ parent / 2)
    (A : Tube (alpha * child) E) (B : Tube (alpha * parent) E)
    (hAB : A.toConvexSpaceBody ≤ B.toConvexSpaceBody) :
    (A.rescale child).toConvexSpaceBody ≤
      (B.rescale parent).toConvexSpaceBody := by
  apply Tube.rescale_le_rescale_of_body_le A B
  · exact mul_le_of_le_one_left child.coe_nonneg
      (le_trans halpha
        ((div_le_iff₀ (by norm_num : (0 : NNReal) < 4)).2 (by norm_num)))
  · have hα : (alpha : Real) ≤ 1 / 4 := by exact_mod_cast halpha
    have hchild : (child : Real) ≤ (parent : Real) / 2 := by
      exact_mod_cast hgap
    have hparent : 0 ≤ (parent : Real) := parent.coe_nonneg
    have hαparent : (alpha : Real) * (parent : Real) ≤
        (parent : Real) / 4 := by nlinarith
    have hmul : (alpha * parent : NNReal) + child ≤ parent := by
      apply NNReal.coe_le_coe.mp
      rw [NNReal.coe_add, NNReal.coe_mul]
      nlinarith
    exact hmul
  exact hAB

end
end Kakeya.ml1Boot.TrialRestartW94
