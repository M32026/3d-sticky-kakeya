import MyLeanRepo.Kakeya.Assouad.MultiscaleUniformRefinement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.MultiscaleCardinalityUniformRefinementStatement

/-!
# Multiscale cardinality uniform refinement

This closes the finite nested-partition uniformization used by the Section 7
projected-set refinement.
-/

namespace Kakeya.Assouad

theorem multiscale_cardinality_uniform_refinement :
    MultiscaleCardinalityUniformRefinementStatement := by
  intro α _ A hA T P h_partition h_refine
  let L := Nat.log 2 A.card + 1
  have hL : L = Nat.log 2 A.card + 1 := rfl
  have h_main :=
    multiscale_uniformity_induction
      A hA T P h_partition h_refine L hL T (by linarith)
  rcases h_main with
    ⟨A', hA'_nonempty, hA'_sub, hA'_unif, hA'_ret⟩
  have hA'_ret' :
      (A.card : ℝ) ≤
        (Nat.log 2 A.card + 1 : ℝ) ^ T * (A'.card : ℝ) := by
    simpa [L, hL] using hA'_ret
  refine ⟨A', hA'_nonempty, hA'_sub, hA'_ret', ?_⟩
  intro k hk
  have h1 : T - T ≤ k := by simp
  exact hA'_unif k h1 hk

end Kakeya.Assouad
