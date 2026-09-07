import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberGridParameterSelectionStatement

/-!
# Match an arbitrary local scale to the projected-fiber grid tree

The OS tree has integer levels with mesh `base^(-level)`.  Once the terminal
mesh at level `levels + 1` is finer than `delta`, every intermediate scale
`rho ∈ [delta,1]` is comparable to the mesh at one tree level.
-/

noncomputable section

namespace Kakeya.Assouad

/--
Select the first grid level whose mesh is at most `rho`.

The selected level lies in the OS tree and its mesh differs from `rho` by
less than one factor of `base`.  This is the scale bridge from
`ParameterLocalFullBlockData.blockScale` to same-level projected cell-area
uniformity.
-/
def ProjectedFiberGridLevelSelectionStatement : Prop :=
  ∀ base levels : ℕ,
    2 ≤ base →
      ∀ delta : ℝ,
        0 < delta →
        ((base ^ (levels + 1) : ℝ)⁻¹) < delta →
          ∀ rho : ℝ,
            delta ≤ rho →
            rho ≤ 1 →
              ∃ level : ℕ,
                level ≤ levels + 1 ∧
                ((base ^ level : ℝ)⁻¹) ≤ rho ∧
                rho <
                  (base : ℝ) *
                    ((base ^ level : ℝ)⁻¹)

end Kakeya.Assouad
