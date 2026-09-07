import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-!
# Positive cluster lower scale

Convert a common coarse support lower bound into the positive integer scale
required by the separated-cluster pigeonhole.
-/

namespace Kakeya.Cinematic

lemma exists_positive_cluster_lower
    (centers support : ℕ)
    (hcenters : 0 < centers)
    (hlarge : 2 * centers ≤ support) :
    ∃ clusterLower : ℕ,
      0 < clusterLower ∧
      2 * centers * clusterLower ≤ support ∧
      support < 2 * centers * (clusterLower + 1) := by
  let denominator := 2 * centers
  let clusterLower := support / denominator
  have hdenominator : 0 < denominator := by
    dsimp [denominator]
    omega
  have hclusterLower : 0 < clusterLower := by
    dsimp [clusterLower]
    exact Nat.div_pos hlarge hdenominator
  have hlower0 :
      support / denominator * denominator ≤ support :=
    Nat.div_mul_le_self support denominator
  have hlower : denominator * clusterLower ≤ support := by
    dsimp [clusterLower]
    simpa [Nat.mul_comm] using hlower0
  have hmod : support % denominator < denominator :=
    Nat.mod_lt support hdenominator
  have hdecomp :
      denominator * (support / denominator) +
          support % denominator =
        support :=
    Nat.div_add_mod support denominator
  have hupper :
      support < denominator * (clusterLower + 1) := by
    calc
      support =
          denominator * (support / denominator) +
            support % denominator :=
        hdecomp.symm
      _ <
          denominator * (support / denominator) +
            denominator :=
        Nat.add_lt_add_left hmod _
      _ = denominator * (clusterLower + 1) := by
        simp [clusterLower, Nat.mul_add]
  exact
    ⟨clusterLower, hclusterLower,
      by simpa [denominator] using hlower,
      by simpa [denominator] using hupper⟩

end Kakeya.Cinematic
