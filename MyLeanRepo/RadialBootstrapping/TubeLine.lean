module

/-
  TubeLine.lean

  Shared definitions for tubes around affine subspace lines and
  half-mass concentration predicates.

  Moved here from BootstrappingOneDirection.lean to break an import cycle
  with SingletonStepBWrapper.lean.
-/

public import MyLeanRepo.RadialBootstrapping.Basic

@[expose] public section

open MeasureTheory Metric Set Finset
open scoped ENNReal NNReal Classical

noncomputable section

namespace RadialBootstrapping
namespace B1

/-- The r-tube around an affine subspace line. -/
def tubeLine (r : ℝ) (ℓ : AffineSubspace ℝ Point) : Set Point :=
  Metric.thickening r (ℓ : Set Point)

/-- At least half of the tube mass is in concentrated tubes (mass-based). -/
def HalfMassConcentrated (ν : Measure Point) (Y : Set Point)
    (T : Finset (AffineSubspace ℝ Point)) (r κ : ℝ) : Prop :=
  2 * ∑ ℓ ∈ T.filter (fun ℓ => IsConcentrated ν Y (tubeLine r ℓ) r κ),
    ν (tubeLine r ℓ ∩ Y) ≥ ∑ ℓ ∈ T, ν (tubeLine r ℓ ∩ Y)

/-- At least half of the tube mass is in non-concentrated tubes (mass-based). -/
def HalfMassNonConcentrated (ν : Measure Point) (Y : Set Point)
    (T : Finset (AffineSubspace ℝ Point)) (r κ : ℝ) : Prop :=
  2 * ∑ ℓ ∈ T.filter (fun ℓ => IsNonConcentrated ν Y (tubeLine r ℓ) r κ),
    ν (tubeLine r ℓ ∩ Y) ≥ ∑ ℓ ∈ T, ν (tubeLine r ℓ ∩ Y)

/-- For any finite T, either concentrated tubes or non-concentrated tubes
    contain at least half the total tube-intersection mass. -/
lemma partition_half_mass (ν : Measure Point) (Y : Set Point)
    (T : Finset (AffineSubspace ℝ Point)) (r κ : ℝ) :
    HalfMassConcentrated ν Y T r κ ∨ HalfMassNonConcentrated ν Y T r κ := by
  classical
  let f : AffineSubspace ℝ Point → ENNReal := fun ℓ => ν (tubeLine r ℓ ∩ Y)
  let total : ENNReal := ∑ ℓ ∈ T, f ℓ
  let C_set := T.filter (fun ℓ => IsConcentrated ν Y (tubeLine r ℓ) r κ)
  let NotC_set := T.filter (fun ℓ => ¬ IsConcentrated ν Y (tubeLine r ℓ) r κ)
  let NC_set := T.filter (fun ℓ => IsNonConcentrated ν Y (tubeLine r ℓ) r κ)
  have h_disj : Disjoint C_set NotC_set := by
    rw [Finset.disjoint_left]
    intro ℓ hℓc hℓn
    have h1 : IsConcentrated ν Y (tubeLine r ℓ) r κ := (Finset.mem_filter.mp hℓc).2
    have h2 : ¬ IsConcentrated ν Y (tubeLine r ℓ) r κ := (Finset.mem_filter.mp hℓn).2
    exact h2 h1
  have h_cover : C_set ∪ NotC_set = T := by
    ext ℓ
    simp only [C_set, NotC_set, Finset.mem_union, Finset.mem_filter]
    <;> by_cases h : IsConcentrated ν Y (tubeLine r ℓ) r κ <;> simp [h] <;> tauto
  have h_sum : ∑ ℓ ∈ C_set, f ℓ + ∑ ℓ ∈ NotC_set, f ℓ = total := by
    have h : (C_set ∪ NotC_set).sum f = ∑ ℓ ∈ C_set, f ℓ + ∑ ℓ ∈ NotC_set, f ℓ :=
      Finset.sum_union h_disj
    rw [h_cover] at h
    exact h.symm
  have h_notc_subset_nc : NotC_set ⊆ NC_set := by
    intro ℓ hℓ
    have h' : ¬ IsConcentrated ν Y (tubeLine r ℓ) r κ := (Finset.mem_filter.mp hℓ).2
    have h'' : IsNonConcentrated ν Y (tubeLine r ℓ) r κ :=
      not_concentrated_imp_nonconcentrated h'
    simp only [NC_set, Finset.mem_filter]
    exact ⟨(Finset.mem_filter.mp hℓ).1, h''⟩
  have h_sum_nc : ∑ ℓ ∈ NotC_set, f ℓ ≤ ∑ ℓ ∈ NC_set, f ℓ :=
    Finset.sum_le_sum_of_subset_of_nonneg h_notc_subset_nc (fun _ _ _ => by positivity)
  set a : ENNReal := ∑ ℓ ∈ C_set, f ℓ with ha_def
  set b : ENNReal := ∑ ℓ ∈ NotC_set, f ℓ with hb_def
  have h_sum2 : a + b = total := h_sum
  by_cases h : 2 * a ≥ total
  · exact Or.inl (by simpa [HalfMassConcentrated, ha_def] using h)
  · have h_lt : 2 * a < total := by exact Std.not_le.mp h
    have h_goal : 2 * b ≥ total := by
      by_contra h_contra
      have h_lt2 : 2 * b < total := by exact Std.not_le.mp h_contra
      have h_add : 2 * a + 2 * b < total + total := ENNReal.add_lt_add h_lt h_lt2
      have h_total2 : total + total = 2 * total := by ring
      rw [h_total2] at h_add
      have h_eq : 2 * a + 2 * b = 2 * (a + b) := by rw [mul_add]
      rw [h_eq, h_sum2] at h_add
      <;> exact (lt_self_iff_false (2 * total)).mp h_add
    have h_final : 2 * ∑ ℓ ∈ NC_set, f ℓ ≥ total := by
      calc 2 * ∑ ℓ ∈ NC_set, f ℓ ≥ 2 * b := by gcongr
        _ ≥ total := h_goal
    exact Or.inr (by simpa [HalfMassNonConcentrated] using h_final)

end B1
end RadialBootstrapping
