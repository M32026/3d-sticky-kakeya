import MyLeanRepo.Kakeya.Cinematic.Section5.PackingInjection
import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.Clusters

/-!
# Per-point overlap bound

Combines the iterated doubling cover with the packing injection to bound
the number of strictly `t`-separated centers within distance `3*t` of a
given function by `D^3`.
-/

open Metric Finset

namespace Kakeya.Cinematic

/-- The number of strictly `t`-separated centers within `c2Distance` `3*t`
of a given function `f ∈ family` is at most `D^3`. -/
lemma point_overlap_bound {family : Set C2Function} {K D t : ℝ}
    (hfamily : IsCinematicFamily family K D) (_hD : 1 ≤ D)
    {centers : Finset C2Function}
    (hcenters_sub : (centers : Set C2Function) ⊆ family)
    (hsep : ∀ c ∈ centers, ∀ d ∈ centers, c ≠ d → t < c2Distance c d)
    (ht : 0 < t)
    (f : C2Function) (hf : f ∈ family) :
    (centers.filter (fun c => c2Distance f c ≤ 3 * t)).card ≤ D ^ 3 := by
  set r : ℝ := 3 * t / 8 with hr_def
  have hpos : 0 < 3 * t := by positivity
  obtain ⟨B, hB_sub, hB_cover, hB_card⟩ :=
    iterated_doubling_cover hfamily f hf (3 * t) hpos 3
  let C_f : Finset C2Function := centers.filter (fun c => c2Distance f c ≤ 3 * t)
  have hC_sub : (C_f : Set C2Function) ⊆ (centers : Set C2Function) := by
    exact Finset.filter_subset _ _
  have hC_family : ∀ c ∈ C_f, c ∈ family := by
    intro c hc
    have hc' : c ∈ centers := (Finset.mem_filter.mp hc).1
    exact hcenters_sub hc'
  have hC_dist : ∀ c ∈ C_f, c2Distance f c ≤ 3 * t := by
    intro c hc
    exact (Finset.mem_filter.mp hc).2
  have h_cover : ∀ c ∈ C_f, ∃ b ∈ B, c ∈ Metric.closedBall b r := by
    intro c hc
    have hcin : c ∈ {g : C2Function | g ∈ family ∧ c2Distance f g ≤ 3 * t} := by
      exact ⟨hC_family c hc, hC_dist c hc⟩
    have hunion : c ∈ ⋃ b ∈ B, Metric.closedBall b ((3 * t) / 2 ^ 3) := hB_cover hcin
    have hr_eq : (3 * t) / 2 ^ 3 = r := by
      norm_num [hr_def]
    rw [hr_eq] at hunion
    rcases Set.mem_iUnion₂.mp hunion with ⟨b, hb, hball⟩
    exact ⟨b, hb, hball⟩
  have hsep_C : ∀ c ∈ C_f, ∀ d ∈ C_f, c ≠ d → t < c2Distance c d := by
    intro c hc d hd hne
    have hc' : c ∈ centers := hC_sub hc
    have hd' : d ∈ centers := hC_sub hd
    exact hsep c hc' d hd' hne
  have h_r_lt : 2 * r < t := by
    rw [hr_def]
    linarith
  have h_card : C_f.card ≤ B.card :=
    packing_injection ht h_r_lt C_f B hsep_C h_cover
  have h_main : (C_f.card : ℝ) ≤ D ^ 3 := by
    calc (C_f.card : ℝ)
      ≤ (B.card : ℝ) := by exact_mod_cast h_card
    _ ≤ D ^ 3 := hB_card
  exact_mod_cast h_main

end Kakeya.Cinematic
