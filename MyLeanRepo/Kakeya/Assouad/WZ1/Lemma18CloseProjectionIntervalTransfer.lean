import MyLeanRepo.Kakeya.Assouad.WZ1.RootRelativeFineProjectionCoveringTransfer
import MyLeanRepo.Kakeya.Assouad.WZ1.IntervalADHelpers

/-!
# Interval covering transfer through pointwise-close projections

This scalar lemma is used twice in the final WZ1 Lemma 18 assembly:

* to compare different plane normals after centered alignment; and
* to transfer the retained rho-family estimate back to the original fine
  family.
-/

noncomputable section

open Metric Set

namespace Kakeya.Assouad

/--
Transfer a uniform radius-`tau` interval covering bound through a pointwise
`epsilon` perturbation.

The source values relevant to one target interval lie in a radius-`2*tau`
source interval when `epsilon ≤ tau`.  Five radius-`tau` intervals cover it.
The final `epsilon`-thickening contributes the explicit grid factor.
-/
theorem wz1_lemma18_close_projection_interval_transfer
    (target source : Set ℝ)
    (rho tau epsilon : ℝ)
    (bound : ENNReal)
    (hrho : 0 < rho)
    (htau : 0 < tau)
    (hepsilon : 0 < epsilon)
    (hepsilonTau : epsilon ≤ tau)
    (hclose :
      ∀ value ∈ target,
        ∃ sourceValue ∈ source,
          dist value sourceValue ≤ epsilon)
    (hsource :
      ∀ intervalCenter : ℝ,
        (↑(externalCoveringNumber
          (Real.toNNReal rho)
          (source ∩ closedBall intervalCenter tau)) : ENNReal) ≤
            bound) :
    ∀ intervalCenter : ℝ,
      (↑(externalCoveringNumber
        (Real.toNNReal rho)
        (target ∩ closedBall intervalCenter tau)) : ENNReal) ≤
          (2 * Nat.ceil (epsilon / rho) + 2 : ENNReal) *
            (5 * bound) := by
  intro intervalCenter
  let localSource :=
    source ∩ closedBall intervalCenter (2 * tau)
  have htargetSubset :
      target ∩ closedBall intervalCenter tau ⊆
        cthickening epsilon localSource := by
    intro value hvalue
    rcases hclose value hvalue.1 with
      ⟨sourceValue, hsourceValue, hdistance⟩
    have hsourceBall :
        sourceValue ∈
          closedBall intervalCenter (2 * tau) := by
      rw [Metric.mem_closedBall]
      calc
        dist sourceValue intervalCenter ≤
            dist sourceValue value +
              dist value intervalCenter :=
          dist_triangle _ _ _
        _ ≤ epsilon + tau := by
          have hdistance' :
              dist sourceValue value ≤ epsilon := by
            simpa [dist_comm] using hdistance
          exact add_le_add hdistance'
            (Metric.mem_closedBall.mp hvalue.2)
        _ ≤ 2 * tau := by linarith
    exact
      mem_cthickening_of_dist_le
        value sourceValue epsilon localSource
        ⟨hsourceValue, hsourceBall⟩ hdistance
  rcases
      real_closedBall_finer_cover
        intervalCenter htau
        (show 0 < 2 * tau by positivity)
        (by linarith : tau ≤ 2 * tau) with
    ⟨centers, hcentersCard, hcentersCover⟩
  have hcardFive :
      (centers.card : ENNReal) ≤ 5 := by
    have hceil :
        Nat.ceil (2 * (2 * tau) / tau) = 4 := by
      have htauNe : tau ≠ 0 := htau.ne'
      have hratio :
          2 * (2 * tau) / tau = (4 : ℝ) := by
        field_simp [htauNe] <;> ring
      rw [hratio]
      norm_num
    rw [hceil] at hcentersCard
    norm_num at hcentersCard ⊢
    exact hcentersCard
  have hlocalSourceSubset :
      localSource ⊆
        ⋃ center ∈ centers,
          source ∩ closedBall center tau := by
    intro value hvalue
    rcases Set.mem_iUnion₂.mp
        (hcentersCover hvalue.2) with
      ⟨center, hcenter, hvalueCenter⟩
    exact Set.mem_iUnion₂.mpr
      ⟨center, hcenter, ⟨hvalue.1, hvalueCenter⟩⟩
  have hlocalSourceCover :
      (↑(externalCoveringNumber
        (Real.toNNReal rho) localSource) : ENNReal) ≤
          5 * bound := by
    have hmono :
        (↑(externalCoveringNumber
          (Real.toNNReal rho) localSource) : ENNReal) ≤
            (↑(externalCoveringNumber
              (Real.toNNReal rho)
              (⋃ center ∈ centers,
                source ∩ closedBall center tau)) : ENNReal) := by
      exact_mod_cast
        externalCoveringNumber_mono_set
          hlocalSourceSubset
    have hunion :=
      externalCoveringNumber_biUnion_le_card
        (ε := Real.toNNReal rho)
        (s := centers)
        (A := fun center =>
          source ∩ closedBall center tau)
        (fun center _ => hsource center)
    exact hmono.trans (hunion.trans (by gcongr))
  exact
    externalCoveringNumber_of_subset_cthickening
      hrho hepsilon htargetSubset hlocalSourceCover

end Kakeya.Assouad
