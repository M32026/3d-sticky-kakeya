import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientBallInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.MaximalSeparatedCover
import MyLeanRepo.Kakeya.Cinematic.Section5.PointOverlapBound
import MyLeanRepo.Kakeya.Cinematic.Section5.ClusterCardSumSwap

/-!
# Finite bounded-overlap ambient ball cover

PYZ Section 5.1.1: after the first two-ends scale is frozen, choose radius-`t`
balls with centers forming a maximal strictly `t`-separated subset. Each cluster
`F ∩ 3B` has diameter at most `6t`, and the overlap sum is bounded by `D^3 * #F`
via iterated doubling and a packing injection.
-/

namespace Kakeya.Cinematic

theorem finite_ambient_ball_cover :
    FiniteAmbientBallCoverStatement := by
  intro K D t hD ht family hfamily F hF
  have h_main := exists_maximal_separated_cover (S := F.toFinset) ht
  rcases h_main with ⟨centers, hcenters_sub, hsep, hcover⟩
  have hcenters_sub_set : (centers : Set C2Function) ⊆ F.carrier := by
    simpa [FiniteFunctionFamily.toFinset] using hcenters_sub
  have hcenters_family : (centers : Set C2Function) ⊆ family :=
    subset_trans hcenters_sub_set hF
  have hsep' : ∀ c ∈ centers, ∀ d ∈ centers, c ≠ d → t < c2Distance c d := by
    intro c hc d hd hne
    have h := hsep c hc d hd hne
    simpa [c2Distance_eq_dist] using h
  have hcover' : ∀ f ∈ F.carrier, ∃ c ∈ centers, c2Distance f c ≤ t := by
    intro f hf
    have h_f_in_toFinset : f ∈ F.toFinset := by
      simpa [FiniteFunctionFamily.toFinset] using hf
    rcases hcover f h_f_in_toFinset with ⟨c, hc, hle⟩
    exact ⟨c, hc, by simpa [c2Distance_eq_dist] using hle⟩
  have h_card_eq : F.toFinset.card = F.card := by
    have h : F.card = F.toFinset.card :=
      Set.ncard_eq_toFinset_card F.carrier (hs := F.finite)
    exact h.symm
  refine ⟨centers, hcenters_sub_set, hcover', hsep', ?_, ?_, ?_⟩
  -- Condition 4: cluster ⊆ family
  · intro c _
    intro x hx
    have h_cluster_def : (F.cluster c (3 * t)).carrier = F.carrier ∩ c2Ball c (3 * t) := by rfl
    rw [h_cluster_def] at hx
    have h2 : x ∈ F.carrier := hx.1
    exact hF h2
  -- Condition 5: diameter ≤ 6*t
  · intro c _ f hf g hg
    have h_cluster_def : (F.cluster c (3 * t)).carrier = F.carrier ∩ c2Ball c (3 * t) := by rfl
    have hf' : c2Distance f c ≤ 3 * t := by
      rw [h_cluster_def] at hf
      have h2 : f ∈ c2Ball c (3 * t) := hf.2
      simpa [c2Ball] using h2
    have hg' : c2Distance g c ≤ 3 * t := by
      rw [h_cluster_def] at hg
      have h2 : g ∈ c2Ball c (3 * t) := hg.2
      simpa [c2Ball] using h2
    have h_symm : c2Distance c g = c2Distance g c := by
      simp [c2Distance_eq_dist, dist_comm]
    calc
      c2Distance f g
        ≤ c2Distance f c + c2Distance c g := dist_triangle f c g
      _ = c2Distance f c + c2Distance g c := by rw [h_symm]
      _ ≤ 3 * t + 3 * t := by linarith
      _ = 6 * t := by ring
  -- Condition 6: overlap sum
  · have h_sum_swap := cluster_card_sum_swap (F := F) (centers := centers) (t := t)
    rw [h_sum_swap]
    have h_bound : ∀ f ∈ F.toFinset,
        ((centers.filter (fun c => c2Distance f c ≤ 3 * t)).card : ℝ) ≤ D ^ 3 := by
      intro f hf
      have hf_carrier : f ∈ F.carrier := by
        simpa [FiniteFunctionFamily.toFinset] using hf
      have hf_family : f ∈ family := hF hf_carrier
      have h := point_overlap_bound hfamily hD hcenters_family hsep' ht f hf_family
      exact_mod_cast h
    have h_sum_le : (∑ f ∈ F.toFinset, ((centers.filter (fun c => c2Distance f c ≤ 3 * t)).card : ℝ)) ≤
        ∑ f ∈ F.toFinset, (D ^ 3 : ℝ) := by
      apply Finset.sum_le_sum
      intro f hf
      exact h_bound f hf
    have h_sum_const : (∑ f ∈ F.toFinset, (D ^ 3 : ℝ)) = (F.toFinset.card : ℝ) * D ^ 3 := by
      simp [Finset.sum_const]
      <;> ring
    calc
      (∑ f ∈ F.toFinset, ((centers.filter (fun c => c2Distance f c ≤ 3 * t)).card : ℝ))
        ≤ ∑ f ∈ F.toFinset, (D ^ 3 : ℝ) := h_sum_le
      _ = (F.toFinset.card : ℝ) * D ^ 3 := h_sum_const
      _ = (F.card : ℝ) * D ^ 3 := by rw [h_card_eq]
      _ = D ^ 3 * (F.card : ℝ) := by ring

end Kakeya.Cinematic
