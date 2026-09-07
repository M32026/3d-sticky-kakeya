import MyLeanRepo.Kakeya.Cinematic.Section5.LevelSetInputs

/-!
# Separated clusters at an arbitrary tangency dilation
-/

namespace Kakeya.Cinematic

theorem fiberwise_separated_tangent_ball_pair_at :
    FiberwiseSeparatedTangentBallPairAtStatement := by
  classical
  intro delta t r tangency hr H R _hR T hTsub centers hcenters hcover q hq htotal
    hnonconcentration i
  let tangent : Finset C2Function :=
    (T i).toFinset.filter fun f => (R.rectangle i).IsLambdaTangent f tangency
  let ballTangencies (center : C2Function) (radius : ℝ) :
      Finset C2Function :=
    tangent.filter fun f => f ∈ c2Ball center radius
  have htangent_card :
      tangent.card =
        RectangleFamily.tangentCount (R.rectangle i) (T i) tangency := by
    rfl
  have hball_card (center : C2Function) (radius : ℝ) :
      (ballTangencies center radius).card =
        RectangleFamily.tangentCount
          (R.rectangle i) ((T i).cluster center radius) tangency := by
    dsimp only [ballTangencies, tangent]
    unfold RectangleFamily.tangentCount
    congr 1
    ext f
    simp [FiniteFunctionFamily.toFinset, FiniteFunctionFamily.cluster]
    aesop
  have tangentCount_mono
      (F G : FiniteFunctionFamily)
      (hFG : F.carrier ⊆ G.carrier) :
      RectangleFamily.tangentCount (R.rectangle i) F tangency ≤
        RectangleFamily.tangentCount (R.rectangle i) G tangency := by
    unfold RectangleFamily.tangentCount
    apply Finset.card_le_card
    intro f hf
    have hf' := Finset.mem_filter.mp hf
    exact Finset.mem_filter.mpr
      ⟨by
        simpa [FiniteFunctionFamily.toFinset] using
          hFG (by
            simpa [FiniteFunctionFamily.toFinset] using hf'.1),
        hf'.2⟩
  have hcluster_subset (center : C2Function) (radius : ℝ) :
      ((T i).cluster center radius).carrier ⊆
        (H.cluster center radius).carrier := by
    intro f hf
    exact ⟨hTsub i hf.1, hf.2⟩
  have exists_large_piece
      (s : Finset C2Function)
      (pieces : C2Function → Finset C2Function)
      (m : ℕ)
      (hcovered : s ⊆ centers.biUnion pieces)
      (hlower : centers.card * m ≤ s.card) :
      ∃ center ∈ centers, m ≤ (pieces center).card := by
    have hcard : s.card ≤ ∑ center ∈ centers, (pieces center).card :=
      (Finset.card_le_card hcovered).trans Finset.card_biUnion_le
    by_contra hexists
    push Not at hexists
    have hsum_lt :
        (∑ center ∈ centers, (pieces center).card) <
          ∑ _center ∈ centers, m := by
      apply Finset.sum_lt_sum
      · intro center hcenter
        exact (hexists center hcenter).le
      · obtain ⟨center, hcenter⟩ := hcenters
        exact ⟨center, hcenter, hexists center hcenter⟩
    simp only [Finset.sum_const, smul_eq_mul] at hsum_lt
    omega
  have htangent_cover :
      tangent ⊆ centers.biUnion fun center => ballTangencies center r := by
    intro f hf
    have hf' :
        f ∈ (T i).toFinset ∧
          (R.rectangle i).IsLambdaTangent f tangency := by
      simpa [tangent] using hf
    have hfT : f ∈ (T i).carrier := by
      simpa [FiniteFunctionFamily.toFinset] using hf'.1
    obtain ⟨center, hcenter, hfball⟩ :=
      Set.mem_iUnion₂.mp (hcover i hfT)
    exact Finset.mem_biUnion.mpr
      ⟨center, hcenter, Finset.mem_filter.mpr ⟨hf, hfball⟩⟩
  have htotal_tangent : 2 * centers.card * q ≤ tangent.card := by
    rw [htangent_card]
    exact htotal i
  have hpigeon_lower : centers.card * (2 * q) ≤ tangent.card := by
    calc
      centers.card * (2 * q) = 2 * centers.card * q := by ring
      _ ≤ tangent.card := htotal_tangent
  obtain ⟨c, hc, hc_count⟩ :=
    exists_large_piece tangent (fun center => ballTangencies center r)
      (2 * q) htangent_cover hpigeon_lower
  let largeTangencies : Finset C2Function :=
    ballTangencies c (11 * r)
  let outsideTangencies : Finset C2Function :=
    tangent.filter fun f => f ∉ c2Ball c (11 * r)
  have hlarge_nonconcentration :
      2 * largeTangencies.card ≤ tangent.card := by
    calc
      2 * largeTangencies.card =
          2 * RectangleFamily.tangentCount
            (R.rectangle i) ((T i).cluster c (11 * r)) tangency := by
              rw [show largeTangencies.card =
                RectangleFamily.tangentCount
                  (R.rectangle i) ((T i).cluster c (11 * r)) tangency from
                    hball_card c (11 * r)]
      _ ≤ RectangleFamily.tangentCount (R.rectangle i) (T i) tangency :=
        hnonconcentration i c hc
      _ = tangent.card := htangent_card.symm
  have hpartition :
      largeTangencies.card + outsideTangencies.card = tangent.card := by
    simpa [largeTangencies, outsideTangencies, ballTangencies] using
      (Finset.card_filter_add_card_filter_not
        (s := tangent) (p := fun f => f ∈ c2Ball c (11 * r)))
  have houtside_lower :
      centers.card * q ≤ outsideTangencies.card := by
    have htwice_lower : 2 * (centers.card * q) ≤ tangent.card := by
      calc
        2 * (centers.card * q) = 2 * centers.card * q := by ring
        _ ≤ tangent.card := htotal_tangent
    omega
  let outsideBallTangencies (center : C2Function) :
      Finset C2Function :=
    outsideTangencies.filter fun f => f ∈ c2Ball center r
  have houtside_cover :
      outsideTangencies ⊆ centers.biUnion outsideBallTangencies := by
    intro f hf
    have hftangent : f ∈ tangent :=
      Finset.filter_subset
        (fun f => f ∉ c2Ball c (11 * r)) tangent hf
    have hf' :
        f ∈ (T i).toFinset ∧
          (R.rectangle i).IsLambdaTangent f tangency := by
      simpa [tangent] using hftangent
    have hfT : f ∈ (T i).carrier := by
      simpa [FiniteFunctionFamily.toFinset] using hf'.1
    obtain ⟨center, hcenter, hfball⟩ :=
      Set.mem_iUnion₂.mp (hcover i hfT)
    exact Finset.mem_biUnion.mpr
      ⟨center, hcenter, Finset.mem_filter.mpr ⟨hf, hfball⟩⟩
  obtain ⟨d, hd, hd_outside_count⟩ :=
    exists_large_piece outsideTangencies outsideBallTangencies q
      houtside_cover houtside_lower
  have houtsideBall_subset :
      outsideBallTangencies d ⊆ ballTangencies d r := by
    intro f hf
    have hf' := Finset.mem_filter.mp hf
    have hftangent : f ∈ tangent :=
      Finset.filter_subset
        (fun f => f ∉ c2Ball c (11 * r)) tangent hf'.1
    exact Finset.mem_filter.mpr ⟨hftangent, hf'.2⟩
  have hd_count : q ≤ (ballTangencies d r).card :=
    hd_outside_count.trans (Finset.card_le_card houtsideBall_subset)
  have houtsideBall_nonempty :
      (outsideBallTangencies d).Nonempty := by
    exact Finset.card_pos.mp (hq.trans_le hd_outside_count)
  obtain ⟨f, hf⟩ := houtsideBall_nonempty
  have hf' := Finset.mem_filter.mp hf
  have hfoutside := Finset.mem_filter.mp hf'.1
  have hfc_far : 11 * r < c2Distance f c := by
    simpa only [mem_c2Ball, not_le] using hfoutside.2
  have hfd_near : c2Distance f d ≤ r := by
    simpa only [mem_c2Ball] using hf'.2
  have hcd : 10 * r ≤ c2Distance c d := by
    have htriangle :
        c2Distance f c ≤ c2Distance f d + c2Distance d c := by
      exact dist_triangle f d c
    have hsymm : c2Distance d c = c2Distance c d :=
      dist_comm d c
    linarith
  have hseparated :
      (H.cluster c r).AreSeparated (H.cluster d r) (8 * r) := by
    intro w hw b hb
    have hw_near : dist c w ≤ r := by
      have hw' : c2Distance w c ≤ r := by
        simpa only [mem_c2Ball] using hw.2
      simpa only [c2Distance_eq_dist, dist_comm] using hw'
    have hb_near : dist b d ≤ r := by
      have hb' : c2Distance b d ≤ r := by
        simpa only [mem_c2Ball] using hb.2
      exact hb'
    have htriangle := dist_triangle4 c w b d
    have hcd' : 10 * r ≤ dist c d := hcd
    linarith
  refine ⟨c, hc, d, hd, hcd, ?_, ?_, hseparated⟩
  · have hT_count :
        q ≤ RectangleFamily.tangentCount
          (R.rectangle i) ((T i).cluster c r) tangency := by
      rw [← hball_card c r]
      omega
    exact hT_count.trans
      (tangentCount_mono ((T i).cluster c r) (H.cluster c r)
        (hcluster_subset c r))
  · have hT_count :
        q ≤ RectangleFamily.tangentCount
          (R.rectangle i) ((T i).cluster d r) tangency := by
      rw [← hball_card d r]
      exact hd_count
    exact hT_count.trans
      (tangentCount_mono ((T i).cluster d r) (H.cluster d r)
        (hcluster_subset d r))

end Kakeya.Cinematic
