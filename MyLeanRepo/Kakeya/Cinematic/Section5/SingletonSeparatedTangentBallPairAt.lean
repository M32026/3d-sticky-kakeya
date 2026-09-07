import MyLeanRepo.Kakeya.Cinematic.Section5.SingletonSeparatedTangentBallPairAtInputs

/-!
# Separated tangent balls from one retained tangent

Construct the `q = 1` separated cluster pair without the average tangent-count
hypothesis used by the general fiberwise pigeonhole.
-/

namespace Kakeya.Cinematic

theorem singleton_separated_tangent_ball_pair_at :
    SingletonSeparatedTangentBallPairAtStatement := by
  classical
  intro delta t r tangency hr H R T hTsub centers hcenters hcover hnonempty
    halltangent hnonconcentration i
  let tangent : Finset C2Function :=
    (T i).toFinset.filter fun f =>
      (R.rectangle i).IsLambdaTangent f tangency
  let ballTangencies (center : C2Function) (radius : ℝ) :
      Finset C2Function :=
    tangent.filter fun f => f ∈ c2Ball center radius
  have hall_tangent : tangent = (T i).toFinset := by
    ext f
    simp only [tangent, Finset.mem_filter]
    constructor
    · rintro ⟨h, _⟩
      exact h
    · intro h
      have hft : f ∈ (T i).carrier := by
        simpa [FiniteFunctionFamily.toFinset] using h
      exact ⟨h, halltangent i f hft⟩
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
  obtain ⟨f, hfT⟩ := hnonempty i
  obtain ⟨c, hc, hfball⟩ :=
    Set.mem_iUnion₂.mp (hcover i hfT)
  have hf_tangent :
      (R.rectangle i).IsLambdaTangent f tangency :=
    halltangent i f hfT
  have hf_in_tangent : f ∈ tangent := by
    rw [hall_tangent]
    simpa [FiniteFunctionFamily.toFinset] using hfT
  have hf_in_11r : f ∈ c2Ball c (11 * r) := by
    have h1 : f ∈ c2Ball c r := hfball
    have h2 : c2Ball c r ⊆ c2Ball c (11 * r) := by
      intro g hg
      simp only [mem_c2Ball] at hg ⊢
      have h3 : r ≤ 11 * r := by linarith
      exact hg.trans h3
    exact h2 h1
  let insideTangencies : Finset C2Function :=
    ballTangencies c (11 * r)
  let outsideTangencies : Finset C2Function :=
    tangent.filter fun f => f ∉ c2Ball c (11 * r)
  have hinside_nonempty : insideTangencies.Nonempty := by
    refine ⟨f, ?_⟩
    exact Finset.mem_filter.mpr ⟨hf_in_tangent, hf_in_11r⟩
  have hinside_pos : 0 < insideTangencies.card :=
    Finset.card_pos.mpr hinside_nonempty
  have hpartition :
      insideTangencies.card + outsideTangencies.card = tangent.card := by
    simpa [insideTangencies, outsideTangencies, ballTangencies] using
      (Finset.card_filter_add_card_filter_not
        (s := tangent)
        (p := fun f => f ∈ c2Ball c (11 * r)))
  have htangent_card :
      RectangleFamily.tangentCount (R.rectangle i) (T i) tangency =
        tangent.card := by
    rfl
  have hnonconc :
      2 * insideTangencies.card ≤ tangent.card := by
    calc
      2 * insideTangencies.card =
          2 * RectangleFamily.tangentCount
            (R.rectangle i) ((T i).cluster c (11 * r)) tangency := by
        rw [show insideTangencies.card =
          RectangleFamily.tangentCount
            (R.rectangle i) ((T i).cluster c (11 * r)) tangency from
              hball_card c (11 * r)]
      _ ≤ RectangleFamily.tangentCount
          (R.rectangle i) (T i) tangency :=
        hnonconcentration i c hc
      _ = tangent.card := htangent_card
  have houtside_pos : 0 < outsideTangencies.card := by
    omega
  have houtside_nonempty : outsideTangencies.Nonempty :=
    Finset.card_pos.mp houtside_pos
  obtain ⟨g, hg_outside⟩ := houtside_nonempty
  have hg_tangent : g ∈ tangent :=
    Finset.filter_subset _ _ hg_outside
  have hgT : g ∈ (T i).carrier := by
    rw [hall_tangent] at hg_tangent
    simpa [FiniteFunctionFamily.toFinset] using hg_tangent
  have hg_outside_11r : g ∉ c2Ball c (11 * r) :=
    (Finset.mem_filter.mp hg_outside).2
  have hg_far : 11 * r < c2Distance g c := by
    simpa only [mem_c2Ball, not_le] using hg_outside_11r
  obtain ⟨d, hd, hgball⟩ :=
    Set.mem_iUnion₂.mp (hcover i hgT)
  have hg_near : c2Distance g d ≤ r := by
    simpa only [mem_c2Ball] using hgball
  have hcd : 10 * r ≤ c2Distance c d := by
    have htriangle :
        c2Distance g c ≤ c2Distance g d + c2Distance d c :=
      dist_triangle g d c
    have hsymm : c2Distance d c = c2Distance c d :=
      dist_comm d c
    linarith
  have hc_count :
      1 ≤ RectangleFamily.tangentCount
        (R.rectangle i) ((T i).cluster c r) tangency := by
    rw [← hball_card c r]
    have h : f ∈ ballTangencies c r :=
      Finset.mem_filter.mpr ⟨hf_in_tangent, hfball⟩
    exact Finset.card_pos.mpr ⟨f, h⟩
  have hd_count :
      1 ≤ RectangleFamily.tangentCount
        (R.rectangle i) ((T i).cluster d r) tangency := by
    rw [← hball_card d r]
    have h : g ∈ ballTangencies d r :=
      Finset.mem_filter.mpr ⟨hg_tangent, hgball⟩
    exact Finset.card_pos.mpr ⟨g, h⟩
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
  · exact hc_count.trans
      (tangentCount_mono ((T i).cluster c r) (H.cluster c r)
        (hcluster_subset c r))
  · exact hd_count.trans
      (tangentCount_mono ((T i).cluster d r) (H.cluster d r)
        (hcluster_subset d r))

end Kakeya.Cinematic
