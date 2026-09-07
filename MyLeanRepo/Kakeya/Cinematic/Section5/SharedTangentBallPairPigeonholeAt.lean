import MyLeanRepo.Kakeya.Cinematic.Section5.LevelSetInputs

/-!
# Shared cluster pair at an arbitrary tangency dilation
-/

namespace Kakeya.Cinematic

theorem shared_tangent_ball_pair_pigeonhole_at :
    SharedTangentBallPairPigeonholeAtStatement := by
  intro delta t r tangency H R hR centers q hPairs
  classical
  choose center₁ hcenter₁ center₂ hcenter₂ hdist hcount₁ hcount₂ hseparated using hPairs
  let pairOf : Fin R.card → C2Function × C2Function :=
    fun i => (center₁ i, center₂ i)
  let usedPairs : Finset (C2Function × C2Function) :=
    Finset.image pairOf Finset.univ
  let fiber (pair : C2Function × C2Function) : Finset (Fin R.card) :=
    Finset.univ.filter fun i => pairOf i = pair
  have husedPairs_nonempty : usedPairs.Nonempty := by
    let i : Fin R.card := ⟨0, hR⟩
    exact ⟨pairOf i, by
      simp only [usedPairs, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨i, rfl⟩⟩
  rcases Finset.exists_max_image usedPairs (fun pair => (fiber pair).card)
      husedPairs_nonempty with
    ⟨pair, hpair_used, hpair_max⟩
  rcases pair with ⟨c, d⟩
  have hpair_witness :
      ∃ i : Fin R.card, pairOf i = (c, d) := by
    simpa only [usedPairs, Finset.mem_image, Finset.mem_univ, true_and] using hpair_used
  rcases hpair_witness with ⟨i₀, hi₀⟩
  have hc_eq : center₁ i₀ = c := congrArg Prod.fst hi₀
  have hd_eq : center₂ i₀ = d := congrArg Prod.snd hi₀
  let embedding : Fin (fiber (c, d)).card ↪ Fin R.card :=
    ((fiber (c, d)).orderEmbOfFin rfl).toEmbedding
  let S : RectangleSubfamily R := {
    card := (fiber (c, d)).card
    embedding := embedding
  }
  have husedPairs_subset : usedPairs ⊆ centers.product centers := by
    intro pair hpair
    rcases Finset.mem_image.mp hpair with ⟨i, _, rfl⟩
    exact Finset.mem_product.mpr ⟨hcenter₁ i, hcenter₂ i⟩
  have husedPairs_card : usedPairs.card ≤ centers.card ^ 2 := by
    calc
      usedPairs.card ≤ (centers.product centers).card :=
        Finset.card_le_card husedPairs_subset
      _ = centers.card ^ 2 := by simp [pow_two]
  have hmapsTo :
      Set.MapsTo pairOf
        (Finset.univ : Finset (Fin R.card))
        usedPairs := by
    intro i _
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  have hcard_eq :
      R.card = ∑ pair ∈ usedPairs, (fiber pair).card := by
    calc
      R.card = (Finset.univ : Finset (Fin R.card)).card := by simp
      _ = ∑ pair ∈ usedPairs,
          ((Finset.univ : Finset (Fin R.card)).filter
            fun i => pairOf i = pair).card :=
        Finset.card_eq_sum_card_fiberwise hmapsTo
      _ = ∑ pair ∈ usedPairs, (fiber pair).card := by rfl
  have hcard :
      R.card ≤ centers.card ^ 2 * S.card := by
    calc
      R.card = ∑ pair ∈ usedPairs, (fiber pair).card := hcard_eq
      _ ≤ ∑ _pair ∈ usedPairs, (fiber (c, d)).card := by
        exact Finset.sum_le_sum fun pair hpair => hpair_max pair hpair
      _ = usedPairs.card * (fiber (c, d)).card := by simp
      _ ≤ centers.card ^ 2 * (fiber (c, d)).card :=
        Nat.mul_le_mul_right (fiber (c, d)).card husedPairs_card
      _ = centers.card ^ 2 * S.card := by rfl
  refine ⟨c, ?_, d, ?_, ?_, ?_, S, hcard, ?_⟩
  · simpa only [hc_eq] using hcenter₁ i₀
  · simpa only [hd_eq] using hcenter₂ i₀
  · simpa only [hc_eq, hd_eq] using hdist i₀
  · simpa only [hc_eq, hd_eq] using hseparated i₀
  · intro j
    have hj_mem : embedding j ∈ fiber (c, d) :=
      Finset.orderEmbOfFin_mem (fiber (c, d)) rfl j
    have hj_pair : pairOf (embedding j) = (c, d) :=
      (Finset.mem_filter.mp hj_mem).2
    have hjc_eq : center₁ (embedding j) = c :=
      congrArg Prod.fst hj_pair
    have hjd_eq : center₂ (embedding j) = d :=
      congrArg Prod.snd hj_pair
    change
      q ≤ RectangleFamily.tangentCount
          (R.rectangle (embedding j)) (H.cluster c r) tangency ∧
        q ≤ RectangleFamily.tangentCount
          (R.rectangle (embedding j)) (H.cluster d r) tangency
    exact ⟨by simpa only [hjc_eq] using hcount₁ (embedding j),
      by simpa only [hjd_eq] using hcount₂ (embedding j)⟩

end Kakeya.Cinematic
