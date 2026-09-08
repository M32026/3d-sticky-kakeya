import MyLeanRepo.Kakeya.Streamlined.Estimates
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.TubeVolume

/-!
# Fine deltaMax from coarse Katz-Tao at the same scale

At the same scale δ, tube containment forces equality, ED forces singleton
fibers, so the parent map is a bijection and `F.deltaMax = G.deltaMax`.
-/

noncomputable section

open MeasureTheory Kakeya.Streamlined

namespace Kakeya.Streamlined

/-- Convert a `TubeCover` to a `Factoring` on the underlying body families. -/
private def TubeCover.toFactoring' {δ ρ : ℝ} {F : TubeFamily δ} {G : TubeFamily ρ}
    (P : TubeCover F G) : Factoring F.toBodyFamily G.toBodyFamily :=
  { parent := P.parent
    parent_surjective := P.parent_surjective
    contained := P.nested }

/-- If `s ⊆ t` are closed, `t` convex with nonempty interior, and
`volume s = volume t < ⊤`, then `s = t`. -/
private lemma convex_closed_subset_eq_of_volume_eq {s t : Set Point3}
    (hs : IsClosed s) (ht : IsClosed t)
    (hconv_t : Convex ℝ t)
    (hsub : s ⊆ t) (hvol : volume s = volume t)
    (htop : volume t ≠ ⊤) (ht_int : (interior t).Nonempty) :
    s = t := by
  by_contra h
  have h1 : ¬ (interior t ⊆ s) := by
    intro h2
    have h3 : closure (interior t) ⊆ s := closure_minimal h2 hs
    have h4 : closure (interior t) = t := by
      have h5 : closure (interior t) = closure t :=
        hconv_t.closure_interior_eq_closure_of_nonempty_interior ht_int
      rw [h5, ht.closure_eq]
    rw [h4] at h3
    have h6 : t ⊆ s := h3
    exact h (Set.Subset.antisymm hsub h6)
  have h2 : ∃ (x : Point3), x ∈ interior t ∧ x ∉ s := by
    simpa [Set.not_subset] using h1
  rcases h2 with ⟨x, hx_int, hx_ns⟩
  have hsc : IsOpen (sᶜ) := isOpen_compl_iff.mpr hs
  have h3 : IsOpen (interior t ∩ sᶜ) := isOpen_interior.inter hsc
  have h4 : x ∈ interior t ∩ sᶜ := ⟨hx_int, hx_ns⟩
  rcases Metric.isOpen_iff.mp h3 x h4 with ⟨ε, hε_pos, hball⟩
  have h5 : Metric.ball x ε ⊆ t \ s := by
    intro y hy
    have h6 : y ∈ interior t ∩ sᶜ := hball hy
    exact ⟨interior_subset h6.1, h6.2⟩
  have h6 : 0 < volume (Metric.ball x ε) :=
    Metric.measure_ball_pos volume x hε_pos
  have h7 : 0 < volume (t \ s) :=
    lt_of_lt_of_le h6 (measure_mono h5)
  have h_ms : MeasurableSet s := hs.measurableSet
  have h_mt : MeasurableSet t := ht.measurableSet
  have h_mdiff : MeasurableSet (t \ s) := h_mt.diff h_ms
  have h_dis : Disjoint s (t \ s) := by
    rw [Set.disjoint_left]
    intro z hz1 hz2
    exact hz2.2 hz1
  have h_union : s ∪ (t \ s) = t := by
    ext z
    simp only [Set.mem_union, Set.mem_sdiff]
    constructor
    · rintro (h | h)
      · exact hsub h
      · exact h.1
    · intro hz
      by_cases h : z ∈ s
      · exact Or.inl h
      · exact Or.inr ⟨hz, h⟩
  have h_eq : volume (s ∪ (t \ s)) = volume s + volume (t \ s) :=
    measure_union h_dis h_mdiff
  have h9 : volume t = volume s + volume (t \ s) := by
    have h10 : s ∪ (t \ s) = t := h_union
    rw [h10] at h_eq
    exact h_eq
  have h10 : volume t + volume (t \ s) = volume t := by
    rw [hvol] at h9
    exact h9.symm
  have h11 : volume (t \ s) + volume t = 0 + volume t := by
    have h11a : volume (t \ s) + volume t = volume t + volume (t \ s) := by apply add_comm
    rw [h11a, h10]
    simp
  have h12 : volume (t \ s) = 0 := (ENNReal.add_left_inj htop).mp h11
  rw [h12] at h7
  exact False.elim (lt_irrefl 0 h7)

/-- The unit segment is convex. -/
private lemma unitSegment_convex (base direction : Point3) :
    Convex ℝ (unitSegment base direction) := by
  have h_sub : (base + direction) - base = direction := by simp
  have h_eq : unitSegment base direction = segment ℝ base (base + direction) := by
    rw [segment_eq_image']
    apply Set.ext
    intro x
    simp only [unitSegment, Set.mem_image]
    constructor
    · rintro ⟨t, ht, hxt⟩
      refine ⟨t, ht, ?_⟩
      rw [h_sub] at *
      exact hxt
    · rintro ⟨t, ht, hxt⟩
      refine ⟨t, ht, ?_⟩
      rw [h_sub] at *
      exact hxt
  rw [h_eq]
  exact convex_segment _ _

/-- A `δ`-tube is convex. -/
private lemma deltaTube_convex {δ : ℝ} (hδ : 0 < δ)
    (T : Kakeya.DeltaTube δ) : Convex ℝ T.carrier := by
  have h_seg_conv : Convex ℝ (unitSegment T.base T.direction) :=
    unitSegment_convex T.base T.direction
  exact h_seg_conv.cthickening δ

/-- A `δ`-tube has nonempty interior for `δ > 0`. -/
private lemma deltaTube_interior_nonempty {δ : ℝ} (hδ : 0 < δ)
    (T : Kakeya.DeltaTube δ) : (interior T.carrier).Nonempty := by
  let m : Point3 := T.base + (1 / 2 : ℝ) • T.direction
  have hm_in_seg : m ∈ unitSegment T.base T.direction := by
    refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
    simp [m] <;> abel
  have h_ball : Metric.ball m (δ / 2) ⊆ T.carrier := by
    intro x hx
    have h_lt : dist x m < δ / 2 := by
      simpa [Metric.mem_ball] using hx
    have h_le : dist x m ≤ δ := by linarith
    exact Metric.mem_cthickening_of_dist_le x m δ (unitSegment T.base T.direction) hm_in_seg h_le
  have h_ball_sub : Metric.ball m (δ / 2) ⊆ interior T.carrier := by
    intro y hy
    have h10 : Metric.ball m (δ / 2) ∈ nhds y :=
      IsOpen.mem_nhds Metric.isOpen_ball hy
    have h11 : T.carrier ∈ nhds y := Filter.mem_of_superset h10 h_ball
    exact mem_interior_iff_mem_nhds.mpr h11
  have h : m ∈ interior T.carrier := h_ball_sub (Metric.mem_ball_self (by linarith))
  exact ⟨m, h⟩

/-- A `δ`-tube has positive volume. -/
private lemma deltaTube_volume_pos {δ : ℝ} (hδ : 0 < δ)
    (T : Kakeya.DeltaTube δ) : 0 < T.volume := by
  have h_int : (interior T.carrier).Nonempty := deltaTube_interior_nonempty hδ T
  rcases h_int with ⟨x, hx⟩
  have h_open : IsOpen (interior T.carrier) := isOpen_interior
  rcases Metric.isOpen_iff.mp h_open x hx with ⟨ε, hε_pos, hball⟩
  have hball2 : Metric.ball x ε ⊆ T.carrier := by
    intro y hy
    exact interior_subset (hball hy)
  have h7 : 0 < volume (Metric.ball x ε) := Metric.measure_ball_pos volume x hε_pos
  exact lt_of_lt_of_le h7 (measure_mono hball2)

/-- A `δ`-tube has finite volume. -/
private lemma deltaTube_volume_lt_top {δ : ℝ} (hδ : 0 < δ)
    (T : Kakeya.DeltaTube δ) : T.volume ≠ ⊤ := by
  have h_seg_bdd : Bornology.IsBounded (unitSegment T.base T.direction) := by
    have h1 : unitSegment T.base T.direction ⊆ Metric.closedBall T.base 1 := by
      intro x hx
      rcases hx with ⟨t, ⟨ht0, ht1⟩, rfl⟩
      have h2 : dist (T.base + t • T.direction) T.base ≤ 1 := by
        have h3 : dist (T.base + t • T.direction) T.base = ‖t • T.direction‖ := by
          simp [dist_eq_norm]
        rw [h3]
        have h4 : ‖t • T.direction‖ = |t| * ‖T.direction‖ := by
          simpa [norm_smul] using rfl
        rw [h4, T.direction_unit]
        have h5 : |t| = t := abs_of_nonneg ht0
        rw [h5] <;> linarith
      exact h2
    exact Metric.isBounded_closedBall.subset h1
  have h_bdd : Bornology.IsBounded T.carrier := h_seg_bdd.cthickening
  exact h_bdd.measure_lt_top.ne

/-- If two `δ`-tubes have one carrier contained in the other, they are equal. -/
lemma deltaTube_carrier_eq_of_subset {δ : ℝ} (hδ : 0 < δ)
    {T U : Kakeya.DeltaTube δ} (h : T.carrier ⊆ U.carrier) :
    T.carrier = U.carrier := by
  have h_vol : T.volume = U.volume := tube_volume_eq T U
  have hT_closed : IsClosed T.carrier := Metric.isClosed_cthickening
  have hU_closed : IsClosed U.carrier := Metric.isClosed_cthickening
  have hU_conv : Convex ℝ U.carrier := deltaTube_convex hδ U
  have hU_top : U.volume ≠ ⊤ := deltaTube_volume_lt_top hδ U
  have hU_int : (interior U.carrier).Nonempty := deltaTube_interior_nonempty hδ U
  exact convex_closed_subset_eq_of_volume_eq hT_closed hU_closed hU_conv h h_vol hU_top hU_int

/-- At the same scale, an ED fine family has singleton fibers in any cover. -/
lemma tubeCover_fiber_singleton {δ : ℝ} (hδ : 0 < δ)
    {F : TubeFamily δ} {G : TubeFamily δ}
    (hF_ed : F.IsEssentiallyDistinct)
    (P : TubeCover F G) :
    ∀ (j : Fin G.card), (P.toFactoring'.fiberIndices j).card = 1 := by
  intro j
  let fiber := P.toFactoring'.fiberIndices j
  have h_surj : ∃ i, P.parent i = j := P.parent_surjective j
  rcases h_surj with ⟨i, hi⟩
  have h1 : i ∈ fiber := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
  have h_card_pos : 0 < fiber.card := Finset.card_pos.mpr ⟨i, h1⟩
  by_contra h
  have h_ne_one : fiber.card ≠ 1 := h
  have h_ge2 : 2 ≤ fiber.card := by
    by_contra h2
    have h3 : fiber.card < 2 := by omega
    have h4 : fiber.card = 0 ∨ fiber.card = 1 := by omega
    rcases h4 with (h4 | h4)
    · have h5 : 0 < fiber.card := h_card_pos
      rw [h4] at h5
      <;> simp at h5
    · exact h_ne_one h4
  have h_exists : ∃ (a : Fin F.card), a ∈ fiber ∧ ∃ (b : Fin F.card), b ∈ fiber ∧ a ≠ b :=
    Finset.one_lt_card.mp (show 1 < fiber.card from by omega)
  rcases h_exists with ⟨i1, hi1, i2, hi2, hne⟩
  have h_p1 : P.parent i1 = j := (Finset.mem_filter.mp hi1).2
  have h_p2 : P.parent i2 = j := (Finset.mem_filter.mp hi2).2
  have h_sub1 : (F.tube i1).carrier ⊆ (G.tube j).carrier := by
    have h := P.nested i1
    rw [h_p1] at h
    exact h
  have h_sub2 : (F.tube i2).carrier ⊆ (G.tube j).carrier := by
    have h := P.nested i2
    rw [h_p2] at h
    exact h
  have h_eq1 : (F.tube i1).carrier = (G.tube j).carrier :=
    deltaTube_carrier_eq_of_subset hδ h_sub1
  have h_eq2 : (F.tube i2).carrier = (G.tube j).carrier :=
    deltaTube_carrier_eq_of_subset hδ h_sub2
  have h_eq3 : (F.tube i1).carrier = (F.tube i2).carrier :=
    h_eq1.trans h_eq2.symm
  have h_vol_pos : 0 < (F.tube i1).volume := deltaTube_volume_pos hδ (F.tube i1)
  have h_inter_vol : volume ((F.tube i1).carrier ∩ (F.tube i2).carrier) =
      (F.tube i1).volume := by
    have h_set : (F.tube i1).carrier ∩ (F.tube i2).carrier = (F.tube i1).carrier := by
      rw [h_eq3]
      exact Set.inter_self _
    rw [h_set]
    <;> rfl
  have h_ed : (F.tube i1).EssentiallyDistinct (F.tube i2) := hF_ed i1 i2 hne
  have h_eq4 : (F.tube i2).volume = (F.tube i1).volume := by
    simp [DeltaTube.volume, h_eq3]
  have h_max : max (F.tube i1).volume (F.tube i2).volume = (F.tube i1).volume := by
    rw [h_eq4]
    <;> simp
  have h_ed2 : volume ((F.tube i1).carrier ∩ (F.tube i2).carrier) ≤
      (2 : ENNReal)⁻¹ * max (F.tube i1).volume (F.tube i2).volume := h_ed
  rw [h_inter_vol, h_max] at h_ed2
  have h_ne_zero : (F.tube i1).volume ≠ 0 := h_vol_pos.ne'
  have h_ne_top : (F.tube i1).volume ≠ ⊤ := deltaTube_volume_lt_top hδ (F.tube i1)
  have h_lt : (2 : ENNReal)⁻¹ * (F.tube i1).volume < (F.tube i1).volume := by
    have h_comm : (2 : ENNReal)⁻¹ * (F.tube i1).volume =
        (F.tube i1).volume * (2 : ENNReal)⁻¹ := mul_comm _ _
    rw [h_comm]
    have h_div : (F.tube i1).volume * (2 : ENNReal)⁻¹ = (F.tube i1).volume / 2 := by rfl
    rw [h_div]
    exact ENNReal.half_lt_self h_ne_zero h_ne_top
  exact not_le.mpr h_lt h_ed2

/-- The fine deltaMax equals the coarse deltaMax when both are at the same
scale and the fine family is essentially distinct. -/
theorem fine_deltaMax_eq_coarse_deltaMax {δ : ℝ} (hδ : 0 < δ)
    {F : TubeFamily δ} {G : TubeFamily δ}
    (hF_ed : F.IsEssentiallyDistinct)
    (P : TubeCover F G) :
    F.toBodyFamily.deltaMax = G.toBodyFamily.deltaMax := by
  let P' := P.toFactoring'
  have h_fiber_singleton : ∀ j, (P'.fiberIndices j).card = 1 :=
    tubeCover_fiber_singleton hδ hF_ed P
  have h_parent_inj : Function.Injective P.parent := by
    intro i1 i2 h_eq
    let j := P.parent i1
    have h_j1 : P.parent i1 = j := by rfl
    have h_j2 : P.parent i2 = j := h_eq.symm
    have h1 : i1 ∈ P'.fiberIndices j := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i1, h_j1⟩
    have h2 : i2 ∈ P'.fiberIndices j := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i2, h_j2⟩
    have h_card : (P'.fiberIndices j).card = 1 := h_fiber_singleton j
    rcases Finset.card_eq_one.mp h_card with ⟨a, ha⟩
    have h_i1_in : i1 ∈ ({a} : Finset (Fin F.card)) := by
      rw [ha] at h1
      exact h1
    have h_i1_eq : i1 = a := Finset.mem_singleton.mp h_i1_in
    have h_i2_in : i2 ∈ ({a} : Finset (Fin F.card)) := by
      rw [ha] at h2
      exact h2
    have h_i2_eq : i2 = a := Finset.mem_singleton.mp h_i2_in
    have h_goal : i1 = i2 := by
      rw [h_i1_eq, h_i2_eq]
    exact h_goal
  have h_parent_bij : Function.Bijective P.parent :=
    ⟨h_parent_inj, P.parent_surjective⟩
  have h_carrier_eq : ∀ (i : Fin F.card),
      (F.tube i).carrier = (G.tube (P.parent i)).carrier := by
    intro i
    have h_sub : (F.tube i).carrier ⊆ (G.tube (P.parent i)).carrier := P.nested i
    exact deltaTube_carrier_eq_of_subset hδ h_sub
  have h_mass_eq : ∀ (i : Fin F.card),
      (F.toBodyFamily.body i).volume = (G.toBodyFamily.body (P.parent i)).volume := by
    intro i
    have h_eq : (F.tube i).carrier = (G.tube (P.parent i)).carrier := h_carrier_eq i
    have h_car1 : (F.toBodyFamily.body i).carrier = (F.tube i).carrier := by rfl
    have h_car2 : (G.toBodyFamily.body (P.parent i)).carrier = (G.tube (P.parent i)).carrier := by rfl
    have h_vol1 : (F.toBodyFamily.body i).volume = volume (F.toBodyFamily.body i).carrier := by rfl
    have h_vol2 : (G.toBodyFamily.body (P.parent i)).volume = volume (G.toBodyFamily.body (P.parent i)).carrier := by rfl
    rw [h_vol1, h_vol2, h_car1, h_car2, h_eq]
  have h_containment_iff : ∀ (i : Fin F.card) (K : Set Point3),
      (F.tube i).carrier ⊆ K ↔ (G.tube (P.parent i)).carrier ⊆ K := by
    intro i K
    rw [h_carrier_eq i]
  have h_density_eq : ∀ (K : Set Point3),
      F.toBodyFamily.density K = G.toBodyFamily.density K := by
    intro K
    classical
    have h_carrier_eq' : ∀ (i : Fin F.toBodyFamily.card),
        (F.toBodyFamily.body i).carrier = (G.toBodyFamily.body (P'.parent i)).carrier := by
      intro i
      have h_sub : (F.toBodyFamily.body i).carrier ⊆ (G.toBodyFamily.body (P'.parent i)).carrier := P'.contained i
      exact deltaTube_carrier_eq_of_subset hδ h_sub
    have h_mass_eq' : ∀ (i : Fin F.toBodyFamily.card),
        (F.toBodyFamily.body i).volume = (G.toBodyFamily.body (P'.parent i)).volume := by
      intro i
      have h_eq : (F.toBodyFamily.body i).carrier = (G.toBodyFamily.body (P'.parent i)).carrier := h_carrier_eq' i
      have h1 : (F.toBodyFamily.body i).volume = volume (F.toBodyFamily.body i).carrier := by rfl
      have h2 : (G.toBodyFamily.body (P'.parent i)).volume = volume (G.toBodyFamily.body (P'.parent i)).carrier := by rfl
      rw [h1, h2, h_eq]
    have h_image : Finset.image P'.parent (F.toBodyFamily.containedIndices K) =
        G.toBodyFamily.containedIndices K := by
      ext j
      simp only [BodyFamily.containedIndices, Finset.mem_image, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, hi, rfl⟩
        have h_sub : (G.toBodyFamily.body (P'.parent i)).carrier ⊆ K := by
          have h_eq : (F.toBodyFamily.body i).carrier = (G.toBodyFamily.body (P'.parent i)).carrier :=
            h_carrier_eq' i
          rw [←h_eq]
          exact hi
        exact h_sub
      · intro hj
        rcases P'.parent_surjective j with ⟨i, hpi⟩
        have h7 : (F.toBodyFamily.body i).carrier ⊆ K := by
          have h_eq : (F.toBodyFamily.body i).carrier = (G.toBodyFamily.body (P'.parent i)).carrier :=
            h_carrier_eq' i
          rw [h_eq, hpi]
          exact hj
        exact ⟨i, h7, hpi⟩
    have h_cm : F.toBodyFamily.containedMass K = G.toBodyFamily.containedMass K := by
      rw [BodyFamily.containedMass, BodyFamily.containedMass]
      have h_sum1 : ∑ i ∈ F.toBodyFamily.containedIndices K, (F.toBodyFamily.body i).volume =
          ∑ i ∈ F.toBodyFamily.containedIndices K, (G.toBodyFamily.body (P'.parent i)).volume := by
        apply Finset.sum_congr rfl
        intro i _
        exact h_mass_eq' i
      have h_inj : Set.InjOn P'.parent (F.toBodyFamily.containedIndices K) :=
        fun x _ y _ h => h_parent_inj h
      let f_sum : Fin G.toBodyFamily.card → ENNReal := fun j => (G.toBodyFamily.body j).volume
      have h_sum2 : ∑ i ∈ F.toBodyFamily.containedIndices K, f_sum (P'.parent i) =
          ∑ j ∈ Finset.image P'.parent (F.toBodyFamily.containedIndices K), f_sum j :=
        (Finset.sum_image h_inj).symm
      rw [h_sum1, h_sum2, h_image]
    rw [BodyFamily.density, BodyFamily.density, h_cm]
  have h_set_eq : {d : ENNReal | ∃ (K : Set Point3), Convex ℝ K ∧ d = F.toBodyFamily.density K} =
      {d : ENNReal | ∃ (K : Set Point3), Convex ℝ K ∧ d = G.toBodyFamily.density K} := by
    ext d
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨K, hK, rfl⟩
      exact ⟨K, hK, h_density_eq K⟩
    · rintro ⟨K, hK, rfl⟩
      exact ⟨K, hK, (h_density_eq K).symm⟩
  have h_main : F.toBodyFamily.deltaMax = G.toBodyFamily.deltaMax := by
    simp only [BodyFamily.deltaMax]
    <;> congr
    <;> exact h_set_eq
  exact h_main

/-- Fine deltaMax from coarse Katz-Tao at scale δ.

Requires `δ ≤ 1` so that `δ` is an admissible scale.
-/
theorem fine_deltaMax_from_coarse_at_delta
    {δ : ℝ} {F : TubeFamily δ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hF_ed : F.IsEssentiallyDistinct)
    (U : UniformTubeStructure F)
    {C_KT : ENNReal}
    (hKT : U.IsKatzTaoAtEveryScale C_KT) :
    F.toBodyFamily.deltaMax ≤ U.uniformity ^ 2 * C_KT := by
  let rho : AdmissibleScale δ := ⟨δ, by linarith, by linarith⟩
  let G := U.coarse rho
  let P := U.cover rho
  have h_eq : F.toBodyFamily.deltaMax = G.toBodyFamily.deltaMax :=
    fine_deltaMax_eq_coarse_deltaMax hδ hF_ed P
  have h_G_KT : G.toBodyFamily.deltaMax ≤ C_KT := hKT rho
  have h1 : F.toBodyFamily.deltaMax ≤ C_KT := by
    rw [h_eq]
    exact h_G_KT
  have h3 : 1 ≤ U.uniformity := U.one_le_uniformity
  have h4 : 1 ≤ U.uniformity ^ 2 := by
    calc 1
      = 1 * 1 := by ring
    _ ≤ U.uniformity * U.uniformity := by gcongr
    _ = U.uniformity ^ 2 := by ring
  have h5 : C_KT ≤ U.uniformity ^ 2 * C_KT := by
    calc C_KT
      = 1 * C_KT := by simp
    _ ≤ U.uniformity ^ 2 * C_KT := by gcongr <;> exact h4
  exact h1.trans h5

end Kakeya.Streamlined
