module

/-
# Regular Set Bounded Energy

Construct a probability measure on a (δ,2s)-regular planar set P with
bounded 2κ-Riesz energy.

## Proof route

1. Construct S: one representative point per δ-cube meeting P.
2. Convert IsDeltaSCSet to ball-counting bound for S (constant 9C) via DeltaSCToBallCounting.
3. Prove energy bound using max(dist,δ) regularization and dyadic annulus decomposition.
4. Define ν = normalized counting measure on S (in RegularSetHasBoundedEnergy).

## Constant

Proved energy constant:
  `1 + Cball*(1 - 2^(2(κ-s)) + 2^(2κ)) / (1 - 2^(2(κ-s)))`
where Cball = 9*C from the ball-covering bound.

## Whiteprint node
Helper for KaufmanProjection energy axiom (H3).
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.Compat
public import MyLeanRepo.CoveringToFinset
public import MyLeanRepo.OSWPrelude

@[expose] public section


noncomputable section

open MeasureTheory ENNReal Finset Set Bornology Classical BigOperators

namespace robust_projection

/-! ### Representative set construction -/

/-- The δ-cubes meeting P, as a finset. -/
def energyCubesFinset (δ : ℝ) (P : Set (EuclideanSpace ℝ (Fin 2)))
    (hδ : 0 < δ) (hP_bdd : Bornology.IsBounded P) :
    Finset (Set (EuclideanSpace ℝ (Fin 2))) :=
  (ProductLikeIncidence.dyadicCubesMeeting_finite hδ hP_bdd).toFinset

/-- Choose a representative point in Q ∩ P. -/
def energyCubeRep (δ : ℝ) (P : Set (EuclideanSpace ℝ (Fin 2)))
    (Q : Set (EuclideanSpace ℝ (Fin 2))) :
    EuclideanSpace ℝ (Fin 2) :=
  if h : (Q ∩ P).Nonempty then Classical.choose h else 0

lemma energyCubeRep_mem {δ P Q} (hQ : Q ∈ dyadicCubesMeeting δ P) :
    energyCubeRep δ P Q ∈ Q ∩ P := by
  have h_nonempty : (Q ∩ P).Nonempty := hQ.2
  have h : energyCubeRep δ P Q = Classical.choose h_nonempty := by
    rw [energyCubeRep, dif_pos h_nonempty]
  rw [h]
  exact Classical.choose_spec h_nonempty

lemma energyCubesFinset_mem {δ P hδ hP_bdd Q} :
    Q ∈ energyCubesFinset δ P hδ hP_bdd ↔ Q ∈ dyadicCubesMeeting δ P :=
  Set.Finite.mem_toFinset _

/-- Representative finset: one point per δ-cube meeting P. -/
def energyRepFinset (δ : ℝ) (P : Set (EuclideanSpace ℝ (Fin 2)))
    (hδ : 0 < δ) (hP_bdd : Bornology.IsBounded P) :
    Finset (EuclideanSpace ℝ (Fin 2)) :=
  (energyCubesFinset δ P hδ hP_bdd).image (energyCubeRep δ P)

lemma energyRepFinset_injective {δ P hδ hP_bdd} :
    Set.InjOn (energyCubeRep δ P) (energyCubesFinset δ P hδ hP_bdd : Set _) := by
  intro Q1 hQ1 Q2 hQ2 h
  have h1 : Q1 ∈ dyadicCubesMeeting δ P := energyCubesFinset_mem.mp hQ1
  have h2 : Q2 ∈ dyadicCubesMeeting δ P := energyCubesFinset_mem.mp hQ2
  have hp1 : energyCubeRep δ P Q1 ∈ Q1 := (energyCubeRep_mem h1).1
  have hp2 : energyCubeRep δ P Q2 ∈ Q2 := (energyCubeRep_mem h2).1
  rw [h] at hp1
  have h_in_both : energyCubeRep δ P Q2 ∈ Q1 ∩ Q2 := ⟨hp1, hp2⟩
  rcases h1 with ⟨⟨k1, rfl⟩, _⟩
  rcases h2 with ⟨⟨k2, rfl⟩, _⟩
  by_cases hk : k1 = k2
  · congr
  · have h_disj : Disjoint (dyadicCube δ k1) (dyadicCube δ k2) :=
      dyadic_cubes_disjoint hδ hk
    have h_empty : (dyadicCube δ k1) ∩ (dyadicCube δ k2) = ∅ :=
      Set.disjoint_iff_inter_eq_empty.mp h_disj
    rw [h_empty] at h_in_both
    simpa using h_in_both

lemma energyRepFinset_card {δ P hδ hP_bdd} :
    (energyRepFinset δ P hδ hP_bdd).card =
      (energyCubesFinset δ P hδ hP_bdd).card := by
  have h : Set.InjOn (energyCubeRep δ P) (energyCubesFinset δ P hδ hP_bdd : Set _) :=
    energyRepFinset_injective
  have h_img : ((energyCubesFinset δ P hδ hP_bdd).image (energyCubeRep δ P)).card =
      (energyCubesFinset δ P hδ hP_bdd).card :=
    Finset.card_image_iff.mpr h
  dsimp only [energyRepFinset]
  exact h_img

lemma energyRepFinset_card_ENNReal {δ P hδ hP_bdd} :
    ((energyRepFinset δ P hδ hP_bdd).card : ENNReal) = Nplane δ P := by
  let C := energyCubesFinset δ P hδ hP_bdd
  have h_fin : Set.Finite (dyadicCubesMeeting δ P) :=
    ProductLikeIncidence.dyadicCubesMeeting_finite hδ hP_bdd
  have h1 : (C.card : ENNReal) = ENat.toENNReal (dyadicCubesMeeting δ P).encard := by
    have h_eq : C = h_fin.toFinset := by rfl
    rw [h_eq]
    have h2 : (dyadicCubesMeeting δ P).encard = ↑(h_fin.toFinset.card) := by exact Finite.encard_eq_coe_toFinset_card h_fin
    simp [h2]
  have h2 : Nplane δ P = ENat.toENNReal (dyadicCubesMeeting δ P).encard := by rfl
  rw [energyRepFinset_card, h1, h2]

lemma energyRepFinset_rep {δ P hδ hP_bdd} :
    ∀ Q ∈ dyadicCubesMeeting δ P,
      ∃! (p : EuclideanSpace ℝ (Fin 2)),
        p ∈ energyRepFinset δ P hδ hP_bdd ∧ p ∈ Q ∩ P := by
  intro Q hQ
  let p_Q := energyCubeRep δ P Q
  have hQ_fin : Q ∈ energyCubesFinset δ P hδ hP_bdd :=
    energyCubesFinset_mem.mpr hQ
  have hpQ_S : p_Q ∈ energyRepFinset δ P hδ hP_bdd := by
    apply Finset.mem_image.mpr
    exact ⟨Q, hQ_fin, rfl⟩
  have hpQ_P : p_Q ∈ Q ∩ P := energyCubeRep_mem hQ
  refine' ⟨p_Q, ⟨hpQ_S, hpQ_P⟩, _⟩
  intro p hp
  have hpS : p ∈ energyRepFinset δ P hδ hP_bdd := hp.1
  have hpQP : p ∈ Q ∩ P := hp.2
  rcases Finset.mem_image.mp hpS with ⟨Q', hQ'_fin, rfl⟩
  have hQ'_in : Q' ∈ dyadicCubesMeeting δ P := energyCubesFinset_mem.mp hQ'_fin
  have h4 : energyCubeRep δ P Q' ∈ Q' := (energyCubeRep_mem hQ'_in).1
  have h5 : energyCubeRep δ P Q' ∈ Q := hpQP.1
  have h6 : energyCubeRep δ P Q' ∈ Q' ∩ Q := ⟨h4, h5⟩
  rcases hQ'_in with ⟨⟨k', hQ'_eq⟩, _⟩
  rcases hQ with ⟨⟨k, hQ_eq⟩, _⟩
  have hQ'_eq_Q : Q' = Q := by
    by_cases hk : k' = k
    · rw [hk] at hQ'_eq
      rw [hQ'_eq, hQ_eq]
    · have h_disj : Disjoint (dyadicCube δ k') (dyadicCube δ k) :=
        dyadic_cubes_disjoint hδ hk
      have h_empty : (dyadicCube δ k') ∩ (dyadicCube δ k) = ∅ :=
        Set.disjoint_iff_inter_eq_empty.mp h_disj
      have h7 : ((dyadicCube δ k') ∩ (dyadicCube δ k)).Nonempty := by
        refine' ⟨energyCubeRep δ P Q', _⟩
        have h8 : energyCubeRep δ P Q' ∈ Q' := h4
        have h9 : energyCubeRep δ P Q' ∈ Q := h5
        have h10 : energyCubeRep δ P Q' ∈ dyadicCube δ k' := by
          rw [←hQ'_eq]; exact h8
        have h11 : energyCubeRep δ P Q' ∈ dyadicCube δ k := by
          rw [←hQ_eq]; exact h9
        exact ⟨h10, h11⟩
      rw [h_empty] at h7
      simpa using h7
  rw [hQ'_eq_Q]

lemma energyRepFinset_subset_P {δ P hδ hP_bdd} :
    ∀ p ∈ energyRepFinset δ P hδ hP_bdd, p ∈ P := by
  intro p hp
  rcases Finset.mem_image.mp hp with ⟨Q, hQ, rfl⟩
  have hQ' : Q ∈ dyadicCubesMeeting δ P := energyCubesFinset_mem.mp hQ
  exact (energyCubeRep_mem hQ').2

/-- Construct a representative set S with one point per δ-cube meeting P. -/
lemma representative_set_construction
    {δ : ℝ} (hδ : 0 < δ)
    {P : Set (EuclideanSpace ℝ (Fin 2))}
    (hP_bdd : Bornology.IsBounded P)
    (hP_nonempty : P.Nonempty) :
    ∃ (S : Finset (EuclideanSpace ℝ (Fin 2))),
      (∀ Q ∈ dyadicCubesMeeting δ P,
        ∃! (p : EuclideanSpace ℝ (Fin 2)), p ∈ S ∧ p ∈ Q ∩ P) ∧
      (S.card : ENNReal) = Nplane δ P ∧
      (∀ p ∈ S, p ∈ P) := by
  let S := energyRepFinset δ P hδ hP_bdd
  refine' ⟨S, _ , _ , _⟩
  · exact energyRepFinset_rep
  · exact energyRepFinset_card_ENNReal
  · exact energyRepFinset_subset_P

/-! ### Geometric series helper -/

lemma geom_sum_formula {x : ℝ} (hx : x ≠ 1) (n : ℕ) :
    ∑ j ∈ Finset.range n, x ^ j = (1 - x ^ n) / (1 - x) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    field_simp [hx] <;> ring

lemma geom_sum_bound {x : ℝ} (hx_pos : 0 < x) (hx_lt_one : x < 1) (n : ℕ) :
    ∑ j ∈ Finset.range n, x ^ j ≤ 1 / (1 - x) := by
  have h1 : ∑ j ∈ Finset.range n, x ^ j = (1 - x ^ n) / (1 - x) :=
    geom_sum_formula (by linarith) n
  rw [h1]
  have h2 : 0 ≤ x ^ n := by positivity
  have h3 : 0 < 1 - x := by linarith
  gcongr <;> linarith

/-! ### Energy bound via annulus decomposition -/

lemma energy_max_from_ball_counting
    {δ s κ Cball : ℝ}
    {S : Finset (EuclideanSpace ℝ (Fin 2))}
    (hδ : 0 < δ) (hδ_lt_one : δ < 1)
    (hδ_dyadic : δ ∈ dyadicScales)
    (hs : 0 < s) (hκ_pos : 0 < κ) (hκ_lt_s : κ < s)
    (hCball_pos : 0 < Cball)
    (hS_nonempty : S.Nonempty)
    (h_ball : ∀ (p : EuclideanSpace ℝ (Fin 2)) (r : ℝ),
        δ ≤ r → r ≤ 1 → r ∈ dyadicScales →
        (S.filter (fun q => dist p q < r)).card ≤ Cball * (S.card : ℝ) * r ^ (2 * s)) :
    ∑ p ∈ S, ∑ q ∈ S, (max (dist p q) δ) ^ (-2 * κ) ≤
      (1 + Cball * (1 - (2 : ℝ) ^ (2 * (κ - s)) + (2 : ℝ) ^ (2 * κ)) /
        (1 - (2 : ℝ) ^ (2 * (κ - s)))) * (S.card : ℝ)^2 := by
  set x : ℝ := (2 : ℝ) ^ (2 * (κ - s)) with hx_def
  have hx_pos : 0 < x := by positivity
  have hx_lt_one : x < 1 := by
    have h1 : 2 * (κ - s) < 0 := by linarith
    have h2 : (2 : ℝ) ^ (2 * (κ - s)) < (2 : ℝ) ^ (0 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h1
    simpa using h2
  have h_denom_pos : 0 < 1 - x := by linarith
  have hδ_dyadic_copy := hδ_dyadic
  rcases hδ_dyadic with ⟨n, hn⟩
  have hn_pos : 0 < n := by
    by_contra h
    have h0 : n = 0 := by omega
    rw [h0] at hn
    norm_num at hn <;> linarith
  have hδ_eq : δ = (2 : ℝ) ^ (-(n : ℝ)) := by
    rw [hn] <;> norm_cast
  have h_card_pos : 0 < (S.card : ℝ) := by exact_mod_cast hS_nonempty.card_pos

  have h_x_pow : ∀ (j : ℕ), x ^ j = (2 : ℝ) ^ (2 * (κ - s) * (j : ℝ)) := by
    intro j
    induction j with
    | zero => norm_num
    | succ j ih =>
      calc x ^ (j + 1)
        = x ^ j * x := by ring
      _ = (2 : ℝ) ^ (2 * (κ - s) * (j : ℝ)) * x := by rw [ih]
      _ = (2 : ℝ) ^ (2 * (κ - s) * (j : ℝ)) * (2 : ℝ) ^ (2 * (κ - s)) := by
        rw [show x = (2 : ℝ) ^ (2 * (κ - s)) from hx_def]
      _ = (2 : ℝ) ^ (2 * (κ - s) * ((j + 1 : ℕ) : ℝ)) := by
        rw [← Real.rpow_add (by norm_num)]
        <;> simp [Nat.cast_add] <;> ring_nf

  have h_main : ∀ p ∈ S,
      ∑ q ∈ S, (max (dist p q) δ) ^ (-2 * κ) ≤
        (1 + Cball * (1 - x + (2 : ℝ) ^ (2 * κ)) / (1 - x)) * (S.card : ℝ) := by
    intro p hp
    let S_close : Finset _ := S.filter (fun q => dist p q < δ)
    let S_far : Finset _ := S.filter (fun q => dist p q ≥ 1)
    let S_ann : ℕ → Finset _ := fun j =>
      S.filter (fun q => (2 : ℝ) ^ (-((j : ℝ) + 1)) ≤ dist p q ∧
        dist p q < (2 : ℝ) ^ (-(j : ℝ)))

    have h_sub_close : S_close ⊆ S := by simp [S_close]
    have h_sub_far : S_far ⊆ S := by simp [S_far]

    -- Close pairs bound
    have h_close_count : (S_close.card : ℝ) ≤ Cball * (S.card : ℝ) * δ ^ (2 * s) :=
      h_ball p δ (by linarith) (by linarith) hδ_dyadic_copy
    have h_close_kernel : ∀ q ∈ S_close, (max (dist p q) δ) ^ (-2 * κ) = δ ^ (-2 * κ) := by
      intro q hq
      have h : dist p q < δ := (Finset.mem_filter.mp hq).2
      have h2 : max (dist p q) δ = δ := by
        rw [max_eq_right] <;> linarith
      rw [h2]
    have h_close_sum : ∑ q ∈ S_close, (max (dist p q) δ) ^ (-2 * κ) =
        (S_close.card : ℝ) * δ ^ (-2 * κ) := by
      have h_eq : ∑ q ∈ S_close, (max (dist p q) δ) ^ (-2 * κ) =
          ∑ q ∈ S_close, δ ^ (-2 * κ) := by
        apply Finset.sum_congr rfl
        intro q hq
        exact h_close_kernel q hq
      rw [h_eq]
      simp [Finset.sum_const] <;> ring
    have h_close_contrib : ∑ q ∈ S_close, (max (dist p q) δ) ^ (-2 * κ) ≤
        Cball * (S.card : ℝ) := by
      rw [h_close_sum]
      have h1 : (S_close.card : ℝ) * δ ^ (-2 * κ) ≤
          (Cball * (S.card : ℝ) * δ ^ (2 * s)) * δ ^ (-2 * κ) := by gcongr
      have h2 : (Cball * (S.card : ℝ) * δ ^ (2 * s)) * δ ^ (-2 * κ) =
          Cball * (S.card : ℝ) * δ ^ (2 * s - 2 * κ) := by
        have h_exp : δ ^ (2 * s) * δ ^ (-2 * κ) = δ ^ (2 * s - 2 * κ) := by
          rw [← Real.rpow_add hδ] <;> ring_nf
        have h_assoc : (Cball * (S.card : ℝ) * δ ^ (2 * s)) * δ ^ (-2 * κ) =
            Cball * (S.card : ℝ) * (δ ^ (2 * s) * δ ^ (-2 * κ)) := by ring
        rw [h_assoc, h_exp] <;> ring
      rw [h2] at h1
      have h3 : δ ^ (2 * s - 2 * κ) ≤ 1 := by
        have h4 : 0 < 2 * s - 2 * κ := by linarith
        apply Real.rpow_le_one (by linarith) (by linarith) (by linarith)
      have h5 : Cball * (S.card : ℝ) * δ ^ (2 * s - 2 * κ) ≤ Cball * (S.card : ℝ) := by
        have h6 : δ ^ (2 * s - 2 * κ) ≤ 1 := h3
        have h7 : 0 ≤ Cball * (S.card : ℝ) := by positivity
        nlinarith
      exact le_trans h1 h5

    -- Far pairs bound
    have h_far_kernel : ∀ q ∈ S_far, (max (dist p q) δ) ^ (-2 * κ) ≤ 1 := by
      intro q hq
      have h1 : 1 ≤ dist p q := (Finset.mem_filter.mp hq).2
      have h2 : 1 ≤ max (dist p q) δ := by
        have h3 : max (dist p q) δ ≥ dist p q := le_max_left _ _
        linarith
      have h4 : 0 < max (dist p q) δ := by positivity
      have h5 : (max (dist p q) δ) ^ (2 * κ) ≥ 1 := by
        have h6 : (max (dist p q) δ) ^ (2 * κ) ≥ (1 : ℝ) ^ (2 * κ) :=
          Real.rpow_le_rpow (by norm_num) h2 (by linarith)
        simpa using h6
      have h_exp : (-2 * κ : ℝ) = -(2 * κ) := by ring
      have h7 : (max (dist p q) δ) ^ (-2 * κ) = 1 / (max (dist p q) δ) ^ (2 * κ) := by
        rw [h_exp, Real.rpow_neg (by linarith)] <;> ring
      rw [h7]
      have h8 : 1 / (max (dist p q) δ) ^ (2 * κ) ≤ 1 := by
        apply (div_le_one (by positivity)).mpr
        exact h5
      exact h8
    have h_far_contrib : ∑ q ∈ S_far, (max (dist p q) δ) ^ (-2 * κ) ≤ (S.card : ℝ) := by
      calc ∑ q ∈ S_far, (max (dist p q) δ) ^ (-2 * κ)
        ≤ ∑ q ∈ S_far, (1 : ℝ) := Finset.sum_le_sum h_far_kernel
      _ = (S_far.card : ℝ) := by simp
      _ ≤ (S.card : ℝ) := by
        exact_mod_cast Finset.card_le_card h_sub_far

    -- Annuli contribution bounds
    have h_ann_contrib : ∀ j ∈ Finset.range n,
        ∑ q ∈ S_ann j, (max (dist p q) δ) ^ (-2 * κ) ≤
          Cball * (S.card : ℝ) * (2 : ℝ) ^ (2 * κ) * x ^ j := by
      intro j hj
      have h_j_lt_n : j < n := Finset.mem_range.mp hj
      let r_j : ℝ := (2 : ℝ) ^ (-(j : ℝ))
      have hr_j_dyadic : r_j ∈ dyadicScales := by
        refine' ⟨j, _⟩
        simp [r_j] <;> ring_nf
      have hr_j_ge_delta : δ ≤ r_j := by
        rw [hδ_eq]
        have h_j_le_n : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show j ≤ n from by omega)
        have h : -(n : ℝ) ≤ -(j : ℝ) := by linarith
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) h
      have hr_j_le_one : r_j ≤ 1 := by
        have h : (j : ℝ) ≥ 0 := by positivity
        have h' : r_j ≤ (2 : ℝ) ^ (0 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        simpa using h'
      have h_sub : S_ann j ⊆ S.filter (fun q => dist p q < r_j) := by
        intro q hq
        have hqS : q ∈ S := (Finset.mem_filter.mp hq).1
        have h_lt : dist p q < r_j := (Finset.mem_filter.mp hq).2.2
        exact Finset.mem_filter.mpr ⟨hqS, h_lt⟩
      have h_count : (S_ann j).card ≤ (S.filter (fun q => dist p q < r_j)).card :=
        Finset.card_le_card h_sub
      have h_ball' : (S.filter (fun q => dist p q < r_j)).card ≤
          Cball * (S.card : ℝ) * r_j ^ (2 * s) :=
        h_ball p r_j hr_j_ge_delta hr_j_le_one hr_j_dyadic
      have h_count' : ((S_ann j).card : ℝ) ≤ Cball * (S.card : ℝ) * r_j ^ (2 * s) := by
        have h_cast : ((S_ann j).card : ℝ) ≤ ((S.filter (fun q => dist p q < r_j)).card : ℝ) := by
          exact_mod_cast h_count
        exact le_trans h_cast h_ball'
      have h_kernel : ∀ q ∈ S_ann j, (max (dist p q) δ) ^ (-2 * κ) ≤
          (2 : ℝ) ^ (2 * κ) * (2 : ℝ) ^ (2 * (j : ℝ) * κ) := by
        intro q hq
        have h_ge : (2 : ℝ) ^ (-((j : ℝ) + 1)) ≤ dist p q :=
          (Finset.mem_filter.mp hq).2.1
        have h_pos_dist : 0 < dist p q := by
          have hδ_le : δ ≤ (2 : ℝ) ^ (-((j : ℝ) + 1)) := by
            rw [hδ_eq]
            have h3 : (n : ℝ) ≥ (j : ℝ) + 1 := by
              have h4 : j < n := h_j_lt_n
              exact_mod_cast (by omega)
            have h5 : -(n : ℝ) ≤ -((j : ℝ) + 1) := by linarith
            exact Real.rpow_le_rpow_of_exponent_le (by norm_num) h5
          have h6 : δ ≤ dist p q := by linarith
          linarith
        have h_max : max (dist p q) δ = dist p q := by
          rw [max_eq_left]
          have hδ_le : δ ≤ (2 : ℝ) ^ (-((j : ℝ) + 1)) := by
            rw [hδ_eq]
            have h3 : (n : ℝ) ≥ (j : ℝ) + 1 := by
              have h4 : j < n := h_j_lt_n
              exact_mod_cast (by omega)
            have h5 : -(n : ℝ) ≤ -((j : ℝ) + 1) := by linarith
            exact Real.rpow_le_rpow_of_exponent_le (by norm_num) h5
          linarith
        rw [h_max]
        have h_base_pos : 0 < (2 : ℝ) ^ (-((j : ℝ) + 1)) := by positivity
        have h6 : (dist p q) ^ (2 * κ) ≥ ((2 : ℝ) ^ (-((j : ℝ) + 1))) ^ (2 * κ) :=
          Real.rpow_le_rpow (by positivity) h_ge (by linarith)
        have h_exp : (-2 * κ : ℝ) = -(2 * κ) := by ring
        have h7 : (dist p q) ^ (-2 * κ) = 1 / (dist p q) ^ (2 * κ) := by
          rw [h_exp]
          rw [Real.rpow_neg (show 0 ≤ dist p q from by linarith)] <;> ring
        have h8 : ((2 : ℝ) ^ (-((j : ℝ) + 1))) ^ (-2 * κ) =
            1 / (((2 : ℝ) ^ (-((j : ℝ) + 1))) ^ (2 * κ)) := by
          rw [h_exp]
          rw [Real.rpow_neg (by positivity)] <;> ring
        have h9 : 1 / (dist p q) ^ (2 * κ) ≤
            1 / (((2 : ℝ) ^ (-((j : ℝ) + 1))) ^ (2 * κ)) := by
          gcongr
        have h10 : ((2 : ℝ) ^ (-((j : ℝ) + 1))) ^ (-2 * κ) =
            (2 : ℝ) ^ (2 * κ) * (2 : ℝ) ^ (2 * (j : ℝ) * κ) := by
          have h_pos1 : (0 : ℝ) ≤ (2 : ℝ) := by norm_num
          have h11 : ((2 : ℝ) ^ (-((j : ℝ) + 1))) ^ (-2 * κ) =
              (2 : ℝ) ^ ((-((j : ℝ) + 1)) * (-2 * κ)) := by
            exact (Real.rpow_mul h_pos1 (-((j : ℝ) + 1)) (-2 * κ)).symm
          rw [h11]
          have h12 : (-((j : ℝ) + 1)) * (-2 * κ) = 2 * κ * ((j : ℝ) + 1) := by ring
          rw [h12]
          have h13 : 2 * κ * ((j : ℝ) + 1) = 2 * κ + 2 * κ * (j : ℝ) := by ring
          rw [h13]
          rw [Real.rpow_add (by norm_num)]
          <;> ring_nf
        have h_ineq : (dist p q) ^ (-2 * κ) ≤ ((2 : ℝ) ^ (-((j : ℝ) + 1))) ^ (-2 * κ) := by
          rw [h7, h8]
          exact h9
        calc (dist p q) ^ (-2 * κ)
          ≤ ((2 : ℝ) ^ (-((j : ℝ) + 1))) ^ (-2 * κ) := h_ineq
        _ = (2 : ℝ) ^ (2 * κ) * (2 : ℝ) ^ (2 * (j : ℝ) * κ) := h10
      calc ∑ q ∈ S_ann j, (max (dist p q) δ) ^ (-2 * κ)
        ≤ ∑ q ∈ S_ann j, ((2 : ℝ) ^ (2 * κ) * (2 : ℝ) ^ (2 * (j : ℝ) * κ)) :=
          Finset.sum_le_sum h_kernel
      _ = ((S_ann j).card : ℝ) * ((2 : ℝ) ^ (2 * κ) * (2 : ℝ) ^ (2 * (j : ℝ) * κ)) := by
        simp [Finset.sum_const] <;> ring
      _ ≤ (Cball * (S.card : ℝ) * r_j ^ (2 * s)) *
            ((2 : ℝ) ^ (2 * κ) * (2 : ℝ) ^ (2 * (j : ℝ) * κ)) := by gcongr
      _ = Cball * (S.card : ℝ) * (2 : ℝ) ^ (2 * κ) * x ^ j := by
        have h_exp1 : r_j ^ (2 * s) = (2 : ℝ) ^ (-2 * s * (j : ℝ)) := by
          dsimp only [r_j]
          rw [← Real.rpow_mul (by norm_num)] <;> ring_nf
        have h_exp2 : x ^ j = (2 : ℝ) ^ (2 * (κ - s) * (j : ℝ)) := h_x_pow j
        have h14 : (2 : ℝ) ^ (-2 * s * (j : ℝ)) * (2 : ℝ) ^ (2 * (j : ℝ) * κ) =
            (2 : ℝ) ^ (2 * (κ - s) * (j : ℝ)) := by
          rw [← Real.rpow_add (by norm_num)] <;> ring_nf
        calc (Cball * (S.card : ℝ) * r_j ^ (2 * s)) *
              ((2 : ℝ) ^ (2 * κ) * (2 : ℝ) ^ (2 * (j : ℝ) * κ))
          = Cball * (S.card : ℝ) * (2 : ℝ) ^ (2 * κ) *
              (r_j ^ (2 * s) * (2 : ℝ) ^ (2 * (j : ℝ) * κ)) := by ring
        _ = Cball * (S.card : ℝ) * (2 : ℝ) ^ (2 * κ) *
              ((2 : ℝ) ^ (-2 * s * (j : ℝ)) * (2 : ℝ) ^ (2 * (j : ℝ) * κ)) := by rw [h_exp1]
        _ = Cball * (S.card : ℝ) * (2 : ℝ) ^ (2 * κ) * x ^ j := by
          rw [h14, h_exp2] <;> ring

    -- Annuli are pairwise disjoint
    have h_disj_ann : ∀ j ∈ Finset.range n, ∀ k ∈ Finset.range n,
        j ≠ k → Disjoint (S_ann j) (S_ann k) := by
      intro j hj k hk hjk
      by_cases h_jk : j < k
      · simp only [S_ann, Finset.disjoint_left]
        intro q hq1 hq2
        have h1 : (2 : ℝ) ^ (-((j : ℝ) + 1)) ≤ dist p q :=
          (Finset.mem_filter.mp hq1).2.1
        have h2 : dist p q < (2 : ℝ) ^ (-(k : ℝ)) :=
          (Finset.mem_filter.mp hq2).2.2
        have h3 : (j + 1 : ℕ) ≤ k := by omega
        have h4 : (j : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast h3
        have h5 : -(k : ℝ) ≤ -((j : ℝ) + 1) := by linarith
        have h6 : (2 : ℝ) ^ (-(k : ℝ)) ≤ (2 : ℝ) ^ (-((j : ℝ) + 1)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) h5
        linarith
      · have h_kj : k < j := by omega
        have h : Disjoint (S_ann k) (S_ann j) := by
          simp only [S_ann, Finset.disjoint_left]
          intro q hq1 hq2
          have h1 : (2 : ℝ) ^ (-((k : ℝ) + 1)) ≤ dist p q :=
            (Finset.mem_filter.mp hq1).2.1
          have h2 : dist p q < (2 : ℝ) ^ (-(j : ℝ)) :=
            (Finset.mem_filter.mp hq2).2.2
          have h3 : (k + 1 : ℕ) ≤ j := by omega
          have h4 : (k : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast h3
          have h5 : -(j : ℝ) ≤ -((k : ℝ) + 1) := by linarith
          have h6 : (2 : ℝ) ^ (-(j : ℝ)) ≤ (2 : ℝ) ^ (-((k : ℝ) + 1)) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) h5
          linarith
        exact Disjoint.symm h

    let S_near := Finset.biUnion (Finset.range n) S_ann

    have h_sub_near : S_near ⊆ S := by
      intro q hq
      rcases Finset.mem_biUnion.mp hq with ⟨j, _, hq2⟩
      exact (Finset.mem_filter.mp hq2).1

    -- Sum over near equals sum over annuli (by disjointness)
    have h_near_sum : ∑ q ∈ S_near, (max (dist p q) δ) ^ (-2 * κ) =
        ∑ j ∈ Finset.range n, ∑ q ∈ S_ann j, (max (dist p q) δ) ^ (-2 * κ) := by
      rw [Finset.sum_biUnion h_disj_ann]

    -- Total annulus sum bound
    have h_ann_total : ∑ j ∈ Finset.range n, ∑ q ∈ S_ann j, (max (dist p q) δ) ^ (-2 * κ) ≤
        Cball * (S.card : ℝ) * (2 : ℝ) ^ (2 * κ) / (1 - x) := by
      calc ∑ j ∈ Finset.range n, ∑ q ∈ S_ann j, (max (dist p q) δ) ^ (-2 * κ)
        ≤ ∑ j ∈ Finset.range n, (Cball * (S.card : ℝ) * (2 : ℝ) ^ (2 * κ) * x ^ j) :=
          Finset.sum_le_sum (fun j hj => h_ann_contrib j hj)
      _ = Cball * (S.card : ℝ) * (2 : ℝ) ^ (2 * κ) * ∑ j ∈ Finset.range n, x ^ j := by
          rw [Finset.mul_sum] <;> ring
      _ ≤ Cball * (S.card : ℝ) * (2 : ℝ) ^ (2 * κ) * (1 / (1 - x)) := by
          gcongr
          exact geom_sum_bound hx_pos hx_lt_one n
      _ = Cball * (S.card : ℝ) * (2 : ℝ) ^ (2 * κ) / (1 - x) := by ring

    -- Covering: every q with δ ≤ dist < 1 is in some annulus
    have h_cover : ∀ q ∈ S, δ ≤ dist p q → dist p q < 1 → q ∈ S_near := by
      intro q hq hge hlt
      have hpos : 0 < dist p q := by linarith
      let L : ℝ := Real.logb 2 (1 / dist p q)
      have h1 : 1 / dist p q > 1 := by apply one_lt_one_div <;> linarith
      have h2 : Real.logb 2 (1 / dist p q) > Real.logb 2 1 :=
        Real.logb_lt_logb (by norm_num) (by norm_num) h1
      have h3 : Real.logb 2 1 = 0 := by simp
      have hL_pos : 0 < L := by
        dsimp only [L]
        linarith
      have hL_le_n : L ≤ (n : ℝ) := by
        have h10 : 1 / dist p q ≤ 1 / δ := by gcongr <;> linarith
        have h11 : Real.logb 2 (1 / dist p q) ≤ Real.logb 2 (1 / δ) :=
          (Real.logb_le_logb (by norm_num) (by positivity) (by positivity)).mpr h10
        have h12 : Real.logb 2 (1 / δ) = (n : ℝ) := by
          rw [hδ_eq]
          have h13 : (2 : ℝ) ^ (-(n : ℝ)) > 0 := by positivity
          have h14 : 1 / ((2 : ℝ) ^ (-(n : ℝ))) = (2 : ℝ) ^ (n : ℝ) := by
            field_simp [h13.ne']
            <;> rw [← Real.rpow_add (by norm_num)] <;> ring_nf <;> norm_num
          rw [h14]
          have h15 : Real.logb 2 ((2 : ℝ) ^ (n : ℝ)) = (n : ℝ) := by
            simp [Real.logb_pow] <;> ring
          exact h15
        linarith
      let j_q : ℕ := Nat.ceil L - 1
      have h_ceil_pos : 0 < Nat.ceil L := Nat.ceil_pos.mpr hL_pos
      have h1_le_ceil : 1 ≤ Nat.ceil L := by exact_mod_cast h_ceil_pos
      have h_jq_cast : (j_q : ℝ) = (Nat.ceil L : ℝ) - 1 := by
        rw [Nat.cast_sub h1_le_ceil] <;> norm_num
      have h_j_lt_L : (j_q : ℝ) < L := by
        rw [h_jq_cast]
        have h : (Nat.ceil L : ℝ) < L + 1 := Nat.ceil_lt_add_one (by linarith)
        linarith
      have h_L_le_j1 : L ≤ (j_q : ℝ) + 1 := by
        rw [h_jq_cast]
        have h : L ≤ (Nat.ceil L : ℝ) := Nat.le_ceil L
        linarith
      have h_ann1 : (2 : ℝ) ^ (-((j_q : ℝ) + 1)) ≤ dist p q := by
        have h4 : L ≤ (j_q : ℝ) + 1 := h_L_le_j1
        have h5 : (2 : ℝ) ^ L ≤ (2 : ℝ) ^ ((j_q : ℝ) + 1) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) h4
        have h6 : (2 : ℝ) ^ L = 1 / dist p q :=
          Real.rpow_logb (by norm_num) (by norm_num) (by positivity)
        rw [h6] at h5
        have h_pos2 : 0 < (2 : ℝ) ^ ((j_q : ℝ) + 1) := by positivity
        have h7 : 1 / dist p q ≤ (2 : ℝ) ^ ((j_q : ℝ) + 1) := h5
        have h8 : (2 : ℝ) ^ (-((j_q : ℝ) + 1)) ≤ dist p q := by
          have h9 : (2 : ℝ) ^ (-((j_q : ℝ) + 1)) = 1 / (2 : ℝ) ^ ((j_q : ℝ) + 1) := by
            have h_exp : (-((j_q : ℝ) + 1) : ℝ) = -((j_q : ℝ) + 1) := by ring
            rw [h_exp, Real.rpow_neg (by positivity)] <;> ring
          rw [h9]
          have h10 : 0 < dist p q := hpos
          calc 1 / (2 : ℝ) ^ ((j_q : ℝ) + 1)
            ≤ 1 / (1 / dist p q) := by gcongr
          _ = dist p q := by
            field_simp [h10.ne'] <;> ring
        exact h8
      have h_ann2 : dist p q < (2 : ℝ) ^ (-(j_q : ℝ)) := by
        have h4 : (j_q : ℝ) < L := h_j_lt_L
        have h5 : (2 : ℝ) ^ (-(j_q : ℝ)) > (2 : ℝ) ^ (-L) := by
          have h6 : -(j_q : ℝ) > -L := by linarith
          exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h6
        have h6 : (2 : ℝ) ^ (-L) = dist p q := by
          have h7 : (2 : ℝ) ^ L = 1 / dist p q :=
            Real.rpow_logb (by norm_num) (by norm_num) (by positivity)
          have h8 : (2 : ℝ) ^ (-L) = 1 / ((2 : ℝ) ^ L) := by
            have h_exp : (-L : ℝ) = -L := by ring
            rw [h_exp, Real.rpow_neg (by norm_num)] <;> ring
          rw [h8, h7]
          field_simp [hpos.ne'] <;> ring
        rw [h6] at h5
        exact h5
      have h_j_range : j_q ∈ Finset.range n := by
        have h9 : Nat.ceil L ≤ n := by
          exact Nat.ceil_le.mpr hL_le_n
        have h10 : j_q < n := by omega
        exact Finset.mem_range.mpr h10
      have hq_ann : q ∈ S_ann j_q := Finset.mem_filter.mpr ⟨hq, ⟨h_ann1, h_ann2⟩⟩
      exact Finset.mem_biUnion.mpr ⟨j_q, h_j_range, hq_ann⟩

    -- Disjointness of close, near, far
    have h_disj1 : Disjoint S_close S_near := by
      simp only [S_close, S_near, S_ann, Finset.disjoint_left, Finset.mem_biUnion]
      intro q hq1 ⟨j, _, hq2⟩
      have h1 : dist p q < δ := (Finset.mem_filter.mp hq1).2
      have h2 : (2 : ℝ) ^ (-((j : ℝ) + 1)) ≤ dist p q :=
        (Finset.mem_filter.mp hq2).2.1
      have h3 : δ ≤ (2 : ℝ) ^ (-((j : ℝ) + 1)) := by
        rw [hδ_eq]
        have h4 : j < n := Finset.mem_range.mp ‹_›
        have h5 : (n : ℝ) ≥ (j : ℝ) + 1 := by exact_mod_cast (by omega)
        have h6 : -(n : ℝ) ≤ -((j : ℝ) + 1) := by linarith
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) h6
      linarith

    have h_disj2 : Disjoint S_far S_near := by
      simp only [S_far, S_near, S_ann, Finset.disjoint_left, Finset.mem_biUnion]
      intro q hq1 ⟨j, _, hq2⟩
      have h1 : 1 ≤ dist p q := (Finset.mem_filter.mp hq1).2
      have h2 : dist p q < (2 : ℝ) ^ (-(j : ℝ)) :=
        (Finset.mem_filter.mp hq2).2.2
      have h3 : (2 : ℝ) ^ (-(j : ℝ)) ≤ 1 := by
        have h4 : (j : ℝ) ≥ 0 := by positivity
        have h5 : (2 : ℝ) ^ (-(j : ℝ)) ≤ (2 : ℝ) ^ (0 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        simpa using h5
      linarith

    have h_disj3 : Disjoint S_close S_far := by
      simp only [S_close, S_far, Finset.disjoint_left]
      intro q hq1 hq2
      have h1 : dist p q < δ := (Finset.mem_filter.mp hq1).2
      have h2 : 1 ≤ dist p q := (Finset.mem_filter.mp hq2).2
      linarith

    -- Partition S = close ∪ near ∪ far
    have h_partition : S_close ∪ S_near ∪ S_far = S := by
      apply Finset.ext
      intro q
      simp only [Finset.mem_union]
      constructor
      · intro h
        rcases h with (h | h)
        · rcases h with (h | h)
          · exact h_sub_close h
          · exact h_sub_near h
        · exact h_sub_far h
      · intro hq
        by_cases h1 : dist p q < δ
        · have h : q ∈ S_close := Finset.mem_filter.mpr ⟨hq, h1⟩
          simpa [Finset.mem_union] using Or.inl (Or.inl h)
        · by_cases h2 : 1 ≤ dist p q
          · have h : q ∈ S_far := Finset.mem_filter.mpr ⟨hq, h2⟩
            simpa [Finset.mem_union] using Or.inr h
          · have h3 : δ ≤ dist p q := by linarith
            have h4 : dist p q < 1 := by linarith
            have h5 : q ∈ S_near := h_cover q hq h3 h4
            simpa [Finset.mem_union] using Or.inl (Or.inr h5)

    have h_sum_all : ∑ q ∈ S, (max (dist p q) δ) ^ (-2 * κ) =
        ∑ q ∈ S_close, (max (dist p q) δ) ^ (-2 * κ) +
        ∑ q ∈ S_near, (max (dist p q) δ) ^ (-2 * κ) +
        ∑ q ∈ S_far, (max (dist p q) δ) ^ (-2 * κ) := by
      have h1 : S = (S_close ∪ S_near) ∪ S_far := h_partition.symm
      rw [h1]
      have h_disj2' : Disjoint S_near S_far := Disjoint.symm h_disj2
      have h_disj4 : Disjoint (S_close ∪ S_near) S_far := by
        rw [Finset.disjoint_left]
        intro q hq1 hq2
        rcases Finset.mem_union.mp hq1 with (h | h)
        · have h_contra : ∀ (x : EuclideanSpace ℝ (Fin 2)), x ∈ S_close → x ∈ S_far → False := by
            simpa [Finset.disjoint_left] using h_disj3
          exact h_contra q h hq2
        · have h_contra : ∀ (x : EuclideanSpace ℝ (Fin 2)), x ∈ S_near → x ∈ S_far → False := by
            simpa [Finset.disjoint_left] using h_disj2'
          exact h_contra q h hq2
      rw [Finset.sum_union h_disj4, Finset.sum_union h_disj1] <;> ring

    rw [h_sum_all]

    have h_far_card_sum : ∑ q ∈ S_far, (max (dist p q) δ) ^ (-2 * κ) ≤ (S_far.card : ℝ) := by
      calc ∑ q ∈ S_far, (max (dist p q) δ) ^ (-2 * κ)
        ≤ ∑ q ∈ S_far, (1 : ℝ) := Finset.sum_le_sum h_far_kernel
      _ = (S_far.card : ℝ) := by simp

    have h4 : ∑ q ∈ S_close, (max (dist p q) δ) ^ (-2 * κ) +
        ∑ q ∈ S_near, (max (dist p q) δ) ^ (-2 * κ) +
        ∑ q ∈ S_far, (max (dist p q) δ) ^ (-2 * κ) ≤
        (S_close.card : ℝ) * δ ^ (-2 * κ) +
        Cball * (S.card : ℝ) * (2 : ℝ) ^ (2 * κ) / (1 - x) + (S_far.card : ℝ) := by
      have h_near : ∑ q ∈ S_near, (max (dist p q) δ) ^ (-2 * κ) ≤
          Cball * (S.card : ℝ) * (2 : ℝ) ^ (2 * κ) / (1 - x) := by
        rw [h_near_sum]
        exact h_ann_total
      linarith [h_close_sum, h_far_card_sum, h_near]

    have h1 : (S_close.card : ℝ) * δ ^ (-2 * κ) ≤ Cball * (S.card : ℝ) := by
      rw [← h_close_sum]
      exact h_close_contrib
    have h2 : (S_far.card : ℝ) ≤ (S.card : ℝ) := by
      exact_mod_cast Finset.card_le_card h_sub_far

    have h_bound2 : (S_close.card : ℝ) * δ ^ (-2 * κ) +
        Cball * (S.card : ℝ) * (2 : ℝ) ^ (2 * κ) / (1 - x) + (S_far.card : ℝ) ≤
        Cball * (S.card : ℝ) + Cball * (S.card : ℝ) * (2 : ℝ) ^ (2 * κ) / (1 - x) + (S.card : ℝ) := by
      linarith [h1, h2]
    have h_alg : Cball * (S.card : ℝ) + Cball * (S.card : ℝ) * (2 : ℝ) ^ (2 * κ) / (1 - x) + (S.card : ℝ) =
        (1 + Cball * (1 - x + (2 : ℝ) ^ (2 * κ)) / (1 - x)) * (S.card : ℝ) := by
      have h_pos : 0 < 1 - x := h_denom_pos
      have h : Cball + Cball * (2 : ℝ) ^ (2 * κ) / (1 - x) + (1 : ℝ) =
          1 + Cball * (1 - x + (2 : ℝ) ^ (2 * κ)) / (1 - x) := by
        field_simp [h_pos.ne'] <;> ring
      have h' : Cball * (S.card : ℝ) + Cball * (S.card : ℝ) * (2 : ℝ) ^ (2 * κ) / (1 - x) + (S.card : ℝ) =
          (Cball + Cball * (2 : ℝ) ^ (2 * κ) / (1 - x) + 1) * (S.card : ℝ) := by ring
      rw [h']
      rw [h] <;> ring
    have h5 : (S_close.card : ℝ) * δ ^ (-2 * κ) +
        Cball * (S.card : ℝ) * (2 : ℝ) ^ (2 * κ) / (1 - x) + (S_far.card : ℝ) ≤
        (1 + Cball * (1 - x + (2 : ℝ) ^ (2 * κ)) / (1 - x)) * (S.card : ℝ) := by
      calc _ ≤ Cball * (S.card : ℝ) + Cball * (S.card : ℝ) * (2 : ℝ) ^ (2 * κ) / (1 - x) + (S.card : ℝ) := h_bound2
           _ = (1 + Cball * (1 - x + (2 : ℝ) ^ (2 * κ)) / (1 - x)) * (S.card : ℝ) := h_alg

    exact le_trans h4 h5

  calc ∑ p ∈ S, ∑ q ∈ S, (max (dist p q) δ) ^ (-2 * κ)
    ≤ ∑ p ∈ S, (1 + Cball * (1 - x + (2 : ℝ) ^ (2 * κ)) / (1 - x)) * (S.card : ℝ) :=
      Finset.sum_le_sum (fun p hp => h_main p hp)
  _ = (1 + Cball * (1 - x + (2 : ℝ) ^ (2 * κ)) / (1 - x)) * (S.card : ℝ)^2 := by
    let c : ℝ := (1 + Cball * (1 - x + (2 : ℝ) ^ (2 * κ)) / (1 - x)) * (S.card : ℝ)
    have h_sum : ∑ p ∈ S, c = (S.card : ℝ) * c := by
      rw [Finset.sum_const]
      <;> ring
    rw [h_sum]
    <;> simp [c] <;> ring

end robust_projection
