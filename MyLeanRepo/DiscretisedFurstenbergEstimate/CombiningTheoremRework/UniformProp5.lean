module

/-
  Uniform Elementary Incidence Bound (OS Proposition 2.4 + Corollary 2.5)

  Proves the paper's genuine incidence bound using Cauchy-Schwarz and
  pair intersection estimates, yielding a UNIFORM logarithmic factor.

  Whiteprint node: combining_theorem_rework / uniform_prop5
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.ElementaryIncidence
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AuxLemma
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.IncidenceCauchySchwarz
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal BigOperators Classical

set_option maxHeartbeats 1000000

noncomputable section

namespace DiscretisedFurstenbergEstimate

open Finset

/-! ========================================================================
   Geometric helpers
   ======================================================================== -/

lemma tube_pair_slope_interval {n : ℕ} {p p' : DSquare n} {T : DTube n}
    (h1 : (T.toSet ∩ p.toSet).Nonempty)
    (h2 : (T.toSet ∩ p'.toSet).Nonempty)
    (h_slope : |T.slope| ≤ 1)
    (hk : 2 ≤ Int.natAbs (p.i - p'.i)) :
    |T.slope - ((p.j - p'.j : ℝ) / (p.i - p'.i : ℝ))| ≤ 12 / (Int.natAbs (p.i - p'.i) : ℝ) :=
  single_slope_bound h1 h2 h_slope hk

lemma square_horizontal_dist {n : ℕ} {p p' : DSquare n} :
    (Int.natAbs (p.i - p'.i) : ℝ) * δ n ≤ dist p p' := by
  have hdx : |(p.i : ℝ) - (p'.i : ℝ)| * δ n ≤ dist p p' := by
    have h_def : dist p p' = dist (p.toPoint) (p'.toPoint) := by rfl
    rw [h_def]
    let xi : ℝ × ℝ := p.toPoint
    let yi : ℝ × ℝ := p'.toPoint
    have h6 : |xi.1 - yi.1| ≤ dist xi yi := by
      have h10 : dist xi.1 yi.1 ≤ dist xi yi := by apply le_max_left
      simpa [Real.dist_eq] using h10
    have h7 : xi.1 = (p.i : ℝ) * δ n := by rfl
    have h8 : yi.1 = (p'.i : ℝ) * δ n := by rfl
    rw [h7, h8] at h6
    have h9 : |(p.i : ℝ) * δ n - (p'.i : ℝ) * δ n| = |(p.i : ℝ) - (p'.i : ℝ)| * δ n := by
      rw [show (p.i : ℝ) * δ n - (p'.i : ℝ) * δ n = ((p.i : ℝ) - (p'.i : ℝ)) * δ n by ring]
      rw [abs_mul, abs_of_pos (δ_pos n)] <;> ring
    rw [h9] at h6; exact h6
  have h2 : |(p.i : ℝ) - (p'.i : ℝ)| = (Int.natAbs (p.i - p'.i) : ℝ) := by
    simp [abs_eq_max_neg] <;> norm_cast <;> omega
  rw [h2] at hdx; exact hdx

/-! ========================================================================
   Algebraic core: Cauchy-Schwarz incidence bound
   ======================================================================== -/

/-- Double-counting identity: ∑_{t∈T} a_t(a_t-1) = ∑_{p≠p'} |Tp p ∩ Tp p'|.
    Proof: a_t(a_t-1) = a_t² - a_t. Then ∑ a_t² = ∑_{p,p'} |Tp p ∩ Tp p'| and
    ∑ a_t = ∑_p |Tp p|, so subtracting the diagonal gives the result. -/
lemma double_counting_pair_sum
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    {P : Finset α} {T : Finset β} {Tp : α → Finset β}
    (hTp_sub : ∀ p ∈ P, Tp p ⊆ T) :
    ∑ t ∈ T, ((P.filter (fun p => t ∈ Tp p)).card : ℝ) *
      (((P.filter (fun p => t ∈ Tp p)).card : ℝ) - 1) =
    (∑ p ∈ P, ∑ p' ∈ P.erase p, ((Tp p) ∩ (Tp p')).card : ℝ) := by
  let a : β → ℝ := fun t => ((P.filter (fun p => t ∈ Tp p)).card : ℝ)
  let ind : β → α → ℝ := fun t p => if t ∈ Tp p then 1 else 0

  have ha : ∀ t ∈ T, a t = ∑ p ∈ P, ind t p := by
    intro t _
    simp [a, ind] <;> norm_cast

  have h2 : ∀ t ∈ T, (a t)^2 = ∑ p ∈ P, ∑ p' ∈ P, ind t p * ind t p' := by
    intro t ht
    rw [ha t ht]
    have h : (∑ p ∈ P, ind t p)^2 = (∑ p ∈ P, ind t p) * (∑ p ∈ P, ind t p) := by ring
    rw [h, Finset.sum_mul_sum] <;> rfl

  have h3 : ∀ t p p', ind t p * ind t p' = if t ∈ Tp p ∩ Tp p' then (1 : ℝ) else 0 := by
    intro t p p'
    simp [ind, Finset.mem_inter] <;> split_ifs <;> norm_num <;> tauto

  have h_inner_sum : ∀ (p : α), p ∈ P → ∀ (p' : α), p' ∈ P →
      (∑ t ∈ T, (if t ∈ Tp p ∩ Tp p' then (1 : ℝ) else 0)) = ((Tp p ∩ Tp p').card : ℝ) := by
    intro p hp p' hp'
    have h_sub : Tp p ∩ Tp p' ⊆ T := by
      apply Finset.inter_subset_left.trans
      exact hTp_sub p hp
    have h_eq : T.filter (fun t => t ∈ Tp p ∩ Tp p') = Tp p ∩ Tp p' := by
      ext x
      simp only [Finset.mem_filter]
      <;> constructor
      · rintro ⟨h1, h2⟩; exact h2
      · intro h2; exact ⟨h_sub h2, h2⟩
    have h_sum : ∑ t ∈ T, (if t ∈ Tp p ∩ Tp p' then (1 : ℝ) else 0) =
        ((T.filter (fun t => t ∈ Tp p ∩ Tp p')).card : ℝ) := by
      rw [Finset.sum_ite] <;> simp
    rw [h_sum, h_eq] <;> norm_cast

  have h_sum_a2 : (∑ t ∈ T, (a t)^2) =
      ∑ p ∈ P, ∑ p' ∈ P, ((Tp p ∩ Tp p').card : ℝ) := by
    calc (∑ t ∈ T, (a t)^2)
        = ∑ t ∈ T, ∑ p ∈ P, ∑ p' ∈ P, ind t p * ind t p' := by
          apply Finset.sum_congr rfl; intro t ht; exact h2 t ht
      _ = ∑ p ∈ P, ∑ p' ∈ P, ∑ t ∈ T, ind t p * ind t p' := by
          have h_swap1 : ∑ t ∈ T, ∑ p ∈ P, ∑ p' ∈ P, ind t p * ind t p' =
              ∑ p ∈ P, ∑ t ∈ T, ∑ p' ∈ P, ind t p * ind t p' := by
            rw [Finset.sum_comm]
          rw [h_swap1]
          apply Finset.sum_congr rfl; intro p _
          rw [Finset.sum_comm]
      _ = ∑ p ∈ P, ∑ p' ∈ P, ∑ t ∈ T, (if t ∈ Tp p ∩ Tp p' then (1 : ℝ) else 0) := by
          apply Finset.sum_congr rfl; intro p _
          apply Finset.sum_congr rfl; intro p' _
          apply Finset.sum_congr rfl; intro t _; exact h3 t p p'
      _ = ∑ p ∈ P, ∑ p' ∈ P, ((Tp p ∩ Tp p').card : ℝ) := by
          apply Finset.sum_congr rfl; intro p hp
          apply Finset.sum_congr rfl; intro p' hp'
          exact h_inner_sum p hp p' hp'

  have h_sum_a : (∑ t ∈ T, a t) = ∑ p ∈ P, ((Tp p).card : ℝ) := by
    calc (∑ t ∈ T, a t)
        = ∑ t ∈ T, ∑ p ∈ P, ind t p := by
          apply Finset.sum_congr rfl; intro t ht; exact ha t ht
      _ = ∑ p ∈ P, ∑ t ∈ T, ind t p := by rw [Finset.sum_comm]
      _ = ∑ p ∈ P, ((Tp p).card : ℝ) := by
          apply Finset.sum_congr rfl; intro p _
          rw [Finset.sum_ite]
          simp [hTp_sub p ‹_›] <;> norm_cast

  have h_main : (∑ t ∈ T, a t * (a t - 1)) = (∑ t ∈ T, (a t)^2) - (∑ t ∈ T, a t) := by
    have h : ∀ t ∈ T, a t * (a t - 1) = (a t)^2 - a t := by intro t _; ring
    rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib]

  rw [h_main, h_sum_a2, h_sum_a]

  have h_diag : ∀ p ∈ P, (∑ p' ∈ P, ((Tp p ∩ Tp p').card : ℝ)) - ((Tp p).card : ℝ) =
      ∑ p' ∈ P.erase p, ((Tp p ∩ Tp p').card : ℝ) := by
    intro p hp
    have h4 : (Tp p ∩ Tp p) = Tp p := by rw [Finset.inter_self]
    have h9 : p ∉ P.erase p := by simp
    let f : α → ℝ := fun p' => ((Tp p ∩ Tp p').card : ℝ)
    have h10 : ∑ p' ∈ P, f p' = f p + ∑ p' ∈ P.erase p, f p' := by
      have h11 : P = insert p (P.erase p) := by rw [Finset.insert_erase hp]
      rw [h11]
      simpa using Finset.sum_insert h9
    have h5 : (∑ p' ∈ P, ((Tp p ∩ Tp p').card : ℝ)) =
        ((Tp p).card : ℝ) + ∑ p' ∈ P.erase p, ((Tp p ∩ Tp p').card : ℝ) := by
      have h6 : ∑ p' ∈ P, f p' = f p + ∑ p' ∈ P.erase p, f p' := h10
      have h7 : f p = ((Tp p ∩ Tp p).card : ℝ) := by rfl
      rw [h7] at h6
      rw [h6, h4] <;> ring
    linarith

  have h_final : (∑ p ∈ P, ∑ p' ∈ P, ((Tp p ∩ Tp p').card : ℝ)) - (∑ p ∈ P, ((Tp p).card : ℝ)) =
      ∑ p ∈ P, ∑ p' ∈ P.erase p, ((Tp p ∩ Tp p').card : ℝ) := by
    have h : ∑ p ∈ P, (∑ p' ∈ P, ((Tp p ∩ Tp p').card : ℝ)) =
        ∑ p ∈ P, (((Tp p).card : ℝ) + ∑ p' ∈ P.erase p, ((Tp p ∩ Tp p').card : ℝ)) := by
      apply Finset.sum_congr rfl; intro p hp
      have h5 := h_diag p hp
      linarith
    rw [h, Finset.sum_add_distrib] <;> ring
  exact h_final


/-! ========================================================================
   DSquare ball-growth from S-set property
   ======================================================================== -/

/-- DSquare distinct points are at least δ apart. -/
lemma dsquare_separated {n : ℕ} {P : Finset (DSquare n)} :
    SeparatedAt (δ n) (P : Set (DSquare n)) := by
  intro p _ q _ hne
  have h3 : (p.i ≠ q.i) ∨ (p.j ≠ q.j) := by
    by_contra h
    push Not at h
    have h4 : p = q := by
      cases p; cases q; simp_all
    exact hne h4
  have h4 : (1 : ℝ) ≤ |(p.i : ℝ) - (q.i : ℝ)| ∨ (1 : ℝ) ≤ |(p.j : ℝ) - (q.j : ℝ)| := by
    rcases h3 with (h3 | h3)
    · left
      have h5 : (p.i : ℤ) - (q.i : ℤ) ≠ 0 := sub_ne_zero.mpr h3
      have h6 : 1 ≤ |(p.i : ℤ) - (q.i : ℤ)| := Int.one_le_abs h5
      exact_mod_cast h6
    · right
      have h5 : (p.j : ℤ) - (q.j : ℤ) ≠ 0 := sub_ne_zero.mpr h3
      have h6 : 1 ≤ |(p.j : ℤ) - (q.j : ℤ)| := Int.one_le_abs h5
      exact_mod_cast h6
  have h5 : dist p q = δ n * max |(p.i : ℝ) - (q.i : ℝ)| |(p.j : ℝ) - (q.j : ℝ)| := by
    have hδ : 0 < δ n := δ_pos n
    have h_dist1 : dist p q = dist p.toPoint q.toPoint := by rfl
    rw [h_dist1]
    have h_dist2 : dist p.toPoint q.toPoint =
        max (|(p.i : ℝ) * δ n - (q.i : ℝ) * δ n|) (|(p.j : ℝ) * δ n - (q.j : ℝ) * δ n|) := by
      simp [DSquare.toPoint, Prod.dist_eq] <;> rfl
    rw [h_dist2]
    have h6 : |(p.i : ℝ) * δ n - (q.i : ℝ) * δ n| = |(p.i : ℝ) - (q.i : ℝ)| * δ n := by
      rw [show (p.i : ℝ) * δ n - (q.i : ℝ) * δ n = ((p.i : ℝ) - (q.i : ℝ)) * δ n by ring]
      rw [abs_mul, abs_of_pos hδ] <;> ring
    have h7 : |(p.j : ℝ) * δ n - (q.j : ℝ) * δ n| = |(p.j : ℝ) - (q.j : ℝ)| * δ n := by
      rw [show (p.j : ℝ) * δ n - (q.j : ℝ) * δ n = ((p.j : ℝ) - (q.j : ℝ)) * δ n by ring]
      rw [abs_mul, abs_of_pos hδ] <;> ring
    rw [h6, h7, mul_max_of_nonneg _ _ (by linarith)] <;> ring_nf
  rw [h5]
  rcases h4 with (h4i | h4j)
  · have h6 : 1 ≤ max |(p.i : ℝ) - (q.i : ℝ)| |(p.j : ℝ) - (q.j : ℝ)| :=
      le_trans h4i (le_max_left _ _)
    have h7 : 0 < δ n := δ_pos n
    nlinarith
  · have h6 : 1 ≤ max |(p.i : ℝ) - (q.i : ℝ)| |(p.j : ℝ) - (q.j : ℝ)| :=
      le_trans h4j (le_max_right _ _)
    have h7 : 0 < δ n := δ_pos n
    nlinarith

/-- Ball-growth for DSquare S-set via isometric embedding into ℝ². -/
lemma dsquare_ball_growth
    {n : ℕ} {t C_P : ℝ} {P : Finset (DSquare n)}
    (ht : 0 ≤ t) (hCP_pos : 0 < C_P)
    (hP_sset : IsFinsetDeltaSSet (δ n) t C_P P)
    {p : DSquare n} {r : ℝ} (hr : δ n ≤ r) :
    ((P.filter (fun q => dist p q ≤ r)).card : ℝ) ≤
      (9 : ℝ) * C_P * r^t * (P.card : ℝ) := by
  let B := P.filter (fun q => dist p q ≤ r)
  let P' : Finset (ℝ × ℝ) := P.image DSquare.toPoint
  let B' : Finset (ℝ × ℝ) := B.image DSquare.toPoint

  have h_toPoint_isometry : Isometry (DSquare.toPoint (n := n)) := by
    intro x y
    rfl

  have h_inj : Set.InjOn DSquare.toPoint (P : Set (DSquare n)) := by
    intro x _ y _ h
    exact Isometry.injective h_toPoint_isometry h

  have hB_inj : Set.InjOn DSquare.toPoint (B : Set (DSquare n)) :=
    h_inj.mono (fun x hx => (Finset.mem_filter.mp hx).1)

  have hB_card : B'.card = B.card := by
    rw [Finset.card_image_of_injOn hB_inj]

  have hP'_card : P'.card = P.card := by
    rw [Finset.card_image_of_injOn h_inj]

  have hB'_sep : SeparatedAt (δ n) (B' : Set (ℝ × ℝ)) := by
    intro x hx y hy hne
    rcases Finset.mem_image.mp hx with ⟨x', hx', rfl⟩
    rcases Finset.mem_image.mp hy with ⟨y', hy', rfl⟩
    have hne' : x' ≠ y' := by intro h; rw [h] at hne; exact hne rfl
    have hx'in : x' ∈ (P : Set (DSquare n)) := (Finset.mem_filter.mp hx').1
    have hy'in : y' ∈ (P : Set (DSquare n)) := (Finset.mem_filter.mp hy').1
    exact dsquare_separated (P := P) hx'in hy'in hne'

  let ε : NNReal := (δ n).toNNReal
  have hε : (ε : ℝ) = δ n := by
    have hδ : 0 < δ n := δ_pos n
    simp [ε, hδ] <;> linarith

  -- Transfer: externalCoveringNumber ε (f '' A) ≤ externalCoveringNumber ε A
  have h_cover_transfer : ∀ (A : Finset (DSquare n)),
      Metric.externalCoveringNumber ε ((A.image DSquare.toPoint) : Set (ℝ × ℝ)) ≤
      Metric.externalCoveringNumber ε (A : Set (DSquare n)) := by
    intro A
    have h_main : ∀ (C : Set (DSquare n)) (hC : Metric.IsCover ε (A : Set (DSquare n)) C),
        Metric.externalCoveringNumber ε ((A.image DSquare.toPoint) : Set (ℝ × ℝ)) ≤ C.encard := by
      intro C hC
      let C' := DSquare.toPoint '' C
      have hC' : Metric.IsCover ε ((A.image DSquare.toPoint) : Set (ℝ × ℝ)) C' := by
        have h := Metric.IsCover.image_lipschitz hC (Isometry.lipschitz h_toPoint_isometry)
        simpa [one_mul] using h
      have h_le : Metric.externalCoveringNumber ε ((A.image DSquare.toPoint) : Set (ℝ × ℝ)) ≤ C'.encard :=
        Metric.IsCover.externalCoveringNumber_le_encard hC'
      have h_inj_C : Set.InjOn DSquare.toPoint C := by
        intro x _ y _ h
        exact Isometry.injective h_toPoint_isometry h
      have h_eq : C'.encard = C.encard := h_inj_C.encard_image
      rw [h_eq] at h_le
      exact h_le
    simp only [Metric.externalCoveringNumber]
    rw [le_iInf_iff]
    intro C
    rw [le_iInf_iff]
    exact h_main C

  have h_cover_B' : (Metric.externalCoveringNumber ε (B' : Set (ℝ × ℝ)) : ENNReal) ≤
      (Metric.externalCoveringNumber ε (B : Set (DSquare n)) : ENNReal) := by
    exact_mod_cast h_cover_transfer B

  have h_cover_P' : (Metric.externalCoveringNumber ε (P' : Set (ℝ × ℝ)) : ENNReal) ≤
      (Metric.externalCoveringNumber ε (P : Set (DSquare n)) : ENNReal) := by
    exact_mod_cast h_cover_transfer P

  have hB_in : (B : Set (DSquare n)) ⊆ (P : Set (DSquare n)) ∩ Metric.closedBall p r := by
    intro y hy
    have h1 : y ∈ P := (Finset.mem_filter.mp hy).1
    have h2 : dist p y ≤ r := (Finset.mem_filter.mp hy).2
    have h2' : dist y p ≤ r := by rw [dist_comm]; exact h2
    exact ⟨h1, by simpa [Metric.mem_closedBall] using h2'⟩

  have h_cover_mono : (Metric.externalCoveringNumber ε (B : Set (DSquare n)) : ENNReal) ≤
      (Metric.externalCoveringNumber ε ((P : Set (DSquare n)) ∩ Metric.closedBall p r) : ENNReal) := by
    exact_mod_cast Metric.externalCoveringNumber_mono_set hB_in

  have h_sset : (Metric.externalCoveringNumber ε ((P : Set (DSquare n)) ∩ Metric.closedBall p r) : ENNReal) ≤
      ENNReal.ofReal C_P * (ENNReal.ofReal r) ^ t *
        (Metric.externalCoveringNumber ε (P : Set (DSquare n)) : ENNReal) :=
    hP_sset.2.2.2.2 p r hr

  have h_cover_P_le : (Metric.externalCoveringNumber ε (P : Set (DSquare n)) : ENNReal) ≤ (P.card : ENNReal) := by
    have h : (Metric.externalCoveringNumber ε (P : Set (DSquare n)) : ENNReal) ≤ (P : Set (DSquare n)).encard := by
      exact_mod_cast Metric.externalCoveringNumber_le_encard_self (P : Set (DSquare n))
    have h2 : (P : Set (DSquare n)).encard = (P.card : ℕ∞) := by simp
    rw [h2] at h
    exact_mod_cast h

  have h_main_cover : (Metric.externalCoveringNumber ε (B' : Set (ℝ × ℝ)) : ENNReal) ≤
      ENNReal.ofReal C_P * (ENNReal.ofReal r) ^ t * (P.card : ENNReal) := by
    calc (Metric.externalCoveringNumber ε (B' : Set (ℝ × ℝ)) : ENNReal)
      ≤ (Metric.externalCoveringNumber ε (B : Set (DSquare n)) : ENNReal) := by exact_mod_cast h_cover_B'
    _ ≤ (Metric.externalCoveringNumber ε ((P : Set (DSquare n)) ∩ Metric.closedBall p r) : ENNReal) := h_cover_mono
    _ ≤ ENNReal.ofReal C_P * (ENNReal.ofReal r) ^ t *
          (Metric.externalCoveringNumber ε (P : Set (DSquare n)) : ENNReal) := h_sset
    _ ≤ ENNReal.ofReal C_P * (ENNReal.ofReal r) ^ t * (P.card : ENNReal) := by gcongr

  have h3 : (B'.card : ENNReal) ≤
      9 * Metric.externalCoveringNumber ε (B' : Set (ℝ × ℝ)) :=
    EnergyBoundLemmas.separated_covering_lower_plane (δ_pos n) hB'_sep

  have h5 : (B'.card : ENNReal) ≤
      9 * (ENNReal.ofReal C_P * (ENNReal.ofReal r) ^ t * (P.card : ENNReal)) := by
    calc (B'.card : ENNReal)
      ≤ 9 * Metric.externalCoveringNumber ε (B' : Set (ℝ × ℝ)) := h3
    _ ≤ 9 * (ENNReal.ofReal C_P * (ENNReal.ofReal r) ^ t * (P.card : ENNReal)) := by
      gcongr

  have hr_nonneg : 0 ≤ r := by linarith
  have h_rpow_eq : (ENNReal.ofReal r) ^ t = ENNReal.ofReal (r ^ t) :=
    ENNReal.ofReal_rpow_of_nonneg hr_nonneg ht
  have h6 : (B'.card : ENNReal) ≤
      9 * (ENNReal.ofReal C_P * ENNReal.ofReal (r ^ t) * (P.card : ENNReal)) := by
    simpa [h_rpow_eq] using h5
  have h7 : (B.card : ENNReal) ≤
      9 * (ENNReal.ofReal C_P * ENNReal.ofReal (r ^ t) * (P.card : ENNReal)) := by
    rw [hB_card] at h6
    exact h6
  have hfin : (9 * (ENNReal.ofReal C_P * ENNReal.ofReal (r ^ t) * (P.card : ENNReal))) ≠ ⊤ := by
    simp [ENNReal.mul_ne_top, ENNReal.ofReal_ne_top]
    <;> tauto
  have h8 : (B.card : ℝ) ≤ 9 * C_P * r ^ t * (P.card : ℝ) := by
    have h9 : (B.card : ENNReal).toReal ≤ (9 * (ENNReal.ofReal C_P * ENNReal.ofReal (r ^ t) * (P.card : ENNReal))).toReal :=
      (ENNReal.toReal_le_toReal (by simp) hfin).mpr h7
    have h10 : (9 * (ENNReal.ofReal C_P * ENNReal.ofReal (r ^ t) * (P.card : ENNReal))).toReal =
        9 * C_P * r ^ t * (P.card : ℝ) := by
      have h11 : (ENNReal.ofReal C_P).toReal = C_P := ENNReal.toReal_ofReal (by linarith)
      have h12 : (ENNReal.ofReal (r ^ t)).toReal = r ^ t := ENNReal.toReal_ofReal (by positivity)
      have h13 : ((P.card : ENNReal)).toReal = (P.card : ℝ) := by simp
      simp [h11, h12, h13, ENNReal.toReal_mul] <;> ring
    rw [h10] at h9
    exact h9
  exact h8

/-! ========================================================================
   Annulus sum (from Ember, fully proved)
   ======================================================================== -/

lemma dyadic_decomp (δ : ℝ) (hδ_pos : 0 < δ) (N : ℕ) (d : ℝ)
    (h1 : δ ≤ d) (h2 : d < (2 : ℝ)^N * δ) :
    ∃ k : ℕ, k < N ∧ (2 : ℝ)^k * δ ≤ d ∧ d < (2 : ℝ)^(k + 1) * δ := by
  have h_main : ∀ (m : ℕ), d < (2 : ℝ)^m * δ →
      ∃ k : ℕ, k < m ∧ (2 : ℝ)^k * δ ≤ d ∧ d < (2 : ℝ)^(k + 1) * δ := by
    intro m
    induction m with
    | zero =>
      intro h
      exfalso
      have h0 : (2 : ℝ)^0 * δ = δ := by simp
      rw [h0] at h; linarith
    | succ m ih =>
      intro h
      by_cases h3 : d < (2 : ℝ)^m * δ
      · rcases ih h3 with ⟨k, hk, h4, h5⟩
        exact ⟨k, by linarith, h4, h5⟩
      · have h4 : (2 : ℝ)^m * δ ≤ d := by linarith
        exact ⟨m, by linarith, h4, by simpa [pow_succ] using h⟩
  exact h_main N h2

/-- Point-energy bound via dyadic annulus decomposition (Ember). -/
lemma pointEnergy_annulus_bound
    {X : Type*} [MetricSpace X] [DecidableEq X]
    {δ t C : ℝ} (hδ_pos : 0 < δ) (ht_pos : 0 < t) (hC_pos : 0 < C)
    (hδ_lt_3 : δ < 3)
    {P : Finset X}
    (h_sep : SeparatedAt δ (P : Set X))
    (h_growth : ∀ (x : X) (r : ℝ), δ ≤ r →
      ((P.filter (fun y => dist x y ≤ r)).card : ℝ) ≤ C * r^t * (P.card : ℝ))
    (h_diam : ∀ (x y : X), x ∈ P → y ∈ P → dist x y ≤ 3)
    (x : X) (hx : x ∈ P) :
    ∑ y ∈ P.erase x, Real.rpow (dist x y) (-t) ≤
      C * (2 : ℝ)^t * (P.card : ℝ) * (Real.log (3 / δ) / Real.log 2 + 1) := by
  have h_log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h3_div_delta_pos : 0 < 3 / δ := by positivity
  have h_log_nonneg : 0 ≤ Real.log (3 / δ) / Real.log 2 := by
    have h1 : 1 ≤ 3 / δ := by
      apply (div_le_one (by positivity)).mp; linarith
    have h2 : 0 ≤ Real.log (3 / δ) := Real.log_nonneg h1
    positivity
  let c : ℤ := ⌊Real.log (3 / δ) / Real.log 2⌋ + 1
  have hc_nonneg : 0 ≤ c := by
    have h1 : 0 ≤ Real.log (3 / δ) / Real.log 2 := h_log_nonneg
    have h2 : 0 ≤ ⌊Real.log (3 / δ) / Real.log 2⌋ := Int.floor_nonneg.mpr h1
    linarith
  let N : ℕ := c.toNat
  have hN_eq : (N : ℤ) = c := by
    simp [N, Int.toNat_of_nonneg hc_nonneg]
  have hN_gt : (N : ℝ) > Real.log (3 / δ) / Real.log 2 := by
    have h2 : (c : ℝ) > Real.log (3 / δ) / Real.log 2 := by
      have h3 : (⌊Real.log (3 / δ) / Real.log 2⌋ : ℝ) ≤ Real.log (3 / δ) / Real.log 2 := Int.floor_le _
      have h4 : Real.log (3 / δ) / Real.log 2 < (⌊Real.log (3 / δ) / Real.log 2⌋ : ℝ) + 1 := Int.lt_floor_add_one _
      simpa [c] using h4
    have h3 : (N : ℝ) = (c : ℝ) := by exact_mod_cast hN_eq
    linarith
  have hN_le : (N : ℝ) ≤ Real.log (3 / δ) / Real.log 2 + 1 := by
    have h2 : (c : ℝ) ≤ Real.log (3 / δ) / Real.log 2 + 1 := by
      have h3 : (⌊Real.log (3 / δ) / Real.log 2⌋ : ℝ) ≤ Real.log (3 / δ) / Real.log 2 := Int.floor_le _
      simpa [c] using add_le_add_right h3 1
    have h3 : (N : ℝ) = (c : ℝ) := by exact_mod_cast hN_eq
    linarith
  have h2N_delta_gt_3 : (2 : ℝ)^N * δ > 3 := by
    have h1 : Real.log ((2 : ℝ)^N) = (N : ℝ) * Real.log 2 := by
      rw [Real.log_pow] <;> ring
    have h2 : (N : ℝ) * Real.log 2 > Real.log (3 / δ) := by
      calc (N : ℝ) * Real.log 2
        > (Real.log (3 / δ) / Real.log 2) * Real.log 2 := by gcongr
      _ = Real.log (3 / δ) := by field_simp [h_log2_pos.ne'] <;> ring
    have h3 : Real.log ((2 : ℝ)^N * δ) > Real.log 3 := by
      have h4 : Real.log ((2 : ℝ)^N * δ) = Real.log ((2 : ℝ)^N) + Real.log δ :=
        Real.log_mul (by positivity) (by positivity)
      rw [h4, h1]
      have h5 : Real.log (3 / δ) + Real.log δ = Real.log 3 := by
        rw [←Real.log_mul (by positivity) (by positivity)] <;> field_simp [hδ_pos.ne'] <;> ring
      linarith
    have h6 : (2 : ℝ)^N * δ > 0 := by positivity
    exact (Real.log_lt_log_iff (by positivity) h6).mp h3
  let shell (k : ℕ) : Finset X :=
    P.filter (fun y => (2 : ℝ)^k * δ ≤ dist x y ∧ dist x y < (2 : ℝ)^(k + 1) * δ)
  have h_shell_disjoint : ∀ k ∈ Finset.range N, ∀ l ∈ Finset.range N, k ≠ l →
      Disjoint (shell k) (shell l) := by
    intro k hk l hl hne
    simp only [shell, Finset.disjoint_left]
    intro y hy1 hy2
    have h1 := (Finset.mem_filter.mp hy1).2
    have h2 := (Finset.mem_filter.mp hy2).2
    by_cases hkl : k < l
    · have h3 : (2 : ℝ)^l * δ ≤ dist x y := h2.1
      have h4 : dist x y < (2 : ℝ)^(k + 1) * δ := h1.2
      have h5 : (2 : ℝ)^(k + 1) * δ ≤ (2 : ℝ)^l * δ := by gcongr <;> linarith
      linarith
    · have hkl' : l < k := by omega
      have h3 : (2 : ℝ)^k * δ ≤ dist x y := h1.1
      have h4 : dist x y < (2 : ℝ)^(l + 1) * δ := h2.2
      have h5 : (2 : ℝ)^(l + 1) * δ ≤ (2 : ℝ)^k * δ := by gcongr <;> linarith
      linarith
  have h_shell_cover : P.erase x = Finset.biUnion (Finset.range N) shell := by
    ext y
    simp only [Finset.mem_erase, Finset.mem_biUnion]
    constructor
    · rintro ⟨hyne, hyS⟩
      have hdist_ge : δ ≤ dist x y := h_sep hx hyS hyne.symm
      have hdist_le : dist x y ≤ 3 := h_diam x y hx hyS
      have hdist_lt : dist x y < (2 : ℝ)^N * δ := by
        calc dist x y ≤ 3 := hdist_le
             _ < (2 : ℝ)^N * δ := h2N_delta_gt_3
      have h_exists := dyadic_decomp δ hδ_pos N (dist x y) hdist_ge hdist_lt
      rcases h_exists with ⟨k, hk_lt_N, h_low, h_high⟩
      have hk : k ∈ Finset.range N := Finset.mem_range.mpr hk_lt_N
      have h_in_shell : y ∈ shell k := by
        have hprop : (2 : ℝ)^k * δ ≤ dist x y ∧ dist x y < (2 : ℝ)^(k + 1) * δ := ⟨h_low, h_high⟩
        exact Finset.mem_filter.mpr ⟨hyS, hprop⟩
      exact ⟨k, hk, h_in_shell⟩
    · rintro ⟨k, _, hy⟩
      have hyS : y ∈ P := (Finset.mem_filter.mp hy).1
      have hprop := (Finset.mem_filter.mp hy).2
      have hyne : y ≠ x := by
        intro h
        rw [h] at hprop
        have h6 : dist x x = 0 := dist_self x
        rw [h6] at hprop
        have h7 : 0 < (2 : ℝ)^k * δ := by positivity
        linarith
      exact ⟨hyne, hyS⟩
  have h_shell_bound : ∀ k ∈ Finset.range N,
      ((shell k).card : ℝ) ≤ C * Real.rpow ((2 : ℝ)^(k + 1) * δ) t * (P.card : ℝ) := by
    intro k _
    have h1 : shell k ⊆ P.filter (fun y => dist x y ≤ (2 : ℝ)^(k + 1) * δ) := by
      intro y hy
      have h2 := (Finset.mem_filter.mp hy).2
      have h2' : dist x y ≤ (2 : ℝ)^(k + 1) * δ := by linarith
      have hys : y ∈ P := (Finset.mem_filter.mp hy).1
      exact Finset.mem_filter.mpr ⟨hys, h2'⟩
    have h3 : (shell k).card ≤ (P.filter (fun y => dist x y ≤ (2 : ℝ)^(k + 1) * δ)).card :=
      Finset.card_le_card h1
    have h4 : δ ≤ (2 : ℝ)^(k + 1) * δ := by
      have h5 : (1 : ℝ) ≤ (2 : ℝ)^(k + 1) := by
        have h6 : 1 ≤ 2 ^ (k + 1) := by apply Nat.one_le_pow <;> norm_num
        exact_mod_cast h6
      nlinarith
    have h5 := h_growth x ((2 : ℝ)^(k + 1) * δ) h4
    have h3' : ((shell k).card : ℝ) ≤
        ((P.filter (fun y => dist x y ≤ (2 : ℝ)^(k + 1) * δ)).card : ℝ) := by exact_mod_cast h3
    exact le_trans h3' h5
  have h_shell_energy : ∀ k ∈ Finset.range N,
      ∑ y ∈ shell k, Real.rpow (dist x y) (-t) ≤
      C * (2 : ℝ)^t * (P.card : ℝ) := by
    intro k hk
    have h1 : ∀ y ∈ shell k, Real.rpow (dist x y) (-t) ≤ Real.rpow ((2 : ℝ)^k * δ) (-t) := by
      intro y hy
      have h2 : (2 : ℝ)^k * δ ≤ dist x y := (Finset.mem_filter.mp hy).2.1
      have h3 : 0 < (2 : ℝ)^k * δ := by positivity
      have h4 : 0 < dist x y := by linarith
      have h5 : Real.rpow (dist x y) t ≥ Real.rpow ((2 : ℝ)^k * δ) t :=
        Real.rpow_le_rpow h3.le h2 ht_pos.le
      have h6 : Real.rpow (dist x y) (-t) = (Real.rpow (dist x y) t)⁻¹ := by
        simpa using Real.rpow_neg (by linarith) t
      have h7 : Real.rpow ((2 : ℝ)^k * δ) (-t) = (Real.rpow ((2 : ℝ)^k * δ) t)⁻¹ := by
        simpa using Real.rpow_neg h3.le t
      rw [h6, h7]
      have h_pos1 : 0 < Real.rpow ((2 : ℝ)^k * δ) t := Real.rpow_pos_of_pos h3 t
      have h_pos2 : 0 < Real.rpow (dist x y) t := Real.rpow_pos_of_pos h4 t
      have h_goal : (Real.rpow (dist x y) t)⁻¹ ≤ (Real.rpow ((2 : ℝ)^k * δ) t)⁻¹ := by
        have h : 1 / Real.rpow (dist x y) t ≤ 1 / Real.rpow ((2 : ℝ)^k * δ) t :=
          one_div_le_one_div_of_le h_pos1 h5
        simpa [one_div] using h
      exact h_goal
    have h4 : ∑ y ∈ shell k, Real.rpow (dist x y) (-t) ≤
        ((shell k).card : ℝ) * Real.rpow ((2 : ℝ)^k * δ) (-t) := by
      calc ∑ y ∈ shell k, Real.rpow (dist x y) (-t)
        ≤ ∑ y ∈ shell k, Real.rpow ((2 : ℝ)^k * δ) (-t) := Finset.sum_le_sum h1
      _ = ((shell k).card : ℝ) * Real.rpow ((2 : ℝ)^k * δ) (-t) := by
        simp [Finset.sum_const] <;> ring
    have h5 : ((shell k).card : ℝ) ≤ C * Real.rpow ((2 : ℝ)^(k + 1) * δ) t * (P.card : ℝ) :=
      h_shell_bound k hk
    have h7 : ((shell k).card : ℝ) * Real.rpow ((2 : ℝ)^k * δ) (-t) ≤
        (C * Real.rpow ((2 : ℝ)^(k + 1) * δ) t * (P.card : ℝ)) * Real.rpow ((2 : ℝ)^k * δ) (-t) := by
      have h_pos : 0 ≤ Real.rpow ((2 : ℝ)^k * δ) (-t) := Real.rpow_nonneg (by positivity) _
      gcongr <;> linarith
    have h9 : 0 < (2 : ℝ)^k * δ := by positivity
    have h10 : (2 : ℝ)^(k + 1) * δ = 2 * ((2 : ℝ)^k * δ) := by
      simp [pow_succ] <;> ring
    have h8 : Real.rpow ((2 : ℝ)^(k + 1) * δ) t * Real.rpow ((2 : ℝ)^k * δ) (-t) = (2 : ℝ)^t := by
      rw [h10]
      have h13 : Real.rpow (2 * ((2 : ℝ)^k * δ)) t =
          Real.rpow 2 t * Real.rpow ((2 : ℝ)^k * δ) t :=
        Real.mul_rpow (by norm_num) (by positivity)
      rw [h13]
      have h15 : Real.rpow ((2 : ℝ)^k * δ) (-t) = (Real.rpow ((2 : ℝ)^k * δ) t)⁻¹ := by
        simpa using Real.rpow_neg h9.le t
      rw [h15]
      field_simp [h9.ne'] <;> ring_nf <;> norm_cast
    calc ∑ y ∈ shell k, Real.rpow (dist x y) (-t)
      ≤ ((shell k).card : ℝ) * Real.rpow ((2 : ℝ)^k * δ) (-t) := h4
    _ ≤ (C * Real.rpow ((2 : ℝ)^(k + 1) * δ) t * (P.card : ℝ)) * Real.rpow ((2 : ℝ)^k * δ) (-t) := h7
    _ = C * (Real.rpow ((2 : ℝ)^(k + 1) * δ) t * Real.rpow ((2 : ℝ)^k * δ) (-t)) * (P.card : ℝ) := by ring
    _ = C * (2 : ℝ)^t * (P.card : ℝ) := by rw [h8] <;> ring
  have h_main : ∑ y ∈ P.erase x, Real.rpow (dist x y) (-t) =
      ∑ k ∈ Finset.range N, ∑ y ∈ shell k, Real.rpow (dist x y) (-t) := by
    rw [h_shell_cover]
    rw [Finset.sum_biUnion]
    <;> exact h_shell_disjoint
  have h_final : ∑ k ∈ Finset.range N, ∑ y ∈ shell k, Real.rpow (dist x y) (-t) ≤
      (N : ℝ) * (C * (2 : ℝ)^t * (P.card : ℝ)) := by
    calc ∑ k ∈ Finset.range N, ∑ y ∈ shell k, Real.rpow (dist x y) (-t)
      ≤ ∑ k ∈ Finset.range N, C * (2 : ℝ)^t * (P.card : ℝ) :=
        Finset.sum_le_sum (fun k hk => h_shell_energy k hk)
    _ = (N : ℝ) * (C * (2 : ℝ)^t * (P.card : ℝ)) := by
      simp [Finset.sum_const] <;> ring
  have hN_bound : (N : ℝ) ≤ Real.log (3 / δ) / Real.log 2 + 1 := hN_le
  calc ∑ y ∈ P.erase x, Real.rpow (dist x y) (-t)
    = ∑ k ∈ Finset.range N, ∑ y ∈ shell k, Real.rpow (dist x y) (-t) := h_main
  _ ≤ (N : ℝ) * (C * (2 : ℝ)^t * (P.card : ℝ)) := h_final
  _ ≤ (Real.log (3 / δ) / Real.log 2 + 1) * (C * (2 : ℝ)^t * (P.card : ℝ)) := by
    gcongr <;> linarith
  _ = C * (2 : ℝ)^t * (P.card : ℝ) * (Real.log (3 / δ) / Real.log 2 + 1) := by ring

/-- Total pair-energy bound (Ember). -/
lemma pairEnergy_annulus_bound
    {X : Type*} [MetricSpace X] [DecidableEq X]
    {δ t C : ℝ} (hδ_pos : 0 < δ) (ht_pos : 0 < t) (hC_pos : 0 < C)
    (hδ_lt_3 : δ < 3)
    {P : Finset X}
    (h_sep : SeparatedAt δ (P : Set X))
    (h_growth : ∀ (x : X) (r : ℝ), δ ≤ r →
      ((P.filter (fun y => dist x y ≤ r)).card : ℝ) ≤ C * r^t * (P.card : ℝ))
    (h_diam : ∀ (x y : X), x ∈ P → y ∈ P → dist x y ≤ 3) :
    ∑ x ∈ P, ∑ y ∈ P.erase x, Real.rpow (dist x y) (-t) ≤
      C * (2 : ℝ)^t * (P.card : ℝ)^2 * (Real.log (3 / δ) / Real.log 2 + 1) := by
  have h1 : ∀ x ∈ P, ∑ y ∈ P.erase x, Real.rpow (dist x y) (-t) ≤
      C * (2 : ℝ)^t * (P.card : ℝ) * (Real.log (3 / δ) / Real.log 2 + 1) :=
    fun x hx => pointEnergy_annulus_bound hδ_pos ht_pos hC_pos hδ_lt_3 h_sep h_growth h_diam x hx
  calc ∑ x ∈ P, ∑ y ∈ P.erase x, Real.rpow (dist x y) (-t)
    ≤ ∑ x ∈ P, C * (2 : ℝ)^t * (P.card : ℝ) * (Real.log (3 / δ) / Real.log 2 + 1) :=
      Finset.sum_le_sum h1
  _ = C * (2 : ℝ)^t * (P.card : ℝ)^2 * (Real.log (3 / δ) / Real.log 2 + 1) := by
    simp [Finset.sum_const] <;> ring

/-! ### Intercept difference bound -/

/-- If two tubes both meet a square p whose x-coordinates lie in [-1,1],
    then their intercepts differ by at most `4δ + |slope1 - slope2|`. -/
lemma intercept_diff_near_square {n : ℕ} {p : DSquare n} {T1 T2 : DTube n}
    (h1 : (T1.toSet ∩ p.toSet).Nonempty)
    (h2 : (T2.toSet ∩ p.toSet).Nonempty)
    (h_slope1 : |T1.slope| ≤ 1)
    (h_x_bound : ∀ (x : ℝ × ℝ), x ∈ p.toSet → |x.1| ≤ 1) :
    |T1.intercept - T2.intercept| ≤ 4 * δ n + |T1.slope - T2.slope| := by
  rcases h1 with ⟨x, hxT1, hxS1⟩
  rcases h2 with ⟨y, hyT2, hyS2⟩
  have h_e1 : |x.2 - T1.slope * x.1 - T1.intercept| ≤ δ n := hxT1
  have h_e2 : |y.2 - T2.slope * y.1 - T2.intercept| ≤ δ n := hyT2
  have h_xdiff : |x.1 - y.1| ≤ δ n := by
    have h11 : (p.i : ℝ) * δ n ≤ x.1 := hxS1.1
    have h12 : x.1 < ((p.i : ℝ) + 1) * δ n := hxS1.2.1
    have h21 : (p.i : ℝ) * δ n ≤ y.1 := hyS2.1
    have h22 : y.1 < ((p.i : ℝ) + 1) * δ n := hyS2.2.1
    rw [abs_sub_le_iff] <;> constructor <;> linarith
  have h_ydiff : |x.2 - y.2| ≤ δ n := by
    have h11 : (p.j : ℝ) * δ n ≤ x.2 := hxS1.2.2.1
    have h12 : x.2 < ((p.j : ℝ) + 1) * δ n := hxS1.2.2.2
    have h21 : (p.j : ℝ) * δ n ≤ y.2 := hyS2.2.2.1
    have h22 : y.2 < ((p.j : ℝ) + 1) * δ n := hyS2.2.2.2
    rw [abs_sub_le_iff] <;> constructor <;> linarith
  have h_y1_bound : |y.1| ≤ 1 := h_x_bound y hyS2
  have h_main : T1.intercept - T2.intercept =
      (x.2 - y.2) - T1.slope * (x.1 - y.1) + (T2.slope - T1.slope) * y.1 +
      ((y.2 - T2.slope * y.1 - T2.intercept) - (x.2 - T1.slope * x.1 - T1.intercept)) := by ring
  rw [h_main]
  set a := x.2 - y.2 with ha_def
  set b := -T1.slope * (x.1 - y.1) with hb_def
  set c := (T2.slope - T1.slope) * y.1 with hc_def
  set d := (y.2 - T2.slope * y.1 - T2.intercept) - (x.2 - T1.slope * x.1 - T1.intercept) with hd_def
  have h_abs_add : ∀ (x y : ℝ), |x + y| ≤ |x| + |y| := by
    intro x y
    have h1 : x ≤ |x| := le_abs_self x
    have h2 : y ≤ |y| := le_abs_self y
    have h3 : -x ≤ |x| := by simpa [abs_neg] using le_abs_self (-x)
    have h4 : -y ≤ |y| := by simpa [abs_neg] using le_abs_self (-y)
    rw [abs_le] <;> constructor <;> linarith
  have h_abs4 : |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
    have h1 : |a + b + c + d| ≤ |a + b + c| + |d| := by
      simpa [add_assoc] using h_abs_add (a + b + c) d
    have h2 : |a + b + c| ≤ |a| + |b| + |c| := by
      have h21 : |a + b + c| ≤ |a + b| + |c| := by
        simpa [add_assoc] using h_abs_add (a + b) c
      have h22 : |a + b| ≤ |a| + |b| := h_abs_add a b
      linarith
    linarith
  have ha : |a| ≤ δ n := h_ydiff
  have hb : |b| ≤ δ n := by
    have hb1 : |b| = |T1.slope| * |x.1 - y.1| := by
      simp [hb_def, abs_mul] <;> ring
    rw [hb1]
    have h : |T1.slope| * |x.1 - y.1| ≤ 1 * δ n := by
      gcongr <;> linarith [h_slope1, h_xdiff]
    linarith
  have hc : |c| ≤ |T2.slope - T1.slope| := by
    have hc1 : |c| = |T2.slope - T1.slope| * |y.1| := by
      simp [hc_def, abs_mul] <;> ring
    rw [hc1]
    have h : |y.1| ≤ 1 := h_y1_bound
    have h5 : |T2.slope - T1.slope| * |y.1| ≤ |T2.slope - T1.slope| := by
      have h6 : 0 ≤ |T2.slope - T1.slope| := abs_nonneg _
      nlinarith
    exact h5
  have hd : |d| ≤ 2 * δ n := by
    have h11 : d = (y.2 - T2.slope * y.1 - T2.intercept) - (x.2 - T1.slope * x.1 - T1.intercept) := by
      simp [hd_def] <;> ring
    rw [h11]
    have h12 : |(y.2 - T2.slope * y.1 - T2.intercept) - (x.2 - T1.slope * x.1 - T1.intercept)| ≤
        |y.2 - T2.slope * y.1 - T2.intercept| + |x.2 - T1.slope * x.1 - T1.intercept| := by
      exact abs_sub _ _
    have h2 : |x.2 - T1.slope * x.1 - T1.intercept| ≤ δ n := h_e1
    have h3 : |y.2 - T2.slope * y.1 - T2.intercept| ≤ δ n := h_e2
    linarith
  have h_final : |a + b + c + d| ≤ 4 * δ n + |T2.slope - T1.slope| := by
    calc |a + b + c + d|
      ≤ |a| + |b| + |c| + |d| := h_abs4
    _ ≤ δ n + δ n + |T2.slope - T1.slope| + 2 * δ n := by linarith
    _ = 4 * δ n + |T2.slope - T1.slope| := by ring
  have h_abs_comm : |T2.slope - T1.slope| = |T1.slope - T2.slope| := by
    rw [show T2.slope - T1.slope = -(T1.slope - T2.slope) by ring, abs_neg]
  have h_final2 : |a + b + c + d| ≤ 4 * δ n + |T1.slope - T2.slope| := by
    rw [h_abs_comm] at h_final
    exact h_final
  have h_eq2 : (x.2 - y.2) - T1.slope * (x.1 - y.1) + (T2.slope - T1.slope) * y.1 + ((y.2 - T2.slope * y.1 - T2.intercept) - (x.2 - T1.slope * x.1 - T1.intercept)) = a + b + c + d := by
    simp [ha_def, hb_def, hc_def, hd_def] <;> ring
  rw [h_eq2]
  exact h_final2

/-! ### Small-distance bound -/

/-- If k ≤ 1 and a common tube with |slope|≤1 exists, then dist(p,p') ≤ 7δ. -/
lemma small_k_dist_bound {n : ℕ} {p p' : DSquare n} {T : DTube n}
    (h1 : (T.toSet ∩ p.toSet).Nonempty)
    (h2 : (T.toSet ∩ p'.toSet).Nonempty)
    (h_slope : |T.slope| ≤ 1)
    (hk : Int.natAbs (p.i - p'.i) ≤ 1) :
    dist p p' ≤ 7 * δ n := by
  rcases h1 with ⟨x, hxT, hxS⟩
  rcases h2 with ⟨y, hyT, hyS⟩
  have hδ : 0 < δ n := δ_pos n
  have h_abs_add : ∀ (a b : ℝ), |a + b| ≤ |a| + |b| := by
    intro a b
    have h1 : a ≤ |a| := le_abs_self a
    have h2 : b ≤ |b| := le_abs_self b
    have h3 : -a ≤ |a| := by simpa [abs_neg] using le_abs_self (-a)
    have h4 : -b ≤ |b| := by simpa [abs_neg] using le_abs_self (-b)
    rw [abs_le] <;> constructor <;> linarith
  have h_e1 : |x.2 - T.slope * x.1 - T.intercept| ≤ δ n := hxT
  have h_e2 : |y.2 - T.slope * y.1 - T.intercept| ≤ δ n := hyT
  have h_abs_i : |(p.i : ℝ) - (p'.i : ℝ)| ≤ 1 := by
    have h : |(p.i - p'.i : ℤ)| = ↑(Int.natAbs (p.i - p'.i)) := by
      rw [Int.abs_eq_natAbs]
    have h' : |(p.i - p'.i : ℤ)| ≤ 1 := by
      rw [h]
      exact_mod_cast hk
    exact_mod_cast h'
  have h_i1 : (p.i : ℝ) - (p'.i : ℝ) ≤ 1 := (abs_le.mp h_abs_i).2
  have h_i2 : -1 ≤ (p.i : ℝ) - (p'.i : ℝ) := (abs_le.mp h_abs_i).1
  have h_xdiff : |x.1 - y.1| ≤ 2 * δ n := by
    have h_i1 : (p.i : ℝ) - (p'.i : ℝ) ≤ 1 := (abs_le.mp h_abs_i).2
    have h_i2 : -1 ≤ (p.i : ℝ) - (p'.i : ℝ) := (abs_le.mp h_abs_i).1
    have h11 : (p.i : ℝ) * δ n ≤ x.1 := hxS.1
    have h12 : x.1 < ((p.i : ℝ) + 1) * δ n := hxS.2.1
    have h21 : (p'.i : ℝ) * δ n ≤ y.1 := hyS.1
    have h22 : y.1 < ((p'.i : ℝ) + 1) * δ n := hyS.2.1
    have h_upper : x.1 - y.1 < 2 * δ n := by
      have h : x.1 - y.1 < ((p.i : ℝ) - (p'.i : ℝ) + 1) * δ n := by linarith
      have h' : ((p.i : ℝ) - (p'.i : ℝ) + 1) * δ n ≤ 2 * δ n := by
        have h'' : (p.i : ℝ) - (p'.i : ℝ) ≤ 1 := h_i1
        nlinarith
      linarith
    have h_lower : -(2 * δ n) ≤ x.1 - y.1 := by
      have h : y.1 - x.1 < ((p'.i : ℝ) - (p.i : ℝ) + 1) * δ n := by linarith
      have h' : ((p'.i : ℝ) - (p.i : ℝ) + 1) * δ n ≤ 2 * δ n := by
        have h'' : (p'.i : ℝ) - (p.i : ℝ) ≤ 1 := by linarith
        nlinarith
      linarith
    rw [abs_le] <;> constructor <;> linarith
  have h_ydiff : |x.2 - y.2| ≤ |T.slope| * |x.1 - y.1| + 2 * δ n := by
    let a := x.2 - T.slope * x.1 - T.intercept
    let b := y.2 - T.slope * y.1 - T.intercept
    let c := T.slope * (x.1 - y.1)
    have h_eq : x.2 - y.2 = a - b + c := by
      simp [a, b, c] <;> ring
    rw [h_eq]
    have h1 : |a - b + c| ≤ |a - b| + |c| := by
      have h : a - b + c = (a - b) + c := by ring
      rw [h]
      exact h_abs_add (a - b) c
    have h2 : |a - b| ≤ |a| + |b| := by
      have h3 : a - b = a + (-b) := by ring
      rw [h3]
      have h4 : |a + (-b)| ≤ |a| + |(-b)| := h_abs_add a (-b)
      have h5 : |(-b)| = |b| := by simp [abs_neg]
      rw [h5] at h4; exact h4
    have h3 : |a - b + c| ≤ |a| + |b| + |c| := by linarith
    have h4 : |c| = |T.slope| * |x.1 - y.1| := by
      simp [c, abs_mul] <;> ring
    rw [h4] at h3
    have h5 : |a| ≤ δ n := h_e1
    have h6 : |b| ≤ δ n := h_e2
    linarith
  have h_ydiff2 : |x.2 - y.2| ≤ 4 * δ n := by
    calc |x.2 - y.2|
      ≤ |T.slope| * |x.1 - y.1| + 2 * δ n := h_ydiff
    _ ≤ 1 * (2 * δ n) + 2 * δ n := by gcongr <;> linarith [h_slope]
    _ = 4 * δ n := by ring
  have h_jdiff : |(p.j : ℝ) - (p'.j : ℝ)| ≤ 5 := by
    have h4 : |(p.j : ℝ) * δ n - x.2| < δ n := by
      have h5 : (p.j : ℝ) * δ n ≤ x.2 := hxS.2.2.1
      have h6 : x.2 < ((p.j : ℝ) + 1) * δ n := hxS.2.2.2
      have h7 : (p.j : ℝ) * δ n - x.2 ≤ 0 := by linarith
      rw [abs_of_nonpos h7] <;> linarith
    have h7 : |(p'.j : ℝ) * δ n - y.2| < δ n := by
      have h8 : (p'.j : ℝ) * δ n ≤ y.2 := hyS.2.2.1
      have h9 : y.2 < ((p'.j : ℝ) + 1) * δ n := hyS.2.2.2
      have h10 : (p'.j : ℝ) * δ n - y.2 ≤ 0 := by linarith
      rw [abs_of_nonpos h10] <;> linarith
    have h14 : |(p.j : ℝ) * δ n - (p'.j : ℝ) * δ n| ≤ |(p.j : ℝ) * δ n - x.2| + |x.2 - y.2| + |y.2 - (p'.j : ℝ) * δ n| := by
      have h15 : |(p.j : ℝ) * δ n - (p'.j : ℝ) * δ n| ≤ |(p.j : ℝ) * δ n - x.2| + |x.2 - (p'.j : ℝ) * δ n| := by
        have h_eq : (p.j : ℝ) * δ n - (p'.j : ℝ) * δ n =
            ((p.j : ℝ) * δ n - x.2) + (x.2 - (p'.j : ℝ) * δ n) := by ring
        rw [h_eq]
        exact h_abs_add _ _
      have h16 : |x.2 - (p'.j : ℝ) * δ n| ≤ |x.2 - y.2| + |y.2 - (p'.j : ℝ) * δ n| := by
        have h17 : x.2 - (p'.j : ℝ) * δ n = (x.2 - y.2) + (y.2 - (p'.j : ℝ) * δ n) := by ring
        rw [h17]
        exact h_abs_add _ _
      linarith
    have h13 : |(p.j : ℝ) * δ n - (p'.j : ℝ) * δ n| < 6 * δ n := by
      have h_abs_symm : |y.2 - (p'.j : ℝ) * δ n| = |(p'.j : ℝ) * δ n - y.2| := by
        rw [show y.2 - (p'.j : ℝ) * δ n = -((p'.j : ℝ) * δ n - y.2) by ring, abs_neg]
      have h_sum : |(p.j : ℝ) * δ n - x.2| + |x.2 - y.2| + |(p'.j : ℝ) * δ n - y.2| < 6 * δ n := by
        linarith [h4, h7, h_ydiff2]
      calc |(p.j : ℝ) * δ n - (p'.j : ℝ) * δ n|
        ≤ |(p.j : ℝ) * δ n - x.2| + |x.2 - y.2| + |y.2 - (p'.j : ℝ) * δ n| := h14
      _ = |(p.j : ℝ) * δ n - x.2| + |x.2 - y.2| + |(p'.j : ℝ) * δ n - y.2| := by rw [h_abs_symm]
      _ < 6 * δ n := h_sum
    have h15 : |(p.j : ℝ) - (p'.j : ℝ)| * δ n < 6 * δ n := by
      have h16 : |(p.j : ℝ) * δ n - (p'.j : ℝ) * δ n| = |(p.j : ℝ) - (p'.j : ℝ)| * δ n := by
        rw [show (p.j : ℝ) * δ n - (p'.j : ℝ) * δ n = ((p.j : ℝ) - (p'.j : ℝ)) * δ n by ring]
        rw [abs_mul, abs_of_pos hδ] <;> ring
      rw [h16] at h13; exact h13
    have h17 : |(p.j : ℝ) - (p'.j : ℝ)| < 6 := by nlinarith
    have h18 : |(p.j : ℝ) - (p'.j : ℝ)| ≤ 5 := by
      have h19 : |(p.j - p'.j : ℤ)| < 6 := by exact_mod_cast h17
      have h20 : |(p.j - p'.j : ℤ)| ≤ 5 := by omega
      exact_mod_cast h20
    exact h18
  have h_dist : dist p p' =
      max (|(p.i : ℝ) - (p'.i : ℝ)| * δ n) (|(p.j : ℝ) - (p'.j : ℝ)| * δ n) := by
    have h1 : dist p p' = dist p.toPoint p'.toPoint := by rfl
    rw [h1]
    have h2 : dist p.toPoint p'.toPoint =
        max (|(p.i : ℝ) * δ n - (p'.i : ℝ) * δ n|) (|(p.j : ℝ) * δ n - (p'.j : ℝ) * δ n|) := by
      simp [DSquare.toPoint, Prod.dist_eq] <;> rfl
    rw [h2]
    have h3 : |(p.i : ℝ) * δ n - (p'.i : ℝ) * δ n| = |(p.i : ℝ) - (p'.i : ℝ)| * δ n := by
      rw [show (p.i : ℝ) * δ n - (p'.i : ℝ) * δ n = ((p.i : ℝ) - (p'.i : ℝ)) * δ n by ring]
      rw [abs_mul, abs_of_pos hδ] <;> ring
    have h4 : |(p.j : ℝ) * δ n - (p'.j : ℝ) * δ n| = |(p.j : ℝ) - (p'.j : ℝ)| * δ n := by
      rw [show (p.j : ℝ) * δ n - (p'.j : ℝ) * δ n = ((p.j : ℝ) - (p'.j : ℝ)) * δ n by ring]
      rw [abs_mul, abs_of_pos hδ] <;> ring
    rw [h3, h4] <;> rw [mul_max_of_nonneg _ _ (by linarith)] <;> ring
  rw [h_dist]
  have h5 : |(p.i : ℝ) - (p'.i : ℝ)| * δ n ≤ 7 * δ n := by
    have h6 : |(p.i : ℝ) - (p'.i : ℝ)| ≤ 1 := h_abs_i
    nlinarith
  have h7 : |(p.j : ℝ) - (p'.j : ℝ)| * δ n ≤ 7 * δ n := by
    have h8 : |(p.j : ℝ) - (p'.j : ℝ)| ≤ 5 := h_jdiff
    nlinarith
  exact max_le_iff.mpr ⟨h5, h7⟩

/-! ### DTube packing bound -/

/-- Any finite set of dyadic tubes is δ-separated in parameter space. -/
lemma dtube_separated {n : ℕ} {δ' : ℝ} (hδ_pos : 0 < δ') (hδ_eq : δ' = DiscretisedFurstenbergEstimate.δ n)
    {S : Finset (DTube n)} : SeparatedAt δ' (S : Set (DTube n)) := by
  have h_int_abs : ∀ (x y : ℤ), x ≠ y → |(x : ℝ) - (y : ℝ)| ≥ 1 := by
    intro x y hxy
    have h1 : x - y ≠ 0 := by omega
    have h2 : 1 ≤ Int.natAbs (x - y) := by omega
    have h3 : |(x - y : ℤ)| = ↑(Int.natAbs (x - y)) := by rw [Int.abs_eq_natAbs]
    have h4 : |(x : ℝ) - (y : ℝ)| = |(x - y : ℤ)| := by exact_mod_cast rfl
    rw [h4, h3]; exact_mod_cast h2
  intro T hT T' hT' hne
  have h : T.a ≠ T'.a ∨ T.b ≠ T'.b := by
    by_contra h'; push Not at h'
    have h_eq : T = T' := by cases T; cases T'; simp_all
    exact hne h_eq
  rcases h with (ha | hb)
  · have h1 : |(T.a : ℝ) - (T'.a : ℝ)| ≥ 1 := h_int_abs T.a T'.a ha
    have h2 : dist T T' ≥ |T.slope - T'.slope| := by
      have hdist : dist T T' = max (|T.slope - T'.slope|) (|T.intercept - T'.intercept|) := by
        have h1 : dist T T' = dist T.toParam T'.toParam := by rfl
        rw [h1]
        have h2 : dist T.toParam T'.toParam = max (|(T.toParam).1 - (T'.toParam).1|) (|(T.toParam).2 - (T'.toParam).2|) := by
          simp [Prod.dist_eq] <;> rfl
        rw [h2]
        have h3 : (T.toParam).1 = T.slope := by simp [DTube.toParam]
        have h4 : (T.toParam).2 = T.intercept := by simp [DTube.toParam]
        have h5 : (T'.toParam).1 = T'.slope := by simp [DTube.toParam]
        have h6 : (T'.toParam).2 = T'.intercept := by simp [DTube.toParam]
        rw [h3, h4, h5, h6]
      rw [hdist]
      exact le_max_left _ _
    have h3 : |T.slope - T'.slope| = |(T.a : ℝ) - (T'.a : ℝ)| * δ' := by
      have hslope : T.slope - T'.slope = ((T.a : ℝ) - (T'.a : ℝ)) * DiscretisedFurstenbergEstimate.δ n := by
        simp [DTube.slope] <;> ring
      rw [hslope]
      have h4 : ((T.a : ℝ) - (T'.a : ℝ)) * DiscretisedFurstenbergEstimate.δ n = ((T.a : ℝ) - (T'.a : ℝ)) * δ' := by
        rw [hδ_eq.symm] <;> ring
      rw [h4, abs_mul, abs_of_pos hδ_pos] <;> ring
    rw [h3] at h2
    have h4 : |(T.a : ℝ) - (T'.a : ℝ)| * δ' ≥ δ' := by
      have h5 : 0 < δ' := hδ_pos
      nlinarith [h1]
    linarith
  · have h1 : |(T.b : ℝ) - (T'.b : ℝ)| ≥ 1 := h_int_abs T.b T'.b hb
    have h2 : dist T T' ≥ |T.intercept - T'.intercept| := by
      have hdist : dist T T' = max (|T.slope - T'.slope|) (|T.intercept - T'.intercept|) := by
        have h1 : dist T T' = dist T.toParam T'.toParam := by rfl
        rw [h1]
        have h2 : dist T.toParam T'.toParam = max (|(T.toParam).1 - (T'.toParam).1|) (|(T.toParam).2 - (T'.toParam).2|) := by
          simp [Prod.dist_eq] <;> rfl
        rw [h2]
        have h3 : (T.toParam).1 = T.slope := by simp [DTube.toParam]
        have h4 : (T.toParam).2 = T.intercept := by simp [DTube.toParam]
        have h5 : (T'.toParam).1 = T'.slope := by simp [DTube.toParam]
        have h6 : (T'.toParam).2 = T'.intercept := by simp [DTube.toParam]
        rw [h3, h4, h5, h6]
      rw [hdist]
      exact le_max_right _ _
    have h3 : |T.intercept - T'.intercept| = |(T.b : ℝ) - (T'.b : ℝ)| * δ' := by
      have hintercept : T.intercept - T'.intercept = ((T.b : ℝ) - (T'.b : ℝ)) * DiscretisedFurstenbergEstimate.δ n := by
        simp [DTube.intercept] <;> ring
      rw [hintercept]
      have h4 : ((T.b : ℝ) - (T'.b : ℝ)) * DiscretisedFurstenbergEstimate.δ n = ((T.b : ℝ) - (T'.b : ℝ)) * δ' := by
        rw [hδ_eq.symm] <;> ring
      rw [h4, abs_mul, abs_of_pos hδ_pos] <;> ring
    rw [h3] at h2
    have h4 : |(T.b : ℝ) - (T'.b : ℝ)| * δ' ≥ δ' := by
      have h5 : 0 < δ' := hδ_pos
      nlinarith [h1]
    linarith

/-- For a finite set of dyadic tubes, |S| ≤ 9 * covering_δ(S). -/
lemma separated_covering_lower_dtube {n : ℕ} {δ' : ℝ} (hδ_pos : 0 < δ') (hδ_eq : δ' = DiscretisedFurstenbergEstimate.δ n)
    {S : Finset (DTube n)} :
    (S.card : ENNReal) ≤ 9 * Metric.externalCoveringNumber δ'.toNNReal (S : Set (DTube n)) := by
  have hS_sep : SeparatedAt δ' (S : Set (DTube n)) := dtube_separated hδ_pos hδ_eq
  have h1 : 0 ≤ δ' := by linarith
  have hε : (δ'.toNNReal : ℝ) = δ' := by
    have h2 : (δ'.toNNReal : ℝ) = max δ' 0 := by simp
    rw [h2]; exact max_eq_left h1
  have hS_sep' : SeparatedAt (δ'.toNNReal : ℝ) (S : Set (DTube n)) := by
    rw [hε]; exact hS_sep
  let f_toParam : DTube n → ℝ × ℝ := fun T => DTube.toParam T
  let S' := S.image f_toParam
  have h_inj : Function.Injective f_toParam := by
    intro T1 T2 h
    have hslope : T1.slope = T2.slope := by simpa [f_toParam, DTube.toParam] using congr_arg Prod.fst h
    have hintercept : T1.intercept = T2.intercept := by simpa [f_toParam, DTube.toParam] using congr_arg Prod.snd h
    have ha : T1.a = T2.a := by
      have hδpos : 0 < DiscretisedFurstenbergEstimate.δ n := δ_pos n
      have h_eq : (T1.a : ℝ) * DiscretisedFurstenbergEstimate.δ n = (T2.a : ℝ) * DiscretisedFurstenbergEstimate.δ n := hslope
      have h : (T1.a : ℝ) = (T2.a : ℝ) := mul_right_cancel₀ hδpos.ne' h_eq
      exact_mod_cast h
    have hb : T1.b = T2.b := by
      have hδpos : 0 < DiscretisedFurstenbergEstimate.δ n := δ_pos n
      have h_eq : (T1.b : ℝ) * DiscretisedFurstenbergEstimate.δ n = (T2.b : ℝ) * DiscretisedFurstenbergEstimate.δ n := hintercept
      have h : (T1.b : ℝ) = (T2.b : ℝ) := mul_right_cancel₀ hδpos.ne' h_eq
      exact_mod_cast h
    cases T1; cases T2; simp_all
  have hS'_sep : SeparatedAt δ' (S' : Set (ℝ × ℝ)) := by
    intro x hx y hy hne
    rcases Finset.mem_image.mp hx with ⟨T1, hT1, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨T2, hT2, rfl⟩
    have hT1neT2 : T1 ≠ T2 := by intro h; apply hne; simp [h]
    exact hS_sep hT1 hT2 hT1neT2
  have h_pack : ∀ (c : DTube n), (S.filter (fun t => dist t c ≤ (δ'.toNNReal : ℝ))).card ≤ 9 := by
    intro c
    have h9 : (S.filter (fun t => dist t c ≤ (δ'.toNNReal : ℝ))) =
        (S.filter (fun t => dist t c ≤ δ')) := by congr with t <;> rw [hε]
    rw [h9]
    let B := S.filter (fun t : DTube n => dist t c ≤ δ')
    let B' := S'.filter (fun p : ℝ × ℝ => dist p (f_toParam c) ≤ δ')
    have hB_img : B.image f_toParam = B' := by
      apply Finset.ext
      intro y
      dsimp only [B, B', S']
      simp only [Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨t, ⟨htS, htdist⟩, rfl⟩
        refine ⟨⟨t, htS, rfl⟩, ?_⟩
        have h : dist (f_toParam t) (f_toParam c) = dist t c := by rfl
        rw [h]; exact htdist
      · rintro ⟨⟨t, htS, rfl⟩, hdist⟩
        refine ⟨t, ⟨htS, ?_⟩, rfl⟩
        have h : dist (f_toParam t) (f_toParam c) = dist t c := by rfl
        rw [←h]; exact hdist
    have h_card : B.card = B'.card := by
      rw [← Finset.card_image_of_injective B h_inj, hB_img]
    rw [h_card]
    exact EnergyBoundLemmas.ball_9packing_plane hδ_pos hS'_sep (c := f_toParam c)
  have h_main := EnergyBoundLemmas.packing_cover_bound (ε := δ'.toNNReal) hS_sep' 9 (by norm_num) h_pack
  exact h_main

/-! ### Pair intersection S-set bound -/

/-- Pair intersection S-set bound: |Tp| ≤ C_a·C_T·M·(δ/dist)^s.
    Uses S-set property of a superset Ssup (e.g. Tp p).
    Requires p's x-coordinates in [-1,1]. -/
lemma pair_intersection_sset_bound
    {n : ℕ} {δ s C_T M : ℝ}
    (hδ : δ = DiscretisedFurstenbergEstimate.δ n)
    (hδ_pos : 0 < δ) (hs : 0 < s)
    (hCT_pos : 0 < C_T) (hCT_ge_one : 1 ≤ C_T) (hM_pos : 0 < M)
    {p p' : DSquare n} {Tp Ssup : Finset (DTube n)}
    (hTp_sub : Tp ⊆ Ssup)
    (hSsup_sset : IsFinsetDeltaSSet δ s C_T Ssup)
    (hSsup_card : (Ssup.card : ℝ) ≤ M)
    (hTp_int : ∀ t ∈ Tp, (t.toSet ∩ p.toSet).Nonempty)
    (hTp_slope : ∀ t ∈ Tp, |t.slope| ≤ 1)
    (h_int' : ∀ t ∈ Tp, (t.toSet ∩ p'.toSet).Nonempty)
    (hne : p ≠ p')
    (h_x_bound : ∀ (x : ℝ × ℝ), x ∈ p.toSet → |x.1| ≤ 1)
    (h_bounded : dist p p' ≤ 3) :
    (Tp.card : ℝ) ≤
      (9 : ℝ) * (348 : ℝ)^s * C_T * M * (δ / dist p p')^s := by
  let common := Tp
  by_cases h_empty : common = ∅
  · have h_goal : (Tp.card : ℝ) ≤ (9 : ℝ) * (348 : ℝ)^s * C_T * M * (δ / dist p p')^s := by
      have h_card0 : Tp.card = 0 := by
        simpa [common] using h_empty
      rw [h_card0]
      have h_pos : 0 ≤ (9 : ℝ) * (348 : ℝ)^s * C_T * M * (δ / dist p p')^s := by
        apply mul_nonneg
        · positivity
        · apply Real.rpow_nonneg
          positivity
      exact_mod_cast h_pos
    exact h_goal
  · rcases Finset.nonempty_iff_ne_empty.mpr h_empty with ⟨T0, hT0_in⟩
    have hT0_Tp : T0 ∈ Tp := hT0_in
    have hT0_Ssup : T0 ∈ Ssup := hTp_sub hT0_Tp
    have hT0_p' : (T0.toSet ∩ p'.toSet).Nonempty := h_int' T0 hT0_Tp
    set k : ℕ := Int.natAbs (p.i - p'.i) with hk_def
    by_cases h_k_small : k ≤ 1
    · have h_dist_le_n : dist p p' ≤ 7 * DiscretisedFurstenbergEstimate.δ n := small_k_dist_bound
          (hTp_int T0 hT0_Tp) hT0_p' (hTp_slope T0 hT0_Tp) h_k_small
      have h_dist_le : dist p p' ≤ 7 * δ := by
        have h : dist p p' ≤ 7 * DiscretisedFurstenbergEstimate.δ n := h_dist_le_n
        rw [hδ] at *; exact h
      have h_sep_prop : SeparatedAt (DiscretisedFurstenbergEstimate.δ n) (({p, p'} : Finset (DSquare n)) : Set (DSquare n)) :=
        dsquare_separated (P := ({p, p'} : Finset (DSquare n)))
      have h_sep : DiscretisedFurstenbergEstimate.δ n ≤ dist p p' := h_sep_prop (by simp) (by simp) hne
      have hδ_dist : δ ≤ dist p p' := by
        rw [hδ]; exact h_sep
      have h_pos_dist : 0 < dist p p' := by linarith [hδ_pos]
      have h_main : (common.card : ℝ) ≤ M := by
        have h : common ⊆ Ssup := hTp_sub
        have h' : (common.card : ℝ) ≤ (Ssup.card : ℝ) := by exact_mod_cast Finset.card_le_card h
        linarith [hSsup_card]
      have h_goal : M ≤ (9 : ℝ) * (348 : ℝ)^s * C_T * M * (δ / dist p p')^s := by
        have h1 : δ / dist p p' ≥ 1 / 7 := by
          calc δ / dist p p' ≥ δ / (7 * δ) := by gcongr
          _ = 1 / 7 := by field_simp [hδ_pos.ne'] <;> ring
        have h2 : (δ / dist p p')^s ≥ (1 / 7 : ℝ)^s :=
          Real.rpow_le_rpow (by norm_num) h1 (by linarith)
        have h3 : (9 : ℝ) * (348 : ℝ)^s * C_T * (1 / 7 : ℝ)^s ≥ 1 := by
          have h4 : (9 : ℝ) * (348 : ℝ)^s * C_T * (1 / 7 : ℝ)^s = 9 * C_T * ((348 / 7 : ℝ)^s) := by
            have h5 : (348 : ℝ)^s * (1 / 7 : ℝ)^s = ((348 / 7 : ℝ)^s) := by
              rw [← Real.mul_rpow (by norm_num) (by norm_num)] <;> ring_nf
            calc (9 : ℝ) * (348 : ℝ)^s * C_T * (1 / 7 : ℝ)^s
              = 9 * C_T * ((348 : ℝ)^s * (1 / 7 : ℝ)^s) := by ring
            _ = 9 * C_T * ((348 / 7 : ℝ)^s) := by rw [h5]
          rw [h4]
          have h6 : (348 / 7 : ℝ)^s ≥ 1 := Real.one_le_rpow (by norm_num) (by linarith)
          have h7 : 9 * C_T ≥ 9 := by linarith [hCT_ge_one]
          nlinarith
        have h_pos1 : 0 < (9 : ℝ) * (348 : ℝ)^s * C_T := by positivity
        have h9 : (9 : ℝ) * (348 : ℝ)^s * C_T * (δ / dist p p')^s ≥ 1 := by
          have h10 : (9 : ℝ) * (348 : ℝ)^s * C_T * (δ / dist p p')^s ≥
              (9 : ℝ) * (348 : ℝ)^s * C_T * (1 / 7 : ℝ)^s := by
            gcongr
          linarith [h3, h10]
        have h7 : 0 < M := hM_pos
        have h_goal2 : M ≤ (9 : ℝ) * (348 : ℝ)^s * C_T * M * (δ / dist p p')^s := by
          have h11 : (9 : ℝ) * (348 : ℝ)^s * C_T * (δ / dist p p')^s ≥ 1 := h9
          nlinarith
        exact h_goal2
      exact le_trans h_main h_goal
    · have h_k_ge2 : 2 ≤ k := by omega
      have h_geom1 : ∀ T ∈ common, |T.slope - T0.slope| ≤ 24 / (k : ℝ) := by
        intro T hT
        have hT_Tp : T ∈ Tp := hT
        have hT_p' : (T.toSet ∩ p'.toSet).Nonempty := h_int' T hT_Tp
        have h_k_ne_zero : (p.i : ℝ) - (p'.i : ℝ) ≠ 0 := by
          have h' : (k : ℤ) ≠ 0 := by omega
          have h'' : (p.i - p'.i : ℤ) ≠ 0 := by
            intro h_eq
            have : Int.natAbs (p.i - p'.i) = 0 := by rw [h_eq] <;> simp
            omega
          exact_mod_cast h''
        let ref : ℝ := (p.j - p'.j : ℝ) / (p.i - p'.i : ℝ)
        have h_slope_eq : ref = (p'.j - p.j : ℝ) / (p'.i - p.i : ℝ) := by
          dsimp only [ref]
          have h1 : (p'.i - p.i : ℝ) = -((p.i - p'.i : ℝ)) := by ring
          have h2 : (p'.j - p.j : ℝ) = -((p.j - p'.j : ℝ)) := by ring
          rw [h1, h2]
          have h3 : (-((p.j - p'.j : ℝ))) / (-((p.i - p'.i : ℝ))) = (p.j - p'.j : ℝ) / (p.i - p'.i : ℝ) := by
            rw [neg_div_neg_eq]
          rw [h3]
        have h1 : |T.slope - ref| ≤ 12 / (k : ℝ) := single_slope_bound (hTp_int T hT_Tp) hT_p' (hTp_slope T hT_Tp) h_k_ge2
        have h2_raw := single_slope_bound (hTp_int T0 hT0_Tp) hT0_p' (hTp_slope T0 hT0_Tp) h_k_ge2
        have h2 : |T0.slope - ref| ≤ 12 / (k : ℝ) := by
          exact h2_raw
        have h3 : |T.slope - T0.slope| ≤ |T.slope - ref| + |T0.slope - ref| := by
          calc |T.slope - T0.slope| = |(T.slope - ref) - (T0.slope - ref)| := by ring_nf
            _ ≤ |T.slope - ref| + |T0.slope - ref| := by
              exact abs_sub (T.slope - ref) (T0.slope - ref)
        have h4 : |T.slope - T0.slope| ≤ 24 / (k : ℝ) := by
          calc |T.slope - T0.slope| ≤ |T.slope - ref| + |T0.slope - ref| := h3
            _ ≤ (12 / (k : ℝ)) + (12 / (k : ℝ)) := by gcongr
            _ = 24 / (k : ℝ) := by ring
        exact h4
      have h_ball : ∀ T ∈ common, dist T T0 ≤ 4 * δ + 24 / (k : ℝ) := by
        intro T hT
        have hT_Tp : T ∈ Tp := hT
        have h_slope_diff : |T.slope - T0.slope| ≤ 24 / (k : ℝ) := h_geom1 T hT
        have h_int_diff_n : |T.intercept - T0.intercept| ≤ 4 * DiscretisedFurstenbergEstimate.δ n + |T.slope - T0.slope| :=
          intercept_diff_near_square (hTp_int T hT_Tp) (hTp_int T0 hT0_Tp)
            (hTp_slope T hT_Tp) h_x_bound
        have h_int_diff : |T.intercept - T0.intercept| ≤ 4 * δ + |T.slope - T0.slope| := by
          have h_eq : 4 * DiscretisedFurstenbergEstimate.δ n + |T.slope - T0.slope| = 4 * δ + |T.slope - T0.slope| := by
            rw [hδ] <;> ring
          rw [h_eq] at h_int_diff_n
          exact h_int_diff_n
        have h1 : |T.intercept - T0.intercept| ≤ 4 * δ + 24 / (k : ℝ) := by linarith
        have h_slope_bound : |T.slope - T0.slope| ≤ 4 * δ + 24 / (k : ℝ) := by
          calc |T.slope - T0.slope| ≤ 24 / (k : ℝ) := h_slope_diff
            _ ≤ 4 * δ + 24 / (k : ℝ) := by linarith
        have h_dist_eq : dist T T0 = max (|T.slope - T0.slope|) (|T.intercept - T0.intercept|) := by
          have h1 : dist T T0 = dist T.toParam T0.toParam := by rfl
          rw [h1]
          have h2 : dist T.toParam T0.toParam = max (|(T.toParam).1 - (T0.toParam).1|) (|(T.toParam).2 - (T0.toParam).2|) := by
            simp [Prod.dist_eq] <;> rfl
          rw [h2]
          have h3 : (T.toParam).1 = T.slope := by simp [DTube.toParam]
          have h4 : (T.toParam).2 = T.intercept := by simp [DTube.toParam]
          have h5 : (T0.toParam).1 = T0.slope := by simp [DTube.toParam]
          have h6 : (T0.toParam).2 = T0.intercept := by simp [DTube.toParam]
          rw [h3, h4, h5, h6]
        rw [h_dist_eq]
        exact max_le h_slope_bound h1
      set r : ℝ := 4 * δ + 24 / (k : ℝ) with hr_def
      have hk_pos : 0 < (k : ℝ) := by positivity
      have hr_geδ : δ ≤ r := by
        dsimp only [r]
        have h : 4 * δ + 24 / (k : ℝ) ≥ δ := by
          have h2 : 0 < 24 / (k : ℝ) := by positivity
          linarith
        exact h
      have h_common_sub : common ⊆ Ssup.filter (fun t => dist t T0 ≤ r) := by
        intro T hT
        exact Finset.mem_filter.mpr ⟨hTp_sub hT, h_ball T hT⟩
      have h_pack : (common.card : ENNReal) ≤
          9 * Metric.externalCoveringNumber δ.toNNReal (common : Set (DTube n)) :=
        separated_covering_lower_dtube hδ_pos hδ
      have h_sset := hSsup_sset.2.2.2.2 T0 r hr_geδ
      have h_filter_eq : (Ssup.filter (fun t : DTube n => dist t T0 ≤ r) : Set (DTube n)) =
          (Ssup : Set (DTube n)) ∩ Metric.closedBall T0 r := by
        ext x; simp [Metric.mem_closedBall]
        <;> tauto
      have h_cover : (Metric.externalCoveringNumber δ.toNNReal (common : Set (DTube n)) : ENNReal) ≤
          ENNReal.ofReal C_T * (ENNReal.ofReal r) ^ s * (Ssup.card : ENNReal) := by
        have h1 : (common : Set (DTube n)) ⊆
            (Ssup.filter (fun t => dist t T0 ≤ r) : Set (DTube n)) := by exact_mod_cast h_common_sub
        have h2' : (Metric.externalCoveringNumber δ.toNNReal (common : Set (DTube n)) : ENNReal) ≤
            (Metric.externalCoveringNumber δ.toNNReal ((Ssup.filter (fun t => dist t T0 ≤ r)) : Set (DTube n)) : ENNReal) := by
          exact_mod_cast Metric.externalCoveringNumber_mono_set h1
        have h3' : (Metric.externalCoveringNumber δ.toNNReal (Ssup : Set (DTube n)) : ENNReal) ≤ (Ssup.card : ENNReal) := by
          have h31 : Metric.externalCoveringNumber δ.toNNReal (Ssup : Set (DTube n)) ≤ (Ssup : Set (DTube n)).encard :=
            Metric.externalCoveringNumber_le_encard_self _
          exact_mod_cast h31
        have h4' : (Metric.externalCoveringNumber δ.toNNReal ((Ssup.filter (fun t => dist t T0 ≤ r)) : Set (DTube n)) : ENNReal) ≤
            ENNReal.ofReal C_T * (ENNReal.ofReal r) ^ s * (Metric.externalCoveringNumber δ.toNNReal (Ssup : Set (DTube n)) : ENNReal) := by
          rw [h_filter_eq]
          exact h_sset
        calc _
          ≤ _ := h2'
          _ ≤ _ := h4'
          _ ≤ _ := by gcongr
      have h4 : (common.card : ENNReal) ≤
          9 * (ENNReal.ofReal C_T * (ENNReal.ofReal r) ^ s * (Ssup.card : ENNReal)) := by
        calc (common.card : ENNReal)
          ≤ 9 * Metric.externalCoveringNumber δ.toNNReal (common : Set (DTube n)) := h_pack
        _ ≤ 9 * (ENNReal.ofReal C_T * (ENNReal.ofReal r) ^ s * (Ssup.card : ENNReal)) := by gcongr
      have h_dist_k : dist p p' ≤ 14 * (k : ℝ) * δ := by
        have h_slope : |T0.slope| ≤ 1 := hTp_slope T0 hT0_Tp
        let ref : ℝ := (p.j - p'.j : ℝ) / (p.i - p'.i : ℝ)
        have h1 : |T0.slope - ref| ≤ 12 / (k : ℝ) := single_slope_bound (hTp_int T0 hT0_Tp) hT0_p' h_slope h_k_ge2
        have h2 : |ref| ≤ 13 := by
          have h21 : |ref| ≤ |T0.slope| + |T0.slope - ref| := by
            calc |ref| = |T0.slope - (T0.slope - ref)| := by ring_nf
              _ ≤ |T0.slope| + |T0.slope - ref| := by exact abs_sub T0.slope (T0.slope - ref)
          have h22 : 12 / (k : ℝ) ≤ 12 := by
            have h23 : 1 ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k from by omega)
            have h24 : 0 < (k : ℝ) := by positivity
            have h25 : 1 / (k : ℝ) ≤ 1 := (div_le_one h24).mpr h23
            have h26 : 12 / (k : ℝ) ≤ 12 := by
              calc 12 / (k : ℝ) = 12 * (1 / (k : ℝ)) := by field_simp [h24.ne'] <;> ring
                _ ≤ 12 * 1 := by gcongr
                _ = 12 := by ring
            exact h26
          linarith
        have h_k_ne_zero : (p.i : ℝ) - (p'.i : ℝ) ≠ 0 := by
          have h' : (k : ℤ) ≠ 0 := by omega
          have h'' : (p.i - p'.i : ℤ) ≠ 0 := by
            intro h_eq
            have : Int.natAbs (p.i - p'.i) = 0 := by rw [h_eq] <;> simp
            omega
          exact_mod_cast h''
        have h_k_abs : |(p.i : ℝ) - (p'.i : ℝ)| = (k : ℝ) := by
          have h_eq : |(p.i - p'.i : ℤ)| = ↑(Int.natAbs (p.i - p'.i)) := by rw [Int.abs_eq_natAbs]
          have h' : |(p.i : ℝ) - (p'.i : ℝ)| = |(p.i - p'.i : ℤ)| := by exact_mod_cast rfl
          rw [h', h_eq] <;> norm_cast
        have h3 : |(p.j : ℝ) - (p'.j : ℝ)| ≤ 13 * (k : ℝ) := by
          have h4 : |(p.j - p'.j : ℝ)| = |ref| * |(p.i - p'.i : ℝ)| := by
            dsimp only [ref]
            rw [abs_div] <;> field_simp [h_k_ne_zero] <;> ring
          rw [h4, h_k_abs]
          nlinarith
        have h_dist_form : dist p p' =
            max (|(p.i : ℝ) - (p'.i : ℝ)| * δ) (|(p.j : ℝ) - (p'.j : ℝ)| * δ) := by
          have h_eq1 : dist p p' = dist p.toPoint p'.toPoint := by rfl
          rw [h_eq1]
          have h_eq2 : dist p.toPoint p'.toPoint =
              max (|(p.i : ℝ) * DiscretisedFurstenbergEstimate.δ n - (p'.i : ℝ) * DiscretisedFurstenbergEstimate.δ n|)
                  (|(p.j : ℝ) * DiscretisedFurstenbergEstimate.δ n - (p'.j : ℝ) * DiscretisedFurstenbergEstimate.δ n|) := by
            simp [DSquare.toPoint, Prod.dist_eq] <;> rfl
          rw [h_eq2]
          have h3 : |(p.i : ℝ) * DiscretisedFurstenbergEstimate.δ n - (p'.i : ℝ) * DiscretisedFurstenbergEstimate.δ n| =
              |(p.i : ℝ) - (p'.i : ℝ)| * DiscretisedFurstenbergEstimate.δ n := by
            rw [show (p.i : ℝ) * DiscretisedFurstenbergEstimate.δ n - (p'.i : ℝ) * DiscretisedFurstenbergEstimate.δ n =
                ((p.i : ℝ) - (p'.i : ℝ)) * DiscretisedFurstenbergEstimate.δ n by ring]
            rw [abs_mul, abs_of_pos (δ_pos n)] <;> ring
          have h4 : |(p.j : ℝ) * DiscretisedFurstenbergEstimate.δ n - (p'.j : ℝ) * DiscretisedFurstenbergEstimate.δ n| =
              |(p.j : ℝ) - (p'.j : ℝ)| * DiscretisedFurstenbergEstimate.δ n := by
            rw [show (p.j : ℝ) * DiscretisedFurstenbergEstimate.δ n - (p'.j : ℝ) * DiscretisedFurstenbergEstimate.δ n =
                ((p.j : ℝ) - (p'.j : ℝ)) * DiscretisedFurstenbergEstimate.δ n by ring]
            rw [abs_mul, abs_of_pos (δ_pos n)] <;> ring
          rw [h3, h4]
          have h5 : max (|(p.i : ℝ) - (p'.i : ℝ)| * DiscretisedFurstenbergEstimate.δ n)
                         (|(p.j : ℝ) - (p'.j : ℝ)| * DiscretisedFurstenbergEstimate.δ n) =
              max (|(p.i : ℝ) - (p'.i : ℝ)| * δ) (|(p.j : ℝ) - (p'.j : ℝ)| * δ) := by
            rw [hδ] <;> rfl
          exact h5
        rw [h_dist_form, h_k_abs]
        have h6 : max ((k : ℝ) * δ) (|(p.j : ℝ) - (p'.j : ℝ)| * δ) ≤ 14 * (k : ℝ) * δ := by
          rw [max_le_iff] <;> constructor <;> nlinarith
        exact h6
      have h_r_bound : r ≤ 348 * δ / dist p p' := by
        have h_k_pos : 0 < (k : ℝ) := by positivity
        have h_pos_dist : 0 < dist p p' := dist_pos.mpr hne
        have h1 : 24 / (k : ℝ) ≤ 24 * 14 * δ / dist p p' := by
          have h2 : dist p p' ≤ 14 * (k : ℝ) * δ := h_dist_k
          have h3 : 0 < (k : ℝ) := h_k_pos
          have h4 : 0 < dist p p' := h_pos_dist
          calc 24 / (k : ℝ)
            = (24 * dist p p') / ((k : ℝ) * dist p p') := by field_simp [h3.ne', h4.ne'] <;> ring
          _ ≤ (24 * 14 * δ * (k : ℝ)) / ((k : ℝ) * dist p p') := by
            have h5 : 24 * dist p p' ≤ 24 * (14 * (k : ℝ) * δ) := by gcongr
            have h6 : 24 * (14 * (k : ℝ) * δ) = 24 * 14 * δ * (k : ℝ) := by ring
            rw [h6] at h5
            gcongr
          _ = 24 * 14 * δ / dist p p' := by field_simp [h3.ne', h4.ne'] <;> ring
        have h4 : 4 * δ ≤ 12 * δ / dist p p' := by
          have h5 : dist p p' ≤ 3 := h_bounded
          have h_ineq : 4 * δ * dist p p' ≤ 12 * δ := by nlinarith
          have h_eq : 4 * δ = (4 * δ * dist p p') / dist p p' := by
            field_simp [h_pos_dist.ne'] <;> ring
          rw [h_eq]
          gcongr
        dsimp only [r]
        have h_sum : 4 * δ + 24 / (k : ℝ) ≤ 12 * δ / dist p p' + 336 * δ / dist p p' := by linarith
        have h_final : 12 * δ / dist p p' + 336 * δ / dist p p' = 348 * δ / dist p p' := by ring
        rw [h_final] at h_sum
        exact h_sum
      have h_card_real : (common.card : ℝ) ≤ (9 : ℝ) * C_T * r^s * M := by
        have hr_nonneg : 0 ≤ r := by positivity
        have hs_nonneg : 0 ≤ s := by linarith [hs]
        have h7 : (ENNReal.ofReal r) ^ s = ENNReal.ofReal (r^s) :=
          ENNReal.ofReal_rpow_of_nonneg hr_nonneg hs_nonneg
        rw [h7] at h4
        have hfin : (9 * (ENNReal.ofReal C_T * ENNReal.ofReal (r^s) * (Ssup.card : ENNReal))) ≠ ⊤ := by
          have h1 : (ENNReal.ofReal C_T * ENNReal.ofReal (r^s) * (Ssup.card : ENNReal)) ≠ ⊤ := by
            simp [ENNReal.mul_ne_top, ENNReal.ofReal_ne_top]
          have h9 : (9 : ENNReal) ≠ ⊤ := by simp
          exact ENNReal.mul_ne_top h9 h1
        have h8 : (common.card : ENNReal).toReal ≤
            (9 * (ENNReal.ofReal C_T * ENNReal.ofReal (r^s) * (Ssup.card : ENNReal))).toReal :=
          (ENNReal.toReal_le_toReal (by simp) hfin).mpr h4
        have h9 : (9 * (ENNReal.ofReal C_T * ENNReal.ofReal (r^s) * (Ssup.card : ENNReal))).toReal =
            (9 : ℝ) * C_T * r^s * (Ssup.card : ℝ) := by
          have h10 : (ENNReal.ofReal C_T).toReal = C_T := ENNReal.toReal_ofReal (by linarith)
          have h11 : (ENNReal.ofReal (r^s)).toReal = r^s := ENNReal.toReal_ofReal (by positivity)
          have h12 : ((Ssup.card : ENNReal)).toReal = (Ssup.card : ℝ) := by simp
          simp [h10, h11, h12, ENNReal.toReal_mul] <;> ring
        rw [h9] at h8
        have h13 : (common.card : ℝ) ≤ (9 : ℝ) * C_T * r^s * (Ssup.card : ℝ) := h8
        have h14 : (9 : ℝ) * C_T * r^s * (Ssup.card : ℝ) ≤ (9 : ℝ) * C_T * r^s * M := by
          gcongr <;> linarith [hSsup_card]
        exact le_trans h13 h14
      have h9 : r^s ≤ (348 : ℝ)^s * (δ / dist p p')^s := by
        have h10 : 0 ≤ r := by positivity
        have h11 : r^s ≤ (348 * δ / dist p p')^s := Real.rpow_le_rpow h10 h_r_bound (by linarith [hs])
        have h121 : 348 * δ / dist p p' = (348 : ℝ) * (δ / dist p p') := by ring
        have h_pos1 : 0 ≤ (348 : ℝ) := by norm_num
        have h_pos2 : 0 ≤ δ / dist p p' := by positivity
        have h12 : (348 * δ / dist p p')^s = (348 : ℝ)^s * (δ / dist p p')^s := by
          rw [h121]
          exact Real.mul_rpow h_pos1 h_pos2
        rw [h12] at h11
        exact h11
      have h10 : (9 : ℝ) * C_T * r^s * M ≤ (9 : ℝ) * (348 : ℝ)^s * C_T * M * (δ / dist p p')^s := by
        have h11 : r^s ≤ (348 : ℝ)^s * (δ / dist p p')^s := h9
        have h12 : (9 : ℝ) * C_T * r^s * M ≤
            (9 : ℝ) * C_T * (((348 : ℝ)^s * (δ / dist p p')^s)) * M := by
          have h_pos : 0 ≤ (9 : ℝ) * C_T * M := by positivity
          calc (9 : ℝ) * C_T * r^s * M
            = ((9 : ℝ) * C_T * M) * r^s := by ring
          _ ≤ ((9 : ℝ) * C_T * M) * ((348 : ℝ)^s * (δ / dist p p')^s) :=
            mul_le_mul_of_nonneg_left h11 h_pos
          _ = (9 : ℝ) * C_T * (((348 : ℝ)^s * (δ / dist p p')^s)) * M := by ring
        have h13 : (9 : ℝ) * C_T * (((348 : ℝ)^s * (δ / dist p p')^s)) * M =
            (9 : ℝ) * (348 : ℝ)^s * C_T * M * (δ / dist p p')^s := by ring
        rw [h13] at h12
        exact h12
      exact le_trans h_card_real h10

/-! ========================================================================
   Pair intersection bound (geometric — KEY MISSING PIECE)
   ======================================================================== -/

/-! ### Pair intersection packing bound -/

/-- Pair intersection packing bound: |common| ≤ 3150 / dist. -/
lemma pair_intersection_packing_bound
    {n : ℕ} {δ : ℝ}
    (hδ : δ = DiscretisedFurstenbergEstimate.δ n)
    (hδ_pos : 0 < δ)
    {p p' : DSquare n} {Tp : Finset (DTube n)}
    (hTp_int : ∀ t ∈ Tp, (t.toSet ∩ p.toSet).Nonempty)
    (hTp_slope : ∀ t ∈ Tp, |t.slope| ≤ 1)
    (h_int' : ∀ t ∈ Tp, (t.toSet ∩ p'.toSet).Nonempty)
    (hne : p ≠ p')
    (h_bounded : dist p p' ≤ 3) :
    (Tp.card : ℝ) ≤ (6426 : ℝ) / dist p p' := by
  let common := Tp.filter (fun t => (t.toSet ∩ p'.toSet).Nonempty)
  have h_common_eq : common = Tp := by
    ext t
    simp only [common, Finset.mem_filter, Finset.mem_coe]
    <;> constructor <;> intro h <;> tauto
  by_cases h_empty : common = ∅
  · have hTp_empty : Tp = ∅ := by
      have h : common = Tp := h_common_eq
      rw [h] at h_empty
      exact h_empty
    rw [hTp_empty]
    have h_pos : 0 < dist p p' := dist_pos.mpr hne
    have h_nonneg : 0 ≤ (6426 : ℝ) / dist p p' := by
      apply div_nonneg
      · positivity
      · exact h_pos.le
    simp
    exact h_nonneg
  · rcases Finset.nonempty_iff_ne_empty.mpr h_empty with ⟨T0, hT0_in⟩
    have hT0_Tp : T0 ∈ Tp := (Finset.mem_filter.mp hT0_in).1
    have hT0_p' : (T0.toSet ∩ p'.toSet).Nonempty := (Finset.mem_filter.mp hT0_in).2
    set k : ℕ := Int.natAbs (p.i - p'.i) with hk_def
    by_cases h_k_small : k ≤ 1
    · have h_dist_le_n : dist p p' ≤ 7 * DiscretisedFurstenbergEstimate.δ n := small_k_dist_bound
          (hTp_int T0 hT0_Tp) hT0_p' (hTp_slope T0 hT0_Tp) h_k_small
      have h_dist_le : dist p p' ≤ 7 * δ := by
        simpa [hδ] using h_dist_le_n
      have h_main : (common.card : ℝ) ≤ 27 / δ := by
        have h : common ⊆ Tp := by intro t ht; exact (Finset.mem_filter.mp ht).1
        have h' : common.card ≤ Tp.card := Finset.card_le_card h
        have h''_n : (Tp.card : ℝ) ≤ 27 * (DiscretisedFurstenbergEstimate.δ n)⁻¹ := tubes_per_square_bound
          (fun t ht => hTp_int t ht) (fun t ht => hTp_slope t ht)
        have h'' : (Tp.card : ℝ) ≤ 27 * δ⁻¹ := by
          simpa [hδ] using h''_n
        have h'_real : (common.card : ℝ) ≤ (Tp.card : ℝ) := by exact_mod_cast h'
        have h_eq : 27 * δ⁻¹ = 27 / δ := by ring
        rw [h_eq] at h''
        exact le_trans h'_real h''
      have h_pos_dist : 0 < dist p p' := dist_pos.mpr hne
      have h_goal : 27 / δ ≤ 6426 / dist p p' := by
        have h3 : 27 / δ ≤ 189 / dist p p' := by
          have h4 : 0 < δ := hδ_pos
          have h5 : 0 < dist p p' := h_pos_dist
          have h6 : 27 * dist p p' ≤ 189 * δ := by
            calc 27 * dist p p' ≤ 27 * (7 * δ) := by gcongr
              _ = 189 * δ := by ring
          have h7 : 27 / δ = (27 * dist p p') / (δ * dist p p') := by
            field_simp [h4.ne', h5.ne'] <;> ring
          rw [h7]
          have h8 : (27 * dist p p') / (δ * dist p p') ≤ (189 * δ) / (δ * dist p p') := by gcongr
          have h9 : (189 * δ) / (δ * dist p p') = 189 / dist p p' := by
            field_simp [h4.ne', h5.ne'] <;> ring
          rw [h9] at h8
          exact h8
        have h7 : 189 / dist p p' ≤ 6426 / dist p p' := by
          gcongr <;> norm_num
        exact le_trans h3 h7
      have h_common_card : (common.card : ℝ) = (Tp.card : ℝ) := by
        rw [h_common_eq]
      have h_main2 : (Tp.card : ℝ) ≤ 27 / δ := by
        rw [←h_common_card]
        exact h_main
      exact le_trans h_main2 h_goal
    · have h_k_ge2 : 2 ≤ k := by omega
      have h_geom : ∀ T ∈ common, |T.slope - T0.slope| ≤ 24 / (k : ℝ) := by
        intro T hT
        have hT_Tp : T ∈ Tp := (Finset.mem_filter.mp hT).1
        have hT_p' : (T.toSet ∩ p'.toSet).Nonempty := (Finset.mem_filter.mp hT).2
        let ref : ℝ := (p.j - p'.j : ℝ) / (p.i - p'.i : ℝ)
        have h1 : |T.slope - ref| ≤ 12 / (k : ℝ) := single_slope_bound (hTp_int T hT_Tp) hT_p' (hTp_slope T hT_Tp) h_k_ge2
        have h2_raw := single_slope_bound (hTp_int T0 hT0_Tp) hT0_p' (hTp_slope T0 hT0_Tp) h_k_ge2
        have h2 : |T0.slope - ref| ≤ 12 / (k : ℝ) := by
          exact h2_raw
        have h3 : |T.slope - T0.slope| ≤ |T.slope - ref| + |T0.slope - ref| := by
          calc |T.slope - T0.slope|
            = |(T.slope - ref) + (-(T0.slope - ref))| := by ring_nf
          _ ≤ |T.slope - ref| + |-(T0.slope - ref)| := abs_add_le _ _
          _ = |T.slope - ref| + |T0.slope - ref| := by
            have h7 : |-(T0.slope - ref)| = |T0.slope - ref| := by
              rw [show -(T0.slope - ref) = (-1 : ℝ) * (T0.slope - ref) by ring]
              rw [abs_mul, abs_neg] <;> norm_num
            rw [h7]
        have h_goal : |T.slope - T0.slope| ≤ 24 / (k : ℝ) := by
          calc |T.slope - T0.slope|
            ≤ |T.slope - ref| + |T0.slope - ref| := h3
          _ ≤ 12 / (k : ℝ) + 12 / (k : ℝ) := by gcongr
          _ = 24 / (k : ℝ) := by ring
        exact h_goal
      let slope_set : Finset ℤ := common.image DTube.a
      have h_slope_interval : ∀ a ∈ slope_set, |(a : ℝ) * δ - T0.slope| ≤ 24 / (k : ℝ) := by
        intro a ha
        rcases Finset.mem_image.mp ha with ⟨T, hT, rfl⟩
        have hg := h_geom T hT
        have h_eq : T.slope = (T.a : ℝ) * δ := by
          simp [DTube.slope, hδ] <;> ring
        rw [h_eq] at hg
        exact hg
      have h_slope_card : slope_set.card ≤ 51 / ((k : ℝ) * δ) := by
        have h1 : ∀ a ∈ slope_set, (a : ℝ) * δ ∈ Set.Icc (T0.slope - 24 / (k : ℝ)) (T0.slope + 24 / (k : ℝ)) := by
          intro a ha
          have h2 : |(a : ℝ) * δ - T0.slope| ≤ 24 / (k : ℝ) := h_slope_interval a ha
          have h3 : T0.slope - 24 / (k : ℝ) ≤ (a : ℝ) * δ := by linarith [abs_le.mp h2]
          have h4 : (a : ℝ) * δ ≤ T0.slope + 24 / (k : ℝ) := by linarith [abs_le.mp h2]
          exact ⟨h3, h4⟩
        let lower := (T0.slope - 24 / (k : ℝ)) / δ
        let upper := (T0.slope + 24 / (k : ℝ)) / δ
        have h3 : slope_set ⊆ Finset.Icc ⌈lower⌉ ⌊upper⌋ := by
          intro a ha
          have h4 : (a : ℝ) * δ ∈ Set.Icc (T0.slope - 24 / (k : ℝ)) (T0.slope + 24 / (k : ℝ)) := h1 a ha
          have h5 : lower ≤ (a : ℝ) := by
            have h51 : T0.slope - 24 / (k : ℝ) ≤ (a : ℝ) * δ := h4.1
            have h52 : lower ≤ ((a : ℝ) * δ) / δ := by
              dsimp only [lower]
              exact div_le_div_of_nonneg_right h51 hδ_pos.le
            have h53 : ((a : ℝ) * δ) / δ = (a : ℝ) := by field_simp [hδ_pos.ne'] <;> ring
            rw [h53] at h52
            exact h52
          have h6 : (a : ℝ) ≤ upper := by
            have h61 : (a : ℝ) * δ ≤ T0.slope + 24 / (k : ℝ) := h4.2
            have h62 : (a : ℝ) ≤ ((a : ℝ) * δ) / δ := by
              have h : ((a : ℝ) * δ) / δ = (a : ℝ) := by field_simp [hδ_pos.ne'] <;> ring
              exact le_of_eq h.symm
            have h63 : ((a : ℝ) * δ) / δ ≤ upper := by
              dsimp only [upper]
              exact div_le_div_of_nonneg_right h61 hδ_pos.le
            linarith
          have h7 : ⌈lower⌉ ≤ a := Int.ceil_le.mpr h5
          have h8 : a ≤ ⌊upper⌋ := Int.le_floor.mpr h6
          exact Finset.mem_Icc.mpr ⟨h7, h8⟩
        have h5 : slope_set.card ≤ (Finset.Icc ⌈lower⌉ ⌊upper⌋).card := Finset.card_le_card h3
        have h6 : ((Finset.Icc ⌈lower⌉ ⌊upper⌋).card : ℝ) ≤ 48 / ((k : ℝ) * δ) + 1 := by
          by_cases h_case : ⌈lower⌉ ≤ ⌊upper⌋
          · have h' : ⌈lower⌉ ≤ ⌊upper⌋ + 1 := by linarith
            have h_int : ((Finset.Icc ⌈lower⌉ ⌊upper⌋).card : ℤ) = ⌊upper⌋ + 1 - ⌈lower⌉ :=
              Int.card_Icc_of_le ⌈lower⌉ ⌊upper⌋ h'
            have h_le : ((Finset.Icc ⌈lower⌉ ⌊upper⌋).card : ℝ) ≤ (⌊upper⌋ : ℝ) - (⌈lower⌉ : ℝ) + 1 := by
              have h2 : ((Finset.Icc ⌈lower⌉ ⌊upper⌋).card : ℤ) ≤ ⌊upper⌋ + 1 - ⌈lower⌉ := by
                rw [h_int]
              have h3 : ((Finset.Icc ⌈lower⌉ ⌊upper⌋).card : ℝ) ≤ ((⌊upper⌋ + 1 - ⌈lower⌉ : ℤ) : ℝ) := by
                exact_mod_cast h2
              have h4 : ((⌊upper⌋ + 1 - ⌈lower⌉ : ℤ) : ℝ) = (⌊upper⌋ : ℝ) - (⌈lower⌉ : ℝ) + 1 := by
                simp
                <;> ring
              rw [h4] at h3
              exact h3
            have h8 : (⌊upper⌋ : ℝ) ≤ upper := Int.floor_le upper
            have h9 : (lower : ℝ) ≤ (⌈lower⌉ : ℝ) := Int.le_ceil lower
            have h10 : (⌊upper⌋ : ℝ) - (⌈lower⌉ : ℝ) + 1 ≤ upper - lower + 1 := by linarith
            have h11 : upper - lower + 1 = 48 / ((k : ℝ) * δ) + 1 := by
              dsimp only [upper, lower] <;> ring
            linarith
          · have h_empty : Finset.Icc ⌈lower⌉ ⌊upper⌋ = ∅ := by
              apply Finset.Icc_eq_empty_of_lt
              exact not_le.mp h_case
            rw [h_empty]
            simp only [Finset.card_empty, Nat.cast_zero]
            have h_kpos : 0 < (k : ℝ) := by positivity
            have h_pos : 0 < (k : ℝ) * δ := mul_pos h_kpos hδ_pos
            have h_goal : (0 : ℝ) ≤ 48 / ((k : ℝ) * δ) + 1 := by
              have h4 : 0 ≤ 48 / ((k : ℝ) * δ) := div_nonneg (by norm_num) h_pos.le
              linarith
            exact h_goal
        have h7 : (1 : ℝ) ≤ 3 / ((k : ℝ) * δ) := by
          have h8 : (k : ℝ) * δ ≤ 3 := by
            have h9 : dist p p' ≤ 3 := h_bounded
            have h10 : (k : ℝ) * δ ≤ dist p p' := by
              have h_dist_form : dist p p' = max (|(p.i : ℝ) - (p'.i : ℝ)| * δ) (|(p.j : ℝ) - (p'.j : ℝ)| * δ) := by
                have h_eq1 : dist p p' = dist p.toPoint p'.toPoint := by rfl
                rw [h_eq1]
                have h_eq2 : dist p.toPoint p'.toPoint = max (|(p.i : ℝ) * (DiscretisedFurstenbergEstimate.δ n) - (p'.i : ℝ) * (DiscretisedFurstenbergEstimate.δ n)|)
                    (|(p.j : ℝ) * (DiscretisedFurstenbergEstimate.δ n) - (p'.j : ℝ) * (DiscretisedFurstenbergEstimate.δ n)|) := by
                  simp [DSquare.toPoint, Prod.dist_eq] <;> rfl
                rw [h_eq2]
                have h3 : |(p.i : ℝ) * (DiscretisedFurstenbergEstimate.δ n) - (p'.i : ℝ) * (DiscretisedFurstenbergEstimate.δ n)| =
                    |(p.i : ℝ) - (p'.i : ℝ)| * (DiscretisedFurstenbergEstimate.δ n) := by
                  rw [show (p.i : ℝ) * (DiscretisedFurstenbergEstimate.δ n) - (p'.i : ℝ) * (DiscretisedFurstenbergEstimate.δ n) =
                      ((p.i : ℝ) - (p'.i : ℝ)) * (DiscretisedFurstenbergEstimate.δ n) by ring]
                  rw [abs_mul, abs_of_pos (δ_pos n)] <;> ring
                have h4 : |(p.j : ℝ) * (DiscretisedFurstenbergEstimate.δ n) - (p'.j : ℝ) * (DiscretisedFurstenbergEstimate.δ n)| =
                    |(p.j : ℝ) - (p'.j : ℝ)| * (DiscretisedFurstenbergEstimate.δ n) := by
                  rw [show (p.j : ℝ) * (DiscretisedFurstenbergEstimate.δ n) - (p'.j : ℝ) * (DiscretisedFurstenbergEstimate.δ n) =
                      ((p.j : ℝ) - (p'.j : ℝ)) * (DiscretisedFurstenbergEstimate.δ n) by ring]
                  rw [abs_mul, abs_of_pos (δ_pos n)] <;> ring
                rw [h3, h4]
                have h5 : max (|(p.i : ℝ) - (p'.i : ℝ)| * (DiscretisedFurstenbergEstimate.δ n))
                               (|(p.j : ℝ) - (p'.j : ℝ)| * (DiscretisedFurstenbergEstimate.δ n)) =
                    max (|(p.i : ℝ) - (p'.i : ℝ)| * δ) (|(p.j : ℝ) - (p'.j : ℝ)| * δ) := by
                  rw [hδ] <;> rfl
                exact h5
              rw [h_dist_form]
              have h_k_abs : |(p.i : ℝ) - (p'.i : ℝ)| = (k : ℝ) := by
                have h1 : (p.i : ℝ) - (p'.i : ℝ) = ↑(p.i - p'.i) := by exact_mod_cast rfl
                rw [h1]
                have h2 : |(↑(p.i - p'.i) : ℝ)| ^ 2 = (k : ℝ) ^ 2 := by
                  have h3 : |(↑(p.i - p'.i) : ℝ)| ^ 2 = (↑(p.i - p'.i) : ℝ) ^ 2 := by rw [sq_abs]
                  rw [h3]
                  have h4 : (↑(p.i - p'.i) : ℝ) ^ 2 = ↑((p.i - p'.i).natAbs) ^ 2 := by
                    have h41 : ∀ (z : ℤ), (↑z : ℝ) ^ 2 = (↑(z.natAbs) : ℝ) ^ 2 := by
                      intro z
                      have h_eq : (↑(z.natAbs) : ℝ) = |(↑z : ℝ)| := by
                        have h1 : (↑|z| : ℝ) = |(↑z : ℝ)| := Int.cast_abs (a := z)
                        have h2 : |z| = z.natAbs := Int.abs_eq_natAbs z
                        rw [h2] at h1
                        exact h1
                      have h : (↑z : ℝ) ^ 2 = (|(↑z : ℝ)|) ^ 2 := by rw [sq_abs]
                      rw [h, ← h_eq]
                    exact h41 (p.i - p'.i)
                  rw [h4, hk_def] <;> norm_cast
                have h5 : 0 ≤ |(↑(p.i - p'.i) : ℝ)| := abs_nonneg _
                have h6 : 0 ≤ (k : ℝ) := by positivity
                nlinarith
              rw [h_k_abs]
              exact le_max_left _ _
            linarith
          have h_k_pos : 0 < (k : ℝ) := by positivity
          have h_pos : 0 < (k : ℝ) * δ := by positivity
          exact (one_le_div h_pos).mpr h8
        have h9 : 48 / ((k : ℝ) * δ) + 1 ≤ 51 / ((k : ℝ) * δ) := by
          have h10 : (1 : ℝ) ≤ 3 / ((k : ℝ) * δ) := h7
          have h11 : 48 / ((k : ℝ) * δ) + 1 ≤ 48 / ((k : ℝ) * δ) + 3 / ((k : ℝ) * δ) := by gcongr
          have h12 : 48 / ((k : ℝ) * δ) + 3 / ((k : ℝ) * δ) = 51 / ((k : ℝ) * δ) := by ring
          linarith
        have h5' : (slope_set.card : ℝ) ≤ ((Finset.Icc ⌈lower⌉ ⌊upper⌋).card : ℝ) := by exact_mod_cast h5
        exact le_trans (le_trans h5' h6) h9
      have h_per_slope : ∀ a ∈ slope_set, (common.filter (fun t => t.a = a)).card ≤ 9 := by
        intro a _
        exact tubesSlopes (fun t ht => hTp_int t (Finset.mem_filter.mp ht).1)
          (fun t ht => hTp_slope t (Finset.mem_filter.mp ht).1) a
      have h_sum : common.card ≤ ∑ a ∈ slope_set, (common.filter (fun t => t.a = a)).card := by
        let f : ℤ → Finset (DTube n) := fun a => common.filter (fun t => t.a = a)
        have h_part : common = slope_set.biUnion f := by
          ext T
          simp only [Finset.mem_biUnion, Finset.mem_filter, f]
          constructor
          · intro h
            have hT_in : T ∈ common := h
            have ha : T.a ∈ slope_set := Finset.mem_image.mpr ⟨T, hT_in, rfl⟩
            exact ⟨T.a, ha, hT_in, rfl⟩
          · rintro ⟨a, ha, hT, rfl⟩
            exact hT
        have h_card : (slope_set.biUnion f).card ≤ ∑ a ∈ slope_set, (f a).card :=
          Finset.card_biUnion_le
        have h_sum2 : ∑ a ∈ slope_set, (f a).card = ∑ a ∈ slope_set, (common.filter (fun t => t.a = a)).card := by
          apply Finset.sum_congr rfl
          intro a _
          rfl
        have h1 : common.card = (slope_set.biUnion f).card := by rw [h_part]
        have h2 : (slope_set.biUnion f).card ≤ ∑ a ∈ slope_set, (f a).card := h_card
        have h3 : ∑ a ∈ slope_set, (f a).card = ∑ a ∈ slope_set, (common.filter (fun t => t.a = a)).card := h_sum2
        rw [h1]
        rw [h3] at h2
        exact h2
      have h_common_card : (common.card : ℝ) = (Tp.card : ℝ) := by rw [h_common_eq]
      calc (Tp.card : ℝ)
        = (common.card : ℝ) := by rw [h_common_card]
      _ ≤ ∑ a ∈ slope_set, ((common.filter (fun t => t.a = a)).card : ℝ) := by exact_mod_cast h_sum
      _ ≤ ∑ a ∈ slope_set, (9 : ℝ) := by
        apply Finset.sum_le_sum
        intro a ha
        exact_mod_cast h_per_slope a ha
      _ = 9 * (slope_set.card : ℝ) := by simp [Finset.sum_const] <;> ring
      _ ≤ 9 * (51 / ((k : ℝ) * δ)) := by gcongr
      _ = 459 / ((k : ℝ) * δ) := by ring
      _ ≤ 459 * 14 / dist p p' := by
        have h_dist_k : dist p p' ≤ 14 * (k : ℝ) * δ := by
          have h_slope : |T0.slope| ≤ 1 := hTp_slope T0 hT0_Tp
          let ref : ℝ := (p.j - p'.j : ℝ) / (p.i - p'.i : ℝ)
          have h1 : |T0.slope - ref| ≤ 12 / (k : ℝ) := single_slope_bound (hTp_int T0 hT0_Tp) hT0_p' h_slope h_k_ge2
          have h21 : 12 / (k : ℝ) ≤ 12 := by
            have h22 : 1 ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k from by omega)
            have h23 : 0 < (k : ℝ) := by positivity
            calc 12 / (k : ℝ) ≤ 12 / 1 := by gcongr
              _ = 12 := by norm_num
          have h2 : |ref| ≤ 13 := by
            calc |ref| = |T0.slope - (T0.slope - ref)| := by ring_nf
              _ ≤ |T0.slope| + |T0.slope - ref| := by exact abs_sub _ _
              _ ≤ 1 + 12 / (k : ℝ) := by linarith
              _ ≤ 1 + 12 := by gcongr
              _ = 13 := by norm_num
          have h_k_ne_zero : (p.i : ℝ) - (p'.i : ℝ) ≠ 0 := by
            have h' : (p.i - p'.i : ℤ) ≠ 0 := by omega
            exact_mod_cast h'
          have h_k_abs : |(p.i : ℝ) - (p'.i : ℝ)| = (k : ℝ) := by
            have h_eq1 : |(p.i - p'.i : ℤ)| = ↑(Int.natAbs (p.i - p'.i)) := by
              rw [Int.abs_eq_natAbs]
            have h_eq2 : |(p.i : ℝ) - (p'.i : ℝ)| = |(p.i - p'.i : ℤ)| := by exact_mod_cast rfl
            have h_eq3 : (Int.natAbs (p.i - p'.i) : ℕ) = k := by
              rw [hk_def]
            rw [h_eq2, h_eq1, h_eq3] <;> norm_cast
          have h3 : |(p.j : ℝ) - (p'.j : ℝ)| ≤ 13 * (k : ℝ) := by
            have h4 : |(p.j - p'.j : ℝ)| = |ref| * |(p.i - p'.i : ℝ)| := by
              dsimp only [ref]; rw [abs_div] <;> field_simp [h_k_ne_zero] <;> ring
            rw [h4, h_k_abs]
            have h5 : 0 ≤ (k : ℝ) := by positivity
            have h6 : |ref| * (k : ℝ) ≤ 13 * (k : ℝ) := by
              exact mul_le_mul_of_nonneg_right h2 h5
            exact h6
          have h_dist_form : dist p p' = max (|(p.i : ℝ) - (p'.i : ℝ)| * δ) (|(p.j : ℝ) - (p'.j : ℝ)| * δ) := by
            have h_eq1 : dist p p' = dist p.toPoint p'.toPoint := by rfl
            rw [h_eq1]
            have h_eq2 : dist p.toPoint p'.toPoint = max (|(p.i : ℝ) * (DiscretisedFurstenbergEstimate.δ n) - (p'.i : ℝ) * (DiscretisedFurstenbergEstimate.δ n)|)
                (|(p.j : ℝ) * (DiscretisedFurstenbergEstimate.δ n) - (p'.j : ℝ) * (DiscretisedFurstenbergEstimate.δ n)|) := by
              simp [DSquare.toPoint, Prod.dist_eq] <;> rfl
            rw [h_eq2]
            have h3 : |(p.i : ℝ) * (DiscretisedFurstenbergEstimate.δ n) - (p'.i : ℝ) * (DiscretisedFurstenbergEstimate.δ n)| =
                |(p.i : ℝ) - (p'.i : ℝ)| * (DiscretisedFurstenbergEstimate.δ n) := by
              rw [show (p.i : ℝ) * (DiscretisedFurstenbergEstimate.δ n) - (p'.i : ℝ) * (DiscretisedFurstenbergEstimate.δ n) =
                  ((p.i : ℝ) - (p'.i : ℝ)) * (DiscretisedFurstenbergEstimate.δ n) by ring]
              rw [abs_mul, abs_of_pos (δ_pos n)] <;> ring
            have h4 : |(p.j : ℝ) * (DiscretisedFurstenbergEstimate.δ n) - (p'.j : ℝ) * (DiscretisedFurstenbergEstimate.δ n)| =
                |(p.j : ℝ) - (p'.j : ℝ)| * (DiscretisedFurstenbergEstimate.δ n) := by
              rw [show (p.j : ℝ) * (DiscretisedFurstenbergEstimate.δ n) - (p'.j : ℝ) * (DiscretisedFurstenbergEstimate.δ n) =
                  ((p.j : ℝ) - (p'.j : ℝ)) * (DiscretisedFurstenbergEstimate.δ n) by ring]
              rw [abs_mul, abs_of_pos (δ_pos n)] <;> ring
            rw [h3, h4]
            have h5 : max (|(p.i : ℝ) - (p'.i : ℝ)| * (DiscretisedFurstenbergEstimate.δ n))
                         (|(p.j : ℝ) - (p'.j : ℝ)| * (DiscretisedFurstenbergEstimate.δ n)) =
                max (|(p.i : ℝ) - (p'.i : ℝ)| * δ) (|(p.j : ℝ) - (p'.j : ℝ)| * δ) := by
              rw [hδ] <;> rfl
            exact h5
          rw [h_dist_form, h_k_abs]
          have h6 : max ((k : ℝ) * δ) (|(p.j : ℝ) - (p'.j : ℝ)| * δ) ≤ 14 * (k : ℝ) * δ := by
            rw [max_le_iff] <;> constructor <;> nlinarith
          exact h6
        have h_posdist : 0 < dist p p' := dist_pos.mpr hne
        have h_poskd : 0 < (k : ℝ) * δ := by positivity
        have h_calc1 : 459 / ((k : ℝ) * δ) = (459 * dist p p') / (((k : ℝ) * δ) * dist p p') := by
          field_simp [h_poskd.ne', h_posdist.ne'] <;> ring
        have h_calc2 : (459 * dist p p') / (((k : ℝ) * δ) * dist p p') ≤ (459 * (14 * (k : ℝ) * δ)) / (((k : ℝ) * δ) * dist p p') := by
          gcongr
        have h_calc3 : (459 * (14 * (k : ℝ) * δ)) / (((k : ℝ) * δ) * dist p p') = 459 * 14 / dist p p' := by
          field_simp [h_poskd.ne', h_posdist.ne'] <;> ring
        have h_goal : 459 / ((k : ℝ) * δ) ≤ 459 * 14 / dist p p' := by
          calc 459 / ((k : ℝ) * δ)
            = (459 * dist p p') / (((k : ℝ) * δ) * dist p p') := h_calc1
          _ ≤ (459 * (14 * (k : ℝ) * δ)) / (((k : ℝ) * δ) * dist p p') := h_calc2
          _ = 459 * 14 / dist p p' := h_calc3
        exact h_goal
      _ ≤ (6426 : ℝ) / dist p p' := by
        have h_eq : (459 * 14 : ℝ) = (6426 : ℝ) := by norm_num
        have h : (459 * 14 : ℝ) / dist p p' = (6426 : ℝ) / dist p p' := by
          rw [h_eq]
        exact le_of_eq h

/-! ========================================================================
   Algebraic core with lower-bound cardinality
   ======================================================================== -/

/-- Cauchy-Schwarz incidence core with `|Tp p| ≥ M` (lower bound only).
    Uses monotonicity of x ↦ x²/(x+S) for x > 0. -/
lemma incidence_algebraic_core_lower
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    {P : Finset α} {T : Finset β} {Tp : α → Finset β}
    {M C_pair : ℝ}
    (hM_pos : 0 < M)
    (hC_pair_pos : 0 < C_pair)
    (hP_nonempty : P.Nonempty)
    (hTp_sub : ∀ p ∈ P, Tp p ⊆ T)
    (hTp_card : ∀ p ∈ P, M ≤ (Tp p).card)
    (hS_le : (∑ p ∈ P, ∑ p' ∈ P.erase p, ((Tp p) ∩ (Tp p')).card : ℝ) ≤ C_pair * (P.card : ℝ)^2) :
    (T.card : ℝ) ≥ min ((2 / 3 : ℝ) * M * (P.card : ℝ))
        ((1 / 3 : ℝ) * M^2 / C_pair) := by
  let I : ℝ := M * (P.card : ℝ)
  have hI_pos : 0 < I := mul_pos hM_pos (by exact_mod_cast Finset.card_pos.mpr hP_nonempty)
  let S : ℝ := ∑ p ∈ P, (∑ p' ∈ P.erase p, ((Tp p) ∩ (Tp p')).card : ℝ)
  have hS_nonneg : 0 ≤ S := by
    dsimp only [S]; apply Finset.sum_nonneg; intro p _
    apply Finset.sum_nonneg; intro p' _; exact Nat.cast_nonneg _
  let a : β → ℕ := fun t => (P.filter (fun p => t ∈ Tp p)).card
  let I_actual : ℝ := ∑ t ∈ T, (a t : ℝ)

  have h_sum_actual : I_actual = ∑ p ∈ P, ((Tp p).card : ℝ) := by
    calc I_actual
        = ∑ t ∈ T, ∑ p ∈ P, if t ∈ Tp p then (1 : ℝ) else 0 := by
          apply Finset.sum_congr rfl; intro t _
          simp [a, Finset.sum_ite] <;> ring
      _ = ∑ p ∈ P, ∑ t ∈ T, if t ∈ Tp p then (1 : ℝ) else 0 := by rw [Finset.sum_comm]
      _ = ∑ p ∈ P, ((Tp p).card : ℝ) := by
          apply Finset.sum_congr rfl; intro p _
          rw [Finset.sum_ite]; simp [hTp_sub p ‹_›] <;> ring

  have hI_actual_ge : I_actual ≥ I := by
    have h1 : ∀ p ∈ P, ((Tp p).card : ℝ) ≥ M := by
      intro p hp; exact_mod_cast hTp_card p hp
    have h2 : (∑ p ∈ P, ((Tp p).card : ℝ)) ≥ ∑ p ∈ P, M := by
      apply Finset.sum_le_sum; intro p hp; exact h1 p hp
    have h3 : (∑ p ∈ P, M) = M * (P.card : ℝ) := by
      rw [Finset.sum_const] <;> ring
    rw [h_sum_actual]
    linarith

  have h_sum_aa1 : (∑ t ∈ T, (a t : ℝ) * ((a t : ℝ) - 1)) = S :=
    double_counting_pair_sum (hTp_sub)

  have h_sum_a2 : (∑ t ∈ T, (a t : ℝ)^2) = I_actual + S := by
    have h_main : ∀ t ∈ T, (a t : ℝ)^2 = (a t : ℝ) + (a t : ℝ) * ((a t : ℝ) - 1) := by
      intro t _; ring
    have h1 : (∑ t ∈ T, (a t : ℝ)^2) = ∑ t ∈ T, ((a t : ℝ) + (a t : ℝ) * ((a t : ℝ) - 1)) := by
      apply Finset.sum_congr rfl; intro t ht; exact h_main t ht
    rw [h1]
    have h2 : ∑ t ∈ T, ((a t : ℝ) + (a t : ℝ) * ((a t : ℝ) - 1)) =
        (∑ t ∈ T, (a t : ℝ)) + (∑ t ∈ T, (a t : ℝ) * ((a t : ℝ) - 1)) := by
      rw [Finset.sum_add_distrib]
    rw [h2, h_sum_aa1]
    <;> rfl

  have h_cauchy_raw : (∑ t ∈ T, (a t : ℝ))^2 ≤ (T.card : ℝ) * ∑ t ∈ T, (a t : ℝ)^2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq T (fun t => (a t : ℝ)) (fun _ => (1 : ℝ))
    simpa [Finset.sum_const, mul_comm] using h
  have h_cs : I_actual^2 ≤ (T.card : ℝ) * (I_actual + S) := by
    have h_eq1 : (∑ t ∈ T, (a t : ℝ)) = I_actual := by rfl
    have h_eq2 : (∑ t ∈ T, (a t : ℝ)^2) = I_actual + S := h_sum_a2
    rw [h_eq1, h_eq2] at h_cauchy_raw
    exact h_cauchy_raw

  -- f(x) = x²/(x+S) is increasing for x > 0
  have h_f_mono : I^2 / (I + S) ≤ I_actual^2 / (I_actual + S) := by
    have h_pos1 : 0 < I + S := by linarith
    have h_pos2 : 0 < I_actual + S := by linarith
    have hdiff : 0 ≤ I_actual - I := by linarith
    have hI_nonneg : 0 ≤ I := by linarith
    have hIact_nonneg : 0 ≤ I_actual := by linarith
    have h_pos5 : 0 ≤ I * I_actual + S * (I + I_actual) := by
      have h_pos3 : 0 ≤ I * I_actual := mul_nonneg hI_nonneg hIact_nonneg
      have h_pos4 : 0 ≤ S * (I + I_actual) := by
        have h : 0 ≤ I + I_actual := by linarith
        exact mul_nonneg hS_nonneg h
      exact add_nonneg h_pos3 h_pos4
    have h7 : I^2 * (I_actual + S) ≤ I_actual^2 * (I + S) := by
      have h_alg : I_actual^2 * (I + S) - I^2 * (I_actual + S) =
          (I_actual - I) * (I * I_actual + S * (I + I_actual)) := by ring
      have h6 : 0 ≤ I_actual^2 * (I + S) - I^2 * (I_actual + S) := by
        rw [h_alg]; exact mul_nonneg hdiff h_pos5
      exact le_of_sub_nonneg h6
    have h_denom : 0 < (I + S) * (I_actual + S) := mul_pos h_pos1 h_pos2
    have h_eq1 : I^2 / (I + S) = (I^2 * (I_actual + S)) / ((I + S) * (I_actual + S)) := by
      field_simp [h_pos1.ne', h_pos2.ne'] <;> ring
    have h_eq2 : (I_actual^2 * (I + S)) / ((I + S) * (I_actual + S)) = I_actual^2 / (I_actual + S) := by
      field_simp [h_pos1.ne', h_pos2.ne'] <;> ring
    have h_le : (I^2 * (I_actual + S)) / ((I + S) * (I_actual + S)) ≤
        (I_actual^2 * (I + S)) / ((I + S) * (I_actual + S)) :=
      div_le_div_of_nonneg_right h7 h_denom.le
    rw [h_eq1]
    exact le_trans h_le (le_of_eq h_eq2)

  by_cases h_case : I ≤ 2 * S
  · -- Case 1: I ≤ 2S → |T| ≥ M²/(3·C_pair)
    have hS_pos : 0 < S := by linarith
    have h3_pos : (0 : ℝ) < 3 := by norm_num
    have h3S_pos : 0 < 3 * S := mul_pos h3_pos hS_pos
    have h4 : I^2 / (I + S) ≤ (T.card : ℝ) := by
      have h5 : I_actual^2 / (I_actual + S) ≤ (T.card : ℝ) := by
        have h6 : I_actual^2 ≤ (T.card : ℝ) * (I_actual + S) := h_cs
        have h7 : 0 < I_actual + S := by linarith
        have h8 : I_actual^2 / (I_actual + S) ≤ ((T.card : ℝ) * (I_actual + S)) / (I_actual + S) :=
          div_le_div_of_nonneg_right h6 h7.le
        have h9 : ((T.card : ℝ) * (I_actual + S)) / (I_actual + S) = (T.card : ℝ) := by
          have h10 : (I_actual + S) ≠ 0 := h7.ne'
          field_simp [h10]
          <;> ring
        rw [h9] at h8
        exact h8
      calc I^2 / (I + S) ≤ I_actual^2 / (I_actual + S) := h_f_mono
           _ ≤ (T.card : ℝ) := h5
    have h5 : I + S ≤ 3 * S := by linarith [h_case]
    have hI2_pos : 0 < I^2 := by positivity
    have h_pos1 : 0 < I + S := add_pos hI_pos (by linarith)
    have h_pos2 : 0 < 3 * S := mul_pos (by norm_num) hS_pos
    have h6 : I^2 / (3 * S) ≤ I^2 / (I + S) := by
      rw [div_le_div_iff_of_pos_left hI2_pos h_pos2 h_pos1]
      exact h5
    have h7 : (T.card : ℝ) ≥ I^2 / (3 * S) := by
      calc (T.card : ℝ) ≥ I^2 / (I + S) := h4
           _ ≥ I^2 / (3 * S) := h6
    have hP_card_pos : 0 < (P.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hP_nonempty
    have h8 : 3 * S ≤ 3 * (C_pair * (P.card : ℝ)^2) := by
      have h : S ≤ C_pair * (P.card : ℝ)^2 := hS_le; linarith
    have h9 : M^2 * (P.card : ℝ)^2 / (3 * S) ≥
               M^2 * (P.card : ℝ)^2 / (3 * (C_pair * (P.card : ℝ)^2)) := by
      set a := M^2 * (P.card : ℝ)^2 with ha_def
      set b := 3 * S with hb_def
      set c := 3 * (C_pair * (P.card : ℝ)^2) with hc_def
      have ha_nonneg : 0 ≤ a := by positivity
      have ha_pos : 0 < a := by positivity
      have hb_pos : 0 < b := h3S_pos
      have hc_pos : 0 < c := by positivity
      have hbc : b ≤ c := h8
      have h : a / c ≤ a / b := by
        rw [div_le_div_iff_of_pos_left ha_pos hc_pos hb_pos]
        exact hbc
      exact h
    have h10 : M^2 * (P.card : ℝ)^2 / (3 * (C_pair * (P.card : ℝ)^2)) =
                M^2 / (3 * C_pair) := by
      field_simp [hP_card_pos.ne', hC_pair_pos.ne'] <;> ring
    have h11 : I^2 / (3 * S) ≥ M^2 / (3 * C_pair) := by
      have h12 : I^2 = M^2 * (P.card : ℝ)^2 := by simp [I] <;> ring
      rw [h12]; rw [h10] at h9; exact h9
    have h13 : (T.card : ℝ) ≥ (1 / 3 : ℝ) * M^2 / C_pair := by
      calc (T.card : ℝ) ≥ I^2 / (3 * S) := h7
           _ ≥ M^2 / (3 * C_pair) := h11
           _ = (1 / 3 : ℝ) * M^2 / C_pair := by ring
    exact le_trans (min_le_right _ _) h13
  · -- Case 2: I > 2S → |T| ≥ (2/3)·M·|P|
    have h3 : I_actual + S < (3 / 2 : ℝ) * I_actual := by
      have h4 : I_actual ≥ I := hI_actual_ge
      have h5 : S < I / 2 := by linarith
      nlinarith
    have h4 : (T.card : ℝ) ≥ (2 / 3 : ℝ) * I_actual := by nlinarith
    have h5 : (T.card : ℝ) ≥ (2 / 3 : ℝ) * I := by
      calc (T.card : ℝ) ≥ (2 / 3 : ℝ) * I_actual := h4
           _ ≥ (2 / 3 : ℝ) * I := by gcongr
    have h6 : (T.card : ℝ) ≥ (2 / 3 : ℝ) * M * (P.card : ℝ) := by
      have h7 : (2 / 3 : ℝ) * M * (P.card : ℝ) = (2 / 3 : ℝ) * I := by
        simp [I] <;> ring
      rw [h7]; exact h5
    exact le_trans (min_le_left _ _) h6

/-! ========================================================================
   Uniform Prop 5: final theorem
   ======================================================================== -/

/-- Interpolation algebra: `(C_a * C_T * M * (δ/d)^s)^θ * (C_b/d)^(1-θ)
    = C_int * (C_T * M * δ^s)^θ * d^(-t)`, where `C_int = C_a^θ * C_b^(1-θ)`
    and `t = s*θ + (1-θ)`. -/
lemma pair_interp_rpow_simp
    {C_a C_b C_T M δ d s θ t C_int : ℝ}
    (hCa_pos : 0 < C_a) (hCb_pos : 0 < C_b)
    (hCT_pos : 0 < C_T) (hM_pos : 0 < M)
    (hδ_pos : 0 < δ) (hd_pos : 0 < d)
    (hs_nonneg : 0 ≤ s) (hθ_nonneg : 0 ≤ θ) (hθ_le_one : θ ≤ 1)
    (hCint_def : C_int = C_a^θ * C_b^(1-θ))
    (h3 : s * θ + (1 - θ) = t) :
    (C_a * C_T * M * (δ / d)^s)^θ * (C_b / d)^(1-θ) =
    C_int * (C_T * M * δ^s)^θ * d^(-t) := by
  have h1s_pos : 0 ≤ 1 - θ := by linarith
  have hδd_pos : 0 < δ / d := div_pos hδ_pos hd_pos
  have h_d_neg_s_pos : 0 < d^(-s) := Real.rpow_pos_of_pos hd_pos (-s)
  have h_step1 : (δ / d)^s = δ^s * d^(-s) := by
    have h : (δ / d)^s = δ^s / d^s := Real.div_rpow hδ_pos.le hd_pos.le s
    rw [h]
    have h2 : δ^s / d^s = δ^s * (d^s)⁻¹ := by ring
    rw [h2]
    have h3 : (d^s)⁻¹ = d^(-s) := by
      rw [Real.rpow_neg hd_pos.le] <;> ring
    rw [h3] <;> ring
  set X : ℝ := C_T * M * δ^s with hX_def
  have hX_pos : 0 < X := by positivity
  have h_step2 : (C_a * C_T * M * (δ / d)^s)^θ =
      C_a^θ * X^θ * d^(-s * θ) := by
    rw [h_step1]
    have h4 : C_a * C_T * M * (δ^s * d^(-s)) = C_a * (X * d^(-s)) := by
      simp [hX_def] <;> ring
    rw [h4]
    have h5 : (C_a * (X * d^(-s)))^θ = C_a^θ * (X * d^(-s))^θ :=
      Real.mul_rpow hCa_pos.le (by positivity)
    rw [h5]
    have h6 : (X * d^(-s))^θ = X^θ * (d^(-s))^θ :=
      Real.mul_rpow hX_pos.le h_d_neg_s_pos.le
    rw [h6]
    have h7 : (d^(-s))^θ = d^(-s * θ) := by
      rw [Real.rpow_mul hd_pos.le] <;> ring
    rw [h7] <;> ring
  have h_step3 : (C_b / d)^(1 - θ) = C_b^(1 - θ) * d^(-(1 - θ)) := by
    have h4 : (C_b / d)^(1 - θ) = C_b^(1 - θ) / d^(1 - θ) :=
      Real.div_rpow hCb_pos.le hd_pos.le (1 - θ)
    rw [h4]
    have h5 : C_b^(1 - θ) / d^(1 - θ) = C_b^(1 - θ) * (d^(1 - θ))⁻¹ := by ring
    rw [h5]
    have h6 : (d^(1 - θ))⁻¹ = d^(-(1 - θ)) := by
      rw [Real.rpow_neg hd_pos.le] <;> ring
    rw [h6] <;> ring
  have h_step4 : d^(-s * θ) * d^(-(1 - θ)) = d^(-t) := by
    have h5 : d^(-s * θ + (-(1 - θ))) = d^(-s * θ) * d^(-(1 - θ)) :=
      Real.rpow_add hd_pos (-s * θ) (-(1 - θ))
    have h6 : -s * θ + (-(1 - θ)) = -t := by linarith [h3]
    rw [h6] at h5
    exact h5.symm
  have h_main1 : (C_a * C_T * M * (δ / d)^s)^θ * (C_b / d)^(1 - θ) =
      (C_a^θ * X^θ * d^(-s * θ)) * (C_b^(1 - θ) * d^(-(1 - θ))) := by
    rw [h_step2, h_step3] <;> rfl
  have h_main2 : (C_a^θ * X^θ * d^(-s * θ)) * (C_b^(1 - θ) * d^(-(1 - θ))) =
      (C_a^θ * C_b^(1 - θ)) * X^θ * (d^(-s * θ) * d^(-(1 - θ))) := by ring
  have h_main3 : (C_a^θ * C_b^(1 - θ)) * X^θ * (d^(-s * θ) * d^(-(1 - θ))) =
      (C_a^θ * C_b^(1 - θ)) * X^θ * d^(-t) := by
    rw [h_step4] <;> ring
  have h_main4 : (C_a^θ * C_b^(1 - θ)) * X^θ * d^(-t) =
      C_int * (C_T * M * δ^s)^θ * d^(-t) := by
    have h9 : C_a^θ * C_b^(1 - θ) = C_int := hCint_def.symm
    rw [h9, hX_def] <;> ring
  calc
    (C_a * C_T * M * (δ / d)^s)^θ * (C_b / d)^(1 - θ)
      = (C_a^θ * X^θ * d^(-s * θ)) * (C_b^(1 - θ) * d^(-(1 - θ))) := h_main1
  _ = (C_a^θ * C_b^(1 - θ)) * X^θ * (d^(-s * θ) * d^(-(1 - θ))) := h_main2
  _ = (C_a^θ * C_b^(1 - θ)) * X^θ * d^(-t) := h_main3
  _ = C_int * (C_T * M * δ^s)^θ * d^(-t) := h_main4

/-- Uniform Prop 5 - genuine incidence bound with K independent of δ, C_P, C_T, M.

    K depends only on s,t. Requires P contained in the vertical strip |x| ≤ 1
    and diameter ≤ 3. Uses Cauchy-Schwarz + pair intersection interpolation
    + dyadic energy bound. -/
theorem uniform_prop5
    (s : ℝ) (hs_pos : 0 < s) (hs_lt_one : s < 1) :
    ∃ (K : ℝ), 0 < K ∧
      ∀ (t : ℝ), s ≤ t → t ≤ 1 →
        ∀ {n : ℕ} (C_P C_T M : ℝ),
          0 < C_P → 1 ≤ C_P → 0 < C_T → 1 ≤ C_T → 1 ≤ M → 2 ≤ n →
          ∀ (P : Finset (DSquare n)),
            P.Nonempty →
            IsFinsetDeltaSSet (δ n) t C_P P →
            (∀ (x y : DSquare n), x ∈ P → y ∈ P → dist x y ≤ 3) →
            (∀ p ∈ P, ∀ (x : ℝ × ℝ), x ∈ p.toSet → |x.1| ≤ 1) →
            ∀ (Tp : TubeFamily n),
              (∀ p ∈ P, ∀ T ∈ Tp p, (T.toSet ∩ p.toSet).Nonempty) →
              (∀ p ∈ P, ∀ T ∈ Tp p, |T.slope| ≤ 1) →
              (∀ p ∈ P, IsFinsetDeltaSSet (δ n) s C_T (Tp p)) →
              (∀ p ∈ P, M / 2 < (Tp p).card ∧ (Tp p).card ≤ M) →
              let T := P.biUnion fun p => Tp p
              (T.card : ℝ) ≥ (1 / K) * Real.log (1 / δ n) ^ (-K) *
                (1 / (C_P * C_T)) * M * (δ n) ^ (-s) *
                  (M * (δ n) ^ s) ^ ((t - s) / (1 - s)) := by
  -- Universal constants depending only on s
  set C_a : ℝ := 9 * (348 : ℝ)^s with hCa_def
  set C_b : ℝ := 6426 with hCb_def
  set C_log_min : ℝ := Real.log 4 with hClogmin_def
  have hClogmin_gt_one : 1 < C_log_min := by
    dsimp only [C_log_min]
    have h5 : Real.exp 1 < (4 : ℝ) := by linarith [Real.exp_one_lt_d9]
    have h6 : Real.log (Real.exp 1) < Real.log 4 := Real.log_lt_log (by positivity) h5
    have h7 : Real.log (Real.exp 1) = 1 := Real.log_exp 1
    rw [h7] at h6; exact h6
  have hClogmin_pos : 0 < C_log_min := by linarith
  -- Uniform K (independent of t): use upper bound X_univ ≤ C_b * 80 * 12 + 1
  set K_uniform : ℝ := 4 + Real.log (C_b * 80 * 12 + 1) / Real.log C_log_min with hKuniform_def
  have hK_uniform_pos : 0 < K_uniform := by
    dsimp only [K_uniform]
    have h1 : 1 < C_b * 80 * 12 + 1 := by
      dsimp only [C_b] <;> norm_num
    have h2 : 0 < Real.log (C_b * 80 * 12 + 1) := Real.log_pos h1
    have h3 : 0 < Real.log C_log_min := Real.log_pos hClogmin_gt_one
    have h4 : 0 < Real.log (C_b * 80 * 12 + 1) / Real.log C_log_min := div_pos h2 h3
    linarith
  refine ⟨K_uniform, hK_uniform_pos, ?_⟩
  intro t hst ht_le_one
  -- t-dependent constants
  set θ : ℝ := (1 - t) / (1 - s) with hθ_def
  set α : ℝ := (t - s) / (1 - s) with hα_def
  have h1s : 0 < 1 - s := by linarith
  have h1t : 0 ≤ 1 - t := by linarith [ht_le_one]
  have hθ_nonneg : 0 ≤ θ := by
    dsimp only [θ]
    exact div_nonneg h1t (by linarith)
  have hθ_le_one : θ ≤ 1 := by
    dsimp only [θ]
    have h : (1 - t) / (1 - s) ≤ 1 := by
      rw [div_le_one (by linarith)] <;> linarith
    exact h
  have hα_nonneg : 0 ≤ α := by
    dsimp only [α]
    exact div_nonneg (by linarith) (by linarith)
  have hα_le_one : α ≤ 1 := by
    dsimp only [α]
    have h : (t - s) / (1 - s) ≤ 1 := by
      rw [div_le_one (by linarith)] <;> linarith
    exact h
  have hθ_add_α : θ + α = 1 := by
    dsimp only [θ, α]; field_simp [h1s.ne'] <;> ring
  set C_int : ℝ := C_a^θ * C_b^(1-θ) with hCint_def
  set K_energy : ℝ := 40 * (2 : ℝ)^t with hKe_def
  set X_univ : ℝ := max (C_int * K_energy * 12) ((3 / 2 : ℝ) * 54) + 1 with hX_def
  have hX_gt_one : 1 < X_univ := by
    dsimp only [X_univ]
    have h_pos : 0 < (3 / 2 : ℝ) * 54 := by norm_num
    have h_max : (3 / 2 : ℝ) * 54 ≤ max (C_int * K_energy * 12) ((3 / 2 : ℝ) * 54) := le_max_right _ _
    have h0 : 0 < max (C_int * K_energy * 12) ((3 / 2 : ℝ) * 54) := by linarith
    linarith
  have hX_pos : 0 < X_univ := by linarith [hX_gt_one]
  set K : ℝ := 4 + Real.log X_univ / Real.log C_log_min with hK_def
  have hK_pos : 0 < K := by
    dsimp only [K]
    have h1 : 0 < Real.log X_univ := Real.log_pos hX_gt_one
    have h2 : 0 < Real.log C_log_min := Real.log_pos hClogmin_gt_one
    have h3 : 0 < Real.log X_univ / Real.log C_log_min := div_pos h1 h2
    linarith
  have hK_ge4 : K ≥ 4 := by
    dsimp only [K]
    have hX_ge_one : 1 ≤ X_univ := by linarith [hX_gt_one]
    have hCmin_ge_one : 1 ≤ C_log_min := by linarith [hClogmin_gt_one]
    have h : 0 ≤ Real.log X_univ / Real.log C_log_min := by
      apply div_nonneg
      · exact Real.log_nonneg hX_ge_one
      · exact Real.log_nonneg hCmin_ge_one
    linarith
  have hK_ge_pow : K ≥ (2 : ℝ)^(1 + α) := by
    have h1 : 1 + α ≤ 2 := by linarith [hα_le_one]
    have h2 : (2 : ℝ)^(1 + α) ≤ 4 := by
      have h21 : (2 : ℝ)^(1 + α) ≤ (2 : ℝ)^(2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
      have h22 : (2 : ℝ)^(2 : ℝ) = 4 := by norm_num
      rw [h22] at h21
      exact h21
    have h4 : K ≥ 4 := hK_ge4
    exact le_trans h2 h4
  intro n C_P C_T M hCP hCP_ge_one hCT hCT_ge_one hM h_n_ge_2 P hP_nonempty hP_set hP_diam hP_unit Tp
    hTp_int hTp_slope hTp_set hTp_card
  have hδ_n_le : δ n ≤ 1 / 4 := by
    have h1 : (n : ℤ) ≥ 2 := by
      have h2 : n ≥ 2 := h_n_ge_2
      exact_mod_cast h2
    have h2 : -(n : ℤ) ≤ -2 := by linarith
    have h3 : (2 : ℝ)^(-(n : ℤ)) ≤ (2 : ℝ)^(-2 : ℤ) := by
      gcongr <;> norm_num <;> linarith
    have h4 : (2 : ℝ)^(-2 : ℤ) = 1 / 4 := by norm_num
    rw [h4] at h3
    have h5 : δ n = (2 : ℝ)^(-(n : ℤ)) := by
      simp [δ] <;> rfl
    rw [h5] <;> exact h3
  set δ : ℝ := δ n with hδ_def
  have hδ_pos : 0 < δ := δ_pos n
  have hδ_le : δ ≤ 1 / 4 := by
    rw [hδ_def] <;> exact hδ_n_le
  set N : ℝ := (P.card : ℝ) with hN_def
  have hN_pos : 0 < N := by
    dsimp only [N]; have h : 0 < P.card := Finset.card_pos.mpr hP_nonempty
    exact_mod_cast h
  have hM_pos : 0 < M := by exact lt_of_lt_of_le (by norm_num) hM
  set T : Finset (DTube n) := P.biUnion Tp with hT_def
  set C_log : ℝ := Real.log (1 / δ) with hClog_def
  have hClog_gt_one : 1 < C_log := by
    dsimp only [C_log]
    have h1 : 1 / δ ≥ 4 := by
      have h2 : 0 < δ := hδ_pos
      calc 1 / δ ≥ 1 / (1 / 4) := by gcongr
        _ = 4 := by norm_num
    have h4 : (1 : ℝ) < Real.log 4 := by
      have h5 : Real.exp 1 < (4 : ℝ) := by linarith [Real.exp_one_lt_d9]
      have h6 : Real.log (Real.exp 1) < Real.log 4 := Real.log_lt_log (by positivity) h5
      have h7 : Real.log (Real.exp 1) = 1 := Real.log_exp 1
      rw [h7] at h6; exact h6
    have h3 : Real.log (1 / δ) ≥ Real.log 4 := Real.log_le_log (by positivity) h1
    linarith
  have hClog_pos : 0 < C_log := by linarith
  have hClog_ge_min : C_log ≥ C_log_min := by
    dsimp only [C_log, C_log_min]
    have h1 : 1 / δ ≥ 4 := by
      have h2 : 0 < δ := hδ_pos
      calc 1 / δ ≥ 1 / (1 / 4) := by gcongr
        _ = 4 := by norm_num
    exact Real.log_le_log (by positivity) h1
  have hK_absorb : C_log^K ≥ X_univ * C_log := by
    have h1 : C_log^(K - 1) ≥ X_univ := by
      have h2 : K - 1 = 3 + Real.log X_univ / Real.log C_log_min := by
        dsimp only [K] <;> ring
      rw [h2]
      have h3 : C_log^(3 + Real.log X_univ / Real.log C_log_min) =
          C_log^(Real.log X_univ / Real.log C_log_min) * C_log^(3 : ℝ) := by
        rw [Real.rpow_add hClog_pos] <;> ring
      rw [h3]
      have h4 : C_log^(Real.log X_univ / Real.log C_log_min) ≥ X_univ := by
        have h5 : C_log ≥ C_log_min := hClog_ge_min
        have hX_ge_one2 : 1 ≤ X_univ := by linarith [hX_gt_one]
        have hCmin_ge_one2 : 1 ≤ C_log_min := by linarith [hClogmin_gt_one]
        have h6 : Real.log X_univ / Real.log C_log_min ≥ 0 := by
          apply div_nonneg
          · exact Real.log_nonneg hX_ge_one2
          · exact Real.log_nonneg hCmin_ge_one2
        have h7 : C_log_min ≤ C_log := by linarith
        have h8 : C_log_min^(Real.log X_univ / Real.log C_log_min) ≤ C_log^(Real.log X_univ / Real.log C_log_min) :=
          Real.rpow_le_rpow (by linarith) h7 h6
        have h9 : C_log_min^(Real.log X_univ / Real.log C_log_min) = X_univ := by
          have h10 : 0 < C_log_min := hClogmin_pos
          have h11 : Real.log C_log_min ≠ 0 := by
            have h12 : 0 < Real.log C_log_min := Real.log_pos hClogmin_gt_one
            exact h12.ne'
          have h13 : C_log_min^(Real.log X_univ / Real.log C_log_min) = Real.exp ((Real.log X_univ / Real.log C_log_min) * Real.log C_log_min) := by
            simp [Real.rpow_def_of_pos h10] <;> ring
          rw [h13]
          have h14 : (Real.log X_univ / Real.log C_log_min) * Real.log C_log_min = Real.log X_univ := by
            field_simp [h11] <;> ring
          rw [h14, Real.exp_log hX_pos]
        linarith
      have h9 : C_log^(3 : ℝ) ≥ 1 := by
        have h10 : 1 ≤ C_log := by linarith
        have h11 : C_log^(0 : ℝ) ≤ C_log^(3 : ℝ) := Real.rpow_le_rpow_of_exponent_le h10 (by norm_num)
        have h12 : C_log^(0 : ℝ) = 1 := by simp
        rw [h12] at h11
        exact h11
      nlinarith
    have h10 : C_log^K = C_log^(K - 1) * C_log := by
      have h11 : C_log^K = C_log^((K - 1) + (1 : ℝ)) := by ring_nf
      rw [h11]
      rw [Real.rpow_add hClog_pos]
      have h12 : C_log^(1 : ℝ) = C_log := by simp
      rw [h12] <;> ring
    rw [h10]
    have h12 : 0 < C_log := hClog_pos
    nlinarith
  have hK_absorb2 : C_log^K ≥ C_int * K_energy * 12 * C_log := by
    have h1 : X_univ ≥ C_int * K_energy * 12 := by
      rw [hX_def]
      have h2 : C_int * K_energy * 12 ≤ max (C_int * K_energy * 12) ((3 / 2 : ℝ) * 54) := le_max_left _ _
      linarith
    have h2 : C_log^K ≥ X_univ * C_log := hK_absorb
    have h3 : X_univ * C_log ≥ (C_int * K_energy * 12) * C_log := by gcongr
    calc C_log^K ≥ X_univ * C_log := h2
      _ ≥ (C_int * K_energy * 12) * C_log := h3
      _ = C_int * K_energy * 12 * C_log := by ring
  have hK_absorb3 : C_log^K ≥ (3 / 2 : ℝ) * 54 := by
    have h1 : X_univ ≥ (3 / 2 : ℝ) * 54 := by
      rw [hX_def]
      have h2 : (3 / 2 : ℝ) * 54 ≤ max (C_int * K_energy * 12) ((3 / 2 : ℝ) * 54) := le_max_right _ _
      linarith
    have h2 : C_log^K ≥ X_univ * C_log := hK_absorb
    have h3 : C_log ≥ 1 := by linarith [hClog_gt_one]
    have h4 : X_univ * C_log ≥ X_univ := by
      have h5 : 0 < X_univ := hX_pos
      have h6 : X_univ * C_log ≥ X_univ * 1 := by gcongr
      simpa using h6
    calc C_log^K ≥ X_univ * C_log := h2
      _ ≥ X_univ := h4
      _ ≥ (3 / 2 : ℝ) * 54 := h1
  -- Pair intersection bound (interpolated)
  have h_pair : ∀ (p : DSquare n), p ∈ P → ∀ (p' : DSquare n), p' ∈ P → p ≠ p' →
      ((Tp p) ∩ (Tp p')).card ≤
        C_int * (C_T * M * δ^s)^θ * (dist p p')^(-t) := by
    intro p hp p' hp' hne
    let common := (Tp p) ∩ (Tp p')
    have hA : (common.card : ℝ) ≤ C_a * C_T * M * (δ / dist p p')^s :=
      pair_intersection_sset_bound hδ_def hδ_pos hs_pos hCT hCT_ge_one (by linarith)
        (hTp_sub := by intro t ht; exact (Finset.mem_inter.mp ht).1)
        (hSsup_sset := hTp_set p hp)
        (hSsup_card := by exact_mod_cast (hTp_card p hp).2)
        (hTp_int := fun t ht => hTp_int p hp t (Finset.mem_inter.mp ht).1)
        (hTp_slope := fun t ht => hTp_slope p hp t (Finset.mem_inter.mp ht).1)
        (h_int' := fun t ht => hTp_int p' hp' t (Finset.mem_inter.mp ht).2)
        hne (fun x hx => hP_unit p hp x hx) (hP_diam p p' hp hp')
    have hB : (common.card : ℝ) ≤ C_b / dist p p' :=
      pair_intersection_packing_bound hδ_def hδ_pos
        (fun t ht => hTp_int p hp t (Finset.mem_inter.mp ht).1)
        (fun t ht => hTp_slope p hp t (Finset.mem_inter.mp ht).1)
        (fun t ht => hTp_int p' hp' t (Finset.mem_inter.mp ht).2)
        hne (hP_diam p p' hp hp')
    have hCa_pos : 0 < C_a := by dsimp only [C_a]; positivity
    have h_pos1 : 0 < C_a * C_T * M * (δ / dist p p')^s := by
      have hdist_pos : 0 < dist p p' := dist_pos.mpr hne
      have h1 : 0 < δ / dist p p' := div_pos hδ_pos hdist_pos
      have h2 : 0 < (δ / dist p p')^s := Real.rpow_pos_of_pos h1 s
      positivity
    have h_pos2 : 0 < C_b / dist p p' := by
      have h3 : 0 < dist p p' := dist_pos.mpr hne
      positivity
    have h_interp : (common.card : ℝ) ≤
        (C_a * C_T * M * (δ / dist p p')^s)^θ * (C_b / dist p p')^(1-θ) := by
      have h_min : (common.card : ℝ) ≤ min (C_a * C_T * M * (δ / dist p p')^s) (C_b / dist p p') :=
        le_min hA hB
      have h_geom : min (C_a * C_T * M * (δ / dist p p')^s) (C_b / dist p p') ≤
          (C_a * C_T * M * (δ / dist p p')^s)^θ * (C_b / dist p p')^(1-θ) := by
        set a := C_a * C_T * M * (δ / dist p p')^s with ha_def
        set b := C_b / dist p p' with hb_def
        have ha_pos : 0 < a := h_pos1
        have hb_pos : 0 < b := h_pos2
        by_cases h : a ≤ b
        · -- a ≤ b, so min a b = a
          have hmin : min a b = a := by rw [min_eq_left h]
          rw [hmin]
          have h11 : 0 ≤ 1 - θ := by linarith [hθ_le_one]
          have h12 : a^(1-θ) ≤ b^(1-θ) := Real.rpow_le_rpow ha_pos.le h h11
          have h1 : a^θ * b^(1-θ) ≥ a^θ * a^(1-θ) := by
            have h13 : 0 ≤ a^θ := Real.rpow_nonneg ha_pos.le θ
            exact mul_le_mul_of_nonneg_left h12 h13
          have h2 : a^θ * a^(1-θ) = a := by
            have h3 : a^θ * a^(1-θ) = a^(θ + (1-θ)) := by
              rw [← Real.rpow_add ha_pos] <;> ring
            rw [h3]
            have h4 : θ + (1 - θ) = 1 := by linarith
            rw [h4]
            exact Real.rpow_one a
          linarith
        · -- b < a, so min a b = b
          have h' : b ≤ a := by linarith
          have hmin : min a b = b := by rw [min_eq_right h']
          rw [hmin]
          have h11 : 0 ≤ θ := hθ_nonneg
          have h12 : b^θ ≤ a^θ := Real.rpow_le_rpow hb_pos.le h' h11
          have h1 : a^θ * b^(1-θ) ≥ b^θ * b^(1-θ) := by
            have h13 : 0 ≤ b^(1-θ) := Real.rpow_nonneg hb_pos.le (1-θ)
            exact mul_le_mul_of_nonneg_right h12 h13
          have h2 : b^θ * b^(1-θ) = b := by
            have h3 : b^θ * b^(1-θ) = b^(θ + (1-θ)) := by
              rw [← Real.rpow_add hb_pos] <;> ring
            rw [h3]
            have h4 : θ + (1 - θ) = 1 := by linarith
            rw [h4]
            exact Real.rpow_one b
          linarith
      exact le_trans h_min h_geom
    set d := dist p p' with hd_def
    have hd_pos : 0 < d := dist_pos.mpr hne
    have h3_eq : s * θ + (1 - θ) = t := by
      have hθ_expand : θ = (1 - t) / (1 - s) := by simp [hθ_def]
      rw [hθ_expand]
      have h_pos : 0 < 1 - s := h1s
      have h : s * ((1 - t) / (1 - s)) + (1 - (1 - t) / (1 - s)) = t := by
        have h2 : s * ((1 - t) / (1 - s)) = (s * (1 - t)) / (1 - s) := by ring
        have h3 : 1 - (1 - t) / (1 - s) = ((1 - s) - (1 - t)) / (1 - s) := by
          field_simp [h_pos.ne'] <;> ring
        rw [h2, h3]
        have h4 : (s * (1 - t)) / (1 - s) + ((1 - s) - (1 - t)) / (1 - s) =
            (s * (1 - t) + ((1 - s) - (1 - t))) / (1 - s) := by
          rw [← add_div] <;> ring
        rw [h4]
        have h5 : s * (1 - t) + ((1 - s) - (1 - t)) = t * (1 - s) := by ring
        rw [h5]
        field_simp [h_pos.ne'] <;> ring
      exact h
    have hCa_pos : 0 < C_a := by
      have h : 0 < (9 : ℝ) := by norm_num
      have h2 : 0 < (348 : ℝ)^s := Real.rpow_pos_of_pos (by norm_num) s
      exact mul_pos h h2
    have hCb_pos : 0 < C_b := by dsimp only [C_b]; norm_num
    have hM_pos : 0 < M := by linarith
    have hs_nonneg : 0 ≤ s := by linarith
    have h_simp : (C_a * C_T * M * (δ / d)^s)^θ * (C_b / d)^(1-θ) =
        C_int * (C_T * M * δ^s)^θ * d^(-t) :=
      pair_interp_rpow_simp
        (hCa_pos := hCa_pos) (hCb_pos := hCb_pos)
        (hCT_pos := hCT) (hM_pos := hM_pos)
        (hδ_pos := hδ_pos) (hd_pos := hd_pos)
        (hs_nonneg := hs_nonneg) (hθ_nonneg := hθ_nonneg) (hθ_le_one := hθ_le_one)
        (hCint_def := hCint_def)
        (h3 := h3_eq)
    rw [h_simp] at h_interp
    exact h_interp
  -- Energy bound
  have h_sep : SeparatedAt δ (P : Set (DSquare n)) := dsquare_separated
  set C_growth : ℝ := 9 * C_P with hCgrowth_def
  have hCgrowth_pos : 0 < C_growth := by positivity
  have h_growth : ∀ (x : DSquare n) (r : ℝ), δ ≤ r →
      ((P.filter (fun y => dist x y ≤ r)).card : ℝ) ≤ C_growth * r^t * (P.card : ℝ) := by
    intro x r hr
    have ht_nonneg : 0 ≤ t := (hs_pos.trans_le hst).le
    have h : ((P.filter (fun y => dist x y ≤ r)).card : ℝ) ≤ (9 : ℝ) * C_P * r^t * (P.card : ℝ) :=
      dsquare_ball_growth (p := x) ht_nonneg hCP hP_set hr
    rw [hCgrowth_def]
    exact h
  have hδ_lt_3 : δ < 3 := by linarith [hδ_le]
  have h_energy_raw : ∑ p ∈ P, ∑ q ∈ P.erase p, (dist p q)^(-t) ≤
      C_growth * (2 : ℝ)^t * N^2 * (Real.log (3 / δ) / Real.log 2 + 1) :=
    pairEnergy_annulus_bound hδ_pos (hs_pos.trans_le hst) hCgrowth_pos hδ_lt_3 h_sep h_growth hP_diam
  have h_log_bound : Real.log (3 / δ) / Real.log 2 + 1 ≤ (40 / 9 : ℝ) * Real.log (3 / δ) := by
    have h_log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h_log12_pos : 0 < Real.log 12 := Real.log_pos (by norm_num)
    have h_exp1_lt3 : Real.exp 1 < 3 := Real.exp_one_lt_three
    have h_log2_gt_half : (1 / 2 : ℝ) < Real.log 2 := by
      have h : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
      linarith
    have h_inv_log2_lt2 : 1 / Real.log 2 < 2 := by
      have h5 : 0 < Real.log 2 := h_log2_pos
      have h6 : 1 < 2 * Real.log 2 := by linarith [h_log2_gt_half]
      have h7 : 1 / Real.log 2 < (2 * Real.log 2) / Real.log 2 := by
        apply div_lt_div_of_pos_right h6 h5
      have h8 : (2 * Real.log 2) / Real.log 2 = 2 := by
        field_simp [h5.ne'] <;> ring
      rw [h8] at h7
      exact h7
    have h_log3δ_gt1 : 1 < Real.log (3 / δ) := by
      have h7 : 3 / δ ≥ 12 := by
        have h8 : δ ≤ 1 / 4 := hδ_le
        have h9 : 0 < δ := hδ_pos
        have h10 : 3 / (1 / 4 : ℝ) ≤ 3 / δ := by
          rw [div_le_div_iff_of_pos_left (by norm_num) (by norm_num) hδ_pos]
          exact h8
        have h11 : 3 / (1 / 4 : ℝ) = 12 := by norm_num
        linarith
      have h10 : Real.exp 1 < (12 : ℝ) := by linarith [h_exp1_lt3]
      have h11 : Real.log (3 / δ) ≥ Real.log 12 := Real.log_le_log (by positivity) h7
      have h12 : Real.log 12 > 1 := by
        have h13 : (1.0986122885 : ℝ) < Real.log 3 := Real.log_three_gt_d9
        have h14 : Real.log 3 ≤ Real.log 12 := Real.log_le_log (by norm_num) (by norm_num)
        linarith
      linarith
    have h_main : 1 ≤ Real.log (3 / δ) * ((40 / 9 : ℝ) - 1 / Real.log 2) := by
      have h13 : (40 / 9 : ℝ) - 1 / Real.log 2 > 22 / 9 := by linarith [h_inv_log2_lt2]
      have h14 : Real.log (3 / δ) > 1 := h_log3δ_gt1
      have h15 : Real.log (3 / δ) * ((40 / 9 : ℝ) - 1 / Real.log 2) > (22 / 9 : ℝ) := by
        have h16 : 0 < Real.log (3 / δ) := by linarith [h14]
        have h17 : 0 < (40 / 9 : ℝ) - 1 / Real.log 2 := by linarith
        have h18 : Real.log (3 / δ) * ((40 / 9 : ℝ) - 1 / Real.log 2) > 1 * ((40 / 9 : ℝ) - 1 / Real.log 2) := by
          exact mul_lt_mul_of_pos_right h14 h17
        linarith
      linarith
    have h16 : Real.log (3 / δ) / Real.log 2 + 1 ≤ (40 / 9 : ℝ) * Real.log (3 / δ) := by
      have h17 : 0 < Real.log 2 := h_log2_pos
      have h18 : Real.log (3 / δ) / Real.log 2 + 1 = Real.log (3 / δ) * (1 / Real.log 2) + 1 := by
        field_simp [h17.ne'] <;> ring
      rw [h18]
      linarith
    exact h16
  have h_energy : ∑ p ∈ P, ∑ q ∈ P.erase p, (dist p q)^(-t) ≤
      K_energy * C_P * N^2 * Real.log (3 / δ) := by
    have h6 : C_growth * (2 : ℝ)^t * N^2 * (Real.log (3 / δ) / Real.log 2 + 1) ≤
        K_energy * C_P * N^2 * Real.log (3 / δ) := by
      have h7 : 0 < N := hN_pos
      have h8 : 0 < (2 : ℝ)^t := by positivity
      have h9 : 0 < C_P := hCP
      have h10 : C_growth = 9 * C_P := hCgrowth_def
      have h11 : K_energy = 40 * (2 : ℝ)^t := hKe_def
      rw [h10, h11]
      have h13 : 9 * (Real.log (3 / δ) / Real.log 2 + 1) ≤ 40 * Real.log (3 / δ) := by
        have h14 : 9 * (Real.log (3 / δ) / Real.log 2 + 1) ≤ 9 * ((40 / 9 : ℝ) * Real.log (3 / δ)) := by gcongr
        have h15 : 9 * ((40 / 9 : ℝ) * Real.log (3 / δ)) = 40 * Real.log (3 / δ) := by ring
        linarith
      have h17 : (9 * C_P) * (2 : ℝ)^t * N^2 * (Real.log (3 / δ) / Real.log 2 + 1) =
          C_P * (2 : ℝ)^t * N^2 * (9 * (Real.log (3 / δ) / Real.log 2 + 1)) := by ring
      rw [h17]
      have h18 : C_P * (2 : ℝ)^t * N^2 * (9 * (Real.log (3 / δ) / Real.log 2 + 1)) ≤
          C_P * (2 : ℝ)^t * N^2 * (40 * Real.log (3 / δ)) := by gcongr
      have h19 : C_P * (2 : ℝ)^t * N^2 * (40 * Real.log (3 / δ)) =
          (40 * (2 : ℝ)^t) * C_P * N^2 * Real.log (3 / δ) := by ring
      rw [h19] at h18
      exact h18
    exact le_trans h_energy_raw h6
  have h_log_eq : Real.log (3 / δ) = Real.log 3 + Real.log (1 / δ) := by
    have h : 3 / δ = 3 * (1 / δ) := by ring
    rw [h, Real.log_mul (by norm_num) (by positivity)] <;> ring
  have h_energy2 : ∑ p ∈ P, ∑ q ∈ P.erase p, (dist p q)^(-t) ≤
      K_energy * C_P * N^2 * Real.log (1 / δ) * 2 := by
    rw [h_log_eq] at h_energy
    have h : Real.log 3 + Real.log (1 / δ) ≤ 2 * Real.log (1 / δ) := by
      have h1 : 1 / δ ≥ 4 := by
        have h2 : 0 < δ := hδ_pos
        calc 1 / δ ≥ 1 / (1 / 4) := by gcongr
          _ = 4 := by norm_num
      have h' : Real.log (1 / δ) ≥ Real.log 4 := Real.log_le_log (by positivity) h1
      have h_log3_le_log4 : Real.log 3 ≤ Real.log 4 := Real.log_le_log (by norm_num) (by norm_num)
      have h3 : Real.log 3 ≤ Real.log (1 / δ) := by linarith
      linarith
    have h5 : (∑ p ∈ P, ∑ q ∈ P.erase p, (dist p q)^(-t)) ≤ K_energy * C_P * N^2 * (Real.log 3 + Real.log (1 / δ)) := h_energy
    have h6 : K_energy * C_P * N^2 * (Real.log 3 + Real.log (1 / δ)) ≤ K_energy * C_P * N^2 * (2 * Real.log (1 / δ)) := by gcongr
    have h7 : K_energy * C_P * N^2 * (2 * Real.log (1 / δ)) = K_energy * C_P * N^2 * Real.log (1 / δ) * 2 := by ring
    rw [h7] at h6
    exact le_trans h5 h6
  -- Pair sum bound
  have h_S : (∑ p ∈ P, ∑ q ∈ P.erase p, (((Tp p) ∩ (Tp q)).card : ℝ)) ≤
      C_int * (C_T * M * δ^s)^θ * K_energy * C_P * N^2 * Real.log (1 / δ) * 2 := by
    have h_sum1 : ∑ p ∈ P, ∑ q ∈ P.erase p, (((Tp p) ∩ (Tp q)).card : ℝ) ≤
        ∑ p ∈ P, ∑ q ∈ P.erase p, (C_int * (C_T * M * δ^s)^θ * (dist p q)^(-t)) := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro q hq
      have hq' : q ∈ P := (Finset.mem_erase.mp hq).2
      have hne : p ≠ q := (Finset.mem_erase.mp hq).1.symm
      exact_mod_cast h_pair p hp q hq' hne
    calc ∑ p ∈ P, ∑ q ∈ P.erase p, (((Tp p) ∩ (Tp q)).card : ℝ)
      ≤ ∑ p ∈ P, ∑ q ∈ P.erase p, (C_int * (C_T * M * δ^s)^θ * (dist p q)^(-t)) := h_sum1
    _ = C_int * (C_T * M * δ^s)^θ * (∑ p ∈ P, ∑ q ∈ P.erase p, (dist p q)^(-t)) := by
        rw [Finset.mul_sum] <;> apply Finset.sum_congr rfl <;> intro p _ <;> rw [Finset.mul_sum] <;> ring
    _ ≤ C_int * (C_T * M * δ^s)^θ * (K_energy * C_P * N^2 * Real.log (1 / δ) * 2) := by gcongr
    _ = C_int * (C_T * M * δ^s)^θ * K_energy * C_P * N^2 * Real.log (1 / δ) * 2 := by ring
  set C_pair : ℝ := C_int * K_energy * C_P * (C_T * M * δ^s)^θ * Real.log (1 / δ) * 2 with hCpair_def
  have hCpair_pos : 0 < C_pair := by positivity
  have hS_le : (∑ p ∈ P, ∑ q ∈ P.erase p, (((Tp p) ∩ (Tp q)).card : ℝ)) ≤ C_pair * N^2 := by
    rw [hCpair_def] <;> linarith [h_S]
  -- Thin Tp(p) to lower bound M_low = M/2
  let M_low : ℝ := M / 2
  have hMlow_pos : 0 < M_low := by
    dsimp only [M_low]
    exact half_pos hM_pos
  have hTp_sub : ∀ p ∈ P, Tp p ⊆ T := by
    intro p hp t ht
    exact Finset.mem_biUnion.mpr ⟨p, hp, ht⟩
  have hTp_card_low : ∀ p ∈ P, (Tp p).card ≥ M_low := by
    intro p hp
    have h : M / 2 < (Tp p).card := (hTp_card p hp).1
    exact le_of_lt h
  -- Apply algebraic core with lower bound M_low
  have h_main : (T.card : ℝ) ≥ min ((2 / 3 : ℝ) * M_low * N) ((1 / 3 : ℝ) * M_low^2 / C_pair) :=
    incidence_algebraic_core_lower
      (hM_pos := hMlow_pos) (hC_pair_pos := hCpair_pos) (hP_nonempty := hP_nonempty)
      (hTp_sub := hTp_sub)
      (hTp_card := fun p hp => by exact_mod_cast hTp_card_low p hp)
      (hS_le := hS_le)
  -- Lower bound on N from S-set condition
  have hN_lower : N ≥ (1 / C_P) * δ^(-t) := by
    have h_lb := CombiningTheoremRework.sset_lower_bound hP_set
    have h1 : (Metric.externalCoveringNumber δ.toNNReal (P : Set (DSquare n)) : ENNReal) ≥
        ENNReal.ofReal (1 / (C_P * δ^t)) := h_lb
    have h2 : (Metric.externalCoveringNumber δ.toNNReal (P : Set (DSquare n)) : ENNReal) ≤
        (P.card : ENNReal) := by
      have h21 : Metric.externalCoveringNumber δ.toNNReal (P : Set (DSquare n)) ≤
          (P : Set (DSquare n)).encard :=
        Metric.externalCoveringNumber_le_encard_self _
      have h22 : (P : Set (DSquare n)).encard = P.card := by simp
      rw [h22] at h21
      exact_mod_cast h21
    have h3 : ENNReal.ofReal (1 / (C_P * δ^t)) ≤ (P.card : ENNReal) := le_trans h1 h2
    have h_pos : 0 ≤ 1 / (C_P * δ^t) := by positivity
    have h_pos2 : 0 ≤ (P.card : ℝ) := by positivity
    have h_card_eq : (P.card : ENNReal) = ENNReal.ofReal ((P.card : ℝ)) := by
      simp
    have h3' : ENNReal.ofReal (1 / (C_P * δ^t)) ≤ ENNReal.ofReal ((P.card : ℝ)) := by
      rw [←h_card_eq]; exact h3
    have h4 : (1 / (C_P * δ^t) : ℝ) ≤ (P.card : ℝ) :=
      (ENNReal.ofReal_le_ofReal_iff h_pos2).mp h3'
    have h5 : (1 / C_P) * δ^(-t) = 1 / (C_P * δ^t) := by
      have h6 : δ^(-t) = 1 / δ^t := by
        rw [Real.rpow_neg hδ_pos.le t] <;> field_simp
      rw [h6] <;> field_simp <;> ring
    rw [h5] at *
    exact h4
  -- Upper bound on M_low * δ^s (corrected: δ^s > δ for 0<δ<1, s<1)
  have hM_bound : M_low * δ^s ≤ 54 * δ^(-(1-s)) := by
    let p := Classical.choose hP_nonempty
    have hp : p ∈ P := Classical.choose_spec hP_nonempty
    have h3 : ((Tp p).card : ℝ) ≤ 27 * (1 / δ) := by
      have h31 := tubes_per_square_bound (hTp_int p hp) (hTp_slope p hp)
      have h32 : (DiscretisedFurstenbergEstimate.δ n)⁻¹ = 1 / δ := by
        have h33 : DiscretisedFurstenbergEstimate.δ n = δ := hδ_def.symm
        rw [h33]
        <;> simp
      rw [h32] at h31
      exact h31
    have h4 : (M / 2 : ℝ) < ((Tp p).card : ℝ) := by
      exact_mod_cast (hTp_card p hp).1
    have h5 : M < 54 * (1 / δ) := by linarith
    have h6 : M * δ < 54 := by
      calc M * δ < (54 * (1 / δ)) * δ := by gcongr
        _ = 54 := by field_simp [hδ_pos.ne'] <;> ring
    have h7 : M ≤ 54 / δ := by
      have h71 : M * δ ≤ 54 := le_of_lt h6
      have h72 : M = (M * δ) / δ := by field_simp [hδ_pos.ne'] <;> ring
      rw [h72]; gcongr
    have h8 : M_low ≤ M := by dsimp only [M_low]; linarith [hM_pos]
    have h9 : M_low ≤ 54 / δ := by linarith
    have h10 : M_low * δ^s ≤ (54 / δ) * δ^s := by gcongr
    have h11 : (54 / δ) * δ^s = 54 * δ^(-(1-s)) := by
      have h111 : (54 / δ) * δ^s = 54 * (δ^s / δ) := by ring
      rw [h111]
      have h112 : δ^s / δ = δ^(s - 1) := by
        have h113 : δ^s / δ = δ^s * (1 / δ) := by ring
        rw [h113]
        have h114 : 1 / δ = δ^(-1 : ℝ) := by
          have h115 : δ^(-1 : ℝ) = (δ^(1 : ℝ))⁻¹ := Real.rpow_neg hδ_pos.le (1 : ℝ)
          have h116 : δ^(1 : ℝ) = δ := Real.rpow_one δ
          rw [h116] at h115
          have h117 : δ⁻¹ = 1 / δ := by simp
          rw [h117] at h115
          exact h115.symm
        rw [h114]
        have h115 : δ^s * δ^(-1 : ℝ) = δ^(s + (-1 : ℝ)) := by
          rw [← Real.rpow_add hδ_pos s (-1 : ℝ)]
        rw [h115]
        have h116 : s + (-1 : ℝ) = s - 1 := by ring
        rw [h116]
      rw [h112]
      have h117 : s - 1 = -(1 - s) := by ring
      rw [h117]
    rw [h11] at h10
    exact h10
  -- Desired bound using M_low
  set D_low : ℝ := (1 / (C_P * C_T)) * M_low * δ^(-s) * (M_low * δ^s)^α / C_log^K with hDlow_def
  -- Prove both branches of min are ≥ D_low
  have hA_ge : (2 / 3 : ℝ) * M_low * N ≥ D_low := by
    let A := (2 / 3 : ℝ) * M_low
    have hA_pos : 0 < A := by positivity
    have h1 : A * N ≥ A * ((1 / C_P) * δ^(-t)) :=
      mul_le_mul_of_nonneg_left hN_lower hA_pos.le
    have h1' : (2 / 3 : ℝ) * M_low * N ≥ (2 / 3 : ℝ) * (1 / C_P) * M_low * δ^(-t) := by
      convert h1 using 1 <;> ring
    have h2 : (2 / 3 : ℝ) * (1 / C_P) * M_low * δ^(-t) ≥ D_low := by
      have h3 : δ^(-t) = δ^(-s) * δ^(-(t - s)) := by
        have h4 : -t = -s + (-(t - s)) := by ring
        rw [h4]
        rw [Real.rpow_add hδ_pos (-s) (-(t - s))]
      have h4 : δ^(-(t - s)) ≥ 1 := by
        by_cases h5 : t = s
        · rw [h5]; simp
        · have hne : s ≠ t := by intro h; exact h5 (h.symm)
          have h5' : s < t := lt_of_le_of_ne hst hne
          have h6 : 0 < t - s := by linarith
          have h7 : δ ≤ 1 := by linarith [hδ_le]
          have h8 : δ^(t - s) ≤ 1 := Real.rpow_le_one hδ_pos.le h7 (by linarith)
          have h_pos : 0 < δ^(t - s) := by positivity
          have h10 : δ^(-(t - s)) = (δ^(t - s))⁻¹ := by
            rw [Real.rpow_neg (le_of_lt hδ_pos)]
          rw [h10]
          exact (one_le_inv₀ h_pos).mpr h8
      have h5 : (M_low * δ^s)^α ≤ (54 : ℝ)^α * δ^(-(t-s)) := by
        have h7 : (M_low * δ^s)^α ≤ (54 * δ^(-(1-s)))^α := by
          have h71 : 0 ≤ M_low * δ^s := by positivity
          exact Real.rpow_le_rpow h71 hM_bound hα_nonneg
        have h8 : (54 * δ^(-(1-s)))^α = (54 : ℝ)^α * (δ^(-(1-s)))^α := by
          rw [Real.mul_rpow (by norm_num) (by positivity)]
        rw [h8] at h7
        have h9 : (δ^(-(1-s)))^α = δ^((-(1-s))*α) := by
          rw [← Real.rpow_mul (by positivity)] <;> ring
        rw [h9] at h7
        have h10 : (-(1-s))*α = -(t-s) := by
          dsimp only [α]; field_simp [h1s.ne'] <;> ring
        rw [h10] at h7; exact h7
      have h6 : (2 / 3 : ℝ) * C_log^K ≥ (54 : ℝ)^α := by
        have h7 : (54 : ℝ)^α ≤ 54 := by
          have h8 : 0 ≤ α := hα_nonneg
          have h9 : α ≤ 1 := hα_le_one
          have h10 : (54 : ℝ)^α ≤ (54 : ℝ)^(1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 54 by norm_num) h9
          simpa using h10
        have h10 : (2 / 3 : ℝ) * C_log^K ≥ 54 := by
          have h11 : C_log^K ≥ (3 / 2 : ℝ) * 54 := hK_absorb3
          linarith
        linarith
      have h10 : (2 / 3 : ℝ) * δ^(-(t - s)) ≥ (1 / C_T) * (M_low * δ^s)^α / C_log^K := by
        have h11 : (2 / 3 : ℝ) ≥ (1 / C_T) * (54 : ℝ)^α / C_log^K := by
          have h12 : (2 / 3 : ℝ) * C_T * C_log^K ≥ (54 : ℝ)^α := by
            have h13 : 0 < C_log^K := Real.rpow_pos_of_pos hClog_pos K
            have h14 : (2 / 3 : ℝ) * C_T * C_log^K ≥ (2 / 3 : ℝ) * C_log^K := by
              have h151 : (2 / 3 : ℝ) ≥ 0 := by norm_num
              have h15 : (2 / 3 : ℝ) * C_log^K ≥ 0 := mul_nonneg h151 h13.le
              have h16 : (2 / 3 : ℝ) * C_T * C_log^K = (2 / 3 : ℝ) * C_log^K * C_T := by ring
              rw [h16]
              have h17 : (2 / 3 : ℝ) * C_log^K * C_T ≥ (2 / 3 : ℝ) * C_log^K * (1 : ℝ) :=
                mul_le_mul_of_nonneg_left hCT_ge_one h15
              simpa using h17
            exact le_trans h6 h14
          have h15 : 0 < C_T * C_log^K := mul_pos hCT (Real.rpow_pos_of_pos hClog_pos K)
          calc (2 / 3 : ℝ)
            = ((2 / 3 : ℝ) * C_T * C_log^K) / (C_T * C_log^K) := by field_simp [h15.ne'] <;> ring
          _ ≥ ((54 : ℝ)^α) / (C_T * C_log^K) := by gcongr
          _ = (1 / C_T) * (54 : ℝ)^α / C_log^K := by field_simp [h15.ne'] <;> ring
        have h_pos_dt : 0 < δ^(-(t-s)) := Real.rpow_pos_of_pos hδ_pos (-(t-s))
        have h12 : (1 / C_T) * (M_low * δ^s)^α / C_log^K ≤
            ((1 / C_T) * (54 : ℝ)^α / C_log^K) * δ^(-(t-s)) := by
          have h13 : (M_low * δ^s)^α ≤ (54 : ℝ)^α * δ^(-(t-s)) := h5
          have h14 : (1 / C_T) * (M_low * δ^s)^α / C_log^K ≤
              (1 / C_T) * ((54 : ℝ)^α * δ^(-(t-s))) / C_log^K := by gcongr
          have h15 : (1 / C_T) * ((54 : ℝ)^α * δ^(-(t-s))) / C_log^K =
              ((1 / C_T) * (54 : ℝ)^α / C_log^K) * δ^(-(t-s)) := by ring
          rw [h15] at h14; exact h14
        calc (2 / 3 : ℝ) * δ^(-(t - s))
          ≥ ((1 / C_T) * (54 : ℝ)^α / C_log^K) * δ^(-(t - s)) := by gcongr
        _ ≥ (1 / C_T) * (M_low * δ^s)^α / C_log^K := h12
      have h1CP : 0 < 1 / C_P := div_pos zero_lt_one hCP
      have hMlow : 0 < M_low := hMlow_pos
      have hds : 0 < δ^(-s) := Real.rpow_pos_of_pos hδ_pos (-s)
      have h_pos_factor : 0 ≤ (1 / C_P) * M_low * δ^(-s) :=
        mul_nonneg (mul_nonneg h1CP.le hMlow.le) hds.le
      have h14 : (1 / C_P) * M_low * δ^(-s) * ((2 / 3 : ℝ) * δ^(-(t - s))) ≥
          (1 / C_P) * M_low * δ^(-s) * ((1 / C_T) * (M_low * δ^s)^α / C_log^K) := by
        have h15 : (1 / C_P) * M_low * δ^(-s) * ((2 / 3 : ℝ) * δ^(-(t - s))) =
            ((1 / C_P) * M_low * δ^(-s)) * ((2 / 3 : ℝ) * δ^(-(t - s))) := by ring
        have h16 : (1 / C_P) * M_low * δ^(-s) * ((1 / C_T) * (M_low * δ^s)^α / C_log^K) =
            ((1 / C_P) * M_low * δ^(-s)) * ((1 / C_T) * (M_low * δ^s)^α / C_log^K) := by ring
        rw [h15, h16]
        exact mul_le_mul_of_nonneg_left h10 h_pos_factor
      have h17 : (2 / 3 : ℝ) * (1 / C_P) * M_low * δ^(-t) =
          (1 / C_P) * M_low * δ^(-s) * ((2 / 3 : ℝ) * δ^(-(t - s))) := by
        have h18 : δ^(-t) = δ^(-s) * δ^(-(t - s)) := h3
        rw [h18] <;> ring
      have h19 : (1 / (C_P * C_T)) * M_low * δ^(-s) * (M_low * δ^s)^α / C_log^K =
          (1 / C_P) * M_low * δ^(-s) * ((1 / C_T) * (M_low * δ^s)^α / C_log^K) := by ring
      calc (2 / 3 : ℝ) * (1 / C_P) * M_low * δ^(-t)
        = (1 / C_P) * M_low * δ^(-s) * ((2 / 3 : ℝ) * δ^(-(t - s))) := h17
      _ ≥ (1 / C_P) * M_low * δ^(-s) * ((1 / C_T) * (M_low * δ^s)^α / C_log^K) := h14
      _ = (1 / (C_P * C_T)) * M_low * δ^(-s) * (M_low * δ^s)^α / C_log^K := h19.symm
      _ = D_low := by simp [hDlow_def]
    exact le_trans h2 h1'
  have hB_ge : (1 / 3 : ℝ) * M_low^2 / C_pair ≥ D_low := by
    have hM_eq : M = 2 * M_low := by
      dsimp only [M_low]; ring
    have h1 : M_low^2 / C_pair =
        M_low^(2 - θ) * δ^(-s * θ) / (C_int * K_energy * C_P * C_T^θ * C_log * (2 : ℝ)^(1 + θ)) := by
      rw [hCpair_def]
      have h3 : (C_T * M * δ^s)^θ = C_T^θ * M^θ * δ^(s * θ) := by
        have h31 : (C_T * M * δ^s)^θ = (C_T * M)^θ * (δ^s)^θ := by
          rw [Real.mul_rpow (by positivity) (by positivity)]
        have h32 : (C_T * M)^θ = C_T^θ * M^θ := by
          rw [Real.mul_rpow (by positivity) (by positivity)]
        have h33 : (δ^s)^θ = δ^(s * θ) := by
          rw [← Real.rpow_mul hδ_pos.le] <;> ring
        rw [h31, h32, h33] <;> ring
      rw [h3, hM_eq]
      have h4 : (2 * M_low)^θ = (2 : ℝ)^θ * M_low^θ := by
        rw [Real.mul_rpow (by norm_num) (by positivity)]
      rw [h4]
      have h5 : (2 : ℝ)^θ * (2 : ℝ) = (2 : ℝ)^(1 + θ) := by
        have h6 : (2 : ℝ)^θ * (2 : ℝ)^(1 : ℝ) = (2 : ℝ)^(θ + 1) :=
          (Real.rpow_add (show (0 : ℝ) < 2 by norm_num) θ 1).symm
        have h7 : (2 : ℝ)^(1 : ℝ) = (2 : ℝ) := by simp
        rw [h7] at h6
        have h8 : θ + 1 = 1 + θ := by ring
        rw [h8] at h6
        exact h6
      set D : ℝ := C_int * K_energy * C_P * C_T^θ * C_log with hD
      have h_posD : 0 < D := by positivity
      have h_posMθ : 0 < M_low^θ := Real.rpow_pos_of_pos hMlow_pos θ
      have h_posδθ : 0 < δ^(s * θ) := Real.rpow_pos_of_pos hδ_pos (s * θ)
      have hC_log : Real.log (1 / δ) = C_log := by simp [hClog_def]
      have h_denom : C_int * K_energy * C_P * (C_T^θ * ((2 : ℝ)^θ * M_low^θ) * δ^(s * θ)) * Real.log (1 / δ) * 2 =
          D * (2 : ℝ)^(1 + θ) * M_low^θ * δ^(s * θ) := by
        rw [hC_log]
        have h_rearr : C_int * K_energy * C_P * (C_T^θ * ((2 : ℝ)^θ * M_low^θ) * δ^(s * θ)) * C_log * 2 =
            D * (((2 : ℝ)^θ * (2 : ℝ)) * M_low^θ * δ^(s * θ)) := by ring
        rw [h_rearr, h5] <;> ring
      rw [h_denom]
      have h_eq1 : M_low^2 = M_low^(2 - θ) * M_low^θ := by
        have h : M_low^(2 - θ) * M_low^θ = M_low^((2 - θ) + θ) := by
          rw [← Real.rpow_add hMlow_pos (2 - θ) θ]
        have h2 : (2 - θ) + θ = 2 := by ring
        have h3 : M_low^(2 - θ) * M_low^θ = M_low^(2 : ℝ) := by
          rw [h, h2]
        have h4 : (M_low^2 : ℝ) = M_low^(2 : ℝ) := by simp
        exact h4.trans h3.symm
      have h_eq2 : (δ^(s * θ))⁻¹ = δ^(-s * θ) := by
        rw [← Real.rpow_neg hδ_pos.le] <;> ring_nf
      have h_simp : M_low^2 / (D * (2 : ℝ)^(1 + θ) * M_low^θ * δ^(s * θ)) =
          M_low^(2 - θ) * δ^(-s * θ) / (D * (2 : ℝ)^(1 + θ)) := by
        have h_pos1 : 0 < D * (2 : ℝ)^(1 + θ) * M_low^θ * δ^(s * θ) := by positivity
        rw [h_eq1]
        have h_cancel : (M_low^(2 - θ) * M_low^θ) / (D * (2 : ℝ)^(1 + θ) * M_low^θ * δ^(s * θ)) =
            M_low^(2 - θ) / (D * (2 : ℝ)^(1 + θ) * δ^(s * θ)) := by
          field_simp [h_posMθ.ne'] <;> ring
        rw [h_cancel]
        have h_final2 : M_low^(2 - θ) / (D * (2 : ℝ)^(1 + θ) * δ^(s * θ)) =
            M_low^(2 - θ) * δ^(-s * θ) / (D * (2 : ℝ)^(1 + θ)) := by
          have h3 : δ^(-s * θ) = (δ^(s * θ))⁻¹ := by
            rw [← Real.rpow_neg hδ_pos.le] <;> ring_nf
          rw [h3] <;> field_simp [h_posδθ.ne'] <;> ring
        exact h_final2
      rw [h_simp]
    have h1' : (1 / 3 : ℝ) * M_low^2 / C_pair =
        (1 / 3 : ℝ) * (M_low^(2 - θ) * δ^(-s * θ) / (C_int * K_energy * C_P * C_T^θ * C_log * (2 : ℝ)^(1 + θ))) := by
      have h_eq : (1 / 3 : ℝ) * M_low^2 / C_pair = (1 / 3 : ℝ) * (M_low^2 / C_pair) := by ring
      rw [h_eq, h1]
    rw [h1']
    have h3 : M_low^(2 - θ) * δ^(-s * θ) = M_low * δ^(-s) * (M_low * δ^s)^α := by
      have h4 : 2 - θ = 1 + α := by
        dsimp only [θ, α]; field_simp [h1s.ne'] <;> ring
      have h5 : -s * θ = -s + s * α := by
        dsimp only [θ, α]; field_simp [h1s.ne'] <;> ring
      rw [h4, h5]
      have h6 : M_low^(1 + α) = M_low * M_low^α := by
        have h61 : M_low^(1 + α) = M_low^(1 : ℝ) * M_low^α :=
          Real.rpow_add hMlow_pos (1 : ℝ) α
        rw [h61]
        have h62 : M_low^(1 : ℝ) = M_low := Real.rpow_one M_low
        rw [h62] <;> ring
      have h7 : δ^(-s + s * α) = δ^(-s) * δ^(s * α) := by
        rw [Real.rpow_add hδ_pos (-s) (s * α)]
      have h8 : (M_low * δ^s)^α = M_low^α * δ^(s * α) := by
        have hδs_nonneg : 0 ≤ δ^s := Real.rpow_nonneg hδ_pos.le s
        have h81 : (M_low * δ^s)^α = M_low^α * (δ^s)^α :=
          Real.mul_rpow hMlow_pos.le hδs_nonneg
        have h82 : (δ^s)^α = δ^(s * α) := by
          rw [← Real.rpow_mul hδ_pos.le] <;> ring
        rw [h81, h82]
      calc M_low^(1 + α) * δ^(-s + s * α)
        = (M_low * M_low^α) * (δ^(-s) * δ^(s * α)) := by rw [h6, h7]
      _ = M_low * δ^(-s) * (M_low^α * δ^(s * α)) := by ring
      _ = M_low * δ^(-s) * (M_low * δ^s)^α := by rw [h8]
    rw [h3]
    set X : ℝ := M_low * δ^(-s) * (M_low * δ^s)^α with hX
    set A : ℝ := C_int * K_energy * C_P * C_T^θ * C_log * (2 : ℝ)^(1 + θ) with hA
    set B : ℝ := C_log^K with hB
    set Y : ℝ := (1 / (C_P * C_T)) * X with hY
    have h_posX : 0 < X := by
      have h1 : 0 < M_low := hMlow_pos
      have h2 : 0 < δ^(-s) := Real.rpow_pos_of_pos hδ_pos (-s)
      have h3 : 0 < (M_low * δ^s)^α := Real.rpow_pos_of_pos (by positivity) α
      positivity
    have h_posA : 0 < A := by positivity
    have h_posBK : 0 < B := Real.rpow_pos_of_pos hClog_pos K
    have h_ct_le_one : C_T^(θ - 1) ≤ 1 := by
      have h7 : θ - 1 ≤ 0 := by linarith [hθ_le_one]
      have h8 : C_T^(θ - 1) ≤ C_T^(0 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith [hCT_ge_one]) h7
      have h9 : C_T^(0 : ℝ) = 1 := by simp
      rw [h9] at h8; exact h8
    have h2pow_le_four : (2 : ℝ)^(1 + θ) ≤ 4 := by
      have h7 : 1 + θ ≤ 2 := by linarith [hθ_le_one]
      have h8 : (2 : ℝ)^(1 + θ) ≤ (2 : ℝ)^(2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h7
      have h9 : (2 : ℝ)^(2 : ℝ) = 4 := by norm_num
      rw [h9] at h8; exact h8
    have h_main_ineq : B ≥ 3 * C_int * K_energy * C_T^(θ - 1) * C_log * (2 : ℝ)^(1 + θ) := by
      have h10 : 3 * C_T^(θ - 1) * (2 : ℝ)^(1 + θ) ≤ 12 := by
        have h11 : 3 * C_T^(θ - 1) * (2 : ℝ)^(1 + θ) ≤ 3 * 1 * (2 : ℝ)^(1 + θ) := by gcongr
        have h12 : 3 * 1 * (2 : ℝ)^(1 + θ) ≤ 3 * 1 * 4 := by gcongr
        linarith
      have h15 : 0 < C_int * K_energy * C_log := by positivity
      have h13 : 3 * C_int * K_energy * C_T^(θ - 1) * C_log * (2 : ℝ)^(1 + θ) ≤
          C_int * K_energy * 12 * C_log := by
        calc
          3 * C_int * K_energy * C_T^(θ - 1) * C_log * (2 : ℝ)^(1 + θ)
            = (C_int * K_energy * C_log) * (3 * C_T^(θ - 1) * (2 : ℝ)^(1 + θ)) := by ring
          _ ≤ (C_int * K_energy * C_log) * 12 := by gcongr
          _ = C_int * K_energy * 12 * C_log := by ring
      have h16 : B ≥ C_int * K_energy * 12 * C_log := hK_absorb2
      exact le_trans h13 h16
    have h_ct_mul : C_T * C_T^(θ - 1) = C_T^θ := by
      have h4 : C_T^(1 + (θ - 1)) = C_T^(1 : ℝ) * C_T^(θ - 1) :=
        Real.rpow_add hCT (1 : ℝ) (θ - 1)
      have h5 : 1 + (θ - 1) = θ := by ring
      have h6 : C_T^θ = C_T^(1 : ℝ) * C_T^(θ - 1) := by
        have h7 : C_T^θ = C_T^(1 + (θ - 1)) := by rw [h5]
        rw [h7]
        exact h4
      have h8 : C_T^(1 : ℝ) = C_T := by simp
      have h9 : C_T^θ = C_T * C_T^(θ - 1) := by
        rw [h6, h8] <;> ring
      exact h9.symm
    have h_denom_ineq : (C_P * C_T) * B ≥ 3 * A := by
      have h1 : (C_P * C_T) * B ≥ (C_P * C_T) * (3 * C_int * K_energy * C_T^(θ - 1) * C_log * (2 : ℝ)^(1 + θ)) :=
        mul_le_mul_of_nonneg_left h_main_ineq (by positivity)
      have h2 : (C_P * C_T) * (3 * C_int * K_energy * C_T^(θ - 1) * C_log * (2 : ℝ)^(1 + θ)) =
          3 * C_int * K_energy * C_P * C_T^θ * C_log * (2 : ℝ)^(1 + θ) := by
        calc
          (C_P * C_T) * (3 * C_int * K_energy * C_T^(θ - 1) * C_log * (2 : ℝ)^(1 + θ))
            = 3 * C_int * K_energy * C_P * (C_T * C_T^(θ - 1)) * C_log * (2 : ℝ)^(1 + θ) := by ring
          _ = 3 * C_int * K_energy * C_P * C_T^θ * C_log * (2 : ℝ)^(1 + θ) := by rw [h_ct_mul]
      have h3 : (C_P * C_T) * B ≥ 3 * C_int * K_energy * C_P * C_T^θ * C_log * (2 : ℝ)^(1 + θ) := by
        rw [h2] at h1; exact h1
      have h4 : 3 * A = 3 * C_int * K_energy * C_P * C_T^θ * C_log * (2 : ℝ)^(1 + θ) := by
        simp only [hA] <;> ring
      rw [h4]
      exact h3
    have h8 : (1 / 3 : ℝ) * (X / A) ≥ Y / B := by
      have h2 : (1 / 3 : ℝ) * (X / A) = X / (3 * A) := by ring
      have h3 : Y / B = X / ((C_P * C_T) * B) := by
        simp only [hY] <;> field_simp [h_posBK.ne'] <;> ring
      rw [h2, h3]
      exact div_le_div_of_nonneg_left h_posX.le (by positivity) h_denom_ineq
    have hYB : Y / B = D_low := by
      simp only [hY, hB, hX, hDlow_def] <;> ring
    rw [hYB] at h8
    exact h8
  have h_min_ge : min ((2 / 3 : ℝ) * M_low * N) ((1 / 3 : ℝ) * M_low^2 / C_pair) ≥ D_low := by
    exact le_min hA_ge hB_ge
  have h_goal : (T.card : ℝ) ≥ D_low := le_trans h_min_ge h_main
  -- Convert from M_low = M/2 to M, and add 1/K factor
  have h_final : (T.card : ℝ) ≥ (1 / K) * C_log^(-K) * (1 / (C_P * C_T)) * M * δ^(-s) * (M * δ^s)^α := by
    have h2pos : (0 : ℝ) ≤ 2 := by norm_num
    have h2pos' : (0 : ℝ) < 2 := by norm_num
    have h5 : (1 / 2 : ℝ)^α = (2 : ℝ)^(-α) := by
      have h1 : (1 / 2 : ℝ) = (2 : ℝ)^(-1 : ℝ) := by
        rw [Real.rpow_neg_one] <;> norm_num
      rw [h1]
      rw [← Real.rpow_mul (by norm_num)]
      have h2 : (-1 : ℝ) * α = -α := by ring
      rw [h2]
    have hM2 : (M / 2 : ℝ) = (2 : ℝ)^(-1 : ℝ) * M := by
      have h4 : (2 : ℝ)^(-1 : ℝ) = 1 / 2 := by
        have h5 : (2 : ℝ)^(-1 : ℝ) = ((2 : ℝ)^(1 : ℝ))⁻¹ := Real.rpow_neg (by norm_num) (1 : ℝ)
        rw [h5] <;> norm_num
      rw [h4] <;> ring
    have h2pow : ((M / 2) * δ^s)^α = (2 : ℝ)^(-α) * (M * δ^s)^α := by
      have h_pos1 : 0 < (1 / 2 : ℝ) := by norm_num
      have h_pos2 : 0 < M * δ^s := by positivity
      have h_eq : ((M / 2) * δ^s)^α = ((1 / 2 : ℝ) * (M * δ^s))^α := by
        congr 1 <;> ring
      rw [h_eq]
      have h4 : ((1 / 2 : ℝ) * (M * δ^s))^α = (1 / 2 : ℝ)^α * (M * δ^s)^α := by
        rw [Real.mul_rpow (by positivity) (by positivity)]
      rw [h4, h5] <;> ring
    have h3add : (2 : ℝ)^(-1 : ℝ) * (2 : ℝ)^(-α) = (2 : ℝ)^(-(1 + α)) := by
      have h4 : (2 : ℝ)^((-1 : ℝ) + (-α)) = (2 : ℝ)^(-1 : ℝ) * (2 : ℝ)^(-α) :=
        Real.rpow_add (by norm_num) (-1 : ℝ) (-α)
      have h5 : (-1 : ℝ) + (-α) = -(1 + α) := by ring
      rw [h5] at h4
      exact h4.symm
    have h1 : D_low = (2 : ℝ)^(-(1 + α)) * (1 / (C_P * C_T)) * M * δ^(-s) * (M * δ^s)^α / C_log^K := by
      dsimp only [D_low, M_low]
      have h_step1 : (M / 2) * ((M / 2) * δ^s)^α =
          ((2 : ℝ)^(-1 : ℝ) * M) * ((2 : ℝ)^(-α) * (M * δ^s)^α) := by
        rw [h2pow, hM2]
      have h_step2 : ((2 : ℝ)^(-1 : ℝ) * M) * ((2 : ℝ)^(-α) * (M * δ^s)^α) =
          (2 : ℝ)^(-(1 + α)) * M * (M * δ^s)^α := by
        calc
          ((2 : ℝ)^(-1 : ℝ) * M) * ((2 : ℝ)^(-α) * (M * δ^s)^α)
            = (2 : ℝ)^(-1 : ℝ) * (2 : ℝ)^(-α) * M * (M * δ^s)^α := by ring
          _ = (2 : ℝ)^(-(1 + α)) * M * (M * δ^s)^α := by rw [h3add]
      have h_inner : (M / 2) * ((M / 2) * δ^s)^α =
          (2 : ℝ)^(-(1 + α)) * M * (M * δ^s)^α := by
        rw [h_step1, h_step2]
      have h_outer : (1 / (C_P * C_T)) * (M / 2) * δ^(-s) * ((M / 2) * δ^s)^α / C_log^K =
          (1 / (C_P * C_T)) * ((M / 2) * ((M / 2) * δ^s)^α) * δ^(-s) / C_log^K := by ring
      rw [h_outer, h_inner] <;> ring
    rw [h1] at h_goal
    have h6 : (2 : ℝ)^(-(1 + α)) ≥ 1 / K := by
      have h7 : K ≥ (2 : ℝ)^(1 + α) := hK_ge_pow
      have h8 : 0 < (2 : ℝ)^(1 + α) := by positivity
      have h9 : (2 : ℝ)^(-(1 + α)) = 1 / (2 : ℝ)^(1 + α) := by
        have h10 : (2 : ℝ)^(-(1 + α)) = ((2 : ℝ)^(1 + α))⁻¹ := Real.rpow_neg (by norm_num) (1 + α)
        rw [h10] <;> field_simp
      rw [h9]
      exact one_div_le_one_div_of_le h8 h7
    have h10 : C_log^(-K) = 1 / C_log^K := by
      rw [Real.rpow_neg hClog_pos.le K] <;> field_simp
    have h11 : (1 / K) * (1 / (C_P * C_T)) * M * δ^(-s) * (M * δ^s)^α / C_log^K =
        (1 / K) * C_log^(-K) * (1 / (C_P * C_T)) * M * δ^(-s) * (M * δ^s)^α := by
      set A : ℝ := (1 / K) * (1 / (C_P * C_T)) * M * δ^(-s) * (M * δ^s)^α with hA
      have h14 : A / C_log^K = A * (1 / C_log^K) := by ring
      have h15 : A * (1 / C_log^K) = A * C_log^(-K) := by
        rw [h10.symm]
      rw [h14, h15]
      <;> simp only [hA] <;> ring
    have h_final_ineq : (2 : ℝ)^(-(1 + α)) * (1 / (C_P * C_T)) * M * δ^(-s) * (M * δ^s)^α / C_log^K ≥
        (1 / K) * (1 / (C_P * C_T)) * M * δ^(-s) * (M * δ^s)^α / C_log^K := by
      set A : ℝ := (1 / (C_P * C_T)) * M * δ^(-s) * (M * δ^s)^α with hA
      have hA_pos : 0 < A := by positivity
      have hClogK_pos : 0 < C_log^K := by positivity
      have h6le : (1 / K) ≤ (2 : ℝ)^(-(1 + α)) := h6
      have h_mul : (1 / K) * A ≤ (2 : ℝ)^(-(1 + α)) * A :=
        mul_le_mul_of_nonneg_right h6le hA_pos.le
      have h_div : ((1 / K) * A) / C_log^K ≤ ((2 : ℝ)^(-(1 + α)) * A) / C_log^K :=
        div_le_div_of_nonneg_right h_mul hClogK_pos.le
      have h_goal_lhs : ((2 : ℝ)^(-(1 + α)) * A) / C_log^K =
          (2 : ℝ)^(-(1 + α)) * (1 / (C_P * C_T)) * M * δ^(-s) * (M * δ^s)^α / C_log^K := by
        rw [hA]
        rw [←mul_assoc, ←mul_assoc, ←mul_assoc]
        <;> rfl
      have h_goal_rhs : ((1 / K) * A) / C_log^K =
          (1 / K) * (1 / (C_P * C_T)) * M * δ^(-s) * (M * δ^s)^α / C_log^K := by
        rw [hA]
        rw [←mul_assoc, ←mul_assoc, ←mul_assoc]
        <;> rfl
      rw [h_goal_rhs, h_goal_lhs] at h_div
      exact h_div
    calc (T.card : ℝ)
      ≥ (2 : ℝ)^(-(1 + α)) * (1 / (C_P * C_T)) * M * δ^(-s) * (M * δ^s)^α / C_log^K := h_goal
    _ ≥ (1 / K) * (1 / (C_P * C_T)) * M * δ^(-s) * (M * δ^s)^α / C_log^K := h_final_ineq
    _ = (1 / K) * C_log^(-K) * (1 / (C_P * C_T)) * M * δ^(-s) * (M * δ^s)^α := h11
  -- Prove K ≤ K_uniform using uniform bounds on C_int and K_energy
  have hCa_lt_Cb : C_a < C_b := by
    dsimp only [C_a, C_b]
    have h1 : (348 : ℝ)^s < (348 : ℝ)^(1 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hs_lt_one
    have h2 : (348 : ℝ)^s < 348 := by simpa using h1
    have h3 : (9 : ℝ) * (348 : ℝ)^s < 9 * 348 := by gcongr
    have h4 : (9 : ℝ) * 348 < 6426 := by norm_num
    have h5 : (9 : ℝ) * (348 : ℝ)^s < 6426 := by linarith
    exact h5
  have hC_int_le : C_int ≤ C_b := by
    dsimp only [C_int]
    have h1 : C_a^θ ≤ C_b^θ := Real.rpow_le_rpow (by positivity) hCa_lt_Cb.le hθ_nonneg
    have h2 : C_a^θ * C_b^(1-θ) ≤ C_b^θ * C_b^(1-θ) := by gcongr
    have h3 : C_b^θ * C_b^(1-θ) = C_b := by
      rw [← Real.rpow_add (by positivity)]
      have h4 : θ + (1 - θ) = 1 := by linarith
      rw [h4]; exact Real.rpow_one C_b
    linarith
  have hK_energy_le : K_energy ≤ 80 := by
    dsimp only [K_energy]
    have h1 : (2 : ℝ)^t ≤ 2 := by
      have h2 : (2 : ℝ)^t ≤ (2 : ℝ)^(1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) ht_le_one
      simpa using h2
    nlinarith
  have hX_le : X_univ ≤ C_b * 80 * 12 + 1 := by
    dsimp only [X_univ]
    have h1 : C_int * K_energy * 12 ≤ C_b * 80 * 12 := by
      have h2 : C_int ≤ C_b := hC_int_le
      have h3 : K_energy ≤ 80 := hK_energy_le
      have h4 : 0 ≤ C_int := by positivity
      have h5 : 0 ≤ K_energy := by positivity
      gcongr <;> linarith
    have h6 : max (C_int * K_energy * 12) ((3 / 2 : ℝ) * 54) ≤ C_b * 80 * 12 := by
      apply max_le
      · exact h1
      · dsimp only [C_b] <;> norm_num
    linarith
  have hK_le_uniform : K ≤ K_uniform := by
    dsimp only [K, K_uniform]
    have h1 : Real.log X_univ ≤ Real.log (C_b * 80 * 12 + 1) := Real.log_le_log hX_pos hX_le
    have h2 : 0 < Real.log C_log_min := Real.log_pos hClogmin_gt_one
    gcongr
  -- Convert bound from K to K_uniform (larger K gives weaker bound)
  have h1_div : (1 : ℝ) / K_uniform ≤ 1 / K :=
    one_div_le_one_div_of_le hK_pos hK_le_uniform
  have h2_rpow : C_log^(-K_uniform) ≤ C_log^(-K) := by
    have h3 : -K_uniform ≤ -K := by linarith
    have h4 : 1 ≤ C_log := by linarith [hClog_gt_one]
    exact Real.rpow_le_rpow_of_exponent_le h4 h3
  set A : ℝ := (1 / (C_P * C_T)) * M * δ^(-s) * (M * δ^s)^α with hA_def
  have hA_nonneg : 0 ≤ A := by positivity
  have h_final_uniform : (1 / K_uniform) * C_log^(-K_uniform) * A ≤ (1 / K) * C_log^(-K) * A := by
    have h5 : (1 / K_uniform) * C_log^(-K_uniform) ≤ (1 / K) * C_log^(-K) :=
      mul_le_mul h1_div h2_rpow (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_right h5 hA_nonneg
  have h_final' : (T.card : ℝ) ≥ (1 / K) * C_log^(-K) * A := by
    have h_eq : (1 / K) * C_log^(-K) * A = (1 / K) * C_log^(-K) * (1 / (C_P * C_T)) * M * δ^(-s) * (M * δ^s)^α := by
      rw [hA_def] <;> ring
    rw [h_eq]
    exact h_final
  calc (T.card : ℝ)
    ≥ (1 / K) * C_log^(-K) * A := h_final'
  _ ≥ (1 / K_uniform) * C_log^(-K_uniform) * A := h_final_uniform
  _ = (1 / K_uniform) * C_log^(-K_uniform) * (1 / (C_P * C_T)) * M * δ^(-s) * (M * δ^s)^α := by
    rw [hA_def] <;> ring

end DiscretisedFurstenbergEstimate