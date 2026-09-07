import MyLeanRepo.Kakeya.Assouad.WZ1.Corollary26RepairedStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.IntervalADHelpers

/-!
# Helper lemmas for the WZ1 Corollary 26 anchored hierarchy proof

This module collects proved supporting lemmas from multiple contributors:

1. **AD set contradiction** (Aurora): ruling out projection dichotomy conclusion B
2. **Numerical nesting** (Bacon): slope approximations imply numerical nesting
3. **Unique parent** (Bacon): separated cores + endpoint coverage ⇒ unique parent
4. **Interval shrinking** (Bacon): shrink trapezoid cores to active endpoints
5. **Package assembly** (Dune): restrict/weaken local grains and global slab AD

All lemmas in this module are complete.
-/

namespace Kakeya.Assouad

open scoped ENNReal

/-!
## 1. AD set vs projection dichotomy conclusion B contradiction
-/

/-- Finite union bound for external covering numbers (ENNReal version). -/
lemma externalCoveringNumber_finite_union_le
  {X : Type*} [PseudoEMetricSpace X] {ε : NNReal}
  {α : Type*} [DecidableEq α]
  (s : Finset α) (f : α → Set X) :
  (↑(Metric.externalCoveringNumber ε (⋃ i ∈ s, f i)) : ENNReal) ≤
    ∑ i ∈ s, (↑(Metric.externalCoveringNumber ε (f i)) : ENNReal) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    have h_set : (⋃ i ∈ insert a s, f i) = f a ∪ (⋃ i ∈ s, f i) := by
      ext x
      simp [Finset.mem_insert] <;> tauto
    rw [h_set]
    have h_union :
        (↑(Metric.externalCoveringNumber ε (f a ∪ (⋃ i ∈ s, f i))) : ENNReal) ≤
        (↑(Metric.externalCoveringNumber ε (f a)) : ENNReal) +
        (↑(Metric.externalCoveringNumber ε (⋃ i ∈ s, f i)) : ENNReal) := by
      exact_mod_cast externalCoveringNumber_union_le (ε := ε) (A := f a) (B := (⋃ i ∈ s, f i))
    rw [Finset.sum_insert ha]
    exact h_union.trans (add_le_add_right ih _)

/--
Small-radius case: the AD set upper bound on `A ∩ ball(center, radius)`
contradicts a strictly larger lower bound on `D ∩ ball(center, radius)`
when `D ⊆ A`.
-/
lemma ad_set_contradicts_B_small_radius
  {adDelta rho radius alpha epsilon : ℝ}
  {C : ENNReal}
  {A D : Set ℝ}
  {center : ℝ}
  (hA : IsADSet1 A adDelta alpha C)
  (hD_sub : D ⊆ A)
  (hrad : adDelta ≤ rho)
  (hrho1 : rho ≤ 1)
  (hrho_nonneg : 0 ≤ rho)
  (hradius_ge : rho ≤ radius)
  (hradius_le : radius ≤ 1)
  (h_lower :
    Kakeya.realRpowENN (2 * radius / rho) (1 - epsilon) ≤
    (↑(Metric.externalCoveringNumber (Real.toNNReal rho)
       (D ∩ Metric.closedBall center radius)) : ENNReal))
  (h_strict :
    C * Kakeya.realRpowENN (radius / rho) alpha <
    Kakeya.realRpowENN (2 * radius / rho) (1 - epsilon)) :
  False := by
  rcases hA with ⟨_, _, _, _, _, hcover⟩
  have h_eq : Real.toNNReal rho = ⟨rho, hrho_nonneg⟩ :=
    Real.toNNReal_of_nonneg hrho_nonneg
  have hAD_upper :
      (↑(Metric.externalCoveringNumber (Real.toNNReal rho)
         (A ∩ Metric.closedBall center radius)) : ENNReal) ≤
      C * Kakeya.realRpowENN (radius / rho) alpha := by
    rw [h_eq]
    exact hcover rho hrho_nonneg hrad hrho1 center radius hradius_ge hradius_le
  have hsub :
      D ∩ Metric.closedBall center radius ⊆
      A ∩ Metric.closedBall center radius :=
    Set.inter_subset_inter hD_sub Set.Subset.rfl
  have hmono :
      (↑(Metric.externalCoveringNumber (Real.toNNReal rho)
         (D ∩ Metric.closedBall center radius)) : ENNReal) ≤
      (↑(Metric.externalCoveringNumber (Real.toNNReal rho)
         (A ∩ Metric.closedBall center radius)) : ENNReal) := by
    exact_mod_cast Metric.externalCoveringNumber_mono_set hsub
  have h1 :
      (↑(Metric.externalCoveringNumber (Real.toNNReal rho)
         (D ∩ Metric.closedBall center radius)) : ENNReal) ≤
      C * Kakeya.realRpowENN (radius / rho) alpha :=
    hmono.trans hAD_upper
  have h2 :
      Kakeya.realRpowENN (2 * radius / rho) (1 - epsilon) ≤
      C * Kakeya.realRpowENN (radius / rho) alpha :=
    h_lower.trans h1
  exact not_le.mpr h_strict h2

/--
Large-radius case: cover A ⊆ [-4,4] by 9 unit balls and sum the AD bounds.
-/
lemma ad_set_contradicts_B_large_radius
  {adDelta rho radius alpha epsilon : ℝ}
  {C : ENNReal}
  {A D : Set ℝ}
  {center : ℝ}
  (hA : IsADSet1 A adDelta alpha C)
  (hD_sub : D ⊆ A)
  (hrad : adDelta ≤ rho)
  (hrho1 : rho ≤ 1)
  (hrho_nonneg : 0 ≤ rho)
  (h_lower :
    Kakeya.realRpowENN (2 * radius / rho) (1 - epsilon) ≤
    (↑(Metric.externalCoveringNumber (Real.toNNReal rho)
       (D ∩ Metric.closedBall center radius)) : ENNReal))
  (h_strict :
    (9 : ENNReal) * C * Kakeya.realRpowENN (1 / rho) alpha <
    Kakeya.realRpowENN (2 * radius / rho) (1 - epsilon)) :
  False := by
  rcases hA with ⟨_, _, _, _, hbounded, hcover⟩
  let centers : Finset ℝ :=
    {(-4 : ℝ), -3, -2, -1, 0, 1, 2, 3, 4}
  have hcover9 : A ⊆ ⋃ i ∈ centers, Metric.closedBall i 1 := by
    intro x hx
    have hxb : x ∈ Set.Icc (-4 : ℝ) 4 := hbounded hx
    let k : ℤ := Int.floor x
    have hk1 : (k : ℝ) ≤ x := Int.floor_le x
    have hk2 : x < (k : ℝ) + 1 := Int.lt_floor_add_one x
    have hk3 : -4 ≤ k := by
      have h : (-4 : ℝ) ≤ x := hxb.1
      have h' : (-4 : ℤ) ≤ k := by
        rw [Int.le_floor] <;> exact_mod_cast h
      exact h'
    have hk4 : k ≤ 4 := by
      have h : (k : ℝ) ≤ 4 := by linarith [hk1, hxb.2]
      exact_mod_cast h
    have hk_mem : (k : ℝ) ∈ centers := by
      have h5 : -4 ≤ k := hk3
      have h6 : k ≤ 4 := hk4
      interval_cases k <;> simp [centers] <;> norm_num
    have hdist : dist x (k : ℝ) ≤ 1 := by
      have : |x - (k : ℝ)| ≤ 1 := by
        have h3 : 0 ≤ x - (k : ℝ) := by linarith
        have h4 : x - (k : ℝ) < 1 := by linarith
        rw [abs_of_nonneg h3] <;> linarith
      simpa [Real.dist_eq] using this
    exact Set.mem_iUnion₂.mpr ⟨(k : ℝ), hk_mem, hdist⟩
  have hDcover :
      D ∩ Metric.closedBall center radius ⊆
      ⋃ i ∈ centers, (A ∩ Metric.closedBall i 1) := by
    intro x hx
    have hxA : x ∈ A := hD_sub hx.1
    have h9 : x ∈ ⋃ i ∈ centers, Metric.closedBall i 1 := hcover9 hxA
    rcases Set.mem_iUnion₂.mp h9 with ⟨i, hi, hxi⟩
    exact Set.mem_iUnion₂.mpr ⟨i, hi, ⟨hxA, hxi⟩⟩
  have hmono :
      (↑(Metric.externalCoveringNumber (Real.toNNReal rho)
         (D ∩ Metric.closedBall center radius)) : ENNReal) ≤
      (↑(Metric.externalCoveringNumber (Real.toNNReal rho)
         (⋃ i ∈ centers, (A ∩ Metric.closedBall i 1))) : ENNReal) := by
    exact_mod_cast Metric.externalCoveringNumber_mono_set hDcover
  have hsum :
      (↑(Metric.externalCoveringNumber (Real.toNNReal rho)
         (⋃ i ∈ centers, (A ∩ Metric.closedBall i 1))) : ENNReal) ≤
      ∑ i ∈ centers,
        (↑(Metric.externalCoveringNumber (Real.toNNReal rho)
           (A ∩ Metric.closedBall i 1)) : ENNReal) := by
    have h := externalCoveringNumber_finite_union_le (ε := Real.toNNReal rho) centers
      (fun i : ℝ => A ∩ Metric.closedBall i 1)
    exact h
  have h_eq : Real.toNNReal rho = ⟨rho, hrho_nonneg⟩ :=
    Real.toNNReal_of_nonneg hrho_nonneg
  have heach : ∀ i ∈ centers,
      (↑(Metric.externalCoveringNumber (Real.toNNReal rho)
         (A ∩ Metric.closedBall i 1)) : ENNReal) ≤
      C * Kakeya.realRpowENN (1 / rho) alpha := by
    intro i _
    rw [h_eq]
    exact hcover rho hrho_nonneg hrad hrho1 i 1 (by linarith) (by norm_num)
  have hsum2 :
      (∑ i ∈ centers,
        (↑(Metric.externalCoveringNumber (Real.toNNReal rho)
           (A ∩ Metric.closedBall i 1)) : ENNReal)) ≤
      (centers.card : ENNReal) * C * Kakeya.realRpowENN (1 / rho) alpha := by
    calc
      (∑ i ∈ centers, _) ≤
          ∑ i ∈ centers, C * Kakeya.realRpowENN (1 / rho) alpha :=
        Finset.sum_le_sum fun i hi => heach i hi
      _ = (centers.card : ENNReal) * C * Kakeya.realRpowENN (1 / rho) alpha := by
        simp [Finset.sum_const, mul_assoc] <;> ring
  have hcard : centers.card = 9 := by
    simp [centers] <;> norm_num
  have h1 :
      (↑(Metric.externalCoveringNumber (Real.toNNReal rho)
         (D ∩ Metric.closedBall center radius)) : ENNReal) ≤
      (9 : ENNReal) * C * Kakeya.realRpowENN (1 / rho) alpha := by
    rw [hcard] at hsum2
    exact hmono.trans (hsum.trans hsum2)
  have h2 :
      Kakeya.realRpowENN (2 * radius / rho) (1 - epsilon) ≤
      (9 : ENNReal) * C * Kakeya.realRpowENN (1 / rho) alpha :=
    h_lower.trans h1
  exact not_le.mpr h_strict h2

/-!
## 2. Numerical nesting from slope approximations
-/

/--
If child and parent trapezoids both approximate the same source slope on
their cores, and the child core is contained in the parent core, then
the child is numerically nested in the parent.
-/
lemma numerical_nesting_from_approximations
    {sourceSlope : ℝ → ℝ}
    {child parent : WZ1VerticalTrapezoid}
    {rho_child rho_parent : ℝ}
    (h_child_height : child.height = rho_child)
    (h_parent_height : parent.height = rho_parent)
    (h_core_sub : child.core ⊆ parent.core)
    (h_child_approx : ∀ z ∈ child.core,
        |sourceSlope z - child.affine z| ≤ rho_child)
    (h_parent_approx : ∀ z ∈ parent.core,
        |sourceSlope z - parent.affine z| ≤ rho_parent) :
    WZ1VerticalTrapezoid.IsNumericallyNestedIn child parent := by
  refine ⟨h_core_sub, fun z hz => ?_⟩
  set a : ℝ := sourceSlope z - child.affine z with ha
  set b : ℝ := sourceSlope z - parent.affine z with hb
  have h1 : |a| ≤ rho_child := h_child_approx z hz
  have h2 : |b| ≤ rho_parent := h_parent_approx z (h_core_sub hz)
  have h_eq : child.affine z - parent.affine z = b - a := by
    simp [ha, hb]
  rw [h_eq]
  have h_tri : |b - a| ≤ |b| + |a| := by
    simp [abs_sub]
  have h4 : |b - a| ≤ rho_child + rho_parent := by
    calc |b - a| ≤ |b| + |a| := h_tri
         _ ≤ rho_parent + rho_child := by gcongr
         _ = rho_child + rho_parent := by ring
  rw [h_child_height, h_parent_height]
  exact h4

/-!
## 3. Unique parent core containment
-/

/--
Given a family of pairwise `sqrt(rho_parent)`-separated intervals (trapezoid cores),
and a child interval of length at most `sqrt(rho_child)` with `rho_child < rho_parent`,
whose endpoints each lie in some parent interval, the child interval is contained in
a UNIQUE parent interval.
-/
lemma unique_parent_core_containment
    {parents : Finset WZ1VerticalTrapezoid}
    {child : WZ1VerticalTrapezoid}
    {rho_parent rho_child : ℝ}
    (h_rho_parent_pos : 0 < rho_parent)
    (h_rho_child_pos : 0 < rho_child)
    (h_separated :
      ∀ p ∈ parents, ∀ q ∈ parents, p ≠ q →
        ∀ z ∈ p.core, ∀ w ∈ q.core,
          Real.sqrt rho_parent ≤ |z - w|)
    (h_child_length : child.length ≤ Real.sqrt rho_child)
    (h_rho_child_lt_parent : rho_child < rho_parent)
    (h_left_covered : ∃ p ∈ parents, child.left ∈ p.core)
    (h_right_covered : ∃ p ∈ parents, child.right ∈ p.core) :
    ∃! p : WZ1VerticalTrapezoid,
      p ∈ parents ∧ child.core ⊆ p.core := by
  rcases h_left_covered with ⟨p, hp_mem, hp_left⟩
  rcases h_right_covered with ⟨q, hq_mem, hq_right⟩
  by_cases hpq : p = q
  · subst hpq
    have h_contain : child.core ⊆ p.core := by
      intro z hz
      have hz1 : child.left ≤ z := (Set.mem_Icc.mp hz).1
      have hz2 : z ≤ child.right := (Set.mem_Icc.mp hz).2
      have hpl1 : p.left ≤ child.left := (Set.mem_Icc.mp hp_left).1
      have hpl2 : child.right ≤ p.right := (Set.mem_Icc.mp hq_right).2
      exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
    refine ⟨p, ⟨hp_mem, h_contain⟩, ?_⟩
    intro y hy
    have h_y_mem : y ∈ parents := hy.1
    have h_y_contain : child.core ⊆ y.core := hy.2
    by_cases hyq : y = p
    · exact hyq
    · have h_nonempty : child.core.Nonempty :=
        ⟨child.left, Set.left_mem_Icc.mpr child.left_lt_right.le⟩
      rcases h_nonempty with ⟨z, hz⟩
      have hz_p : z ∈ p.core := h_contain hz
      have hz_y : z ∈ y.core := h_y_contain hz
      have h_sep : Real.sqrt rho_parent ≤ |z - z| :=
        h_separated y h_y_mem p hp_mem hyq z hz_y z hz_p
      have h_pos : 0 < Real.sqrt rho_parent := Real.sqrt_pos.mpr h_rho_parent_pos
      rw [show z - z = 0 by ring] at h_sep
      rw [abs_zero] at h_sep
      linarith
  · have h_sep : Real.sqrt rho_parent ≤ |child.left - child.right| :=
      h_separated p hp_mem q hq_mem hpq
        child.left hp_left child.right hq_right
    have hlen : |child.left - child.right| = child.length := by
      have h : child.left < child.right := child.left_lt_right
      rw [show child.left - child.right = -(child.right - child.left) by ring]
      rw [abs_neg, abs_of_pos (show 0 < child.right - child.left from by linarith)]
      <;> simp [WZ1VerticalTrapezoid.length] <;> linarith
    rw [hlen] at h_sep
    have hsqrt_lt : Real.sqrt rho_child < Real.sqrt rho_parent :=
      Real.sqrt_lt_sqrt (by linarith) h_rho_child_lt_parent
    linarith

/-!
## 4. Interval shrinking to active endpoints
-/

/--
Shrink an interval `[a, b]` to endpoints `a', b'` drawn from an active set `A`,
preserving a minimum length.
-/
lemma shrink_interval_to_active_set
    {A : Set ℝ} {a b min_length slack : ℝ}
    (hab : a < b)
    (hmin_pos : 0 < min_length)
    (hmin_len : min_length ≤ b - a)
    (hslack_pos : 0 ≤ slack)
    (hslack : 2 * slack ≤ b - a - min_length)
    (ha_active : ∃ a' : ℝ, a' ∈ A ∧ a ≤ a' ∧ a' ≤ a + slack)
    (hb_active : ∃ b' : ℝ, b' ∈ A ∧ b - slack ≤ b' ∧ b' ≤ b) :
    ∃ a' b' : ℝ,
      a' ∈ A ∧ b' ∈ A ∧ a ≤ a' ∧ a' < b' ∧ b' ≤ b ∧
      min_length ≤ b' - a' := by
  rcases ha_active with ⟨a', haA, ha1, ha2⟩
  rcases hb_active with ⟨b', hbA, hb1, hb2⟩
  have hlen : min_length ≤ b' - a' := by
    calc
      b' - a' ≥ (b - slack) - (a + slack) := by linarith
      _ = b - a - 2 * slack := by ring
      _ ≥ min_length := by linarith
  have h_pos : 0 < b' - a' := by
    have h : min_length ≤ b' - a' := hlen
    linarith [hmin_pos]
  have hlt : a' < b' := by linarith
  exact ⟨a', b', haA, hbA, ha1, hlt, hb2, hlen⟩

/--
Construct a shrunk trapezoid whose endpoints lie in the active set.
Given an existing trapezoid and active points near both endpoints,
produce a new trapezoid with the same slope and height but shrunk core.
-/
lemma shrink_trapezoid_to_active_endpoints
    {A : Set ℝ} {trapezoid : WZ1VerticalTrapezoid}
    {min_length slack : ℝ}
    (hmin_pos : 0 < min_length)
    (hmin : min_length ≤ trapezoid.length)
    (hslack_pos : 0 ≤ slack)
    (hslack : 2 * slack ≤ trapezoid.length - min_length)
    (ha_active : ∃ a' : ℝ, a' ∈ A ∧ trapezoid.left ≤ a' ∧ a' ≤ trapezoid.left + slack)
    (hb_active : ∃ b' : ℝ, b' ∈ A ∧ trapezoid.right - slack ≤ b' ∧ b' ≤ trapezoid.right) :
    ∃ trapezoid' : WZ1VerticalTrapezoid,
      trapezoid'.core ⊆ trapezoid.core ∧
      trapezoid'.left ∈ A ∧ trapezoid'.right ∈ A ∧
      trapezoid'.slope = trapezoid.slope ∧
      trapezoid'.height = trapezoid.height ∧
      min_length ≤ trapezoid'.length := by
  have h_ab : trapezoid.left < trapezoid.right := trapezoid.left_lt_right
  have h_main := shrink_interval_to_active_set
    (hab := h_ab) (hmin_pos := hmin_pos) (hmin_len := hmin)
    (hslack_pos := hslack_pos)
    (hslack := hslack) ha_active hb_active
  rcases h_main with ⟨a', b', haA, hbA, ha1, hlt, hb2, hlen⟩
  let trapezoid' : WZ1VerticalTrapezoid :=
    { left := a'
      right := b'
      left_lt_right := hlt
      slope := trapezoid.slope
      intercept := trapezoid.intercept
      height := trapezoid.height
      height_pos := trapezoid.height_pos }
  have h_core_sub : trapezoid'.core ⊆ trapezoid.core := by
    intro z hz
    have h1 : a' ≤ z := (Set.mem_Icc.mp hz).1
    have h2 : z ≤ b' := (Set.mem_Icc.mp hz).2
    exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
  exact ⟨trapezoid', h_core_sub, haA, hbA, rfl, rfl, hlen⟩

/-!
## 5. Combined child nesting lemma
-/

/--
Combine coverage, separation, and slope approximations to show that a
child trapezoid is numerically nested in a unique parent trapezoid.

This is the main nesting lemma used between adjacent hierarchy levels.
-/
lemma child_nests_in_unique_parent
    {sourceSlope : ℝ → ℝ}
    {parents : Finset WZ1VerticalTrapezoid}
    {child : WZ1VerticalTrapezoid}
    {rho_parent rho_child : ℝ}
    (h_rho_parent_pos : 0 < rho_parent)
    (h_rho_child_pos : 0 < rho_child)
    (h_separated :
      ∀ p ∈ parents, ∀ q ∈ parents, p ≠ q →
        ∀ z ∈ p.core, ∀ w ∈ q.core,
          Real.sqrt rho_parent ≤ |z - w|)
    (h_child_length : child.length ≤ Real.sqrt rho_child)
    (h_rho_child_lt_parent : rho_child < rho_parent)
    (h_child_height : child.height = rho_child)
    (h_parent_heights : ∀ p ∈ parents, p.height = rho_parent)
    (h_left_covered : ∃ p ∈ parents, child.left ∈ p.core)
    (h_right_covered : ∃ p ∈ parents, child.right ∈ p.core)
    (h_child_approx : ∀ z ∈ child.core,
        |sourceSlope z - child.affine z| ≤ rho_child)
    (h_parent_approx : ∀ p ∈ parents, ∀ z ∈ p.core,
        |sourceSlope z - p.affine z| ≤ rho_parent) :
    ∃! p : WZ1VerticalTrapezoid,
      p ∈ parents ∧ WZ1VerticalTrapezoid.IsNumericallyNestedIn child p := by
  have h_unique_core := unique_parent_core_containment
    h_rho_parent_pos h_rho_child_pos h_separated
    h_child_length h_rho_child_lt_parent
    h_left_covered h_right_covered
  rcases h_unique_core with ⟨p, ⟨hp_mem, h_core_sub⟩, h_uniq⟩
  have h_parent_height : p.height = rho_parent := h_parent_heights p hp_mem
  have h_nesting : WZ1VerticalTrapezoid.IsNumericallyNestedIn child p :=
    numerical_nesting_from_approximations
      h_child_height h_parent_height h_core_sub
      h_child_approx (h_parent_approx p hp_mem)
  refine ⟨p, ⟨hp_mem, h_nesting⟩, ?_⟩
  intro q hq
  have hq_mem : q ∈ parents := hq.1
  have hq_nesting : WZ1VerticalTrapezoid.IsNumericallyNestedIn child q := hq.2
  have hq_core_sub : child.core ⊆ q.core := hq_nesting.1
  have hq' : q ∈ parents ∧ child.core ⊆ q.core := ⟨hq_mem, hq_core_sub⟩
  have hq_eq_p : q = p := h_uniq q hq'
  exact hq_eq_p

/-!
## 6. Local grain and global slab AD restriction / weakening
-/

/-- Weaken the constant of a WZ1LocalGrainData. -/
def weakenLocalGrainsConstant
    {delta sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C C' : ENNReal}
    (hCC' : C ≤ C')
    (lg : WZ1LocalGrainData Y sigma C) :
    WZ1LocalGrainData Y sigma C' :=
  { planeMap := lg.planeMap
    measurable := lg.measurable
    lipschitzConstant := lg.lipschitzConstant
    lipschitz := lg.lipschitz
    unit := lg.unit
    incidence := lg.incidence
    local_ad := fun rho hdelta_rho hrho_one p hp =>
      (lg.local_ad rho hdelta_rho hrho_one p hp).mono_constant hCC' }

/--
Restrict a WZ1LocalGrainData from a source shading to a subshading,
with a possibly weakened constant.
-/
def restrictAndWeakenLocalGrains
    {delta sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y Z : Kakeya.Streamlined.TubeShading F}
    (hsub : IsSubshading Z Y)
    {C C' : ENNReal}
    (hCC' : C ≤ C')
    (localGrains : WZ1LocalGrainData Y sigma C) :
    WZ1LocalGrainData Z sigma C' :=
  weakenLocalGrainsConstant hCC'
    { planeMap := localGrains.planeMap
      measurable := localGrains.measurable
      lipschitzConstant := localGrains.lipschitzConstant
      lipschitz := localGrains.lipschitz.mono (by
        rintro p ⟨i, hi⟩
        exact ⟨i, hsub i hi⟩)
      unit := fun p hp => localGrains.unit p (by
        rcases hp with ⟨i, hi⟩
        exact ⟨i, hsub i hi⟩)
      incidence := fun i p hp => localGrains.incidence i p (hsub i hp)
      local_ad := fun rho hdelta_rho hrho_one p hp =>
        (localGrains.local_ad rho hdelta_rho hrho_one p (by
          rcases hp with ⟨i, hi⟩
          exact ⟨i, hsub i hi⟩)).mono (by
            rintro y ⟨x, hx, rfl⟩
            exact ⟨x, ⟨by
              rcases hx.1 with ⟨i, hi⟩
              exact ⟨i, hsub i hi⟩, hx.2⟩, rfl⟩) }

/--
Restrict and weaken HasGlobalSlabAD from a source shading to a subshading.
-/
lemma restrictAndWeakenGlobalSlabAD
    {delta sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y Z : Kakeya.Streamlined.TubeShading F}
    (hsub : IsSubshading Z Y)
    {slope : ℝ → ℝ}
    {C C' : ENNReal}
    (hCC' : C ≤ C')
    (h : HasGlobalSlabAD Y slope sigma C) :
    HasGlobalSlabAD Z slope sigma C' := by
  intro z hz
  have hZ_sub_Y : Z.union ⊆ Y.union := by
    rintro p ⟨i, hi⟩
    exact ⟨i, hsub i hi⟩
  have hslab_Y := h z hz
  have hslab_Z : IsADSet1
      (globalGrainProjection slope (globalGrainSlab Z.union z delta))
      delta (1 - sigma) C := by
    exact hslab_Y.mono (by
      rintro y ⟨p, hp, rfl⟩
      exact ⟨p, ⟨Set.inter_subset_inter hZ_sub_Y Set.Subset.rfl hp.1, hp.2⟩, rfl⟩)
  exact hslab_Z.mono_constant hCC'

/-!
## 7. Weaken source package loss exponent
-/

/--
Weaken a `WZ1PlaninessGraininessPackage` from `inputLoss` to `inputLoss'`
when `inputLoss ≤ inputLoss'`.

Larger epsilon means weaker bounds, so all loss-dependent fields are weakened:
extremal pair via `mono_epsilon`, constant bound, and Lipschitz bounds via
rpow monotonicity.
-/
noncomputable def weakenSourceLoss
    {sigma inputLoss inputLoss' delta : ℝ}
    (h : inputLoss ≤ inputLoss')
    (hdelta_pos : 0 < delta) (hdelta_one : delta ≤ 1)
    (source : WZ1PlaninessGraininessPackage sigma inputLoss delta) :
    WZ1PlaninessGraininessPackage sigma inputLoss' delta := by
  have h_power :
      Kakeya.realRpowENN delta (-inputLoss) ≤
      Kakeya.realRpowENN delta (-inputLoss') := by
    apply ENNReal.ofReal_mono
    exact Real.rpow_le_rpow_of_exponent_ge hdelta_pos hdelta_one (by linarith)
  exact
    { family := source.family
      uniform := source.uniform
      shading := source.shading
      vertical_chart := source.vertical_chart
      constant := source.constant
      extremal := source.extremal.mono_epsilon h
      constant_one := source.constant_one
      constant_ne_top := source.constant_ne_top
      constant_bound := source.constant_bound.trans h_power
      global_grains := source.global_grains
      local_grains := source.local_grains
      slope_lipschitz_bound := source.slope_lipschitz_bound.trans h_power
      slope_one_lipschitz := source.slope_one_lipschitz
      slope_bound := source.slope_bound
      planeMap_vertical_bound := source.planeMap_vertical_bound
      planeMap_lipschitz_bound := source.planeMap_lipschitz_bound.trans h_power
      planeMap_one_lipschitz := source.planeMap_one_lipschitz }

/-!
## 8. Package assembly
-/

/--
Assemble the non-hierarchy fields of `WZ1Corollary26AnchoredHierarchyPackage`
from a source package, a refined shading, and a hierarchy.

Requires `inputLoss ≤ hierarchyLoss` so that constants can be weakened from
`delta^(-inputLoss)` to `delta^(-hierarchyLoss)`.
-/
noncomputable def packageAssembly
    {sigma inputLoss delta hierarchyLoss : ℝ}
    (source : WZ1PlaninessGraininessPackage sigma inputLoss delta)
    (h_inputLoss_le : inputLoss ≤ hierarchyLoss)
    (Z : Kakeya.Streamlined.TubeShading source.family)
    (hZ_sub : IsSubshading Z source.shading)
    (hZ_extremal : WZ1ExtremalPair sigma hierarchyLoss source.family source.uniform Z)
    (h_hierarchy :
      WZ1Corollary26AnchoredHierarchyData
        Z source.global_grains.slope hierarchyLoss) :
    WZ1Corollary26AnchoredHierarchyPackage source hierarchyLoss := by
  let targetConstant : ENNReal := Kakeya.realRpowENN delta (-hierarchyLoss)
  have h_const_weaken : source.constant ≤ targetConstant :=
    source.constant_bound.trans (by
      simp only [Kakeya.realRpowENN]
      apply ENNReal.ofReal_mono
      exact Real.rpow_le_rpow_of_exponent_ge
        hZ_extremal.1 hZ_extremal.2.1 (by linarith))
  let localGrains : WZ1LocalGrainData Z sigma targetConstant :=
    restrictAndWeakenLocalGrains hZ_sub h_const_weaken source.local_grains
  have hplaneMap_lipschitz_bound :
      (localGrains.lipschitzConstant : ENNReal) ≤ targetConstant := by
    have h1 : (localGrains.lipschitzConstant : ENNReal) ≤
        Kakeya.realRpowENN delta (-inputLoss) := source.planeMap_lipschitz_bound
    have h2 : Kakeya.realRpowENN delta (-inputLoss) ≤ targetConstant := by
      simp only [Kakeya.realRpowENN, targetConstant]
      apply ENNReal.ofReal_mono
      exact Real.rpow_le_rpow_of_exponent_ge
        hZ_extremal.1 hZ_extremal.2.1 (by linarith)
    exact h1.trans h2
  have hsource_global_slab_ad :
      HasGlobalSlabAD Z source.global_grains.slope sigma targetConstant :=
    restrictAndWeakenGlobalSlabAD hZ_sub h_const_weaken
      source.global_grains.global_slab_ad
  exact
    { shading := Z
      subshading := hZ_sub
      extremal := hZ_extremal
      local_grains := localGrains
      planeMap_eq := rfl
      planeMap_lipschitz_bound := hplaneMap_lipschitz_bound
      source_global_slab_ad := hsource_global_slab_ad
      source_slope_bound := source.slope_bound
      hierarchy := h_hierarchy }

end Kakeya.Assouad
