import MyLeanRepo.Kakeya.Streamlined.DividingScales.Combinatorics

/-!
# Finite scale chains for the dividing-scales stopping time

A recursive splitting path is represented only by its positive decreasing
scales.  No cover transition map is part of this data.  Adjacent coarse-to-
fine ratios telescope exactly from the unit scale to `delta`.
-/

noncomputable section

namespace Kakeya.Streamlined

/-- A positive decreasing scale chain from `1` to `delta`. -/
structure PositiveScaleChain (delta : ℝ) (J : ℕ) where
  rho : ℕ → ℝ
  rho_pos : ∀ k ≤ J, 0 < rho k
  rho_antitone : ∀ k < J, rho (k + 1) ≤ rho k
  rho_zero : rho 0 = 1
  rho_last : rho J = delta

/--
A splitting path through the distinguished paper grid.

Only the increasing grid indices are recorded.  Covers at those indices
remain independent.
-/
structure GridIndexChain (delta : ℝ) (J : ℕ) where
  index : ℕ → UniformScaleIndex delta
  index_strict : ∀ k < J, index k < index (k + 1)
  index_zero :
    index 0 = (⟨0, Nat.succ_pos _⟩ : UniformScaleIndex delta)
  index_last :
    index J = Fin.last (uniformScaleSteps delta)

/--
A strictly increasing finite chain of distinguished grid indices with
arbitrary endpoints.

Unlike `GridIndexChain`, this structure does not require the coarse endpoint
to be the unit scale or the fine endpoint to be `delta`.
-/
structure GridIndexSubchain (delta : ℝ) (J : ℕ) where
  index : ℕ → UniformScaleIndex delta
  index_strict : ∀ k < J, index k < index (k + 1)

namespace PositiveScaleChain

/-- The `k`-th coarse-to-fine ratio along a scale chain. -/
def ratio {delta : ℝ} {J : ℕ}
    (chain : PositiveScaleChain delta J) (k : Fin J) : ℝ :=
  chain.rho k / chain.rho (k + 1)

/-- Every coarse-to-fine ratio is at least one. -/
lemma one_le_ratio
    {delta : ℝ} {J : ℕ}
    (chain : PositiveScaleChain delta J)
    (k : Fin J) :
    1 ≤ chain.ratio k := by
  apply (le_div_iff₀ (chain.rho_pos (k + 1) (by omega))).2
  simpa [mul_comm] using chain.rho_antitone k k.isLt

/-- The chain is antitone between arbitrary indices before its endpoint. -/
lemma rho_le_of_le
    {delta : ℝ} {J : ℕ}
    (chain : PositiveScaleChain delta J)
    {k l : ℕ} (hkl : k ≤ l) (hl : l ≤ J) :
    chain.rho l ≤ chain.rho k := by
  have hstep :
      ∀ d : ℕ, k + d ≤ J →
        chain.rho (k + d) ≤ chain.rho k := by
    intro d
    induction d with
    | zero =>
        simp
    | succ d ih =>
        intro hbound
        calc
          chain.rho (k + (d + 1))
              = chain.rho ((k + d) + 1) := by
                congr 1 <;> omega
          _ ≤ chain.rho (k + d) :=
            chain.rho_antitone (k + d) (by omega)
          _ ≤ chain.rho k := ih (by omega)
  have hl_eq : k + (l - k) = l := by
    omega
  simpa [hl_eq] using hstep (l - k) (by simpa [hl_eq] using hl)

/-- Every chain scale lies below the unit endpoint. -/
lemma rho_le_one
    {delta : ℝ} {J : ℕ}
    (chain : PositiveScaleChain delta J)
    {k : ℕ} (hk : k ≤ J) :
    chain.rho k ≤ 1 := by
  simpa [chain.rho_zero] using
    chain.rho_le_of_le (k := 0) (l := k) (by omega) hk

/-- Every chain scale lies above the `delta` endpoint. -/
lemma delta_le_rho
    {delta : ℝ} {J : ℕ}
    (chain : PositiveScaleChain delta J)
    {k : ℕ} (hk : k ≤ J) :
    delta ≤ chain.rho k := by
  simpa [chain.rho_last] using
    chain.rho_le_of_le (k := k) (l := J) hk le_rfl

/-- A natural-number telescoping product with explicit nonzero endpoints. -/
private lemma prod_range_div_telescope_of_ne_zero
    (rho : ℕ → ℝ) (J : ℕ)
    (hrho : ∀ k ≤ J, rho k ≠ 0) :
    (∏ k ∈ Finset.range J, rho k / rho (k + 1)) =
      rho 0 / rho J := by
  induction J with
  | zero =>
      simp [hrho 0 le_rfl]
  | succ J ih =>
      rw [Finset.prod_range_succ]
      rw [ih (fun k hk => hrho k (Nat.le.step hk))]
      field_simp [
        hrho 0 (by omega),
        hrho J (by omega),
        hrho (J + 1) (by omega)]

/-- The product of all adjacent ratios is exactly `1 / delta`. -/
lemma prod_ratio
    {delta : ℝ} {J : ℕ}
    (chain : PositiveScaleChain delta J) :
    ∏ k : Fin J, chain.ratio k = 1 / delta := by
  have hfin :
      (∏ k : Fin J, chain.rho k / chain.rho (k + 1)) =
        ∏ k ∈ Finset.range J,
          chain.rho k / chain.rho (k + 1) := by
    simpa using Fin.prod_univ_eq_prod_range
      (fun k : ℕ => chain.rho k / chain.rho (k + 1)) J
  change (∏ k : Fin J,
    chain.rho k / chain.rho (k + 1)) = _
  rw [hfin]
  rw [prod_range_div_telescope_of_ne_zero chain.rho J]
  · rw [chain.rho_zero, chain.rho_last]
  · intro k hk
    exact (chain.rho_pos k hk).ne'

/--
Powers of the adjacent scale ratios telescope to the same power of the
endpoint ratio.
-/
lemma prod_realRpowENN_ratio
    {delta : ℝ} {J : ℕ}
    (chain : PositiveScaleChain delta J)
    (exponent : ℝ) :
    ∏ k : Fin J,
        Kakeya.realRpowENN (chain.ratio k) exponent =
      Kakeya.realRpowENN (1 / delta) exponent := by
  simp only [Kakeya.realRpowENN]
  have hratio_nonneg :
      ∀ k ∈ (Finset.univ : Finset (Fin J)),
        0 ≤ chain.ratio k := by
    intro k _
    exact (chain.one_le_ratio k).trans' zero_le_one
  have hpower_nonneg :
      ∀ k ∈ (Finset.univ : Finset (Fin J)),
        0 ≤ chain.ratio k ^ exponent := by
    intro k _
    exact Real.rpow_nonneg (hratio_nonneg k (Finset.mem_univ k)) _
  change (∏ k ∈ (Finset.univ : Finset (Fin J)),
      ENNReal.ofReal (chain.ratio k ^ exponent)) =
    ENNReal.ofReal ((1 / delta) ^ exponent)
  rw [← ENNReal.ofReal_prod_of_nonneg hpower_nonneg]
  congr 1
  rw [Real.finsetProd_rpow Finset.univ chain.ratio
    hratio_nonneg exponent]
  rw [chain.prod_ratio]

/--
If every split gains at least `delta^(-epsilon^2)` in the scale ratio, the
chain has length at most `1 / epsilon^2`.
-/
lemma depth_bound
    {delta epsilon : ℝ} {J : ℕ}
    (chain : PositiveScaleChain delta J)
    (hdelta_one : delta < 1)
    (hepsilon : 0 < epsilon)
    (hratio :
      ∀ k, delta ^ (-epsilon ^ 2) ≤ chain.ratio k) :
    (J : ℝ) ≤ 1 / epsilon ^ 2 := by
  apply splitting_termination_bound
    (by simpa [chain.rho_last] using chain.rho_pos J le_rfl)
    hdelta_one hepsilon chain.ratio hratio
  rw [chain.prod_ratio]

/--
Either every terminal interval has relative fine scale at least
`delta^epsilon`, or one interval has the separated-scale relation used in
the bad alternative of `dividingScalesLemma`.
-/
lemma allIntervalsShort_or_existsSeparated
    {delta epsilon : ℝ} {J : ℕ}
    (chain : PositiveScaleChain delta J) :
    (∀ k : Fin J,
      delta ^ epsilon * chain.rho k ≤ chain.rho (k + 1)) ∨
    ∃ k : Fin J,
      chain.rho (k + 1) ≤ delta ^ epsilon * chain.rho k := by
  classical
  by_cases h :
      ∀ k : Fin J,
        delta ^ epsilon * chain.rho k ≤ chain.rho (k + 1)
  · exact Or.inl h
  · push Not at h
    rcases h with ⟨k, hk⟩
    exact Or.inr ⟨k, hk.le⟩

/--
A separated chain interval directly supplies scales with the endpoint and
ordering conditions appearing in the bad alternative.
-/
lemma exists_scales_of_separated
    {delta epsilon : ℝ} {J : ℕ}
    (chain : PositiveScaleChain delta J)
    (hseparated :
      ∃ k : Fin J,
        chain.rho (k + 1) ≤
          delta ^ epsilon * chain.rho k) :
    ∃ tau theta : ℝ,
      0 < tau ∧
      tau ≤ theta ∧
      theta ≤ 1 ∧
      delta ≤ tau ∧
      tau ≤ delta ^ epsilon * theta := by
  rcases hseparated with ⟨k, hk⟩
  refine ⟨chain.rho (k + 1), chain.rho k, ?_, ?_, ?_, ?_, hk⟩
  · exact chain.rho_pos (k + 1) (by omega)
  · exact chain.rho_antitone k k.isLt
  · exact chain.rho_le_one (by omega)
  · exact chain.delta_le_rho (by omega)

end PositiveScaleChain

namespace GridIndexSubchain

/-- Grid indices are monotone between arbitrary positions in a subchain. -/
lemma index_le_of_le
    {delta : ℝ} {J : ℕ}
    (chain : GridIndexSubchain delta J)
    {k l : ℕ} (hkl : k ≤ l) (hl : l ≤ J) :
    chain.index k ≤ chain.index l := by
  have hstep :
      ∀ distance : ℕ, k + distance ≤ J →
        chain.index k ≤ chain.index (k + distance) := by
    intro distance
    induction distance with
    | zero =>
        simp
    | succ distance inductionHypothesis =>
        intro hbound
        have hprevious :
            chain.index k ≤ chain.index (k + distance) :=
          inductionHypothesis (by omega)
        have hnext :
            chain.index (k + distance) <
              chain.index (k + distance + 1) := by
          simpa [Nat.add_assoc] using
            chain.index_strict (k + distance) (by omega)
        exact hprevious.trans hnext.le
  have hposition : k + (l - k) = l := by
    omega
  simpa [hposition] using hstep (l - k) (by simpa [hposition] using hl)

/-- Coarse endpoint index of one subchain interval. -/
def coarseIndex
    {delta : ℝ} {J : ℕ}
    (chain : GridIndexSubchain delta J)
    (interval : Fin J) :
    UniformScaleIndex delta :=
  chain.index interval.val

/-- Fine endpoint index of one subchain interval. -/
def fineIndex
    {delta : ℝ} {J : ℕ}
    (chain : GridIndexSubchain delta J)
    (interval : Fin J) :
    UniformScaleIndex delta :=
  chain.index (interval.val + 1)

/-- Adjacent subchain endpoint scales have the coarse-to-fine ordering. -/
lemma fineScale_le_coarseScale
    {delta : ℝ} {J : ℕ}
    (chain : GridIndexSubchain delta J)
    (hdelta : 0 < delta)
    (hdelta_le_one : delta ≤ 1)
    (interval : Fin J) :
    (uniformScale delta hdelta_le_one
        (chain.fineIndex interval)).1 ≤
      (uniformScale delta hdelta_le_one
        (chain.coarseIndex interval)).1 := by
  exact uniformScale_antitone hdelta hdelta_le_one
    (Nat.le_of_lt (chain.index_strict interval.val interval.isLt))

end GridIndexSubchain

namespace GridIndexChain

/-- The paper-grid scale selected at position `k` of the chain. -/
def scale
    {delta : ℝ} {J : ℕ}
    (chain : GridIndexChain delta J)
    (hdelta_le_one : delta ≤ 1)
    (k : ℕ) : ℝ :=
  (uniformScale delta hdelta_le_one (chain.index k)).1

/-- Grid indices grow by at least their chain position. -/
lemma position_le_index
    {delta : ℝ} {J : ℕ}
    (chain : GridIndexChain delta J) :
    ∀ k ≤ J, k ≤ (chain.index k).val := by
  intro k hk
  induction k with
  | zero =>
      omega
  | succ k ih =>
      have hkJ : k < J := by
        omega
      have hstep := chain.index_strict k hkJ
      have hprev : k ≤ (chain.index k).val :=
        ih (by omega)
      exact Nat.succ_le_of_lt
        (lt_of_le_of_lt hprev hstep)

/-- A grid-index chain has at most `uniformScaleSteps delta` intervals. -/
lemma length_le_uniformScaleSteps
    {delta : ℝ} {J : ℕ}
    (chain : GridIndexChain delta J) :
    J ≤ uniformScaleSteps delta := by
  have h := chain.position_le_index J le_rfl
  rw [chain.index_last] at h
  simpa using h

/--
Project a grid-index chain to its positive decreasing geometric scales.
-/
def toPositiveScaleChain
    {delta : ℝ} {J : ℕ}
    (chain : GridIndexChain delta J)
    (hdelta : 0 < delta)
    (hdelta_le_one : delta ≤ 1) :
    PositiveScaleChain delta J where
  rho := chain.scale hdelta_le_one
  rho_pos k _ :=
    lt_of_lt_of_le hdelta
      (uniformScale delta hdelta_le_one
        (chain.index k)).property.1
  rho_antitone k hk :=
    uniformScale_antitone hdelta hdelta_le_one
      (Nat.le_of_lt (chain.index_strict k hk))
  rho_zero := by
    rw [scale, chain.index_zero, uniformScale_zero]
  rho_last := by
    rw [scale, chain.index_last, uniformScale_last]

/-- The full distinguished grid is itself a grid-index chain. -/
def full (delta : ℝ) :
    GridIndexChain delta (uniformScaleSteps delta) where
  index k :=
    ⟨min k (uniformScaleSteps delta),
      Nat.lt_succ_of_le (min_le_right _ _)⟩
  index_strict k hk := by
    change min k (uniformScaleSteps delta) <
      min (k + 1) (uniformScaleSteps delta)
    rw [min_eq_left (Nat.le_of_lt hk),
      min_eq_left (Nat.succ_le_of_lt hk)]
    omega
  index_zero := by
    apply Fin.ext
    simp
  index_last := by
    apply Fin.ext
    simp

@[simp] lemma full_index
    (delta : ℝ) (k : UniformScaleIndex delta) :
    (full delta).index k = k := by
  apply Fin.ext
  simp [full, Nat.min_eq_left (Nat.le_of_lt_succ k.isLt)]

/--
Insert one distinguished grid scale strictly inside interval `interval`.
-/
def insertAt
    {delta : ℝ} {J : ℕ}
    (chain : GridIndexChain delta J)
    (interval : Fin J)
    (middle : UniformScaleIndex delta)
    (hleft : chain.index interval.val < middle)
    (hright : middle < chain.index (interval.val + 1)) :
    GridIndexChain delta (J + 1) where
  index position :=
    if position ≤ interval.val then chain.index position
    else if position = interval.val + 1 then middle
    else chain.index (position - 1)
  index_strict position hposition := by
    by_cases hbefore : position < interval.val
    · have hp : position ≤ interval.val := by
        omega
      have hq : position + 1 ≤ interval.val := by
        omega
      simp only [hp, hq, ↓reduceIte]
      exact chain.index_strict position (by omega)
    · by_cases hat : position = interval.val
      · subst position
        simp only [le_refl, ↓reduceIte]
        rw [if_neg (by omega)]
        exact hleft
      · by_cases hafter : position = interval.val + 1
        · subst position
          simp only [
            show ¬ interval.val + 1 ≤ interval.val by omega,
            show ¬ interval.val + 1 + 1 ≤ interval.val by omega,
            ↓reduceIte]
          rw [if_neg (by omega)]
          simpa using hright
        · have hp : ¬ position ≤ interval.val := by
            omega
          have hq : ¬ position + 1 ≤ interval.val := by
            omega
          have hp_eq : position ≠ interval.val + 1 := hafter
          have hq_eq : position + 1 ≠ interval.val + 1 := by
            omega
          simp only [hp, hq, hp_eq, hq_eq, ↓reduceIte]
          have hpred : position - 1 < J := by
            omega
          simpa [
            show position - 1 + 1 = position by omega,
            show position + 1 - 1 = position by omega] using
              chain.index_strict (position - 1) hpred
  index_zero := by
    simp only [Nat.zero_le, ↓reduceIte]
    exact chain.index_zero
  index_last := by
    have hp : ¬ J + 1 ≤ interval.val := by
      omega
    have hp_eq : J + 1 ≠ interval.val + 1 := by
      omega
    simp only [hp, hp_eq, ↓reduceIte]
    have heq : J + 1 - 1 = J := by
      omega
    rw [heq, chain.index_last]

@[simp] lemma insertAt_index_before
    {delta : ℝ} {J : ℕ}
    (chain : GridIndexChain delta J)
    (interval : Fin J)
    (middle : UniformScaleIndex delta)
    (hleft : chain.index interval.val < middle)
    (hright : middle < chain.index (interval.val + 1))
    (position : ℕ) (hposition : position ≤ interval.val) :
    (chain.insertAt interval middle hleft hright).index position =
      chain.index position := by
  simp [insertAt, hposition]

@[simp] lemma insertAt_index_middle
    {delta : ℝ} {J : ℕ}
    (chain : GridIndexChain delta J)
    (interval : Fin J)
    (middle : UniformScaleIndex delta)
    (hleft : chain.index interval.val < middle)
    (hright : middle < chain.index (interval.val + 1)) :
    (chain.insertAt interval middle hleft hright).index
        (interval.val + 1) =
      middle := by
  simp [insertAt]

@[simp] lemma insertAt_index_after
    {delta : ℝ} {J : ℕ}
    (chain : GridIndexChain delta J)
    (interval : Fin J)
    (middle : UniformScaleIndex delta)
    (hleft : chain.index interval.val < middle)
    (hright : middle < chain.index (interval.val + 1))
    (position : ℕ) (hposition : interval.val + 1 < position) :
    (chain.insertAt interval middle hleft hright).index position =
      chain.index (position - 1) := by
  simp [insertAt,
    show ¬ position ≤ interval.val by omega,
    show position ≠ interval.val + 1 by omega]

/-- The coarse endpoint index of interval `k`. -/
def coarseIndex
    {delta : ℝ} {J : ℕ}
    (chain : GridIndexChain delta J)
    (k : Fin J) : UniformScaleIndex delta :=
  chain.index k

/-- The fine endpoint index of interval `k`. -/
def fineIndex
    {delta : ℝ} {J : ℕ}
    (chain : GridIndexChain delta J)
    (k : Fin J) : UniformScaleIndex delta :=
  chain.index (k + 1)

/-- Fine endpoint scales do not exceed coarse endpoint scales. -/
lemma fineScale_le_coarseScale
    {delta : ℝ} {J : ℕ}
    (chain : GridIndexChain delta J)
    (hdelta : 0 < delta)
    (hdelta_le_one : delta ≤ 1)
    (k : Fin J) :
    (uniformScale delta hdelta_le_one
        (chain.fineIndex k)).1 ≤
      (uniformScale delta hdelta_le_one
        (chain.coarseIndex k)).1 := by
  exact uniformScale_antitone hdelta hdelta_le_one
    (Nat.le_of_lt (chain.index_strict k k.isLt))

/--
Every distinguished grid index belongs to one interval of a grid-index chain.

The endpoint conventions force every such chain to have positive length:
`uniformScaleSteps delta` is at least one, so the zero and last grid indices
cannot coincide.
-/
lemma exists_interval_containing
    {delta : ℝ} (hdelta : 0 < delta)
    {hdelta_le_one : delta ≤ 1}
    {J : ℕ} (chain : GridIndexChain delta J)
    (t : UniformScaleIndex delta) :
    ∃ interval : Fin J,
      (uniformScale delta hdelta_le_one
          (chain.fineIndex interval)).1 ≤
        (uniformScale delta hdelta_le_one t).1 ∧
      (uniformScale delta hdelta_le_one t).1 ≤
        (uniformScale delta hdelta_le_one
          (chain.coarseIndex interval)).1 := by
  have hJ_pos : 0 < J := by
    by_contra hJ
    have hJ_zero : J = 0 := by omega
    subst hJ_zero
    have hzero :
        chain.index 0 =
          (⟨0, Nat.succ_pos _⟩ : UniformScaleIndex delta) :=
      chain.index_zero
    have hlast :
        chain.index 0 = Fin.last (uniformScaleSteps delta) :=
      chain.index_last
    have hindices :
        (0 : UniformScaleIndex delta) =
          Fin.last (uniformScaleSteps delta) :=
      hzero.symm.trans hlast
    have hsteps_zero : uniformScaleSteps delta = 0 := by
      have hvalues := congrArg Fin.val hindices
      simpa using hvalues.symm
    have hsteps_pos : 1 ≤ uniformScaleSteps delta :=
      uniformScaleSteps_pos delta
    omega
  let positions : Finset ℕ :=
    Finset.filter
      (fun n => chain.index n ≤ t)
      (Finset.Icc 0 J)
  have hzero_mem : 0 ∈ positions := by
    simp [positions, chain.index_zero]
  have hpositions : positions.Nonempty := ⟨0, hzero_mem⟩
  let k := positions.max' hpositions
  have hk_mem : k ∈ positions :=
    Finset.max'_mem positions hpositions
  have hk_le_J : k ≤ J :=
    (Finset.mem_Icc.mp (Finset.mem_filter.mp hk_mem).1).2
  have hk_t : chain.index k ≤ t :=
    (Finset.mem_filter.mp hk_mem).2
  by_cases hk_lt_J : k < J
  · have hsucc_Icc : k + 1 ∈ Finset.Icc 0 J := by
      simp only [Finset.mem_Icc]
      omega
    have hsucc_not_mem : k + 1 ∉ positions := by
      intro hsucc
      have := Finset.le_max' positions (k + 1) hsucc
      omega
    have ht_lt_succ : ¬ chain.index (k + 1) ≤ t := by
      intro hle
      exact hsucc_not_mem
        (by simp [positions, hsucc_Icc, hle])
    have ht_succ : t ≤ chain.index (k + 1) :=
      le_of_not_ge ht_lt_succ
    let interval : Fin J := ⟨k, hk_lt_J⟩
    refine ⟨interval, ?_, ?_⟩
    · exact uniformScale_antitone
        hdelta hdelta_le_one ht_succ
    · exact uniformScale_antitone
        hdelta hdelta_le_one hk_t
  · have hk_eq : k = J := by omega
    have ht_last : t = chain.index J := by
      apply le_antisymm
      · rw [chain.index_last]
        exact Fin.le_last t
      · simpa [hk_eq] using hk_t
    have hpred_lt : J - 1 < J := by omega
    let interval : Fin J := ⟨J - 1, hpred_lt⟩
    have hsucc : (J - 1) + 1 = J := by omega
    refine ⟨interval, ?_, ?_⟩
    · change
        (uniformScale delta hdelta_le_one
            (chain.index ((J - 1) + 1))).1 ≤
          (uniformScale delta hdelta_le_one t).1
      rw [hsucc, ht_last]
    · change
        (uniformScale delta hdelta_le_one t).1 ≤
          (uniformScale delta hdelta_le_one
            (chain.index (J - 1))).1
      rw [ht_last]
      exact uniformScale_antitone hdelta hdelta_le_one
        (Nat.le_of_lt (by
          simpa [hsucc] using
            chain.index_strict (J - 1) hpred_lt))

/--
A separated grid interval directly supplies target-shaped `tau, theta`
scales.
-/
lemma exists_grid_scales_of_separated
    {delta epsilon : ℝ} {J : ℕ}
    (chain : GridIndexChain delta J)
    (hdelta : 0 < delta)
    (hdelta_le_one : delta ≤ 1)
    (hseparated :
      ∃ k : Fin J,
        chain.scale hdelta_le_one (k + 1) ≤
          delta ^ epsilon *
            chain.scale hdelta_le_one k) :
    ∃ tau theta : ℝ,
      0 < tau ∧
      tau ≤ theta ∧
      theta ≤ 1 ∧
      delta ≤ tau ∧
      tau ≤ delta ^ epsilon * theta := by
  exact (chain.toPositiveScaleChain hdelta hdelta_le_one)
    |>.exists_scales_of_separated hseparated

end GridIndexChain

end Kakeya.Streamlined
