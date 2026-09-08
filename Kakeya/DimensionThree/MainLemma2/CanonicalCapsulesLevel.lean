/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.CanonicalCapsulesCore
public import Kakeya.DimensionThree.MainLemma2.BallCoreEDSegments

/-!
# C7-b: the dyadic level of the canonical-capsule core — mass and fullness

The refined fibre regularisation (l.3735–3743, l.5457–5470) pigeonholes the working shading over
the dyadic levels `m = 2^k` of the fibre count.  Two things are wanted of the chosen level at once:
it must keep a `1/polylog` share of the shading **mass** (`BallDataCore.Yg_mass`), and its
segments must be **full** — the shading of the level-`m` segments must dominate their carriers at
the Markov threshold `4 c₁ δ^{2η}` that `Kakeya.VeryNotSticky.exists_heavyBalls_core` reads.  A
level chosen by mass alone loses a `log(1/δ)` in fullness (the top levels have small bins in large
capsules), which the `δ`-free density constant `c₁` cannot absorb.  The two-constraint pigeonhole
`exists_level_heavy_full` below picks a level that is mass-heavy **and** full, with a `δ`-free
constant: the heavy levels carry half the mass, and the level-weighted carriers
`∑_k 2^k · #{ν : bin_k ν ≠ ∅} · |caps ν|` are bounded without a log because
`∑_{k : 2^k ≤ #fibre} 2^k ≤ 2 · #fibre` (geometric sum), while
`#fibre · |caps ν| ≤ 384 · ∑_{i ∈ fibre} |seg_T3(i)|` compares the capsule to T3's segments of its
fibre members — so T3's own fullness (`segs_fullness_of_cover`) pays, at `c₁' = 3072 c₁`.
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

namespace Kakeya.VeryNotSticky

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### The two-constraint pigeonhole over levels -/

/-- **A level that is both mass-heavy and full.**  Among `K` levels with masses `T k` and
weights `C k`, if `2 θ ∑ C ≤ ∑ T` then some level carries at least `1/(2K)` of the mass and has
`θ C k ≤ T k`.  (The heavy levels carry half the mass; if every heavy level failed the second
inequality, their mass would be strictly below `θ ∑ C ≤ ∑ T / 2`.) -/
theorem exists_level_heavy_full (K : ℕ) (hK : 0 < K) (T C : ℕ → ENNReal) (θ : ENNReal)
    (hfin : ∑ k ∈ Finset.range K, T k ≠ ⊤)
    (hcond : 2 * θ * ∑ k ∈ Finset.range K, C k ≤ ∑ k ∈ Finset.range K, T k) :
    ∃ k ∈ Finset.range K, ∑ j ∈ Finset.range K, T j ≤ 2 * K * T k ∧ θ * C k ≤ T k := by
  classical
  set S := ∑ k ∈ Finset.range K, T k with hS
  have hK0 : (K : ENNReal) ≠ 0 := by exact_mod_cast hK.ne'
  have hKtop : (K : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top K
  have h2K0 : (2 * (K : ENNReal)) ≠ 0 := mul_ne_zero two_ne_zero hK0
  have h2Ktop : (2 * (K : ENNReal)) ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofNat_ne_top hKtop
  by_cases hS0 : S = 0
  · refine ⟨0, Finset.mem_range.2 hK, ?_, ?_⟩
    · rw [hS0]; exact zero_le
    · have h1 : T 0 = 0 := (Finset.sum_eq_zero_iff.1 hS0) 0 (Finset.mem_range.2 hK)
      have h2 : θ * C 0 ≤ 0 := by
        calc θ * C 0 ≤ θ * ∑ k ∈ Finset.range K, C k := by
              gcongr
              exact Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_range.2 hK)
          _ ≤ 2 * θ * ∑ k ∈ Finset.range K, C k := by
              rw [mul_assoc]
              exact le_mul_of_one_le_left zero_le (by norm_num)
          _ ≤ S := hcond
          _ = 0 := hS0
      rw [h1]; exact h2
  · set H := (Finset.range K).filter (fun k => S ≤ 2 * K * T k) with hH
    have hlight : ∀ k ∈ Finset.range K, k ∉ H → T k ≤ S / (2 * K) := by
      intro k hk hkH
      have hnot : ¬ S ≤ 2 * K * T k := fun h => hkH (Finset.mem_filter.2 ⟨hk, h⟩)
      rw [ENNReal.le_div_iff_mul_le (Or.inl h2K0) (Or.inl h2Ktop), mul_comm]
      exact (not_le.1 hnot).le
    have hsumlight : ∑ k ∈ (Finset.range K).filter (fun k => k ∉ H), T k ≤ S / 2 := by
      calc ∑ k ∈ (Finset.range K).filter (fun k => k ∉ H), T k
          ≤ ∑ k ∈ (Finset.range K).filter (fun k => k ∉ H), S / (2 * K) :=
            Finset.sum_le_sum fun k hk =>
              hlight k (Finset.mem_filter.1 hk).1 (Finset.mem_filter.1 hk).2
        _ = (((Finset.range K).filter (fun k => k ∉ H)).card : ENNReal) * (S / (2 * K)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (K : ENNReal) * (S / (2 * K)) := by
            gcongr
            exact_mod_cast (Finset.card_le_card (Finset.filter_subset _ _)).trans
              (by simp)
        _ = S / 2 := by
            rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl two_ne_zero)
              (Or.inl ENNReal.ofNat_ne_top), ← mul_assoc, ← mul_assoc, mul_comm (K : ENNReal),
              mul_assoc (2⁻¹ : ENNReal), ENNReal.mul_inv_cancel hK0 hKtop, mul_one]
    have hsplit : S = ∑ k ∈ H, T k + ∑ k ∈ (Finset.range K).filter (fun k => k ∉ H), T k := by
      have h := (Finset.sum_filter_add_sum_filter_not (Finset.range K) (fun k => k ∈ H) T).symm
      rw [hS, h]
      congr 1
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext k
      simp only [Finset.mem_filter, hH, Finset.mem_range]
      constructor
      · rintro ⟨hk, -, h⟩; exact ⟨hk, h⟩
      · rintro ⟨hk, h⟩; exact ⟨hk, hk, h⟩
    have hheavy : S / 2 ≤ ∑ k ∈ H, T k := by
      have h1 : S ≤ ∑ k ∈ H, T k + S / 2 := by
        calc S = ∑ k ∈ H, T k + ∑ k ∈ (Finset.range K).filter (fun k => k ∉ H), T k := hsplit
          _ ≤ ∑ k ∈ H, T k + S / 2 := by gcongr
      calc S / 2 = S - S / 2 := (ENNReal.sub_half hfin).symm
        _ ≤ ∑ k ∈ H, T k := tsub_le_iff_right.2 h1
    have hHne : H.Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      rw [h, Finset.sum_empty, le_zero_iff, ENNReal.div_eq_zero_iff] at hheavy
      rcases hheavy with h0 | h0
      · exact hS0 h0
      · exact ENNReal.ofNat_ne_top h0
    by_contra hcon
    have hcon' : ∀ k ∈ H, T k < θ * C k := by
      intro k hk
      by_contra hle
      exact hcon ⟨k, (Finset.mem_filter.1 hk).1, (Finset.mem_filter.1 hk).2, not_lt.1 hle⟩
    have hlt : ∑ k ∈ H, T k < ∑ k ∈ H, θ * C k :=
      ENNReal.sum_lt_sum_of_nonempty hHne hcon'
    have hup : ∑ k ∈ H, θ * C k ≤ S / 2 := by
      calc ∑ k ∈ H, θ * C k = θ * ∑ k ∈ H, C k := by rw [Finset.mul_sum]
        _ ≤ θ * ∑ k ∈ Finset.range K, C k := by
            gcongr
            exact Finset.filter_subset _ _
        _ ≤ S / 2 := by
            rw [ENNReal.le_div_iff_mul_le (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top)]
            calc (θ * ∑ k ∈ Finset.range K, C k) * 2 = 2 * θ * ∑ k ∈ Finset.range K, C k := by
                  ring
              _ ≤ S := hcond
    exact absurd (lt_of_le_of_lt hheavy hlt) (not_lt.2 hup)

/-! ### Sums over the fibres -/

namespace CoverData

variable {cfg : VeryNotSticky.{u}} {bι : Type u} (cd : CoverData cfg bι)

open scoped Classical in
/-- The fibres of the net partition the index set of the piece. -/
theorem idx_eq_biUnion_fib (B : bι) : cd.idx B = (cd.net B).net.biUnion (cd.fib B) := by
  ext i
  simp only [Finset.mem_biUnion]
  constructor
  · intro hi
    exact (cd.net B).exists_mem_fibre hi
  · rintro ⟨ν, -, hi⟩
    exact cd.fib_subset_idx B ν hi

open scoped Classical in
/-- A sum over the index set of a piece is the sum over the net of the fibre sums. -/
theorem sum_idx_eq_sum_net_fib (B : bι) (g : cfg.ι → ENNReal) :
    ∑ i ∈ cd.idx B, g i = ∑ ν ∈ (cd.net B).net, ∑ i ∈ cd.fib B ν, g i := by
  calc ∑ i ∈ cd.idx B, g i = ∑ i ∈ (cd.net B).net.biUnion (cd.fib B), g i :=
        Finset.sum_congr (cd.idx_eq_biUnion_fib B) fun _ _ => rfl
    _ = ∑ ν ∈ (cd.net B).net, ∑ i ∈ cd.fib B ν, g i :=
        Finset.sum_biUnion (cd.net B).fibre_disjoint

open scoped Classical in
/-- A sum over `cfg.s` of a function vanishing off the index set of the piece. -/
theorem sum_s_eq_sum_net_fib (B : bι) (g : cfg.ι → ENNReal)
    (hg : ∀ i ∈ cfg.s, i ∉ cd.idx B → g i = 0) :
    ∑ i ∈ cfg.s, g i = ∑ ν ∈ (cd.net B).net, ∑ i ∈ cd.fib B ν, g i := by
  rw [← cd.sum_idx_eq_sum_net_fib B g]
  exact (Finset.sum_subset (cd.idx_subset B) fun i hi hni => hg i hi hni).symm

open scoped Classical in
/-- The working shading of `i` at level `m` has the volume of its pieces summed. -/
theorem volume_Yg (m : ℕ) (i : cfg.ι) :
    volume (cd.Yg m i) = ∑ B ∈ cd.bs, volume (cd.trunc B ((cd.net B).assign i) m i) := by
  unfold Yg
  refine measure_biUnion_finset ?_ fun B _ => cd.measurableSet_trunc B _ m i
  intro B hB B' hB' hne
  rw [Finset.mem_coe] at hB hB'
  exact Set.disjoint_of_subset (cd.trunc_subset_P B _ m i) (cd.trunc_subset_P B' _ m i)
    (cd.Pdisj hB hB' hne)

open scoped Classical in
/-- The total working mass at level `m`, as a sum over balls, net points and fibre members. -/
theorem sum_volume_Yg (m : ℕ) :
    ∑ i ∈ cfg.s, volume (cd.Yg m i) =
      ∑ B ∈ cd.bs, ∑ ν ∈ (cd.net B).net, ∑ i ∈ cd.fib B ν, volume (cd.trunc B ν m i) := by
  simp_rw [cd.volume_Yg m]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun B _ => ?_
  rw [cd.sum_s_eq_sum_net_fib B (fun i => volume (cd.trunc B ((cd.net B).assign i) m i))]
  · refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun i hi => ?_
    rw [(cd.mem_fib_iff.1 hi).2]
  · intro i _ hi
    have h : i ∉ cd.fib B ((cd.net B).assign i) := fun h => hi (cd.fib_subset_idx B _ h)
    rw [cd.trunc_eq_empty_of_not_mem m h, measure_empty]

/-- The shading of a tube is the disjoint union of its pieces. -/
theorem volume_shade_eq_sum (i : cfg.ι) (hi : i ∈ cfg.s) :
    volume (cfg.T i).shade = ∑ B ∈ cd.bs, volume (cd.S B i) := by
  have hcov : (cfg.T i).shade = ⋃ B ∈ cd.bs, cd.S B i := by
    ext x
    simp only [S, Set.mem_iUnion, Set.mem_inter_iff, exists_prop]
    constructor
    · intro hx
      obtain ⟨B, hB, hxB⟩ := Set.mem_iUnion₂.1 (cd.Pcov i hi hx)
      exact ⟨B, hB, hx, hxB⟩
    · rintro ⟨B, -, hx, -⟩; exact hx
  rw [hcov]
  refine measure_biUnion_finset ?_ fun B _ => cd.measurableSet_S B i
  intro B hB B' hB' hne
  rw [Finset.mem_coe] at hB hB'
  exact Set.disjoint_of_subset (cd.S_subset_P B i) (cd.S_subset_P B' i) (cd.Pdisj hB hB' hne)

open scoped Classical in
/-- The total shading mass, as a sum over balls, net points and fibre members. -/
theorem sum_volume_shade_eq :
    ∑ i ∈ cfg.s, volume (cfg.T i).shade =
      ∑ B ∈ cd.bs, ∑ ν ∈ (cd.net B).net, ∑ i ∈ cd.fib B ν, volume (cd.S B i) := by
  rw [Finset.sum_congr rfl fun i hi => cd.volume_shade_eq_sum i hi, Finset.sum_comm]
  refine Finset.sum_congr rfl fun B _ => ?_
  rw [cd.sum_s_eq_sum_net_fib B (fun i => volume (cd.S B i))]
  intro i hi hni
  rw [cd.S_eq_empty_of_not_mem_idx hi hni, measure_empty]


end CoverData

/-! ### Bins beyond the fibre size are empty -/

open scoped Classical in
theorem levelBin_eq_empty_of_card_lt {ι : Type*} (F : Finset ι) (S : ι → Set E3) (P : Set E3)
    {m : ℕ} (h : F.card < m) : levelBin F S P m = ∅ := by
  ext x
  simp only [levelBin, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro _ hm
  exact absurd hm (not_le.2 (lt_of_le_of_lt (Finset.card_filter_le _ _) h))

/-- The number of dyadic levels: `⌊log₂ #𝕋⌋ + 1`. -/
def numLevels (cfg : VeryNotSticky.{u}) : ℕ := Nat.log 2 cfg.s.card + 1

theorem numLevels_pos (cfg : VeryNotSticky.{u}) : 0 < numLevels cfg := Nat.succ_pos _

namespace CoverData

variable {cfg : VeryNotSticky.{u}} {bι : Type u} (cd : CoverData cfg bι)

open scoped Classical in
/-- The working mass at level `2^k`. -/
noncomputable def levelMass (k : ℕ) : ENNReal :=
  ∑ B ∈ cd.bs, ∑ ν ∈ (cd.net B).net, ∑ i ∈ cd.fib B ν, volume (cd.trunc B ν (2 ^ k) i)

open scoped Classical in
/-- The level-weighted carrier mass at level `2^k`: `2^k` times the capsules with a nonempty bin. -/
noncomputable def levelCarrier (k : ℕ) : ENNReal :=
  ∑ B ∈ cd.bs, ∑ ν ∈ (cd.net B).net with (cd.bin B ν (2 ^ k)).Nonempty,
    ((2 ^ k : ℕ) : ENNReal) * volume (cd.caps B ν)

open scoped Classical in
theorem sum_volume_Yg_eq_levelMass (k : ℕ) :
    ∑ i ∈ cfg.s, volume (cd.Yg (2 ^ k) i) = cd.levelMass k := cd.sum_volume_Yg (2 ^ k)

open scoped Classical in
theorem numLevels_ge (B : bι) (ν : cfg.ι) :
    Nat.log 2 (cd.fib B ν).card + 1 ≤ numLevels cfg :=
  Nat.succ_le_succ (Nat.log_mono_right (Finset.card_le_card (cd.fib_subset_s B ν)))

open scoped Classical in
/-- The shading pieces of a fibre are dominated by twice the level masses of the fibre. -/
theorem sum_S_fib_le (B : bι) (ν : cfg.ι) :
    ∑ i ∈ cd.fib B ν, volume (cd.S B i) ≤
      2 * ∑ k ∈ Finset.range (numLevels cfg),
        ∑ i ∈ cd.fib B ν, volume (cd.trunc B ν (2 ^ k) i) := by
  letI := indexOrder cfg
  have hdecomp : ∀ i ∈ cd.fib B ν, volume (cd.S B i) =
      ∑ k ∈ Finset.range (numLevels cfg), volume (cd.S B i ∩ cd.bin B ν (2 ^ k)) := by
    intro i hi
    have h1 : volume (cd.S B i) = volume (cd.S B i ∩ cd.P B) := by
      rw [Set.inter_eq_left.2 (cd.S_subset_P B i)]
    rw [h1, volume_inter_eq_sum_levelBin (cd.fib B ν) (cd.S B) (fun j _ => cd.measurableSet_S B j)
      (cd.Pmeas B) hi]
    refine Finset.sum_subset (Finset.range_mono (cd.numLevels_ge B ν)) ?_
    intro k hk hk'
    rw [Finset.mem_range, not_lt] at hk'
    have hcard : (cd.fib B ν).card < 2 ^ k :=
      lt_of_lt_of_le (Nat.lt_pow_succ_log_self one_lt_two _) (Nat.pow_le_pow_right two_pos hk')
    rw [levelBin_eq_empty_of_card_lt _ _ _ hcard, Set.inter_empty, measure_empty]
  rw [Finset.sum_congr rfl hdecomp, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  exact sum_volume_inter_levelBin_le_two_mul (cd.fib B ν) (cd.S B)
    (fun j _ => cd.measurableSet_S B j) (cd.Pmeas B) (2 ^ k)

open scoped Classical in
/-- The total shading mass is at most twice the sum of the level masses. -/
theorem sum_volume_shade_le :
    ∑ i ∈ cfg.s, volume (cfg.T i).shade ≤
      2 * ∑ k ∈ Finset.range (numLevels cfg), cd.levelMass k := by
  rw [cd.sum_volume_shade_eq]
  unfold levelMass
  have key : ∀ B ∈ cd.bs, ∑ ν ∈ (cd.net B).net, ∑ i ∈ cd.fib B ν, volume (cd.S B i) ≤
      ∑ k ∈ Finset.range (numLevels cfg), ∑ ν ∈ (cd.net B).net,
        2 * ∑ i ∈ cd.fib B ν, volume (cd.trunc B ν (2 ^ k) i) := by
    intro B _
    calc ∑ ν ∈ (cd.net B).net, ∑ i ∈ cd.fib B ν, volume (cd.S B i)
        ≤ ∑ ν ∈ (cd.net B).net, 2 * ∑ k ∈ Finset.range (numLevels cfg),
            ∑ i ∈ cd.fib B ν, volume (cd.trunc B ν (2 ^ k) i) :=
          Finset.sum_le_sum fun ν _ => cd.sum_S_fib_le B ν
      _ = ∑ ν ∈ (cd.net B).net, ∑ k ∈ Finset.range (numLevels cfg),
            2 * ∑ i ∈ cd.fib B ν, volume (cd.trunc B ν (2 ^ k) i) :=
          Finset.sum_congr rfl fun ν _ => Finset.mul_sum _ _ _
      _ = ∑ k ∈ Finset.range (numLevels cfg), ∑ ν ∈ (cd.net B).net,
            2 * ∑ i ∈ cd.fib B ν, volume (cd.trunc B ν (2 ^ k) i) := Finset.sum_comm
  calc ∑ B ∈ cd.bs, ∑ ν ∈ (cd.net B).net, ∑ i ∈ cd.fib B ν, volume (cd.S B i)
      ≤ ∑ B ∈ cd.bs, ∑ k ∈ Finset.range (numLevels cfg), ∑ ν ∈ (cd.net B).net,
          2 * ∑ i ∈ cd.fib B ν, volume (cd.trunc B ν (2 ^ k) i) := Finset.sum_le_sum key
    _ = ∑ k ∈ Finset.range (numLevels cfg), ∑ B ∈ cd.bs, ∑ ν ∈ (cd.net B).net,
          2 * ∑ i ∈ cd.fib B ν, volume (cd.trunc B ν (2 ^ k) i) := Finset.sum_comm
    _ = 2 * ∑ k ∈ Finset.range (numLevels cfg), ∑ B ∈ cd.bs, ∑ ν ∈ (cd.net B).net,
          ∑ i ∈ cd.fib B ν, volume (cd.trunc B ν (2 ^ k) i) := by
        simp only [Finset.mul_sum]

open scoped Classical in
/-- The level mass, as `2^k` times the bin volumes. -/
theorem levelMass_eq (k : ℕ) :
    cd.levelMass k = ∑ B ∈ cd.bs, ∑ ν ∈ (cd.net B).net,
      ((2 ^ k : ℕ) : ENNReal) * volume (cd.bin B ν (2 ^ k)) := by
  letI := indexOrder cfg
  unfold levelMass
  refine Finset.sum_congr rfl fun B _ => Finset.sum_congr rfl fun ν _ => ?_
  exact sum_volume_truncated (cd.fib B ν) (cd.S B) (fun j _ => cd.measurableSet_S B j)
    (cd.Pmeas B) (2 ^ k)

open scoped Classical in
/-- A nonempty level-`2^k` bin forces `2^k ≤ #fibre`. -/
theorem pow_le_card_fib_of_bin_nonempty {B : bι} {ν : cfg.ι} {k : ℕ}
    (h : (cd.bin B ν (2 ^ k)).Nonempty) : 2 ^ k ≤ (cd.fib B ν).card := by
  obtain ⟨x, hx⟩ := h
  exact le_trans hx.2.1 (Finset.card_filter_le _ _)

/-- The geometric sum: `∑_{k < K, 2^k ≤ n} 2^k ≤ 2 n`. -/
theorem sum_pow_two_filter_le (K n : ℕ) :
    ∑ k ∈ (Finset.range K).filter (fun k => 2 ^ k ≤ n), 2 ^ k ≤ 2 * n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h : (Finset.range K).filter (fun k => 2 ^ k ≤ 0) = ∅ := by
      ext k; simp
    rw [h, Finset.sum_empty]
    exact Nat.zero_le _
  · calc ∑ k ∈ (Finset.range K).filter (fun k => 2 ^ k ≤ n), 2 ^ k
        ≤ ∑ k ∈ Finset.range (Nat.log 2 n + 1), 2 ^ k := by
          refine Finset.sum_le_sum_of_subset ?_
          intro k hk
          rw [Finset.mem_filter] at hk
          rw [Finset.mem_range, Nat.lt_succ_iff]
          exact Nat.le_log_of_pow_le one_lt_two hk.2
      _ = 2 ^ (Nat.log 2 n + 1) - 1 := by
          rw [Nat.geomSum_eq (le_refl 2)]; simp
      _ ≤ 2 * n := by
          have := Nat.pow_log_le_self 2 hn.ne'
          rw [pow_succ]
          omega

open scoped Classical in
/-- The level-weighted carriers summed over the levels: at most twice the fibre-weighted
capsule volumes. -/
theorem sum_levelCarrier_le :
    ∑ k ∈ Finset.range (numLevels cfg), cd.levelCarrier k ≤
      2 * ∑ B ∈ cd.bs, ∑ ν ∈ (cd.net B).net,
        ((cd.fib B ν).card : ENNReal) * volume (cd.caps B ν) := by
  unfold levelCarrier
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun B _ => ?_
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun ν _ => ?_
  have hsum : ∑ k ∈ Finset.range (numLevels cfg),
      (if (cd.bin B ν (2 ^ k)).Nonempty then ((2 ^ k : ℕ) : ENNReal) * volume (cd.caps B ν) else 0)
      = ((∑ k ∈ (Finset.range (numLevels cfg)).filter (fun k => (cd.bin B ν (2 ^ k)).Nonempty),
          2 ^ k : ℕ) : ENNReal) * volume (cd.caps B ν) := by
    rw [← Finset.sum_filter, Nat.cast_sum, Finset.sum_mul]
  rw [hsum]
  have h1 : ∑ k ∈ (Finset.range (numLevels cfg)).filter (fun k => (cd.bin B ν (2 ^ k)).Nonempty),
      2 ^ k ≤ ∑ k ∈ (Finset.range (numLevels cfg)).filter (fun k => 2 ^ k ≤ (cd.fib B ν).card),
      2 ^ k := by
    refine Finset.sum_le_sum_of_subset ?_
    intro k hk
    rw [Finset.mem_filter] at hk ⊢
    exact ⟨hk.1, cd.pow_le_card_fib_of_bin_nonempty hk.2⟩
  have h2 := sum_pow_two_filter_le (numLevels cfg) (cd.fib B ν).card
  have h3 : ((∑ k ∈ (Finset.range (numLevels cfg)).filter
      (fun k => (cd.bin B ν (2 ^ k)).Nonempty), 2 ^ k : ℕ) : ENNReal) ≤
      ((2 * (cd.fib B ν).card : ℕ) : ENNReal) := by exact_mod_cast h1.trans h2
  calc ((∑ k ∈ (Finset.range (numLevels cfg)).filter
        (fun k => (cd.bin B ν (2 ^ k)).Nonempty), 2 ^ k : ℕ) : ENNReal) * volume (cd.caps B ν)
      ≤ ((2 * (cd.fib B ν).card : ℕ) : ENNReal) * volume (cd.caps B ν) :=
        mul_le_mul' h3 le_rfl
    _ = 2 * (((cd.fib B ν).card : ENNReal) * volume (cd.caps B ν)) := by
        push_cast; ring


/-! ### The capsule against T3's segment of a fibre member -/

theorem lt_volume_convexHull_c_three :
    ((Metric.lt_volume_convexHull.c 3 : NNReal) : ℝ) = 1 / 6 := by
  simp [Metric.lt_volume_convexHull.c, Nat.factorial]

/-- `|caps ν| ≤ 384 · |seg_T3(i)|` for any tube `i` (both are windows of half-length `r₁/4`:
radius `2δ` against radius `δ`; `16 r₁ δ²` against `r₁ δ² / 24`). -/
theorem volume_caps_le (B : bι) (ν i : cfg.ι) :
    volume (cd.caps B ν) ≤
      384 * volume (segCarrierSet (cfg.T i).toTube (cd.ctr B) ((cfg.r₁ : ℝ) / 4)) := by
  have hδ0 : (0 : ℝ) ≤ (cfg.δ : ℝ) := (cfg.δ).coe_nonneg
  have hr0 : (0 : ℝ) ≤ (cfg.r₁ : ℝ) := (cfg.r₁).coe_nonneg
  have hr1 := r₁_le_one cfg
  have hup : volume (cd.caps B ν) ≤
      4 * ENNReal.ofReal (4 * capL cfg) * ((capρ cfg : NNReal) : ENNReal) ^ 2 :=
    volume_segCarrierSet_le_four_mul (centredTube (cfg.T ν).toTube (cd.ctr B) (capρ cfg))
      (cd.ctr B) (capL_nonneg cfg) cd.capρ_le_capL
  have hlo := ofReal_le_volume_segCarrierSet (cfg.T i).toTube (cd.ctr B)
    (by positivity : (0 : ℝ) ≤ (cfg.r₁ : ℝ) / 4) (by linarith)
  refine hup.trans (le_trans ?_ (mul_le_mul' (le_refl (384 : ENNReal)) hlo))
  rw [lt_volume_convexHull_c_three]
  have hL0 := capL_nonneg cfg
  have h44L : (0 : ℝ) ≤ 4 * (4 * capL cfg) := by positivity
  have e1 : ENNReal.ofReal (4 * (4 * capL cfg) * ((capρ cfg : NNReal) : ℝ) ^ 2) =
      (4 : ENNReal) * ENNReal.ofReal (4 * capL cfg) * ((capρ cfg : NNReal) : ENNReal) ^ 2 := by
    rw [ENNReal.ofReal_mul (p := 4 * (4 * capL cfg)) (q := ((capρ cfg : NNReal) : ℝ) ^ 2) h44L,
      ENNReal.ofReal_mul (p := 4) (q := 4 * capL cfg) (by norm_num), ENNReal.ofReal_ofNat,
      ENNReal.ofReal_pow (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal]
  have e2 : ENNReal.ofReal (384 * (1 / 6 * ((cfg.r₁ : ℝ) / 4 * (cfg.δ : ℝ) * (cfg.δ : ℝ)))) =
      (384 : ENNReal) *
        ENNReal.ofReal (1 / 6 * ((cfg.r₁ : ℝ) / 4 * (cfg.δ : ℝ) * (cfg.δ : ℝ))) := by
    rw [ENNReal.ofReal_mul (p := 384) (q := 1 / 6 * ((cfg.r₁ : ℝ) / 4 * (cfg.δ : ℝ) * (cfg.δ : ℝ)))
      (by norm_num), ENNReal.ofReal_ofNat]
  rw [← e1, ← e2]
  apply ENNReal.ofReal_le_ofReal
  rw [coe_capρ]
  unfold capL
  exact le_of_eq (by ring)

open scoped Classical in
/-- The fibre-weighted capsule volumes against T3's segment carriers of the cover. -/
theorem sum_card_fib_mul_caps_le :
    ∑ B ∈ cd.bs, ∑ ν ∈ (cd.net B).net, ((cd.fib B ν).card : ENNReal) * volume (cd.caps B ν) ≤
      384 * ∑ B ∈ cd.bs, ∑ p ∈ segsOfCover cfg cd.P B,
        volume (segBodyOfCover cfg cd.ctr cd.P cd.Pmeas p).carrier := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun B _ => ?_
  have hseg : ∑ p ∈ segsOfCover cfg cd.P B,
      volume (segBodyOfCover cfg cd.ctr cd.P cd.Pmeas p).carrier =
      ∑ i ∈ cd.idx B, volume (segCarrierSet (cfg.T i).toTube (cd.ctr B) ((cfg.r₁ : ℝ) / 4)) := by
    unfold segsOfCover
    rw [Finset.sum_image (fun i _ j _ h => (Prod.mk.inj h).1)]
    rfl
  rw [hseg, cd.sum_idx_eq_sum_net_fib B, Finset.mul_sum]
  refine Finset.sum_le_sum fun ν _ => ?_
  rw [Finset.mul_sum]
  calc ((cd.fib B ν).card : ENNReal) * volume (cd.caps B ν)
      = ∑ _i ∈ cd.fib B ν, volume (cd.caps B ν) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ i ∈ cd.fib B ν,
          384 * volume (segCarrierSet (cfg.T i).toTube (cd.ctr B) ((cfg.r₁ : ℝ) / 4)) :=
        Finset.sum_le_sum fun i _ => cd.volume_caps_le B ν i

/-! ### The pigeonhole's hypothesis, from T3's fullness -/

open scoped Classical in
/-- `2 θ ∑_k Cw_k ≤ ∑_k T_k` at `θ = 4 c₁ δ^{2η}`, from T3's global fullness at `3072 c₁`. -/
theorem two_mul_theta_sum_levelCarrier_le {c₁ : NNReal}
    (hc₁ : 4 * (3072 * c₁) * (ballCoverConstant : NNReal) ≤ 1) :
    2 * (4 * ((c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η))) *
        ∑ k ∈ Finset.range (numLevels cfg), cd.levelCarrier k ≤
      ∑ k ∈ Finset.range (numLevels cfg), cd.levelMass k := by
  have hfull := segs_fullness_of_cover cfg cd.Pmeas cd.δ_le cd.Pball16 cd.Pdisj cd.Pcov cd.overlap
    hc₁
  have hshade := sum_sum_segShade_eq cfg cd.Pmeas cd.δ_le cd.Pball16 cd.Pdisj cd.Pcov
  have h1 : ∑ k ∈ Finset.range (numLevels cfg), cd.levelCarrier k ≤
      2 * (384 * ∑ B ∈ cd.bs, ∑ p ∈ segsOfCover cfg cd.P B,
        volume (segBodyOfCover cfg cd.ctr cd.P cd.Pmeas p).carrier) :=
    cd.sum_levelCarrier_le.trans (by gcongr; exact cd.sum_card_fib_mul_caps_le)
  have h2 := cd.sum_volume_shade_le
  have h3 : (12288 : ENNReal) * ((c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η)) *
      ∑ B ∈ cd.bs, ∑ p ∈ segsOfCover cfg cd.P B,
        volume (segBodyOfCover cfg cd.ctr cd.P cd.Pmeas p).carrier ≤
      2 * ∑ k ∈ Finset.range (numLevels cfg), cd.levelMass k := by
    calc (12288 : ENNReal) * ((c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η)) *
          ∑ B ∈ cd.bs, ∑ p ∈ segsOfCover cfg cd.P B,
            volume (segBodyOfCover cfg cd.ctr cd.P cd.Pmeas p).carrier
        = 4 * (((3072 * c₁ : NNReal) : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η)) *
          ∑ B ∈ cd.bs, ∑ p ∈ segsOfCover cfg cd.P B,
            volume (segBodyOfCover cfg cd.ctr cd.P cd.Pmeas p).carrier := by
          push_cast; ring
      _ ≤ ∑ B ∈ cd.bs, ∑ p ∈ segsOfCover cfg cd.P B,
            volume (segBodyOfCover cfg cd.ctr cd.P cd.Pmeas p).shade := hfull
      _ = ∑ i ∈ cfg.s, volume (cfg.T i).shade := hshade
      _ ≤ 2 * ∑ k ∈ Finset.range (numLevels cfg), cd.levelMass k := h2
  have h4 : (6144 : ENNReal) * ((c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η)) *
      ∑ B ∈ cd.bs, ∑ p ∈ segsOfCover cfg cd.P B,
        volume (segBodyOfCover cfg cd.ctr cd.P cd.Pmeas p).carrier ≤
      ∑ k ∈ Finset.range (numLevels cfg), cd.levelMass k := by
    refine (ENNReal.mul_le_mul_iff_right (a := 2) two_ne_zero ENNReal.ofNat_ne_top).1 ?_
    calc (2 : ENNReal) * ((6144 : ENNReal) * ((c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η)) *
          ∑ B ∈ cd.bs, ∑ p ∈ segsOfCover cfg cd.P B,
            volume (segBodyOfCover cfg cd.ctr cd.P cd.Pmeas p).carrier)
        = (12288 : ENNReal) * ((c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η)) *
          ∑ B ∈ cd.bs, ∑ p ∈ segsOfCover cfg cd.P B,
            volume (segBodyOfCover cfg cd.ctr cd.P cd.Pmeas p).carrier := by ring
      _ ≤ _ := h3
  calc 2 * (4 * ((c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η))) *
        ∑ k ∈ Finset.range (numLevels cfg), cd.levelCarrier k
      ≤ 2 * (4 * ((c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η))) *
        (2 * (384 * ∑ B ∈ cd.bs, ∑ p ∈ segsOfCover cfg cd.P B,
          volume (segBodyOfCover cfg cd.ctr cd.P cd.Pmeas p).carrier)) := by gcongr
    _ = (6144 : ENNReal) * ((c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η)) *
        ∑ B ∈ cd.bs, ∑ p ∈ segsOfCover cfg cd.P B,
          volume (segBodyOfCover cfg cd.ctr cd.P cd.Pmeas p).carrier := by ring
    _ ≤ ∑ k ∈ Finset.range (numLevels cfg), cd.levelMass k := h4

/-! ### The level's segments, summed -/

open scoped Classical in
/-- A sum over the level's balls and segments is a sum over the net points with a nonempty bin. -/
theorem sum_bs'_segs (m : ℕ) (f : cfg.ι × bι → ENNReal) :
    ∑ B ∈ cd.bs' m, ∑ p ∈ cd.segs m B, f p =
      ∑ B ∈ cd.bs, ∑ ν ∈ (cd.net B).net with (cd.bin B ν m).Nonempty, f (ν, B) := by
  have h1 : ∑ B ∈ cd.bs' m, ∑ p ∈ cd.segs m B, f p = ∑ B ∈ cd.bs, ∑ p ∈ cd.segs m B, f p := by
    refine Finset.sum_subset (cd.bs'_subset m) fun B hB hB' => ?_
    have hempty : cd.segs m B = ∅ := by
      by_contra h
      exact hB' (cd.mem_bs'.2 ⟨hB, Finset.nonempty_iff_ne_empty.2 h⟩)
    rw [hempty, Finset.sum_empty]
  rw [h1]
  refine Finset.sum_congr rfl fun B _ => ?_
  unfold segs
  rw [Finset.sum_image (fun i _ j _ h => (Prod.mk.inj h).1)]

open scoped Classical in
theorem levelCarrier_eq_pow_mul (k : ℕ) :
    cd.levelCarrier k = ((2 ^ k : ℕ) : ENNReal) *
      ∑ B ∈ cd.bs' (2 ^ k), ∑ p ∈ cd.segs (2 ^ k) B, volume (cd.Y (2 ^ k) p).carrier := by
  rw [cd.sum_bs'_segs (2 ^ k) (fun p => volume (cd.Y (2 ^ k) p).carrier)]
  unfold levelCarrier
  simp only [Finset.mul_sum, Y_carrier]

open scoped Classical in
theorem levelMass_eq_pow_mul (k : ℕ) :
    cd.levelMass k = ((2 ^ k : ℕ) : ENNReal) *
      ∑ B ∈ cd.bs' (2 ^ k), ∑ p ∈ cd.segs (2 ^ k) B, volume (cd.Y (2 ^ k) p).shade := by
  rw [cd.sum_bs'_segs (2 ^ k) (fun p => volume (cd.Y (2 ^ k) p).shade), cd.levelMass_eq k]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun B hB => ?_
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun ν _ => ?_
  split_ifs with h
  · rw [cd.Y_shade_eq_bin (pow_pos two_pos k) hB]
  · rw [Set.not_nonempty_iff_eq_empty.1 h, measure_empty, mul_zero]

theorem s_nonempty (cd : CoverData cfg bι) : cfg.s.Nonempty := by
  obtain ⟨B, hB⟩ := cd.bs_nonempty
  obtain ⟨x, -, hxs⟩ := cd.Pne B hB
  obtain ⟨i, hi, -⟩ := Set.mem_iUnion₂.mp hxs
  exact ⟨i, hi⟩

theorem sum_volume_shade_ne_top' (cfg : VeryNotSticky.{u}) :
    ∑ i ∈ cfg.s, volume (cfg.T i).shade ≠ ⊤ := by
  refine ne_top_of_le_ne_top (sum_volume_carrier_ne_top cfg) ?_
  exact Finset.sum_le_sum fun i _ => measure_mono (cfg.T i).shade_subset

open scoped Classical in
theorem levelMass_le (k : ℕ) : cd.levelMass k ≤ ∑ i ∈ cfg.s, volume (cfg.T i).shade := by
  rw [← cd.sum_volume_Yg_eq_levelMass k]
  exact Finset.sum_le_sum fun i _ => measure_mono (cd.Yg_subset_shade _ i)

open scoped Classical in
/-- **The good level** (refined l.3735–3743, made two-sided): a dyadic level `2^k` whose balls are
nonempty, whose working shading keeps `(4 · numLevels)⁻¹` of the shading mass, and whose segments
are full at the Markov threshold `4 c₁ δ^{2η}` — under T3's density floor at `3072 c₁`. -/
theorem exists_good_level {c₁ : NNReal}
    (hc₁ : 4 * (3072 * c₁) * (ballCoverConstant : NNReal) ≤ 1) :
    ∃ k ∈ Finset.range (numLevels cfg),
      (cd.bs' (2 ^ k)).Nonempty ∧
      ((4 * (numLevels cfg : NNReal) : NNReal) : ENNReal)⁻¹ * ∑ i ∈ cfg.s, volume (cfg.T i).shade ≤
        ∑ i ∈ cfg.s, volume (cd.Yg (2 ^ k) i) ∧
      4 * ((c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η)) *
          ∑ B ∈ cd.bs' (2 ^ k), ∑ p ∈ cd.segs (2 ^ k) B, volume (cd.Y (2 ^ k) p).carrier ≤
        ∑ B ∈ cd.bs' (2 ^ k), ∑ p ∈ cd.segs (2 ^ k) B, volume (cd.Y (2 ^ k) p).shade ∧
      ∑ B ∈ cd.bs' (2 ^ k), ∑ p ∈ cd.segs (2 ^ k) B, volume (cd.Y (2 ^ k) p).shade ≠ 0 := by
  have hshade_pos : 0 < ∑ i ∈ cfg.s, volume (cfg.T i).shade :=
    sum_volume_shade_pos_of_nonempty cfg cd.s_nonempty
  have hfin : ∑ k ∈ Finset.range (numLevels cfg), cd.levelMass k ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top (numLevels cfg))
      (sum_volume_shade_ne_top' cfg)) ?_
    calc ∑ k ∈ Finset.range (numLevels cfg), cd.levelMass k
        ≤ ∑ _k ∈ Finset.range (numLevels cfg), ∑ i ∈ cfg.s, volume (cfg.T i).shade :=
          Finset.sum_le_sum fun k _ => cd.levelMass_le k
      _ = (numLevels cfg : ENNReal) * ∑ i ∈ cfg.s, volume (cfg.T i).shade := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  obtain ⟨k, hk, ha, hb⟩ := exists_level_heavy_full (numLevels cfg) (numLevels_pos cfg)
    cd.levelMass cd.levelCarrier (4 * ((c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η))) hfin
    (cd.two_mul_theta_sum_levelCarrier_le hc₁)
  have hT := cd.sum_volume_Yg_eq_levelMass k
  have hTpos : cd.levelMass k ≠ 0 := by
    intro h0
    rw [h0, mul_zero, le_zero_iff] at ha
    have : ∑ i ∈ cfg.s, volume (cfg.T i).shade ≤ 0 := by
      calc ∑ i ∈ cfg.s, volume (cfg.T i).shade
          ≤ 2 * ∑ k ∈ Finset.range (numLevels cfg), cd.levelMass k := cd.sum_volume_shade_le
        _ = 0 := by rw [ha, mul_zero]
    exact hshade_pos.ne' (le_zero_iff.1 this)
  refine ⟨k, hk, ?_, ?_, ?_, ?_⟩
  · obtain ⟨B, hB, hB0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hTpos
    obtain ⟨ν, hν, hν0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hB0
    obtain ⟨i, hi, hi0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hν0
    have hne : (cd.trunc B ν (2 ^ k) i).Nonempty :=
      Set.nonempty_iff_ne_empty.2 fun h => hi0 (by rw [h, measure_empty])
    obtain ⟨x, hx⟩ := hne
    exact ⟨B, cd.mem_bs'.2 ⟨hB, ⟨_, cd.mem_segs_self hν ⟨x, cd.trunc_subset_bin B ν _ i hx⟩⟩⟩⟩
  · rw [hT]
    have h4K0 : ((4 * (numLevels cfg : NNReal) : NNReal) : ENNReal) ≠ 0 := by
      have : (0 : NNReal) < 4 * (numLevels cfg : NNReal) := by
        have := numLevels_pos cfg; positivity
      exact_mod_cast this.ne'
    rw [ENNReal.inv_mul_le_iff h4K0 ENNReal.coe_ne_top]
    calc ∑ i ∈ cfg.s, volume (cfg.T i).shade
        ≤ 2 * ∑ j ∈ Finset.range (numLevels cfg), cd.levelMass j := cd.sum_volume_shade_le
      _ ≤ 2 * (2 * (numLevels cfg : ENNReal) * cd.levelMass k) := by gcongr
      _ = ((4 * (numLevels cfg : NNReal) : NNReal) : ENNReal) * cd.levelMass k := by
          push_cast; ring
  · rw [cd.levelCarrier_eq_pow_mul k, cd.levelMass_eq_pow_mul k] at hb
    have h2k0 : ((2 ^ k : ℕ) : ENNReal) ≠ 0 := by exact_mod_cast (pow_pos two_pos k).ne'
    have h2kt : ((2 ^ k : ℕ) : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
    rw [← mul_assoc, mul_comm _ ((2 ^ k : ℕ) : ENNReal), mul_assoc] at hb
    exact (ENNReal.mul_le_mul_iff_right h2k0 h2kt).1 hb
  · intro h0
    apply hTpos
    rw [cd.levelMass_eq_pow_mul k, h0, mul_zero]

end CoverData

end Kakeya.VeryNotSticky
