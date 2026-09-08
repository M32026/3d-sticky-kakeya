/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFibreSupplyProducer
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCentredHandBack
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSiteClosure

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

universe u

noncomputable def sourceTowerRadius (delta : NNReal) (M k : Nat) : NNReal :=
  if k < M then (1 / 40) * delta ^ ((k : Real) / (M : Real)) else delta

structure SourceTowerMesh (N M1 Mc M : Nat) (etaOne : Real) (parent : Nat -> Real) : Prop where
  sticky_integer_pos : 0 < M1
  coarse_integer_pos : 0 < Mc
  count_pos : 1 <= N
  levels_ge_two : 2 <= M
  divisible : M1 * Mc ∣ M
  first_rung_pos : 0 < etaOne
  parent_pos : ∀ m, m < N -> 0 < parent m
  global_mesh : 512 * (N : Real) / etaOne <= (M : Real)
  all_parent_meshes : ∀ m, m < N -> 8 / parent m <= (M : Real)

theorem source_exists_fixed_tower_mesh {N M1 Mc : Nat} {etaOne : Real}
    {parent : Nat -> Real} (hN : 1 <= N) (hM1 : 0 < M1) (hMc : 0 < Mc)
    (heta : 0 < etaOne) (hparent : ∀ m, m < N -> 0 < parent m) :
    ∃ M : Nat, SourceTowerMesh N M1 Mc M etaOne parent := by
  classical
  let L := 2 + Nat.ceil (512 * (N : Real) / etaOne) +
    (Finset.range N).sup (fun m => Nat.ceil (8 / parent m))
  have hprod : 0 < M1 * Mc := Nat.mul_pos hM1 hMc
  have hLM : L <= M1 * Mc * L := Nat.le_mul_of_pos_left L hprod
  have hglobal : 512 * (N : Real) / etaOne <= (L : Real) := by
    refine (Nat.le_ceil _).trans ?_
    exact_mod_cast (show Nat.ceil (512 * (N : Real) / etaOne) <= L by omega)
  have hparents : ∀ m, m < N -> 8 / parent m <= (L : Real) := by
    intro m hm
    refine (Nat.le_ceil _).trans ?_
    have hsup := Finset.le_sup (f := fun m => Nat.ceil (8 / parent m))
      (Finset.mem_range.mpr hm)
    exact_mod_cast (show Nat.ceil (8 / parent m) <= L by omega)
  refine ⟨M1 * Mc * L, hM1, hMc, hN, ?_, dvd_mul_right _ _, heta, hparent, ?_, ?_⟩
  · have : 2 <= L := by omega
    omega
  · exact hglobal.trans (by exact_mod_cast hLM)
  · intro m hm
    exact (hparents m hm).trans (by exact_mod_cast hLM)

theorem source_eventually_fixed_tower_radius_conditions (M : Nat) (hM : 2 <= M)
    {e : Real} (he : 0 < e) :
    ∀ᶠ delta : NNReal in 𝓝[>] 0,
      delta < (400 : NNReal) ^ (-(M : Real)) /\ delta ^ e <= (1 / 200 : NNReal) /\
      0 < delta /\ sourceTowerRadius delta M 0 <= 1 /\
      (∀ k, k < M -> 4 * delta <= sourceTowerRadius delta M k) /\
      (∀ k, k < M -> sourceTowerRadius delta M (k + 1) <=
        sourceTowerRadius delta M k / 2) := by
  have hMr : 0 < (M : Real) := by exact_mod_cast (show 0 < M by omega)
  have htower : (0 : NNReal) < (400 : NNReal) ^ (-(M : Real)) := by positivity
  have hshade : (0 : NNReal) < (1 / 200 : NNReal) ^ (1 / e) := by positivity
  filter_upwards [Ioo_mem_nhdsGT htower, Ioo_mem_nhdsGT hshade] with delta ht hs
  have hepow : delta ^ e <= (1 / 200 : NNReal) := by
    have hle := NNReal.rpow_le_rpow hs.2.le he.le
    rw [← NNReal.rpow_mul, one_div_mul_cancel he.ne', NNReal.rpow_one] at hle
    exact hle
  let x : NNReal := delta ^ (1 / (M : Real))
  have hx : x <= (1 / 400 : NNReal) := by
    calc x <= ((400 : NNReal) ^ (-(M : Real))) ^ (1 / (M : Real)) :=
        NNReal.rpow_le_rpow ht.2.le (by positivity)
      _ = 1 / 400 := by
        rw [← NNReal.rpow_mul]
        have hpow : (-(M : Real)) * (1 / (M : Real)) = -1 := by
          field_simp
        rw [hpow]
        norm_num
  have hx1 : x <= 1 := hx.trans (by
    norm_num [div_le_iff₀ (show (0 : NNReal) < 400 by norm_num)])
  have hrep : ∀ k : Nat, delta ^ ((k : Real) / (M : Real)) = x ^ k := by
    intro k
    rw [show (k : Real) / (M : Real) = (1 / (M : Real)) * (k : Real) by ring,
      NNReal.rpow_mul, NNReal.rpow_natCast]
  have hbottom : delta = x ^ M := by
    simpa [div_self hMr.ne', NNReal.rpow_one] using hrep M
  have hstep : ∀ k, k < M -> delta <= x ^ k * x := by
    intro k hk
    rw [hbottom, ← pow_succ]
    exact pow_le_pow_of_le_one (by positivity) hx1 (by omega)
  refine ⟨ht.2, hepow, ht.1, ?_, ?_, ?_⟩
  · simp only [sourceTowerRadius, show 0 < M by omega, if_true, Nat.cast_zero,
      zero_div, NNReal.rpow_zero, mul_one]
    norm_num [div_le_iff₀ (show (0 : NNReal) < 40 by norm_num)]
  · intro k hk
    rw [sourceTowerRadius, if_pos hk, hrep]
    have hle := hstep k hk
    have hmul := mul_le_mul_of_nonneg_left hx (show 0 <= x ^ k by positivity)
    nlinarith
  · intro k hk
    simp only [sourceTowerRadius, if_pos hk, hrep]
    by_cases hk1 : k + 1 < M
    · rw [if_pos hk1, pow_succ]
      have hxhalf : x <= (1 / 2 : NNReal) := hx.trans (by
        norm_num [div_le_div_iff₀ (show (0 : NNReal) < 400 by norm_num)
          (show (0 : NNReal) < 2 by norm_num)])
      calc (1 / 40 : NNReal) * (x ^ k * x) <= (1 / 40) * (x ^ k * (1 / 2)) := by
            gcongr
        _ = (1 / 40) * x ^ k / 2 := by ring
    · rw [if_neg hk1]
      have hle := hstep k hk
      have hmul := mul_le_mul_of_nonneg_left hx (show 0 <= x ^ k by positivity)
      nlinarith

end Kakeya.ML2Core
