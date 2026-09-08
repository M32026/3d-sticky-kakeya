/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Frostman
public import Kakeya.Thickness.BoundingBox

/-!
# The `hdilate` clause of the two-sided Frostman transport needs nothing of its container

`ConvexSpaceBody.frostmanConstIn_ge_of_comparable` (`Kakeya/Frostman.lean`) transports the
Frostman constant between two families `W i ≤ V i` inside a container `K` and asks, as its
hypothesis `hdilate`, that

> for every `K' ≤ K` there is an `L ≤ K` with `K' ≤ L`, `|L| ≤ C |K'|` and `V i ≤ L`
> whenever `i ∈ s` and `W i ≤ K'`.

`Kakeya.ml1Boot.exists_fineNormalization_lower` records the reading that this clause "is
false at `K = ConvexSpaceBody.closedUnitBall` — a thin tube tangent to the unit sphere has
its dilate stick out", and that at a larger ambient radius it is a separate geometric condition.  The first
half of that reading is **wrong**, and this file says why in one lemma.

The clause does not ask for `L` to be a dilate of `K'`.  Given any convex enlargement `D` of
`K'` that is large enough to swallow the relevant `V i` and small enough in volume, the
witness

`L = D ⊓ K`   (`ConvexSpaceBody.inter`)

satisfies all four requirements: `L ≤ K` by construction, `K' ≤ L` because `K' ≤ D` and
`K' ≤ K`, `|L| ≤ |D| ≤ C |K'|` by monotonicity of the measure, and `V i ≤ L` because
`V i ≤ D` is the enlargement's clause while `V i ≤ K` is the hypothesis `hVK` that
`ConvexSpaceBody.frostmanConstIn_ge_of_comparable` already carries.  Nothing about `K` is
used — not its radius, not convex position, not volume.  A dilate of `K'` sticking out of `K`
is harmless, because only the part of it inside `K` is ever needed.

So the real content of `hdilate` is entirely local: the **per-body enlargement**
`∀ i ∈ s, W i ≤ K' → V i ≤ D` at a `D ⊇ K'` of comparable volume.  That is a statement about
`W`, `V` and `K'` alone, and it is what a producer has to prove.  It does not follow from
`W i ≤ V i` plus `|V i| ≤ C |W i|`: a needle `V i` of the same volume as `W i` but far
longer contains `W i`, is volume-comparable to it, and leaves every constant-volume
enlargement of `K' = W i`.  What is available in the normalization is stronger than volume
comparability — `V i` is the centred extension of `W i` to core length `1`, hence sits in a
bounded dilate of `W i` — and that is the shape a producer should aim at.
-/

@[expose] public section

open MeasureTheory
namespace ConvexSpaceBody

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*}
  {s : Finset ι} {W V : ι → ConvexSpaceBody E} {K : ConvexSpaceBody E} {C : ENNReal}

/-- **A container-side witness, out of a container-free enlargement.**

If every `K' ≤ K` admits a convex enlargement `D ⊇ K'` of volume at most `C |K'|` that
contains the `V i` of those `i` with `W i ≤ K'`, then the `hdilate` clause of
`ConvexSpaceBody.frostmanConstIn_ge_of_comparable` holds at `K`.  The witness is `D ⊓ K`, and
the only thing used about `K` is the hypothesis `hVK : ∀ i ∈ s, V i ≤ K`, which that lemma
already assumes. -/
theorem exists_dilate_witness_of_enlargement (hVK : ∀ i ∈ s, V i ≤ K)
    (hD : ∀ K', K' ≤ K → ∃ D : ConvexSpaceBody E, K' ≤ D ∧
      volume D.carrier ≤ C * volume K'.carrier ∧ ∀ i ∈ s, W i ≤ K' → V i ≤ D) :
    ∀ K' ≤ K, ∃ L ≤ K, K' ≤ L ∧ volume L.carrier ≤ C * volume K'.carrier ∧
      ∀ i ∈ s, W i ≤ K' → V i ≤ L := by
  intro K' hK'K
  obtain ⟨D, hK'D, hvolD, hVD⟩ := hD K' hK'K
  have hK'DK : K'.carrier ⊆ D.carrier ∩ K.carrier :=
    Set.subset_inter (SetLike.coe_subset_coe.mpr hK'D) (SetLike.coe_subset_coe.mpr hK'K)
  have hne : (D.carrier ∩ K.carrier).Nonempty := K'.nonempty.mono hK'DK
  have hLK : ConvexSpaceBody.inter D K hne ≤ K :=
    SetLike.coe_subset_coe.mp (Set.inter_subset_right (s := D.carrier) (t := K.carrier))
  have hK'L : K' ≤ ConvexSpaceBody.inter D K hne := SetLike.coe_subset_coe.mp hK'DK
  have hvolL : volume (ConvexSpaceBody.inter D K hne).carrier ≤ C * volume K'.carrier :=
    le_trans (measure_mono (Set.inter_subset_left (s := D.carrier) (t := K.carrier))) hvolD
  refine ⟨ConvexSpaceBody.inter D K hne, hLK, hK'L, hvolL, fun i hi hWi =>
    SetLike.coe_subset_coe.mp (Set.subset_inter
      (SetLike.coe_subset_coe.mpr (hVD i hi hWi)) (SetLike.coe_subset_coe.mpr (hVK i hi)))⟩

/-- **Two-sided transport of the Frostman constant, with the container-free hypothesis.**

`ConvexSpaceBody.frostmanConstIn_ge_of_comparable` with its `hdilate` clause replaced by the
purely local enlargement clause of
`ConvexSpaceBody.exists_dilate_witness_of_enlargement`. -/
theorem frostmanConstIn_ge_of_comparable_of_enlargement (hC : 1 ≤ C)
    (hVK : ∀ i ∈ s, V i ≤ K)
    (hWV : ∀ i ∈ s, W i ≤ V i)
    (hvol : ∀ i ∈ s, volume (V i).carrier ≤ C * volume (W i).carrier)
    (hD : ∀ K', K' ≤ K → ∃ D : ConvexSpaceBody E, K' ≤ D ∧
      volume D.carrier ≤ C * volume K'.carrier ∧ ∀ i ∈ s, W i ≤ K' → V i ≤ D) :
    frostmanConstIn s W K ≤ C ^ 2 * frostmanConstIn s V K ∧
      frostmanConstIn s V K ≤ C * frostmanConstIn s W K :=
  frostmanConstIn_ge_of_comparable hC hVK hWV hvol
    (exists_dilate_witness_of_enlargement hVK hD)

/-- The clause is satisfiable at the closed unit ball: witness data at `C = 1`, `s = ∅`.
This is only a sanity check that the hypothesis bundle of
`ConvexSpaceBody.frostmanConstIn_ge_of_comparable_of_enlargement` is not vacuous. -/
theorem enlargement_of_isEmpty_index (K : ConvexSpaceBody E) :
    ∀ K', K' ≤ K → ∃ D : ConvexSpaceBody E, K' ≤ D ∧
      volume D.carrier ≤ (1 : ENNReal) * volume K'.carrier ∧
      ∀ i ∈ (∅ : Finset ι), W i ≤ K' → V i ≤ D := by
  intro K' _
  exact ⟨K', le_rfl, by simp, by simp⟩

/-- **The `hdilate` enlargement clause, from a per-body homothety presentation.**

Suppose each `V i` is contained in the image of `W i` under a homothety of ratio `λ ≥ 1`
centred at *some point of `W i` itself* -- the centre may differ from `i` to `i`.  Then the
container-free enlargement hypothesis of
`ConvexSpaceBody.exists_dilate_witness_of_enlargement` holds with the dimensional constant
`(4 λ) ^ n * n !`, so `hdilate` follows.

The enlargement is `Convex.exists_homothety_container` applied to `K'` itself, which swallows
every homothety image of every `W i ≤ K'` at once precisely because the container's defining
property quantifies over the homothety centre.

The degenerate case is handled without a hypothesis on `K'`: if some `W i ≤ K'` then
`|K'| ≠ 0` because `|W i| ≠ 0`, and if no `W i ≤ K'` then `D = K'` works, the constant
being at least `1`. -/
theorem exists_enlargement_of_homothety [Nontrivial E]
    {ι : Type*} {s : Finset ι} {W V : ι → ConvexSpaceBody E} {lam : ℝ} (hlam : 1 ≤ lam)
    (hW0 : ∀ i ∈ s, volume (W i).carrier ≠ 0)
    (hhom : ∀ i ∈ s, ∃ p ∈ (W i).carrier,
      (V i).carrier ⊆ (fun x => lam • (x - p) + p) '' (W i).carrier)
    (K' : ConvexSpaceBody E) :
    ∃ D : ConvexSpaceBody E, K' ≤ D ∧
      volume D.carrier
        ≤ (ENNReal.ofReal (4 * lam) ^ (Module.finrank ℝ E)
            * ((Module.finrank ℝ E).factorial : ENNReal)) * volume K'.carrier ∧
      ∀ i ∈ s, W i ≤ K' → V i ≤ D := by
  set n := Module.finrank ℝ E with hn
  have hC1 : (1 : ENNReal) ≤ ENNReal.ofReal (4 * lam) ^ n * ((n.factorial : ENNReal)) := by
    refine one_le_mul_of_one_le_of_one_le ?_ ?_
    · refine one_le_pow₀ ?_
      rw [show (1:ENNReal) = ENNReal.ofReal 1 by simp]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    · exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_pos n).ne'
  by_cases hex : ∃ i ∈ s, W i ≤ K'
  · obtain ⟨i₀, hi₀, hi₀K⟩ := hex
    have h0 : volume K'.carrier ≠ 0 := by
      intro hcon
      exact hW0 i₀ hi₀ (measure_mono_null (SetLike.coe_subset_coe.mpr hi₀K) hcon)
    have htop : volume K'.carrier ≠ ⊤ := K'.isCompact'.measure_lt_top.ne
    obtain ⟨P, hKP, hhomP, hvolP⟩ :=
      (K'.convex'.convex).exists_homothety_container h0 htop hlam
    refine ⟨P.toConvexSpaceBody, SetLike.coe_subset_coe.mp hKP, ?_, ?_⟩
    · rw [mul_assoc] at hvolP ⊢
      exact hvolP
    · intro i hi hiK
      obtain ⟨p, hp, hsubV⟩ := hhom i hi
      intro y hy
      obtain ⟨x, hx, rfl⟩ := hsubV hy
      exact hhomP p (hiK hp) x (hiK hx)
  · refine ⟨K', le_refl _, ?_, ?_⟩
    · calc volume K'.carrier = 1 * volume K'.carrier := (one_mul _).symm
        _ ≤ _ := by gcongr
    · intro i hi hiK
      exact absurd ⟨i, hi, hiK⟩ hex

end ConvexSpaceBody

#print axioms ConvexSpaceBody.exists_enlargement_of_homothety
