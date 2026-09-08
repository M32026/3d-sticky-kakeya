/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Mathlib.ENNReal
public import Kakeya.Mathlib.MeasureTheory.Simplex
public import Kakeya.Thickness.Basic
public import Kakeya.Thickness.InnerSimplex
public import Kakeya.Thickness.OuterPrism
public import Kakeya.DimensionN.Volume
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# Volume and thickness

We relate the Lebesgue volume of a set to its `thickness`/`ethickness`.

* `volume_le_prod_thickness` and `volume_le_prod_ethickness` bound the volume of an arbitrary set
  by the product of its thicknesses: every set fits, up to a `2 ^ n` factor, inside the axis-aligned
  box of half-widths its `thickness`es (via `outerPrism`, extended to unbounded sets by exhausting
  with bounded slices).
* For a convex set we also derive the matching lower bounds (`Convex.ethickness_prod_le_volume` and
  friends), so that positivity of the volume is equivalent to all `ethickness`es being nonzero.

Check also Kakeya.Thickness.Lemmas for more.
-/

@[expose] public section

open MeasureTheory Metric

variable
  {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

omit [Nontrivial E] in
/-- For a bounded set `s`, its volume is bounded by `2 ^ n` times the product of its
`thickness`es. This is obtained from `outerPrism`, the axis-aligned box of half-widths
`thickness ℝ s ·` containing the (compact) closure of `s`. -/
theorem volume_le_prod_thickness {s : Set E} (hs : Bornology.IsBounded s) :
    volume s ≤ 2 ^ (Module.finrank ℝ E) *
      ∏ i ∈ Finset.range (Module.finrank ℝ E), ENNReal.ofReal (thickness ℝ s i) := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp
  have hK : IsCompact (closure s) := hs.isCompact_closure
  have hKne : (closure s).Nonempty := hne.closure
  have key : volume (outerPrism rfl hK hKne).carrier
      = 2 ^ Module.finrank ℝ E *
        ∏ i ∈ Finset.range (Module.finrank ℝ E), ENNReal.ofReal (thickness ℝ s i) := by
    rw [PrismNDim.volume_carrier]
    congr 1
    rw [← Fin.prod_univ_eq_prod_range
      (fun k => ENNReal.ofReal (thickness ℝ s k)) (Module.finrank ℝ E)]
    apply Finset.prod_congr rfl
    intro i _
    rw [outerPrism.thicknesses_eq, ENNReal.coe_nnreal_eq]
    congr 1
    exact thickness_closure hs (i : ℕ)
  rw [← key]
  exact measure_mono (subset_closure.trans (outerPrism.self_subset rfl hK hKne))

omit [Nontrivial E] in
theorem volume_le_prod_ethickness (s : Set E) :
    volume s ≤ 2 ^ (Module.finrank ℝ E) *
      ∏ i ∈ Finset.range (Module.finrank ℝ E), ethickness ℝ s i := by
  -- Exhaust `s` by the bounded pieces `A k = s ∩ closedBall 0 k` and pass to the limit.
  set A : ℕ → Set E := fun k => s ∩ closedBall 0 k with hA_def
  have hmono : Monotone A := fun a b hab =>
    Set.inter_subset_inter_right s (closedBall_subset_closedBall (by exact_mod_cast hab))
  have hbound : ∀ k, volume (A k) ≤ 2 ^ Module.finrank ℝ E *
      ∏ i ∈ Finset.range (Module.finrank ℝ E), ethickness ℝ s i := by
    intro k
    have hbdd : Bornology.IsBounded (A k) :=
      isBounded_closedBall.subset Set.inter_subset_right
    calc volume (A k)
        ≤ 2 ^ Module.finrank ℝ E *
            ∏ i ∈ Finset.range (Module.finrank ℝ E), ENNReal.ofReal (thickness ℝ (A k) i) :=
          volume_le_prod_thickness hbdd
      _ = 2 ^ Module.finrank ℝ E *
            ∏ i ∈ Finset.range (Module.finrank ℝ E), ethickness ℝ (A k) i := by
          congr 1
          exact Finset.prod_congr rfl fun i _ => (ethickness_thickness' hbdd i).symm
      _ ≤ 2 ^ Module.finrank ℝ E *
            ∏ i ∈ Finset.range (Module.finrank ℝ E), ethickness ℝ s i := by
          gcongr with i _
          exact ethickness_monotone Set.inter_subset_left i
  calc volume s = volume (⋃ k, A k) := by rw [iUnion_inter_closedBall_nat s 0]
    _ = ⨆ k, volume (A k) := hmono.measure_iUnion
    _ ≤ _ := iSup_le hbound

omit [Nontrivial E] in
/-- The volume of the unit ball in a finite-dimensional inner product space is at most
`2 ^ n` where `n = Module.finrank ℝ E`, since each `ethickness` is at most `1`. -/
theorem volume_closedBall_le_two_pow_finrank :
    volume (closedBall (0 : E) 1) ≤ 2 ^ Module.finrank ℝ E := by
  have hprod : (∏ i ∈ Finset.range (Module.finrank ℝ E),
      ethickness ℝ (closedBall (0 : E) 1) i) ≤ 1 := by
    calc _ ≤ ∏ _i ∈ Finset.range (Module.finrank ℝ E), (1 : ENNReal) :=
          Finset.prod_le_prod' fun i _ => by
            apply ethickness_closedBall_le
      _ = 1 := by simp
  grw [volume_le_prod_ethickness, hprod, mul_one]

theorem Convex.lt_volume_of_lt_ethickness {n} (hn : n = Module.finrank ℝ E)
    {s : Set E} (hs : Convex ℝ s)
    {r : Fin n → ENNReal} (hr : ∀ i, r i < ethickness ℝ s i) :
    lt_volume_convexHull.c (Module.finrank ℝ E) * ∏ i, r i < volume s := by
  have hE : 0 < Module.finrank ℝ E := Module.finrank_pos
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (hn ▸ hE)
  have hsn : s.Nonempty := by
    by_contra!
    simp [this] at hr
  obtain ⟨p, hp⟩ := exists_simplex_of_lt_ethickness hsn hr
  exact lt_of_lt_of_le (lt_volume_convexHull hn hp.2)
    <| measure_mono (convexHull_min (Set.range_subset_iff.2 hp.1) hs)

theorem Convex.ethickness_prod_le_volume {s : Set E} (hs : Convex ℝ s) :
    lt_volume_convexHull.c (Module.finrank ℝ E) *
      ∏ i ∈ Finset.range (Module.finrank ℝ E), ethickness ℝ s i ≤ volume s := by
  set n := Module.finrank ℝ E with hn_def
  rw [← Fin.prod_univ_eq_prod_range (fun i => ethickness ℝ s i) n]
  refine ENNReal.mul_le_of_forall_lt fun C' hC' P' hP' ↦ ?_
  obtain ⟨r, hr_lt, hr⟩ := ENNReal.exists_lt_prod_of_lt_prod (Finset.univ : Finset (Fin n))
    (fun i => ethickness ℝ s i.val) P' hP'
  grw [hr, hC', hs.lt_volume_of_lt_ethickness hn_def.symm <| fun i => hr_lt i <| Finset.mem_univ i]

theorem Convex.volume_pos_of_ethickness_ne_zero {s : Set E} (hs : Convex ℝ s)
    (h : ∀ i ∈ Finset.range (Module.finrank ℝ E), ethickness ℝ s i ≠ 0) :
    0 < volume s := lt_of_lt_of_le (ENNReal.mul_pos (ENNReal.coe_ne_coe.2
  (lt_volume_convexHull.c_pos _).ne') (Finset.prod_ne_zero_iff.2 h))
  hs.ethickness_prod_le_volume

omit [Nontrivial E] in
/-- A set of positive volume has nonzero `ethickness` at every rank below the ambient
dimension. -/
theorem ethickness_ne_zero_of_volume_pos {s : Set E} (h : 0 < volume s)
    {i : ℕ} (hi : i ∈ Finset.range (Module.finrank ℝ E)) : ethickness ℝ s i ≠ 0 := by
  intro hz
  exact h.ne' <| nonpos_iff_eq_zero.mp <| (volume_le_prod_ethickness s).trans_eq <| by
    rw [Finset.prod_eq_zero hi hz, mul_zero]

/-- For a convex set, having positive volume is equivalent to having nonzero `ethickness`
at every rank below the ambient dimension. -/
theorem Convex.volume_pos_iff_ethickness_all_pos {s : Set E} (hs : Convex ℝ s) :
    0 < volume s ↔ ∀ i ∈ Finset.range (Module.finrank ℝ E), ethickness ℝ s i ≠ 0 :=
  ⟨fun h _ hi => ethickness_ne_zero_of_volume_pos h hi, hs.volume_pos_of_ethickness_ne_zero⟩

theorem Convex.le_volume_of_pow_scale {s : Set E} (hs : Convex ℝ s) :
    lt_volume_convexHull.c (Module.finrank ℝ E) *
      (ethickness.scale ℝ s)^(Module.finrank ℝ E) ≤ volume s := by
  grw [← hs.ethickness_prod_le_volume]
  nth_rw 2 [← Finset.card_range (Module.finrank ℝ E)]
  grw [Finset.pow_card_le_prod _ _ _ fun _ hi ↦ ethickness.scale_le _ (Finset.mem_range.mp hi)]

/-- **Volume lower bound at scale `δ`** (blueprint `lem:volumeLowerBdAtScale`): a convex set whose
`ethickness.scale` is at least `δ` has volume at least `c(n) δ ^ n = δ ^ n / n !`, where
`c(n) = Metric.lt_volume_convexHull.c n` and `n = Module.finrank ℝ E`.

This is `Convex.le_volume_of_pow_scale` with the scale replaced by the lower bound `δ`; together
with `volume_le_two_pow_finrank_of_subset_closedBall` it is the two-sided volume estimate for a
family discretized at scale `δ` (blueprint `def:scaleDeltaFamily`). When `0 < δ` it gives in
particular `0 < volume s`, which is `Convex.volume_pos_of_scale_ne_zero`. -/
theorem Convex.le_volume_of_le_scale {s : Set E} (hs : Convex ℝ s) {δ : NNReal}
    (hδ : (δ : ENNReal) ≤ ethickness.scale ℝ s) :
    (lt_volume_convexHull.c (Module.finrank ℝ E) : ENNReal) * (δ : ENNReal) ^ Module.finrank ℝ E
      ≤ volume s :=
  calc
    (lt_volume_convexHull.c (Module.finrank ℝ E) : ENNReal) * (δ : ENNReal) ^ Module.finrank ℝ E
        ≤ (lt_volume_convexHull.c (Module.finrank ℝ E) : ENNReal) *
          (ethickness.scale ℝ s) ^ Module.finrank ℝ E := by
      gcongr
    _ ≤ volume s := hs.le_volume_of_pow_scale

theorem Convex.volume_pos_of_scale_ne_zero {s : Set E} (hs : Convex ℝ s)
    (h : ethickness.scale ℝ s ≠ 0) : 0 < volume s := by
  apply hs.volume_pos_of_ethickness_ne_zero
  intro i hi
  apply ne_bot_of_le_ne_bot h
  exact ethickness.scale_le _ (Finset.mem_range.mp hi)


/-- Inscribed simplex volume lower bound: for any convex compact nonempty `K ⊆ E`, the
volume of `K` dominates the product of its thicknesses, with constant `c_K = 1/n!`.

This is the real-valued specialization of `Convex.ethickness_prod_le_volume`. -/
theorem Convex.prod_thickness_le_volumeReal {K : Set E}
    (h1 : Convex ℝ K) (h2 : Bornology.IsBounded K) :
      lt_volume_convexHull.c (Module.finrank ℝ E) *
        ∏ i ∈ Finset.range (Module.finrank ℝ E), Metric.thickness ℝ K i
      ≤ MeasureTheory.volume.real K := by
  have hvol_ne_top : volume K ≠ ⊤ := h2.measure_lt_top.ne
  have hAPI : (Metric.lt_volume_convexHull.c (Module.finrank ℝ E) : ENNReal) *
      ∏ i ∈ Finset.range (Module.finrank ℝ E), Metric.ethickness ℝ K i ≤ volume K :=
    h1.ethickness_prod_le_volume
  have heth : ∀ i, Metric.ethickness ℝ K i = ENNReal.ofReal (Metric.thickness ℝ K i) :=
    fun i => ethickness_thickness' h2 _
  apply ENNReal.toReal_mono hvol_ne_top at hAPI
  rw [ENNReal.toReal_mul, ENNReal.toReal_prod] at hAPI
  convert hAPI
  · simp
  · rw [toReal_ethickness h2]
  · rfl

/-- A dimension-dependent lower bound for the volume of a bounded convex set in terms of
the product of its affine thicknesses. -/
theorem convex_body_volume_thickness_lower_bound :
    ∃ c_K : ℝ, 0 < c_K ∧
      ∀ (K : Set E), Convex ℝ K → IsCompact K → K.Nonempty →
        c_K * (∏ j : Fin (Module.finrank ℝ E), Metric.thickness ℝ K j.val)
          ≤ MeasureTheory.volume.real K := by
  refine ⟨Metric.lt_volume_convexHull.c (Module.finrank ℝ E), ?_, ?_⟩
  · exact_mod_cast Metric.lt_volume_convexHull.c_pos (Module.finrank ℝ E)
  · intro K hK hK_compact _
    rw [Fin.prod_univ_eq_prod_range]
    exact hK.prod_thickness_le_volumeReal hK_compact.isBounded

omit [Nontrivial E] in
/-- For `ρ` at most the smallest thickness (`ethickness.scale`) of `s`, the `ρ`-thickening
inflates the volume by at most the dimensional factor `4 ^ n`: `|N_ρ s| ≤ 4ⁿ · ∏ ethickness s`. -/
theorem volume_cthickening_le_prod {s : Set E} {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρscale : ENNReal.ofReal ρ ≤ ethickness.scale ℝ s) :
    volume (cthickening ρ s) ≤ 4 ^ Module.finrank ℝ E *
      ∏ i ∈ Finset.range (Module.finrank ℝ E), ethickness ℝ s i := by
  have hstep : ∀ i ∈ Finset.range (Module.finrank ℝ E),
      ethickness ℝ (cthickening ρ s) i ≤ 2 * ethickness ℝ s i := by
    intro i hi
    have h1 := ethickness_cthickening_le (𝕜 := ℝ) (s := s) ρ.toNNReal i
    rw [Real.coe_toNNReal ρ hρ0] at h1
    have h2 : (ρ.toNNReal : ENNReal) ≤ ethickness ℝ s i :=
      hρscale.trans (ethickness.scale_le s (Finset.mem_range.mp hi))
    calc ethickness ℝ (cthickening ρ s) i
        ≤ (ρ.toNNReal : ENNReal) + ethickness ℝ s i := h1
      _ ≤ ethickness ℝ s i + ethickness ℝ s i := by gcongr
      _ = 2 * ethickness ℝ s i := (two_mul _).symm
  calc volume (cthickening ρ s)
      ≤ 2 ^ Module.finrank ℝ E * ∏ i ∈ Finset.range (Module.finrank ℝ E),
          ethickness ℝ (cthickening ρ s) i := volume_le_prod_ethickness _
    _ ≤ 2 ^ Module.finrank ℝ E * ∏ i ∈ Finset.range (Module.finrank ℝ E),
          (2 * ethickness ℝ s i) := by gcongr with i hi; exact hstep i hi
    _ = 4 ^ Module.finrank ℝ E * ∏ i ∈ Finset.range (Module.finrank ℝ E),
          ethickness ℝ s i := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← mul_assoc, ← mul_pow]
        norm_num

omit [Nontrivial E] in
/-- Upper bound for the volume of a `ρ`-thickening in terms of `ρ + ethickness`. -/
theorem volume_cthickening_le_prod_add (X : Set E) (ρ : NNReal) :
    volume (cthickening ρ X) ≤ 2 ^ Module.finrank ℝ E *
      ∏ i ∈ Finset.range (Module.finrank ℝ E), ((ρ : ENNReal) + ethickness ℝ X i) := by
  calc volume (cthickening ρ X)
      ≤ 2 ^ Module.finrank ℝ E *
          ∏ i ∈ Finset.range (Module.finrank ℝ E), ethickness ℝ (cthickening ρ X) i :=
        volume_le_prod_ethickness _
    _ ≤ 2 ^ Module.finrank ℝ E *
          ∏ i ∈ Finset.range (Module.finrank ℝ E), ((ρ : ENNReal) + ethickness ℝ X i) := by
        gcongr with i hi
        exact ethickness_cthickening_le ρ i

/-- Lower bound for the volume of a `ρ`-thickening of a nonempty convex set, in terms of
`ρ + ethickness`. Uses `le_ethickness_cthickening` for the per-direction lower bound. -/
theorem prod_add_le_volume_cthickening {X : Set E} (hX : Convex ℝ X) (hXne : X.Nonempty)
    (ρ : NNReal) :
    lt_volume_convexHull.c (Module.finrank ℝ E) *
        ∏ i ∈ Finset.range (Module.finrank ℝ E), ((ρ : ENNReal) + ethickness ℝ X i)
      ≤ volume (cthickening ρ X) := by
  calc lt_volume_convexHull.c (Module.finrank ℝ E) *
          ∏ i ∈ Finset.range (Module.finrank ℝ E), ((ρ : ENNReal) + ethickness ℝ X i)
      ≤ lt_volume_convexHull.c (Module.finrank ℝ E) *
          ∏ i ∈ Finset.range (Module.finrank ℝ E), ethickness ℝ (cthickening ρ X) i := by
        gcongr with i hi
        have h := le_ethickness_cthickening hXne (ρ := (ρ : ℝ)) (Finset.mem_range.mp hi)
        rw [ENNReal.ofReal_coe_nnreal] at h
        rw [add_comm]
        exact h
    _ ≤ volume (cthickening ρ X) := (hX.cthickening _).ethickness_prod_le_volume
