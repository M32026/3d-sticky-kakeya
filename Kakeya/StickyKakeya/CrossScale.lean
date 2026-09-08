/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.FibreCommon
public import Mathlib.Tactic.Monotonicity
public import Kakeya.Sticky.Definitions

/-!
  # Cross-scale parent density transfer

  Step B6 of the GWZ Theorem 7.3 (A) ⇒ (B) deduction needs a `Δ_max` bound on the parent family of
  an inner hierarchy at an inner grid scale `ρ`, while the hypothesis available is the node reading
  of the Katz–Tao condition along a different, finer grid.  This file compares the two covers at
  nested scales `ρ ≤ r`: parents are charged to nodes, only packing-many parents meet one node, and
  a node holding a common leaf lies in a bounded thickening of the tested body.
-/

@[expose] public section

open MeasureTheory
open Tube

namespace Kakeya

open MultiScaleFac

namespace StickyKakeya

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*}

/-! ### Cross-scale parent density transfer

Step B6 of the GWZ Theorem 7.3 (A) ⇒ (B) deduction needs a `Δ_max` bound on the parent family of
the *inner* hierarchy at an inner grid scale `ρ`.  What the hypothesis of `StickyKatzTaoEstimate`
supplies is the *node* reading of the Katz–Tao condition on the input bundle, read along that
bundle's own grid, which is a different (and, in the regime the statement is applied in, strictly
finer) grid.  The thickened reading that would bridge the two directly is unsatisfiable
(`Kakeya.StickyKakeya.card_mul_le_of_isKatzTaoAtEveryScale`, no longer formalized), and the
leaf-scale reading is too
weak: a leaf family may be `Δ_max`-bounded at scale `δ` while its `ρ`-parents have density
`(ρ/δ)^{n-1}` (take one leaf inside each member of a maximal essentially distinct family of
`ρ`-tubes with `ρ = δ^{1/2}`).

The transfer below is therefore a comparison of two *covers* at nested scales `ρ ≤ r`:

* every parent contains a leaf, and that leaf lies in a node of the coarser cover, so each parent
  is charged to a node;
* only packing-many parents are charged to one node (`card_parents_meeting_tube_le`): the count is
  the `L¹` endpoint-metric box count `2 (25 r/ρ)^{2n}`, and the hypothesis that makes it available
  is the bounded overlap clause of `Tube.IsUniformAtScale`, not any separation of the parents;
* a node holding a leaf of a body `K` lies in the `4r`-thickening of `K`
  (`tube_le_cthickening_of_common_leaf`), and thickening a convex body that already contains a
  `ρ`-ball costs only `((ρ + 4r)/ρ)^n ≤ (5 r/ρ)^n` in volume.

The total cost is `(r/ρ)^{3n}`, which is `δ^{-o(1)}` as soon as the two grids are within one step
of each other.  `Kakeya.densityIn` counts the members whose body is *contained* in the test body,
which is what makes a comparison across two scales possible at all: the parents contained in `K`
are charged to nodes contained in a fixed dilate of `K`. -/

omit [Nontrivial E] in
open scoped Pointwise in
/-- **Volume of a thickening of a convex body containing a ball.**  A compact convex set `K`
containing a ball of radius `ρ > 0` thickens with only a dimensional volume blowup:
`vol(cthickening t K) ≤ ((ρ+t)/ρ)ⁿ · vol K`.  A convex set containing `B(p,ρ)` has its
`t`-thickening inside the homothety of `K` about `p` by `(ρ+t)/ρ`, whose volume scales by the
`n`-th power of that ratio (`addHaar_smul`). -/
theorem volume_cthickening_le_of_closedBall_subset
    {K : Set E} (hKcomp : IsCompact K) (hKconv : Convex ℝ K)
    {p : E} {ρ : NNReal} (hρ : 0 < (ρ : ℝ)) (hball : Metric.closedBall p (ρ : ℝ) ⊆ K)
    {t : ℝ} (ht : 0 < t) :
    MeasureTheory.volume (Metric.cthickening t K) ≤
      ENNReal.ofReal (((ρ : ℝ) + t) / (ρ : ℝ)) ^ Module.finrank ℝ E * MeasureTheory.volume K := by
  classical
  set r : ℝ := ((ρ : ℝ) + t) / (ρ : ℝ) with hr_def
  have htne : t ≠ 0 := ht.ne'
  have hρt : (0 : ℝ) < (ρ : ℝ) + t := by positivity
  have hr_pos : 0 < r := by rw [hr_def]; positivity
  set μ : ℝ := (ρ : ℝ) / ((ρ : ℝ) + t) with hμ_def
  have hμ_pos : 0 < μ := by rw [hμ_def]; positivity
  have hμ_le : μ ≤ 1 := by rw [hμ_def, div_le_one hρt]; linarith
  have hrμ : r * μ = 1 := by rw [hr_def, hμ_def]; field_simp
  have hcoef : (1 - μ) * ((ρ : ℝ) / t) = μ := by rw [hμ_def]; field_simp; ring
  have hKne : K.Nonempty := ⟨p, hball (Metric.mem_closedBall_self hρ.le)⟩
  have hsub : Metric.cthickening t K ⊆ (p : E) +ᵥ (r • ((-p : E) +ᵥ K)) := by
    intro z hz
    obtain ⟨x, hxK, hxdist⟩ := hKcomp.exists_infDist_eq_dist hKne z
    have hzx : dist z x ≤ t := by
      rw [← hxdist]
      have hinf : Metric.infEDist z K ≤ ENNReal.ofReal t := (Metric.mem_cthickening_iff).mp hz
      have heq : Metric.infDist z K = (Metric.infEDist z K).toReal := rfl
      rw [heq]
      calc (Metric.infEDist z K).toReal
          ≤ (ENNReal.ofReal t).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hinf
        _ = t := ENNReal.toReal_ofReal ht.le
    set u : E := z - x with hu_def
    set q : E := p + ((ρ : ℝ) / t) • u with hq_def
    have hqK : q ∈ K := by
      refine hball ?_
      rw [Metric.mem_closedBall, hq_def, dist_eq_norm]
      have : (p + ((ρ : ℝ) / t) • u) - p = ((ρ : ℝ) / t) • u := by abel
      rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ (ρ:ℝ)/t)]
      calc (ρ : ℝ) / t * ‖u‖ ≤ (ρ : ℝ) / t * t := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              rw [hu_def, ← dist_eq_norm]; exact hzx
        _ = (ρ : ℝ) := by field_simp
    set w : E := μ • x + (1 - μ) • q with hw_def
    have hwK : w ∈ K := hKconv hxK hqK hμ_pos.le (by linarith) (by ring)
    have hwp : -p + w = μ • (z - p) := by
      rw [hw_def, hq_def]
      have hstep : (1 - μ) • (((ρ : ℝ) / t) • u) = μ • u := by rw [smul_smul, hcoef]
      rw [smul_add, hstep, hu_def]
      module
    have hz_eq : z = p + r • (-p + w) := by
      rw [hwp, smul_smul, hrμ, one_smul]; abel
    have hmemv : (p : E) +ᵥ (r • ((-p : E) +ᵥ w)) ∈ (p : E) +ᵥ (r • ((-p : E) +ᵥ K)) :=
      Set.vadd_mem_vadd_set (Set.smul_mem_smul_set (Set.vadd_mem_vadd_set hwK))
    rwa [show (p : E) +ᵥ (r • ((-p : E) +ᵥ w)) = z by
      simp only [vadd_eq_add]; exact hz_eq.symm] at hmemv
  have hvol : MeasureTheory.volume ((p : E) +ᵥ (r • ((-p : E) +ᵥ K)))
      = ENNReal.ofReal r ^ Module.finrank ℝ E * MeasureTheory.volume K := by
    rw [MeasureTheory.measure_vadd, MeasureTheory.Measure.addHaar_smul, MeasureTheory.measure_vadd,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ r ^ Module.finrank ℝ E),
      ENNReal.ofReal_pow hr_pos.le]
  calc MeasureTheory.volume (Metric.cthickening t K)
      ≤ MeasureTheory.volume ((p : E) +ᵥ (r • ((-p : E) +ᵥ K))) := MeasureTheory.measure_mono hsub
    _ = ENNReal.ofReal r ^ Module.finrank ℝ E * MeasureTheory.volume K := hvol

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **A node lies in the `4r`-thickening of any body holding one of its leaves.**  If the `δ`-tube
`T` lies both in the `r`-tube `W` and in the convex body `K`, then `W ⊆ K⁺ = K.cthickening (4r)`:
containment in `W` pins the endpoints of `T` to within `3r` of those of `W`
(`Tube.endpoints_close_of_body_le`), so the core of `W` lies in the `3r`-thickening of the core of
`T`, and `W` is the `r`-thickening of its own core. -/
theorem tube_le_cthickening_of_common_leaf {δ r : NNReal} (T : Tube δ E) (W : Tube r E)
    (hTW : T.toConvexSpaceBody ≤ W.toConvexSpaceBody)
    {K : ConvexSpaceBody E} (hTK : T.toConvexSpaceBody ≤ K) :
    W.toConvexSpaceBody ≤ K.cthickening (4 * (r : ℝ)) := by
  set d : ℝ := 3 * (r : ℝ) with hd_def
  have hd_nonneg : 0 ≤ d := by
    rw [hd_def]
    positivity
  have hTK_carrier : T.carrier ⊆ K.carrier := by
    intro x hx
    exact hTK hx
  have seg_pair : ∀ (u₁ u₂ v₁ v₂ : E), ‖v₁ - u₁‖ ≤ d → ‖v₂ - u₂‖ ≤ d →
      segment ℝ v₁ v₂ ⊆ Metric.cthickening d (segment ℝ u₁ u₂) := by
    intro u₁ u₂ v₁ v₂ dv₁ dv₂ z hz
    obtain ⟨a, b, ha, hb, hab, hz_eq⟩ := hz
    let q : E := a • u₁ + b • u₂
    have hq : q ∈ segment ℝ u₁ u₂ := by
      exact ⟨a, b, ha, hb, hab, rfl⟩
    have hzq : z - q = a • (v₁ - u₁) + b • (v₂ - u₂) := by
      rw [← hz_eq]
      module
    have hnorm : dist z q ≤ d := by
      rw [dist_eq_norm, hzq]
      calc
        ‖a • (v₁ - u₁) + b • (v₂ - u₂)‖
            ≤ ‖a • (v₁ - u₁)‖ + ‖b • (v₂ - u₂)‖ := norm_add_le _ _
        _ = a * ‖v₁ - u₁‖ + b * ‖v₂ - u₂‖ := by
            rw [norm_smul_of_nonneg ha, norm_smul_of_nonneg hb]
        _ ≤ a * d + b * d := by
            exact add_le_add (mul_le_mul_of_nonneg_left dv₁ ha)
              (mul_le_mul_of_nonneg_left dv₂ hb)
        _ = d := by
            rw [← add_mul, hab, one_mul]
    exact Metric.mem_cthickening_of_dist_le z q d (segment ℝ u₁ u₂) hq hnorm
  have hsegTW : segment ℝ W.x W.y ⊆ Metric.cthickening d (segment ℝ T.x T.y) := by
    rcases Tube.endpoints_close_of_body_le T W hTW with hcase | hcase
    · rcases hcase with ⟨hx, hy⟩
      exact seg_pair T.x T.y W.x W.y
        (by simpa [norm_sub_rev] using hx)
        (by simpa [norm_sub_rev] using hy)
    · rcases hcase with ⟨hxy, hyx⟩
      have hseg' : segment ℝ W.x W.y ⊆ Metric.cthickening d (segment ℝ T.y T.x) := by
        exact seg_pair T.y T.x W.x W.y
          (by simpa [norm_sub_rev] using hyx)
          (by simpa [norm_sub_rev] using hxy)
      simpa [segment_symm] using hseg'
  have hsegT_carrier : segment ℝ T.x T.y ⊆ T.carrier := by
    rw [T.carrier_eq_cthickening]
    exact Metric.self_subset_cthickening (segment ℝ T.x T.y)
  have hcore : segment ℝ W.x W.y ⊆ Metric.cthickening d K.carrier := by
    calc
      segment ℝ W.x W.y ⊆ Metric.cthickening d (segment ℝ T.x T.y) := hsegTW
      _ ⊆ Metric.cthickening d T.carrier := by
        exact Metric.cthickening_subset_of_subset d hsegT_carrier
      _ ⊆ Metric.cthickening d K.carrier := by
        exact Metric.cthickening_subset_of_subset d hTK_carrier
  change W.carrier ⊆ Metric.cthickening (4 * (r : ℝ)) K.carrier
  calc
    W.carrier = Metric.cthickening (r : ℝ) (segment ℝ W.x W.y) := by
      exact W.carrier_eq_cthickening
    _ ⊆ Metric.cthickening (r : ℝ) (Metric.cthickening d K.carrier) := by
      exact Metric.cthickening_subset_of_subset (r : ℝ) hcore
    _ ⊆ Metric.cthickening ((r : ℝ) + d) K.carrier := by
      exact Metric.cthickening_cthickening_subset (by positivity : 0 ≤ (r : ℝ)) hd_nonneg
        K.carrier
    _ = Metric.cthickening (4 * (r : ℝ)) K.carrier := by
      congr 1
      rw [hd_def]
      ring

open scoped Classical in
/-- **Packing count of the parents charged to one container tube.**  For a family that is
`C`-uniform at scale `ρ` and any container `r`-tube `W` with `ρ ≤ r`, at most `2 (25 r/ρ)^{2n} · C`
parents hold a leaf of `s` lying inside `W`: the `L¹` endpoint-metric net of
`exists_net_of_le_common_tube` covers those leaves by `2 (25 r/ρ)^{2n}` genuine `ρ`-tubes, and
bounded overlap allows at most `C` parents per such `ρ`-tube. -/
theorem card_parents_meeting_tube_le {δ ρ r : NNReal} (hρ_pos : 0 < ρ) (hδρ : 2 * δ ≤ ρ)
    (hρr : ρ ≤ r) {s : Finset ι} {T : ι → Tube δ E} {C : NNReal}
    (h : Tube.IsUniformAtScale s T ρ C) (W : Tube r E) :
    ((h.parent.filter (fun j => ∃ i ∈ s,
        (T i).toConvexSpaceBody ≤ (h.parentTube j).toConvexSpaceBody ∧
        (T i).toConvexSpaceBody ≤ W.toConvexSpaceBody)).card : ℝ)
      ≤ 2 * (25 : ℝ) ^ (2 * Module.finrank ℝ E)
          * ((r : ℝ) / (ρ : ℝ)) ^ (2 * Module.finrank ℝ E) * (C : ℝ) := by
  classical
  set F : Finset ι := s.filter (fun i => (T i).toConvexSpaceBody ≤ W.toConvexSpaceBody) with hF_def
  set n : ℕ := Module.finrank ℝ E with hn_def
  set B : ℝ := 2 * (25 : ℝ) ^ (2 * n) * ((r : ℝ) / (ρ : ℝ)) ^ (2 * n) with hB_def
  have hρR_pos : 0 < (ρ : ℝ) := by exact_mod_cast hρ_pos
  have hε : 0 < (ρ : ℝ) / 2 := by linarith
  have hB_ineq : 2 * ((3 * (r : ℝ) + ((ρ : ℝ) / 2) / 4) / (((ρ : ℝ) / 2) / 4)) ^ (2 * n)
      ≤ 2 * (25 : ℝ) ^ (2 * n) * ((r : ℝ) / (ρ : ℝ)) ^ (2 * n) := by
    have hρ0 : (ρ : ℝ) ≠ 0 := hρR_pos.ne'
    have hratio_eq : ((3 * (r : ℝ) + (ρ : ℝ) / 8) / ((ρ : ℝ) / 8))
        = (24 * ((r : ℝ) / (ρ : ℝ)) + 1) := by
      field_simp [hρ0]
      ring
    have h_one_le : (1 : ℝ) ≤ (r : ℝ) / (ρ : ℝ) := by
      exact (one_le_div hρR_pos).mpr (by exact_mod_cast hρr)
    have hratio_le : 24 * ((r : ℝ) / (ρ : ℝ)) + 1 ≤ 25 * ((r : ℝ) / (ρ : ℝ)) := by
      nlinarith
    have hratio_nonneg : 0 ≤ 24 * ((r : ℝ) / (ρ : ℝ)) + 1 := by
      have hdivnonneg : 0 ≤ (r : ℝ) / (ρ : ℝ) := div_nonneg (by positivity) (le_of_lt hρR_pos)
      nlinarith
    calc
      2 * ((3 * (r : ℝ) + ((ρ : ℝ) / 2) / 4) / (((ρ : ℝ) / 2) / 4)) ^ (2 * n)
          = 2 * ((3 * (r : ℝ) + (ρ : ℝ) / 8) / ((ρ : ℝ) / 8)) ^ (2 * n) := by ring
      _ = 2 * (24 * ((r : ℝ) / (ρ : ℝ)) + 1) ^ (2 * n) := by rw [hratio_eq]
      _ ≤ 2 * (25 * ((r : ℝ) / (ρ : ℝ))) ^ (2 * n) := by
        have hpow_le : (24 * ((r : ℝ) / (ρ : ℝ)) + 1) ^ (2 * n)
            ≤ (25 * ((r : ℝ) / (ρ : ℝ))) ^ (2 * n) :=
          pow_le_pow_left₀ hratio_nonneg hratio_le _
        nlinarith
      _ = 2 * (25 : ℝ) ^ (2 * n) * ((r : ℝ) / (ρ : ℝ)) ^ (2 * n) := by
        rw [mul_pow]
        ring
  obtain ⟨F', hF'sub_F, hnet, hcardF'⟩ :=
    exists_net_of_le_common_tube F T W (fun i hi => (Finset.mem_filter.mp hi).2)
      (ε := (ρ : ℝ) / 2) (B := B) (hε := hε) (hB := by simpa [B] using hB_ineq)
  set σ : ι → Finset ι := fun a => h.parent.filter (fun j => ∃ i ∈ s,
      (T i).toConvexSpaceBody ≤ (h.parentTube j).toConvexSpaceBody ∧
      (T i).toConvexSpaceBody ≤ ((T a).rescale ρ).toConvexSpaceBody) with hσ_def
  set G : Finset ι := h.parent.filter (fun j => ∃ i ∈ s,
      (T i).toConvexSpaceBody ≤ (h.parentTube j).toConvexSpaceBody ∧
      (T i).toConvexSpaceBody ≤ W.toConvexSpaceBody) with hG_def
  have hGsub : G ⊆ F'.biUnion σ := by
    intro j hjG
    rw [Finset.mem_biUnion]
    rw [Finset.mem_filter] at hjG
    rcases hjG with ⟨hjp, hjwit⟩
    rcases hjwit with ⟨i, his, hi_par, hi_W⟩
    have hiF : i ∈ F := by
      dsimp [F]
      exact Finset.mem_filter.mpr ⟨his, hi_W⟩
    rcases hnet i hiF with ⟨a, haF', hdist⟩
    refine ⟨a, haF', ?_⟩
    rw [Finset.mem_filter]
    refine ⟨hjp, i, his, hi_par, ?_⟩
    have hdist_add : ‖(T i).x - (T a).x‖ + ‖(T i).y - (T a).y‖ + (δ : ℝ) ≤ (ρ : ℝ) := by
      have hδρR : (2 : ℝ) * (δ : ℝ) ≤ (ρ : ℝ) := by exact_mod_cast hδρ
      have hδρ' : (δ : ℝ) ≤ (ρ : ℝ) / 2 := by linarith
      nlinarith
    calc
      (T i).toConvexSpaceBody = ((T i).rescale δ).toConvexSpaceBody := by simp
      _ ≤ ((T a).rescale ρ).toConvexSpaceBody :=
        Tube.rescale_le_rescale_of_endpoint_dist (T i) (T a) hdist_add
  have hterm : ∀ a ∈ F', ((σ a).card : ℝ) ≤ (C : ℝ) := by
    intro a haF'
    dsimp [σ]
    exact_mod_cast (h.boundedOverlap ((T a).rescale ρ))
  have hcard_unpack : (G.card : ℝ) ≤ ∑ a ∈ F', ((σ a).card : ℝ) := by
    calc
      (G.card : ℝ) ≤ ((F'.biUnion σ).card : ℝ) := by
        exact_mod_cast (Finset.card_le_card hGsub)
      _ ≤ ∑ a ∈ F', ((σ a).card : ℝ) := by
        have hb := Finset.card_biUnion_le (s := F') (t := σ)
        exact_mod_cast hb
  have hsum : (∑ a ∈ F', ((σ a).card : ℝ)) ≤ (F'.card : ℝ) * (C : ℝ) := by
    calc
      (∑ a ∈ F', ((σ a).card : ℝ)) ≤ ∑ a ∈ F', (C : ℝ) := Finset.sum_le_sum hterm
      _ = (F'.card : ℝ) * (C : ℝ) := by
        rw [Finset.sum_const]
        simp
  calc
    (G.card : ℝ) ≤ ∑ a ∈ F', ((σ a).card : ℝ) := hcard_unpack
    _ ≤ (F'.card : ℝ) * (C : ℝ) := hsum
    _ ≤ B * (C : ℝ) := by
      exact mul_le_mul_of_nonneg_right hcardF' (by positivity : 0 ≤ (C : ℝ))

/-- Dimensional constant of the cross-scale parent density transfer: the volume ratio of
`Tube.volume_le`/`Tube.le_volume`, the `L¹` box packing count `2 · 25^{2n}` of
`card_parents_meeting_tube_le`, and the thickening blowup `5^n`. -/
noncomputable def crossScaleConst (n : ℕ) : NNReal :=
  Tube.volume_le.C n / Tube.le_volume.c n * (2 * 25 ^ (2 * n)) * 5 ^ n

/-- **A cross-scale node cover with a density bound.**  `HasNodeCoverAt s T ρ Λ A` says that `T`
admits, at some scale `r ∈ [ρ, 1]` within a factor `Λ` of `ρ`, a cover by a family of `r`-tubes
whose `Δ_max` is at most `A`.  This is the reading of the Katz–Tao hypothesis of
`StickyKatzTaoEstimate` that the (A) ⇒ (B) deduction actually consumes. -/
def HasNodeCoverAt {δ : NNReal} (s : Finset ι) (T : ι → Tube δ E)
    (ρ : NNReal) (Λ : ℝ) (A : ENNReal) : Prop :=
  ∃ (r : NNReal) (Q : Finset ι) (W : ι → Tube r E),
    ρ ≤ r ∧ r ≤ 1 ∧ ((r : ℝ) / (ρ : ℝ)) ≤ Λ ∧
    (∀ i ∈ s, ∃ b ∈ Q, (T i).toConvexSpaceBody ≤ (W b).toConvexSpaceBody) ∧
    Kakeya.maxDensity Q (fun b => (W b).toConvexSpaceBody) ≤ A

omit [Nontrivial E] in
/-- **Thickening by `4r` a body that already accommodates a `ρ`-ball.**  The blowup is the
dimensional factor `((ρ+4r)/ρ)ⁿ ≤ (5r/ρ)ⁿ`; this is the volume step of the cross-scale transfer,
where the test body of the parent side contains a parent `ρ`-tube and the nodes charged to it live
in its `4r`-thickening. -/
theorem volume_cthickening_four_mul_le {ρ r : NNReal} (hρ_pos : 0 < (ρ : ℝ)) (hρr : ρ ≤ r)
    (K : ConvexSpaceBody E) {p : E} (hball : Metric.closedBall p (ρ : ℝ) ⊆ K.carrier) :
    MeasureTheory.volume (K.cthickening (4 * (r : ℝ))).carrier
      ≤ ENNReal.ofReal ((5 * ((r : ℝ) / (ρ : ℝ))) ^ Module.finrank ℝ E)
          * MeasureTheory.volume K.carrier := by
  have hr_pos : (0 : ℝ) < (r : ℝ) := lt_of_lt_of_le hρ_pos (by exact_mod_cast hρr)
  have hlem := volume_cthickening_le_of_closedBall_subset
      (K := K.carrier) K.isCompact K.convex hρ_pos hball (t := 4 * (r : ℝ)) (by positivity)
  have hratio : ((ρ : ℝ) + 4 * (r : ℝ)) / (ρ : ℝ) ≤ 5 * ((r : ℝ) / (ρ : ℝ)) := by
    rw [div_le_iff₀ hρ_pos]
    field_simp [hρ_pos.ne']
    nlinarith [hr_pos, (show (ρ : ℝ) ≤ (r : ℝ) by exact_mod_cast hρr)]
  have hbase : ENNReal.ofReal (((ρ : ℝ) + 4 * (r : ℝ)) / (ρ : ℝ))
      ≤ ENNReal.ofReal (5 * ((r : ℝ) / (ρ : ℝ))) := ENNReal.ofReal_le_ofReal hratio
  have hpow : ENNReal.ofReal (((ρ : ℝ) + 4 * (r : ℝ)) / (ρ : ℝ)) ^ Module.finrank ℝ E
      ≤ ENNReal.ofReal ((5 * ((r : ℝ) / (ρ : ℝ))) ^ Module.finrank ℝ E) := by
    rw [ENNReal.ofReal_pow (by positivity : 0 ≤ 5 * ((r : ℝ) / (ρ : ℝ)))]
    mono
  calc
    MeasureTheory.volume (K.cthickening (4 * (r : ℝ))).carrier
        ≤ ENNReal.ofReal (((ρ : ℝ) + 4 * (r : ℝ)) / (ρ : ℝ)) ^ Module.finrank ℝ E
            * MeasureTheory.volume K.carrier := by
          change MeasureTheory.volume (Metric.cthickening (4 * (r : ℝ)) K.carrier) ≤ _
          exact hlem
    _ ≤ ENNReal.ofReal ((5 * ((r : ℝ) / (ρ : ℝ))) ^ Module.finrank ℝ E)
            * MeasureTheory.volume K.carrier := by
          gcongr

open scoped Classical in
/-- **Charging the parents contained in `K` to the nodes contained in its `4r`-thickening.**
Each parent holds a leaf (the branching number is at least `1`), that leaf lies in a node of the
cover, and the node then lies in `K⁺ = K.cthickening (4r)`
(`tube_le_cthickening_of_common_leaf`); at most `2 (25 r/ρ)^{2n} C` parents are charged to one
node (`card_parents_meeting_tube_le`). -/
theorem card_parents_le_mul_card_nodes {δ ρ r : NNReal} (hρ_pos : 0 < ρ) (hδρ : 2 * δ ≤ ρ)
    (hρr : ρ ≤ r) {s : Finset ι} {T : ι → Tube δ E} {C : NNReal}
    (h : Tube.IsUniformAtScale s T ρ C) (hbr : 1 ≤ h.branchingN)
    {Q : Finset ι} {W : ι → Tube r E}
    (hcover : ∀ i ∈ s, ∃ b ∈ Q, (T i).toConvexSpaceBody ≤ (W b).toConvexSpaceBody)
    (K : ConvexSpaceBody E) :
    ((h.parent.filter (fun j => (h.parentTube j).toConvexSpaceBody ≤ K)).card : ℝ)
      ≤ ((Q.filter (fun b =>
            (W b).toConvexSpaceBody ≤ K.cthickening (4 * (r : ℝ)))).card : ℝ)
          * (2 * (25 : ℝ) ^ (2 * Module.finrank ℝ E)
              * ((r : ℝ) / (ρ : ℝ)) ^ (2 * Module.finrank ℝ E) * (C : ℝ)) := by
  classical
  set PK : Finset ι := h.parent.filter (fun j => (h.parentTube j).toConvexSpaceBody ≤ K)
    with hPK_def
  set QK : Finset ι := Q.filter (fun b =>
      (W b).toConvexSpaceBody ≤ K.cthickening (4 * (r : ℝ))) with hQK_def
  set B : ℝ := 2 * (25 : ℝ) ^ (2 * Module.finrank ℝ E)
      * ((r : ℝ) / (ρ : ℝ)) ^ (2 * Module.finrank ℝ E) * (C : ℝ) with hB_def
  have hrep : ∀ j ∈ PK, ∃ i ∈ s, (T i).toConvexSpaceBody ≤ (h.parentTube j).toConvexSpaceBody := by
    intro j hj
    have hjP : j ∈ h.parent := Finset.mem_of_mem_filter j hj
    have hlb := h.le_mul_card_filter hjP
    have hpos : 0 < ({i ∈ s | (T i).toConvexSpaceBody ≤
            (h.parentTube j).toConvexSpaceBody}).card := by
      rcases Nat.eq_zero_or_pos
        ({i ∈ s | (T i).toConvexSpaceBody ≤ (h.parentTube j).toConvexSpaceBody}).card with h0 | hp
      · exfalso
        rw [h0, Nat.cast_zero, mul_zero, nonpos_iff_eq_zero] at hlb
        rw [hlb] at hbr; exact absurd hbr (by norm_num)
      · exact hp
    obtain ⟨i₀, hi₀⟩ := Finset.card_pos.mp hpos
    rw [Finset.mem_filter] at hi₀
    exact ⟨i₀, hi₀.1, hi₀.2⟩
  let i_rep : ι → ι := fun j => if hj : j ∈ PK then (hrep j hj).choose else j
  have hi_rep_mem : ∀ j ∈ PK, i_rep j ∈ s := by
    intro j hj; simp only [i_rep, dif_pos hj]; exact (hrep j hj).choose_spec.1
  have hi_rep_le : ∀ j ∈ PK,
      (T (i_rep j)).toConvexSpaceBody ≤ (h.parentTube j).toConvexSpaceBody := by
    intro j hj; simp only [i_rep, dif_pos hj]; exact (hrep j hj).choose_spec.2
  have bhrep : ∀ j ∈ PK, ∃ b ∈ Q, (T (i_rep j)).toConvexSpaceBody ≤ (W b).toConvexSpaceBody := by
    intro j hj
    exact hcover (i_rep j) (hi_rep_mem j hj)
  let b_rep : ι → ι := fun j => if hj : j ∈ PK then (bhrep j hj).choose else j
  have b_rep_mem : ∀ j ∈ PK, b_rep j ∈ Q := by
    intro j hj; simp only [b_rep, dif_pos hj]; exact (bhrep j hj).choose_spec.1
  have b_rep_le : ∀ j ∈ PK,
      (T (i_rep j)).toConvexSpaceBody ≤ (W (b_rep j)).toConvexSpaceBody := by
    intro j hj; simp only [b_rep, dif_pos hj]; exact (bhrep j hj).choose_spec.2
  have hmaps : ∀ j ∈ PK, b_rep j ∈ QK := by
    intro j hj
    have hKj : (h.parentTube j).toConvexSpaceBody ≤ K := (Finset.mem_filter.mp hj).2
    have hTj : (T (i_rep j)).toConvexSpaceBody ≤ K := le_trans (hi_rep_le j hj) hKj
    have hWj : (W (b_rep j)).toConvexSpaceBody ≤ K.cthickening (4 * (r : ℝ)) :=
      tube_le_cthickening_of_common_leaf (T (i_rep j)) (W (b_rep j)) (b_rep_le j hj) hTj
    dsimp [QK]
    exact Finset.mem_filter.mpr ⟨b_rep_mem j hj, hWj⟩
  have hfibre_nat : PK.card = ∑ b ∈ QK, (PK.filter (fun j => b_rep j = b)).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  have hfibre : (PK.card : ℝ) = ∑ b ∈ QK, ((PK.filter (fun j => b_rep j = b)).card : ℝ) := by
    exact_mod_cast hfibre_nat
  have hfibre_le : ∀ b ∈ QK, ((PK.filter (fun j => b_rep j = b)).card : ℝ) ≤ B := by
    intro b hb
    have hsub : PK.filter (fun j => b_rep j = b) ⊆ h.parent.filter (fun j => ∃ i ∈ s,
        (T i).toConvexSpaceBody ≤ (h.parentTube j).toConvexSpaceBody ∧
        (T i).toConvexSpaceBody ≤ (W b).toConvexSpaceBody) := by
      intro j hj
      rw [Finset.mem_filter] at hj ⊢
      rcases hj with ⟨hjPK, hbj⟩
      have hjP : j ∈ h.parent := Finset.mem_of_mem_filter j hjPK
      exact ⟨hjP, i_rep j, hi_rep_mem j hjPK, hi_rep_le j hjPK, by
        rw [← hbj]; exact b_rep_le j hjPK⟩
    have hcardsub : ((PK.filter (fun j => b_rep j = b)).card : ℝ)
        ≤ ((h.parent.filter (fun j => ∃ i ∈ s,
            (T i).toConvexSpaceBody ≤ (h.parentTube j).toConvexSpaceBody ∧
            (T i).toConvexSpaceBody ≤ (W b).toConvexSpaceBody)).card : ℝ) := by
      exact_mod_cast (Finset.card_le_card hsub)
    have hpack := card_parents_meeting_tube_le hρ_pos hδρ hρr (h := h) (W b)
    calc
      ((PK.filter (fun j => b_rep j = b)).card : ℝ) ≤
          ((h.parent.filter (fun j => ∃ i ∈ s,
            (T i).toConvexSpaceBody ≤ (h.parentTube j).toConvexSpaceBody ∧
            (T i).toConvexSpaceBody ≤ (W b).toConvexSpaceBody)).card : ℝ) := hcardsub
      _ ≤ 2 * (25 : ℝ) ^ (2 * Module.finrank ℝ E)
            * ((r : ℝ) / (ρ : ℝ)) ^ (2 * Module.finrank ℝ E) * (C : ℝ) := hpack
      _ = B := by simp [B]
  have hsum : (∑ b ∈ QK, ((PK.filter (fun j => b_rep j = b)).card : ℝ)) ≤ (QK.card : ℝ) * B := by
    calc
      (∑ b ∈ QK, ((PK.filter (fun j => b_rep j = b)).card : ℝ))
          ≤ ∑ b ∈ QK, B := Finset.sum_le_sum (fun b hb => hfibre_le b hb)
      _ = (QK.card : ℝ) * B := by
        rw [Finset.sum_const]
        simp
  calc
    ((h.parent.filter (fun j => (h.parentTube j).toConvexSpaceBody ≤ K)).card : ℝ)
        = (PK.card : ℝ) := by simp [PK]
    _ = ∑ b ∈ QK, ((PK.filter (fun j => b_rep j = b)).card : ℝ) := hfibre
    _ ≤ (QK.card : ℝ) * B := hsum
    _ = ((Q.filter (fun b =>
            (W b).toConvexSpaceBody ≤ K.cthickening (4 * (r : ℝ)))).card : ℝ) * B := by simp [QK]
    _ = ((Q.filter (fun b =>
            (W b).toConvexSpaceBody ≤ K.cthickening (4 * (r : ℝ)))).card : ℝ)
          * (2 * (25 : ℝ) ^ (2 * Module.finrank ℝ E)
              * ((r : ℝ) / (ρ : ℝ)) ^ (2 * Module.finrank ℝ E) * (C : ℝ)) := by simp [B]

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- Constant bookkeeping for `uniform_parent_maxDensity_le_of_nodeCover`, packing step: the
parent-volume side against the node-volume side, the loss being the tube volume ratio and
`ρ^{n-1} ≤ r^{n-1}`. -/
theorem crossScaleConst_step_le (n : ℕ) (C : NNReal) {ρ r : NNReal} (hρr : ρ ≤ r) :
    ENNReal.ofReal (2 * (25 : ℝ) ^ (2 * n) * ((r : ℝ) / (ρ : ℝ)) ^ (2 * n) * (C : ℝ))
        * ((↑(Tube.volume_le.C n) : ENNReal) * (ρ : ENNReal) ^ (n - 1))
      ≤ (↑(Tube.volume_le.C n / Tube.le_volume.c n * C) : ENNReal)
          * ENNReal.ofReal (2 * (25 : ℝ) ^ (2 * n) * ((r : ℝ) / (ρ : ℝ)) ^ (2 * n))
          * ((↑(Tube.le_volume.c n) : ENNReal) * (r : ENNReal) ^ (n - 1)) := by
  set x : ℝ := 2 * (25 : ℝ) ^ (2 * n) * ((r : ℝ) / (ρ : ℝ)) ^ (2 * n) with hx
  have hx_pos : 0 ≤ x := by
    dsimp [x]
    positivity
  have hc_ne : Tube.le_volume.c n ≠ 0 := (Tube.le_volume.c_pos n).ne'
  have hcoef :
      (↑(Tube.volume_le.C n / Tube.le_volume.c n * C) : ENNReal)
          * (↑(Tube.le_volume.c n) : ENNReal)
        = (↑(Tube.volume_le.C n) : ENNReal) * (↑C : ENNReal) := by
    rw [← ENNReal.coe_mul, ← ENNReal.coe_mul]
    congr 1
    rw [div_mul_eq_mul_div]
    rw [div_mul_cancel₀ _ hc_ne]
  have hp : (ρ : ENNReal) ^ (n - 1) ≤ (r : ENNReal) ^ (n - 1) := by
    exact pow_le_pow_left₀ zero_le (ENNReal.coe_le_coe.mpr hρr) (n - 1)
  calc
    ENNReal.ofReal (x * (C : ℝ))
        * ((↑(Tube.volume_le.C n) : ENNReal) * (ρ : ENNReal) ^ (n - 1))
        = (↑(Tube.volume_le.C n) : ENNReal) * (↑C : ENNReal) * ENNReal.ofReal x
            * (ρ : ENNReal) ^ (n - 1) := by
            rw [ENNReal.ofReal_mul hx_pos]
            rw [ENNReal.ofReal_coe_nnreal]
            ring
    _ ≤ (↑(Tube.volume_le.C n) : ENNReal) * (↑C : ENNReal) * ENNReal.ofReal x
            * (r : ENNReal) ^ (n - 1) := by
            exact mul_le_mul_right hp _
    _ = (↑(Tube.volume_le.C n / Tube.le_volume.c n * C) : ENNReal) * ENNReal.ofReal x
            * ((↑(Tube.le_volume.c n) : ENNReal) * (r : ENNReal) ^ (n - 1)) := by
            rw [← hcoef]
            ring

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- Constant bookkeeping for `uniform_parent_maxDensity_le_of_nodeCover`, thickening step:
`2·25^{2n}·t^{2n} · (5t)^n = (2·25^{2n}·5^n) · t^{3n}` folds into `crossScaleConst`. -/
theorem crossScaleConst_mul_le (n : ℕ) (C : NNReal) {ρ r : NNReal} (hρ_pos : 0 < (ρ : ℝ))
    (_hρr : ρ ≤ r) :
    (↑(Tube.volume_le.C n / Tube.le_volume.c n * C) : ENNReal)
        * ENNReal.ofReal (2 * (25 : ℝ) ^ (2 * n) * ((r : ℝ) / (ρ : ℝ)) ^ (2 * n))
        * ENNReal.ofReal ((5 * ((r : ℝ) / (ρ : ℝ))) ^ n)
      ≤ (↑(crossScaleConst n * C) : ENNReal)
          * ENNReal.ofReal (((r : ℝ) / (ρ : ℝ)) ^ (3 * n)) := by
  set t : ℝ := (r : ℝ) / (ρ : ℝ) with ht
  set cNN : NNReal := 2 * (25 : NNReal) ^ (2 * n) * 5 ^ n with hcNN
  have ht_nonneg : 0 ≤ t := by
    dsimp [t]
    positivity
  have hprod_real : 2 * (25 : ℝ) ^ (2 * n) * t ^ (2 * n) * (5 * t) ^ n
      = (2 * (25 : ℝ) ^ (2 * n) * 5 ^ n) * t ^ (3 * n) := by
    have hn3 : 3 * n = 2 * n + n := by ring
    rw [hn3, pow_add, mul_pow]
    ring
  have hbr :
      ENNReal.ofReal (2 * (25 : ℝ) ^ (2 * n) * t ^ (2 * n))
        * ENNReal.ofReal ((5 * t) ^ n)
      = ENNReal.ofReal ((2 * (25 : ℝ) ^ (2 * n) * 5 ^ n) * t ^ (3 * n)) := by
    rw [← ENNReal.ofReal_mul, hprod_real]
    positivity
  have hcast_expr : (cNN : ℝ) = 2 * (25 : ℝ) ^ (2 * n) * 5 ^ n := by
    dsimp [cNN]
  have hsplit :
      ENNReal.ofReal ((2 * (25 : ℝ) ^ (2 * n) * 5 ^ n) * t ^ (3 * n))
      = (cNN : ENNReal) * ENNReal.ofReal (t ^ (3 * n)) := by
    rw [ENNReal.ofReal_mul]
    · rw [← hcast_expr, ENNReal.ofReal_coe_nnreal]
    · positivity
  have hcoef : (Tube.volume_le.C n / Tube.le_volume.c n * C) * cNN = crossScaleConst n * C := by
    unfold crossScaleConst cNN
    ring
  exact le_of_eq (by
    calc
      (↑(Tube.volume_le.C n / Tube.le_volume.c n * C) : ENNReal)
          * ENNReal.ofReal (2 * (25 : ℝ) ^ (2 * n) * t ^ (2 * n))
          * ENNReal.ofReal ((5 * t) ^ n)
        = (↑(Tube.volume_le.C n / Tube.le_volume.c n * C) : ENNReal)
            * (ENNReal.ofReal (2 * (25 : ℝ) ^ (2 * n) * t ^ (2 * n))
                * ENNReal.ofReal ((5 * t) ^ n)) := by
            rw [mul_assoc]
      _ = (↑(Tube.volume_le.C n / Tube.le_volume.c n * C) : ENNReal)
            * ENNReal.ofReal ((2 * (25 : ℝ) ^ (2 * n) * 5 ^ n) * t ^ (3 * n)) := by
            rw [hbr]
      _ = (↑(Tube.volume_le.C n / Tube.le_volume.c n * C) : ENNReal)
            * ((cNN : ENNReal) * ENNReal.ofReal (t ^ (3 * n))) := by
            rw [hsplit]
      _ = (↑((Tube.volume_le.C n / Tube.le_volume.c n * C) * cNN) : ENNReal)
            * ENNReal.ofReal (t ^ (3 * n)) := by
            rw [← mul_assoc, ← ENNReal.coe_mul]
      _ = (↑(crossScaleConst n * C) : ENNReal) * ENNReal.ofReal (t ^ (3 * n)) := by
            rw [hcoef])

open scoped Pointwise Classical in
/-- **Node → parent `Δ_max` transfer across scales.**  A `C`-uniform structure at scale `ρ` whose
leaves are covered by a family of `r`-tubes of density at most `A` (`ρ ≤ r ≤ 1`, `2δ ≤ ρ`) has its
parent family bounded by `crossScaleConst n · C · (r/ρ)^{3n} · A`. -/
theorem uniform_parent_maxDensity_le_of_nodeCover
    {δ ρ r : NNReal} (hδ : 0 < δ) (hδρ : 2 * δ ≤ ρ) (hρr : ρ ≤ r) (hr1 : r ≤ 1)
    {s : Finset ι} {T : ι → Tube δ E} {C : NNReal}
    (h : Tube.IsUniformAtScale s T ρ C) (hbr : 1 ≤ h.branchingN)
    {Q : Finset ι} {W : ι → Tube r E}
    (hcover : ∀ i ∈ s, ∃ b ∈ Q, (T i).toConvexSpaceBody ≤ (W b).toConvexSpaceBody)
    {A : ENNReal}
    (hA : Kakeya.maxDensity Q (fun b => (W b).toConvexSpaceBody) ≤ A) :
    Kakeya.maxDensity (h.parent.image h.parentTube) (fun u : Tube ρ E => u.toConvexSpaceBody)
      ≤ (↑(crossScaleConst (Module.finrank ℝ E) * C) : ENNReal)
          * ENNReal.ofReal (((r : ℝ) / (ρ : ℝ)) ^ (3 * Module.finrank ℝ E)) * A := by
  classical
  set n := Module.finrank ℝ E with hn_def
  have hρ_pos : 0 < ρ := lt_of_lt_of_le (mul_pos (by norm_num) hδ) hδρ
  have hρ_pos_real : (0 : ℝ) < (ρ : ℝ) := by exact_mod_cast hρ_pos
  have hρ1 : ρ ≤ 1 := hρr.trans hr1
  set t : ℝ := (r : ℝ) / (ρ : ℝ) with ht
  let Cv : ENNReal := ↑(Tube.volume_le.C n)
  let cv : ENNReal := ↑(Tube.le_volume.c n)
  let B : ℝ := 2 * (25 : ℝ) ^ (2 * n) * t ^ (2 * n) * (C : ℝ)
  let Λ : ENNReal := (↑(Tube.volume_le.C n / Tube.le_volume.c n * C) : ENNReal)
      * ENNReal.ofReal (2 * (25 : ℝ) ^ (2 * n) * t ^ (2 * n))
  rw [Kakeya.maxDensity_le_iff]
  intro K
  rcases eq_or_ne (volume K.carrier) 0 with hK0 | hK0
  · rw [Kakeya.densityIn_eq_zero_of_volume_eq_zero hK0]
    exact bot_le
  let Kp : ConvexSpaceBody E := K.cthickening (4 * (r : ℝ))
  set PK : Finset ι := h.parent.filter (fun j => (h.parentTube j).toConvexSpaceBody
      ≤ K) with hPK_def
  set QK : Finset ι := Q.filter (fun b => (W b).toConvexSpaceBody ≤ Kp) with hQK_def
  have hnum : (∑ u ∈ (h.parent.image h.parentTube) with u.toConvexSpaceBody ≤ K, volume u.carrier)
      = ∑ j ∈ PK, volume (h.parentTube j).carrier := by
    simp only [hPK_def, Finset.sum_filter]
    exact Finset.sum_image (fun a ha b hb hab =>
      h.parentTube_injOn (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hab)
  have hpar : ∑ j ∈ PK, volume (h.parentTube j).carrier
      ≤ (PK.card : ENNReal) * (Cv * (ρ : ENNReal) ^ (n - 1)) := by
    calc
      ∑ j ∈ PK, volume (h.parentTube j).carrier ≤ ∑ j ∈ PK, Cv * (ρ : ENNReal) ^ (n - 1) := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        have hv := Tube.volume_le hρ1 (h.parentTube j)
        rw [← hn_def] at hv
        simpa [Cv] using hv
      _ = (PK.card : ENNReal) * (Cv * (ρ : ENNReal) ^ (n - 1)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
  have hQvol : (QK.card : ENNReal) * (cv * (r : ENNReal) ^ (n - 1))
      ≤ ∑ b ∈ QK, volume (W b).carrier := by
    have hb : ∀ b ∈ QK, cv * (r : ENNReal) ^ (n - 1) ≤ volume (W b).carrier := by
      intro b _
      have hv := Tube.le_volume (W b)
      rw [← hn_def] at hv
      simpa [cv] using hv
    rw [← nsmul_eq_mul]
    exact Finset.card_nsmul_le_sum QK (fun b => volume (W b).carrier)
      (cv * (r : ENNReal) ^ (n - 1)) hb
  have hdens : ∑ b ∈ QK, volume (W b).carrier ≤ A * volume Kp.carrier := by
    have hle : Kakeya.densityIn Q (fun b => (W b).toConvexSpaceBody) Kp ≤ A :=
      le_trans (Kakeya.le_maxDensity Q (fun b => (W b).toConvexSpaceBody) Kp) hA
    have hd := (Kakeya.densityIn_le_iff Q (fun b => (W b).toConvexSpaceBody) Kp A).mp hle
    rw [← hQK_def] at hd
    exact hd
  have hcnt : (PK.card : ENNReal) ≤ (QK.card : ENNReal) * ENNReal.ofReal B := by
    have h0 := card_parents_le_mul_card_nodes hρ_pos hδρ hρr h hbr hcover K
    have hraw : (PK.card : ℝ) ≤ (QK.card : ℝ) * B := by
      simpa [← hPK_def, ← hQK_def, ← ht, ← hn_def, B] using h0
    have hraw' : ENNReal.ofReal (PK.card : ℝ) ≤ ENNReal.ofReal ((QK.card : ℝ) * B) :=
      ENNReal.ofReal_le_ofReal hraw
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (QK.card : ℝ))] at hraw'
    rwa [ENNReal.ofReal_natCast, ENNReal.ofReal_natCast] at hraw'
  rcases PK.eq_empty_or_nonempty with hPKe | hPKne
  · refine (Kakeya.densityIn_le_iff _ _ _ _).mpr ?_
    rw [hnum, hPKe, Finset.sum_empty]
    exact bot_le
  · obtain ⟨j₀, hj₀⟩ := hPKne
    have hball : Metric.closedBall ((h.parentTube j₀).x) (ρ : ℝ) ⊆ K.carrier := by
      have h1 : Metric.closedBall ((h.parentTube j₀).x) (ρ : ℝ) ⊆ (h.parentTube j₀).carrier := by
        rw [(h.parentTube j₀).carrier_eq]
        exact fun w hw => Set.mem_biUnion (left_mem_segment ℝ _ _) hw
      exact h1.trans (Finset.mem_filter.mp hj₀).2
    have hKplus : volume Kp.carrier ≤ ENNReal.ofReal ((5 * t) ^ n) * volume K.carrier := by
      have hlem := volume_cthickening_four_mul_le hρ_pos_real hρr K hball
      simpa [Kp, ← ht, ← hn_def] using hlem
    have hmain : (∑ j ∈ PK, volume (h.parentTube j).carrier)
        ≤ (↑(crossScaleConst n * C) : ENNReal) * ENNReal.ofReal (t ^ (3 * n))
            * (A * volume K.carrier) := by
      calc
        (∑ j ∈ PK, volume (h.parentTube j).carrier)
            ≤ (PK.card : ENNReal) * (Cv * (ρ : ENNReal) ^ (n - 1)) := hpar
        _ ≤ ((QK.card : ENNReal) * ENNReal.ofReal B) * (Cv * (ρ : ENNReal) ^ (n - 1)) := by
              gcongr
        _ = (QK.card : ENNReal) * (ENNReal.ofReal B * (Cv * (ρ : ENNReal) ^ (n - 1))) := by ring
        _ ≤ (QK.card : ENNReal) * (Λ * (cv * (r : ENNReal) ^ (n - 1))) := by
              have hstep : ENNReal.ofReal B * (Cv * (ρ : ENNReal) ^ (n - 1))
                  ≤ Λ * (cv * (r : ENNReal) ^ (n - 1)) := by
                simpa [B, Λ, Cv, cv, ← ht] using crossScaleConst_step_le n C hρr
              gcongr
        _ = Λ * ((QK.card : ENNReal) * (cv * (r : ENNReal) ^ (n - 1))) := by ring
        _ ≤ Λ * (∑ b ∈ QK, volume (W b).carrier) := by
              gcongr
        _ ≤ Λ * (A * volume Kp.carrier) := by
              gcongr
        _ ≤ Λ * (A * (ENNReal.ofReal ((5 * t) ^ n) * volume K.carrier)) := by
              gcongr
        _ = (Λ * ENNReal.ofReal ((5 * t) ^ n)) * (A * volume K.carrier) := by ring
        _ ≤ (↑(crossScaleConst n * C) : ENNReal) * ENNReal.ofReal (t ^ (3 * n))
              * (A * volume K.carrier) := by
              have hf : Λ * ENNReal.ofReal ((5 * t) ^ n)
                  ≤ (↑(crossScaleConst n * C) : ENNReal) * ENNReal.ofReal (t ^ (3 * n)) := by
                simpa [Λ, ← ht] using crossScaleConst_mul_le n C hρ_pos_real hρr
              gcongr
    refine (Kakeya.densityIn_le_iff _ _ _ _).mpr ?_
    rw [hnum]
    exact hmain.trans (le_of_eq (by ring))

/-- **The grid length diverges.**  `ssfGridLen δ = ⌈log log (1/δ)⌉₊` exceeds any fixed bound once
`δ` is small enough.  This is the threshold that makes the grid-rounding loss `δ^{-1/ssfGridLen δ}`
of `exists_nodeCover_of_isKatzTaoAtEveryScale` subpolynomial. -/
theorem exists_threshold_le_ssfGridLen (K : ℝ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ {δ : NNReal}, 0 < δ → (δ : ℝ) ≤ δ₀ → K ≤ (ssfGridLen δ : ℝ) := by
  let δ₀ : ℝ := min (Real.exp (-(Real.exp (max K 0)))) (1 / 2)
  refine ⟨δ₀, ?_, ?_⟩
  · have h1 : (0 : ℝ) < Real.exp (-(Real.exp (max K 0))) := Real.exp_pos _
    exact lt_min h1 (by norm_num)
  · intro δ hδ hδle
    have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
    have hδ1 : 0 < 1 / (δ : ℝ) := one_div_pos.mpr hδR
    have hδle_eval : (δ : ℝ) ≤ Real.exp (-(Real.exp (max K 0))) :=
      le_trans hδle (min_le_left _ (1 / 2))
    have hE : Real.exp (Real.exp (max K 0)) ≤ 1 / (δ : ℝ) := by
      have hht : (δ : ℝ) ≤ (Real.exp (Real.exp (max K 0)))⁻¹ := by
        rw [← Real.exp_neg]
        exact hδle_eval
      have hEpos : 0 < Real.exp (Real.exp (max K 0)) := Real.exp_pos _
      have hmul : (δ : ℝ) * Real.exp (Real.exp (max K 0)) ≤ 1 := by
        calc
          (δ : ℝ) * Real.exp (Real.exp (max K 0))
              ≤ (Real.exp (Real.exp (max K 0)))⁻¹ * Real.exp (Real.exp (max K 0)) :=
                mul_le_mul_of_nonneg_right hht (le_of_lt hEpos)
          _ = 1 := inv_mul_cancel₀ hEpos.ne'
      exact (le_div_iff₀ hδR).mpr (by simpa [mul_comm] using hmul)
    have h_expm_le_log : Real.exp (max K 0) ≤ Real.log (1 / (δ : ℝ)) :=
      (Real.le_log_iff_exp_le hδ1).mpr hE
    have hδlt1 : (δ : ℝ) < 1 := by
      have hle12 : (δ : ℝ) ≤ 1 / 2 := le_trans hδle (min_le_right _ _)
      linarith
    have hlog1pos : 0 < Real.log (1 / (δ : ℝ)) := by
      have hgt1 : 1 < 1 / (δ : ℝ) := one_lt_one_div hδR hδlt1
      exact Real.log_pos hgt1
    have hm_le : max K 0 ≤ Real.log (Real.log (1 / (δ : ℝ))) :=
      (Real.le_log_iff_exp_le hlog1pos).mpr h_expm_le_log
    have hceil : Real.log (Real.log (1 / (δ : ℝ))) ≤ (ssfGridLen δ : ℝ) := by
      dsimp [ssfGridLen]
      exact Nat.le_ceil (Real.log (Real.log (1 / (δ : ℝ))))
    calc
      K ≤ max K 0 := le_max_left K 0
      _ ≤ Real.log (Real.log (1 / (δ : ℝ))) := hm_le
      _ ≤ (ssfGridLen δ : ℝ) := hceil

omit [Nontrivial E] in
open scoped Classical in
/-- **Rounding an arbitrary grid scale to a scale of the bundle's own grid.**  Given a uniform
bundle of grid length `N` satisfying the node Katz–Tao condition, every scale `δ^{k/M}` of another
grid of length `M` admits a node cover at the rounded scale `δ^{k'/N}`, `k' = ⌊kN/M⌋`, at a
rounding loss of at most one step of the bundle's grid, `δ^{-1/N}`. -/
theorem exists_nodeCover_of_isKatzTaoAtEveryScale
    {δ : NNReal} (hδ_pos : 0 < δ) (hδ_lt1 : δ < 1) {s : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} (hN : 0 < N) {C : NNReal} (𝒰 : UniformTubeSet s T N C) {A : ENNReal}
    (hKT : 𝒰.IsKatzTaoAtEveryScale A) {M : ℕ} (hM : 0 < M) (k : ℕ) (hk : k ≤ M) :
    HasNodeCoverAt s T (δ ^ ((k : ℝ) / (M : ℝ))) ((δ : ℝ) ^ (-(1 / (N : ℝ)))) A := by
  classical
  let k' : ℕ := k * N / M
  have hk' : k' ≤ N := by
    dsimp [k']
    calc
      k * N / M ≤ (M * N) / M := Nat.div_le_div_right (Nat.mul_le_mul_right N hk)
      _ = N := Nat.mul_div_cancel_left N hM
  refine ⟨gridScale δ N k', 𝒰.cover.indexSet k', 𝒰.cover.tube k', ?_, ?_, ?_, ?_, ?_⟩
  · have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
    have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hmul : (k' : ℝ) * (M : ℝ) ≤ (k : ℝ) * (N : ℝ) := by
      have hle : k' * M ≤ k * N := by
        dsimp [k']
        exact Nat.div_mul_le_self (k * N) M
      exact_mod_cast hle
    have hexp : (k' : ℝ) / (N : ℝ) ≤ (k : ℝ) / (M : ℝ) := by
      field_simp [hN0.ne', hM0.ne']
      nlinarith [hmul]
    rw [gridScale]
    exact NNReal.rpow_le_rpow_of_exponent_ge hδ_pos hδ_lt1.le hexp
  · exact gridScale_le_one hδ_lt1.le N k'
  · have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
    have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hδ0 : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ_pos
    have hδ1real : (δ : ℝ) < 1 := by exact_mod_cast hδ_lt1
    have hsubR : (k : ℝ) * (N : ℝ) - (k' : ℝ) * (M : ℝ) < (M : ℝ) := by
      have hle : k' * M ≤ k * N := by
        dsimp [k']
        exact Nat.div_mul_le_self (k * N) M
      have hsub : k * N - k' * M < M := by
        dsimp [k']
        have hdivmod' : k * N = (k * N / M) * M + (k * N) % M := by
          calc
            k * N = M * (k * N / M) + (k * N) % M := (Nat.div_add_mod (k * N) M).symm
            _ = (k * N / M) * M + (k * N) % M := by rw [Nat.mul_comm M (k * N / M)]
        have hmodlt : (k * N) % M < M := Nat.mod_lt (k * N) hM
        omega
      have hcast : ((k * N - k' * M : ℕ) : ℝ) < (M : ℝ) := by exact_mod_cast hsub
      simpa [Nat.cast_sub hle] using hcast
    have hexp_goal : -(1 / (N : ℝ)) ≤ (k' : ℝ) / (N : ℝ) - (k : ℝ) / (M : ℝ) := by
      field_simp [hM0.ne', hN0.ne']
      linarith
    change (δ : ℝ) ^ ((k' : ℝ) / (N : ℝ)) / (δ : ℝ) ^ ((k : ℝ) / (M : ℝ))
        ≤ (δ : ℝ) ^ (-(1 / (N : ℝ)))
    rw [← Real.rpow_sub hδ0]
    exact Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1real.le hexp_goal
  · intro i hi
    refine ⟨𝒰.cover.assign k' i, 𝒰.cover.assign_mem k' hk' i hi, ?_⟩
    exact 𝒰.cover.le_tube_assign k' hk' i hi
  · exact hKT k' hk'

end StickyKakeya

end Kakeya
