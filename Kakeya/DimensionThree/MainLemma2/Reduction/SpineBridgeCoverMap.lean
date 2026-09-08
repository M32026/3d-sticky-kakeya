/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineDefectCoveringBridge

/-!
# The bridge's cover map `ϖ : 𝕌 ↠ 𝕍` — `eq:defect-bridge-cover-map`

`Reduction/SpineDefectCoveringBridge.lean` binds four clauses about the canonical exact cover map
(refined l.5512–5515): `hϖmaps`, `hϖsurj`, the containment `L(S) ⊂ ϖ(S)`, and the fibre bound
`#ϖ⁻¹(V) ≤ 5000⁶·A` (`hϖfib` + `hAfib`).  This leaf produces all four.

## Source of record

`lemcanonicalcover` (refined l.4774–4784) is the canonical exact tube cover: for `0 < r ≤ 1/80`
and sets `X_i ⊆ B̄(0,2/5)` each inside the `r`-neighbourhood of an oriented line, there is a family
`𝒞_r` of exact `4r`-tubes in `B(0,3/4)` and a **surjection** `ϖ : i ↦ C_i` with `X_i ⊆ C_i`, and
`𝒞_r` is `A₀`-essentially distinct with `A₀ = 2·223⁶`.  The `5000⁶` is not from that lemma: it is
`F₀` of `eq:rescalingledger` (l.4811–4814), and l.4823–4826 says where it comes from — "inverting
a `10δ/(8ρ)` line tube and using the fact that the original tubes are line-based
`A`-essentially distinct gives the fibre bound".  So `F₀` is the **packing cost of reading the
family's line-essential-distinctness at the node's radius instead of the tube's own**.

## What the tree already had, and what was missing

`Kakeya.Tube.exists_canonicalCentredCover` (`MainLemma2/CanonicalCentredCover.lean:608`) is
`lemcanonicalcover`, existing: it delivers the map `ϖ`, `∀ i ∈ s, ϖ i ∈ G`, **`∀ W ∈ G, ∃ i ∈ s,
ϖ i = W`** (that is `hϖsurj`, verbatim), the exact containment
`(T i).toConvexSpaceBody ≤ (ϖ i).toConvexSpaceBody`, and the node family's line-ED at `5ρ` with
`Tube.canonicalCoverEDConstant`.  The one clause it does **not** expose is the fibre bound.

`card_fibre_le_of_lineEDAt` supplies it, and the argument is the source's own: every member of a
fibre is contained in its node `W`, hence in `N_{5ρ}(core W)` by
`Kakeya.VeryNotSticky.carrier_subset_own_lineNbhd`, hence in `N_{Kδ}(core W)` once `5ρ ≤ Kδ`; so
line-based `A`-essential distinctness **at radius `Kδ`** charges at most `A` of them to `W`.
`exists_coverMap_of_canonicalCentredCover` is the two composed, and
`coverMap_fills_bridge_binders` is the tie: it produces the bridge's four clauses with
`Afib := A`, so `hAfib : (Afib : ℝ) ≤ 5000⁶·A` holds outright — the source's constant is pure
slack on this route.

Family / shading / level pair: `s` is the level-`b` family `𝕌 ⊆ 𝕋_b⟨S_a⟩` of `δ`-tubes **after
the normalisation of `S_a`** (`δ` is the normalised fine radius, `ρ = δ̃ = ρ_b/(2ρ_a)` the exact
cover's radius); `G = 𝕍` is the family of exact `ρ`-tubes; `ϖ : 𝕌 ↠ 𝕍` is at that single level
pair and carries no shading — the induced shading `Z'(S') = ⋃_{ϖ(S)=S'} L(Z(S))` (l.4817) is a
separate object and is **not** used by the bridge.

## The `5000⁶`, measured — and a NAMED `max`

The hypothesis `IsLineEssDistinctAt K A s T` above is at the **node's** radius, `K ≥ 5ρ/δ ≥ 20`
(the cover needs `4δ ≤ ρ`).  The tree's data are at radius `5` (`IsLineEssDistinct`) or at
`Tube.tubeOverlapCoreClose.C 3`.  `lineED_push_radius` is the conversion, built here from the
existing net (`Tube.exists_centred_net`), the existing packing count
(`Tube.card_filter_line_le_of_centred_sep`) and the existing core comparison
(`Kakeya.VeryNotSticky.carrier_subset_lineNbhd`) — exactly the three ingredients of l.4794–4797.
Its cost is `2·linePackingConstant n R₀ (3/2 + (K−1)(5+4R₀)) 8`.

**That constant is bigger than the source's `F₀ = 5000⁶`**, and the gap is not marginal:
`source_lt_tree_constant_at_twenty` compiles the comparison at the smallest admissible ratio
`K = 20`, `n = 3`, `R₀ = 1`.  So `coverFibreConstant` is a NAMED `max` of the two, with
`source_le_coverFibreConstant` / `push_le_coverFibreConstant` its two sides and
`coverFibreConstant_eq_at_twenty` the `_eq` that says which side wins there.
`push_constant_not_below_source` is the control: on the **push** route the bridge's `hAfib` as
written (`≤ 5000⁶·A`) is FALSE, so a caller that reaches the cover map through the push must read
`hAfib` against `coverFibreConstant`, not against `5000⁶`.  On the **direct** route
(`coverMap_fills_bridge_binders`, the datum already at radius `K`) `hAfib` holds as written and
nothing changes.  The bridge statement is therefore left exactly as existing.
-/

@[expose] public section

open Kakeya Kakeya.VeryNotSticky

namespace Kakeya.ML2Core

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
open scoped Classical in
/-- **The cover map's fibre bound at the enlarged radius.** -/
theorem card_fibre_le_of_lineEDAt {δ ρ : NNReal} {ι : Type*} {s : Finset ι} {T : ι → Tube δ E}
    {ϖ : ι → Tube ρ E} {K : ℝ} {A : ℕ}
    (hED : IsLineEssDistinctAt K A s T)
    (hK : 5 * (ρ : ℝ) ≤ K * (δ : ℝ))
    (hcov : ∀ i ∈ s, (T i).toConvexSpaceBody ≤ (ϖ i).toConvexSpaceBody)
    (W : Tube ρ E) :
    (s.filter (fun i ↦ ϖ i = W)).card ≤ A := by
  classical
  refine le_trans (Finset.card_le_card ?_) (hED W.x W.direction W.norm_direction)
  intro i hi
  rw [Finset.mem_filter] at hi ⊢
  obtain ⟨his, hiW⟩ := hi
  refine ⟨his, ?_⟩
  have h1 : (T i).carrier ⊆ (ϖ i).carrier := hcov i his
  have h2 : (ϖ i).carrier ⊆ lineNbhd (ϖ i).x (ϖ i).direction (5 * (ρ : ℝ)) :=
    carrier_subset_own_lineNbhd (ϖ i)
  have h3 : lineNbhd (ϖ i).x (ϖ i).direction (5 * (ρ : ℝ))
      ⊆ lineNbhd (ϖ i).x (ϖ i).direction (K * (δ : ℝ)) :=
    Metric.cthickening_mono hK _
  rw [hiW] at h1 h2 h3
  exact fun x hx ↦ h3 (h2 (h1 hx))

open scoped Classical in
/-- **`eq:defect-bridge-cover-map` (refined l.5512–5515), produced.** -/
theorem exists_coverMap_of_canonicalCentredCover {δ ρ : NNReal} (hρ : 0 < ρ)
    (h4 : 4 * (δ : ℝ) ≤ (ρ : ℝ)) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {ι : Type*} (s : Finset ι) (T : ι → Tube δ E)
    (hcen : ∀ i ∈ s, (T i).IsCentred) (hmid : ∀ i ∈ s, ‖(T i).midpoint‖ ≤ R₀)
    {K : ℝ} {A : ℕ} (hED : IsLineEssDistinctAt K A s T) (hK : 5 * (ρ : ℝ) ≤ K * (δ : ℝ)) :
    ∃ (G : Finset (Tube ρ E)) (ϖ : ι → Tube ρ E),
      (∀ i ∈ s, ϖ i ∈ G) ∧
      (∀ W ∈ G, ∃ i ∈ s, ϖ i = W) ∧
      (∀ i ∈ s, (T i).carrier ⊆ (ϖ i).carrier) ∧
      (∀ W ∈ G, (s.filter (fun i ↦ ϖ i = W)).card ≤ A) := by
  classical
  obtain ⟨G, ϖ, hmaps, hsurj, hcov, -, -, -, -, -⟩ :=
    Tube.exists_canonicalCentredCover hρ h4 hR₀ s T hcen hmid
  exact ⟨G, ϖ, hmaps, hsurj, fun i hi ↦ hcov i hi,
    fun W _ ↦ card_fibre_le_of_lineEDAt hED hK hcov W⟩

open scoped Classical in
/-- **The radius push: line-ED at `5δ` gives line-ED at `Kδ`, at a packing cost.** -/
theorem lineED_push_radius {δ : NNReal} (hδ : 0 < δ) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {ι : Type*} {s : Finset ι} {T : ι → Tube δ E}
    (hcen : ∀ i ∈ s, (T i).IsCentred) (hmid : ∀ i ∈ s, ‖(T i).midpoint‖ ≤ R₀)
    {A : ℕ} (hED : IsLineEssDistinctAt 5 A s T)
    {K : ℝ} (hK : 1 ≤ K) (o d : E) (hd : ‖d‖ = 1) :
    ((s.filter (fun i ↦ (T i).carrier ⊆
        Metric.cthickening (K * (δ : ℝ)) (Set.range fun t : ℝ ↦ o + t • d))).card : ℝ)
      ≤ 2 * Tube.linePackingConstant (Module.finrank ℝ E) R₀
            (3 / 2 + (K - 1) * (5 + 4 * R₀)) 8 * A := by
  classical
  have hδr : (0 : ℝ) < (δ : ℝ) := hδ
  set F : Finset ι := s.filter (fun i ↦ (T i).carrier ⊆
    Metric.cthickening (K * (δ : ℝ)) (Set.range fun t : ℝ ↦ o + t • d)) with hF
  obtain ⟨G₀, hG₀cen, hG₀mid, hG₀sep, hG₀cover⟩ :=
    Tube.exists_centred_net (E := E) δ R₀ (ε := (δ : ℝ) / 8) (by positivity)
  -- the assignment to a net point
  have hchoice : ∀ i, ∃ W : Tube δ E, i ∈ s →
      W ∈ G₀ ∧ ‖(T i).midpoint - W.midpoint‖ ≤ (δ : ℝ) / 4 ∧
        ‖(T i).direction - W.direction‖ ≤ (δ : ℝ) / 4 := by
    intro i
    by_cases hi : i ∈ s
    · obtain ⟨W, hW, h1, h2⟩ := hG₀cover (T i).midpoint (T i).direction (hcen i hi)
        (T i).norm_direction (hmid i hi)
      exact ⟨W, fun _ ↦ ⟨hW, by linarith [h1], by linarith [h2]⟩⟩
    · exact ⟨Tube.ofMidpointDirection δ 0 (T i).direction (T i).norm_direction,
        fun h ↦ (hi h).elim⟩
  choose Wm hWm using hchoice
  set N : Finset (Tube δ E) := F.image Wm with hN
  -- (1) each fibre of the assignment is bounded by `A`, by line-ED at radius `5δ`
  have hfib : ∀ W ∈ N, (F.filter (fun i ↦ Wm i = W)).card ≤ A := by
    intro W _
    refine le_trans (Finset.card_le_card ?_) (hED W.midpoint W.direction W.norm_direction)
    intro i hi
    rw [Finset.mem_filter] at hi ⊢
    obtain ⟨hiF, hiW⟩ := hi
    have his : i ∈ s := (Finset.mem_filter.mp hiF).1
    refine ⟨his, ?_⟩
    obtain ⟨-, hp, hdd⟩ := hWm i his
    have hsub := Kakeya.VeryNotSticky.carrier_subset_lineNbhd (T i)
      (c := (T i).midpoint) (p := (Wm i).midpoint) (d := (T i).direction)
      (dp := (Wm i).direction) (εp := (δ : ℝ) / 4) (εd := (δ : ℝ) / 4) (r := 5 * (δ : ℝ))
      (by simpa using (T i).midpoint_add_smul_mem_segment (t := 0) (by norm_num))
      (Or.inl rfl) hp hdd (by linarith)
    rw [hiW] at hsub
    exact hsub
  have hFcard : (F.card : ℝ) ≤ (A : ℝ) * (N.card : ℝ) := by
    have := Finset.card_le_mul_card_image_of_maps_to
      (f := Wm) (s := F) (t := N) (fun i hi ↦ Finset.mem_image_of_mem _ hi) A hfib
    exact_mod_cast this
  -- (2) the net points used lie in a slightly larger line neighbourhood
  set K' : ℝ := 3 / 2 + (K - 1) * (5 + 4 * R₀) with hK'
  have hK'1 : 1 ≤ K' := by rw [hK']; nlinarith
  have hNline : ∀ W ∈ N, ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      W.carrier ⊆ Metric.cthickening (K' * (δ : ℝ))
        (Set.range fun t : ℝ ↦ Tube.lineFoot o d + t • (σ • d)) := by
    intro W hW
    obtain ⟨i, hiF, rfl⟩ := Finset.mem_image.mp hW
    have his : i ∈ s := (Finset.mem_filter.mp hiF).1
    have hTi : (T i).carrier ⊆ Metric.cthickening (K * (δ : ℝ))
        (Set.range fun t : ℝ ↦ o + t • d) := (Finset.mem_filter.mp hiF).2
    obtain ⟨σ, hσ, hdir, hmidf⟩ :=
      Tube.params_close_of_carrier_subset_line (T i) (hcen i his) (hmid i his) hd hK hTi
    obtain ⟨-, hp, hdd⟩ := hWm i his
    have hσn : ‖σ • d‖ = 1 := by
      rcases hσ with rfl | rfl <;> simp [hd]
    refine ⟨σ, hσ, ?_⟩
    have hdir' : ‖(Wm i).direction - σ • d‖ ≤ 4 * ((K - 1) * (δ : ℝ)) + (δ : ℝ) / 4 := by
      calc ‖(Wm i).direction - σ • d‖
          ≤ ‖(Wm i).direction - (T i).direction‖ + ‖(T i).direction - σ • d‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ (δ : ℝ) / 4 + 4 * ((K - 1) * (δ : ℝ)) := by
            rw [norm_sub_rev]; linarith [hp, hdd, hdir]
        _ = 4 * ((K - 1) * (δ : ℝ)) + (δ : ℝ) / 4 := by ring
    have hmid' : ‖(Wm i).midpoint - Tube.lineFoot o d‖
        ≤ (K - 1) * (δ : ℝ) * (1 + 4 * R₀) + (δ : ℝ) / 4 := by
      calc ‖(Wm i).midpoint - Tube.lineFoot o d‖
          ≤ ‖(Wm i).midpoint - (T i).midpoint‖ + ‖(T i).midpoint - Tube.lineFoot o d‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ (δ : ℝ) / 4 + (K - 1) * (δ : ℝ) * (1 + 4 * R₀) := by
            rw [norm_sub_rev]; linarith [hp, hmidf]
        _ = (K - 1) * (δ : ℝ) * (1 + 4 * R₀) + (δ : ℝ) / 4 := by ring
    have hsub := Kakeya.VeryNotSticky.carrier_subset_lineNbhd (Wm i)
      (c := (Wm i).midpoint) (p := Tube.lineFoot o d) (d := (Wm i).direction)
      (dp := σ • d) (εp := (K - 1) * (δ : ℝ) * (1 + 4 * R₀) + (δ : ℝ) / 4)
      (εd := 4 * ((K - 1) * (δ : ℝ)) + (δ : ℝ) / 4) (r := K' * (δ : ℝ))
      (by simpa using (Wm i).midpoint_add_smul_mem_segment (t := 0) (by norm_num))
      (Or.inl rfl) hmid' hdir' (by rw [hK']; nlinarith)
    rw [Kakeya.VeryNotSticky.lineNbhd_eq_cthickening_range] at hsub
    exact hsub
  -- (3) the packing bound on the net points, split by the sign
  have hNsub : N ⊆ G₀ := by
    intro W hW
    obtain ⟨i, hiF, rfl⟩ := Finset.mem_image.mp hW
    exact (hWm i (Finset.mem_filter.mp hiF).1).1
  have hpack : ∀ σ : ℝ, ‖σ • d‖ = 1 →
      ((N.filter fun W : Tube δ E ↦ W.carrier ⊆ Metric.cthickening (K' * (δ : ℝ))
          (Set.range fun t : ℝ ↦ Tube.lineFoot o d + t • (σ • d))).card : ℝ)
        ≤ Tube.linePackingConstant (Module.finrank ℝ E) R₀ K' 8 := by
    intro σ hσn
    exact Tube.card_filter_line_le_of_centred_sep N hδ (fun W ↦ W)
      (fun W hW ↦ hG₀cen W (hNsub hW)) hR₀ (fun W hW ↦ hG₀mid W (hNsub hW))
      (m := 8) (by norm_num)
      (fun a ha b hb hab ↦ by
        have := hG₀sep a (hNsub ha) b (hNsub hb) hab
        rw [show (δ : ℝ) / 8 = (δ : ℝ) / 8 from rfl] at this
        exact this)
      hK'1 (Tube.lineFoot o d) (σ • d) hσn
  have hNcard : (N.card : ℝ)
      ≤ 2 * Tube.linePackingConstant (Module.finrank ℝ E) R₀ K' 8 := by
    have hone : ‖(1 : ℝ) • d‖ = 1 := by simp [hd]
    have hmone : ‖(-1 : ℝ) • d‖ = 1 := by simp [hd]
    have hcover : N ⊆ (N.filter fun W : Tube δ E ↦ W.carrier ⊆ Metric.cthickening (K' * (δ : ℝ))
          (Set.range fun t : ℝ ↦ Tube.lineFoot o d + t • ((1 : ℝ) • d)))
        ∪ (N.filter fun W : Tube δ E ↦ W.carrier ⊆ Metric.cthickening (K' * (δ : ℝ))
          (Set.range fun t : ℝ ↦ Tube.lineFoot o d + t • ((-1 : ℝ) • d))) := by
      intro W hW
      obtain ⟨σ, hσ, hsub⟩ := hNline W hW
      rcases hσ with rfl | rfl
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hW, hsub⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hW, hsub⟩))
    have h1 := hpack 1 hone
    have h2 := hpack (-1) hmone
    set Np : Finset (Tube δ E) := N.filter (fun W : Tube δ E ↦ W.carrier ⊆
      Metric.cthickening (K' * (δ : ℝ))
        (Set.range fun t : ℝ ↦ Tube.lineFoot o d + t • ((1 : ℝ) • d))) with hNp
    set Nm : Finset (Tube δ E) := N.filter (fun W : Tube δ E ↦ W.carrier ⊆
      Metric.cthickening (K' * (δ : ℝ))
        (Set.range fun t : ℝ ↦ Tube.lineFoot o d + t • ((-1 : ℝ) • d))) with hNm
    have hle : N.card ≤ Np.card + Nm.card :=
      le_trans (Finset.card_le_card hcover) (Finset.card_union_le _ _)
    have hc : (N.card : ℝ) ≤ (Np.card : ℝ) + (Nm.card : ℝ) := by exact_mod_cast hle
    linarith
  have hA0 : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg _
  calc (F.card : ℝ) ≤ (A : ℝ) * (N.card : ℝ) := hFcard
    _ ≤ (A : ℝ) * (2 * Tube.linePackingConstant (Module.finrank ℝ E) R₀ K' 8) := by
        exact mul_le_mul_of_nonneg_left hNcard hA0
    _ = 2 * Tube.linePackingConstant (Module.finrank ℝ E) R₀ K' 8 * A := by ring

/-- **The cover-map fibre constant, as a NAMED `max`.** -/
noncomputable def coverFibreConstant (n : ℕ) (R₀ K : ℝ) : ℝ :=
  max ((5000 : ℝ) ^ 6)
    (2 * Tube.linePackingConstant n R₀ (3 / 2 + (K - 1) * (5 + 4 * R₀)) 8)

theorem source_le_coverFibreConstant (n : ℕ) (R₀ K : ℝ) :
    (5000 : ℝ) ^ 6 ≤ coverFibreConstant n R₀ K := le_max_left _ _

theorem push_le_coverFibreConstant (n : ℕ) (R₀ K : ℝ) :
    2 * Tube.linePackingConstant n R₀ (3 / 2 + (K - 1) * (5 + 4 * R₀)) 8
      ≤ coverFibreConstant n R₀ K := le_max_right _ _

/-- The `max` is NOT decoration: at the smallest ratio the cover map admits (`4δ ≤ ρ` forces
`K ≥ 20`), in dimension `3` and at `R₀ = 1`, the tree's packing constant already EXCEEDS the
source's `F₀ = 5000⁶`. -/
theorem source_lt_tree_constant_at_twenty :
    (5000 : ℝ) ^ 6 < 2 * Tube.linePackingConstant 3 1 (3 / 2 + (20 - 1) * (5 + 4 * 1)) 8 := by
  unfold Tube.linePackingConstant
  norm_num

theorem coverFibreConstant_eq_at_twenty :
    coverFibreConstant 3 1 20
      = 2 * Tube.linePackingConstant 3 1 (3 / 2 + (20 - 1) * (5 + 4 * 1)) 8 := by
  unfold coverFibreConstant
  exact max_eq_right (le_of_lt (by norm_num [Tube.linePackingConstant]))

open scoped Classical in
/-- The push, restated as `IsLineEssDistinctAt` at the enlarged radius. -/
theorem isLineEssDistinctAt_push {δ : NNReal} (hδ : 0 < δ) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {ι : Type*} {s : Finset ι} {T : ι → Tube δ E}
    (hcen : ∀ i ∈ s, (T i).IsCentred) (hmid : ∀ i ∈ s, ‖(T i).midpoint‖ ≤ R₀)
    {A : ℕ} (hED : IsLineEssDistinctAt 5 A s T) {K : ℝ} (hK : 1 ≤ K) :
    IsLineEssDistinctAt K ⌈coverFibreConstant (Module.finrank ℝ E) R₀ K * A⌉₊ s T := by
  classical
  intro o d hd
  have h := lineED_push_radius hδ hR₀ hcen hmid hED hK o d hd
  have hA0 : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg _
  have hstep : 2 * Tube.linePackingConstant (Module.finrank ℝ E) R₀
        (3 / 2 + (K - 1) * (5 + 4 * R₀)) 8 * A
      ≤ coverFibreConstant (Module.finrank ℝ E) R₀ K * A :=
    mul_le_mul_of_nonneg_right (push_le_coverFibreConstant _ _ _) hA0
  have hfin : ((s.filter (fun i ↦ (T i).carrier ⊆
      Kakeya.VeryNotSticky.lineNbhd o d (K * (δ : ℝ)))).card : ℝ)
      ≤ coverFibreConstant (Module.finrank ℝ E) R₀ K * A := by
    rw [Kakeya.VeryNotSticky.lineNbhd_eq_cthickening_range]
    exact le_trans h hstep
  exact_mod_cast le_trans hfin (Nat.le_ceil _)

/-- **Control: the push route does NOT meet the bridge's `hAfib` as written.** -/
theorem push_constant_not_below_source :
    ¬ ((⌈coverFibreConstant 3 1 20 * ((1 : ℕ) : ℝ)⌉₊ : ℝ) ≤ (5000 : ℝ) ^ 6 * ((1 : ℕ) : ℝ)) := by
  intro h
  have h1 : (5000 : ℝ) ^ 6 < coverFibreConstant 3 1 20 := by
    rw [coverFibreConstant_eq_at_twenty]; exact source_lt_tree_constant_at_twenty
  have h2 : coverFibreConstant 3 1 20 * ((1 : ℕ) : ℝ)
      ≤ (⌈coverFibreConstant 3 1 20 * ((1 : ℕ) : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
  push_cast at h h2
  linarith

open scoped Classical in
/-- **The tie: the cover map fills the bridge's four `ϖ` binders.** -/
theorem coverMap_fills_bridge_binders {δ ρ : NNReal} (hρ : 0 < ρ)
    (h4 : 4 * (δ : ℝ) ≤ (ρ : ℝ)) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {ι : Type*} (s : Finset ι) (T : ι → Tube δ E)
    (hcen : ∀ i ∈ s, (T i).IsCentred) (hmid : ∀ i ∈ s, ‖(T i).midpoint‖ ≤ R₀)
    {K : ℝ} {A : ℕ} (hED : IsLineEssDistinctAt K A s T) (hK : 5 * (ρ : ℝ) ≤ K * (δ : ℝ)) :
    ∃ (G : Finset (Tube ρ E)) (ϖ : ι → Tube ρ E) (Afib : ℕ),
      (∀ i ∈ s, ϖ i ∈ G) ∧
      (∀ W ∈ G, ∃ i ∈ s, ϖ i = W) ∧
      (∀ W ∈ G, (s.filter (fun i ↦ ϖ i = W)).card ≤ Afib) ∧
      ((Afib : ℝ) ≤ 5000 ^ 6 * (A : ℝ)) ∧
      (∀ i ∈ s, (T i).carrier ⊆ (ϖ i).carrier) := by
  obtain ⟨G, ϖ, hmaps, hsurj, hcov, hfib⟩ :=
    exists_coverMap_of_canonicalCentredCover hρ h4 hR₀ s T hcen hmid hED hK
  refine ⟨G, ϖ, A, hmaps, hsurj, hfib, ?_, hcov⟩
  have hA0 : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg _
  nlinarith

end Kakeya.ML2Core

end
