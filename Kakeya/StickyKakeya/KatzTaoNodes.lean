/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.MultiScaleFac.ScaleGapTransport

/-!
# The Katz–Tao analogue of the leaf-anchored-to-node bridge

`Kakeya.StickyKakeya.isFrostmanAtEveryScale_nodes_of_ambient_fibre` turns a *leaf-anchored*
Frostman condition on an ambient family into the *node-anchored*
`Tube.UniformTubeSet.IsFrostmanAtEveryScale` carried by a hierarchy on a subfamily.  This file
is its Katz–Tao counterpart: it turns a *balanced partitioning cover of the ambient family by
`ρ`-tubes of bounded maximal density* — Wang–Zahl's reading of the Katz–Tao convex Wolff axioms
at the scale `ρ` — into a bound on `Kakeya.maxDensity` of the *nodes* of a hierarchy at a
comparable grid scale, which is the project's reading
(`Tube.UniformTubeSet.IsKatzTaoAtEveryScale`).

The comparison is the one piece of the Wang–Zahl ⇒ GWZ translation of Theorem 7.3(B) that has
no counterpart elsewhere in the tree.  Three inputs drive it:

* `Tube.rescale_le_of_le` — a `ρ`-tube containing a `δ`-tube lies in the `4ρ`-rescale of that
  `δ`-tube.  This is what lets a *parent* of the ambient cover be located from any single leaf
  under it, in both directions;
* `Kakeya.StickyKakeya.exists_gapFibre_cover_of_ratio` — the `4ρ`-fibre of a leaf is covered by
  `≲ (ρ / ρ_k) ^ {2n}` fibres at the grid scale `ρ_k`;
* `Tube.UniformTubeSet.boundedOverlap` — at most `Cu` nodes meet one `ρ_k`-tube through the
  family.

Composing them bounds the number of nodes lying over one parent, and the abstract density
transfer `densityIn_le_mul_maxDensity_of_multi_selection` (a multiplicity-carrying variant of
`Kakeya.MultiScaleFac.densityIn_le_mul_maxDensity_of_selection`) converts that into the density
comparison.
-/

@[expose] public section

open MeasureTheory Real Metric
open Tube

namespace Kakeya

namespace StickyKakeya

open MultiScaleFac

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*}

/-! ### The density transfer with a multiplicity -/

omit [Nontrivial E] in
/-- **The density comparison with a many-to-one selection.**  This is
`Kakeya.MultiScaleFac.densityIn_le_mul_maxDensity_of_selection` with the injectivity of the
selection relaxed to a bound `#t ≤ M · #t'` on its multiplicity; the multiplicity is paid for
in the constant.  The Katz–Tao bridge needs the relaxed form because many nodes of a hierarchy
may lie over one parent of the ambient cover. -/
theorem densityIn_le_mul_maxDensity_of_multi_selection {ι' : Type*} {t t' s' : Finset ι'}
    {W W' : ι' → ConvexSpaceBody E} {K' K'' : ConvexSpaceBody E} {vlo vhi q D M : ENNReal}
    (hvlo0 : vlo ≠ 0) (hvloTop : vlo ≠ ⊤)
    (hhi : ∀ j ∈ t, MeasureTheory.volume (W j).carrier ≤ vhi)
    (hlo : ∀ j' ∈ t', vlo ≤ MeasureTheory.volume (W' j').carrier)
    (hcard : (t.card : ENNReal) ≤ M * (t'.card : ENNReal)) (ht's' : t' ⊆ s')
    (hmem' : ∀ j' ∈ t', W' j' ≤ K'')
    (hKq : MeasureTheory.volume K''.carrier ≤ q * MeasureTheory.volume K'.carrier)
    (hD : M * (vhi * q) ≤ D * vlo) :
    Kakeya.densityIn t W K' ≤ D * Kakeya.maxDensity s' W' := by
  set Mx := Kakeya.maxDensity s' W' with hMx
  set V := MeasureTheory.volume K'.carrier with hV
  have hA : (∑ j ∈ t with W j ≤ K', MeasureTheory.volume (W j).carrier) ≤
      (t.card : ENNReal) * vhi :=
    calc
      ∑ j ∈ t with W j ≤ K', MeasureTheory.volume (W j).carrier
          ≤ ∑ j ∈ t with W j ≤ K', vhi :=
            Finset.sum_le_sum fun j hj => hhi j (Finset.mem_filter.mp hj).1
      _ ≤ (t.card : ENNReal) * vhi := by
            rw [Finset.sum_const, nsmul_eq_mul]
            exact mul_le_mul_left (Nat.cast_le.mpr (Finset.card_filter_le _ _)) vhi
  have hB : (t.card : ENNReal) * vlo ≤ M * (Mx * (q * V)) :=
    calc
      (t.card : ENNReal) * vlo ≤ (M * (t'.card : ENNReal)) * vlo := by gcongr
      _ = M * ((t'.card : ENNReal) * vlo) := by ring
      _ = M * (∑ _j' ∈ t', vlo) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ M * (∑ j' ∈ t', MeasureTheory.volume (W' j').carrier) := by
            gcongr with j' hj'
            exact hlo j' hj'
      _ ≤ M * (Kakeya.maxDensity t' W' * MeasureTheory.volume K''.carrier) := by
            gcongr
            exact Kakeya.sum_volume_le_maxDensity_mul_volume' hmem'
      _ ≤ M * (Mx * MeasureTheory.volume K''.carrier) := by
            gcongr
            exact Kakeya.maxDensity_mono W' ht's'
      _ ≤ M * (Mx * (q * V)) := by gcongr
  have hC : ((t.card : ENNReal) * vhi) * vlo ≤ ((D * Mx) * V) * vlo :=
    calc
      ((t.card : ENNReal) * vhi) * vlo = ((t.card : ENNReal) * vlo) * vhi := by ring
      _ ≤ (M * (Mx * (q * V))) * vhi := by gcongr
      _ = (M * (vhi * q)) * (Mx * V) := by ring
      _ ≤ (D * vlo) * (Mx * V) := by gcongr
      _ = ((D * Mx) * V) * vlo := by ring
  rw [Kakeya.densityIn_le_iff]
  exact hA.trans ((ENNReal.mul_le_mul_iff_left hvlo0 hvloTop).mp hC)

/-! ### Counting the nodes over one parent -/

/-- **The nodes over a common anchor.**  Let `F` be a set of nodes of a hierarchy `𝒰` on `t ⊆ s`
at the grid index `k`, each carrying a distinguished leaf `ℓ j` of its own class, and suppose all
those leaves lie in the `r`-rescale of one ambient leaf `ℓ₀`.  Then `#F` is at most the number of
grid-scale fibres needed to cover that rescale — `≲ (r / ρ_k) ^ {2n}` — times the bounded-overlap
constant `Cu`.

This is the counting half of the Katz–Tao bridge: applied with `r = 4ρ` and `F` the set of nodes
lying over one parent of the ambient cover, it bounds the multiplicity of the selection
`node ↦ parent`. -/
theorem card_le_mul_of_nodes_over_common_anchor
    {δ : NNReal} {s t : Finset ι} {T : ι → Tube δ E} {N : ℕ} {Cu : NNReal}
    (hts : t ⊆ s) (𝒰 : UniformTubeSet t T N Cu) {k : ℕ} (hk : k ≤ N)
    (hδσ : 2 * δ ≤ gridScale δ N k) (hσpos : 0 < gridScale δ N k)
    {r : NNReal} (hσr : gridScale δ N k ≤ r)
    (F : Finset ι) (ℓ : ι → ι) {ℓ₀ : ι}
    (hFnode : ∀ j ∈ F, j ∈ 𝒰.cover.indexSet k)
    (hℓt : ∀ j ∈ F, ℓ j ∈ t)
    (hℓj : ∀ j ∈ F, 𝒰.cover.assign k (ℓ j) = j)
    (hfib : ∀ j ∈ F, (T (ℓ j)).toConvexSpaceBody
      ≤ ((T ℓ₀).rescale r).toConvexSpaceBody) :
    (F.card : ℝ) ≤ 2 * (25 : ℝ) ^ (2 * Module.finrank ℝ E)
        * ((r : ℝ) / ((gridScale δ N k : NNReal) : ℝ)) ^ (2 * Module.finrank ℝ E) * (Cu : ℝ) := by
  classical
  obtain ⟨Acov, hAs, hAcard, hAcov⟩ :=
    exists_gapFibre_cover_of_ratio (s := s) (T := T) (δ := δ) (σ := δ)
      (ρ := gridScale δ N k) (ρ' := r) hσpos le_rfl hδσ hσr ℓ₀
  set G : ι → Finset ι := fun a => (𝒰.cover.indexSet k).filter (fun j => ∃ i ∈ t,
      (T i).toConvexSpaceBody ≤ (𝒰.cover.tube k j).toConvexSpaceBody ∧
      (T i).toConvexSpaceBody ≤ ((T a).rescale (gridScale δ N k)).toConvexSpaceBody) with hG
  have hsub : F ⊆ Acov.biUnion G := by
    intro j hj
    have hℓs : ℓ j ∈ s := hts (hℓt j hj)
    have hmemfib : ℓ j ∈ fibreIndex s T δ r ℓ₀ := by
      rw [fibreIndex_self]
      exact Finset.mem_filter.mpr ⟨hℓs, hfib j hj⟩
    obtain ⟨a, haA, hia⟩ := hAcov (ℓ j) hmemfib
    rw [fibreIndex_self] at hia
    refine Finset.mem_biUnion.mpr ⟨a, haA, ?_⟩
    refine Finset.mem_filter.mpr ⟨hFnode j hj, ℓ j, hℓt j hj, ?_, (Finset.mem_filter.mp hia).2⟩
    have hle := 𝒰.cover.le_tube_assign k hk (ℓ j) (hℓt j hj)
    rwa [hℓj j hj] at hle
  have hGcard : ∀ a ∈ Acov, ((G a).card : ℝ) ≤ (Cu : ℝ) := by
    intro a _
    have := 𝒰.boundedOverlap k hk ((T a).rescale (gridScale δ N k))
    have h' : ((G a).card : NNReal) ≤ Cu := by
      simpa [hG] using this
    exact_mod_cast h'
  have hstep : (F.card : ℝ) ≤ (Acov.card : ℝ) * (Cu : ℝ) := by
    have h1 : F.card ≤ ∑ a ∈ Acov, (G a).card :=
      le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
    have h2 : ((∑ a ∈ Acov, (G a).card : ℕ) : ℝ) ≤ ∑ _a ∈ Acov, (Cu : ℝ) := by
      push_cast
      exact Finset.sum_le_sum hGcard
    have h3 : (F.card : ℝ) ≤ ((∑ a ∈ Acov, (G a).card : ℕ) : ℝ) := by exact_mod_cast h1
    calc (F.card : ℝ) ≤ ((∑ a ∈ Acov, (G a).card : ℕ) : ℝ) := h3
      _ ≤ ∑ _a ∈ Acov, (Cu : ℝ) := h2
      _ = (Acov.card : ℝ) * (Cu : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
  refine hstep.trans ?_
  exact mul_le_mul_of_nonneg_right hAcard (NNReal.coe_nonneg Cu)

/-! ### The node-density comparison -/

/-- **The dimensional constant of the Katz–Tao node comparison.**  It collects the fibre-cover
count `2 · 100 ^ {2n}`, the cost `thickenVolConstN 5` of thickening a test body, and the ratio of
the two tube-volume constants. -/
noncomputable def ktNodeCmpConst : NNReal :=
  2 * (100 : NNReal) ^ (2 * Module.finrank ℝ E) * thickenVolConstN (E := E) 5
    * Tube.volume_le.C (Module.finrank ℝ E) / Tube.le_volume.c (Module.finrank ℝ E)

/-- **The Katz–Tao node-density comparison.**

Let `t ⊆ s` carry a uniform hierarchy `𝒰` along the grid of length `N`, and let the *ambient*
family `s` admit a partitioning cover by `ρ`-tubes `P` — every `T i`, `i ∈ s`, lies in the tube
`P (assign i)` of a finite parent set — whose own maximal density is at most `A`.  If `ρ` is
comparable to the grid scale `ρ_k`, `ρ_k ≤ ρ ≤ G ρ_k`, and `ρ_k` is at least `2δ`, then the
*nodes* of `𝒰` at the grid index `k` have maximal density at most
`ktNodeCmpConst · Cu · G ^ {3n} · A`.

This is the Katz–Tao analogue of
`Kakeya.StickyKakeya.isFrostmanIn_coverClass_of_ambient_fibre`, and the piece of the Wang–Zahl
encoding of the every-scale hypothesis (a `K`-balanced partitioning cover at *some* scale
`ρ ∈ [ρ_0, K ρ_0)` with `C_KT ≤ K`) that the project's encoding
(`Tube.UniformTubeSet.IsKatzTaoAtEveryScale`, read on the hierarchy's own nodes) needs.  The
balance bracket of the Wang–Zahl cover is not used: only the cover clause and the density bound
enter.

Three ingredients: a node is located from one of its own leaves, a parent is located from any
leaf under it (`Tube.rescale_le_of_le`, in both directions), and the nodes over one parent are
counted by `card_le_mul_of_nodes_over_common_anchor`. -/
theorem maxDensity_nodes_le_of_ambient_cover
    {δ : NNReal} {s t : Finset ι} {T : ι → Tube δ E} {N : ℕ} {Cu : NNReal}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hts : t ⊆ s) (htne : t.Nonempty)
    (𝒰 : UniformTubeSet t T N Cu)
    {k : ℕ} (hk : k ≤ N) (h2δ : 2 * δ ≤ gridScale δ N k)
    {ρ : NNReal} (hσρ : gridScale δ N k ≤ ρ)
    {G : NNReal} (hG : 1 ≤ G) (hGρ : ρ ≤ G * gridScale δ N k)
    {parent : Finset ι} {P : ι → Tube ρ E} {assign : ι → ι}
    (hassign : ∀ i ∈ s, assign i ∈ parent)
    (hleaf : ∀ i ∈ s, (T i).toConvexSpaceBody ≤ (P (assign i)).toConvexSpaceBody)
    {A : ENNReal}
    (hA : Kakeya.maxDensity parent (fun j => (P j).toConvexSpaceBody) ≤ A) :
    Kakeya.maxDensity (𝒰.cover.indexSet k) (fun j => (𝒰.cover.tube k j).toConvexSpaceBody)
      ≤ ((ktNodeCmpConst (E := E) * Cu * G ^ (3 * Module.finrank ℝ E) : NNReal) : ENNReal) * A := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn
  set σ : NNReal := gridScale δ N k with hσdef
  have hσpos : 0 < σ := gridScale_pos hδ N k
  have hσ1 : σ ≤ 1 := gridScale_le_one hδ1 N k
  have hρpos : 0 < ρ := lt_of_lt_of_le hσpos hσρ
  have hcpos : 0 < Tube.le_volume.c n := Tube.le_volume.c_pos n
  set W : ι → ConvexSpaceBody E := fun j => (𝒰.cover.tube k j).toConvexSpaceBody with hW
  set vhi : ENNReal := ((Tube.volume_le.C n * σ ^ (n - 1) : NNReal) : ENNReal) with hvhi
  set vlo : ENNReal := ((Tube.le_volume.c n * ρ ^ (n - 1) : NNReal) : ENNReal) with hvlo
  set q : ENNReal := ((thickenVolConstN (E := E) 5 * G ^ n : NNReal) : ENNReal) with hq
  set M : ENNReal := ((Cu * (2 * (100 : NNReal) ^ (2 * n)) * G ^ (2 * n) : NNReal) : ENNReal)
    with hM
  set D : ENNReal := ((ktNodeCmpConst (E := E) * Cu * G ^ (3 * n) : NNReal) : ENNReal) with hD
  -- the numeric core of the transfer
  have hDineq : M * (vhi * q) ≤ D * vlo := by
    have hNN : Cu * (2 * (100 : NNReal) ^ (2 * n)) * G ^ (2 * n)
          * ((Tube.volume_le.C n * σ ^ (n - 1)) * (thickenVolConstN (E := E) 5 * G ^ n))
        ≤ ktNodeCmpConst (E := E) * Cu * G ^ (3 * n)
          * (Tube.le_volume.c n * ρ ^ (n - 1)) := by
      have hcne : Tube.le_volume.c n ≠ 0 := hcpos.ne'
      have hktn : ktNodeCmpConst (E := E) * Tube.le_volume.c n
          = 2 * (100 : NNReal) ^ (2 * n) * thickenVolConstN (E := E) 5 * Tube.volume_le.C n := by
        rw [ktNodeCmpConst, ← hn]
        exact div_mul_cancel₀ _ hcne
      have hpowle : σ ^ (n - 1) ≤ ρ ^ (n - 1) := pow_le_pow_left₀ (by positivity) hσρ _
      calc Cu * (2 * (100 : NNReal) ^ (2 * n)) * G ^ (2 * n)
            * ((Tube.volume_le.C n * σ ^ (n - 1)) * (thickenVolConstN (E := E) 5 * G ^ n))
          = (2 * (100 : NNReal) ^ (2 * n) * thickenVolConstN (E := E) 5 * Tube.volume_le.C n)
              * Cu * (G ^ (2 * n) * G ^ n) * σ ^ (n - 1) := by ring
        _ ≤ (2 * (100 : NNReal) ^ (2 * n) * thickenVolConstN (E := E) 5 * Tube.volume_le.C n)
              * Cu * (G ^ (2 * n) * G ^ n) * ρ ^ (n - 1) := by gcongr
        _ = (ktNodeCmpConst (E := E) * Tube.le_volume.c n)
              * Cu * (G ^ (2 * n) * G ^ n) * ρ ^ (n - 1) := by rw [hktn]
        _ = ktNodeCmpConst (E := E) * Cu * G ^ (3 * n)
              * (Tube.le_volume.c n * ρ ^ (n - 1)) := by
            rw [show (3 * n) = (2 * n) + n by ring, pow_add]
            ring
    rw [hvhi, hvlo, hq, hM, hD, ← ENNReal.coe_mul, ← ENNReal.coe_mul, ← ENNReal.coe_mul]
    exact_mod_cast hNN
  have hvlo0 : vlo ≠ 0 := by
    rw [hvlo]
    exact ENNReal.coe_ne_zero.mpr (mul_ne_zero hcpos.ne' (pow_ne_zero _ hρpos.ne'))
  have hvloTop : vlo ≠ ⊤ := by rw [hvlo]; exact ENNReal.coe_ne_top
  -- the per-test-body estimate
  rw [Kakeya.maxDensity_le_iff]
  intro K'
  have key : ∀ t₀ : Finset ι, (∀ j ∈ t₀, j ∈ 𝒰.cover.indexSet k) →
      (∀ j ∈ t₀, W j ≤ K') → Kakeya.densityIn t₀ W K' ≤ D * A := by
    intro t₀ ht₀node ht₀K
    rcases Finset.eq_empty_or_nonempty t₀ with hemp | hne
    · simp [hemp]
    obtain ⟨j₀, hj₀⟩ := hne
    -- a distinguished leaf in the class of each node
    have hex : ∀ j : ι, ∃ i : ι, j ∈ t₀ → (i ∈ t ∧ 𝒰.cover.assign k i = j) := by
      intro j
      by_cases hj : j ∈ t₀
      · obtain ⟨i, hi⟩ := coverClass_nonempty_of_mem_parent 𝒰 hk htne (ht₀node j hj)
        exact ⟨i, fun _ => by simpa [coverClass] using hi⟩
      · exact ⟨j, fun h => absurd h hj⟩
    choose ℓ hℓ using hex
    have hℓt : ∀ j ∈ t₀, ℓ j ∈ t := fun j hj => (hℓ j hj).1
    have hℓs : ∀ j ∈ t₀, ℓ j ∈ s := fun j hj => hts (hℓt j hj)
    have hℓj : ∀ j ∈ t₀, 𝒰.cover.assign k (ℓ j) = j := fun j hj => (hℓ j hj).2
    have hleafnode : ∀ j ∈ t₀, (T (ℓ j)).toConvexSpaceBody ≤ W j := by
      intro j hj
      have hle := 𝒰.cover.le_tube_assign k hk (ℓ j) (hℓt j hj)
      rw [hℓj j hj] at hle
      exact hle
    have hleafK : ∀ j ∈ t₀, (T (ℓ j)).toConvexSpaceBody ≤ K' := fun j hj =>
      (hleafnode j hj).trans (ht₀K j hj)
    set f : ι → ι := fun j => assign (ℓ j) with hf
    have hleafP : ∀ j ∈ t₀, (T (ℓ j)).toConvexSpaceBody ≤ (P (f j)).toConvexSpaceBody :=
      fun j hj => hleaf (ℓ j) (hℓs j hj)
    have hPrescale : ∀ j ∈ t₀, (P (f j)).toConvexSpaceBody
        ≤ ((T (ℓ j)).rescale (4 * ρ)).toConvexSpaceBody :=
      fun j hj => Tube.rescale_le_of_le (T (ℓ j)) (P (f j)) (hleafP j hj)
    set t' : Finset ι := t₀.image f with ht'
    have hft' : ∀ j ∈ t₀, f j ∈ t' := fun j hj => Finset.mem_image_of_mem f hj
    have ht'parent : t' ⊆ parent := by
      intro j' hj'
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hj'
      exact hassign (ℓ j) (hℓs j hj)
    -- the container: `K'` thickened by `4ρ`
    set K'' : ConvexSpaceBody E := K'.cthickening ((4 * ρ : NNReal) : ℝ) with hK''
    have hmem' : ∀ j' ∈ t', (fun j => (P j).toConvexSpaceBody) j' ≤ K'' := by
      intro j' hj'
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hj'
      exact (hPrescale j hj).trans
        (tube_rescale_le_cthickening (T (ℓ j)) (le_refl ((4 * ρ : NNReal) : ℝ)) (hleafK j hj))
    -- the volume of that container
    have hKq : MeasureTheory.volume K''.carrier ≤ q * MeasureTheory.volume K'.carrier := by
      set m : ℕ := ⌈(4 * (G : ℝ))⌉₊ with hm
      have h4G : (4 : NNReal) * G ≤ (m : NNReal) := by
        have : (4 : ℝ) * (G : ℝ) ≤ (m : ℝ) := Nat.le_ceil _
        exact_mod_cast this
      have hρm : 4 * ρ ≤ (m : NNReal) * σ := by
        calc 4 * ρ ≤ 4 * (G * σ) := by gcongr
          _ = (4 * G) * σ := by ring
          _ ≤ (m : NNReal) * σ := by gcongr
      have hthick := volume_thickenBody_le_nsmul (𝒰.cover.tube k j₀)
        (show (𝒰.cover.tube k j₀).toConvexSpaceBody ≤ K' from ht₀K j₀ hj₀) hρm
      have hconst : thickenVolConstN (E := E) m ≤ thickenVolConstN (E := E) 5 * G ^ n := by
        have hmlt : ((m : NNReal)) ≤ 4 * G + 1 := by
          have : (m : ℝ) ≤ 4 * (G : ℝ) + 1 :=
            (Nat.ceil_lt_add_one (by positivity : (0:ℝ) ≤ 4 * (G : ℝ))).le
          exact_mod_cast this
        have hbase : 2 * ((m : NNReal) + 1) ≤ 12 * G := by
          have h4 : (4 : NNReal) ≤ 4 * G := le_mul_of_one_le_right (by positivity) hG
          calc 2 * ((m : NNReal) + 1) ≤ 2 * ((4 * G + 1) + 1) := by gcongr
            _ = 8 * G + 4 := by ring
            _ ≤ 8 * G + 4 * G := by gcongr
            _ = 12 * G := by ring
        rw [thickenVolConstN, thickenVolConstN, ← hn]
        rw [div_mul_eq_mul_div]
        gcongr
        calc (2 * ((m : NNReal) + 1)) ^ n ≤ (12 * G) ^ n := by gcongr
          _ = (2 * ((5 : ℕ) + 1)) ^ n * G ^ n := by push_cast; rw [mul_pow]; norm_num
      calc MeasureTheory.volume K''.carrier
          = MeasureTheory.volume (thickenBody K' (4 * ρ)).carrier := by
            rw [hK'']
            rfl
        _ ≤ (thickenVolConstN (E := E) m : ENNReal) * MeasureTheory.volume K'.carrier := hthick
        _ ≤ q * MeasureTheory.volume K'.carrier := by
            rw [hq]
            exact mul_le_mul_right' (by exact_mod_cast hconst) _
    -- the multiplicity of the selection `node ↦ parent`
    have hcard : (t₀.card : ENNReal) ≤ M * (t'.card : ENNReal) := by
      have hfib : ∀ j' ∈ t', ((t₀.filter (fun j => f j = j')).card : ℝ)
          ≤ 2 * (100 : ℝ) ^ (2 * n) * (G : ℝ) ^ (2 * n) * (Cu : ℝ) := by
        intro j' hj'
        set F : Finset ι := t₀.filter (fun j => f j = j') with hF
        rcases Finset.eq_empty_or_nonempty F with hFe | ⟨j₁, hj₁⟩
        · rw [hFe]
          simp only [Finset.card_empty, Nat.cast_zero]
          positivity
        have hj₁t₀ : j₁ ∈ t₀ := (Finset.mem_filter.mp hj₁).1
        have hj₁f : f j₁ = j' := (Finset.mem_filter.mp hj₁).2
        have hanchor : ∀ j ∈ F, (T (ℓ j)).toConvexSpaceBody
            ≤ ((T (ℓ j₁)).rescale (4 * ρ)).toConvexSpaceBody := by
          intro j hjF
          have hjt₀ : j ∈ t₀ := (Finset.mem_filter.mp hjF).1
          have hjf : f j = j' := (Finset.mem_filter.mp hjF).2
          have h1 : (T (ℓ j)).toConvexSpaceBody ≤ (P j').toConvexSpaceBody := by
            have := hleafP j hjt₀
            rwa [hjf] at this
          exact h1.trans (by
            have := hPrescale j₁ hj₁t₀
            rwa [hj₁f] at this)
        have hcount := card_le_mul_of_nodes_over_common_anchor (s := s) (t := t) (T := T)
          hts 𝒰 hk h2δ hσpos (r := 4 * ρ)
          (by
            calc σ ≤ ρ := hσρ
              _ ≤ 4 * ρ := by
                  calc ρ = 1 * ρ := by ring
                    _ ≤ 4 * ρ := by gcongr <;> norm_num)
          F ℓ (fun j hjF => ht₀node j (Finset.mem_filter.mp hjF).1)
          (fun j hjF => hℓt j (Finset.mem_filter.mp hjF).1)
          (fun j hjF => hℓj j (Finset.mem_filter.mp hjF).1) hanchor
        refine hcount.trans ?_
        have hratio : (((4 * ρ : NNReal) : ℝ) / ((σ : NNReal) : ℝ)) ≤ 4 * (G : ℝ) := by
          rw [div_le_iff₀ (by exact_mod_cast hσpos)]
          have : ((4 * ρ : NNReal) : ℝ) ≤ ((4 * (G * σ) : NNReal) : ℝ) := by
            have : (4 : NNReal) * ρ ≤ 4 * (G * σ) := by gcongr
            exact_mod_cast this
          calc ((4 * ρ : NNReal) : ℝ) ≤ ((4 * (G * σ) : NNReal) : ℝ) := this
            _ = 4 * (G : ℝ) * ((σ : NNReal) : ℝ) := by push_cast; ring
        have hpow : ((((4 * ρ : NNReal) : ℝ) / ((σ : NNReal) : ℝ))) ^ (2 * n)
            ≤ (4 * (G : ℝ)) ^ (2 * n) := by
          refine pow_le_pow_left₀ ?_ hratio _
          positivity
        calc 2 * (25 : ℝ) ^ (2 * n)
              * (((4 * ρ : NNReal) : ℝ) / ((σ : NNReal) : ℝ)) ^ (2 * n) * (Cu : ℝ)
            ≤ 2 * (25 : ℝ) ^ (2 * n) * (4 * (G : ℝ)) ^ (2 * n) * (Cu : ℝ) := by gcongr
          _ = 2 * (100 : ℝ) ^ (2 * n) * (G : ℝ) ^ (2 * n) * (Cu : ℝ) := by
              have h100 : (100 : ℝ) ^ (2 * n) = (25 : ℝ) ^ (2 * n) * (4 : ℝ) ^ (2 * n) := by
                rw [← mul_pow]
                norm_num
              rw [h100, mul_pow]
              ring
      have hsum : (t₀.card : ℝ) ≤ (t'.card : ℝ)
          * (2 * (100 : ℝ) ^ (2 * n) * (G : ℝ) ^ (2 * n) * (Cu : ℝ)) := by
        have hfw := Finset.card_eq_sum_card_fiberwise hft'
        have h2 : ((∑ j' ∈ t', (t₀.filter (fun j => f j = j')).card : ℕ) : ℝ)
            ≤ ∑ _j' ∈ t', (2 * (100 : ℝ) ^ (2 * n) * (G : ℝ) ^ (2 * n) * (Cu : ℝ)) := by
          push_cast
          exact Finset.sum_le_sum hfib
        calc (t₀.card : ℝ)
            = ((∑ j' ∈ t', (t₀.filter (fun j => f j = j')).card : ℕ) : ℝ) := by
              exact_mod_cast congrArg (fun m : ℕ => (m : ℝ)) hfw
          _ ≤ ∑ _j' ∈ t', (2 * (100 : ℝ) ^ (2 * n) * (G : ℝ) ^ (2 * n) * (Cu : ℝ)) := h2
          _ = (t'.card : ℝ) * (2 * (100 : ℝ) ^ (2 * n) * (G : ℝ) ^ (2 * n) * (Cu : ℝ)) := by
              rw [Finset.sum_const, nsmul_eq_mul]
      have hNN : (t₀.card : NNReal)
          ≤ (Cu * (2 * (100 : NNReal) ^ (2 * n)) * G ^ (2 * n)) * (t'.card : NNReal) := by
        have : (t₀.card : ℝ)
            ≤ ((Cu * (2 * (100 : NNReal) ^ (2 * n)) * G ^ (2 * n)) * (t'.card : NNReal) : NNReal) := by
          refine hsum.trans (le_of_eq ?_)
          push_cast
          ring
        exact_mod_cast this
      rw [hM]
      have := hNN
      calc (t₀.card : ENNReal) = ((t₀.card : NNReal) : ENNReal) := by norm_cast
        _ ≤ (((Cu * (2 * (100 : NNReal) ^ (2 * n)) * G ^ (2 * n)) * (t'.card : NNReal) : NNReal)
              : ENNReal) := by exact_mod_cast hNN
        _ = ((Cu * (2 * (100 : NNReal) ^ (2 * n)) * G ^ (2 * n) : NNReal) : ENNReal)
              * (t'.card : ENNReal) := by push_cast; ring
    have hhi : ∀ j ∈ t₀, MeasureTheory.volume (W j).carrier ≤ vhi := by
      intro j _
      have hv := Tube.volume_le hσ1 (𝒰.cover.tube k j)
      rw [hvhi]
      simpa [hW, hn, hσdef] using hv
    have hlo : ∀ j' ∈ t', vlo ≤ MeasureTheory.volume ((P j').toConvexSpaceBody).carrier := by
      intro j' _
      have hv := Tube.le_volume (P j')
      rw [hvlo]
      simpa [hn] using hv
    refine le_trans (densityIn_le_mul_maxDensity_of_multi_selection (t := t₀) (t' := t')
      (s' := parent) (W := W) (W' := fun j => (P j).toConvexSpaceBody) (K' := K') (K'' := K'')
      (vlo := vlo) (vhi := vhi) (q := q) (D := D) (M := M)
      hvlo0 hvloTop hhi hlo hcard ht'parent hmem' hKq hDineq) ?_
    exact mul_le_mul_left' hA D
  refine le_trans (le_of_eq (Kakeya.densityIn_eq_densityIn_filter _ W K')) ?_
  exact key _ (fun j hj => (Finset.mem_filter.mp hj).1) (fun j hj => (Finset.mem_filter.mp hj).2)

/-! ### The bottom grid scale -/

/-- **The Katz--Tao node comparison at the bottom of the grid.**  At a grid index whose scale is
at most `δ` — in practice `k = N`, where `ρ_N = δ` — the nodes are `δ`-tubes, each containing a
leaf of its own class, and the assignment `node ↦ that leaf` is *injective*.  So no covering
argument is needed and no thickening is paid for: the node density is at most
`Kakeya.MultiScaleFac.tubeVolRatio` times the *leaf* density of the ambient family.

This is the Katz--Tao counterpart of `Kakeya.MultiScaleFac.isFrostmanIn_coverClass_bottom`, and
covers exactly the index at which the grid separation `2δ ≤ ρ_k` required by
`maxDensity_nodes_le_of_ambient_cover` fails outright.  Unlike the Frostman bottom lemma the
bound is *not* purely dimensional: a family of `δ`-tubes can have arbitrarily large `Δ_max`, and
the nodes inherit it. -/
theorem maxDensity_nodes_bottom_le_of_ambient_leaf
    {δ : NNReal} {s t : Finset ι} {T : ι → Tube δ E} {N : ℕ} {Cu : NNReal}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hts : t ⊆ s) (htne : t.Nonempty)
    (𝒰 : UniformTubeSet t T N Cu)
    {k : ℕ} (hk : k ≤ N) (hσδ : gridScale δ N k ≤ δ)
    {A : ENNReal}
    (hA : Kakeya.maxDensity s (fun i => (T i).toConvexSpaceBody) ≤ A) :
    Kakeya.maxDensity (𝒰.cover.indexSet k) (fun j => (𝒰.cover.tube k j).toConvexSpaceBody)
      ≤ ((tubeVolRatio (E := E) : NNReal) : ENNReal) * A := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn
  set σ : NNReal := gridScale δ N k with hσdef
  have hσpos : 0 < σ := gridScale_pos hδ N k
  have hσ1 : σ ≤ 1 := gridScale_le_one hδ1 N k
  have hcpos : 0 < Tube.le_volume.c n := Tube.le_volume.c_pos n
  set W : ι → ConvexSpaceBody E := fun j => (𝒰.cover.tube k j).toConvexSpaceBody with hW
  set vhi : ENNReal := ((Tube.volume_le.C n * δ ^ (n - 1) : NNReal) : ENNReal) with hvhi
  set vlo : ENNReal := ((Tube.le_volume.c n * δ ^ (n - 1) : NNReal) : ENNReal) with hvlo
  set D : ENNReal := ((tubeVolRatio (E := E) : NNReal) : ENNReal) with hD
  have hvlo0 : vlo ≠ 0 := by
    rw [hvlo]
    exact ENNReal.coe_ne_zero.mpr (mul_ne_zero hcpos.ne' (pow_ne_zero _ hδ.ne'))
  have hvloTop : vlo ≠ ⊤ := by rw [hvlo]; exact ENNReal.coe_ne_top
  have hDineq : (1 : ENNReal) * (vhi * 1) ≤ D * vlo := by
    have hNN : Tube.volume_le.C n * δ ^ (n - 1)
        ≤ tubeVolRatio (E := E) * (Tube.le_volume.c n * δ ^ (n - 1)) := by
      have hkey : tubeVolRatio (E := E) * Tube.le_volume.c n = Tube.volume_le.C n := by
        rw [tubeVolRatio, ← hn]
        exact div_mul_cancel₀ _ hcpos.ne'
      have heq : tubeVolRatio (E := E) * (Tube.le_volume.c n * δ ^ (n - 1))
          = Tube.volume_le.C n * δ ^ (n - 1) := by
        rw [← mul_assoc, hkey]
      exact heq.ge
    rw [hvhi, hvlo, hD, one_mul, mul_one, ← ENNReal.coe_mul]
    exact_mod_cast hNN
  rw [Kakeya.maxDensity_le_iff]
  intro K'
  have key : ∀ t₀ : Finset ι, (∀ j ∈ t₀, j ∈ 𝒰.cover.indexSet k) →
      (∀ j ∈ t₀, W j ≤ K') → Kakeya.densityIn t₀ W K' ≤ D * A := by
    intro t₀ ht₀node ht₀K
    have hex : ∀ j : ι, ∃ i : ι, j ∈ t₀ → (i ∈ t ∧ 𝒰.cover.assign k i = j) := by
      intro j
      by_cases hj : j ∈ t₀
      · obtain ⟨i, hi⟩ := coverClass_nonempty_of_mem_parent 𝒰 hk htne (ht₀node j hj)
        exact ⟨i, fun _ => by simpa [coverClass] using hi⟩
      · exact ⟨j, fun h => absurd h hj⟩
    choose ℓ hℓ using hex
    have hℓt : ∀ j ∈ t₀, ℓ j ∈ t := fun j hj => (hℓ j hj).1
    have hℓs : ∀ j ∈ t₀, ℓ j ∈ s := fun j hj => hts (hℓt j hj)
    have hℓj : ∀ j ∈ t₀, 𝒰.cover.assign k (ℓ j) = j := fun j hj => (hℓ j hj).2
    have hleafnode : ∀ j ∈ t₀, (T (ℓ j)).toConvexSpaceBody ≤ W j := by
      intro j hj
      have hle := 𝒰.cover.le_tube_assign k hk (ℓ j) (hℓt j hj)
      rw [hℓj j hj] at hle
      exact hle
    have hleafK : ∀ j ∈ t₀, (T (ℓ j)).toConvexSpaceBody ≤ K' := fun j hj =>
      (hleafnode j hj).trans (ht₀K j hj)
    set t' : Finset ι := t₀.image ℓ with ht'
    have hinj : Set.InjOn ℓ t₀ := by
      intro a ha b hb hab
      rw [← hℓj a ha, ← hℓj b hb, hab]
    have hcard : (t₀.card : ENNReal) ≤ 1 * (t'.card : ENNReal) := by
      rw [one_mul, ht', Finset.card_image_of_injOn hinj]
    have ht'sub : t' ⊆ s := by
      intro j' hj'
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hj'
      exact hℓs j hj
    have hmem' : ∀ j' ∈ t', (fun i => (T i).toConvexSpaceBody) j' ≤ K' := by
      intro j' hj'
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hj'
      exact hleafK j hj
    have hhi : ∀ j ∈ t₀, MeasureTheory.volume (W j).carrier ≤ vhi := by
      intro j _
      have hv := Tube.volume_le hσ1 (𝒰.cover.tube k j)
      refine hv.trans ?_
      rw [hvhi]
      have hmono : Tube.volume_le.C (Module.finrank ℝ E)
            * (gridScale δ N k) ^ (Module.finrank ℝ E - 1)
          ≤ Tube.volume_le.C n * δ ^ (n - 1) := by
        rw [← hn]
        gcongr
      exact_mod_cast hmono
    have hlo : ∀ j' ∈ t', vlo ≤ MeasureTheory.volume ((T j').toConvexSpaceBody).carrier := by
      intro j' _
      have hv := Tube.le_volume (T j')
      rw [hvlo]
      simpa [hn] using hv
    refine le_trans (densityIn_le_mul_maxDensity_of_multi_selection (t := t₀) (t' := t')
      (s' := s) (W := W) (W' := fun i => (T i).toConvexSpaceBody) (K' := K') (K'' := K')
      (vlo := vlo) (vhi := vhi) (q := 1) (D := D) (M := 1)
      hvlo0 hvloTop hhi hlo hcard ht'sub hmem' (by rw [one_mul]) hDineq) ?_
    exact mul_le_mul_left' hA D
  refine le_trans (le_of_eq (Kakeya.densityIn_eq_densityIn_filter _ W K')) ?_
  exact key _ (fun j hj => (Finset.mem_filter.mp hj).1) (fun j hj => (Finset.mem_filter.mp hj).2)

/-! ### The every-scale node condition -/

/-- **The node-reading Katz--Tao condition from ambient covers at every grid scale.**

Suppose `t ⊆ s` carries a uniform hierarchy `𝒰` along the grid of length `N`, that the ambient
family `s` has leaf density at most `D`, and that at each grid index `k < N` the ambient family
admits *some* partitioning cover by `ρ`-tubes with `ρ_k ≤ ρ ≤ G ρ_k` whose own maximal density
is at most `A`.  Then the hierarchy satisfies
`Tube.UniformTubeSet.IsKatzTaoAtEveryScale` with the explicit error
`max (ktNodeCmpConst · Cu · G ^ {3n} · A) (tubeVolRatio · D)`.

This is the Katz--Tao counterpart of
`Kakeya.StickyKakeya.isFrostmanAtEveryScale_nodes_of_ambient_fibre`, and it is exactly the
translation between the two encodings of "Katz--Tao at every scale" that the Wang--Zahl
reduction of [GWZ, Theorem 7.3(B)] needs: the hypothesis is the source's (a cover at *some*
comparable scale, with `C_KT ≤ A` on the parents), the conclusion is the project's (a bound on
`Kakeya.maxDensity` of the hierarchy's own nodes).

The two grid regimes are handled by different lemmas.  For `k < N` the grid separation
`8δ ≤ ρ_k` holds and `maxDensity_nodes_le_of_ambient_cover` applies; at `k = N` that separation
fails outright, and `maxDensity_nodes_bottom_le_of_ambient_leaf` supplies the bound from the
*leaf* density instead.  The second branch is why the leaf-scale datum `D` is a hypothesis: the
node reading at the bottom of the grid is not implied by the cover data at coarser scales. -/
theorem isKatzTaoAtEveryScale_nodes_of_ambient_covers
    {δ : NNReal} {s t : Finset ι} {T : ι → Tube δ E} {N : ℕ} {Cu : NNReal}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hN : 0 < N) (hδN : δ ≤ (16 : NNReal) ^ (-(N : ℝ)))
    (hts : t ⊆ s) (htne : t.Nonempty) (𝒰 : UniformTubeSet t T N Cu)
    {G A D : NNReal} (hG : 1 ≤ G)
    (hcov : ∀ k < N, ∃ ρ : NNReal, gridScale δ N k ≤ ρ ∧ ρ ≤ G * gridScale δ N k ∧
      ∃ (parent : Finset ι) (P : ι → Tube ρ E) (assign : ι → ι),
        (∀ i ∈ s, assign i ∈ parent) ∧
        (∀ i ∈ s, (T i).toConvexSpaceBody ≤ (P (assign i)).toConvexSpaceBody) ∧
        Kakeya.maxDensity parent (fun j => (P j).toConvexSpaceBody) ≤ (A : ENNReal))
    (hD : Kakeya.maxDensity s (fun i => (T i).toConvexSpaceBody) ≤ (D : ENNReal)) :
    𝒰.IsKatzTaoAtEveryScale
      (max ((ktNodeCmpConst (E := E) * Cu * G ^ (3 * Module.finrank ℝ E) * A : NNReal) : ENNReal)
        ((tubeVolRatio (E := E) * D : NNReal) : ENNReal)) := by
  intro k hk
  rcases Nat.lt_or_ge k N with hkN | hkN
  · obtain ⟨ρ, hσρ, hGρ, parent, P, assign, hassign, hleaf, hA⟩ := hcov k hkN
    have h8 : 8 * δ ≤ gridScale δ N k := eight_delta_le_gridScale hδ hδ1 hkN hδN
    have h2 : 2 * δ ≤ gridScale δ N k :=
      le_trans (mul_le_mul_of_nonneg_right (by norm_num : (2 : NNReal) ≤ 8) hδ.le) h8
    refine le_trans (maxDensity_nodes_le_of_ambient_cover hδ hδ1 hts htne 𝒰 hk h2 hσρ hG hGρ
      hassign hleaf hA) (le_trans (le_of_eq ?_) (le_max_left _ _))
    push_cast
    ring
  · have hkeq : k = N := le_antisymm hk hkN
    subst hkeq
    have hσδ : gridScale δ k k ≤ δ := le_of_eq (gridScale_self δ hN)
    refine le_trans (maxDensity_nodes_bottom_le_of_ambient_leaf hδ hδ1 hts htne 𝒰 hk hσδ hD)
      (le_trans (le_of_eq ?_) (le_max_right _ _))
    push_cast
    ring

/-! ### The leaf-scale density -/

/-- **The dimensional constant of the leaf-scale Katz--Tao comparison.** -/
noncomputable def ktLeafCmpConst : NNReal :=
  thickenVolConstN (E := E) 5 * Tube.volume_le.C (Module.finrank ℝ E)
    / Tube.le_volume.c (Module.finrank ℝ E)

/-- **The Katz--Tao comparison at the leaf scale.**

Let `s` be a family of `δ`-tubes admitting a partitioning cover by `ρ`-tubes `P` with
`δ ≤ ρ ≤ G δ`, whose own maximal density is at most `A`, and suppose no more than `M` leaves are
assigned to any one parent.  Then the *leaves* have maximal density at most
`ktLeafCmpConst · M · G ^ n · A`.

This is the datum that `Kakeya.StickyKakeya.isKatzTaoAtEveryScale_nodes_of_ambient_covers` takes
as its separate hypothesis `hD`, and that `StickyKakeya.StickyKatzTaoEstimate` carries as
`ConvexSpaceBody.IsKatzTao s _ δ^{-η}`: the node reading at coarse scales says nothing about
leaf multiplicities, because a node may bunch essentially identical leaves.

The bound on the multiplicity `M` is left as a hypothesis and is *not* dimensional: it is the one
place where essential distinctness of the family has to be spent.  For a family of pairwise
essentially distinct `δ`-tubes one expects `M ≲_n (ρ/δ)^{2(n-1)} ≤ G^{2(n-1)}`; that packing
count inside a *tube* (as opposed to inside a ball, `Tube.card_le_of_EssDistinct`) is not
available in the tree. -/
theorem maxDensity_leaves_le_of_ambient_cover [DecidableEq ι]
    {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {ρ : NNReal} (hδρ : δ ≤ ρ)
    {G : NNReal} (hG : 1 ≤ G) (hGρ : ρ ≤ G * δ)
    {parent : Finset ι} {P : ι → Tube ρ E} {assign : ι → ι}
    (hassign : ∀ i ∈ s, assign i ∈ parent)
    (hleaf : ∀ i ∈ s, (T i).toConvexSpaceBody ≤ (P (assign i)).toConvexSpaceBody)
    {M : NNReal}
    (hmult : ∀ j' : ι, (((s.filter (fun i => assign i = j')).card : ℕ) : NNReal) ≤ M)
    {A : ENNReal}
    (hA : Kakeya.maxDensity parent (fun j => (P j).toConvexSpaceBody) ≤ A) :
    Kakeya.maxDensity s (fun i => (T i).toConvexSpaceBody)
      ≤ ((ktLeafCmpConst (E := E) * M * G ^ Module.finrank ℝ E : NNReal) : ENNReal) * A := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn
  have hρpos : 0 < ρ := lt_of_lt_of_le hδ hδρ
  have hcpos : 0 < Tube.le_volume.c n := Tube.le_volume.c_pos n
  set W : ι → ConvexSpaceBody E := fun i => (T i).toConvexSpaceBody with hW
  set vhi : ENNReal := ((Tube.volume_le.C n * δ ^ (n - 1) : NNReal) : ENNReal) with hvhi
  set vlo : ENNReal := ((Tube.le_volume.c n * ρ ^ (n - 1) : NNReal) : ENNReal) with hvlo
  set q : ENNReal := ((thickenVolConstN (E := E) 5 * G ^ n : NNReal) : ENNReal) with hq
  set Mx : ENNReal := ((M : NNReal) : ENNReal) with hMx
  set D : ENNReal := ((ktLeafCmpConst (E := E) * M * G ^ n : NNReal) : ENNReal) with hD
  have hDineq : Mx * (vhi * q) ≤ D * vlo := by
    have hktn : ktLeafCmpConst (E := E) * Tube.le_volume.c n
        = thickenVolConstN (E := E) 5 * Tube.volume_le.C n := by
      rw [ktLeafCmpConst, ← hn]
      exact div_mul_cancel₀ _ hcpos.ne'
    have hpowle : δ ^ (n - 1) ≤ ρ ^ (n - 1) := pow_le_pow_left₀ (by positivity) hδρ _
    have hNN : M * ((Tube.volume_le.C n * δ ^ (n - 1))
          * (thickenVolConstN (E := E) 5 * G ^ n))
        ≤ ktLeafCmpConst (E := E) * M * G ^ n * (Tube.le_volume.c n * ρ ^ (n - 1)) := by
      calc M * ((Tube.volume_le.C n * δ ^ (n - 1))
            * (thickenVolConstN (E := E) 5 * G ^ n))
          = (thickenVolConstN (E := E) 5 * Tube.volume_le.C n) * M * G ^ n * δ ^ (n - 1) := by
            ring
        _ ≤ (thickenVolConstN (E := E) 5 * Tube.volume_le.C n) * M * G ^ n * ρ ^ (n - 1) := by
            gcongr
        _ = (ktLeafCmpConst (E := E) * Tube.le_volume.c n) * M * G ^ n * ρ ^ (n - 1) := by
            rw [hktn]
        _ = ktLeafCmpConst (E := E) * M * G ^ n * (Tube.le_volume.c n * ρ ^ (n - 1)) := by ring
    rw [hvhi, hvlo, hq, hMx, hD, ← ENNReal.coe_mul, ← ENNReal.coe_mul, ← ENNReal.coe_mul]
    exact_mod_cast hNN
  have hvlo0 : vlo ≠ 0 := by
    rw [hvlo]
    exact ENNReal.coe_ne_zero.mpr (mul_ne_zero hcpos.ne' (pow_ne_zero _ hρpos.ne'))
  have hvloTop : vlo ≠ ⊤ := by rw [hvlo]; exact ENNReal.coe_ne_top
  rw [Kakeya.maxDensity_le_iff]
  intro K'
  have key : ∀ t₀ : Finset ι, t₀ ⊆ s → (∀ i ∈ t₀, W i ≤ K') →
      Kakeya.densityIn t₀ W K' ≤ D * A := by
    intro t₀ ht₀s ht₀K
    rcases Finset.eq_empty_or_nonempty t₀ with hemp | hne
    · simp [hemp]
    obtain ⟨i₀, hi₀⟩ := hne
    set t' : Finset ι := t₀.image assign with ht'
    have ht'parent : t' ⊆ parent := by
      intro j' hj'
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj'
      exact hassign i (ht₀s hi)
    have hPrescale : ∀ i ∈ t₀, (P (assign i)).toConvexSpaceBody
        ≤ ((T i).rescale (4 * ρ)).toConvexSpaceBody :=
      fun i hi => Tube.rescale_le_of_le (T i) (P (assign i)) (hleaf i (ht₀s hi))
    set K'' : ConvexSpaceBody E := K'.cthickening ((4 * ρ : NNReal) : ℝ) with hK''
    have hmem' : ∀ j' ∈ t', (fun j => (P j).toConvexSpaceBody) j' ≤ K'' := by
      intro j' hj'
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj'
      exact (hPrescale i hi).trans
        (tube_rescale_le_cthickening (T i) (le_refl ((4 * ρ : NNReal) : ℝ)) (ht₀K i hi))
    have hKq : MeasureTheory.volume K''.carrier ≤ q * MeasureTheory.volume K'.carrier := by
      set m : ℕ := ⌈(4 * (G : ℝ))⌉₊ with hm
      have h4G : (4 : NNReal) * G ≤ (m : NNReal) := by
        have : (4 : ℝ) * (G : ℝ) ≤ (m : ℝ) := Nat.le_ceil _
        exact_mod_cast this
      have hρm : 4 * ρ ≤ (m : NNReal) * δ := by
        calc 4 * ρ ≤ 4 * (G * δ) := by gcongr
          _ = (4 * G) * δ := by ring
          _ ≤ (m : NNReal) * δ := by gcongr
      have hthick := volume_thickenBody_le_nsmul (T i₀)
        (show (T i₀).toConvexSpaceBody ≤ K' from ht₀K i₀ hi₀) hρm
      have hconst : thickenVolConstN (E := E) m ≤ thickenVolConstN (E := E) 5 * G ^ n := by
        have hmlt : ((m : NNReal)) ≤ 4 * G + 1 := by
          have : (m : ℝ) ≤ 4 * (G : ℝ) + 1 :=
            (Nat.ceil_lt_add_one (by positivity : (0:ℝ) ≤ 4 * (G : ℝ))).le
          exact_mod_cast this
        have hbase : 2 * ((m : NNReal) + 1) ≤ 12 * G := by
          have h4 : (4 : NNReal) ≤ 4 * G := le_mul_of_one_le_right (by positivity) hG
          calc 2 * ((m : NNReal) + 1) ≤ 2 * ((4 * G + 1) + 1) := by gcongr
            _ = 8 * G + 4 := by ring
            _ ≤ 8 * G + 4 * G := by gcongr
            _ = 12 * G := by ring
        rw [thickenVolConstN, thickenVolConstN, ← hn]
        rw [div_mul_eq_mul_div]
        gcongr
        calc (2 * ((m : NNReal) + 1)) ^ n ≤ (12 * G) ^ n := by gcongr
          _ = (2 * ((5 : ℕ) + 1)) ^ n * G ^ n := by push_cast; rw [mul_pow]; norm_num
      calc MeasureTheory.volume K''.carrier
          = MeasureTheory.volume (thickenBody K' (4 * ρ)).carrier := by
            rw [hK'']
            rfl
        _ ≤ (thickenVolConstN (E := E) m : ENNReal) * MeasureTheory.volume K'.carrier := hthick
        _ ≤ q * MeasureTheory.volume K'.carrier := by
            rw [hq]
            exact mul_le_mul_right' (by exact_mod_cast hconst) _
    have hcard : (t₀.card : ENNReal) ≤ Mx * (t'.card : ENNReal) := by
      have hfib : ∀ j' ∈ t', ((t₀.filter (fun i => assign i = j')).card : NNReal) ≤ M := by
        intro j' _
        refine le_trans ?_ (hmult j')
        have : (t₀.filter (fun i => assign i = j')).card
            ≤ (s.filter (fun i => assign i = j')).card :=
          Finset.card_le_card (Finset.filter_subset_filter _ ht₀s)
        exact_mod_cast this
      have hfw : t₀.card = ∑ j' ∈ t', (t₀.filter (fun i => assign i = j')).card :=
        Finset.card_eq_sum_card_fiberwise (fun i hi => Finset.mem_image_of_mem assign hi)
      have hNN : (t₀.card : NNReal) ≤ M * (t'.card : NNReal) := by
        have h2 : ((∑ j' ∈ t', (t₀.filter (fun i => assign i = j')).card : ℕ) : NNReal)
            ≤ ∑ _j' ∈ t', M := by
          push_cast
          exact Finset.sum_le_sum hfib
        calc (t₀.card : NNReal)
            = ((∑ j' ∈ t', (t₀.filter (fun i => assign i = j')).card : ℕ) : NNReal) := by
              exact_mod_cast congrArg (fun m : ℕ => (m : NNReal)) hfw
          _ ≤ ∑ _j' ∈ t', M := h2
          _ = (t'.card : NNReal) * M := by rw [Finset.sum_const, nsmul_eq_mul]
          _ = M * (t'.card : NNReal) := by ring
      rw [hMx]
      calc (t₀.card : ENNReal) = ((t₀.card : NNReal) : ENNReal) := by norm_cast
        _ ≤ ((M * (t'.card : NNReal) : NNReal) : ENNReal) := by exact_mod_cast hNN
        _ = ((M : NNReal) : ENNReal) * (t'.card : ENNReal) := by push_cast; ring
    have hhi : ∀ i ∈ t₀, MeasureTheory.volume (W i).carrier ≤ vhi := by
      intro i _
      have hv := Tube.volume_le hδ1 (T i)
      rw [hvhi]
      simpa [hW, hn] using hv
    have hlo : ∀ j' ∈ t', vlo ≤ MeasureTheory.volume ((P j').toConvexSpaceBody).carrier := by
      intro j' _
      have hv := Tube.le_volume (P j')
      rw [hvlo]
      simpa [hn] using hv
    refine le_trans (densityIn_le_mul_maxDensity_of_multi_selection (t := t₀) (t' := t')
      (s' := parent) (W := W) (W' := fun j => (P j).toConvexSpaceBody) (K' := K') (K'' := K'')
      (vlo := vlo) (vhi := vhi) (q := q) (D := D) (M := Mx)
      hvlo0 hvloTop hhi hlo hcard ht'parent hmem' hKq hDineq) ?_
    exact mul_le_mul_left' hA D
  refine le_trans (le_of_eq (Kakeya.densityIn_eq_densityIn_filter _ W K')) ?_
  exact key _ (Finset.filter_subset _ _) (fun i hi => (Finset.mem_filter.mp hi).2)

end StickyKakeya

end Kakeya

end
