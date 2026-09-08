/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.Cases
public import Kakeya.DimensionThree.MainLemma1.Repair

/-!
# Scalar factorization: the one-scale selected wrapper and the independent two-scale product

This file carries Steps 1, 3 and 4 of the Main Lemma 1 repair blueprint: the zero-extension
view lemmas, the *one-scale selected certificate* `Kakeya.ml1Boot.IsOneScaleSelected` (B2),
and the *independent two-scale scalar factorization* `Kakeya.ml1Boot.IsTwoScaleFactors` (B3).

It replaces the synchronisation demands of the mega-structure
`Kakeya.ml1Boot.IsFactorTwoScales` by the two things GWZ actually provides.
-/

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology
open scoped NNReal ENNReal

namespace Kakeya

namespace ml1Boot

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ## Step 1: zero-extension views -/

section ZeroExtend

/-- The tube `T` shaded by `∅`. -/
def nullShaded {σ : NNReal} (T : Tube σ E) : ShadedTube σ E where
  toTube := T
  shade := ∅
  measurableSet_shade := MeasurableSet.empty
  shade_subset := Set.empty_subset _

@[simp] theorem nullShaded_toTube {σ : NNReal} (T : Tube σ E) :
    (nullShaded T).toTube = T := rfl

@[simp] theorem nullShaded_shade {σ : NNReal} (T : Tube σ E) :
    (nullShaded T).shade = (∅ : Set E) := rfl

/-- **Zero-extension of a shading off the active support** (blueprint §2.2).

`zeroExtend a T Z` keeps the shading `Z i` on the active index set `a` and replaces it by the
empty shading elsewhere, *without touching the underlying tube*.  This is the only operation
by which a shading defined on an active subfamily is transported to the fixed ambient
skeleton; by the lemmas below it preserves shade mass, shaded union, multiplicity and point
fibres, and it preserves nothing else. -/
noncomputable def zeroExtend {ι : Type*} [DecidableEq ι] {σ : NNReal} (a : Finset ι)
    (T : ι → Tube σ E) (Z : ι → ShadedTube σ E) : ι → ShadedTube σ E :=
  fun i => if i ∈ a then Z i else nullShaded (T i)

theorem zeroExtend_toTube_of_mem {ι : Type*} [DecidableEq ι] {σ : NNReal} {a : Finset ι}
    {T : ι → Tube σ E} {Z : ι → ShadedTube σ E} {i : ι} (hi : i ∈ a) :
    (zeroExtend a T Z i).toTube = (Z i).toTube := by
  unfold zeroExtend; simp [hi]

theorem zeroExtend_toTube_of_not_mem {ι : Type*} [DecidableEq ι] {σ : NNReal} {a : Finset ι}
    {T : ι → Tube σ E} {Z : ι → ShadedTube σ E} {i : ι} (hi : i ∉ a) :
    (zeroExtend a T Z i).toTube = T i := by
  unfold zeroExtend; simp [hi]

/-- **The zero-extension lives on the fixed ambient skeleton.**  If the active shading shades
the ambient tubes, the zero-extension shades *every* ambient tube. -/
theorem zeroExtend_toTube {ι : Type*} [DecidableEq ι] {σ : NNReal} {a : Finset ι}
    {T : ι → Tube σ E} {Z : ι → ShadedTube σ E} (hT : ∀ i ∈ a, (Z i).toTube = T i) (i : ι) :
    (zeroExtend a T Z i).toTube = T i := by
  by_cases hi : i ∈ a
  · rw [zeroExtend_toTube_of_mem hi]; exact hT i hi
  · exact zeroExtend_toTube_of_not_mem hi

theorem volume_carrier_zeroExtend {ι : Type*} [DecidableEq ι] {σ : NNReal} (a : Finset ι)
    (T : ι → Tube σ E) (Z : ι → ShadedTube σ E) (i : ι) :
    volume (zeroExtend a T Z i).carrier = volume (T i).carrier := by
  by_cases hi : i ∈ a
  · rw [show (zeroExtend a T Z i).carrier = ((zeroExtend a T Z i).toTube).carrier from rfl,
      zeroExtend_toTube_of_mem hi]
    exact _root_.Tube.volume_carrier_eq_volume_carrier (Z i).toTube (T i)
  · rw [zeroExtend]; simp [hi]

theorem zeroExtend_shade_of_mem {ι : Type*} [DecidableEq ι] {σ : NNReal} {a : Finset ι}
    {T : ι → Tube σ E} {Z : ι → ShadedTube σ E} {i : ι} (hi : i ∈ a) :
    (zeroExtend a T Z i).shade = (Z i).shade := by
  unfold zeroExtend; simp [hi]

theorem zeroExtend_shade_of_not_mem {ι : Type*} [DecidableEq ι] {σ : NNReal} {a : Finset ι}
    {T : ι → Tube σ E} {Z : ι → ShadedTube σ E} {i : ι} (hi : i ∉ a) :
    (zeroExtend a T Z i).shade = (∅ : Set E) := by
  unfold zeroExtend; simp [hi]

variable {ι : Type*} [DecidableEq ι] {σ : NNReal}

/-- **Zero-extension preserves shade mass.** -/
theorem sum_volume_shade_zeroExtend (s a : Finset ι) (T : ι → Tube σ E)
    (Z : ι → ShadedTube σ E) :
    ∑ i ∈ s, volume (zeroExtend a T Z i).shade = ∑ i ∈ s ∩ a, volume (Z i).shade := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not s (· ∈ a)]
  have h₁ : ∑ i ∈ s.filter (· ∈ a), volume (zeroExtend a T Z i).shade
      = ∑ i ∈ s ∩ a, volume (Z i).shade := by
    rw [Finset.filter_mem_eq_inter]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [zeroExtend_shade_of_mem (Finset.mem_inter.mp hi).2]
  have h₂ : ∑ i ∈ s.filter (¬ · ∈ a), volume (zeroExtend a T Z i).shade = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [zeroExtend_shade_of_not_mem (Finset.mem_filter.mp hi).2]
    simp
  rw [h₁, h₂, add_zero]

/-- **Zero-extension preserves the shaded union.** -/
theorem iUnionShade_zeroExtend (s a : Finset ι) (T : ι → Tube σ E)
    (Z : ι → ShadedTube σ E) :
    (⋃ i ∈ s, (zeroExtend a T Z i).shade) = ⋃ i ∈ s ∩ a, (Z i).shade := by
  classical
  ext x
  simp only [Set.mem_iUnion, exists_prop, Finset.mem_inter]
  constructor
  · rintro ⟨i, hi, hx⟩
    by_cases hia : i ∈ a
    · exact ⟨i, ⟨hi, hia⟩, by rwa [zeroExtend_shade_of_mem hia] at hx⟩
    · rw [zeroExtend_shade_of_not_mem hia] at hx; exact absurd hx (Set.notMem_empty x)
  · rintro ⟨i, ⟨hi, hia⟩, hx⟩
    exact ⟨i, hi, by rwa [zeroExtend_shade_of_mem hia]⟩

/-- **Zero-extension preserves multiplicity.** -/
theorem multiplicity_zeroExtend (s a : Finset ι) (T : ι → Tube σ E)
    (Z : ι → ShadedTube σ E) :
    ShadedBody.multiplicity s (fun i => (zeroExtend a T Z i).toShadedBody)
      = ShadedBody.multiplicity (s ∩ a) (fun i => (Z i).toShadedBody) := by
  classical
  rw [ShadedBody.multiplicity_eq_div, ShadedBody.multiplicity_eq_div]
  congr 1
  · exact sum_volume_shade_zeroExtend s a T Z
  · exact congrArg volume (iUnionShade_zeroExtend s a T Z)

/-- **Zero-extension preserves point fibres**: the set of indices of `s` whose shading
contains a given point is unchanged, once intersected with the active support. -/
theorem pointFibre_zeroExtend (s a : Finset ι) (T : ι → Tube σ E)
    (Z : ι → ShadedTube σ E) (x : E) :
    {i | i ∈ s ∧ x ∈ (zeroExtend a T Z i).shade}
      = {i | i ∈ s ∩ a ∧ x ∈ (Z i).shade} := by
  classical
  ext i
  simp only [Set.mem_setOf_eq, Finset.mem_inter]
  constructor
  · rintro ⟨hi, hx⟩
    by_cases hia : i ∈ a
    · exact ⟨⟨hi, hia⟩, by rwa [zeroExtend_shade_of_mem hia] at hx⟩
    · rw [zeroExtend_shade_of_not_mem hia] at hx; exact absurd hx (Set.notMem_empty x)
  · rintro ⟨⟨hi, hia⟩, hx⟩
    exact ⟨hi, by rwa [zeroExtend_shade_of_mem hia]⟩

/-- The special case of `Kakeya.ml1Boot.multiplicity_zeroExtend` at an active support already
contained in the ambient index set. -/
theorem multiplicity_zeroExtend_of_subset {s a : Finset ι} (h : a ⊆ s)
    (T : ι → Tube σ E) (Z : ι → ShadedTube σ E) :
    ShadedBody.multiplicity s (fun i => (zeroExtend a T Z i).toShadedBody)
      = ShadedBody.multiplicity a (fun i => (Z i).toShadedBody) := by
  rw [multiplicity_zeroExtend, Finset.inter_eq_right.mpr h]

theorem sum_volume_shade_zeroExtend_of_subset {s a : Finset ι} (h : a ⊆ s)
    (T : ι → Tube σ E) (Z : ι → ShadedTube σ E) :
    ∑ i ∈ s, volume (zeroExtend a T Z i).shade = ∑ i ∈ a, volume (Z i).shade := by
  rw [sum_volume_shade_zeroExtend, Finset.inter_eq_right.mpr h]

/-- **The selected child shading on the fixed ambient skeleton**: the child shading `Z'` on
its active support `act'`, zero-extended over the ambient tubes of the input family `V`. -/
noncomputable def selectedShade (act' : Finset ι) (V Z' : ι → ShadedTube σ E) :
    ι → ShadedTube σ E :=
  zeroExtend act' (fun i => (V i).toTube) Z'

theorem selectedShade_toTube {act' : Finset ι} {V Z' : ι → ShadedTube σ E}
    (hT : ∀ i ∈ act', (Z' i).toTube = (V i).toTube) (i : ι) :
    (selectedShade act' V Z' i).toTube = (V i).toTube :=
  zeroExtend_toTube hT i

end ZeroExtend

/-! ## The averaging step: one good child fibre

GWZ Lemma 5.11 does **not** assert that every surviving child fibre is full; the wrapper
selects **one** by mass averaging.  These are the two ingredients: a finite pigeonhole in
`ℝ≥0∞`, and the selection lemma itself. -/

section Selection

/-- A ratio comparison in `ℝ≥0∞` with finite nonzero denominators. -/
theorem div_le_div_of_mul_le_mul {x y u v : ENNReal} (hu0 : u ≠ 0) (hut : u ≠ ⊤)
    (hv0 : v ≠ 0) (hvt : v ≠ ⊤) (h : x * v ≤ y * u) : x / u ≤ y / v := by
  have hswap : y / v * u = y * u / v := by
    rw [div_eq_mul_inv, div_eq_mul_inv]; ring
  rw [ENNReal.div_le_iff hu0 hut, hswap, ENNReal.le_div_iff_mul_le
    (Or.inl hv0) (Or.inl hvt)]
  simpa [mul_comm, mul_left_comm, mul_assoc] using h

/-- **Finite mass pigeonhole.**  If a total mass `A` is spread over the cells of `t`, whose
weights `n` sum to at most `N`, then some cell carries at least the average density. -/
theorem exists_mul_natCast_le {κ : Type*} (t : Finset κ) (ht : t.Nonempty)
    (a : κ → ENNReal) (n : κ → ℕ) (A : ENNReal) (N : ℕ)
    (hafin : ∀ k ∈ t, a k ≠ ⊤) (hAtop : A ≠ ⊤)
    (hA : A ≤ ∑ k ∈ t, a k) (hn : ∑ k ∈ t, n k ≤ N) :
    ∃ k ∈ t, A * (n k : ENNReal) ≤ a k * (N : ENNReal) := by
  classical
  set a' : κ → NNReal := fun k => (a k).toNNReal with ha'
  set A' : NNReal := A.toNNReal with hA'
  have hcoe : ∀ k ∈ t, ((a' k : NNReal) : ENNReal) = a k := fun k hk =>
    ENNReal.coe_toNNReal (hafin k hk)
  have hAcoe : ((A' : NNReal) : ENNReal) = A := ENNReal.coe_toNNReal hAtop
  have hAle : A' ≤ ∑ k ∈ t, a' k := by
    rw [← ENNReal.coe_le_coe, hAcoe, ENNReal.coe_finset_sum]
    exact le_trans hA (le_of_eq (Finset.sum_congr rfl fun k hk => (hcoe k hk).symm))
  have hsum : ∑ k ∈ t, A' * (n k : NNReal) ≤ ∑ k ∈ t, a' k * (N : NNReal) := by
    calc ∑ k ∈ t, A' * (n k : NNReal) = A' * ∑ k ∈ t, (n k : NNReal) := by
          rw [Finset.mul_sum]
      _ ≤ A' * (N : NNReal) := by
          have : ∑ k ∈ t, (n k : NNReal) ≤ (N : NNReal) := by
            rw [← Nat.cast_sum]; exact_mod_cast hn
          exact mul_le_mul_left' this A'
      _ ≤ (∑ k ∈ t, a' k) * (N : NNReal) := by
          exact mul_le_mul_right' hAle _
      _ = ∑ k ∈ t, a' k * (N : NNReal) := by rw [Finset.sum_mul]
  obtain ⟨k, hk, hle⟩ := Finset.exists_le_of_sum_le ht hsum
  refine ⟨k, hk, ?_⟩
  have := (ENNReal.coe_le_coe.mpr hle)
  rw [ENNReal.coe_mul, ENNReal.coe_mul, hAcoe, hcoe k hk] at this
  simpa using this

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {σ : NNReal}

/-- The zero-extended fibre mass is the mass of the *active* fibre. -/
theorem sum_shade_fibre_zeroExtend {amb act : Finset ι} (hact : act ⊆ amb) (p : ι → κ)
    (T : ι → Tube σ E) (Z : ι → ShadedTube σ E) (k : κ) :
    ∑ i ∈ fibre amb p k, volume (zeroExtend act T Z i).shade
      = ∑ i ∈ fibre act p k, volume (Z i).shade := by
  classical
  rw [sum_volume_shade_zeroExtend]
  congr 1
  unfold fibre
  ext i
  simp only [Finset.mem_inter, Finset.mem_filter]
  exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hact h.1, h.2⟩, h.1⟩⟩

/-- **One good child fibre, by averaging** (blueprint §3 B2, selection certificate).

Given a fixed ambient carrier `amb` at scale `σ`, an active subfamily `act` all of whose
parents lie in `t`, and a shading of positive total mass, some parent `k₀ ∈ t` has a
**nonempty ambient fibre** whose fullness — computed against the *full* ambient fibre, with
the shading zero-extended over the inactive tubes — is at least the ambient average fullness.

This is the only place where a "good fibre" is produced, and it produces exactly one; the
source gives no statement about the remaining fibres. -/
theorem exists_selected_fibre [Nontrivial E] {τ : NNReal} (hτ0 : 0 < τ)
    {amb act : Finset ι} (hact : act ⊆ amb) {p : ι → κ} {t : Finset κ}
    (hmaps : ∀ i ∈ act, p i ∈ t) (T : ι → Tube τ E) (Z : ι → ShadedTube τ E)
    (hpos : 0 < ∑ i ∈ act, volume (Z i).shade) :
    ∃ k₀ ∈ t, (fibre amb p k₀).Nonempty ∧
      (ShadedBody.fullness amb (fun i => (zeroExtend act T Z i).toShadedBody) : ENNReal)
        ≤ (ShadedBody.fullness (fibre amb p k₀)
            (fun i => (zeroExtend act T Z i).toShadedBody) : ENNReal) := by
  classical
  set W : ι → ShadedTube τ E := zeroExtend act T Z with hW
  -- the common carrier volume of a `τ`-tube
  obtain ⟨i₁, hi₁⟩ : act.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h] at hpos; simp at hpos
  have hi₁amb : i₁ ∈ amb := hact hi₁
  set v : ENNReal := volume (Z i₁).carrier with hv
  have hvol : ∀ i : ι, volume (W i).carrier = v := by
    intro i
    rw [hW, volume_carrier_zeroExtend, hv]
    exact _root_.Tube.volume_carrier_eq_volume_carrier (T i) (Z i₁).toTube
  have hv_pos : 0 < v := by
    have hc : 0 < (_root_.Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) :=
      ENNReal.coe_pos.mpr (_root_.Tube.le_volume.c_pos (Module.finrank ℝ E))
    have hδp : 0 < (τ : ENNReal) ^ (Module.finrank ℝ E - 1) :=
      ENNReal.pow_pos (ENNReal.coe_pos.mpr hτ0) (Module.finrank ℝ E - 1)
    exact lt_of_lt_of_le (ENNReal.mul_pos hc.ne' hδp.ne')
      (by simpa [hv] using _root_.Tube.le_volume (Z i₁).toTube)
  have hv_top : v ≠ ⊤ := by
    rw [hv]; exact (Z i₁).isCompact.measure_ne_top
  -- the cells
  set tp : Finset κ := t.filter (fun k => 0 < (fibre amb p k).card) with htp
  set aa : κ → ENNReal := fun k => ∑ i ∈ fibre amb p k, volume (W i).shade with haa
  set M : ENNReal := ∑ i ∈ act, volume (Z i).shade with hM
  have hMtop : M ≠ ⊤ := by
    rw [hM]
    refine ENNReal.sum_ne_top.mpr fun i _ => ?_
    exact ne_top_of_le_ne_top (Z i).isCompact.measure_ne_top
      (measure_mono (Z i).shade_subset)
  have hafin : ∀ k ∈ tp, aa k ≠ ⊤ := by
    intro k _
    rw [haa]
    refine ENNReal.sum_ne_top.mpr fun i _ => ?_
    exact ne_top_of_le_ne_top (W i).isCompact.measure_ne_top
      (measure_mono (W i).shade_subset)
  -- (1) the cells carry the whole active mass
  have hfib : ∀ k : κ, aa k = ∑ i ∈ fibre act p k, volume (Z i).shade := fun k =>
    sum_shade_fibre_zeroExtend hact p T Z k
  have hsum_t : ∑ k ∈ t, aa k = M := by
    simp_rw [hfib]
    rw [hM]
    exact Finset.sum_fiberwise_of_maps_to hmaps (fun i => volume (Z i).shade)
  have hsum_tp : ∑ k ∈ tp, aa k = M := by
    rw [← hsum_t, htp]
    refine Finset.sum_filter_of_ne fun k _ hne => ?_
    by_contra hcon
    have hz : fibre amb p k = ∅ :=
      Finset.card_eq_zero.mp (Nat.eq_zero_of_not_pos hcon)
    exact hne (by simp [haa, hz])
  -- (2) the cells do not overcount the ambient carrier
  have hcard : ∑ k ∈ tp, (fibre amb p k).card ≤ amb.card := by
    set s₁ : Finset ι := amb.filter (fun i => p i ∈ tp) with hs₁
    have hmapsTo : Set.MapsTo p (s₁ : Set ι) (tp : Set κ) := by
      intro i hi
      exact_mod_cast (Finset.mem_filter.mp hi).2
    have hsplit : s₁.card = ∑ k ∈ tp, (fibre amb p k).card := by
      rw [Finset.card_eq_sum_card_fiberwise hmapsTo]
      refine Finset.sum_congr rfl fun k hk => ?_
      have : fibre s₁ p k = fibre amb p k := fibre_filter_mem amb p tp hk
      simpa [fibre, hs₁] using congrArg Finset.card this
    rw [← hsplit, hs₁]
    exact Finset.card_filter_le _ _
  -- (3) at least one cell is nonempty
  have hk₁ : p i₁ ∈ tp := by
    refine Finset.mem_filter.mpr ⟨hmaps i₁ hi₁, ?_⟩
    exact Finset.card_pos.mpr ⟨i₁, Finset.mem_filter.mpr ⟨hi₁amb, rfl⟩⟩
  -- (4) pigeonhole
  obtain ⟨k₀, hk₀, hpig⟩ := exists_mul_natCast_le tp ⟨_, hk₁⟩ aa
    (fun k => (fibre amb p k).card) M amb.card hafin hMtop (le_of_eq hsum_tp.symm) hcard
  have hk₀t : k₀ ∈ t := (Finset.mem_filter.mp hk₀).1
  have hk₀ne : (fibre amb p k₀).Nonempty :=
    Finset.card_pos.mp (Finset.mem_filter.mp hk₀).2
  refine ⟨k₀, hk₀t, hk₀ne, ?_⟩
  -- (5) the two fullnesses, as ratios with a common tube volume
  have hambmass : ∑ i ∈ amb, volume (W i).shade = M := by
    rw [hW, sum_volume_shade_zeroExtend_of_subset hact]
  have hambcar : ∑ i ∈ amb, volume (W i).carrier = (amb.card : ENNReal) * v := by
    rw [Finset.sum_congr rfl (fun i _ => hvol i), Finset.sum_const, nsmul_eq_mul]
  have hfibcar : ∑ i ∈ fibre amb p k₀, volume (W i).carrier
      = ((fibre amb p k₀).card : ENNReal) * v := by
    rw [Finset.sum_congr rfl (fun i _ => hvol i), Finset.sum_const, nsmul_eq_mul]
  have hn₀ : (1 : ENNReal) ≤ ((fibre amb p k₀).card : ENNReal) := by
    exact_mod_cast Nat.succ_le_of_lt (Finset.card_pos.mpr hk₀ne)
  have hN : (1 : ENNReal) ≤ (amb.card : ENNReal) := by
    exact_mod_cast Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨i₁, hi₁amb⟩)
  rw [ShadedBody.coe_fullness, ShadedBody.coe_fullness]
  show (∑ i ∈ amb, volume (W i).shade) / (∑ i ∈ amb, volume (W i).carrier)
      ≤ (∑ i ∈ fibre amb p k₀, volume (W i).shade)
        / (∑ i ∈ fibre amb p k₀, volume (W i).carrier)
  rw [hambmass, hambcar, hfibcar]
  refine div_le_div_of_mul_le_mul ?_ ?_ ?_ ?_ ?_
  · exact mul_ne_zero (by positivity) hv_pos.ne'
  · exact ENNReal.mul_ne_top (by simp) hv_top
  · exact mul_ne_zero (by positivity) hv_pos.ne'
  · exact ENNReal.mul_ne_top (by simp) hv_top
  · calc M * (((fibre amb p k₀).card : ENNReal) * v)
        = (M * ((fibre amb p k₀).card : ENNReal)) * v := by ring
      _ ≤ (aa k₀ * (amb.card : ENNReal)) * v := by gcongr
      _ = aa k₀ * ((amb.card : ENNReal) * v) := by ring

end Selection

/-! ## B2: the one-scale selected certificate -/

section OneScale

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {σ ρ : NNReal}

/-- The active part of an ambient fibre. -/
theorem fibre_inter {amb act : Finset ι} (hact : act ⊆ amb) (p : ι → κ) (k : κ) :
    fibre amb p k ∩ act = fibre act p k := by
  classical
  unfold fibre
  ext i
  simp only [Finset.mem_inter, Finset.mem_filter]
  exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hact h.1, h.2⟩, h.1⟩⟩

/-- Multiplicity does not see tubes that carry no shading. -/
theorem sum_shade_eq_of_shade_empty_off {amb act : Finset ι} (hact : act ⊆ amb)
    (V : ι → ShadedTube σ E) (hoff : ∀ i ∈ amb, i ∉ act → (V i).shade = ∅) :
    ∑ i ∈ amb, volume (V i).shade = ∑ i ∈ act, volume (V i).shade := by
  classical
  rw [← Finset.sum_subset hact]
  intro i hi hni
  rw [hoff i hi hni]; simp

theorem iUnionShade_eq_of_shade_empty_off {amb act : Finset ι} (hact : act ⊆ amb)
    (V : ι → ShadedTube σ E) (hoff : ∀ i ∈ amb, i ∉ act → (V i).shade = ∅) :
    (⋃ i ∈ amb, (V i).shade) = ⋃ i ∈ act, (V i).shade := by
  classical
  ext x
  simp only [Set.mem_iUnion, exists_prop]
  refine ⟨?_, fun ⟨i, hi, hx⟩ => ⟨i, hact hi, hx⟩⟩
  rintro ⟨i, hi, hx⟩
  by_cases hia : i ∈ act
  · exact ⟨i, hia, hx⟩
  · rw [hoff i hi hia] at hx; exact absurd hx (Set.notMem_empty x)

theorem multiplicity_eq_of_shade_empty_off {amb act : Finset ι} (hact : act ⊆ amb)
    (V : ι → ShadedTube σ E) (hoff : ∀ i ∈ amb, i ∉ act → (V i).shade = ∅) :
    ShadedBody.multiplicity amb (fun i => (V i).toShadedBody)
      = ShadedBody.multiplicity act (fun i => (V i).toShadedBody) := by
  rw [ShadedBody.multiplicity_eq_div, ShadedBody.multiplicity_eq_div]
  congr 1
  · exact sum_shade_eq_of_shade_empty_off hact V hoff
  · exact congrArg volume (iUnionShade_eq_of_shade_empty_off hact V hoff)

/-- **B2: the one-scale selected certificate** (blueprint §3 B2, §9 Step 3).

A faithful wrapper around GWZ Lemma 5.11, in two layers.

*The raw one-scale certificate* (`child_*`, `parent_*`, `scalar`) records what Lemma 5.11
gives: a child refinement with its **true shade-mass retention** `c`, the active parent
family `tAct` inside the fixed parent skeleton `tAmb` together with the induced parent
shading `Zρ`, the parent's **average** fullness `lamP`, the containment (26), and the scalar
inequality (25) for **every** active parent.

*The selection certificate* (`sel_*`) records the one thing averaging buys: **one** good
child fibre `k₀`, whose fullness `lamF` is measured against that fibre's *full ambient
skeleton* `fibre amb p k₀` with the shading zero-extended over the inactive tubes.

Deliberately absent, because the source does not provide them:

* "every surviving child fibre is good" — only `k₀` is;
* Definition 2.2 shaded uniformity of any output family;
* a permanent per-tube density bracket on the selected fibre;
* any compatibility of `k₀` with a selection made at another scale.

The active/ambient separation of blueprint §2.1 is in the binder: `amb` is the fixed carrier
that the analytic estimates and the parent maps read, `act` is the currently shaded support
that the *next* Lemma 5.11 reads, and `shade_off` says the input shading is already
zero-extended. -/
structure IsOneScaleSelected (c L : ENNReal)
    (amb act : Finset ι) (V : ι → ShadedTube σ E)
    (tAmb : Finset κ) (Vρ : κ → Tube ρ E) (p : ι → κ)
    (act' : Finset ι) (Z' : ι → ShadedTube σ E)
    (tAct : Finset κ) (Zρ : κ → ShadedTube ρ E)
    (k₀ : κ) (lamP lamF : NNReal) : Prop where
  /-- The active support sits inside the fixed ambient carrier. -/
  active_subset : act ⊆ amb
  /-- The input shading is zero-extended: it is empty off the active support. -/
  shade_off : ∀ i ∈ amb, i ∉ act → (V i).shade = ∅
  /-- (raw) The child refinement is a subfamily of the active support. -/
  child_subset : act' ⊆ act
  /-- (raw) The child shading shades the same tubes and is contained in the input shading. -/
  child_shade : ∀ i ∈ act', (Z' i).toTube = (V i).toTube ∧ (Z' i).shade ⊆ (V i).shade
  /-- (raw) The child refinement's **true shade-mass retention** (blueprint §2.3). -/
  child_retention : c * (∑ i ∈ act, volume (V i).shade) ≤ ∑ i ∈ act', volume (Z' i).shade
  /-- (raw) The active parent family sits inside the fixed parent skeleton. -/
  parent_subset : tAct ⊆ tAmb
  /-- (raw) Every retained child has its parent active. -/
  parent_mapsTo : ∀ i ∈ act', p i ∈ tAct
  /-- (raw) The induced parent shading shades the parent tubes. -/
  parent_tube : ∀ k ∈ tAct, (Zρ k).toTube = Vρ k
  /-- (raw) GWZ (26): the child shadings are nested in the parent ones. -/
  parent_contain : ∀ i ∈ act', (Z' i).shade ⊆ (Zρ (p i)).shade
  /-- (raw) The parent family's **average** fullness — not a per-tube bracket. -/
  parent_fullness : (lamP : ENNReal)
    ≤ (ShadedBody.fullness tAct (fun k => (Zρ k).toShadedBody) : ENNReal)
  /-- (raw) GWZ (25), for **every** active parent. -/
  scalar : ∀ k ∈ tAct, ShadedBody.multiplicity amb (fun i => (V i).toShadedBody)
    ≤ L * ShadedBody.multiplicity tAct (fun k' => (Zρ k').toShadedBody)
      * ShadedBody.multiplicity (fibre act' p k) (fun i => (Z' i).toShadedBody)
  /-- (selection) The selected parent is active. -/
  sel_mem : k₀ ∈ tAct
  /-- (selection) Its ambient fibre is nonempty. -/
  sel_nonempty : (fibre amb p k₀).Nonempty
  /-- (selection) The good fibre's fullness, computed against the **full ambient fibre** with
  the child shading zero-extended over the inactive tubes. -/
  sel_fullness : (lamF : ENNReal)
    ≤ (ShadedBody.fullness (fibre amb p k₀)
        (fun i => (selectedShade act' V Z' i).toShadedBody) : ENNReal)
  /-- (selection) That fullness is at least the retention factor times the input fullness. -/
  sel_fullness_lb : c * (ShadedBody.fullness amb (fun i => (V i).toShadedBody) : ENNReal)
    ≤ (lamF : ENNReal)

namespace IsOneScaleSelected

variable {c L : ENNReal} {amb act : Finset ι} {V : ι → ShadedTube σ E}
  {tAmb : Finset κ} {Vρ : κ → Tube ρ E} {p : ι → κ}
  {act' : Finset ι} {Z' : ι → ShadedTube σ E}
  {tAct : Finset κ} {Zρ : κ → ShadedTube ρ E} {k₀ : κ} {lamP lamF : NNReal}

variable (h : IsOneScaleSelected c L amb act V tAmb Vρ p act' Z' tAct Zρ k₀ lamP lamF)

include h

theorem child_subset_amb : act' ⊆ amb := h.child_subset.trans h.active_subset

/-- **The scalar inequality instantiated at the selected parent**, with the fine factor read
on the *full ambient fibre* of `k₀` and the zero-extended shading.  This is the form the
two-scale composition consumes; it is the raw `scalar` at `k₀` plus
`Kakeya.ml1Boot.multiplicity_zeroExtend`, i.e. zero-extension is free for multiplicity. -/
theorem sel_scalar :
    ShadedBody.multiplicity amb (fun i => (V i).toShadedBody)
      ≤ L * ShadedBody.multiplicity tAct (fun k => (Zρ k).toShadedBody)
        * ShadedBody.multiplicity (fibre amb p k₀)
            (fun i => (selectedShade act' V Z' i).toShadedBody) := by
  have hfib : fibre amb p k₀ ∩ act' = fibre act' p k₀ :=
    fibre_inter h.child_subset_amb p k₀
  rw [selectedShade, multiplicity_zeroExtend, hfib]
  exact h.scalar k₀ h.sel_mem

/-- **The parent-side shade-mass lower bound** implied by the parent average fullness: the
`activeParentCardRetained` slot of blueprint §3 B2, in the only form the source supports
(GWZ Lemma 5.11 carries no absolute parent-count clause; see the docstring of
`Kakeya.ml1Boot.IsFactorOneScale`). -/
theorem parent_shade_mass :
    (lamP : ENNReal) * (∑ k ∈ tAct, volume (Zρ k).carrier)
      ≤ ∑ k ∈ tAct, volume (Zρ k).shade := by
  have := h.parent_fullness
  rw [ShadedBody.coe_fullness] at this
  have hsum : ∑ k ∈ tAct, volume ((Zρ k).toShadedBody).shade
      = (ShadedBody.fullness tAct (fun k => (Zρ k).toShadedBody) : ENNReal)
        * ∑ k ∈ tAct, volume ((Zρ k).toShadedBody).carrier :=
    ShadedBody.sum_volumeReal_shade_eq_fullness_mul tAct (fun k => (Zρ k).toShadedBody)
  rw [hsum, ShadedBody.coe_fullness]
  exact mul_le_mul_right' this _

end IsOneScaleSelected

end OneScale

/-! ## The B2 producer: projecting GWZ Lemma 5.11, then averaging -/

section OneScaleProducer

variable {ι κ lc : Type*} [DecidableEq ι] [DecidableEq κ] [DecidableEq lc] {σ ρ δ : NNReal}

/-- **B2 is produced by GWZ Lemma 5.11 plus one averaging step** (blueprint §9 Step 3).

Only the *true* fields of `Kakeya.ml1Boot.IsFactorOneScale` are projected — no uniformity
clause, no per-tube density bracket on the output, no parent-count clause — and the good
child fibre is then chosen by `Kakeya.ml1Boot.exists_selected_fibre`.  The positive-shade-mass
hypothesis is blueprint B0: nothing positive is produced from a null shading. -/
theorem isOneScaleSelected_of_isFactorOneScale [Nontrivial E]
    (hδ0 : 0 < δ) (hσ0 : 0 < σ) (hρ0 : 0 < ρ) {ε' : ℝ}
    {amb act : Finset ι} (hact : act ⊆ amb) {V : ι → ShadedTube σ E}
    (hoff : ∀ i ∈ amb, i ∉ act → (V i).shade = ∅)
    {tAmb : Finset κ} {Vρ : κ → Tube ρ E} {p : ι → κ}
    {tq : Finset lc} {q : κ → lc} {act' : Finset ι} {tAct : Finset κ} {t'q : Finset lc}
    {Z' : ι → ShadedTube σ E} {Zρ : κ → ShadedTube ρ E} {lamσ lamρ N : NNReal}
    (h : IsFactorOneScale δ ε' act V tAmb Vρ p tq q act' tAct t'q Z' Zρ lamσ lamρ N)
    (hpos : 0 < ∑ i ∈ act', volume (Z' i).shade) :
    ∃ k₀ : κ, ∃ lamF : NNReal,
      IsOneScaleSelected ((δ : ENNReal) ^ (2 * ε'))
        ((factorOneScale.C act.card σ : ENNReal) * (δ : ENNReal) ^ (-2 * ε'))
        amb act V tAmb Vρ p act' Z' tAct Zρ k₀ lamρ lamF := by
  classical
  have hact' : act' ⊆ amb := h.fine_subset.trans hact
  -- the active support of the child family, and its parents
  obtain ⟨i₁, hi₁⟩ : act'.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne] at hpos; simp at hpos
  have htActne : tAct.Nonempty := ⟨p i₁, h.branch_mapsTo i₁ hi₁⟩
  -- the good fibre
  obtain ⟨k₀, hk₀, hk₀ne, hsel⟩ :=
    exists_selected_fibre (E := E) hσ0 hact' (p := p) (t := tAct)
      (fun i hi => h.branch_mapsTo i hi) (fun i => (V i).toTube) Z' hpos
  refine ⟨k₀, ShadedBody.fullness (fibre amb p k₀)
    (fun i => (selectedShade act' V Z' i).toShadedBody), ?_⟩
  -- the retention factor, in its `[0, ∞]` spelling
  have hc : ∀ cN : NNReal, (cN : ℝ) = (δ : ℝ) ^ (2 * ε') →
      (cN : ENNReal) = (δ : ENNReal) ^ (2 * ε') := fun cN hcN => coe_nnreal_rpow_eq hδ0 hcN
  refine
    { active_subset := hact
      shade_off := hoff
      child_subset := h.fine_subset
      child_shade := h.fine_shade
      child_retention := ?_
      parent_subset := h.coarse_subset
      parent_mapsTo := h.branch_mapsTo
      parent_tube := h.coarse_tube
      parent_contain := ?_
      parent_fullness := ?_
      scalar := ?_
      sel_mem := hk₀
      sel_nonempty := hk₀ne
      sel_fullness := le_rfl
      sel_fullness_lb := ?_ }
  · have := h.fine_refinement.2
    rwa [hc _ rfl] at this
  · intro i hi
    exact h.contain i hi (h.branch_mapsTo i hi)
  · refine le_fullness_of_dens_lower hρ0 htActne Zρ (fun k hk => ?_)
    have hcar : (Zρ k).carrier = (Vρ k).carrier :=
      congrArg (fun T : Tube ρ E => T.carrier) (h.coarse_tube k hk)
    rw [hcar]
    exact (h.coarse_dens k hk).1
  · intro k hk
    have hprod := h.product k hk
    rw [multiplicity_eq_of_shade_empty_off hact V hoff]
    calc ShadedBody.multiplicity act (fun i => (V i).toShadedBody)
        ≤ (factorOneScale.C act.card σ : ENNReal) * (δ : ENNReal) ^ (-2 * ε')
            * ShadedBody.multiplicity tAct (fun k' => (Zρ k').toShadedBody)
            * ShadedBody.multiplicity (fibre act' p k) (fun i => (Z' i).toShadedBody) := hprod
      _ = (factorOneScale.C act.card σ : ENNReal) * (δ : ENNReal) ^ (-2 * ε')
            * ShadedBody.multiplicity tAct (fun k' => (Zρ k').toShadedBody)
            * ShadedBody.multiplicity (fibre act' p k) (fun i => (Z' i).toShadedBody) := rfl
  · -- the ambient fullness comparison: same denominator, mass retained by `child_retention`
    refine le_trans ?_ hsel
    rw [ShadedBody.coe_fullness, ShadedBody.coe_fullness]
    have hnum : ∑ i ∈ amb, volume (selectedShade act' V Z' i).shade
        = ∑ i ∈ act', volume (Z' i).shade :=
      sum_volume_shade_zeroExtend_of_subset hact' _ Z'
    have hden : ∑ i ∈ amb, volume (selectedShade act' V Z' i).carrier
        = ∑ i ∈ amb, volume (V i).carrier := by
      refine Finset.sum_congr rfl fun i _ => ?_
      exact volume_carrier_zeroExtend _ _ _ i
    show (δ : ENNReal) ^ (2 * ε')
        * ((∑ i ∈ amb, volume (V i).shade) / (∑ i ∈ amb, volume (V i).carrier))
      ≤ (∑ i ∈ amb, volume (selectedShade act' V Z' i).shade)
        / (∑ i ∈ amb, volume (selectedShade act' V Z' i).carrier)
    rw [hnum, hden, ← mul_div_assoc]
    refine ENNReal.div_le_div_right ?_ _
    rw [sum_shade_eq_of_shade_empty_off hact V hoff]
    have := h.fine_refinement.2
    rwa [hc _ rfl] at this

end OneScaleProducer

/-! ## B3: the independent two-scale scalar factorization -/

section TwoScale

variable {ι κ lc : Type*} [DecidableEq ι] [DecidableEq κ] [DecidableEq lc]
  {δ τ θ : NNReal}

/-- **B3: the two-scale scalar factorization, with independently selected fibres**
(blueprint §3 B3, §9 Step 4).

One fixed carrier skeleton `𝕋_δ → 𝕋_τ → 𝕋_θ` (`amb`, `tτAmb`, `tθAmb` with the parent maps
`pτ`, `pθ`), one fine fibre `𝓕 = fibre amb pτ kF` and one middle fibre
`𝓜 = fibre tτAmb pθ lM`, **chosen independently**: GWZ equation (59) holds for each `T_τ` and
each `T_θ` separately, so there is no nested witness relating `kF` to `lM` and this structure
carries none.  The three shadings are zero-extended over their full ambient index sets and
come with their *actual* average-fullness lower bounds `lamF`, `lamM`, `lamC`.

The whole cost of the construction is the **single** factor `Lfact`, paid once in `product`;
the retention factors of the two refinements are already absorbed into it and are not charged
again against the fullnesses.

The three analytic multiplicity conclusions (fine, middle, coarse) are **not** here: they are
the consumers' business, and `product` is exactly the shape
`Kakeya.ml1Boot.multiplicity_le_of_middle` consumes. -/
structure IsTwoScaleFactors (Lfact Lcard : ENNReal)
    (amb : Finset ι) (V : ι → ShadedTube δ E)
    (tτAmb : Finset κ) (Vτ : κ → Tube τ E) (pτ : ι → κ)
    (tθAmb : Finset lc) (Vθ : lc → Tube θ E) (pθ : κ → lc)
    (kF : κ) (Yf : ι → ShadedTube δ E) (lamF : NNReal)
    (lM : lc) (Ym : κ → ShadedTube τ E) (lamM : NNReal)
    (tθAct : Finset lc) (Yc : lc → ShadedTube θ E) (lamC : NNReal) : Prop where
  /-- The fixed skeleton: every ambient `δ`-tube has its `τ`-parent in the fixed middle
  carrier. -/
  skeleton_fine : ∀ i ∈ amb, pτ i ∈ tτAmb
  /-- The fixed skeleton: every ambient `τ`-tube has its `θ`-parent in the fixed coarse
  carrier. -/
  skeleton_mid : ∀ k ∈ tτAmb, pθ k ∈ tθAmb
  /-- The selected fine parent lies in the fixed middle carrier. -/
  fine_mem : kF ∈ tτAmb
  /-- Its ambient fine fibre is nonempty. -/
  fine_nonempty : (fibre amb pτ kF).Nonempty
  /-- The fine shading shades the ambient fine tubes (it is zero-extended, not restricted). -/
  fine_tube : ∀ i ∈ fibre amb pτ kF, (Yf i).toTube = (V i).toTube
  /-- The fine fibre's actual average fullness. -/
  fine_fullness : (lamF : ENNReal)
    ≤ (ShadedBody.fullness (fibre amb pτ kF) (fun i => (Yf i).toShadedBody) : ENNReal)
  /-- The selected middle parent lies in the fixed coarse carrier.  It is chosen
  **independently** of `kF`. -/
  mid_mem : lM ∈ tθAmb
  /-- Its ambient middle fibre is nonempty. -/
  mid_nonempty : (fibre tτAmb pθ lM).Nonempty
  /-- The middle shading shades the ambient middle tubes. -/
  mid_tube : ∀ k ∈ fibre tτAmb pθ lM, (Ym k).toTube = Vτ k
  /-- The middle fibre's actual average fullness. -/
  mid_fullness : (lamM : ENNReal)
    ≤ (ShadedBody.fullness (fibre tτAmb pθ lM) (fun k => (Ym k).toShadedBody) : ENNReal)
  /-- The active coarse family sits inside the fixed coarse carrier. -/
  coarse_subset : tθAct ⊆ tθAmb
  /-- It is nonempty. -/
  coarse_nonempty : tθAct.Nonempty
  /-- The coarse shading shades the coarse tubes. -/
  coarse_tube : ∀ l ∈ tθAct, (Yc l).toTube = Vθ l
  /-- The coarse family's actual average fullness. -/
  coarse_fullness : (lamC : ENNReal)
    ≤ (ShadedBody.fullness tθAct (fun l => (Yc l).toShadedBody) : ENNReal)
  /-- The branch/cardinality comparison: the product of the three retained cardinalities is
  controlled by the ambient cardinality. -/
  branch_card : ((fibre amb pτ kF).card : ENNReal) * ((fibre tτAmb pθ lM).card : ENNReal)
      * (tθAct.card : ENNReal) ≤ Lcard * (amb.card : ENNReal)
  /-- **(F)** the scalar product inequality, with the single total factor loss. -/
  product : ShadedBody.multiplicity amb (fun i => (V i).toShadedBody)
    ≤ Lfact * ShadedBody.multiplicity (fibre amb pτ kF) (fun i => (Yf i).toShadedBody)
      * ShadedBody.multiplicity (fibre tτAmb pθ lM) (fun k => (Ym k).toShadedBody)
      * ShadedBody.multiplicity tθAct (fun l => (Yc l).toShadedBody)

namespace IsTwoScaleFactors

variable {Lfact Lcard : ENNReal}
  {amb : Finset ι} {V : ι → ShadedTube δ E}
  {tτAmb : Finset κ} {Vτ : κ → Tube τ E} {pτ : ι → κ}
  {tθAmb : Finset lc} {Vθ : lc → Tube θ E} {pθ : κ → lc}
  {kF : κ} {Yf : ι → ShadedTube δ E} {lamF : NNReal}
  {lM : lc} {Ym : κ → ShadedTube τ E} {lamM : NNReal}
  {tθAct : Finset lc} {Yc : lc → ShadedTube θ E} {lamC : NNReal}

variable (h : IsTwoScaleFactors Lfact Lcard amb V tτAmb Vτ pτ tθAmb Vθ pθ
  kF Yf lamF lM Ym lamM tθAct Yc lamC)

include h

/-- The coarse factor read on the **fixed coarse skeleton**, with the coarse shading
zero-extended over the inactive coarse tubes: zero-extension is free for multiplicity
(blueprint §2.2), so `(F)` holds verbatim in the ambient reading of blueprint §4.2. -/
theorem product_coarse_ambient :
    ShadedBody.multiplicity amb (fun i => (V i).toShadedBody)
      ≤ Lfact * ShadedBody.multiplicity (fibre amb pτ kF) (fun i => (Yf i).toShadedBody)
        * ShadedBody.multiplicity (fibre tτAmb pθ lM) (fun k => (Ym k).toShadedBody)
        * ShadedBody.multiplicity tθAmb
            (fun l => (zeroExtend tθAct Vθ Yc l).toShadedBody) := by
  rw [multiplicity_zeroExtend_of_subset h.coarse_subset Vθ Yc]
  exact h.product

/-- The zero-extended coarse shading shades every tube of the fixed coarse skeleton. -/
theorem coarse_ambient_tube (l : lc) : (zeroExtend tθAct Vθ Yc l).toTube = Vθ l :=
  zeroExtend_toTube h.coarse_tube l

end IsTwoScaleFactors

/-- **B3 from two independent applications of B2** (blueprint §9 Step 4).

The two `Kakeya.ml1Boot.IsOneScaleSelected` bundles share the fixed carrier skeleton but are
otherwise unrelated: `h₂` is applied to the *fixed middle skeleton* `tτAmb` with active
support `mid`, and its selected fibre `lM` has nothing to do with `h₁`'s selected fibre `kF`.

`hbridge` is the contract of blueprint B1 (`regularizeOnFixedTree`, in the concrete shape of
`Kakeya.ml1Boot.exists_internalDensityNormalization`): the density normalization of the active
parent family costs a single multiplicity factor `Lreg`.  Feeding `mid`, and not the
zero-extended ambient family, into the second Lemma 5.11 is invariant §2.1.

The total loss `Lfact = L₁ · Lreg · L₂` is paid exactly once; neither refinement's shade-mass
retention is charged a second time. -/
theorem isTwoScaleFactors_of_two {c₁ L₁ c₂ L₂ Lreg Lcard : ENNReal}
    {amb act act' : Finset ι} {V Z' : ι → ShadedTube δ E}
    {tτAmb tAct₁ mid mid' : Finset κ} {Vτ : κ → Tube τ E} {pτ : ι → κ}
    {Zτ Zτ' : κ → ShadedTube τ E}
    {tθAmb tAct₂ : Finset lc} {Vθ : lc → Tube θ E} {pθ : κ → lc}
    {Zθ : lc → ShadedTube θ E}
    {kF : κ} {lM : lc} {lamP₁ lamF lamP₂ lamM : NNReal}
    (hsk₁ : ∀ i ∈ amb, pτ i ∈ tτAmb) (hsk₂ : ∀ k ∈ tτAmb, pθ k ∈ tθAmb)
    (h₁ : IsOneScaleSelected c₁ L₁ amb act V tτAmb Vτ pτ act' Z' tAct₁ Zτ kF lamP₁ lamF)
    (hmid : mid ⊆ tAct₁)
    (hbridge : ShadedBody.multiplicity tAct₁ (fun k => (Zτ k).toShadedBody)
      ≤ Lreg * ShadedBody.multiplicity mid (fun k => (Zτ k).toShadedBody))
    (h₂ : IsOneScaleSelected c₂ L₂ tτAmb mid (zeroExtend mid Vτ Zτ) tθAmb Vθ pθ
      mid' Zτ' tAct₂ Zθ lM lamP₂ lamM)
    (hcard : ((fibre amb pτ kF).card : ENNReal) * ((fibre tτAmb pθ lM).card : ENNReal)
      * (tAct₂.card : ENNReal) ≤ Lcard * (amb.card : ENNReal)) :
    IsTwoScaleFactors (L₁ * Lreg * L₂) Lcard amb V tτAmb Vτ pτ tθAmb Vθ pθ
      kF (selectedShade act' V Z') lamF
      lM (selectedShade mid' (zeroExtend mid Vτ Zτ) Zτ') lamM
      tAct₂ Zθ lamP₂ := by
  classical
  have hmidAmb : mid ⊆ tτAmb := hmid.trans h₁.parent_subset
  have hWτ : ∀ k, (zeroExtend mid Vτ Zτ k).toTube = Vτ k :=
    zeroExtend_toTube (fun k hk => h₁.parent_tube k (hmid hk))
  refine
    { skeleton_fine := hsk₁
      skeleton_mid := hsk₂
      fine_mem := h₁.parent_subset h₁.sel_mem
      fine_nonempty := h₁.sel_nonempty
      fine_tube := fun i _ => selectedShade_toTube (fun i hi => (h₁.child_shade i hi).1) i
      fine_fullness := h₁.sel_fullness
      mid_mem := h₂.parent_subset h₂.sel_mem
      mid_nonempty := h₂.sel_nonempty
      mid_tube := fun k _ => ?_
      mid_fullness := h₂.sel_fullness
      coarse_subset := h₂.parent_subset
      coarse_nonempty := ⟨lM, h₂.sel_mem⟩
      coarse_tube := h₂.parent_tube
      coarse_fullness := h₂.parent_fullness
      branch_card := hcard
      product := ?_ }
  · rw [selectedShade_toTube (fun k hk => (h₂.child_shade k hk).1) k]
    exact hWτ k
  · have hbr : ShadedBody.multiplicity mid (fun k => (Zτ k).toShadedBody)
        = ShadedBody.multiplicity tτAmb
            (fun k => (zeroExtend mid Vτ Zτ k).toShadedBody) :=
      (multiplicity_zeroExtend_of_subset hmidAmb Vτ Zτ).symm
    calc ShadedBody.multiplicity amb (fun i => (V i).toShadedBody)
        ≤ L₁ * ShadedBody.multiplicity tAct₁ (fun k => (Zτ k).toShadedBody)
            * ShadedBody.multiplicity (fibre amb pτ kF)
                (fun i => (selectedShade act' V Z' i).toShadedBody) := h₁.sel_scalar
      _ ≤ L₁ * (Lreg * ShadedBody.multiplicity tτAmb
                (fun k => (zeroExtend mid Vτ Zτ k).toShadedBody))
            * ShadedBody.multiplicity (fibre amb pτ kF)
                (fun i => (selectedShade act' V Z' i).toShadedBody) := by
            rw [← hbr]; gcongr
      _ ≤ L₁ * (Lreg * (L₂ * ShadedBody.multiplicity tAct₂ (fun l => (Zθ l).toShadedBody)
                * ShadedBody.multiplicity (fibre tτAmb pθ lM)
                    (fun k => (selectedShade mid' (zeroExtend mid Vτ Zτ) Zτ' k).toShadedBody)))
            * ShadedBody.multiplicity (fibre amb pτ kF)
                (fun i => (selectedShade act' V Z' i).toShadedBody) := by
            gcongr
            exact h₂.sel_scalar
      _ = L₁ * Lreg * L₂
            * ShadedBody.multiplicity (fibre amb pτ kF)
                (fun i => (selectedShade act' V Z' i).toShadedBody)
            * ShadedBody.multiplicity (fibre tτAmb pθ lM)
                (fun k => (selectedShade mid' (zeroExtend mid Vτ Zτ) Zτ' k).toShadedBody)
            * ShadedBody.multiplicity tAct₂ (fun l => (Zθ l).toShadedBody) := by ring

end TwoScale

/-! ### Replacing the independently proved branch-cardinality comparison -/

section B3Recard

variable [Nontrivial E]

/-- Replace the free cardinality parameter of a B3 certificate by any proved comparison. -/
theorem IsTwoScaleFactors.recard
    {ι κ lc : Type*} [DecidableEq ι] [DecidableEq κ] [DecidableEq lc]
    {δ τ θ : NNReal} {Lfact Lcard Lcard' : ENNReal}
    {amb : Finset ι} {V : ι → ShadedTube δ E}
    {tτAmb : Finset κ} {Vτ : κ → Tube τ E} {pτ : ι → κ}
    {tθAmb : Finset lc} {Vθ : lc → Tube θ E} {pθ : κ → lc}
    {kF : κ} {Yf : ι → ShadedTube δ E} {lamF : NNReal}
    {lM : lc} {Ym : κ → ShadedTube τ E} {lamM : NNReal}
    {tθAct : Finset lc} {Yc : lc → ShadedTube θ E} {lamC : NNReal}
    (h : IsTwoScaleFactors Lfact Lcard amb V tτAmb Vτ pτ tθAmb Vθ pθ
      kF Yf lamF lM Ym lamM tθAct Yc lamC)
    (hcard : ((fibre amb pτ kF).card : ENNReal) *
        ((fibre tτAmb pθ lM).card : ENNReal) * (tθAct.card : ENNReal)
      ≤ Lcard' * (amb.card : ENNReal)) :
    IsTwoScaleFactors Lfact Lcard' amb V tτAmb Vτ pτ tθAmb Vθ pθ
      kF Yf lamF lM Ym lamM tθAct Yc lamC := by
  exact { h with branch_card := hcard }

end B3Recard

/-! ## (F) keeps the Case (ii) collapse usable -/

section Collapse

variable {ι κ lc : Type*} [DecidableEq ι] [DecidableEq κ] [DecidableEq lc]

/-- **The Case (ii) collapse, driven by (F)** (blueprint `lem:ml1bootCaseNonSticky`, now read
off `Kakeya.ml1Boot.IsTwoScaleFactors` instead of the mega-structure).

This is the check that the new interface keeps the four consumers of `Cases.lean` usable:
`Kakeya.ml1Boot.multiplicity_le_of_middle` is stated abstractly in `X, M₁, M₂, M₃, P₁, P₂, P₃`,
and (F) together with the branch/cardinality comparison supplies exactly its `htriple` and
`hunif`.  The three factor bounds `hfine`, `hmiddle`, `hcoarse` remain the consumers'
business — B3 carries none of them. -/
theorem multiplicity_le_collapse_of_isTwoScaleFactors
    {δ τ θ : NNReal} (hδ0 : 0 < δ) (hδτ : δ ≤ τ) (hτθ : τ ≤ θ) (hθ1 : θ ≤ 1)
    {γ ν a a' ε' ηvol : ℝ}
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hν0 : 0 < ν) (hνγ : ν ≤ γ)
    (ha : 0 ≤ a) (haa' : a ≤ a') (hgain : 8 * a' ≤ 10 * a) (hε' : 0 < ε')
    (hηvol : 0 ≤ ηvol) {c₃ : NNReal} (hc₃0 : 0 < c₃) (hc₃1 : c₃ ≤ 1)
    {Cf Cu : NNReal} (hCu : 1 ≤ Cu)
    {Lfact : ENNReal} {amb : Finset ι} {V : ι → ShadedTube δ E}
    {tτAmb : Finset κ} {Vτ : κ → Tube τ E} {pτ : ι → κ}
    {tθAmb : Finset lc} {Vθ : lc → Tube θ E} {pθ : κ → lc}
    {kF : κ} {Yf : ι → ShadedTube δ E} {lamF : NNReal}
    {lM : lc} {Ym : κ → ShadedTube τ E} {lamM : NNReal}
    {tθAct : Finset lc} {Yc : lc → ShadedTube θ E} {lamC : NNReal}
    (h : IsTwoScaleFactors Lfact ((Cu : ENNReal) ^ 4) amb V tτAmb Vτ pτ tθAmb Vθ pθ
      kF Yf lamF lM Ym lamM tθAct Yc lamC)
    (hLfact : Lfact ≤ (Cf : ENNReal) * (δ : ENNReal) ^ (-ε'))
    (hscard : 0 < amb.card)
    (hfine : ShadedBody.multiplicity (fibre amb pτ kF) (fun i => (Yf i).toShadedBody)
      ≤ (δ : ENNReal) ^ (-4 * a') * ((δ / τ : NNReal) : ENNReal) ^ (-2 * γ)
        * (((fibre amb pτ kF).card : ENNReal)
            * ((δ / τ : NNReal) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2))
    (hmiddle : ShadedBody.multiplicity (fibre tτAmb pθ lM) (fun k => (Ym k).toShadedBody)
      ≤ (δ : ENNReal) ^ (10 * a) * ((τ / θ : NNReal) : ENNReal) ^ (-2 * γ)
        * (((fibre tτAmb pθ lM).card : ENNReal)
            * ((τ / θ : NNReal) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2))
    (hcoarse : ShadedBody.multiplicity tθAct (fun l => (Yc l).toShadedBody)
      ≤ (δ : ENNReal) ^ (-4 * a') * (θ : ENNReal) ^ (-2 * γ)
        * ((tθAct.card : ENNReal) * (θ : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2))
    (hvol : (c₃ : ENNReal) * (δ : ENNReal) ^ ηvol
      ≤ (amb.card : ENNReal) * (δ : ENNReal) ^ (2 : ℕ))
    (habsorb : (Cf : ENNReal) * (Cu : ENNReal) ^ 4 * (c₃ : ENNReal) ^ (-ν / 2)
      * (δ : ENNReal) ^ (-ε') * (δ : ENNReal) ^ (10 * a - 8 * a')
      * (δ : ENNReal) ^ (-2 * ν - ηvol * ν / 2) ≤ 1) :
    ShadedBody.multiplicity amb (fun i => (V i).toShadedBody)
      ≤ (δ : ENNReal) ^ (-2 * (γ - ν))
        * ((amb.card : ENNReal) * (δ : ENNReal) ^ (2 : ℕ)) ^ (1 - (γ - ν) / 2) := by
  have hP₁ : (1 : ENNReal) ≤ ((fibre amb pτ kF).card : ENNReal) := by
    exact_mod_cast Nat.succ_le_iff.mpr (Finset.card_pos.mpr h.fine_nonempty)
  have hP₂ : (1 : ENNReal) ≤ ((fibre tτAmb pθ lM).card : ENNReal) := by
    exact_mod_cast Nat.succ_le_iff.mpr (Finset.card_pos.mpr h.mid_nonempty)
  have hP₃ : (1 : ENNReal) ≤ (tθAct.card : ENNReal) := by
    exact_mod_cast Nat.succ_le_iff.mpr (Finset.card_pos.mpr h.coarse_nonempty)
  have htriple : ShadedBody.multiplicity amb (fun i => (V i).toShadedBody)
      ≤ (Cf : ENNReal) * (δ : ENNReal) ^ (-ε')
        * ShadedBody.multiplicity (fibre amb pτ kF) (fun i => (Yf i).toShadedBody)
        * ShadedBody.multiplicity (fibre tτAmb pθ lM) (fun k => (Ym k).toShadedBody)
        * ShadedBody.multiplicity tθAct (fun l => (Yc l).toShadedBody) := by
    refine le_trans h.product ?_
    gcongr
  have habsorb' : (Cf : ENNReal) * (Cu : ENNReal) ^ 4 * (c₃ : ENNReal) ^ (-ν / 2)
      * (δ : ENNReal) ^ (-ε') * (δ : ENNReal) ^ (10 * a - 8 * a')
      * (δ : ENNReal) ^ (-2 * ν - ηvol * ν / 2) ≤ (δ : ENNReal) ^ (-(0 : ℝ)) := by
    simpa [neg_zero, ENNReal.rpow_zero] using habsorb
  have hres := multiplicity_le_of_middle hδ0 hδτ hτθ hθ1
    (ν := ν) (ℓ := 0) (η := ηvol) (a := a) (a' := a') (ε' := ε')
    hηvol ha haa' hgain hε' (by norm_num : 0 ≤ (0 : ℝ))
    hγ0 hγ1 hν0 hνγ hCu hscard hc₃0 hc₃1
    hP₁ hP₂ hP₃ htriple hfine hmiddle hcoarse h.branch_card hvol habsorb'
  simpa [neg_zero, ENNReal.rpow_zero, one_mul] using hres

end Collapse






/-! ## Satisfiability witnesses

Both structures are bundles of inequalities; a bundle that is *unsatisfiable* compiles green
and `#print axioms` cannot see it.  These are the witnesses, and they are **not** degenerate:
every shading below has positive volume, so every multiplicity, fullness and mass inequality
is tested at a nonzero value. -/

section Witnesses

/-- A tube shaded by the whole of its carrier. -/
def fullShade {σ : NNReal} (T : Tube σ E) : ShadedTube σ E where
  toTube := T
  shade := T.carrier
  measurableSet_shade := T.toConvexSpaceBody.isCompact.isClosed.measurableSet
  shade_subset := subset_rfl

@[simp] theorem fullShade_toTube {σ : NNReal} (T : Tube σ E) : (fullShade T).toTube = T := rfl

@[simp] theorem fullShade_shade {σ : NNReal} (T : Tube σ E) :
    (fullShade T).shade = T.carrier := rfl

/-- A fully shaded singleton family has fullness `1`. -/
theorem fullness_singleton_fullShade [Nontrivial E] {σ : NNReal} (hσ0 : 0 < σ)
    {ι : Type*} (i₀ : ι) (T : ι → Tube σ E) :
    (ShadedBody.fullness ({i₀} : Finset ι) (fun i => (fullShade (T i)).toShadedBody) : ENNReal)
      = 1 := by
  obtain ⟨hpos, htop⟩ := tube_volume_pos_ne_top hσ0 (T i₀)
  rw [ShadedBody.coe_fullness]
  show (∑ i ∈ ({i₀} : Finset ι), volume (fullShade (T i)).shade)
      / (∑ i ∈ ({i₀} : Finset ι), volume (fullShade (T i)).carrier) = 1
  rw [Finset.sum_singleton, Finset.sum_singleton]
  exact ENNReal.div_self hpos.ne' htop

/-- A fully shaded singleton family has multiplicity `1`. -/
theorem multiplicity_singleton_fullShade [Nontrivial E] {σ : NNReal} (hσ0 : 0 < σ)
    {ι : Type*} (i₀ : ι) (T : ι → Tube σ E) :
    ShadedBody.multiplicity ({i₀} : Finset ι) (fun i => (fullShade (T i)).toShadedBody)
      = 1 :=
  multiplicity_singleton i₀ _ (tube_volume_pos_ne_top hσ0 (T i₀)).1.ne'

theorem fibre_singleton_unit {ι : Type*} (i₀ : ι) :
    fibre ({i₀} : Finset ι) (fun _ : ι => (() : Unit)) () = ({i₀} : Finset ι) := by
  unfold fibre; simp

/-- **`Kakeya.ml1Boot.IsOneScaleSelected` is satisfiable, nondegenerately.**

The witness is a single `1/2`-tube shaded by its whole carrier, sitting inside a `1`-tube
shaded by *its* whole carrier — the tower of `Kakeya.ml1Boot.exists_emptyShadedTubeTower`,
re-shaded.  Every multiplicity and every fullness in the bundle equals `1`, so no clause is
satisfied vacuously by a null shading. -/
theorem nonempty_isOneScaleSelected :
    ∃ (V Z' : Unit → ShadedTube (1 / 2 : NNReal) (EuclideanSpace ℝ (Fin 3)))
      (Vρ : Unit → Tube 1 (EuclideanSpace ℝ (Fin 3)))
      (Zρ : Unit → ShadedTube 1 (EuclideanSpace ℝ (Fin 3))),
      IsOneScaleSelected 1 1 ({()} : Finset Unit) ({()} : Finset Unit) V
        ({()} : Finset Unit) Vρ (fun _ => ())
        ({()} : Finset Unit) Z' ({()} : Finset Unit) Zρ () 1 1 := by
  classical
  obtain ⟨W, P, -, -, hWvol, hWP⟩ :=
    exists_emptyShadedTubeTower (ρ := (1 / 2 : NNReal)) (by norm_num) (le_refl _)
  refine ⟨fun _ => fullShade W.toTube, fun _ => fullShade W.toTube, fun _ => P,
    fun _ => fullShade P, ?_⟩
  have hσ0 : (0 : NNReal) < 1 / 2 := by norm_num
  have hρ0 : (0 : NNReal) < 1 := by norm_num
  have hfib := fibre_singleton_unit (ι := Unit) ()
  refine
    { active_subset := Finset.Subset.refl _
      shade_off := by intro i _ hi; exact absurd (Finset.mem_singleton_self ()) hi
      child_subset := Finset.Subset.refl _
      child_shade := fun i _ => ⟨rfl, subset_rfl⟩
      child_retention := by simp
      parent_subset := Finset.Subset.refl _
      parent_mapsTo := fun _ _ => Finset.mem_singleton_self ()
      parent_tube := fun _ _ => rfl
      parent_contain := fun i _ => hWP
      parent_fullness := ?_
      scalar := ?_
      sel_mem := Finset.mem_singleton_self ()
      sel_nonempty := by rw [hfib]; exact ⟨(), Finset.mem_singleton_self ()⟩
      sel_fullness := ?_
      sel_fullness_lb := ?_ }
  · rw [fullness_singleton_fullShade hρ0 () (fun _ => P)]; norm_num
  · intro k _
    rw [hfib, multiplicity_singleton_fullShade hσ0 () (fun _ => W.toTube),
      multiplicity_singleton_fullShade hρ0 () (fun _ => P)]
    norm_num
  · rw [hfib]
    have hsel : ∀ i : Unit, selectedShade ({()} : Finset Unit)
        (fun _ => fullShade W.toTube) (fun _ => fullShade W.toTube) i
          = fullShade W.toTube := by
      intro i
      rw [selectedShade, zeroExtend]
      simp
    rw [show (fun i : Unit => (selectedShade ({()} : Finset Unit)
        (fun _ => fullShade W.toTube) (fun _ => fullShade W.toTube) i).toShadedBody)
        = (fun i : Unit => (fullShade ((fun _ : Unit => W.toTube) i)).toShadedBody) from
      funext fun i => by rw [hsel i]]
    rw [fullness_singleton_fullShade hσ0 () (fun _ => W.toTube)]
    norm_num
  · rw [fullness_singleton_fullShade hσ0 () (fun _ => W.toTube)]
    norm_num

/-- **`Kakeya.ml1Boot.IsTwoScaleFactors` is satisfiable, nondegenerately.**

Three fully shaded singleton families, one at each scale.  Nothing in the structure relates
the three geometrically — that is the point of B3: the fine and middle fibres are selected
independently, and no nesting witness is demanded.  Every multiplicity, fullness and
cardinality in the bundle is `1`. -/
theorem nonempty_isTwoScaleFactors [Nontrivial E] {δ τ θ : NNReal}
    (hδ0 : 0 < δ) (hτ0 : 0 < τ) (hθ0 : 0 < θ) :
    ∃ (V : Unit → ShadedTube δ E) (Vτ : Unit → Tube τ E) (Vθ : Unit → Tube θ E)
      (Ym : Unit → ShadedTube τ E) (Yc : Unit → ShadedTube θ E),
      IsTwoScaleFactors 1 1 ({()} : Finset Unit) V
        ({()} : Finset Unit) Vτ (fun _ => ())
        ({()} : Finset Unit) Vθ (fun _ => ())
        () V 1 () Ym 1 ({()} : Finset Unit) Yc 1 := by
  classical
  obtain ⟨Tδ⟩ := nonempty_tube (E := E) δ
  obtain ⟨Tτ⟩ := nonempty_tube (E := E) τ
  obtain ⟨Tθ⟩ := nonempty_tube (E := E) θ
  refine ⟨fun _ => fullShade Tδ, fun _ => Tτ, fun _ => Tθ,
    fun _ => fullShade Tτ, fun _ => fullShade Tθ, ?_⟩
  have hfibδ := fibre_singleton_unit (ι := Unit) ()
  refine
    { skeleton_fine := fun _ _ => Finset.mem_singleton_self ()
      skeleton_mid := fun _ _ => Finset.mem_singleton_self ()
      fine_mem := Finset.mem_singleton_self ()
      fine_nonempty := by rw [hfibδ]; exact ⟨(), Finset.mem_singleton_self ()⟩
      fine_tube := fun _ _ => rfl
      fine_fullness := ?_
      mid_mem := Finset.mem_singleton_self ()
      mid_nonempty := by rw [hfibδ]; exact ⟨(), Finset.mem_singleton_self ()⟩
      mid_tube := fun _ _ => rfl
      mid_fullness := ?_
      coarse_subset := Finset.Subset.refl _
      coarse_nonempty := ⟨(), Finset.mem_singleton_self ()⟩
      coarse_tube := fun _ _ => rfl
      coarse_fullness := ?_
      branch_card := ?_
      product := ?_ }
  · rw [hfibδ, fullness_singleton_fullShade hδ0 () (fun _ => Tδ)]; norm_num
  · rw [hfibδ, fullness_singleton_fullShade hτ0 () (fun _ => Tτ)]; norm_num
  · rw [fullness_singleton_fullShade hθ0 () (fun _ => Tθ)]; norm_num
  · rw [hfibδ]; simp
  · rw [hfibδ, multiplicity_singleton_fullShade hδ0 () (fun _ => Tδ),
      multiplicity_singleton_fullShade hτ0 () (fun _ => Tτ),
      multiplicity_singleton_fullShade hθ0 () (fun _ => Tθ)]
    norm_num

end Witnesses

/-! ### The fine and middle selections really are independent

The one clause the retired mega-structure carried and the source does not is a nesting
witness tying the fine parent to the selected middle fibre.  The witness below has
`pθ kF ≠ lM`, so `Kakeya.ml1Boot.IsTwoScaleFactors` provably does **not** imply one. -/

section Independence

/-- **B3 does not force the fine parent into the selected middle fibre.**

A two-element middle and coarse skeleton with `kF = true` and `lM = false`: the bundle is
satisfied and `pθ kF ≠ lM`.  Hence no `compatibleChain`-style clause is derivable from
`Kakeya.ml1Boot.IsTwoScaleFactors`, which is exactly blueprint §1.3 (GWZ equation (59) holds
for each `T_τ` and each `T_θ` separately). -/
theorem exists_isTwoScaleFactors_parent_ne [Nontrivial E] {δ τ θ : NNReal}
    (hδ0 : 0 < δ) (hτ0 : 0 < τ) (hθ0 : 0 < θ) :
    ∃ (V : Unit → ShadedTube δ E) (Vτ : Bool → Tube τ E) (Vθ : Bool → Tube θ E)
      (Ym : Bool → ShadedTube τ E) (Yc : Bool → ShadedTube θ E)
      (pτ : Unit → Bool) (pθ : Bool → Bool) (kF lM : Bool),
      pθ kF ≠ lM ∧
      IsTwoScaleFactors 1 1 ({()} : Finset Unit) V
        ({true, false} : Finset Bool) Vτ pτ
        ({true, false} : Finset Bool) Vθ pθ
        kF V 1 lM Ym 1 ({false} : Finset Bool) Yc 1 := by
  classical
  obtain ⟨Tδ⟩ := nonempty_tube (E := E) δ
  obtain ⟨Tτ⟩ := nonempty_tube (E := E) τ
  obtain ⟨Tθ⟩ := nonempty_tube (E := E) θ
  refine ⟨fun _ => fullShade Tδ, fun _ => Tτ, fun _ => Tθ,
    fun _ => fullShade Tτ, fun _ => fullShade Tθ,
    (fun _ => true), (fun b => b), true, false, by decide, ?_⟩
  have hfine : fibre ({()} : Finset Unit) (fun _ : Unit => true) true = ({()} : Finset Unit) := by
    unfold fibre; decide
  have hmid : fibre ({true, false} : Finset Bool) (fun b => b) false
      = ({false} : Finset Bool) := by
    unfold fibre; decide
  refine
    { skeleton_fine := by decide
      skeleton_mid := by decide
      fine_mem := by decide
      fine_nonempty := by rw [hfine]; exact ⟨(), Finset.mem_singleton_self ()⟩
      fine_tube := fun _ _ => rfl
      fine_fullness := ?_
      mid_mem := by decide
      mid_nonempty := by rw [hmid]; exact ⟨false, Finset.mem_singleton_self false⟩
      mid_tube := fun _ _ => rfl
      mid_fullness := ?_
      coarse_subset := by decide
      coarse_nonempty := ⟨false, Finset.mem_singleton_self false⟩
      coarse_tube := fun _ _ => rfl
      coarse_fullness := ?_
      branch_card := ?_
      product := ?_ }
  · rw [hfine, fullness_singleton_fullShade hδ0 () (fun _ : Unit => Tδ)]; norm_num
  · rw [hmid, fullness_singleton_fullShade hτ0 false (fun _ : Bool => Tτ)]; norm_num
  · rw [fullness_singleton_fullShade hθ0 false (fun _ : Bool => Tθ)]; norm_num
  · rw [hfine, hmid]; simp
  · rw [hfine, hmid, multiplicity_singleton_fullShade hδ0 () (fun _ : Unit => Tδ),
      multiplicity_singleton_fullShade hτ0 false (fun _ : Bool => Tτ),
      multiplicity_singleton_fullShade hθ0 false (fun _ : Bool => Tθ)]
    norm_num

end Independence


end ml1Boot

end Kakeya
