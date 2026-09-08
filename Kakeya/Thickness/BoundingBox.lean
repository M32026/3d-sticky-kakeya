/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Thickness.Volume

/-!
# Bounding boxes for convex sets

A convex set of finite nonzero volume in a finite-dimensional inner product
space is contained in an axis-aligned box, in a frame the set itself chooses, of
volume at most `2 ^ n * n !` times its own.  This is the weak form of John's
theorem that convex-geometry arguments usually want: it asks only for a
*circumscribed box of comparable volume*, not for the extremal ellipsoid, and
unlike John's theorem it is available here.

Both halves are already in this project and are simply composed:

* `outerPrism` (`Kakeya/Thickness/OuterPrism.lean`) circumscribes a nonempty
  compact set by the box whose half-widths are exactly its `Metric.thickness`es,
  in a frame it constructs itself;
* `Convex.ethickness_prod_le_volume` (`Kakeya/Thickness/Volume.lean`), whose
  proof runs through the maximal inscribed simplex of
  `exists_simplex_of_lt_ethickness`, is the matching lower bound
  `(n !)⁻¹ * prod_i thickness_i <= |W|`.

The only step not already present is that `outerPrism` wants a compact set,
while a convex set of finite volume is not obviously bounded.
`isBounded_of_ethickness_zero_ne_top` supplies that: the rank-`0` thickness is
finite (by the same volume lower bound), and a rank-`0` affine subspace is a
single point, so the set lies in a ball around it.  Since `thickness` is
invariant under closure, the box of the closure is a box of the set with the
set's own half-widths, and no comparison between `|W|` and `|closure W|` is
needed.
-/

@[expose] public section

open MeasureTheory Metric Pointwise

/-- A nonempty set whose rank-`0` `ethickness` is finite is bounded: the rank-`0`
affine subspace realising the thickness is a single point, and the set lies in a
closed ball around it. -/
theorem isBounded_of_ethickness_zero_ne_top {V P : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] {s : Set P}
    (hne : s.Nonempty) (h : ethickness ℝ s 0 ≠ ⊤) : Bornology.IsBounded s := by
  set r : NNReal := (ethickness ℝ s 0).toNNReal + 1 with hr_def
  have hlt : ethickness ℝ s 0 < (r : ENNReal) := by
    rw [hr_def, ENNReal.coe_add, ENNReal.coe_toNNReal h]
    exact ENNReal.lt_add_right h (by simp)
  obtain ⟨A, hA, hsA⟩ := exists_cthickening_of_ethickness_lt (𝕜 := ℝ) hlt
  have hdir : A.direction = ⊥ := by
    rw [← Submodule.rank_eq_zero]
    exact le_antisymm (by simpa using hA) (zero_le)
  obtain ⟨x, hx⟩ := hne
  have hAne : (A : Set P).Nonempty := by
    rcases Set.eq_empty_or_nonempty (A : Set P) with he | hne'
    · rw [he, cthickening_empty] at hsA
      exact absurd (hsA hx) (Set.notMem_empty x)
    · exact hne'
  obtain ⟨a, ha⟩ := hAne
  have hsub : (A : Set P) ⊆ {a} := by
    intro y hy
    have : y -ᵥ a ∈ A.direction := AffineSubspace.vsub_mem_direction hy ha
    rw [hdir, Submodule.mem_bot] at this
    simpa using vsub_eq_zero_iff_eq.mp this
  exact ((Bornology.isBounded_singleton.subset hsub).cthickening).subset hsA

variable
  {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-- A convex set of finite nonzero volume is bounded: its rank-`0` `ethickness`
is finite because the product of all its `ethickness`es is, and none of them
vanishes. -/
theorem Convex.isBounded_of_volume_ne_zero_of_ne_top {W : Set E} (hW : Convex ℝ W)
    (h0 : volume W ≠ 0) (htop : volume W ≠ ⊤) : Bornology.IsBounded W := by
  set n := Module.finrank ℝ E with hn
  have hnpos : 0 < n := Module.finrank_pos
  have hpos : 0 < volume W := pos_iff_ne_zero.mpr h0
  have hne0 : ∀ i ∈ Finset.range n, ethickness ℝ W i ≠ 0 := fun i hi =>
    ethickness_ne_zero_of_volume_pos hpos hi
  have hWne : W.Nonempty := by
    rcases Set.eq_empty_or_nonempty W with he | h
    · rw [he] at h0; simp at h0
    · exact h
  have key : (lt_volume_convexHull.c n : ENNReal) *
      ∏ i ∈ Finset.range n, ethickness ℝ W i ≤ volume W := hW.ethickness_prod_le_volume
  have hprodtop : ∏ i ∈ Finset.range n, ethickness ℝ W i ≠ ⊤ := by
    intro hcon
    have hcne : (lt_volume_convexHull.c n : ENNReal) ≠ 0 := by
      simp only [lt_volume_convexHull.c, ne_eq, ENNReal.coe_eq_zero, inv_eq_zero,
        Nat.cast_eq_zero]
      exact (Nat.factorial_pos n).ne'
    rw [hcon, ENNReal.mul_top hcne] at key
    exact htop (top_le_iff.mp key)
  refine isBounded_of_ethickness_zero_ne_top hWne ?_
  intro hcon
  refine hprodtop ?_
  have h0mem : 0 ∈ Finset.range n := Finset.mem_range.mpr hnpos
  have herase : ∏ i ∈ (Finset.range n).erase 0, ethickness ℝ W i ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i hi =>
      hne0 i (Finset.mem_of_mem_erase hi)
  rw [← Finset.mul_prod_erase _ _ h0mem, hcon, ENNReal.top_mul herase]

/-- **Bounding box for a convex set**, in the frame the set itself chooses.  A
convex `W` of finite nonzero volume is contained in the box centred at `c` with
axes `b` and half-widths `len`, and the product of the half-widths costs at most
`n !` times `|W|`.  Since the box has volume `2 ^ n * prod len`, this is a
circumscribed box of volume at most `2 ^ n * n ! * |W|`.

This is the weak form of John's theorem: it asks only for comparable volume, not
for the extremal ellipsoid. -/
theorem Convex.exists_boundingBox {W : Set E} (hW : Convex ℝ W)
    (h0 : volume W ≠ 0) (htop : volume W ≠ ⊤)
    {n : ℕ} (hn : Module.finrank ℝ E = n) :
    ∃ (c : E) (b : OrthonormalBasis (Fin n) ℝ E) (len : Fin n → ℝ),
      (∀ i, 0 < len i) ∧
      (∀ x ∈ W, ∀ i, |b.repr (x - c) i| ≤ len i) ∧
      ENNReal.ofReal (∏ i, len i)
        ≤ ((n.factorial : NNReal) : ENNReal) * volume W := by
  have hpos : 0 < volume W := pos_iff_ne_zero.mpr h0
  have hbdd : Bornology.IsBounded W := hW.isBounded_of_volume_ne_zero_of_ne_top h0 htop
  have hWne : W.Nonempty := by
    rcases Set.eq_empty_or_nonempty W with he | h
    · rw [he] at h0; simp at h0
    · exact h
  have hne0 : ∀ i : Fin n, ethickness ℝ W i ≠ 0 := fun i =>
    ethickness_ne_zero_of_volume_pos hpos (Finset.mem_range.mpr (hn ▸ i.isLt))
  have heth : ∀ i : ℕ, ethickness ℝ W i = ENNReal.ofReal (thickness ℝ W i) :=
    ethickness_thickness' hbdd
  -- the circumscribed box of the closure, with the closure's (= `W`'s) half-widths
  have hK : IsCompact (closure W) := hbdd.isCompact_closure
  have hKne : (closure W).Nonempty := hWne.closure
  obtain ⟨c, b, hcb⟩ := outerPrism.exists_limit hn hK hKne
  have hthick : ∀ i : ℕ, thickness ℝ (closure W) i = thickness ℝ W i := thickness_closure hbdd
  refine ⟨c, b, fun i => thickness ℝ W i, ?_, ?_, ?_⟩
  · intro i
    have h1 : ENNReal.ofReal (thickness ℝ W i) ≠ 0 := by rw [← heth]; exact hne0 i
    rw [← ENNReal.ofReal_pos]
    exact pos_iff_ne_zero.mpr h1
  · intro x hx i
    have h := hcb x (subset_closure hx) i
    rw [hthick] at h
    simpa using h
  · -- the volume lower bound, with `c(n) = (n !)⁻¹`, read as an upper bound on the product
    have hprod : ENNReal.ofReal (∏ i : Fin n, thickness ℝ W i)
        = ∏ i ∈ Finset.range n, ethickness ℝ W i := by
      rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => thickness_nonneg _ _),
        ← Fin.prod_univ_eq_prod_range (fun i => ethickness ℝ W i) n]
      exact Finset.prod_congr rfl fun i _ => (heth i).symm
    have key : (lt_volume_convexHull.c n : ENNReal) *
        ∏ i ∈ Finset.range n, ethickness ℝ W i ≤ volume W := by
      have := hW.ethickness_prod_le_volume
      rwa [hn] at this
    have hfac : ((n.factorial : NNReal) : ENNReal) * (lt_volume_convexHull.c n : ENNReal) = 1 := by
      rw [← ENNReal.coe_mul, lt_volume_convexHull.c,
        mul_inv_cancel₀ (by exact_mod_cast (Nat.factorial_pos n).ne'), ENNReal.coe_one]
    rw [hprod]
    calc ∏ i ∈ Finset.range n, ethickness ℝ W i
        = ((n.factorial : NNReal) : ENNReal) * ((lt_volume_convexHull.c n : ENNReal) *
            ∏ i ∈ Finset.range n, ethickness ℝ W i) := by
          rw [← mul_assoc, hfac, one_mul]
      _ ≤ ((n.factorial : NNReal) : ENNReal) * volume W := by gcongr

/-- **Bounding prism for a convex set**, the `PrismNDim` form of
`Convex.exists_boundingBox`: a convex set of finite nonzero volume is contained
in a prism of volume at most `2 ^ n * n !` times its own.  This is the weak form
of John's theorem in the shape most consumers want -- a circumscribed box of
comparable volume, with the comparison stated purely as volumes. -/
theorem Convex.exists_boundingPrism {W : Set E} (hW : Convex ℝ W)
    (h0 : volume W ≠ 0) (htop : volume W ≠ ⊤) :
    ∃ P : PrismNDim (Module.finrank ℝ E) E E, W ⊆ P.carrier ∧
      volume P.carrier
        ≤ 2 ^ (Module.finrank ℝ E) * ((Module.finrank ℝ E).factorial : ENNReal)
            * volume W := by
  set n := Module.finrank ℝ E with hn
  obtain ⟨c, b, len, hlen, hsub, hvol⟩ := hW.exists_boundingBox h0 htop hn.symm
  refine ⟨PrismNDim.mk' c b (fun i => (len i).toNNReal), ?_, ?_⟩
  · intro x hx
    rw [PrismNDim.mem_carrier_iff]
    intro i
    rw [PrismNDim.basis_mk', PrismNDim.center_mk', PrismNDim.thicknesses_mk',
      Real.coe_toNNReal _ (hlen i).le]
    simpa [vsub_eq_sub] using hsub x hx i
  · rw [PrismNDim.volume_carrier, PrismNDim.thicknesses_mk', ← hn]
    have hcoe : ∏ i, (((len i).toNNReal : NNReal) : ENNReal)
        = ENNReal.ofReal (∏ i, len i) := by
      rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => (hlen i).le)]
      exact Finset.prod_congr rfl fun i _ => rfl
    rw [hcoe, mul_assoc]
    gcongr
    simpa using hvol

/-- **The difference body of a convex set has comparable volume**, in the weak
form the bounding box gives for free: `W - W` lies in the box with the same axes
and centre `0` and *twice* the half-widths of a bounding box of `W`, whose volume
is `2 ^ n` times that box's, so

`|W - W| ≤ 4 ^ n * n ! * |W|`.

This is a crude substitute for Rogers-Shephard (`|W - W| ≤ C(2n, n) |W|`, sharp,
not in Mathlib and not proved here); only the finiteness of the constant is ever
used.  In `ℝ³` the constant is `4 ^ 3 * 3 ! = 384`, against Rogers-Shephard's
`20`.

No convexity of `W - W` and no measurability of it is needed: the bound is by
monotonicity of the measure against a prism carrier. -/
theorem Convex.volume_sub_le {W : Set E} (hW : Convex ℝ W)
    (h0 : volume W ≠ 0) (htop : volume W ≠ ⊤) :
    volume (W - W)
      ≤ 4 ^ (Module.finrank ℝ E) * ((Module.finrank ℝ E).factorial : ENNReal) * volume W := by
  set n := Module.finrank ℝ E with hn
  obtain ⟨c, b, len, hlen, hsub, hvol⟩ := hW.exists_boundingBox h0 htop hn.symm
  set P : PrismNDim n E E := PrismNDim.mk' (0 : E) b (fun i => (2 * len i).toNNReal) with hP
  have hWW : W - W ⊆ P.carrier := by
    rintro x ⟨a, ha, a', ha', rfl⟩
    rw [hP, PrismNDim.mem_carrier_iff]
    intro i
    rw [PrismNDim.basis_mk', PrismNDim.center_mk', PrismNDim.thicknesses_mk',
      Real.coe_toNNReal _ (by have := (hlen i).le; positivity)]
    have h1 := hsub a ha i
    have h2 := hsub a' ha' i
    have hrw : (a - a' -ᵥ (0:E)) = (a - c) - (a' - c) := by
      simp [vsub_eq_sub, sub_sub_sub_cancel_right]
    rw [hrw, map_sub]
    change |b.repr (a - c) i - b.repr (a' - c) i| ≤ _
    calc |b.repr (a - c) i - b.repr (a' - c) i| ≤ |b.repr (a - c) i| + |b.repr (a' - c) i| :=
          abs_sub _ _
      _ ≤ len i + len i := by gcongr
      _ = 2 * len i := by ring
  refine le_trans (measure_mono hWW) ?_
  rw [hP, PrismNDim.volume_carrier, PrismNDim.thicknesses_mk', ← hn]
  have hcoe : ∏ i, (((2 * len i).toNNReal : NNReal) : ENNReal)
      = ENNReal.ofReal (∏ i, (2 * len i)) := by
    rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => by have := (hlen i).le; positivity)]
    exact Finset.prod_congr rfl fun i _ => rfl
  rw [hcoe]
  have hsplit : ∏ i, (2 * len i) = 2 ^ n * ∏ i, len i := by
    rw [Finset.prod_mul_distrib]
    simp
  rw [hsplit, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
  have h2 : ENNReal.ofReal (2:ℝ) = 2 := by
    rw [show (2:ℝ) = ((2:NNReal):ℝ) by norm_num, ENNReal.ofReal_coe_nnreal]; rfl
  rw [h2]
  calc (2:ENNReal) ^ n * (2 ^ n * ENNReal.ofReal (∏ i, len i))
      = (4:ENNReal) ^ n * ENNReal.ofReal (∏ i, len i) := by
        rw [← mul_assoc, ← mul_pow]; norm_num
    _ ≤ 4 ^ n * (((n.factorial : NNReal) : ENNReal) * volume W) := by gcongr
    _ = 4 ^ n * ((n.factorial : ENNReal)) * volume W := by
        rw [mul_assoc]; norm_num

/-- **A single convex container for all `λ`-homothety images of a convex set about
its own points.**  The bounding box does the whole job: if `W` lies in the box of
centre `c` and half-widths `len`, then for `p, x ∈ W` the point `p + λ (x - p)`
has coordinates `λ (x - c)_i + (1 - λ) (p - c)_i`, of modulus at most
`(2 λ - 1) len i`.  So the *concentric* box with half-widths `2 λ len i` contains
`W` and every such image, and has volume `(4 λ) ^ n * prod len ≤ (4 λ) ^ n n ! |W|`.

This is the form `hdilate` needs and it is strictly better than routing through the
difference body `W - W`: the container is a prism (hence convex and compact) and
its centre is `W`'s own box centre, so no Minkowski sum has to be measured.  The
point `p` is allowed to vary with the object being enlarged -- that is exactly what
defeats a fixed-centre dilate. -/
theorem Convex.exists_homothety_container {W : Set E} (hW : Convex ℝ W)
    (h0 : volume W ≠ 0) (htop : volume W ≠ ⊤) {lam : ℝ} (hlam : 1 ≤ lam) :
    ∃ D : PrismNDim (Module.finrank ℝ E) E E,
      W ⊆ D.carrier ∧
      (∀ p ∈ W, ∀ x ∈ W, lam • (x - p) + p ∈ D.carrier) ∧
      volume D.carrier
        ≤ ENNReal.ofReal (4 * lam) ^ (Module.finrank ℝ E)
            * ((Module.finrank ℝ E).factorial : ENNReal) * volume W := by
  set n := Module.finrank ℝ E with hn
  obtain ⟨c, b, len, hlen, hsub, hvol⟩ := hW.exists_boundingBox h0 htop hn.symm
  have hlam0 : (0:ℝ) < lam := lt_of_lt_of_le one_pos hlam
  refine ⟨PrismNDim.mk' c b (fun i => (2 * lam * len i).toNNReal), ?_, ?_, ?_⟩
  · intro x hx
    rw [PrismNDim.mem_carrier_iff]
    intro i
    rw [PrismNDim.basis_mk', PrismNDim.center_mk', PrismNDim.thicknesses_mk',
      Real.coe_toNNReal _ (by have := (hlen i).le; positivity)]
    have h1 := hsub x hx i
    refine le_trans (by simpa [vsub_eq_sub] using h1) ?_
    nlinarith [(hlen i).le, (hlen i)]
  · intro p hp x hx
    rw [PrismNDim.mem_carrier_iff]
    intro i
    rw [PrismNDim.basis_mk', PrismNDim.center_mk', PrismNDim.thicknesses_mk',
      Real.coe_toNNReal _ (by have := (hlen i).le; positivity)]
    have habs : ∀ A B : ℝ, |A| ≤ len i → |B| ≤ len i → |lam * A + (1 - lam) * B|
        ≤ 2 * lam * len i := by
      intro A B hA hB
      have hA' := abs_le.mp hA
      have hB' := abs_le.mp hB
      rw [abs_le]
      constructor <;> nlinarith [hA'.1, hA'.2, hB'.1, hB'.2, hlen i]
    have h1 : |(b.repr (x - c)) i| ≤ len i := by simpa [vsub_eq_sub] using hsub x hx i
    have h2 : |(b.repr (p - c)) i| ≤ len i := by simpa [vsub_eq_sub] using hsub p hp i
    have hrw : (lam • (x - p) + p -ᵥ c) = lam • (x - c) + (1 - lam) • (p - c) := by
      simp [vsub_eq_sub, sub_smul, smul_sub]
      abel
    rw [hrw, map_add, map_smul, map_smul]
    exact habs _ _ h1 h2
  · rw [PrismNDim.volume_carrier, PrismNDim.thicknesses_mk', ← hn]
    have hcoe : ∏ i, (((2 * lam * len i).toNNReal : NNReal) : ENNReal)
        = ENNReal.ofReal (∏ i, (2 * lam * len i)) := by
      rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => by have := (hlen i).le; positivity)]
      exact Finset.prod_congr rfl fun i _ => rfl
    rw [hcoe]
    have hsplit : ∏ i, (2 * lam * len i) = (2 * lam) ^ n * ∏ i, len i := by
      rw [Finset.prod_mul_distrib]; simp
    rw [hsplit, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity)]
    have h2 : (2:ENNReal) ^ n * (ENNReal.ofReal (2 * lam) ^ n)
        = ENNReal.ofReal (4 * lam) ^ n := by
      rw [← mul_pow]
      congr 1
      rw [show (2:ENNReal) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
      ring_nf
    rw [← mul_assoc, h2, mul_assoc]
    gcongr
    simpa using hvol

end

#print axioms isBounded_of_ethickness_zero_ne_top
#print axioms Convex.isBounded_of_volume_ne_zero_of_ne_top
#print axioms Convex.exists_boundingBox
#print axioms Convex.exists_boundingPrism
#print axioms Convex.volume_sub_le
#print axioms Convex.exists_homothety_container
