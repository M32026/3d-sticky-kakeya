/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.ThickCase

/-!
# The non-concentration field of the thick-case plank presentation (GWZ 9.4.2)

This file proves field 18 (`nonconcentration`) of
`Kakeya.VeryNotSticky.ThickPlankPresentation` — blueprint `lem:ml2thickMbound`, GWZ
`gwz.txt` l.2133-2159 — from the geometric data that the normalisation row of the thick
plank presentation supplies, and from nothing else.

## What is proved

`Kakeya.VeryNotSticky.thickPlank_nonconcentration` produces, verbatim, the type of the
structure field

`Plank.IsThickeningNonconcentrated sel (fun p => (P p).toPrism3D) C_NC
  (Θ * bd.Cbias * (δ/a)^{2+ϱ} * |𝕋_{B,W}|)`

at `Θ = Kakeya.VeryNotSticky.thickNonconcΘ bd.C₀ C_NC CP cW cfg.ϱ`, a `δ`-free function of
`bd.C₀`, the dilation `C_NC`, the comparability constant `CP` of `long_upper`, the
normalisation constant `cW`, and the bias exponent `cfg.ϱ`. The fidelity of the conclusion
against the structure is recorded by the tripwire `example` at the end of the file.

## The argument (GWZ 9.4.2, l.2133-2159, at `K = T_θ`)

Fix a selected plank `P_p` and a thickening parameter `φ`. The container being counted in is
the `C_NC`-dilated thickening `K := ((P_p)_φ).dilation C_NC`, a prism of half-widths
`C_NC (φ b', b', 1)`, so `|K| = 8 C_NC³ φ (b')²` (`PrismNDim.volume_dilation` on
`Plank.volume_thickened`). Pull it back along the normalisation `L` and cut it down to the
factoring body: `K' := L⁻¹(K) ∩ W`, a convex body with `K' ≤ W`, which is the only shape in
which `Kakeya.VeryNotSticky.BallData.biasedDensity` of (C4) may be read. Every selected plank
`P_q ⊆ K` forces `Y_q ⊆ K'`, because `L(Y_q) ⊆ P_q`; so the count of GWZ (90) is bounded by
`|𝕋_{B,W}[K']|`, and

* `Kakeya.le_densityIn_mul_of_volume_band` converts that count into `Δ(𝕋_{B,W}, K') |K'|`,
  paying the segment volume floor of `Kakeya.VeryNotSticky.thickSegVol`;
* `biasedDensity` replaces `Δ(𝕋_{B,W}, K')` by `C_bias (|K'|/|W|)^ϱ Δ(𝕋_{B,W}, W)` — this is
  the one and only source of the gain, exactly as GWZ (82) is used at l.2140;
* `Kakeya.sum_volume_eq_densityIn_mul_volume` turns `Δ(𝕋_{B,W}, W) |W|` into the block's
  total segment mass, bounded by `|𝕋_{B,W}|` times the segment volume ceiling of
  `thickSegVol`.

The two segment bounds are two-sided at the same `C₀`, so their ratio is the `δ`-free
`48 C₀⁶` and nothing else survives of them. What remains is the volume ratio
`|K'|/|W| ≤ |K|/|L(W)| ≤ Λ φ (δ/a)²` with `Λ = 8 C_NC³ CP²/cW` (`long_upper` for
`b' ≤ CP δ/a`, and the binder `cW ≤ |L(W)|`), giving

`|{q : P_q ⊆ K}| ≤ 48 C₀⁶ Λ^{1+ϱ} C_bias · φ^{1+ϱ} (δ/a)^{2+2ϱ} |𝕋_{B,W}|`.

## The exponent budget, which is the question this row was dispatched to settle

The derivation produces `(δ/a)^{2+2ϱ}`, **two** powers of the bias exponent, where the field
asks only for `(δ/a)^{2+ϱ}`; the surplus `(δ/a)^ϱ ≤ 1` is discarded by `δ ≤ a` (`cfg.hdims`).
One power of `ϱ` comes from `biasedDensity`'s own gain and the second from the linear factor
`|K'|/|W|` that the density-to-count conversion already carries. So the budget is not tight,
and it is not tight uniformly in `a < b`: `a` and `b` enter only through `long_upper`
(`b' ≤ CP δ/a`), which is a hypothesis about the plank dimensions and carries no `b`. In
particular no eccentricity condition, and no relation between `a` and `b`, is used anywhere
below.

For the same reason the thickening range is irrelevant: `Kakeya.VeryNotSticky.thickNonconc_count_le`
is stated with no thickening parameter at all, and the bound is linear in `φ` for **every**
`φ ≤ 1`, not merely for `φ ≥ a'/b'`. The hypothesis `a'/b' ≤ φ` of
`Plank.IsThickeningNonconcentrated` is therefore not consumed, and the `CP²` that
`ThickPlankInterface`'s docstring charges for widening the range from `[a/b, 1]` to
`[a'/b', 1]` is not spent here.

## The binders, and who owes them

`cfg`, `bd`, `hB`, `hj` are the general-branch inputs. `P`, `sel`, `hsel`, `CP`,
`long_upper` are fields 9, 10, 11 and 8 of the presentation being built. The three binders
that the normalisation row (`ThickPlankNormalise.lean`) owes are

* `L`, the normalising affine **equivalence** — `Plank.exists_affineEquiv_of_isPlankNormalisation`
  turns the affine map of `Plank.IsPlankNormalisation` into one;
* `hPY : L(Y_q) ⊆ P_q` for the selected `q` — the third conjunct of
  `Plank.exists_normalisedTubePlank`;
* `hLW : cW ≤ |L(W)|` with `0 < cW` `δ`-free — the image of the body is a `κ`-cube of volume
  `8κ³` when `W` *is* the modelled plank (`Plank.image_carrier_eq_cube`); when the plank only
  encloses `W`, `Kakeya.VeryNotSticky.thickNonconc_le_volume_image_of_subset` below converts
  the cube volume into this binder at the cost of the enclosure constant, which
  `Prism3D.volume_carrier_le_of_hasThicknesses` supplies as `48 C₀⁶`.

Nothing here is imported from an auxiliary file: the three are ordinary explicit hypotheses.
-/

@[expose] public section

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric

universe u

/-- The `δ`-free volume-ratio constant of blueprint `lem:ml2thickThickenedVol`:
`|L⁻¹(((P)_φ).dilation C_NC) ∩ W| / |W| ≤ Λ · φ · (δ/a)²` holds at
`Λ = 8 C_NC³ CP² / cW`, where `CP` is the comparability constant of the plank's middle
dimension (`long_upper`) and `cW` is the lower bound for `|L(W)|` supplied by the
normalisation. It is `Λ₀` of the `nonconcentration` docstring, with `384 C₀³` replaced by the
explicit `cW⁻¹`. -/
noncomputable def thickNonconcΛ (C_NC CP cW : NNReal) : NNReal :=
  8 * C_NC ^ (3 : ℕ) * CP ^ (2 : ℕ) / cW

/-- The constant `Θ` of the `nonconcentration` field of
`Kakeya.VeryNotSticky.ThickPlankPresentation`, as this file produces it:
`Θ = 48 C₀⁶ · Λ^{1+ϱ}`. The `48 C₀⁶` is the ratio of the two sides of
`Kakeya.VeryNotSticky.thickSegVol` and the `Λ^{1+ϱ}` is the volume-ratio constant raised to
the one power the biased density spends plus the one power the count already carries.

It is `δ`-free: `C₀`, `C_NC`, `CP`, `cW` and `ϱ` are all fixed before `cfg.δ`. It carries
`C_NC^{3(1+ϱ)}`, which for `ϱ ≤ 1` is inside the `C_NC⁶` the field's docstring budgets. -/
noncomputable def thickNonconcΘ (C₀ C_NC CP cW : NNReal) (ϱ : ℝ) : NNReal :=
  48 * C₀ ^ (6 : ℕ) * (thickNonconcΛ C_NC CP cW) ^ (1 + ϱ)

/-- `1 ≤ Θ`, which the assembly of `Kakeya.VeryNotSticky.ThickPlankPresentable` needs. The
hypothesis `cW ≤ 8 C_NC³ CP²` is exactly `1 ≤ Λ`, and it is free in the intended
instantiation: `cW` is a lower bound for the volume of the normalised body, hence at most
`|B̄(0,1)|`-sized, while `8 C_NC³ CP² ≥ 8` for `1 ≤ C_NC`, `1 ≤ CP`. If a producer ever wants
a `Θ` not of this shape, `Kakeya.VeryNotSticky.thickNonconc_weaken` raises it. -/
theorem one_le_thickNonconcΘ {C₀ C_NC CP cW : NNReal} {ϱ : ℝ} (hC₀ : 1 ≤ C₀) (hϱ : 0 ≤ ϱ)
    (hcW0 : 0 < cW) (hcW : cW ≤ 8 * C_NC ^ (3 : ℕ) * CP ^ (2 : ℕ)) :
    1 ≤ thickNonconcΘ C₀ C_NC CP cW ϱ := by
  have hΛ : 1 ≤ thickNonconcΛ C_NC CP cW := by
    rw [thickNonconcΛ, one_le_div hcW0]
    exact hcW
  have h1 : (1 : NNReal) ≤ (thickNonconcΛ C_NC CP cW) ^ (1 + ϱ) :=
    NNReal.one_le_rpow hΛ (by linarith)
  have h2 : (1 : NNReal) ≤ 48 * C₀ ^ (6 : ℕ) := by
    have hpow : (1 : NNReal) ≤ C₀ ^ (6 : ℕ) := one_le_pow₀ hC₀
    nlinarith [hpow]
  rw [thickNonconcΘ]
  exact one_le_mul_of_one_le_of_one_le h2 h1

/-- Cancellation of the two-sided segment volume bound of
`Kakeya.VeryNotSticky.thickSegVol`: the common factor `v = r₁ δ²` divides out and leaves the
ratio `c₁ c₂` of the two constants. Stated abstractly because that is all the counting step
uses; no positivity of `Z` or `A` is needed. -/
theorem thickNonconc_cancel_aux {A Z v c₁ c₂ : ENNReal} (hv0 : v ≠ 0) (hvt : v ≠ ⊤)
    (hc₁0 : c₁ ≠ 0) (hc₁t : c₁ ≠ ⊤)
    (h : A * (c₁⁻¹ * v) ≤ Z * (c₂ * v)) : A ≤ c₁ * c₂ * Z := by
  have h1 : A * c₁⁻¹ * v ≤ Z * c₂ * v := by
    calc A * c₁⁻¹ * v = A * (c₁⁻¹ * v) := by ring
      _ ≤ Z * (c₂ * v) := h
      _ = Z * c₂ * v := by ring
  have h2 : A * c₁⁻¹ ≤ Z * c₂ := (ENNReal.mul_le_mul_iff_left hv0 hvt).mp h1
  have h3 : A * c₁⁻¹ * c₁ ≤ Z * c₂ * c₁ := by gcongr
  calc A = A * c₁⁻¹ * c₁ := by
        rw [mul_assoc, ENNReal.inv_mul_cancel hc₁0 hc₁t, mul_one]
    _ ≤ Z * c₂ * c₁ := h3
    _ = c₁ * c₂ * Z := by ring

/-- **The exponent bookkeeping of blueprint `lem:ml2thickPowerAbsorb`.**
`(Λ φ T²)^ϱ (Λ φ T²) ≤ Λ^{1+ϱ} T^{2+ϱ} φ`: the two surplus powers `φ^ϱ ≤ 1` and `T^ϱ ≤ 1`
are discarded, using `φ ≤ 1` and `T = δ/a ≤ 1`. This is where the derivation's
`(δ/a)^{2+2ϱ}` is weakened to the field's `(δ/a)^{2+ϱ}`, and it is the only step that
touches the exponent at all. -/
theorem thickNonconc_rpow_aux {Λ φ T : NNReal} {ϱ : ℝ} (hϱ : 0 < ϱ) (hΛ : Λ ≠ 0)
    (hφ1 : φ ≤ 1) (hT0 : T ≠ 0) (hT1 : T ≤ 1) :
    (Λ * φ * T ^ (2 : ℕ)) ^ ϱ * (Λ * φ * T ^ (2 : ℕ)) ≤ Λ ^ (1 + ϱ) * T ^ (2 + ϱ) * φ := by
  have e1 : (Λ * φ * T ^ (2 : ℕ)) ^ ϱ = Λ ^ ϱ * φ ^ ϱ * T ^ (2 * ϱ) := by
    rw [NNReal.mul_rpow, NNReal.mul_rpow]
    congr 1
    rw [← NNReal.rpow_natCast T 2, ← NNReal.rpow_mul]
    norm_num
  have eΛ : Λ ^ ϱ * Λ = Λ ^ (1 + ϱ) := by
    rw [NNReal.rpow_add hΛ, NNReal.rpow_one, mul_comm]
  have eT : T ^ (2 * ϱ) * T ^ (2 : ℕ) = T ^ (2 + ϱ) * T ^ ϱ := by
    rw [← NNReal.rpow_natCast T 2, ← NNReal.rpow_add hT0, ← NNReal.rpow_add hT0]
    congr 1
    push_cast
    ring
  calc (Λ * φ * T ^ (2 : ℕ)) ^ ϱ * (Λ * φ * T ^ (2 : ℕ))
      = (Λ ^ ϱ * Λ) * (φ ^ ϱ * φ) * (T ^ (2 * ϱ) * T ^ (2 : ℕ)) := by rw [e1]; ring
    _ = Λ ^ (1 + ϱ) * (φ ^ ϱ * φ) * (T ^ (2 + ϱ) * T ^ ϱ) := by rw [eΛ, eT]
    _ ≤ Λ ^ (1 + ϱ) * (1 * φ) * (T ^ (2 + ϱ) * 1) := by
        gcongr
        · exact NNReal.rpow_le_one hφ1 hϱ.le
        · exact NNReal.rpow_le_one hT1 hϱ.le
    _ = Λ ^ (1 + ϱ) * T ^ (2 + ϱ) * φ := by ring

/-- **The `cW` binder survives passing from the modelled plank to the body it encloses.**
If `S` has volume at most `Cencl |W|`, and if the image of `S` under the affine equivalence
`L` has volume at least `v`, then the image of `W` has volume at least `v / Cencl`. Both
images are multiplied by the same Jacobian, so no containment, measurability or finiteness
side condition enters — the volume comparison is the whole content.

This is what turns `Plank.image_carrier_eq_cube` — which says that the image of the *plank
model* is a `κ`-cube, of volume `8κ³` — into the hypothesis `hLW` of
`Kakeya.VeryNotSticky.thickPlank_nonconcentration` for the *body* `W_j`, at
`Cencl = Prism3D.enclosureVolumeConstant bd.C₀ = 48 C₀⁶`
(`Prism3D.volume_carrier_le_of_hasThicknesses` on `BallData.bodies_thickness`). Both
constants are `δ`-free, so `cW = 8κ³/(48 C₀⁶)` is. -/
theorem thickNonconc_le_volume_image_of_volume_le
    (L : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin 3))
    {W S : Set (EuclideanSpace ℝ (Fin 3))}
    {Cencl v : ENNReal} (hvol : volume S ≤ Cencl * volume W)
    (hv : v ≤ volume (⇑L '' S)) :
    v / Cencl ≤ volume (⇑L '' W) := by
  set J : ENNReal := ENNReal.ofReal
    |LinearMap.det ((L.linear : EuclideanSpace ℝ (Fin 3) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 3)) :
      EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3))| with hJdef
  have hJvol : ∀ A : Set (EuclideanSpace ℝ (Fin 3)), volume (⇑L '' A) = J * volume A := by
    intro A
    simpa [hJdef] using Kakeya.volume_affineImage L A
  refine ENNReal.div_le_of_le_mul ?_
  calc v ≤ volume (⇑L '' S) := hv
    _ = J * volume S := hJvol S
    _ ≤ J * (Cencl * volume W) := by gcongr
    _ = volume (⇑L '' W) * Cencl := by rw [hJvol W]; ring

/-- **Weakening in the non-concentration parameter.** `Plank.IsThickeningNonconcentrated` is
antitone in `M`: a larger parameter is a weaker statement. This is what lets the assembly
enlarge the `Θ` produced here to whatever `δ`-free `Θ` the interface's consumer has fixed. -/
theorem thickNonconc_weaken {a b : NNReal} {hab : a ≤ b} {hb1 : b ≤ 1} {ι : Type*}
    {s : Finset ι} {V : ι → Plank a b hab hb1} {C M M' : NNReal} (hMM' : M ≤ M')
    (h : Plank.IsThickeningNonconcentrated s V C M) :
    Plank.IsThickeningNonconcentrated s V C M' := by
  intro i hi φ hφ1 hφa
  exact (h i hi φ hφ1 hφa).trans (by gcongr)

open scoped Classical in
/-- **The count of GWZ (90) at `K = T_θ`, with no thickening parameter.**

For any subfamily `G` of the block `𝕋_{B,W}` whose members are carried by `L` into a convex
body `Kb` — the shape in which the non-concentration field's container arrives — the
cardinality of `G` is bounded by `48 C₀⁶ C_bias ρ^{1+ϱ} |𝕋_{B,W}|`, where `ρ` is any bound
for `|Kb| / cW` and `cW` is a lower bound for `|L(W_j)|`.

The proof is GWZ l.2133-2159 verbatim: transport `Kb` back to `K' = L⁻¹(Kb) ∩ W_j`, which is
`≤ W_j` and hence a legal test body for `Kakeya.VeryNotSticky.BallData.biasedDensity` of (C4);
convert the count into a density with `Kakeya.le_densityIn_mul_of_volume_band`; spend
`biasedDensity` once, which is the only source of the exponent gain; and pay for the
conversion with the two-sided segment volume bound `Kakeya.VeryNotSticky.thickSegVol`, whose
ratio is `48 C₀⁶`.

Nothing here is specific to the thickened prism: the container is an arbitrary convex body,
so the statement holds at every thickening parameter, including below `a'/b'`. -/
theorem thickNonconc_count_le
    (cfg : VeryNotSticky.{u}) (bd : BallData cfg) {B : bd.bι} (hB : B ∈ bd.bs)
    {j : bd.ω} (hj : j ∈ bd.bodies B)
    (G : Finset bd.σ) (hG : G ⊆ (bd.segs B).filter fun q => bd.blk q = j)
    (L : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin 3))
    (Kb : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
    (hGK : ∀ q ∈ G, ⇑L '' ((bd.Y q).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ (Kb.carrier : Set (EuclideanSpace ℝ (Fin 3))))
    {cW : NNReal} (hcW : 0 < cW)
    (hLW : (cW : ENNReal)
      ≤ volume (⇑L '' ((bd.Wb j).carrier : Set (EuclideanSpace ℝ (Fin 3)))))
    {ρ : NNReal} (hρ : volume Kb.carrier ≤ (ρ : ENNReal) * (cW : ENNReal)) :
    ((G.card : ℕ) : ENNReal) ≤ 48 * (bd.C₀ : ENNReal) ^ (6 : ℕ) * (bd.Cbias : ENNReal)
        * ((ρ : ENNReal) ^ cfg.ϱ * (ρ : ENNReal))
        * ((((bd.segs B).filter fun q => bd.blk q = j).card : ℕ) : ENNReal) := by
  classical
  rcases Finset.eq_empty_or_nonempty G with rfl | hGne
  · simp
  obtain ⟨q₀, hq₀⟩ := hGne
  have hcont : Continuous (L : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) :=
    L.continuous_of_finiteDimensional
  have hcont' : Continuous (L.symm : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) :=
    L.symm.continuous_of_finiteDimensional
  set Kpre : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
    Kb.affineImage L.symm.toAffineMap hcont' with hKpre
  have hKpre_carrier : (Kpre.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      = ⇑L.symm '' (Kb.carrier : Set (EuclideanSpace ℝ (Fin 3))) := rfl
  have hYsub : ∀ q ∈ G, ((bd.Y q).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ (Kpre.carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
    intro q hq x hx
    rw [hKpre_carrier]
    refine ⟨L x, hGK q hq ⟨x, hx, rfl⟩, ?_⟩
    simp
  have hYW : ∀ q ∈ G, ((bd.Y q).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ ((bd.Wb j).carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
    intro q hq
    have hq' := Finset.mem_filter.mp (hG hq)
    have hle := bd.segs_le B hB q hq'.1
    rw [hq'.2] at hle
    exact SetLike.coe_subset_coe.mpr hle
  have hne : ((Kpre.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ∩ ((bd.Wb j).carrier : Set (EuclideanSpace ℝ (Fin 3)))).Nonempty := by
    obtain ⟨x, hx⟩ := (bd.Y q₀).nonempty
    exact ⟨x, hYsub q₀ hq₀ hx, hYW q₀ hq₀ hx⟩
  set K' : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) := Kpre.inter (bd.Wb j) hne with hK'
  have hK'carrier : (K'.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      = (Kpre.carrier : Set (EuclideanSpace ℝ (Fin 3)))
        ∩ ((bd.Wb j).carrier : Set (EuclideanSpace ℝ (Fin 3))) := rfl
  have hK'W : K' ≤ bd.Wb j := by
    intro x hx
    exact hx.2
  -- the Jacobian of `L`
  set J : ENNReal := ENNReal.ofReal
    |LinearMap.det ((L.linear : EuclideanSpace ℝ (Fin 3) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 3)) :
      EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3))| with hJdef
  have hJvol : ∀ S : Set (EuclideanSpace ℝ (Fin 3)), volume (⇑L '' S) = J * volume S := by
    intro S
    simpa [hJdef] using Kakeya.volume_affineImage L S
  -- `L` maps `K'` into `Kb`
  have hLK' : ⇑L '' (K'.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ (Kb.carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
    rintro _ ⟨x, hx, rfl⟩
    have hx1 : x ∈ (Kpre.carrier : Set (EuclideanSpace ℝ (Fin 3))) := hx.1
    rw [hKpre_carrier] at hx1
    obtain ⟨y, hy, rfl⟩ := hx1
    simpa using hy
  -- the volume band `|K'| ≤ ρ |W|`
  have hK'le : volume (K'.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ≤ (ρ : ENNReal) * volume ((bd.Wb j).carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
    have hcW0 : (cW : ENNReal) ≠ 0 := by
      simpa using hcW.ne'
    have hcWt : (cW : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    refine (ENNReal.mul_le_mul_iff_left hcW0 hcWt).mp ?_
    calc volume (K'.carrier : Set (EuclideanSpace ℝ (Fin 3))) * (cW : ENNReal)
        ≤ volume (K'.carrier : Set (EuclideanSpace ℝ (Fin 3)))
            * (J * volume ((bd.Wb j).carrier : Set (EuclideanSpace ℝ (Fin 3)))) := by
          gcongr
          rw [← hJvol]
          exact hLW
      _ = volume (⇑L '' (K'.carrier : Set (EuclideanSpace ℝ (Fin 3))))
            * volume ((bd.Wb j).carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
          rw [hJvol]; ring
      _ ≤ volume (Kb.carrier : Set (EuclideanSpace ℝ (Fin 3)))
            * volume ((bd.Wb j).carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
          gcongr
      _ ≤ ((ρ : ENNReal) * (cW : ENNReal))
            * volume ((bd.Wb j).carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
          gcongr
      _ = (ρ : ENNReal) * volume ((bd.Wb j).carrier : Set (EuclideanSpace ℝ (Fin 3)))
            * (cW : ENNReal) := by ring
  -- volume band for the segments and the body
  set Yb : bd.σ → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
    fun q => (bd.Y q).toConvexSpaceBody with hYb
  set vlo : ENNReal := (((6 * bd.C₀ ^ 3 : NNReal) : ENNReal))⁻¹
    * ((cfg.r₁ * cfg.δ ^ 2 : NNReal) : ENNReal) with hvlodef
  set vhi : ENNReal := ((8 * bd.C₀ ^ 3 * cfg.r₁ * cfg.δ ^ 2 : NNReal) : ENNReal) with hvhidef
  have hvlo : ∀ q ∈ (bd.segs B).filter (fun q => bd.blk q = j), vlo ≤ volume (Yb q).carrier :=
    fun q hq => (thickSegVol cfg bd hB (Finset.mem_filter.mp hq).1).1
  have hvhi : ∀ q ∈ (bd.segs B).filter (fun q => bd.blk q = j), volume (Yb q).carrier ≤ vhi :=
    fun q hq => (thickSegVol cfg bd hB (Finset.mem_filter.mp hq).1).2
  obtain ⟨hWlo, hWhi⟩ := thickBodyVol cfg bd hB hj
  have hW0 : volume ((bd.Wb j).carrier : Set (EuclideanSpace ℝ (Fin 3))) ≠ 0 := by
    have hpos : (0 : ENNReal) < (((6 * bd.C₀ ^ 3 : NNReal) : ENNReal))⁻¹
        * ((cfg.r₁ * cfg.b * cfg.a : NNReal) : ENNReal) := by
      have h1 : (0 : ENNReal) < (((6 * bd.C₀ ^ 3 : NNReal) : ENNReal))⁻¹ :=
        ENNReal.inv_pos.mpr ENNReal.coe_ne_top
      have h2 : (0 : ENNReal) < ((cfg.r₁ * cfg.b * cfg.a : NNReal) : ENNReal) := by
        have hr : (0 : NNReal) < cfg.r₁ := NNReal.rpow_pos cfg.hδ
        have ha : (0 : NNReal) < cfg.a := cfg_a_pos cfg
        have hb : (0 : NNReal) < cfg.b := cfg_b_pos cfg
        have hprod : (0 : NNReal) < cfg.r₁ * cfg.b * cfg.a := by positivity
        exact_mod_cast hprod
      exact ENNReal.mul_pos h1.ne' h2.ne'
    exact (lt_of_lt_of_le hpos hWlo).ne'
  have hWt : volume ((bd.Wb j).carrier : Set (EuclideanSpace ℝ (Fin 3))) ≠ ⊤ :=
    (bd.Wb j).isCompact.measure_ne_top
  -- the family bound
  have hGsub : G ⊆ Kakeya.familyIn ((bd.segs B).filter fun q => bd.blk q = j) Yb K' := by
    intro q hq
    refine Finset.mem_filter.mpr ⟨hG hq, ?_⟩
    intro x hx
    exact ⟨hYsub q hq hx, hYW q hq hx⟩
  set R : ENNReal := volume (K'.carrier : Set (EuclideanSpace ℝ (Fin 3)))
    / volume ((bd.Wb j).carrier : Set (EuclideanSpace ℝ (Fin 3))) with hRdef
  have hRρ : R ≤ (ρ : ENNReal) := ENNReal.div_le_of_le_mul hK'le
  have e1 : volume (K'.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      = R * volume ((bd.Wb j).carrier : Set (EuclideanSpace ℝ (Fin 3))) :=
    (ENNReal.div_mul_cancel hW0 hWt).symm
  have hstep1 := Kakeya.le_densityIn_mul_of_volume_band
    ((bd.segs B).filter fun q => bd.blk q = j) Yb K'
    (vhi := volume (K'.carrier : Set (EuclideanSpace ℝ (Fin 3)))) (vlo := vlo) hvlo le_rfl
  have hstep2 := bd.biasedDensity B hB j hj K' hK'W
  have hstep3 : Kakeya.densityIn ((bd.segs B).filter fun q => bd.blk q = j) Yb (bd.Wb j)
      * volume ((bd.Wb j).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ≤ ((((bd.segs B).filter fun q => bd.blk q = j).card : ℕ) : ENNReal) * vhi := by
    rw [← Kakeya.sum_volume_eq_densityIn_mul_volume]
    calc ∑ q ∈ ((bd.segs B).filter fun q => bd.blk q = j) with Yb q ≤ bd.Wb j,
            volume (Yb q).carrier
        ≤ ∑ q ∈ ((bd.segs B).filter fun q => bd.blk q = j), volume (Yb q).carrier :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ ≤ ∑ _q ∈ ((bd.segs B).filter fun q => bd.blk q = j), vhi :=
          Finset.sum_le_sum hvhi
      _ = ((((bd.segs B).filter fun q => bd.blk q = j).card : ℕ) : ENNReal) * vhi := by
          rw [Finset.sum_const, nsmul_eq_mul]
  rw [← hYb] at hstep2
  have hchain : Kakeya.densityIn ((bd.segs B).filter fun q => bd.blk q = j) Yb K'
        * volume (K'.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ≤ (bd.Cbias : ENNReal) * ((ρ : ENNReal) ^ cfg.ϱ * (ρ : ENNReal))
          * (((((bd.segs B).filter fun q => bd.blk q = j).card : ℕ) : ENNReal) * vhi) := by
    calc Kakeya.densityIn ((bd.segs B).filter fun q => bd.blk q = j) Yb K'
            * volume (K'.carrier : Set (EuclideanSpace ℝ (Fin 3)))
        = Kakeya.densityIn ((bd.segs B).filter fun q => bd.blk q = j) Yb K'
            * (R * volume ((bd.Wb j).carrier : Set (EuclideanSpace ℝ (Fin 3)))) := by
          rw [← e1]
      _ ≤ ((bd.Cbias : ENNReal) * R ^ cfg.ϱ
            * Kakeya.densityIn ((bd.segs B).filter fun q => bd.blk q = j) Yb (bd.Wb j))
            * (R * volume ((bd.Wb j).carrier : Set (EuclideanSpace ℝ (Fin 3)))) := by
          gcongr
      _ = (bd.Cbias : ENNReal) * (R ^ cfg.ϱ * R)
            * (Kakeya.densityIn ((bd.segs B).filter fun q => bd.blk q = j) Yb (bd.Wb j)
              * volume ((bd.Wb j).carrier : Set (EuclideanSpace ℝ (Fin 3)))) := by ring
      _ ≤ (bd.Cbias : ENNReal) * ((ρ : ENNReal) ^ cfg.ϱ * (ρ : ENNReal))
            * (((((bd.segs B).filter fun q => bd.blk q = j).card : ℕ) : ENNReal) * vhi) := by
          gcongr
          exact cfg.hϱ.le
  have hv0 : ((cfg.r₁ * cfg.δ ^ 2 : NNReal) : ENNReal) ≠ 0 := by
    have hr : (0 : NNReal) < cfg.r₁ := NNReal.rpow_pos cfg.hδ
    have hd : (0 : NNReal) < cfg.δ := cfg.hδ
    have hprod : (0 : NNReal) < cfg.r₁ * cfg.δ ^ 2 := by positivity
    simpa using hprod.ne'
  have hvt : ((cfg.r₁ * cfg.δ ^ 2 : NNReal) : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hc10 : ((6 * bd.C₀ ^ 3 : NNReal) : ENNReal) ≠ 0 := by
    have hC : (0 : NNReal) < bd.C₀ := lt_of_lt_of_le zero_lt_one bd.hC₀
    have hprod : (0 : NNReal) < 6 * bd.C₀ ^ 3 := by positivity
    simpa using hprod.ne'
  have hc1t : ((6 * bd.C₀ ^ 3 : NNReal) : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hh : ((G.card : ℕ) : ENNReal) * vlo
      ≤ ((bd.Cbias : ENNReal) * ((ρ : ENNReal) ^ cfg.ϱ * (ρ : ENNReal))
          * ((((bd.segs B).filter fun q => bd.blk q = j).card : ℕ) : ENNReal)) * vhi := by
    calc ((G.card : ℕ) : ENNReal) * vlo
        ≤ ((Kakeya.familyIn ((bd.segs B).filter fun q => bd.blk q = j) Yb K').card : ENNReal)
            * vlo := by
          gcongr
      _ ≤ Kakeya.densityIn ((bd.segs B).filter fun q => bd.blk q = j) Yb K'
            * volume (K'.carrier : Set (EuclideanSpace ℝ (Fin 3))) := hstep1
      _ ≤ (bd.Cbias : ENNReal) * ((ρ : ENNReal) ^ cfg.ϱ * (ρ : ENNReal))
            * (((((bd.segs B).filter fun q => bd.blk q = j).card : ℕ) : ENNReal) * vhi) := hchain
      _ = ((bd.Cbias : ENNReal) * ((ρ : ENNReal) ^ cfg.ϱ * (ρ : ENNReal))
            * ((((bd.segs B).filter fun q => bd.blk q = j).card : ℕ) : ENNReal)) * vhi := by ring
  rw [hvlodef, hvhidef] at hh
  have hvhi_eq : ((8 * bd.C₀ ^ 3 * cfg.r₁ * cfg.δ ^ 2 : NNReal) : ENNReal)
      = ((8 * bd.C₀ ^ 3 : NNReal) : ENNReal) * ((cfg.r₁ * cfg.δ ^ 2 : NNReal) : ENNReal) := by
    push_cast
    ring
  rw [hvhi_eq] at hh
  have hres := thickNonconc_cancel_aux hv0 hvt hc10 hc1t hh
  refine hres.trans (le_of_eq ?_)
  push_cast
  ring


open scoped Classical in
/-- **Field 18 of `Kakeya.VeryNotSticky.ThickPlankPresentation`** (blueprint
`lem:ml2thickMbound`, GWZ `gwz.txt` l.2133-2159), produced from the normalisation data.

The conclusion is the field's type verbatim, at
`Θ = Kakeya.VeryNotSticky.thickNonconcΘ bd.C₀ C_NC CP cW cfg.ϱ`; the tripwire `example`
below records that fit against the structure.

Hypotheses beyond the general-branch inputs `cfg`, `bd`, `hB`, `hj`:

* `P`, `sel`, `hsel` — fields 9, 10, 11 of the presentation;
* `CP`, `hCP`, `long_upper` — field 8 (`b' ≤ CP δ/a`), the only place `cfg.a` enters;
* `L`, `hPY`, `cW`, `hcW`, `hLW` — the normalisation, its enclosure property, and the
  `δ`-free lower bound for the volume of the image of the body (see the module docstring);
* `C_NC`, `hC_NC` — the dilation, an **input** and not an output.

Neither `a'` nor the range hypothesis `a'/b' ≤ φ` of `Plank.IsThickeningNonconcentrated` is
used, and no relation between `cfg.a` and `cfg.b` is used: see the module docstring. -/
theorem thickPlank_nonconcentration
    (cfg : VeryNotSticky.{u}) (bd : BallData cfg) {B : bd.bι} (hB : B ∈ bd.bs)
    {j : bd.ω} (hj : j ∈ bd.bodies B)
    {a' b' : NNReal} {hab' : a' ≤ b'} {hb1' : b' ≤ 1}
    (P : bd.σ → ShadedPlank a' b' hab' hb1')
    (sel : Finset bd.σ)
    (hsel : sel ⊆ (bd.segs B).filter fun p => bd.blk p = j)
    {CP : NNReal} (hCP : 1 ≤ CP)
    (long_upper : (b' : ℝ) ≤ (CP : ℝ) * ((cfg.δ : ℝ) / (cfg.a : ℝ)))
    (L : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin 3))
    (hPY : ∀ q ∈ sel, ⇑L '' ((bd.Y q).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ ((P q).carrier : Set (EuclideanSpace ℝ (Fin 3))))
    {cW : NNReal} (hcW : 0 < cW)
    (hLW : (cW : ENNReal)
      ≤ volume (⇑L '' ((bd.Wb j).carrier : Set (EuclideanSpace ℝ (Fin 3)))))
    {C_NC : NNReal} (hC_NC : 1 ≤ C_NC) :
    Plank.IsThickeningNonconcentrated sel (fun p => (P p).toPrism3D) C_NC
      (thickNonconcΘ bd.C₀ C_NC CP cW cfg.ϱ * bd.Cbias *
        (cfg.δ / cfg.a) ^ (2 + cfg.ϱ) *
        ((((bd.segs B).filter fun p => bd.blk p = j).card : ℕ) : NNReal)) := by
  classical
  intro p hp φ hφ1 _hφa
  have hapos : (0 : NNReal) < cfg.a := cfg_a_pos cfg
  set T : NNReal := cfg.δ / cfg.a with hTdef
  have hT0 : T ≠ 0 := by
    rw [hTdef]
    exact div_ne_zero cfg.hδ.ne' hapos.ne'
  have hT1 : T ≤ 1 := by
    rw [hTdef, div_le_one hapos]
    exact cfg.hdims.1
  set Λ : NNReal := thickNonconcΛ C_NC CP cW with hΛdef
  have hCNC0 : C_NC ≠ 0 := (lt_of_lt_of_le zero_lt_one hC_NC).ne'
  have hCP0 : CP ≠ 0 := (lt_of_lt_of_le zero_lt_one hCP).ne'
  have hΛ0 : Λ ≠ 0 := by
    rw [hΛdef, thickNonconcΛ]
    refine div_ne_zero ?_ hcW.ne'
    positivity
  set Kb : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
    ((Plank.thickened ((P p).toPrism3D) φ hφ1).toPrismNDim.dilation C_NC).toConvexSpaceBody
      with hKbdef
  have hb'T : b' ≤ CP * T := by
    rw [hTdef]
    have hcast : (b' : ℝ) ≤ ((CP * (cfg.δ / cfg.a) : NNReal) : ℝ) := by
      push_cast
      exact long_upper
    exact_mod_cast hcast
  have hKbvol : volume (Kb.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ≤ ((Λ * φ * T ^ (2 : ℕ) : NNReal) : ENNReal) * (cW : ENNReal) := by
    have hvol : volume (Kb.carrier : Set (EuclideanSpace ℝ (Fin 3)))
        = (C_NC : ENNReal) ^ (3 : ℕ)
          * (8 * (φ : ENNReal) * (b' : ENNReal) * (b' : ENNReal)) := by
      rw [hKbdef, PrismNDim.volume_dilation, Plank.volume_thickened]
    have hcancel : Λ * cW = 8 * C_NC ^ (3 : ℕ) * CP ^ (2 : ℕ) := by
      rw [hΛdef, thickNonconcΛ]
      exact div_mul_cancel₀ _ hcW.ne'
    have hnn : C_NC ^ (3 : ℕ) * (8 * φ * b' * b') ≤ Λ * φ * T ^ (2 : ℕ) * cW := by
      calc C_NC ^ (3 : ℕ) * (8 * φ * b' * b')
          ≤ C_NC ^ (3 : ℕ) * (8 * φ * (CP * T) * (CP * T)) := by gcongr
        _ = (8 * C_NC ^ (3 : ℕ) * CP ^ (2 : ℕ)) * φ * T ^ (2 : ℕ) := by ring
        _ = Λ * cW * φ * T ^ (2 : ℕ) := by rw [hcancel]
        _ = Λ * φ * T ^ (2 : ℕ) * cW := by ring
    rw [hvol]
    calc (C_NC : ENNReal) ^ (3 : ℕ) * (8 * (φ : ENNReal) * (b' : ENNReal) * (b' : ENNReal))
        = ((C_NC ^ (3 : ℕ) * (8 * φ * b' * b') : NNReal) : ENNReal) := by push_cast; ring
      _ ≤ ((Λ * φ * T ^ (2 : ℕ) * cW : NNReal) : ENNReal) := by exact_mod_cast hnn
      _ = ((Λ * φ * T ^ (2 : ℕ) : NNReal) : ENNReal) * (cW : ENNReal) := by push_cast; ring
  have key : ∀ G : Finset bd.σ, (∀ q ∈ G, q ∈ sel) →
      (∀ q ∈ G, ((P q).toPrism3D.carrier : Set (EuclideanSpace ℝ (Fin 3)))
        ⊆ (Kb.carrier : Set (EuclideanSpace ℝ (Fin 3)))) →
      ((G.card : ℕ) : NNReal)
        ≤ (thickNonconcΘ bd.C₀ C_NC CP cW cfg.ϱ * bd.Cbias *
            (cfg.δ / cfg.a) ^ (2 + cfg.ϱ) *
            ((((bd.segs B).filter fun p => bd.blk p = j).card : ℕ) : NNReal)) * φ := by
    intro G hGsel hGKb
    have hG : G ⊆ (bd.segs B).filter fun q => bd.blk q = j := fun q hq => hsel (hGsel q hq)
    have hGK : ∀ q ∈ G, ⇑L '' ((bd.Y q).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        ⊆ (Kb.carrier : Set (EuclideanSpace ℝ (Fin 3))) :=
      fun q hq => (hPY q (hGsel q hq)).trans (hGKb q hq)
    have hcore := thickNonconc_count_le cfg bd hB hj G hG L Kb hGK hcW hLW hKbvol
    have hcoe : ((G.card : ℕ) : NNReal)
        ≤ 48 * bd.C₀ ^ (6 : ℕ) * bd.Cbias
            * ((Λ * φ * T ^ (2 : ℕ)) ^ cfg.ϱ * (Λ * φ * T ^ (2 : ℕ)))
            * ((((bd.segs B).filter fun p => bd.blk p = j).card : ℕ) : NNReal) := by
      rw [← ENNReal.coe_le_coe]
      refine hcore.trans (le_of_eq ?_)
      rw [← ENNReal.coe_rpow_of_nonneg _ cfg.hϱ.le]
      push_cast
      ring
    refine hcoe.trans ?_
    have hr := thickNonconc_rpow_aux (Λ := Λ) (φ := φ) (T := T) (ϱ := cfg.ϱ) cfg.hϱ hΛ0 hφ1 hT0 hT1
    calc 48 * bd.C₀ ^ (6 : ℕ) * bd.Cbias
            * ((Λ * φ * T ^ (2 : ℕ)) ^ cfg.ϱ * (Λ * φ * T ^ (2 : ℕ)))
            * ((((bd.segs B).filter fun p => bd.blk p = j).card : ℕ) : NNReal)
        ≤ 48 * bd.C₀ ^ (6 : ℕ) * bd.Cbias * (Λ ^ (1 + cfg.ϱ) * T ^ (2 + cfg.ϱ) * φ)
            * ((((bd.segs B).filter fun p => bd.blk p = j).card : ℕ) : NNReal) := by gcongr
      _ = (thickNonconcΘ bd.C₀ C_NC CP cW cfg.ϱ * bd.Cbias *
            (cfg.δ / cfg.a) ^ (2 + cfg.ϱ) *
            ((((bd.segs B).filter fun p => bd.blk p = j).card : ℕ) : NNReal)) * φ := by
          rw [thickNonconcΘ, ← hΛdef, ← hTdef]
          ring
  exact key _ (fun q hq => (Finset.mem_filter.mp hq).1) (fun q hq => (Finset.mem_filter.mp hq).2)

/-- **Fidelity tripwire.** The conclusion of
`Kakeya.VeryNotSticky.thickPlank_nonconcentration` is, verbatim, the field
`nonconcentration` of `Kakeya.VeryNotSticky.ThickPlankPresentation` read at
`Θ = Kakeya.VeryNotSticky.thickNonconcΘ bd.C₀ C_NC CP cW cfg.ϱ`. If the field's text drifts
— an exponent moved, `bd.Cbias` absorbed into `Θ`, the block cardinality replaced by
`sel.card`, the container changed — this stops compiling. It is an `example` so that it
records the fit without adding a declaration. -/
example {cfg : VeryNotSticky.{u}} {bd : BallData cfg} {B : bd.bι} {j : bd.ω}
    {CP Θ C_NC : NNReal} (h : ThickPlankPresentation bd B j CP Θ C_NC) :
    Plank.IsThickeningNonconcentrated h.sel (fun p => (h.P p).toPrism3D) C_NC
      (Θ * bd.Cbias * (cfg.δ / cfg.a) ^ (2 + cfg.ϱ) *
        ((((bd.segs B).filter fun p => bd.blk p = j).card : ℕ) : NNReal)) :=
  h.nonconcentration

end Kakeya.VeryNotSticky
