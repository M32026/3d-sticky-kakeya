/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.FrostmanPlankGeometry
public import Kakeya.DimensionThree.Plank.TubePlankNormalisation
public import Kakeya.DimensionThree.Plank.Section6CoarseFactorisation

/-!
# GWZ Section 6 geometry: thickened pullback slabs, transversality, slab non-concentration

Second half of the Section 6 geometry development, split off from
`Kakeya.DimensionThree.Plank.FrostmanPlankGeometry` for file size. It contains the volume estimates for
thickened pullback slabs (S6G19), the coarse/fine fibre slab count (S6G20), and the two
consumer-facing results `Plank.katzTaoTransverseFactorBound` and `Plank.slabNonconcentration_of_factorization` behind
GWZ Proposition 6.6(B).
-/

@[expose] public section

open MeasureTheory Kakeya
open scoped NNReal Real Classical

noncomputable section

namespace Plank

/-- **The volume half of S6G19, proved.** Thickening the pullback `K_{W,S}` by `C_rad·ρ` inflates
its volume by at most an absolute factor, so the S6G17 bound `|K_{W,S}| ≤ C_pull·θ·|W|` survives.

The mechanism is the one the blueprint describes as "`∏(1 + 2Cρ/w_k)` is absolutely bounded":
by S6G18 the least width of `K_{W,S}` is at least `c_tr·θ·b`, while the radius is
`C_rad·ρ ≤ C_rad·a ≤ C_rad·θ·b`, so radius and least width are comparable with ratio
`C_rad / c_tr`. `Convex.volume_cthickening_le_of_le_scale` (which packages
`volume_cthickening_le_prod_max_ethickness`, i.e. `Metric.ethickness_cthickening_le` +
`volume_le_prod_ethickness`, together with `Convex.ethickness_prod_le_volume`) then bounds the
inflation, and intersecting with `W` only decreases volume.

The constant depends on `c_tr` and `C_rad`, which is why they are quantified *before* it. -/
theorem volumeCthickeningPullbackSlab (ctr Crad : ℝ≥0) (hctr : 0 < ctr) (hCrad : 1 ≤ Crad) :
    ∃ Cctr : ℝ≥0, 1 ≤ Cctr ∧
      ∀ {a b ρ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} (ha : 0 < a) (hρa : ρ ≤ a)
        (W : Plank a b hab hb1) (K : Set (EuclideanSpace ℝ (Fin 3))), Convex ℝ K →
        ∀ (θ Cpull : ℝ≥0), 1 ≤ Cpull → a / b ≤ θ →
          volume K ≤ (Cpull : ENNReal) * (θ : ENNReal) * volume W.carrier →
          ((ctr * a : ℝ≥0) : ENNReal) ≤ Metric.ethickness.scale ℝ K →
          volume (W.carrier ∩ Metric.cthickening ((Crad * ρ : ℝ≥0) : ℝ) K)
            ≤ (Cctr : ENNReal) * (Cpull : ENNReal) * (θ : ENNReal) * volume W.carrier := by
  set M : ℝ≥0 := Crad / ctr with hM
  set Cctr : ℝ≥0 := max 1 (volume_cthickening_le_of_le_scale.C 3 M) with hCctr
  have hCctr_one : 1 ≤ Cctr := le_max_left _ _
  refine ⟨Cctr, hCctr_one, ?_⟩
  intro a b ρ hab hb1 ha hρa W K hKconv θ Cpull hCpull hθge hvolK hwidth
  have hwpos : 0 < ctr * a := by positivity
  have hrM : Crad * ρ ≤ M * (ctr * a) := by
    have h1 : (Crad : ℝ) * (ρ : ℝ) ≤ (Crad : ℝ) * (a : ℝ) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hρa) (by positivity : 0 ≤ (Crad : ℝ))
    have h2 : (M : ℝ) * ((ctr : ℝ) * (a : ℝ)) = (Crad : ℝ) * (a : ℝ) := by
      dsimp [M]
      field_simp [hctr.ne']
    have h3 : (Crad : ℝ) * (ρ : ℝ) ≤ (M : ℝ) * ((ctr : ℝ) * (a : ℝ)) := by
      calc
        (Crad : ℝ) * (ρ : ℝ) ≤ (Crad : ℝ) * (a : ℝ) := h1
        _ = (M : ℝ) * ((ctr : ℝ) * (a : ℝ)) := by rw [h2]
    exact_mod_cast h3
  have hNontriv : Nontrivial (EuclideanSpace ℝ (Fin 3)) := by infer_instance
  have hmain := Convex.volume_cthickening_le_of_le_scale (E := EuclideanSpace ℝ (Fin 3)) hKconv
    hwpos hrM hwidth
  have hfinrank : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := finrank_euclideanSpace_fin
  rw [hfinrank] at hmain
  calc
    volume (W.carrier ∩ Metric.cthickening ((Crad * ρ : ℝ≥0) : ℝ) K)
        ≤ volume (Metric.cthickening ((Crad * ρ : ℝ≥0) : ℝ) K) :=
      measure_mono Set.inter_subset_right
    _ ≤ ((volume_cthickening_le_of_le_scale.C 3 M : ℝ≥0) : ENNReal) * volume K := hmain
    _ ≤ ((Cctr : ℝ≥0) : ENNReal) * volume K := by
      gcongr
      exact_mod_cast le_max_right 1 (volume_cthickening_le_of_le_scale.C 3 M)
    _ ≤ ((Cctr : ℝ≥0) : ENNReal) * ((Cpull : ENNReal) * (θ : ENNReal) * volume W.carrier) := by
      gcongr
    _ = (Cctr : ENNReal) * (Cpull : ENNReal) * (θ : ENNReal) * volume W.carrier := by ring

/-- The slab with the **same frame** as `S`, thin half-width `θ'`, and centre re-positioned so that it
agrees with `S` in the thin coordinate but is centred at `c` in the two long coordinates:
`c + ⟪S.center - c, S.basis 0⟫ • S.basis 0`.

Re-centring is what makes the dilated slab usable. Enlarging only the thin thickness cannot work,
since the type `Slab` pins the two long thicknesses to `1`, while points of a thickening of `f⁻¹(S)`
overshoot the long constraints of `S` as well. After re-centring at `c = f W.center`, the long
coordinate of `f x` is `⟪f x - f W.center, S.basis j⟫`, bounded by `‖f x - f W.center‖ ≤ 1` for
`x ∈ W`, with no dependence on the thickening radius. -/
def recentredThinSlab {θ : ℝ≥0} {hθ1 : θ ≤ 1} (S : Slab θ hθ1)
    (c : EuclideanSpace ℝ (Fin 3)) (θ' : ℝ≥0) (hθ'1 : θ' ≤ 1) : Slab θ' hθ'1 where
  toPrismNDim :=
    PrismNDim.mk' (c + (inner ℝ (S.center - c) (S.basis 0)) • S.basis 0) S.basis ![θ', 1, 1]
  thicknesses_eq := rfl

/-- **The containment behind the dilated-slab route.** A thickening of the pullback, intersected with
`W`, lands in the pullback of the re-centred dilated slab, provided the thin thickness `θ'` absorbs
`θ + r‖m₀‖`.

The thin coordinate is unchanged by re-centring (the shift is parallel to `S.basis 0`), so it is
bounded by `θ + r‖m₀‖` using `Plank.inner_pullbackNormal_sub` and Cauchy--Schwarz against a nearby
point of the pullback. The two long coordinates are bounded by `‖f x - f W.center‖ ≤ 1` and involve no
`r`. -/
theorem subset_preimage_recentredThinSlab {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (W : Plank a b hab hb1)
    {f : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)} {κ : ℝ}
    {g : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))}
    (hnorm : IsPlankNormalisation W f κ g)
    (hWimg : ∀ x ∈ W.carrier, ‖f x - f W.center‖ ≤ 1)
    {θ : ℝ≥0} {hθ1 : θ ≤ 1} (S : Slab θ hθ1)
    {θ' : ℝ≥0} (hθ'1 : θ' ≤ 1) {r : ℝ} (hr : 0 ≤ r)
    (hthin : (θ : ℝ) + r * ‖pullbackNormal W κ g (S.basis 0)‖ ≤ (θ' : ℝ)) :
    W.carrier ∩ Metric.cthickening r (W.carrier ∩ f ⁻¹' S.carrier)
      ⊆ f ⁻¹' (recentredThinSlab S (f W.center) θ' hθ'1).carrier := by
  intro x hx
  rcases hx with ⟨hxW, hxN⟩
  set c := f W.center
  set n := S.basis 0
  set m := pullbackNormal W κ g n
  set P := recentredThinSlab S c θ' hθ'1
  have hcenter : P.center = c + (inner ℝ (S.center - c) n) • n := rfl
  have hbasis : P.basis = S.basis := rfl
  have hthicknesses : P.thicknesses = ![θ', 1, 1] := rfl
  -- Goal: f x ∈ P.carrier
  rw [Set.mem_preimage, P.mem_carrier_iff, hbasis, hthicknesses]
  intro i
  have h_inner : S.basis.repr (f x -ᵥ P.center) i = inner ℝ (f x -ᵥ P.center) (S.basis i) := by
    rw [S.basis.repr_apply_apply, real_inner_comm]
  rw [h_inner, vsub_eq_sub, hcenter]
  -- three cases: i = 0 (thin coordinate), i = 1, 2 (long coordinates)
  by_cases hi0 : i = 0
  · subst hi0; simp
    -- i = 0: thickness is θ'.  Show that inner ℝ (f x - (c + (inner ℝ (S.center - c) n) • n)) n = inner ℝ (f x - S.center) n
    -- because the shift cancels orthogonally
    have h_eq : inner ℝ (f x - (c + (inner ℝ (S.center - c) n) • n)) n = inner ℝ (f x - S.center) n := by
      calc
        inner ℝ (f x - (c + (inner ℝ (S.center - c) n) • n)) n
            = inner ℝ (f x - c - (inner ℝ (S.center - c) n) • n) n := by
              rw [show f x - (c + (inner ℝ (S.center - c) n) • n) = (f x - c) - (inner ℝ (S.center - c) n) • n by abel]
        _ = inner ℝ (f x - c) n - inner ℝ ((inner ℝ (S.center - c) n) • n) n := by rw [inner_sub_left]
        _ = inner ℝ (f x - c) n - (inner ℝ (S.center - c) n) * inner ℝ n n := by
          rw [inner_smul_left]; simp
        _ = inner ℝ (f x - c) n - (inner ℝ (S.center - c) n) * 1 := by
          rw [real_inner_self_eq_norm_sq, S.basis.norm_eq_one 0]; norm_num
        _ = inner ℝ (f x - c) n - inner ℝ (S.center - c) n := by ring
        _ = inner ℝ (f x - c - (S.center - c)) n := by
          simp [inner_sub_left, sub_sub]
        _ = inner ℝ (f x - S.center) n := by
          simp [sub_sub]
    rw [h_eq]
    set K := W.carrier ∩ f ⁻¹' S.carrier
    have hK_nonempty_or : K = ∅ ∨ K.Nonempty :=
      Set.eq_empty_or_nonempty _
    rcases hK_nonempty_or with (hK_empty | hK_nonempty)
    · -- If K is empty, then cthickening r ∅ = ∅, so hxN gives a contradiction
      rw [hK_empty] at hxN
      rw [Metric.cthickening_empty] at hxN
      exact absurd hxN (Set.notMem_empty _)
    · -- K is nonempty, we can use the Metric.infEDist approach
      have h_mem_cthick : Metric.infEDist x K ≤ ENNReal.ofReal r := by
        rw [← Metric.mem_cthickening_iff]
        exact hxN
      -- Show |inner ℝ (f x - S.center) n| ≤ θ + r * ‖m‖
      have h_bound : |inner ℝ (f x - S.center) n| ≤ θ + r * ‖m‖ := by
        -- For any η > 0, pick ε = η / (‖m‖ + 1) so that (r + ε) * ‖m‖ ≤ r * ‖m‖ + η
        refine le_of_forall_pos_le_add fun η hη => ?_
        have hnm : 0 ≤ ‖m‖ := norm_nonneg _
        set ε := η / (‖m‖ + 1) with hε_def
        have hε_pos : 0 < ε := by
          refine div_pos hη ?_
          nlinarith
        have h_ineq : (r + ε) * ‖m‖ ≤ r * ‖m‖ + η := by
          calc
            (r + ε) * ‖m‖ = r * ‖m‖ + ε * ‖m‖ := by ring
            _ ≤ r * ‖m‖ + ε * (‖m‖ + 1) := by
              gcongr; nlinarith
            _ = r * ‖m‖ + η := by
              dsimp [ε]
              field_simp [show ‖m‖ + 1 ≠ 0 from by nlinarith]
        have h_lt : Metric.infEDist x K < ENNReal.ofReal (r + ε) := by
          calc
            Metric.infEDist x K ≤ ENNReal.ofReal r := h_mem_cthick
            _ < ENNReal.ofReal (r + ε) := by
              rw [ENNReal.ofReal_lt_ofReal_iff (by nlinarith : 0 < r + ε)]
              nlinarith
        obtain ⟨z, hzK, hz_edist⟩ := Metric.infEDist_lt_iff.mp h_lt
        have hz_dist : dist x z < r + ε := by
          have : edist x z = ENNReal.ofReal (dist x z) := edist_dist x z
          rw [this] at hz_edist
          have hpos : 0 < r + ε := by nlinarith
          have := (ENNReal.ofReal_lt_ofReal_iff hpos).mp hz_edist
          exact this
        rcases hzK with ⟨hzW, hzfS⟩
        have hz_fS : f z ∈ S.carrier := hzfS
        have hz_S_mem : |inner ℝ (f z - S.center) n| ≤ (θ : ℝ) := by
          rw [S.mem_carrier_iff] at hz_fS
          have hz0 := hz_fS 0
          have h_inner' : S.basis.repr (f z -ᵥ S.center) 0 = inner ℝ (f z -ᵥ S.center) (S.basis 0) := by
            rw [S.basis.repr_apply_apply, real_inner_comm]
          rw [h_inner', vsub_eq_sub, S.thicknesses_eq] at hz0
          simpa using hz0
        have h_inner_sub : inner ℝ (f x - S.center) n = inner ℝ (f z - S.center) n + inner ℝ (f x - f z) n := by
          rw [show f x - S.center = (f z - S.center) + (f x - f z) by abel, inner_add_left]
        have h_inner_fx_fz_n : inner ℝ (f x - f z) n = inner ℝ (x - z) m :=
          W.inner_pullbackNormal_sub hnorm n x z
        have h_abs_inner : |inner ℝ (f x - f z) n| ≤ dist x z * ‖m‖ := by
          rw [h_inner_fx_fz_n]
          calc
            |inner ℝ (x - z) m| ≤ ‖x - z‖ * ‖m‖ := abs_real_inner_le_norm _ _
            _ = dist x z * ‖m‖ := by rw [dist_eq_norm]
        calc
          |inner ℝ (f x - S.center) n|
              = |inner ℝ (f z - S.center) n + inner ℝ (f x - f z) n| := by rw [h_inner_sub]
          _ ≤ |inner ℝ (f z - S.center) n| + |inner ℝ (f x - f z) n| := abs_add_le _ _
          _ ≤ (θ : ℝ) + dist x z * ‖m‖ := by nlinarith
          _ ≤ (θ : ℝ) + (r + ε) * ‖m‖ := by
            gcongr
          _ ≤ (θ : ℝ) + (r * ‖m‖ + η) := by gcongr
          _ = (θ : ℝ) + r * ‖m‖ + η := by ring
      have h_goal : |inner ℝ (f x - S.center) n| ≤ (θ' : ℝ) := by
        nlinarith
      simpa [hthicknesses] using h_goal
  · by_cases hi1 : i = 1
    · subst hi1; simp
      -- i = 1: long coordinate, thickness 1
      have h_orth : inner ℝ ((inner ℝ (S.center - c) n) • n) (S.basis 1) = 0 := by
        rw [inner_smul_left, S.basis.inner_eq_zero (show (0 : Fin 3) ≠ 1 by decide), mul_zero]
      have h_eq : inner ℝ (f x - (c + (inner ℝ (S.center - c) n) • n)) (S.basis 1) = inner ℝ (f x - c) (S.basis 1) := by
        calc
          inner ℝ (f x - (c + (inner ℝ (S.center - c) n) • n)) (S.basis 1)
              = inner ℝ (f x - c - (inner ℝ (S.center - c) n) • n) (S.basis 1) := by
                rw [show f x - (c + (inner ℝ (S.center - c) n) • n) = (f x - c) - (inner ℝ (S.center - c) n) • n by abel]
          _ = inner ℝ (f x - c) (S.basis 1) - inner ℝ ((inner ℝ (S.center - c) n) • n) (S.basis 1) := by rw [inner_sub_left]
          _ = inner ℝ (f x - c) (S.basis 1) - 0 := by rw [h_orth]
          _ = inner ℝ (f x - c) (S.basis 1) := sub_zero _
      rw [h_eq]
      calc
        |inner ℝ (f x - c) (S.basis 1)| ≤ ‖f x - c‖ * ‖S.basis 1‖ := abs_real_inner_le_norm _ _
        _ = ‖f x - c‖ * 1 := by rw [S.basis.norm_eq_one 1]
        _ = ‖f x - c‖ := by ring
        _ ≤ 1 := hWimg x hxW
        _ = (1 : ℝ) := by norm_num
    · have hi2 : i = 2 := by
        fin_cases i <;> simp at hi0 hi1 <;> tauto
      subst hi2; simp
      -- i = 2: long coordinate, thickness 1
      have h_orth : inner ℝ ((inner ℝ (S.center - c) n) • n) (S.basis 2) = 0 := by
        rw [inner_smul_left, S.basis.inner_eq_zero (show (0 : Fin 3) ≠ 2 by decide), mul_zero]
      have h_eq : inner ℝ (f x - (c + (inner ℝ (S.center - c) n) • n)) (S.basis 2) = inner ℝ (f x - c) (S.basis 2) := by
        calc
          inner ℝ (f x - (c + (inner ℝ (S.center - c) n) • n)) (S.basis 2)
              = inner ℝ (f x - c - (inner ℝ (S.center - c) n) • n) (S.basis 2) := by
                rw [show f x - (c + (inner ℝ (S.center - c) n) • n) = (f x - c) - (inner ℝ (S.center - c) n) • n by abel]
          _ = inner ℝ (f x - c) (S.basis 2) - inner ℝ ((inner ℝ (S.center - c) n) • n) (S.basis 2) := by rw [inner_sub_left]
          _ = inner ℝ (f x - c) (S.basis 2) - 0 := by rw [h_orth]
          _ = inner ℝ (f x - c) (S.basis 2) := sub_zero _
      rw [h_eq]
      calc
        |inner ℝ (f x - c) (S.basis 2)| ≤ ‖f x - c‖ * ‖S.basis 2‖ := abs_real_inner_le_norm _ _
        _ = ‖f x - c‖ * 1 := by rw [S.basis.norm_eq_one 2]
        _ = ‖f x - c‖ := by ring
        _ ≤ 1 := hWimg x hxW
        _ = (1 : ℝ) := by norm_num

/-- **Volume of the thickened pullback, via the dilated slab** — the replacement for the least-width
route to the volume half of S6G19.

`Plank.volumeCthickeningPullbackSlab` above is true and proved, but its least-width hypothesis cannot
be discharged: the honest width bound for `K_{W,S}` is `δ` (see
`Plank.pullbackNormalisedSlabMinWidthOfTube`, and the counterexample in its docstring showing that
`c_tr · a` is false), while the thickening radius is `C_rad · ρ` with `δ ≤ ρ ≤ a`. So the ratio of
radius to width is unbounded and that route is closed.

The route that does work avoids widths entirely. By `Plank.inner_pullbackNormal` the `S.basis 0`
constraint pulls back to the strip `|⟪x - x_c, m₀⟫| ≤ θ`, so thickening by `r` enlarges it to
`|⟪x - x_c, m₀⟫| ≤ θ + r‖m₀‖`, i.e. `N_r(K_{W,S})` lies in the pullback of the slab `S` *dilated in
its thin direction* by the factor `1 + r‖m₀‖/θ`. By `Plank.norm_pullbackNormal_le`,
`‖m₀‖ ≤ κ(C_tang + 2)·θ/a`, and `r = C_rad·ρ ≤ C_rad·a`, so that factor is at most
`1 + C_rad·κ(C_tang + 2)` — an absolute constant, with both `a` and `θ` cancelling. Applying S6G17
(`Plank.volumePullbackNormalisedSlab`) to the dilated slab bounds the volume by
`C_pull · (1 + C_rad κ(C_tang+2)) · θ · |W|`, which is the claim.

The dilated slab must be **re-centred**: enlarging only the thin thickness is not enough, because
points of `N_r(K_{W,S})` also overshoot the two *long* constraints of `S`, whose thickness is pinned to
`1` by the type `Slab`. Moving the centre to `f W.center` in the long directions fixes this: the long
coordinate of `f x` relative to the new centre is `⟪f x - f W.center, S.basis j⟫`, which is at most
`‖f x - f W.center‖ ≤ 1` for `x ∈ W` and carries no `r` at all. Only the thin direction has to absorb
`r‖m₀‖`. See `Plank.recentredThinSlab` and `Plank.subset_preimage_recentredThinSlab`. -/
theorem thickenedPullbackSlabVolume (κ : ℝ) (hκ : 0 < κ) (Ctang Cpull Crad : ℝ≥0)
    (hCpull : 1 ≤ Cpull) (hCrad : 1 ≤ Crad) :
    ∃ Cctr : ℝ≥0, 1 ≤ Cctr ∧
      ∀ {a b ρ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} (ha : 0 < a) (hρa : ρ ≤ a)
        (W : Plank a b hab hb1)
        (f : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3))
        (g : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))),
        IsPlankNormalisation W f κ g →
        (∀ x ∈ W.carrier, ‖f x - f W.center‖ ≤ 1) →
        (∀ (θ' : ℝ≥0) (hθ'1 : θ' ≤ 1) (S' : Slab θ' hθ'1),
            volume (W.carrier ∩ f ⁻¹' S'.carrier)
              ≤ (Cpull : ENNReal) * (θ' : ENNReal) * volume W.carrier) →
        ∀ (θ : ℝ≥0) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (S : Slab θ hθ1), a / b ≤ θ →
          |inner ℝ (S.basis 0) (g 0)| ≤ (Ctang : ℝ) * (θ : ℝ) →
          volume (W.carrier ∩ Metric.cthickening ((Crad * ρ : ℝ≥0) : ℝ)
              (W.carrier ∩ f ⁻¹' S.carrier))
            ≤ (Cctr : ENNReal) * (Cpull : ENNReal) * (θ : ENNReal) * volume W.carrier := by
  set L : ℝ≥0 := 1 + Crad * Real.toNNReal κ * (Ctang + 2) with hL
  have hκ_real : (Real.toNNReal κ : ℝ) = κ := Real.coe_toNNReal κ hκ.le
  have hκ_nonneg : 0 ≤ κ := hκ.le
  have hL_one : (1 : ℝ≥0) ≤ L := by
    have hpos : (1 : ℝ) ≤ (L : ℝ) := by
      have hpos' : (0 : ℝ) ≤ (Crad : ℝ) * κ * ((Ctang : ℝ) + 2) := by
        positivity
      calc
        (1 : ℝ) ≤ 1 + (Crad : ℝ) * κ * ((Ctang : ℝ) + 2) := by nlinarith
        _ = 1 + (Crad : ℝ) * (Real.toNNReal κ : ℝ) * ((Ctang : ℝ) + 2) := by simp [hκ_real]
        _ = ((1 + Crad * Real.toNNReal κ * (Ctang + 2) : ℝ≥0) : ℝ) := by
          push_cast
          ring
        _ = (L : ℝ) := rfl
    exact_mod_cast hpos
  refine ⟨L, hL_one, ?_⟩
  intro a b ρ hab hb1 ha hρa W f g hnorm hWimg hS17 θ hθ0 hθ1 S hθab htang
  have hθ_nonneg : 0 ≤ (θ : ℝ) := θ.coe_nonneg
  have hρ_nonneg : 0 ≤ (ρ : ℝ) := ρ.coe_nonneg
  have ha_nonneg : 0 ≤ (a : ℝ) := a.coe_nonneg
  have ha_pos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hane : (a : ℝ) ≠ 0 := by linarith
  have hn_norm : ‖S.basis 0‖ = 1 := S.basis.norm_eq_one 0
  have hnorm_m : ‖pullbackNormal W κ g (S.basis 0)‖
      ≤ κ * ((Ctang : ℝ) + 2) * (θ : ℝ) / (a : ℝ) :=
    W.norm_pullbackNormal_le hκ ha hn_norm hθab htang
  set r : ℝ := ((Crad * ρ : ℝ≥0) : ℝ) with hr
  have hr_nonneg : 0 ≤ r := by positivity
  have hr_bound : r ≤ (Crad : ℝ) * (a : ℝ) := by
    dsimp [r]
    push_cast
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hρa) (by positivity : 0 ≤ (Crad : ℝ))
  by_cases hcase : (L : ℝ≥0) * θ ≤ 1
  · -- Main case: L * θ ≤ 1, so we can form a dilated slab
    have hθ'1 : L * θ ≤ 1 := hcase
    set θ' : ℝ≥0 := L * θ with hθ'
    set S' : Slab (L * θ) hθ'1 := recentredThinSlab S (f W.center) (L * θ) hθ'1 with hS'
    have hthin : (θ : ℝ) + r * ‖pullbackNormal W κ g (S.basis 0)‖ ≤ ((L * θ : ℝ≥0) : ℝ) := by
      calc
        (θ : ℝ) + r * ‖pullbackNormal W κ g (S.basis 0)‖
            ≤ (θ : ℝ) + ((Crad : ℝ) * (a : ℝ)) * (κ * ((Ctang : ℝ) + 2) * (θ : ℝ) / (a : ℝ)) := by
          have h_mul_bound : r * ‖pullbackNormal W κ g (S.basis 0)‖
              ≤ ((Crad : ℝ) * (a : ℝ)) * (κ * ((Ctang : ℝ) + 2) * (θ : ℝ) / (a : ℝ)) := by
            have h_mul_r : r * ‖pullbackNormal W κ g (S.basis 0)‖
                ≤ (Crad : ℝ) * (a : ℝ) * ‖pullbackNormal W κ g (S.basis 0)‖ :=
              mul_le_mul_of_nonneg_right hr_bound (norm_nonneg _)
            calc
              r * ‖pullbackNormal W κ g (S.basis 0)‖
                  ≤ (Crad : ℝ) * (a : ℝ) * ‖pullbackNormal W κ g (S.basis 0)‖ := h_mul_r
              _ ≤ (Crad : ℝ) * (a : ℝ) * (κ * ((Ctang : ℝ) + 2) * (θ : ℝ) / (a : ℝ)) :=
                mul_le_mul_of_nonneg_left hnorm_m (by positivity : 0 ≤ (Crad : ℝ) * (a : ℝ))
              _ = ((Crad : ℝ) * (a : ℝ)) * (κ * ((Ctang : ℝ) + 2) * (θ : ℝ) / (a : ℝ)) := by ring
          nlinarith
        _ = (θ : ℝ) + (Crad : ℝ) * κ * ((Ctang : ℝ) + 2) * (θ : ℝ) := by
          field_simp [hane]
        _ = (1 + (Crad : ℝ) * κ * ((Ctang : ℝ) + 2)) * (θ : ℝ) := by ring
        _ = ((L : ℝ≥0) : ℝ) * (θ : ℝ) := by
          dsimp [L]
          push_cast
          simp [hκ.le, mul_comm, mul_left_comm, mul_assoc]
        _ = ((L * θ : ℝ≥0) : ℝ) := by push_cast; ring
    have hsub : W.carrier ∩ Metric.cthickening r (W.carrier ∩ f ⁻¹' S.carrier)
        ⊆ W.carrier ∩ f ⁻¹' S'.carrier := by
      refine Set.subset_inter Set.inter_subset_left ?_
      have := W.subset_preimage_recentredThinSlab hnorm hWimg S hθ'1 hr_nonneg hthin
      -- The lemma returns subset of f⁻¹'(recentredThinSlab...).carrier
      simpa [hS'] using this
    have hvol : volume (W.carrier ∩ f ⁻¹' S'.carrier)
        ≤ (Cpull : ENNReal) * ((L * θ : ℝ≥0) : ENNReal) * volume W.carrier :=
      hS17 (L * θ) hθ'1 S'
    calc
      volume (W.carrier ∩ Metric.cthickening r (W.carrier ∩ f ⁻¹' S.carrier))
          ≤ volume (W.carrier ∩ f ⁻¹' S'.carrier) := measure_mono hsub
      _ ≤ (Cpull : ENNReal) * ((L * θ : ℝ≥0) : ENNReal) * volume W.carrier := hvol
      _ = (Cpull : ENNReal) * ((L : ENNReal) * (θ : ENNReal)) * volume W.carrier := by
        simp [ENNReal.coe_mul]
      _ = (L : ENNReal) * (Cpull : ENNReal) * (θ : ENNReal) * volume W.carrier := by ring
  · -- Degenerate case: L * θ > 1, use trivial bound
    have hLθ_gt_one : (1 : ℝ≥0) < (L : ℝ≥0) * θ := by
      refine lt_of_not_ge hcase
    have hLθ_one : (1 : ℝ≥0) ≤ (L : ℝ≥0) * θ := le_of_lt hLθ_gt_one
    have hLCθ_one : (1 : ℝ≥0) ≤ L * Cpull * θ := by
      calc
        (1 : ℝ≥0) ≤ L * θ := hLθ_one
        _ = (L * θ) * 1 := by ring
        _ ≤ (L * θ) * Cpull := mul_le_mul_of_nonneg_left hCpull (by positivity : 0 ≤ L * θ)
        _ = L * Cpull * θ := by ring
    have h_one_enn : (1 : ENNReal) ≤ (L : ENNReal) * (Cpull : ENNReal) * (θ : ENNReal) := by
      calc
        (1 : ENNReal) = ((1 : ℝ≥0) : ENNReal) := by simp
        _ ≤ ((L * Cpull * θ : ℝ≥0) : ENNReal) := ENNReal.coe_le_coe.mpr hLCθ_one
        _ = (L : ENNReal) * (Cpull : ENNReal) * (θ : ENNReal) := by simp [ENNReal.coe_mul]
    have hvol_mono : volume (W.carrier ∩ Metric.cthickening ((Crad * ρ : ℝ≥0) : ℝ)
        (W.carrier ∩ f ⁻¹' S.carrier)) ≤ volume W.carrier :=
      measure_mono Set.inter_subset_left
    calc
      volume (W.carrier ∩ Metric.cthickening ((Crad * ρ : ℝ≥0) : ℝ)
          (W.carrier ∩ f ⁻¹' S.carrier))
          ≤ volume W.carrier := hvol_mono
      _ = (1 : ENNReal) * volume W.carrier := by simp
      _ ≤ ((L : ENNReal) * (Cpull : ENNReal) * (θ : ENNReal)) * volume W.carrier := by
        gcongr
      _ = (L : ENNReal) * (Cpull : ENNReal) * (θ : ENNReal) * volume W.carrier := by ring

/-- **The thickened pullback, packaged as a convex body.** `W ∩ N_r(W ∩ f⁻¹(S))` is convex
(intersection of the convex plank with the closed thickening of a convex set), compact (a closed
subset of the compact `W`), and nonempty as soon as the raw pullback is. The Frostman counting
lemmas need it in this bundled form, so the equality of carriers is exported as well. -/
theorem exists_cthickenedPullbackBody {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (W : Plank a b hab hb1)
    (f : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3))
    {θ : ℝ≥0} {hθ1 : θ ≤ 1} (S : Slab θ hθ1) (r : ℝ≥0)
    (hne : (W.carrier ∩ f ⁻¹' S.carrier).Nonempty) :
    ∃ K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)),
      (K : Set (EuclideanSpace ℝ (Fin 3)))
        = W.carrier ∩ Metric.cthickening (r : ℝ) (W.carrier ∩ f ⁻¹' S.carrier) := by
  refine ⟨⟨W.carrier ∩ Metric.cthickening (r : ℝ) (W.carrier ∩ f ⁻¹' S.carrier), ?_, ?_, ?_⟩, rfl⟩
  · -- convexity: convex plank ∩ closed thickening of a convex pullback
    have hWconvex : Convexity.IsConvexSet ℝ (W.carrier : Set _) := W.convex'
    have hSconv : Convexity.IsConvexSet ℝ (S.carrier : Set _) := S.convex'
    have hpre : Convexity.IsConvexSet ℝ (f ⁻¹' S.carrier) :=
      Convexity.IsConvexSet.affineMap_preimage f hSconv
    have hK : Convexity.IsConvexSet ℝ (W.carrier ∩ f ⁻¹' S.carrier) := hWconvex.inter hpre
    have hKc : Convex ℝ (W.carrier ∩ f ⁻¹' S.carrier) := hK.convex
    have hct : Convexity.IsConvexSet ℝ
        (Metric.cthickening (r : ℝ) (W.carrier ∩ f ⁻¹' S.carrier)) :=
      Convex.isConvexSet (Convex.cthickening hKc (r : ℝ))
    exact hWconvex.inter hct
  · -- compactness: closed subset of the compact plank
    have hWcomp : IsCompact (W.carrier : Set (EuclideanSpace ℝ (Fin 3))) := W.isCompact'
    have hclosed : IsClosed (Metric.cthickening (r : ℝ) (W.carrier ∩ f ⁻¹' S.carrier)) :=
      Metric.isClosed_cthickening
    exact hWcomp.inter_right hclosed
  · -- nonempty: the raw pullback sits inside both factors
    have hct : W.carrier ∩ f ⁻¹' S.carrier
        ⊆ W.carrier ∩ Metric.cthickening (r : ℝ) (W.carrier ∩ f ⁻¹' S.carrier) := by
      exact Set.subset_inter Set.inter_subset_left
        (Metric.self_subset_cthickening (W.carrier ∩ f ⁻¹' S.carrier))
    exact hne.mono hct

/-- **Coarse Frostman count times fibre comparability.** If the coarse `ρ`-tubes `(R k)_{k ∈ rW}` are
`C₀`-Frostman in the body `W`, every fine index of `qW` is assigned to one of them, all coarse
fibres have cardinality within a factor `Cfib` of a common `m`, and `Kplus ≤ W` has relative volume
at most `Cvol · θ`, then any set `qS ⊆ qW` of fine indices whose coarse parents all lie in `Kplus`
satisfies `|qS| ≤ coarseTubeVolumeRatio · Cvol · C₀ · Cfib² · θ · |qW|`.

The fibre hypotheses are deliberately UNGUARDED (they range over all of `rW`, not only over the
coarse indices with nonempty fibre): the normalisation `m · |rW| ≤ Cfib · |qW|` is what converts the
coarse count into a fine count, and it fails if `rW` may contain empty-fibre indices. -/
theorem card_le_of_coarseFibreFrostman {ι κ : Type*} {qW qS : Finset ι} {rW : Finset κ}
    {ρ : ℝ≥0} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    {R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))} {assign : ι → κ}
    {W Kplus : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    {C₀ Cfib m Cvol θ : ℝ≥0} (hCfib : 1 ≤ Cfib) (hrW : rW.Nonempty)
    (hproj : ∀ i ∈ qW, assign i ∈ rW)
    (hfrost : ConvexSpaceBody.IsFrostmanIn rW (fun k => (R k).toConvexSpaceBody) W (C₀ : ENNReal))
    (hRW : ∀ k ∈ rW, (R k).toConvexSpaceBody ≤ W) (hKW : Kplus ≤ W)
    (hW0 : volume W.carrier ≠ 0) (hWtop : volume W.carrier ≠ ⊤)
    (hvolK : volume Kplus.carrier ≤ (Cvol : ENNReal) * (θ : ENNReal) * volume W.carrier)
    (hlb : ∀ k ∈ rW, m / Cfib ≤ (({i ∈ qW | assign i = k}).card : ℝ≥0))
    (hub : ∀ k ∈ rW, (({i ∈ qW | assign i = k}).card : ℝ≥0) ≤ Cfib * m)
    (hqS : qS ⊆ qW) (hmem : ∀ i ∈ qS, (R (assign i)).toConvexSpaceBody ≤ Kplus) :
    (qS.card : ℝ≥0)
      ≤ Kakeya.coarseTubeVolumeRatio * Cvol * C₀ * Cfib ^ 2 * θ * (qW.card : ℝ≥0) := by
  classical
  set sel : Finset κ := {k ∈ rW | (R k).toConvexSpaceBody ≤ Kplus}
  have hsel : sel ⊆ rW := by
    rw [show sel = rW.filter (fun k => (R k).toConvexSpaceBody ≤ Kplus) by rfl]
    exact Finset.filter_subset _ _
  have hvolK' : volume Kplus.carrier ≤ (((Cvol * θ : ℝ≥0)) : ENNReal) * volume W.carrier := by
    simpa [ENNReal.coe_mul, mul_assoc] using hvolK
  have hget := Kakeya.card_coarse_le_of_frostmanIn hρ0 hρ1 (r := rW) (W := W) (K := Kplus)
    (CF := C₀) (θ := Cvol * θ) hfrost hRW hKW hW0 hWtop hvolK'
  have hselcard : (sel.card : ℝ≥0) ≤
      (Kakeya.coarseTubeVolumeRatio * C₀ * (Cvol * θ)) * (rW.card : ℝ≥0) := by
    simpa [sel] using hget
  have hlb' : ∀ k ∈ rW, Cfib⁻¹ * m ≤ (({i ∈ qW | assign i = k}).card : ℝ≥0) := by
    intro k hk
    calc
      Cfib⁻¹ * m = m * Cfib⁻¹ := by ring
      _ = m / Cfib := by rw [div_eq_mul_inv]
      _ ≤ (({i ∈ qW | assign i = k}).card : ℝ≥0) := hlb k hk
  have hmem' : ∀ i ∈ qS, assign i ∈ sel := by
    intro i hi
    rw [Finset.mem_filter]
    exact ⟨hproj i (hqS hi), hmem i hi⟩
  have hfinal := Kakeya.card_le_of_comparable_fibres_of_selected_le (q := qW) (r := rW)
    (proj := assign) (Cθ := Kakeya.coarseTubeVolumeRatio * C₀ * (Cvol * θ))
    hCfib hrW hproj hlb' hub hsel hselcard hqS hmem'
  calc
    (qS.card : ℝ≥0)
        ≤ Cfib ^ 2 * (Kakeya.coarseTubeVolumeRatio * C₀ * (Cvol * θ)) * (qW.card : ℝ≥0) := hfinal
    _ = Kakeya.coarseTubeVolumeRatio * Cvol * C₀ * Cfib ^ 2 * θ * (qW.card : ℝ≥0) := by
      ring

/-- **Coarse/fine fibre counting** (`lem:geometryCoarseFineFibreCount`, S6G20).

Let the coarse `ρ`-tubes be `C₀`-Frostman in `W` and suppose the positive fine-over-coarse fibre
sizes lie in `[m/C_fib, C_fib·m]`. Then the fine indices whose normalised planks belong to `S`
satisfy `|(qW)_S| ≤ C_count · C₀ · C_fib ^ 2 · θ · |qW|`.

Proof shape: let `rW_S` be the coarse tubes containing at least one fine index of `(qW)_S`; by S6G19
they all lie in `K⁺_{W,S}` (hypothesis `hcontain`), so the coarse Frostman inequality together with
the volume bound of S6G19 (hypothesis `hvolK`) gives `|rW_S| ≤ C_count · C₀ · θ · |rW|`. Every
selected coarse tube carries at most `C_fib · m` fine indices, and every coarse tube of `rW` carries
at least `m / C_fib`, whence `m · |rW| ≤ C_fib · |qW|`; substituting gives the claim with the two
fibre-comparison factors displayed. This bound is exactly the conclusion of
`Plank.katzTaoTransverseFactorBound`.

The fibre hypothesis is deliberately unguarded — the two-sided comparability ranges over all of `rW`,
not only over the coarse indices with nonempty fibre — because the fine count needs
`m · |rW| ≤ C_fib · |qW|`, which fails if `rW` may contain empty-fibre coarse indices (padding `rW`
with far-away empty-fibre coarse tubes lowers the admissible Frostman constant `C₀` without changing
either side of the conclusion, and for a small `a×1×1` plank with `θ = a` this breaks the bound by an
arbitrary factor). `Kplus` is a `ConvexSpaceBody`, not a bare `Set`, because
`ConvexSpaceBody.IsFrostmanIn` only constrains convex test bodies, so a bare `Set` gives no purchase;
the call site's `Kplus` is convex, compact and nonempty and is bundled by
`Plank.exists_cthickenedPullbackBody`.

Proved by `Plank.card_le_of_coarseFibreFrostman`. -/
theorem coarseFineSlabFibreCardinality :
    ∃ Ccount : ℝ≥0, 1 ≤ Ccount ∧
      ∀ {a b δ ρ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} (ha : 0 < a) (hδ0 : 0 < δ) (hρa : ρ ≤ a)
        (W : Plank a b hab hb1)
        (f : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)) (J : ℝ≥0),
        0 < J →
        (∀ E : Set (EuclideanSpace ℝ (Fin 3)), volume (f '' E) = (J : ENNReal) * volume E) →
        f '' W.carrier ⊆ Metric.closedBall 0 1 →
        ∀ {ι κ : Type*} (qW : Finset ι) (rW : Finset κ)
          (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
          (R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))) (assign : ι → κ)
          (C₀ Cfib m : ℝ≥0),
          1 ≤ C₀ → 1 ≤ Cfib → 0 < m →
          (∀ i ∈ qW, (T i).carrier ⊆ W.carrier) →
          (∀ i ∈ qW, assign i ∈ rW ∧
            (T i).toConvexSpaceBody ≤ (R (assign i)).toConvexSpaceBody) →
          ConvexSpaceBody.IsFrostmanIn rW (fun k => (R k).toConvexSpaceBody)
            W.toConvexSpaceBody C₀ →
          (∀ k ∈ rW,
              m / Cfib ≤ (({i ∈ qW | assign i = k}).card : ℝ≥0) ∧
              (({i ∈ qW | assign i = k}).card : ℝ≥0) ≤ Cfib * m) →
          (∀ k ∈ rW, (R k).carrier ⊆ W.carrier) →
          ∀ {a' b' : ℝ≥0} {ha'b' : a' ≤ b'} {hb'1 : b' ≤ 1}
            (Pj : ι → Plank a' b' ha'b' hb'1)
            (Kplus : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))),
            Kplus ≤ W.toConvexSpaceBody →
            ∀ (Cvol : ℝ≥0), 1 ≤ Cvol →
            ∀ (θ : ℝ≥0) (hθ1 : θ ≤ 1) (S : Slab θ hθ1), a / b ≤ θ →
              volume Kplus.carrier ≤ (Cvol : ENNReal) * (θ : ENNReal) * volume W.carrier →
              (∀ i ∈ Plank.inSlabFamily qW Pj S, (R (assign i)).toConvexSpaceBody ≤ Kplus) →
              ((Plank.inSlabFamily qW Pj S).card : ℝ≥0)
                ≤ Ccount * Cvol * C₀ * Cfib ^ 2 * θ * (qW.card : ℝ≥0) := by
  classical
  refine ⟨Kakeya.coarseTubeVolumeRatio, Kakeya.one_le_coarseTubeVolumeRatio, ?_⟩
  intro a b δ ρ hab hb1 ha hδ0 hρa W f J hJ himg hsub
  intro ι κ qW rW T R assign C₀ Cfib m hC₀ hCfib hm hTsub hAssign hFrost hFibre hCar
  rintro _ _ _ _ Pj Kplus hKW Cvol hCvol1 θ hθ1 S hθge hvol hQmem
  let qS : Finset ι := Plank.inSlabFamily qW Pj S
  rcases Finset.eq_empty_or_nonempty qW with hqW | hqW
  · -- `qW = ∅`: LHS is 0.
    simp [hqW]
  · obtain ⟨i0, hi0⟩ := hqW
    have hrho1 : ρ ≤ 1 := hρa.trans (hab.trans hb1)
    have hrho0 : 0 < ρ := by
      by_contra hnlt
      have hle0 : ρ ≤ 0 := le_of_not_gt hnlt
      have hrho : ρ = 0 := le_antisymm hle0 zero_le
      have hcr : assign i0 ∈ rW ∧ (T i0).toConvexSpaceBody ≤ (R (assign i0)).toConvexSpaceBody :=
        hAssign i0 hi0
      have hsetT : (T i0).carrier ⊆ (R (assign i0)).carrier :=
        (SetLike.coe_subset_coe (S := (T i0).toConvexSpaceBody)
          (T := (R (assign i0)).toConvexSpaceBody)).mp hcr.2
      have hvolle : volume (T i0).carrier ≤ volume (R (assign i0)).carrier := measure_mono hsetT
      have hTvol : 0 < volume (T i0).carrier := by
        have hcpos : ((Tube.le_volume.c 3 : ℝ≥0) : ENNReal) ≠ 0 :=
          ne_of_gt (ENNReal.coe_pos.mpr (Tube.le_volume.c_pos 3))
        have hδE : (0 : ENNReal) < (δ : ENNReal) := ENNReal.coe_pos.mpr hδ0
        have hδpow : (0 : ENNReal) < (δ : ENNReal) ^ 2 := ENNReal.pow_pos hδE 2
        have hcls2 : (0 : ENNReal) < ((Tube.le_volume.c 3 : ℝ≥0) : ENNReal) * (δ : ENNReal) ^ 2 :=
          ENNReal.mul_pos hcpos (ne_of_gt hδpow)
        have hcls : (0 : ENNReal) <
            ((Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) : ℝ≥0) : ENNReal) *
              (δ : ENNReal) ^ (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - 1) := by
          rw [finrank_euclideanSpace_fin]
          simpa [show (3 : ℕ) - 1 = 2 by norm_num] using hcls2
        exact lt_of_lt_of_le hcls (Tube.le_volume (T i0).toTube)
      have hvolR0 : 0 < volume (R (assign i0)).carrier :=
        lt_of_lt_of_le (by simpa using hTvol) hvolle
      have hvu : volume (R (assign i0)).carrier ≤ (0 : ENNReal) := by
        have hv := Tube.volume_le hrho1 (R (assign i0))
        simpa [finrank_euclideanSpace_fin, hrho, show (3 : ℕ) - 1 = 2 by norm_num] using hv
      exact (lt_irrefl (0 : ENNReal)) (lt_of_lt_of_le hvolR0 hvu)
    -- assemble the hypotheses of `card_le_of_coarseFibreFrostman`
    have hw0 : volume (W.toConvexSpaceBody).carrier ≠ 0 := by
      have hp : 0 < volume W.carrier := Prism3D.volume_pos_of_pos W ha
      exact ne_of_gt (by simpa using hp)
    have hwtop : volume (W.toConvexSpaceBody).carrier ≠ (⊤ : ENNReal) := by
      simpa using (W.isCompact'.measure_ne_top : volume W.carrier ≠ ⊤)
    have hqSsub : qS ⊆ qW := by
      simpa [qS] using (Plank.inSlabFamily_subset (s := qW) (V := Pj) (S := S))
    have hlb : ∀ k ∈ rW, m / Cfib ≤ (({i ∈ qW | assign i = k}).card : ℝ≥0) :=
      fun k hk => (hFibre k hk).1
    have hub : ∀ k ∈ rW, (({i ∈ qW | assign i = k}).card : ℝ≥0) ≤ Cfib * m :=
      fun k hk => (hFibre k hk).2
    have hRW : ∀ k ∈ rW, (R k).toConvexSpaceBody ≤ W.toConvexSpaceBody := fun k hk =>
      (SetLike.coe_subset_coe (S := (R k).toConvexSpaceBody)
        (T := W.toConvexSpaceBody)).mp (hCar k hk)
    have hfinal := Plank.card_le_of_coarseFibreFrostman (W := W.toConvexSpaceBody) (Kplus := Kplus)
      (qW := qW) (qS := qS) (rW := rW) (ρ := ρ) (R := R) (assign := assign)
      (C₀ := C₀) (Cfib := Cfib) (m := m) (Cvol := Cvol) (θ := θ)
      (hCfib := hCfib) (hrW := ⟨assign i0, (hAssign i0 hi0).1⟩)
      hrho0 hrho1
      (hproj := fun i hi => (hAssign i hi).1)
      hFrost hRW hKW hw0 hwtop hvol hlb hub
      (hqS := hqSsub) (hmem := by simpa [qS] using hQmem)
    simpa [qS] using hfinal

/-- **Normalise tubes inside a factor plank** (`lem:geometryTubeFamilyInsidePlankNormalisation`).

Under the affine normalisation `f` of the `a × b × 1` plank `W`, each fine `δ`-tube `T i ⊆ W`
acquires an outer plank model `Pj i` of dimensions `(δ/b) × (δ/a) × 1` inside the unit ball. The
inner scales are therefore *determined*, `a' = δ/b` and `b' = δ/a`, and the eccentricity is
preserved: `a'/b' = (δ/b)/(δ/a) = a/b`. The inequalities `a' ≤ b'`, `b' ≤ 1`, `δ ≤ a'` and
`a' ≤ a₀` come from `a ≤ b`, `δ ≤ a`, `b ≤ 1` and `δ ≤ a₀ * b` respectively.

The essential conjunct for the consumers is the **slab-membership link**: if the normalised plank
`Pj i` lies in a normalised slab `S` (i.e. `i ∈ Plank.inSlabFamily qW Pj S`), then the original tube
lies in the pullback, `T i ⊆ f⁻¹(S)`. This is what lets the pullback lemmas S6G17–S6G20 be applied
to the original coarse/fine structure.

Compared with the blueprint lemma this states the *total* pointwise normalisation and omits the
dyadic-plus-conflict-graph extraction of an essentially-distinct fixed-loss subfamily: the Lean form
of GWZ Lemma 6.1 carries no essential-distinctness hypothesis, so its consumers here do not need it.
The maximal-density transfer of `lem:geometryAffineShadingTransfer` is retained.

It also emits the **tangency bound** that S6G18 consumes: the normalised planks have their thin
direction along `g 1` (the coordinate scaled by `κ/b`, giving the smallest extent `δκ/b`), so a slab
`S` containing one of them at angle `≤ θ` has its own thin direction `S.basis 0` within `≈ θ` of
`g 1`, hence nearly orthogonal to `g 0`: `|⟪S.basis 0, g 0⟫| ≤ C_tang · θ`.

**Proved**, with `C_tang = 1`, from the explicit construction in
`Kakeya.DimensionThree.Plank.TubePlankNormalisation`: `Plank.exists_normalisedTubePlank` builds each
tube's model plank (thin normal orthogonal to `g 0`, long axis along the image of the tube axis),
`Plank.abs_inner_slabNormal_le_of_angle` gives the tangency bound and
`Plank.maxDensity_le_of_image_subset` the density transfer. The window hypothesis is what forces
`3κ² ≤ 1` (`Plank.three_mul_sq_le_one_of_image_subset_closedBall`), and that is what makes the
*exact* inner scales `δ/b`, `δ/a` admissible. -/
theorem normaliseTubesInsidePlank (κ : ℝ) (hκ : 0 < κ) :
    ∃ Cnorm Ctang : ℝ≥0, 1 ≤ Cnorm ∧ 1 ≤ Ctang ∧
      ∀ {a b δ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} (ha : 0 < a) (hδ0 : 0 < δ) (hδa : δ ≤ a)
        (a₀ : ℝ≥0) (ha₀ : 0 < a₀) (hsmall : δ ≤ a₀ * b)
        (W : Plank a b hab hb1)
        (f : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)) (J : ℝ≥0)
        (g : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))),
        0 < J →
        IsPlankNormalisation W f κ g →
        (∀ E : Set (EuclideanSpace ℝ (Fin 3)), volume (f '' E) = (J : ENNReal) * volume E) →
        f '' W.carrier ⊆ Metric.closedBall 0 1 →
        ∀ {ι : Type*} (qW : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
          (∀ i ∈ qW, (T i).carrier ⊆ W.carrier) →
          ∃ (a' b' : ℝ≥0) (ha'b' : a' ≤ b') (hb'1 : b' ≤ 1)
            (Pj : ι → Plank a' b' ha'b' hb'1),
            a' = δ / b ∧ b' = δ / a ∧
            0 < a' ∧ δ ≤ a' ∧ a' ≤ a₀ ∧
            (a' / b' = a / b) ∧
            ((a' : ENNReal) / (b' : ENNReal) = (a : ENNReal) / (b : ENNReal)) ∧
            (∀ i ∈ qW, (Pj i).carrier ⊆ Metric.closedBall 0 (plankWindowRadius : ℝ)) ∧
            (∀ (θ : ℝ≥0) (hθ1 : θ ≤ 1) (S : Slab θ hθ1) (i : ι),
              i ∈ Plank.inSlabFamily qW Pj S → (T i).carrier ⊆ f ⁻¹' S.carrier) ∧
            (∀ (θ : ℝ≥0) (hθ1 : θ ≤ 1) (S : Slab θ hθ1),
              (Plank.inSlabFamily qW Pj S).Nonempty →
              |inner ℝ (S.basis 0) (g 0)| ≤ (Ctang : ℝ) * (θ : ℝ)) ∧
            Kakeya.maxDensity qW (fun i => (Pj i).toConvexSpaceBody)
              ≤ (Cnorm : ENNReal) * Kakeya.maxDensity qW
                  (fun i => (T i).toConvexSpaceBody) := by
  classical
  let CnormNN : ℝ≥0 := max 1 (8 / (Real.toNNReal κ ^ 3 * Tube.le_volume.c 3))
  refine ⟨CnormNN, 1, le_max_left _ _, le_rfl, ?_⟩
  intro a b δ hab hb1 ha hδ0 hδa a₀ ha₀ hsmall W f J g hJ hnorm hvolf himg ι qW T hcarrier
  -- Scale facts --------------------------------------------------------------
  have hb0 : 0 < b := lt_of_lt_of_le ha hab
  have hb0R : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb0
  have ha0R : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hκ3 : 3 * κ ^ 2 ≤ 1 := three_mul_sq_le_one_of_image_subset_closedBall ha W hκ hnorm himg
  have ha'b' : δ / b ≤ δ / a := by
    rw [← NNReal.coe_le_coe]
    rw [NNReal.coe_div, NNReal.coe_div]
    exact div_le_div_of_nonneg_left (NNReal.coe_nonneg δ) ha0R (by exact_mod_cast hab)
  have hb'1 : δ / a ≤ 1 := by
    rw [← NNReal.coe_le_coe]
    rw [NNReal.coe_div]
    have hδaR : (δ : ℝ) ≤ (a : ℝ) := by exact_mod_cast hδa
    rw [div_le_iff₀ ha0R]
    simpa using hδaR
  have hδR0pos : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
  have hδpos_a' : 0 < δ / b := by
    rw [← NNReal.coe_pos]
    rw [NNReal.coe_div]
    exact div_pos hδR0pos hb0R
  have hδ_le_a' : δ ≤ δ / b := by
    rw [← NNReal.coe_le_coe]
    rw [NNReal.coe_div]
    have hb1R : (b : ℝ) ≤ 1 := by exact_mod_cast hb1
    have hδR0' : (0 : ℝ) ≤ (δ : ℝ) := le_of_lt hδR0pos
    rw [le_div_iff₀ hb0R]
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_right hb1R hδR0'
  have ha'_le_a0 : δ / b ≤ a₀ := by
    rw [← NNReal.coe_le_coe]
    rw [NNReal.coe_div]
    have hδsR : (δ : ℝ) ≤ (a₀ : ℝ) * (b : ℝ) := by exact_mod_cast hsmall
    exact (div_le_iff₀ hb0R).mpr hδsR
  have hratio_nn : (δ / b) / (δ / a) = a / b := by
    apply NNReal.coe_injective
    simp [NNReal.coe_div]
    field_simp [show (δ : ℝ) ≠ 0 from (by exact_mod_cast hδ0.ne'),
      show (a : ℝ) ≠ 0 from ne_of_gt ha0R,
      show (b : ℝ) ≠ 0 from ne_of_gt hb0R]
  have hδa_pos : 0 < δ / a := by
    rw [← NNReal.coe_pos]
    rw [NNReal.coe_div]
    exact div_pos hδR0pos ha0R
  have hδa_ne : δ / a ≠ 0 := ne_of_gt hδa_pos
  have hb_ne : (b : NNReal) ≠ 0 := ne_of_gt hb0
  have hratio_enn : ((δ / b : NNReal) : ENNReal) / ((δ / a : NNReal) : ENNReal)
      = (a : ENNReal) / (b : ENNReal) := by
    rw [← ENNReal.coe_div hδa_ne]
    rw [← ENNReal.coe_div hb_ne]
    exact congrArg (fun z : NNReal => (z : ENNReal)) hratio_nn
  -- The family of normalised planks --------------------------------------------
  have key : ∀ i : ι, ∃ P : Plank (δ / b) (δ / a) ha'b' hb'1,
      i ∈ qW → (inner ℝ (P.basis 0) (g 0) = 0 ∧
                f '' ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆ (P.carrier : Set _) ∧
                (P.carrier : Set _) ⊆ Metric.closedBall 0 (plankWindowRadius : ℝ)) := by
    intro i
    by_cases hi : i ∈ qW
    · obtain ⟨P, hortho, _, hcont, hwin⟩ := exists_normalisedTubePlank ha hδ0 hδa W hκ hκ3 hnorm
        himg ha'b' hb'1 (T i).toTube (hcarrier i hi)
      exact ⟨P, fun _ => ⟨hortho, hcont, hwin⟩⟩
    · exact ⟨
        { toPrismNDim := PrismNDim.mk' (0 : EuclideanSpace ℝ (Fin 3)) g
            ![δ / b, δ / a, (1 : NNReal)]
          thicknesses_eq := rfl },
        fun h => absurd h hi⟩
  choose Pj hPj using key
  -- Window and slab link --------------------------------------------------------
  have hwin : ∀ i ∈ qW, (Pj i).carrier ⊆ Metric.closedBall 0 (plankWindowRadius : ℝ) := by
    intro i hi
    exact (hPj i hi).2.2
  have hlink : ∀ (θ : NNReal) (hθ1 : θ ≤ 1) (S : Slab θ hθ1) (i : ι),
      i ∈ Plank.inSlabFamily qW Pj S → (T i).carrier ⊆ f ⁻¹' S.carrier := by
    intro θ hθ1 S i hi x hx
    have hiq : i ∈ qW := (mem_inSlabFamily.mp hi).1
    have hPc : (Pj i).carrier ⊆ S.carrier := (mem_inSlabFamily.mp hi).2.1
    rw [Set.mem_preimage]
    exact hPc ((hPj i hiq).2.1 ⟨x, hx, rfl⟩)
  -- tangency -------------------------------------------------------------------
  have htangent : ∀ (θ : NNReal) (hθ1 : θ ≤ 1) (S : Slab θ hθ1),
      (Plank.inSlabFamily qW Pj S).Nonempty →
      |inner ℝ (S.basis 0) (g 0)| ≤ ((1 : NNReal) : ℝ) * (θ : ℝ) := by
    intro θ hθ1 S hne
    rcases hne with ⟨i, hi⟩
    have hiq : i ∈ qW := (mem_inSlabFamily.mp hi).1
    have hang : Prism3D.angle (Pj i) S ≤ (θ : ℝ) := (mem_inSlabFamily.mp hi).2.2
    have hPn : inner ℝ ((Pj i).basis 0) (g 0) = 0 := (hPj i hiq).1
    have hbnd : |inner ℝ (S.basis 0) (g 0)| ≤ (θ : ℝ) :=
      abs_inner_slabNormal_le_of_angle (Pj i) (g.norm_eq_one 0) hPn S hang
    simpa using hbnd
  -- density --------------------------------------------------------------------
  have hmd_le : Kakeya.maxDensity qW (fun i => (Pj i).toConvexSpaceBody)
      ≤ ((8 / (Real.toNNReal κ ^ 3 * Tube.le_volume.c 3) : NNReal) : ENNReal)
        * Kakeya.maxDensity qW (fun i => (T i).toConvexSpaceBody) :=
    maxDensity_le_of_image_subset qW ha hδ0 W hκ hnorm hvolf T Pj
      (fun i hi => (hPj i hi).2.1)
  have hC_le : ((8 / (Real.toNNReal κ ^ 3 * Tube.le_volume.c 3) : NNReal) : ENNReal)
      ≤ (CnormNN : ENNReal) := by
    dsimp [CnormNN]
    exact ENNReal.coe_le_coe.mpr (le_max_right (1 : NNReal) _)
  have hmaxd : Kakeya.maxDensity qW (fun i => (Pj i).toConvexSpaceBody)
      ≤ (CnormNN : ENNReal) * Kakeya.maxDensity qW (fun i => (T i).toConvexSpaceBody) := by
    calc
      Kakeya.maxDensity qW (fun i => (Pj i).toConvexSpaceBody)
          ≤ ((8 / (Real.toNNReal κ ^ 3 * Tube.le_volume.c 3) : NNReal) : ENNReal)
            * Kakeya.maxDensity qW (fun i => (T i).toConvexSpaceBody) := hmd_le
      _ ≤ (CnormNN : ENNReal) * Kakeya.maxDensity qW (fun i => (T i).toConvexSpaceBody) := by
        gcongr
  -- assemble --------------------------------------------------------------------
  refine ⟨δ / b, δ / a, ha'b', hb'1, Pj, rfl, rfl, hδpos_a', hδ_le_a', ha'_le_a0,
    hratio_nn, hratio_enn, hwin, hlink, htangent, hmaxd⟩

/-- **Transversality and slab counting for a plank factorisation** (`lem:katzTaoTransverseFactorBound`,
the split corollary behind GWZ Proposition 6.6(B)).

Let `W` be an `a × b × 1` plank containing a finite family of coarse `ρ`-tubes `(R k)_{k ∈ rW}`
which is `C₀`-Frostman in `W`, and let `(T i)_{i ∈ qW}` be the fine `δ`-tubes lying over them
(`assign`), with all nonempty coarse fibres of comparable size (two-sided, factor `Cfib`). Assume
the coarse scale is below the plank width, `ρ ≤ a`. Writing `Φ_W` for the affine normalisation of
`W` onto the unit ball, each fine tube `T i ⊆ W` becomes a plank of dimensions
`≈ δ/b × δ/a × 1`, of eccentricity `(δ/b)/(δ/a) = a/b`; this lemma produces that normalised inner
family together with the slab-counting bound

`|{i ∈ qW : Φ_W(T i) ⊆ S}| ≤ Ctr · C₀ · Cfib ^ 2 · θ · |qW|`

for every `θ` with `a'/b' = a/b ≤ θ ≤ 1` and every `θ × 1 × 1` slab `S` in normalised coordinates.

The pullback geometry is internal to this statement and is deliberately *not* exposed: the
transversality calculation (the pullback of `S` along `Φ_W` has least width `≳ θ·b ≥ a ≳ ρ`, so
that thickening it by `Cctr·ρ` to capture the supporting coarse tubes does not inflate its volume)
is the only transversality input required by 6.6(B). Consumers receive only the count. Constants are
absolute and quantified before the configuration.

The inner-scale threshold `a₀` is an input, and the configuration hypothesis `δ ≤ a₀ * b` (which is
`δ/b ≤ a₀`, i.e. the normalised small scale is below the threshold) yields `a' ≤ a₀` in the
conclusion. `Plank.slabNonconcentration_of_factorization` uses that to absorb the loss constants.

Internally this is the composite of `Plank.factorNormalisingAffineEquiv`,
`Plank.volumePullbackNormalisedSlab` (S6G17), `Plank.pullbackNormalisedSlabMinWidth` (S6G18),
`Plank.coarseTubeContainerOfPullbackSlab` (S6G19) and `Plank.coarseFineSlabFibreCardinality` (S6G20).
Sorried interface leaf. -/
theorem katzTaoTransverseFactorBound :
    ∃ Ctr : ℝ≥0, 1 ≤ Ctr ∧
      ∀ {a b δ ρ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} (ha : 0 < a) (hδ0 : 0 < δ)
        (hδa : δ ≤ a) (hρa : ρ ≤ a) (a₀ : ℝ≥0) (ha₀ : 0 < a₀) (hsmall : δ ≤ a₀ * b)
        (W : Plank a b hab hb1)
        {ι κ : Type*} (qW : Finset ι) (rW : Finset κ)
        (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
        (R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))) (assign : ι → κ)
        (C₀ Cfib m : ℝ≥0),
        1 ≤ C₀ → 1 ≤ Cfib → 0 < m →
        (∀ i ∈ qW, (T i).carrier ⊆ W.carrier) →
        (∀ i ∈ qW, assign i ∈ rW ∧
          (T i).toConvexSpaceBody ≤ (R (assign i)).toConvexSpaceBody) →
        ConvexSpaceBody.IsFrostmanIn rW (fun k => (R k).toConvexSpaceBody)
          W.toConvexSpaceBody C₀ →
        (∀ k ∈ rW,
            m / Cfib ≤ (({i ∈ qW | assign i = k}).card : ℝ≥0) ∧
            (({i ∈ qW | assign i = k}).card : ℝ≥0) ≤ Cfib * m) →
        (∀ k ∈ rW, (R k).carrier ⊆ W.carrier) →
        ∃ (a' b' : ℝ≥0) (ha'b' : a' ≤ b') (hb'1 : b' ≤ 1)
          (Pj : ι → Plank a' b' ha'b' hb'1),
          0 < a' ∧ δ ≤ a' ∧ a' ≤ a₀ ∧
          (a' / b' = a / b) ∧
          ((a' : ENNReal) / (b' : ENNReal) = (a : ENNReal) / (b : ENNReal)) ∧
          (∀ i ∈ qW, (Pj i).carrier ⊆ Metric.closedBall 0 (plankWindowRadius : ℝ)) ∧
          ∀ (θ : ℝ≥0) (hθ1 : θ ≤ 1), a' / b' ≤ θ → ∀ (S : Slab θ hθ1),
            ((Plank.inSlabFamily qW Pj S).card : ℝ≥0)
              ≤ Ctr * C₀ * Cfib ^ 2 * θ * (qW.card : ℝ≥0) := by
  obtain ⟨kap, cfac, _Cfac, hkap, hcfac, _hCfac, haff⟩ := factorNormalisingAffineEquiv
  obtain ⟨Cpull, hCpull, hS17⟩ := volumePullbackNormalisedSlab cfac hcfac
  obtain ⟨_Cnorm, Ctang, _hCnorm, _hCtang, hNorm⟩ := normaliseTubesInsidePlank kap hkap
  obtain ⟨Crad, hCrad, hS19cont⟩ := coarseTubeContainerOfPullbackSlab
  obtain ⟨Cctr, hCctr, hS19vol⟩ :=
    thickenedPullbackSlabVolume kap hkap Ctang Cpull Crad hCpull hCrad
  obtain ⟨Ccount, hCcount, hS20⟩ := coarseFineSlabFibreCardinality
  refine ⟨Ccount * (Cctr * Cpull), ?_, ?_⟩
  · -- 1 ≤ Ccount * (Cctr * Cpull): all three are ≥ 1
    have hCctrCpull : (1 : ℝ≥0) ≤ Cctr * Cpull := by
      calc
        (1 : ℝ≥0) = 1 * 1 := by norm_num
        _ ≤ Cctr * Cpull := mul_le_mul hCctr hCpull (by positivity) (by positivity)
    calc (1 : ℝ≥0) = 1 * 1 := by norm_num
      _ ≤ Ccount * (Cctr * Cpull) := mul_le_mul hCcount hCctrCpull (by positivity) (by positivity)
  intro a b δ ρ hab hb1 ha hδ0 hδa hρa a₀ ha₀ hsmall W ι κ qW rW T R assign C₀ Cfib m
    hC₀ hCfib hm hcarrier hassign hfrost hfibre hRW
  obtain ⟨f, J, g, hJ, hnorm, hvolf, himg, hWimg, hJab, _⟩ := haff ha W
  obtain ⟨a', b', ha'b', hb'1, Pj, ha'def, hb'def, ha'pos, hδa', ha'a₀, hratioNN, hratioENN,
    hballPj, hlink, htang, _hmaxd⟩ := hNorm ha hδ0 hδa a₀ ha₀ hsmall W f J g hJ hnorm hvolf himg qW T hcarrier
  refine ⟨a', b', ha'b', hb'1, Pj, ha'pos, hδa', ha'a₀, hratioNN, hratioENN, hballPj, ?_⟩
  intro θ hθ1 hθge S
  have hθge' : a / b ≤ θ := by
    rw [← hratioNN]
    exact hθge
  by_cases hne : (Plank.inSlabFamily qW Pj S).Nonempty
  · obtain ⟨_, _⟩ := hS17 ha W f J hJ hvolf himg hJab θ hθ1 S
    have hbpos : 0 < b := lt_of_lt_of_le ha hab
    have hθ0 : 0 < θ := lt_of_lt_of_le (div_pos ha hbpos) hθge'
    have hS17vol : ∀ (θ' : ℝ≥0) (hθ'1 : θ' ≤ 1) (S' : Slab θ' hθ'1),
        volume (W.carrier ∩ f ⁻¹' S'.carrier)
          ≤ (Cpull : ENNReal) * (θ' : ENNReal) * volume W.carrier :=
      fun θ' hθ'1 S' => (hS17 ha W f J hJ hvolf himg hJab θ' hθ'1 S').2
    have hneK : (W.carrier ∩ f ⁻¹' S.carrier).Nonempty := by
      obtain ⟨i, hi⟩ := hne
      have hiq : i ∈ qW := by
        rcases Finset.mem_filter.mp hi with ⟨hiq, _⟩
        exact hiq
      have hsub : (T i).carrier ⊆ W.carrier ∩ f ⁻¹' S.carrier := by
        exact Set.subset_inter (hcarrier i hiq) (hlink θ hθ1 S i hi)
      rcases (T i).toConvexSpaceBody.nonempty with ⟨x, hx⟩
      exact ⟨x, hsub hx⟩
    obtain ⟨Kb, hKb⟩ := exists_cthickenedPullbackBody W f S (Crad * ρ) hneK
    have hvolKplus := hS19vol ha hρa W f g hnorm hWimg hS17vol θ hθ0 hθ1 S hθge' (htang θ hθ1 S hne)
    have hKW : Kb ≤ W.toConvexSpaceBody := by
      exact (SetLike.coe_subset_coe (S := Kb) (T := W.toConvexSpaceBody)).mp (by
        rw [hKb]
        exact Set.inter_subset_left)
    have hvolKb : volume Kb.carrier ≤
        ((Cctr * Cpull : ℝ≥0) : ENNReal) * (θ : ENNReal) * volume W.carrier := by
      change volume (Kb : Set (EuclideanSpace ℝ (Fin 3))) ≤
        ((Cctr * Cpull : ℝ≥0) : ENNReal) * (θ : ENNReal) * volume W.carrier
      rw [hKb]
      simpa [ENNReal.coe_mul, mul_assoc] using hvolKplus
    have hcontain : ∀ i ∈ Plank.inSlabFamily qW Pj S,
        (R (assign i)).carrier ⊆ W.carrier ∩ Metric.cthickening ((Crad * ρ : ℝ≥0) : ℝ)
          (W.carrier ∩ f ⁻¹' S.carrier) := by
      intro i hi
      have hiq : i ∈ qW := by
        rcases Finset.mem_filter.mp hi with ⟨hiq, _⟩
        exact hiq
      have hTi_contain : (T i).carrier ⊆ W.carrier ∩ f ⁻¹' S.carrier := by
        have hTi_W : (T i).carrier ⊆ W.carrier := hcarrier i hiq
        have hTi_fS : (T i).carrier ⊆ f ⁻¹' S.carrier := hlink θ hθ1 S i hi
        exact Set.subset_inter hTi_W hTi_fS
      have hRi_W : (R (assign i)).carrier ⊆ W.carrier :=
        hRW (assign i) (hassign i hiq).1
      have hTi_R : (T i).carrier ⊆ (R (assign i)).carrier :=
        (SetLike.coe_subset_coe (S := (T i).toConvexSpaceBody)
          (T := (R (assign i)).toConvexSpaceBody)).mp (hassign i hiq).2
      have hcompat := hS19cont ha hδ0 hρa W f J hJ hvolf himg θ hθ1 S hθge' qW T R assign
      exact hcompat i hiq hTi_contain hTi_R hRi_W
    have hcontainKb : ∀ i ∈ Plank.inSlabFamily qW Pj S,
        (R (assign i)).toConvexSpaceBody ≤ Kb := by
      intro i hi
      apply (SetLike.coe_subset_coe (S := (R (assign i)).toConvexSpaceBody)
        (T := Kb)).mp
      rw [hKb]
      exact hcontain i hi
    have hCctrCpull : (1 : ℝ≥0) ≤ Cctr * Cpull := by
      calc
        (1 : ℝ≥0) = 1 * 1 := by norm_num
        _ ≤ Cctr * Cpull := mul_le_mul hCctr hCpull (by positivity) (by positivity)
    have hcount := hS20 ha hδ0 hρa W f J hJ hvolf himg
      qW rW T R assign C₀ Cfib m hC₀ hCfib hm hcarrier hassign hfrost hfibre hRW
      Pj Kb hKW (Cctr * Cpull) hCctrCpull θ hθ1 S hθge' hvolKb hcontainKb
    simpa [mul_assoc] using hcount
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne]
    simp

/-- `ℝ≥0` companion of `Kakeya.rpowConstAbsorb`: for an absolute constant `C ≥ 1` and a positive
exponent `e` there is a threshold `x₀ > 0` with `C ≤ x ^ (-e)` for every `0 < x ≤ x₀`
(take `x₀ = C ^ (-1/e)`).

The `ENNReal` version cannot be used here: it lives in `FrostmanPlankEstimate.lean`, which *imports*
this file, and the slab counts of this file are stated in `ℝ≥0`. -/
theorem exists_rpow_absorbs_constant (C : ℝ≥0) (hC : 1 ≤ C) {e : ℝ} (he : 0 < e) :
    ∃ x₀ : ℝ≥0, 0 < x₀ ∧ ∀ x : ℝ≥0, 0 < x → x ≤ x₀ → C ≤ x ^ (-e) := by
  have hC0 : 0 < C := lt_of_lt_of_le (by norm_num : (0 : ℝ≥0) < 1) hC
  set x₀ : ℝ≥0 := C ^ ((-1) / e) with hx₀_def
  have hx₀_pos : 0 < x₀ := NNReal.rpow_pos hC0
  refine ⟨x₀, hx₀_pos, ?_⟩
  intro x hx_pos hx_le
  have hx₀_eq : x₀ ^ (-e) = C := by
    calc
      x₀ ^ (-e) = (C ^ ((-1) / e)) ^ (-e) := by rw [hx₀_def]
      _ = C ^ (((-1) / e) * (-e)) := by rw [NNReal.rpow_mul]
      _ = C ^ (1 : ℝ) := by
        field_simp [he.ne']
      _ = C := by rw [NNReal.rpow_one C]
  have hx₀_pow_le : x₀ ^ (-e) ≤ x ^ (-e) :=
    NNReal.rpow_le_rpow_of_nonpos hx_pos hx_le (neg_nonpos.mpr he.le)
  calc
    C = x₀ ^ (-e) := by symm; exact hx₀_eq
    _ ≤ x ^ (-e) := hx₀_pow_le

/-- **Packaged `γ = 1` slab non-concentration for a plank factorisation**
(`lem:geometryFactorSlabNonconcentration`, S6G21).

The consumer-facing form of `Plank.katzTaoTransverseFactorBound`: the normalised inner plank family obtained
from the fine `δ`-tubes inside an `a × b × 1` plank `W` satisfies

`|{i ∈ qW : Φ_W(T i) ⊆ S}| ≤ (a')^(-η) · θ · |qW|`

for every `θ` with `a'/b' ≤ θ ≤ 1` and every `θ × 1 × 1` slab `S`, where `a' ≈ δ/b` is the inner
small scale. This is *precisely* the `γ = 1` hypothesis consumed by GWZ Lemma 6.1
(`Kakeya.KatzTaoEstimate.plankEstimate`), and it is what supplies the `(a/b)^β` gain in GWZ
Proposition 6.6(B).

**Proved** from `Plank.katzTaoTransverseFactorBound` and `Plank.exists_rpow_absorbs_constant`: the threshold `a₀` is
chosen so that the fixed losses `Ctr · C₀ · Cfib ^ 2` are below `a₀ ^ (-η)`, and since the produced
inner scale satisfies `a' ≤ a₀` the same bound holds with `a'` in place of `a₀`. The coarse Frostman
constant `C₀` and the fibre-comparability constant `Cfib` are therefore quantified *before* the
threshold: `a₀` depends on them, which is the precise content of "`C₀` is sub-polynomial in the
ambient small scale". -/
theorem slabNonconcentration_of_factorization {η : ℝ} (hη : 0 < η) (C₀ Cfib : ℝ≥0)
    (hC₀ : 1 ≤ C₀) (hCfib : 1 ≤ Cfib) :
    ∃ a₀ : ℝ≥0, 0 < a₀ ∧
      ∀ {a b δ ρ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}, 0 < a → 0 < δ → δ ≤ a → ρ ≤ a →
        δ ≤ a₀ * b →
        ∀ (W : Plank a b hab hb1) {ι κ : Type*} (qW : Finset ι) (rW : Finset κ)
          (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
          (R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))) (assign : ι → κ) (m : ℝ≥0),
          0 < m →
          (∀ i ∈ qW, (T i).carrier ⊆ W.carrier) →
          (∀ i ∈ qW, assign i ∈ rW ∧
            (T i).toConvexSpaceBody ≤ (R (assign i)).toConvexSpaceBody) →
          ConvexSpaceBody.IsFrostmanIn rW (fun k => (R k).toConvexSpaceBody)
            W.toConvexSpaceBody C₀ →
          (∀ k ∈ rW,
              m / Cfib ≤ (({i ∈ qW | assign i = k}).card : ℝ≥0) ∧
              (({i ∈ qW | assign i = k}).card : ℝ≥0) ≤ Cfib * m) →
          (∀ k ∈ rW, (R k).carrier ⊆ W.carrier) →
          ∃ (a' b' : ℝ≥0) (ha'b' : a' ≤ b') (hb'1 : b' ≤ 1)
            (Pj : ι → Plank a' b' ha'b' hb'1),
            0 < a' ∧ δ ≤ a' ∧ a' ≤ a₀ ∧
            (a' / b' = a / b) ∧
            ((a' : ENNReal) / (b' : ENNReal) = (a : ENNReal) / (b : ENNReal)) ∧
            (∀ i ∈ qW, (Pj i).carrier ⊆ Metric.closedBall 0 (plankWindowRadius : ℝ)) ∧
            ∀ (θ : ℝ≥0) (hθ1 : θ ≤ 1), a' / b' ≤ θ → ∀ (S : Slab θ hθ1),
              ((Plank.inSlabFamily qW Pj S).card : ℝ≥0)
                ≤ a' ^ (-η) * θ ^ (1 : ℝ) * (qW.card : ℝ≥0) := by
  obtain ⟨Ctr, hCtr1, hKT⟩ := katzTaoTransverseFactorBound
  have h1 : (1 : ℝ≥0) ≤ Cfib ^ 2 := by
    calc
      (1 : ℝ≥0) = 1 * 1 := by norm_num
      _ ≤ Cfib * Cfib := mul_le_mul hCfib hCfib (by norm_num) (by norm_num)
      _ = Cfib ^ 2 := by ring
  have hprod1 : (1 : ℝ≥0) ≤ Ctr * C₀ * Cfib ^ 2 := by
    calc
      (1 : ℝ≥0) = 1 * 1 * 1 := by norm_num
      _ ≤ Ctr * C₀ * Cfib ^ 2 := by
        refine mul_le_mul (mul_le_mul hCtr1 hC₀ (by norm_num) (by norm_num)) h1 (by norm_num) (by norm_num)
  obtain ⟨a₀, ha₀pos, habs⟩ := exists_rpow_absorbs_constant (Ctr * C₀ * Cfib ^ 2) hprod1 hη
  refine ⟨a₀, ha₀pos, ?_⟩
  intro a b δ ρ hab hb1 ha hδ0 hδa hρa hsmall W ι κ qW rW T R assign m hm hcarrier hassign hfrost
    hfibre hRW
  obtain ⟨a', b', ha'b', hb'1, Pj, ha'pos, hδa', ha'a₀, hratioNN, hratioENN, hballPj, hcount⟩ :=
    hKT ha hδ0 hδa hρa a₀ ha₀pos hsmall W qW rW T R assign C₀ Cfib m hC₀ hCfib hm
      hcarrier hassign hfrost hfibre hRW
  refine ⟨a', b', ha'b', hb'1, Pj, ha'pos, hδa', ha'a₀, hratioNN, hratioENN, hballPj, ?_⟩
  intro θ hθ1 hθge S
  have hconst : Ctr * C₀ * Cfib ^ 2 ≤ a' ^ (-η) := habs a' ha'pos ha'a₀
  calc ((Plank.inSlabFamily qW Pj S).card : ℝ≥0)
      ≤ Ctr * C₀ * Cfib ^ 2 * θ * (qW.card : ℝ≥0) := hcount θ hθ1 hθge S
    _ ≤ a' ^ (-η) * θ ^ (1 : ℝ) * (qW.card : ℝ≥0) := by
      calc
        Ctr * C₀ * Cfib ^ 2 * θ * (qW.card : ℝ≥0) ≤ a' ^ (-η) * θ * (qW.card : ℝ≥0) := by
          have hθ0 : (0 : ℝ≥0) ≤ θ := θ.property
          have ha0 : (0 : ℝ≥0) ≤ a' ^ (-η) := (a' ^ (-η)).property
          have hq0 : (0 : ℝ≥0) ≤ (qW.card : ℝ≥0) := (qW.card : ℝ≥0).property
          have haθ0 : (0 : ℝ≥0) ≤ a' ^ (-η) * θ := mul_nonneg ha0 hθ0
          refine mul_le_mul (mul_le_mul hconst (le_refl _) hθ0 ha0) (le_refl _) hq0 haθ0
        _ = a' ^ (-η) * θ ^ (1 : ℝ) * (qW.card : ℝ≥0) := by simp [NNReal.rpow_one]

end Plank

end
