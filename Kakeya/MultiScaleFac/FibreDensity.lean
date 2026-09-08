/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.FibreCommon
public import Kakeya.Frostman

/-!
# Counts, densities and Frostman constants of a single fibre

Every remaining geometric step of GWZ Lemma 7.7(A)
(`Kakeya.StickyKakeya.dividingScalesFrostman`) has the same three-layer shape:

1. a comparison of two *fibre counts*, supplied by uniformity
   (`Kakeya.MultiScaleFac.comparableFibreCounts_of_isUniformAtScale`,
   `Kakeya.MultiScaleFac.anchorGraded_of_isUniformAtScale`);
2. the passage from counts to *densities*, which is pure tube-volume bookkeeping;
3. the passage from densities to *Frostman constants*, which is division by the anchor density.

Layers 2 and 3 are identical in every one of those steps, so they are isolated here once and for
all.  The pivotal statement is `frostmanConstant_fibre_le_of_card_le`: a comparison of the two
fibre counts at anchors `ρ ≤ ρ'` immediately yields the comparison of the two Frostman constants,
with a loss depending only on the ambient dimension.  Both interpolation lemmas of
`Kakeya.MultiScaleFac.Interp` and both halves of a cut in `Kakeya.MultiScaleFac.Stopping` are
instances of it.

Every constant depends only on `Module.finrank ℝ E`; none depends on `δ`, so the blueprint's `⪅`
never appears.
-/

@[expose] public section

open MeasureTheory Real Metric

namespace Kakeya

open StickyKakeya

namespace MultiScaleFac

open _root_.StickyKakeya

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}

/-! ### The fibre as a family inside its own anchor -/

/-! ### Counts and densities -/

/-- A member of a fibre family at a positive member scale has positive volume: a tube of positive
scale has volume at least `c_n σ^{n-1} > 0`. -/
private theorem volume_fibreBodies_pos {σ : NNReal} (hσ : 0 < σ) (i : ι) :
    0 < volume ((fibreBodies T σ) i).carrier := -- (extracted by Fuse golfer)
  (ENNReal.coe_pos.mpr (mul_pos (Tube.le_volume.c_pos _) (pow_pos hσ _))).trans_le
    (Tube.le_volume ((T i).rescale σ))

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- Membership in the fibre index set is, by definition, containment of the thickened member in
the anchor body. -/
private theorem fibreBodies_le_of_mem_fibreIndex {σ ρ : NNReal} {i₀ i : ι}
    (hi : i ∈ fibreIndex s T σ ρ i₀) :
    fibreBodies T σ i ≤ ((T i₀).rescale ρ).toConvexSpaceBody := -- (extracted by Fuse golfer)
  (Finset.mem_filter.mp hi).2

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- A leaf of the fibre `s_{δ∣ρ}(i₀)`, thickened to any member scale `σ ∈ [δ, ρ]`, still fits in
the doubled anchor `T_{i₀}^{(2ρ)}`. -/
private theorem fibreBodies_le_double_anchor {σ ρ : NNReal} (hδσ : δ ≤ σ) (hσρ : σ ≤ ρ)
    {i₀ i : ι} (hi : i ∈ fibreIndex s T δ ρ i₀) :
    fibreBodies T σ i ≤ ((T i₀).rescale (2 * ρ)).toConvexSpaceBody := -- (extracted by Fuse golfer)
  Tube.rescale_le_rescale_of_body_le (T i) ((T i₀).rescale ρ) (σ := σ) (θ := 2 * ρ)
    hδσ (by rw [two_mul]; gcongr) (by simpa using fibreBodies_le_of_mem_fibreIndex hi)

/-- The anchor density of a fibre is positive: the anchor index lies in its own fibre and a tube
of positive scale has positive volume. -/
theorem densityIn_fibre_pos {σ ρ : NNReal} (hσ : 0 < σ) (hσρ : σ ≤ ρ) {i₀ : ι} (hi₀ : i₀ ∈ s) :
    0 < Kakeya.densityIn (fibreIndex s T σ ρ i₀) (fibreBodies T σ)
      ((T i₀).rescale ρ).toConvexSpaceBody :=
  have hm : i₀ ∈ fibreIndex s T σ ρ i₀ := mem_fibreIndex_self hσρ hi₀
  (Kakeya.densityIn_pos_iff _ _ _).mpr
    ⟨i₀, hm, volume_fibreBodies_pos hσ i₀, fibreBodies_le_of_mem_fibreIndex hm⟩

/-! ### Densities and Frostman constants -/

/-- A ratio of `NNReal` scales, raised to a power and pushed into `ENNReal`, is the ratio of the
two powers. -/
private theorem coe_pow_div_pow (x : NNReal) {y : NNReal} (hy : y ≠ 0) (k : ℕ) :
    (x : ENNReal) ^ k / (y : ENNReal) ^ k = (((x / y) ^ k : NNReal) : ENNReal) := by
  -- (extracted by Fuse golfer)
  rw [div_pow, ENNReal.coe_div (pow_ne_zero k hy), ENNReal.coe_pow, ENNReal.coe_pow]

/-- Cross-multiplied comparison of two `ENNReal` quotients with nonzero finite denominators. -/
private theorem div_le_div_of_mul_le_mul {M N d e : ENNReal} (hd : d ≠ 0) (hd' : d ≠ ⊤)
    (he : e ≠ 0) (he' : e ≠ ⊤) (h : M * e ≤ N * d) : M / d ≤ N / e := by
  -- (extracted by Fuse golfer)
  rwa [ENNReal.le_div_iff_mul_le (Or.inl he) (Or.inl he'), div_eq_mul_inv, mul_right_comm,
    ← div_eq_mul_inv, ENNReal.div_le_iff hd hd']

/-- Solving a two-sided band `c · r' · x ≤ A · D · r · y` for `x`. -/
private theorem le_div_mul_of_mul_le_mul {x y A D c r r' : ENNReal} (hc : c ≠ 0) (hc' : c ≠ ⊤)
    (hr' : r' ≠ 0) (hr'' : r' ≠ ⊤) (h : c * r' * x ≤ A * D * r * y) :
    x ≤ D / c * A * (r / r') * y := by
  -- (extracted by Fuse golfer)
  have key : D / c * A * (r / r') * y = A * D * r * y / (c * r') := by
    simp only [div_eq_mul_inv, ENNReal.mul_inv (Or.inl hc) (Or.inl hc')]
    ring
  rw [key, ENNReal.le_div_iff_mul_le (Or.inl (mul_ne_zero hc hr'))
    (Or.inl (ENNReal.mul_ne_top hc' hr''))]
  exact (mul_comm x (c * r')).trans_le h

/-- The arithmetic core of the two Frostman band lemmas: a numerator comparison `Mt ≤ m · Mu`
together with a cross-multiplied denominator comparison `a · du ≤ b · dt` gives the comparison of
the two quotients. -/
private theorem mul_div_le_mul_div_of_band {Mt Mu dt du a b m : ENNReal}
    (hdt : dt ≠ 0) (hdt' : dt ≠ ⊤) (hdu : du ≠ 0) (hdu' : du ≠ ⊤)
    (hmax : Mt ≤ m * Mu) (hband : a * du ≤ b * dt) :
    a * (Mt / dt) ≤ m * b * (Mu / du) := by
  -- (extracted by Fuse golfer)
  rw [mul_div_assoc', mul_div_assoc']
  refine div_le_div_of_mul_le_mul hdt hdt' hdu hdu' ?_
  calc a * Mt * du = Mt * (a * du) := by ring
    _ ≤ (m * Mu) * (b * dt) := mul_le_mul' hmax hband
    _ = m * b * Mu * dt := by ring

omit [Nontrivial E] in
/-- **The density comparison controls the Frostman comparison, across a change of member map.**
The variant of `frostmanConstant_le_of_densityIn_band` in which the two families carry *different*
member bodies `W` and `V`; monotonicity of `Kakeya.maxDensity` in the index set is then unavailable,
so the numerator comparison `Δ_max(t,W) ≤ m · Δ_max(u,V)` becomes a hypothesis. -/
private theorem frostmanConstant_le_of_maxDensity_densityIn_band {ι' : Type*} {t u : Finset ι'}
    {V W : ι' → ConvexSpaceBody E} {K K' : ConvexSpaceBody E} {a b m : ENNReal}
    (htK : ∀ i ∈ t, W i ≤ K) (huK' : ∀ i ∈ u, V i ≤ K')
    (hdt : 0 < Kakeya.densityIn t W K) (hdu : 0 < Kakeya.densityIn u V K')
    (hmax : Kakeya.maxDensity t W ≤ m * Kakeya.maxDensity u V)
    (hband : a * Kakeya.densityIn u V K' ≤ b * Kakeya.densityIn t W K) :
    a * ConvexSpaceBody.frostmanConstant t W K
      ≤ m * b * ConvexSpaceBody.frostmanConstant u V K' := by
  rw [ConvexSpaceBody.frostmanConstant_eq_maxDensity_div hdt htK,
      ConvexSpaceBody.frostmanConstant_eq_maxDensity_div hdu huK']
  exact mul_div_le_mul_div_of_band hdt.ne' (Kakeya.densityIn_ne_top t W K)
    hdu.ne' (Kakeya.densityIn_ne_top u V K') hmax hband

omit [Nontrivial E] in
/-- **The density comparison controls the Frostman comparison.**  If `t ⊆ u`, every member of `t`
sits in `K`, every member of `u` sits in `K'`, and the anchor densities satisfy the band
`a · Δ(u,K') ≤ b · Δ(t,K)`, then the same band holds for the Frostman constants, since
`C_F = Δ_max / Δ` and the numerators obey `Δ_max(t) ≤ Δ_max(u)` by monotonicity. -/
theorem frostmanConstant_le_of_densityIn_band {ι' : Type*} {t u : Finset ι'}
    {W : ι' → ConvexSpaceBody E} {K K' : ConvexSpaceBody E} {a b : ENNReal}
    (htu : t ⊆ u) (htK : ∀ i ∈ t, W i ≤ K) (huK' : ∀ i ∈ u, W i ≤ K')
    (_ha : 0 < a) (_ha' : a ≠ ⊤) (_hb' : b ≠ ⊤)
    (hdt : 0 < Kakeya.densityIn t W K) (hdu : 0 < Kakeya.densityIn u W K')
    (hband : a * Kakeya.densityIn u W K' ≤ b * Kakeya.densityIn t W K) :
    a * ConvexSpaceBody.frostmanConstant t W K
      ≤ b * ConvexSpaceBody.frostmanConstant u W K' := by
  refine (frostmanConstant_le_of_maxDensity_densityIn_band (m := 1) htK huK' hdt hdu
    ((maxDensity_mono W htu).trans_eq (one_mul _).symm) hband).trans_eq ?_
  rw [one_mul]

/-- The dimensional loss incurred when a fibre count comparison is turned into a comparison of
Frostman constants: two anchor-volume bands and two member-volume bands. -/
noncomputable abbrev fibreFrostmanConst (n : ℕ) : NNReal :=
  2 * Tube.volume_le.C n ^ 2 / Tube.le_volume.c n ^ 2

/-! ### Thickening the members -/

/-- **Thickening the members of a family costs a fixed power of the thickening ratio.**  Passing
from member scale `σ` to a coarser member scale `σ'` multiplies `Δ_max` by at most
`C_n/c_n · (σ'/σ)^{n-1}`, and one may simultaneously pass to a superset `u ⊇ t` of the index set. -/
theorem maxDensity_fibreBodies_le_of_member_le {σ σ' : NNReal} (hσ : 0 < σ) (hσσ' : σ ≤ σ')
    (hσ'1 : σ' ≤ 1) {t u : Finset ι} (htu : t ⊆ u) :
    Kakeya.maxDensity t (fibreBodies T σ')
      ≤ (((Tube.volume_le.C (Module.finrank ℝ E) / Tube.le_volume.c (Module.finrank ℝ E)
              * (σ' / σ) ^ (Module.finrank ℝ E - 1) : NNReal)) : ENNReal)
          * Kakeya.maxDensity u (fibreBodies T σ) := by
  classical
  set n := Module.finrank ℝ E
  set C := Tube.volume_le.C n
  set c := Tube.le_volume.c n
  set ratio : NNReal := C / c * (σ' / σ) ^ (n - 1) with hratio
  have hc_ne : c ≠ 0 := (Tube.le_volume.c_pos n).ne'
  have hσ_ne : σ ≠ 0 := hσ.ne'
  have hcast : ((C * σ' ^ (n - 1) : NNReal) : ENNReal)
      = (ratio : ENNReal) * ((c * σ ^ (n - 1) : NNReal) : ENNReal) := by
    have hNN : (C * σ' ^ (n - 1) : NNReal) = ratio * (c * σ ^ (n - 1)) := by
      rw [hratio]
      field_simp [hc_ne, hσ_ne]
      rw [div_pow, mul_assoc, div_mul_cancel₀ (σ' ^ (n - 1)) (pow_ne_zero _ hσ_ne)]
    exact_mod_cast hNN
  have hterm : ∀ i : ι, volume ((fibreBodies T σ') i).carrier
      ≤ (ratio : ENNReal) * volume ((fibreBodies T σ) i).carrier := fun i =>
    (Tube.volume_le hσ'1 ((T i).rescale σ')).trans
      (hcast.trans_le (mul_le_mul_right (Tube.le_volume ((T i).rescale σ)) _))
  rw [maxDensity_le_iff t (fibreBodies T σ')]
  intro K
  have hsubset :
      (t.filter (fun i => (fibreBodies T σ') i ≤ K)) ⊆
        (u.filter (fun i => (fibreBodies T σ) i ≤ K)) := fun i hi =>
    Finset.mem_filter.mpr ⟨htu (Finset.mem_filter.mp hi).1,
      (Tube.rescale_le_rescale_of_radius_le (T i) hσσ').trans (Finset.mem_filter.mp hi).2⟩
  rw [densityIn_le_iff t (fibreBodies T σ') K
    ((ratio : ENNReal) * maxDensity u (fibreBodies T σ))]
  calc
    (∑ i ∈ t with (fibreBodies T σ') i ≤ K, volume ((fibreBodies T σ') i).carrier)
        ≤ ∑ i ∈ u with (fibreBodies T σ) i ≤ K,
            (ratio : ENNReal) * volume ((fibreBodies T σ) i).carrier :=
          (Finset.sum_le_sum fun i _ => hterm i).trans (Finset.sum_le_sum_of_subset hsubset)
    _ = (ratio : ENNReal) * (densityIn u (fibreBodies T σ) K * volume K.carrier) := by
        rw [← Finset.mul_sum, sum_volume_eq_densityIn_mul_volume u (fibreBodies T σ) K]
    _ ≤ (ratio : ENNReal) * maxDensity u (fibreBodies T σ) * volume K.carrier := by
        rw [mul_assoc]
        exact mul_le_mul_right (mul_le_mul_left (le_maxDensity u (fibreBodies T σ) K) _) _

/-! ### The sharp form, keeping the anchor-volume gain -/

/-- The bookkeeping behind `densityIn_fibre_band_of_card_le_sharp`: two volume bands and a count
comparison, with the common member-volume factor `S` cancelled at the end. -/
private theorem band_of_card_algebra {c C A k k' Δ Δ' R R' S : ENNReal} (hS : S ≠ 0) (hS' : S ≠ ⊤)
    (h1 : Δ' * (c * R') ≤ k' * (C * S)) (hk : k' ≤ A * k)
    (h2 : k * (c * S) ≤ Δ * (2 * C * R)) :
    c ^ 2 * R' * Δ' ≤ A * (2 * C ^ 2) * R * Δ := by
  -- (extracted by Fuse golfer)
  refine (ENNReal.mul_le_mul_iff_left hS hS').mp ?_
  calc c ^ 2 * R' * Δ' * S = Δ' * (c * R') * (c * S) := by ring
    _ ≤ A * k * (C * S) * (c * S) := mul_le_mul' (h1.trans (mul_le_mul' hk le_rfl)) le_rfl
    _ = A * (C * S) * (k * (c * S)) := by ring
    _ ≤ A * (C * S) * (Δ * (2 * C * R)) := mul_le_mul' le_rfl h2
    _ = A * (2 * C ^ 2) * R * Δ * S := by ring

/-- The bookkeeping behind `frostmanConstant_blockFibre_le_of_card_le`: the member-volume
comparison ratio `ratio` is the only loss, because the two anchor bodies are nested. -/
private theorem block_band_algebra {Δu Δt V V' ku kt A ratio c S : ENNReal}
    (h1 : Δu * V' ≤ ku * (ratio * c * S)) (hk : ku ≤ A * kt)
    (h2 : kt * (c * S) ≤ Δt * V) (hV : V ≤ V') :
    Δu * V' ≤ A * ratio * Δt * V' := by
  -- (extracted by Fuse golfer)
  calc Δu * V' ≤ A * kt * (ratio * c * S) := h1.trans (mul_le_mul' hk le_rfl)
    _ = A * (kt * (c * S)) * ratio := by ring
    _ ≤ A * (Δt * V') * ratio :=
        mul_le_mul' (mul_le_mul' le_rfl (h2.trans (mul_le_mul' le_rfl hV))) le_rfl
    _ = A * ratio * Δt * V' := by ring

/-- **Sharp form of `densityIn_fibre_band_of_card_le`.**  The crude form throws away the factor
`(ρ/ρ')^{n-1}` coming from the two anchor volumes; here it is kept.  That factor is decisive
whenever the count comparison `A` itself grows like a power of `ρ'/ρ`, as it does at every
anchor-shrinking step of GWZ Lemma 7.7(A). -/
theorem densityIn_fibre_band_of_card_le_sharp {σ ρ ρ' : NNReal} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hρ : 0 < ρ) (hρρ' : ρ ≤ ρ') (hρ'1 : ρ' ≤ 1) {A : ENNReal} {i₀ : ι}
    (hcard : ((fibreIndex s T σ ρ' i₀).card : ENNReal)
      ≤ A * ((fibreIndex s T σ ρ i₀).card : ENNReal)) :
    (((Tube.le_volume.c (Module.finrank ℝ E) : NNReal) : ENNReal)) ^ 2
        * ((ρ' : ENNReal) ^ (Module.finrank ℝ E - 1))
        * Kakeya.densityIn (fibreIndex s T σ ρ' i₀) (fibreBodies T σ)
            ((T i₀).rescale ρ').toConvexSpaceBody
      ≤ A * (((2 * Tube.volume_le.C (Module.finrank ℝ E) ^ 2 : NNReal) : ENNReal))
          * ((ρ : ENNReal) ^ (Module.finrank ℝ E - 1))
          * Kakeya.densityIn (fibreIndex s T σ ρ i₀) (fibreBodies T σ)
              ((T i₀).rescale ρ).toConvexSpaceBody := by
  have _hρ := hρ -- `0 < ρ` is not needed for the band, only `ρ ≤ 1`
  have hband2 := card_mul_le_densityIn_fibre (s := s) (T := T) (σ := σ) (ρ := ρ) (b := 1)
    (hρρ'.trans hρ'1) i₀
  push_cast [one_add_one_eq_two] at hband2 ⊢
  exact band_of_card_algebra (pow_ne_zero _ (ENNReal.coe_ne_zero.mpr hσ.ne'))
    (ENNReal.pow_ne_top ENNReal.coe_ne_top) (densityIn_fibre_mul_le_card hσ1 ρ' i₀) hcard hband2

/-- **Sharp form of `frostmanConstant_fibre_le_of_card_le`.**  Keeping the anchor-volume factor, a
count comparison `|s_{σ∣ρ'}(i₀)| ≤ A · |s_{σ∣ρ}(i₀)|` gives
`C_F(𝕋_{σ∣ρ}[i₀]) ≤ 2C_n²/c_n² · A · (ρ/ρ')^{n-1} · C_F(𝕋_{σ∣ρ'}[i₀])`, so with the packing count
`A ≈ (ρ'/ρ)^{2n}` the net loss is `(ρ'/ρ)^{n+1}` rather than `(ρ'/ρ)^{2n}`. -/
theorem frostmanConstant_fibre_le_of_card_le_sharp {σ ρ ρ' : NNReal} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hσρ : σ ≤ ρ) (hρρ' : ρ ≤ ρ') (hρ'1 : ρ' ≤ 1) {A : ENNReal} (hA : A ≠ ⊤) {i₀ : ι}
    (hi₀ : i₀ ∈ s)
    (hcard : ((fibreIndex s T σ ρ' i₀).card : ENNReal)
      ≤ A * ((fibreIndex s T σ ρ i₀).card : ENNReal)) :
    ConvexSpaceBody.frostmanConstant (fibreIndex s T σ ρ i₀) (fibreBodies T σ)
        ((T i₀).rescale ρ).toConvexSpaceBody
      ≤ ((fibreFrostmanConst (Module.finrank ℝ E) : NNReal) : ENNReal) * A
          * (((ρ / ρ') ^ (Module.finrank ℝ E - 1) : NNReal) : ENNReal)
          * ConvexSpaceBody.frostmanConstant (fibreIndex s T σ ρ' i₀) (fibreBodies T σ)
            ((T i₀).rescale ρ').toConvexSpaceBody := by
  classical
  set n := Module.finrank ℝ E
  set p := n - 1
  let cn : NNReal := Tube.le_volume.c n
  let Cn : NNReal := Tube.volume_le.C n
  have hρ : 0 < ρ := lt_of_lt_of_le hσ hσρ
  have hρ' : 0 < ρ' := lt_of_lt_of_le hρ hρρ'
  have hc_ne0 : (cn : NNReal) ≠ 0 := (Tube.le_volume.c_pos n).ne'
  have hc2_ne0 : (cn : ENNReal) ^ 2 ≠ 0 := pow_ne_zero 2 (ENNReal.coe_ne_zero.mpr hc_ne0)
  have hc2_ne_top : (cn : ENNReal) ^ 2 ≠ ⊤ := ENNReal.pow_ne_top ENNReal.coe_ne_top
  have hρ'p_ne : (ρ' : ENNReal) ^ p ≠ 0 := pow_ne_zero p (ENNReal.coe_ne_zero.mpr hρ'.ne')
  have hρ'p_top : (ρ' : ENNReal) ^ p ≠ ⊤ := ENNReal.pow_ne_top ENNReal.coe_ne_top
  have hfr := frostmanConstant_le_of_densityIn_band
    (ι' := ι) (t := fibreIndex s T σ ρ i₀) (u := fibreIndex s T σ ρ' i₀)
    (W := fibreBodies T σ) (K := ((T i₀).rescale ρ).toConvexSpaceBody)
    (K' := ((T i₀).rescale ρ').toConvexSpaceBody)
    (a := (cn : ENNReal) ^ 2 * (ρ' : ENNReal) ^ p)
    (b := A * ((2 * Cn ^ 2 : NNReal) : ENNReal) * (ρ : ENNReal) ^ p)
    (fibreIndex_subset_of_anchor_le hρρ' i₀)
    (fun _ hi => fibreBodies_le_of_mem_fibreIndex hi)
    (fun _ hi => fibreBodies_le_of_mem_fibreIndex hi)
    (ENNReal.mul_pos hc2_ne0 hρ'p_ne) (ENNReal.mul_ne_top hc2_ne_top hρ'p_top)
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top hA ENNReal.coe_ne_top)
      (ENNReal.pow_ne_top ENNReal.coe_ne_top))
    (densityIn_fibre_pos hσ hσρ hi₀) (densityIn_fibre_pos hσ (hσρ.trans hρρ') hi₀)
    (densityIn_fibre_band_of_card_le_sharp hσ hσ1 hρ hρρ' hρ'1 hcard)
  have hcoediv : ((fibreFrostmanConst n : NNReal) : ENNReal)
      = ((2 * Cn ^ 2 : NNReal) : ENNReal) / (cn : ENNReal) ^ 2 := by
    rw [show (fibreFrostmanConst n : NNReal) = 2 * Cn ^ 2 / cn ^ 2 from rfl,
      ENNReal.coe_div (show cn ^ 2 ≠ 0 from pow_ne_zero 2 hc_ne0)]
    simp
  rw [hcoediv, ← coe_pow_div_pow ρ hρ'.ne' p]
  exact le_div_mul_of_mul_le_mul hc2_ne0 hc2_ne_top hρ'p_ne hρ'p_top hfr

/-- **The pivotal comparison: counts control Frostman constants.**  If the fibre of `i₀` at the
coarse anchor `ρ'` has at most `A` times as many members as the fibre at the fine anchor `ρ`, then
the Frostman constant at `ρ` is at most `2 C_n²/c_n² · A` times the one at `ρ'`.  Note the
direction: the *finer* anchor carries the bounded Frostman constant. -/
theorem frostmanConstant_fibre_le_of_card_le {σ ρ ρ' : NNReal} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hσρ : σ ≤ ρ) (hρρ' : ρ ≤ ρ') (hρ'1 : ρ' ≤ 1) {A : ENNReal} (hA : A ≠ ⊤) {i₀ : ι}
    (hi₀ : i₀ ∈ s)
    (hcard : ((fibreIndex s T σ ρ' i₀).card : ENNReal)
      ≤ A * ((fibreIndex s T σ ρ i₀).card : ENNReal)) :
    ConvexSpaceBody.frostmanConstant (fibreIndex s T σ ρ i₀) (fibreBodies T σ)
        ((T i₀).rescale ρ).toConvexSpaceBody
      ≤ ((fibreFrostmanConst (Module.finrank ℝ E) : NNReal) : ENNReal) * A *
          ConvexSpaceBody.frostmanConstant (fibreIndex s T σ ρ' i₀) (fibreBodies T σ)
            ((T i₀).rescale ρ').toConvexSpaceBody := by
  have hr : (((ρ / ρ') ^ (Module.finrank ℝ E - 1) : NNReal) : ENNReal) ≤ 1 := by
    exact_mod_cast pow_le_one₀ bot_le ((div_le_one ((hσ.trans_le hσρ).trans_le hρρ')).mpr hρρ')
  exact (frostmanConstant_fibre_le_of_card_le_sharp hσ hσ1 hσρ hρρ' hρ'1 hA hi₀ hcard).trans
    (mul_le_mul' ((mul_le_mul' le_rfl hr).trans_eq (mul_one _)) le_rfl)

/-! ### Two unconditional bounds on a fibre Frostman constant -/

/-- **The crude fibre bound.**  With no uniformity hypothesis whatsoever, the Frostman constant of
a fibre is at most a dimensional constant times `(ρ/σ)^{n-1}`: the numerator `Δ_max` is at most the
fibre count (`Kakeya.maxDensity_le_card`), while the anchor density is at least the fibre count
times `c_n σ^{n-1} / (2 C_n ρ^{n-1})`. -/
theorem frostmanConstant_fibre_le_ratio_pow {σ ρ : NNReal} (hσ : 0 < σ) (hσρ : σ ≤ ρ)
    (hρ1 : ρ ≤ 1) {i₀ : ι} (hi₀ : i₀ ∈ s) :
    ConvexSpaceBody.frostmanConstant (fibreIndex s T σ ρ i₀) (fibreBodies T σ)
        ((T i₀).rescale ρ).toConvexSpaceBody
      ≤ (((2 * Tube.volume_le.C (Module.finrank ℝ E) / Tube.le_volume.c (Module.finrank ℝ E)
              * (ρ / σ) ^ (Module.finrank ℝ E - 1) : NNReal)) : ENNReal) := by
  classical
  set n := Module.finrank ℝ E
  set p := n - 1
  have hc_ne0 : Tube.le_volume.c n ≠ 0 := (Tube.le_volume.c_pos n).ne'
  have hc0 : ((Tube.le_volume.c n : NNReal) : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hc_ne0
  have hσp_ne : (σ : ENNReal) ^ p ≠ 0 := pow_ne_zero p (ENNReal.coe_ne_zero.mpr hσ.ne')
  rw [ConvexSpaceBody.frostmanConstant_eq_maxDensity_div (densityIn_fibre_pos hσ hσρ hi₀)
      (fun _ hi => fibreBodies_le_of_mem_fibreIndex hi),
    show (((2 * Tube.volume_le.C n / Tube.le_volume.c n * (ρ / σ) ^ p : NNReal)) : ENNReal)
        = 2 * ((Tube.volume_le.C n : NNReal) : ENNReal) * (ρ : ENNReal) ^ p
            / (((Tube.le_volume.c n : NNReal) : ENNReal) * (σ : ENNReal) ^ p) from by
      rw [ENNReal.coe_mul, ENNReal.coe_div hc_ne0, ← coe_pow_div_pow ρ hσ.ne' p,
        ENNReal.mul_div_mul_comm (Or.inl hc0) (Or.inr hσp_ne)]
      norm_num]
  refine div_le_div_of_mul_le_mul (densityIn_fibre_pos hσ hσρ hi₀).ne' (densityIn_ne_top _ _ _)
    (mul_ne_zero hc0 hσp_ne)
    (ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)) ?_
  calc maxDensity (fibreIndex s T σ ρ i₀) (fibreBodies T σ)
        * (((Tube.le_volume.c n : NNReal) : ENNReal) * (σ : ENNReal) ^ p)
      ≤ ((fibreIndex s T σ ρ i₀).card : ENNReal)
          * (((Tube.le_volume.c n : NNReal) : ENNReal) * (σ : ENNReal) ^ p) :=
        mul_le_mul_left (maxDensity_le_card _ _) _
    _ ≤ Kakeya.densityIn (fibreIndex s T σ ρ i₀) (fibreBodies T σ)
            ((T i₀).rescale ρ).toConvexSpaceBody
          * ((((1 + 1) * Tube.volume_le.C n : NNReal) : ENNReal) * (ρ : ENNReal) ^ p) :=
        card_mul_le_densityIn_fibre (b := 1) hρ1 i₀
    _ = 2 * ((Tube.volume_le.C n : NNReal) : ENNReal) * (ρ : ENNReal) ^ p
          * Kakeya.densityIn (fibreIndex s T σ ρ i₀) (fibreBodies T σ)
              ((T i₀).rescale ρ).toConvexSpaceBody := by
        push_cast
        ring

/-- **Member-scale comparison for the leaf-indexed fibre.**  Raising the member scale of the
leaf-indexed fibre `{i : T_i ⊆ T_{i₀}^{(ρ)}}` from `σ` to `σ' ∈ [σ, ρ]`, with the index set and the
test body `T_{i₀}^{(2ρ)}` held fixed, multiplies the Frostman constant by at most `(C_n/c_n)²`.
There is **no** power of `σ'/σ`: numerator and denominator both gain `(σ'/σ)^{n-1}`. -/
theorem frostmanConstant_blockFibre_member_le {σ σ' ρ : NNReal} (hδ : 0 < δ) (hδσ : δ ≤ σ)
    (hσσ' : σ ≤ σ') (hσ'ρ : σ' ≤ ρ) (hρ1 : ρ ≤ 1) {i₀ : ι} (hi₀ : i₀ ∈ s) :
    ConvexSpaceBody.frostmanConstant (fibreIndex s T δ ρ i₀) (fibreBodies T σ')
        ((T i₀).rescale (2 * ρ)).toConvexSpaceBody
      ≤ (((Tube.volume_le.C (Module.finrank ℝ E)
            / Tube.le_volume.c (Module.finrank ℝ E)) ^ 2 : NNReal) : ENNReal)
          * ConvexSpaceBody.frostmanConstant (fibreIndex s T δ ρ i₀) (fibreBodies T σ)
              ((T i₀).rescale (2 * ρ)).toConvexSpaceBody := by
  classical
  set n := Module.finrank ℝ E
  set C := Tube.volume_le.C n
  set c := Tube.le_volume.c n
  let t : Finset ι := fibreIndex s T δ ρ i₀
  let K : ConvexSpaceBody E := ((T i₀).rescale (2 * ρ)).toConvexSpaceBody
  let m_coeff : ENNReal := ((C / c * (σ' / σ) ^ (n - 1) : NNReal) : ENNReal)
  let b_coeff : ENNReal := ((C / c * (σ / σ') ^ (n - 1) : NNReal) : ENNReal)
  have hσ : 0 < σ := lt_of_lt_of_le hδ hδσ
  have hσ' : 0 < σ' := lt_of_lt_of_le hσ hσσ'
  have hσρ : σ ≤ ρ := hσσ'.trans hσ'ρ
  have hc_ne : c ≠ 0 := (Tube.le_volume.c_pos n).ne'
  have hσ_ne : σ ≠ 0 := hσ.ne'
  have hσ'_ne : σ' ≠ 0 := hσ'.ne'
  have hi₀t : i₀ ∈ t := mem_fibreIndex_self (hδσ.trans hσρ) hi₀
  have htK : ∀ i ∈ t, (fibreBodies T σ') i ≤ K := fun _ hi =>
    fibreBodies_le_double_anchor (hδσ.trans hσσ') hσ'ρ hi
  have huK' : ∀ i ∈ t, (fibreBodies T σ) i ≤ K := fun _ hi =>
    fibreBodies_le_double_anchor hδσ hσρ hi
  have hbv : b_coeff * ((c * σ' ^ (n - 1) : NNReal) : ENNReal)
      = ((C * σ ^ (n - 1) : NNReal) : ENNReal) := by
    have hNN : (C * σ ^ (n - 1) : NNReal) = (C / c * (σ / σ') ^ (n - 1)) * (c * σ' ^ (n - 1)) := by
      field_simp [hc_ne, hσ'_ne]
      rw [div_pow, mul_assoc, div_mul_cancel₀ (σ ^ (n - 1)) (pow_ne_zero (n - 1) hσ'_ne)]
    unfold b_coeff
    exact_mod_cast hNN.symm
  have hband_sum : (∑ i ∈ t, volume ((fibreBodies T σ) i).carrier) ≤
      b_coeff * (∑ i ∈ t, volume ((fibreBodies T σ') i).carrier) :=
    calc (∑ i ∈ t, volume ((fibreBodies T σ) i).carrier)
        ≤ ∑ _i ∈ t, ((C * σ ^ (n - 1) : NNReal) : ENNReal) :=
          Finset.sum_le_sum fun i _ => Tube.volume_le (hσρ.trans hρ1) ((T i).rescale σ)
      _ = ∑ _i ∈ t, b_coeff * ((c * σ' ^ (n - 1) : NNReal) : ENNReal) := by rw [hbv]
      _ ≤ ∑ i ∈ t, b_coeff * volume ((fibreBodies T σ') i).carrier :=
          Finset.sum_le_sum fun i _ => mul_le_mul_right (Tube.le_volume ((T i).rescale σ')) _
      _ = b_coeff * ∑ i ∈ t, volume ((fibreBodies T σ') i).carrier := by rw [Finset.mul_sum]
  have hfr := frostmanConstant_le_of_maxDensity_densityIn_band
    (ι' := ι) (t := t) (u := t) (W := fibreBodies T σ') (V := fibreBodies T σ)
    (K := K) (K' := K) (a := 1) (m := m_coeff) (b := b_coeff) htK huK'
    ((Kakeya.densityIn_pos_iff _ _ _).mpr
      ⟨i₀, hi₀t, volume_fibreBodies_pos hσ' i₀, htK i₀ hi₀t⟩)
    ((Kakeya.densityIn_pos_iff _ _ _).mpr
      ⟨i₀, hi₀t, volume_fibreBodies_pos hσ i₀, huK' i₀ hi₀t⟩)
    (maxDensity_fibreBodies_le_of_member_le (σ := σ) (σ' := σ')
      hσ hσσ' (hσ'ρ.trans hρ1) (t := t) (u := t) (Finset.Subset.refl t))
    (by
      rw [Kakeya.densityIn_of_all_le huK', Kakeya.densityIn_of_all_le htK, one_mul,
        ← mul_div_assoc]
      exact ENNReal.div_le_div_right hband_sum _)
  have hmul : m_coeff * b_coeff = (((C / c : NNReal) ^ 2 : NNReal) : ENNReal) := by
    have hcancel : (σ' / σ) * (σ / σ') = 1 := by field_simp [hσ_ne, hσ'_ne]
    have hNN_mul : (C / c * (σ' / σ) ^ (n - 1)) * (C / c * (σ / σ') ^ (n - 1)) = (C / c) ^ 2 := by
      rw [mul_mul_mul_comm, ← mul_pow, hcancel, one_pow, mul_one, ← pow_two]
    unfold m_coeff b_coeff
    exact_mod_cast hNN_mul
  rw [← hmul]
  exact (one_mul _).symm.trans_le hfr

/-- **Anchor comparison for the leaf-indexed fibre.**  With index set the leaf fibre
`{i : T_i ⊆ T_{i₀}^{(ρ)}}`, members thickened to a fixed scale `σ ≤ ρ` and test body the doubled
anchor `T_{i₀}^{(2ρ)}`, a comparison of the two *leaf counts* at anchors `ρ ≤ ρ'` yields the
comparison of the Frostman constants, at the sole loss `C_n/c_n` and with no `(ρ'/ρ)^{n-1}`. -/
theorem frostmanConstant_blockFibre_le_of_card_le {σ ρ ρ' : NNReal} (hδ : 0 < δ) (hδσ : δ ≤ σ)
    (hσ1 : σ ≤ 1) (hσρ : σ ≤ ρ) (hρρ' : ρ ≤ ρ') {A : ENNReal} {i₀ : ι} (hi₀ : i₀ ∈ s)
    (hcard : ((fibreIndex s T δ ρ' i₀).card : ENNReal)
      ≤ A * ((fibreIndex s T δ ρ i₀).card : ENNReal)) :
    ConvexSpaceBody.frostmanConstant (fibreIndex s T δ ρ i₀) (fibreBodies T σ)
        ((T i₀).rescale (2 * ρ)).toConvexSpaceBody
      ≤ A * ((Tube.volume_le.C (Module.finrank ℝ E)
            / Tube.le_volume.c (Module.finrank ℝ E) : NNReal) : ENNReal)
          * ConvexSpaceBody.frostmanConstant (fibreIndex s T δ ρ' i₀) (fibreBodies T σ)
              ((T i₀).rescale (2 * ρ')).toConvexSpaceBody := by
  classical
  set n := Module.finrank ℝ E
  set p := n - 1
  let cn : NNReal := Tube.le_volume.c n
  let Cn : NNReal := Tube.volume_le.C n
  let c : ENNReal := (cn : ENNReal)
  let C : ENNReal := (Cn : ENNReal)
  let ratio : ENNReal := ((Cn / cn : NNReal) : ENNReal)
  let t := fibreIndex s T δ ρ i₀
  let u := fibreIndex s T δ ρ' i₀
  let W := fibreBodies T σ
  let K := ((T i₀).rescale (2 * ρ)).toConvexSpaceBody
  let K' := ((T i₀).rescale (2 * ρ')).toConvexSpaceBody
  let V : ENNReal := volume K.carrier
  let V' : ENNReal := volume K'.carrier
  let vlo : ENNReal := c * (σ : ENNReal) ^ p
  let vhi : ENNReal := C * (σ : ENNReal) ^ p
  have hσ : 0 < σ := lt_of_lt_of_le hδ hδσ
  have hρ' : 0 < ρ' := lt_of_lt_of_le (lt_of_lt_of_le hσ hσρ) hρρ'
  have hσρ' : σ ≤ ρ' := hσρ.trans hρρ'
  have htK : ∀ i ∈ t, W i ≤ K := fun _ hi => fibreBodies_le_double_anchor hδσ hσρ hi
  have huK' : ∀ i ∈ u, W i ≤ K' := fun _ hi => fibreBodies_le_double_anchor hδσ hσρ' hi
  have hvolW_pos : 0 < volume (W i₀).carrier := volume_fibreBodies_pos hσ i₀
  have hi₀t : i₀ ∈ t := mem_fibreIndex_self (hδσ.trans hσρ) hi₀
  have hi₀u : i₀ ∈ u := mem_fibreIndex_self (hδσ.trans hσρ') hi₀
  have hdt : 0 < Kakeya.densityIn t W K :=
    (Kakeya.densityIn_pos_iff _ _ _).mpr ⟨i₀, hi₀t, hvolW_pos, htK i₀ hi₀t⟩
  have hdu : 0 < Kakeya.densityIn u W K' :=
    (Kakeya.densityIn_pos_iff _ _ _).mpr ⟨i₀, hi₀u, hvolW_pos, huK' i₀ hi₀u⟩
  have hcn_ne : cn ≠ 0 := (Tube.le_volume.c_pos n).ne'
  have hratio_ne0 : ratio ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (div_ne_zero (Tube.volume_le.C_pos n).ne' hcn_ne)
  by_cases hA : A = ⊤
  · rw [hA]
    have hCFu_ne0 : ConvexSpaceBody.frostmanConstant u W K' ≠ 0 :=
      (zero_lt_one.trans_le (ConvexSpaceBody.IsFrostmanIn.one_le
        ConvexSpaceBody.isFrostmanIn_frostmanConstant hdu)).ne'
    calc ConvexSpaceBody.frostmanConstant t W K ≤ ⊤ := le_top
      _ = ⊤ * ratio * ConvexSpaceBody.frostmanConstant u W K' := by
        simp [ENNReal.top_mul, hratio_ne0, hCFu_ne0]
  · have hcast : ∀ x : NNReal, ((x * σ ^ p : NNReal) : ENNReal)
        = (x : ENNReal) * (σ : ENNReal) ^ p := fun x => by push_cast; ring
    have hfam_t : Kakeya.familyIn t W K = t := Finset.filter_eq_self.mpr htK
    have hfam_u : Kakeya.familyIn u W K' = u := Finset.filter_eq_self.mpr huK'
    have hband1 : Kakeya.densityIn u W K' * V' ≤ (u.card : ENNReal) * vhi := by
      have h := densityIn_mul_le_of_volume_band u W K' (vhi := vhi) (vlo := V')
        (fun i _ => (Tube.volume_le hσ1 ((T i).rescale σ)).trans_eq (hcast Cn))
        (le_rfl : V' ≤ volume K'.carrier)
      rwa [hfam_u] at h
    have hband2 : (t.card : ENNReal) * vlo ≤ Kakeya.densityIn t W K * V := by
      have h := le_densityIn_mul_of_volume_band t W K (vlo := vlo) (vhi := V)
        (fun i _ => (hcast cn).symm.trans_le (Tube.le_volume ((T i).rescale σ)))
        (le_rfl : volume K.carrier ≤ V)
      rwa [hfam_t] at h
    have hV_le_V' : V ≤ V' :=
      measure_mono (SetLike.coe_subset_coe.mpr (Tube.rescale_le_rescale_of_radius_le (T i₀)
        (by gcongr : (2 : NNReal) * ρ ≤ 2 * ρ')))
    have hband : Kakeya.densityIn u W K' ≤ A * ratio * Kakeya.densityIn t W K :=
      (ENNReal.mul_le_mul_iff_left
          (volume_fibreBodies_pos (σ := 2 * ρ')
            (mul_pos (by norm_num : (0 : NNReal) < 2) hρ') i₀).ne'
          K'.isCompact'.measure_ne_top).mp
        (block_band_algebra (c := c) (S := (σ : ENNReal) ^ p) (ratio := ratio)
          (by
            rw [show ratio * c = C from by
              rw [← ENNReal.coe_mul, ENNReal.coe_inj]; field_simp [hcn_ne]]
            exact hband1)
          hcard hband2 hV_le_V')
    exact (one_mul _).symm.trans_le (frostmanConstant_le_of_densityIn_band
      (ι' := ι) (t := t) (u := u) (W := W) (K := K) (K' := K') (a := 1) (b := A * ratio)
      (fibreIndex_subset_of_anchor_le (σ := δ) hρρ' i₀) htK huK'
      zero_lt_one ENNReal.one_ne_top (ENNReal.mul_ne_top hA ENNReal.coe_ne_top)
      hdt hdu ((one_mul _).trans_le hband))

omit [Nontrivial E] in
/-- **Inflating the anchor body multiplies the Frostman constant by the volume ratio.**  If every
member of the family lies in *both* test bodies, the numerators of `Δ(·,K)` and `Δ(·,K')` agree, so
the two densities are in inverse proportion to the volumes and the Frostman constants in direct
proportion.  The statement is symmetric in `K` and `K'`; at `r = 1` it gives free monotonicity. -/
theorem frostmanConstant_mono_anchor {ι : Type*} {t : Finset ι} {W : ι → ConvexSpaceBody E}
    {K K' : ConvexSpaceBody E} {r : ENNReal} (hmem : ∀ i ∈ t, W i ≤ K)
    (hmem' : ∀ i ∈ t, W i ≤ K')
    (hvol : volume K'.carrier ≤ r * volume K.carrier) (_hr : r ≠ ⊤) :
    ConvexSpaceBody.frostmanConstant t W K' ≤ r * ConvexSpaceBody.frostmanConstant t W K := by
  classical
  set C := ConvexSpaceBody.frostmanConstant t W K
  by_cases hK : volume K.carrier = 0
  · exact ConvexSpaceBody.frostmanConstant_le_of_isFrostmanIn
      (ConvexSpaceBody.IsFrostmanIn.of_volume_eq_zero (s := t) (W := W) (K := K')
        (C := r * C) (by simpa [hK] using hvol))
  · have hd' : Kakeya.densityIn t W K ≤ r * Kakeya.densityIn t W K' := by
      rw [← ENNReal.mul_le_mul_iff_left (c := volume K.carrier) hK K.isCompact.measure_ne_top]
      calc Kakeya.densityIn t W K * volume K.carrier
            = Kakeya.densityIn t W K' * volume K'.carrier :=
            (Kakeya.sum_volume_eq_densityIn_mul_volume' hmem).symm.trans
              (Kakeya.sum_volume_eq_densityIn_mul_volume' hmem')
        _ ≤ Kakeya.densityIn t W K' * (r * volume K.carrier) := mul_le_mul_right hvol _
        _ = (r * Kakeya.densityIn t W K') * volume K.carrier := by
            rw [← mul_assoc, mul_comm (Kakeya.densityIn t W K') r]
    have hmax' : maxDensity t W ≤ (r * C) * Kakeya.densityIn t W K' :=
      calc maxDensity t W ≤ C * Kakeya.densityIn t W K :=
            ConvexSpaceBody.IsFrostmanIn.maxDensity_le_of_carrier_subset
              ConvexSpaceBody.isFrostmanIn_frostmanConstant hmem
        _ ≤ C * (r * Kakeya.densityIn t W K') := mul_le_mul_right hd' C
        _ = (r * C) * Kakeya.densityIn t W K' := by rw [← mul_assoc, mul_comm C r]
    exact ConvexSpaceBody.frostmanConstant_le_of_isFrostmanIn
      (ConvexSpaceBody.IsFrostmanIn.of_maxDensity_le hmax')

end MultiScaleFac

end Kakeya
