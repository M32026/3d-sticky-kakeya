import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12
import MyLeanRepo.Kakeya.Assouad.TubeVolumeRatio
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.FrostmanTransfer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZBridge
import MyLeanRepo.Kakeya.Streamlined.Families
import MyLeanRepo.Kakeya.Streamlined.Targets.StickyImpliesGeneral
import Mathlib.Tactic

/-!
# Grid Frostman transfer

Frostman transfer for the shifted-copy grid family (far-range case Aρ ≥ 1/2).

The grid tubes are at scale `2*A*ρ`, which is larger than the A-dilated carrier
of the parent GWZ tube (at scale `A*ρ`). Unlike the tiling case, grid tubes are
NOT contained in the A-dilated carrier. We use a convexity-intersection argument
to extend the Frostman bound from the A-dilated carrier to the grid tube carrier,
losing a constant factor in the volume ratio.

## Key results

1. `frostman_extension_concrete_no_sub`: extends a Frostman bound from `Tρ` to `Tσ`
   without requiring `Tρ ⊆ Tσ`; only requires all bodies to lie in both sets.
2. `grid_tube_volume_ratio`: `deltaTubeVolume (2*A*ρ) ≤ 20 * A^3 * deltaTubeVolume ρ`
   for `A ≥ 1` and `0 < ρ ≤ 1`.
3. `gwz_grid_tile_frostman_transfer_single`: transfers Frostman from a GWZ A-fiber
   to a strict subfiber inside a grid tube, with constant degraded by the volume ratio.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

open Kakeya.Streamlined Metric MeasureTheory Set

/--
Frostman extension without ambient containment.

If `F` satisfies the concrete Frostman bound in `Tρ`, all bodies are in both
`Tρ` and `Tσ`, `Tρ` is convex, and `volume Tσ ≤ R * volume Tρ`, then `F`
satisfies the bound with constant `C * R` in `Tσ`.

Unlike `frostman_extension_concrete`, this does NOT require `Tρ ⊆ Tσ`.
-/
lemma frostman_extension_concrete_no_sub
    {F : Kakeya.Streamlined.BodyFamily} {Tρ Tσ : Set Point3} {C R : ENNReal}
    (hFrost : ∀ (K : Set Point3), Convex ℝ K → K ⊆ Tρ →
      F.containedMass K * volume Tρ ≤ C * F.containedMass Tρ * volume K)
    (h_contained_Tρ : ∀ i, (F.body i).carrier ⊆ Tρ)
    (h_contained_Tσ : ∀ i, (F.body i).carrier ⊆ Tσ)
    (hTρ_conv : Convex ℝ Tρ)
    (h_vol_ratio : volume Tσ ≤ R * volume Tρ) :
    ∀ (K : Set Point3), Convex ℝ K → K ⊆ Tσ →
      F.containedMass K * volume Tσ ≤ (C * R) * F.containedMass Tσ * volume K := by
  have h_indices_Tρ : F.containedIndices Tρ = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro i
    simp only [Kakeya.Streamlined.BodyFamily.containedIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    exact h_contained_Tρ i
  have h_indices_Tσ : F.containedIndices Tσ = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro i
    simp only [Kakeya.Streamlined.BodyFamily.containedIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    exact h_contained_Tσ i
  have h_mass_eq : F.containedMass Tσ = F.containedMass Tρ := by
    simp only [Kakeya.Streamlined.BodyFamily.containedMass, h_indices_Tσ, h_indices_Tρ]
  intro K hK_conv hK_sub
  let K' := K ∩ Tρ
  have hK'_conv : Convex ℝ K' := hK_conv.inter hTρ_conv
  have hK'_sub : K' ⊆ Tρ := Set.inter_subset_right
  have h_indices_K : F.containedIndices K = F.containedIndices K' := by
    ext i
    simp only [Kakeya.Streamlined.BodyFamily.containedIndices, Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun x hx => ⟨h2 hx, h_contained_Tρ i hx⟩⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun x hx => (h2 hx).1⟩
  have h_mass_K : F.containedMass K = F.containedMass K' := by
    simp only [Kakeya.Streamlined.BodyFamily.containedMass, h_indices_K]
  have h_frost_K' := hFrost K' hK'_conv hK'_sub
  have h_vol_K' : volume K' ≤ volume K := measure_mono (Set.inter_subset_left)
  have h_goal : F.containedMass K * volume Tσ ≤ (C * R) * F.containedMass Tσ * volume K := by
    rw [h_mass_K]
    calc
      F.containedMass K' * volume Tσ
          ≤ F.containedMass K' * (R * volume Tρ) := by gcongr
      _ = R * (F.containedMass K' * volume Tρ) := by ring
      _ ≤ R * (C * F.containedMass Tρ * volume K') := by gcongr
      _ ≤ R * (C * F.containedMass Tρ * volume K) := by gcongr
      _ = (C * R) * F.containedMass Tσ * volume K := by
        rw [h_mass_eq] <;> ring
  exact h_goal

/--
Volume ratio bound for grid tubes:
`deltaTubeVolume (2*A*ρ) ≤ 20 * A^3 * deltaTubeVolume ρ`
for `A ≥ 1` and `0 < ρ ≤ 1`.
-/
lemma grid_tube_volume_ratio {A ρ : ℝ} (hA : 1 ≤ A) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    Kakeya.deltaTubeVolume (2 * A * ρ) ≤
      (20 : ENNReal) * ENNReal.ofReal (A ^ 3) * Kakeya.deltaTubeVolume ρ := by
  have hσ_pos : 0 < 2 * A * ρ := by positivity
  have h_upper : Kakeya.deltaTubeVolume (2 * A * ρ) ≤
      ENNReal.ofReal (Real.pi * (2 * A * ρ)^2 * (1 + 2 * (2 * A * ρ))) :=
    deltaTubeVolume_upper_pi hσ_pos
  have h_lower : ENNReal.ofReal (Real.pi * ρ^2) ≤ Kakeya.deltaTubeVolume ρ :=
    deltaTubeVolume_lower_pi hρ
  have h_real_ineq : Real.pi * (2 * A * ρ)^2 * (1 + 2 * (2 * A * ρ)) ≤
      20 * A^3 * Real.pi * ρ^2 := by
    have h1 : 0 < Real.pi := Real.pi_pos
    have h2 : 0 < ρ^2 := by positivity
    have h3 : 0 < A^3 := by positivity
    have h4 : 4 * A^2 * (1 + 4 * A * ρ) ≤ 20 * A^3 := by
      nlinarith [sq_nonneg (A - 1), sq_nonneg (ρ - 1), hA, hρ1]
    have h5 : Real.pi * (2 * A * ρ)^2 * (1 + 2 * (2 * A * ρ)) =
        Real.pi * ρ^2 * (4 * A^2 * (1 + 4 * A * ρ)) := by ring
    rw [h5]
    have h6 : Real.pi * ρ^2 * (4 * A^2 * (1 + 4 * A * ρ)) ≤
        Real.pi * ρ^2 * (20 * A^3) := by gcongr
    linarith
  have h6 : ENNReal.ofReal (Real.pi * (2 * A * ρ)^2 * (1 + 2 * (2 * A * ρ))) ≤
      ENNReal.ofReal (20 * A^3 * Real.pi * ρ^2) :=
    ENNReal.ofReal_mono h_real_ineq
  have h_pos1 : 0 ≤ (20 : ℝ) := by norm_num
  have h_pos2 : 0 ≤ A^3 := by positivity
  have h_pos3 : 0 ≤ Real.pi * ρ^2 := by positivity
  have h7a : ENNReal.ofReal (20 * A^3 * Real.pi * ρ^2) =
      ENNReal.ofReal (20 : ℝ) * ENNReal.ofReal (A^3 * Real.pi * ρ^2) := by
    rw [← ENNReal.ofReal_mul h_pos1] <;> ring
  have h7b : ENNReal.ofReal (A^3 * Real.pi * ρ^2) =
      ENNReal.ofReal (A^3) * ENNReal.ofReal (Real.pi * ρ^2) := by
    rw [← ENNReal.ofReal_mul h_pos2] <;> ring
  have h7 : ENNReal.ofReal (20 * A^3 * Real.pi * ρ^2) =
      (20 : ENNReal) * ENNReal.ofReal (A^3) * ENNReal.ofReal (Real.pi * ρ^2) := by
    rw [h7a, h7b] <;> simp [mul_assoc] <;> ring
  calc
    Kakeya.deltaTubeVolume (2 * A * ρ)
      ≤ ENNReal.ofReal (Real.pi * (2 * A * ρ)^2 * (1 + 2 * (2 * A * ρ))) := h_upper
    _ ≤ ENNReal.ofReal (20 * A^3 * Real.pi * ρ^2) := h6
    _ = (20 : ENNReal) * ENNReal.ofReal (A^3) * ENNReal.ofReal (Real.pi * ρ^2) := h7
    _ ≤ (20 : ENNReal) * ENNReal.ofReal (A^3) * Kakeya.deltaTubeVolume ρ := by gcongr

/--
Transfer Frostman from a GWZ A-fiber to a strict subfiber inside a grid tube.

The grid tube is at scale `2*A*ρ` and is NOT contained in the A-dilated carrier.
We use the convexity-intersection extension with a volume ratio factor of 20.

Given:
- `S_strict ⊆ fullFiberIndices parent`
- All strict bodies are in the grid tube
- `S_strict` retains at least `threshold` fraction of the full fiber mass

Output: Frostman bound for the strict subfiber with ambient = grid tube carrier,
at constant `20 * C'`.
-/
lemma gwz_grid_tile_frostman_transfer_single
    {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    {A : ℝ} (hA : 1 ≤ A)
    {C_in C' threshold : ENNReal}
    {fine : Kakeya.Streamlined.TubeFamily δ}
    {gwzScale : Kakeya.Streamlined.AdmissibleScale δ}
    (hρ_eq : gwzScale.1 = ρ)
    (scaleData : PureWZ2GWZScaleData (A := A) fine gwzScale C_in)
    (parent : Fin scaleData.coarse.card)
    (gridTube : Kakeya.DeltaTube (2 * A * ρ))
    (S_strict : Finset (Fin fine.card))
    (hS : S_strict ⊆ scaleData.fullFiberIndices parent)
    (hBodiesInGrid : ∀ i ∈ S_strict, (fine.tube i).carrier ⊆ gridTube.carrier)
    (hSubstantial : (S_strict.card : ENNReal) ≥
      threshold * (scaleData.fullFiberIndices parent).card)
    (hC : C_in ≤ C' * threshold) :
    ∀ (K : Set Point3), Convex ℝ K → K ⊆ gridTube.carrier →
      (Kakeya.Streamlined.TubeSubfamily.fromFinset fine S_strict).family.toBodyFamily.containedMass K *
      volume gridTube.carrier ≤
      (20 * C') * (Kakeya.Streamlined.TubeSubfamily.fromFinset fine S_strict).family.toBodyFamily.mass *
      volume K := by
  let S_full := scaleData.fullFiberIndices parent
  let ACarrier : Set Point3 :=
    wz2PaperCenteredDilatedCarrier A (scaleData.coarse.tube parent)
  let strict_sub := Kakeya.Streamlined.TubeSubfamily.fromFinset fine S_strict
  let full_sub := Kakeya.Streamlined.TubeSubfamily.fromFinset fine S_full

  -- Injection from strict to full
  have h_surj : ∀ (s : Finset (Fin fine.card)) (x : Fin fine.card), x ∈ s →
      ∃ (y : Fin s.card), (s.orderEmbOfFin rfl).toEmbedding y = x := by
    intro s x hx
    have h_in_sort : x ∈ s.sort := by rw [Finset.mem_sort] <;> exact hx
    rcases List.mem_iff_get.mp h_in_sort with ⟨i, hi⟩
    have h_len : (s.sort).length = s.card :=
      Finset.length_sort fun a b => a ≤ b
    let y : Fin s.card := Fin.cast h_len i
    refine ⟨y, ?_⟩
    simpa [Finset.orderEmbOfFin_apply, y, Fin.cast] using hi
  have h_emb_in : ∀ (s : Finset (Fin fine.card)) (i : Fin s.card),
      (s.orderEmbOfFin rfl).toEmbedding i ∈ s := by
    intro s i
    exact Finset.orderEmbOfFin_mem s rfl i
  have h_in_range : ∀ (i : Fin strict_sub.family.card),
      ∃ (y : Fin full_sub.family.card), full_sub.embedding y = strict_sub.embedding i := by
    intro i
    have h1 : strict_sub.embedding i ∈ S_strict := h_emb_in S_strict i
    have h2 : strict_sub.embedding i ∈ S_full := hS h1
    exact h_surj S_full (strict_sub.embedding i) h2
  let f_toFun : Fin strict_sub.family.card → Fin full_sub.family.card := fun i =>
    Classical.choose (h_in_range i)
  have h_spec : ∀ i, full_sub.embedding (f_toFun i) = strict_sub.embedding i := by
    intro i
    exact Classical.choose_spec (h_in_range i)
  have f_inj : Function.Injective f_toFun := by
    intro i1 i2 h
    have h4 : full_sub.embedding (f_toFun i1) = full_sub.embedding (f_toFun i2) := by rw [h]
    have h5 : strict_sub.embedding i1 = strict_sub.embedding i2 := by
      rw [←h_spec i1, ←h_spec i2, h4]
    exact strict_sub.embedding.injective h5
  let f : Fin strict_sub.family.card ↪ Fin full_sub.family.card :=
    ⟨f_toFun, f_inj⟩

  have h_eq_body : ∀ (i : Fin strict_sub.family.toBodyFamily.card),
      strict_sub.family.toBodyFamily.body i =
      full_sub.family.toBodyFamily.body (f i) := by
    intro i
    have h1 : strict_sub.family.tube i = fine.tube (strict_sub.embedding i) :=
      strict_sub.tube_eq i
    have h2 : full_sub.family.tube (f i) = fine.tube (full_sub.embedding (f i)) :=
      full_sub.tube_eq (f i)
    have h3 : full_sub.embedding (f i) = strict_sub.embedding i := h_spec i
    have h4 : strict_sub.family.toBodyFamily.body i =
        Kakeya.Streamlined.tubeBody (strict_sub.family.tube i) := by rfl
    have h5 : full_sub.family.toBodyFamily.body (f i) =
        Kakeya.Streamlined.tubeBody (full_sub.family.tube (f i)) := by rfl
    rw [h4, h5, h1, h2, h3]

  -- Mass ratio
  have h_vol : ∀ (t : Kakeya.DeltaTube δ),
      (Kakeya.Streamlined.tubeBody t).volume = Kakeya.deltaTubeVolume δ := by
    intro t
    exact deltaTube_volume_eq t
  have h_mass_strict : strict_sub.family.toBodyFamily.mass =
      (S_strict.card : ENNReal) * Kakeya.deltaTubeVolume δ := by
    have h : ∀ i, (strict_sub.family.toBodyFamily.body i).volume = Kakeya.deltaTubeVolume δ := by
      intro i; exact h_vol (strict_sub.family.tube i)
    have h_sum : strict_sub.family.toBodyFamily.mass =
        ∑ i : Fin strict_sub.family.card, Kakeya.deltaTubeVolume δ := by
      simp [Kakeya.Streamlined.BodyFamily.mass, h] <;> rfl
    rw [h_sum]
    simp [Finset.sum_const] <;> norm_cast
  have h_mass_full : full_sub.family.toBodyFamily.mass =
      (S_full.card : ENNReal) * Kakeya.deltaTubeVolume δ := by
    have h : ∀ i, (full_sub.family.toBodyFamily.body i).volume = Kakeya.deltaTubeVolume δ := by
      intro i; exact h_vol (full_sub.family.tube i)
    have h_sum : full_sub.family.toBodyFamily.mass =
        ∑ i : Fin full_sub.family.card, Kakeya.deltaTubeVolume δ := by
      simp [Kakeya.Streamlined.BodyFamily.mass, h] <;> rfl
    rw [h_sum]
    simp [Finset.sum_const] <;> norm_cast
  have h_mass_ratio : strict_sub.family.toBodyFamily.mass ≥
      threshold * full_sub.family.toBodyFamily.mass := by
    rw [h_mass_strict, h_mass_full]
    have h' : (S_strict.card : ENNReal) ≥ threshold * (S_full.card : ENNReal) := hSubstantial
    have h'' : (S_strict.card : ENNReal) * Kakeya.deltaTubeVolume δ ≥
        (threshold * (S_full.card : ENNReal)) * Kakeya.deltaTubeVolume δ := by
      exact mul_le_mul_of_nonneg_right h' (by positivity)
    simpa [mul_assoc] using h''

  -- Frostman on full body from scaleData
  have hfrost_full : ∀ (K : Set Point3), Convex ℝ K → K ⊆ ACarrier →
      full_sub.family.toBodyFamily.containedMass K * volume ACarrier ≤
      C_in * full_sub.family.toBodyFamily.mass * volume K :=
    scaleData.full_fiber_frostman parent

  -- Transfer to strict (constant C')
  have hfrost_strict := frostman_transfer_to_strict_subfiber
    (f := f) (h_eq := h_eq_body) threshold C_in C' hC h_mass_ratio ACarrier hfrost_full

  -- All strict bodies are in ACarrier (from full fiber definition)
  have hBodiesInACarrier : ∀ (i : Fin strict_sub.family.toBodyFamily.card),
      (strict_sub.family.toBodyFamily.body i).carrier ⊆ ACarrier := by
    intro i
    have h1 : strict_sub.embedding i ∈ S_strict := h_emb_in S_strict i
    have h2 : strict_sub.embedding i ∈ S_full := hS h1
    have h3 : (fine.tube (strict_sub.embedding i)).carrier ⊆ ACarrier := by
      have h4 : strict_sub.embedding i ∈ scaleData.fullFiberIndices parent := h2
      have h5 : strict_sub.embedding i ∈
          Finset.univ.filter (fun index =>
            (fine.tube index).carrier ⊆ ACarrier) := by
        have h_eq := scaleData.fullFiberIndices_eq parent
        rwa [h_eq] at h4
      simpa using h5
    have h4 : (strict_sub.family.toBodyFamily.body i).carrier =
        (strict_sub.family.tube i).carrier := by rfl
    have h5 : (strict_sub.family.tube i).carrier =
        (fine.tube (strict_sub.embedding i)).carrier := by
      exact congr_arg (fun (t : Kakeya.DeltaTube δ) => t.carrier) (strict_sub.tube_eq i)
    rw [h4, h5]
    exact h3

  -- All strict bodies are in grid tube
  have hBodiesInGrid' : ∀ (i : Fin strict_sub.family.toBodyFamily.card),
      (strict_sub.family.toBodyFamily.body i).carrier ⊆ gridTube.carrier := by
    intro i
    have h1 : strict_sub.embedding i ∈ S_strict := h_emb_in S_strict i
    have h2 := hBodiesInGrid (strict_sub.embedding i) h1
    have h3 : (strict_sub.family.toBodyFamily.body i).carrier =
        (strict_sub.family.tube i).carrier := by rfl
    have h4 : (strict_sub.family.tube i).carrier =
        (fine.tube (strict_sub.embedding i)).carrier := by
      exact congr_arg (fun (t : Kakeya.DeltaTube δ) => t.carrier) (strict_sub.tube_eq i)
    rw [h3, h4]
    exact h2

  -- ACarrier is convex (homothety image of convex tube carrier)
  have hACarrier_conv : Convex ℝ ACarrier :=
    Convex.affine_image (AffineMap.homothety (wz2PaperTubeMidpoint (scaleData.coarse.tube parent)) A)
      (wz2_paper_ordinary_tube_carrier_convex (scaleData.coarse.tube parent))

  -- Volume ratio: volume(gridTube) ≤ 20 * volume(ACarrier)
  have hVolRatio : volume gridTube.carrier ≤
      (20 : ENNReal) * volume ACarrier := by
    have h1 : volume gridTube.carrier = Kakeya.deltaTubeVolume (2 * A * ρ) :=
      deltaTube_volume_eq gridTube
    have h2 : volume ACarrier =
        ENNReal.ofReal (A ^ 3) * volume (scaleData.coarse.tube parent).carrier := by
      rw [wz2_paper_centeredDilatedCarrier_volume (scaleData.coarse.tube parent)]
      have h_abs : |A| = A := abs_of_nonneg (by linarith)
      rw [h_abs] <;> rfl
    have h3 : volume (scaleData.coarse.tube parent).carrier = Kakeya.deltaTubeVolume ρ := by
      have h31 : (scaleData.coarse.tube parent).volume = Kakeya.deltaTubeVolume gwzScale.1 :=
        deltaTube_volume_eq (scaleData.coarse.tube parent)
      have h32 : volume (scaleData.coarse.tube parent).carrier = (scaleData.coarse.tube parent).volume := by rfl
      rw [h32, h31]
      congr <;> exact hρ_eq
    rw [h1, h2, h3]
    have h4 : (20 : ENNReal) * (ENNReal.ofReal (A ^ 3) * Kakeya.deltaTubeVolume ρ) =
        (20 : ENNReal) * ENNReal.ofReal (A ^ 3) * Kakeya.deltaTubeVolume ρ := by
      simp [mul_assoc]
    rw [h4]
    exact grid_tube_volume_ratio hA hρ hρ1

  -- Mass equality: strict_sub.mass = strict_sub.containedMass ACarrier
  have h_mass_ACarrier : strict_sub.family.toBodyFamily.containedMass ACarrier =
      strict_sub.family.toBodyFamily.mass := by
    have h_indices : strict_sub.family.toBodyFamily.containedIndices ACarrier = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro i
      simp only [Kakeya.Streamlined.BodyFamily.containedIndices, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hBodiesInACarrier i
    have h : strict_sub.family.toBodyFamily.containedMass ACarrier =
        ∑ i : Fin strict_sub.family.toBodyFamily.card, (strict_sub.family.toBodyFamily.body i).volume := by
      rw [Kakeya.Streamlined.BodyFamily.containedMass, h_indices]
      <;> rfl
    rw [h]
    <;> rfl

  -- Convert hfrost_strict to use containedMass ACarrier instead of mass
  have hfrost_strict' : ∀ (K : Set Point3), Convex ℝ K → K ⊆ ACarrier →
      strict_sub.family.toBodyFamily.containedMass K * volume ACarrier ≤
      C' * strict_sub.family.toBodyFamily.containedMass ACarrier * volume K := by
    intro K hK hK_sub
    have h := hfrost_strict K hK hK_sub
    rw [h_mass_ACarrier] at *
    exact h

  -- Extend Frostman from ACarrier to grid tube carrier
  have h_extended := frostman_extension_concrete_no_sub
    (F := strict_sub.family.toBodyFamily)
    (Tρ := ACarrier)
    (Tσ := gridTube.carrier)
    (C := C')
    (R := (20 : ENNReal))
    hfrost_strict'
    hBodiesInACarrier
    hBodiesInGrid'
    hACarrier_conv
    hVolRatio

  -- containedMass gridTube.carrier = mass (all bodies in grid tube)
  have h_mass_grid : strict_sub.family.toBodyFamily.containedMass gridTube.carrier =
      strict_sub.family.toBodyFamily.mass := by
    have h_indices : strict_sub.family.toBodyFamily.containedIndices gridTube.carrier = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro i
      simp only [Kakeya.Streamlined.BodyFamily.containedIndices, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hBodiesInGrid' i
    have h : strict_sub.family.toBodyFamily.containedMass gridTube.carrier =
        ∑ i : Fin strict_sub.family.toBodyFamily.card, (strict_sub.family.toBodyFamily.body i).volume := by
      rw [Kakeya.Streamlined.BodyFamily.containedMass, h_indices] <;> rfl
    rw [h] <;> rfl

  intro K hK hK_sub
  have h := h_extended K hK hK_sub
  rw [h_mass_grid] at h
  have h_comm : (C' * (20 : ENNReal)) = (20 * C' : ENNReal) := by ring
  rw [h_comm] at h
  exact h

end Kakeya.Assouad
