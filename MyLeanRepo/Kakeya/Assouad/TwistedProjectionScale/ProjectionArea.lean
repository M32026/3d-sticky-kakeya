import MyLeanRepo.Kakeya.Assouad.Definitions
import Mathlib.Tactic

/-!
# Projection area lower bound

For a set B ⊆ ℝ² with y-diameter ≤ 2δ, the length of the image under
φ(x,y) = x + c*y is at least area(B)/(4δ).

Uses an area-preserving shear T(x,y) = (x+cy, y) and Fubini's theorem.
-/

noncomputable section

open MeasureTheory Set

namespace Kakeya.Assouad

/-- 2D lemma: if B ⊆ ℝ² has y-diameter ≤ 2δ, then
the length of the image under φ(x,y) = x + c*y is at least area(B)/(4δ). -/
lemma image_linear_functional_length_lower
    {δ c : ℝ} (hδ : 0 < δ)
    {B : Set (ℝ × ℝ)} (hB_meas : MeasurableSet B)
    (h_y_diam : ∀ (y1 y2 : ℝ), (∃ x1 x2 : ℝ, (x1, y1) ∈ B ∧ (x2, y2) ∈ B) → |y1 - y2| ≤ 2 * δ) :
    volume ((fun p : ℝ × ℝ => p.1 + c * p.2) '' B) ≥ volume B / ENNReal.ofReal (4 * δ) := by
  let φ : (ℝ × ℝ) → ℝ := fun p => p.1 + c * p.2
  let T : (ℝ × ℝ) → (ℝ × ℝ) := fun p => (p.1 + c * p.2, p.2)
  let T_inv : (ℝ × ℝ) → (ℝ × ℝ) := fun p => (p.1 - c * p.2, p.2)
  -- T as homeomorphism
  have hT_cont : Continuous T := by continuity
  have hT_inv_cont : Continuous T_inv := by continuity
  let T_homeo : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) :=
    { toFun := T
      invFun := T_inv
      left_inv := by
        intro p
        simp [T, T_inv, Prod.ext_iff] <;> constructor <;> ring
      right_inv := by
        intro p
        simp [T, T_inv, Prod.ext_iff] <;> constructor <;> ring
      continuous_toFun := hT_cont
      continuous_invFun := hT_inv_cont }
  let T_measEquiv : MeasurableEquiv (ℝ × ℝ) (ℝ × ℝ) :=
    T_homeo.toMeasurableEquiv
  have hT_meas : Measurable T := T_homeo.continuous.measurable
  have hTB_meas : MeasurableSet (T '' B) :=
    T_measEquiv.measurableSet_image.mpr hB_meas
  -- T is volume-preserving via matrix determinant
  let shearMat : Matrix (Fin 2) (Fin 2) ℝ := !![1, c; 0, 1]
  let T_lin : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) := shearMat.toLin'
  have h_det : LinearMap.det T_lin = 1 := by
    rw [LinearMap.det_toLin' shearMat]
    simp [shearMat, Matrix.det_fin_two] <;> ring
  have h_ne : LinearMap.det T_lin ≠ 0 := by
    rw [h_det] <;> norm_num
  have h_map : Measure.map T_lin volume = volume := by
    rw [Real.map_linearMap_volume_pi_eq_smul_volume_pi h_ne]
    rw [h_det] <;> simp
  have hT_lin_cont : Continuous T_lin := by
    exact LinearMap.continuous_on_pi T_lin
  have hT_lin_mp : MeasurePreserving T_lin volume volume :=
    ⟨hT_lin_cont.measurable, h_map⟩
  let e : (Fin 2 → ℝ) → (ℝ × ℝ) := fun q => (q 0, q 1)
  have h_e_mp : MeasurePreserving e volume volume := measurePreserving_finTwoArrow volume
  let e' : (ℝ × ℝ) → (Fin 2 → ℝ) := fun p => ![p.1, p.2]
  have h_e'_mp : MeasurePreserving e' volume volume := (measurePreserving_finTwoArrow volume).symm
  have h_comm : T = e ∘ T_lin ∘ e' := by
    funext p
    apply Prod.ext
    · simp [T, e, e', T_lin, shearMat, Matrix.toLin'_apply, Fin.sum_univ_two] <;> ring
    · simp [T, e, e', T_lin, shearMat, Matrix.toLin'_apply, Fin.sum_univ_two] <;> ring
  have hT_mp : MeasurePreserving T volume volume := by
    rw [h_comm]
    exact h_e_mp.comp (hT_lin_mp.comp h_e'_mp)
  have h_inj : Function.Injective T := T_homeo.injective
  have h_eq_vol : volume (T '' B) = volume B := by
    have h1 : Measure.map T volume = volume := hT_mp.map_eq
    have h2 : volume (T '' B) = Measure.map T volume (T '' B) := by rw [h1]
    rw [h2, Measure.map_apply hT_meas hTB_meas]
    have h3 : T ⁻¹' (T '' B) = B := by
      ext x
      simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · rintro ⟨z, hz, h_eq⟩
        have h4 : z = x := h_inj h_eq
        rw [h4] at hz
        exact hz
      · intro hx
        exact ⟨x, hx, rfl⟩
    rw [h3]
  -- y-projection of B (and T(B), since T preserves y)
  let C : Set ℝ := Prod.snd '' B
  have hC_diam : ∀ y1 ∈ C, ∀ y2 ∈ C, |y1 - y2| ≤ 2 * δ := by
    intro y1 hy1 y2 hy2
    rcases hy1 with ⟨p1, hp1, rfl⟩
    rcases hy2 with ⟨p2, hp2, rfl⟩
    exact h_y_diam p1.2 p2.2 ⟨p1.1, p2.1, hp1, hp2⟩
  -- Slice function
  let g : ℝ → ENNReal := fun x => volume {y : ℝ | (x, y) ∈ T '' B}
  have hg_meas : Measurable g := measurable_measure_prodMk_left hTB_meas
  -- Each slice has volume ≤ 4δ
  have h_slice_bound : ∀ (x : ℝ), g x ≤ ENNReal.ofReal (4 * δ) := by
    intro x
    let S_x : Set ℝ := {y | (x, y) ∈ T '' B}
    have h_sub : S_x ⊆ C := by
      intro y hy
      rcases hy with ⟨p, hp, hpy⟩
      exact ⟨p, hp, congr_arg Prod.snd hpy⟩
    by_cases h_empty : S_x = ∅
    · have h_goal : g x = 0 := by
        dsimp only [g]
        have h_eq : {y : ℝ | (x, y) ∈ T '' B} = ∅ := by
          exact h_empty
        rw [h_eq] <;> simp
      rw [h_goal] <;> positivity
    · have h_nonempty : S_x.Nonempty := Set.nonempty_iff_ne_empty.mpr h_empty
      rcases h_nonempty with ⟨y0, hy0⟩
      have h_y0_in_C : y0 ∈ C := h_sub hy0
      have h_interval : S_x ⊆ Set.Icc (y0 - 2 * δ) (y0 + 2 * δ) := by
        intro y hy
        have h_y_in_C : y ∈ C := h_sub hy
        have h4 : |y - y0| ≤ 2 * δ := hC_diam y h_y_in_C y0 h_y0_in_C
        have h5 : -(2 * δ) ≤ y - y0 := (abs_le.mp h4).1
        have h6 : y - y0 ≤ 2 * δ := (abs_le.mp h4).2
        exact ⟨by linarith, by linarith⟩
      have h_goal : g x ≤ ENNReal.ofReal (4 * δ) := by
        dsimp only [g]
        calc volume S_x
          ≤ volume (Set.Icc (y0 - 2 * δ) (y0 + 2 * δ)) := measure_mono h_interval
        _ = ENNReal.ofReal ((y0 + 2 * δ) - (y0 - 2 * δ)) := by
          rw [Real.volume_Icc] <;> ring_nf
        _ = ENNReal.ofReal (4 * δ) := by
          rw [show (y0 + 2 * δ) - (y0 - 2 * δ) = 4 * δ by ring]
      exact h_goal
  -- Support of g is contained in φ(B)
  let S' : Set ℝ := {x | g x ≠ 0}
  have hS'_meas : MeasurableSet S' :=
    hg_meas (measurableSet_singleton 0).compl
  have hS'_sub : S' ⊆ φ '' B := by
    intro x hx
    have hgx : g x ≠ 0 := hx
    have h_nonempty : Set.Nonempty {y : ℝ | (x, y) ∈ T '' B} := by
      by_contra h
      have h_empty : {y : ℝ | (x, y) ∈ T '' B} = ∅ := by
        simpa [Set.not_nonempty_iff_eq_empty] using h
      have h9 : g x = 0 := by
        dsimp only [g]
        rw [h_empty] <;> simp
      exact hgx h9
    rcases h_nonempty with ⟨y, hy⟩
    rcases hy with ⟨p, hp, hpy⟩
    have h10 : φ p = x := by simpa [φ, T] using congr_arg Prod.fst hpy
    exact ⟨p, hp, h10⟩
  -- g(x) ≤ 4δ * indicator of S'
  have h_le : ∀ (x : ℝ), g x ≤ ENNReal.ofReal (4 * δ) * S'.indicator (fun _ => (1 : ENNReal)) x := by
    intro x
    by_cases hx : x ∈ S'
    · have h1 : g x ≤ ENNReal.ofReal (4 * δ) := h_slice_bound x
      simpa [hx, Set.indicator_apply] using h1
    · have h2 : g x = 0 := by
        simpa [S', Set.mem_setOf_eq] using hx
      simpa [hx, Set.indicator_apply, h2] using by simp
  -- Fubini: volume(T(B)) = ∫⁻ x, g(x)
  have h_volume_eq_prod : (volume : Measure (ℝ × ℝ)) = volume.prod volume :=
    MeasureTheory.Measure.volume_eq_prod ℝ ℝ
  have h_fubini : volume (T '' B) = ∫⁻ (x : ℝ), g x := by
    rw [h_volume_eq_prod]
    exact MeasureTheory.Measure.prod_apply hTB_meas
  -- Bound the integral
  have h_main : ∫⁻ (x : ℝ), g x ≤
      ∫⁻ (x : ℝ), ENNReal.ofReal (4 * δ) * S'.indicator (fun _ => (1 : ENNReal)) x :=
    MeasureTheory.lintegral_mono h_le
  have h_rhs : ∫⁻ (x : ℝ), ENNReal.ofReal (4 * δ) * S'.indicator (fun _ => (1 : ENNReal)) x =
      ENNReal.ofReal (4 * δ) * volume S' := by
    have h_ind : ∫⁻ (x : ℝ), S'.indicator (fun _ => (1 : ENNReal)) x = volume S' := by
      rw [MeasureTheory.lintegral_indicator_const₀ hS'_meas.nullMeasurableSet]
      <;> ring
    rw [MeasureTheory.lintegral_const_mul (ENNReal.ofReal (4 * δ)) (measurable_const.indicator hS'_meas)]
    rw [h_ind]
  have h_vol_S' : volume S' ≤ volume (φ '' B) := measure_mono hS'_sub
  have h4 : ∫⁻ (x : ℝ), g x ≤ ENNReal.ofReal (4 * δ) * volume S' := by
    calc ∫⁻ (x : ℝ), g x
      ≤ ∫⁻ (x : ℝ), ENNReal.ofReal (4 * δ) * S'.indicator (fun _ => (1 : ENNReal)) x := h_main
    _ = ENNReal.ofReal (4 * δ) * volume S' := h_rhs
  have h_final : volume (T '' B) ≤ ENNReal.ofReal (4 * δ) * volume (φ '' B) := by
    rw [h_fubini]
    calc ∫⁻ (x : ℝ), g x
      ≤ ENNReal.ofReal (4 * δ) * volume S' := h4
    _ ≤ ENNReal.ofReal (4 * δ) * volume (φ '' B) := by gcongr
  rw [h_eq_vol] at h_final
  have h_pos : 0 < ENNReal.ofReal (4 * δ) := by
    apply ENNReal.ofReal_pos.mpr
    linarith
  have h_ne_top : ENNReal.ofReal (4 * δ) ≠ ⊤ := ENNReal.ofReal_ne_top
  have h_goal : volume B / ENNReal.ofReal (4 * δ) ≤ volume (φ '' B) := by
    have h1 : volume B ≤ ENNReal.ofReal (4 * δ) * volume (φ '' B) := h_final
    have h2 : volume B / ENNReal.ofReal (4 * δ) ≤
        (ENNReal.ofReal (4 * δ) * volume (φ '' B)) / ENNReal.ofReal (4 * δ) := by
      gcongr
    have h3 : (ENNReal.ofReal (4 * δ) * volume (φ '' B)) / ENNReal.ofReal (4 * δ) =
        volume (φ '' B) := by
      have h4 : ENNReal.ofReal (4 * δ) * volume (φ '' B) =
          volume (φ '' B) * ENNReal.ofReal (4 * δ) := by
        exact mul_comm _ _
      rw [h4]
      exact ENNReal.mul_div_cancel_right h_pos.ne' h_ne_top
    rw [h3] at h2
    exact h2
  exact h_goal

/-- General 2D lemma: if B ⊆ ℝ² has y-diameter ≤ D, then
the length of the image under φ(x,y) = x + c*y is at least area(B)/(2D). -/
lemma image_linear_functional_length_lower_general
    {D c : ℝ} (hD : 0 < D)
    {B : Set (ℝ × ℝ)} (hB_meas : MeasurableSet B)
    (h_y_diam : ∀ (y1 y2 : ℝ), (∃ x1 x2 : ℝ, (x1, y1) ∈ B ∧ (x2, y2) ∈ B) → |y1 - y2| ≤ D) :
    volume ((fun p : ℝ × ℝ => p.1 + c * p.2) '' B) ≥ volume B / ENNReal.ofReal (2 * D) := by
  set δ : ℝ := D / 2 with hδ_def
  have hδ : 0 < δ := half_pos hD
  have h_y_diam2 : ∀ (y1 y2 : ℝ), (∃ x1 x2 : ℝ, (x1, y1) ∈ B ∧ (x2, y2) ∈ B) → |y1 - y2| ≤ 2 * δ := by
    intro y1 y2 h
    have h5 : |y1 - y2| ≤ D := h_y_diam y1 y2 h
    have h6 : 2 * δ = D := by
      rw [hδ_def] <;> ring
    rw [h6]
    exact h5
  have h_main : volume ((fun p : ℝ × ℝ => p.1 + c * p.2) '' B) ≥ volume B / ENNReal.ofReal (4 * δ) :=
    image_linear_functional_length_lower (δ := δ) (c := c) hδ hB_meas h_y_diam2
  have h7 : ENNReal.ofReal (4 * δ) = ENNReal.ofReal (2 * D) := by
    have h8 : 4 * δ = 2 * D := by
      rw [hδ_def] <;> ring
    rw [h8]
  rw [h7] at h_main
  exact h_main

-- ============================================================================
-- 3D projection volume lower bound via Fubini
-- ============================================================================

/-- 3D projection volume lower bound for compact sets.
Domain is `ℝ × (ℝ × ℝ)`: first factor z, second (x,y).
Projection: (z, (x,y)) ↦ (x + f(z)*y, z). -/
private lemma projection3d_compact_volume_lower
    {D : ℝ} (hD : 0 < D)
    {K : Set (ℝ × (ℝ × ℝ))} (hK_compact : IsCompact K)
    {f : ℝ → ℝ} (hf : Continuous f)
    (h_y_diam : ∀ z, ∀ y1 y2 : ℝ,
      (∃ x1 x2 : ℝ, (z, (x1, y1)) ∈ K ∧ (z, (x2, y2)) ∈ K) → |y1 - y2| ≤ D) :
    volume ((fun p : ℝ × (ℝ × ℝ) => (p.2.1 + f p.1 * p.2.2, p.1)) '' K) ≥
    volume K / ENNReal.ofReal (2 * D) := by
  let π_f : ℝ × (ℝ × ℝ) → ℝ × ℝ := fun p => (p.2.1 + f p.1 * p.2.2, p.1)
  have hπ_cont : Continuous π_f := by fun_prop
  have hK_meas : MeasurableSet K := hK_compact.measurableSet
  have himg_compact : IsCompact (π_f '' K) := hK_compact.image hπ_cont
  have himg_meas : MeasurableSet (π_f '' K) := himg_compact.measurableSet
  let c : ENNReal := ENNReal.ofReal (2 * D)
  have hc_pos : 0 < c := by apply ENNReal.ofReal_pos.mpr; linarith
  have hc_ne_top : c ≠ ⊤ := ENNReal.ofReal_ne_top
  let gK : ℝ → ENNReal := fun z => volume {xy : ℝ × ℝ | (z, xy) ∈ K}
  have h_slice_eq1 : ∀ (z : ℝ), (Prod.mk z ⁻¹' K) = {xy : ℝ × ℝ | (z, xy) ∈ K} := by
    intro z
    ext xy
    simp
  have hgK_meas : Measurable gK := by
    have h : Measurable (fun (z : ℝ) => volume (Prod.mk z ⁻¹' K)) := by
      exact measurable_measure_prodMk_left hK_meas
    have h2 : (fun (z : ℝ) => volume (Prod.mk z ⁻¹' K)) = gK := by
      funext z
      rw [h_slice_eq1 z]
      <;> rfl
    rw [←h2]
    exact h
  let gI : ℝ → ENNReal := fun z => volume {u : ℝ | (u, z) ∈ π_f '' K}
  have h_vol_prod1 : (volume : Measure (ℝ × (ℝ × ℝ))) = volume.prod volume :=
    MeasureTheory.Measure.volume_eq_prod ℝ (ℝ × ℝ)
  have h_fub_K : volume K = ∫⁻ z, gK z := by
    rw [h_vol_prod1]
    exact MeasureTheory.Measure.prod_apply hK_meas
  have h_vol_prod2 : (volume : Measure (ℝ × ℝ)) = volume.prod volume :=
    MeasureTheory.Measure.volume_eq_prod ℝ ℝ
  have h_swap_mp : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ) volume volume :=
    MeasureTheory.Measure.measurePreserving_swap (μ := volume) (ν := volume)
  have h_fub_I : volume (π_f '' K) = ∫⁻ z, gI z := by
    let S := π_f '' K
    have hS_swap_compact : IsCompact (Prod.swap '' S) := himg_compact.image continuous_swap
    have hS_swap_meas : MeasurableSet (Prod.swap '' S) := hS_swap_compact.measurableSet
    have h1 : volume S = volume (Prod.swap '' S) := by
      have h_map : Measure.map Prod.swap volume = volume := h_swap_mp.map_eq
      have h_inj : Function.Injective (Prod.swap : ℝ × ℝ → ℝ × ℝ) := Prod.swap_injective
      have h_preimg : Prod.swap ⁻¹' (Prod.swap '' S) = S := by
        ext x
        simp [h_inj]
      calc volume S
        = volume (Prod.swap ⁻¹' (Prod.swap '' S)) := by rw [h_preimg]
      _ = Measure.map Prod.swap volume (Prod.swap '' S) := by
          rw [Measure.map_apply continuous_swap.measurable hS_swap_meas]
      _ = volume (Prod.swap '' S) := by rw [h_map]
    rw [h1]
    rw [h_vol_prod2]
    have h2 : (volume.prod volume) (Prod.swap '' S) =
        ∫⁻ (z : ℝ), volume (Prod.mk z ⁻¹' (Prod.swap '' S)) :=
      MeasureTheory.Measure.prod_apply (μ := volume) (ν := volume) hS_swap_meas
    rw [h2]
    congr with z
    have h3 : Prod.mk z ⁻¹' (Prod.swap '' S) = {u : ℝ | (u, z) ∈ S} := by
      ext u
      simp [Prod.swap]
      <;> aesop
    rw [h3]
    <;> rfl
  have h_slice_eq : ∀ z, {u : ℝ | (u, z) ∈ π_f '' K} =
      (fun xy : ℝ × ℝ => xy.1 + f z * xy.2) '' {xy : ℝ × ℝ | (z, xy) ∈ K} := by
    intro z
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨p, hp, h_eq⟩
      have hz : p.1 = z := by
        have h9 : (π_f p).2 = (u, z).2 := congr_arg Prod.snd h_eq
        simpa [π_f] using h9
      have hu : p.2.1 + f p.1 * p.2.2 = u := congr_arg Prod.fst h_eq
      have h_p2_in : p.2 ∈ {xy : ℝ × ℝ | (z, xy) ∈ K} := by
        simp only [Set.mem_setOf_eq]
        rw [← hz]
        exact hp
      refine ⟨p.2, h_p2_in, ?_⟩
      rw [hz] at hu
      exact hu
    · rintro ⟨xy, hxy, rfl⟩
      exact ⟨(z, xy), hxy, by simp [π_f]⟩
  have h_pointwise : ∀ z, gI z ≥ gK z / c := by
    intro z
    dsimp only [gI]
    rw [h_slice_eq z]
    let B_z : Set (ℝ × ℝ) := {xy | (z, xy) ∈ K}
    have hBz_meas : MeasurableSet B_z := by
      have h_cont : Continuous (fun xy : ℝ × ℝ => (z, xy)) := by fun_prop
      exact hK_meas.preimage h_cont.measurable
    have h_diam_z : ∀ (y1 y2 : ℝ), (∃ x1 x2 : ℝ, (x1, y1) ∈ B_z ∧ (x2, y2) ∈ B_z) → |y1 - y2| ≤ D := by
      intro y1 y2 h
      rcases h with ⟨x1, x2, h1, h2⟩
      exact h_y_diam z y1 y2 ⟨x1, x2, h1, h2⟩
    exact image_linear_functional_length_lower_general hD hBz_meas h_diam_z
  have h_le : ∫⁻ z, gK z / c ≤ ∫⁻ z, gI z := lintegral_mono h_pointwise
  have h_div : ∫⁻ z, gK z / c = (∫⁻ z, gK z) / c := by
    have h1 : ∀ z, gK z / c = c⁻¹ * gK z := by
      intro z
      rw [div_eq_mul_inv, mul_comm]
    have h2 : ∫⁻ z, gK z / c = ∫⁻ z, c⁻¹ * gK z := by
      congr with z
      exact h1 z
    rw [h2]
    have h3 : ∫⁻ z, c⁻¹ * gK z = c⁻¹ * (∫⁻ z, gK z) :=
      lintegral_const_mul c⁻¹ hgK_meas
    rw [h3]
    have h4 : c⁻¹ * (∫⁻ z, gK z) = (∫⁻ z, gK z) / c := by
      have h5 : c⁻¹ * (∫⁻ z, gK z) = (∫⁻ z, gK z) * c⁻¹ := by
        exact mul_comm _ _
      rw [h5]
      exact Eq.symm (div_eq_mul_inv (∫⁻ z, gK z) c)
    exact h4
  rw [h_fub_I, h_fub_K]
  rw [h_div] at h_le
  exact h_le

/-- 3D projection volume lower bound for measurable sets via compact approximation. -/
lemma projection3d_volume_lower
    {D : ℝ} (hD : 0 < D)
    {A : Set (ℝ × (ℝ × ℝ))} (hA_meas : MeasurableSet A)
    {f : ℝ → ℝ} (hf : Continuous f)
    (h_y_diam : ∀ z, ∀ y1 y2 : ℝ,
      (∃ x1 x2 : ℝ, (z, (x1, y1)) ∈ A ∧ (z, (x2, y2)) ∈ A) → |y1 - y2| ≤ D) :
    volume ((fun p : ℝ × (ℝ × ℝ) => (p.2.1 + f p.1 * p.2.2, p.1)) '' A) ≥
    volume A / ENNReal.ofReal (2 * D) := by
  let π_f : ℝ × (ℝ × ℝ) → ℝ × ℝ := fun p => (p.2.1 + f p.1 * p.2.2, p.1)
  let c : ENNReal := ENNReal.ofReal (2 * D)
  have hc_pos : 0 < c := by apply ENNReal.ofReal_pos.mpr; linarith
  have hc_ne_top : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have h_c_pos' : c ≠ 0 := hc_pos.ne'
  have h_inv_mul : c⁻¹ * c = 1 := ENNReal.inv_mul_cancel h_c_pos' hc_ne_top
  have h_div_mul : ∀ (a : ENNReal), (a / c) * c = a := by
    intro a
    calc (a / c) * c
      = a * c⁻¹ * c := by simp [div_eq_mul_inv] <;> rfl
    _ = a * (c⁻¹ * c) := by rw [mul_assoc]
    _ = a * 1 := by rw [h_inv_mul]
    _ = a := by simp
  have h_main : ∀ (r : ENNReal), r < volume A → volume (π_f '' A) > r / c := by
    intro r hr
    have h_exists : ∃ (K : Set (ℝ × (ℝ × ℝ))), K ⊆ A ∧ IsCompact K ∧ r < volume K :=
      hA_meas.exists_lt_isCompact hr
    rcases h_exists with ⟨K, hK_sub, hK_compact, hrK⟩
    have hK_diam : ∀ z, ∀ y1 y2 : ℝ,
        (∃ x1 x2 : ℝ, (z, (x1, y1)) ∈ K ∧ (z, (x2, y2)) ∈ K) → |y1 - y2| ≤ D := by
      intro z y1 y2 h
      rcases h with ⟨x1, x2, h1, h2⟩
      exact h_y_diam z y1 y2 ⟨x1, x2, hK_sub h1, hK_sub h2⟩
    have hK_bound : volume (π_f '' K) ≥ volume K / c :=
      projection3d_compact_volume_lower hD hK_compact hf hK_diam
    have h_img_mono : volume (π_f '' K) ≤ volume (π_f '' A) :=
      measure_mono (by gcongr)
    have h_div_lt : r / c < volume K / c :=
      ENNReal.div_lt_div_right h_c_pos' hc_ne_top hrK
    calc volume (π_f '' A)
      ≥ volume (π_f '' K) := h_img_mono
    _ ≥ volume K / c := hK_bound
    _ > r / c := h_div_lt
  by_contra h_contra
  have h_lt : volume (π_f '' A) < volume A / c := by
    have h9 : c = ENNReal.ofReal (2 * D) := by rfl
    simpa [not_le, h9] using h_contra
  set r : ENNReal := volume (π_f '' A) * c with hr_def
  have hr : r < volume A := by
    have h1 : r = volume (π_f '' A) * c := by rfl
    rw [h1]
    have h2 : volume (π_f '' A) * c < (volume A / c) * c := by
      exact ENNReal.mul_lt_mul_left h_c_pos' hc_ne_top h_lt
    have h3 : (volume A / c) * c = volume A := h_div_mul (volume A)
    rw [h3] at h2
    exact h2
  have h4 : volume (π_f '' A) > r / c := h_main r hr
  have h5 : r / c = volume (π_f '' A) := by
    have h6 : r = volume (π_f '' A) * c := by rfl
    rw [h6]
    have h7 : (volume (π_f '' A) * c) / c = volume (π_f '' A) := by
      exact ENNReal.mul_div_cancel_right h_c_pos' hc_ne_top
    exact h7
  rw [h5] at h4
  exact lt_irrefl _ h4

end Kakeya.Assouad
