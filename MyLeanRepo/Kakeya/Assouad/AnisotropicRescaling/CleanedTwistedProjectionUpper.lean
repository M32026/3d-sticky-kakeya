import MyLeanRepo.Kakeya.Assouad.Statements
import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.GlobalThickening
import MyLeanRepo.Kakeya.Assouad.AnisotropicRescalingGeometry
import MyLeanRepo.Kakeya.Assouad.SliceCovering
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Complete proof of cleaned_anisotropic_twisted_projection_upper
-/

noncomputable section

open MeasureTheory Set Metric

namespace Kakeya.Assouad

-- ============================================================================
-- coord_le_norm
-- ============================================================================

private lemma coord_le_norm {n : ℕ} {p : EuclideanSpace ℝ (Fin n)} {i : Fin n} :
    |p i| ≤ ‖p‖ := by
  have h : (p i)^2 ≤ ∑ j : Fin n, (p j)^2 := by
    apply Finset.single_le_sum (fun j _ => sq_nonneg (p j)) (Finset.mem_univ i)
  have hsq : (|p i|)^2 ≤ ∑ j : Fin n, (p j)^2 := by
    simpa [sq_abs] using h
  have h2 : |p i| ≤ Real.sqrt (∑ j : Fin n, (p j)^2) := by
    have h3 : Real.sqrt ((|p i|)^2) ≤ Real.sqrt (∑ j : Fin n, (p j)^2) :=
      Real.sqrt_le_sqrt hsq
    have h4 : Real.sqrt ((|p i|)^2) = |p i| := by
      rw [Real.sqrt_sq] <;> exact abs_nonneg _
    rw [h4] at h3
    exact h3
  simpa [EuclideanSpace.norm_eq] using h2

-- ============================================================================
-- volume_by_slices (Aurora)
-- ============================================================================

private lemma coordMap_volumePreserving2 :
    MeasurePreserving (fun p : Point2 => (p 0, p 1)) volume volume := by
  let e1 : Point2 → (Fin 2 → ℝ) := WithLp.ofLp
  have hpres1 : MeasurePreserving e1 volume volume :=
    PiLp.volume_preserving_ofLp (ι := Fin 2)
  let e2 : (Fin 2 → ℝ) → ℝ × ℝ := MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)
  have hpres2 : MeasurePreserving e2 volume volume :=
    MeasureTheory.volume_preserving_piFinTwo (fun _ => ℝ)
  let e : Point2 → ℝ × ℝ := e2 ∘ e1
  have hpres : MeasurePreserving e volume volume := hpres2.comp hpres1
  have h_eq : e = (fun p : Point2 => (p 0, p 1)) := by
    funext p <;> rfl
  rw [h_eq] at hpres
  exact hpres

lemma volume_by_slices {U : Set Point2} {B : ENNReal}
    (hU_meas : MeasurableSet U)
    (hU_vert : ∀ p ∈ U, (p 1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1)
    (h_bound : ∀ t ∈ Set.Icc (-1 : ℝ) 1, volume (sliceAt U t) ≤ B) :
    volume U ≤ ENNReal.ofReal 2 * B := by
  let e : Point2 → ℝ × ℝ := fun p => (p 0, p 1)
  have he_meas : Measurable e := by fun_prop
  have hpres : MeasurePreserving e volume volume := coordMap_volumePreserving2
  have hmap : Measure.map e volume = volume := hpres.2
  let imageU : Set (ℝ × ℝ) := e '' U
  have h_inj : Function.Injective e := by
    intro p q h
    have h1 : p 0 = q 0 := by simpa [e] using congr_arg Prod.fst h
    have h2 : p 1 = q 1 := by simpa [e] using congr_arg Prod.snd h
    ext i; fin_cases i <;> tauto
  have h_injOn : Set.InjOn e U := fun x _ y _ hxy => h_inj hxy
  have hU'_meas : MeasurableSet imageU :=
    MeasurableSet.image_of_measurable_injOn hU_meas he_meas h_injOn
  have h3 : e ⁻¹' imageU = U := by
    ext p
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · rintro ⟨q, hq, heq⟩; exact h_inj heq ▸ hq
    · intro hp; exact ⟨p, hp, rfl⟩
  have hvol_eq : volume U = volume imageU := by
    have h : volume imageU = volume U := by
      calc volume imageU
        = (Measure.map e volume) imageU := by rw [hmap]
      _ = volume (e ⁻¹' imageU) := by rw [Measure.map_apply he_meas hU'_meas]
      _ = volume U := by rw [h3]
    exact h.symm
  have h_fubini : volume imageU =
      ∫⁻ (t : ℝ), volume {x : ℝ | (x, t) ∈ imageU} ∂volume := by
    have hvol_eq_prod : (volume : Measure (ℝ × ℝ)) = volume.prod volume :=
      MeasureTheory.Measure.volume_eq_prod ℝ ℝ
    rw [hvol_eq_prod]
    exact MeasureTheory.Measure.prod_apply_symm hU'_meas
  have h_slice_eq : ∀ (t : ℝ), {x : ℝ | (x, t) ∈ imageU} = sliceAt U t := by
    intro t
    ext x
    simp only [Set.mem_image, sliceAt, e]
    constructor
    · rintro ⟨p, hp, hpe⟩
      have hpt : p 1 = t := by simpa [e] using congr_arg Prod.snd hpe
      have hpx : p 0 = x := by simpa [e] using congr_arg Prod.fst hpe
      exact ⟨p, ⟨hp, hpt⟩, hpx⟩
    · rintro ⟨p, ⟨hp, hpt⟩, hpx⟩
      have hpe : e p = (x, t) := by
        simp [e, hpx, hpt] <;> rfl
      exact ⟨p, hp, hpe⟩
  have h_fubini_main : volume U = ∫⁻ (t : ℝ), volume (sliceAt U t) ∂volume := by
    calc volume U
      = volume imageU := hvol_eq
    _ = ∫⁻ (t : ℝ), volume {x : ℝ | (x, t) ∈ imageU} ∂volume := h_fubini
    _ = ∫⁻ (t : ℝ), volume (sliceAt U t) ∂volume := by
      congr with t; rw [h_slice_eq t]
  have h_support : ∀ (t : ℝ), t ∉ Set.Icc (-1 : ℝ) 1 →
      volume (sliceAt U t) = 0 := by
    intro t ht
    by_contra hne
    have h_nonempty : Set.Nonempty (sliceAt U t) := by
      by_contra h
      have h_empty : sliceAt U t = ∅ := by
        simpa [Set.not_nonempty_iff_eq_empty] using h
      rw [h_empty] at hne
      simp at hne
    obtain ⟨x, hx⟩ := h_nonempty
    obtain ⟨p, hp_in, hpx⟩ : ∃ (p : Point2), p ∈ {p ∈ U | p 1 = t} ∧ p 0 = x := by
      simpa [sliceAt, Set.mem_image] using hx
    have hp : p ∈ U := hp_in.1
    have hpt : p 1 = t := hp_in.2
    have hvt : p 1 ∈ Set.Icc (-1 : ℝ) 1 := hU_vert p hp
    rw [hpt] at hvt
    exact ht hvt
  let g : ℝ → ENNReal := fun t => volume (sliceAt U t)
  have h_integral : ∫⁻ (t : ℝ), g t ∂volume =
      ∫⁻ (t : ℝ) in Set.Icc (-1 : ℝ) 1, g t ∂volume := by
    rw [← lintegral_add_compl g measurableSet_Icc]
    have h6 : ∫⁻ (t : ℝ) in (Set.Icc (-1 : ℝ) 1)ᶜ, g t ∂volume = 0 := by
      apply le_zero_iff.mp
      have h_ae : ∀ᵐ (t : ℝ) ∂(volume.restrict (Set.Icc (-1 : ℝ) 1)ᶜ), g t ≤ (0 : ENNReal) := by
        filter_upwards [self_mem_ae_restrict measurableSet_Icc.compl] with t ht
        have hgt : g t = 0 := h_support t ht
        rw [hgt] <;> simp
      have h_le : ∫⁻ (t : ℝ) in (Set.Icc (-1 : ℝ) 1)ᶜ, g t ∂volume ≤
          ∫⁻ (t : ℝ) in (Set.Icc (-1 : ℝ) 1)ᶜ, (0 : ENNReal) ∂volume :=
        lintegral_mono_ae h_ae
      simpa using h_le
    rw [h6, add_zero]
  rw [h_fubini_main, h_integral]
  have h_le_all : ∀ (t : ℝ), g t ≤ B := by
    intro t
    by_cases ht : t ∈ Set.Icc (-1 : ℝ) 1
    · exact h_bound t ht
    · have hgt : g t = 0 := h_support t ht
      rw [hgt] <;> exact bot_le
  have h6 : ∫⁻ (t : ℝ) in Set.Icc (-1 : ℝ) 1, g t ∂volume ≤
      ∫⁻ (t : ℝ) in Set.Icc (-1 : ℝ) 1, B ∂volume :=
    lintegral_mono h_le_all
  have h7 : ∫⁻ (t : ℝ) in Set.Icc (-1 : ℝ) 1, B ∂volume =
      B * volume (Set.Icc (-1 : ℝ) 1) := by
    simp [lintegral_const] <;> rfl
  have h8 : volume (Set.Icc (-1 : ℝ) 1) = ENNReal.ofReal 2 := by
    rw [Real.volume_Icc] <;> norm_num
  calc
    ∫⁻ (t : ℝ) in Set.Icc (-1 : ℝ) 1, g t ∂volume
      ≤ ∫⁻ (t : ℝ) in Set.Icc (-1 : ℝ) 1, B ∂volume := h6
    _ = B * volume (Set.Icc (-1 : ℝ) 1) := h7
    _ = B * ENNReal.ofReal 2 := by rw [h8]
    _ = ENNReal.ofReal 2 * B := by rw [mul_comm]

-- ============================================================================
-- Inner product identity
-- ============================================================================

private lemma globalGrain_inner (slope : ℝ → ℝ) (p : Point3) (z : ℝ) :
    inner ℝ p (globalGrainDirection (slope z)) = p 0 + slope z * p 1 := by
  rw [globalGrainDirection]
  have h_add : inner ℝ p (EuclideanSpace.single (0 : Fin 3) (1 : ℝ) +
      slope z • EuclideanSpace.single (1 : Fin 3) (1 : ℝ)) =
      inner ℝ p (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) +
      inner ℝ p (slope z • EuclideanSpace.single (1 : Fin 3) (1 : ℝ)) := by
    rw [inner_add_right]
  rw [h_add]
  have h0 : inner ℝ p (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) = p 0 := by
    rw [EuclideanSpace.inner_single_right] <;> simp
  have h1 : inner ℝ p (slope z • EuclideanSpace.single (1 : Fin 3) (1 : ℝ)) =
      slope z * inner ℝ p (EuclideanSpace.single (1 : Fin 3) (1 : ℝ)) := by
    rw [inner_smul_right]
  rw [h0, h1]
  have h2 : inner ℝ p (EuclideanSpace.single (1 : Fin 3) (1 : ℝ)) = p 1 := by
    rw [EuclideanSpace.inner_single_right] <;> simp
  rw [h2] <;> ring

-- ============================================================================
-- Slice equality
-- ============================================================================

lemma twisted_slice_equality
    {delta sigma c d m : ℝ} {C : ENNReal}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {G : C2GrainStructure Y sigma C}
    (hcd : c < d) (hm : 0 < m)
    {f : SlopeFunction}
    (hf : ∀ t : ℝ,
      f t =
        G.slope (c + (d - c) / 2 * (t + 1)) /
            (m * (d - c) / 2) -
          G.slope (c + (d - c) / 2) /
            (m * (d - c) / 2))
    (S : Set Point3) (s : ℝ) :
    sliceAt (twistedProjection f '' (anisotropicRescalingMap G.slope c d m '' S)) s =
    globalGrainProjection G.slope (horizontalSlice S (c + (d - c) / 2 * (s + 1))) := by
  let zs := c + (d - c) / 2 * (s + 1)
  let Φ := anisotropicRescalingMap G.slope c d m
  have hcd' : d - c ≠ 0 := by linarith
  have hΦ2 : ∀ (p : Point3), (Φ p) 2 = 2 * (p 2 - c) / (d - c) - 1 := by
    intro p
    simp [Φ, anisotropicRescalingMap, point3] <;> ring
  ext x
  simp only [sliceAt, Set.mem_image, globalGrainProjection, horizontalSlice]
  constructor
  · rintro ⟨b, ⟨hbB, hbs⟩, rfl⟩
    rcases hbB with ⟨y, hy, h_eq⟩
    rcases hy with ⟨p, hpS, hΦy⟩
    have h_b_eq : b = twistedProjection f (Φ p) := by
      have h : twistedProjection f y = twistedProjection f (Φ p) := by
        exact congr_arg (twistedProjection f) hΦy.symm
      exact h_eq.symm.trans h
    have h_twisted1 : (twistedProjection f (Φ p)) 1 = (Φ p) 2 := by
      simp [twistedProjection]
    have hbs' : (twistedProjection f (Φ p)) 1 = s := by
      rw [h_b_eq] at hbs
      exact hbs
    have hvert : (Φ p) 2 = s := by
      rw [←h_twisted1]
      exact hbs'
    have hp2 : p 2 = zs := by
      have h : 2 * (p 2 - c) / (d - c) - 1 = s := by
        rw [hΦ2 p] at hvert
        exact hvert
      have h' : 2 * (p 2 - c) = (d - c) * (s + 1) := by
        have h1 : 2 * (p 2 - c) / (d - c) = s + 1 := by linarith
        field_simp [hcd'] at h1 ⊢ <;> linarith
      have h'' : p 2 - c = (d - c) / 2 * (s + 1) := by linarith
      have h_zs : zs = c + (d - c) / 2 * (s + 1) := by rfl
      linarith
    have hhoriz : (twistedProjection f (Φ p)) 0 = p 0 + G.slope (p 2) * p 1 :=
      twistedProjection_anisotropicRescalingMap_zero G.slope f hcd hm hf p
    have hinner : inner ℝ p (globalGrainDirection (G.slope (p 2))) =
        p 0 + G.slope (p 2) * p 1 := globalGrain_inner G.slope p (p 2)
    have h_goal : inner ℝ p (globalGrainDirection (G.slope (p 2))) = b 0 := by
      calc inner ℝ p (globalGrainDirection (G.slope (p 2)))
        = p 0 + G.slope (p 2) * p 1 := hinner
      _ = (twistedProjection f (Φ p)) 0 := hhoriz.symm
      _ = b 0 := by rw [h_b_eq]
    exact ⟨p, ⟨hpS, hp2⟩, h_goal⟩
  · rintro ⟨p, ⟨hpS, hp2⟩, rfl⟩
    have hvert : (Φ p) 2 = s := by
      rw [hΦ2 p, hp2]
      field_simp [hcd'] <;> ring
    have hbs : (twistedProjection f (Φ p)) 1 = s := by
      have h : (twistedProjection f (Φ p)) 1 = (Φ p) 2 := by
        simp [twistedProjection]
      rw [h, hvert]
    have hhoriz : (twistedProjection f (Φ p)) 0 = p 0 + G.slope (p 2) * p 1 :=
      twistedProjection_anisotropicRescalingMap_zero G.slope f hcd hm hf p
    have hinner : inner ℝ p (globalGrainDirection (G.slope (p 2))) =
        p 0 + G.slope (p 2) * p 1 := globalGrain_inner G.slope p (p 2)
    have hB : twistedProjection f (Φ p) ∈ twistedProjection f '' (Φ '' S) :=
      ⟨Φ p, ⟨p, hpS, rfl⟩, rfl⟩
    refine ⟨twistedProjection f (Φ p), ⟨hB, hbs⟩, ?_⟩
    have h_final : (twistedProjection f (Φ p)) 0 =
        inner ℝ p (globalGrainDirection (G.slope (p 2))) := by
      rw [hhoriz, hinner]
    exact h_final

-- ============================================================================
-- Slab covering (43 centers for 42*delta interval)
-- ============================================================================

private def clampToOne (x : ℝ) : ℝ := max (-1) (min 1 x)

private lemma clampToOne_mem (x : ℝ) : clampToOne x ∈ Set.Icc (-1 : ℝ) 1 := by
  simp [clampToOne]

private lemma clampToOne_near {w x : ℝ} (delta : ℝ) (hw : w ∈ Set.Icc (-1 : ℝ) 1) (h : |w - x| ≤ delta) :
    |w - clampToOne x| ≤ delta := by
  by_cases h2 : x < -1
  · have h4 : -1 ≤ w := hw.1
    have h5 : 0 ≤ w - x := by linarith
    have h6 : w - x ≤ delta := by
      have h7 : |w - x| = w - x := abs_of_nonneg h5
      rw [h7] at h
      exact h
    have h3 : clampToOne x = -1 := by
      have hmin : min 1 x = x := by apply min_eq_right; linarith
      have hmax : max (-1) x = -1 := by apply max_eq_left; linarith
      simp [clampToOne, hmin, hmax]
    rw [h3]
    have h8 : 0 ≤ w - (-1 : ℝ) := by linarith
    rw [abs_of_nonneg h8] <;> linarith
  · by_cases h3 : x > 1
    · have h4 : w ≤ 1 := hw.2
      have h5 : 0 ≤ x - w := by linarith
      have h6 : x - w ≤ delta := by
        have h71 : |w - x| = |x - w| := by exact abs_sub_comm w x
        have h7 : |x - w| = x - w := abs_of_nonneg h5
        rw [h71] at h
        rw [h7] at h
        exact h
      have hmax : max (-1) (1 : ℝ) = 1 := by apply max_eq_right; norm_num
      have hmin : min 1 x = 1 := by apply min_eq_left; linarith
      have hclamp : clampToOne x = 1 := by
        have h : clampToOne x = max (-1) (min 1 x) := by rfl
        rw [h, hmin, hmax]
      rw [hclamp]
      have h8 : 0 ≤ (1 : ℝ) - w := by linarith
      have h9 : |w - (1 : ℝ)| = (1 : ℝ) - w := by
        have h10 : |w - (1 : ℝ)| = |(1 : ℝ) - w| := by exact abs_sub_comm w 1
        rw [h10, abs_of_nonneg h8]
      rw [h9] <;> linarith
    · have h4 : x ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
      have h5 : clampToOne x = x := by
        simp [clampToOne, h4.1, h4.2]
      rw [h5]
      exact h

lemma slab_centers_cover (z0 : ℝ) (hz0 : z0 ∈ Set.Icc (-1 : ℝ) 1)
    (delta : ℝ) (hdelta : 0 < delta) :
    ∃ centers : Finset ℝ,
      (∀ z ∈ centers, z ∈ Set.Icc (-1 : ℝ) 1) ∧
      centers.card ≤ 43 ∧
      ∀ w ∈ Set.Icc (z0 - 21 * delta) (z0 + 21 * delta) ∩ Set.Icc (-1 : ℝ) 1,
        ∃ z ∈ centers, |w - z| ≤ delta := by
  let f : ℕ → ℝ := fun k => clampToOne (z0 - 21 * delta + (k : ℝ) * delta)
  let centers : Finset ℝ := Finset.image f (Finset.range 43)
  have h1 : ∀ z ∈ centers, z ∈ Set.Icc (-1 : ℝ) 1 := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨k, _, rfl⟩
    exact clampToOne_mem _
  have h2 : centers.card ≤ 43 := by
    have h : centers.card ≤ (Finset.range 43).card := Finset.card_image_le
    have h' : (Finset.range 43).card = 43 := by decide
    rw [h'] at h
    exact h
  refine ⟨centers, h1, h2, ?_⟩
  intro w hw
  have hw1 : w ∈ Set.Icc (-1 : ℝ) 1 := hw.2
  have h11 : z0 - 21 * delta ≤ w := hw.1.1
  have h12 : w ≤ z0 + 21 * delta := hw.1.2
  set u : ℝ := w - (z0 - 21 * delta) with hu_def
  have hu0 : 0 ≤ u := by linarith
  have hu1 : u ≤ 42 * delta := by linarith
  let k : ℕ := Nat.floor (u / delta)
  have hk1 : (k : ℝ) ≤ u / delta := Nat.floor_le (by positivity)
  have hk2 : u / delta < (k : ℝ) + 1 := Nat.lt_floor_add_one _
  have hk_range : k ∈ Finset.range 43 := by
    have h6 : (k : ℝ) ≤ 42 := by
      calc (k : ℝ) ≤ u / delta := hk1
        _ ≤ (42 * delta) / delta := by gcongr
        _ = 42 := by field_simp [hdelta.ne']
    have h7 : k ≤ 42 := by exact_mod_cast h6
    simp only [Finset.mem_range] <;> omega
  have hk3 : (k : ℝ) * delta ≤ u := by
    calc (k : ℝ) * delta
      ≤ (u / delta) * delta := by gcongr
    _ = u := by field_simp [hdelta.ne']
  have hk4 : u < ((k : ℝ) + 1) * delta := by
    calc u = (u / delta) * delta := by field_simp [hdelta.ne']
      _ < ((k : ℝ) + 1) * delta := by gcongr
  let x0 : ℝ := z0 - 21 * delta + (k : ℝ) * delta
  have hdist : |w - x0| ≤ delta := by
    have h13 : 0 ≤ w - x0 := by
      simp [x0, hu_def] <;> linarith
    have h14 : w - x0 < delta := by
      simp [x0, hu_def] <;> linarith
    rw [abs_of_nonneg h13] <;> linarith
  have h4 : f k ∈ centers := Finset.mem_image.mpr ⟨k, hk_range, rfl⟩
  have h5 : |w - f k| ≤ delta := by
    have hfk : f k = clampToOne x0 := by rfl
    rw [hfk]
    exact clampToOne_near delta hw1 hdist
  exact ⟨f k, h4, h5⟩

-- ============================================================================
-- Crude volume bound for large rho (Cobalt)
-- ============================================================================

private lemma twistedProjection_image_bounded
    {sigma delta c d m : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C : ENNReal} {G : C2GrainStructure Y sigma C}
    {f : SlopeFunction}
    (hcd : c < d) (hm_pos : 0 < m)
    (hsub : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1)
    (hdelta : 0 < delta)
    (hf : ∀ t : ℝ,
      f t =
        G.slope (c + (d - c) / 2 * (t + 1)) /
            (m * (d - c) / 2) -
          G.slope (c + (d - c) / 2) /
            (m * (d - c) / 2)) :
    twistedProjection f '' (anisotropicRescalingMap G.slope c d m '' (Y.union ∩ horizontalSlab c d))
    ⊆ closedBall (0 : Point2) 5 := by
  let Φ := anisotropicRescalingMap G.slope c d m
  let S := Y.union ∩ horizontalSlab c d
  intro p hp
  have hq1 : ∃ (q : Point3), q ∈ Φ '' S ∧ twistedProjection f q = p :=
    (Set.mem_image _ _ _).mp hp
  rcases hq1 with ⟨q, hq_in, rfl⟩
  have hr1 : ∃ (r : Point3), r ∈ S ∧ Φ r = q :=
    (Set.mem_image _ _ _).mp hq_in
  rcases hr1 with ⟨r, hr, rfl⟩
  let z : ℝ := r (2 : Fin 3)
  have hz_cd : z ∈ Set.Icc c d := by
    have h : r ∈ horizontalSlab c d := hr.2
    simpa [horizontalSlab] using h
  have hz1 : z ∈ Set.Icc (-1 : ℝ) 1 := hsub hz_cd
  have h_r_in_slab : r ∈ globalGrainSlab Y.union z delta := by
    simp only [globalGrainSlab, Set.mem_inter_iff, Set.mem_setOf_eq]
    exact ⟨⟨hr.1, ⟨by linarith, by linarith⟩⟩, hz1⟩
  have hAD : IsADSet1
      (globalGrainProjection G.slope (globalGrainSlab Y.union z delta))
      delta (1 - sigma) C :=
    G.global_slab_ad z hz1
  rcases hAD with ⟨_, _, _, _, h_bounded, _⟩
  have h_horiz : (twistedProjection f (Φ r)) (0 : Fin 2) =
      r (0 : Fin 3) + G.slope z * r (1 : Fin 3) :=
    twistedProjection_anisotropicRescalingMap_zero G.slope f hcd hm_pos hf r
  have h_inner : inner ℝ r (globalGrainDirection (G.slope z)) =
      r (0 : Fin 3) + G.slope z * r (1 : Fin 3) :=
    globalGrain_inner G.slope r z
  have h_r2 : r (2 : Fin 3) = z := rfl
  have h_goal : inner ℝ r (globalGrainDirection (G.slope (r (2 : Fin 3)))) =
      (twistedProjection f (Φ r)) (0 : Fin 2) := by
    rw [h_r2]
    exact h_inner.trans h_horiz.symm
  have h_p0_in : (twistedProjection f (Φ r)) (0 : Fin 2) ∈
      globalGrainProjection G.slope (globalGrainSlab Y.union z delta) :=
    ⟨r, h_r_in_slab, h_goal⟩
  have h_p0_Icc : (twistedProjection f (Φ r)) (0 : Fin 2) ∈ Set.Icc (-4 : ℝ) 4 :=
    h_bounded h_p0_in
  have h_p0_bdd : |(twistedProjection f (Φ r)) (0 : Fin 2)| ≤ 4 :=
    abs_le.mpr ⟨h_p0_Icc.1, h_p0_Icc.2⟩
  have h_vert : (twistedProjection f (Φ r)) (1 : Fin 2) =
      2 * (z - c) / (d - c) - 1 :=
    twistedProjection_anisotropicRescalingMap_one G.slope f c d m r
  have hcd_pos : 0 < d - c := by linarith
  have h_p1_bdd : |(twistedProjection f (Φ r)) (1 : Fin 2)| ≤ 1 := by
    rw [h_vert]
    have h1 : 0 ≤ 2 * (z - c) / (d - c) := by
      apply div_nonneg <;> linarith [hz_cd.1]
    have h2 : 2 * (z - c) / (d - c) ≤ 2 := by
      have h3 : z - c ≤ d - c := by linarith [hz_cd.2]
      have h4 : 0 ≤ d - c := by linarith
      have h5 : 2 * (z - c) / (d - c) ≤ 2 * (d - c) / (d - c) := by
        apply div_le_div_of_nonneg_right <;> linarith
      have h6 : 2 * (d - c) / (d - c) = 2 := by
        field_simp [hcd_pos.ne'] <;> ring
      rw [h6] at h5
      exact h5
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  set p := twistedProjection f (Φ r) with hp_def
  have h2 : ‖p‖ ^ 2 = (p (0 : Fin 2)) ^ 2 + (p (1 : Fin 2)) ^ 2 := by
    have h3 : ‖p‖ = Real.sqrt ((p (0 : Fin 2)) ^ 2 + (p (1 : Fin 2)) ^ 2) := by
      rw [EuclideanSpace.norm_eq]
      <;> simp [Fin.sum_univ_two, sq_abs] <;> rfl
    have h4 : ‖p‖ ^ 2 = (Real.sqrt ((p (0 : Fin 2)) ^ 2 + (p (1 : Fin 2)) ^ 2)) ^ 2 := by rw [h3]
    rw [h4, Real.sq_sqrt] <;> positivity
  have h4sq : (p (0 : Fin 2)) ^ 2 ≤ 16 := by
    have h5 : |p (0 : Fin 2)| ≤ 4 := h_p0_bdd
    have h6 : 0 ≤ |p (0 : Fin 2)| := abs_nonneg _
    have h7 : |p (0 : Fin 2)| ^ 2 ≤ 16 := by
      calc |p (0 : Fin 2)| ^ 2 ≤ (4 : ℝ) ^ 2 := by gcongr
        _ = 16 := by norm_num
    have h8 : (p (0 : Fin 2)) ^ 2 = |p (0 : Fin 2)| ^ 2 := by rw [sq_abs]
    rw [h8]; exact h7
  have h7sq : (p (1 : Fin 2)) ^ 2 ≤ 1 := by
    have h8 : |p (1 : Fin 2)| ≤ 1 := h_p1_bdd
    have h9 : 0 ≤ |p (1 : Fin 2)| := abs_nonneg _
    have h10 : |p (1 : Fin 2)| ^ 2 ≤ 1 := by
      calc |p (1 : Fin 2)| ^ 2 ≤ (1 : ℝ) ^ 2 := by gcongr
        _ = 1 := by norm_num
    have h11 : (p (1 : Fin 2)) ^ 2 = |p (1 : Fin 2)| ^ 2 := by rw [sq_abs]
    rw [h11]; exact h10
  have h_sq_le : ‖p‖ ^ 2 ≤ 25 := by
    rw [h2]
    have h : (p (0 : Fin 2)) ^ 2 + (p (1 : Fin 2)) ^ 2 ≤ 16 + 1 := by linarith
    linarith
  have h_nonneg : 0 ≤ ‖p‖ := by positivity
  have h_norm : ‖p‖ ≤ 5 := by nlinarith
  simpa [mem_closedBall, dist_zero_right] using h_norm

lemma twistedUnion_crude_volume_bound
    {sigma delta rho c d m : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C : ENNReal} {G : C2GrainStructure Y sigma C}
    {cleaned : CleanedAnisotropicTarget (rho := rho) (c := c) (d := d) (m := m) F Y G.slope}
    {f : SlopeFunction}
    (hsigma : 0 < sigma) (hsigma1 : sigma < 1)
    (hdelta : 0 < delta) (hrho : 0 < rho) (hrho_one : rho ≤ 1)
    (hcd : c < d) (hsub : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1)
    (hm_pos : 0 < m)
    (hC : 1 ≤ C)
    (hf_nonsing : f.IsNonsingular) (hf_zero : f 0 = 0)
    (hf : ∀ t : ℝ,
      f t =
        G.slope (c + (d - c) / 2 * (t + 1)) /
            (m * (d - c) / 2) -
          G.slope (c + (d - c) / 2) /
            (m * (d - c) / 2))
    (h_large : 20 * rho ≥ 1) :
    volume (twistedUnion cleaned.shading f) ≤
      1000000 * C * Kakeya.realRpowENN rho sigma := by
  set Φ := anisotropicRescalingMap G.slope c d m with hΦ
  set S := Y.union ∩ horizontalSlab c d with hS
  set B := twistedProjection f '' (Φ '' S) with hB
  set U := twistedUnion cleaned.shading f with hU
  have h1 : U ⊆ cthickening (20 * rho) B :=
    twisted_union_global_thickening hf_nonsing hf_zero hrho_one hrho hcd hm_pos hsub
  have h2 : B ⊆ closedBall (0 : Point2) 5 :=
    twistedProjection_image_bounded hcd hm_pos hsub hdelta hf
  have h3 : cthickening (20 * rho) B ⊆ closedBall (0 : Point2) (5 + 20 * rho) := by
    intro x hx
    have h4 : infEDist x B ≤ ENNReal.ofReal (20 * rho) := hx
    have h5 : ∀ (ε : ℝ), 0 < ε → ∃ (y : Point2), y ∈ B ∧ dist x y < 20 * rho + ε := by
      intro ε hε
      have h6 : infEDist x B < ENNReal.ofReal (20 * rho + ε) := by
        have h7 : ENNReal.ofReal (20 * rho) < ENNReal.ofReal (20 * rho + ε) := by
          exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
        exact lt_of_le_of_lt h4 h7
      have h8 : ∃ (y : Point2), y ∈ B ∧ edist x y < ENNReal.ofReal (20 * rho + ε) :=
        Metric.infEDist_lt_iff.mp h6
      rcases h8 with ⟨y, hy, h9⟩
      have h10 : dist x y < 20 * rho + ε := by
        have h11 : edist x y = ENNReal.ofReal (dist x y) := edist_dist x y
        rw [h11] at h9
        exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp h9
      exact ⟨y, hy, h10⟩
    have h_norm : ‖x‖ ≤ 5 + 20 * rho := by
      by_contra h
      set δ' : ℝ := (‖x‖ - (5 + 20 * rho)) / 2 with hδ'_def
      have hδ'_pos : 0 < δ' := by linarith
      rcases h5 δ' hδ'_pos with ⟨y, hy, hdist⟩
      have h_y_in : y ∈ closedBall (0 : Point2) 5 := h2 hy
      have h_y_norm : ‖y‖ ≤ 5 := by
        simpa [mem_closedBall, dist_zero_right] using h_y_in
      have h10 : ‖x‖ ≤ dist x y + ‖y‖ := by
        simpa [dist_eq_norm] using norm_add_le (x - y) y
      linarith
    simpa [mem_closedBall, dist_zero_right] using h_norm
  have h4 : U ⊆ closedBall (0 : Point2) (5 + 20 * rho) := h1.trans h3
  have h5 : volume U ≤ volume (closedBall (0 : Point2) (5 + 20 * rho)) :=
    measure_mono h4
  have h6 : volume (closedBall (0 : Point2) (5 + 20 * rho)) =
      ENNReal.ofReal (5 + 20 * rho) ^ 2 * ENNReal.ofReal Real.pi :=
    EuclideanSpace.volume_closedBall_fin_two (0 : Point2) (5 + 20 * rho)
  have h7 : ENNReal.ofReal (5 + 20 * rho) ^ 2 * ENNReal.ofReal Real.pi ≤
      ENNReal.ofReal 2500 := by
    have h8 : 5 + 20 * rho ≤ 25 := by linarith [hrho_one]
    have h9 : ENNReal.ofReal (5 + 20 * rho) ≤ ENNReal.ofReal 25 :=
      ENNReal.ofReal_le_ofReal (by linarith)
    have h10 : ENNReal.ofReal (5 + 20 * rho) ^ 2 ≤ ENNReal.ofReal 25 ^ 2 := by gcongr
    have h11 : ENNReal.ofReal Real.pi ≤ ENNReal.ofReal 4 :=
      ENNReal.ofReal_le_ofReal Real.pi_le_four
    have h12 : ENNReal.ofReal (5 + 20 * rho) ^ 2 * ENNReal.ofReal Real.pi ≤
        ENNReal.ofReal 25 ^ 2 * ENNReal.ofReal 4 := by gcongr
    have h13 : ENNReal.ofReal 25 ^ 2 * ENNReal.ofReal 4 = ENNReal.ofReal 2500 := by
      simp [pow_two] <;> norm_num
    exact h12.trans (le_of_eq h13)
  have h12 : volume U ≤ ENNReal.ofReal 2500 := by
    calc volume U
      ≤ volume (closedBall (0 : Point2) (5 + 20 * rho)) := h5
    _ = ENNReal.ofReal (5 + 20 * rho) ^ 2 * ENNReal.ofReal Real.pi := h6
    _ ≤ ENNReal.ofReal 2500 := h7
  have h13 : (1 : ℝ) / 20 ≤ rho := by linarith
  have h14 : rho ≤ Real.rpow rho sigma := by
    have hpos : 0 < rho := hrho
    have hpos2 : 0 < Real.rpow rho sigma := Real.rpow_pos_of_pos hpos sigma
    have hlog1 : Real.log (Real.rpow rho sigma) = sigma * Real.log rho := by
      simpa [Real.log_rpow hpos] using rfl
    have hlog_nonpos : Real.log rho ≤ 0 := Real.log_nonpos hpos.le (by linarith)
    have hlog2 : Real.log rho ≤ Real.log (Real.rpow rho sigma) := by
      rw [hlog1]
      have hsigma_le1 : sigma ≤ 1 := by linarith
      nlinarith
    exact (Real.log_le_log_iff hpos hpos2).mp hlog2
  have h17 : (1 : ℝ) / 20 ≤ Real.rpow rho sigma := by linarith
  have h18 : ENNReal.ofReal 2500 ≤
      (1000000 : ENNReal) * C * Kakeya.realRpowENN rho sigma := by
    have h19 : Kakeya.realRpowENN rho sigma = ENNReal.ofReal (Real.rpow rho sigma) := by
      simp [Kakeya.realRpowENN]
    rw [h19]
    have h20 : ENNReal.ofReal ((1 : ℝ) / 20) ≤ ENNReal.ofReal (Real.rpow rho sigma) :=
      ENNReal.ofReal_le_ofReal (by linarith)
    have h21 : ENNReal.ofReal 50000 ≤
        (1000000 : ENNReal) * C * ENNReal.ofReal (Real.rpow rho sigma) := by
      have h22 : ENNReal.ofReal 50000 =
          (1000000 : ENNReal) * ENNReal.ofReal ((1 : ℝ) / 20) := by
        have h : (1000000 : ENNReal) * ENNReal.ofReal ((1 : ℝ) / 20) =
            ENNReal.ofReal (1000000 * ((1 : ℝ) / 20)) := by
          have hcast : (1000000 : ENNReal) = ENNReal.ofReal (1000000 : ℝ) := by norm_cast
          rw [hcast]
          rw [← ENNReal.ofReal_mul (by norm_num)] <;> rfl
        rw [h] <;> norm_num
      rw [h22]
      have h23 : (1000000 : ENNReal) * ENNReal.ofReal ((1 : ℝ) / 20) ≤
          (1000000 : ENNReal) * C * ENNReal.ofReal ((1 : ℝ) / 20) := by
        have hC' : (1 : ENNReal) ≤ C := hC
        calc (1000000 : ENNReal) * ENNReal.ofReal ((1 : ℝ) / 20)
          = (1000000 : ENNReal) * (1 : ENNReal) * ENNReal.ofReal ((1 : ℝ) / 20) := by simp
        _ ≤ (1000000 : ENNReal) * C * ENNReal.ofReal ((1 : ℝ) / 20) := by gcongr
      have h24 : (1000000 : ENNReal) * C * ENNReal.ofReal ((1 : ℝ) / 20) ≤
          (1000000 : ENNReal) * C * ENNReal.ofReal (Real.rpow rho sigma) := by
        gcongr
      exact le_trans h23 h24
    have h25 : ENNReal.ofReal 2500 ≤ ENNReal.ofReal 50000 := by
      exact ENNReal.ofReal_le_ofReal (by norm_num)
    exact h25.trans h21
  exact h12.trans h18

-- ============================================================================
-- Main theorem
-- ============================================================================

theorem cleaned_anisotropic_twisted_projection_upper :
    CleanedAnisotropicTwistedProjectionUpperStatement := by
  intro sigma delta rho c d m hsigma hsigma1 hdelta hdelta_rho hrho_one hcd hsub hrho_eq hm_pos
        F Y C hC hCtop G cleaned f hf_nonsing hf_zero hf_formula
  set U := twistedUnion cleaned.shading f with hU_def
  set Φ := anisotropicRescalingMap G.slope c d m with hΦ_def
  set S := Y.union ∩ horizontalSlab c d with hS_def
  set B := twistedProjection f '' (Φ '' S) with hB_def
  set V := cthickening (20 * rho) B with hV_def
  set V' := V ∩ {p : Point2 | p 1 ∈ Set.Icc (-1 : ℝ) 1} with hV'_def

  have h1 : U ⊆ V :=
    twisted_union_global_thickening hf_nonsing hf_zero hrho_one (by linarith) hcd hm_pos hsub

  have hU_vert : ∀ p ∈ U, (p 1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by
    intro p hp
    rcases hp with ⟨q, hq, rfl⟩
    have h : q ∈ cleaned.shading.union := hq
    have h2 : q ∈ horizontalSlab (-1) 1 := cleaned.slopeWindow h
    simpa [horizontalSlab] using h2

  have h2 : U ⊆ V' := by
    intro p hp
    exact ⟨h1 hp, hU_vert p hp⟩

  have hV'_meas : MeasurableSet V' := by
    have h1 : IsClosed V := isClosed_cthickening
    have h_meas : Measurable (fun (p : Point2) => p 1) := by fun_prop
    have h2 : MeasurableSet {p : Point2 | p 1 ∈ Set.Icc (-1 : ℝ) 1} :=
      measurableSet_Icc.preimage h_meas
    exact h1.measurableSet.inter h2

  have hV'_vert : ∀ p ∈ V', (p 1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by
    intro p hp; exact hp.2

  by_cases h_small : 20 * rho < 1
  · -- SMALL RHO CASE
    set R' : ℝ := min (21 * rho) 1 with hR'_def
    have hR'_pos : 0 < R' := by
      have h1 : 0 < 21 * rho := by linarith [hrho_eq]
      exact lt_min h1 (by norm_num)
    have hR'_le1 : R' ≤ 1 := min_le_right _ _
    have hdelta_R' : delta ≤ R' := by
      have h : 20 * rho < R' := by
        by_cases h : 21 * rho ≤ 1
        · have hR' : R' = 21 * rho := by
            rw [hR'_def, min_eq_left] <;> linarith
          rw [hR'] <;> linarith [hrho_eq]
        · have hR' : R' = 1 := by
            rw [hR'_def, min_eq_right] <;> linarith
          rw [hR'] <;> exact h_small
      linarith [hdelta_rho]
    have hR'_le21rho : R' ≤ 21 * rho := min_le_left _ _
    have hR'_gt20rho : 20 * rho < R' := by
      by_cases h : 21 * rho ≤ 1
      · have hR' : R' = 21 * rho := by
          rw [hR'_def, min_eq_left] <;> linarith
        rw [hR'] <;> linarith [hrho_eq]
      · have hR' : R' = 1 := by
          rw [hR'_def, min_eq_right] <;> linarith
        rw [hR'] <;> exact h_small

    have h_slice_bound : ∀ t ∈ Set.Icc (-1 : ℝ) 1,
        volume (sliceAt V' t) ≤ 14448 * C * Kakeya.realRpowENN rho sigma := by
      intro t ht
      let w_t := c + (d - c) / 2 * (t + 1)
      have h_wt_in1 : w_t ∈ Set.Icc (-1 : ℝ) 1 := by
        have h1 : 0 ≤ t + 1 := by linarith [ht.1]
        have h2 : t + 1 ≤ 2 := by linarith [ht.2]
        have h3 : 0 ≤ (d - c) / 2 * (t + 1) := by positivity
        have h4 : (d - c) / 2 * (t + 1) ≤ d - c := by
          have h5 : (d - c) / 2 * (t + 1) ≤ (d - c) / 2 * 2 := by gcongr
          have h6 : (d - c) / 2 * 2 = d - c := by ring
          linarith
        have h7 : -1 ≤ c := (hsub (left_mem_Icc.mpr hcd.le)).1
        have h8 : d ≤ 1 := (hsub (right_mem_Icc.mpr hcd.le)).2
        simp only [w_t]
        constructor <;> linarith
      rcases slab_centers_cover w_t h_wt_in1 delta hdelta with ⟨centers, hmem, hcard, hcover⟩
      let E : ℝ → Set ℝ := fun z =>
        globalGrainProjection G.slope (globalGrainSlab Y.union z delta)
      have hAD : ∀ z ∈ centers, IsADSet1 (E z) delta (1 - sigma) C := by
        intro z hz
        exact G.global_slab_ad z (hmem z hz)
      have h_main_contain : sliceAt V t ⊆ ⋃ z ∈ centers, cthickening R' (E z) := by
        intro x hx
        have h_exists : ∃ (p : Point2), (p ∈ V ∧ p 1 = t) ∧ p 0 = x := by
          simpa [sliceAt, Set.mem_image] using hx
        rcases h_exists with ⟨p, ⟨hpV, hp1⟩, hp0⟩
        by_cases hB_empty : B = ∅
        · have hV_empty : V = ∅ := by
            rw [hV_def, hB_empty] <;> simp
          rw [hV_empty] at hpV
          simpa using hpV
        · have h_inf : infEDist p B ≤ ENNReal.ofReal (20 * rho) := hpV
          have h_pos : 0 ≤ (20 * rho : ℝ) := by linarith [hdelta]
          have h_iff : ENNReal.ofReal (20 * rho) < ENNReal.ofReal R' ↔ (20 * rho : ℝ) < R' :=
            ENNReal.ofReal_lt_ofReal_iff (by linarith)
          have h_lt1 : (20 * rho : ℝ) < R' := by linarith
          have h_lt : infEDist p B < ENNReal.ofReal R' :=
            lt_of_le_of_lt h_inf (h_iff.mpr h_lt1)
          have h_exists_b : ∃ (b : Point2), b ∈ B ∧ edist p b < ENNReal.ofReal R' :=
            Metric.infEDist_lt_iff.mp h_lt
          rcases h_exists_b with ⟨b, hbB, hbedist⟩
          have hdist : dist p b < R' := by
            have h_eq : edist p b = ENNReal.ofReal (dist p b) := edist_dist p b
            rw [h_eq] at hbedist
            have hpos : 0 ≤ dist p b := by positivity
            exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hpos).mp hbedist
          have h_coord1 : |b 1 - p 1| ≤ dist p b := by
            have h : |(p - b) 1| ≤ ‖p - b‖ := @coord_le_norm 2 (p - b) (1 : Fin 2)
            have h2 : |b 1 - p 1| = |(p - b) 1| := by
              have h3 : b 1 - p 1 = -((p - b) 1) := by simp
              rw [h3, abs_neg]
            rw [h2]
            simpa [dist_eq_norm] using h
          have h_s_range : |b 1 - t| < R' := by
            have h_eq : |b 1 - t| = |b 1 - p 1| := by
              have h4 : t = p 1 := hp1.symm
              rw [h4]
            rw [h_eq]
            exact lt_of_le_of_lt h_coord1 hdist
          let w_s := c + (d - c) / 2 * (b 1 + 1)
          have h_ws_range : |w_s - w_t| < 21 * delta := by
            have h_eq : w_s - w_t = (d - c) / 2 * (b 1 - t) := by
              simp [w_s, w_t] <;> ring
            rw [h_eq]
            have h_abs : |(d - c) / 2 * (b 1 - t)| = ((d - c) / 2) * |b 1 - t| := by
              have hpos : 0 ≤ (d - c) / 2 := by linarith
              rw [abs_mul, abs_of_nonneg hpos]
            rw [h_abs]
            have h3 : ((d - c) / 2) * |b 1 - t| < ((d - c) / 2) * R' :=
              mul_lt_mul_of_pos_left h_s_range (by linarith)
            have h4 : ((d - c) / 2) * R' ≤ 21 * delta := by
              have h5 : ((d - c) / 2) * R' ≤ ((d - c) / 2) * (21 * rho) := by
                gcongr <;> linarith
              have h6 : ((d - c) / 2) * (21 * rho) = 21 * delta := by
                have hcd' : d - c ≠ 0 := by linarith
                rw [hrho_eq]
                field_simp [hcd'] <;> ring
              rw [h6] at h5
              exact h5
            exact lt_of_lt_of_le h3 h4
          rcases hbB with ⟨q, hq_in, hb_eq⟩
          rcases hq_in with ⟨r, hrS, hΦr⟩
          have hr2 : r 2 ∈ Set.Icc c d := by
            have h : r ∈ horizontalSlab c d := hrS.2
            simpa [horizontalSlab] using h
          have hcd' : 0 < d - c := by linarith
          have h_vert : (twistedProjection f q) 1 = q 2 := by
            simp [twistedProjection, EuclideanSpace.single_apply] <;> ring
          have hq2 : q 2 = (Φ r) 2 := by rw [hΦr]
          have h_Φ2 : (Φ r) 2 = 2 * (r 2 - c) / (d - c) - 1 := by
            simp [Φ, anisotropicRescalingMap, point3] <;> ring
          have h_b1_eq : (twistedProjection f q) 1 = 2 * (r 2 - c) / (d - c) - 1 := by
            rw [h_vert, hq2, h_Φ2]
          have h_s_in1 : (twistedProjection f q) 1 ∈ Set.Icc (-1 : ℝ) 1 := by
            rw [h_b1_eq]
            have h1 : 0 ≤ 2 * (r 2 - c) / (d - c) := by
              apply div_nonneg <;> linarith [hr2.1]
            have h2 : 2 * (r 2 - c) / (d - c) ≤ 2 := by
              have h3 : r 2 - c ≤ d - c := by linarith [hr2.2]
              have h4 : 0 ≤ d - c := by linarith
              have h5 : 2 * (r 2 - c) / (d - c) ≤ 2 * (d - c) / (d - c) := by
                apply div_le_div_of_nonneg_right <;> linarith
              have h6 : 2 * (d - c) / (d - c) = 2 := by
                field_simp [hcd'.ne'] <;> ring
              rw [h6] at h5
              exact h5
            constructor <;> linarith
          have h_b1_in1 : b 1 ∈ Set.Icc (-1 : ℝ) 1 := by
            have h : (twistedProjection f q) 1 = b 1 := by rw [hb_eq]
            rw [←h]
            exact h_s_in1
          have h_ws_in1 : w_s ∈ Set.Icc (-1 : ℝ) 1 := by
            have h1 : 0 ≤ b 1 + 1 := by linarith [h_b1_in1.1]
            have h2 : b 1 + 1 ≤ 2 := by linarith [h_b1_in1.2]
            have h3 : 0 ≤ (d - c) / 2 * (b 1 + 1) := by positivity
            have h4 : (d - c) / 2 * (b 1 + 1) ≤ d - c := by
              have h5 : (d - c) / 2 * (b 1 + 1) ≤ (d - c) / 2 * 2 := by gcongr
              have h6 : (d - c) / 2 * 2 = d - c := by ring
              linarith
            have h7 : -1 ≤ c := (hsub (left_mem_Icc.mpr hcd.le)).1
            have h8 : d ≤ 1 := (hsub (right_mem_Icc.mpr hcd.le)).2
            simp only [w_s]
            constructor <;> linarith
          have h_ws_interval : w_s ∈ Set.Icc (w_t - 21 * delta) (w_t + 21 * delta) := by
            have h : |w_s - w_t| < 21 * delta := h_ws_range
            have h5 : w_t - 21 * delta ≤ w_s := by linarith [abs_lt.mp h]
            have h6 : w_s ≤ w_t + 21 * delta := by linarith [abs_lt.mp h]
            exact ⟨h5, h6⟩
          rcases hcover w_s ⟨h_ws_interval, h_ws_in1⟩ with ⟨z, hz_center, hz_dist⟩
          have h_slice_B : sliceAt B (b 1) =
              globalGrainProjection G.slope (horizontalSlice S w_s) :=
            twisted_slice_equality hcd hm_pos hf_formula S (b 1)
          have h_slab_sub : horizontalSlice S w_s ⊆ globalGrainSlab Y.union z delta := by
            intro p hp
            have hpY : p ∈ Y.union := (hp.1).1
            have hp2 : p 2 = w_s := hp.2
            have h7 : p 2 ∈ Set.Icc (z - delta) (z + delta) := by
              rw [hp2]
              have h8 : |w_s - z| ≤ delta := hz_dist
              exact ⟨by linarith [abs_le.mp h8], by linarith [abs_le.mp h8]⟩
            have h9 : p 2 ∈ Set.Icc (-1 : ℝ) 1 := by
              rw [hp2] <;> exact h_ws_in1
            simp only [globalGrainSlab, Set.mem_inter_iff, Set.mem_setOf_eq]
            exact ⟨⟨hpY, h7⟩, h9⟩
          have h_E_sub : sliceAt B (b 1) ⊆ E z := by
            rw [h_slice_B]
            intro y hy
            rcases hy with ⟨p, hp, h_eq⟩
            exact ⟨p, h_slab_sub hp, h_eq⟩
          have hq_in' : q ∈ Φ '' S := ⟨r, hrS, hΦr⟩
          have hbB' : b ∈ B := by
            rw [←hb_eq]
            exact ⟨q, hq_in', rfl⟩
          have h_b0_in : b 0 ∈ E z := h_E_sub ⟨b, ⟨hbB', rfl⟩, rfl⟩
          have h_coord0 : |p 0 - b 0| ≤ dist p b := by
            have h : |(p - b) 0| ≤ ‖p - b‖ := @coord_le_norm 2 (p - b) (0 : Fin 2)
            have h2 : |p 0 - b 0| = |(p - b) 0| := by
              have h3 : p 0 - b 0 = (p - b) 0 := by simp
              rw [h3]
            rw [h2]
            simpa [dist_eq_norm] using h
          have h_dist0 : dist x (b 0) < R' := by
            have h2 : dist x (b 0) = |x - b 0| := by rw [Real.dist_eq] <;> rfl
            rw [h2]
            have h3 : x = p 0 := hp0.symm
            rw [h3]
            exact lt_of_le_of_lt h_coord0 hdist
          have h10 : infEDist x (E z) ≤ edist x (b 0) :=
            Metric.infEDist_le_edist_of_mem h_b0_in
          have h11 : edist x (b 0) = ENNReal.ofReal (dist x (b 0)) := edist_dist x (b 0)
          rw [h11] at h10
          have hpos2 : 0 ≤ dist x (b 0) := by positivity
          have h_iff : ENNReal.ofReal (dist x (b 0)) < ENNReal.ofReal R' ↔ dist x (b 0) < R' :=
            ENNReal.ofReal_lt_ofReal_iff_of_nonneg hpos2
          have h12 : ENNReal.ofReal (dist x (b 0)) < ENNReal.ofReal R' := h_iff.mpr h_dist0
          have h13 : x ∈ cthickening R' (E z) :=
            le_of_lt (lt_of_le_of_lt h10 h12)
          exact Set.mem_iUnion₂.mpr ⟨z, hz_center, h13⟩
      have h10 : sliceAt V' t = sliceAt V t := by
        have h_set_eq : {p : Point2 | p ∈ V' ∧ p 1 = t} = {p : Point2 | p ∈ V ∧ p 1 = t} := by
          ext p
          simp only [V', Set.mem_inter_iff, Set.mem_setOf_eq]
          constructor
          · rintro ⟨⟨hpV, _⟩, hp1⟩
            exact ⟨hpV, hp1⟩
          · rintro ⟨hpV, hp1⟩
            have hvt : p 1 ∈ Set.Icc (-1 : ℝ) 1 := by rw [hp1] <;> exact ht
            exact ⟨⟨hpV, hvt⟩, hp1⟩
        simp only [sliceAt]
        rw [h_set_eq]
      rw [h10]
      have h11 : volume (sliceAt V t) ≤ volume (⋃ z ∈ centers, cthickening R' (E z)) :=
        measure_mono h_main_contain
      have h12 : volume (⋃ z ∈ centers, cthickening R' (E z)) ≤
          ∑ z ∈ centers, volume (cthickening R' (E z)) :=
        measure_biUnion_finset_le centers (fun z => cthickening R' (E z))
      have h13 : ∀ z ∈ centers, volume (cthickening R' (E z)) ≤
          16 * C * Kakeya.realRpowENN R' sigma := by
        intro z hz
        exact (hAD z hz).volume_cthickening_le hdelta hsigma hsigma1 hCtop hR'_pos hR'_le1 hdelta_R'
      have h14 : ∑ z ∈ centers, volume (cthickening R' (E z)) ≤
          ∑ z ∈ centers, (16 * C * Kakeya.realRpowENN R' sigma) :=
        Finset.sum_le_sum h13
      have h15 : ∑ z ∈ centers, (16 * C * Kakeya.realRpowENN R' sigma) =
          (centers.card : ENNReal) * (16 * C * Kakeya.realRpowENN R' sigma) := by
        simp [Finset.sum_const] <;> ring
      have h16 : Kakeya.realRpowENN R' sigma ≤ 21 * Kakeya.realRpowENN rho sigma := by
        simp only [Kakeya.realRpowENN]
        have hpos2 : 0 < rho := by linarith
        have h1 : Real.rpow R' sigma ≤ Real.rpow (21 * rho) sigma :=
          Real.rpow_le_rpow (by linarith) hR'_le21rho hsigma.le
        have h2 : Real.rpow (21 * rho) sigma = Real.rpow 21 sigma * Real.rpow rho sigma :=
          Real.mul_rpow (by norm_num) (by linarith)
        have h3 : Real.rpow 21 sigma ≤ 21 := by
          have h4 : Real.rpow 21 sigma ≤ Real.rpow 21 1 :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          have h5 : Real.rpow 21 1 = 21 := by simp
          rw [h5] at h4
          exact h4
        have h6 : Real.rpow R' sigma ≤ 21 * Real.rpow rho sigma := by
          calc Real.rpow R' sigma ≤ Real.rpow (21 * rho) sigma := h1
            _ = Real.rpow 21 sigma * Real.rpow rho sigma := h2
            _ ≤ 21 * Real.rpow rho sigma := by
              have hpos : 0 ≤ Real.rpow rho sigma := Real.rpow_nonneg (by linarith) sigma
              exact mul_le_mul_of_nonneg_right h3 hpos
        have h7 : ENNReal.ofReal (Real.rpow R' sigma) ≤
            ENNReal.ofReal (21 * Real.rpow rho sigma) := ENNReal.ofReal_le_ofReal h6
        have h8 : ENNReal.ofReal (21 * Real.rpow rho sigma) =
            (21 : ENNReal) * ENNReal.ofReal (Real.rpow rho sigma) := by
          have h9 : ENNReal.ofReal (21 * Real.rpow rho sigma) =
              ENNReal.ofReal (21 : ℝ) * ENNReal.ofReal (Real.rpow rho sigma) :=
            ENNReal.ofReal_mul (by positivity)
          rw [h9]
          have h10 : ENNReal.ofReal (21 : ℝ) = (21 : ENNReal) := by simp
          rw [h10]
        simpa using h7.trans (le_of_eq h8)
      set X := Kakeya.realRpowENN rho sigma with hX
      have h2 : (43 : ENNReal) * (16 * (21 * X)) ≤ 14448 * X := by
        have h3 : (43 : ENNReal) * (16 * (21 * X)) =
            ((43 : ENNReal) * 16 * 21) * X := by
          simp [mul_assoc] <;> rfl
        rw [h3]
        have h4 : (43 : ENNReal) * 16 * 21 = (14448 : ENNReal) := by norm_num
        rw [h4] <;> rfl
      have h5 : (43 : ENNReal) * (16 * C * (21 * X)) =
          C * ((43 : ENNReal) * (16 * (21 * X))) := by
        simp [mul_assoc, mul_comm, mul_left_comm] <;> rfl
      have h_const : (43 : ENNReal) * (16 * C * (21 * X)) ≤ 14448 * C * X := by
        calc (43 : ENNReal) * (16 * C * (21 * X))
          = C * ((43 : ENNReal) * (16 * (21 * X))) := h5
        _ ≤ C * (14448 * X) := by
          exact mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = 14448 * C * X := by
          simp [mul_assoc, mul_comm, mul_left_comm] <;> rfl
      calc
        volume (sliceAt V t)
          ≤ volume (⋃ z ∈ centers, cthickening R' (E z)) := h11
        _ ≤ ∑ z ∈ centers, volume (cthickening R' (E z)) := h12
        _ ≤ ∑ z ∈ centers, (16 * C * Kakeya.realRpowENN R' sigma) := h14
        _ = (centers.card : ENNReal) * (16 * C * Kakeya.realRpowENN R' sigma) := h15
        _ ≤ (43 : ENNReal) * (16 * C * Kakeya.realRpowENN R' sigma) := by gcongr <;> exact_mod_cast hcard
        _ ≤ (43 : ENNReal) * (16 * C * (21 * X)) := by gcongr
        _ ≤ 14448 * C * X := h_const

    have h_final : volume V' ≤ ENNReal.ofReal 2 * (14448 * C * Kakeya.realRpowENN rho sigma) :=
      volume_by_slices hV'_meas hV'_vert h_slice_bound

    have h_absorb : ENNReal.ofReal 2 * (14448 * C * Kakeya.realRpowENN rho sigma) ≤
        1000000 * C * Kakeya.realRpowENN rho sigma := by
      have h : (ENNReal.ofReal 2 * 14448 : ENNReal) ≤ 1000000 := by norm_num
      simpa [mul_assoc, mul_comm, mul_left_comm] using
        mul_le_mul_right' h (C * Kakeya.realRpowENN rho sigma)

    calc volume U
      ≤ volume V' := measure_mono h2
      _ ≤ ENNReal.ofReal 2 * (14448 * C * Kakeya.realRpowENN rho sigma) := h_final
      _ ≤ 1000000 * C * Kakeya.realRpowENN rho sigma := h_absorb

  · -- LARGE RHO CASE
    have h_large : 20 * rho ≥ 1 := by linarith
    exact twistedUnion_crude_volume_bound
      hsigma hsigma1 hdelta (by linarith) hrho_one hcd hsub hm_pos hC
      hf_nonsing hf_zero hf_formula h_large

end Kakeya.Assouad
