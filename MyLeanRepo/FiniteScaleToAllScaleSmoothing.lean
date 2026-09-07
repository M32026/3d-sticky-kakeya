module

/-
Clean version of finite-scale to all-scale Frostman smoothing.
-/

public import MyLeanRepo.AllScaleFrostman
public import MyLeanRepo.OSWPrelude

@[expose] public section

open MeasureTheory ENNReal Set Classical

namespace WeakTwoEndsSumProduct

noncomputable section

/-- Normalized Lebesgue measure on [0,δ], as pushforward of Lebesgue on [0,1]. -/
def normalizedLebesgueOn (δ : ℝ) (hδ : 0 < δ) : Measure ℝ :=
  Measure.map (fun t : ℝ => δ * t) (volume.restrict (Set.Icc (0 : ℝ) 1))

/-- The smoothing map F(y,u) = (1-δ)*y + u. -/
def smoothingMap (δ : ℝ) (y u : ℝ) : ℝ :=
  (1 - δ) * y + u

/-- Finite-scale Frostman. -/
def IsFiniteScaleFrostman (δ κ C : ℝ) (μ : Measure ℝ) : Prop :=
  μ Set.univ = 1 ∧
    μ.support ⊆ Set.Icc 0 1 ∧
      0 < δ ∧ 0 < κ ∧ κ ≤ 1 ∧ 0 < C ∧
        ∀ (x r : ℝ), δ ≤ r → r ≤ 1 →
          μ (Set.Icc (x - r) (x + r)) ≤ ENNReal.ofReal (C * r ^ κ)

/-- Smoothing constant: 2^(κ+1). -/
def smoothingConstant (κ : ℝ) : ℝ := (2 : ℝ) ^ (κ + 1)

/-- If f maps μ.support into a closed set S, then (map f μ).support ⊆ S. -/
lemma support_map_into_closed {α β : Type*}
    [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
    [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]
    [HereditarilyLindelofSpace α]
    {μ : Measure α} {f : α → β} (hf : Continuous f)
    {S : Set β} (hS : IsClosed S) (h : f '' μ.support ⊆ S) :
    (Measure.map f μ).support ⊆ S := by
  intro z hz
  by_contra hzS
  have h_compl_open : IsOpen Sᶜ := hS.isOpen_compl
  have hzS' : z ∈ Sᶜ := hzS
  have h_mem : Sᶜ ∈ nhds z := h_compl_open.mem_nhds hzS'
  have h_pos : 0 < (Measure.map f μ) Sᶜ :=
    (Measure.mem_support_iff_forall z).mp hz Sᶜ h_mem
  have h_eq : (Measure.map f μ) Sᶜ = μ (f ⁻¹' Sᶜ) := by
    rw [Measure.map_apply hf.measurable h_compl_open.measurableSet]
  rw [h_eq] at h_pos
  have h_preimage : f ⁻¹' Sᶜ ⊆ (μ.support)ᶜ := by
    intro x hx
    have h2 : f x ∈ Sᶜ := hx
    intro h3
    have h4 : f x ∈ f '' μ.support := ⟨x, h3, rfl⟩
    have h5 : f x ∈ S := h h4
    exact h2 h5
  have h6 : μ (f ⁻¹' Sᶜ) = 0 := by
    have h7 : μ (f ⁻¹' Sᶜ) ≤ μ (μ.support)ᶜ := measure_mono h_preimage
    have h8 : μ (μ.support)ᶜ = 0 := Measure.measure_compl_support
    have h9 : μ (f ⁻¹' Sᶜ) ≤ 0 := h7.trans (le_of_eq h8)
    exact le_zero_iff.mp h9
  rw [h6] at h_pos
  simp at h_pos

/-- normalizedLebesgueOn is a probability measure. -/
lemma normalizedLebesgueOn_univ {δ : ℝ} (hδ : 0 < δ) :
    normalizedLebesgueOn δ hδ Set.univ = 1 := by
  have h_meas : Measurable (fun t : ℝ => δ * t) := measurable_const_mul δ
  dsimp only [normalizedLebesgueOn]
  rw [Measure.map_apply h_meas MeasurableSet.univ]
  have h2 : (fun t : ℝ => δ * t) ⁻¹' Set.univ = Set.univ := by simp
  rw [h2]
  have h3 : volume.restrict (Set.Icc (0 : ℝ) 1) Set.univ = volume (Set.Icc (0 : ℝ) 1) := by
    rw [Measure.restrict_apply MeasurableSet.univ] <;> simp
  rw [h3]
  have h4 : volume (Set.Icc (0 : ℝ) 1) = 1 := by
    rw [Real.volume_Icc] <;> norm_num
  rw [h4]

/-- normalizedLebesgueOn support is contained in [0,δ]. -/
lemma normalizedLebesgueOn_support_subset {δ : ℝ} (hδ : 0 < δ) :
    (normalizedLebesgueOn δ hδ).support ⊆ Set.Icc 0 δ := by
  have h_cont : Continuous (fun t : ℝ => δ * t) := continuous_const_mul δ
  have h_supp_restrict : (volume.restrict (Set.Icc (0 : ℝ) 1)).support ⊆ Set.Icc (0 : ℝ) 1 := by
    have h2 : (volume.restrict (Set.Icc (0 : ℝ) 1)).support ⊆ closure (Set.Icc (0 : ℝ) 1) ∩ volume.support :=
      Measure.support_restrict_subset
    have h1 : (volume.restrict (Set.Icc (0 : ℝ) 1)).support ⊆ closure (Set.Icc (0 : ℝ) 1) := by
      intro x hx
      exact (h2 hx).1
    have h3 : closure (Set.Icc (0 : ℝ) 1) = Set.Icc (0 : ℝ) 1 := isClosed_Icc.closure_eq
    rw [h3] at h1
    exact h1
  have h_image : (fun t : ℝ => δ * t) '' (volume.restrict (Set.Icc (0 : ℝ) 1)).support ⊆ Set.Icc (0 : ℝ) δ := by
    intro z hz
    rcases hz with ⟨t, ht, rfl⟩
    have h_t_in : t ∈ Set.Icc (0 : ℝ) 1 := h_supp_restrict ht
    have h_t_nonneg : 0 ≤ t := h_t_in.1
    have h_t_le_one : t ≤ 1 := h_t_in.2
    have h_dt_nonneg : 0 ≤ δ * t := by positivity
    have h_dt_le_delta : δ * t ≤ δ := by
      calc δ * t ≤ δ * 1 := by gcongr
        _ = δ := by ring
    exact ⟨h_dt_nonneg, h_dt_le_delta⟩
  exact support_map_into_closed h_cont isClosed_Icc h_image

/-- normalizedLebesgueOn(S) ≤ (1/δ) * volume(S). -/
lemma normalizedLebesgueOn_le {δ : ℝ} (hδ : 0 < δ) {S : Set ℝ} (hS : MeasurableSet S) :
    normalizedLebesgueOn δ hδ S ≤ ENNReal.ofReal (δ⁻¹) * volume S := by
  have h_meas : Measurable (fun t : ℝ => δ * t) := measurable_const_mul δ
  dsimp only [normalizedLebesgueOn]
  rw [Measure.map_apply h_meas hS]
  have h2 : volume.restrict (Set.Icc (0 : ℝ) 1) ((fun t : ℝ => δ * t) ⁻¹' S) ≤
      volume ((fun t : ℝ => δ * t) ⁻¹' S) := by
    exact Measure.restrict_le_self ((fun t : ℝ => δ * t) ⁻¹' S)
  have h3 : volume ((fun t : ℝ => δ * t) ⁻¹' S) = ENNReal.ofReal (δ⁻¹) * volume S := by
    have h4 := Real.volume_preimage_mul_left hδ.ne' S
    have h5 : ENNReal.ofReal |δ⁻¹| = ENNReal.ofReal δ⁻¹ := by
      have h6 : |δ⁻¹| = δ⁻¹ := by rw [abs_of_pos] <;> positivity
      rw [h6]
    rw [h4, h5]
  calc volume.restrict (Set.Icc (0 : ℝ) 1) ((fun t : ℝ => δ * t) ⁻¹' S)
    ≤ volume ((fun t : ℝ => δ * t) ⁻¹' S) := h2
  _ = ENNReal.ofReal (δ⁻¹) * volume S := h3

/-- Product measure support is contained in product of supports. -/
lemma prod_support_subset {α β : Type*}
    [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
    [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite ν] :
    (μ.prod ν).support ⊆ μ.support ×ˢ ν.support := by
  intro p hp
  have h_y : p.1 ∈ μ.support := by
    by_contra h
    have h1 : ∃ (s : Set α), s ∈ nhds p.1 ∧ μ s = 0 := by
      have h2 : ¬(∀ (t : Set α), t ∈ nhds p.1 → 0 < μ t) := by
        simpa [Measure.mem_support_iff_forall] using h
      push Not at h2
      rcases h2 with ⟨s, hs_nhds, hnotpos⟩
      have h3 : μ s = 0 := by simpa using hnotpos
      exact ⟨s, hs_nhds, h3⟩
    rcases h1 with ⟨s, hs_nhds, hs_zero⟩
    have h4 : ∃ (U : Set α), IsOpen U ∧ p.1 ∈ U ∧ U ⊆ s := by
      have h5 := (nhds_basis_opens p.1).mem_iff.mp hs_nhds
      rcases h5 with ⟨U, ⟨hpU, hU_open⟩, hU_sub⟩
      exact ⟨U, hU_open, hpU, hU_sub⟩
    rcases h4 with ⟨U, hU_open, hpU, hU_sub⟩
    have h5 : μ U = 0 := by
      have h6 : μ U ≤ μ s := measure_mono hU_sub
      rw [hs_zero] at h6
      exact le_zero_iff.mp h6
    have h7 : (μ.prod ν) (U ×ˢ Set.univ) = 0 := by
      rw [Measure.prod_prod U Set.univ, h5, zero_mul]
    have h8 : U ×ˢ Set.univ ∈ nhds p := by
      apply IsOpen.mem_nhds
      · exact hU_open.prod isOpen_univ
      · exact ⟨hpU, trivial⟩
    have h9 : 0 < (μ.prod ν) (U ×ˢ Set.univ) :=
      (Measure.mem_support_iff_forall p).mp hp (U ×ˢ Set.univ) h8
    rw [h7] at h9
    simp at h9
  have h_u : p.2 ∈ ν.support := by
    by_contra h
    have h1 : ∃ (s : Set β), s ∈ nhds p.2 ∧ ν s = 0 := by
      have h2 : ¬(∀ (t : Set β), t ∈ nhds p.2 → 0 < ν t) := by
        simpa [Measure.mem_support_iff_forall] using h
      push Not at h2
      rcases h2 with ⟨s, hs_nhds, hnotpos⟩
      have h3 : ν s = 0 := by simpa using hnotpos
      exact ⟨s, hs_nhds, h3⟩
    rcases h1 with ⟨s, hs_nhds, hs_zero⟩
    have h4 : ∃ (V : Set β), IsOpen V ∧ p.2 ∈ V ∧ V ⊆ s := by
      have h5 := (nhds_basis_opens p.2).mem_iff.mp hs_nhds
      rcases h5 with ⟨V, ⟨hpV, hV_open⟩, hV_sub⟩
      exact ⟨V, hV_open, hpV, hV_sub⟩
    rcases h4 with ⟨V, hV_open, hpV, hV_sub⟩
    have h5 : ν V = 0 := by
      have h6 : ν V ≤ ν s := measure_mono hV_sub
      rw [hs_zero] at h6
      exact le_zero_iff.mp h6
    have h7 : (μ.prod ν) (Set.univ ×ˢ V) = 0 := by
      rw [Measure.prod_prod Set.univ V, h5, mul_zero]
    have h8 : Set.univ ×ˢ V ∈ nhds p := by
      apply IsOpen.mem_nhds
      · exact isOpen_univ.prod hV_open
      · exact ⟨trivial, hpV⟩
    have h9 : 0 < (μ.prod ν) (Set.univ ×ˢ V) :=
      (Measure.mem_support_iff_forall p).mp hp (Set.univ ×ˢ V) h8
    rw [h7] at h9
    simp at h9
  exact ⟨h_y, h_u⟩

/-- Main theorem. -/
theorem finite_scale_to_all_scale_smoothing
    {δ κ C : ℝ} {μ : Measure ℝ}
    (hδ : 0 < δ) (hδ_lt_fourth : δ < 1 / 4)
    (hκ : 0 < κ) (hκ_le_one : κ ≤ 1)
    (h_fin : IsFiniteScaleFrostman δ κ C μ) :
    ∃ (ν : Measure ℝ),
      ν Set.univ = 1 ∧
      ν.support ⊆ Set.Icc 0 1 ∧
      (∀ z ∈ ν.support, ∃ y ∈ μ.support, |z - y| ≤ δ) ∧
      IsAllScaleFrostman κ (smoothingConstant κ * C) ν := by
  have h_unpack : μ Set.univ = 1 ∧ μ.support ⊆ Set.Icc 0 1 ∧ 0 < δ ∧ 0 < κ ∧ κ ≤ 1 ∧ 0 < C ∧ ∀ (x r : ℝ), δ ≤ r → r ≤ 1 → μ (Set.Icc (x - r) (x + r)) ≤ ENNReal.ofReal (C * r ^ κ) := h_fin
  have hμ_univ : μ Set.univ = 1 := h_unpack.1
  have hμ_supp : μ.support ⊆ Set.Icc 0 1 := h_unpack.2.1
  have hC_pos : 0 < C := h_unpack.2.2.2.2.2.1
  have hFrost : ∀ (x r : ℝ), δ ≤ r → r ≤ 1 → μ (Set.Icc (x - r) (x + r)) ≤ ENNReal.ofReal (C * r ^ κ) := h_unpack.2.2.2.2.2.2
  let lamδ : Measure ℝ := normalizedLebesgueOn δ hδ
  let F : ℝ × ℝ → ℝ := fun p => smoothingMap δ p.1 p.2
  let ν : Measure ℝ := Measure.map F (μ.prod lamδ)
  have hlamδ_univ : lamδ Set.univ = 1 := normalizedLebesgueOn_univ hδ
  have hlamδ_supp : lamδ.support ⊆ Set.Icc 0 δ := normalizedLebesgueOn_support_subset hδ
  have h_one_minus_delta_pos : 0 < 1 - δ := by linarith
  have hδ_lt_one : δ < 1 := by linarith
  have h_cont : Continuous F := by
    dsimp only [F, smoothingMap]
    fun_prop
  letI : IsFiniteMeasure lamδ := ⟨by rw [hlamδ_univ] <;> exact ENNReal.one_lt_top⟩
  have h_prod_univ : (μ.prod lamδ) Set.univ = 1 := by
    have h : (μ.prod lamδ) (Set.univ ×ˢ Set.univ) = μ Set.univ * lamδ Set.univ :=
      Measure.prod_prod Set.univ Set.univ
    have h2 : (Set.univ ×ˢ Set.univ : Set (ℝ × ℝ)) = Set.univ := by simp
    rw [h2] at h
    rw [h, hμ_univ, hlamδ_univ] <;> ring
  have h_preimage_univ : F ⁻¹' Set.univ = Set.univ := by simp
  have hν_univ : ν Set.univ = 1 := by
    rw [Measure.map_apply h_cont.measurable MeasurableSet.univ, h_preimage_univ, h_prod_univ]
  have h_prod_supp : (μ.prod lamδ).support ⊆ μ.support ×ˢ lamδ.support :=
    prod_support_subset
  have hF_maps_Icc : F '' ((μ.prod lamδ).support) ⊆ Set.Icc (0 : ℝ) 1 := by
    intro z hz
    rcases hz with ⟨p, hp, rfl⟩
    have h_p1 : p.1 ∈ μ.support := (h_prod_supp hp).1
    have h_p2 : p.2 ∈ lamδ.support := (h_prod_supp hp).2
    have hy : p.1 ∈ Set.Icc 0 1 := hμ_supp h_p1
    have hu : p.2 ∈ Set.Icc 0 δ := hlamδ_supp h_p2
    dsimp only [F, smoothingMap]
    have h11 : 0 ≤ (1 - δ) := by linarith
    have h12 : 0 ≤ p.1 := hy.1
    have h13 : 0 ≤ p.2 := hu.1
    have h1 : 0 ≤ (1 - δ) * p.1 + p.2 := by positivity
    have h12' : p.1 ≤ 1 := hy.2
    have h14 : (1 - δ) * p.1 ≤ 1 - δ := by
      calc (1 - δ) * p.1 ≤ (1 - δ) * 1 := by gcongr
        _ = 1 - δ := by ring
    have h15 : p.2 ≤ δ := hu.2
    have h2 : (1 - δ) * p.1 + p.2 ≤ 1 := by linarith
    exact ⟨h1, h2⟩
  have hν_supp : ν.support ⊆ Set.Icc (0 : ℝ) 1 :=
    support_map_into_closed h_cont isClosed_Icc hF_maps_Icc
  -- δ-neighborhood of μ.support
  let Sδ : Set ℝ := {z | ∃ y ∈ μ.support, |z - y| ≤ δ}
  have hμ_supp_closed : IsClosed μ.support := Measure.isClosed_support
  have hμ_supp_compact : IsCompact μ.support := by
    apply IsCompact.of_isClosed_subset isCompact_Icc hμ_supp_closed
    exact hμ_supp
  have hSδ_closed : IsClosed Sδ := by
    have h_rep : Sδ = (fun p : ℝ × ℝ => p.1 + p.2) '' (μ.support ×ˢ Set.Icc (-δ) δ) := by
      ext z
      simp only [Sδ, Set.mem_image, Set.mem_prod, Set.mem_Icc, Set.mem_setOf_eq]
      constructor
      · rintro ⟨y, hy, hzy⟩
        refine ⟨(y, z - y), ⟨hy, ?_⟩, by ring⟩
        have h_abs : |z - y| ≤ δ := hzy
        exact ⟨by linarith [abs_le.mp h_abs], by linarith [abs_le.mp h_abs]⟩
      · rintro ⟨p, ⟨hp1, hp2⟩, rfl⟩
        refine ⟨p.1, hp1, ?_⟩
        have h_abs : |p.2| ≤ δ := by
          rw [abs_le] <;> exact ⟨by linarith, by linarith⟩
        simpa using h_abs
    rw [h_rep]
    have h_compact : IsCompact (μ.support ×ˢ Set.Icc (-δ) δ) :=
      hμ_supp_compact.prod isCompact_Icc
    have h_cont : Continuous (fun p : ℝ × ℝ => p.1 + p.2) := continuous_fst.add continuous_snd
    exact h_compact.image h_cont |>.isClosed
  have hF_maps_Sδ : F '' ((μ.prod lamδ).support) ⊆ Sδ := by
    intro z hz
    rcases hz with ⟨p, hp, rfl⟩
    have h_p1 : p.1 ∈ μ.support := (h_prod_supp hp).1
    have h_p2 : p.2 ∈ lamδ.support := (h_prod_supp hp).2
    have hy1 : 0 ≤ p.1 := (hμ_supp h_p1).1
    have hy2 : p.1 ≤ 1 := (hμ_supp h_p1).2
    have hu1 : 0 ≤ p.2 := (hlamδ_supp h_p2).1
    have hu2 : p.2 ≤ δ := (hlamδ_supp h_p2).2
    refine ⟨p.1, h_p1, ?_⟩
    dsimp only [F, smoothingMap]
    have h_eq : (1 - δ) * p.1 + p.2 - p.1 = p.2 - δ * p.1 := by ring
    rw [h_eq]
    have h1 : 0 ≤ δ * p.1 := by positivity
    have h2 : δ * p.1 ≤ δ := by
      calc δ * p.1 ≤ δ * 1 := by gcongr
        _ = δ := by ring
    have h3 : -δ ≤ p.2 - δ * p.1 := by
      have h31 : 0 ≤ p.2 := hu1
      have h32 : δ * p.1 ≤ δ := h2
      linarith
    have h4 : p.2 - δ * p.1 ≤ δ := by
      have h41 : p.2 ≤ δ := hu2
      have h42 : 0 ≤ δ * p.1 := h1
      linarith
    exact abs_le.mpr ⟨h3, h4⟩
  have hν_supp_Sδ : ν.support ⊆ Sδ := support_map_into_closed h_cont hSδ_closed hF_maps_Sδ
  have h_near : ∀ z ∈ ν.support, ∃ y ∈ μ.support, |z - y| ≤ δ := by
    intro z hz
    exact hν_supp_Sδ hz
  have hC_ge_one : 1 ≤ C := by
    have h1 : μ (Set.Icc ((1 / 2 : ℝ) - 1) ((1 / 2 : ℝ) + 1)) ≤ ENNReal.ofReal (C * (1 : ℝ) ^ κ) :=
      hFrost (1 / 2 : ℝ) 1 (by linarith) (by norm_num)
    have h3 : μ.support ⊆ Set.Icc ((1 / 2 : ℝ) - 1) ((1 / 2 : ℝ) + 1) := by
        intro x hx
        have h4 : x ∈ Set.Icc 0 1 := hμ_supp hx
        have h5 : (1 / 2 : ℝ) - 1 ≤ x := by linarith [h4.1]
        have h6 : x ≤ (1 / 2 : ℝ) + 1 := by linarith [h4.2]
        exact ⟨h5, h6⟩
    have h_compl_zero : μ (Set.Icc ((1 / 2 : ℝ) - 1) ((1 / 2 : ℝ) + 1))ᶜ = 0 := by
      have h5 : (Set.Icc ((1 / 2 : ℝ) - 1) ((1 / 2 : ℝ) + 1))ᶜ ⊆ μ.supportᶜ := by
        intro x hx
        intro h6
        have h7 : x ∈ μ.support := h6
        have h8 : x ∈ Set.Icc ((1 / 2 : ℝ) - 1) ((1 / 2 : ℝ) + 1) := h3 h7
        exact hx h8
      have h9 : μ (Set.Icc ((1 / 2 : ℝ) - 1) ((1 / 2 : ℝ) + 1))ᶜ ≤ μ μ.supportᶜ := measure_mono h5
      have h10 : μ μ.supportᶜ = 0 := Measure.measure_compl_support
      exact le_zero_iff.mp (h9.trans (le_of_eq h10))
    have h11 : μ Set.univ = μ (Set.Icc ((1 / 2 : ℝ) - 1) ((1 / 2 : ℝ) + 1)) + μ (Set.Icc ((1 / 2 : ℝ) - 1) ((1 / 2 : ℝ) + 1))ᶜ := by
      rw [← measure_union (disjoint_compl_right) measurableSet_Icc.compl] <;> simp
    have h2 : μ (Set.Icc ((1 / 2 : ℝ) - 1) ((1 / 2 : ℝ) + 1)) = 1 := by
      rw [h_compl_zero] at h11
      rw [hμ_univ] at h11
      have h12 : μ (Set.Icc ((1 / 2 : ℝ) - 1) ((1 / 2 : ℝ) + 1)) + 0 = 1 := h11.symm
      simpa using h12
    rw [h2] at h1
    have h6 : (1 : ENNReal) ≤ ENNReal.ofReal (C * (1 : ℝ) ^ κ) := h1
    have h7 : (1 : ℝ) ^ κ = 1 := by simp
    have h8 : C * (1 : ℝ) ^ κ = C := by rw [h7] <;> ring
    rw [h8] at h6
    have h_pos : 0 ≤ C := by positivity
    have h6' : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal C := by simpa using h6
    exact (ENNReal.ofReal_le_ofReal_iff h_pos).mp h6'
  have h_smooth_pos : 0 < smoothingConstant κ * C := by
    have h1 : 0 < smoothingConstant κ := by
      dsimp only [smoothingConstant] <;> positivity
    positivity
  have h_main : ∀ (x r : ℝ), 0 < r →
      ν (Set.Icc (x - r) (x + r)) ≤ ENNReal.ofReal (smoothingConstant κ * C * r ^ κ) := by
    intro x r hr
    let I : Set ℝ := Set.Icc (x - r) (x + r)
    have hI_meas : MeasurableSet I := measurableSet_Icc
    have hF_meas : Measurable F := h_cont.measurable
    have h_preimage_meas : MeasurableSet (F ⁻¹' I) := hF_meas hI_meas
    have hν_I : ν I = (μ.prod lamδ) (F ⁻¹' I) := by
      rw [Measure.map_apply hF_meas hI_meas]
    let J : Set ℝ := Set.Icc ((x - r - δ) / (1 - δ)) ((x + r) / (1 - δ))
    have hJ_meas : MeasurableSet J := measurableSet_Icc
    let yc : ℝ := (2 * x - δ) / (2 * (1 - δ))
    let R : ℝ := (2 * r + δ) / (2 * (1 - δ))
    have hJ_eq : J = Set.Icc (yc - R) (yc + R) := by
      dsimp only [J, yc, R]
      have h_left : (x - r - δ) / (1 - δ) = (2 * x - δ) / (2 * (1 - δ)) - (2 * r + δ) / (2 * (1 - δ)) := by
        field_simp [h_one_minus_delta_pos.ne'] <;> ring
      have h_right : (x + r) / (1 - δ) = (2 * x - δ) / (2 * (1 - δ)) + (2 * r + δ) / (2 * (1 - δ)) := by
        field_simp [h_one_minus_delta_pos.ne'] <;> ring
      rw [h_left, h_right]
    have h_slice_eq : ∀ (y : ℝ), (Prod.mk y ⁻¹' (F ⁻¹' I)) = {u : ℝ | F (y, u) ∈ I} := by
      intro y
      ext u
      simp only [Set.mem_preimage, Set.mem_setOf_eq] <;> rfl
    have h_slice_interval : ∀ (y : ℝ), {u : ℝ | F (y, u) ∈ I} = Set.Icc (x - r - (1 - δ) * y) (x + r - (1 - δ) * y) := by
      intro y
      ext u
      simp only [Set.mem_setOf_eq, Set.mem_Icc]
      dsimp only [F, smoothingMap]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨by linarith, by linarith⟩
      · rintro ⟨h1, h2⟩
        exact ⟨by linarith, by linarith⟩
    have h_slice_le : ∀ (y : ℝ), lamδ ({u : ℝ | F (y, u) ∈ I}) ≤ ENNReal.ofReal (2 * r / δ) := by
      intro y
      rw [h_slice_interval y]
      have h_vol : volume (Set.Icc (x - r - (1 - δ) * y) (x + r - (1 - δ) * y)) = ENNReal.ofReal (2 * r) := by
        rw [Real.volume_Icc] <;> ring_nf <;> norm_num <;> linarith
      calc lamδ (Set.Icc (x - r - (1 - δ) * y) (x + r - (1 - δ) * y))
        ≤ ENNReal.ofReal (δ⁻¹) * volume (Set.Icc (x - r - (1 - δ) * y) (x + r - (1 - δ) * y)) :=
          normalizedLebesgueOn_le hδ measurableSet_Icc
      _ = ENNReal.ofReal (δ⁻¹) * ENNReal.ofReal (2 * r) := by rw [h_vol]
      _ = ENNReal.ofReal (2 * r / δ) := by
        rw [← ENNReal.ofReal_mul (by positivity)] <;> ring_nf
    have h_slice_zero : ∀ y ∉ J, lamδ ({u : ℝ | F (y, u) ∈ I}) = 0 := by
      intro y hy
      have h_supp_empty : Disjoint ({u : ℝ | F (y, u) ∈ I}) lamδ.support := by
        rw [Set.disjoint_left]
        intro u hu1 hu2
        have h_u_in : u ∈ Set.Icc 0 δ := hlamδ_supp hu2
        have hF_in : F (y, u) ∈ I := hu1
        have h11 : 0 ≤ u := h_u_in.1
        have h12 : u ≤ δ := h_u_in.2
        have h13 : x - r ≤ F (y, u) := hF_in.1
        have h14 : F (y, u) ≤ x + r := hF_in.2
        dsimp only [F, smoothingMap] at h13 h14
        have h15 : (1 - δ) * y ≥ x - r - δ := by linarith
        have h16 : (1 - δ) * y ≤ x + r := by linarith
        have h17 : y ≥ (x - r - δ) / (1 - δ) := by
          calc y
            = ((1 - δ) * y) / (1 - δ) := by field_simp [h_one_minus_delta_pos.ne'] <;> ring
          _ ≥ (x - r - δ) / (1 - δ) := by gcongr
        have h18 : y ≤ (x + r) / (1 - δ) := by
          calc y
            = ((1 - δ) * y) / (1 - δ) := by field_simp [h_one_minus_delta_pos.ne'] <;> ring
          _ ≤ (x + r) / (1 - δ) := by gcongr
        have h_y_in_J : y ∈ J := ⟨h17, h18⟩
        exact hy h_y_in_J
      have h_disj : ∀ (x : ℝ), x ∈ {u : ℝ | F (y, u) ∈ I} → x ∉ lamδ.support :=
        Set.disjoint_left.mp h_supp_empty
      have h3 : {u : ℝ | F (y, u) ∈ I} ⊆ lamδ.supportᶜ := by
        intro u hu
        exact h_disj u hu
      have h4 : lamδ ({u : ℝ | F (y, u) ∈ I}) ≤ lamδ lamδ.supportᶜ :=
        measure_mono h3
      have h5 : lamδ lamδ.supportᶜ = 0 := Measure.measure_compl_support
      have h6 : lamδ ({u : ℝ | F (y, u) ∈ I}) ≤ 0 := h4.trans (le_of_eq h5)
      exact le_zero_iff.mp h6
    have h_prod_apply : (μ.prod lamδ) (F ⁻¹' I) =
        ∫⁻ y, lamδ (Prod.mk y ⁻¹' (F ⁻¹' I)) ∂μ :=
      Measure.prod_apply h_preimage_meas
    by_cases h_r_ge_delta : δ ≤ r
    · -- Case r ≥ δ
      have h_indicator : ∀ y, lamδ (Prod.mk y ⁻¹' (F ⁻¹' I)) ≤
          Set.indicator J (fun _ => (1 : ENNReal)) y := by
        intro y
        by_cases hy : y ∈ J
        · have h6 : lamδ (Prod.mk y ⁻¹' (F ⁻¹' I)) ≤ 1 := by
            have h7 : lamδ (Prod.mk y ⁻¹' (F ⁻¹' I)) ≤ lamδ Set.univ :=
              measure_mono (Set.subset_univ _)
            rw [hlamδ_univ] at h7 <;> exact h7
          have h8 : Set.indicator J (fun _ => (1 : ENNReal)) y = 1 := by
            rw [Set.indicator_of_mem hy] <;> simp
          rw [h8]
          exact h6
        · have h22 : (Prod.mk y ⁻¹' (F ⁻¹' I)) = {u : ℝ | F (y, u) ∈ I} := by
            ext u
            simp only [Set.mem_preimage, Set.mem_setOf_eq] <;> rfl
          have h21 : lamδ (Prod.mk y ⁻¹' (F ⁻¹' I)) = 0 := by
            rw [h22]
            exact h_slice_zero y hy
          have h8 : Set.indicator J (fun _ => (1 : ENNReal)) y = 0 := by
            simp [Set.indicator_apply, hy]
          rw [h8, h21] <;> simp
      have h_int : ∫⁻ y, lamδ (Prod.mk y ⁻¹' (F ⁻¹' I)) ∂μ ≤ μ J := by
        calc ∫⁻ y, lamδ (Prod.mk y ⁻¹' (F ⁻¹' I)) ∂μ
          ≤ ∫⁻ y, Set.indicator J (fun _ => (1 : ENNReal)) y ∂μ := lintegral_mono h_indicator
        _ = μ J := by
          rw [lintegral_indicator_const hJ_meas (1 : ENNReal)] <;> ring
      by_cases h_r_le_half : r ≤ 1 / 2
      · -- r ≤ 1/2
        have hR_le_2r : R ≤ 2 * r := by
          dsimp only [R]
          have h_pos : 0 < 1 - δ := h_one_minus_delta_pos
          have h1 : 2 * r + δ ≤ 4 * r * (1 - δ) := by nlinarith
          have h2 : (2 * r + δ) / (2 * (1 - δ)) ≤ 2 * r := by
            calc (2 * r + δ) / (2 * (1 - δ))
              ≤ (4 * r * (1 - δ)) / (2 * (1 - δ)) := by gcongr
            _ = 2 * r := by
              have h3 : 4 * r * (1 - δ) = 2 * r * (2 * (1 - δ)) := by ring
              rw [h3]
              <;> field_simp [h_pos.ne'] <;> ring
          exact h2
        have hJ_sub : J ⊆ Set.Icc (yc - 2 * r) (yc + 2 * r) := by
          rw [hJ_eq]
          intro y hy
          have h_yl : yc - R ≤ y := hy.1
          have h_yr : y ≤ yc + R := hy.2
          have h_left : yc - 2 * r ≤ y := by
            calc yc - 2 * r ≤ yc - R := by gcongr
              _ ≤ y := h_yl
          have h_right : y ≤ yc + 2 * r := by
            calc y ≤ yc + R := h_yr
              _ ≤ yc + 2 * r := by gcongr
          exact ⟨h_left, h_right⟩
        have h2r_ge_delta : δ ≤ 2 * r := by linarith
        have h2r_le_one : 2 * r ≤ 1 := by linarith
        have h_frost : μ (Set.Icc (yc - 2 * r) (yc + 2 * r)) ≤ ENNReal.ofReal (C * (2 * r) ^ κ) :=
          hFrost yc (2 * r) h2r_ge_delta h2r_le_one
        have hμJ : μ J ≤ ENNReal.ofReal (C * (2 * r) ^ κ) := by
          calc μ J ≤ μ (Set.Icc (yc - 2 * r) (yc + 2 * r)) := measure_mono hJ_sub
            _ ≤ ENNReal.ofReal (C * (2 * r) ^ κ) := h_frost
        have h_final : μ J ≤ ENNReal.ofReal (smoothingConstant κ * C * r ^ κ) := by
          calc μ J
            ≤ ENNReal.ofReal (C * (2 * r) ^ κ) := hμJ
          _ = ENNReal.ofReal (C * (2 : ℝ) ^ κ * r ^ κ) := by
            have h_eq : C * (2 * r) ^ κ = C * (2 : ℝ) ^ κ * r ^ κ := by
              have h : (2 * r) ^ κ = (2 : ℝ) ^ κ * r ^ κ := by
                rw [Real.mul_rpow (by norm_num) (by linarith)] <;> ring
              rw [h] <;> ring
            rw [h_eq]
          _ ≤ ENNReal.ofReal (smoothingConstant κ * C * r ^ κ) := by
            have h9 : C * (2 : ℝ) ^ κ * r ^ κ ≤ smoothingConstant κ * C * r ^ κ := by
              dsimp only [smoothingConstant]
              have h10 : (2 : ℝ) ^ κ ≤ (2 : ℝ) ^ (κ + 1) := by
                apply Real.rpow_le_rpow_of_exponent_le
                <;> norm_num <;> linarith
              have h11 : 0 ≤ C * r ^ κ := by positivity
              nlinarith
            have h_pos2 : 0 ≤ smoothingConstant κ * C * r ^ κ := by positivity
            exact (ENNReal.ofReal_le_ofReal_iff h_pos2).mpr h9
        have h_le : ν I ≤ μ J := by
          calc ν I
            = (μ.prod lamδ) (F ⁻¹' I) := hν_I
          _ = ∫⁻ y, lamδ (Prod.mk y ⁻¹' (F ⁻¹' I)) ∂μ := h_prod_apply
          _ ≤ μ J := h_int
        exact h_le.trans h_final
      · -- r > 1/2
        have hν_le_one : ν I ≤ 1 := by
          calc ν I
            = (μ.prod lamδ) (F ⁻¹' I) := hν_I
          _ ≤ (μ.prod lamδ) Set.univ := measure_mono (Set.subset_univ _)
          _ = 1 := h_prod_univ
        have h_bound : (1 : ENNReal) ≤ ENNReal.ofReal (smoothingConstant κ * C * r ^ κ) := by
          have h1 : 1 ≤ smoothingConstant κ * C * r ^ κ := by
            dsimp only [smoothingConstant]
            have h2 : (1 : ℝ) / 2 < r := by linarith
            have h3 : (1 / 2 : ℝ) ^ κ < r ^ κ := Real.rpow_lt_rpow (by linarith) (by linarith) hκ
            have h4 : (2 : ℝ) ^ (κ + 1) * C * r ^ κ ≥ (2 : ℝ) ^ (κ + 1) * 1 * (1 / 2 : ℝ) ^ κ := by
              gcongr <;> linarith [hC_ge_one]
            have h5 : (2 : ℝ) ^ (κ + 1) * (1 / 2 : ℝ) ^ κ = 2 := by
              have h6 : (2 : ℝ) ^ (κ + 1) = (2 : ℝ) ^ κ * 2 := by
                rw [Real.rpow_add (by norm_num)] <;> ring
              rw [h6]
              have h7 : (2 : ℝ) ^ κ * (1 / 2 : ℝ) ^ κ = 1 := by
                rw [← Real.mul_rpow (by norm_num) (by positivity)] <;> norm_num
              have h8 : (2 : ℝ) ^ κ * 2 * (1 / 2 : ℝ) ^ κ = 2 := by
                calc (2 : ℝ) ^ κ * 2 * (1 / 2 : ℝ) ^ κ
                  = 2 * ((2 : ℝ) ^ κ * (1 / 2 : ℝ) ^ κ) := by ring
                _ = 2 * 1 := by rw [h7]
                _ = 2 := by ring
              exact h8
            have h9 : (2 : ℝ) ^ (κ + 1) * C * r ^ κ ≥ 2 := by
              calc (2 : ℝ) ^ (κ + 1) * C * r ^ κ
                ≥ (2 : ℝ) ^ (κ + 1) * 1 * (1 / 2 : ℝ) ^ κ := h4
              _ = (2 : ℝ) ^ (κ + 1) * (1 / 2 : ℝ) ^ κ := by ring
              _ = 2 := h5
            linarith
          have h_pos2 : 0 ≤ smoothingConstant κ * C * r ^ κ := by positivity
          have h1' : (1 : ℝ) ≤ smoothingConstant κ * C * r ^ κ := by
            simpa [smoothingConstant] using h1
          have h_iff : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal (smoothingConstant κ * C * r ^ κ) ↔
              (1 : ℝ) ≤ smoothingConstant κ * C * r ^ κ :=
            ENNReal.ofReal_le_ofReal_iff h_pos2
          have h_goal : (1 : ENNReal) = ENNReal.ofReal (1 : ℝ) := by simp
          rw [h_goal]
          exact h_iff.mpr h1'
        have hμJ_le_one : μ J ≤ 1 := by
          calc μ J ≤ μ Set.univ := measure_mono (Set.subset_univ _)
            _ = 1 := hμ_univ
        have h_le : ν I ≤ ENNReal.ofReal (smoothingConstant κ * C * r ^ κ) := by
          calc ν I
            = (μ.prod lamδ) (F ⁻¹' I) := hν_I
          _ = ∫⁻ y, lamδ (Prod.mk y ⁻¹' (F ⁻¹' I)) ∂μ := h_prod_apply
          _ ≤ μ J := h_int
          _ ≤ 1 := hμJ_le_one
          _ ≤ ENNReal.ofReal (smoothingConstant κ * C * r ^ κ) := h_bound
        exact h_le
    · -- Case r < δ
      have h_r_lt_delta : r < δ := by linarith
      have h_indicator : ∀ y, lamδ (Prod.mk y ⁻¹' (F ⁻¹' I)) ≤
          Set.indicator J (fun _ => ENNReal.ofReal (2 * r / δ)) y := by
        intro y
        by_cases hy : y ∈ J
        · have h9 : Set.indicator J (fun _ => ENNReal.ofReal (2 * r / δ)) y = ENNReal.ofReal (2 * r / δ) := by
            rw [Set.indicator_of_mem hy] <;> simp
          rw [h9]
          rw [h_slice_eq y]
          exact h_slice_le y
        · have h21 : lamδ (Prod.mk y ⁻¹' (F ⁻¹' I)) = 0 := by
            rw [h_slice_eq y]
            exact h_slice_zero y hy
          have h8 : Set.indicator J (fun _ => ENNReal.ofReal (2 * r / δ)) y = 0 := by
            simp [Set.indicator_apply, hy]
          rw [h8, h21] <;> simp
      have h_int : ∫⁻ y, lamδ (Prod.mk y ⁻¹' (F ⁻¹' I)) ∂μ ≤
          ENNReal.ofReal (2 * r / δ) * μ J := by
        calc ∫⁻ y, lamδ (Prod.mk y ⁻¹' (F ⁻¹' I)) ∂μ
          ≤ ∫⁻ y, Set.indicator J (fun _ => ENNReal.ofReal (2 * r / δ)) y ∂μ := lintegral_mono h_indicator
        _ = ENNReal.ofReal (2 * r / δ) * μ J := by
          rw [lintegral_indicator_const hJ_meas (ENNReal.ofReal (2 * r / δ))] <;> ring
      have hR_lt_2δ : R < 2 * δ := by
        dsimp only [R]
        have h1 : 2 * r + δ < 4 * δ * (1 - δ) := by nlinarith
        have h2 : (2 * r + δ) / (2 * (1 - δ)) < 2 * δ := by
          calc (2 * r + δ) / (2 * (1 - δ))
            < (4 * δ * (1 - δ)) / (2 * (1 - δ)) := by gcongr
          _ = 2 * δ := by field_simp [h_one_minus_delta_pos.ne'] <;> ring
        exact h2
      have h2δ_le_one : 2 * δ ≤ 1 := by linarith
      have hJ_sub : J ⊆ Set.Icc (yc - 2 * δ) (yc + 2 * δ) := by
        rw [hJ_eq]
        intro y hy
        have h_yl : yc - R ≤ y := hy.1
        have h_yr : y ≤ yc + R := hy.2
        have h_left : yc - 2 * δ ≤ y := by
          calc yc - 2 * δ ≤ yc - R := by gcongr <;> linarith [hR_lt_2δ]
            _ ≤ y := h_yl
        have h_right : y ≤ yc + 2 * δ := by
          calc y ≤ yc + R := h_yr
            _ ≤ yc + 2 * δ := by gcongr <;> linarith [hR_lt_2δ]
        exact ⟨h_left, h_right⟩
      have h_frost : μ (Set.Icc (yc - 2 * δ) (yc + 2 * δ)) ≤ ENNReal.ofReal (C * (2 * δ) ^ κ) :=
        hFrost yc (2 * δ) (by linarith) h2δ_le_one
      have hμJ : μ J ≤ ENNReal.ofReal (C * (2 * δ) ^ κ) := by
        calc μ J ≤ μ (Set.Icc (yc - 2 * δ) (yc + 2 * δ)) := measure_mono hJ_sub
          _ ≤ ENNReal.ofReal (C * (2 * δ) ^ κ) := h_frost
      have h_rpow : r * δ ^ (κ - 1) ≤ r ^ κ := by
        have h1 : 0 ≤ 1 - κ := by linarith
        have h2 : r ^ (1 - κ) ≤ δ ^ (1 - κ) := Real.rpow_le_rpow (by positivity) (by linarith) h1
        have h3 : r * δ ^ (κ - 1) = r ^ κ * (r / δ) ^ (1 - κ) := by
          have h4 : r ^ κ * r ^ (1 - κ) = r := by
            rw [← Real.rpow_add (by positivity)] <;> ring_nf <;> rw [Real.rpow_one]
          have h5 : r * δ ^ (κ - 1) = r ^ κ * (r ^ (1 - κ) * δ ^ (κ - 1)) := by
            calc r * δ ^ (κ - 1)
              = (r ^ κ * r ^ (1 - κ)) * δ ^ (κ - 1) := by rw [h4]
            _ = r ^ κ * (r ^ (1 - κ) * δ ^ (κ - 1)) := by ring
          rw [h5]
          have h6 : r ^ (1 - κ) * δ ^ (κ - 1) = (r / δ) ^ (1 - κ) := by
            have h7 : κ - 1 = -(1 - κ) := by ring
            rw [h7]
            have h8 : δ ^ (-(1 - κ)) = (δ ^ (1 - κ))⁻¹ := by
              rw [Real.rpow_neg (by positivity)] <;> ring
            rw [h8]
            have h9 : (r / δ) ^ (1 - κ) = r ^ (1 - κ) * (δ ^ (1 - κ))⁻¹ := by
              have h10 : (r / δ) ^ (1 - κ) = r ^ (1 - κ) / δ ^ (1 - κ) := by
                rw [Real.div_rpow (by positivity) (by positivity)]
              rw [h10, div_eq_mul_inv]
            rw [h9] <;> ring
          rw [h6] <;> ring
        rw [h3]
        have h4 : (r / δ) ^ (1 - κ) ≤ 1 := by
          have h5 : 0 ≤ 1 - κ := by linarith
          have h6 : r / δ ≤ 1 := by
            have h61 : r ≤ δ := by linarith
            have h62 : r / δ ≤ δ / δ := by gcongr
            have h63 : δ / δ = 1 := by
              field_simp [hδ.ne'] <;> ring
            rw [h63] at h62
            exact h62
          have h7 : 0 ≤ r / δ := by positivity
          exact Real.rpow_le_one h7 h6 h5
        have h5 : r ^ κ * (r / δ) ^ (1 - κ) ≤ r ^ κ * 1 := by gcongr
        have h6 : r ^ κ * 1 = r ^ κ := by ring
        rw [h6] at h5
        exact h5
      have h_final : ENNReal.ofReal (2 * r / δ) * μ J ≤
          ENNReal.ofReal (smoothingConstant κ * C * r ^ κ) := by
        calc ENNReal.ofReal (2 * r / δ) * μ J
          ≤ ENNReal.ofReal (2 * r / δ) * ENNReal.ofReal (C * (2 * δ) ^ κ) := by gcongr
        _ = ENNReal.ofReal ((2 * r / δ) * (C * (2 * δ) ^ κ)) := by
          rw [← ENNReal.ofReal_mul (by positivity)] <;> ring
        _ = ENNReal.ofReal (smoothingConstant κ * C * (r * δ ^ (κ - 1))) := by
          have h_eq : (2 * r / δ) * (C * (2 * δ) ^ κ) = smoothingConstant κ * C * (r * δ ^ (κ - 1)) := by
            dsimp only [smoothingConstant]
            have h1 : (2 * δ) ^ κ = (2 : ℝ) ^ κ * δ ^ κ := by
              rw [Real.mul_rpow (by norm_num) (by linarith)] <;> ring
            have h3 : δ ^ (κ - 1) = δ ^ κ / δ := by
              have h4 : κ - 1 = κ + (-1 : ℝ) := by ring
              rw [h4]
              rw [Real.rpow_add (by positivity)]
              have h5 : δ ^ (-1 : ℝ) = (δ ^ (1 : ℝ))⁻¹ := by
                rw [Real.rpow_neg (by positivity)]
                <;> simp
              have h6 : δ ^ (1 : ℝ) = δ := Real.rpow_one δ
              rw [h5, h6] <;> ring
            rw [h1, h3]
            have h4 : (2 * r / δ) * (C * ((2 : ℝ) ^ κ * δ ^ κ)) =
                (2 : ℝ) ^ (κ + 1) * C * (r * (δ ^ κ / δ)) := by
              have h5 : (2 * r / δ) * (C * ((2 : ℝ) ^ κ * δ ^ κ)) =
                  (2 : ℝ) ^ κ * C * (2 * r) * (δ ^ κ / δ) := by
                field_simp [hδ.ne'] <;> ring
              rw [h5]
              have h6 : (2 : ℝ) ^ (κ + 1) = (2 : ℝ) ^ κ * 2 := by
                rw [Real.rpow_add (by norm_num)] <;> ring
              rw [h6] <;> ring
            exact h4
          rw [h_eq]
        _ ≤ ENNReal.ofReal (smoothingConstant κ * C * r ^ κ) := by
          have h10 : smoothingConstant κ * C * (r * δ ^ (κ - 1)) ≤ smoothingConstant κ * C * r ^ κ := by
            gcongr
            <;> exact h_rpow
          have h_pos2 : 0 ≤ smoothingConstant κ * C * r ^ κ := by positivity
          exact (ENNReal.ofReal_le_ofReal_iff h_pos2).mpr h10
      have h_le : ν I ≤ ENNReal.ofReal (smoothingConstant κ * C * r ^ κ) := by
        calc ν I
          = (μ.prod lamδ) (F ⁻¹' I) := hν_I
        _ = ∫⁻ y, lamδ (Prod.mk y ⁻¹' (F ⁻¹' I)) ∂μ := h_prod_apply
        _ ≤ ENNReal.ofReal (2 * r / δ) * μ J := h_int
        _ ≤ ENNReal.ofReal (smoothingConstant κ * C * r ^ κ) := h_final
      exact h_le
  exact ⟨ν, hν_univ, hν_supp, h_near, ⟨hν_univ, hκ, h_smooth_pos, h_main⟩⟩

end

end WeakTwoEndsSumProduct
