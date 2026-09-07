import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.Basic
import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.CoareaFinalAssembly
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.PerimeterDensityOne
import Mathlib.Tactic


open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory

namespace Geometry

variable {n : ℕ} [Nonempty (Fin n)]

/-! # Helper lemmas for mollification_good_level_sequence -/

/-- Perimeter is invariant under modifications by Lebesgue-null sets. -/
lemma perimeter_eq_of_symmDiff_null {A B : Set (E n)}
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (h_null : volume (symmDiff A B) = 0) :
    Perimeter.perimeter A = Perimeter.perimeter B := by
  have h_ae : ∀ᵐ x ∂volume, x ∈ A ↔ x ∈ B := by
    have h : ∀ᵐ x ∂volume, x ∉ symmDiff A B := by
      simpa [ae_iff] using h_null
    filter_upwards [h] with x hx
    constructor
    · intro hA; by_contra hB; exact hx (Or.inl ⟨hA, hB⟩)
    · intro hB; by_contra hA; exact hx (Or.inr ⟨hB, hA⟩)
  have h1 : ∀ (φ : Perimeter.TestVectorField),
      (∫ x in A, Perimeter.divergence φ.toFun x) =
      (∫ x in B, Perimeter.divergence φ.toFun x) := by
    intro φ
    have h_ind_ae : (Set.indicator A (Perimeter.divergence φ.toFun)) =ᵐ[volume]
        (Set.indicator B (Perimeter.divergence φ.toFun)) := by
      filter_upwards [h_ae] with x hx
      have h_iff : x ∈ A ↔ x ∈ B := hx
      by_cases h : x ∈ A
      · have h' : x ∈ B := h_iff.mp h
        simp [Set.indicator_apply, h, h']
      · have h' : x ∉ B := by
          intro h''; exact h (h_iff.mpr h'')
        simp [Set.indicator_apply, h, h']
    have h_eq : ∫ (x : E n), Set.indicator A (Perimeter.divergence φ.toFun) x =
        ∫ (x : E n), Set.indicator B (Perimeter.divergence φ.toFun) x :=
      integral_congr_ae h_ind_ae
    have hA_eq : (∫ x in A, Perimeter.divergence φ.toFun x) =
        ∫ (x : E n), Set.indicator A (Perimeter.divergence φ.toFun) x := by
      exact Eq.symm (integral_indicator hA)
    have hB_eq : (∫ x in B, Perimeter.divergence φ.toFun x) =
        ∫ (x : E n), Set.indicator B (Perimeter.divergence φ.toFun) x := by
      exact Eq.symm (integral_indicator hB)
    rw [hA_eq, hB_eq, h_eq]
  simp only [Perimeter.perimeter]
  congr with φ
  have h_eq2 := h1 φ
  rw [h_eq2]

/-- For a measurable `u` with `0 ≤ u ≤ 1`,
`volume {u = s} = 0` for a.e. `s ∈ (0,1]`. -/
lemma volume_level_set_zero_ae
    {u : E n → ℝ} (hu : Measurable u)
    (h0 : ∀ x, 0 ≤ u x) (h1 : ∀ x, u x ≤ 1) :
    ∀ᵐ s ∂volume.restrict (Set.Ioc (0 : ℝ) 1),
      volume {x | u x = s} = 0 := by
  have h1 : Measurable (fun p : E n × ℝ => u p.1) := hu.comp measurable_fst
  have h2 : Measurable (fun p : E n × ℝ => p.2) := measurable_snd
  let S_eq : Set (E n × ℝ) := {p | u p.1 = p.2}
  have hS_eq_meas : MeasurableSet S_eq := by
    have h3 : MeasurableSet {p : E n × ℝ | u p.1 = p.2} := by exact measurableSet_eq_fun h1 h2
    exact h3
  let f : E n × ℝ → ENNReal := Set.indicator S_eq (fun _ => (1 : ENNReal))
  have hf_meas : Measurable f :=
    (measurable_const : Measurable (fun _ : E n × ℝ => (1 : ENNReal))).indicator hS_eq_meas
  have h3 : ∀ (s : ℝ), volume {x | u x = s} = ∫⁻ x : E n, f (x, s) := by
    intro s
    have h_set_meas : MeasurableSet {x | u x = s} :=
      hu (isClosed_singleton.measurableSet)
    have h4 : (fun x : E n => f (x, s)) = Set.indicator {x | u x = s} (fun _ : E n => (1 : ENNReal)) := by
      funext x
      simp [f, S_eq]
      <;> aesop
    rw [h4]
    have h5 : ∫⁻ (x : E n), Set.indicator {x | u x = s} (fun _ : E n => (1 : ENNReal)) x =
        volume {x | u x = s} := by
      rw [lintegral_indicator h_set_meas]
      <;> simp
    exact h5.symm
  have h_prod : ∫⁻ (p : E n × ℝ) in (Set.univ ×ˢ Set.Ioc (0 : ℝ) 1), f p =
      ∫⁻ (s : ℝ) in Set.Ioc (0 : ℝ) 1, ∫⁻ (x : E n), f (x, s) := by
    have h : ∫⁻ (p : E n × ℝ) in (Set.univ ×ˢ Set.Ioc (0 : ℝ) 1), f p =
        ∫⁻ (s : ℝ) in Set.Ioc (0 : ℝ) 1, ∫⁻ (x : E n) in Set.univ, f (x, s) := by
      exact MeasureTheory.setLIntegral_prod_symm (μ := volume) (ν := volume)
        (s := Set.univ) (t := Set.Ioc (0 : ℝ) 1) f hf_meas.aemeasurable
    have h' : ∀ (s : ℝ), (∫⁻ (x : E n) in Set.univ, f (x, s)) = ∫⁻ (x : E n), f (x, s) := by
      intro s; simp
    rw [h]
    congr with s
    exact h' s
  have h_main1 : ∫⁻ s in Set.Ioc (0 : ℝ) 1, volume {x | u x = s} =
      ∫⁻ (p : E n × ℝ) in (Set.univ ×ˢ Set.Ioc (0 : ℝ) 1), f p := by
    simp_rw [h3]
    exact h_prod.symm
  have h_inner : ∀ (x : E n), ∫⁻ s in Set.Ioc (0 : ℝ) 1, f (x, s) = 0 := by
    intro x
    have h2 : ∀ᵐ s ∂volume.restrict (Set.Ioc (0 : ℝ) 1), f (x, s) = 0 := by
      have h3 : {s ∈ Set.Ioc (0 : ℝ) 1 | f (x, s) ≠ 0} ⊆ {u x} := by
        intro s hs
        have h4 : f (x, s) ≠ 0 := hs.2
        have h5 : u x = s := by
          simp [f, S_eq] at h4 <;> tauto
        exact h5.symm
      have h4 : volume {s ∈ Set.Ioc (0 : ℝ) 1 | f (x, s) ≠ 0} = 0 :=
        measure_mono_null h3 (measure_singleton _)
      have h5 : ∀ᵐ s ∂volume.restrict (Set.Ioc (0 : ℝ) 1), f (x, s) = 0 := by
        have h_meas : MeasurableSet (Set.Ioc (0 : ℝ) 1) := by exact measurableSet_Ioc
        rw [MeasureTheory.ae_restrict_iff' h_meas]
        rw [ae_iff]
        have h7 : {s : ℝ | ¬(s ∈ Set.Ioc (0 : ℝ) 1 → f (x, s) = 0)} =
            {s | s ∈ Set.Ioc (0 : ℝ) 1 ∧ f (x, s) ≠ 0} := by
          ext s
          simp [Set.mem_setOf_eq]
          <;> tauto
        rw [h7]
        exact h4
      exact h5
    have h3 : ∫⁻ s in Set.Ioc (0 : ℝ) 1, f (x, s) = 0 := by
      rw [lintegral_congr_ae h2]
      <;> simp
    exact h3
  have h4 : ∫⁻ (x : E n), ∫⁻ s in Set.Ioc (0 : ℝ) 1, f (x, s) = 0 := by
    have h5 : (fun x : E n => ∫⁻ s in Set.Ioc (0 : ℝ) 1, f (x, s)) =ᵐ[volume] fun _ => (0 : ENNReal) := by
      filter_upwards with x
      exact h_inner x
    rw [lintegral_congr_ae h5] <;> simp
  have h5 : ∫⁻ s in Set.Ioc (0 : ℝ) 1, volume {x | u x = s} = 0 := by
    rw [h_main1]
    have h6 : ∫⁻ (p : E n × ℝ) in (Set.univ ×ˢ Set.Ioc (0 : ℝ) 1), f p =
        ∫⁻ (x : E n), ∫⁻ s in Set.Ioc (0 : ℝ) 1, f (x, s) := by
      have h7 := MeasureTheory.setLIntegral_prod (μ := volume) (ν := volume)
        (s := Set.univ) (t := Set.Ioc (0 : ℝ) 1) f hf_meas.aemeasurable
      have h_vol : (volume : Measure (E n × ℝ)) = volume.prod volume := by exact Measure.volume_eq_prod (E n) ℝ
      rw [h_vol]
      simpa using h7
    rw [h6, h4]
  have h_ae_meas : AEMeasurable (fun s : ℝ => volume {x | u x = s})
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    have h_eq : (fun s : ℝ => volume {x | u x = s}) = fun s : ℝ => ∫⁻ (x : E n), f (x, s) := by
      funext s; exact h3 s
    rw [h_eq]
    have h_meas : Measurable (fun s : ℝ => ∫⁻ (x : E n), f (x, s)) :=
      hf_meas.lintegral_prod_left'
    exact h_meas.aemeasurable
  have h6 : ∀ᵐ s ∂volume.restrict (Set.Ioc (0 : ℝ) 1), volume {x | u x = s} = 0 := by
    rwa [MeasureTheory.lintegral_eq_zero_iff' h_ae_meas] at h5
  exact h6

/-- For a C¹ compactly supported `u` with `0 ≤ u ≤ 1`,
`μHE[n-1] {u = s} < ⊤` for a.e. `s ∈ (0,1]`. -/
lemma hausdorff_level_set_finite_ae
    {u : E n → ℝ} (hu : ContDiff ℝ 1 u)
    (h_support : HasCompactSupport u)
    (h0 : ∀ x, 0 ≤ u x) (h1 : ∀ x, u x ≤ 1)
    (hn : 2 ≤ n) :
    ∀ᵐ s ∂volume.restrict (Set.Ioc (0 : ℝ) 1),
      μHE[n - 1] {x | u x = s} < ⊤ := by
  let F : E n → ENNReal := fun x => ENNReal.ofReal ‖fderiv ℝ u x‖
  let G : ENNReal := ∫⁻ x, F x
  let K : Set (E n) := tsupport u
  have hK_compact : IsCompact K := h_support
  have hK_meas : MeasurableSet K := hK_compact.measurableSet
  have hK_bdd : Bornology.IsBounded K := hK_compact.isBounded
  have hG_finite : G < ⊤ := by
    have h_cont : Continuous (fun x => ‖fderiv ℝ u x‖) :=
      (hu.continuous_fderiv (by norm_num)).norm
    rcases hK_compact.bddAbove_image h_cont.continuousOn with ⟨M, hM⟩
    let M' := max M 0
    have hM' : ∀ (x : E n), x ∈ K → ‖fderiv ℝ u x‖ ≤ M' := by
      intro x hx
      have h : ‖fderiv ℝ u x‖ ≤ M := hM ⟨x, hx, rfl⟩
      exact le_trans h (le_max_left _ _)
    have h_outside : ∀ x ∉ K, fderiv ℝ u x = 0 := by
      intro x hx
      have h8 : Kᶜ ∈ nhds x := hK_compact.isClosed.isOpen_compl.mem_nhds hx
      have h9 : ∀ y ∈ Kᶜ, u y = 0 := by
        intro y hy
        have hK_def : K = closure (Function.support u) := by simp [K, tsupport]
        rw [hK_def] at hy
        have h10 : y ∉ Function.support u := fun h => hy (subset_closure h)
        simpa [Function.mem_support] using h10
      have h7 : u =ᶠ[nhds x] 0 := by
        filter_upwards [h8] with y hy
        exact h9 y hy
      rw [h7.fderiv_eq] <;> simp
    have h_ae : F =ᵐ[volume] Set.indicator K F := by
      filter_upwards with x
      by_cases hx : x ∈ K
      · simp [F, hx, Set.indicator_apply]
      · have h10 : fderiv ℝ u x = 0 := h_outside x hx
        have h11 : F x = 0 := by
          dsimp only [F]
          rw [h10]
          simp
        have h12 : (Set.indicator K F) x = 0 := by simp [Set.indicator_apply, hx]
        rw [h11, h12]
    have h10 : ∫⁻ (x : E n), F x = ∫⁻ (x : E n), (Set.indicator K F) x :=
      lintegral_congr_ae h_ae
    have h_ind : ∫⁻ (x : E n), (Set.indicator K F) x = ∫⁻ (x : E n) in K, F x :=
      MeasureTheory.lintegral_indicator hK_meas F
    have h9 : G = ∫⁻ x in K, F x := by
      simp only [G]
      rw [h10, h_ind]
    rw [h9]
    have h10 : ∫⁻ x in K, F x ≤ ENNReal.ofReal M' * volume K := by
      have h11 : ∫⁻ x in K, F x ≤ ∫⁻ x in K, ENNReal.ofReal M' := by
        apply setLIntegral_mono' hK_meas
        intro x _
        exact ENNReal.ofReal_le_ofReal (hM' x ‹_›)
      simpa using h11
    exact lt_top_iff_ne_top.mpr (ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hK_compact.measure_lt_top.ne) h10)
  have h_coarea : ∫⁻ s in Set.Ioc (0 : ℝ) 1, μHE[n - 1] {x | u x = s} ≤
      ENNReal.ofReal (1 + (1 : ℝ)) * G :=
    coarea_hausdorff_smooth_upper u hu h_support h0 h1 (1 : ℝ) (by norm_num) hn
  have h_finite : (∫⁻ s in Set.Ioc (0 : ℝ) 1, μHE[n - 1] {x | u x = s}) < ⊤ := by
    have h10 : ENNReal.ofReal (1 + (1 : ℝ)) * G < ⊤ :=
      ENNReal.mul_lt_top (by simp) hG_finite
    exact h_coarea.trans_lt h10
  rcases hu.lipschitzWith_of_hasCompactSupport h_support (by norm_num) with ⟨L, hL⟩
  have h_level_eq : ∀ s ∈ Set.Ioc (0 : ℝ) 1, K ∩ u ⁻¹' {s} = {x | u x = s} := by
    intro s hs
    have h_s_pos : 0 < s := hs.1
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
    constructor
    · rintro ⟨_, h⟩; exact h
    · intro h
      have h_u_x_ne_zero : u x ≠ 0 := by
        rw [h]; linarith
      have h_x_support : x ∈ Function.support u := Function.mem_support.mpr h_u_x_ne_zero
      have h_x_K : x ∈ K := subset_closure h_x_support
      exact ⟨h_x_K, h⟩
  have h_aemeas_unscaled : AEMeasurable (fun s : ℝ => μHE[n - 1] (K ∩ u ⁻¹' {s})) volume :=
    levelSet_aemeasurable_lipschitz hn hL hK_meas hK_bdd
  rcases h_aemeas_unscaled with ⟨g, hg_meas, hg_eq⟩
  have h_restrict_eq : (fun s : ℝ => μHE[n - 1] {x | u x = s}) =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] g := by
    have h1 : ∀ᵐ s ∂volume.restrict (Set.Ioc (0 : ℝ) 1), s ∈ Set.Ioc (0 : ℝ) 1 :=
      self_mem_ae_restrict (by exact measurableSet_Ioc)
    have h_filter : ae (volume.restrict (Set.Ioc (0 : ℝ) 1)) ≤ ae volume := by exact ae_restrict_le
    have hg_eq' : (fun s : ℝ => μHE[n - 1] (K ∩ u ⁻¹' {s})) =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] g :=
      hg_eq.filter_mono h_filter
    filter_upwards [hg_eq', h1] with s hsg hsmem
    have h2 : μHE[n - 1] (K ∩ u ⁻¹' {s}) = g s := hsg
    have h3 : K ∩ u ⁻¹' {s} = {x | u x = s} := h_level_eq s hsmem
    rw [h3] at h2
    exact h2
  have h_aemeas : AEMeasurable (fun s : ℝ => μHE[n - 1] {x | u x = s})
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    ⟨g, hg_meas, h_restrict_eq⟩
  exact MeasureTheory.ae_lt_top' h_aemeas h_finite.ne

/-- Topological fact: `interior (closure (interior (closure A))) = interior (closure A)`. -/
lemma interior_closure_idempotent {A : Set (E n)} :
    interior (closure (interior (closure A))) = interior (closure A) := by
  let U := interior (closure A)
  have h1 : U ⊆ closure A := interior_subset
  have h2 : closure U ⊆ closure (closure A) := closure_mono h1
  have h2' : closure (closure A) = closure A := closure_closure
  have h3 : interior (closure U) ⊆ interior (closure A) := by
    rw [h2'] at h2; exact interior_mono h2
  have h4 : U ⊆ interior (closure U) := by
    have hU_open : IsOpen U := isOpen_interior
    exact hU_open.subset_interior_closure
  exact Set.Subset.antisymm h3 h4

/-- For continuous `u`, `frontier (interior (closure {u > s})) ⊆ {u = s}`. -/
lemma frontier_regularized_level_set_subset {u : E n → ℝ} (hu : Continuous u) {s : ℝ} :
    frontier (interior (closure {x | u x > s})) ⊆ {x | u x = s} := by
  let A := {x | u x > s}
  let V := interior (closure A)
  have h1 : closure A ⊆ {x | u x ≥ s} := by
    have h2 : IsClosed {x | u x ≥ s} := isClosed_Ici.preimage hu
    have h3 : A ⊆ {x | u x ≥ s} := by
      intro x hx
      have h4 : u x > s := hx
      exact le_of_lt h4
    exact closure_minimal h3 h2
  have h4 : closure V ⊆ closure (closure A) := by
    have h5 : V ⊆ closure A := interior_subset
    exact closure_mono h5
  have h4' : closure (closure A) = closure A := closure_closure
  have h4'' : closure V ⊆ closure A := by rw [h4'] at h4; exact h4
  have h6 : A ⊆ V := by
    have h7 : IsOpen A := isOpen_Ioi.preimage hu
    exact h7.subset_interior_closure
  have hV_open : IsOpen V := isOpen_interior
  have h7 : frontier V = closure V \ V := by
    have h71 : closure V \ interior V = frontier V := closure_sdiff_interior V
    have h72 : interior V = V := hV_open.interior_eq
    rw [h72] at h71
    exact h71.symm
  have h7' : frontier V ⊆ closure V \ V := by rw [h7] <;> exact subset_refl _
  have h8 : closure V \ V ⊆ closure A \ A := by
    intro x hx
    have h9 : x ∈ closure V := hx.1
    have h10 : x ∉ V := hx.2
    have h11 : x ∈ closure A := h4'' h9
    have h12 : x ∉ A := by
      intro h13
      exact h10 (h6 h13)
    exact ⟨h11, h12⟩
  have h9 : closure A \ A ⊆ {x | u x = s} := by
    intro x hx
    have h10 : x ∈ closure A := hx.1
    have h11 : x ∉ A := hx.2
    have h12 : u x ≥ s := h1 h10
    have h13 : ¬(u x > s) := h11
    have h14 : u x ≤ s := not_lt.mp h13
    have h15 : u x = s := le_antisymm h14 h12
    exact h15
  intro x hx
  exact h9 (h8 (h7' hx))

/-- If `volume {u = s} = 0`, then `volume (V_s △ {u > s}) = 0`. -/
lemma regularized_symmDiff_null {u : E n → ℝ} (hu : Continuous u) {s : ℝ}
    (h_null : volume {x | u x = s} = 0) :
    volume (symmDiff (interior (closure {x | u x > s})) {x | u x > s}) = 0 := by
  let A := {x | u x > s}
  let V := interior (closure A)
  have h1 : A ⊆ V := by
    have h2 : IsOpen A := isOpen_Ioi.preimage hu
    exact h2.subset_interior_closure
  have h3 : V \ A ⊆ {x | u x = s} := by
    intro x hx
    have h4 : x ∈ V := hx.1
    have h5 : x ∉ A := hx.2
    have h7 : closure A ⊆ {x | u x ≥ s} := by
      have h8 : IsClosed {x | u x ≥ s} := isClosed_Ici.preimage hu
      have h9 : A ⊆ {x | u x ≥ s} := by
        intro y hy
        have h10 : u y > s := hy
        exact le_of_lt h10
      exact closure_minimal h9 h8
    have h61 : V ⊆ interior {x | u x ≥ s} := interior_mono h7
    have h62 : interior {x | u x ≥ s} ⊆ {x | u x ≥ s} := interior_subset
    have h6 : V ⊆ {x | u x ≥ s} := h61.trans h62
    have h7' : u x ≥ s := h6 h4
    have h8' : ¬(u x > s) := h5
    have h9' : u x ≤ s := not_lt.mp h8'
    have h10' : u x = s := le_antisymm h9' h7'
    exact h10'
  have h10 : volume (V \ A) = 0 := measure_mono_null h3 h_null
  have h11 : symmDiff V A = V \ A := by
    ext x
    simp only [mem_symmDiff, mem_diff]
    constructor
    · rintro (h | h)
      · exact h
      · exfalso; exact h.2 (h1 h.1)
    · intro h; exact Or.inl h
  rw [h11]
  exact h10

/-- **Pointwise level-set perimeter bound**: For a specific `s ∈ (0,1)` with
`volume {u = s} = 0` and `μHE[n-1] {u = s} < ⊤`,
`perimeter {u > s} ≤ μHE[n-1] {u = s}`. -/
lemma perimeter_le_hausdorff_level_set
    {u : E n → ℝ} (hu : ContDiff ℝ 1 u)
    (h_support : HasCompactSupport u)
    (h0 : ∀ x, 0 ≤ u x) (h1 : ∀ x, u x ≤ 1)
    {s : ℝ} (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (h_null : volume {x | u x = s} = 0)
    (hH_finite : μHE[n - 1] {x | u x = s} < ⊤)
    (hn : 2 ≤ n) :
    Perimeter.perimeter {x | u x > s} ≤ μHE[n - 1] {x | u x = s} := by
  let A := {x | u x > s}
  let V := interior (closure A)
  have hA_open : IsOpen A := isOpen_Ioi.preimage hu.continuous
  have hV_open : IsOpen V := isOpen_interior
  have hV_reg : V = interior (closure V) := interior_closure_idempotent.symm
  have hA_bdd : Bornology.IsBounded A := by
    let K := tsupport u
    have hK_compact : IsCompact K := h_support
    have h2 : A ⊆ K := by
      intro x hx
      have h3 : u x > s := hx
      have h4 : u x ≠ 0 := by linarith
      have h5 : x ∈ Function.support u := Function.mem_support.mpr h4
      exact subset_closure h5
    exact hK_compact.isBounded.subset h2
  have hV_bdd : Bornology.IsBounded V := hA_bdd.closure.subset interior_subset
  have h_frontier_sub : frontier V ⊆ {x | u x = s} :=
    frontier_regularized_level_set_subset hu.continuous
  have hH_frontier : μHE[n - 1] (frontier V) < ⊤ :=
    lt_of_le_of_lt (measure_mono h_frontier_sub) hH_finite
  have h_symmDiff_null : volume (symmDiff V A) = 0 :=
    regularized_symmDiff_null hu.continuous h_null
  have h_perim_eq : Perimeter.perimeter V = Perimeter.perimeter A :=
    perimeter_eq_of_symmDiff_null hV_open.measurableSet hA_open.measurableSet h_symmDiff_null
  have h_main : Perimeter.perimeter V ≤ μHE[n - 1] (frontier V) :=
    StructureTheorem.perimeter_le_hausdorff_frontier hV_open hV_reg hV_bdd hH_frontier hn
  have h_final : Perimeter.perimeter A ≤ μHE[n - 1] {x | u x = s} := by
    rw [←h_perim_eq]
    exact h_main.trans (measure_mono h_frontier_sub)
  exact h_final

/-- **Key lemma**: For a.e. `s ∈ (0,1]`,
`perimeter {u > s} ≤ μHE[n-1] {u = s}`. -/
theorem perimeter_level_set_le_hausdorff_ae
    {u : E n → ℝ} (hu : ContDiff ℝ 1 u)
    (h_support : HasCompactSupport u)
    (h0 : ∀ x, 0 ≤ u x) (h1 : ∀ x, u x ≤ 1)
    (hn : 2 ≤ n) :
    ∀ᵐ s ∂volume.restrict (Set.Ioc (0 : ℝ) 1),
      Perimeter.perimeter {x | u x > s} ≤ μHE[n - 1] {x | u x = s} := by
  have h_vol0 := volume_level_set_zero_ae hu.continuous.measurable h0 h1
  have h_Hfin := hausdorff_level_set_finite_ae hu h_support h0 h1 hn
  have h_mem : ∀ᵐ s ∂volume.restrict (Set.Ioc (0 : ℝ) 1), s ∈ Set.Ioc (0 : ℝ) 1 :=
    self_mem_ae_restrict (by exact measurableSet_Ioc)
  have h_ne_one : ∀ᵐ s ∂volume.restrict (Set.Ioc (0 : ℝ) 1), s ≠ 1 := by
    have h : volume.restrict (Set.Ioc (0 : ℝ) 1) {1} = 0 := by
      rw [Measure.restrict_apply (by exact measurableSet_singleton 1)]
      <;> simp
    rw [ae_iff]
    simpa using h
  filter_upwards [h_vol0, h_Hfin, h_mem, h_ne_one] with s hs_vol0 hs_Hfin hs_mem hs_ne_one
  have hs_pos : 0 < s := hs_mem.1
  have hs_lt_one : s < 1 := lt_of_le_of_ne hs_mem.2 hs_ne_one
  exact perimeter_le_hausdorff_level_set hu h_support h0 h1 hs_pos hs_lt_one hs_vol0 hs_Hfin hn

end Geometry
