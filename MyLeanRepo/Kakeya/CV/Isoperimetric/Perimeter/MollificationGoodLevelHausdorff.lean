import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.BrunnMinkowski.BM
import MyLeanRepo.Kakeya.CV.Isoperimetric.MinkowskiContent.Basic
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.Basic
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.LowerSemicontinuity
import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.CoareaFinalAssembly
import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.LevelSetSmoothCover
import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.FullSmoothBoundaryCover
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.MollificationGradientBound
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.MollificationContraction
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.NonSharpIsoperimetric
import MyLeanRepo.Kakeya.CV.Isoperimetric.Measure.LevelSetMeasurability
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.LayerCakeSymdiff
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.RegularizationHelpers
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.PerimeterDensityOne
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.SmoothIsoperimetricHausdorff
import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard
import Mathlib.Tactic
import Mathlib.MeasureTheory.Order.Group.Lattice


open scoped Pointwise Convolution MeasureTheory

open MeasureTheory ENNReal Metric Set Filter
open scoped MeasureTheory ContDiff
open ForMathlib.Analysis.Calculus.Sard

namespace Geometry

open Isoperimetric

/-!
# Good Level Sequence — Hausdorff Version (dimension m+1)

Selects level sets `s_k` from mollification `u_k` in `E(m+1)` such that:
1. `0 < s_k < 1`
2. `U_k := {u_k > s_k}` is open, measurable, bounded
3. `(m+1) · V(U_k)^(m/(m+1)) · ω^(1/(m+1)) ≤ μHE[m](frontier U_k)`
4. `V(U_k) → V(S)`
5. `limsup μHE[m](frontier U_k) ≤ P(S)`
-/

/-- Measurability of symmDiff volume as a function of level s. -/
lemma symmDiff_volume_measurable'
    {n : ℕ} {u : E n → ℝ} (hu : Measurable u) {S : Set (E n)} (hS : MeasurableSet S) :
    Measurable (fun s : ℝ => volume (symmDiff {x | u x > s} S)) := by
  let f1 : ℝ → ENNReal := fun s => volume ({x | u x > s} ∩ Sᶜ)
  let f2 : ℝ → ENNReal := fun s => volume (S ∩ {x | u x ≤ s})
  have hf1_antitone : Antitone f1 := by
    intro s1 s2 h
    have h_sub : {x | u x > s2} ∩ Sᶜ ⊆ {x | u x > s1} ∩ Sᶜ := by
      intro x hx
      have h5 : u x > s2 := hx.1
      have h6 : u x > s1 := by linarith
      exact ⟨h6, hx.2⟩
    exact measure_mono h_sub
  have hf1_meas : Measurable f1 := hf1_antitone.measurable
  have hf2_monotone : Monotone f2 := by
    intro s1 s2 h
    have h_sub : S ∩ {x | u x ≤ s1} ⊆ S ∩ {x | u x ≤ s2} := by
      intro x hx
      have h5 : u x ≤ s1 := hx.2
      have h6 : u x ≤ s2 := by linarith
      exact ⟨hx.1, h6⟩
    exact measure_mono h_sub
  have hf2_meas : Measurable f2 := hf2_monotone.measurable
  have h_eq : (fun s : ℝ => volume (symmDiff {x | u x > s} S)) = fun s => f1 s + f2 s := by
    funext s
    have h_disj : Disjoint ({x | u x > s} ∩ Sᶜ) (S ∩ {x | u x ≤ s}) := by
      rw [Set.disjoint_left]; intro x hx1 hx2; exact hx1.2 hx2.1
    have h1 : MeasurableSet ({x | u x > s} ∩ Sᶜ) := (hu isOpen_Ioi.measurableSet).inter hS.compl
    have h2 : MeasurableSet (S ∩ {x | u x ≤ s}) := hS.inter (hu isClosed_Iic.measurableSet)
    have h_union : symmDiff {x | u x > s} S = ({x | u x > s} ∩ Sᶜ) ∪ (S ∩ {x | u x ≤ s}) := by
      ext x; simp [symmDiff, Set.mem_compl_iff] <;> tauto
    have h_meas_union : volume (({x | u x > s} ∩ Sᶜ) ∪ (S ∩ {x | u x ≤ s})) =
        volume ({x | u x > s} ∩ Sᶜ) + volume (S ∩ {x | u x ≤ s}) := by
      exact measure_union h_disj h2
    rw [h_union, h_meas_union] <;> rfl
  rw [h_eq]; exact hf1_meas.add hf2_meas

/-- Volume of level set as a function of s is measurable. -/
lemma level_volume_measurable' {n : ℕ} {u : E n → ℝ} (hu : Measurable u) :
    Measurable (fun s : ℝ => volume {x | u x = s}) := by
  let g : ℝ × E n → ENNReal := fun p =>
    Set.indicator {p : ℝ × E n | u p.2 = p.1} (fun _ => (1 : ENNReal)) p
  have h_meas_set : MeasurableSet {p : ℝ × E n | u p.2 = p.1} := by
    have h1 : Measurable (fun p : ℝ × E n => u p.2) := hu.comp measurable_snd
    have h2 : Measurable (fun p : ℝ × E n => p.1) := measurable_fst
    exact measurableSet_eq_fun h1 h2
  have hg_meas : Measurable g := measurable_const.indicator h_meas_set
  have h_main : (fun s : ℝ => volume {x | u x = s}) = fun s : ℝ => ∫⁻ (x : E n), g (s, x) := by
    funext s
    have h_set_meas : MeasurableSet {x : E n | u x = s} := hu (isClosed_singleton.measurableSet)
    have h_g_s : (fun x : E n => g (s, x)) = Set.indicator {x : E n | u x = s} (fun _ => (1 : ENNReal)) := by
      funext x
      simp [g, Set.indicator_apply]
      <;> aesop
    rw [h_g_s, lintegral_indicator h_set_meas] <;> simp
  rw [h_main]
  exact hg_meas.lintegral_prod_right'

/-- Frontier of strict level set is contained in the level set. -/
lemma frontier_level_set_subset' {n : ℕ} {u : E n → ℝ} (hu : Continuous u) {s : ℝ} :
    frontier {x | u x > s} ⊆ {x | u x = s} := by
  let A := {x | u x > s}
  have hA_open : IsOpen A := hu.isOpen_preimage _ isOpen_Ioi
  have h1 : closure A ⊆ {x | u x ≥ s} := by
    intro x hx
    by_contra h
    have h' : u x < s := lt_of_not_ge h
    let W := {y | u y < s}
    have hW_open : IsOpen W := hu.isOpen_preimage _ isOpen_Iio
    have hxW : x ∈ W := h'
    have h_inter : ∃ y, y ∈ W ∧ y ∈ A := by
      rw [_root_.mem_closure_iff] at hx; exact hx W hW_open hxW
    rcases h_inter with ⟨y, hyW, hyA⟩
    have h9 : u y > s := hyA
    have h10 : u y < s := hyW
    linarith
  intro x hx
  have h2 : x ∈ closure A := frontier_subset_closure hx
  have h3 : x ∉ A := by
    have h4 : frontier A = closure A ∩ Aᶜ := by
      have h5 : closure Aᶜ = Aᶜ := hA_open.isClosed_compl.closure_eq
      rw [frontier_eq_closure_inter_closure, h5]
    rw [h4] at hx; exact hx.2
  have h4 : u x ≥ s := h1 h2
  have h5 : ¬(u x > s) := by simpa [A] using h3
  have h6 : u x = s := by linarith
  simpa using h6

/-- **Good level sequence from mollification** (Hausdorff version, dimension m+1). -/
lemma mollification_good_level_sequence_hausdorff
    {m : ℕ} [Nonempty (Fin m)] (hm : 1 ≤ m)
    {S : Set (E (m + 1))} (hS : MeasurableSet S) (hBdd : Bornology.IsBounded S)
    (hP_pos : 0 < Perimeter.perimeter S)
    (hP_lt_top : Perimeter.perimeter S < ⊤)
    (K : Set (E (m + 1))) (hK_compact : IsCompact K) (hS_sub_K : S ⊆ K)
    (u : ℕ → E (m + 1) → ℝ)
    (h_u_smooth : ∀ k, ContDiff ℝ ∞ (u k))
    (h_u_bound : ∀ k x, 0 ≤ u k x ∧ u k x ≤ 1)
    (h_u_support : ∀ k, HasCompactSupport (u k))
    (h_supp_K : ∀ k, ∀ x ∉ K, u k x = 0)
    (h_u_L1 : ∀ (L : Set (E (m + 1))), IsCompact L →
      Filter.Tendsto (fun k => ∫ x in L, |u k x - Set.indicator S (fun _ => (1 : ℝ)) x|)
        Filter.atTop (nhds 0))
    (h_grad_conv : Filter.Tendsto
        (fun k => ∫⁻ x, ENNReal.ofReal ‖fderiv ℝ (u k) x‖)
        Filter.atTop (nhds (Perimeter.perimeter S))) :
    ∃ (s : ℕ → ℝ),
      (∀ k, 0 < s k ∧ s k < 1) ∧
      (∀ k, IsOpen {x | u k x > s k} ∧
        MeasurableSet {x | u k x > s k} ∧
        Bornology.IsBounded {x | u k x > s k}) ∧
      (∀ k, 0 < volume {x | u k x > s k} →
        ((m + 1 : ℕ) : ENNReal) * (volume {x | u k x > s k})^((m : ℝ) / (m + 1)) *
          (volume (unitBall (m + 1)))^(1 / ((m + 1 : ℝ))) ≤
        μHE[m] (frontier {x | u k x > s k})) ∧
      Filter.Tendsto (fun k => volume {x | u k x > s k}) Filter.atTop (nhds (volume S)) ∧
      Filter.limsup (fun k => μHE[m] (frontier {x | u k x > s k})) Filter.atTop ≤
        Perimeter.perimeter S := by
  let P : ENNReal := Perimeter.perimeter S
  have hP_pos' : 0 < P := hP_pos
  have hP_lt_top' : P < ⊤ := hP_lt_top
  let p : ℝ := P.toReal
  have hp_pos : 0 < p := ENNReal.toReal_pos_iff.mpr ⟨hP_pos', hP_lt_top'⟩
  have hP_eq : P = ENNReal.ofReal p := by rw [ENNReal.ofReal_toReal hP_lt_top'.ne]
  have hK_meas : MeasurableSet K := hK_compact.measurableSet
  have hn2 : 2 ≤ m + 1 := by linarith

  let G : ℕ → ENNReal := fun k => ∫⁻ x, ENNReal.ofReal ‖fderiv ℝ (u k) x‖
  let J : ℕ → ENNReal := fun k => ∫⁻ s in Set.Ioc (0 : ℝ) 1, μHE[m] {x | u k x = s}
  let I : ℕ → ENNReal := fun k => ∫⁻ s in Set.Ioc (0 : ℝ) 1,
      volume (symmDiff {x | u k x > s} S)

  have hJ_le : ∀ k, J k ≤ ENNReal.ofReal (1 + 1 / (k + 1 : ℝ)^2) * G k := by
    intro k
    have hε_pos : 0 < (1 / (k + 1 : ℝ)^2) := by positivity
    exact coarea_hausdorff_smooth_upper (u k) ((h_u_smooth k).of_le (by norm_num)) (h_u_support k)
      (fun x => (h_u_bound k x).1) (fun x => (h_u_bound k x).2)
      (1 / (k + 1 : ℝ)^2) hε_pos hn2

  have hG_tendsto : Filter.Tendsto G Filter.atTop (nhds P) := h_grad_conv

  let c : ℕ → ENNReal := fun k => ENNReal.ofReal (1 + 1 / (k + 1 : ℝ)^2)
  have hc_tendsto : Filter.Tendsto c Filter.atTop (nhds 1) := by
    have h1 : Filter.Tendsto (fun k : ℕ => (1 + 1 / (k + 1 : ℝ)^2)) Filter.atTop (nhds 1) := by
      have h21 : Filter.Tendsto (fun k : ℕ => (k + 1 : ℝ)) Filter.atTop Filter.atTop :=
        tendsto_atTop_mono (fun k : ℕ => by linarith) tendsto_natCast_atTop_atTop
      have h2 : Filter.Tendsto (fun k : ℕ => ((k + 1 : ℝ)^2)) Filter.atTop Filter.atTop :=
        (Filter.tendsto_pow_atTop (by norm_num)).comp h21
      have h3 : Filter.Tendsto (fun k : ℕ => ((k + 1 : ℝ)^2)⁻¹) Filter.atTop (nhds 0) :=
        tendsto_inv_atTop_zero.comp h2
      have h4 : Filter.Tendsto (fun k : ℕ => 1 + ((k + 1 : ℝ)^2)⁻¹) Filter.atTop (nhds 1) := by
        have h41 : Filter.Tendsto (fun k : ℕ => 1 + ((k + 1 : ℝ)^2)⁻¹) Filter.atTop (nhds (1 + (0 : ℝ))) :=
          h3.const_add 1
        have h42 : (1 + (0 : ℝ)) = (1 : ℝ) := by ring
        rw [h42] at h41
        exact h41
      have h5 : (fun k : ℕ => 1 + 1 / (k + 1 : ℝ)^2) = fun k : ℕ => 1 + ((k + 1 : ℝ)^2)⁻¹ := by
        funext k; field_simp
      rw [h5]
      exact h4
    have h4 : Filter.Tendsto (fun k : ℕ => ENNReal.ofReal (1 + 1 / (k + 1 : ℝ)^2))
        Filter.atTop (nhds (ENNReal.ofReal 1)) :=
      (ENNReal.continuous_ofReal.tendsto (1 : ℝ)).comp h1
    have h5 : ENNReal.ofReal (1 : ℝ) = (1 : ENNReal) := by simp
    rw [h5] at h4; exact h4

  have h_prod_tendsto : Filter.Tendsto (fun k => c k * G k) Filter.atTop (nhds P) := by
    have h := ENNReal.Tendsto.mul hc_tendsto (by simp) hG_tendsto (by simp [hP_lt_top'.ne])
    have h1 : (1 : ENNReal) * P = P := by simp
    rw [h1] at h
    exact h

  have hJ_limsup_le : Filter.limsup J Filter.atTop ≤ P := by
    have h_le : ∀ k, J k ≤ c k * G k := hJ_le
    have h : Filter.limsup J Filter.atTop ≤ Filter.limsup (fun k => c k * G k) Filter.atTop :=
      limsup_le_limsup (Filter.univ_mem' h_le)
    rw [h_prod_tendsto.limsup_eq] at h; exact h

  -- I_k → 0
  have hI_eq : ∀ k, I k = ∫⁻ x in K, ENNReal.ofReal |u k x - Set.indicator S (fun _ => (1 : ℝ)) x| := by
    intro k
    have h_meas : Measurable (u k) := (h_u_smooth k).continuous.measurable
    exact layer_cake_symdiff h_meas
      (fun x => (h_u_bound k x).1) (fun x => (h_u_bound k x).2)
      hS K hK_meas (h_supp_K k) hS_sub_K

  have hI_tendsto : Filter.Tendsto I Filter.atTop (nhds 0) := by
    have h5 : ∀ k, I k = ENNReal.ofReal (∫ x in K, |u k x - Set.indicator S (fun _ => (1 : ℝ)) x|) := by
      intro k
      rw [hI_eq k]
      let f : E (m + 1) → ℝ := fun x => |u k x - Set.indicator S (fun _ => (1 : ℝ)) x|
      have h_meas_u : Measurable (u k) := (h_u_smooth k).continuous.measurable
      have h_meas_ind : Measurable (Set.indicator S (fun _ => (1 : ℝ))) := measurable_const.indicator hS
      have hf_meas : Measurable f := (h_meas_u.sub h_meas_ind).abs
      have hf_nonneg : ∀ x, 0 ≤ f x := fun x => abs_nonneg _
      have hK_vol : volume K < ⊤ := hK_compact.measure_lt_top
      letI : IsFiniteMeasure (volume.restrict K) := ⟨by simpa [Measure.restrict_apply] using hK_vol⟩
      have h1_int : Integrable (fun _ : E (m + 1) => (1 : ℝ)) (volume.restrict K) := by
        simpa using integrable_const (1 : ℝ)
      have hf_sm : AEStronglyMeasurable f (volume.restrict K) := hf_meas.aestronglyMeasurable
      have h_bdd_ae : ∀ᵐ x ∂volume.restrict K, ‖f x‖ ≤ ‖(1 : ℝ)‖ := by
        filter_upwards with x
        have h6 : 0 ≤ f x := hf_nonneg x
        have h7 : ‖f x‖ = f x := by rw [Real.norm_eq_abs, abs_of_nonneg h6]
        have h8 : ‖(1 : ℝ)‖ = 1 := by simp
        rw [h7, h8]
        have h9 : f x ≤ 1 := by
          have h10 : 0 ≤ u k x := (h_u_bound k x).1
          have h11 : u k x ≤ 1 := (h_u_bound k x).2
          have h12 : (0 : ℝ) ≤ Set.indicator S (fun _ => (1 : ℝ)) x := by
            apply Set.indicator_nonneg; intro; norm_num
          have h13 : Set.indicator S (fun _ => (1 : ℝ)) x ≤ 1 := by
            by_cases h : x ∈ S <;> simp [h, Set.indicator_apply] <;> norm_num
          exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
        exact h9
      have hf_int : Integrable f (volume.restrict K) := h1_int.mono hf_sm h_bdd_ae
      have h_nn : 0 ≤ᵐ[volume.restrict K] f := by filter_upwards with x; exact hf_nonneg x
      have h6 : ∫⁻ x in K, ENNReal.ofReal (f x) = ENNReal.ofReal (∫ x in K, f x) :=
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hf_int h_nn).symm
      exact h6
    have h7 : Filter.Tendsto (fun k => ∫ x in K, |u k x - Set.indicator S (fun _ => (1 : ℝ)) x|)
        Filter.atTop (nhds 0) := h_u_L1 K hK_compact
    have h8 : Filter.Tendsto (fun k => ENNReal.ofReal (∫ x in K, |u k x - Set.indicator S (fun _ => (1 : ℝ)) x|))
        Filter.atTop (nhds (0 : ENNReal)) := by
      have h9 : ENNReal.ofReal (0 : ℝ) = (0 : ENNReal) := by simp
      have h10 := (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp h7
      rw [h9] at h10; exact h10
    have h11 : Filter.Tendsto I Filter.atTop (nhds (0 : ENNReal)) := by
      have h12 : I = fun k => ENNReal.ofReal (∫ x in K, |u k x - Set.indicator S (fun _ => (1 : ℝ)) x|) := by
        funext k; exact h5 k
      rw [h12]; exact h8
    simpa using h11

  -- Diagonal selection with factor 3 (ensures strict sum < 1)
  let GoodLevelBound (m' : ℕ) (k : ℕ) : Prop :=
    I k < ENNReal.ofReal (1 / ((m' : ℝ) * (3 * (m' : ℝ) * p + 3))) ∧
    J k < P + ENNReal.ofReal (1 / (3 * (m' : ℝ)))

  have hGood_eventually : ∀ m' : ℕ, 0 < m' → ∀ᶠ k in Filter.atTop, GoodLevelBound m' k := by
    intro m' hm'
    have h1 : 0 < (1 : ℝ) / ((m' : ℝ) * (3 * (m' : ℝ) * p + 3)) := by positivity
    have h2 : 0 < (1 : ℝ) / (3 * (m' : ℝ)) := by positivity
    have hI_ev : ∀ᶠ k in Filter.atTop, I k < ENNReal.ofReal (1 / ((m' : ℝ) * (3 * (m' : ℝ) * p + 3))) := by
      have h3 : ENNReal.ofReal (1 / ((m' : ℝ) * (3 * (m' : ℝ) * p + 3))) > 0 := by positivity
      exact hI_tendsto (Iio_mem_nhds h3)
    have hJ_ev : ∀ᶠ k in Filter.atTop, J k < P + ENNReal.ofReal (1 / (3 * (m' : ℝ))) := by
      have h4 : P < P + ENNReal.ofReal (1 / (3 * (m' : ℝ))) := by
        have h5 : 0 < ENNReal.ofReal (1 / (3 * (m' : ℝ))) := by positivity
        exact ENNReal.lt_add_right hP_lt_top'.ne h5.ne'
      have h5 : ∀ (y : ENNReal), P < y → (∀ᶠ k in Filter.atTop, J k < y) :=
        (Filter.limsup_le_iff (x := P)).mp hJ_limsup_le
      exact h5 (P + ENNReal.ofReal (1 / (3 * (m' : ℝ)))) h4
    filter_upwards [hI_ev, hJ_ev] with k hI hJ
    exact ⟨hI, hJ⟩

  classical
  let m_best : ℕ → ℕ := fun k => Nat.findGreatest (fun m' => GoodLevelBound m' k) k
  have hmb_tendsto : Filter.Tendsto m_best Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_atTop.mpr
    intro M
    by_cases hM : M = 0
    · refine ⟨0, fun k _ => by simp [hM]⟩
    · have hM_pos : 0 < M := Nat.pos_of_ne_zero hM
      have h_ev : ∀ᶠ k in Filter.atTop, GoodLevelBound M k := hGood_eventually M hM_pos
      have h_exists : ∃ N, ∀ k, N ≤ k → GoodLevelBound M k := by
        simpa [Filter.eventually_atTop] using h_ev
      rcases h_exists with ⟨N1, hN1⟩
      refine ⟨max M N1, fun k hk => ?_⟩
      have hkM : M ≤ k := le_trans (le_max_left M N1) hk
      have hkN : N1 ≤ k := le_trans (le_max_right M N1) hk
      have h_GL : GoodLevelBound M k := hN1 k hkN
      exact Nat.le_findGreatest hkM h_GL
  have hmb_pos : ∀ᶠ k in Filter.atTop, 0 < m_best k := by
    have h_ev := hGood_eventually 1 (by norm_num)
    have h_ev2 : ∀ᶠ k in Filter.atTop, 1 ≤ k := eventually_atTop.mpr ⟨1, fun k hk => hk⟩
    filter_upwards [h_ev, h_ev2] with k hk hk1
    have h5 : 1 ≤ m_best k := Nat.le_findGreatest hk1 hk
    omega

  let δ : ℕ → ℝ := fun k => 1 / (m_best k : ℝ)
  let η : ℕ → ℝ := fun k => 1 / (m_best k : ℝ)

  have hmb_real_tendsto : Filter.Tendsto (fun k : ℕ => (m_best k : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp hmb_tendsto

  have hδ_tendsto : Filter.Tendsto δ Filter.atTop (nhds 0) := by
    have h_eq : δ = fun k : ℕ => (m_best k : ℝ)⁻¹ := by funext k; simp [δ]
    rw [h_eq]; exact tendsto_inv_atTop_zero.comp hmb_real_tendsto
  have hη_tendsto : Filter.Tendsto η Filter.atTop (nhds 0) := by
    have h_eq : η = fun k : ℕ => (m_best k : ℝ)⁻¹ := by funext k; simp [η]
    rw [h_eq]; exact tendsto_inv_atTop_zero.comp hmb_real_tendsto

  -- Sum condition: I/η + J/(P+δ) < 1
  have h_sum_condition : ∀ k, GoodLevelBound (m_best k) k →
      I k / ENNReal.ofReal (η k) + J k / (P + ENNReal.ofReal (δ k)) < 1 := by
    intro k hk
    have hmb_pos' : 0 < m_best k := by
      by_contra h
      have h0 : m_best k = 0 := by omega
      rw [h0] at hk
      have h1 : I k < 0 := by simpa [GoodLevelBound] using hk.1
      exact False.elim (not_le.mpr h1 bot_le)
    set m' : ℝ := (m_best k : ℝ) with hm'_def
    have hm'_pos : 0 < m' := by
      have h : 0 < m_best k := hmb_pos'
      have h' : (m_best k : ℝ) > 0 := by exact_mod_cast h
      simpa [hm'_def] using h'
    have hI_bound : I k < ENNReal.ofReal (1 / (m' * (3 * m' * p + 3))) := hk.1
    have hJ_bound : J k < P + ENNReal.ofReal (1 / (3 * m')) := hk.2
    have hδ_eq : ENNReal.ofReal (δ k) = ENNReal.ofReal (1 / m') := by
      simp [δ, hm'_def] <;> norm_cast
    have hη_eq : ENNReal.ofReal (η k) = ENNReal.ofReal (1 / m') := by
      simp [η, hm'_def] <;> norm_cast
    rw [hη_eq, hδ_eq]
    let b : ENNReal := ENNReal.ofReal (1 / m')
    have hb_pos : 0 < b := by positivity
    have hb_ne_top : b ≠ ⊤ := ENNReal.ofReal_lt_top.ne

    have hdiv_mono : ∀ {a c : ENNReal}, a < c → a / b < c / b := by
      intro a c h
      have hinv_pos : 0 < b⁻¹ := ENNReal.inv_pos.mpr hb_ne_top
      have hinv_ne_top : b⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hb_pos.ne'
      have hinv_ne_zero : b⁻¹ ≠ 0 := ne_of_gt hinv_pos
      have h' : b⁻¹ * a < b⁻¹ * c := ENNReal.mul_lt_mul_right hinv_ne_zero hinv_ne_top h
      have h'' : a * b⁻¹ < c * b⁻¹ := by
        have hcomm1 : a * b⁻¹ = b⁻¹ * a := by rw [mul_comm]
        have hcomm2 : c * b⁻¹ = b⁻¹ * c := by rw [mul_comm]
        rw [hcomm1, hcomm2]
        exact h'
      simpa [div_eq_mul_inv] using h''

    have h1 : I k / b < ENNReal.ofReal (1 / (3 * m' * p + 3)) := by
      have h11 : I k / b < ENNReal.ofReal (1 / (m' * (3 * m' * p + 3))) / b := hdiv_mono hI_bound
      have hden_pos : 0 < (1 / m' : ℝ) := by positivity
      have h_b_def : b = ENNReal.ofReal (1 / m') := by rfl
      have h12 : ENNReal.ofReal (1 / (m' * (3 * m' * p + 3))) / b =
          ENNReal.ofReal (1 / (3 * m' * p + 3)) := by
        have hden_pos : 0 < (1 / m' : ℝ) := by positivity
        have h_real_div : ((1 : ℝ) / (m' * (3 * m' * p + 3))) / (1 / m') =
            1 / (3 * m' * p + 3) := by
          field_simp [hm'_pos.ne'] <;> ring
        have h_ofReal_div : ENNReal.ofReal (((1 : ℝ) / (m' * (3 * m' * p + 3))) / (1 / m')) =
            ENNReal.ofReal (1 / (m' * (3 * m' * p + 3))) / ENNReal.ofReal (1 / m') := by
          rw [ENNReal.ofReal_div_of_pos hden_pos]
        have h_b_eq : b = ENNReal.ofReal (1 / m') := by rfl
        rw [h_b_eq, ←h_ofReal_div, h_real_div]
      rw [h12] at h11; exact h11

    let b2 : ENNReal := P + b
    have hb2_pos : 0 < b2 := by positivity
    have hb2_ne_top : b2 ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hP_lt_top'.ne, hb_ne_top⟩
    have hdiv_mono2 : ∀ {a c : ENNReal}, a < c → a / b2 < c / b2 := by
      intro a c h
      have hinv_pos : 0 < b2⁻¹ := ENNReal.inv_pos.mpr hb2_ne_top
      have hinv_ne_top : b2⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hb2_pos.ne'
      have hinv_ne_zero : b2⁻¹ ≠ 0 := ne_of_gt hinv_pos
      have h' : b2⁻¹ * a < b2⁻¹ * c := ENNReal.mul_lt_mul_right hinv_ne_zero hinv_ne_top h
      have h'' : a * b2⁻¹ < c * b2⁻¹ := by
        have hcomm1 : a * b2⁻¹ = b2⁻¹ * a := by rw [mul_comm]
        have hcomm2 : c * b2⁻¹ = b2⁻¹ * c := by rw [mul_comm]
        rw [hcomm1, hcomm2]
        exact h'
      simpa [div_eq_mul_inv] using h''

    have hP_eq2 : b2 = ENNReal.ofReal (p + 1 / m') := by
      have h_b2_def : b2 = P + b := by rfl
      rw [h_b2_def, hP_eq]
      have h_b_def : b = ENNReal.ofReal (1 / m') := by rfl
      rw [h_b_def, ENNReal.ofReal_add] <;> positivity

    have h2 : J k / b2 < ENNReal.ofReal ((p + 1 / (3 * m')) / (p + 1 / m')) := by
      have hJ_real : J k < ENNReal.ofReal (p + 1 / (3 * m')) := by
        have h_eq : P + ENNReal.ofReal (1 / (3 * m')) = ENNReal.ofReal (p + 1 / (3 * m')) := by
          rw [hP_eq, ENNReal.ofReal_add] <;> positivity
        rw [h_eq] at hJ_bound; exact hJ_bound
      have h21 : J k / b2 < ENNReal.ofReal (p + 1 / (3 * m')) / b2 := hdiv_mono2 hJ_real
      have hden2_pos : 0 < (p + 1 / m' : ℝ) := by positivity
      have h22 : ENNReal.ofReal (p + 1 / (3 * m')) / b2 =
          ENNReal.ofReal ((p + 1 / (3 * m')) / (p + 1 / m')) := by
        have h_b2_eq : b2 = ENNReal.ofReal (p + 1 / m') := hP_eq2
        rw [h_b2_eq]
        rw [← ENNReal.ofReal_div_of_pos hden2_pos] <;> rfl
      have h23 : J k / b2 < ENNReal.ofReal ((p + 1 / (3 * m')) / (p + 1 / m')) := by
        rw [h22] at h21; exact h21
      exact h23

    have h3 : (1 : ℝ) / (3 * m' * p + 3) + (p + 1 / (3 * m')) / (p + 1 / m') < 1 := by
      have h4 : 0 < m' := hm'_pos
      have h5 : 0 < p := hp_pos
      have h6 : 0 < p + 1 / m' := by positivity
      have h7 : 1 / (3 * m' * p + 3) + (p + 1 / (3 * m')) / (p + 1 / m') < 1 := by
        calc
          1 / (3 * m' * p + 3) + (p + 1 / (3 * m')) / (p + 1 / m')
            = (1 + 3 * m' * p + 1) / (3 * (m' * p + 1)) := by
              field_simp [h4.ne', h5.ne', h6.ne'] <;> ring
          _ < 1 := by
            rw [div_lt_one (by positivity)]
            <;> ring_nf <;> nlinarith
      exact h7
    have h4 : ENNReal.ofReal (1 / (3 * m' * p + 3)) + ENNReal.ofReal ((p + 1 / (3 * m')) / (p + 1 / m')) < 1 := by
      have h5 : 0 ≤ 1 / (3 * m' * p + 3) := by positivity
      have h6 : 0 ≤ (p + 1 / (3 * m')) / (p + 1 / m') := by positivity
      rw [← ENNReal.ofReal_add h5 h6]
      have h7 : ENNReal.ofReal (1 / (3 * m' * p + 3) + (p + 1 / (3 * m')) / (p + 1 / m')) < 1 := by
        rw [ENNReal.ofReal_lt_one] <;> linarith
      exact h7
    have h5 : I k / b + J k / b2 <
        ENNReal.ofReal (1 / (3 * m' * p + 3)) + ENNReal.ofReal ((p + 1 / (3 * m')) / (p + 1 / m')) := by
      gcongr
    exact h5.trans h4

  -- Level functions and measurability
  let H : ℕ → ℝ → ENNReal := fun k s => μHE[m] {x | u k x = s}
  let V : ℕ → ℝ → ENNReal := fun k s => volume (symmDiff {x | u k x > s} S)
  have hH_meas : ∀ k, Measurable (H k) := by
    intro k
    have h_meas : Measurable (fun s : ℝ => μHE[(m + 1) - 1] {x | u k x = s}) :=
      level_set_hausdorff_measurable ((h_u_smooth k).of_le (by norm_num)) (h_u_support k) (by linarith)
    have h_eq : (m + 1) - 1 = m := by omega
    simpa [h_eq] using h_meas
  have hV_meas : ∀ k, Measurable (V k) := by
    intro k
    exact symmDiff_volume_measurable' (h_u_smooth k).continuous.measurable hS
  have hVol_meas : ∀ k, Measurable (fun s : ℝ => volume {x | u k x = s}) := by
    intro k; exact level_volume_measurable' (h_u_smooth k).continuous.measurable

  -- Integrals over Ioo equal Ioc (they differ only by {1}, measure zero)
  have h_sub : Set.Ioo (0 : ℝ) 1 ⊆ Set.Ioc (0 : ℝ) 1 := by
    intro x hx; exact ⟨hx.1, hx.2.le⟩
  have h_ae : (Set.Ioc (0 : ℝ) 1) =ᵐ[volume] (Set.Ioo (0 : ℝ) 1) :=
    Ioo_ae_eq_Ioc.symm
  have h_restrict_eq : volume.restrict (Set.Ioc (0 : ℝ) 1) = volume.restrict (Set.Ioo (0 : ℝ) 1) :=
    Measure.restrict_congr_set h_ae

  have hJ_Ioo : ∀ k, ∫⁻ s in Set.Ioo (0 : ℝ) 1, H k s = J k := by
    intro k
    have h_eq : ∫⁻ s in Set.Ioc (0 : ℝ) 1, H k s = ∫⁻ s in Set.Ioo (0 : ℝ) 1, H k s := by
      rw [h_restrict_eq]
    exact h_eq.symm
  have hI_Ioo : ∀ k, ∫⁻ s in Set.Ioo (0 : ℝ) 1, V k s = I k := by
    intro k
    have h_eq : ∫⁻ s in Set.Ioc (0 : ℝ) 1, V k s = ∫⁻ s in Set.Ioo (0 : ℝ) 1, V k s := by
      rw [h_restrict_eq]
    exact h_eq.symm

  -- Basic existence
  have h_exists_all : ∀ k, ∃ (s : ℝ),
      0 < s ∧ s < 1 ∧ volume {x | u k x = s} = 0 ∧ μHE[m] {x | u k x = s} < ⊤ ∧
      IsRegularValue (u k) s := by
    intro k
    have h_vol0 : ∀ᵐ s ∂volume.restrict (Set.Ioc (0 : ℝ) 1), volume {x | u k x = s} = 0 :=
      volume_level_set_zero_ae (h_u_smooth k).continuous.measurable
        (fun x => (h_u_bound k x).1) (fun x => (h_u_bound k x).2)
    have h_Hfin : ∀ᵐ s ∂volume.restrict (Set.Ioc (0 : ℝ) 1), μHE[m] {x | u k x = s} < ⊤ := by
      have h : ∀ᵐ s ∂volume.restrict (Set.Ioc (0 : ℝ) 1),
          μHE[(m + 1) - 1] {x | u k x = s} < ⊤ :=
        hausdorff_level_set_finite_ae (n := m + 1) (u := u k) ((h_u_smooth k).of_le (by norm_num)) (h_u_support k)
          (fun x => (h_u_bound k x).1) (fun x => (h_u_bound k x).2) (by linarith)
      have h_eq : (m + 1) - 1 = m := by omega
      simpa [h_eq] using h
    have h_reg_ae : ∀ᵐ s ∂volume.restrict (Set.Ioc (0 : ℝ) 1), IsRegularValue (u k) s := by
      have h_main : ∀ᵐ s ∂volume, IsRegularValue (u k) s :=
        regular_value_ae (u k) (h_u_smooth k)
      exact h_main.filter_mono (MeasureTheory.ae_mono Measure.restrict_le_self)
    have h_ne_one : ∀ᵐ s ∂volume.restrict (Set.Ioc (0 : ℝ) 1), s ≠ 1 := by
      have h : volume.restrict (Set.Ioc (0 : ℝ) 1) {1} = 0 := by
        rw [Measure.restrict_apply (by exact measurableSet_singleton 1)] <;> simp
      have h_set : {s : ℝ | ¬(s ≠ 1)} = ({1} : Set ℝ) := by ext s; simp
      rw [ae_iff, h_set]
      exact h
    have h_ne_zero : ∀ᵐ s ∂volume.restrict (Set.Ioc (0 : ℝ) 1), s ≠ 0 := by
      have h : volume.restrict (Set.Ioc (0 : ℝ) 1) {0} = 0 := by
        rw [Measure.restrict_apply (by exact measurableSet_singleton 0)] <;> simp
      have h_set : {s : ℝ | ¬(s ≠ 0)} = ({0} : Set ℝ) := by ext s; simp
      rw [ae_iff, h_set]
      exact h
    have h_mem : ∀ᵐ s ∂volume.restrict (Set.Ioc (0 : ℝ) 1), s ∈ Set.Ioc (0 : ℝ) 1 :=
      self_mem_ae_restrict (by exact measurableSet_Ioc)
    have h_full : ∀ᵐ s ∂volume.restrict (Set.Ioc (0 : ℝ) 1),
        s ∈ Set.Ioc (0 : ℝ) 1 ∧ s ≠ 1 ∧ s ≠ 0 ∧ volume {x | u k x = s} = 0 ∧
        μHE[m] {x | u k x = s} < ⊤ ∧ IsRegularValue (u k) s := by
      filter_upwards [h_mem, h_ne_one, h_ne_zero, h_vol0, h_Hfin, h_reg_ae] with s hs_mem hs_ne_one hs_ne_zero hs_vol0 hs_Hfin hs_reg
      exact ⟨hs_mem, hs_ne_one, hs_ne_zero, hs_vol0, hs_Hfin, hs_reg⟩
    have h_pos : 0 < volume.restrict (Set.Ioc (0 : ℝ) 1) Set.univ := by simp
    have h_ne_zero : volume.restrict (Set.Ioc (0 : ℝ) 1) ≠ 0 := by
      intro h_contra
      rw [h_contra] at h_pos
      simpa using h_pos
    letI : NeBot (ae (volume.restrict (Set.Ioc (0 : ℝ) 1))) := by
      have h : (volume.restrict (Set.Ioc (0 : ℝ) 1)) ≠ 0 := h_ne_zero
      exact ae_neBot.mpr h_ne_zero
    have h_exists : ∃ (s : ℝ), s ∈ Set.Ioc (0 : ℝ) 1 ∧ s ≠ 1 ∧ s ≠ 0 ∧
        volume {x | u k x = s} = 0 ∧ μHE[m] {x | u k x = s} < ⊤ ∧ IsRegularValue (u k) s :=
      h_full.exists
    rcases h_exists with ⟨s, hs_mem, hs_ne_one, hs_ne_zero, hs_vol0, hs_Hfin, hs_reg⟩
    have h_s_pos : 0 < s := hs_mem.1
    have h_s_lt_one : s < 1 := lt_of_le_of_ne hs_mem.2 hs_ne_one
    exact ⟨s, h_s_pos, h_s_lt_one, hs_vol0, hs_Hfin, hs_reg⟩

  choose s0 hs0 using h_exists_all

  let GoodLevel (k : ℕ) (t : ℝ) : Prop :=
    0 < t ∧ t < 1 ∧
    volume {x | u k x = t} = 0 ∧
    μHE[m] {x | u k x = t} < ⊤ ∧
    μHE[m] {x | u k x = t} ≤ P + ENNReal.ofReal (δ k) ∧
    volume (symmDiff {x | u k x > t} S) ≤ ENNReal.ofReal (η k) ∧
    IsRegularValue (u k) t

  have h_exists : ∀ᶠ k in Filter.atTop, ∃ (t : ℝ), GoodLevel k t := by
    filter_upwards [hmb_pos] with k hk
    have h_pos : 0 < m_best k := hk
    have h_exists_witness : ∃ (m' : ℕ), 0 < m' ∧ m' ≤ k ∧ GoodLevelBound m' k :=
      (Nat.findGreatest_pos (P := fun m' => GoodLevelBound m' k)).mp h_pos
    rcases h_exists_witness with ⟨m', hm'_pos, hm'_le, hP_m'⟩
    have h_exists_spec : ∃ m' ≤ k, GoodLevelBound m' k := ⟨m', hm'_le, hP_m'⟩
    have hGB : GoodLevelBound (m_best k) k := by
      have h : GoodLevelBound (Nat.findGreatest (fun m' => GoodLevelBound m' k) k) k :=
        Nat.findGreatest_spec (m := m') (P := fun x => GoodLevelBound x k) (n := k) hm'_le hP_m'
      simpa [m_best] using h
    have h_sum := h_sum_condition k hGB
    have hδ_pos' : 0 < δ k := by
      have h1 : (m_best k : ℝ) > 0 := by exact_mod_cast hk
      simp [δ]; positivity
    have hη_pos' : 0 < η k := by
      have h1 : (m_best k : ℝ) > 0 := by exact_mod_cast hk
      simp [η]; positivity
    let A : Set ℝ := {s | ¬IsRegularValue (u k) s}
    have hA_null : volume A = 0 := by
      have h_main : ∀ᵐ s ∂volume, IsRegularValue (u k) s :=
        regular_value_ae (u k) (h_u_smooth k)
      exact ae_iff.mp h_main
    rcases MeasureTheory.exists_measurable_superset_of_null hA_null with ⟨N, hN_sub, hN_meas, hN_null⟩
    let Bad : Set ℝ := {s | volume {x | u k x = s} ≠ 0} ∪ {s | H k s = ⊤} ∪ N
    have hBad_meas : MeasurableSet Bad := by
      have h1 : MeasurableSet {s : ℝ | volume {x | u k x = s} ≠ 0} :=
        hVol_meas k (measurableSet_singleton 0).compl
      have h2 : MeasurableSet {s : ℝ | H k s = ⊤} :=
        hH_meas k (measurableSet_singleton ⊤)
      exact h1.union h2 |>.union hN_meas
    have hBad_null_Ioc : volume.restrict (Set.Ioc (0 : ℝ) 1) Bad = 0 := by
      have h1 : volume.restrict (Set.Ioc (0 : ℝ) 1) {s | volume {x | u k x = s} ≠ 0} = 0 := by
        have h_ae : ∀ᵐ s ∂volume.restrict (Set.Ioc (0 : ℝ) 1), volume {x | u k x = s} = 0 :=
          volume_level_set_zero_ae (h_u_smooth k).continuous.measurable
            (fun x => (h_u_bound k x).1) (fun x => (h_u_bound k x).2)
        have h_seteq : {s : ℝ | volume {x | u k x = s} ≠ 0} =
            {s : ℝ | ¬(volume {x | u k x = s} = 0)} := by ext s; simp
        rw [h_seteq]; exact ae_iff.mp h_ae
      have h2 : volume.restrict (Set.Ioc (0 : ℝ) 1) {s | H k s = ⊤} = 0 := by
        have h_ae : ∀ᵐ s ∂volume.restrict (Set.Ioc (0 : ℝ) 1), H k s < ⊤ := by
          have h : ∀ᵐ s ∂volume.restrict (Set.Ioc (0 : ℝ) 1),
              μHE[(m + 1) - 1] {x | u k x = s} < ⊤ :=
            hausdorff_level_set_finite_ae (n := m + 1) (u := u k) ((h_u_smooth k).of_le (by norm_num)) (h_u_support k)
              (fun x => (h_u_bound k x).1) (fun x => (h_u_bound k x).2) (by linarith)
          have h_eq : (m + 1) - 1 = m := by omega
          simpa [h_eq, H] using h
        have h_seteq : {s : ℝ | H k s = ⊤} = {s : ℝ | ¬(H k s < ⊤)} := by ext s; simp
        rw [h_seteq]; exact ae_iff.mp h_ae
      have h3 : volume.restrict (Set.Ioc (0 : ℝ) 1) N = 0 := by
        have h : volume.restrict (Set.Ioc (0 : ℝ) 1) N ≤ volume N := Measure.restrict_le_self _
        rw [hN_null] at *; exact le_zero_iff.mp h
      exact measure_union_null (measure_union_null h1 h2) h3
    have h_sub : Set.Ioo (0 : ℝ) 1 ⊆ Set.Ioc (0 : ℝ) 1 := by
      intro x hx; have h2 : x < 1 := hx.2; exact ⟨hx.1, h2.le⟩
    have hBad_null_Ioo : volume.restrict (Set.Ioo (0 : ℝ) 1) Bad = 0 := by
      have h_inter : Bad ∩ Set.Ioo (0 : ℝ) 1 ⊆ Bad ∩ Set.Ioc (0 : ℝ) 1 := by gcongr
      have h : volume (Bad ∩ Set.Ioo (0 : ℝ) 1) ≤ volume (Bad ∩ Set.Ioc (0 : ℝ) 1) := measure_mono h_inter
      have h' : volume (Bad ∩ Set.Ioc (0 : ℝ) 1) = 0 := by
        simpa [Measure.restrict_apply] using hBad_null_Ioc
      rw [Measure.restrict_apply (by exact MeasurableSet.congr hBad_meas rfl)]
      exact le_zero_iff.mp (le_trans h (le_of_eq h'))
    let H' : ℝ → ENNReal := fun t => if t ∈ Bad then ⊤ else H k t
    let V' : ℝ → ENNReal := fun t => if t ∈ Bad then ⊤ else V k t
    have hH'_meas : Measurable H' := Measurable.ite hBad_meas measurable_const (hH_meas k)
    have hV'_meas : Measurable V' := Measurable.ite hBad_meas measurable_const (hV_meas k)
    have hH'_eq : H' =ᵐ[volume.restrict (Set.Ioo (0 : ℝ) 1)] H k := by
      have h_ae : ∀ᵐ t ∂volume.restrict (Set.Ioo (0 : ℝ) 1), t ∉ Bad := by
        exact ae_iff.mpr (by simpa using hBad_null_Ioo)
      filter_upwards [h_ae] with t ht; simp [H', ht]
    have hV'_eq : V' =ᵐ[volume.restrict (Set.Ioo (0 : ℝ) 1)] V k := by
      have h_ae : ∀ᵐ t ∂volume.restrict (Set.Ioo (0 : ℝ) 1), t ∉ Bad := by
        exact ae_iff.mpr (by simpa using hBad_null_Ioo)
      filter_upwards [h_ae] with t ht; simp [V', ht]
    have hJ' : ∫⁻ s in Set.Ioo (0 : ℝ) 1, H' s = J k := by
      have h_eq1 : ∫⁻ s in Set.Ioo (0 : ℝ) 1, H' s = ∫⁻ s in Set.Ioo (0 : ℝ) 1, H k s :=
        lintegral_congr_ae hH'_eq
      rw [h_eq1]; exact hJ_Ioo k
    have hI' : ∫⁻ s in Set.Ioo (0 : ℝ) 1, V' s = I k := by
      have h_eq1 : ∫⁻ s in Set.Ioo (0 : ℝ) 1, V' s = ∫⁻ s in Set.Ioo (0 : ℝ) 1, V k s :=
        lintegral_congr_ae hV'_eq
      rw [h_eq1]; exact hI_Ioo k
    rcases level_set_selection_Ioo hH'_meas hV'_meas
        P hP_pos' hP_lt_top' (δ k) (η k) hδ_pos' hη_pos'
        (J k) (I k) hJ' hI' h_sum
      with ⟨t, ht_Ioo, hH'_le, hV'_le⟩
    have ht_not_Bad : t ∉ Bad := by
      by_contra h
      have h5 : H' t = ⊤ := by simp [H', h]
      rw [h5] at hH'_le
      have h6 : P + ENNReal.ofReal (δ k) < ⊤ := ENNReal.add_lt_top.mpr ⟨hP_lt_top', ENNReal.ofReal_lt_top⟩
      have h7 : (⊤ : ENNReal) ≤ P + ENNReal.ofReal (δ k) := hH'_le
      have h8 : P + ENNReal.ofReal (δ k) = ⊤ := top_le_iff.mp h7
      exact h6.ne h8
    have hH_le : H k t ≤ P + ENNReal.ofReal (δ k) := by
      have h7 : H' t = H k t := by simp [H', ht_not_Bad]
      rw [h7] at hH'_le; exact hH'_le
    have hV_le : V k t ≤ ENNReal.ofReal (η k) := by
      have h7 : V' t = V k t := by simp [V', ht_not_Bad]
      rw [h7] at hV'_le; exact hV'_le
    have h_vol_null : volume {x | u k x = t} = 0 := by
      have h8 : t ∉ {s | volume {x | u k x = s} ≠ 0} := by intro h9; exact ht_not_Bad (Or.inl (Or.inl h9))
      simpa using h8
    have hH_finite : H k t < ⊤ := by
      have h8 : t ∉ {s | H k s = ⊤} := by intro h9; exact ht_not_Bad (Or.inl (Or.inr h9))
      have h9 : H k t ≠ ⊤ := h8
      exact lt_top_iff_ne_top.mpr h9
    have h_regular : IsRegularValue (u k) t := by
      have h8 : t ∉ N := by intro h9; exact ht_not_Bad (Or.inr h9)
      have h9 : t ∉ A := fun h10 => h8 (hN_sub h10)
      simpa [A] using h9
    exact ⟨t, ht_Ioo.1, ht_Ioo.2, h_vol_null, hH_finite, hH_le, hV_le, h_regular⟩

  let s' : ℕ → ℝ := fun k =>
    if h : ∃ (t : ℝ), GoodLevel k t then Classical.choose h else s0 k

  have hs_basic : ∀ k, 0 < s' k ∧ s' k < 1 := by
    intro k
    by_cases h : ∃ (t : ℝ), GoodLevel k t
    · have h_s' : s' k = Classical.choose h := by simp [s', h]
      rw [h_s']
      have hspec : GoodLevel k (Classical.choose h) := Classical.choose_spec h
      exact ⟨hspec.1, hspec.2.1⟩
    · have h_s' : s' k = s0 k := by simp [s', h]
      rw [h_s']; exact ⟨(hs0 k).1, (hs0 k).2.1⟩

  have hs_null : ∀ k, volume {x | u k x = s' k} = 0 := by
    intro k
    by_cases h : ∃ (t : ℝ), GoodLevel k t
    · have h_s' : s' k = Classical.choose h := by simp [s', h]
      rw [h_s']
      rcases (Classical.choose_spec h) with ⟨_, _, h_vol, _, _, _, _⟩
      exact h_vol
    · have h_s' : s' k = s0 k := by simp [s', h]
      rw [h_s']
      rcases (hs0 k) with ⟨_, _, h_vol, _, _⟩
      exact h_vol

  have hs_H_finite : ∀ k, μHE[m] {x | u k x = s' k} < ⊤ := by
    intro k
    by_cases h : ∃ (t : ℝ), GoodLevel k t
    · have h_s' : s' k = Classical.choose h := by simp [s', h]
      rw [h_s']
      rcases (Classical.choose_spec h) with ⟨_, _, _, h_Hfin, _, _, _⟩
      exact h_Hfin
    · have h_s' : s' k = s0 k := by simp [s', h]
      rw [h_s']
      rcases (hs0 k) with ⟨_, _, _, h_Hfin, _⟩
      exact h_Hfin

  have hs_H_bound : ∀ᶠ k in Filter.atTop,
      μHE[m] {x | u k x = s' k} ≤ P + ENNReal.ofReal (δ k) := by
    filter_upwards [h_exists] with k hk
    have h : ∃ (t : ℝ), GoodLevel k t := hk
    have h_s' : s' k = Classical.choose h := by simp [s', h]
    rw [h_s']
    rcases (Classical.choose_spec h) with ⟨_, _, _, _, h_Hbound, _, _⟩
    exact h_Hbound

  have hs_vol_bound : ∀ᶠ k in Filter.atTop,
      volume (symmDiff {x | u k x > s' k} S) ≤ ENNReal.ofReal (η k) := by
    filter_upwards [h_exists] with k hk
    have h : ∃ (t : ℝ), GoodLevel k t := hk
    have h_s' : s' k = Classical.choose h := by simp [s', h]
    rw [h_s']
    rcases (Classical.choose_spec h) with ⟨_, _, _, _, _, h_vol, _⟩
    exact h_vol

  have hs_regular : ∀ k, IsRegularValue (u k) (s' k) := by
    intro k
    by_cases h : ∃ (t : ℝ), GoodLevel k t
    · have h_s' : s' k = Classical.choose h := by simp [s', h]
      rw [h_s']
      rcases (Classical.choose_spec h) with ⟨_, _, _, _, _, _, h_reg⟩
      exact h_reg
    · have h_s' : s' k = s0 k := by simp [s', h]
      rw [h_s']
      rcases (hs0 k) with ⟨_, _, _, _, h_reg⟩
      exact h_reg

  let U : ℕ → Set (E (m + 1)) := fun k => {x | u k x > s' k}

  have h_frontier_sub : ∀ k, frontier (U k) ⊆ {x | u k x = s' k} := by
    intro k; exact frontier_level_set_subset' (h_u_smooth k).continuous

  have h_H_frontier_le : ∀ k, μHE[m] (frontier (U k)) ≤ μHE[m] {x | u k x = s' k} := by
    intro k; exact measure_mono (h_frontier_sub k)

  have h_H_frontier_finite : ∀ k, μHE[m] (frontier (U k)) < ⊤ := by
    intro k; exact lt_of_le_of_lt (h_H_frontier_le k) (hs_H_finite k)

  have hs_props : ∀ k, IsOpen (U k) ∧ MeasurableSet (U k) ∧ Bornology.IsBounded (U k) := by
    intro k
    have h1 : IsOpen (U k) := (h_u_smooth k).continuous.isOpen_preimage _ isOpen_Ioi
    have h2 : MeasurableSet (U k) := h1.measurableSet
    have h3 : Bornology.IsBounded (U k) := by
      have h4 : U k ⊆ tsupport (u k) := by
        intro x hx
        have h5 : u k x ≠ 0 := by have h6 : u k x > s' k := hx; linarith [(hs_basic k).1]
        exact subset_closure (Function.mem_support.mpr h5)
      have h5 : Bornology.IsBounded (tsupport (u k)) := (h_u_support k).isBounded
      exact h5.subset h4
    exact ⟨h1, h2, h3⟩

  have hs_iso : ∀ k, 0 < volume (U k) →
      ((m + 1 : ℕ) : ENNReal) * (volume (U k))^((m : ℝ) / (m + 1)) *
        (volume (unitBall (m + 1)))^(1 / ((m + 1 : ℝ))) ≤ μHE[m] (frontier (U k)) := by
    intro k hVk_pos
    have hU_open : IsOpen (U k) := (hs_props k).1
    have hU_bdd : Bornology.IsBounded (U k) := (hs_props k).2.2
    have hH_lt_top : μHE[m] (frontier (U k)) < ⊤ := h_H_frontier_finite k
    have hcover : ∀ (ε : ENNReal), 0 < ε → ε < ⊤ → SmoothBoundaryCover (U k) ε := by
      intro ε hε hε_top
      have h_reg : ∀ x ∈ {x | u k x = s' k}, fderiv ℝ (u k) x ≠ 0 := hs_regular k
      have h_main : SmoothBoundaryCover (interior (closure (U k))) ε :=
        level_set_smooth_boundary_cover (u k) ((h_u_smooth k).of_le (by norm_num))
          (h_u_support k) (s' k) h_reg ε hε hε_top
      have h_eq : interior (closure (U k)) = U k :=
        interior_closure_gt_eq_self (u k) ((h_u_smooth k).of_le (by norm_num)) (s' k) h_reg
      rw [h_eq] at h_main
      exact h_main
    exact smooth_isoperimetric_hausdorff hU_open hU_bdd hVk_pos hH_lt_top hcover

  -- Volume convergence
  have h_vol_conv : Filter.Tendsto (fun k => volume (U k)) Filter.atTop (nhds (volume S)) := by
    have hS_lt_top : volume S < ⊤ := hBdd.measure_lt_top
    have hU_lt_top : ∀ k, volume (U k) < ⊤ := by
      intro k
      have h_sub : U k ⊆ K := by
        intro x hx
        have h5 : u k x ≠ 0 := by have h6 : u k x > s' k := hx; linarith [(hs_basic k).1]
        have h7 : x ∈ Function.support (u k) := Function.mem_support.mpr h5
        have h8 : Function.support (u k) ⊆ K := by
          intro y hy
          by_contra h9
          have h10 : u k y = 0 := h_supp_K k y h9
          exact Function.mem_support.mp hy h10
        exact h8 h7
      have h : volume (U k) ≤ volume K := measure_mono h_sub
      exact lt_of_le_of_lt h hK_compact.measure_lt_top
    have h_le1 : ∀ k, volume (U k) ≤ volume S + volume (symmDiff (U k) S) := by
      intro k
      have h : U k ⊆ S ∪ symmDiff (U k) S := by
        intro x hx; by_cases hxS : x ∈ S; exact Or.inl hxS; exact Or.inr (Or.inl ⟨hx, hxS⟩)
      calc volume (U k) ≤ volume (S ∪ symmDiff (U k) S) := measure_mono h
           _ ≤ volume S + volume (symmDiff (U k) S) := measure_union_le _ _
    have h_le2 : ∀ k, volume S ≤ volume (U k) + volume (symmDiff (U k) S) := by
      intro k
      have h : S ⊆ U k ∪ symmDiff (U k) S := by
        intro x hx; by_cases hxU : x ∈ U k; exact Or.inl hxU; exact Or.inr (Or.inr ⟨hx, hxU⟩)
      calc volume S ≤ volume (U k ∪ symmDiff (U k) S) := measure_mono h
           _ ≤ volume (U k) + volume (symmDiff (U k) S) := measure_union_le _ _
    have h1 : ∀ᶠ k in Filter.atTop, volume (U k) ≤ volume S + ENNReal.ofReal (η k) := by
      filter_upwards [hs_vol_bound] with k hk
      exact le_trans (h_le1 k) (add_le_add_right hk (volume S))
    have h2 : ∀ᶠ k in Filter.atTop, volume S ≤ volume (U k) + ENNReal.ofReal (η k) := by
      filter_upwards [hs_vol_bound] with k hk
      exact le_trans (h_le2 k) (add_le_add_right hk (volume (U k)))
    have hη_tendsto' : Filter.Tendsto (fun k => ENNReal.ofReal (η k)) Filter.atTop (nhds 0) := by
      have h : Filter.Tendsto (ENNReal.ofReal ∘ η) Filter.atTop (nhds (ENNReal.ofReal (0 : ℝ))) :=
        (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hη_tendsto
      have h_eq : (ENNReal.ofReal ∘ η) = fun k => ENNReal.ofReal (η k) := by funext k; rfl
      have h0 : ENNReal.ofReal (0 : ℝ) = (0 : ENNReal) := by simp
      rw [h_eq] at h
      rw [h0] at h
      exact h
    let f : ℕ → ℝ := fun k => (volume (U k)).toReal
    let s : ℝ := (volume S).toReal
    have h1' : ∀ᶠ k in Filter.atTop, f k ≤ s + η k := by
      filter_upwards [h1] with k hk
      have h_b_ne_top : (volume S + ENNReal.ofReal (η k)) ≠ ⊤ :=
        (ENNReal.add_lt_top.mpr ⟨hS_lt_top, ENNReal.ofReal_lt_top⟩).ne
      have h : (volume (U k)).toReal ≤ (volume S + ENNReal.ofReal (η k)).toReal :=
        ENNReal.toReal_mono h_b_ne_top hk
      have h_sum : (volume S + ENNReal.ofReal (η k)).toReal = (volume S).toReal + (ENNReal.ofReal (η k)).toReal := by
        rw [ENNReal.toReal_add hS_lt_top.ne ENNReal.ofReal_lt_top.ne]
      rw [h_sum] at h
      have h_ofReal : (ENNReal.ofReal (η k)).toReal = η k := by
        rw [ENNReal.toReal_ofReal (by positivity)]
      rw [h_ofReal] at h
      exact h
    have h2' : ∀ᶠ k in Filter.atTop, s ≤ f k + η k := by
      filter_upwards [h2] with k hk
      have h_b_ne_top : (volume (U k) + ENNReal.ofReal (η k)) ≠ ⊤ :=
        (ENNReal.add_lt_top.mpr ⟨hU_lt_top k, ENNReal.ofReal_lt_top⟩).ne
      have h : (volume S).toReal ≤ (volume (U k) + ENNReal.ofReal (η k)).toReal :=
        ENNReal.toReal_mono h_b_ne_top hk
      have h_sum : (volume (U k) + ENNReal.ofReal (η k)).toReal = (volume (U k)).toReal + (ENNReal.ofReal (η k)).toReal := by
        rw [ENNReal.toReal_add (hU_lt_top k).ne ENNReal.ofReal_lt_top.ne]
      rw [h_sum] at h
      have h_ofReal : (ENNReal.ofReal (η k)).toReal = η k := by
        rw [ENNReal.toReal_ofReal (by positivity)]
      rw [h_ofReal] at h
      exact h
    have h3 : ∀ᶠ k in Filter.atTop, |f k - s| ≤ η k := by
      filter_upwards [h1', h2'] with k h1k h2k
      rw [abs_le]
      constructor <;> linarith
    have h4 : Filter.Tendsto f Filter.atTop (nhds s) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      have hη : ∀ᶠ k in Filter.atTop, η k < ε := hη_tendsto (Iio_mem_nhds hε)
      have h_eventually : ∀ᶠ k in Filter.atTop, dist (f k) s < ε := by
        filter_upwards [h3, hη] with k h3k hηk
        have h_abs : |f k - s| < ε := h3k.trans_lt hηk
        simpa [Real.dist_eq] using h_abs
      exact Filter.eventually_atTop.mp h_eventually
    have h5 : Filter.Tendsto (fun k => volume (U k)) Filter.atTop (nhds (volume S)) := by
      have h6 : Filter.Tendsto (fun k => ENNReal.ofReal (f k)) Filter.atTop (nhds (ENNReal.ofReal s)) :=
        (ENNReal.continuous_ofReal.tendsto s).comp h4
      have h7 : (fun k => ENNReal.ofReal (f k)) = fun k => volume (U k) := by
        funext k
        rw [ENNReal.ofReal_toReal (hU_lt_top k).ne]
      have h8 : ENNReal.ofReal s = volume S := by
        rw [ENNReal.ofReal_toReal hS_lt_top.ne]
      rw [h7, h8] at h6
      exact h6
    exact h5

  have h_limsup : Filter.limsup (fun k => μHE[m] (frontier (U k))) Filter.atTop ≤ P := by
    have h1 : ∀ᶠ k in Filter.atTop,
        μHE[m] (frontier (U k)) ≤ P + ENNReal.ofReal (δ k) := by
      filter_upwards [hs_H_bound] with k hk
      exact le_trans (h_H_frontier_le k) hk
    have hδ_tendsto' : Filter.Tendsto (fun k => P + ENNReal.ofReal (δ k)) Filter.atTop (nhds P) := by
      have h : Filter.Tendsto (fun k => ENNReal.ofReal (δ k)) Filter.atTop (nhds 0) := by
        have h' : Filter.Tendsto (ENNReal.ofReal ∘ δ) Filter.atTop (nhds (ENNReal.ofReal (0 : ℝ))) :=
          (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hδ_tendsto
        have h_eq : (ENNReal.ofReal ∘ δ) = fun k => ENNReal.ofReal (δ k) := by funext k; rfl
        have h0 : ENNReal.ofReal (0 : ℝ) = (0 : ENNReal) := by simp
        rw [h_eq] at h'
        rw [h0] at h'
        exact h'
      simpa [add_zero] using tendsto_const_nhds.add h
    rw [Filter.limsup_le_iff]
    intro b' hb'
    have h_eventually : ∀ᶠ k in Filter.atTop, P + ENNReal.ofReal (δ k) < b' :=
      hδ_tendsto' (Iio_mem_nhds hb')
    filter_upwards [h1, h_eventually] with k h1k h2k
    exact lt_of_le_of_lt h1k h2k

  exact ⟨s', hs_basic, hs_props, hs_iso, h_vol_conv, h_limsup⟩

end Geometry
