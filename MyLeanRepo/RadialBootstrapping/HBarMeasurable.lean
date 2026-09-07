module

/-
  HBarMeasurable.lean

  Prove that HBar_r (with strict bad-tube inequality) is open, hence measurable.
-/

public import MyLeanRepo.RadialBootstrapping.Basic
public import MyLeanRepo.OSWPrelude

@[expose] public section

open MeasureTheory Metric Set
open scoped ENNReal NNReal


noncomputable section

namespace RadialBootstrapping

/-- Unit sphere in Point = ℝ². -/
abbrev UnitSphere' : Type := ↥(Metric.sphere (0 : Point) 1)

/-- The linear functional v ↦ dot v n. -/
def normalFunctional (n : UnitSphere') : Point →ₗ[ℝ] ℝ :=
  innerₗ Point (n : Point)

/-- Helper: dot x n = normalFunctional n x. -/
lemma dot_eq_f (n : UnitSphere') (x : Point) :
    dot x (n : Point) = normalFunctional n x := by
  simp [dot, normalFunctional]
  <;> exact real_inner_comm (n : Point) x

/-- Helper: dot (a - b) n = dot a n - dot b n. -/
lemma dot_sub_n (n : UnitSphere') (a b : Point) :
    dot (a - b) (n : Point) = dot a (n : Point) - dot b (n : Point) := by
  let f := normalFunctional n
  have h : f (a - b) = f a - f b := map_sub f a b
  rw [dot_eq_f n (a - b), dot_eq_f n a, dot_eq_f n b] at *
  <;> exact h

/-- Helper: dot (c • a) n = c * dot a n. -/
lemma dot_smul_n (n : UnitSphere') (c : ℝ) (a : Point) :
    dot (c • a) (n : Point) = c * dot a (n : Point) := by
  let f := normalFunctional n
  have h : f (c • a) = c * f a := map_smul f c a
  rw [dot_eq_f n (c • a), dot_eq_f n a] at *
  <;> exact h

/-- The line through x with unit normal n. -/
def lineOfNormal (x : Point) (n : UnitSphere') : AffineSubspace ℝ Point :=
  AffineSubspace.mk' x (normalFunctional n).ker

/-- Membership in lineOfNormal. -/
lemma mem_lineOfNormal_iff (x : Point) (n : UnitSphere') (z : Point) :
    z ∈ (lineOfNormal x n : Set Point) ↔ dot (z - x) (n : Point) = 0 := by
  have h : z ∈ (lineOfNormal x n : Set Point) ↔ (z - x) ∈ (lineOfNormal x n).direction := by
    have h_mk : z ∈ AffineSubspace.mk' x (normalFunctional n).ker ↔
        (z - x) ∈ (normalFunctional n).ker := by
      simpa [vsub_eq_sub] using (@AffineSubspace.mem_mk' ℝ Point Point _ _ _ z x (normalFunctional n).ker)
    simpa [lineOfNormal] using h_mk
  rw [h]
  have h2 : (z - x) ∈ (lineOfNormal x n).direction ↔
      inner ℝ (n : Point) (z - x) = 0 := by
    simp [lineOfNormal, normalFunctional]
    <;> rfl
  rw [h2]
  have h_comm : inner ℝ (n : Point) (z - x) = inner ℝ (z - x) (n : Point) :=
    (real_inner_comm (n : Point) (z - x)).symm
  rw [h_comm]
  <;> rfl

/-- The direction of lineOfNormal has finrank 1. -/
lemma lineOfNormal_finrank (x : Point) (n : UnitSphere') :
    Module.finrank ℝ (lineOfNormal x n).direction = 1 := by
  have hn1 : ‖(n : Point)‖ = 1 := by
    simpa [UnitSphere', Metric.sphere] using n.prop
  have hne : (n : Point) ≠ 0 := by
    intro h; rw [h] at hn1; simp at hn1
  let f : Point →ₗ[ℝ] ℝ := normalFunctional n
  have h1 : f (n : Point) = 1 := by
    simp [f, normalFunctional, hn1, real_inner_self_eq_norm_sq] <;> norm_num
  have hsurj : Function.Surjective f := by
    intro r
    refine ⟨r • (n : Point), ?_⟩
    have h2 : f (r • (n : Point)) = r * f (n : Point) := by
      exact map_smul f r (n : Point)
    rw [h2, h1] <;> ring
  have h_range : LinearMap.range f = ⊤ := by
    rw [LinearMap.range_eq_top] <;> exact hsurj
  have h_eq : Module.finrank ℝ (LinearMap.range f) + Module.finrank ℝ (LinearMap.ker f) =
      Module.finrank ℝ Point := LinearMap.finrank_range_add_finrank_ker f
  have h2 : Module.finrank ℝ (LinearMap.range f) = 1 := by
    rw [h_range] <;> simp
  have h3 : Module.finrank ℝ Point = 2 := by simp
  have h4 : Module.finrank ℝ (LinearMap.ker f) = 1 := by
    rw [h2, h3] at h_eq <;> omega
  have h5 : (lineOfNormal x n).direction = (normalFunctional n).ker := by
    simp [lineOfNormal]
  rw [h5]
  exact h4

/-- Distance from y to line through x with unit normal n. -/
lemma dist_lineOfNormal (x : Point) (n : UnitSphere') (y : Point) :
    Metric.infDist y (lineOfNormal x n : Set Point) = |dot (y - x) (n : Point)| := by
  let d : ℝ := dot (y - x) (n : Point)
  let p : Point := y - d • (n : Point)
  have hn1 : ‖(n : Point)‖ = 1 := by
    simpa [UnitSphere', Metric.sphere] using n.prop
  have hp_in : p ∈ (lineOfNormal x n : Set Point) := by
    rw [mem_lineOfNormal_iff]
    have h_eq1 : p - x = (y - x) - d • (n : Point) := by
      simp [p] <;> abel
    rw [h_eq1]
    have h_inner_sub : inner ℝ ((y - x) - d • (n : Point)) (n : Point) =
        inner ℝ (y - x) (n : Point) - inner ℝ (d • (n : Point)) (n : Point) :=
      inner_sub_left (y - x) (d • (n : Point)) (n : Point)
    have h_inner_smul : inner ℝ (d • (n : Point)) (n : Point) =
        d * inner ℝ (n : Point) (n : Point) := by
      exact inner_smul_left (n : Point) (n : Point) (r := d)
    have h3 : inner ℝ (n : Point) (n : Point) = 1 := by
      simp [real_inner_self_eq_norm_sq, hn1] <;> norm_num
    have h4 : inner ℝ ((y - x) - d • (n : Point)) (n : Point) = 0 := by
      rw [h_inner_sub, h_inner_smul, h3]
      <;> simp [d] <;> ring
    simpa [dot] using h4
  have h1 : ‖y - p‖ = |d| := by
    have h : y - p = d • (n : Point) := by simp [p] <;> abel
    rw [h, norm_smul, hn1]
    have h2 : ‖d‖ = |d| := by exact Real.norm_eq_abs d
    rw [h2] <;> ring
  have h2 : ∀ (z : Point), z ∈ (lineOfNormal x n : Set Point) → |d| ≤ ‖y - z‖ := by
    intro z hz
    have h4 : dot (z - x) (n : Point) = 0 := (mem_lineOfNormal_iff x n z).mp hz
    have h5 : dot (y - z) (n : Point) = d := by
      have h6 : y - z = (y - x) - (z - x) := by abel
      rw [h6]
      have h7 : dot ((y - x) - (z - x)) (n : Point) =
          dot (y - x) (n : Point) - dot (z - x) (n : Point) :=
        dot_sub_n n (y - x) (z - x)
      rw [h7, h4] <;> ring
    have h_cs : |dot (y - z) (n : Point)| ≤ ‖y - z‖ * ‖(n : Point)‖ :=
      abs_real_inner_le_norm (y - z) (n : Point)
    have h7 : |d| ≤ ‖y - z‖ := by
      calc |d|
        = |dot (y - z) (n : Point)| := by rw [h5]
      _ ≤ ‖y - z‖ * ‖(n : Point)‖ := h_cs
      _ = ‖y - z‖ := by rw [hn1] <;> ring
    exact h7
  have h_nonempty : Set.Nonempty (lineOfNormal x n : Set Point) := ⟨p, hp_in⟩
  have h3 : Metric.infDist y (lineOfNormal x n : Set Point) ≤ |d| := by
    have h : Metric.infDist y (lineOfNormal x n : Set Point) ≤ dist y p :=
      Metric.infDist_le_dist_of_mem hp_in
    have h_dist : dist y p = ‖y - p‖ := by simp [dist_eq_norm]
    rw [h_dist] at h
    rw [h1] at h
    exact h
  have h4 : |d| ≤ Metric.infDist y (lineOfNormal x n : Set Point) := by
    have h5 : |d| ≤ Metric.infDist y (lineOfNormal x n : Set Point) ↔
        ∀ (z : Point), z ∈ (lineOfNormal x n : Set Point) → |d| ≤ dist y z :=
      le_infDist h_nonempty
    have h6 : ∀ (z : Point), z ∈ (lineOfNormal x n : Set Point) → |d| ≤ dist y z := by
      intro z hz
      have h7 : |d| ≤ ‖y - z‖ := h2 z hz
      have h8 : dist y z = ‖y - z‖ := by simp [dist_eq_norm]
      rw [h8]
      exact h7
    exact h5.mpr h6
  exact le_antisymm h3 h4

/-- Open r-tube around line through x with normal n. -/
def tubeOfNormal (r : ℝ) (x : Point) (n : UnitSphere') : Set Point :=
  {z | |dot (z - x) (n : Point)| < r}

/-- tubeOfNormal equals Metric.thickening r of the line. -/
lemma tubeOfNormal_eq_thickening (r : ℝ) (hr : 0 < r) (x : Point) (n : UnitSphere') :
    tubeOfNormal r x n = Metric.thickening r (lineOfNormal x n : Set Point) := by
  ext z
  simp only [tubeOfNormal, Set.mem_setOf_eq]
  have h_iff : z ∈ Metric.thickening r (lineOfNormal x n : Set Point) ↔
      ∃ (y : Point), y ∈ (lineOfNormal x n : Set Point) ∧ dist z y < r := by
    simpa [Metric.mem_thickening_iff] using Iff.rfl
  rw [h_iff]
  let d : ℝ := dot (z - x) (n : Point)
  let p : Point := z - d • (n : Point)
  have hn1 : ‖(n : Point)‖ = 1 := by
    simpa [UnitSphere', Metric.sphere] using n.prop
  have hp_in : p ∈ (lineOfNormal x n : Set Point) := by
    rw [mem_lineOfNormal_iff]
    have h_eq1 : p - x = (z - x) - d • (n : Point) := by simp [p] <;> abel
    rw [h_eq1]
    have h_inner_sub : inner ℝ ((z - x) - d • (n : Point)) (n : Point) =
        inner ℝ (z - x) (n : Point) - inner ℝ (d • (n : Point)) (n : Point) :=
      inner_sub_left (z - x) (d • (n : Point)) (n : Point)
    have h_inner_smul : inner ℝ (d • (n : Point)) (n : Point) =
        d * inner ℝ (n : Point) (n : Point) := by
      exact inner_smul_left (n : Point) (n : Point) (r := d)
    have h3 : inner ℝ (n : Point) (n : Point) = 1 := by
      simp [real_inner_self_eq_norm_sq, hn1] <;> norm_num
    have h4 : inner ℝ ((z - x) - d • (n : Point)) (n : Point) = 0 := by
      rw [h_inner_sub, h_inner_smul, h3]
      <;> simp [d] <;> ring
    simpa [dot] using h4
  have h_dist_p : dist z p = |d| := by
    have h : z - p = d • (n : Point) := by simp [p] <;> abel
    have h2 : dist z p = ‖z - p‖ := by simp [dist_eq_norm]
    rw [h2, h, norm_smul, hn1]
    have h3 : ‖d‖ = |d| := by exact Real.norm_eq_abs d
    rw [h3] <;> ring
  constructor
  · intro h_lt
    refine ⟨p, hp_in, ?_⟩
    rw [h_dist_p]
    exact h_lt
  · rintro ⟨y, hy, hlt⟩
    have h4 : dot (y - x) (n : Point) = 0 := (mem_lineOfNormal_iff x n y).mp hy
    have h5 : dot (z - y) (n : Point) = d := by
      have h6 : z - y = (z - x) - (y - x) := by abel
      rw [h6]
      have h7 : dot ((z - x) - (y - x)) (n : Point) =
          dot (z - x) (n : Point) - dot (y - x) (n : Point) :=
        dot_sub_n n (z - x) (y - x)
      rw [h7, h4] <;> ring
    have h_cs : |dot (z - y) (n : Point)| ≤ ‖z - y‖ * ‖(n : Point)‖ :=
      abs_real_inner_le_norm (z - y) (n : Point)
    have h9 : dist z y = ‖z - y‖ := by simp [dist_eq_norm]
    calc |d|
      = |dot (z - y) (n : Point)| := by rw [h5]
    _ ≤ ‖z - y‖ * ‖(n : Point)‖ := h_cs
    _ = ‖z - y‖ := by rw [hn1] <;> ring
    _ = dist z y := by rw [h9] <;> ring
    _ < r := hlt

/-- tubeOfNormal is open. -/
lemma tubeOfNormal_open (r : ℝ) (hr : 0 < r) (x : Point) (n : UnitSphere') :
    IsOpen (tubeOfNormal r x n) := by
  have h1 : Continuous (fun z : Point => z - x) := by fun_prop
  have h2 : Continuous (fun z : Point => (n : Point)) := by fun_prop
  have h3 : Continuous (fun z : Point => dot (z - x) (n : Point)) :=
    Continuous.inner h1 h2
  have h4 : Continuous (fun z : Point => |dot (z - x) (n : Point)|) :=
    Continuous.abs h3
  exact isOpen_lt h4 (by fun_prop)

/-- Lower semicontinuity of tube measure. -/
lemma tubeMeasure_lowerSemicontinuous
    (r : ℝ) (hr : 0 < r) (ν : Measure Point) [IsProbabilityMeasure ν] :
    LowerSemicontinuous (fun p : Point × UnitSphere' => ν (tubeOfNormal r p.1 p.2)) := by
  have h_main : ∀ (t : ENNReal), IsOpen {p : Point × UnitSphere' | ν (tubeOfNormal r p.1 p.2) > t} := by
    intro t
    let S : Set (Point × UnitSphere') := {p | ν (tubeOfNormal r p.1 p.2) > t}
    have hS_open : IsOpen S := by
      rw [isOpen_iff_mem_nhds]
      intro p hp
      have hgt : ν (tubeOfNormal r p.1 p.2) > t := hp
      have h_open : IsOpen (tubeOfNormal r p.1 p.2) :=
        tubeOfNormal_open r hr p.1 p.2
      have hreg : ν.InnerRegularWRT IsCompact IsOpen :=
        MeasureTheory.innerRegularWRT_isCompact_isOpen ν
      have h_inner : ∃ (K : Set Point), K ⊆ tubeOfNormal r p.1 p.2 ∧ IsCompact K ∧ t < ν K :=
        hreg h_open t hgt
      rcases h_inner with ⟨K, hK_sub, hK_comp, hK_gt⟩
      let W : Set (Point × (Point × UnitSphere')) :=
        {zp | |dot (zp.1 - zp.2.1) (zp.2.2 : Point)| < r}
      have hW_open : IsOpen W := by
        let f1 : (Point × (Point × UnitSphere')) → Point := fun zp => zp.1 - zp.2.1
        let f2 : (Point × (Point × UnitSphere')) → Point := fun zp => (zp.2.2 : Point)
        have h1 : Continuous f1 := by fun_prop
        have h2 : Continuous f2 := by fun_prop
        have h3 : Continuous (fun zp => dot (f1 zp) (f2 zp)) := Continuous.inner h1 h2
        exact isOpen_lt (Continuous.abs h3) (by fun_prop)
      have hKxp : K ×ˢ {p} ⊆ W := by
        rintro ⟨z, q⟩ ⟨hz, hq⟩
        have hq' : q = p := by simpa using hq
        rw [hq']
        exact hK_sub hz
      have h_singleton : IsCompact ({p} : Set (Point × UnitSphere')) := by simp
      have h := generalized_tube_lemma hK_comp h_singleton hW_open hKxp
      rcases h with ⟨V, U, hV_open, hU_open, hK_sub_V, hp_sub_U, h_box⟩
      have hK_U_sub : K ×ˢ U ⊆ W := by
        calc K ×ˢ U ⊆ V ×ˢ U := by gcongr <;> exact hK_sub_V
             _ ⊆ W := h_box
      have hpU : p ∈ U := by simpa using hp_sub_U
      have hU_nhds : U ∈ nhds p := hU_open.mem_nhds hpU
      have hU_sub_S : U ⊆ S := by
        intro q hq
        have h5 : K ⊆ tubeOfNormal r q.1 q.2 := by
          intro z hz
          have h6 : (z, q) ∈ W := hK_U_sub ⟨hz, hq⟩
          exact h6
        have h7 : ν K ≤ ν (tubeOfNormal r q.1 q.2) := measure_mono h5
        exact lt_of_lt_of_le hK_gt h7
      exact Filter.mem_of_superset hU_nhds hU_sub_S
    exact hS_open
  rw [lowerSemicontinuous_iff_isOpen_preimage]
  exact h_main

/-- The bad-tube incidence set is open. -/
lemma badTubeIncidence_open
    (r threshold : ℝ) (hr : 0 < r) (hthreshold : 0 ≤ threshold)
    (ν : Measure Point) [IsProbabilityMeasure ν] :
    IsOpen {p : (Point × Point) × UnitSphere' |
      ν (tubeOfNormal r p.1.1 p.2) > ENNReal.ofReal threshold ∧
      |dot (p.1.2 - p.1.1) (p.2 : Point)| < r} := by
  have h_map : Continuous (fun p : (Point × Point) × UnitSphere' => (p.1.1, p.2)) := by fun_prop
  have h1 : IsOpen {p : (Point × Point) × UnitSphere' |
      ν (tubeOfNormal r p.1.1 p.2) > ENNReal.ofReal threshold} := by
    have h_base : ∀ (t : ENNReal), IsOpen {p : Point × UnitSphere' | ν (tubeOfNormal r p.1 p.2) > t} :=
      tubeMeasure_lowerSemicontinuous r hr ν |>.isOpen_preimage
    have h_open : IsOpen {p : Point × UnitSphere' | ν (tubeOfNormal r p.1 p.2) > ENNReal.ofReal threshold} :=
      h_base (ENNReal.ofReal threshold)
    exact h_open.preimage h_map
  let g2 : (Point × Point) × UnitSphere' → ℝ :=
    fun p => |dot (p.1.2 - p.1.1) (p.2 : Point)|
  have hg1 : Continuous (fun p : (Point × Point) × UnitSphere' => p.1.2 - p.1.1) := by fun_prop
  have hg2 : Continuous (fun p : (Point × Point) × UnitSphere' => (p.2 : Point)) := by fun_prop
  have h_inner_cont : Continuous (fun p : (Point × Point) × UnitSphere' =>
      dot (p.1.2 - p.1.1) (p.2 : Point)) := Continuous.inner hg1 hg2
  have hg_cont : Continuous g2 := Continuous.abs h_inner_cont
  have h2 : IsOpen {p | g2 p < r} := isOpen_lt hg_cont (by fun_prop)
  exact h1.inter h2

/-- Every 1D affine subspace through x equals lineOfNormal x n for some n. -/
lemma exists_normal_of_affineSubspace
    (x : Point) (ℓ : AffineSubspace ℝ Point)
    (hxℓ : x ∈ (ℓ : Set Point)) (hfin : Module.finrank ℝ ℓ.direction = 1) :
    ∃ (n : UnitSphere'), ℓ = lineOfNormal x n := by
  let D : Submodule ℝ Point := ℓ.direction
  have hD_rank : Module.finrank ℝ D = 1 := hfin
  let Dperp : Submodule ℝ Point := D.orthogonal
  have hperp_rank : Module.finrank ℝ Dperp = 1 := by
    have h : Module.finrank ℝ D + Module.finrank ℝ Dperp = Module.finrank ℝ Point :=
      Submodule.finrank_add_finrank_orthogonal D
    have h2 : Module.finrank ℝ Point = 2 := by simp
    rw [h2, hD_rank] at h <;> omega
  have hperp_ne_bot : Dperp ≠ ⊥ := by
    intro hbot
    rw [hbot] at hperp_rank
    simp at hperp_rank <;> omega
  have hperp_nonzero : ∃ (v : Point), v ∈ Dperp ∧ v ≠ 0 :=
    Submodule.exists_mem_ne_zero_of_ne_bot hperp_ne_bot
  rcases hperp_nonzero with ⟨v, hv, hvne⟩
  have hnorm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hvne
  let nvec : Point := (‖v‖)⁻¹ • v
  have hn_norm : ‖nvec‖ = 1 := by
    simp [nvec, norm_smul, hnorm_pos.ne'] <;> field_simp <;> norm_num
  let n : UnitSphere' := ⟨nvec, by
    simp [UnitSphere', Metric.sphere, hn_norm] <;> norm_num⟩
  have hn_in_Dperp : (n : Point) ∈ Dperp := by
    have h1 : nvec ∈ Dperp := Dperp.smul_mem (‖v‖)⁻¹ hv
    exact h1
  let K : Submodule ℝ Point := (normalFunctional n).ker
  have hD_sub_K : D ≤ K := by
    intro w hw
    have h_perp : ∀ (u : Point), u ∈ D → inner ℝ u (n : Point) = 0 := by
      exact hn_in_Dperp
    have h : inner ℝ w (n : Point) = 0 := h_perp w hw
    have h' : inner ℝ (n : Point) w = 0 := by
      rw [real_inner_comm] <;> exact h
    simpa [K, normalFunctional] using h'
  have hK_eq_dir : K = (lineOfNormal x n).direction := by
    simp [K, lineOfNormal] <;> rfl
  have hK_rank : Module.finrank ℝ K = 1 := by
    rw [hK_eq_dir]
    exact lineOfNormal_finrank x n
  have hD_eq_K : D = K := by
    apply Submodule.eq_of_le_of_finrank_eq hD_sub_K
    rw [hD_rank, hK_rank]
  have h_dir_eq : ℓ.direction = (lineOfNormal x n).direction := by
    have h9 : D = K := hD_eq_K
    have h10 : (lineOfNormal x n).direction = K := by
      simp [lineOfNormal] <;> rfl
    exact Eq.trans h9 h10.symm
  have hx_line : x ∈ (lineOfNormal x n : Set Point) := by
    rw [mem_lineOfNormal_iff] <;> simp
  have h_eq : ℓ = lineOfNormal x n := by
    have h_iff : ℓ = lineOfNormal x n ↔ ℓ.direction = (lineOfNormal x n).direction :=
      AffineSubspace.eq_iff_direction_eq_of_mem hxℓ hx_line
    exact h_iff.mpr h_dir_eq
  exact ⟨n, h_eq⟩

/-- HBar_r with strict bad-tube inequality is open. -/
lemma HBar_r_strict_isOpen
    (ν₂ : Measure Point) [IsProbabilityMeasure ν₂]
    (K' σ τ r : ℝ) (hr : 0 < r) (hK'_nonneg : 0 ≤ K') (hστ_nonneg : 0 ≤ σ + τ) :
    IsOpen {p : Point × Point | ∃ (ℓ : AffineSubspace ℝ Point),
      p.1 ∈ (ℓ : Set Point) ∧ Module.finrank ℝ ℓ.direction = 1 ∧
      ν₂ (Metric.thickening r (ℓ : Set Point)) > ENNReal.ofReal (K' * Real.rpow r (σ + τ)) ∧
      p.2 ∈ Metric.thickening r (ℓ : Set Point)} := by
  let threshold : ℝ := K' * Real.rpow r (σ + τ)
  have hrpow_nonneg : 0 ≤ Real.rpow r (σ + τ) := Real.rpow_nonneg (by linarith) _
  have hthreshold_nonneg : 0 ≤ threshold := by
    dsimp only [threshold]
    exact mul_nonneg hK'_nonneg hrpow_nonneg
  let S : Set ((Point × Point) × UnitSphere') :=
    {p | ν₂ (tubeOfNormal r p.1.1 p.2) > ENNReal.ofReal threshold ∧
         |dot (p.1.2 - p.1.1) (p.2 : Point)| < r}
  have hS_open : IsOpen S := badTubeIncidence_open r threshold hr hthreshold_nonneg ν₂
  let π : (Point × Point) × UnitSphere' → Point × Point := Prod.fst
  have hπ_open : IsOpenMap π := isOpenMap_fst
  have h_main : {p : Point × Point | ∃ (ℓ : AffineSubspace ℝ Point),
      p.1 ∈ (ℓ : Set Point) ∧ Module.finrank ℝ ℓ.direction = 1 ∧
      ν₂ (Metric.thickening r (ℓ : Set Point)) > ENNReal.ofReal threshold ∧
      p.2 ∈ Metric.thickening r (ℓ : Set Point)} = π '' S := by
    ext ⟨x, y⟩
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨ℓ, hxℓ, hfin, hbad, hytube⟩
      rcases exists_normal_of_affineSubspace x ℓ hxℓ hfin with ⟨n, hℓ_eq⟩
      have h_tube_eq : Metric.thickening r (ℓ : Set Point) = tubeOfNormal r x n := by
        rw [hℓ_eq]
        exact (tubeOfNormal_eq_thickening r hr x n).symm
      have h1 : ν₂ (tubeOfNormal r x n) > ENNReal.ofReal threshold := by
        rw [←h_tube_eq]; exact hbad
      have h2 : |dot (y - x) (n : Point)| < r := by
        have h : y ∈ Metric.thickening r (ℓ : Set Point) := hytube
        rw [h_tube_eq] at h
        simpa [tubeOfNormal] using h
      exact ⟨((x, y), n), ⟨h1, h2⟩, rfl⟩
    · rintro ⟨a, hS, hπ⟩
      let n : UnitSphere' := a.2
      have ha1 : a.1 = (x, y) := by simpa [π] using hπ
      have h_a_eq : a = ((x, y), n) := by
        apply Prod.ext
        · exact ha1
        · rfl
      rw [h_a_eq] at hS
      let ℓ : AffineSubspace ℝ Point := lineOfNormal x n
      have hfin : Module.finrank ℝ ℓ.direction = 1 := lineOfNormal_finrank x n
      have hxℓ : x ∈ (ℓ : Set Point) := by
        rw [mem_lineOfNormal_iff] <;> simp
      have h_tube_eq : Metric.thickening r (ℓ : Set Point) = tubeOfNormal r x n :=
        (tubeOfNormal_eq_thickening r hr x n).symm
      have hbad : ν₂ (Metric.thickening r (ℓ : Set Point)) > ENNReal.ofReal threshold := by
        rw [h_tube_eq]; exact hS.1
      have hytube : y ∈ Metric.thickening r (ℓ : Set Point) := by
        rw [h_tube_eq, tubeOfNormal]; exact hS.2
      exact ⟨ℓ, hxℓ, hfin, hbad, hytube⟩
  rw [h_main]
  exact hπ_open S hS_open

/-- HBar_r with strict bad-tube inequality is measurable. -/
lemma HBar_r_strict_measurable
    (ν₂ : Measure Point) [IsProbabilityMeasure ν₂]
    (K' σ τ r : ℝ) (hr : 0 < r) (hK'_nonneg : 0 ≤ K') (hστ_nonneg : 0 ≤ σ + τ) :
    MeasurableSet {p : Point × Point | ∃ (ℓ : AffineSubspace ℝ Point),
      p.1 ∈ (ℓ : Set Point) ∧ Module.finrank ℝ ℓ.direction = 1 ∧
      ν₂ (Metric.thickening r (ℓ : Set Point)) > ENNReal.ofReal (K' * Real.rpow r (σ + τ)) ∧
      p.2 ∈ Metric.thickening r (ℓ : Set Point)} :=
  (HBar_r_strict_isOpen ν₂ K' σ τ r hr hK'_nonneg hστ_nonneg).measurableSet

end RadialBootstrapping

end
