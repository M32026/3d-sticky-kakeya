/-
# Borsuk-Ulam via Degree Theory (Skeleton)

Standard proof: an odd map f : S^{m+1} → R^{m+1} with no zero normalizes to an odd
map g : S^{m+1} → S^m. Restricting to the equator gives an odd self-map
h : S^m → S^m. By the odd degree lemma, deg(h) is odd (nonzero).
But the equatorial inclusion is nullhomotopic, so h is nullhomotopic,
hence deg(h) = 0. Contradiction.

## Main missing dependency
- `odd_degree_lemma`: any odd self-map of S^m has odd degree.
  Proved for m=1 in `BackupRoute.OddDegreeS1`.
  General case requires mod-2 homology (RP^n transfer sequence).
-/

import MyLeanRepo.Kakeya.BorsukUlam.BaseCases
import MyLeanRepo.Kakeya.BorsukUlam.OddDegreeTheorem
import MyLeanRepo.Kakeya.BorsukUlam.SeedMathlib.AlgebraicTopology.Degree.Homology
import MyLeanRepo.Kakeya.BorsukUlam.SeedMathlib.Topology.Homotopy.HomotopyGroupSphereSubsingletonOfLt.MapMissesPointNullHomotopic
import Mathlib.Analysis.Convex.Contractible

open scoped unitInterval Topology.Homotopy TopCat

namespace BorsukUlam.DegreeProof

open SeedMathlib.AlgebraicTopology.Degree

/-!
## Step 1: Equatorial embedding is nullhomotopic (general n)
-/

/-- North pole of Sphere n. -/
private def northPole {n : ℕ} : Sphere n :=
  let np_f : Fin (n + 1) → ℝ := fun i => if i = Fin.last n then 1 else 0
  let np_vec : EuclideanSpace ℝ (Fin (n + 1)) :=
    (PiLp.continuousLinearEquiv 2 ℝ _).symm np_f
  have hnp_norm : ‖np_vec‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    have h1 : ∀ i, np_vec i = np_f i := by intro i; rfl
    have h_sum : ∑ i : Fin (n + 1), ‖np_vec i‖ ^ 2 = 1 := by
      have h2 : ∑ i : Fin (n + 1), ‖np_vec i‖ ^ 2 = ∑ i : Fin (n + 1), ‖np_f i‖ ^ 2 := by
        apply Finset.sum_congr rfl; intro i _; rw [h1]
      rw [h2]
      simp [np_f, Fin.sum_univ_succ, Fin.last] <;> norm_num
    rw [h_sum] <;> norm_num
  ⟨np_vec, mem_sphere_zero_iff_norm.mpr hnp_norm⟩

/-- Equatorial embedding from Sphere n to Sphere (n+1). -/
private noncomputable def sphereEquatorialEmbedding {n : ℕ} : Sphere n → Sphere (n + 1) :=
  fun x =>
    let v : EuclideanSpace ℝ (Fin (n + 1)) := x.val
    let w : EuclideanSpace ℝ (Fin (n + 2)) := BorsukUlam.extendZero (n + 1) v
    have hw : ‖w‖ = 1 := by
      rw [BorsukUlam.norm_extendZero]
      exact mem_sphere_zero_iff_norm.mp x.property
    ⟨w, mem_sphere_zero_iff_norm.mpr hw⟩

/-- Continuity of sphereEquatorialEmbedding. -/
private lemma continuous_sphereEquatorialEmbedding {n : ℕ} :
    Continuous (@sphereEquatorialEmbedding n) := by
  have h_down : Continuous (fun x : Sphere n => (x : EuclideanSpace ℝ (Fin (n + 1)))) :=
    continuous_subtype_val
  have h_ext : Continuous (fun x : Sphere n => BorsukUlam.extendZero (n + 1) (x : EuclideanSpace ℝ (Fin (n + 1)))) :=
    (BorsukUlam.continuous_extendZero (n + 1)).comp h_down
  exact continuous_induced_rng.mpr h_ext

/-- The equatorial embedding Sphere n → Sphere (n+1) is nullhomotopic. -/
theorem sphere_equatorial_embedding_nullhomotopic {n : ℕ} :
    (⟨sphereEquatorialEmbedding, continuous_sphereEquatorialEmbedding⟩ :
      C(Sphere n, Sphere (n + 1))).Nullhomotopic := by
  let i : C(Sphere n, Sphere (n + 1)) :=
    ⟨sphereEquatorialEmbedding, continuous_sphereEquatorialEmbedding⟩
  let p : Sphere (n + 1) := northPole
  let Y := {y : Sphere (n + 1) // y ≠ p}

  have h_miss : ∀ (x : Sphere n), sphereEquatorialEmbedding x ≠ p := by
    intro x h
    have h_last : (sphereEquatorialEmbedding x).val (Fin.last (n + 1)) = 0 := by
      simp [sphereEquatorialEmbedding, BorsukUlam.extendZero_apply, Fin.last] <;> omega
    have h_p_last : p.val (Fin.last (n + 1)) = 1 := by
      have h1 : p.val (Fin.last (n + 1)) = (if Fin.last (n + 1) = Fin.last (n + 1) then (1 : ℝ) else 0) := by rfl
      rw [h1]; simp
    have h_eq : (sphereEquatorialEmbedding x).val (Fin.last (n + 1)) = p.val (Fin.last (n + 1)) := by
      rw [h]
    rw [h_last, h_p_last] at h_eq <;> norm_num at h_eq

  let i_down : C(Sphere n, Y) := ⟨
    fun x => ⟨sphereEquatorialEmbedding x, h_miss x⟩,
    continuous_sphereEquatorialEmbedding.subtype_mk h_miss
  ⟩

  let e : Y ≃ₜ EuclideanSpace ℝ (Fin (n + 1)) :=
    HomotopySphere.sphere_minus_point_homeo p

  let g : C(Sphere n, EuclideanSpace ℝ (Fin (n + 1))) :=
    ⟨e ∘ i_down, e.continuous.comp i_down.continuous⟩

  have hg_null : g.Nullhomotopic := by
    have h_id : (ContinuousMap.id (EuclideanSpace ℝ (Fin (n + 1)))).Nullhomotopic :=
      id_nullhomotopic _
    exact h_id.comp_left g

  let back : C(EuclideanSpace ℝ (Fin (n + 1)), Sphere (n + 1)) := ⟨
    fun v => (e.symm v).val,
    continuous_subtype_val.comp e.symm.continuous
  ⟩

  have h_eq : back.comp g = i := by
    ext x
    simp [back, g, i_down, e, i] <;> rfl
  have h_goal : (back.comp g).Nullhomotopic := hg_null.comp_right back
  have h_final : i.Nullhomotopic := by
    exact h_eq ▸ h_goal
  exact h_final

/-!
## Step 2: Odd degree lemma (SORRY for general n)
-/

/-- Odd degree lemma: an odd self-map of Sphere m has nonzero degree.
    Proved for m=1; general case requires mod-2 homology. -/
theorem odd_degree_lemma {m : ℕ} (hm : 0 < m)
    (f : C(Sphere m, Sphere m))
    (hf_odd : ∀ x, f (-x) = -f x) :
    degree f hm ≠ 0 :=
  BorsukUlam.OddDegreeTheorem.odd_degree_lemma m hm f hf_odd

/-!
## Step 3: Normalization

Given f : Sphere (m+1) → EuclideanSpace ℝ (Fin (m+1)) with no zero,
normalize to get g : Sphere (m+1) → Sphere m.
-/

/-- Normalize a nowhere-zero vector-valued map to a sphere-valued map. -/
noncomputable def normalizeMap {m : ℕ} {X : Type*} [TopologicalSpace X]
    (f : X → EuclideanSpace ℝ (Fin (m + 1))) (hf_cont : Continuous f)
    (hf_no_zero : ∀ x, f x ≠ 0) :
    X → Sphere m :=
  fun x =>
    let v := f x
    let w := (‖v‖)⁻¹ • v
    have hw : ‖w‖ = 1 := by
      have hpos : 0 < ‖v‖ := norm_pos_iff.mpr (hf_no_zero x)
      simp [w, norm_smul, hpos.ne'] <;> field_simp [hpos.ne'] <;> norm_num
    ⟨w, mem_sphere_zero_iff_norm.mpr hw⟩

/-- The normalized map is continuous. -/
lemma normalizeMap_continuous {m : ℕ} {X : Type*} [TopologicalSpace X]
    (f : X → EuclideanSpace ℝ (Fin (m + 1))) (hf_cont : Continuous f)
    (hf_no_zero : ∀ x, f x ≠ 0) :
    Continuous (normalizeMap f hf_cont hf_no_zero) := by
  have h_norm_cont : Continuous (fun x : X => ‖f x‖) := continuous_norm.comp hf_cont
  have h_norm_ne_zero : ∀ x, ‖f x‖ ≠ 0 := fun x => norm_ne_zero_iff.mpr (hf_no_zero x)
  have h_norm_inv_cont : Continuous (fun x : X => (‖f x‖)⁻¹) :=
    h_norm_cont.inv₀ h_norm_ne_zero
  have h_raw_cont : Continuous (fun x : X => (‖f x‖)⁻¹ • f x) :=
    h_norm_inv_cont.smul hf_cont
  have h_prop : ∀ x, (‖f x‖)⁻¹ • f x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 := by
    intro x
    have hpos : 0 < ‖f x‖ := norm_pos_iff.mpr (hf_no_zero x)
    have h : ‖(‖f x‖)⁻¹ • f x‖ = 1 := by
      simp [norm_smul, hpos.ne'] <;> field_simp [hpos.ne'] <;> norm_num
    exact mem_sphere_zero_iff_norm.mpr h
  have h_main : Continuous (fun x : X => (⟨(‖f x‖)⁻¹ • f x, h_prop x⟩ : Sphere m)) :=
    h_raw_cont.subtype_mk h_prop
  exact h_main

/-- The normalized map is odd if the original map is odd. -/
lemma normalizeMap_odd {m : ℕ} {X : Type*} [TopologicalSpace X]
    (f : X → EuclideanSpace ℝ (Fin (m + 1))) (hf_cont : Continuous f)
    (hf_no_zero : ∀ x, f x ≠ 0)
    (neg : X → X) (hf_odd : ∀ x, f (neg x) = -f x) :
    ∀ x, (normalizeMap f hf_cont hf_no_zero) (neg x) =
        -(normalizeMap f hf_cont hf_no_zero) x := by
  intro x
  apply Subtype.ext
  have h1 : f (neg x) = -f x := hf_odd x
  have h2 : ‖f (neg x)‖ = ‖f x‖ := by rw [h1, norm_neg]
  have h3 : (‖f (neg x)‖)⁻¹ • f (neg x) = -((‖f x‖)⁻¹ • f x) := by
    have h4 : ‖f (neg x)‖ = ‖f x‖ := by rw [h1, norm_neg]
    have h5 : (‖f (neg x)‖)⁻¹ = (‖f x‖)⁻¹ := by rw [h4]
    rw [h5, h1]
    <;> simp [smul_neg]
  exact h3

/-!
## Step 4: Main Borsuk-Ulam critical case j=n
-/

/-- Borsuk-Ulam critical case j=m+1 via degree theory.
    Requires m > 0 (the m=0 case is the n=1 base case). -/
theorem borsuk_ulam_critical {m : ℕ} (hm : 0 < m)
    (f : 𝕊 (m + 1) → EuclideanSpace ℝ (Fin (m + 1)))
    (hf_cont : Continuous f)
    (hf_odd : ∀ x, f (BorsukUlam.sphereAntipodal (m + 1) x) = -f x) :
    0 ∈ Set.range f := by
  by_contra h
  have h_no_zero : ∀ x, f x ≠ 0 := by
    intro x hfx; exact h ⟨x, hfx⟩

  -- Transfer to Sphere (m+1) (Type 0)
  let f_down : Sphere (m + 1) → EuclideanSpace ℝ (Fin (m + 1)) :=
    fun y => f (ULift.up y)
  have hf_down_cont : Continuous f_down := hf_cont.comp continuous_uliftUp
  have h_no_zero_down : ∀ y, f_down y ≠ 0 := fun y => h_no_zero (ULift.up y)
  have hf_down_odd : ∀ y, f_down (-y) = -f_down y := by
    intro y
    have h_antipodal : BorsukUlam.sphereAntipodal (m + 1) (ULift.up y) = ULift.up (-y) := by
      apply ULift.ext; apply Subtype.ext
      simp [BorsukUlam.sphereAntipodal] <;> rfl
    calc
      f_down (-y) = f (ULift.up (-y)) := rfl
      _ = f (BorsukUlam.sphereAntipodal (m + 1) (ULift.up y)) := by rw [←h_antipodal]
      _ = -f (ULift.up y) := hf_odd (ULift.up y)
      _ = -f_down y := rfl

  -- Normalize
  let g : Sphere (m + 1) → Sphere m := normalizeMap f_down hf_down_cont h_no_zero_down
  have hg_cont : Continuous g := normalizeMap_continuous f_down hf_down_cont h_no_zero_down
  have hg_odd : ∀ y, g (-y) = -g y :=
    normalizeMap_odd f_down hf_down_cont h_no_zero_down (fun y => -y) hf_down_odd

  let g_cmap : C(Sphere (m + 1), Sphere m) := ⟨g, hg_cont⟩

  -- Restrict to equator
  let i : C(Sphere m, Sphere (m + 1)) :=
    ⟨sphereEquatorialEmbedding, continuous_sphereEquatorialEmbedding⟩
  let h_map : C(Sphere m, Sphere m) := g_cmap.comp i

  -- h_map is odd
  have h_h_odd : ∀ x, h_map (-x) = -h_map x := by
    intro x
    have h1 : i (-x) = -i x := by
      apply Subtype.ext
      ext j
      simp [i, sphereEquatorialEmbedding, BorsukUlam.extendZero_apply]
      <;> split_ifs <;> simp_all <;> ring_nf <;> omega
    calc
      h_map (-x) = g_cmap (i (-x)) := rfl
      _ = g_cmap (-(i x)) := by rw [h1]
      _ = -g_cmap (i x) := hg_odd (i x)
      _ = -h_map x := rfl

  -- h_map is nullhomotopic because i is nullhomotopic
  have h_i_null : i.Nullhomotopic := sphere_equatorial_embedding_nullhomotopic
  have h_h_null : h_map.Nullhomotopic := h_i_null.comp_right g_cmap

  -- Therefore degree is 0
  have h_deg_zero : degree h_map hm = 0 :=
    degree_zero_of_nullhomotopic h_map hm h_h_null

  -- But odd degree lemma says degree is nonzero
  have h_deg_nonzero : degree h_map hm ≠ 0 :=
    odd_degree_lemma hm h_map h_h_odd

  exact h_deg_nonzero h_deg_zero

/-!
## Step 5: Full Borsuk-Ulam theorem by induction

Combines base cases, reduction, and the critical case.
-/

/-- Full Borsuk-Ulam theorem (skeleton). -/
theorem borsuk_ulam_full {n j : ℕ} (hjn : j ≤ n)
    (f : 𝕊 n → EuclideanSpace ℝ (Fin j))
    (hf_cont : Continuous f)
    (hf_odd : ∀ x, f (BorsukUlam.sphereAntipodal n x) = -f x) :
    0 ∈ Set.range f := by
  induction n with
  | zero =>
    have h_j0 : j = 0 := by omega
    subst h_j0
    exact BorsukUlam.borsuk_ulam_j_zero 0 f hf_cont hf_odd
  | succ n ih =>
    by_cases h : j ≤ n
    · -- j < n+1, reduce to (n, j)
      exact BorsukUlam.borsuk_ulam_reduction h f hf_cont hf_odd
        (fun g hg_cont hg_odd => ih h g hg_cont hg_odd)
    · -- j = n+1, critical case
      have h_j_eq : j = n + 1 := by omega
      subst h_j_eq
      cases n with
      | zero =>
        -- n+1 = 1, use base case via EuclideanSpace ℝ (Fin 1) ≅ ℝ
        let e1 : EuclideanSpace ℝ (Fin 1) ≃L[ℝ] (Fin 1 → ℝ) :=
          PiLp.continuousLinearEquiv 2 ℝ _
        let e2 : (Fin 1 → ℝ) ≃L[ℝ] ℝ :=
          { toFun := fun f => f 0
            invFun := fun r _ => r
            map_add' := by simp
            map_smul' := by simp
            continuous_toFun := by fun_prop
            continuous_invFun := by fun_prop
            left_inv := by
              intro f
              funext i
              have h_i : i = 0 := by simp [Fin.ext_iff] <;> omega
              rw [h_i] <;> rfl
            right_inv := by
              intro r
              simp }
        let e : EuclideanSpace ℝ (Fin 1) ≃L[ℝ] ℝ := e1.trans e2
        let f' : 𝕊 1 → ℝ := fun x => e (f x)
        have hf'_cont : Continuous f' := by fun_prop
        have hf'_odd : ∀ x, f' (BorsukUlam.sphereAntipodal 1 x) = -f' x := by
          intro x
          have h1 : f (BorsukUlam.sphereAntipodal 1 x) = -f x := hf_odd x
          simp [f', h1]
          <;> rfl
        have h_main : 0 ∈ Set.range f' :=
          BorsukUlam.borsuk_ulam_n1_j1 f' hf'_cont hf'_odd
        rcases h_main with ⟨x, hx⟩
        have h_fx_zero : f x = 0 := by
          have h2 : e (f x) = 0 := hx
          have h3 : e (f x) = e 0 := by
            rw [map_zero e] at * <;> exact h2
          exact e.injective h3
        exact ⟨x, h_fx_zero⟩
      | succ n' =>
        -- n+1 ≥ 2, use critical case with m = n
        exact borsuk_ulam_critical (by linarith) f hf_cont hf_odd

end BorsukUlam.DegreeProof
