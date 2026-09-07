/-
# Deformation Retraction: V ≃ RP^{n-1}

Proves that V = EmbeddedRP n \\ {erp0 n} deformation retracts onto
RPnMinus1 = {z : EmbeddedRP n | z_{00} = 0}.

Uses an explicit formula in Veronese coordinates.

## Main Results
- `vHomotopyEquiv`: VType (m+1) ≃ₕ EmbeddedRP m

## Whiteprint Node
- rp_affine_cover (supporting)
-/

import MyLeanRepo.Kakeya.BorsukUlam.RealProjective.Cover
import MyLeanRepo.Kakeya.BorsukUlam.RealProjective.MetricEmbedding
import MyLeanRepo.Kakeya.BorsukUlam.Vendored.AlgebraicTopology.SingularHomology.EuclideanSpace.StdSphereHomology
import Mathlib.Tactic

noncomputable section

open BorsukUlam.BackupRoute
open BorsukUlam.RealProjective
open AlgebraicTopology CategoryTheory
open AlgebraicTopology.StdSphereHomology

namespace BorsukUlam.RealProjective.Cover

variable {n : ℕ}

/-! ### Deformation formula -/

/-- Squared norm of deformation vector: 1 - z_{00} * t * (2 - t). -/
def deformNormSq (t : ℝ) (z : EmbeddedRP n) : ℝ :=
  1 - z.val (0, 0) * t * (2 - t)

/-- V = EmbeddedRP n \\ {erp0 n}. -/
abbrev VType (n : ℕ) : Type := {z : EmbeddedRP n // z ≠ erp0 n}

/-- RP^{n-1} subspace: z_{00} = 0. -/
abbrev RPnMinus1Type (n : ℕ) : Type :=
  {z : EmbeddedRP n // z.val (0, 0) = 0}

lemma deformNormSq_pos (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    {z : EmbeddedRP n} (hz : z ≠ erp0 n) :
    0 < deformNormSq t z := by
  let z00 := z.val (0, 0)
  have h1 : 0 ≤ z00 := coord00_nonneg z
  have h2 : z00 ≤ 1 := coord00_le_one z
  have h3 : z00 < 1 := by
    by_contra h4
    have h5 : z00 = 1 := by linarith
    exact hz ((coord00_eq_one_iff_erp0 z).mp h5)
  have h_t0 : 0 ≤ t := ht.1
  have h_t1 : t ≤ 1 := ht.2
  have h5 : 0 ≤ t * (2 - t) := by nlinarith
  have h6 : t * (2 - t) ≤ 1 := by nlinarith
  dsimp only [deformNormSq]
  nlinarith

/-- Deformation in Veronese coordinates. -/
def deformFun (t : ℝ) (z : EmbeddedRP n) :
    EuclideanSpace ℝ (Fin (n + 1) × Fin (n + 1)) :=
  let s2 := deformNormSq t z
  let c := 1 - t
  WithLp.toLp 2 fun (p : Fin (n + 1) × Fin (n + 1)) =>
    if p.1 = 0 then
      if p.2 = 0 then c ^ 2 * z.val (0, 0) / s2
      else c * z.val (0, p.2) / s2
    else
      if p.2 = 0 then c * z.val (p.1, 0) / s2
      else z.val (p.1, p.2) / s2

/-! ### Sphere-level helpers (private) -/

/-- Sphere-level deformation vector. -/
private def deformVec (t : ℝ) (x : SphereType n) : EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 fun j =>
    if j = 0 then (1 - t) * x.val 0 else x.val j

private lemma deformVec_coord0 (t : ℝ) (x : SphereType n) :
    (deformVec t x) 0 = (1 - t) * x.val 0 := by
  simp [deformVec] <;> rfl

private lemma deformVec_coordSucc (t : ℝ) (x : SphereType n) (i : Fin n) :
    (deformVec t x) i.succ = x.val i.succ := by
  simp [deformVec, Fin.succ_ne_zero] <;> rfl

private lemma deformVec_normSq (t : ℝ) (x : SphereType n) :
    ‖deformVec t x‖ ^ 2 = deformNormSq t (veroneseEquiv n (quotientMap n x)) := by
  let c := 1 - t
  let z := veroneseEquiv n (quotientMap n x)
  have h_z00 : z.val (0, 0) = (x.val 0) ^ 2 := by
    have h5 : z.val = veroneseMap (quotientMap n x) := by rfl
    rw [h5]
    have h6 : veroneseMap (quotientMap n x) = veroneseFun x := by
      simp [veroneseMap, Quotient.lift_mk] <;> rfl
    rw [h6]
    have h7 := veroneseFun_apply x 0 0
    rw [h7] <;> ring
  have h2 : ‖deformVec t x‖ ^ 2 = ∑ j : Fin (n + 1), ((deformVec t x) j) ^ 2 :=
    EuclideanSpace.real_norm_sq_eq (deformVec t x)
  have h3 : ∑ j : Fin (n + 1), ((deformVec t x) j) ^ 2 =
      (deformVec t x) 0 ^ 2 + ∑ i : Fin n, (deformVec t x) i.succ ^ 2 := by
    rw [Fin.sum_univ_succ] <;> rfl
  have h4 : (deformVec t x) 0 = c * x.val 0 := deformVec_coord0 t x
  have h5 : ∀ i : Fin n, (deformVec t x) i.succ = x.val i.succ := deformVec_coordSucc t x
  have h6 : ∑ i : Fin n, (deformVec t x) i.succ ^ 2 = ∑ i : Fin n, (x.val i.succ) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _; rw [h5 i]
  have h_ynorm : ‖x.val‖ ^ 2 = 1 := by
    have h7 : ‖x.val‖ = 1 := mem_sphere_zero_iff_norm.mp x.property
    rw [h7] <;> norm_num
  have h_sum : ‖x.val‖ ^ 2 = (x.val 0) ^ 2 + ∑ i : Fin n, (x.val i.succ) ^ 2 := by
    have h9 : ‖x.val‖ ^ 2 = ∑ j : Fin (n + 1), (x.val j) ^ 2 :=
      EuclideanSpace.real_norm_sq_eq x.val
    rw [h9, Fin.sum_univ_succ] <;> rfl
  have h_succ_sum : ∑ i : Fin n, (x.val i.succ) ^ 2 = 1 - (x.val 0) ^ 2 := by linarith
  have h_lhs : (deformVec t x) 0 ^ 2 + ∑ i : Fin n, (deformVec t x) i.succ ^ 2 =
      1 - (x.val 0) ^ 2 * t * (2 - t) := by
    rw [h4, h6, h_succ_sum]
    <;> dsimp only [c] <;> ring
  have h_rhs : deformNormSq t z = 1 - (x.val 0) ^ 2 * t * (2 - t) := by
    dsimp only [deformNormSq]
    rw [h_z00] <;> ring
  rw [h2, h3]
  exact Eq.trans h_lhs h_rhs.symm

/-- Normalized sphere-level deformation. -/
private def deformSphere (t : ℝ) (x : SphereType n) (hnv : 0 < ‖deformVec t x‖) :
    SphereType n :=
  let v := deformVec t x
  let nv := ‖v‖
  ⟨nv⁻¹ • v, by
    have h_norm : ‖nv⁻¹ • v‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hnv]
      <;> field_simp [hnv.ne'] <;> ring
    exact mem_sphere_zero_iff_norm.mpr h_norm⟩

private lemma deformSphere_val (t : ℝ) (x : SphereType n) (hnv : 0 < ‖deformVec t x‖) :
    (deformSphere t x hnv).val = ‖deformVec t x‖⁻¹ • deformVec t x := by rfl

/-! ### Membership proof -/

/-- deformFun t z ∈ RPnEmbedded n for z ∈ V. -/
lemma deformFun_mem_RPnEmbedded (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    {z : EmbeddedRP n} (hz : z ≠ erp0 n) :
    deformFun t z ∈ RPnEmbedded n := by
  let rp : RPType n := (veroneseEquiv n).symm z
  let x : SphereType n := Quotient.out rp
  have h_eq1 : quotientMap n x = rp := Quotient.out_eq rp
  have h_z_eq : z = veroneseEquiv n rp :=
    (veroneseEquiv n).right_inv z |>.symm
  have h_zval : ∀ (a b : Fin (n + 1)), z.val (a, b) = x.val a * x.val b := by
    intro a b
    have h5 : z.val = veroneseMap (quotientMap n x) := by
      rw [h_z_eq, h_eq1] <;> rfl
    rw [h5]
    have h6 : veroneseMap (quotientMap n x) = veroneseFun x := by
      simp [veroneseMap, Quotient.lift_mk] <;> rfl
    rw [h6]
    exact veroneseFun_apply x a b
  have h_ver_eq : veroneseEquiv n (quotientMap n x) = z := by
    rw [h_eq1] <;> exact h_z_eq.symm
  have hnv : 0 < ‖deformVec t x‖ := by
    have h_sq : 0 < ‖deformVec t x‖ ^ 2 := by
      rw [deformVec_normSq t x, h_ver_eq]
      exact deformNormSq_pos t ht hz
    have h_ne : ‖deformVec t x‖ ≠ 0 := by
      intro h; rw [h] at h_sq; simp at h_sq
    exact lt_of_le_of_ne (norm_nonneg _) h_ne.symm
  let y := deformSphere t x hnv
  have h_s2 : ‖deformVec t x‖ ^ 2 = deformNormSq t z := by
    rw [deformVec_normSq t x, h_ver_eq]
  have h_main : deformFun t z = veroneseFun y := by
    ext ⟨i, j⟩
    have h_ver : veroneseFun y (i, j) = y.val i * y.val j := veroneseFun_apply y i j
    rw [h_ver]
    have h_yval : y.val = ‖deformVec t x‖⁻¹ • deformVec t x := deformSphere_val t x hnv
    have h_vi : y.val i = ‖deformVec t x‖⁻¹ * (deformVec t x) i := by
      rw [h_yval] <;> rfl
    have h_vj : y.val j = ‖deformVec t x‖⁻¹ * (deformVec t x) j := by
      rw [h_yval] <;> rfl
    rw [h_vi, h_vj]
    have h_pos : 0 < ‖deformVec t x‖ := hnv
    have h_main2 : (‖deformVec t x‖⁻¹ * (deformVec t x) i) * (‖deformVec t x‖⁻¹ * (deformVec t x) j) =
        ((deformVec t x) i * (deformVec t x) j) / ‖deformVec t x‖ ^ 2 := by
      field_simp [h_pos.ne'] <;> ring
    rw [h_main2, h_s2]
    by_cases hi : i = 0 <;> by_cases hj : j = 0
    · subst hi hj
      have h_v0 : (deformVec t x) 0 = (1 - t) * x.val 0 := deformVec_coord0 t x
      have h_goal : (deformVec t x) 0 * (deformVec t x) 0 / deformNormSq t z =
          (1 - t) ^ 2 * z.val (0, 0) / deformNormSq t z := by
        rw [h_v0, h_zval 0 0] <;> ring
      simpa [deformFun] using h_goal.symm
    · subst hi
      have h_v0 : (deformVec t x) 0 = (1 - t) * x.val 0 := deformVec_coord0 t x
      have h_vj : (deformVec t x) j = x.val j := by
        have h_exists : ∃ (k : Fin n), j = k.succ := by
          refine' ⟨Fin.pred j hj, _⟩; exact (Fin.succ_pred j hj).symm
        rcases h_exists with ⟨k, rfl⟩
        exact deformVec_coordSucc t x k
      have h_goal : (deformVec t x) 0 * (deformVec t x) j / deformNormSq t z =
          (1 - t) * z.val (0, j) / deformNormSq t z := by
        rw [h_v0, h_vj, h_zval 0 j] <;> ring
      simpa [deformFun, hj] using h_goal.symm
    · subst hj
      have h_vi : (deformVec t x) i = x.val i := by
        have h_exists : ∃ (k : Fin n), i = k.succ := by
          refine' ⟨Fin.pred i hi, _⟩; exact (Fin.succ_pred i hi).symm
        rcases h_exists with ⟨k, rfl⟩
        exact deformVec_coordSucc t x k
      have h_v0 : (deformVec t x) 0 = (1 - t) * x.val 0 := deformVec_coord0 t x
      have h_goal : (deformVec t x) i * (deformVec t x) 0 / deformNormSq t z =
          (1 - t) * z.val (i, 0) / deformNormSq t z := by
        rw [h_vi, h_v0, h_zval i 0] <;> ring
      simpa [deformFun, hi] using h_goal.symm
    · have h_vi : (deformVec t x) i = x.val i := by
        have h_exists : ∃ (k : Fin n), i = k.succ := by
          refine' ⟨Fin.pred i hi, _⟩; exact (Fin.succ_pred i hi).symm
        rcases h_exists with ⟨k, rfl⟩
        exact deformVec_coordSucc t x k
      have h_vj : (deformVec t x) j = x.val j := by
        have h_exists : ∃ (k : Fin n), j = k.succ := by
          refine' ⟨Fin.pred j hj, _⟩; exact (Fin.succ_pred j hj).symm
        rcases h_exists with ⟨k, rfl⟩
        exact deformVec_coordSucc t x k
      have h_goal : (deformVec t x) i * (deformVec t x) j / deformNormSq t z =
          z.val (i, j) / deformNormSq t z := by
        rw [h_vi, h_vj, h_zval i j] <;> ring
      simpa [deformFun, hi, hj] using h_goal.symm
  rw [h_main]
  exact ⟨quotientMap n y, rfl⟩

/-- deformFun t z ≠ erp0 n for z ∈ V. -/
lemma deformFun_ne_erp0 (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    {z : EmbeddedRP n} (hz : z ≠ erp0 n) :
    (⟨deformFun t z, deformFun_mem_RPnEmbedded t ht hz⟩ : EmbeddedRP n) ≠ erp0 n := by
  have h_z00_le_one : z.val (0, 0) ≤ 1 := coord00_le_one z
  have h_z00_lt_one : z.val (0, 0) < 1 := by
    by_contra h4
    have h5 : z.val (0, 0) = 1 := by linarith [h_z00_le_one]
    exact hz ((coord00_eq_one_iff_erp0 z).mp h5)
  let s2 := deformNormSq t z
  have h_s2_pos : 0 < s2 := deformNormSq_pos t ht hz
  have h_deform00 : (deformFun t z) (0, 0) = (1 - t) ^ 2 * z.val (0, 0) / s2 := by
    simp [deformFun] <;> rfl
  by_cases h : z.val (0, 0) = 0
  · have h_prop : deformFun t z ∈ RPnEmbedded n := deformFun_mem_RPnEmbedded t ht hz
    let w : EmbeddedRP n := ⟨deformFun t z, h_prop⟩
    intro h_eq
    have h4 : w.val (0, 0) = 1 := (coord00_eq_one_iff_erp0 w).mpr h_eq
    have h5 : w.val (0, 0) = (deformFun t z) (0, 0) := by rfl
    rw [h5] at h4
    rw [h_deform00, h] at h4
    simp at h4 <;> norm_num at h4
  · have h_z00_pos : 0 < z.val (0, 0) := by
      have h1 := coord00_nonneg z
      exact lt_of_le_of_ne h1 (Ne.symm h)
    have h_deform00_lt_one : (deformFun t z) (0, 0) < 1 := by
      rw [h_deform00]
      have h5 : (1 - t) ^ 2 * z.val (0, 0) < s2 := by
        dsimp only [s2, deformNormSq]
        nlinarith [sq_nonneg (t * z.val (0, 0))]
      have h6 : (1 - t) ^ 2 * z.val (0, 0) / s2 < 1 := by
        apply (div_lt_one h_s2_pos).mpr
        exact h5
      exact h6
    have h_prop : deformFun t z ∈ RPnEmbedded n := deformFun_mem_RPnEmbedded t ht hz
    let w : EmbeddedRP n := ⟨deformFun t z, h_prop⟩
    intro h_eq
    have h7 : w.val (0, 0) = 1 := (coord00_eq_one_iff_erp0 w).mpr h_eq
    have h8 : w.val (0, 0) = (deformFun t z) (0, 0) := by rfl
    rw [h8] at h7
    linarith

/-- The deformation map on V. -/
def deformV (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (z : VType n) : VType n :=
  ⟨⟨deformFun t z.val, deformFun_mem_RPnEmbedded t ht z.prop⟩,
    deformFun_ne_erp0 t ht z.prop⟩

/-! ### Continuity -/

/-- Joint continuity of deformV in (t, z). -/
lemma continuous_deformV_joint :
    Continuous (fun (p : {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1} × VType n) =>
      deformV (p.1 : ℝ) p.1.prop p.2) := by
  let T := {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1}
  have h_e : Continuous (fun (p : T × VType n) => p.2.val.val) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)
  have h_t : Continuous (fun (p : T × VType n) => (p.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have h_pos : ∀ (p : T × VType n), 0 < deformNormSq (p.1 : ℝ) p.2.val :=
    fun p => deformNormSq_pos (p.1 : ℝ) p.1.prop p.2.prop
  have h_denom : Continuous (fun (p : T × VType n) => deformNormSq (p.1 : ℝ) p.2.val) := by
    have h1 : Continuous (fun (p : T × VType n) => p.2.val.val (0,0)) :=
      (EuclideanSpace.proj (0,0)).continuous.comp h_e
    have h_2mt : Continuous (fun (p : T × VType n) => 2 - (p.1 : ℝ)) :=
      continuous_const.sub h_t
    dsimp only [deformNormSq]
    exact continuous_const.sub ((h1.mul h_t).mul h_2mt)
  have h_coord : Continuous (fun (p : T × VType n) (q : Fin (n + 1) × Fin (n + 1)) =>
      (if q.1 = 0 then
        if q.2 = 0 then (1 - (p.1 : ℝ)) ^ 2 * p.2.val.val (0, 0) / deformNormSq (p.1 : ℝ) p.2.val
        else (1 - (p.1 : ℝ)) * p.2.val.val (0, q.2) / deformNormSq (p.1 : ℝ) p.2.val
      else
        if q.2 = 0 then (1 - (p.1 : ℝ)) * p.2.val.val (q.1, 0) / deformNormSq (p.1 : ℝ) p.2.val
        else p.2.val.val (q.1, q.2) / deformNormSq (p.1 : ℝ) p.2.val)) := by
    apply continuous_pi
    intro q
    have h_1mt : Continuous (fun (p : T × VType n) => 1 - (p.1 : ℝ)) :=
      continuous_const.sub h_t
    by_cases h1 : q.1 = 0
    · by_cases h2 : q.2 = 0
      · have h : Continuous (fun (p : T × VType n) =>
            (1 - (p.1 : ℝ)) ^ 2 * p.2.val.val (0, 0) / deformNormSq (p.1 : ℝ) p.2.val) :=
          Continuous.div (h_1mt.pow 2 |>.mul ((EuclideanSpace.proj (0,0)).continuous.comp h_e))
            h_denom (fun p => (h_pos p).ne')
        convert h using 1
        funext p
        simp [deformFun, deformNormSq, h1, h2] <;> rfl
      · have h : Continuous (fun (p : T × VType n) =>
            (1 - (p.1 : ℝ)) * p.2.val.val (0, q.2) / deformNormSq (p.1 : ℝ) p.2.val) :=
          Continuous.div (h_1mt.mul ((EuclideanSpace.proj (0, q.2)).continuous.comp h_e))
            h_denom (fun p => (h_pos p).ne')
        convert h using 1
        funext p
        simp [deformFun, deformNormSq, h1, h2] <;> rfl
    · by_cases h2 : q.2 = 0
      · have h : Continuous (fun (p : T × VType n) =>
            (1 - (p.1 : ℝ)) * p.2.val.val (q.1, 0) / deformNormSq (p.1 : ℝ) p.2.val) :=
          Continuous.div (h_1mt.mul ((EuclideanSpace.proj (q.1, 0)).continuous.comp h_e))
            h_denom (fun p => (h_pos p).ne')
        convert h using 1
        funext p
        simp [deformFun, deformNormSq, h1, h2] <;> rfl
      · have h : Continuous (fun (p : T × VType n) =>
            p.2.val.val (q.1, q.2) / deformNormSq (p.1 : ℝ) p.2.val) :=
          Continuous.div ((EuclideanSpace.proj (q.1, q.2)).continuous.comp h_e)
            h_denom (fun p => (h_pos p).ne')
        convert h using 1
        funext p
        simp [deformFun, deformNormSq, h1, h2] <;> rfl
  have h_toLp : Continuous (fun (f : (Fin (n + 1) × Fin (n + 1)) → ℝ) => WithLp.toLp 2 f) :=
    PiLp.continuous_toLp 2 fun _ => ℝ
  have h1 : Continuous (fun (p : T × VType n) => deformFun (p.1 : ℝ) p.2.val) :=
    h_toLp.comp h_coord
  have h2 : Continuous (fun (p : T × VType n) =>
      (⟨deformFun (p.1 : ℝ) p.2.val, deformFun_mem_RPnEmbedded (p.1 : ℝ) p.1.prop p.2.prop⟩ : EmbeddedRP n)) :=
    Continuous.subtype_mk h1 _
  exact Continuous.subtype_mk h2 _

/-- Continuity of deformV for fixed t. -/
lemma continuous_deformV {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Continuous (deformV (n := n) t ht) := by
  let T := {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1}
  let t' : T := ⟨t, ht⟩
  have h : Continuous (fun (z : VType n) => (t', z)) := by fun_prop
  exact continuous_deformV_joint.comp h

/-! ### Properties of the deformation -/

/-- H_0 = id. -/
lemma deformV_zero (z : VType n) :
    deformV 0 (by norm_num) z = z := by
  have h1 : deformFun 0 z.val = z.val := by
    ext ⟨i, j⟩
    dsimp only [deformFun, deformNormSq]
    by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp [hi, hj] <;> ring
  apply Subtype.ext
  apply Subtype.ext
  exact h1

/-- H_1 maps into RPnMinus1. -/
lemma deformV_one_in_RPnMinus1 (z : VType n) :
    (deformV 1 (by norm_num) z).val.val (0, 0) = 0 := by
  have h_main : (deformV 1 (by norm_num) z).val.val (0, 0) = (deformFun 1 z.val) (0, 0) := by rfl
  rw [h_main]
  dsimp only [deformFun, deformNormSq]
  have h_s2_pos : 0 < 1 - z.val.val (0, 0) := by
    have h : z.val.val (0, 0) < 1 := by
      have h_le : z.val.val (0, 0) ≤ 1 := coord00_le_one z.val
      by_contra h4
      have h5 : z.val.val (0, 0) = 1 := by linarith
      exact z.prop ((coord00_eq_one_iff_erp0 z.val).mp h5)
    linarith
  simp [h_s2_pos.ne'] <;> ring

/-- If z.val(0,0)=0 and z ∈ EmbeddedRP, then the entire 0th row/col are zero. -/
lemma rowcol_zero_of_coord00_zero {z : EmbeddedRP n} (h : z.val (0, 0) = 0) :
    (∀ j, z.val (0, j) = 0) ∧ (∀ i, z.val (i, 0) = 0) := by
  obtain ⟨rp, hrp⟩ := z.property
  let x : SphereType n := Quotient.out rp
  have h_eq1 : quotientMap n x = rp := Quotient.out_eq rp
  have h_zval : z.val = veroneseMap (quotientMap n x) := by
    rw [←hrp, h_eq1] <;> rfl
  have h_x0 : x.val 0 = 0 := by
    have h1 : z.val (0, 0) = (x.val 0) ^ 2 := by
      rw [h_zval]
      have h2 : veroneseMap (quotientMap n x) = veroneseFun x := by
        simp [veroneseMap, Quotient.lift_mk] <;> rfl
      rw [h2]
      have h3 := veroneseFun_apply x 0 0
      rw [h3] <;> ring
    have h4 : (x.val 0) ^ 2 = 0 := by rw [←h1, h]
    exact sq_eq_zero_iff.mp h4
  have h_row : ∀ j, z.val (0, j) = 0 := by
    intro j
    rw [h_zval]
    have h2 : veroneseMap (quotientMap n x) = veroneseFun x := by
      simp [veroneseMap, Quotient.lift_mk] <;> rfl
    rw [h2]
    have h3 := veroneseFun_apply x 0 j
    rw [h3, h_x0] <;> ring
  have h_col : ∀ i, z.val (i, 0) = 0 := by
    intro i
    rw [h_zval]
    have h2 : veroneseMap (quotientMap n x) = veroneseFun x := by
      simp [veroneseMap, Quotient.lift_mk] <;> rfl
    rw [h2]
    have h3 := veroneseFun_apply x i 0
    rw [h3, h_x0] <;> ring
  exact ⟨h_row, h_col⟩

/-- H_t fixes RPnMinus1. -/
lemma deformV_fixes_RPnMinus1 (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (z : VType n) (hz : z.val.val (0, 0) = 0) :
    deformV t ht z = z := by
  have h_rc := rowcol_zero_of_coord00_zero hz
  have h_row : ∀ j, z.val.val (0, j) = 0 := h_rc.1
  have h_col : ∀ i, z.val.val (i, 0) = 0 := h_rc.2
  have h1 : deformFun t z.val = z.val := by
    ext ⟨i, j⟩
    have h_s2 : deformNormSq t z.val = 1 := by
      dsimp only [deformNormSq]
      rw [hz] <;> ring
    dsimp only [deformFun]
    rw [h_s2]
    by_cases hi : i = 0 <;> by_cases hj : j = 0
    · subst hi hj; simp [h_row 0] <;> rfl
    · subst hi; simp [h_row j, hj] <;> rfl
    · subst hj; simp [h_col i, hi] <;> rfl
    · simp [hi, hj] <;> rfl
  apply Subtype.ext
  apply Subtype.ext
  exact h1

/-! ### Retraction and inclusion -/

/-- Retraction V → RPnMinus1. -/
def retractV (z : VType n) : RPnMinus1Type n :=
  let w := deformV 1 (by norm_num) z
  ⟨w.val, deformV_one_in_RPnMinus1 z⟩

/-- Inclusion RPnMinus1 → V. -/
def inclRPnMinus1 (z : RPnMinus1Type n) : VType n :=
  have h_ne : z.val ≠ erp0 n := by
    intro h
    have h4 : z.val.val (0, 0) = 1 := by
      rw [h]
      have h5 : (erp0 n).val (0, 0) = 1 := by
        have h6 : (erp0 n : EuclideanSpace ℝ (Fin (n + 1) × Fin (n + 1))) =
            veroneseMap (rp0 n) := by rfl
        rw [h6]
        have h7 : veroneseMap (rp0 n) (0, 0) = (e0 n).val 0 * (e0 n).val 0 :=
          veroneseFun_apply (e0 n) 0 0
        rw [h7, e0_coord0 n] <;> norm_num
      exact h5
    rw [z.prop] at h4 <;> norm_num at h4
  ⟨z.val, h_ne⟩

/-- retractV ∘ inclRPnMinus1 = id. -/
lemma retract_incl (z : RPnMinus1Type n) :
    retractV (inclRPnMinus1 z) = z := by
  let y : VType n := inclRPnMinus1 z
  have h1 : deformV 1 (by norm_num) y = y :=
    deformV_fixes_RPnMinus1 1 (by norm_num) y z.prop
  apply Subtype.ext
  have h2 : (retractV y).val = (deformV 1 (by norm_num) y).val := by rfl
  rw [h2, h1]
  <;> rfl

/-- inclRPnMinus1 ∘ retractV = deformV 1. -/
lemma incl_retract_eq_deformV1 (z : VType n) :
    inclRPnMinus1 (retractV z) = deformV 1 (by norm_num) z := by
  apply Subtype.ext
  rfl

/-! ### Homotopy equivalence -/

/-- The homotopy from incl∘retract to id via deformV(1-t). -/
noncomputable def deformHomotopy :
    ContinuousMap.Homotopy
      (ContinuousMap.mk (fun z : VType n => inclRPnMinus1 (retractV z))
        (by
          have h_eq : (fun z : VType n => inclRPnMinus1 (retractV z)) = deformV 1 (by norm_num) := by
            funext z; exact incl_retract_eq_deformV1 z
          rw [h_eq]
          exact continuous_deformV (ht := by norm_num)))
      (ContinuousMap.mk (fun z : VType n => z) continuous_id) :=
  let T := {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1}
  { toFun := fun (p : ↥unitInterval × (VType n)) =>
      let s : ℝ := 1 - (p.1 : ℝ)
      have hs : s ∈ Set.Icc (0 : ℝ) 1 := by
        have h₁ : (0 : ℝ) ≤ (p.1 : ℝ) := p.1.prop.1
        have h₂ : (p.1 : ℝ) ≤ 1 := p.1.prop.2
        exact ⟨by linarith, by linarith⟩
      deformV s hs p.2
    continuous_toFun := by
      let g : (↥unitInterval × VType n) → (T × VType n) := fun p =>
        (⟨1 - (p.1 : ℝ), by
          have h₁ : (0 : ℝ) ≤ (p.1 : ℝ) := p.1.prop.1
          have h₂ : (p.1 : ℝ) ≤ 1 := p.1.prop.2
          exact ⟨by linarith, by linarith⟩⟩, p.2)
      have hg : Continuous g := by fun_prop
      exact continuous_deformV_joint.comp hg
    map_zero_left := by
      intro z
      simpa [incl_retract_eq_deformV1] using rfl
    map_one_left := by
      intro z
      simpa [deformV_zero] using rfl }

/-- V ≃ₕ RPnMinus1. -/
noncomputable def V_homotopyEquiv_RPnMinus1 (n : ℕ) :
    ContinuousMap.HomotopyEquiv (VType n) (RPnMinus1Type n) :=
  { toFun := ContinuousMap.mk retractV (by
      have h1 : Continuous (fun z : VType n => (deformV 1 (by norm_num) z).val) :=
        continuous_subtype_val.comp (continuous_deformV (ht := by norm_num))
      exact Continuous.subtype_mk h1 _)
    invFun := ContinuousMap.mk inclRPnMinus1 (by
      exact Continuous.subtype_mk continuous_subtype_val _)
    left_inv := ⟨deformHomotopy⟩
    right_inv := by
      have h_cont_retract : Continuous (retractV (n := n)) := by
        have h1 : Continuous (fun z : VType n => (deformV 1 (by norm_num) z).val) :=
          continuous_subtype_val.comp (continuous_deformV (ht := by norm_num))
        exact Continuous.subtype_mk h1 _
      have h_main : ∀ (h : ContinuousMap (RPnMinus1Type n) (RPnMinus1Type n)),
          h = ContinuousMap.id (RPnMinus1Type n) → h.Homotopic (ContinuousMap.id (RPnMinus1Type n)) := by
        intro h hh
        subst hh
        exact ⟨ContinuousMap.Homotopy.refl _⟩
      have h_cont_incl : Continuous (inclRPnMinus1 (n := n)) :=
        Continuous.subtype_mk continuous_subtype_val _
      exact h_main (ContinuousMap.mk (retractV ∘ inclRPnMinus1) (h_cont_retract.comp h_cont_incl)) (by
        apply ContinuousMap.ext
        intro x
        exact retract_incl x) }

/-! ### Bridge: RPnMinus1Type (m+1) ≃ₜ EmbeddedRP m -/

variable {m : ℕ}

/-- Drop the 0th row and column. -/
private def dropZeroRowCol (z : EuclideanSpace ℝ (Fin (m + 2) × Fin (m + 2))) :
    EuclideanSpace ℝ (Fin (m + 1) × Fin (m + 1)) :=
  WithLp.toLp 2 fun (p : Fin (m + 1) × Fin (m + 1)) =>
    z (p.1.succ, p.2.succ)

/-- Add a 0th row and column of zeros. -/
private def addZeroRowCol (w : EuclideanSpace ℝ (Fin (m + 1) × Fin (m + 1))) :
    EuclideanSpace ℝ (Fin (m + 2) × Fin (m + 2)) :=
  WithLp.toLp 2 fun (p : Fin (m + 2) × Fin (m + 2)) =>
    if h1 : p.1 = 0 then 0
    else if h2 : p.2 = 0 then 0
    else w (Fin.pred p.1 h1, Fin.pred p.2 h2)

private lemma dropZeroRowCol_addZeroRowCol (w : EuclideanSpace ℝ (Fin (m + 1) × Fin (m + 1))) :
    dropZeroRowCol (addZeroRowCol w) = w := by
  ext ⟨i, j⟩
  simp [dropZeroRowCol, addZeroRowCol, Fin.succ_ne_zero] <;> rfl

private lemma continuous_dropZeroRowCol : Continuous (dropZeroRowCol (m := m)) := by
  have h : Continuous (fun (w : EuclideanSpace ℝ (Fin (m + 2) × Fin (m + 2)))
      (p : Fin (m + 1) × Fin (m + 1)) => w (p.1.succ, p.2.succ)) := by
    apply continuous_pi
    intro p
    exact (EuclideanSpace.proj (p.1.succ, p.2.succ)).continuous
  exact (PiLp.continuous_toLp 2 (fun _ => ℝ)).comp h

private lemma continuous_addZeroRowCol : Continuous (addZeroRowCol (m := m)) := by
  have h : Continuous (fun (w : EuclideanSpace ℝ (Fin (m + 1) × Fin (m + 1)))
      (p : Fin (m + 2) × Fin (m + 2)) =>
      if h1 : p.1 = 0 then 0
      else if h2 : p.2 = 0 then 0
      else w (Fin.pred p.1 h1, Fin.pred p.2 h2)) := by
    apply continuous_pi
    intro p
    by_cases h1 : p.1 = 0
    · have h_eq : (fun (w : EuclideanSpace ℝ (Fin (m + 1) × Fin (m + 1))) =>
          (if h1' : p.1 = 0 then (0 : ℝ)
           else if h2' : p.2 = 0 then (0 : ℝ)
           else w (Fin.pred p.1 h1', Fin.pred p.2 h2'))) = (fun _ => (0 : ℝ)) := by
        funext w; rw [dif_pos h1]
      rw [h_eq]; exact continuous_const
    · by_cases h2 : p.2 = 0
      · have h_eq : (fun (w : EuclideanSpace ℝ (Fin (m + 1) × Fin (m + 1))) =>
            (if h1' : p.1 = 0 then (0 : ℝ)
             else if h2' : p.2 = 0 then (0 : ℝ)
             else w (Fin.pred p.1 h1', Fin.pred p.2 h2'))) = (fun _ => (0 : ℝ)) := by
          funext w; rw [dif_neg h1, dif_pos h2]
        rw [h_eq]; exact continuous_const
      · have h_eq : (fun (w : EuclideanSpace ℝ (Fin (m + 1) × Fin (m + 1))) =>
            (if h1' : p.1 = 0 then (0 : ℝ)
             else if h2' : p.2 = 0 then (0 : ℝ)
             else w (Fin.pred p.1 h1', Fin.pred p.2 h2'))) =
            (fun w => w (Fin.pred p.1 h1, Fin.pred p.2 h2)) := by
          funext w; rw [dif_neg h1, dif_neg h2]
        rw [h_eq]
        exact (EuclideanSpace.proj (Fin.pred p.1 h1, Fin.pred p.2 h2)).continuous
  exact (PiLp.continuous_toLp 2 (fun _ => ℝ)).comp h

/-- Prepend a zero coordinate: S^m → S^{m+1}. -/
private def spherePrependZero (y : SphereType m) : SphereType (m + 1) :=
  let v : EuclideanSpace ℝ (Fin (m + 2)) :=
    WithLp.toLp 2 fun j : Fin (m + 2) =>
      if h : j = 0 then 0 else y.val (Fin.pred j h)
  have h_norm : ‖v‖ = 1 := by
    have h1 : ‖v‖ ^ 2 = ∑ j : Fin (m + 2), (v j) ^ 2 :=
      EuclideanSpace.real_norm_sq_eq v
    have h2 : v 0 = 0 := by simp [v] <;> rfl
    have h3 : ∑ i : Fin (m + 1), (v i.succ) ^ 2 = ∑ i : Fin (m + 1), (y.val i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      have h4 : v i.succ = y.val i := by
        simp [v, Fin.succ_ne_zero] <;> rfl
      rw [h4]
    have h4 : ‖y.val‖ ^ 2 = 1 := by
      have h5 : ‖y.val‖ = 1 := mem_sphere_zero_iff_norm.mp y.property
      rw [h5] <;> norm_num
    have h6 : ‖y.val‖ ^ 2 = ∑ i : Fin (m + 1), (y.val i) ^ 2 :=
      EuclideanSpace.real_norm_sq_eq y.val
    have h7 : ‖v‖ ^ 2 = 1 := by
      calc ‖v‖ ^ 2
        = (v 0) ^ 2 + ∑ i : Fin (m + 1), (v i.succ) ^ 2 := by rw [h1, Fin.sum_univ_succ] <;> rfl
      _ = 0 ^ 2 + ∑ i : Fin (m + 1), (v i.succ) ^ 2 := by rw [h2]
      _ = ∑ i : Fin (m + 1), (v i.succ) ^ 2 := by ring
      _ = ∑ i : Fin (m + 1), (y.val i) ^ 2 := h3
      _ = ‖y.val‖ ^ 2 := h6.symm
      _ = 1 := h4
    have h8 : 0 ≤ ‖v‖ := norm_nonneg v
    nlinarith
  ⟨v, mem_sphere_zero_iff_norm.mpr h_norm⟩

private lemma spherePrependZero_coord0 (y : SphereType m) :
    (spherePrependZero y).val 0 = 0 := by
  simp [spherePrependZero] <;> rfl

private lemma spherePrependZero_coordSucc (y : SphereType m) (i : Fin (m + 1)) :
    (spherePrependZero y).val i.succ = y.val i := by
  simp [spherePrependZero, Fin.succ_ne_zero] <;> rfl

/-- If x ∈ S^{m+1} has x_0 = 0, drop first coordinate. -/
private def sphereDropFirst (x : SphereType (m + 1)) (h0 : x.val 0 = 0) : SphereType m :=
  let v : EuclideanSpace ℝ (Fin (m + 1)) :=
    WithLp.toLp 2 fun i : Fin (m + 1) => x.val i.succ
  have h_norm : ‖v‖ = 1 := by
    have h1 : ‖v‖ ^ 2 = ∑ i : Fin (m + 1), (v i) ^ 2 :=
      EuclideanSpace.real_norm_sq_eq v
    have h2 : ∑ i : Fin (m + 1), (v i) ^ 2 = ∑ i : Fin (m + 1), (x.val i.succ) ^ 2 := by
      apply Finset.sum_congr rfl; intro i _; rfl
    have h3 : ‖x.val‖ ^ 2 = (x.val 0) ^ 2 + ∑ i : Fin (m + 1), (x.val i.succ) ^ 2 := by
      have h4 : ‖x.val‖ ^ 2 = ∑ j : Fin (m + 2), (x.val j) ^ 2 :=
        EuclideanSpace.real_norm_sq_eq x.val
      rw [h4, Fin.sum_univ_succ] <;> rfl
    have h5 : ‖x.val‖ ^ 2 = 1 := by
      have h6 : ‖x.val‖ = 1 := mem_sphere_zero_iff_norm.mp x.property
      rw [h6] <;> norm_num
    have h7 : ‖v‖ ^ 2 = 1 := by
      calc ‖v‖ ^ 2
        = ∑ i : Fin (m + 1), (v i) ^ 2 := h1
      _ = ∑ i : Fin (m + 1), (x.val i.succ) ^ 2 := h2
      _ = ‖x.val‖ ^ 2 - (x.val 0) ^ 2 := by
        have h_sum : ‖x.val‖ ^ 2 = (x.val 0) ^ 2 + ∑ i : Fin (m + 1), (x.val i.succ) ^ 2 := by
          have h4 : ‖x.val‖ ^ 2 = ∑ j : Fin (m + 2), (x.val j) ^ 2 :=
            EuclideanSpace.real_norm_sq_eq x.val
          rw [h4, Fin.sum_univ_succ] <;> rfl
        linarith
      _ = 1 := by rw [h5, h0] <;> ring
    have h8 : 0 ≤ ‖v‖ := norm_nonneg v
    nlinarith
  ⟨v, mem_sphere_zero_iff_norm.mpr h_norm⟩

private lemma sphereDropFirst_coord (x : SphereType (m + 1)) (h0 : x.val 0 = 0) (i : Fin (m + 1)) :
    (sphereDropFirst x h0).val i = x.val i.succ := by
  simp [sphereDropFirst] <;> rfl

private lemma sphereDropFirst_prependZero (y : SphereType m) :
    sphereDropFirst (spherePrependZero y) (spherePrependZero_coord0 y) = y := by
  apply Subtype.ext; ext i
  rw [sphereDropFirst_coord, spherePrependZero_coordSucc]

private lemma spherePrependZero_dropFirst (x : SphereType (m + 1)) (h0 : x.val 0 = 0) :
    spherePrependZero (sphereDropFirst x h0) = x := by
  apply Subtype.ext; ext j
  by_cases hj : j = 0
  · subst hj; rw [spherePrependZero_coord0, h0]
  · have h_exists : ∃ (i : Fin (m + 1)), j = i.succ := by
      refine' ⟨Fin.pred j hj, _⟩; exact (Fin.succ_pred j hj).symm
    rcases h_exists with ⟨i, rfl⟩
    rw [spherePrependZero_coordSucc, sphereDropFirst_coord]

private lemma veroneseDropZero (x : SphereType (m + 1)) (h0 : x.val 0 = 0) :
    dropZeroRowCol (veroneseFun x) = veroneseFun (sphereDropFirst x h0) := by
  ext ⟨i, j⟩
  simp [dropZeroRowCol, veroneseFun_apply, sphereDropFirst_coord] <;> ring

private lemma veroneseAddZero (y : SphereType m) :
    addZeroRowCol (veroneseFun y) = veroneseFun (spherePrependZero y) := by
  ext ⟨i, j⟩
  by_cases hi : i = 0
  · subst hi
    have h : (veroneseFun (spherePrependZero y)) (0, j) = 0 := by
      rw [veroneseFun_apply, spherePrependZero_coord0] <;> ring
    simp [addZeroRowCol, h]
  · by_cases hj : j = 0
    · subst hj
      have h : (veroneseFun (spherePrependZero y)) (i, 0) = 0 := by
        rw [veroneseFun_apply, spherePrependZero_coord0] <;> ring
      simp [addZeroRowCol, hi, h]
    · have h9 : (Fin.pred i hi).succ = i := Fin.succ_pred i hi
      have h_i : (spherePrependZero y).val i = y.val (Fin.pred i hi) := by
        have h_tmp := spherePrependZero_coordSucc y (Fin.pred i hi)
        rw [h9] at h_tmp
        exact h_tmp
      have h10 : (Fin.pred j hj).succ = j := Fin.succ_pred j hj
      have h_j : (spherePrependZero y).val j = y.val (Fin.pred j hj) := by
        have h_tmp2 := spherePrependZero_coordSucc y (Fin.pred j hj)
        rw [h10] at h_tmp2
        exact h_tmp2
      have h_goal : (addZeroRowCol (veroneseFun y)) (i, j) =
            (veroneseFun (spherePrependZero y)) (i, j) := by
        simp [addZeroRowCol, veroneseFun_apply, hi, hj, h_i, h_j] <;> ring
      exact h_goal

variable {k : ℕ}

/-- Get sphere representative from EmbeddedRP. -/
private def getSphereRep (z : EmbeddedRP k) : SphereType k :=
  Quotient.out ((veroneseEquiv k).symm z)

private lemma embedded_val_eq_veroneseFun (z : EmbeddedRP k) :
    z.val = veroneseFun (getSphereRep z) := by
  let x := getSphereRep z
  let rp := (veroneseEquiv k).symm z
  have h_eq1 : quotientMap k x = rp := Quotient.out_eq rp
  have h_z_eq : z = veroneseEquiv k rp := (veroneseEquiv k).right_inv z |>.symm
  have h : z.val = veroneseMap (quotientMap k x) := by
    rw [h_z_eq, h_eq1] <;> rfl
  rw [h]
  have h2 : veroneseMap (quotientMap k x) = veroneseFun x := by
    simp [veroneseMap, Quotient.lift_mk] <;> rfl
  rw [h2]

/-- Forward map: RPnMinus1Type (m+1) → EmbeddedRP m. -/
private def rpMinus1ToEmbedded (z : RPnMinus1Type (m + 1)) : EmbeddedRP m :=
  let x : SphereType (m + 1) := getSphereRep z.val
  have h_x0 : x.val 0 = 0 := by
    have h1 : z.val.val (0, 0) = (x.val 0) ^ 2 := by
      rw [embedded_val_eq_veroneseFun z.val]
      have h2 := veroneseFun_apply x 0 0
      rw [h2] <;> ring
    have h3 : (x.val 0) ^ 2 = 0 := by rw [←h1, z.prop]
    exact sq_eq_zero_iff.mp h3
  let y := sphereDropFirst x h_x0
  have h5 : dropZeroRowCol z.val.val = veroneseFun y := by
    have h6 : z.val.val = veroneseFun x := embedded_val_eq_veroneseFun z.val
    rw [h6]
    exact veroneseDropZero x h_x0
  ⟨dropZeroRowCol z.val.val, by rw [h5]; exact ⟨quotientMap m y, rfl⟩⟩

/-- Backward map: EmbeddedRP m → RPnMinus1Type (m+1). -/
private def embeddedToRPMinus1 (w : EmbeddedRP m) : RPnMinus1Type (m + 1) :=
  let y : SphereType m := getSphereRep w
  let x := spherePrependZero y
  have h5 : addZeroRowCol w.val = veroneseFun x := by
    have h6 : w.val = veroneseFun y := embedded_val_eq_veroneseFun w
    rw [h6]
    exact veroneseAddZero y
  have hz : addZeroRowCol w.val ∈ RPnEmbedded (m + 1) := by
    rw [h5]
    exact ⟨quotientMap (m + 1) x, rfl⟩
  have h00 : (⟨addZeroRowCol w.val, hz⟩ : EmbeddedRP (m + 1)).val (0, 0) = 0 := by
    simp [addZeroRowCol] <;> rfl
  ⟨⟨addZeroRowCol w.val, hz⟩, h00⟩

private lemma rpMinus1ToEmbedded_left_inv (z : RPnMinus1Type (m + 1)) :
    embeddedToRPMinus1 (rpMinus1ToEmbedded z) = z := by
  apply Subtype.ext
  apply Subtype.ext
  let x : SphereType (m + 1) := getSphereRep z.val
  have h_x0 : x.val 0 = 0 := by
    have h1 : z.val.val (0, 0) = (x.val 0) ^ 2 := by
      rw [embedded_val_eq_veroneseFun z.val]
      have h2 := veroneseFun_apply x 0 0
      rw [h2] <;> ring
    have h3 : (x.val 0) ^ 2 = 0 := by rw [←h1, z.prop]
    exact sq_eq_zero_iff.mp h3
  have h_zval2 : z.val.val = veroneseFun x := embedded_val_eq_veroneseFun z.val
  have h_main : addZeroRowCol (dropZeroRowCol z.val.val) = z.val.val := by
    have h_zval2 : z.val.val = veroneseFun x := embedded_val_eq_veroneseFun z.val
    have h4 : addZeroRowCol (dropZeroRowCol (veroneseFun x)) = veroneseFun x := by
      rw [veroneseDropZero x h_x0, veroneseAddZero (sphereDropFirst x h_x0)]
      rw [spherePrependZero_dropFirst x h_x0]
    rw [h_zval2] at *
    <;> tauto
  exact h_main

private lemma rpMinus1ToEmbedded_right_inv (w : EmbeddedRP m) :
    rpMinus1ToEmbedded (embeddedToRPMinus1 w) = w := by
  apply Subtype.ext
  dsimp only [rpMinus1ToEmbedded, embeddedToRPMinus1]
  exact dropZeroRowCol_addZeroRowCol w.val

/-- Homeomorphism RPnMinus1Type (m+1) ≃ₜ EmbeddedRP m. -/
noncomputable def RPnMinus1EquivEmbeddedRP (m : ℕ) :
    RPnMinus1Type (m + 1) ≃ₜ EmbeddedRP m :=
  have h_cont1 : Continuous (rpMinus1ToEmbedded (m := m)) := by
    have h : Continuous (fun (z : RPnMinus1Type (m + 1)) =>
        dropZeroRowCol z.val.val) :=
      continuous_dropZeroRowCol.comp (continuous_subtype_val.comp continuous_subtype_val)
    exact Continuous.subtype_mk h _
  have h_cont2 : Continuous (embeddedToRPMinus1 (m := m)) := by
    have h_eq : (fun (w : EmbeddedRP m) => (embeddedToRPMinus1 w).val.val) =
        (fun (w : EmbeddedRP m) => addZeroRowCol w.val) := by
      funext w; rfl
    have h_val : Continuous (fun (w : EmbeddedRP m) => (embeddedToRPMinus1 w).val.val) := by
      rw [h_eq]
      exact continuous_addZeroRowCol.comp continuous_subtype_val
    have h_emb : Continuous (fun (w : EmbeddedRP m) => (embeddedToRPMinus1 w).val) :=
      Continuous.subtype_mk h_val _
    exact Continuous.subtype_mk h_emb _
  { toFun := rpMinus1ToEmbedded
    invFun := embeddedToRPMinus1
    left_inv := rpMinus1ToEmbedded_left_inv
    right_inv := rpMinus1ToEmbedded_right_inv
    continuous_toFun := h_cont1
    continuous_invFun := h_cont2 }

/-! ### Final: vHomotopyEquiv -/

/-- V = RP^{m+1} \\ {rp0} deformation retracts onto RP^m. -/
noncomputable def vHomotopyEquiv (m : ℕ) :
    ContinuousMap.HomotopyEquiv
      (TwoSubspaces.twoSubspacesOfOpens (U (m + 1)) (V (m + 1))).V
      (EmbeddedRP m) := by
  let e1 : (TwoSubspaces.twoSubspacesOfOpens (U (m + 1)) (V (m + 1))).V ≃ₜ VType (m + 1) :=
    { toFun := fun x => ⟨x.val, x.prop⟩
      invFun := fun y => ⟨y.val, y.prop⟩
      left_inv := by intro x; apply Subtype.ext; rfl
      right_inv := by intro y; apply Subtype.ext; rfl
      continuous_toFun := Continuous.subtype_mk continuous_subtype_val (by intro x; exact x.prop)
      continuous_invFun := Continuous.subtype_mk continuous_subtype_val (by intro y; exact y.prop) }
  let e2 : ContinuousMap.HomotopyEquiv (VType (m + 1)) (RPnMinus1Type (m + 1)) :=
    V_homotopyEquiv_RPnMinus1 (m + 1)
  let e3 : RPnMinus1Type (m + 1) ≃ₜ EmbeddedRP m := RPnMinus1EquivEmbeddedRP m
  exact e1.toHomotopyEquiv.trans e2 |>.trans e3.toHomotopyEquiv

end BorsukUlam.RealProjective.Cover

end
