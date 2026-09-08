/-
# RP^n Affine Cover for Mayer-Vietoris

Constructs the open cover of RP^n:
- U = {[x] | x_0 ≠ 0} ≅ R^n (contractible)
- V = RP^n \ {[e_0]} ≃ RP^{n-1}
- U ∩ V ≃ S^{n-1}

Uses the Veronese-embedded RP^n as a metric space.

## Whiteprint Node
- rp_affine_cover
-/

import MyLeanRepo.Kakeya.BorsukUlam.RealProjective.MetricEmbedding
import MyLeanRepo.Kakeya.BorsukUlam.BackupRoute.RealProjectiveSpace
import MyLeanRepo.Kakeya.BorsukUlam.SeedMathlib.AlgebraicTopology.SingularHomology.EuclideanSpace.StdSphereHomology
import Mathlib.Tactic

noncomputable section

open BorsukUlam.BackupRoute
open BorsukUlam.RealProjective
open AlgebraicTopology CategoryTheory Limits HomologicalComplex
open AlgebraicTopology.StdSphereHomology

namespace BorsukUlam.RealProjective.Cover

variable {n : ℕ}

abbrev EmbeddedRP (n : ℕ) : Type :=
  {z : EuclideanSpace ℝ (Fin (n + 1) × Fin (n + 1)) // z ∈ RPnEmbedded n}

/-- e_0 = (1,0,...,0) on S^n. -/
def e0 (n : ℕ) : SphereType n :=
  let v : EuclideanSpace ℝ (Fin (n + 1)) :=
    EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ)
  have hv : ‖v‖ = 1 := by
    have h1 : ‖v‖ = ‖(1 : ℝ)‖ :=
      PiLp.norm_single 2 (fun _ : Fin (n + 1) => ℝ) (0 : Fin (n + 1)) (1 : ℝ)
    rw [h1] <;> simp
  ⟨v, mem_sphere_zero_iff_norm.mpr hv⟩

/-- Coordinate 0 of e0 is 1. -/
lemma e0_coord0 (n : ℕ) : (e0 n).val 0 = 1 := by
  simp [e0, EuclideanSpace.single]

/-- rp0 = [e_0] in RP^n. -/
def rp0 (n : ℕ) : RPType n := quotientMap n (e0 n)

/-- The embedded point rp0. -/
def erp0 (n : ℕ) : EmbeddedRP n :=
  veroneseEquiv n (rp0 n)

/-!
## U = {[x] | x_0 ≠ 0}

In Veronese coordinates, x_0 ≠ 0 iff z_{00} > 0.
-/

/-- U = {z | z_{00} > 0}. -/
def U (n : ℕ) : Set (EmbeddedRP n) :=
  {z | (z : EuclideanSpace ℝ (Fin (n + 1) × Fin (n + 1))) (0, 0) > 0}

lemma U_open (n : ℕ) : IsOpen (U n) := by
  let proj : (EmbeddedRP n) → ℝ := fun z =>
    (z : EuclideanSpace ℝ (Fin (n + 1) × Fin (n + 1))) (0, 0)
  have h_cont : Continuous proj := by
    have h1 : Continuous (fun (w : EuclideanSpace ℝ (Fin (n + 1) × Fin (n + 1))) => w (0, 0)) := by
      exact (EuclideanSpace.proj (0, 0)).continuous
    exact h1.comp continuous_subtype_val
  exact isOpen_lt continuous_const h_cont

/-- All points in EmbeddedRP have z_{00} ≥ 0. -/
lemma coord00_nonneg (z : EmbeddedRP n) :
    0 ≤ (z : EuclideanSpace ℝ (Fin (n + 1) × Fin (n + 1))) (0, 0) := by
  obtain ⟨x, hx⟩ := z.property
  let y := Quotient.out x
  have h_eq1 : (Quotient.mk (antipodalSetoid (n := n)) y) = x := Quotient.out_eq x
  have h_eq2 : veroneseMap x = veroneseFun y := by
    have h3 : veroneseMap (Quotient.mk (antipodalSetoid (n := n)) y) = veroneseFun y := by
      simp [veroneseMap, Quotient.lift_mk]
      <;> rfl
    rw [←h_eq1]
    exact h3
  have h_main : (z : EuclideanSpace ℝ (Fin (n + 1) × Fin (n + 1))) (0, 0) =
      (veroneseFun y) (0, 0) := by
    rw [←hx, h_eq2]
  rw [h_main]
  have h : (veroneseFun y) (0, 0) = y.val 0 * y.val 0 := veroneseFun_apply y 0 0
  rw [h]
  have h2 : y.val 0 * y.val 0 = (y.val 0) ^ 2 := by ring
  rw [h2]
  exact sq_nonneg (y.val 0)

/-- z_{00} ≤ 1 for any z ∈ EmbeddedRP n. -/
lemma coord00_le_one (z : EmbeddedRP n) :
    (z : EuclideanSpace ℝ (Fin (n + 1) × Fin (n + 1))) (0, 0) ≤ 1 := by
  obtain ⟨x, hx⟩ := z.property
  let y := Quotient.out x
  have h_eq1 : (Quotient.mk (antipodalSetoid (n := n)) y) = x := Quotient.out_eq x
  have h_eq2 : veroneseMap x = veroneseFun y := by
    have h3 : veroneseMap (Quotient.mk (antipodalSetoid (n := n)) y) = veroneseFun y := by
      simp [veroneseMap, Quotient.lift_mk] <;> rfl
    rw [←h_eq1]; exact h3
  have h_main : (z : EuclideanSpace ℝ (Fin (n + 1) × Fin (n + 1))) (0, 0) =
      (veroneseFun y) (0, 0) := by
    rw [←hx, h_eq2]
  rw [h_main]
  have h : (veroneseFun y) (0, 0) = (y.val 0) ^ 2 := by
    have h2 := veroneseFun_apply y 0 0
    rw [h2] <;> ring
  rw [h]
  have h_ynorm : ‖y.val‖ ^ 2 = 1 := by
    have h7 : ‖y.val‖ = 1 := mem_sphere_zero_iff_norm.mp y.property
    rw [h7] <;> norm_num
  have h9 : ‖y.val‖ ^ 2 = ∑ j : Fin (n + 1), (y.val j) ^ 2 :=
    EuclideanSpace.real_norm_sq_eq y.val
  have h10 : (y.val 0) ^ 2 ≤ ∑ j : Fin (n + 1), (y.val j) ^ 2 := by
    have h_nonneg : ∀ i ∈ (Finset.univ : Finset (Fin (n + 1))), 0 ≤ (y.val i) ^ 2 :=
      fun i _ => sq_nonneg _
    exact Finset.single_le_sum h_nonneg (Finset.mem_univ (0 : Fin (n + 1)))
  have h11 : (y.val 0) ^ 2 ≤ ‖y.val‖ ^ 2 := by
    have h12 : ∑ j : Fin (n + 1), (y.val j) ^ 2 = ‖y.val‖ ^ 2 := h9.symm
    rw [h12] at h10
    exact h10
  rw [h_ynorm] at h11
  exact h11

/-- z_{00} = 1 iff z = erp0. -/
lemma coord00_eq_one_iff_erp0 (z : EmbeddedRP n) :
    z.val (0, 0) = 1 ↔ z = erp0 n := by
  constructor
  · intro h
    obtain ⟨rp, hrp⟩ := z.property
    let x : SphereType n := Quotient.out rp
    have h_eq1 : quotientMap n x = rp := Quotient.out_eq rp
    have h_zval : z.val = veroneseMap rp := by rw [←hrp]
    have h10 : veroneseMap (quotientMap n x) = veroneseFun x := by
      simp [veroneseMap, Quotient.lift_mk] <;> rfl
    have h_x00 : z.val (0, 0) = (x.val 0) ^ 2 := by
      have h11 : z.val = veroneseMap (quotientMap n x) := by
        rw [h_zval, h_eq1]
      rw [h11, h10]
      have h13 : veroneseFun x (0, 0) = x.val 0 * x.val 0 := veroneseFun_apply x 0 0
      rw [h13] <;> ring
    have h_x0sq : (x.val 0) ^ 2 = 1 := by
      rw [←h_x00, h]
    have h_ynorm : ‖x.val‖ ^ 2 = 1 := by
      have h7 : ‖x.val‖ = 1 := mem_sphere_zero_iff_norm.mp x.property
      rw [h7] <;> norm_num
    have h_sum : ‖x.val‖ ^ 2 = (x.val 0) ^ 2 + ∑ j : Fin n, (x.val (j.succ)) ^ 2 := by
      have h9 : ‖x.val‖ ^ 2 = ∑ j : Fin (n + 1), (x.val j) ^ 2 :=
        EuclideanSpace.real_norm_sq_eq x.val
      rw [h9, Fin.sum_univ_succ] <;> rfl
    have h11 : ∑ j : Fin n, (x.val (j.succ)) ^ 2 = 0 := by
      linarith [h_ynorm, h_sum, h_x0sq]
    have h_ysucc : ∀ (i : Fin n), x.val (Fin.succ i) = 0 := by
      intro i
      have h15 : (x.val (Fin.succ i)) ^ 2 ≤ ∑ j : Fin n, (x.val (j.succ)) ^ 2 :=
        Finset.single_le_sum (fun j _ => sq_nonneg (x.val (j.succ))) (Finset.mem_univ i)
      have h16 : (x.val (Fin.succ i)) ^ 2 ≤ 0 := by
        rw [h11] at h15
        exact h15
      have h17 : (x.val (Fin.succ i)) ^ 2 = 0 := by
        have h18 : 0 ≤ (x.val (Fin.succ i)) ^ 2 := sq_nonneg _
        linarith
      have h19 : x.val (Fin.succ i) = 0 := by
        simpa [pow_two] using h17
      exact h19
    have h_x0 : x.val 0 = 1 ∨ x.val 0 = -1 := by
      have h5 : (x.val 0 - 1) * (x.val 0 + 1) = 0 := by linarith
      have h7 : x.val 0 - 1 = 0 ∨ x.val 0 + 1 = 0 := eq_zero_or_eq_zero_of_mul_eq_zero h5
      rcases h7 with (h7 | h7)
      · left; linarith
      · right; linarith
    have h_x_eq : x = e0 n ∨ x = antipodal n (e0 n) := by
      rcases h_x0 with (h_x0 | h_x0)
      · left
        apply Subtype.ext
        ext j
        by_cases h : j = 0
        · subst h
          have h_e0 : (e0 n).val 0 = 1 := e0_coord0 n
          rw [h_x0, h_e0]
        · have h_exists : ∃ (i : Fin n), j = i.succ := by
            refine' ⟨Fin.pred j h, _⟩
            exact (Fin.succ_pred j h).symm
          rcases h_exists with ⟨i, rfl⟩
          exact h_ysucc i
      · right
        apply Subtype.ext
        ext j
        by_cases h : j = 0
        · subst h
          have h1 : (antipodal n (e0 n)).val 0 = - (e0 n).val 0 := by rfl
          have h2 : (e0 n).val 0 = 1 := e0_coord0 n
          have h3 : (antipodal n (e0 n)).val 0 = -1 := by
            rw [h1, h2] <;> norm_num
          rw [h3, h_x0]
        · have h_exists : ∃ (i : Fin n), j = i.succ := by
            refine' ⟨Fin.pred j h, _⟩
            exact (Fin.succ_pred j h).symm
          rcases h_exists with ⟨i, rfl⟩
          have h1 : (antipodal n (e0 n)).val i.succ = - (e0 n).val i.succ := by rfl
          have h2 : (e0 n).val i.succ = 0 := by
            simp [e0, EuclideanSpace.single, Ne.symm (Fin.succ_ne_zero i)]
            <;> tauto
          rw [h1, h2, h_ysucc i] <;> ring
    rcases h_x_eq with (h_x_eq | h_x_eq)
    · have h_rp : rp = rp0 n := by
        rw [←h_eq1, h_x_eq] <;> rfl
      apply Subtype.ext
      have h9 : z.val = veroneseMap rp := by rw [←hrp]
      rw [h9, h_rp] <;> rfl
    · have h_rp : rp = rp0 n := by
        rw [←h_eq1, h_x_eq]
        exact Quotient.sound (Or.inr rfl)
      apply Subtype.ext
      have h9 : z.val = veroneseMap rp := by rw [←hrp]
      rw [h9, h_rp] <;> rfl
  · intro h
    rw [h]
    have h4 : (erp0 n : EuclideanSpace ℝ (Fin (n + 1) × Fin (n + 1))) (0, 0) = 1 := by
      have h5 : (erp0 n : EuclideanSpace ℝ (Fin (n + 1) × Fin (n + 1))) =
          veroneseMap (rp0 n) := by rfl
      rw [h5]
      have h6 : veroneseMap (rp0 n) (0, 0) = (e0 n).val 0 * (e0 n).val 0 :=
        veroneseFun_apply (e0 n) 0 0
      rw [h6, e0_coord0 n] <;> norm_num
    exact h4

/-- V = EmbeddedRP n \ {erp0 n}. -/
def V (n : ℕ) : Set (EmbeddedRP n) :=
  {z | z ≠ erp0 n}

lemma V_open (n : ℕ) : IsOpen (V n) :=
  isOpen_compl_singleton

/-- U ∪ V = univ for n ≥ 1. -/
lemma cover (n : ℕ) (hn : 1 ≤ n) :
    (Set.univ : Set (EmbeddedRP n)) ⊆ U n ∪ V n := by
  intro z _
  by_cases h : z ∈ U n
  · exact Or.inl h
  · have h' : (z : EuclideanSpace ℝ (Fin (n + 1) × Fin (n + 1))) (0, 0) ≤ 0 := by
      simpa [U] using h
    have h'' : (z : EuclideanSpace ℝ (Fin (n + 1) × Fin (n + 1))) (0, 0) = 0 := by
      have h_nonneg := coord00_nonneg z
      linarith
    have h_ne : z ≠ erp0 n := by
      intro h_eq
      have h4 : (veroneseMap (rp0 n)) (0, 0) = 1 := by
        have h5 : (veroneseMap (rp0 n)) (0, 0) = (e0 n).val 0 * (e0 n).val 0 := by
          exact veroneseFun_apply (e0 n) 0 0
        rw [h5]
        have h6 : (e0 n).val 0 = 1 := e0_coord0 n
        rw [h6] <;> norm_num
      have h5 : (z : EuclideanSpace ℝ (Fin (n + 1) × Fin (n + 1))) (0, 0) =
                   (veroneseMap (rp0 n)) (0, 0) := by
        rw [h_eq] <;> rfl
      rw [h'', h4] at h5 <;> norm_num at h5
    exact Or.inr h_ne

/-!
## RP^{n-1} subspace: z_{00} = 0
-/

/-- The RP^{n-1} subspace: points with x_0 = 0, i.e. z_{00} = 0. -/
def RPnMinus1 (n : ℕ) : Set (EmbeddedRP n) :=
  {z | (z : EuclideanSpace ℝ (Fin (n + 1) × Fin (n + 1))) (0, 0) = 0}

/-- RPnMinus1 is a subset of V for n ≥ 1. -/
lemma RPnMinus1_sub_V (n : ℕ) (hn : 1 ≤ n) : RPnMinus1 n ⊆ V n := by
  intro z hz
  have h1 : (z : EuclideanSpace ℝ (Fin (n + 1) × Fin (n + 1))) (0, 0) = 0 := hz
  intro h_eq
  have h2 : (veroneseMap (rp0 n)) (0, 0) = 1 := by
    have h3 : (veroneseMap (rp0 n)) (0, 0) = (e0 n).val 0 * (e0 n).val 0 := by
      exact veroneseFun_apply (e0 n) 0 0
    rw [h3]
    have h4 : (e0 n).val 0 = 1 := e0_coord0 n
    rw [h4] <;> norm_num
  have h5 : (z : EuclideanSpace ℝ (Fin (n + 1) × Fin (n + 1))) (0, 0) =
               (veroneseMap (rp0 n)) (0, 0) := by
    rw [h_eq] <;> rfl
  rw [h1, h2] at h5 <;> norm_num at h5

/-!
## U ∩ V ≅ R^n \ {0}

U ∩ V consists of points with z_{00} > 0 and z ≠ rp0.
Since z_{00} > 0 and z = rp0 implies z_{00} = 1, the only point in U with z_{00} = 1
and all other z_{0j} = 0 is rp0. So U ∩ V = U \ {rp0} ≅ R^n \ {0}.
-/

/-- U ∩ V as a subtype. -/
abbrev UInterV (n : ℕ) : Type := {z : EmbeddedRP n // z ∈ U n ∩ V n}

/-!
## Gnomonic homeomorphism U ≅ R^n

For z ∈ U (z_{00} > 0), the gnomonic projection maps to affine coordinates:
  y_i = z_{i0} / z_{00}  for i = 1, ..., n.
The inverse maps y ∈ R^n to the normalized sphere point (1, y_1, ..., y_n) / ‖...‖.
-/

/-- Subtype of points in U. -/
abbrev UType (n : ℕ) : Type := {z : EmbeddedRP n // z ∈ U n}

/-- Gnomonic projection from U to R^n. -/
def gnomonic (z : UType n) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun i : Fin n =>
    z.val.val (i.succ, 0) / z.val.val (0, 0)

lemma continuous_gnomonic : Continuous (gnomonic (n := n)) := by
  have h : Continuous (fun (z : UType n) =>
    (fun i : Fin n => z.val.val (i.succ, 0) / z.val.val (0, 0))) := by
    apply continuous_pi
    intro i
    have h_num : Continuous (fun (z : UType n) => z.val.val (i.succ, 0)) := by fun_prop
    have h_den : Continuous (fun (z : UType n) => z.val.val (0, 0)) := by fun_prop
    have h_ne : ∀ (z : UType n), z.val.val (0, 0) ≠ 0 := by
      intro z; exact z.prop.ne'
    exact h_num.div h_den h_ne
  have h2 : Continuous (fun (f : Fin n → ℝ) => WithLp.toLp 2 f) :=
    PiLp.continuous_toLp 2 fun _ => ℝ
  exact h2.comp h

/-- Radius for affine-to-sphere map. -/
def affineRadius (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.sqrt (1 + ‖y‖ ^ 2)

/-- Euclidean vector for affine-to-sphere map. -/
def affineVector (y : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  let r := affineRadius y
  WithLp.toLp 2 fun j : Fin (n + 1) =>
    if h : j = 0 then 1 / r else y (Fin.pred j h) / r

lemma affineVector_coord0 (y : EuclideanSpace ℝ (Fin n)) :
    affineVector y 0 = 1 / affineRadius y := by
  simp [affineVector] <;> norm_num

lemma affineVector_coordSucc (y : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    affineVector y i.succ = y i / affineRadius y := by
  have hne : (i.succ : Fin (n + 1)) ≠ 0 := by simp
  simp [affineVector, hne] <;> rfl

lemma affineVector_norm (y : EuclideanSpace ℝ (Fin n)) :
    ‖affineVector y‖ = 1 := by
  let r := affineRadius y
  let v := affineVector y
  have hsq : ‖v‖ ^ 2 = 1 := by
    have h1 : ‖v‖ ^ 2 = ∑ j : Fin (n + 1), (v j) ^ 2 :=
      EuclideanSpace.real_norm_sq_eq v
    rw [h1]
    have h_v0 : v 0 = 1 / r := affineVector_coord0 y
    have h_vsucc : ∀ (i : Fin n), v i.succ = y i / r :=
      affineVector_coordSucc y
    have h_sum1 : ∑ j : Fin (n + 1), (v j) ^ 2 =
        (v 0) ^ 2 + ∑ i : Fin n, (v i.succ) ^ 2 := by
      rw [Fin.sum_univ_succ] <;> rfl
    rw [h_sum1, h_v0]
    have h_sum2 : ∑ i : Fin n, (v i.succ) ^ 2 = ∑ i : Fin n, (y i / r) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      have h : v i.succ = y i / r := h_vsucc i
      rw [h]
    rw [h_sum2]
    have h_sum3 : (1 / r) ^ 2 + ∑ i : Fin n, (y i / r) ^ 2 = (1 + ‖y‖ ^ 2) / r ^ 2 := by
      have h4 : ∑ i : Fin n, (y i / r) ^ 2 = (∑ i : Fin n, (y i) ^ 2) / r ^ 2 := by
        have h5 : ∀ i, (y i / r) ^ 2 = (y i) ^ 2 / r ^ 2 := by
          intro i; field_simp <;> ring
        rw [Finset.sum_congr rfl (fun i _ => h5 i), Finset.sum_div]
      rw [h4]
      have h6 : ‖y‖ ^ 2 = ∑ i : Fin n, (y i) ^ 2 := EuclideanSpace.real_norm_sq_eq y
      rw [h6] <;> field_simp <;> ring
    rw [h_sum3]
    have h7 : 0 ≤ 1 + ‖y‖ ^ 2 := by positivity
    have h8 : r ^ 2 = 1 + ‖y‖ ^ 2 := by
      dsimp only [r, affineRadius]
      exact Real.sq_sqrt h7
    rw [h8] <;> field_simp <;> ring
  have hnonneg : 0 ≤ ‖v‖ := norm_nonneg v
  have h9 : (‖v‖ - 1) * (‖v‖ + 1) = ‖v‖ ^ 2 - 1 := by ring
  have h10 : (‖v‖ - 1) * (‖v‖ + 1) = 0 := by
    have h_sub : ‖v‖ ^ 2 - 1 = 0 := by rw [hsq] <;> norm_num
    nlinarith
  have h11 : ‖v‖ - 1 = 0 ∨ ‖v‖ + 1 = 0 := eq_zero_or_eq_zero_of_mul_eq_zero h10
  cases h11 with
  | inl h11 => linarith
  | inr h11 => linarith

/-- Construct a sphere point from affine coordinates y ∈ R^n. -/
def affineToSphere (y : EuclideanSpace ℝ (Fin n)) : SphereType n :=
  ⟨affineVector y, mem_sphere_zero_iff_norm.mpr (affineVector_norm y)⟩

lemma affineToSphere_coord0 (y : EuclideanSpace ℝ (Fin n)) :
    (affineToSphere y).val 0 = 1 / affineRadius y := by
  rfl

lemma affineToSphere_coordSucc (y : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    (affineToSphere y).val i.succ = y i / affineRadius y := by
  rfl

/-- Inverse gnomonic projection: R^n → U. -/
def gnomonicInv (y : EuclideanSpace ℝ (Fin n)) : UType n :=
  let x := affineToSphere y
  let z : EmbeddedRP n := veroneseEquiv n (quotientMap n x)
  have hz : z ∈ U n := by
    have h2 : z.val (0, 0) = x.val 0 * x.val 0 := by
      have h_eq : z.val = veroneseMap (quotientMap n x) := by rfl
      rw [h_eq]
      exact veroneseFun_apply x 0 0
    have h5 : 0 < affineRadius y := by dsimp only [affineRadius]; positivity
    have h3 : 0 < z.val (0, 0) := by
      rw [h2]
      have h4 : x.val 0 = 1 / affineRadius y := affineToSphere_coord0 y
      rw [h4]
      exact mul_pos (div_pos zero_lt_one h5) (div_pos zero_lt_one h5)
    simpa [U] using h3
  ⟨z, hz⟩

lemma continuous_affineRadius : Continuous (affineRadius (n := n)) := by
  have h1 : Continuous (fun (y : EuclideanSpace ℝ (Fin n)) => ‖y‖) :=
    continuous_norm
  have h2 : Continuous (fun (y : EuclideanSpace ℝ (Fin n)) => 1 + ‖y‖ ^ 2) := by
    continuity
  exact Real.continuous_sqrt.comp h2

/-- Embeds R^n into R^{n+1} with zero 0-th coordinate. -/
def extendZeroMap (y : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 fun j => if h : j = 0 then (0 : ℝ) else y (Fin.pred j h)

lemma continuous_extendZeroMap : Continuous (extendZeroMap (n := n)) := by
  have h : Continuous (fun (y : EuclideanSpace ℝ (Fin n)) =>
      (fun j : Fin (n + 1) => if h : j = 0 then (0 : ℝ) else y (Fin.pred j h))) := by
    apply continuous_pi
    intro j
    by_cases h : j = 0
    · subst h
      have h_eq : (fun (y : EuclideanSpace ℝ (Fin n)) =>
          (if h' : (0 : Fin (n + 1)) = 0 then (0 : ℝ)
           else y (Fin.pred (0 : Fin (n + 1)) h'))) = (fun _ => (0 : ℝ)) := by
        funext y; simp
      rw [h_eq]; exact continuous_const
    · have h_eq : (fun (y : EuclideanSpace ℝ (Fin n)) =>
          (if h' : j = 0 then (0 : ℝ) else y (Fin.pred j h'))) =
          (fun y : EuclideanSpace ℝ (Fin n) => y (Fin.pred j h)) := by
        funext y; simp [h]
      rw [h_eq]
      exact PiLp.continuous_apply 2 (fun _ => ℝ) (Fin.pred j h)
  have h2 : Continuous (fun (f : Fin (n + 1) → ℝ) => WithLp.toLp 2 f) :=
    PiLp.continuous_toLp 2 fun _ => ℝ
  exact h2.comp h

lemma continuous_affineVector : Continuous (affineVector (n := n)) := by
  have h_ne : ∀ (y : EuclideanSpace ℝ (Fin n)), affineRadius y ≠ 0 := by
    intro y
    have h_pos : 0 < affineRadius y := by
      simp only [affineRadius]
      positivity
    exact h_pos.ne'
  have h : Continuous (fun (y : EuclideanSpace ℝ (Fin n)) =>
      (fun j : Fin (n + 1) =>
        if h : j = 0 then 1 / affineRadius y else y (Fin.pred j h) / affineRadius y)) := by
    apply continuous_pi
    intro j
    by_cases h : j = 0
    · subst h
      have h_eq : (fun (y : EuclideanSpace ℝ (Fin n)) =>
          (if h' : (0 : Fin (n + 1)) = 0 then 1 / affineRadius y
           else y (Fin.pred (0 : Fin (n + 1)) h') / affineRadius y)) =
          (fun y => 1 / affineRadius y) := by
        funext y; simp
      rw [h_eq]
      have h_r : Continuous (affineRadius (n := n)) := continuous_affineRadius
      exact continuous_const.div h_r h_ne
    · have h_eq : (fun (y : EuclideanSpace ℝ (Fin n)) =>
          (if h' : j = 0 then 1 / affineRadius y
           else y (Fin.pred j h') / affineRadius y)) =
          (fun y => y (Fin.pred j h) / affineRadius y) := by
        funext y; simp [h]
      rw [h_eq]
      have h_r : Continuous (affineRadius (n := n)) := continuous_affineRadius
      have h_apply : Continuous (fun (y : EuclideanSpace ℝ (Fin n)) => y (Fin.pred j h)) := by
        exact PiLp.continuous_apply 2 (fun _ => ℝ) (Fin.pred j h)
      exact h_apply.div h_r h_ne
  have h2 : Continuous (fun (f : Fin (n + 1) → ℝ) => WithLp.toLp 2 f) :=
    PiLp.continuous_toLp 2 fun _ => ℝ
  exact h2.comp h

lemma continuous_affineToSphere : Continuous (affineToSphere (n := n)) := by
  have h1 : Continuous (affineVector (n := n)) := continuous_affineVector
  exact Continuous.subtype_mk h1 (fun y => mem_sphere_zero_iff_norm.mpr (affineVector_norm y))

lemma continuous_gnomonicInv : Continuous (gnomonicInv (n := n)) := by
  let f : EuclideanSpace ℝ (Fin n) → EmbeddedRP n := fun y =>
    veroneseEquiv n (quotientMap n (affineToSphere y))
  have hf : Continuous f := by
    dsimp only [f]
    have h1 : Continuous (affineToSphere (n := n)) := continuous_affineToSphere
    have h2 : Continuous (fun (x : SphereType n) => veroneseEquiv n (quotientMap n x)) := by
      have h_cont1 : Continuous (quotientMap n) := by
        exact continuous_coinduced_rng
      have h_cont2 : Continuous (veroneseEquiv n) := veroneseEquiv_continuous
      exact h_cont2.comp h_cont1
    exact h2.comp h1
  have hP : ∀ y, f y ∈ U n := by
    intro y
    have h2 : (f y).val (0, 0) = (affineToSphere y).val 0 * (affineToSphere y).val 0 := by
      have h_eq : (f y).val = veroneseMap (quotientMap n (affineToSphere y)) := by rfl
      rw [h_eq]
      exact veroneseFun_apply (affineToSphere y) 0 0
    have h3 : 0 < (f y).val (0, 0) := by
      rw [h2]
      have h4 : (affineToSphere y).val 0 = 1 / affineRadius y := affineToSphere_coord0 y
      have h5 : 0 < affineRadius y := by dsimp only [affineRadius]; positivity
      rw [h4]
      exact mul_pos (div_pos zero_lt_one h5) (div_pos zero_lt_one h5)
    simpa [U] using h3
  exact Continuous.subtype_mk hf hP

/-- Pick the representative of a U-point with positive 0-coordinate. -/
def positiveRep (z : UType n) : SphereType n :=
  let rp : RPType n := (veroneseEquiv n).symm z.val
  let x0 : SphereType n := Quotient.out rp
  if h : 0 < x0.val 0 then x0 else antipodal n x0

lemma positiveRep_val0_pos (z : UType n) : 0 < (positiveRep z).val 0 := by
  let rp : RPType n := (veroneseEquiv n).symm z.val
  let x0 : SphereType n := Quotient.out rp
  have h_veronese : z.val.val = veroneseMap rp := by
    have h_eq : (veroneseEquiv n).toFun rp = z.val := (veroneseEquiv n).right_inv z.val
    have h : ((veroneseEquiv n).toFun rp).val = z.val.val := by rw [h_eq]
    have h2 : ((veroneseEquiv n).toFun rp).val = veroneseMap rp := by rfl
    exact h.symm.trans h2
  have h_z00 : z.val.val (0, 0) = x0.val 0 * x0.val 0 := by
    rw [h_veronese]
    have h_eq2 : veroneseMap rp = veroneseFun x0 := by
      have h : quotientMap n x0 = rp := Quotient.out_eq rp
      rw [←h] <;> rfl
    rw [h_eq2]
    exact veroneseFun_apply x0 0 0
  have h_ne : x0.val 0 ≠ 0 := by
    have h_pos : 0 < z.val.val (0, 0) := z.prop
    rw [h_z00] at h_pos
    nlinarith
  dsimp only [positiveRep]
  split_ifs with h
  · exact h
  · have h' : x0.val 0 < 0 := by
      by_contra h''; exact h_ne (by linarith)
    have h3 : (antipodal n x0).val 0 = -(x0.val 0) := by rfl
    rw [h3]; linarith

lemma positiveRep_quotient (z : UType n) :
    quotientMap n (positiveRep z) = (veroneseEquiv n).symm z.val := by
  let rp : RPType n := (veroneseEquiv n).symm z.val
  let x0 : SphereType n := Quotient.out rp
  dsimp only [positiveRep]
  split_ifs with h
  · exact Quotient.out_eq rp
  · have h_eq : quotientMap n (antipodal n x0) = quotientMap n x0 := by
      exact Quotient.sound (Or.inr rfl)
    have h_out : quotientMap n x0 = rp := Quotient.out_eq rp
    rw [h_eq, h_out]

lemma positiveRep_veronese (z : UType n) :
    veroneseMap (quotientMap n (positiveRep z)) = z.val.val := by
  have h1 : quotientMap n (positiveRep z) = (veroneseEquiv n).symm z.val :=
    positiveRep_quotient z
  rw [h1]
  let rp := (veroneseEquiv n).symm z.val
  have h_eq : (veroneseEquiv n).toFun rp = z.val := (veroneseEquiv n).right_inv z.val
  have h3 : ((veroneseEquiv n).toFun rp).val = z.val.val := by rw [h_eq]
  have h4 : ((veroneseEquiv n).toFun rp).val = veroneseMap rp := by rfl
  have h5 : veroneseMap rp = z.val.val := by
    exact h4.symm.trans h3
  exact h5

lemma gnomonic_gnomonicInv (y : EuclideanSpace ℝ (Fin n)) :
    gnomonic (gnomonicInv y) = y := by
  let x := affineToSphere y
  let r := affineRadius y
  have h1 : ∀ (i : Fin n),
      (gnomonicInv y).val.val (i.succ, 0) = y i / r ^ 2 := by
    intro i
    have h_eq : (gnomonicInv y).val.val = veroneseMap (quotientMap n x) := by rfl
    rw [h_eq]
    have h2 : (veroneseMap (quotientMap n x)) (i.succ, 0) =
        x.val (Fin.succ i) * x.val 0 := veroneseFun_apply x i.succ 0
    rw [h2]
    have h3 : x.val (Fin.succ i) = y i / r := affineToSphere_coordSucc y i
    have h4 : x.val 0 = 1 / r := affineToSphere_coord0 y
    rw [h3, h4] <;> field_simp <;> ring
  have h2 : (gnomonicInv y).val.val (0, 0) = 1 / r ^ 2 := by
    have h_eq : (gnomonicInv y).val.val = veroneseMap (quotientMap n x) := by rfl
    rw [h_eq]
    have h3 : (veroneseMap (quotientMap n x)) (0, 0) = x.val 0 * x.val 0 :=
      veroneseFun_apply x 0 0
    rw [h3]
    have h4 : x.val 0 = 1 / r := affineToSphere_coord0 y
    rw [h4] <;> field_simp <;> ring
  have hr_pos : 0 < r := by
    dsimp only [r, affineRadius]
    positivity
  ext i
  have h_goal : (gnomonic (gnomonicInv y)) i =
      (gnomonicInv y).val.val (i.succ, 0) / (gnomonicInv y).val.val (0, 0) := by rfl
  rw [h_goal, h1 i, h2]
  field_simp [hr_pos.ne'] <;> ring

lemma gnomonicInv_gnomonic (z : UType n) :
    gnomonicInv (gnomonic z) = z := by
  let x := positiveRep z
  let y := gnomonic z
  have h_y_eq : ∀ (i : Fin n), y i = x.val (Fin.succ i) / x.val 0 := by
    intro i
    have h1 : z.val.val (i.succ, 0) = x.val (Fin.succ i) * x.val 0 := by
      rw [←positiveRep_veronese z]
      exact veroneseFun_apply x i.succ 0
    have h2 : z.val.val (0, 0) = x.val 0 * x.val 0 := by
      rw [←positiveRep_veronese z]
      exact veroneseFun_apply x 0 0
    have h_goal : y i = z.val.val (i.succ, 0) / z.val.val (0, 0) := by rfl
    rw [h_goal, h1, h2]
    have hpos : 0 < x.val 0 := positiveRep_val0_pos z
    field_simp [hpos.ne'] <;> ring
  have h_x_norm2 : ‖x.val‖ ^ 2 = 1 := by
    have h : ‖x.val‖ = 1 := mem_sphere_zero_iff_norm.mp x.property
    rw [h] <;> norm_num
  have h_norm_sum : ‖x.val‖ ^ 2 = (x.val 0) ^ 2 + ∑ i : Fin n, (x.val (Fin.succ i)) ^ 2 := by
    have h1 : ‖x.val‖ ^ 2 = ∑ j : Fin (n + 1), (x.val j) ^ 2 :=
      EuclideanSpace.real_norm_sq_eq x.val
    rw [h1, Fin.sum_univ_succ] <;> rfl
  have h_sum : ∑ i : Fin n, (x.val (Fin.succ i)) ^ 2 = 1 - (x.val 0) ^ 2 := by
    linarith [h_x_norm2, h_norm_sum]
  have h_ynorm2 : ‖y‖ ^ 2 = (1 - (x.val 0) ^ 2) / (x.val 0) ^ 2 := by
    have h1 : ‖y‖ ^ 2 = ∑ i : Fin n, (y i) ^ 2 :=
      EuclideanSpace.real_norm_sq_eq y
    rw [h1]
    have h_sum3 : ∑ i : Fin n, (y i) ^ 2 = ∑ i : Fin n, (x.val (Fin.succ i) / x.val 0) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      have h : y i = x.val (Fin.succ i) / x.val 0 := h_y_eq i
      rw [h]
    rw [h_sum3]
    have h_sum4 : ∑ i : Fin n, (x.val (Fin.succ i) / x.val 0) ^ 2 =
        (∑ i : Fin n, (x.val (Fin.succ i)) ^ 2) / (x.val 0) ^ 2 := by
      have hpos2 : 0 < x.val 0 := positiveRep_val0_pos z
      have h : ∀ (i : Fin n), (x.val (Fin.succ i) / x.val 0) ^ 2 = (x.val (Fin.succ i)) ^ 2 / (x.val 0) ^ 2 := by
        intro i
        field_simp [hpos2.ne'] <;> ring
      rw [Finset.sum_congr rfl (fun i _ => h i), Finset.sum_div]
    rw [h_sum4, h_sum]
  have hpos : 0 < x.val 0 := positiveRep_val0_pos z
  have h_r_eq : affineRadius y = 1 / x.val 0 := by
    have h9 : 1 + ‖y‖ ^ 2 = 1 / (x.val 0) ^ 2 := by
      rw [h_ynorm2]
      field_simp [hpos.ne'] <;> ring
    have h10 : affineRadius y = Real.sqrt (1 + ‖y‖ ^ 2) := by rfl
    rw [h10, h9]
    have h11 : 0 < 1 / x.val 0 := by positivity
    have h13 : 1 / (x.val 0) ^ 2 = (1 / x.val 0) ^ 2 := by ring
    rw [h13]
    have h12 : Real.sqrt ((1 / x.val 0) ^ 2) = 1 / x.val 0 := by
      rw [Real.sqrt_sq_eq_abs, abs_of_pos h11]
    exact h12
  have h_main : affineToSphere y = x := by
    apply Subtype.ext
    ext j
    by_cases h : j = 0
    · subst h
      rw [affineToSphere_coord0 y, h_r_eq] <;> field_simp
    · have h_exists : ∃ (i : Fin n), j = i.succ := by
        refine' ⟨Fin.pred j h, _⟩
        exact (Fin.succ_pred j h).symm
      rcases h_exists with ⟨i, rfl⟩
      rw [affineToSphere_coordSucc y i, h_r_eq]
      rw [h_y_eq i] <;> field_simp [hpos.ne'] <;> ring
  have h3 : (gnomonicInv y).val = z.val := by
    have h4 : (gnomonicInv y).val =
        veroneseEquiv n (quotientMap n (affineToSphere y)) := by rfl
    rw [h4, h_main]
    have h5 : veroneseEquiv n (quotientMap n x) = z.val := by
      have h6 : quotientMap n x = (veroneseEquiv n).symm z.val :=
        positiveRep_quotient z
      rw [h6]
      exact (veroneseEquiv n).right_inv z.val
    exact h5
  exact Subtype.ext h3

/-- Homeomorphism U ≃ₜ R^n via gnomonic projection. -/
def uHomeo : UType n ≃ₜ EuclideanSpace ℝ (Fin n) :=
  { toFun := gnomonic
    invFun := gnomonicInv
    left_inv := gnomonicInv_gnomonic
    right_inv := gnomonic_gnomonicInv
    continuous_toFun := continuous_gnomonic
    continuous_invFun := continuous_gnomonicInv }

/-!
## U ∩ V ≅ R^n \ {0}

Under the gnomonic projection, erp0 = [e0] maps to 0 ∈ R^n.
Therefore U ∩ V = U \ {erp0} maps to R^n \ {0}.
-/

/-- erp0 is in U since its (0,0) coordinate is 1 > 0. -/
lemma erp0_in_U (n : ℕ) : erp0 n ∈ U n := by
  have h1 : (erp0 n : EuclideanSpace ℝ (Fin (n + 1) × Fin (n + 1))) (0, 0) = 1 := by
    have h2 : (erp0 n : EuclideanSpace ℝ (Fin (n + 1) × Fin (n + 1))) =
        veroneseMap (rp0 n) := by rfl
    rw [h2]
    have h3 : veroneseMap (rp0 n) (0, 0) = (e0 n).val 0 * (e0 n).val 0 :=
      veroneseFun_apply (e0 n) 0 0
    rw [h3, e0_coord0 n] <;> norm_num
  have h_pos : 0 < (erp0 n : EuclideanSpace ℝ (Fin (n + 1) × Fin (n + 1))) (0, 0) := by
    rw [h1] <;> norm_num
  exact h_pos

/-- erp0 viewed as an element of UType n. -/
def erp0' (n : ℕ) : UType n := ⟨erp0 n, erp0_in_U n⟩

/-- gnomonic(erp0') = 0. -/
lemma gnomonic_erp0 (n : ℕ) : gnomonic (erp0' n) = 0 := by
  ext i
  have h1 : (erp0' n).val.val (i.succ, 0) = 0 := by
    have h2 : (erp0' n).val = erp0 n := by rfl
    rw [h2]
    have h3 : (erp0 n : EuclideanSpace ℝ (Fin (n + 1) × Fin (n + 1))) =
        veroneseMap (rp0 n) := by rfl
    rw [h3]
    have h4 : veroneseMap (rp0 n) (i.succ, 0) = (e0 n).val i.succ * (e0 n).val 0 :=
      veroneseFun_apply (e0 n) i.succ 0
    rw [h4]
    have h5 : (e0 n).val i.succ = 0 := by
      simp [e0, EuclideanSpace.single, Ne.symm (Fin.succ_ne_zero i)]
      <;> tauto
    rw [h5] <;> ring
  have h2 : (erp0' n).val.val (0, 0) = 1 := by
    have h3 : (erp0' n).val = erp0 n := by rfl
    rw [h3]
    have h4 : (erp0 n : EuclideanSpace ℝ (Fin (n + 1) × Fin (n + 1))) (0, 0) = 1 := by
      have h5 : (erp0 n : EuclideanSpace ℝ (Fin (n + 1) × Fin (n + 1))) =
          veroneseMap (rp0 n) := by rfl
      rw [h5]
      have h6 : veroneseMap (rp0 n) (0, 0) = (e0 n).val 0 * (e0 n).val 0 :=
        veroneseFun_apply (e0 n) 0 0
      rw [h6, e0_coord0 n] <;> norm_num
    exact h4
  simpa [gnomonic, h1, h2] using by norm_num

/-- U ∩ V as a subtype of UType n. -/
abbrev UInterVType (n : ℕ) : Type := {z : UType n // z.val ≠ erp0 n}

/-- R^n \ {0} as a subtype. -/
abbrev RnMinus0 (n : ℕ) : Type := {y : EuclideanSpace ℝ (Fin n) // y ≠ 0}

/-- Homeomorphism U ∩ V ≃ₜ R^n \ {0}. -/
def uInterVHomeo : UInterVType n ≃ₜ RnMinus0 n := by
  let h : UType n ≃ₜ EuclideanSpace ℝ (Fin n) := uHomeo
  have h_eq : h (erp0' n) = 0 := gnomonic_erp0 n
  let p : UType n → Prop := fun z => z.val ≠ erp0 n
  let q : EuclideanSpace ℝ (Fin n) → Prop := fun y => y ≠ 0
  have hiff : ∀ (z : UType n), p z ↔ q (h z) := by
    intro z
    have h4 : h z = 0 ↔ z = erp0' n := by
      constructor
      · intro h5
        have h6 : z = h.symm (h z) := (h.left_inv z).symm
        rw [h6, h5]
        have h7 : h.symm (h (erp0' n)) = erp0' n := h.left_inv (erp0' n)
        have h8 : h.symm 0 = h.symm (h (erp0' n)) := by rw [h_eq]
        rw [h8, h7]
      · intro h5
        rw [h5, h_eq]
    have h5 : (z.val ≠ erp0 n) ↔ (z ≠ erp0' n) := by
      constructor
      · intro hne h_eq2
        exact hne (congr_arg Subtype.val h_eq2)
      · intro hne h_eq2
        exact hne (Subtype.ext h_eq2)
    have h6 : (z ≠ erp0' n) ↔ (h z ≠ 0) := by
      exact h4.not.symm
    simpa [p, q] using h5.trans h6
  let f : UInterVType n → RnMinus0 n := fun z =>
    ⟨h z, (hiff z).mp z.prop⟩
  let g : RnMinus0 n → UInterVType n := fun y =>
    let yval : EuclideanSpace ℝ (Fin n) := y.val
    have h9 : h (h.symm yval) = yval := h.right_inv yval
    have h10 : q (h (h.symm yval)) := by
      dsimp only [q]
      rw [h9]
      exact y.prop
    ⟨h.symm yval, (hiff (h.symm yval)).mpr h10⟩
  refine' {
    toFun := f,
    invFun := g,
    left_inv := _,
    right_inv := _,
    continuous_toFun := _,
    continuous_invFun := _
  }
  · intro z; ext; simp [f, g]
  · intro y; ext; simp [f, g]
  · have hcont : Continuous (fun (z : UInterVType n) => h (z : UType n)) :=
      h.continuous_toFun.comp continuous_subtype_val
    exact hcont.subtype_mk (fun z => (hiff z).mp z.prop)
  · have hcont : Continuous (fun (y : RnMinus0 n) => h.symm (y.val)) :=
      h.continuous_invFun.comp continuous_subtype_val
    exact hcont.subtype_mk (fun y =>
      let yval := y.val
      have h9 : h (h.symm yval) = yval := h.right_inv yval
      have h10 : q (h (h.symm yval)) := by
        dsimp only [q]; rw [h9]; exact y.prop
      (hiff (h.symm yval)).mpr h10)

end BorsukUlam.RealProjective.Cover

end
