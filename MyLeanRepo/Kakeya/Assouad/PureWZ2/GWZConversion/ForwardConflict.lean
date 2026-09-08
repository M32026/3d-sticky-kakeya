import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12
import MyLeanRepo.Kakeya.Streamlined.Families
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.TileFilter
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.TightDistinctness
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.CapsuleBounds

set_option linter.constructorNameAsVariable false

/-!
# Constant forward conflict degree bound

Uses harbor's TightDistinctness grid approach to get a CONSTANT bound
on the number of essentially distinct δ-tubes contained in the 2-dilation
of a given δ-tube.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

open Kakeya.Streamlined
open Kakeya.Streamlined.GeometricLemmas

/-- Reflection function: negate z-coordinate. -/
private def zReflectFun (p : Point3) : Point3 :=
  p - (2 * (p 2)) • (EuclideanSpace.single 2 1)

@[simp] private lemma zReflectFun_0 (p : Point3) : (zReflectFun p) 0 = p 0 := by
  simp [zReflectFun, Pi.sub_apply, Pi.smul_apply, EuclideanSpace.single] <;> ring

@[simp] private lemma zReflectFun_1 (p : Point3) : (zReflectFun p) 1 = p 1 := by
  simp [zReflectFun, Pi.sub_apply, Pi.smul_apply, EuclideanSpace.single] <;> ring

@[simp] private lemma zReflectFun_2 (p : Point3) : (zReflectFun p) 2 = - (p 2) := by
  simp [zReflectFun, Pi.sub_apply, Pi.smul_apply, EuclideanSpace.single] <;> ring

/-- Reflection in the z-axis as a linear isometry. -/
private def zReflect : Point3 ≃ₗᵢ[ℝ] Point3 :=
  { toFun := zReflectFun
    invFun := zReflectFun
    left_inv := by
      intro p
      ext i
      fin_cases i <;> simp <;> ring
    right_inv := by
      intro p
      ext i
      fin_cases i <;> simp <;> ring
    map_add' := by
      intro p q
      ext i
      fin_cases i <;> simp [Pi.add_apply] <;> ring
    map_smul' := by
      intro c p
      ext i
      fin_cases i <;> simp [Pi.smul_apply] <;> ring
    norm_map' := by
      intro p
      change ‖zReflectFun p‖ = ‖p‖
      have h1 : ‖zReflectFun p‖ ^ 2 = ∑ i : Fin 3, (zReflectFun p i)^2 :=
        EuclideanSpace.real_norm_sq_eq _
      have h2 : ‖p‖ ^ 2 = ∑ i : Fin 3, (p i)^2 := EuclideanSpace.real_norm_sq_eq _
      have h3 : ∑ i : Fin 3, (zReflectFun p i)^2 = ∑ i : Fin 3, (p i)^2 := by
        apply Finset.sum_congr rfl
        intro i _
        fin_cases i <;> simp <;> ring
      have h4 : ‖zReflectFun p‖ ^ 2 = ‖p‖ ^ 2 := by rw [h1, h2, h3]
      have h5 : 0 ≤ ‖zReflectFun p‖ := by positivity
      have h6 : 0 ≤ ‖p‖ := by positivity
      have h7 : ‖zReflectFun p‖ = ‖p‖ := by nlinarith
      exact h7 }

@[simp] private lemma zReflect_apply (p : Point3) : zReflect p = zReflectFun p := by rfl

/-- Helper: same floor implies |x - y| ≤ c. -/
private lemma same_floor_abs_le {x y c : ℝ} (hc : 0 < c)
    (h : Int.floor (x / c) = Int.floor (y / c)) : |x - y| ≤ c := by
  set k : ℤ := Int.floor (x / c) with hk
  have h1 : (k : ℝ) ≤ x / c := by exact_mod_cast Int.floor_le (x / c)
  have h2 : x / c < (k + 1 : ℝ) := by exact_mod_cast Int.lt_floor_add_one (x / c)
  have h3 : (Int.floor (y / c) : ℝ) ≤ y / c := Int.floor_le (y / c)
  have h4 : y / c < (Int.floor (y / c) + 1 : ℝ) := Int.lt_floor_add_one (y / c)
  have h5 : (k : ℝ) ≤ y / c := by
    have h7 : (Int.floor (y / c) : ℝ) = (k : ℝ) := by exact_mod_cast h.symm
    rw [h7] at h3; exact h3
  have h7 : y / c < (k + 1 : ℝ) := by
    have h9 : (Int.floor (y / c) : ℝ) = (k : ℝ) := by exact_mod_cast h.symm
    rw [h9] at h4; exact h4
  have h12 : |x / c - y / c| < 1 := by
    rw [abs_lt] <;> constructor <;> linarith
  have h13 : |x - y| < c := by
    have h14 : x - y = c * (x / c - y / c) := by field_simp [hc.ne'] <;> ring
    rw [h14]
    have h15 : |c * (x / c - y / c)| = c * |x / c - y / c| := by
      rw [abs_mul, abs_of_pos hc]
    rw [h15]
    have h16 : c * |x / c - y / c| < c * (1 : ℝ) := mul_lt_mul_of_pos_left h12 hc
    have h17 : c * (1 : ℝ) = c := by ring
    rw [h17] at h16
    exact h16
  exact h13.le

/-- Helper: floor x ∈ Icc n m if n ≤ x ≤ m. -/
private lemma floor_in_Icc {x : ℝ} {n m : ℤ} (h1 : (n : ℝ) ≤ x) (h2 : x ≤ (m : ℝ)) :
    Int.floor x ∈ Finset.Icc n m := by
  have h3 : n ≤ Int.floor x := Int.le_floor.mpr h1
  have h4 : (Int.floor x : ℝ) ≤ x := Int.floor_le x
  have h5 : (Int.floor x : ℝ) ≤ (m : ℝ) := by linarith
  have h6 : Int.floor x ≤ m := by exact_mod_cast h5
  exact Finset.mem_Icc.mpr ⟨h3, h6⟩

/-- Helper: affine map applied to p + t•v. -/
private lemma affine_apply (e : Point3 ≃ᵃⁱ[ℝ] Point3) (p : Point3) (t : ℝ) (v : Point3) :
    e (p + t • v) = e p + t • e.linearIsometryEquiv v := by
  have h_vadd := e.toAffineMap.map_vadd p (t • v)
  have h1 : (t • v) +ᵥ p = p + t • v := by simp [vadd_eq_add] <;> abel
  have h_smul : e.linearIsometryEquiv (t • v) = t • e.linearIsometryEquiv v :=
    e.linearIsometryEquiv.map_smul t v
  simpa [h1, vadd_eq_add, h_smul, add_comm] using h_vadd

/-- Helper: membership in 5-ary finset product. -/
private lemma mem_product5 {α β γ δ ε : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ] [DecidableEq ε]
    {s1 : Finset α} {s2 : Finset β} {s3 : Finset γ} {s4 : Finset δ} {s5 : Finset ε}
    {a : α} {b : β} {c : γ} {d : δ} {e : ε}
    (ha : a ∈ s1) (hb : b ∈ s2) (hc : c ∈ s3) (hd : d ∈ s4) (he : e ∈ s5) :
    (a, b, c, d, e) ∈ s1 ×ˢ (s2 ×ˢ (s3 ×ˢ (s4 ×ˢ s5))) := by
  have h5 : (d, e) ∈ s4 ×ˢ s5 := Finset.mem_product.mpr ⟨hd, he⟩
  have h4 : (c, (d, e)) ∈ s3 ×ˢ (s4 ×ˢ s5) := Finset.mem_product.mpr ⟨hc, h5⟩
  have h3 : (b, (c, (d, e))) ∈ s2 ×ˢ (s3 ×ˢ (s4 ×ˢ s5)) := Finset.mem_product.mpr ⟨hb, h4⟩
  have h2 : (a, (b, (c, (d, e)))) ∈ s1 ×ˢ (s2 ×ˢ (s3 ×ˢ (s4 ×ˢ s5))) := Finset.mem_product.mpr ⟨ha, h3⟩
  exact h2

/-- Constant forward conflict degree (independent of δ).
The δ argument is retained for backward compatibility. -/
def gwzForwardConflictDegree (_δ : ℝ) : ℕ := 10^17

/-- Constant forward conflict degree bound using TightDistinctness grid approach. -/
lemma gwz_forward_conflict_degree_bound
    {δ : ℝ} (hδ : 0 < δ) (hδ_small : δ ≤ 1 / 100)
    {source : STubeFamily δ}
    (hdistinct : source.IsEssentiallyDistinct)
    (i : Fin source.card) :
    (Finset.univ.filter fun j =>
      (source.tube j).carrier ⊆
        wz2PaperCenteredDilatedCarrier (2 : ℝ) (source.tube i)).card
      ≤ gwzForwardConflictDegree δ := by
  let T_i := source.tube i
  let indices : Finset (Fin source.card) :=
    Finset.univ.filter fun j =>
      (source.tube j).carrier ⊆ wz2PaperCenteredDilatedCarrier (2 : ℝ) T_i

  rcases frame_of_axis T_i.direction T_i.direction_unit with ⟨e1, e2, frame, hf2, hf0, hf1⟩

  let p_i : Point3 := frame.symm T_i.base
  let v : Point3 := frame.symm.linearIsometryEquiv T_i.direction
  let p (j : Fin source.card) : Point3 := frame.symm (source.tube j).base
  let u (j : Fin source.card) : Point3 := frame.symm.linearIsometryEquiv (source.tube j).direction
  let m (j : Fin source.card) : Point3 := p j + (1 / 2 : ℝ) • u j

  have h_capsule_lower : CapsuleLowerBound := capsule_lower_bound_instantiation
  have h_capsule_upper : CapsuleUpperBound := capsule_upper_bound_instantiation

  have h_params : ∀ j ∈ indices,
      |u j 0| ≤ 4 * δ ∧ |u j 1| ≤ 4 * δ ∧
      ((u j 2 ≥ 1 / 2) ∨ (u j 2 ≤ -1 / 2)) ∧
      |(m j - p_i) 0| ≤ 2 * δ ∧ |(m j - p_i) 1| ≤ 2 * δ ∧
      -1 / 2 - 2 * δ ≤ (m j - p_i) 2 ∧ (m j - p_i) 2 ≤ 3 / 2 + 2 * δ := by
    intro j hj
    have h_contain : (source.tube j).carrier ⊆ wz2PaperCenteredDilatedCarrier (2 : ℝ) T_i :=
      (Finset.mem_filter.mp hj).2
    exact conflict_geometric_bounds hδ (by linarith) frame p_i v (p j) (u j) (m j)
      rfl rfl hf2 hf0 hf1 rfl rfl rfl h_contain

  let c_trans : ℝ := δ / 200
  let c_long : ℝ := 1 / 3200
  have hc_trans_pos : 0 < c_trans := by positivity
  have hc_long_pos : 0 < c_long := by positivity

  let cell (j : Fin source.card) : ℤ × ℤ × ℤ × ℤ × ℤ :=
    (Int.floor ((u j 0) / c_trans),
     Int.floor ((u j 1) / c_trans),
     Int.floor (((m j - p_i) 0) / c_trans),
     Int.floor (((m j - p_i) 1) / c_trans),
     Int.floor (((m j - p_i) 2) / c_long))

  let indices_pos : Finset (Fin source.card) := indices.filter fun j => u j 2 ≥ 1 / 2
  let indices_neg : Finset (Fin source.card) := indices.filter fun j => u j 2 ≤ -1 / 2

  have h_cover : indices ⊆ indices_pos ∪ indices_neg := by
    intro j hj
    have h := (h_params j hj).2.2.1
    rcases h with (h | h)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hj, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hj, h⟩)

  have h_same_cell_diff : ∀ j1 j2, cell j1 = cell j2 →
      |(u j1 - u j2) 0| ≤ δ / 200 ∧
      |(u j1 - u j2) 1| ≤ δ / 200 ∧
      |(m j1 - m j2) 0| ≤ δ / 200 ∧
      |(m j1 - m j2) 1| ≤ δ / 200 ∧
      |(m j1 - m j2) 2| ≤ 1 / 3200 := by
    intro j1 j2 hcell
    have h0 := congr_arg Prod.fst hcell
    have h1 := congr_arg (Prod.fst ∘ Prod.snd) hcell
    have h2 := congr_arg (Prod.fst ∘ Prod.snd ∘ Prod.snd) hcell
    have h3 := congr_arg (Prod.fst ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd) hcell
    have h4 := congr_arg (Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd) hcell
    have d0 : |(u j1 0) - (u j2 0)| ≤ c_trans := same_floor_abs_le hc_trans_pos h0
    have d1 : |(u j1 1) - (u j2 1)| ≤ c_trans := same_floor_abs_le hc_trans_pos h1
    have dm0 : |((m j1 - p_i) 0) - ((m j2 - p_i) 0)| ≤ c_trans := same_floor_abs_le hc_trans_pos h2
    have dm1 : |((m j1 - p_i) 1) - ((m j2 - p_i) 1)| ≤ c_trans := same_floor_abs_le hc_trans_pos h3
    have dm2 : |((m j1 - p_i) 2) - ((m j2 - p_i) 2)| ≤ c_long := same_floor_abs_le hc_long_pos h4
    have h_m0 : |(m j1 - m j2) 0| ≤ δ / 200 := by
      have h_eq : (m j1 - m j2) 0 = (m j1 - p_i) 0 - (m j2 - p_i) 0 := by
        simp [Pi.sub_apply] <;> ring
      rw [h_eq] <;> simpa [c_trans] using dm0
    have h_m1 : |(m j1 - m j2) 1| ≤ δ / 200 := by
      have h_eq : (m j1 - m j2) 1 = (m j1 - p_i) 1 - (m j2 - p_i) 1 := by
        simp [Pi.sub_apply] <;> ring
      rw [h_eq] <;> simpa [c_trans] using dm1
    have h_m2 : |(m j1 - m j2) 2| ≤ 1 / 3200 := by
      have h_eq : (m j1 - m j2) 2 = (m j1 - p_i) 2 - (m j2 - p_i) 2 := by
        simp [Pi.sub_apply] <;> ring
      rw [h_eq] <;> simpa [c_long] using dm2
    have h_u0 : |(u j1 - u j2) 0| ≤ δ / 200 := by
      have h_eq : (u j1 - u j2) 0 = (u j1 0) - (u j2 0) := by simp [Pi.sub_apply] <;> ring
      rw [h_eq] <;> simpa [c_trans] using d0
    have h_u1 : |(u j1 - u j2) 1| ≤ δ / 200 := by
      have h_eq : (u j1 - u j2) 1 = (u j1 1) - (u j2 1) := by simp [Pi.sub_apply] <;> ring
      rw [h_eq] <;> simpa [c_trans] using d1
    exact ⟨h_u0, h_u1, h_m0, h_m1, h_m2⟩

  have h_pos_inj : Set.InjOn cell indices_pos := by
    intro j1 hj1 j2 hj2 hcell
    by_contra hne
    have h_u1_pos : u j1 2 ≥ 1 / 2 := (Finset.mem_filter.mp hj1).2
    have h_u2_pos : u j2 2 ≥ 1 / 2 := (Finset.mem_filter.mp hj2).2
    have h_j1_in : j1 ∈ indices := (Finset.mem_filter.mp hj1).1
    have h_j2_in : j2 ∈ indices := (Finset.mem_filter.mp hj2).1
    have h2_params := h_params j2 h_j2_in
    have h_u2_0 : |(u j2 0)| ≤ 8 * δ := by linarith [h2_params.1]
    have h_u2_1 : |(u j2 1)| ≤ 8 * δ := by linarith [h2_params.2.1]
    have h_diffs := h_same_cell_diff j1 j2 hcell
    have hm1 : m j1 = frame.symm ((source.tube j1).base + (1 / 2 : ℝ) • (source.tube j1).direction) := by
      have h_aff := affine_apply frame.symm (source.tube j1).base (1 / 2) (source.tube j1).direction
      have h_def : m j1 = frame.symm (source.tube j1).base + (1 / 2 : ℝ) • frame.symm.linearIsometryEquiv (source.tube j1).direction := by rfl
      rw [h_def]
      exact h_aff.symm
    have hm2 : m j2 = frame.symm ((source.tube j2).base + (1 / 2 : ℝ) • (source.tube j2).direction) := by
      have h_aff := affine_apply frame.symm (source.tube j2).base (1 / 2) (source.tube j2).direction
      have h_def : m j2 = frame.symm (source.tube j2).base + (1 / 2 : ℝ) • frame.symm.linearIsometryEquiv (source.tube j2).direction := by rfl
      rw [h_def]
      exact h_aff.symm
    have h_nd : ¬ (source.tube j1).EssentiallyDistinct (source.tube j2) :=
      close_params_not_distinct hδ (by linarith) frame
        (m j1) (m j2) (u j1) (u j2)
        hm1 hm2 rfl rfl
        h_u1_pos h_u2_pos h_u2_0 h_u2_1
        h_diffs.2.2.1 h_diffs.2.2.2.1 h_diffs.2.2.2.2 h_diffs.1 h_diffs.2.1
        h_capsule_lower h_capsule_upper
    exact h_nd (hdistinct j1 j2 hne)

  -- Negative case: reflect z-coordinate
  let frame' : Point3 ≃ᵃⁱ[ℝ] Point3 := zReflect.toAffineIsometryEquiv.trans frame
  let u' (j : Fin source.card) : Point3 := frame'.symm.linearIsometryEquiv (source.tube j).direction
  let m' (j : Fin source.card) : Point3 := frame'.symm ((source.tube j).base + (1 / 2 : ℝ) • (source.tube j).direction)

  have h_frame'_symm : ∀ (x : Point3), frame'.symm x = zReflect (frame.symm x) := by
    intro x; rfl
  have h_frame'_lin : ∀ (v : Point3), frame'.symm.linearIsometryEquiv v = zReflect (frame.symm.linearIsometryEquiv v) := by
    intro v; rfl

  have h_u'_eq : ∀ j, u' j = zReflect (u j) := by
    intro j
    have h : u' j = frame'.symm.linearIsometryEquiv (source.tube j).direction := by rfl
    rw [h, h_frame'_lin] <;> rfl
  have h_m'_eq : ∀ j, m' j = zReflect (m j) := by
    intro j
    have h : m' j = frame'.symm ((source.tube j).base + (1 / 2 : ℝ) • (source.tube j).direction) := by rfl
    rw [h, h_frame'_symm]
    have h2 : frame.symm ((source.tube j).base + (1 / 2 : ℝ) • (source.tube j).direction) = m j := by
      have h_aff := affine_apply frame.symm (source.tube j).base (1 / 2) (source.tube j).direction
      have h_def : m j = frame.symm (source.tube j).base + (1 / 2 : ℝ) • frame.symm.linearIsometryEquiv (source.tube j).direction := by rfl
      calc frame.symm ((source.tube j).base + (1 / 2 : ℝ) • (source.tube j).direction)
        = frame.symm (source.tube j).base + (1 / 2 : ℝ) • frame.symm.linearIsometryEquiv (source.tube j).direction := h_aff
      _ = m j := h_def.symm
    rw [h2]

  have h_neg_inj : Set.InjOn cell indices_neg := by
    intro j1 hj1 j2 hj2 hcell
    by_contra hne
    have h_u1_neg : u j1 2 ≤ -1 / 2 := (Finset.mem_filter.mp hj1).2
    have h_u2_neg : u j2 2 ≤ -1 / 2 := (Finset.mem_filter.mp hj2).2
    have h_j1_in : j1 ∈ indices := (Finset.mem_filter.mp hj1).1
    have h_j2_in : j2 ∈ indices := (Finset.mem_filter.mp hj2).1
    have h2_params := h_params j2 h_j2_in
    have h_zr0 : ∀ (x : Point3), (zReflect x) 0 = x 0 := by intro x; simp
    have h_zr1 : ∀ (x : Point3), (zReflect x) 1 = x 1 := by intro x; simp
    have h_zr2 : ∀ (x : Point3), (zReflect x) 2 = - (x 2) := by intro x; simp
    have h_u2_0 : |(u' j2 0)| ≤ 8 * δ := by
      have h : (u' j2 0) = (u j2 0) := by rw [h_u'_eq j2, h_zr0]
      rw [h] <;> linarith [h2_params.1]
    have h_u2_1 : |(u' j2 1)| ≤ 8 * δ := by
      have h : (u' j2 1) = (u j2 1) := by rw [h_u'_eq j2, h_zr1]
      rw [h] <;> linarith [h2_params.2.1]
    have h_u1_pos' : u' j1 2 ≥ 1 / 2 := by
      have h : (u' j1 2) = - (u j1 2) := by rw [h_u'_eq j1, h_zr2]
      rw [h] <;> linarith
    have h_u2_pos' : u' j2 2 ≥ 1 / 2 := by
      have h : (u' j2 2) = - (u j2 2) := by rw [h_u'_eq j2, h_zr2]
      rw [h] <;> linarith
    have h_diffs := h_same_cell_diff j1 j2 hcell
    have h_m0' : |(m' j1 - m' j2) 0| ≤ δ / 200 := by
      have h_sub : m' j1 - m' j2 = zReflect (m j1 - m j2) := by
        rw [h_m'_eq j1, h_m'_eq j2, ←zReflect.map_sub]
      have h : (m' j1 - m' j2) 0 = (m j1 - m j2) 0 := by rw [h_sub, h_zr0]
      rw [h]; exact h_diffs.2.2.1
    have h_m1' : |(m' j1 - m' j2) 1| ≤ δ / 200 := by
      have h_sub : m' j1 - m' j2 = zReflect (m j1 - m j2) := by
        rw [h_m'_eq j1, h_m'_eq j2, ←zReflect.map_sub]
      have h : (m' j1 - m' j2) 1 = (m j1 - m j2) 1 := by rw [h_sub, h_zr1]
      rw [h]; exact h_diffs.2.2.2.1
    have h_m2' : |(m' j1 - m' j2) 2| ≤ 1 / 3200 := by
      have h_sub : m' j1 - m' j2 = zReflect (m j1 - m j2) := by
        rw [h_m'_eq j1, h_m'_eq j2, ←zReflect.map_sub]
      have h : (m' j1 - m' j2) 2 = -((m j1 - m j2) 2) := by
        rw [h_sub, h_zr2] <;> ring
      rw [h, abs_neg]; exact h_diffs.2.2.2.2
    have h_u0' : |(u' j1 - u' j2) 0| ≤ δ / 200 := by
      have h_sub : u' j1 - u' j2 = zReflect (u j1 - u j2) := by
        rw [h_u'_eq j1, h_u'_eq j2, ←zReflect.map_sub]
      have h : (u' j1 - u' j2) 0 = (u j1 - u j2) 0 := by rw [h_sub, h_zr0]
      rw [h]; exact h_diffs.1
    have h_u1' : |(u' j1 - u' j2) 1| ≤ δ / 200 := by
      have h_sub : u' j1 - u' j2 = zReflect (u j1 - u j2) := by
        rw [h_u'_eq j1, h_u'_eq j2, ←zReflect.map_sub]
      have h : (u' j1 - u' j2) 1 = (u j1 - u j2) 1 := by rw [h_sub, h_zr1]
      rw [h]; exact h_diffs.2.1
    have h_nd : ¬ (source.tube j1).EssentiallyDistinct (source.tube j2) :=
      close_params_not_distinct hδ (by linarith) frame'
        (m' j1) (m' j2) (u' j1) (u' j2)
        rfl rfl rfl rfl
        h_u1_pos' h_u2_pos' h_u2_0 h_u2_1
        h_m0' h_m1' h_m2' h_u0' h_u1'
        h_capsule_lower h_capsule_upper
    exact h_nd (hdistinct j1 j2 hne)

  have h_cell_bounds : ∀ j ∈ indices,
      Int.floor ((u j 0) / c_trans) ∈ Finset.Icc (-800 : ℤ) 800 ∧
      Int.floor ((u j 1) / c_trans) ∈ Finset.Icc (-800 : ℤ) 800 ∧
      Int.floor (((m j - p_i) 0) / c_trans) ∈ Finset.Icc (-400 : ℤ) 400 ∧
      Int.floor (((m j - p_i) 1) / c_trans) ∈ Finset.Icc (-400 : ℤ) 400 ∧
      Int.floor (((m j - p_i) 2) / c_long) ∈ Finset.Icc (-1664 : ℤ) 4864 := by
    intro j hj
    have h_p := h_params j hj
    have h_u0_l : -4 * δ ≤ u j 0 := by linarith [abs_le.mp h_p.1]
    have h_u0_u : u j 0 ≤ 4 * δ := by linarith [abs_le.mp h_p.1]
    have h_u1_l : -4 * δ ≤ u j 1 := by linarith [abs_le.mp h_p.2.1]
    have h_u1_u : u j 1 ≤ 4 * δ := by linarith [abs_le.mp h_p.2.1]
    have h_m0_l : -2 * δ ≤ (m j - p_i) 0 := by linarith [abs_le.mp h_p.2.2.2.1]
    have h_m0_u : (m j - p_i) 0 ≤ 2 * δ := by linarith [abs_le.mp h_p.2.2.2.1]
    have h_m1_l : -2 * δ ≤ (m j - p_i) 1 := by linarith [abs_le.mp h_p.2.2.2.2.1]
    have h_m1_u : (m j - p_i) 1 ≤ 2 * δ := by linarith [abs_le.mp h_p.2.2.2.2.1]
    have h_m2_l : -1 / 2 - 2 * δ ≤ (m j - p_i) 2 := h_p.2.2.2.2.2.1
    have h_m2_u : (m j - p_i) 2 ≤ 3 / 2 + 2 * δ := h_p.2.2.2.2.2.2
    have h_div_u0_l : (-800 : ℝ) ≤ (u j 0) / c_trans := by
      have h : c_trans = δ / 200 := by rfl
      rw [h]
      calc (u j 0) / (δ / 200)
        ≥ (-4 * δ) / (δ / 200) := by gcongr
      _ = -800 := by field_simp [hδ.ne'] <;> ring
    have h_div_u0_u : (u j 0) / c_trans ≤ (800 : ℝ) := by
      have h : c_trans = δ / 200 := by rfl
      rw [h]
      calc (u j 0) / (δ / 200)
        ≤ (4 * δ) / (δ / 200) := by gcongr
      _ = 800 := by field_simp [hδ.ne'] <;> ring
    have h_div_u1_l : (-800 : ℝ) ≤ (u j 1) / c_trans := by
      have h : c_trans = δ / 200 := by rfl
      rw [h]
      calc (u j 1) / (δ / 200)
        ≥ (-4 * δ) / (δ / 200) := by gcongr
      _ = -800 := by field_simp [hδ.ne'] <;> ring
    have h_div_u1_u : (u j 1) / c_trans ≤ (800 : ℝ) := by
      have h : c_trans = δ / 200 := by rfl
      rw [h]
      calc (u j 1) / (δ / 200)
        ≤ (4 * δ) / (δ / 200) := by gcongr
      _ = 800 := by field_simp [hδ.ne'] <;> ring
    have h_div_m0_l : (-400 : ℝ) ≤ ((m j - p_i) 0) / c_trans := by
      have h : c_trans = δ / 200 := by rfl
      rw [h]
      calc ((m j - p_i) 0) / (δ / 200)
        ≥ (-2 * δ) / (δ / 200) := by gcongr
      _ = -400 := by field_simp [hδ.ne'] <;> ring
    have h_div_m0_u : ((m j - p_i) 0) / c_trans ≤ (400 : ℝ) := by
      have h : c_trans = δ / 200 := by rfl
      rw [h]
      calc ((m j - p_i) 0) / (δ / 200)
        ≤ (2 * δ) / (δ / 200) := by gcongr
      _ = 400 := by field_simp [hδ.ne'] <;> ring
    have h_div_m1_l : (-400 : ℝ) ≤ ((m j - p_i) 1) / c_trans := by
      have h : c_trans = δ / 200 := by rfl
      rw [h]
      calc ((m j - p_i) 1) / (δ / 200)
        ≥ (-2 * δ) / (δ / 200) := by gcongr
      _ = -400 := by field_simp [hδ.ne'] <;> ring
    have h_div_m1_u : ((m j - p_i) 1) / c_trans ≤ (400 : ℝ) := by
      have h : c_trans = δ / 200 := by rfl
      rw [h]
      calc ((m j - p_i) 1) / (δ / 200)
        ≤ (2 * δ) / (δ / 200) := by gcongr
      _ = 400 := by field_simp [hδ.ne'] <;> ring
    have h_div_m2_l : (-1664 : ℝ) ≤ ((m j - p_i) 2) / c_long := by
      have h : c_long = 1 / 3200 := by rfl
      rw [h]
      have h' : -1 / 2 - 2 * δ ≤ (m j - p_i) 2 := h_m2_l
      have h'' : (-1664 : ℝ) ≤ (-1 / 2 - 2 * δ) / (1 / 3200 : ℝ) := by
        have hδ' : δ ≤ 1 / 100 := hδ_small
        field_simp <;> linarith
      linarith
    have h_div_m2_u : ((m j - p_i) 2) / c_long ≤ (4864 : ℝ) := by
      have h : c_long = 1 / 3200 := by rfl
      rw [h]
      have h' : (m j - p_i) 2 ≤ 3 / 2 + 2 * δ := h_m2_u
      have h'' : (3 / 2 + 2 * δ) / (1 / 3200 : ℝ) ≤ (4864 : ℝ) := by
        have hδ' : δ ≤ 1 / 100 := hδ_small
        field_simp <;> linarith
      linarith
    have h_fl1 : Int.floor ((u j 0) / c_trans) ∈ Finset.Icc (-800 : ℤ) 800 := by
      have h_lower : (-800 : ℤ) ≤ Int.floor ((u j 0) / c_trans) := by
        have h : ((-800 : ℤ) : ℝ) ≤ (u j 0) / c_trans := by exact_mod_cast h_div_u0_l
        exact (Int.le_floor).mpr h
      have h_upper : Int.floor ((u j 0) / c_trans) ≤ (800 : ℤ) := by
        have h : (Int.floor ((u j 0) / c_trans) : ℝ) ≤ (u j 0) / c_trans := Int.floor_le _
        have h' : (Int.floor ((u j 0) / c_trans) : ℝ) ≤ (800 : ℝ) := by linarith
        exact_mod_cast h'
      exact Finset.mem_Icc.mpr ⟨h_lower, h_upper⟩
    have h_fl2 : Int.floor ((u j 1) / c_trans) ∈ Finset.Icc (-800 : ℤ) 800 := by
      have h_lower : (-800 : ℤ) ≤ Int.floor ((u j 1) / c_trans) := by
        have h : ((-800 : ℤ) : ℝ) ≤ (u j 1) / c_trans := by exact_mod_cast h_div_u1_l
        exact (Int.le_floor).mpr h
      have h_upper : Int.floor ((u j 1) / c_trans) ≤ (800 : ℤ) := by
        have h : (Int.floor ((u j 1) / c_trans) : ℝ) ≤ (u j 1) / c_trans := Int.floor_le _
        have h' : (Int.floor ((u j 1) / c_trans) : ℝ) ≤ (800 : ℝ) := by linarith
        exact_mod_cast h'
      exact Finset.mem_Icc.mpr ⟨h_lower, h_upper⟩
    have h_fl3 : Int.floor (((m j - p_i) 0) / c_trans) ∈ Finset.Icc (-400 : ℤ) 400 := by
      have h_lower : (-400 : ℤ) ≤ Int.floor (((m j - p_i) 0) / c_trans) := by
        have h : ((-400 : ℤ) : ℝ) ≤ ((m j - p_i) 0) / c_trans := by exact_mod_cast h_div_m0_l
        exact (Int.le_floor).mpr h
      have h_upper : Int.floor (((m j - p_i) 0) / c_trans) ≤ (400 : ℤ) := by
        have h : (Int.floor (((m j - p_i) 0) / c_trans) : ℝ) ≤ ((m j - p_i) 0) / c_trans := Int.floor_le _
        have h' : (Int.floor (((m j - p_i) 0) / c_trans) : ℝ) ≤ (400 : ℝ) := by linarith
        exact_mod_cast h'
      exact Finset.mem_Icc.mpr ⟨h_lower, h_upper⟩
    have h_fl4 : Int.floor (((m j - p_i) 1) / c_trans) ∈ Finset.Icc (-400 : ℤ) 400 := by
      have h_lower : (-400 : ℤ) ≤ Int.floor (((m j - p_i) 1) / c_trans) := by
        have h : ((-400 : ℤ) : ℝ) ≤ ((m j - p_i) 1) / c_trans := by exact_mod_cast h_div_m1_l
        exact (Int.le_floor).mpr h
      have h_upper : Int.floor (((m j - p_i) 1) / c_trans) ≤ (400 : ℤ) := by
        have h : (Int.floor (((m j - p_i) 1) / c_trans) : ℝ) ≤ ((m j - p_i) 1) / c_trans := Int.floor_le _
        have h' : (Int.floor (((m j - p_i) 1) / c_trans) : ℝ) ≤ (400 : ℝ) := by linarith
        exact_mod_cast h'
      exact Finset.mem_Icc.mpr ⟨h_lower, h_upper⟩
    have h_fl5 : Int.floor (((m j - p_i) 2) / c_long) ∈ Finset.Icc (-1664 : ℤ) 4864 := by
      have h_lower : (-1664 : ℤ) ≤ Int.floor (((m j - p_i) 2) / c_long) := by
        have h : ((-1664 : ℤ) : ℝ) ≤ ((m j - p_i) 2) / c_long := by exact_mod_cast h_div_m2_l
        exact (Int.le_floor).mpr h
      have h_upper : Int.floor (((m j - p_i) 2) / c_long) ≤ (4864 : ℤ) := by
        have h : (Int.floor (((m j - p_i) 2) / c_long) : ℝ) ≤ ((m j - p_i) 2) / c_long := Int.floor_le _
        have h' : (Int.floor (((m j - p_i) 2) / c_long) : ℝ) ≤ (4864 : ℝ) := by linarith
        exact_mod_cast h'
      exact Finset.mem_Icc.mpr ⟨h_lower, h_upper⟩
    exact ⟨h_fl1, h_fl2, h_fl3, h_fl4, h_fl5⟩

  let cellRange : Finset (ℤ × (ℤ × (ℤ × (ℤ × ℤ)))) :=
    (Finset.Icc (-800 : ℤ) 800) ×ˢ
    ((Finset.Icc (-800 : ℤ) 800) ×ˢ
      ((Finset.Icc (-400 : ℤ) 400) ×ˢ
        ((Finset.Icc (-400 : ℤ) 400) ×ˢ
          (Finset.Icc (-1664 : ℤ) 4864))))

  have h_image_sub : ∀ (s : Finset (Fin source.card)), s ⊆ indices →
      Finset.image cell s ⊆ cellRange := by
    intro s hs
    rw [Finset.image_subset_iff]
    intro j hj
    have hj' : j ∈ indices := hs hj
    have h_bounds := h_cell_bounds j hj'
    have h1 := h_bounds.1
    have h2 := h_bounds.2.1
    have h3 := h_bounds.2.2.1
    have h4 := h_bounds.2.2.2.1
    have h5 := h_bounds.2.2.2.2
    rw [Finset.mem_product]
    exact ⟨h1, by
      rw [Finset.mem_product]
      exact ⟨h2, by
        rw [Finset.mem_product]
        exact ⟨h3, by
          rw [Finset.mem_product]
          exact ⟨h4, h5⟩⟩⟩⟩

  have h_card_range : cellRange.card = 1601 * 1601 * 801 * 801 * 6529 := by
    simp [cellRange, Finset.card_product, Finset.Icc_eq_empty_of_lt]
    <;> norm_num

  have h_pos_card : indices_pos.card ≤ cellRange.card := by
    have h1 : (Finset.image cell indices_pos).card = indices_pos.card :=
      Finset.card_image_of_injOn h_pos_inj
    have h2 : Finset.image cell indices_pos ⊆ cellRange := h_image_sub indices_pos (by simp [indices_pos] <;> tauto)
    rw [←h1]
    exact Finset.card_le_card h2

  have h_neg_card : indices_neg.card ≤ cellRange.card := by
    have h1 : (Finset.image cell indices_neg).card = indices_neg.card :=
      Finset.card_image_of_injOn h_neg_inj
    have h2 : Finset.image cell indices_neg ⊆ cellRange := h_image_sub indices_neg (by simp [indices_neg] <;> tauto)
    rw [←h1]
    exact Finset.card_le_card h2

  have h_main : indices.card ≤ indices_pos.card + indices_neg.card := by
    have h : indices ⊆ indices_pos ∪ indices_neg := h_cover
    have h2 : indices.card ≤ (indices_pos ∪ indices_neg).card := Finset.card_le_card h
    have h3 : (indices_pos ∪ indices_neg).card ≤ indices_pos.card + indices_neg.card :=
      Finset.card_union_le _ _
    linarith

  have h_final : indices.card ≤ 2 * cellRange.card := by linarith

  rw [h_card_range] at h_final
  have h_goal : 2 * (1601 * 1601 * 801 * 801 * 6529) ≤ gwzForwardConflictDegree δ := by
    simp [gwzForwardConflictDegree] <;> norm_num
  exact h_final.trans h_goal

end Kakeya.Assouad

end
