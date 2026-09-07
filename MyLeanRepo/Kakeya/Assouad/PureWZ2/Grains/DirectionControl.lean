import MyLeanRepo.Kakeya.Assouad.WZ1.PlaneProjectionPerturbation
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2PaperStatements
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.BaseConfig
import Mathlib.Tactic

/-!
# Direction control for paper tube shadings

Combines the WZ1 plane-projection perturbation lemma with the cubical property
of paper tube shadings to prove that a weak plane map is stable (up to sign)
across points in the same grid cube.

This is the key direction-control hypothesis for the finite-scale Lipschitz
plane-map assembly.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/--
If two points lie in the same grid cube of a cubical paper shading, they
belong to exactly the same set of carriers.
-/
lemma paper_cubical_same_cell_same_carriers
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    (hS_cubical : WZ1PaperIsCubicalShading S)
    (p q : Point3)
    (hcell : wz1PaperGridIndex delta p = wz1PaperGridIndex delta q) :
    ∀ (i : Fin F.card), p ∈ S.carrier i ↔ q ∈ S.carrier i := by
  intro i
  constructor
  · -- p ∈ carrier i → q ∈ carrier i
    intro hp
    have hcube : wz1PaperGridCube delta (wz1PaperGridIndex delta p) ⊆ S.carrier i :=
      hS_cubical i p hp
    have hq_in_cube : q ∈ wz1PaperGridCube delta (wz1PaperGridIndex delta p) := by
      rw [hcell]
      <;> simp [mem_wz1PaperGridCube]
    exact hcube hq_in_cube
  · -- q ∈ carrier i → p ∈ carrier i
    intro hq
    have hcube : wz1PaperGridCube delta (wz1PaperGridIndex delta q) ⊆ S.carrier i :=
      hS_cubical i q hq
    have hp_in_cube : p ∈ wz1PaperGridCube delta (wz1PaperGridIndex delta q) := by
      rw [←hcell]
      <;> simp [mem_wz1PaperGridCube]
    exact hcube hp_in_cube

/--
Direction control within a single grid cube.

Given a unit-normal plane map `V` with incidence bound `I` on a cubical paper
shading, and a transverse pair `(u, v)` of tube directions through `p` with
cross-product norm at least `kappa`, any other point `q` in the same grid cube
satisfies: there exists a sign `±1` such that
`‖V q - sign * normalize(cross(u,v))‖ ≤ 10 * I / kappa`.

This follows from the cubical property (same cell → same carriers) and the
WZ1 plane-projection perturbation lemma.
-/
theorem paper_direction_control_same_cell
    {delta I kappa : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    (hS_cubical : WZ1PaperIsCubicalShading S)
    (V : Point3 → Point3)
    (hV_unit : ∀ p ∈ S.union, ‖V p‖ = 1)
    (hV_inc : ∀ i p, p ∈ S.carrier i →
      |inner ℝ (F.tube i).direction (V p)| ≤ I)
    (p q : Point3) (hp : p ∈ S.union) (hq : q ∈ S.union)
    (hcell : wz1PaperGridIndex delta p = wz1PaperGridIndex delta q)
    (u v : Point3)
    (hu_norm : ‖u‖ = 1) (hv_norm : ‖v‖ = 1)
    (hkappa_pos : 0 < kappa)
    (hkappa : kappa ≤ ‖wz1Cross u v‖)
    (hu_at_p : ∃ i : Fin F.card, p ∈ S.carrier i ∧ (F.tube i).direction = u)
    (hv_at_p : ∃ j : Fin F.card, p ∈ S.carrier j ∧ (F.tube j).direction = v) :
    ∃ (sign : ℝ), (sign = 1 ∨ sign = -1) ∧
      ‖V q - sign • ((‖wz1Cross u v‖)⁻¹ • wz1Cross u v)‖ ≤ 10 * I / kappa := by
  have hcarriers : ∀ (i : Fin F.card), p ∈ S.carrier i ↔ q ∈ S.carrier i :=
    paper_cubical_same_cell_same_carriers hS_cubical p q hcell
  rcases hu_at_p with ⟨i, hpi, rfl⟩
  rcases hv_at_p with ⟨j, hpj, rfl⟩
  have hqi : q ∈ S.carrier i := (hcarriers i).mp hpi
  have hqj : q ∈ S.carrier j := (hcarriers j).mp hpj
  have h_inc_u : |inner ℝ (F.tube i).direction (V q)| ≤ I := hV_inc i q hqi
  have h_inc_v : |inner ℝ (F.tube j).direction (V q)| ≤ I := hV_inc j q hqj
  have h_inc_u' : |inner ℝ (V q) (F.tube i).direction| ≤ I := by
    have h : inner ℝ (V q) (F.tube i).direction = inner ℝ (F.tube i).direction (V q) :=
      Eq.symm (real_inner_comm (V q) (F.tube i).direction)
    rw [h]
    exact h_inc_u
  have h_inc_v' : |inner ℝ (V q) (F.tube j).direction| ≤ I := by
    have h : inner ℝ (V q) (F.tube j).direction = inner ℝ (F.tube j).direction (V q) :=
      Eq.symm (real_inner_comm (V q) (F.tube j).direction)
    rw [h]
    exact h_inc_v
  have hq_unit : ‖V q‖ = 1 := hV_unit q hq
  exact wz1_plane_projection_perturbation
    (F.tube i).direction (F.tube j).direction (V q)
    (F.tube i).direction_unit (F.tube j).direction_unit hq_unit
    kappa I hkappa_pos (show 0 ≤ I from by
      have h : 0 ≤ |inner ℝ (F.tube i).direction (V q)| := abs_nonneg _
      linarith [h_inc_u])
    hkappa h_inc_u' h_inc_v'

/--
Direction overlap lemma: two unit vectors both nearly orthogonal to the same
transverse pair must be close to each other or to each other's negation.

Given transverse directions `u, v` with cross-product norm at least `kappa`,
and two unit plane-map directions `w1, w2` each with incidence at most `I`
to both `u` and `v`, then either `dist(w1, w2) ≤ 20*I/kappa` or
`dist(w1, -w2) ≤ 20*I/kappa`.

This is the key geometric lemma for one-scale plane-map variation: nearby
cells sharing a common transverse pair have plane-map directions that agree
up to a globally resolvable sign ambiguity.
-/
theorem direction_overlap_common_transverse_pair
    {u v w1 w2 : Point3} {I kappa : ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hw1 : ‖w1‖ = 1) (hw2 : ‖w2‖ = 1)
    (hkappa_pos : 0 < kappa)
    (hkappa : kappa ≤ ‖wz1Cross u v‖)
    (hI_nonneg : 0 ≤ I)
    (h1u : |inner ℝ u w1| ≤ I) (h1v : |inner ℝ v w1| ≤ I)
    (h2u : |inner ℝ u w2| ≤ I) (h2v : |inner ℝ v w2| ≤ I) :
    (dist w1 w2 ≤ 20 * I / kappa) ∨ (dist w1 (-w2) ≤ 20 * I / kappa) := by
  let n : Point3 := wz1Cross u v
  let n_hat : Point3 := (‖n‖)⁻¹ • n
  have hN_pos : 0 < ‖n‖ := by
    exact lt_of_lt_of_le hkappa_pos hkappa
  have h_n_hat_norm : ‖n_hat‖ = 1 := by
    rw [show n_hat = (‖n‖)⁻¹ • n from rfl, norm_smul, Real.norm_eq_abs]
    have h1 : |(‖n‖)⁻¹| = (‖n‖)⁻¹ := by
      apply abs_of_pos
      exact inv_pos.mpr hN_pos
    rw [h1]
    field_simp [hN_pos.ne'] <;> ring
  have h1u' : |inner ℝ w1 u| ≤ I := by
    have h : inner ℝ w1 u = inner ℝ u w1 := (real_inner_comm w1 u).symm
    rw [h]
    exact h1u
  have h1v' : |inner ℝ w1 v| ≤ I := by
    have h : inner ℝ w1 v = inner ℝ v w1 := (real_inner_comm w1 v).symm
    rw [h]
    exact h1v
  have h2u' : |inner ℝ w2 u| ≤ I := by
    have h : inner ℝ w2 u = inner ℝ u w2 := (real_inner_comm w2 u).symm
    rw [h]
    exact h2u
  have h2v' : |inner ℝ w2 v| ≤ I := by
    have h : inner ℝ w2 v = inner ℝ v w2 := (real_inner_comm w2 v).symm
    rw [h]
    exact h2v
  rcases wz1_plane_projection_perturbation u v w1 hu hv hw1 kappa I hkappa_pos hI_nonneg hkappa h1u' h1v'
    with ⟨sign1, hsign1, hdist1⟩
  rcases wz1_plane_projection_perturbation u v w2 hu hv hw2 kappa I hkappa_pos hI_nonneg hkappa h2u' h2v'
    with ⟨sign2, hsign2, hdist2⟩
  let n1 := sign1 • n_hat
  let n2 := sign2 • n_hat
  have h1 : ‖w1 - n1‖ ≤ 10 * I / kappa := by simpa [n1] using hdist1
  have h2 : ‖w2 - n2‖ ≤ 10 * I / kappa := by simpa [n2] using hdist2
  have hsign1_sq : sign1 ^ 2 = 1 := by
    rcases hsign1 with (h | h) <;> rw [h] <;> norm_num
  have hsign2_sq : sign2 ^ 2 = 1 := by
    rcases hsign2 with (h | h) <;> rw [h] <;> norm_num
  by_cases h : sign1 = sign2
  · -- Same sign: n1 = n2
    left
    have hn : n1 = n2 := by
      simp [n1, n2, h]
    rw [hn] at h1
    have h_tri : ‖w1 - w2‖ ≤ ‖w1 - n2‖ + ‖w2 - n2‖ := by
      have h_eq : w1 - w2 = (w1 - n2) + (n2 - w2) := by abel
      rw [h_eq]
      have h : ‖(w1 - n2) + (n2 - w2)‖ ≤ ‖w1 - n2‖ + ‖n2 - w2‖ := norm_add_le _ _
      have h2' : ‖n2 - w2‖ = ‖w2 - n2‖ := by
        have h3 : n2 - w2 = -(w2 - n2) := by abel
        rw [h3, norm_neg]
      rw [h2'] at h
      exact h
    calc dist w1 w2
        = ‖w1 - w2‖ := by rw [dist_eq_norm]
      _ ≤ ‖w1 - n2‖ + ‖w2 - n2‖ := h_tri
      _ ≤ 10 * I / kappa + 10 * I / kappa := by gcongr
      _ = 20 * I / kappa := by ring
  · -- Different sign: n1 = -n2
    right
    have hsign : sign1 = -sign2 := by
      have h1 : sign1 ^ 2 = sign2 ^ 2 := by rw [hsign1_sq, hsign2_sq]
      have h2 : (sign1 - sign2) * (sign1 + sign2) = 0 := by linarith
      have h3 : sign1 - sign2 ≠ 0 := by
        intro h4
        have h5 : sign1 = sign2 := by linarith
        exact h h5
      have h4 : sign1 + sign2 = 0 := by
        apply (mul_eq_zero.mp h2).resolve_left h3
      linarith
    have hn : n1 = -n2 := by
      simp [n1, n2, hsign] <;> abel
    rw [hn] at h1
    have h5 : (-n2) - (-w2) = w2 - n2 := by abel
    have h_tri : ‖w1 - (-w2)‖ ≤ ‖w1 - (-n2)‖ + ‖w2 - n2‖ := by
      have h_eq : w1 - (-w2) = (w1 - (-n2)) + ((-n2) - (-w2)) := by abel
      rw [h_eq, h5]
      exact norm_add_le _ _
    calc dist w1 (-w2)
        = ‖w1 - (-w2)‖ := by rw [dist_eq_norm]
      _ ≤ ‖w1 - (-n2)‖ + ‖w2 - n2‖ := h_tri
      _ ≤ 10 * I / kappa + 10 * I / kappa := by gcongr
      _ = 20 * I / kappa := by ring

/--
Cross-product norm bound: `‖wz1Cross a b‖ ≤ ‖a‖ * ‖b‖`.
-/
lemma cross_product_norm_bound (a b : Point3) :
    ‖wz1Cross a b‖ ≤ ‖a‖ * ‖b‖ := by
  have h : ‖wz1Cross a b‖ = ‖a‖ * ‖b‖ * Real.sin (InnerProductGeometry.angle a b) :=
    InnerProductGeometry.norm_ofLp_crossProduct a b
  rw [h]
  have hsin : Real.sin (InnerProductGeometry.angle a b) ≤ 1 := Real.sin_le_one _
  have hnonneg : 0 ≤ ‖a‖ * ‖b‖ := by positivity
  nlinarith

/--
Lipschitz bound for the cross product:
`‖cross(a,b) - cross(a',b')‖ ≤ ‖a-a'‖*‖b‖ + ‖a'‖*‖b-b'‖`.
-/
lemma cross_product_lipschitz (a a' b b' : Point3) :
    ‖wz1Cross a b - wz1Cross a' b'‖ ≤
      ‖a - a'‖ * ‖b‖ + ‖a'‖ * ‖b - b'‖ := by
  have h_add1 : wz1Cross a b = wz1Cross a' b + wz1Cross (a - a') b := by
    unfold wz1Cross
    have h_eq : (a : Fin 3 → ℝ) = (a' : Fin 3 → ℝ) + ((a - a') : Fin 3 → ℝ) := by
      ext i; simp [sub_add_cancel]
    rw [h_eq]
    have h2 : crossProduct ((a' : Fin 3 → ℝ) + ((a - a') : Fin 3 → ℝ)) (b : Fin 3 → ℝ) =
        crossProduct (a' : Fin 3 → ℝ) (b : Fin 3 → ℝ) +
        crossProduct ((a - a') : Fin 3 → ℝ) (b : Fin 3 → ℝ) := by
      have h3 := crossProduct.map_add (a' : Fin 3 → ℝ) ((a - a') : Fin 3 → ℝ)
      simpa [h3] using rfl
    rw [h2] <;> rfl
  have h_add2 : wz1Cross a' b = wz1Cross a' b' + wz1Cross a' (b - b') := by
    unfold wz1Cross
    have h_eq : (b : Fin 3 → ℝ) = (b' : Fin 3 → ℝ) + ((b - b') : Fin 3 → ℝ) := by
      ext i; simp [sub_add_cancel]
    rw [h_eq]
    have h2 : crossProduct (a' : Fin 3 → ℝ) ((b' : Fin 3 → ℝ) + ((b - b') : Fin 3 → ℝ)) =
        crossProduct (a' : Fin 3 → ℝ) (b' : Fin 3 → ℝ) +
        crossProduct (a' : Fin 3 → ℝ) ((b - b') : Fin 3 → ℝ) := by
      have h3 := (crossProduct (a' : Fin 3 → ℝ)).map_add (b' : Fin 3 → ℝ) ((b - b') : Fin 3 → ℝ)
      simpa [h3] using rfl
    rw [h2] <;> rfl
  have h_main : wz1Cross a b - wz1Cross a' b' =
      wz1Cross (a - a') b + wz1Cross a' (b - b') := by
    rw [h_add1, h_add2] <;> abel
  rw [h_main]
  have h1 : ‖wz1Cross (a - a') b + wz1Cross a' (b - b')‖ ≤
      ‖wz1Cross (a - a') b‖ + ‖wz1Cross a' (b - b')‖ := norm_add_le _ _
  have h2 : ‖wz1Cross (a - a') b‖ ≤ ‖a - a'‖ * ‖b‖ := cross_product_norm_bound (a - a') b
  have h3 : ‖wz1Cross a' (b - b')‖ ≤ ‖a'‖ * ‖b - b'‖ := cross_product_norm_bound a' (b - b')
  linarith

/--
Continuity of normalized vectors:
`‖x/‖x‖ - y/‖y‖‖ ≤ 2*‖x-y‖ / min(‖x‖, ‖y‖)`.
-/
lemma normalized_vector_continuity {x y : Point3} (hx_pos : 0 < ‖x‖) (hy_pos : 0 < ‖y‖) :
    ‖(‖x‖)⁻¹ • x - (‖y‖)⁻¹ • y‖ ≤ 2 * ‖x - y‖ / min ‖x‖ ‖y‖ := by
  have h2 : (‖x‖)⁻¹ • (x - y) = (‖x‖)⁻¹ • x - (‖x‖)⁻¹ • y := by
    rw [smul_sub]
  have h3 : ((‖x‖)⁻¹ - (‖y‖)⁻¹) • y = (‖x‖)⁻¹ • y - (‖y‖)⁻¹ • y := by
    rw [sub_smul]
  have h1 : (‖x‖)⁻¹ • x - (‖y‖)⁻¹ • y = (‖x‖)⁻¹ • (x - y) + ((‖x‖)⁻¹ - (‖y‖)⁻¹) • y := by
    calc (‖x‖)⁻¹ • x - (‖y‖)⁻¹ • y
        = ((‖x‖)⁻¹ • x - (‖x‖)⁻¹ • y) + ((‖x‖)⁻¹ • y - (‖y‖)⁻¹ • y) := by abel
      _ = (‖x‖)⁻¹ • (x - y) + ((‖x‖)⁻¹ - (‖y‖)⁻¹) • y := by
        rw [←h2, ←h3] <;> abel
  have h4 : ‖(‖x‖)⁻¹ • x - (‖y‖)⁻¹ • y‖ ≤
      ‖(‖x‖)⁻¹ • (x - y)‖ + ‖((‖x‖)⁻¹ - (‖y‖)⁻¹) • y‖ := by
    rw [h1]
    exact norm_add_le _ _
  have h5 : ‖(‖x‖)⁻¹ • (x - y)‖ = (‖x‖)⁻¹ * ‖x - y‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hx_pos] <;> ring
  have h6 : ‖((‖x‖)⁻¹ - (‖y‖)⁻¹) • y‖ = |(‖x‖)⁻¹ - (‖y‖)⁻¹| * ‖y‖ := by
    rw [norm_smul, Real.norm_eq_abs] <;> ring
  have h7 : |(‖x‖)⁻¹ - (‖y‖)⁻¹| * ‖y‖ = |‖y‖ - ‖x‖| / ‖x‖ := by
    have h71 : (‖x‖)⁻¹ - (‖y‖)⁻¹ = (‖y‖ - ‖x‖) / (‖x‖ * ‖y‖) := by
      field_simp [hx_pos.ne', hy_pos.ne'] <;> ring
    have h72 : |(‖x‖)⁻¹ - (‖y‖)⁻¹| = |‖y‖ - ‖x‖| / (‖x‖ * ‖y‖) := by
      have hpos : 0 < ‖x‖ * ‖y‖ := mul_pos hx_pos hy_pos
      rw [h71, abs_div, abs_of_pos hpos] <;> ring
    calc |(‖x‖)⁻¹ - (‖y‖)⁻¹| * ‖y‖
        = (|‖y‖ - ‖x‖| / (‖x‖ * ‖y‖)) * ‖y‖ := by rw [h72]
      _ = |‖y‖ - ‖x‖| / ‖x‖ := by
        field_simp [hx_pos.ne', hy_pos.ne'] <;> ring
  have h81 : y + (x - y) = x := by abel
  have h82 : ‖x‖ ≤ ‖y‖ + ‖x - y‖ := by
    have h : ‖y + (x - y)‖ ≤ ‖y‖ + ‖x - y‖ := norm_add_le y (x - y)
    rw [h81] at h
    exact h
  have h83 : x + (y - x) = y := by abel
  have h84 : ‖y - x‖ = ‖x - y‖ := by
    have h : y - x = -(x - y) := by abel
    rw [h, norm_neg]
  have h85 : ‖y‖ ≤ ‖x‖ + ‖x - y‖ := by
    have h : ‖x + (y - x)‖ ≤ ‖x‖ + ‖y - x‖ := norm_add_le x (y - x)
    rw [h83, h84] at h
    exact h
  have h8 : |‖y‖ - ‖x‖| ≤ ‖x - y‖ := by
    rw [abs_le]
    constructor <;> linarith
  have h9 : ‖x‖ ≥ min ‖x‖ ‖y‖ := min_le_left ‖x‖ ‖y‖
  calc ‖(‖x‖)⁻¹ • x - (‖y‖)⁻¹ • y‖
      ≤ ‖(‖x‖)⁻¹ • (x - y)‖ + ‖((‖x‖)⁻¹ - (‖y‖)⁻¹) • y‖ := h4
    _ = (‖x‖)⁻¹ * ‖x - y‖ + |(‖x‖)⁻¹ - (‖y‖)⁻¹| * ‖y‖ := by rw [h5, h6]
    _ = ‖x - y‖ / ‖x‖ + |‖y‖ - ‖x‖| / ‖x‖ := by
      rw [h7] <;> field_simp [hx_pos.ne'] <;> ring
    _ ≤ ‖x - y‖ / ‖x‖ + ‖x - y‖ / ‖x‖ := by gcongr
    _ = 2 * ‖x - y‖ / ‖x‖ := by ring
    _ ≤ 2 * ‖x - y‖ / min ‖x‖ ‖y‖ := by
      gcongr
      <;> exact h9

/--
Continuity of the normalized cross product.

Given unit vectors `u, v, u', v'` with both cross products having norm at least
`kappa`, and `‖u-u'‖ ≤ eps`, `‖v-v'‖ ≤ eps`, then
`‖normalize(cross(u,v)) - normalize(cross(u',v'))‖ ≤ 4 * eps / kappa`.
-/
lemma normalized_cross_continuity
    (u v u' v' : Point3)
    (hu_norm : ‖u‖ = 1) (hv_norm : ‖v‖ = 1)
    (hu'_norm : ‖u'‖ = 1) (hv'_norm : ‖v'‖ = 1)
    (kappa : ℝ) (hkappa_pos : 0 < kappa)
    (hkappa : kappa ≤ ‖wz1Cross u v‖)
    (hkappa' : kappa ≤ ‖wz1Cross u' v'‖)
    (eps : ℝ) (heps_nonneg : 0 ≤ eps)
    (h_eps_u : ‖u - u'‖ ≤ eps)
    (h_eps_v : ‖v - v'‖ ≤ eps) :
    ‖(‖wz1Cross u v‖)⁻¹ • wz1Cross u v -
      (‖wz1Cross u' v'‖)⁻¹ • wz1Cross u' v'‖ ≤ 4 * eps / kappa := by
  set n := wz1Cross u v with hn_def
  set n' := wz1Cross u' v' with hn'_def
  have hn_pos : 0 < ‖n‖ := lt_of_lt_of_le hkappa_pos hkappa
  have hn'_pos : 0 < ‖n'‖ := lt_of_lt_of_le hkappa_pos hkappa'
  have h_diff : ‖n - n'‖ ≤ 2 * eps := by
    have h := cross_product_lipschitz u u' v v'
    have hb : ‖v‖ = 1 := hv_norm
    have hu' : ‖u'‖ = 1 := hu'_norm
    rw [hb, hu'] at h
    linarith [h_eps_u, h_eps_v]
  have hmin : kappa ≤ min ‖n‖ ‖n'‖ := by
    exact le_min hkappa hkappa'
  have h_main := normalized_vector_continuity hn_pos hn'_pos
  calc ‖(‖n‖)⁻¹ • n - (‖n'‖)⁻¹ • n'‖
      ≤ 2 * ‖n - n'‖ / min ‖n‖ ‖n'‖ := h_main
    _ ≤ 2 * ‖n - n'‖ / kappa := by
      gcongr
      <;> exact hmin
    _ ≤ 2 * (2 * eps) / kappa := by gcongr
    _ = 4 * eps / kappa := by ring

/--
Cross-cell direction overlap: two unit vectors in nearby cells, each with
small incidence to transverse pairs in their respective cells, are close
to each other or to each other's negation.

Given transverse pairs `(u1,v1)` at cell 1 and `(u2,v2)` at cell 2, with
both cross-product norms at least `kappa`, the transverse pairs within
`eps` of each other, and unit vectors `w1, w2` each with incidence at most
`I` to their respective transverse pairs, then either
`dist(w1, w2) ≤ 20*I/kappa + 4*eps/kappa` or
`dist(w1, -w2) ≤ 20*I/kappa + 4*eps/kappa`.

This is the cross-cell analogue of `direction_overlap_common_transverse_pair`.
-/
theorem direction_overlap_adjacent_cells
    {u1 v1 w1 u2 v2 w2 : Point3} {I kappa eps : ℝ}
    (hu1_norm : ‖u1‖ = 1) (hv1_norm : ‖v1‖ = 1)
    (hu2_norm : ‖u2‖ = 1) (hv2_norm : ‖v2‖ = 1)
    (hw1_norm : ‖w1‖ = 1) (hw2_norm : ‖w2‖ = 1)
    (hkappa_pos : 0 < kappa)
    (hkappa1 : kappa ≤ ‖wz1Cross u1 v1‖)
    (hkappa2 : kappa ≤ ‖wz1Cross u2 v2‖)
    (hI_nonneg : 0 ≤ I)
    (heps_nonneg : 0 ≤ eps)
    (h_eps_u : ‖u1 - u2‖ ≤ eps)
    (h_eps_v : ‖v1 - v2‖ ≤ eps)
    (h_inc1_u : |inner ℝ u1 w1| ≤ I)
    (h_inc1_v : |inner ℝ v1 w1| ≤ I)
    (h_inc2_u : |inner ℝ u2 w2| ≤ I)
    (h_inc2_v : |inner ℝ v2 w2| ≤ I) :
    dist w1 w2 ≤ 20 * I / kappa + 4 * eps / kappa ∨
    dist w1 (-w2) ≤ 20 * I / kappa + 4 * eps / kappa := by
  let n1 := (‖wz1Cross u1 v1‖)⁻¹ • wz1Cross u1 v1
  let n2 := (‖wz1Cross u2 v2‖)⁻¹ • wz1Cross u2 v2
  have hn1_pos : 0 < ‖wz1Cross u1 v1‖ :=
    lt_of_lt_of_le hkappa_pos hkappa1
  have hn1_unit : ‖n1‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos hn1_pos]
    field_simp [hn1_pos.ne'] <;> ring
  have hn2_pos : 0 < ‖wz1Cross u2 v2‖ :=
    lt_of_lt_of_le hkappa_pos hkappa2
  have hn2_unit : ‖n2‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos hn2_pos]
    field_simp [hn2_pos.ne'] <;> ring
  have hcross_cont : ‖n1 - n2‖ ≤ 4 * eps / kappa :=
    normalized_cross_continuity u1 v1 u2 v2
      hu1_norm hv1_norm hu2_norm hv2_norm kappa hkappa_pos
      hkappa1 hkappa2 eps heps_nonneg h_eps_u h_eps_v
  have h1 : ∃ (s1 : ℝ), (s1 = 1 ∨ s1 = -1) ∧ ‖w1 - s1 • n1‖ ≤ 10 * I / kappa :=
    have h_inc1_u' : |inner ℝ w1 u1| ≤ I := by
      have hcomm : inner ℝ w1 u1 = inner ℝ u1 w1 := Eq.symm (real_inner_comm w1 u1)
      rw [hcomm]
      exact h_inc1_u
    have h_inc1_v' : |inner ℝ w1 v1| ≤ I := by
      have hcomm : inner ℝ w1 v1 = inner ℝ v1 w1 := Eq.symm (real_inner_comm w1 v1)
      rw [hcomm]
      exact h_inc1_v
    wz1_plane_projection_perturbation u1 v1 w1
      hu1_norm hv1_norm hw1_norm kappa I hkappa_pos hI_nonneg hkappa1
      h_inc1_u' h_inc1_v'
  have h2 : ∃ (s2 : ℝ), (s2 = 1 ∨ s2 = -1) ∧ ‖w2 - s2 • n2‖ ≤ 10 * I / kappa :=
    have h_inc2_u' : |inner ℝ w2 u2| ≤ I := by
      have hcomm : inner ℝ w2 u2 = inner ℝ u2 w2 := Eq.symm (real_inner_comm w2 u2)
      rw [hcomm]
      exact h_inc2_u
    have h_inc2_v' : |inner ℝ w2 v2| ≤ I := by
      have hcomm : inner ℝ w2 v2 = inner ℝ v2 w2 := Eq.symm (real_inner_comm w2 v2)
      rw [hcomm]
      exact h_inc2_v
    wz1_plane_projection_perturbation u2 v2 w2
      hu2_norm hv2_norm hw2_norm kappa I hkappa_pos hI_nonneg hkappa2
      h_inc2_u' h_inc2_v'
  rcases h1 with ⟨s1, hs1_cases, hb1⟩
  rcases h2 with ⟨s2, hs2_cases, hb2⟩
  have h_cases : s1 = s2 ∨ s1 = -s2 := by
    rcases hs1_cases with (rfl | rfl) <;> rcases hs2_cases with (rfl | rfl) <;> norm_num
  rcases h_cases with (h_eq | h_neg)
  · -- s1 = s2: w1 ≈ s1·n1 ≈ s1·n2 ≈ w2
    have h_main : ‖w1 - w2‖ ≤ 10 * I / kappa + 4 * eps / kappa + 10 * I / kappa := by
      calc ‖w1 - w2‖
          ≤ ‖w1 - s1 • n1‖ + ‖s1 • n1 - s1 • n2‖ + ‖s1 • n2 - w2‖ := by
            have h : w1 - w2 = (w1 - s1 • n1) + (s1 • n1 - s1 • n2) + (s1 • n2 - w2) := by
              simp [h_eq] <;> abel
            rw [h]
            have h_tri : ‖(w1 - s1 • n1) + (s1 • n1 - s1 • n2) + (s1 • n2 - w2)‖ ≤
                ‖w1 - s1 • n1‖ + ‖s1 • n1 - s1 • n2‖ + ‖s1 • n2 - w2‖ := by
              calc ‖(w1 - s1 • n1) + (s1 • n1 - s1 • n2) + (s1 • n2 - w2)‖
                  ≤ ‖(w1 - s1 • n1) + (s1 • n1 - s1 • n2)‖ + ‖s1 • n2 - w2‖ := norm_add_le _ _
                _ ≤ ‖w1 - s1 • n1‖ + ‖s1 • n1 - s1 • n2‖ + ‖s1 • n2 - w2‖ := by
                  have h2 : ‖(w1 - s1 • n1) + (s1 • n1 - s1 • n2)‖ ≤ ‖w1 - s1 • n1‖ + ‖s1 • n1 - s1 • n2‖ := norm_add_le _ _
                  linarith
            exact h_tri
        _ = ‖w1 - s1 • n1‖ + |s1| * ‖n1 - n2‖ + ‖w2 - s2 • n2‖ := by
            have hsmul : ‖s1 • n1 - s1 • n2‖ = |s1| * ‖n1 - n2‖ := by
              rw [←smul_sub, norm_smul, Real.norm_eq_abs]
            have hlast : ‖s1 • n2 - w2‖ = ‖w2 - s2 • n2‖ := by
              rw [h_eq]
              have hrev : ‖s2 • n2 - w2‖ = ‖w2 - s2 • n2‖ := by
                have hneg : s2 • n2 - w2 = -(w2 - s2 • n2) := by abel
                rw [hneg, norm_neg]
              exact hrev
            rw [hsmul, hlast]
        _ ≤ 10 * I / kappa + 1 * (4 * eps / kappa) + 10 * I / kappa := by
            have hs1_abs : |s1| = 1 := by
              rcases hs1_cases with (rfl | rfl) <;> norm_num
            rw [hs1_abs] <;> gcongr
        _ = 10 * I / kappa + 4 * eps / kappa + 10 * I / kappa := by ring
    have h_sum : 10 * I / kappa + 4 * eps / kappa + 10 * I / kappa =
        20 * I / kappa + 4 * eps / kappa := by ring
    have h_final : ‖w1 - w2‖ ≤ 20 * I / kappa + 4 * eps / kappa := by
      rw [h_sum] at h_main
      exact h_main
    exact Or.inl (by simpa [dist_eq_norm] using h_final)
  · -- s1 = -s2: w1 ≈ s1·n1 ≈ s1·n2 ≈ -w2
    have h_main : ‖w1 - (-w2)‖ ≤ 10 * I / kappa + 4 * eps / kappa + 10 * I / kappa := by
      calc ‖w1 - (-w2)‖
          ≤ ‖w1 - s1 • n1‖ + ‖s1 • n1 - s1 • n2‖ + ‖s1 • n2 - (-w2)‖ := by
            have h : w1 - (-w2) = (w1 - s1 • n1) + (s1 • n1 - s1 • n2) + (s1 • n2 - (-w2)) := by
              simp [h_neg] <;> abel
            rw [h]
            have h_tri : ‖(w1 - s1 • n1) + (s1 • n1 - s1 • n2) + (s1 • n2 - (-w2))‖ ≤
                ‖w1 - s1 • n1‖ + ‖s1 • n1 - s1 • n2‖ + ‖s1 • n2 - (-w2)‖ := by
              calc ‖(w1 - s1 • n1) + (s1 • n1 - s1 • n2) + (s1 • n2 - (-w2))‖
                  ≤ ‖(w1 - s1 • n1) + (s1 • n1 - s1 • n2)‖ + ‖s1 • n2 - (-w2)‖ := norm_add_le _ _
                _ ≤ ‖w1 - s1 • n1‖ + ‖s1 • n1 - s1 • n2‖ + ‖s1 • n2 - (-w2)‖ := by
                  have h2 : ‖(w1 - s1 • n1) + (s1 • n1 - s1 • n2)‖ ≤ ‖w1 - s1 • n1‖ + ‖s1 • n1 - s1 • n2‖ := norm_add_le _ _
                  linarith
            exact h_tri
        _ = ‖w1 - s1 • n1‖ + |s1| * ‖n1 - n2‖ + ‖w2 - s2 • n2‖ := by
            have hsmul : ‖s1 • n1 - s1 • n2‖ = |s1| * ‖n1 - n2‖ := by
              rw [←smul_sub, norm_smul, Real.norm_eq_abs]
            have hlast : ‖s1 • n2 - (-w2)‖ = ‖w2 - s2 • n2‖ := by
              have h9 : s1 • n2 - (-w2) = w2 - s2 • n2 := by
                simp [h_neg, smul_neg, neg_smul] <;> abel
              rw [h9]
            rw [hsmul, hlast] <;> ring
        _ ≤ 10 * I / kappa + 1 * (4 * eps / kappa) + 10 * I / kappa := by
            have hs1_abs : |s1| = 1 := by
              rcases hs1_cases with (rfl | rfl) <;> norm_num
            rw [hs1_abs] <;> gcongr
        _ = 10 * I / kappa + 4 * eps / kappa + 10 * I / kappa := by ring
    have h_sum : 10 * I / kappa + 4 * eps / kappa + 10 * I / kappa =
        20 * I / kappa + 4 * eps / kappa := by ring
    have h_final : ‖w1 - (-w2)‖ ≤ 20 * I / kappa + 4 * eps / kappa := by
      rw [h_sum] at h_main
      exact h_main
    exact Or.inr (by simpa [dist_eq_norm] using h_final)

/--
Per-cell plane map construction from transverse pairs on a cubical shading.

Given a cubical paper shading `S` and a transverse-pair condition (for every point
and every tube through it, there exists another tube through it with cross-product
norm at least `kappa`), construct a cell-constant unit-norm plane map `W`.

For each grid cell, the minimum-index tube through the cell is selected as `i`,
and then the minimum-index tube transverse to `i` is selected as `j`. The plane
normal is `normalize(cross(direction i, direction j))`.

The map is constant on each grid cube (by the cubical property), has unit norm,
and has zero incidence with the selected pair `(i, j)`.
-/
theorem per_cell_plane_map_from_transverse
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    (hS_cubical : WZ1PaperIsCubicalShading S)
    (kappa : ℝ) (hkappa_pos : 0 < kappa)
    (htransverse : ∀ p ∈ S.union, ∀ i, p ∈ S.carrier i →
        ∃ j, p ∈ S.carrier j ∧
          kappa ≤ ‖wz1Cross (F.tube i).direction (F.tube j).direction‖) :
    ∃ (W : {p : Point3 // p ∈ S.union} → Point3)
      (selectedI selectedJ : {p : Point3 // p ∈ S.union} → Fin F.card),
      (∀ p, ‖W p‖ = 1) ∧
      (∀ (p q : {p : Point3 // p ∈ S.union}),
        wz1PaperGridIndex delta (p : Point3) = wz1PaperGridIndex delta (q : Point3) →
        W p = W q) ∧
      (∀ p, (p : Point3) ∈ S.carrier (selectedI p) ∧
               (p : Point3) ∈ S.carrier (selectedJ p)) ∧
      (∀ p, kappa ≤
        ‖wz1Cross (F.tube (selectedI p)).direction
                     (F.tube (selectedJ p)).direction‖) ∧
      (∀ p, inner ℝ (F.tube (selectedI p)).direction (W p) = 0 ∧
                inner ℝ (F.tube (selectedJ p)).direction (W p) = 0) ∧
      (∀ p, W p =
        (‖wz1Cross (F.tube (selectedI p)).direction
                         (F.tube (selectedJ p)).direction‖)⁻¹ •
        wz1Cross (F.tube (selectedI p)).direction
                     (F.tube (selectedJ p)).direction) := by
  classical
  let tubesAt (p : Point3) : Finset (Fin F.card) :=
    Finset.univ.filter fun i => p ∈ S.carrier i
  have h_tubes_nonempty : ∀ p ∈ S.union, (tubesAt p).Nonempty := by
    intro p hp
    rcases hp with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    simp only [tubesAt, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hi
  have h_tubes_const : ∀ (p q : Point3),
      wz1PaperGridIndex delta p = wz1PaperGridIndex delta q →
      tubesAt p = tubesAt q := by
    intro p q hcell
    ext i
    simp only [tubesAt, Finset.mem_filter, Finset.mem_univ, true_and]
    exact paper_cubical_same_cell_same_carriers hS_cubical p q hcell i
  let i (p : {p : Point3 // p ∈ S.union}) : Fin F.card :=
    (tubesAt (p : Point3)).min' (h_tubes_nonempty (p : Point3) p.prop)
  have hi_mem : ∀ (p : {p // p ∈ S.union}),
      (p : Point3) ∈ S.carrier (i p) := by
    intro p
    have h : i p ∈ tubesAt (p : Point3) :=
      Finset.min'_mem (tubesAt (p : Point3))
        (h_tubes_nonempty (p : Point3) p.prop)
    simp only [tubesAt, Finset.mem_filter, Finset.mem_univ, true_and] at h
    exact h
  let transverseTo (p : {p // p ∈ S.union}) : Finset (Fin F.card) :=
    (tubesAt (p : Point3)).filter fun j =>
      kappa ≤ ‖wz1Cross (F.tube (i p)).direction (F.tube j).direction‖
  have h_trans_nonempty : ∀ (p : {p // p ∈ S.union}),
      (transverseTo p).Nonempty := by
    intro p
    have h_exists := htransverse (p : Point3) p.prop (i p) (hi_mem p)
    rcases h_exists with ⟨j, hj_mem, hj_trans⟩
    refine ⟨j, ?_⟩
    simp only [transverseTo, Finset.mem_filter]
    have hj_in_tubes : j ∈ tubesAt (p : Point3) := by
      have h_goal : (p : Point3) ∈ S.carrier j := hj_mem
      have h : j ∈ (Finset.univ.filter fun i => (p : Point3) ∈ S.carrier i) := by
        rw [Finset.mem_filter]
        <;> exact ⟨Finset.mem_univ j, h_goal⟩
      exact h
    exact ⟨hj_in_tubes, hj_trans⟩
  let j (p : {p // p ∈ S.union}) : Fin F.card :=
    (transverseTo p).min' (h_trans_nonempty p)
  have hj_mem : ∀ (p : {p // p ∈ S.union}),
      (p : Point3) ∈ S.carrier (j p) := by
    intro p
    have h : j p ∈ transverseTo p :=
      Finset.min'_mem (transverseTo p) (h_trans_nonempty p)
    have h' : j p ∈ tubesAt (p : Point3) := by
      simp only [transverseTo, Finset.mem_filter] at h
      exact h.1
    simp only [tubesAt, Finset.mem_filter, Finset.mem_univ, true_and] at h'
    exact h'
  have hj_trans : ∀ (p : {p // p ∈ S.union}),
      kappa ≤ ‖wz1Cross (F.tube (i p)).direction
                       (F.tube (j p)).direction‖ := by
    intro p
    have h : j p ∈ transverseTo p :=
      Finset.min'_mem (transverseTo p) (h_trans_nonempty p)
    simp only [transverseTo, Finset.mem_filter] at h
    exact h.2
  let W (p : {p // p ∈ S.union}) : Point3 :=
    (‖wz1Cross (F.tube (i p)).direction
                     (F.tube (j p)).direction‖)⁻¹ •
    wz1Cross (F.tube (i p)).direction (F.tube (j p)).direction
  have hW_unit : ∀ p, ‖W p‖ = 1 := by
    intro p
    have hpos : 0 < ‖wz1Cross (F.tube (i p)).direction
                             (F.tube (j p)).direction‖ :=
      lt_of_lt_of_le hkappa_pos (hj_trans p)
    rw [show W p = (‖wz1Cross (F.tube (i p)).direction
                           (F.tube (j p)).direction‖)⁻¹ •
                 wz1Cross (F.tube (i p)).direction (F.tube (j p)).direction
      from rfl]
    rw [norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos hpos]
    field_simp [hpos.ne']
  have h_cell_const : ∀ (p q : {p // p ∈ S.union}),
      wz1PaperGridIndex delta (p : Point3) =
        wz1PaperGridIndex delta (q : Point3) →
      W p = W q := by
    intro p q hcell
    have h_tubes : tubesAt (p : Point3) = tubesAt (q : Point3) :=
      h_tubes_const (p : Point3) (q : Point3) hcell
    have hi_eq : i p = i q := by
      simp only [i, h_tubes]
    have h_trans_eq : transverseTo p = transverseTo q := by
      ext k
      simp only [transverseTo, Finset.mem_filter, hi_eq, h_tubes]
      <;> aesop
    have hj_eq : j p = j q := by
      dsimp only [j]
      congr 1
    simp only [W, hi_eq, hj_eq]
  have h_inner_i : ∀ p,
      inner ℝ (F.tube (i p)).direction (W p) = 0 := by
    intro p
    let u := (F.tube (i p)).direction
    let v := (F.tube (j p)).direction
    have h : inner ℝ u (wz1Cross u v) = 0 := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      have hstar : star (u : Fin 3 → ℝ) = (u : Fin 3 → ℝ) := by ext k; simp
      rw [hstar, dotProduct_comm]
      exact dot_self_cross (u : Fin 3 → ℝ) (v : Fin 3 → ℝ)
    have h2 : inner ℝ (F.tube (i p)).direction (W p) =
        (‖wz1Cross u v‖)⁻¹ * inner ℝ u (wz1Cross u v) := by
      simp only [W]
      <;> rw [inner_smul_right]
    rw [h2, h]
    <;> ring
  have h_inner_j : ∀ p,
      inner ℝ (F.tube (j p)).direction (W p) = 0 := by
    intro p
    let u := (F.tube (i p)).direction
    let v := (F.tube (j p)).direction
    have h : inner ℝ v (wz1Cross u v) = 0 := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      have hstar : star (v : Fin 3 → ℝ) = (v : Fin 3 → ℝ) := by ext k; simp
      rw [hstar, dotProduct_comm]
      exact dot_cross_self (u : Fin 3 → ℝ) (v : Fin 3 → ℝ)
    have h2 : inner ℝ (F.tube (j p)).direction (W p) =
        (‖wz1Cross u v‖)⁻¹ * inner ℝ v (wz1Cross u v) := by
      simp only [W]
      <;> rw [inner_smul_right]
    rw [h2, h]
    <;> ring
  exact ⟨W, i, j, hW_unit, h_cell_const,
    fun p => ⟨hi_mem p, hj_mem p⟩, hj_trans,
    fun p => ⟨h_inner_i p, h_inner_j p⟩,
    fun p => rfl⟩

/--
Existential-pair variant of `per_cell_plane_map_from_transverse`.

Instead of requiring that *every* tube through a point has a transverse partner,
this only requires that *some* transverse pair exists at each point. Both
indices are selected simultaneously from the set of transverse pairs using
`Classical.epsilon`, which is deterministic and cell-constant because the pair
set depends only on the grid cell.

This avoids the pointwise multiplicity lower bound that would be needed to
derive the universal condition from a global mass bound.
-/
theorem per_cell_plane_map_from_transverse_pair
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    (hS_cubical : WZ1PaperIsCubicalShading S)
    (kappa : ℝ) (hkappa_pos : 0 < kappa)
    (htransverse : ∀ p ∈ S.union,
      ∃ (i j : Fin F.card),
        p ∈ S.carrier i ∧ p ∈ S.carrier j ∧
          kappa ≤ ‖wz1Cross (F.tube i).direction (F.tube j).direction‖) :
    ∃ (W : {p : Point3 // p ∈ S.union} → Point3)
      (selectedI selectedJ : {p : Point3 // p ∈ S.union} → Fin F.card),
      (∀ p, ‖W p‖ = 1) ∧
      (∀ (p q : {p : Point3 // p ∈ S.union}),
        wz1PaperGridIndex delta (p : Point3) = wz1PaperGridIndex delta (q : Point3) →
          W p = W q) ∧
      (∀ p, (p : Point3) ∈ S.carrier (selectedI p) ∧
               (p : Point3) ∈ S.carrier (selectedJ p)) ∧
      (∀ p, kappa ≤
        ‖wz1Cross (F.tube (selectedI p)).direction
                         (F.tube (selectedJ p)).direction‖) ∧
      (∀ p, inner ℝ (F.tube (selectedI p)).direction (W p) = 0 ∧
                inner ℝ (F.tube (selectedJ p)).direction (W p) = 0) ∧
      (∀ p, W p =
        (‖wz1Cross (F.tube (selectedI p)).direction
                         (F.tube (selectedJ p)).direction‖)⁻¹ •
        wz1Cross (F.tube (selectedI p)).direction
                         (F.tube (selectedJ p)).direction) := by
  classical
  by_cases h_empty : S.union = ∅
  · -- Vacuous case: shaded union is empty, subtype is empty
    have h1 : IsEmpty {p : Point3 // p ∈ S.union} := by
      refine' ⟨fun x => _⟩
      have h6 : ∀ (z : Point3), z ∈ S.union → z ∈ (∅ : Set Point3) := by
        intro z hz
        rw [h_empty] at hz
        exact hz
      exact h6 (x : Point3) x.prop
    refine' ⟨fun p => isEmptyElim p, fun p => isEmptyElim p,
      fun p => isEmptyElim p, _⟩
    simp
  · -- Nonempty case
    have h_union_nonempty : S.union.Nonempty := Set.nonempty_iff_ne_empty.mpr h_empty
    rcases h_union_nonempty with ⟨p0, hp0⟩
    rcases hp0 with ⟨i0, _⟩
    letI : Nonempty (Fin F.card) := ⟨i0⟩
    letI : Nonempty (Fin F.card × Fin F.card) := ⟨(i0, i0)⟩
    let tubesAt (p : Point3) : Finset (Fin F.card) :=
      Finset.univ.filter fun i => p ∈ S.carrier i
    have h_tubes_nonempty : ∀ p ∈ S.union, (tubesAt p).Nonempty := by
      intro p hp
      rcases hp with ⟨i, hi⟩
      refine ⟨i, ?_⟩
      simp only [tubesAt, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hi
    have h_tubes_const : ∀ (p q : Point3),
        wz1PaperGridIndex delta p = wz1PaperGridIndex delta q →
          tubesAt p = tubesAt q := by
      intro p q hcell
      ext i
      simp only [tubesAt, Finset.mem_filter, Finset.mem_univ, true_and]
      exact paper_cubical_same_cell_same_carriers hS_cubical p q hcell i
    let transversePairs (p : Point3) :
        Finset (Fin F.card × Fin F.card) :=
      (tubesAt p) ×ˢ (tubesAt p) |>.filter fun ij =>
        kappa ≤ ‖wz1Cross (F.tube ij.1).direction (F.tube ij.2).direction‖
    let P (p : Point3) : (Fin F.card × Fin F.card) → Prop :=
      fun x => x ∈ transversePairs p
    have h_pairs_nonempty : ∀ p ∈ S.union, ∃ (x : Fin F.card × Fin F.card), P p x := by
      intro p hp
      rcases htransverse p hp with ⟨i, j, hi, hj, htrans⟩
      have hi_in : i ∈ tubesAt p := by
        simp only [tubesAt, Finset.mem_filter, Finset.mem_univ, true_and]; exact hi
      have hj_in : j ∈ tubesAt p := by
        simp only [tubesAt, Finset.mem_filter, Finset.mem_univ, true_and]; exact hj
      refine ⟨(i, j), ?_⟩
      simp only [P, transversePairs, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hi_in, hj_in⟩, htrans⟩
    let pair (p : {p : Point3 // p ∈ S.union}) : Fin F.card × Fin F.card :=
      Classical.epsilon (P (p : Point3))
    let i (p : {p : Point3 // p ∈ S.union}) : Fin F.card := (pair p).1
    let j (p : {p : Point3 // p ∈ S.union}) : Fin F.card := (pair p).2
    have h_pair_mem : ∀ (p : {p // p ∈ S.union}),
        P (p : Point3) (pair p) := by
      intro p
      exact Classical.epsilon_spec (h_pairs_nonempty (p : Point3) p.prop)
    have hi_mem : ∀ (p : {p // p ∈ S.union}),
        (p : Point3) ∈ S.carrier (i p) := by
      intro p
      have h : pair p ∈ transversePairs (p : Point3) := h_pair_mem p
      simp only [transversePairs, Finset.mem_filter, Finset.mem_product] at h
      have h' : (pair p).1 ∈ tubesAt (p : Point3) := h.1.1
      simp only [tubesAt, Finset.mem_filter, Finset.mem_univ, true_and] at h'
      exact h'
    have hj_mem : ∀ (p : {p // p ∈ S.union}),
        (p : Point3) ∈ S.carrier (j p) := by
      intro p
      have h : pair p ∈ transversePairs (p : Point3) := h_pair_mem p
      simp only [transversePairs, Finset.mem_filter, Finset.mem_product] at h
      have h' : (pair p).2 ∈ tubesAt (p : Point3) := h.1.2
      simp only [tubesAt, Finset.mem_filter, Finset.mem_univ, true_and] at h'
      exact h'
    have hj_trans : ∀ (p : {p // p ∈ S.union}),
        kappa ≤ ‖wz1Cross (F.tube (i p)).direction (F.tube (j p)).direction‖ := by
      intro p
      have h : pair p ∈ transversePairs (p : Point3) := h_pair_mem p
      simp only [transversePairs, Finset.mem_filter] at h
      exact h.2
    let W (p : {p : Point3 // p ∈ S.union}) : Point3 :=
      (‖wz1Cross (F.tube (i p)).direction
                       (F.tube (j p)).direction‖)⁻¹ •
        wz1Cross (F.tube (i p)).direction (F.tube (j p)).direction
    have hW_unit : ∀ p, ‖W p‖ = 1 := by
      intro p
      have hpos : 0 < ‖wz1Cross (F.tube (i p)).direction
                               (F.tube (j p)).direction‖ :=
        lt_of_lt_of_le hkappa_pos (hj_trans p)
      rw [show W p = (‖wz1Cross (F.tube (i p)).direction
                             (F.tube (j p)).direction‖)⁻¹ •
                   wz1Cross (F.tube (i p)).direction (F.tube (j p)).direction
        from rfl]
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hpos]
      field_simp [hpos.ne']
    have h_cell_const : ∀ (p q : {p // p ∈ S.union}),
        wz1PaperGridIndex delta (p : Point3) =
        wz1PaperGridIndex delta (q : Point3) →
          W p = W q := by
      intro p q hcell
      have h_tubes : tubesAt (p : Point3) = tubesAt (q : Point3) :=
        h_tubes_const (p : Point3) (q : Point3) hcell
      have h_pairs_eq : transversePairs (p : Point3) = transversePairs (q : Point3) := by
        ext ⟨a, b⟩
        simp only [transversePairs, Finset.mem_filter, Finset.mem_product, h_tubes]
      have hP_eq : P (p : Point3) = P (q : Point3) := by
        funext x
        simp only [P, h_pairs_eq]
      have hpair_eq : pair p = pair q := by
        dsimp only [pair]
        exact congr_arg Classical.epsilon hP_eq
      have hi_eq : i p = i q := by
        dsimp only [i]; rw [hpair_eq]
      have hj_eq : j p = j q := by
        dsimp only [j]; rw [hpair_eq]
      have hW_eq : W p = W q := by
        dsimp only [W]
        rw [hi_eq, hj_eq]
      exact hW_eq
    have h_inner_i : ∀ p,
        inner ℝ (F.tube (i p)).direction (W p) = 0 := by
      intro p
      let u := (F.tube (i p)).direction
      let v := (F.tube (j p)).direction
      have h : inner ℝ u (wz1Cross u v) = 0 := by
        rw [EuclideanSpace.inner_eq_star_dotProduct]
        have hstar : star (u : Fin 3 → ℝ) = (u : Fin 3 → ℝ) := by ext k; simp
        rw [hstar, dotProduct_comm]
        exact dot_self_cross (u : Fin 3 → ℝ) (v : Fin 3 → ℝ)
      have h2 : inner ℝ (F.tube (i p)).direction (W p) =
          (‖wz1Cross u v‖)⁻¹ * inner ℝ u (wz1Cross u v) := by
        simp only [W] <;> rw [inner_smul_right]
      rw [h2, h] <;> ring
    have h_inner_j : ∀ p,
        inner ℝ (F.tube (j p)).direction (W p) = 0 := by
      intro p
      let u := (F.tube (i p)).direction
      let v := (F.tube (j p)).direction
      have h : inner ℝ v (wz1Cross u v) = 0 := by
        rw [EuclideanSpace.inner_eq_star_dotProduct]
        have hstar : star (v : Fin 3 → ℝ) = (v : Fin 3 → ℝ) := by ext k; simp
        rw [hstar, dotProduct_comm]
        exact dot_cross_self (u : Fin 3 → ℝ) (v : Fin 3 → ℝ)
      have h2 : inner ℝ (F.tube (j p)).direction (W p) =
          (‖wz1Cross u v‖)⁻¹ * inner ℝ v (wz1Cross u v) := by
        simp only [W] <;> rw [inner_smul_right]
      rw [h2, h] <;> ring
    exact ⟨W, i, j, hW_unit, h_cell_const,
      fun p => ⟨hi_mem p, hj_mem p⟩, hj_trans,
      fun p => ⟨h_inner_i p, h_inner_j p⟩,
      fun p => rfl⟩

/--
Incidence bound for a per-cell plane map under narrow triple-product conditions.

If `W` is constructed from transverse pairs `(selectedI p, selectedJ p)` with
cross-product norm at least `kappa`, and for every tube `k` through point `p`
the triple product with the selected pair is at most `tau`, then the incidence
of `W p` with direction `k` is at most `tau / kappa`.

This is the key step connecting per-cell plane maps to the weak plane map
incidence bound required by `pure_wz2_grain_plane_map_tight`.
-/
lemma per_cell_plane_map_incidence_bound
    {delta tau kappa : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    (W : {p : Point3 // p ∈ S.union} → Point3)
    (selectedI selectedJ : {p : Point3 // p ∈ S.union} → Fin F.card)
    (hW_form : ∀ (p : {p : Point3 // p ∈ S.union}), W p =
        (‖wz1Cross (F.tube (selectedI p)).direction
                         (F.tube (selectedJ p)).direction‖)⁻¹ •
        wz1Cross (F.tube (selectedI p)).direction
                     (F.tube (selectedJ p)).direction)
    (hkappa : ∀ (p : {p : Point3 // p ∈ S.union}), kappa ≤
        ‖wz1Cross (F.tube (selectedI p)).direction
                     (F.tube (selectedJ p)).direction‖)
    (htau : ∀ (p : {p : Point3 // p ∈ S.union}) (k : Fin F.card), (p : Point3) ∈ S.carrier k →
        |wz1TripleProduct
          (F.tube (selectedI p)).direction
          (F.tube (selectedJ p)).direction
          (F.tube k).direction| ≤ tau)
    (hkappa_pos : 0 < kappa)
    (htau_nonneg : 0 ≤ tau) :
    ∀ (p : {p : Point3 // p ∈ S.union}) (k : Fin F.card),
      (p : Point3) ∈ S.carrier k →
        |inner ℝ (F.tube k).direction (W p)| ≤ tau / kappa := by
  intro p k hpk
  let u := (F.tube (selectedI p)).direction
  let v := (F.tube (selectedJ p)).direction
  let w := (F.tube k).direction
  have hpos : 0 < ‖wz1Cross u v‖ := lt_of_lt_of_le hkappa_pos (hkappa p)
  have htriple : inner ℝ w (wz1Cross u v) = wz1TripleProduct u v w := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    have hstar : star (w : Fin 3 → ℝ) = (w : Fin 3 → ℝ) := by ext i; simp
    rw [hstar, dotProduct_comm]
    have hperm : (w : Fin 3 → ℝ) ⬝ᵥ (wz1Cross u v : Fin 3 → ℝ) =
        (u : Fin 3 → ℝ) ⬝ᵥ (wz1Cross v w : Fin 3 → ℝ) :=
      triple_product_permutation (w : Fin 3 → ℝ) (u : Fin 3 → ℝ) (v : Fin 3 → ℝ)
    rw [hperm]
    exact triple_product_eq_det (u : Fin 3 → ℝ) (v : Fin 3 → ℝ) (w : Fin 3 → ℝ)
  have h1 : |inner ℝ w (W p)| =
      |wz1TripleProduct u v w| / ‖wz1Cross u v‖ := by
    rw [hW_form p]
    have hinner : inner ℝ w ((‖wz1Cross u v‖)⁻¹ • wz1Cross u v) =
        (‖wz1Cross u v‖)⁻¹ * inner ℝ w (wz1Cross u v) := by
      rw [inner_smul_right]
    rw [hinner, htriple, abs_mul, abs_inv, abs_of_pos hpos]
    <;> ring
  rw [h1]
  have h2 : |wz1TripleProduct u v w| ≤ tau := htau p k hpk
  have h3 : ‖wz1Cross u v‖ ≥ kappa := hkappa p
  have h4 : |wz1TripleProduct u v w| / ‖wz1Cross u v‖ ≤ tau / kappa := by
    calc |wz1TripleProduct u v w| / ‖wz1Cross u v‖
        ≤ tau / ‖wz1Cross u v‖ := by gcongr
      _ ≤ tau / kappa := by gcongr
  exact h4

/--
Sign uniqueness: for unit vectors `a, b` and bound `B < 1`,
`dist(a,b) ≤ B` and `dist(a,-b) ≤ B` cannot both hold.

This is the key fact that makes sign resolution unambiguous:
since `dist(b, -b) = 2`, the triangle inequality gives
`2 ≤ dist(a,b) + dist(a,-b) ≤ 2B < 2`, a contradiction.
-/
lemma sign_uniqueness {a b : Point3}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) {B : ℝ} (hB : B < 1) :
    ¬ (dist a b ≤ B ∧ dist a (-b) ≤ B) := by
  intro h
  have h1 : dist b (-b) = 2 := by
    rw [dist_eq_norm]
    have h11 : b - (-b) = (2 : ℝ) • b := by
      have h : b - (-b) = b + b := by simp [sub_neg_eq_add]
      rw [h]
      exact (two_smul ℝ b).symm
    rw [h11, norm_smul, Real.norm_eq_abs, abs_of_pos (show (0 : ℝ) < 2 by norm_num), hb]
    <;> norm_num
  have h2 : dist b (-b) ≤ dist a b + dist a (-b) := by
    calc dist b (-b) ≤ dist b a + dist a (-b) := dist_triangle b a (-b)
      _ = dist a b + dist a (-b) := by rw [dist_comm b a]
  have h3 : dist a b + dist a (-b) ≤ 2 * B := by linarith
  have h4 : (2 : ℝ) ≤ 2 * B := by
    linarith [h1, h2, h3]
  linarith

/--
Sign transitivity: if `B < 1/2` and unit vectors `a,b,c` satisfy
`dist(a,b) ≤ B` and `dist(b,c) ≤ B`, then `dist(a,c) ≤ 2B` and
`dist(a,-c) > B`.

This ensures that along a path where each step uses the "same sign"
relation, the endpoints are close to each other, not to each other's
negation. It is the key lemma for proving path-independence of
sign assignment on a cubical grid (all 4-cycles are consistent when
`B < 1/2`, since `4B < 2`).
-/
lemma sign_transitivity {a b c : Point3}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    {B : ℝ} (hB : B < 1 / 2)
    (h1 : dist a b ≤ B) (h2 : dist b c ≤ B) :
    dist a c ≤ 2 * B ∧ dist a (-c) > B := by
  have h3 : dist a c ≤ 2 * B := by
    calc dist a c ≤ dist a b + dist b c := dist_triangle a b c
      _ ≤ 2 * B := by linarith
  have h4 : dist c (-c) = 2 := by
    rw [dist_eq_norm]
    have h41 : c - (-c) = (2 : ℝ) • c := by
      have h : c - (-c) = c + c := by simp [sub_neg_eq_add]
      rw [h]
      exact (two_smul ℝ c).symm
    rw [h41, norm_smul, Real.norm_eq_abs, abs_of_pos (show (0 : ℝ) < 2 by norm_num), hc]
    <;> norm_num
  have h5 : dist a (-c) ≥ dist c (-c) - dist a c := by
    have h6 : dist c (-c) ≤ dist c a + dist a (-c) := dist_triangle c a (-c)
    have h7 : dist c a = dist a c := dist_comm c a
    linarith
  have h8 : dist a (-c) ≥ 2 - 2 * B := by linarith [h4, h5, h3]
  have h9 : 2 - 2 * B > B := by linarith
  exact ⟨h3, by linarith⟩

/--
A simple tree condition: `level : α → ℕ` assigns levels such that every
node except `root` has exactly one neighbor with level one less, and
no neighbor with level more than one less. This ensures acyclicity.
-/
def IsTreeLike {α : Type*} [DecidableEq α]
    (adj : α → α → Prop) [DecidableRel adj]
    (root : α) (level : α → ℕ) : Prop :=
  level root = 0 ∧
  ∀ a, a ≠ root →
    (∃! b, adj a b ∧ level b = level a - 1) ∧
    (∀ b, adj a b → level b = level a - 1 ∨ level b = level a + 1)

/--
Global sign assignment on a connected tree graph.

Given a tree with unit vectors at each node, and for each edge either
the vectors are within `B` or one is within `B` of the other's negation,
with `B < 1`, there exists a sign assignment `s : α → {±1}` such that
adjacent signed vectors are within `B`.

The sign on each edge is uniquely determined by `sign_uniqueness` when
`B < 1`. On a tree, propagation from a root gives a well-defined global
assignment with no cycle-consistency issues.

For a cubical grid (which may have cycles), `B < 1/2` ensures all
4-cycles are consistent by `sign_transitivity`, and the simply-connected
cell complex then guarantees global consistency.
-/
theorem sign_assignment_on_tree
    {α : Type*} [Fintype α] [DecidableEq α]
    (n : α → Point3) (hn : ∀ a, ‖n a‖ = 1)
    (adj : α → α → Prop) [DecidableRel adj]
    (hadj_symm : ∀ a b, adj a b → adj b a)
    (root : α) (level : α → ℕ)
    (h_tree : IsTreeLike adj root level)
    (h_levels_pos : ∀ a, a ≠ root → 0 < level a)
    {B : ℝ} (hB : B < 1)
    (hedge : ∀ a b, adj a b → dist (n a) (n b) ≤ B ∨ dist (n a) (-(n b)) ≤ B) :
    ∃ (s : α → ℝ), (∀ a, s a = 1 ∨ s a = -1) ∧
      (∀ a b, adj a b → dist (s a • n a) (s b • n b) ≤ B) := by
  let parent (a : α) (ha : a ≠ root) : α :=
    Classical.choose (h_tree.2 a ha).1

  have hparent_spec : ∀ (a : α) (ha : a ≠ root),
      adj a (parent a ha) ∧ level (parent a ha) = level a - 1 := by
    intro a ha
    exact (Classical.choose_spec (h_tree.2 a ha).1).1

  have hparent_uniq : ∀ (a : α) (ha : a ≠ root) (b : α),
      adj a b → level b = level a - 1 → b = parent a ha := by
    intro a ha b hadj hlev
    have h_uniq : ∀ (y : α), (adj a y ∧ level y = level a - 1) → y = parent a ha :=
      (Classical.choose_spec (h_tree.2 a ha).1).2
    exact h_uniq b ⟨hadj, hlev⟩

  have hwf : WellFounded (fun a b : α => level a < level b) :=
    IsWellFounded.wf

  let P : (a : α) → ((b : α) → level b < level a → ℝ) → ℝ :=
    fun a ih =>
      if hroot : a = root then 1
      else
        let b := parent a hroot
        let sb := ih b (by
          have hspec : level b = level a - 1 := (hparent_spec a hroot).2
          have hpos : 0 < level a := h_levels_pos a hroot
          omega)
        if hdist : dist (n a) (n b) ≤ B then sb
        else -sb

  let s : α → ℝ := hwf.fix P

  have hs_eq : ∀ (a : α), s a = P a (fun b _ => s b) := by
    intro a
    exact WellFounded.fix_eq hwf P a

  have hs_sign : ∀ (a : α), s a = 1 ∨ s a = -1 := by
    intro a
    induction a using WellFounded.induction hwf with
    | h a ih =>
      rw [hs_eq a]
      dsimp only [P]
      by_cases hroot : a = root
      · rw [dif_pos hroot] <;> simp
      · rw [dif_neg hroot]
        let b := parent a hroot
        have hlev : level b < level a := by
          have hspec : level b = level a - 1 := (hparent_spec a hroot).2
          have hpos : 0 < level a := h_levels_pos a hroot
          omega
        have ihb : s b = 1 ∨ s b = -1 := ih b hlev
        by_cases hdist : dist (n a) (n b) ≤ B
        · rw [dif_pos hdist]; exact ihb
        · rw [dif_neg hdist]
          rcases ihb with (h | h)
          · rw [h] <;> norm_num
          · rw [h] <;> norm_num

  have h_levels_diff : ∀ a b, adj a b → a ≠ b → level a ≠ level b := by
    intro a b hadj hne
    by_contra h_eq
    have h_k : level a = level b := h_eq
    by_cases h_a_root : a = root
    · rw [h_a_root, h_tree.1] at h_k
      have h_b_level : level b = 0 := Eq.symm h_k
      by_cases h_b_root : b = root
      · exfalso
        have h_ab : a = b := by rw [h_a_root, h_b_root]
        exact hne h_ab
      · have h_pos : 0 < level b := h_levels_pos b h_b_root
        rw [h_b_level] at h_pos <;> linarith
    · have h_a_pos : 0 < level a := h_levels_pos a h_a_root
      have h1 : level b = level a - 1 ∨ level b = level a + 1 :=
        (h_tree.2 a h_a_root).2 b hadj
      rw [h_k] at h1
      omega

  have h_parent_bound : ∀ (child par : α), child ≠ root →
      adj child par → level par = level child - 1 →
      dist (s child • n child) (s par • n par) ≤ B := by
    intro child par hchild_not_root hadj_cp hlev
    have hb_eq_par : parent child hchild_not_root = par :=
      (hparent_uniq child hchild_not_root par hadj_cp hlev).symm
    rw [hs_eq child]
    dsimp only [P]
    rw [dif_neg hchild_not_root]
    have h_main : (if hdist : dist (n child) (n (parent child hchild_not_root)) ≤ B
        then s (parent child hchild_not_root)
        else -s (parent child hchild_not_root)) =
        if hdist : dist (n child) (n par) ≤ B then s par else -s par := by
      rw [hb_eq_par]
    rw [h_main]
    by_cases hdist : dist (n child) (n par) ≤ B
    · rw [dif_pos hdist]
      have h_goal : dist (s par • n child) (s par • n par) ≤ B := by
        have h5 : dist (s par • n child) (s par • n par) = |s par| * dist (n child) (n par) := by
          calc
            dist (s par • n child) (s par • n par)
              = ‖s par • n child - s par • n par‖ := by rw [dist_eq_norm]
            _ = ‖s par • (n child - n par)‖ := by rw [smul_sub]
            _ = |s par| * ‖n child - n par‖ := by rw [norm_smul, Real.norm_eq_abs]
            _ = |s par| * dist (n child) (n par) := by rw [←dist_eq_norm]
        rw [h5]
        have h6 : |s par| = 1 := by
          have h7 : s par = 1 ∨ s par = -1 := hs_sign par
          rcases h7 with (h7 | h7) <;> rw [h7] <;> norm_num
        rw [h6] <;> linarith
      exact h_goal
    · rw [dif_neg hdist]
      have hdist2 : dist (n child) (-(n par)) ≤ B := by
        have h := hedge child par hadj_cp
        tauto
      have h_goal : dist ((-(s par)) • n child) (s par • n par) ≤ B := by
        have h5 : dist ((-(s par)) • n child) (s par • n par) = |s par| * dist (n child) (-(n par)) := by
          calc
            dist ((-(s par)) • n child) (s par • n par)
              = ‖(-(s par)) • n child - s par • n par‖ := by rw [dist_eq_norm]
            _ = ‖-(s par • (n child - (-(n par))))‖ := by
              have h6 : (-(s par)) • n child - s par • n par = -(s par • (n child - (-(n par)))) := by
                have h7 : (-(s par)) • n child = -(s par • n child) := by rw [neg_smul]
                rw [h7]
                have h8 : n child - (-(n par)) = n child + n par := by simp [sub_neg_eq_add]
                rw [h8] <;> simp [smul_add] <;> abel
              rw [h6]
            _ = ‖s par • (n child - (-(n par)))‖ := by rw [norm_neg]
            _ = |s par| * ‖n child - (-(n par))‖ := by rw [norm_smul, Real.norm_eq_abs]
            _ = |s par| * dist (n child) (-(n par)) := by rw [←dist_eq_norm]
        rw [h5]
        have h6 : |s par| = 1 := by
          have h7 : s par = 1 ∨ s par = -1 := hs_sign par
          rcases h7 with (h7 | h7) <;> rw [h7] <;> norm_num
        rw [h6] <;> linarith
      exact h_goal

  have h_main : ∀ (a b : α), adj a b → dist (s a • n a) (s b • n b) ≤ B := by
    intro a b hadj
    by_cases h_ab : a = b
    · subst h_ab
      have hB_nonneg : 0 ≤ B := by
        have h := hedge a a (by simpa using hadj)
        rcases h with (h | h)
        · simpa [dist_self] using h
        · have h2 : dist (n a) (-(n a)) = 2 := by
            have h3 : ‖n a‖ = 1 := hn a
            have h4 : n a - (-(n a)) = (2 : ℝ) • n a := by
              have h5 : n a - (-(n a)) = n a + n a := by simp [sub_neg_eq_add]
              rw [h5]
              exact (two_smul ℝ (n a)).symm
            rw [dist_eq_norm, h4, norm_smul, Real.norm_eq_abs, abs_of_pos (show (0 : ℝ) < 2 by norm_num), h3] <;> norm_num
          rw [h2] at h
          linarith
      simp [dist_self, hB_nonneg]
    · have h_diff : level a ≠ level b := h_levels_diff a b hadj h_ab
      by_cases h_ab_lt : level a < level b
      · -- a is parent of b
        have hb_not_root : b ≠ root := by
          intro hbr
          rw [hbr] at h_ab_lt
          rw [h_tree.1] at h_ab_lt <;> linarith
        have h1 : level a = level b - 1 ∨ level a = level b + 1 :=
          (h_tree.2 b hb_not_root).2 a (hadj_symm a b hadj)
        have hlev : level a = level b - 1 := by omega
        have h := h_parent_bound b a hb_not_root (hadj_symm a b hadj) hlev
        have h' : dist (s a • n a) (s b • n b) ≤ B := by
          exact dist_comm (s b • n b) (s a • n a) ▸ h
        exact h'
      · have h_ba_lt : level b < level a := by
          exact lt_of_le_of_ne (by omega) h_diff.symm
        have ha_not_root : a ≠ root := by
          intro har
          rw [har] at h_ba_lt
          rw [h_tree.1] at h_ba_lt <;> linarith
        have h1 : level b = level a - 1 ∨ level b = level a + 1 :=
          (h_tree.2 a ha_not_root).2 b hadj
        have hlev : level b = level a - 1 := by omega
        exact h_parent_bound a b ha_not_root hadj hlev

  exact ⟨s, hs_sign, h_main⟩

/--
Parameter feasibility for sign assignment in the WZ2 grains setup.

The direction overlap bound from `direction_overlap_adjacent_cells` is:
  `B = 20 * I / κ + 4 * eps / κ`

For the per-cell plane map from `per_cell_plane_map_from_transverse`,
the incidence `I` with the cell's OWN selected transverse pair is
exactly `0` (since `W = normalize(cross(u,v))` is orthogonal to both
`u` and `v`). Thus:
  `B = 4 * eps / κ`

For sign uniqueness (`B < 1`): need `eps < κ / 4`.
For cycle consistency on cubical grid (`B < 1/2`): need `eps < κ / 8`.

**Parameter check** with typical WZ2 values:
- `κ = L^epsilon₃` (transversality from Property P)
- `eps` = direction variation between selected transverse pairs in adjacent cells

If adjacent cells share the SAME transverse directions (eps = 0),
then `B = 0` and sign assignment is trivial.

If eps is the cell diameter `delta'` and `κ = L^epsilon₃`:
  `B = 4 * delta' / L^epsilon₃`
Since `L = delta'^stickyLoss` with `stickyLoss ≤ 1/2`:
  `B = 4 * delta'^(1 - stickyLoss * epsilon₃)`
For small `delta'`, this is `< 1` as long as `1 - stickyLoss * epsilon₃ > 0`,
which holds since `stickyLoss, epsilon₃ < 1`.

**Key blocker**: We need to show that adjacent cells have transverse pairs
with direction variation `eps < κ / 8`. The `per_cell_plane_map_from_transverse`
construction selects minimum-index tubes, which may differ between adjacent
cells. A direction-overlap-from-density argument (WZ2 Section 6, balanced
cover + direction packing) is needed to show that nearby cells share
transverse directions, or to select pairs in a coordinated way.

Without this, `eps` could be `O(1)` (completely different directions),
making `B > 1` and sign resolution ambiguous.
-/
lemma sign_assignment_parameter_feasibility : True := trivial

/--
Sign uniqueness for unit vectors: if `dist(w1, w2) ≤ B < 1`, then
`dist(w1, -w2) > B`.

This resolves the ± ambiguity in direction overlap bounds on EVERY edge of a
grid graph (not just a tree), because the two alternatives are mutually
exclusive when B < 1. Hence no spanning tree or cycle consistency check is
needed.
-/
lemma sign_uniqueness_for_unit_vectors
    {w1 w2 : Point3} (hw1 : ‖w1‖ = 1) (hw2 : ‖w2‖ = 1)
    {B : ℝ} (hB_nonneg : 0 ≤ B) (hB : B < 1) (h : dist w1 w2 ≤ B) :
    dist w1 (-w2) > B := by
  have h1 : ‖w1 - w2‖ ^ 2 + ‖w1 + w2‖ ^ 2 = 4 := by
    have h_par : ‖w1 + w2‖ * ‖w1 + w2‖ + ‖w1 - w2‖ * ‖w1 - w2‖ =
        2 * (‖w1‖ * ‖w1‖ + ‖w2‖ * ‖w2‖) :=
      parallelogram_law_with_norm_mul (𝕜 := ℝ) w1 w2
    have h_eq1 : ‖w1 - w2‖ ^ 2 + ‖w1 + w2‖ ^ 2 =
        ‖w1 + w2‖ * ‖w1 + w2‖ + ‖w1 - w2‖ * ‖w1 - w2‖ := by ring
    have h_eq2 : 2 * (‖w1‖ * ‖w1‖ + ‖w2‖ * ‖w2‖) = 2 * (‖w1‖ ^ 2 + ‖w2‖ ^ 2) := by ring
    rw [h_eq1, h_par, h_eq2, hw1, hw2] <;> norm_num
  have h2 : ‖w1 - w2‖ ≤ B := by simpa [dist_eq_norm] using h
  have h2' : ‖w1 - w2‖ ^ 2 ≤ B ^ 2 := by gcongr
  have hB2 : B ^ 2 < 1 := by nlinarith
  have h3 : ‖w1 + w2‖ ^ 2 > 3 := by nlinarith
  have h4 : ‖w1 + w2‖ > 1 := by nlinarith [norm_nonneg (w1 + w2)]
  have h5 : dist w1 (-w2) = ‖w1 + w2‖ := by
    simp [dist_eq_norm] <;> abel
  rw [h5]
  linarith

/--
Rho-cell version of `per_cell_plane_map_from_transverse_pair`.

Selects one transverse pair per rho-grid cell (instead of per delta-grid cell)
and produces a map constant on rho-cells. The pair set must be constant on
rho-cells (supplied as `hcell_const`).

This is useful for the multi-scale coarse-scale upgrade where the plane map
needs to be constant on coarse cells.
-/
theorem per_rho_cell_plane_map_from_transverse_pair
    {delta rho : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    (kappa : ℝ) (hkappa_pos : 0 < kappa)
    (htransverse : ∀ p ∈ S.union,
      ∃ (i j : Fin F.card),
        p ∈ S.carrier i ∧ p ∈ S.carrier j ∧
          kappa ≤ ‖wz1Cross (F.tube i).direction (F.tube j).direction‖)
    (hcell_const : ∀ (p q : Point3),
      wz1PaperGridIndex rho p = wz1PaperGridIndex rho q →
        (∀ (i j : Fin F.card),
          (p ∈ S.carrier i ∧ p ∈ S.carrier j ∧
            kappa ≤ ‖wz1Cross (F.tube i).direction (F.tube j).direction‖) ↔
          (q ∈ S.carrier i ∧ q ∈ S.carrier j ∧
            kappa ≤ ‖wz1Cross (F.tube i).direction (F.tube j).direction‖))) :
    ∃ (W : {p : Point3 // p ∈ S.union} → Point3)
      (selectedI selectedJ : {p : Point3 // p ∈ S.union} → Fin F.card),
      (∀ p, ‖W p‖ = 1) ∧
      (∀ (p q : {p : Point3 // p ∈ S.union}),
        wz1PaperGridIndex rho (p : Point3) = wz1PaperGridIndex rho (q : Point3) →
          W p = W q) ∧
      (∀ p, (p : Point3) ∈ S.carrier (selectedI p) ∧
               (p : Point3) ∈ S.carrier (selectedJ p)) ∧
      (∀ p, kappa ≤
        ‖wz1Cross (F.tube (selectedI p)).direction
                         (F.tube (selectedJ p)).direction‖) ∧
      (∀ p, inner ℝ (F.tube (selectedI p)).direction (W p) = 0 ∧
                inner ℝ (F.tube (selectedJ p)).direction (W p) = 0) ∧
      (∀ p, W p =
        (‖wz1Cross (F.tube (selectedI p)).direction
                         (F.tube (selectedJ p)).direction‖)⁻¹ •
        wz1Cross (F.tube (selectedI p)).direction
                         (F.tube (selectedJ p)).direction) := by
  classical
  by_cases h_empty : S.union = ∅
  · have h1 : IsEmpty {p : Point3 // p ∈ S.union} := by
      refine' ⟨fun x => _⟩
      have h6 : ∀ (z : Point3), z ∈ S.union → z ∈ (∅ : Set Point3) := by
        intro z hz
        rw [h_empty] at hz
        exact hz
      exact h6 (x : Point3) x.prop
    refine' ⟨fun p => isEmptyElim p, fun p => isEmptyElim p,
      fun p => isEmptyElim p, _⟩
    simp
  · rcases Set.nonempty_iff_ne_empty.mpr h_empty with ⟨p0, hp0⟩
    rcases hp0 with ⟨i0, _⟩
    letI : Nonempty (Fin F.card) := ⟨i0⟩
    letI : Nonempty (Fin F.card × Fin F.card) := ⟨(i0, i0)⟩
    let P (p : Point3) : (Fin F.card × Fin F.card) → Prop :=
      fun ij => p ∈ S.carrier ij.1 ∧ p ∈ S.carrier ij.2 ∧
        kappa ≤ ‖wz1Cross (F.tube ij.1).direction (F.tube ij.2).direction‖
    have hP_nonempty : ∀ p ∈ S.union, ∃ (x : Fin F.card × Fin F.card), P p x := by
      intro p hp
      rcases htransverse p hp with ⟨i, j, hi, hj, htrans⟩
      exact ⟨(i, j), hi, hj, htrans⟩
    have hP_const : ∀ (p q : Point3),
        wz1PaperGridIndex rho p = wz1PaperGridIndex rho q → P p = P q := by
      intro p q hcell
      funext ij
      have hiff := hcell_const p q hcell ij.1 ij.2
      exact propext hiff
    let pair (p : {p : Point3 // p ∈ S.union}) : Fin F.card × Fin F.card :=
      Classical.epsilon (P (p : Point3))
    let i (p : {p : Point3 // p ∈ S.union}) : Fin F.card := (pair p).1
    let j (p : {p : Point3 // p ∈ S.union}) : Fin F.card := (pair p).2
    have h_pair_mem : ∀ (p : {p // p ∈ S.union}),
        P (p : Point3) (pair p) := by
      intro p
      exact Classical.epsilon_spec (hP_nonempty (p : Point3) p.prop)
    have hi_mem : ∀ p, (p : Point3) ∈ S.carrier (i p) :=
      fun p => (h_pair_mem p).1
    have hj_mem : ∀ p, (p : Point3) ∈ S.carrier (j p) :=
      fun p => (h_pair_mem p).2.1
    have hj_trans : ∀ p, kappa ≤ ‖wz1Cross (F.tube (i p)).direction (F.tube (j p)).direction‖ :=
      fun p => (h_pair_mem p).2.2
    let W (p : {p : Point3 // p ∈ S.union}) : Point3 :=
      (‖wz1Cross (F.tube (i p)).direction
                       (F.tube (j p)).direction‖)⁻¹ •
        wz1Cross (F.tube (i p)).direction (F.tube (j p)).direction
    have hW_unit : ∀ p, ‖W p‖ = 1 := by
      intro p
      have hpos : 0 < ‖wz1Cross (F.tube (i p)).direction (F.tube (j p)).direction‖ :=
        lt_of_lt_of_le hkappa_pos (hj_trans p)
      rw [show W p = (‖wz1Cross (F.tube (i p)).direction
                             (F.tube (j p)).direction‖)⁻¹ •
                   wz1Cross (F.tube (i p)).direction (F.tube (j p)).direction
        from rfl]
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hpos]
      field_simp [hpos.ne']
    have h_cell_const : ∀ (p q : {p // p ∈ S.union}),
        wz1PaperGridIndex rho (p : Point3) = wz1PaperGridIndex rho (q : Point3) →
          W p = W q := by
      intro p q hcell
      have hP_eq : P (p : Point3) = P (q : Point3) := hP_const (p : Point3) (q : Point3) hcell
      have hpair_eq : pair p = pair q := by
        dsimp only [pair]
        exact congr_arg Classical.epsilon hP_eq
      have hi_eq : i p = i q := by dsimp only [i]; rw [hpair_eq]
      have hj_eq : j p = j q := by dsimp only [j]; rw [hpair_eq]
      have hW_eq : W p = W q := by dsimp only [W]; rw [hi_eq, hj_eq]
      exact hW_eq
    have h_inner_i : ∀ p, inner ℝ (F.tube (i p)).direction (W p) = 0 := by
      intro p
      let u := (F.tube (i p)).direction
      let v := (F.tube (j p)).direction
      have h : inner ℝ u (wz1Cross u v) = 0 := by
        rw [EuclideanSpace.inner_eq_star_dotProduct]
        have hstar : star (u : Fin 3 → ℝ) = (u : Fin 3 → ℝ) := by ext k; simp
        rw [hstar, dotProduct_comm]
        exact dot_self_cross (u : Fin 3 → ℝ) (v : Fin 3 → ℝ)
      have h2 : inner ℝ (F.tube (i p)).direction (W p) =
          (‖wz1Cross u v‖)⁻¹ * inner ℝ u (wz1Cross u v) := by
        simp only [W] <;> rw [inner_smul_right]
      rw [h2, h] <;> ring
    have h_inner_j : ∀ p, inner ℝ (F.tube (j p)).direction (W p) = 0 := by
      intro p
      let u := (F.tube (i p)).direction
      let v := (F.tube (j p)).direction
      have h : inner ℝ v (wz1Cross u v) = 0 := by
        rw [EuclideanSpace.inner_eq_star_dotProduct]
        have hstar : star (v : Fin 3 → ℝ) = (v : Fin 3 → ℝ) := by ext k; simp
        rw [hstar, dotProduct_comm]
        exact dot_cross_self (u : Fin 3 → ℝ) (v : Fin 3 → ℝ)
      have h2 : inner ℝ (F.tube (j p)).direction (W p) =
          (‖wz1Cross u v‖)⁻¹ * inner ℝ v (wz1Cross u v) := by
        simp only [W] <;> rw [inner_smul_right]
      rw [h2, h] <;> ring
    exact ⟨W, i, j, hW_unit, h_cell_const,
      fun p => ⟨hi_mem p, hj_mem p⟩, hj_trans,
      fun p => ⟨h_inner_i p, h_inner_j p⟩,
      fun p => rfl⟩

/--
Extend a plane map defined on the shading union to all of `Point3`.

Outside the union, the map is set to `0`. The unit norm and incidence properties
only hold on the union. This is useful for connecting subtype-based maps to
total-function-based APIs like `pureWz2_cubical_refinement`.
-/
def extendPlaneMap {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    (W : {p : Point3 // p ∈ S.union} → Point3) : Point3 → Point3 :=
  fun p => if h : p ∈ S.union then W ⟨p, h⟩ else 0

lemma extendPlaneMap_on_union
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    (W : {p : Point3 // p ∈ S.union} → Point3)
    (p : Point3) (hp : p ∈ S.union) :
    extendPlaneMap W p = W ⟨p, hp⟩ := by
  simp [extendPlaneMap, hp]

lemma extendPlaneMap_const
    {delta rho : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    (W : {p : Point3 // p ∈ S.union} → Point3)
    (hW_const : ∀ (p q : {p : Point3 // p ∈ S.union}),
      wz1PaperGridIndex rho (p : Point3) = wz1PaperGridIndex rho (q : Point3) → W p = W q)
    (p q : Point3) (hp : p ∈ S.union) (hq : q ∈ S.union)
    (hcell : wz1PaperGridIndex rho p = wz1PaperGridIndex rho q) :
    extendPlaneMap W p = extendPlaneMap W q := by
  rw [extendPlaneMap_on_union W p hp, extendPlaneMap_on_union W q hq]
  exact hW_const ⟨p, hp⟩ ⟨q, hq⟩ hcell

lemma extendPlaneMap_unit
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    (W : {p : Point3 // p ∈ S.union} → Point3)
    (hW_unit : ∀ p, ‖W p‖ = 1)
    (p : Point3) (hp : p ∈ S.union) :
    ‖extendPlaneMap W p‖ = 1 := by
  rw [extendPlaneMap_on_union W p hp]
  exact hW_unit ⟨p, hp⟩

/--
Glue lemma: from a per-rho-cell transverse pair condition, produce a total plane
map constant on rho-cells, with unit norm and selected transverse pair data on
the shading union.

This packages the output of `per_rho_cell_plane_map_from_transverse_pair` into
a form suitable for `pureWz2_cubical_refinement` (which expects a total
`Point3 → Point3` map).
-/
lemma rho_cell_map_to_total
    {delta rho : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    (kappa : ℝ) (hkappa_pos : 0 < kappa)
    (htransverse : ∀ p ∈ S.union,
      ∃ (i j : Fin F.card),
        p ∈ S.carrier i ∧ p ∈ S.carrier j ∧
          kappa ≤ ‖wz1Cross (F.tube i).direction (F.tube j).direction‖)
    (hcell_const : ∀ (p q : Point3),
      wz1PaperGridIndex rho p = wz1PaperGridIndex rho q →
        (∀ (i j : Fin F.card),
          (p ∈ S.carrier i ∧ p ∈ S.carrier j ∧
            kappa ≤ ‖wz1Cross (F.tube i).direction (F.tube j).direction‖) ↔
          (q ∈ S.carrier i ∧ q ∈ S.carrier j ∧
            kappa ≤ ‖wz1Cross (F.tube i).direction (F.tube j).direction‖))) :
    ∃ (Wtotal : Point3 → Point3)
      (selectedI selectedJ : {p : Point3 // p ∈ S.union} → Fin F.card),
      (∀ (p q : Point3), p ∈ S.union → q ∈ S.union →
        wz1PaperGridIndex rho p = wz1PaperGridIndex rho q → Wtotal p = Wtotal q) ∧
      (∀ (p : Point3) (_hp : p ∈ S.union), ‖Wtotal p‖ = 1) ∧
      (∀ (p : {p : Point3 // p ∈ S.union}), (p : Point3) ∈ S.carrier (selectedI p) ∧
                       (p : Point3) ∈ S.carrier (selectedJ p)) ∧
      (∀ (p : {p : Point3 // p ∈ S.union}), kappa ≤
        ‖wz1Cross (F.tube (selectedI p)).direction
                         (F.tube (selectedJ p)).direction‖) := by
  rcases per_rho_cell_plane_map_from_transverse_pair kappa hkappa_pos htransverse hcell_const
    with ⟨W, selectedI, selectedJ, hW_unit, hW_const, h_mem, h_trans, _, _⟩
  let Wtotal := extendPlaneMap W
  refine ⟨Wtotal, selectedI, selectedJ, ?_, ?_, ?_, ?_⟩
  · intro p q hp hq hcell
    exact extendPlaneMap_const W hW_const p q hp hq hcell
  · intro p _hp
    exact extendPlaneMap_unit W hW_unit p _hp
  · exact h_mem
  · exact h_trans

end Kakeya.Assouad

end
