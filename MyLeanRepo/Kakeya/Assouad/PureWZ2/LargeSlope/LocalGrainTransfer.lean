import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.Definitions
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Local grain transfer under anisotropic rescaling

Core identities and bounds for transferring `PureWZ2LocalGrainData` through
the anisotropic rescaling map Φ of WZ2 Section 6.

## Key identity

The linear part DΦ and its inverse transpose DΦ^{-T} satisfy:
  `inner(DΦ v, DΦ^{-T} w) = inner(v, w)`

This preserves plane-map incidence exactly. Normalization introduces a
controlled Lipschitz constant.

## Provided lemmas

1. `dPhi_inner_identity`: exact incidence preservation
2. `dPhiLin_sub`, `dPhiInvT_sub`: linearity
3. `dPhiLin_injective`, `dPhiInvT_injective`: injectivity
4. `normalization_lipschitz`: `‖normalize x - normalize y‖ ≤ 2/m · ‖x-y‖`
5. `incidence_preservation`: normalized incidence formula
6. `local_ad_projection_pointwise`: exact projection identity for local AD
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set Metric

variable (g : SlopeFunction) (c d m : ℝ)

/-- Linear part DΦ of the anisotropic rescaling. -/
def dPhiLin (v : Point3) : Point3 :=
  let a := g (c + (d - c) / 2)
  let b := m * (d - c) / 2
  let S := 2 / (d - c)
  point3 (v 0 + a * v 1) (b * v 1) (S * v 2)

/-- DΦ^{-T}: inverse transpose of DΦ. -/
def dPhiInvT (w : Point3) : Point3 :=
  let a := g (c + (d - c) / 2)
  let b := m * (d - c) / 2
  let S := 2 / (d - c)
  point3 (w 0) (-a / b * w 0 + w 1 / b) (w 2 / S)

/-- Linear-map packaging of the inverse transpose. -/
def dPhiInvTLinear : Point3 →ₗ[ℝ] Point3 where
  toFun := dPhiInvT g c d m
  map_add' first second := by
    ext coordinate
    fin_cases coordinate <;> simp [dPhiInvT, point3] <;> ring
  map_smul' scalar point := by
    ext coordinate
    fin_cases coordinate <;> simp [dPhiInvT, point3] <;> ring

@[simp] theorem dPhiInvTLinear_apply (normal : Point3) :
    dPhiInvTLinear g c d m normal = dPhiInvT g c d m normal := rfl

/-- Exact incidence/projection identity: `inner(DΦ v, DΦ^{-T} w) = inner(v, w)`. -/
lemma dPhi_inner_identity (hcd : c < d) (hm : 0 < m) (v w : Point3) :
    inner ℝ (dPhiLin g c d m v) (dPhiInvT g c d m w) = inner ℝ v w := by
  let a := g (c + (d - c) / 2)
  let b := m * (d - c) / 2
  let S := 2 / (d - c)
  have hb_pos : 0 < b := by dsimp only [b] <;> positivity
  have hS_pos : 0 < S := by dsimp only [S] <;> positivity
  let x := dPhiLin g c d m v
  let y := dPhiInvT g c d m w
  have hx0 : x 0 = v 0 + a * v 1 := by
    simp [x, dPhiLin, a, b, S, point3] <;> ring
  have hx1 : x 1 = b * v 1 := by
    simp [x, dPhiLin, a, b, S, point3] <;> ring
  have hx2 : x 2 = S * v 2 := by
    simp [x, dPhiLin, a, b, S, point3] <;> ring
  have hy0 : y 0 = w 0 := by
    simp [y, dPhiInvT, a, b, S, point3] <;> ring
  have hy1 : y 1 = -a / b * w 0 + w 1 / b := by
    simp [y, dPhiInvT, a, b, S, point3] <;> ring
  have hy2 : y 2 = w 2 / S := by
    simp [y, dPhiInvT, a, b, S, point3] <;> ring
  have h_inner1 : inner ℝ x y = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 := by
    simp [inner, Fin.sum_univ_succ] <;> ring
  have h_inner2 : inner ℝ v w = v 0 * w 0 + v 1 * w 1 + v 2 * w 2 := by
    simp [inner, Fin.sum_univ_succ] <;> ring
  rw [h_inner1, h_inner2, hx0, hx1, hx2, hy0, hy1, hy2]
  field_simp [hb_pos.ne', hS_pos.ne'] <;> ring

/-- dPhiLin is linear. -/
lemma dPhiLin_sub (x y : Point3) :
    dPhiLin g c d m (x - y) = dPhiLin g c d m x - dPhiLin g c d m y := by
  ext i
  fin_cases i <;> simp [dPhiLin, point3] <;> ring

/-- dPhiInvT is linear. -/
lemma dPhiInvT_sub (x y : Point3) :
    dPhiInvT g c d m (x - y) = dPhiInvT g c d m x - dPhiInvT g c d m y := by
  ext i
  fin_cases i <;> simp [dPhiInvT, point3] <;> ring

/-!
## Normalization Lipschitz bound
-/

/-- Normalization bound: for `‖x‖, ‖y‖ ≥ m > 0`. -/
lemma normalization_lipschitz {x y : Point3} {m : ℝ} (hm_pos : 0 < m)
    (hx : m ≤ ‖x‖) (hy : m ≤ ‖y‖) :
    ‖(‖x‖⁻¹ : ℝ) • x - (‖y‖⁻¹ : ℝ) • y‖ ≤ (2 / m) * ‖x - y‖ := by
  have hx_pos : 0 < ‖x‖ := by linarith
  have hy_pos : 0 < ‖y‖ := by linarith
  set nx : ℝ := ‖x‖ with hnx
  set ny : ℝ := ‖y‖ with hny
  have h_decomp : (nx⁻¹ : ℝ) • x - (ny⁻¹ : ℝ) • y =
      (nx⁻¹ : ℝ) • (x - y) + ((nx⁻¹ - ny⁻¹ : ℝ) • y) := by
    calc
      (nx⁻¹ : ℝ) • x - (ny⁻¹ : ℝ) • y
        = (nx⁻¹ : ℝ) • (x - y) + (nx⁻¹ : ℝ) • y - (ny⁻¹ : ℝ) • y := by
          rw [smul_sub] <;> abel
      _ = (nx⁻¹ : ℝ) • (x - y) + ((nx⁻¹ - ny⁻¹ : ℝ) • y) := by
          rw [sub_smul] <;> abel
  rw [h_decomp]
  have h_term1 : ‖(nx⁻¹ : ℝ) • (x - y)‖ = nx⁻¹ * ‖x - y‖ := by
    have h : ‖(nx⁻¹ : ℝ) • (x - y)‖ = |nx⁻¹| * ‖x - y‖ := by
      exact norm_smul _ _
    rw [h]
    have hpos : 0 ≤ nx⁻¹ := by positivity
    rw [abs_of_nonneg hpos]
  have h_term2 : ‖((nx⁻¹ - ny⁻¹ : ℝ) • y)‖ = |nx⁻¹ - ny⁻¹| * ny := by
    have h : ‖((nx⁻¹ - ny⁻¹ : ℝ) • y)‖ = |nx⁻¹ - ny⁻¹| * ‖y‖ := by
      exact norm_smul _ _
    rw [h, hny]
  have h_abs : |nx⁻¹ - ny⁻¹| = |nx - ny| / (nx * ny) := by
    have h4 : nx⁻¹ - ny⁻¹ = (ny - nx) / (nx * ny) := by
      field_simp [hx_pos.ne', hy_pos.ne'] <;> ring
    rw [h4]
    have h5 : |(ny - nx) / (nx * ny)| = |ny - nx| / (nx * ny) := by
      rw [abs_div]
      <;> simp [abs_of_pos hx_pos, abs_of_pos hy_pos]
    rw [h5]
    <;> rw [show |ny - nx| = |nx - ny| by rw [abs_sub_comm]]
  have h_norm_diff : |nx - ny| ≤ ‖x - y‖ := by
    have h1 : nx - ny ≤ ‖x - y‖ := norm_sub_norm_le x y
    have h21 : ‖y‖ - ‖x‖ ≤ ‖y - x‖ := norm_sub_norm_le y x
    have h22 : ‖y - x‖ = ‖x - y‖ := by rw [norm_sub_rev]
    have h2 : ny - nx ≤ ‖x - y‖ := by rw [h22] at h21; exact h21
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  calc
    ‖(nx⁻¹ : ℝ) • (x - y) + ((nx⁻¹ - ny⁻¹ : ℝ) • y)‖
      ≤ ‖(nx⁻¹ : ℝ) • (x - y)‖ + ‖((nx⁻¹ - ny⁻¹ : ℝ) • y)‖ :=
        norm_add_le _ _
    _ = nx⁻¹ * ‖x - y‖ + |nx⁻¹ - ny⁻¹| * ny := by
      rw [h_term1, h_term2]
    _ = nx⁻¹ * ‖x - y‖ + (|nx - ny| / (nx * ny)) * ny := by rw [h_abs]
    _ = nx⁻¹ * ‖x - y‖ + |nx - ny| / nx := by
      field_simp [hx_pos.ne', hy_pos.ne'] <;> ring
    _ ≤ nx⁻¹ * ‖x - y‖ + ‖x - y‖ / nx := by
      gcongr
      <;> linarith [h_norm_diff]
    _ = 2 * nx⁻¹ * ‖x - y‖ := by
      field_simp [hx_pos.ne'] <;> ring
    _ ≤ (2 / m) * ‖x - y‖ := by
      have h5 : nx⁻¹ ≤ m⁻¹ := by
        have h6 : m ≤ nx := hx
        have h7 : 0 < m := hm_pos
        have h8 : 0 < nx := hx_pos
        gcongr
        <;> linarith
      have h9 : 2 * nx⁻¹ * ‖x - y‖ ≤ 2 * m⁻¹ * ‖x - y‖ := by
        gcongr
        <;> linarith
      have h10 : (2 / m) * ‖x - y‖ = 2 * m⁻¹ * ‖x - y‖ := by
        field_simp [hm_pos.ne'] <;> ring
      linarith

/-!
## Injectivity
-/

/-- dPhiLin is injective (det = b*S ≠ 0). -/
lemma dPhiLin_injective (hcd : c < d) (hm : 0 < m) :
    Function.Injective (dPhiLin g c d m) := by
  intro x y h
  set a := g (c + (d - c) / 2) with ha
  set b := m * (d - c) / 2 with hb
  set S := 2 / (d - c) with hS
  have hb_pos : 0 < b := by rw [hb] <;> positivity
  have hS_pos : 0 < S := by rw [hS] <;> positivity
  have h_eq2 : S * x 2 = S * y 2 := by
    have h2 : (dPhiLin g c d m x) 2 = (dPhiLin g c d m y) 2 := by rw [h]
    simpa [dPhiLin, ha, hb, hS, point3] using h2
  have hx2 : x 2 = y 2 := by
    apply (mul_right_inj' hS_pos.ne').mp
    exact h_eq2
  have h_eq1 : b * x 1 = b * y 1 := by
    have h1 : (dPhiLin g c d m x) 1 = (dPhiLin g c d m y) 1 := by rw [h]
    simpa [dPhiLin, ha, hb, hS, point3] using h1
  have hx1 : x 1 = y 1 := by
    apply (mul_right_inj' hb_pos.ne').mp
    exact h_eq1
  have h_eq0 : x 0 + a * x 1 = y 0 + a * y 1 := by
    have h0 : (dPhiLin g c d m x) 0 = (dPhiLin g c d m y) 0 := by rw [h]
    simpa [dPhiLin, ha, hb, hS, point3] using h0
  have hx0 : x 0 = y 0 := by
    rw [hx1] at h_eq0
    linarith
  ext i
  fin_cases i <;> tauto

/-- dPhiInvT is injective. -/
lemma dPhiInvT_injective (hcd : c < d) (hm : 0 < m) :
    Function.Injective (dPhiInvT g c d m) := by
  intro x y h
  set a := g (c + (d - c) / 2) with ha
  set b := m * (d - c) / 2 with hb
  set S := 2 / (d - c) with hS
  have hb_pos : 0 < b := by rw [hb] <;> positivity
  have hS_pos : 0 < S := by rw [hS] <;> positivity
  have h_eq0 : x 0 = y 0 := by
    have h0 : (dPhiInvT g c d m x) 0 = (dPhiInvT g c d m y) 0 := by rw [h]
    simpa [dPhiInvT, ha, hb, hS, point3] using h0
  have h_eq1 : -a / b * x 0 + x 1 / b = -a / b * y 0 + y 1 / b := by
    have h1 : (dPhiInvT g c d m x) 1 = (dPhiInvT g c d m y) 1 := by rw [h]
    simpa [dPhiInvT, ha, hb, hS, point3] using h1
  have hx1 : x 1 = y 1 := by
    rw [h_eq0] at h_eq1
    have h : x 1 / b = y 1 / b := by linarith
    have h2 : x 1 = y 1 := by
      field_simp [hb_pos.ne'] at h ⊢ <;> linarith
    exact h2
  have h_eq2 : x 2 / S = y 2 / S := by
    have h2 : (dPhiInvT g c d m x) 2 = (dPhiInvT g c d m y) 2 := by rw [h]
    simpa [dPhiInvT, ha, hb, hS, point3] using h2
  have hx2 : x 2 = y 2 := by
    field_simp [hS_pos.ne'] at h_eq2 ⊢ <;> linarith
  ext i
  fin_cases i <;> tauto

/-!
## Incidence preservation

If `|inner(dir, V)| ≤ delta`, then for the rescaled tube direction
`normalize(DΦ dir)` and transformed planeMap `normalize(DΦ^{-T} V)`:

  |inner(normalize(DΦ dir), normalize(DΦ^{-T} V))|
    = |inner(dir, V)| / (‖DΦ dir‖ · ‖DΦ^{-T} V‖)
    ≤ delta / (‖DΦ dir‖ · ‖DΦ^{-T} V‖)
-/

/-- Incidence preservation under normalization. -/
lemma incidence_preservation
    (hcd : c < d) (hm : 0 < m)
    (dir V : Point3) (hdir : dir ≠ 0) (hV : V ≠ 0) :
    inner ℝ (‖dPhiLin g c d m dir‖⁻¹ • dPhiLin g c d m dir)
      (‖dPhiInvT g c d m V‖⁻¹ • dPhiInvT g c d m V) =
    inner ℝ dir V / (‖dPhiLin g c d m dir‖ * ‖dPhiInvT g c d m V‖) := by
  set A := dPhiLin g c d m dir with hA
  set B := dPhiInvT g c d m V with hB
  have hA_ne : A ≠ 0 := by
    intro h
    have h' : dPhiLin g c d m dir = 0 := h
    have h'' : dPhiLin g c d m dir = dPhiLin g c d m 0 := by
      rw [h'] <;> simp [dPhiLin, point3]
    exact hdir (dPhiLin_injective g c d m hcd hm h'')
  have hB_ne : B ≠ 0 := by
    intro h
    have h' : dPhiInvT g c d m V = 0 := h
    have h'' : dPhiInvT g c d m V = dPhiInvT g c d m 0 := by
      rw [h'] <;> simp [dPhiInvT, point3]
    exact hV (dPhiInvT_injective g c d m hcd hm h'')
  have h1 : inner ℝ (‖A‖⁻¹ • A) (‖B‖⁻¹ • B) =
      ‖A‖⁻¹ * ‖B‖⁻¹ * inner ℝ A B := by
    simp [inner_smul_left, inner_smul_right] <;> ring
  rw [h1]
  have h2 : inner ℝ A B = inner ℝ dir V :=
    dPhi_inner_identity g c d m hcd hm dir V
  rw [h2]
  <;> field_simp [norm_ne_zero_iff.mpr hA_ne, norm_ne_zero_iff.mpr hB_ne] <;> ring

/-!
## Local AD projection identity
-/

/-- Exact pointwise projection identity for local AD transfer. -/
lemma local_ad_projection_pointwise
    (hcd : c < d) (hm : 0 < m)
    {V : Point3 → Point3} (p p' : Point3) :
    inner ℝ (dPhiLin g c d m p' - dPhiLin g c d m p)
      (dPhiInvT g c d m (V p)) =
    inner ℝ (p' - p) (V p) := by
  have h1 : dPhiLin g c d m p' - dPhiLin g c d m p = dPhiLin g c d m (p' - p) :=
    (dPhiLin_sub g c d m p' p).symm
  rw [h1]
  exact dPhi_inner_identity g c d m hcd hm (p' - p) (V p)

/-!
## Horizontal component bound for rescaled directions

When the original direction is in the vertical chart (`|v 2| ≥ 1/2`) and the
slab is narrow (`d - c ≤ 1/25`), the rescaled direction `DΦ · v` is dominated
by its z-component. This gives explicit bounds on the horizontal component
fractions, which are needed for incidence with the height-dependent normal.
-/

/-- Horizontal component bound for a rescaled direction in the vertical chart.

Given `‖v‖ = 1`, `|v 2| ≥ 1/2`, `|g(center)| ≤ 1`, `m ≤ 1`, and `d - c ≤ 1/25`,
both horizontal components of `DΦ · v` are bounded by `(1/10) * ‖DΦ · v‖`. -/
lemma rescaledDirection_horizontal_bound
    (g : SlopeFunction) (c d m : ℝ)
    (hcd : c < d) (hm_pos : 0 < m) (hm_le_one : m ≤ 1)
    (h_len : d - c ≤ 1 / 25)
    (hg_abs : |g (c + (d - c) / 2)| ≤ 1)
    {v : Point3} (hv_unit : ‖v‖ = 1) (hv_vert : (1 / 2 : ℝ) ≤ |v 2|) :
    |(dPhiLin g c d m v) 0| ≤ (1 / 10 : ℝ) * ‖dPhiLin g c d m v‖ ∧
    |(dPhiLin g c d m v) 1| ≤ (1 / 10 : ℝ) * ‖dPhiLin g c d m v‖ := by
  set a : ℝ := g (c + (d - c) / 2) with ha_def
  set b : ℝ := m * (d - c) / 2 with hb_def
  set S : ℝ := 2 / (d - c) with hS_def
  set L : Point3 := dPhiLin g c d m v with hL_def
  have hb_le : b ≤ 1 / 50 := by
    rw [hb_def]
    have h : m ≤ 1 := hm_le_one
    have h2 : d - c ≤ 1 / 25 := h_len
    nlinarith
  have hS_ge : S ≥ 50 := by
    rw [hS_def]
    have h_pos : 0 < d - c := by linarith
    have h : 2 / (d - c) ≥ 50 := by
      calc 2 / (d - c) ≥ 2 / (1 / 25 : ℝ) := by gcongr
           _ = 50 := by norm_num
    exact h
  have hvi0 : |v 0| ≤ 1 := by
    have hsq : (v 0) ^ 2 ≤ ‖v‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq v]
      <;> exact Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ 0)
    have hsq1 : (v 0) ^ 2 ≤ 1 := by
      have h : ‖v‖ ^ 2 = 1 := by rw [hv_unit] <;> norm_num
      rw [h] at hsq
      exact hsq
    have habs : |v 0| ^ 2 ≤ 1 := by
      rw [sq_abs] <;> exact hsq1
    have hpos : 0 ≤ |v 0| := by positivity
    nlinarith
  have hvi1 : |v 1| ≤ 1 := by
    have hsq : (v 1) ^ 2 ≤ ‖v‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq v]
      <;> exact Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ 1)
    have hsq1 : (v 1) ^ 2 ≤ 1 := by
      have h : ‖v‖ ^ 2 = 1 := by rw [hv_unit] <;> norm_num
      rw [h] at hsq
      exact hsq
    have habs : |v 1| ^ 2 ≤ 1 := by
      rw [sq_abs] <;> exact hsq1
    have hpos : 0 ≤ |v 1| := by positivity
    nlinarith
  have hL0_eq : L 0 = v 0 + a * v 1 := by
    simp [hL_def, dPhiLin, ha_def, point3] <;> ring
  have hL1_eq : L 1 = b * v 1 := by
    simp [hL_def, dPhiLin, hb_def, point3] <;> ring
  have hL2_eq : L 2 = S * v 2 := by
    simp [hL_def, dPhiLin, hS_def, point3] <;> ring
  have hL0_abs : |L 0| ≤ 2 := by
    rw [hL0_eq]
    have h1 : |v 0 + a * v 1| ≤ |v 0| + |a * v 1| := abs_add_le _ _
    have h2 : |a * v 1| = |a| * |v 1| := by rw [abs_mul]
    have h3 : |a| ≤ 1 := hg_abs
    have h4 : |a * v 1| ≤ 1 := by
      rw [h2]
      have h5 : |a| * |v 1| ≤ 1 * 1 := by gcongr <;> linarith
      linarith
    calc |v 0 + a * v 1|
      ≤ |v 0| + |a * v 1| := h1
    _ ≤ 1 + 1 := by linarith [hvi0, h4]
    _ = 2 := by norm_num
  have hL1_abs : |L 1| ≤ 1 / 50 := by
    rw [hL1_eq]
    have hpos : 0 ≤ b := by positivity
    have h : |b * v 1| = |b| * |v 1| := by rw [abs_mul]
    have h' : |b| = b := abs_of_nonneg hpos
    rw [h, h']
    have h4 : b ≤ 1 / 50 := hb_le
    have h6 : |v 1| ≤ 1 := hvi1
    nlinarith
  have hL2_lower : |L 2| ≥ 25 := by
    rw [hL2_eq]
    have hpos : 0 ≤ S := by linarith
    have h : |S * v 2| = |S| * |v 2| := by rw [abs_mul]
    have h' : |S| = S := abs_of_nonneg hpos
    rw [h, h']
    have h1 : S ≥ 50 := hS_ge
    have h2 : |v 2| ≥ 1 / 2 := hv_vert
    nlinarith
  have h_norm_lower : ‖L‖ ≥ 25 := by
    have h : |L 2| ≤ ‖L‖ := PiLp.norm_apply_le L 2
    linarith [hL2_lower]
  have hL0_bound : |L 0| ≤ (1 / 10 : ℝ) * ‖L‖ := by
    have h : (1 / 10 : ℝ) * ‖L‖ ≥ 5 / 2 := by
      have h2 : ‖L‖ ≥ 25 := h_norm_lower
      linarith
    linarith [hL0_abs]
  have hL1_bound : |L 1| ≤ (1 / 10 : ℝ) * ‖L‖ := by
    have h : (1 / 10 : ℝ) * ‖L‖ ≥ 5 / 2 := by
      have h2 : ‖L‖ ≥ 25 := h_norm_lower
      linarith
    linarith [hL1_abs]
  exact ⟨hL0_bound, hL1_bound⟩

end Kakeya.Assouad

end
