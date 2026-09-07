import MyLeanRepo.Kakeya.Assouad.Definitions
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Unit rescaling map for WZ1 global planiness

Anisotropic rescaling around a selected coarse tube:
1. Translate by `-lineBase`
2. Reflect via `Submodule.reflection` sending `lineDir` to `e3 = (0,0,1)`
3. Scale transverse coordinates (x,y) by `1/rho`, keep z unchanged

Volume scales by `(1/rho)^2`.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set Metric

/-- Third standard basis vector in Point3. -/
def e3 : Point3 := EuclideanSpace.single (2 : Fin 3) 1

/-- Norm of `e3`. -/
lemma e3_norm : ‖e3‖ = 1 := by
  simp [e3]

/-- Reflection sending unit vector `d` to `e3`. -/
def householderToE3 (d : Point3) (_hd : ‖d‖ = 1) : Point3 ≃ₗᵢ[ℝ] Point3 :=
  Submodule.reflection (ℝ ∙ (d - e3))ᗮ

lemma householderToE3_sends_d_to_e3 (d : Point3) (hd : ‖d‖ = 1) :
    householderToE3 d hd d = e3 := by
  rw [householderToE3]
  exact Submodule.reflection_sub (by rw [hd, e3_norm])

lemma householderToE3_sends_e3_to_d (d : Point3) (hd : ‖d‖ = 1) :
    householderToE3 d hd e3 = d := by
  have h1 := (householderToE3 d hd).injective
  have h2 : householderToE3 d hd (householderToE3 d hd e3) = householderToE3 d hd d := by
    have h3 : (householderToE3 d hd) (householderToE3 d hd e3) = e3 :=
      (householderToE3 d hd).apply_symm_apply e3
    rw [h3, householderToE3_sends_d_to_e3 d hd]
  exact h1 h2

lemma householderToE3_norm (d : Point3) (hd : ‖d‖ = 1) (p : Point3) :
    ‖householderToE3 d hd p‖ = ‖p‖ :=
  (householderToE3 d hd).norm_map p

lemma householderToE3_orthogonal (d : Point3) (hd : ‖d‖ = 1) (p q : Point3) :
    inner ℝ (householderToE3 d hd p) (householderToE3 d hd q) = inner ℝ p q :=
  (householderToE3 d hd).inner_map_map p q

lemma householderToE3_symmetric (d : Point3) (hd : ‖d‖ = 1) (p q : Point3) :
    inner ℝ (householderToE3 d hd p) q = inner ℝ p (householderToE3 d hd q) := by
  let A := householderToE3 d hd
  have h1 : A (A q) = q := A.apply_symm_apply q
  have h2 : inner ℝ (A p) q = inner ℝ (A p) (A (A q)) := by rw [h1]
  rw [h2]
  exact A.inner_map_map p (A q)

lemma householderToE3_involution (d : Point3) (hd : ‖d‖ = 1) (p : Point3) :
    householderToE3 d hd (householderToE3 d hd p) = p :=
  (householderToE3 d hd).apply_symm_apply p

/-- Determinant of the reflection has absolute value 1. -/
lemma householderToE3_abs_det (d : Point3) (hd : ‖d‖ = 1) :
    |LinearMap.det (householderToE3 d hd).toLinearMap| = 1 := by
  let A := householderToE3 d hd
  let x := LinearMap.det A.toLinearMap
  have h1 : A.symm = A := Submodule.reflection_symm
  have h2 : LinearMap.det A.symm.toLinearMap = x := by
    rw [h1] <;> rfl
  have h3 : x * LinearMap.det A.symm.toLinearMap = 1 := by
    have h4 : LinearMap.det (A.toLinearMap.comp A.symm.toLinearMap) = 1 := by
      have h5 : A.toLinearMap.comp A.symm.toLinearMap = LinearMap.id := by
        ext z; simp
      rw [h5] <;> simp
    rw [LinearMap.det_comp] at h4
    exact h4
  rw [h2] at h3
  have h4 : x ^ 2 = 1 := by linarith
  have h5 : 0 ≤ |x| := abs_nonneg x
  have h6 : |x| ^ 2 = 1 := by
    rw [sq_abs] <;> exact h4
  nlinarith

/-- Transverse anisotropic scaling linear map: scales coords 0,1 by 1/rho, keeps coord 2. -/
def transverseScaleLin (rho : ℝ) : Point3 →ₗ[ℝ] Point3 :=
  let f : Point3 → Point3 := fun p => point3 (p 0 / rho) (p 1 / rho) (p 2)
  { toFun := f
    map_add' := by
      intro p q
      have h : ∀ (i : Fin 3), (f (p + q)) i = (f p + f q) i := by
        intro i
        fin_cases i <;> simp [f, point3] <;> ring
      exact PiLp.ext h
    map_smul' := by
      intro c p
      have h : ∀ (i : Fin 3), (f (c • p)) i = (c • f p) i := by
        intro i
        fin_cases i <;> simp [f, point3, smul_eq_mul] <;> ring
      exact PiLp.ext h }

lemma transverseScaleLin_coord0 (rho : ℝ) (p : Point3) :
    (transverseScaleLin rho p) 0 = p 0 / rho := by
  simp [transverseScaleLin, point3]

lemma transverseScaleLin_coord1 (rho : ℝ) (p : Point3) :
    (transverseScaleLin rho p) 1 = p 1 / rho := by
  simp [transverseScaleLin, point3]

lemma transverseScaleLin_coord2 (rho : ℝ) (p : Point3) :
    (transverseScaleLin rho p) 2 = p 2 := by
  simp [transverseScaleLin, point3]

lemma transverseScaleLin_det (rho : ℝ) (_hrho : 0 < rho) :
    LinearMap.det (transverseScaleLin rho) = (1 / rho) ^ 2 := by
  let b : Module.Basis (Fin 3) ℝ Point3 := PiLp.basisFun 2 ℝ (Fin 3)
  have h1 : LinearMap.det (transverseScaleLin rho) =
      (LinearMap.toMatrix b b (transverseScaleLin rho)).det := by
    rw [← LinearMap.det_toMatrix b (transverseScaleLin rho)]
  rw [h1]
  have h2 : (LinearMap.toMatrix b b (transverseScaleLin rho)) =
      !![1 / rho, 0, 0; 0, 1 / rho, 0; 0, 0, 1] := by
    ext i j
    have h3 : (LinearMap.toMatrix b b (transverseScaleLin rho)) i j =
        (transverseScaleLin rho (b j)) i := by
      simp [LinearMap.toMatrix_apply]
      <;> rfl
    rw [h3]
    fin_cases i <;> fin_cases j <;>
      simp [transverseScaleLin_coord0, transverseScaleLin_coord1,
            transverseScaleLin_coord2, b, PiLp.basisFun_apply,
            PiLp.single_apply] <;> ring
  rw [h2]
  simp [Matrix.det_fin_three] <;> ring

/-- Norm of transverse scaling: scales L2 norm by 1/rho when z-component is zero. -/
lemma transverseScaleLin_norm_of_coord2_zero (rho : ℝ) (hrho : 0 < rho) (p : Point3)
    (h : p 2 = 0) :
    ‖transverseScaleLin rho p‖ = ‖p‖ / rho := by
  have h1 : transverseScaleLin rho p = (1 / rho) • p := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [transverseScaleLin_coord0, transverseScaleLin_coord1,
          transverseScaleLin_coord2, h, smul_eq_mul] <;> ring
  rw [h1, norm_smul]
  have h2 : ‖(1 / rho : ℝ)‖ = 1 / rho := by
    have hpos' : 0 < (1 / rho : ℝ) := by positivity
    have h3 : ‖(1 / rho : ℝ)‖ = |(1 / rho : ℝ)| := Real.norm_eq_abs (1 / rho)
    rw [h3, abs_of_pos hpos']
  rw [h2] <;> ring

/--
Unit rescaling map: translate by `-lineBase`, reflect `lineDir` to e3,
scale transverse coords by `1/rho`.
-/
def unitRescalingMap (lineBase lineDir : Point3) (hd : ‖lineDir‖ = 1)
    (rho : ℝ) (hrho : 0 < rho) (p : Point3) : Point3 :=
  transverseScaleLin rho (householderToE3 lineDir hd (p - lineBase))

/--
The normalized WZ1 unit-rescaling map anchored on a distinguished tube.

The paper includes a fixed dimensional constant `c(3) ∼ 1` in the
transverse dilation and centers the distinguished unit segment in the target
window.  We freeze the harmless concrete choice `c(3) = 1 / 100`: subtract
the midpoint of the anchor segment, reflect its direction to `e3`, and divide
the transverse coordinates by `100 * rho`.

The target tubes still have radius `delta / rho`; this is a fixed enlargement
of the exact image radius `delta / (100 * rho)` and allows the rediscretized
family to satisfy the repository's cropped unit-ball convention after the
usual small-scale threshold.
-/
def wz1AnchoredUnitRescalingMap
    {delta : ℝ} (anchor : Kakeya.DeltaTube delta)
    (rho : ℝ) (hrho : 0 < rho) (p : Point3) : Point3 :=
  unitRescalingMap
    (anchor.base + (1 / 2 : ℝ) • anchor.direction)
    anchor.direction anchor.direction_unit
    (100 * rho) (by positivity) p

/-- The linear part D ∘ R. -/
def unitRescalingLinear (lineDir : Point3) (hd : ‖lineDir‖ = 1) (rho : ℝ) :
    Point3 →ₗ[ℝ] Point3 :=
  (transverseScaleLin rho).comp (householderToE3 lineDir hd).toLinearMap

/--
The inverse-transpose action on plane normals for `unitRescalingLinear`.

The point map is `D_rho ∘ R`, where `D_rho` divides the first two
coordinates by `rho` and `R` is the Householder reflection.  Plane normals
therefore transform by `(D_rho ∘ R)⁻ᵀ = D_(1/rho) ∘ R`.  Applying
`unitRescalingLinear` itself to a normal is geometrically incorrect.
-/
def unitRescalingNormalLinear
    (lineDir : Point3) (hd : ‖lineDir‖ = 1) (rho : ℝ) :
    Point3 →ₗ[ℝ] Point3 :=
  (transverseScaleLin (1 / rho)).comp
    (householderToE3 lineDir hd).toLinearMap

/--
The point and normal transforms preserve their scalar pairing.
-/
lemma inner_unitRescalingLinear_unitRescalingNormalLinear
    (lineDir : Point3) (hd : ‖lineDir‖ = 1)
    (rho : ℝ) (hrho : 0 < rho) (v normal : Point3) :
    inner ℝ
        (unitRescalingLinear lineDir hd rho v)
        (unitRescalingNormalLinear lineDir hd rho normal) =
      inner ℝ v normal := by
  let reflectedPoint := householderToE3 lineDir hd v
  let reflectedNormal := householderToE3 lineDir hd normal
  have hcoordinates :
      ∀ a b : Point3,
        inner ℝ a b =
          a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := by
    intro a b
    rw [PiLp.inner_apply]
    simp [Fin.sum_univ_succ, mul_comm]
    <;> ring
  have hpoint :
      unitRescalingLinear lineDir hd rho v =
        transverseScaleLin rho reflectedPoint := by
    rfl
  have hnormal :
      unitRescalingNormalLinear lineDir hd rho normal =
        transverseScaleLin (1 / rho) reflectedNormal := by
    rfl
  rw [hpoint, hnormal, hcoordinates]
  rw [transverseScaleLin_coord0, transverseScaleLin_coord1,
    transverseScaleLin_coord2, transverseScaleLin_coord0,
    transverseScaleLin_coord1, transverseScaleLin_coord2]
  have hrho_inv : (1 / rho : ℝ) ≠ 0 := by positivity
  have hscaled :
      reflectedPoint 0 / rho * (reflectedNormal 0 / (1 / rho)) +
          reflectedPoint 1 / rho *
              (reflectedNormal 1 / (1 / rho)) +
            reflectedPoint 2 * reflectedNormal 2 =
        reflectedPoint 0 * reflectedNormal 0 +
          reflectedPoint 1 * reflectedNormal 1 +
            reflectedPoint 2 * reflectedNormal 2 := by
    field_simp [hrho.ne', hrho_inv]
    <;> ring
  rw [hscaled, ← hcoordinates]
  exact householderToE3_orthogonal lineDir hd v normal

/-- Linear part of `wz1AnchoredUnitRescalingMap`. -/
def wz1AnchoredUnitRescalingLinear
    {delta : ℝ} (anchor : Kakeya.DeltaTube delta)
    (rho : ℝ) : Point3 →ₗ[ℝ] Point3 :=
  unitRescalingLinear
    anchor.direction anchor.direction_unit (100 * rho)

/-- Inverse-transpose action on normals for the anchored map. -/
def wz1AnchoredUnitRescalingNormalLinear
    {delta : ℝ} (anchor : Kakeya.DeltaTube delta)
    (rho : ℝ) : Point3 →ₗ[ℝ] Point3 :=
  unitRescalingNormalLinear
    anchor.direction anchor.direction_unit (100 * rho)

/-- The anchored point and normal transforms preserve scalar pairing. -/
lemma inner_wz1AnchoredUnitRescalingLinear_normal
    {delta : ℝ} (anchor : Kakeya.DeltaTube delta)
    (rho : ℝ) (hrho : 0 < rho) (v normal : Point3) :
    inner ℝ
        (wz1AnchoredUnitRescalingLinear anchor rho v)
        (wz1AnchoredUnitRescalingNormalLinear anchor rho normal) =
      inner ℝ v normal :=
  inner_unitRescalingLinear_unitRescalingNormalLinear
    anchor.direction anchor.direction_unit
    (100 * rho) (by positivity) v normal

/-- Differences of anchored images are governed by the anchored linear map. -/
lemma wz1AnchoredUnitRescalingMap_sub
    {delta : ℝ} (anchor : Kakeya.DeltaTube delta)
    (rho : ℝ) (hrho : 0 < rho) (p q : Point3) :
    wz1AnchoredUnitRescalingMap anchor rho hrho p -
        wz1AnchoredUnitRescalingMap anchor rho hrho q =
      wz1AnchoredUnitRescalingLinear anchor rho (p - q) := by
  let center :=
    anchor.base + (1 / 2 : ℝ) • anchor.direction
  let reflection :=
    householderToE3 anchor.direction anchor.direction_unit
  let scaling := transverseScaleLin (100 * rho)
  change
    scaling (reflection (p - center)) -
        scaling (reflection (q - center)) =
      scaling (reflection (p - q))
  have hcenter :
      (p - center) - (q - center) = p - q := by
    abel
  calc
    scaling (reflection (p - center)) -
          scaling (reflection (q - center)) =
        scaling
          (reflection (p - center) -
            reflection (q - center)) := by
      exact (map_sub scaling _ _).symm
    _ = scaling
          (reflection
            ((p - center) - (q - center))) := by
      exact congrArg scaling
        ((map_sub reflection (p - center) (q - center)).symm)
    _ = scaling (reflection (p - q)) := by
      rw [hcenter]

/-- z-component of linear part equals projection onto original line direction. -/
lemma unitRescalingLinear_coord2 (lineDir : Point3) (hd : ‖lineDir‖ = 1)
    (rho : ℝ) (v : Point3) :
    (unitRescalingLinear lineDir hd rho v) 2 = inner ℝ v lineDir := by
  have h_main : (unitRescalingLinear lineDir hd rho v) 2 =
      (householderToE3 lineDir hd v) 2 := by
    simp [unitRescalingLinear, transverseScaleLin_coord2]
  rw [h_main]
  have h_coord2 : (householderToE3 lineDir hd v) 2 =
      inner ℝ (householderToE3 lineDir hd v) e3 := by
    have h := EuclideanSpace.inner_single_right (2 : Fin 3) (1 : ℝ)
        (householderToE3 lineDir hd v)
    simpa [e3] using h.symm
  rw [h_coord2]
  have h_sym : inner ℝ (householderToE3 lineDir hd v) e3 =
      inner ℝ v (householderToE3 lineDir hd e3) :=
    householderToE3_symmetric lineDir hd v e3
  rw [h_sym, householderToE3_sends_e3_to_d lineDir hd]

/-- For vectors perpendicular to lineDir, norm scales by 1/rho. -/
lemma unitRescalingLinear_perp_norm (lineDir : Point3) (hd : ‖lineDir‖ = 1)
    (rho : ℝ) (hrho : 0 < rho) (v : Point3) (hperp : inner ℝ v lineDir = 0) :
    ‖unitRescalingLinear lineDir hd rho v‖ = ‖v‖ / rho := by
  let w := householderToE3 lineDir hd v
  have h_w2 : w 2 = 0 := by
    have h : (unitRescalingLinear lineDir hd rho v) 2 = inner ℝ v lineDir :=
      unitRescalingLinear_coord2 lineDir hd rho v
    simpa [unitRescalingLinear, transverseScaleLin_coord2, hperp] using h
  have h_norm_w : ‖w‖ = ‖v‖ := householderToE3_norm lineDir hd v
  have h_main : ‖transverseScaleLin rho w‖ = ‖w‖ / rho :=
    transverseScaleLin_norm_of_coord2_zero rho hrho w h_w2
  simpa [unitRescalingLinear] using h_main.trans (by rw [h_norm_w])

/-- z-coordinate equals projection onto original line direction. -/
lemma unitRescalingMap_coord2 (lineBase lineDir : Point3) (hd : ‖lineDir‖ = 1)
    (rho : ℝ) (hrho : 0 < rho) (p : Point3) :
    (unitRescalingMap lineBase lineDir hd rho hrho p) 2 =
      inner ℝ (p - lineBase) lineDir := by
  have h_main : (unitRescalingMap lineBase lineDir hd rho hrho p) 2 =
      (householderToE3 lineDir hd (p - lineBase)) 2 := by
    simp [unitRescalingMap, transverseScaleLin_coord2]
  rw [h_main]
  have h_coord2 : (householderToE3 lineDir hd (p - lineBase)) 2 =
      inner ℝ (householderToE3 lineDir hd (p - lineBase)) e3 := by
    have h := EuclideanSpace.inner_single_right (2 : Fin 3) (1 : ℝ)
        (householderToE3 lineDir hd (p - lineBase))
    simpa [e3] using h.symm
  rw [h_coord2]
  have h_sym : inner ℝ (householderToE3 lineDir hd (p - lineBase)) e3 =
      inner ℝ (p - lineBase) (householderToE3 lineDir hd e3) :=
    householderToE3_symmetric lineDir hd (p - lineBase) e3
  rw [h_sym, householderToE3_sends_e3_to_d lineDir hd]

/-- Volume scaling: volume(Φ '' X) = (1/rho)^2 * volume(X). -/
lemma unitRescalingMap_volume (lineBase lineDir : Point3) (hd : ‖lineDir‖ = 1)
    (rho : ℝ) (hrho : 0 < rho) (X : Set Point3) (hX : MeasurableSet X) :
    volume (unitRescalingMap lineBase lineDir hd rho hrho '' X) =
      ENNReal.ofReal ((1 / rho) ^ 2) * volume X := by
  let L : Point3 →L[ℝ] Point3 :=
    (unitRescalingLinear lineDir hd rho).toContinuousLinearMap
  let t : Point3 := -L lineBase
  have h_eq1 : unitRescalingMap lineBase lineDir hd rho hrho = fun p => L p + t := by
    funext p
    have h2 : L p + t = L (p - lineBase) := by
      simp [t, LinearMap.map_sub] <;> abel
    have h3 : unitRescalingMap lineBase lineDir hd rho hrho p = L (p - lineBase) := by
      rfl
    rw [h3, h2]
  rw [h_eq1]
  have h_abs_det : |LinearMap.det (unitRescalingLinear lineDir hd rho)| = (1 / rho) ^ 2 := by
    have h1 : LinearMap.det (unitRescalingLinear lineDir hd rho) =
        LinearMap.det (transverseScaleLin rho) *
        LinearMap.det (householderToE3 lineDir hd).toLinearMap := by
      simp [unitRescalingLinear, LinearMap.det_comp] <;> ring
    rw [h1, transverseScaleLin_det rho hrho]
    rw [abs_mul, householderToE3_abs_det lineDir hd]
    have hpos : 0 ≤ (1 / rho) ^ 2 := by positivity
    rw [abs_of_nonneg hpos] <;> ring
  have h_translation : volume ((fun p : Point3 => L p + t) '' X) = volume (L '' X) := by
    have h_eq2 : (fun p : Point3 => L p + t) '' X = (fun x : Point3 => x + t) '' (L '' X) := by
      ext y
      constructor
      · rintro ⟨p, hp, rfl⟩
        exact ⟨L p, ⟨p, hp, rfl⟩, rfl⟩
      · rintro ⟨z, ⟨p, hp, rfl⟩, rfl⟩
        exact ⟨p, hp, rfl⟩
    rw [h_eq2]
    have h_img : (fun x : Point3 => x + t) '' (L '' X) =
        (fun x : Point3 => x + (-t)) ⁻¹' (L '' X) := by
      ext y
      simp [sub_eq_iff_eq_add] <;> constructor <;> rintro ⟨x, hx, hxy⟩ <;> exact ⟨x, hx, by simpa using hxy⟩
    rw [h_img]
    exact MeasureTheory.measure_preimage_add_right volume (-t) (L '' X)
  rw [h_translation]
  have h_main : volume (L '' X) =
      ENNReal.ofReal |LinearMap.det (unitRescalingLinear lineDir hd rho)| * volume X :=
    MeasureTheory.Measure.addHaar_image_continuousLinearMap volume L X
  rw [h_main, h_abs_det]

/-- Horizontal slices correspond to lineDir-slices of original set. -/
lemma unitRescalingMap_horizontalSlice (lineBase lineDir : Point3)
    (hd : ‖lineDir‖ = 1) (rho : ℝ) (hrho : 0 < rho)
    (E : Set Point3) (z : ℝ) :
    horizontalSlice (unitRescalingMap lineBase lineDir hd rho hrho '' E) z =
      unitRescalingMap lineBase lineDir hd rho hrho ''
        (E ∩ {p | inner ℝ (p - lineBase) lineDir = z}) := by
  ext y
  constructor
  · intro hy
    have hy_in : y ∈ unitRescalingMap lineBase lineDir hd rho hrho '' E := hy.1
    have hy_z : y 2 = z := hy.2
    rcases hy_in with ⟨p, hp, hpy⟩
    have hz : (unitRescalingMap lineBase lineDir hd rho hrho p) 2 = z := by
      rw [hpy] <;> exact hy_z
    have h9 : inner ℝ (p - lineBase) lineDir = z := by
      rw [unitRescalingMap_coord2 lineBase lineDir hd rho hrho p] at hz
      exact hz
    exact ⟨p, ⟨hp, h9⟩, hpy⟩
  · rintro ⟨p, ⟨hp, h9⟩, hpy⟩
    have hz : (unitRescalingMap lineBase lineDir hd rho hrho p) 2 = z := by
      rw [unitRescalingMap_coord2 lineBase lineDir hd rho hrho p, h9]
    have h10 : y ∈ unitRescalingMap lineBase lineDir hd rho hrho '' E := by
      exact ⟨p, hp, hpy⟩
    exact ⟨h10, by rw [← hpy] <;> exact hz⟩

end Kakeya.Assouad

end
