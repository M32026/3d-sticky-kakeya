module

public import MyLeanRepo.RadialBootstrapping.Basic

@[expose] public section

/-!
# Tube Family Construction

Constructs a finite family of lines at scale `r` using an angle-offset net
with spacing `Δ = r/10`.

Main results:
- `lineOfAngleOffset θ a` — line with normal angle `θ` and signed offset `a`
- `tubeFamily r` — finite set of lines at scale `r`
- `tubeFamily_card_le` — cardinality bound `|tubeFamily r| ≤ C₁ / r²`
-/

open MeasureTheory Metric Set Finset

noncomputable section

namespace RadialBootstrapping

-- ============================================================================
-- 1. Vector helpers
-- ============================================================================

/-- Standard basis vector e₀ = (1, 0). -/
def e0 : Point := PiLp.single (2 : ENNReal) (0 : Fin 2) (1 : ℝ)

/-- Standard basis vector e₁ = (0, 1). -/
def e1 : Point := PiLp.single (2 : ENNReal) (1 : Fin 2) (1 : ℝ)

/-- Unit normal vector for angle θ: (cos θ, sin θ). -/
def normalVec (θ : ℝ) : Point :=
  Real.cos θ • e0 + Real.sin θ • e1

/-- Direction vector for angle θ: (-sin θ, cos θ). -/
def dirVec (θ : ℝ) : Point :=
  -Real.sin θ • e0 + Real.cos θ • e1

lemma normalVec_component0 (θ : ℝ) : (normalVec θ) 0 = Real.cos θ := by
  simp [normalVec, e0, e1, PiLp.single_apply]
  <;> norm_num

lemma normalVec_component1 (θ : ℝ) : (normalVec θ) 1 = Real.sin θ := by
  simp [normalVec, e0, e1, PiLp.single_apply]
  <;> norm_num

lemma dirVec_component0 (θ : ℝ) : (dirVec θ) 0 = -Real.sin θ := by
  simp [dirVec, e0, e1, PiLp.single_apply]
  <;> norm_num

lemma dirVec_component1 (θ : ℝ) : (dirVec θ) 1 = Real.cos θ := by
  simp [dirVec, e0, e1, PiLp.single_apply]
  <;> norm_num

lemma normalVec_ne_zero (θ : ℝ) : normalVec θ ≠ (0 : Point) := by
  intro h
  have h1 : (normalVec θ) 0 = 0 := by rw [h] <;> simp
  have h2 : (normalVec θ) 1 = 0 := by rw [h] <;> simp
  have hcos : Real.cos θ = 0 := by
    rw [normalVec_component0 θ] at h1; exact h1
  have hsin : Real.sin θ = 0 := by
    rw [normalVec_component1 θ] at h2; exact h2
  have h3 : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
  rw [hcos, hsin] at h3
  norm_num at h3

lemma dirVec_ne_zero (θ : ℝ) : dirVec θ ≠ (0 : Point) := by
  intro h
  have h1 : (dirVec θ) 0 = 0 := by rw [h] <;> simp
  have h2 : (dirVec θ) 1 = 0 := by rw [h] <;> simp
  have hsin : Real.sin θ = 0 := by
    rw [dirVec_component0 θ] at h1; linarith
  have hcos : Real.cos θ = 0 := by
    rw [dirVec_component1 θ] at h2; exact h2
  have h3 : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
  rw [hcos, hsin] at h3
  norm_num at h3

-- ============================================================================
-- 2. Line construction
-- ============================================================================

/-- Affine subspace for line with normal angle θ and offset a. -/
def lineOfAngleOffset_aff (θ a : ℝ) : AffineSubspace ℝ Point :=
  let v : Point := dirVec θ
  let pt : Point := a • normalVec θ
  let direction : Submodule ℝ Point := Submodule.span ℝ {v}
  AffineSubspace.mk' pt direction

lemma lineOfAngleOffset_aff_direction (θ a : ℝ) :
    (lineOfAngleOffset_aff θ a).direction = Submodule.span ℝ ({dirVec θ} : Set Point) := by
  dsimp only [lineOfAngleOffset_aff]
  rw [AffineSubspace.direction_mk']

lemma lineOfAngleOffset_finrank (θ a : ℝ) :
    Module.finrank ℝ (lineOfAngleOffset_aff θ a).direction = 1 := by
  rw [lineOfAngleOffset_aff_direction]
  exact finrank_span_singleton (dirVec_ne_zero θ)

/-- Create a line with normal angle `θ` and signed offset `a`. -/
def lineOfAngleOffset (θ a : ℝ) : Line2 :=
  ⟨lineOfAngleOffset_aff θ a, lineOfAngleOffset_finrank θ a⟩

/-- The base point lies on the constructed line. -/
lemma lineOfAngleOffset_basePoint_mem (θ a : ℝ) :
    a • normalVec θ ∈ (lineOfAngleOffset θ a).toAffine := by
  have h : a • normalVec θ ∈ lineOfAngleOffset_aff θ a := by
    rw [lineOfAngleOffset_aff, AffineSubspace.mem_mk']
    <;> simp
  exact h

-- ============================================================================
-- 3. Tube family with Δ = r/10
-- ============================================================================

/-- Net spacing Δ = r/10. -/
def delta (r : ℝ) : ℝ := r / 10

/-- Number of angle samples. -/
def numAngles (r : ℝ) : ℕ := Nat.ceil (Real.pi / delta r)

/-- Number of offset samples (covering [-2, 2]). -/
def numOffsets (r : ℝ) : ℕ := Nat.ceil (4 / delta r) + 1

/-- Angle index set. -/
def angleSet (r : ℝ) : Finset ℕ := Finset.range (numAngles r)

/-- Offset index set. -/
def offsetSet (r : ℝ) : Finset ℕ := Finset.range (numOffsets r)

/-- Offset value: -2 + j * Δ. -/
def offsetVal (r : ℝ) (j : ℕ) : ℝ := -2 + (j : ℝ) * delta r

/-- Projective angle value: k * π / nθ. -/
def angleVal (r : ℝ) (k : ℕ) : ℝ := (k : ℝ) * Real.pi / numAngles r

local instance : DecidableEq Line2 := Classical.decEq _

/-- Tube family at scale r. -/
def tubeFamily (r : ℝ) : Finset Line2 :=
  (angleSet r ×ˢ offsetSet r).image
    (fun ⟨k, j⟩ => lineOfAngleOffset (angleVal r k) (offsetVal r j))

-- ============================================================================
-- 4. Cardinality bound
-- ============================================================================

/-- Bound: Nat.ceil x < x + 1 for x > 0. -/
lemma nat_ceil_lt_add_one (x : ℝ) (hx : 0 < x) :
    (Nat.ceil x : ℝ) < x + 1 := by
  have h_pos : 0 < Nat.ceil x := by
    have h5 : x ≤ (Nat.ceil x : ℝ) := Nat.le_ceil x
    by_contra h6
    have h7 : Nat.ceil x = 0 := by omega
    rw [h7] at h5
    have h8 : x ≤ 0 := by exact_mod_cast h5
    linarith
  have h1 : ∀ (n : ℕ), n < Nat.ceil x → (n : ℝ) < x := by
    intro n hn
    by_contra h2
    have h3 : x ≤ (n : ℝ) := by linarith
    have h4 : Nat.ceil x ≤ n := (Nat.ceil_le).mpr h3
    omega
  have h9 : Nat.ceil x - 1 < Nat.ceil x := by omega
  have h10 : ((Nat.ceil x - 1 : ℕ) : ℝ) < x := h1 (Nat.ceil x - 1) h9
  have h11 : ((Nat.ceil x - 1 : ℕ) : ℝ) = (Nat.ceil x : ℝ) - 1 := by
    simp [h_pos] <;> omega
  rw [h11] at h10
  linarith

/-- Cardinality bound: |tubeFamily r| ≤ C₁ / r² for 0 < r ≤ 1.
With Δ = r/10, C₁ = 600 * (π + 1). -/
lemma tubeFamily_card_le (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    (tubeFamily r).card ≤ (600 * (Real.pi + 1)) / r ^ 2 := by
  set Δ : ℝ := delta r with hΔ
  have hΔ_pos : 0 < Δ := by
    dsimp only [Δ, delta]
    positivity
  have hΔ_le : Δ ≤ 1 / 10 := by
    dsimp only [Δ, delta]
    linarith
  set nθ : ℕ := numAngles r with hnθ
  set nA : ℕ := numOffsets r with hnA
  set θs : Finset ℕ := angleSet r with hθs
  set As : Finset ℕ := offsetSet r with hAs
  have h1 : (tubeFamily r).card ≤ (θs ×ˢ As).card := by
    dsimp only [tubeFamily]
    exact Finset.card_image_le
  have h2 : (θs ×ˢ As).card = θs.card * As.card := by
    rw [Finset.card_product]
  have h3 : θs.card = nθ := by
    have h : θs.card = numAngles r := by simp [hθs, angleSet]
    exact h.trans hnθ.symm
  have h4 : As.card = nA := by
    have h : As.card = numOffsets r := by simp [hAs, offsetSet]
    exact h.trans hnA.symm
  rw [h2, h3, h4] at h1
  have h5 : (nθ : ℝ) < Real.pi / Δ + 1 :=
    nat_ceil_lt_add_one (Real.pi / Δ) (by positivity)
  have h6 : (nA : ℝ) ≤ 4 / Δ + 2 := by
    dsimp only [nA, numOffsets]
    have h7 : (Nat.ceil (4 / Δ) : ℝ) < 4 / Δ + 1 :=
      nat_ceil_lt_add_one (4 / Δ) (by positivity)
    have h8 : ((Nat.ceil (4 / Δ) + 1 : ℕ) : ℝ) = (Nat.ceil (4 / Δ) : ℝ) + 1 := by
      simp
    rw [h8]
    linarith
  have h9 : (1 : ℝ) ≤ 1 / Δ := by
    apply one_le_one_div
    <;> linarith
  have h10 : (nθ : ℝ) ≤ (Real.pi + 1) / Δ := by
    have h101 : (nθ : ℝ) < Real.pi / Δ + 1 := h5
    have h102 : Real.pi / Δ + 1 ≤ (Real.pi + 1) / Δ := by
      calc Real.pi / Δ + 1
          ≤ Real.pi / Δ + 1 / Δ := by gcongr
        _ = (Real.pi + 1) / Δ := by ring
    exact le_of_lt (lt_of_lt_of_le h101 h102)
  have h11 : (nA : ℝ) ≤ 6 / Δ := by
    have h112 : (2 : ℝ) ≤ 2 / Δ := by
      have h113 : Δ ≤ 1 := by linarith
      calc (2 : ℝ) = 2 / 1 := by norm_num
        _ ≤ 2 / Δ := by gcongr
    calc (nA : ℝ) ≤ 4 / Δ + 2 := h6
      _ ≤ 4 / Δ + 2 / Δ := by gcongr
      _ = 6 / Δ := by ring
  have h12 : ((nθ * nA : ℕ) : ℝ) ≤ (Real.pi + 1) / Δ * (6 / Δ) := by
    calc ((nθ * nA : ℕ) : ℝ)
        = (nθ : ℝ) * (nA : ℝ) := by exact_mod_cast rfl
      _ ≤ (Real.pi + 1) / Δ * (6 / Δ) := by gcongr
  have h13 : (Real.pi + 1) / Δ * (6 / Δ) = 6 * (Real.pi + 1) / Δ ^ 2 := by
    field_simp [hΔ_pos.ne'] <;> ring
  have h14 : Δ ^ 2 = r ^ 2 / 100 := by
    dsimp only [Δ, delta]
    <;> ring
  rw [h13, h14] at h12
  have h15 : 6 * (Real.pi + 1) / (r ^ 2 / 100) = 600 * (Real.pi + 1) / r ^ 2 := by
    field_simp [hr.ne'] <;> ring
  rw [h15] at h12
  have h16 : ((tubeFamily r).card : ℝ) ≤ ((nθ * nA : ℕ) : ℝ) := by
    exact_mod_cast h1
  have h17 : ((tubeFamily r).card : ℝ) ≤ 600 * (Real.pi + 1) / r ^ 2 := by
    calc ((tubeFamily r).card : ℝ)
        ≤ ((nθ * nA : ℕ) : ℝ) := h16
      _ ≤ 600 * (Real.pi + 1) / r ^ 2 := h12
  exact_mod_cast h17

-- ============================================================================
-- 5. Angle and offset extraction from arbitrary Line2
-- ============================================================================

/-- Helper: a finrank-1 submodule is nontrivial. -/
lemma submodule_finrank_one_ne_bot {V : Submodule ℝ Point}
    (h : Module.finrank ℝ V = 1) : V ≠ (⊥ : Submodule ℝ Point) := by
  intro hbot
  rw [hbot] at h
  simp at h <;> norm_num at h

/-- Extract a nonzero direction vector from a line. -/
def Line2.directionVector (L : Line2) : Point :=
  Classical.choose ((Submodule.ne_bot_iff L.toAffine.direction).mp
    (submodule_finrank_one_ne_bot L.property))

lemma Line2.directionVector_spec (L : Line2) :
    L.directionVector ∈ L.toAffine.direction ∧ L.directionVector ≠ 0 :=
  Classical.choose_spec ((Submodule.ne_bot_iff L.toAffine.direction).mp
    (submodule_finrank_one_ne_bot L.property))

lemma Line2.directionVector_mem (L : Line2) :
    L.directionVector ∈ L.toAffine.direction :=
  (L.directionVector_spec).1

lemma Line2.directionVector_ne_zero (L : Line2) :
    L.directionVector ≠ 0 :=
  (L.directionVector_spec).2

/-- Unit direction vector. -/
def Line2.unitDirection (L : Line2) : Point :=
  (1 / ‖L.directionVector‖) • L.directionVector

/-- Unit normal vector (rotate unit direction 90° clockwise).
If u = (u₀, u₁), then n = (u₁, -u₀). -/
def Line2.normalVector (L : Line2) : Point :=
  (L.unitDirection 1) • e0 + -(L.unitDirection 0) • e1

lemma Line2.normalVector_component0 (L : Line2) :
    (L.normalVector) 0 = L.unitDirection 1 := by
  simp [Line2.normalVector, e0, e1, PiLp.single_apply] <;> norm_num

lemma Line2.normalVector_component1 (L : Line2) :
    (L.normalVector) 1 = -L.unitDirection 0 := by
  simp [Line2.normalVector, e0, e1, PiLp.single_apply] <;> norm_num

/-- Normal angle in [0, π), using arccos of the first component. -/
def Line2.normalAngle (L : Line2) : ℝ :=
  let n₀ := L.normalVector 0
  let θ := Real.arccos n₀
  if θ = Real.pi then 0 else θ

lemma Line2.normalAngle_nonneg (L : Line2) : 0 ≤ L.normalAngle := by
  dsimp only [Line2.normalAngle]
  have h1 : 0 ≤ Real.arccos (L.normalVector 0) := Real.arccos_nonneg _
  split_ifs <;> linarith

lemma Line2.normalAngle_lt_pi (L : Line2) : L.normalAngle < Real.pi := by
  dsimp only [Line2.normalAngle]
  let θ := Real.arccos (L.normalVector 0)
  have h1 : θ ≤ Real.pi := Real.arccos_le_pi _
  by_cases h : θ = Real.pi
  · rw [if_pos h]
    exact Real.pi_pos
  · rw [if_neg h]
    exact lt_of_le_of_ne h1 h

/-- Signed offset: dot product of closestPoint with normalVector. -/
def Line2.offset (L : Line2) : ℝ :=
  dot (L.closestPoint) (L.normalVector)


-- ============================================================================
-- 6. Dot product and geometric facts
-- ============================================================================

lemma dot_apply (x y : Point) : dot x y = x 0 * y 0 + x 1 * y 1 := by
  have h_real : ∀ (a b : ℝ), inner ℝ a b = a * b := by
    intro a b
    exact Real.inner_apply a b
  have h : inner ℝ x y = x 0 * y 0 + x 1 * y 1 := by
    rw [PiLp.inner_apply]
    have h2 : (∑ i : Fin 2, inner ℝ (x i) (y i)) = ∑ i : Fin 2, x i * y i := by
      apply Finset.sum_congr rfl
      intro i _
      exact h_real (x i) (y i)
    rw [h2]
    simp [Fin.sum_univ_two] <;> ring
  simpa [dot] using h

lemma dot_comm (x y : Point) : dot x y = dot y x := by
  rw [dot_apply, dot_apply] <;> ring

lemma dot_smul_left (c : ℝ) (x y : Point) : dot (c • x) y = c * dot x y := by
  rw [dot_apply, dot_apply] <;> simp [Fin.sum_univ_two] <;> ring

lemma dot_add_left (x y z : Point) : dot (x + y) z = dot x z + dot y z := by
  rw [dot_apply, dot_apply, dot_apply] <;> simp [Fin.sum_univ_two] <;> ring

lemma dot_sub_left (x y z : Point) : dot (x - y) z = dot x z - dot y z := by
  rw [dot_apply, dot_apply, dot_apply] <;> simp [Fin.sum_univ_two] <;> ring

lemma dot_sub_right (x y z : Point) : dot x (y - z) = dot x y - dot x z := by
  rw [dot_apply, dot_apply, dot_apply] <;> simp [Fin.sum_univ_two] <;> ring

lemma inner_eq_dot (x y : Point) : inner ℝ x y = dot x y := by rfl

lemma dot_self_eq_norm_sq (x : Point) : dot x x = ‖x‖ ^ 2 :=
  real_inner_self_eq_norm_sq x

lemma cauchy_schwarz_dot (x y : Point) : (dot x y) ^ 2 ≤ (dot x x) * (dot y y) := by
  have h : inner ℝ x y * inner ℝ x y ≤ inner ℝ x x * inner ℝ y y :=
    real_inner_mul_inner_self_le x y
  have h2 : (dot x y) ^ 2 = inner ℝ x y * inner ℝ x y := by
    simp [dot] <;> ring
  have h3 : (dot x x) * (dot y y) = inner ℝ x x * inner ℝ y y := by
    simp [dot] <;> ring
  rw [h2, h3]
  exact h

lemma abs_dot_le_norm (x y : Point) : |dot x y| ≤ ‖x‖ * ‖y‖ :=
  abs_real_inner_le_norm x y

lemma normalVec_dot_self (θ : ℝ) : dot (normalVec θ) (normalVec θ) = 1 := by
  have h1 : dot (normalVec θ) (normalVec θ) =
      (normalVec θ 0) ^ 2 + (normalVec θ 1) ^ 2 := by rw [dot_apply] <;> ring
  rw [h1, normalVec_component0, normalVec_component1]
  have h2 : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
  linarith

lemma normalVec_norm (θ : ℝ) : ‖normalVec θ‖ = 1 := by
  have h1 : dot (normalVec θ) (normalVec θ) = 1 := normalVec_dot_self θ
  have h2 : ‖normalVec θ‖ ^ 2 = dot (normalVec θ) (normalVec θ) := by
    rw [dot_self_eq_norm_sq] <;> ring
  have h3 : ‖normalVec θ‖ ^ 2 = 1 := by linarith
  have h4 : 0 ≤ ‖normalVec θ‖ := by positivity
  nlinarith

lemma norm_dirVec (θ : ℝ) : ‖dirVec θ‖ = 1 := by
  have h1 : dot (dirVec θ) (dirVec θ) = 1 := by
    rw [dot_apply, dirVec_component0, dirVec_component1]
    have h4 : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
    ring_nf at h4 ⊢ <;> linarith
  have h2 : ‖dirVec θ‖ ^ 2 = dot (dirVec θ) (dirVec θ) := by
    rw [dot_self_eq_norm_sq] <;> ring
  have h3 : ‖dirVec θ‖ ^ 2 = 1 := by linarith
  have h4 : 0 ≤ ‖dirVec θ‖ := by positivity
  nlinarith

lemma normalVec_dot_dirVec (θ : ℝ) : dot (normalVec θ) (dirVec θ) = 0 := by
  have h1 : dot (normalVec θ) (dirVec θ) =
      (normalVec θ 0) * (dirVec θ 0) + (normalVec θ 1) * (dirVec θ 1) := by
    rw [dot_apply] <;> ring
  rw [h1, normalVec_component0, normalVec_component1,
    dirVec_component0, dirVec_component1] <;> ring

/-- Orthonormal decomposition: v = dot(v,n)•n + dot(v,d)•d. -/
lemma orthonormal_decomposition (v : Point) (θ : ℝ) :
    v = dot v (normalVec θ) • normalVec θ + dot v (dirVec θ) • dirVec θ := by
  let n := normalVec θ
  let d := dirVec θ
  let w := dot v n • n + dot v d • d
  have hcos2 : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
  have hdn : dot v n = v 0 * Real.cos θ + v 1 * Real.sin θ := by
    rw [dot_apply, normalVec_component0, normalVec_component1] <;> ring
  have hdd : dot v d = -v 0 * Real.sin θ + v 1 * Real.cos θ := by
    rw [dot_apply, dirVec_component0, dirVec_component1] <;> ring
  have h0 : w 0 = v 0 := by
    have hwn : w 0 = (dot v n) * (n 0) + (dot v d) * (d 0) := by
      simp [w, n, d, PiLp.single_apply] <;> ring
    rw [hwn, normalVec_component0 θ, dirVec_component0 θ, hdn, hdd]
    have h_goal : (v 0 * Real.cos θ + v 1 * Real.sin θ) * Real.cos θ +
        (-v 0 * Real.sin θ + v 1 * Real.cos θ) * (-Real.sin θ) = v 0 := by
      have h : (v 0 * Real.cos θ + v 1 * Real.sin θ) * Real.cos θ +
          (-v 0 * Real.sin θ + v 1 * Real.cos θ) * (-Real.sin θ) =
          v 0 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by ring
      rw [h, hcos2] <;> ring
    exact h_goal
  have h1 : w 1 = v 1 := by
    have hwn : w 1 = (dot v n) * (n 1) + (dot v d) * (d 1) := by
      simp [w, n, d, PiLp.single_apply] <;> ring
    rw [hwn, normalVec_component1 θ, dirVec_component1 θ, hdn, hdd]
    have h_goal : (v 0 * Real.cos θ + v 1 * Real.sin θ) * Real.sin θ +
        (-v 0 * Real.sin θ + v 1 * Real.cos θ) * Real.cos θ = v 1 := by
      have h : (v 0 * Real.cos θ + v 1 * Real.sin θ) * Real.sin θ +
          (-v 0 * Real.sin θ + v 1 * Real.cos θ) * Real.cos θ =
          v 1 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by ring
      rw [h, hcos2] <;> ring
    exact h_goal
  have h2 : w = v := by ext i; fin_cases i <;> tauto
  exact h2.symm

-- ============================================================================
-- 7. Properties of constructed lines
-- ============================================================================

lemma lineOfAngleOffset_dot_eq (θ a : ℝ) {z : Point}
    (hz : z ∈ (lineOfAngleOffset θ a).toAffine) :
    dot z (normalVec θ) = a := by
  let p : Point := a • normalVec θ
  have hp : p ∈ (lineOfAngleOffset θ a).toAffine := lineOfAngleOffset_basePoint_mem θ a
  have hdir0 : z -ᵥ p ∈ (lineOfAngleOffset θ a).toAffine.direction :=
    AffineSubspace.vsub_mem_direction hz hp
  have h_eq1 : (lineOfAngleOffset θ a).toAffine.direction =
      Submodule.span ℝ ({dirVec θ} : Set Point) := lineOfAngleOffset_aff_direction θ a
  have hdir : z -ᵥ p ∈ Submodule.span ℝ ({dirVec θ} : Set Point) := by
    rw [h_eq1] at hdir0; exact hdir0
  rcases Submodule.mem_span_singleton.mp hdir with ⟨t, ht⟩
  have h_eq2 : z - p = t • dirVec θ := by simpa [vsub_eq_sub] using ht.symm
  have h_eq3 : z = p + t • dirVec θ := by
    have h : z - p = t • dirVec θ := h_eq2
    have h2 : z = p + (z - p) := by abel
    rw [h2, h] <;> abel
  rw [h_eq3]
  have h_dot1 : dot (p + t • dirVec θ) (normalVec θ) =
      dot p (normalVec θ) + dot (t • dirVec θ) (normalVec θ) := by rw [dot_add_left]
  rw [h_dot1]
  have h_dot2 : dot (t • dirVec θ) (normalVec θ) = t * dot (dirVec θ) (normalVec θ) := by
    rw [dot_smul_left]
  rw [h_dot2]
  have h_dot3 : dot (dirVec θ) (normalVec θ) = 0 := by
    rw [dot_comm, normalVec_dot_dirVec θ]
  rw [h_dot3]
  have h_dot4 : dot p (normalVec θ) = a := by
    dsimp only [p]
    rw [dot_apply]
    have h_smul0 : (a • normalVec θ) 0 = a * (normalVec θ) 0 := by
      simp [PiLp.smul_apply]
    have h_smul1 : (a • normalVec θ) 1 = a * (normalVec θ) 1 := by
      simp [PiLp.smul_apply]
    rw [h_smul0, h_smul1, normalVec_component0, normalVec_component1]
    have h_trig : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
    have h_goal : a * Real.cos θ * Real.cos θ + a * Real.sin θ * Real.sin θ = a := by
      have h1 : a * Real.cos θ * Real.cos θ + a * Real.sin θ * Real.sin θ =
          a * (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by ring
      rw [h1, Real.cos_sq_add_sin_sq] <;> ring
    exact h_goal
  rw [h_dot4] <;> ring

/-- Projection point q on constructed line with ‖x-q‖ = |dot(x,n)-a|. -/
lemma lineOfAngleOffset_projection (θ a : ℝ) (x : Point) :
    ∃ (q : Point), q ∈ (lineOfAngleOffset θ a).toAffine ∧
      ‖x - q‖ = |dot x (normalVec θ) - a| := by
  let n : Point := normalVec θ
  let d : Point := dirVec θ
  let p : Point := a • n
  let q : Point := x - (dot x n - a) • n
  have h_decomp : x = dot x n • n + dot x d • d := orthonormal_decomposition x θ
  have h11 : q - p = x - (dot x n - a) • n - p := by rfl
  have h12 : x - (dot x n - a) • n - p = x - (dot x n) • n := by
    simp [p, sub_smul] <;> abel
  have h13 : x - (dot x n) • n = (dot x n • n + dot x d • d) - (dot x n) • n := by
    exact congr_arg (fun y : Point => y - (dot x n) • n) h_decomp
  have h14 : (dot x n • n + dot x d • d) - (dot x n) • n = dot x d • d := by
    simp [sub_smul] <;> abel
  have h1 : q - p = dot x d • d := by
    rw [h11, h12, h13, h14]
  have h2 : q -ᵥ p = dot x d • d := by simpa [vsub_eq_sub] using h1
  have h3 : q -ᵥ p ∈ (lineOfAngleOffset_aff θ a).direction := by
    rw [h2, lineOfAngleOffset_aff_direction]
    exact Submodule.mem_span_singleton.mpr ⟨dot x d, rfl⟩
  have h4 : q ∈ (lineOfAngleOffset θ a).toAffine := by
    have h5 : q = (q -ᵥ p) +ᵥ p := by simp [vsub_eq_sub, vadd_eq_add] <;> abel
    rw [h5]
    exact AffineSubspace.vadd_mem_of_mem_direction h3 (lineOfAngleOffset_basePoint_mem θ a)
  have h_norm : ‖x - q‖ = |dot x n - a| := by
    have h6 : x - q = (dot x n - a) • n := by simp [q] <;> abel
    rw [h6, norm_smul, normalVec_norm θ]
    <;> simp [Real.norm_eq_abs] <;> ring
  exact ⟨q, h4, h_norm⟩

-- ============================================================================
-- 8. Properties of Line2 extraction
-- ============================================================================

lemma Line2.unitDirection_norm (L : Line2) : ‖L.unitDirection‖ = 1 := by
  have hpos : 0 < ‖L.directionVector‖ := norm_pos_iff.mpr (L.directionVector_ne_zero)
  simp [Line2.unitDirection, norm_smul, hpos.ne'] <;> field_simp [hpos.ne'] <;> ring

lemma Line2.normalVector_norm (L : Line2) : ‖L.normalVector‖ = 1 := by
  have h1 : (L.normalVector 0) ^ 2 + (L.normalVector 1) ^ 2 = 1 := by
    rw [L.normalVector_component0, L.normalVector_component1]
    have h2 : (L.unitDirection 1) ^ 2 + (-L.unitDirection 0) ^ 2 =
        (L.unitDirection 1) ^ 2 + (L.unitDirection 0) ^ 2 := by ring
    rw [h2]
    have h3 : (L.unitDirection 1) ^ 2 + (L.unitDirection 0) ^ 2 = ‖L.unitDirection‖ ^ 2 := by
      have h4 : ‖L.unitDirection‖ ^ 2 = ∑ i : Fin 2, (L.unitDirection i) ^ 2 :=
        EuclideanSpace.real_norm_sq_eq L.unitDirection
      rw [h4]
      simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] <;> ring
    rw [h3, L.unitDirection_norm] <;> norm_num
  have h4 : dot L.normalVector L.normalVector = 1 := by
    have h5 : dot L.normalVector L.normalVector =
        (L.normalVector 0) ^ 2 + (L.normalVector 1) ^ 2 := by rw [dot_apply] <;> ring
    rw [h5, h1] <;> ring
  have h5 : ‖L.normalVector‖ ^ 2 = dot L.normalVector L.normalVector := by
    rw [dot_self_eq_norm_sq] <;> ring
  have h6 : ‖L.normalVector‖ ^ 2 = 1 := by linarith
  have h7 : 0 ≤ ‖L.normalVector‖ := by positivity
  nlinarith

lemma Line2.normalVector_dot_unitDirection (L : Line2) :
    dot L.normalVector L.unitDirection = 0 := by
  have h1 : dot L.normalVector L.unitDirection =
      L.normalVector 0 * L.unitDirection 0 + L.normalVector 1 * L.unitDirection 1 := by
    rw [dot_apply] <;> ring
  rw [h1, L.normalVector_component0, L.normalVector_component1] <;> ring

lemma Line2.direction_eq_span_unit (L : Line2) :
    L.toAffine.direction = Submodule.span ℝ {L.unitDirection} := by
  have h1 : L.unitDirection ∈ L.toAffine.direction := by
    have h2 : L.directionVector ∈ L.toAffine.direction := L.directionVector_mem
    have h3 : L.unitDirection = (1 / ‖L.directionVector‖) • L.directionVector := by rfl
    rw [h3]
    exact L.toAffine.direction.smul_mem _ h2
  have h4 : Submodule.span ℝ {L.unitDirection} ≤ L.toAffine.direction := by
    exact Submodule.span_le.mpr (fun x hx => by
      rcases hx with (rfl | _); exact h1)
  have h5 : Module.finrank ℝ (Submodule.span ℝ {L.unitDirection}) = 1 := by
    have h6 : L.unitDirection ≠ 0 := by
      rw [← norm_ne_zero_iff, L.unitDirection_norm] <;> norm_num
    exact finrank_span_singleton h6
  have h7 : Module.finrank ℝ L.toAffine.direction = 1 := L.property
  have h8 : Submodule.span ℝ {L.unitDirection} = L.toAffine.direction := by
    apply Submodule.eq_of_le_of_finrank_eq h4
    rw [h5, h7]
  exact h8.symm

lemma Line2.dot_eq_offset (L : Line2) {z : Point}
    (hz : z ∈ L.toAffine) : dot z L.normalVector = L.offset := by
  have h1 : z -ᵥ L.closestPoint ∈ L.toAffine.direction :=
    AffineSubspace.vsub_mem_direction hz L.closestPoint_mem
  rw [L.direction_eq_span_unit] at h1
  rcases Submodule.mem_span_singleton.mp h1 with ⟨t, ht⟩
  have h_eq : z -ᵥ L.closestPoint = t • L.unitDirection := ht.symm
  have h_dot : dot (z -ᵥ L.closestPoint) L.normalVector = 0 := by
    rw [h_eq, dot_smul_left]
    have h : dot L.unitDirection L.normalVector = 0 := by
      rw [dot_comm, L.normalVector_dot_unitDirection]
    rw [h] <;> ring
  have h4 : dot z L.normalVector - dot L.closestPoint L.normalVector = 0 := by
    simpa [dot_sub_left, vsub_eq_sub] using h_dot
  have h5 : dot L.closestPoint L.normalVector = L.offset := by rfl
  linarith

lemma Line2.abs_dot_sub_offset_le_dist_point (L : Line2) (x z : Point)
    (hz : z ∈ L.toAffine) : |dot x L.normalVector - L.offset| ≤ ‖x - z‖ := by
  have h6 : dot z L.normalVector = L.offset := L.dot_eq_offset hz
  have h7 : dot x L.normalVector - L.offset = dot (x - z) L.normalVector := by
    rw [dot_sub_left] <;> rw [h6] <;> ring
  rw [h7]
  have h8 : |dot (x - z) L.normalVector| ≤ ‖x - z‖ * ‖L.normalVector‖ :=
    abs_dot_le_norm (x - z) L.normalVector
  rw [L.normalVector_norm] at h8 <;> linarith

-- ============================================================================
-- 9. Normal vector continuity and rounding
-- ============================================================================

/-- ‖normalVec θ₁ - normalVec θ₂‖ ≤ |θ₁ - θ₂|. -/
lemma normalVec_dist_le (θ₁ θ₂ : ℝ) :
    ‖normalVec θ₁ - normalVec θ₂‖ ≤ |θ₁ - θ₂| := by
  set d : ℝ := θ₁ - θ₂ with hd
  have hc0 : ∀ θ : ℝ, (normalVec θ) 0 = Real.cos θ := normalVec_component0
  have hc1 : ∀ θ : ℝ, (normalVec θ) 1 = Real.sin θ := normalVec_component1
  set n1 : Point := normalVec θ₁ with hn1
  set n2 : Point := normalVec θ₂ with hn2
  have h_dot1 : dot (n1 - n2) (n1 - n2) =
      dot n1 n1 - 2 * dot n1 n2 + dot n2 n2 := by
    have h_a : dot (n1 - n2) (n1 - n2) = dot n1 (n1 - n2) - dot n2 (n1 - n2) := by
      rw [dot_sub_left]
    rw [h_a]
    have h_b : dot n1 (n1 - n2) = dot n1 n1 - dot n1 n2 := by
      rw [dot_sub_right] <;> ring
    have h_c : dot n2 (n1 - n2) = dot n2 n1 - dot n2 n2 := by
      rw [dot_sub_right] <;> ring
    rw [h_b, h_c]
    have h_d : dot n2 n1 = dot n1 n2 := dot_comm n2 n1
    rw [h_d] <;> ring
  have h_dot2 : dot n1 n2 = Real.cos θ₁ * Real.cos θ₂ + Real.sin θ₁ * Real.sin θ₂ := by
    have h := dot_apply n1 n2
    rw [h, hc0 θ₁, hc0 θ₂, hc1 θ₁, hc1 θ₂] <;> ring
  have h_dot3 : dot n1 n2 = Real.cos d := by
    rw [h_dot2, ← Real.cos_sub] <;> rfl
  have h2 : dot (n1 - n2) (n1 - n2) = 2 - 2 * Real.cos d := by
    rw [h_dot1, normalVec_dot_self θ₁, normalVec_dot_self θ₂, h_dot3] <;> ring
  have h3 : ‖normalVec θ₁ - normalVec θ₂‖ ^ 2 = 2 - 2 * Real.cos d := by
    have h1 : ‖normalVec θ₁ - normalVec θ₂‖ ^ 2 =
        dot (normalVec θ₁ - normalVec θ₂) (normalVec θ₁ - normalVec θ₂) := by
      rw [dot_self_eq_norm_sq] <;> ring
    rw [h1, h2]
  have h4 : Real.cos d = 1 - 2 * Real.sin (d / 2) ^ 2 := by
    have h41 : Real.cos (2 * (d / 2)) = 2 * Real.cos (d / 2) ^ 2 - 1 := Real.cos_two_mul (d / 2)
    have h42 : 2 * (d / 2) = d := by ring
    rw [h42] at h41
    have h43 : Real.cos (d / 2) ^ 2 + Real.sin (d / 2) ^ 2 = 1 := Real.cos_sq_add_sin_sq (d / 2)
    linarith
  have h5 : ‖normalVec θ₁ - normalVec θ₂‖ ^ 2 = 4 * Real.sin (d / 2) ^ 2 := by
    rw [h3, h4] <;> ring
  have h6 : 0 ≤ ‖normalVec θ₁ - normalVec θ₂‖ := by positivity
  have h_pos2 : 0 ≤ 2 * |Real.sin (d / 2)| := by positivity
  have h9 : (2 * |Real.sin (d / 2)|) ^ 2 = 4 * Real.sin (d / 2) ^ 2 := by
    calc (2 * |Real.sin (d / 2)|) ^ 2
        = 4 * (|Real.sin (d / 2)|) ^ 2 := by ring
      _ = 4 * Real.sin (d / 2) ^ 2 := by rw [sq_abs (Real.sin (d / 2))]
  have h_eq_sq : ‖normalVec θ₁ - normalVec θ₂‖ ^ 2 = (2 * |Real.sin (d / 2)|) ^ 2 := by
    rw [h5, h9]
  have h7 : ‖normalVec θ₁ - normalVec θ₂‖ = 2 * |Real.sin (d / 2)| := by
    nlinarith [h6, h_pos2, h_eq_sq]
  rw [h7]
  have h10 : |Real.sin (d / 2)| ≤ |d / 2| := Real.abs_sin_le_abs
  calc 2 * |Real.sin (d / 2)|
      ≤ 2 * |d / 2| := by gcongr
    _ = |d| := by
      simp [abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num)] <;> ring

/-- Projective angle rounding: every θ ∈ [0,π) is within π/nθ of a grid angle. -/
lemma angle_rounding (r : ℝ) (hr : 0 < r) (θ : ℝ)
    (hθ1 : 0 ≤ θ) (hθ2 : θ < Real.pi) :
    ∃ k : ℕ, k ∈ angleSet r ∧ |θ - angleVal r k| ≤ Real.pi / numAngles r := by
  set nθ : ℕ := numAngles r with hnθ
  set Δ : ℝ := delta r with hΔ
  have hΔ_pos : 0 < Δ := by dsimp only [Δ, delta] <;> positivity
  have h_nθ_pos : 0 < nθ := by
    dsimp only [nθ, numAngles]
    exact Nat.ceil_pos.mpr (div_pos Real.pi_pos hΔ_pos)
  have h_nθ_pos' : 0 < (nθ : ℝ) := by exact_mod_cast h_nθ_pos
  have hpi : 0 < Real.pi := Real.pi_pos
  let k : ℕ := Nat.floor (θ * (nθ : ℝ) / Real.pi)
  have hk1 : (k : ℝ) ≤ θ * (nθ : ℝ) / Real.pi := Nat.floor_le (by positivity)
  have hk2 : θ * (nθ : ℝ) / Real.pi < (k : ℝ) + 1 := Nat.lt_floor_add_one _
  have h_k_in : k ∈ angleSet r := by
    simp only [angleSet, Finset.mem_range]
    have h9 : θ * (nθ : ℝ) / Real.pi < (nθ : ℝ) := by
      have h10 : θ * (nθ : ℝ) < Real.pi * (nθ : ℝ) := by gcongr
      calc θ * (nθ : ℝ) / Real.pi
        < Real.pi * (nθ : ℝ) / Real.pi := by gcongr
        _ = (nθ : ℝ) := by field_simp [hpi.ne'] <;> ring
    have h : (k : ℝ) < (nθ : ℝ) := by
      calc (k : ℝ) ≤ θ * (nθ : ℝ) / Real.pi := hk1
        _ < (nθ : ℝ) := h9
    exact_mod_cast h
  have h1 : 0 ≤ θ - (k : ℝ) * Real.pi / (nθ : ℝ) := by
    have h13 : (k : ℝ) * Real.pi / (nθ : ℝ) ≤
        (θ * (nθ : ℝ) / Real.pi) * Real.pi / (nθ : ℝ) := by gcongr
    have h14 : (θ * (nθ : ℝ) / Real.pi) * Real.pi / (nθ : ℝ) = θ := by
      field_simp [hpi.ne', h_nθ_pos'.ne'] <;> ring
    linarith
  have h2 : θ - (k : ℝ) * Real.pi / (nθ : ℝ) < Real.pi / (nθ : ℝ) := by
    have h15 : θ * (nθ : ℝ) / Real.pi - (k : ℝ) < 1 := by linarith [hk2]
    have h16 : θ - (k : ℝ) * Real.pi / (nθ : ℝ) =
        Real.pi / (nθ : ℝ) * (θ * (nθ : ℝ) / Real.pi - (k : ℝ)) := by
      field_simp [hpi.ne', h_nθ_pos'.ne'] <;> ring
    rw [h16]
    have h17 : 0 < Real.pi / (nθ : ℝ) := by positivity
    nlinarith
  have h4 : |θ - (k : ℝ) * Real.pi / (nθ : ℝ)| = θ - (k : ℝ) * Real.pi / (nθ : ℝ) := by
    rw [abs_of_nonneg h1]
  have h_err : |θ - angleVal r k| ≤ Real.pi / (nθ : ℝ) := by
    dsimp only [angleVal]
    rw [h4] <;> linarith
  exact ⟨k, h_k_in, h_err⟩

lemma offset_rounding (r : ℝ) (hr : 0 < r) (a : ℝ)
    (ha1 : -2 ≤ a) (ha2 : a ≤ 2) :
    ∃ j : ℕ, j ∈ offsetSet r ∧ |a - offsetVal r j| ≤ delta r := by
  set Δ : ℝ := delta r with hΔ
  have hΔ_pos : 0 < Δ := by dsimp only [Δ, delta] <;> positivity
  have h_a2_nonneg : 0 ≤ a + 2 := by linarith
  have h_nonneg : 0 ≤ (a + 2) / Δ := by
    apply div_nonneg <;> linarith
  let j : ℕ := Nat.floor ((a + 2) / Δ)
  have hj1 : (j : ℝ) ≤ (a + 2) / Δ := Nat.floor_le h_nonneg
  have hj2 : (a + 2) / Δ < (j : ℝ) + 1 := Nat.lt_floor_add_one ((a + 2) / Δ)
  have h_j_in : j ∈ offsetSet r := by
    simp only [offsetSet, Finset.mem_range]
    have h_j_lt : j < numOffsets r := by
      dsimp only [numOffsets]
      have h_j_le4 : (j : ℝ) ≤ 4 / Δ := by
        calc (j : ℝ) ≤ (a + 2) / Δ := hj1
          _ ≤ 4 / Δ := by gcongr <;> linarith
      have h_j_le_ceil : (j : ℝ) ≤ (Nat.ceil (4 / Δ) : ℝ) := by
        calc (j : ℝ) ≤ 4 / Δ := h_j_le4
          _ ≤ (Nat.ceil (4 / Δ) : ℝ) := Nat.le_ceil (4 / Δ)
      have h_goal : (j : ℝ) < (Nat.ceil (4 / Δ) + 1 : ℝ) := by
        have h9 : (j : ℝ) ≤ (Nat.ceil (4 / Δ) : ℝ) := h_j_le_ceil
        have h10 : (Nat.ceil (4 / Δ) : ℝ) < (Nat.ceil (4 / Δ) + 1 : ℝ) := by simp
        linarith
      exact_mod_cast h_goal
    exact h_j_lt
  have h_err : |a - offsetVal r j| ≤ Δ := by
    have h1 : 0 ≤ (a + 2) / Δ - (j : ℝ) := by linarith
    have h2 : (a + 2) / Δ - (j : ℝ) < 1 := by linarith
    have h3 : a - offsetVal r j = Δ * ((a + 2) / Δ - (j : ℝ)) := by
      have h4 : offsetVal r j = -2 + (j : ℝ) * Δ := by
        dsimp only [offsetVal, Δ, delta] <;> ring
      rw [h4]
      have h5 : a - (-2 + (j : ℝ) * Δ) = a + 2 - (j : ℝ) * Δ := by ring
      rw [h5]
      have h6 : a + 2 - (j : ℝ) * Δ = Δ * ((a + 2) / Δ - (j : ℝ)) := by
        have h7 : Δ * ((a + 2) / Δ - (j : ℝ)) = Δ * ((a + 2) / Δ) - Δ * (j : ℝ) := by ring
        rw [h7]
        have h8 : Δ * ((a + 2) / Δ) = a + 2 := by field_simp [hΔ_pos.ne'] <;> ring
        rw [h8] <;> ring
      exact h6
    rw [h3]
    have h4 : |Δ * ((a + 2) / Δ - (j : ℝ))| = Δ * |(a + 2) / Δ - (j : ℝ)| := by
      have h5 : |Δ * ((a + 2) / Δ - (j : ℝ))| = |Δ| * |(a + 2) / Δ - (j : ℝ)| := by rw [abs_mul]
      rw [h5]
      have h6 : |Δ| = Δ := abs_of_pos hΔ_pos
      rw [h6]
    rw [h4]
    have h5 : |(a + 2) / Δ - (j : ℝ)| ≤ 1 := by rw [abs_of_nonneg h1] <;> linarith
    have h6 : Δ * |(a + 2) / Δ - (j : ℝ)| ≤ Δ := by
      calc Δ * |(a + 2) / Δ - (j : ℝ)| ≤ Δ * 1 := by gcongr
        _ = Δ := by ring
    exact h6
  exact ⟨j, h_j_in, h_err⟩

lemma Line2.offset_bound (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (L : Line2) (x : Point) (hx : x ∈ tube r L)
    (hxBall : x ∈ closedBall (0 : Point) 1) : |L.offset| < 2 := by
  have h_ex : ∃ (z : Point), z ∈ L.toSet ∧ dist x z < r :=
    (Metric.mem_thickening_iff (E := L.toSet) (x := x)).mp hx
  rcases h_ex with ⟨z, hz, hdist⟩
  have h_dot : dot z L.normalVector = L.offset := L.dot_eq_offset hz
  have h1 : |L.offset| ≤ ‖z‖ := by
    rw [← h_dot]
    have h2 : |dot z L.normalVector| ≤ ‖z‖ * ‖L.normalVector‖ := abs_dot_le_norm z L.normalVector
    rw [L.normalVector_norm] at h2 <;> linarith
  have h3 : ‖z‖ ≤ ‖x‖ + ‖x - z‖ := by
    calc ‖z‖ = ‖x - (x - z)‖ := by abel_nf
      _ ≤ ‖x‖ + ‖x - z‖ := by exact norm_sub_le _ _
  have h4 : ‖x - z‖ < r := hdist
  have h5 : ‖x‖ ≤ 1 := by simpa [Metric.mem_closedBall] using hxBall
  have h6 : ‖z‖ < 2 := by linarith
  linarith

/-- Canonical representation: find θ_c ∈ [0,π) and a_c such that
  normalVec θ_c = n or -n, and |dot x (normalVec θ_c) - a_c| < r. -/
lemma Line2.canonical_rep (L : Line2) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (x : Point) (hx : x ∈ tube r L) (hxBall : x ∈ closedBall (0 : Point) 1) :
    ∃ (θ_c a_c : ℝ), 0 ≤ θ_c ∧ θ_c < Real.pi ∧ |a_c| < 2 ∧
      |dot x (normalVec θ_c) - a_c| < r := by
  set n := L.normalVector with hn
  set θ := L.normalAngle with hθ
  set a := L.offset with ha
  have hθ1 : 0 ≤ θ := L.normalAngle_nonneg
  have hθ2 : θ < Real.pi := L.normalAngle_lt_pi
  have ha_bound : |a| < 2 := L.offset_bound r hr hr1 x hx hxBall
  have h_ex : ∃ (z : Point), z ∈ L.toSet ∧ dist x z < r :=
    (Metric.mem_thickening_iff (E := L.toSet) (x := x)).mp hx
  rcases h_ex with ⟨z, hz, hdist⟩
  have h1 : |dot x n - a| < r := by
    have h11 : |dot x n - a| ≤ ‖x - z‖ := L.abs_dot_sub_offset_le_dist_point x z hz
    have h12 : ‖x - z‖ < r := hdist
    linarith
  have h_unit : n 0 ^ 2 + n 1 ^ 2 = 1 := by
    have h : n 0 ^ 2 + n 1 ^ 2 = ‖n‖ ^ 2 := by
      have h2 : ‖n‖ ^ 2 = ∑ i : Fin 2, (n i) ^ 2 := EuclideanSpace.real_norm_sq_eq n
      rw [h2]; simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] <;> ring
    rw [h, L.normalVector_norm] <;> norm_num
  have h_n0_abs : -1 ≤ n 0 ∧ n 0 ≤ 1 := by
    have h1 : n 0 ^ 2 ≤ 1 := by nlinarith [h_unit]
    have h2 : -1 ≤ n 0 := by nlinarith
    have h3 : n 0 ≤ 1 := by nlinarith
    exact ⟨h2, h3⟩
  by_cases h_eq : n = normalVec θ
  · exact ⟨θ, a, hθ1, hθ2, ha_bound, by simpa [h_eq] using h1⟩
  · by_cases h_n0 : n 0 = -1
    · have h_n1 : n 1 = 0 := by nlinarith
      have h_nrel : normalVec 0 = -n := by
        ext i; fin_cases i <;> simp [h_n0, h_n1, normalVec_component0, normalVec_component1] <;> norm_num
      refine ⟨0, -a, by norm_num, Real.pi_pos, ?_, ?_⟩
      · simp [ha_bound] <;> linarith
      · rw [h_nrel]
        have h : dot x (-n) - (-a) = -(dot x n - a) := by
          rw [dot_apply x (-n), dot_apply x n] <;> simp [Fin.sum_univ_two] <;> ring
        rw [h, abs_neg] <;> exact h1
    · have h_cos : n 0 = Real.cos θ := by
        dsimp only [θ, Line2.normalAngle]
        have h_arccos_ne : Real.arccos (n 0) ≠ Real.pi := by
          intro h
          have h' : n 0 = -1 := by
            have h3 : Real.cos (Real.arccos (n 0)) = n 0 := Real.cos_arccos h_n0_abs.1 h_n0_abs.2
            rw [h] at h3; norm_num at h3 <;> linarith
          exact h_n0 h'
        rw [if_neg h_arccos_ne]
        have h3 : Real.cos (Real.arccos (n 0)) = n 0 := Real.cos_arccos h_n0_abs.1 h_n0_abs.2
        exact h3.symm
      have h_sin2 : Real.sin θ ^ 2 = n 1 ^ 2 := by
        have h2 : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by
          have h3 : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
          linarith
        rw [h2]
        have h4 : n 1 ^ 2 = 1 - n 0 ^ 2 := by nlinarith
        have h5 : n 0 = Real.cos θ := h_cos
        rw [h5] at * <;> nlinarith
      have h_sin_nonneg : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
      have h_n1_neg : n 1 < 0 := by
        by_contra h_n1_nonneg
        have h_n1_eq : n 1 = Real.sin θ := by nlinarith
        have h_eq2 : n = normalVec θ := by
          ext i; fin_cases i <;> simp [normalVec_component0, normalVec_component1, h_cos, h_n1_eq] <;> ring
        exact h_eq h_eq2
      have h_theta_pos : 0 < θ := by
        by_contra h
        have hθ0 : θ = 0 := by linarith
        have h_sin0 : Real.sin θ = 0 := by rw [hθ0] <;> norm_num
        rw [h_sin0] at h_sin2
        have h_n1_zero : n 1 = 0 := by nlinarith
        linarith
      let θ_c := Real.pi - θ
      have h_θc1 : 0 ≤ θ_c := by linarith [Real.pi_pos, hθ2]
      have h_θc2 : θ_c < Real.pi := by linarith [Real.pi_pos, h_theta_pos]
      have h_cos_pi : Real.cos θ_c = -Real.cos θ := by
        simp [θ_c, Real.cos_pi_sub] <;> ring
      have h_sin_pi : Real.sin θ_c = Real.sin θ := by
        simp [θ_c, Real.sin_pi_sub] <;> ring
      have h_n1_eq : n 1 = -Real.sin θ := by
        have h9 : n 1 ^ 2 = Real.sin θ ^ 2 := by linarith [h_sin2]
        have h10 : n 1 < 0 := h_n1_neg
        have h11 : 0 ≤ Real.sin θ := h_sin_nonneg
        nlinarith [sq_nonneg (n 1 + Real.sin θ)]
      have h_nrel : normalVec θ_c = -n := by
        ext i; fin_cases i <;> simp [normalVec_component0, normalVec_component1,
          h_cos_pi, h_sin_pi, h_cos, h_n1_eq] <;> ring
      refine ⟨θ_c, -a, h_θc1, h_θc2, ?_, ?_⟩
      · simp [ha_bound] <;> linarith
      · rw [h_nrel]
        have h : dot x (-n) - (-a) = -(dot x n - a) := by
          rw [dot_apply x (-n), dot_apply x n] <;> simp [Fin.sum_univ_two] <;> ring
        rw [h, abs_neg] <;> exact h1

-- ============================================================================
-- 10. Covering property
-- ============================================================================

/-- Covering property: for any line L and point x in tube(r,L) ∩ B(0,1),
there exists L' ∈ tubeFamily r such that x ∈ tube(2r, L'). -/
lemma tubeFamily_covering (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (L : Line2) (x : Point) (hx : x ∈ tube r L)
    (hxBall : x ∈ closedBall (0 : Point) 1) :
    ∃ L' : Line2, L' ∈ tubeFamily r ∧ x ∈ tube (2 * r) L' := by
  set Δ : ℝ := delta r with hΔ
  have hΔ_pos : 0 < Δ := by dsimp only [Δ, delta] <;> positivity
  have h_x_norm : ‖x‖ ≤ 1 := by simpa [Metric.mem_closedBall] using hxBall
  rcases L.canonical_rep r hr hr1 x hx hxBall with ⟨θ_c, a_c, h_θc1, h_θc2, h_ac_bound, h_dot_bound⟩
  have h_ac1 : -2 ≤ a_c := by linarith [abs_lt.mp h_ac_bound]
  have h_ac2 : a_c ≤ 2 := by linarith [abs_lt.mp h_ac_bound]
  rcases angle_rounding r hr θ_c h_θc1 h_θc2 with ⟨k, hk_in, hk_err⟩
  rcases offset_rounding r hr a_c h_ac1 h_ac2 with ⟨j, hj_in, hj_err⟩
  set θ' : ℝ := angleVal r k with hθ'
  set a' : ℝ := offsetVal r j with ha'
  set n' : Point := normalVec θ' with hn'
  set nc : Point := normalVec θ_c with hnc
  set L' : Line2 := lineOfAngleOffset θ' a' with hL'
  have hL'_in : L' ∈ tubeFamily r := by
    dsimp only [tubeFamily, L']
    apply Finset.mem_image.mpr
    refine ⟨(k, j), ?_, ?_⟩
    · simp only [Finset.mem_product] <;> exact ⟨hk_in, hj_in⟩
    · rfl
  have h_diff1 : |dot x n' - dot x nc| ≤ ‖x‖ * ‖n' - nc‖ := by
    have h : dot x n' - dot x nc = dot x (n' - nc) := by
      have h2 : dot x (n' - nc) = dot x n' - dot x nc := dot_sub_right x n' nc
      exact h2.symm
    rw [h]
    exact abs_dot_le_norm x (n' - nc)
  have h_diff2 : ‖n' - nc‖ ≤ |θ_c - θ'| := by
    have h : ‖n' - nc‖ = ‖nc - n'‖ := by rw [norm_sub_rev]
    rw [h]
    simpa [hn', hnc] using normalVec_dist_le θ_c θ'
  have h_pi_le_delta : Real.pi / (numAngles r : ℝ) ≤ Δ := by
    have h1 : Real.pi / Δ ≤ (numAngles r : ℝ) := by
      dsimp only [numAngles]
      exact Nat.le_ceil (Real.pi / Δ)
    have h2 : 0 < Δ := hΔ_pos
    have h3 : 0 < (numAngles r : ℝ) := by
      have h4 : 0 < Real.pi / Δ := div_pos Real.pi_pos h2
      linarith
    calc Real.pi / (numAngles r : ℝ)
      ≤ Real.pi / (Real.pi / Δ) := by gcongr
      _ = Δ := by field_simp [h2.ne'] <;> ring
  have h2 : |dot x n' - a'| < 2 * r := by
    have h_ineq : |dot x n' - a'| ≤
        |dot x n' - dot x nc| + |dot x nc - a_c| + |a_c - a'| := by
      have h_eq : dot x n' - a' = (dot x n' - dot x nc) + (dot x nc - a_c) + (a_c - a') := by ring
      rw [h_eq]
      have h_assoc : (dot x n' - dot x nc) + (dot x nc - a_c) + (a_c - a') =
          (dot x n' - dot x nc) + ((dot x nc - a_c) + (a_c - a')) := by ring
      rw [h_assoc]
      have h12 : |(dot x n' - dot x nc) + ((dot x nc - a_c) + (a_c - a'))| ≤
          |dot x n' - dot x nc| + |(dot x nc - a_c) + (a_c - a')| := by
        exact abs_add_le _ _
      have h13 : |(dot x nc - a_c) + (a_c - a')| ≤ |dot x nc - a_c| + |a_c - a'| := by
        exact abs_add_le _ _
      linarith
    calc |dot x n' - a'|
        ≤ |dot x n' - dot x nc| + |dot x nc - a_c| + |a_c - a'| := h_ineq
      _ ≤ ‖x‖ * ‖n' - nc‖ + |dot x nc - a_c| + |a_c - a'| := by gcongr <;> exact h_diff1
      _ ≤ 1 * |θ_c - θ'| + r + Δ := by gcongr <;> linarith <;> exact h_diff2 <;> exact h_dot_bound <;> exact hj_err
      _ ≤ 1 * (Real.pi / (numAngles r : ℝ)) + r + Δ := by gcongr <;> exact hk_err
      _ ≤ 1 * Δ + r + Δ := by gcongr <;> exact h_pi_le_delta
      _ = r + 2 * Δ := by ring
      _ < 2 * r := by dsimp only [Δ, delta] <;> linarith
  rcases lineOfAngleOffset_projection θ' a' x with ⟨q, hq_mem, hq_norm⟩
  have h3 : ‖x - q‖ < 2 * r := by rw [hq_norm] <;> exact h2
  have h4 : x ∈ tube (2 * r) L' := by
    have h_tube : tube (2 * r) L' = Metric.thickening (2 * r) L'.toSet := by simp only [tube]
    rw [h_tube]
    rw [Metric.mem_thickening_iff (E := L'.toSet) (x := x)]
    exact ⟨q, hq_mem, h3⟩
  exact ⟨L', hL'_in, h4⟩

-- ============================================================================
-- 11. Separation property
-- ============================================================================

/-- Projection onto span of a unit vector. -/
lemma proj_span_unit (u : Point) (hu : ‖u‖ = 1) (x : Point) :
    submoduleProj (Submodule.span ℝ {u}) x = (dot u x) • u := by
  have h1 : submoduleProj (Submodule.span ℝ {u}) = (Submodule.span ℝ {u}).starProjection :=
    submoduleProj_eq_starProjection _
  rw [h1]
  have h2 : (Submodule.span ℝ {u}).starProjection x = inner ℝ u x • u :=
    Submodule.starProjection_unit_singleton ℝ hu x
  rw [h2, inner_eq_dot]

/-- Direction distance ≥ √(1 - (u1·u2)²) for unit vectors. -/
lemma dirDist_lower (u1 u2 : Point) (h1 : ‖u1‖ = 1) (h2 : ‖u2‖ = 1) :
    submoduleDirDist (Submodule.span ℝ {u1}) (Submodule.span ℝ {u2}) ≥
      Real.sqrt (1 - (dot u1 u2) ^ 2) := by
  let P1 := submoduleProj (Submodule.span ℝ {u1})
  let P2 := submoduleProj (Submodule.span ℝ {u2})
  have hP1 : P1 u1 = u1 := by
    rw [proj_span_unit u1 h1 u1]
    have h3 : dot u1 u1 = 1 := by
      have h4 : dot u1 u1 = ‖u1‖ ^ 2 := dot_self_eq_norm_sq u1
      have h5 : ‖u1‖ ^ 2 = 1 := by rw [h1] <;> norm_num
      linarith
    rw [h3] <;> simp
  have hP2 : P2 u1 = (dot u2 u1) • u2 := by
    rw [proj_span_unit u2 h2 u1] <;> rw [dot_comm]
  set c : ℝ := dot u1 u2 with hc
  set w : Point := u1 - c • u2 with hw
  have h_eq : (P1 - P2) u1 = w := by
    simp [hP1, hP2, hw, ContinuousLinearMap.sub_apply] <;> rw [dot_comm u2 u1] <;> abel
  have h4 : ‖w‖ ^ 2 = 1 - c ^ 2 := by
    have h_norm : ‖u1 - c • u2‖ ^ 2 = ‖u1‖ ^ 2 - 2 * inner ℝ u1 (c • u2) + ‖c • u2‖ ^ 2 :=
      norm_sub_sq_real u1 (c • u2)
    rw [h_norm]
    have h_inner : inner ℝ u1 (c • u2) = c * inner ℝ u1 u2 := by simp [inner_smul_right]
    have h_smul : ‖c • u2‖ ^ 2 = c^2 * ‖u2‖ ^ 2 := by
      have h31 : ‖c • u2‖ = ‖c‖ * ‖u2‖ := norm_smul c u2
      have h32 : ‖c‖ = |c| := by exact Real.norm_eq_abs c
      rw [h31, h32]
      have h33 : (|c| * ‖u2‖) ^ 2 = c ^ 2 * ‖u2‖ ^ 2 := by
        have h34 : |c| ^ 2 = c ^ 2 := by rw [sq_abs]
        calc (|c| * ‖u2‖) ^ 2 = |c| ^ 2 * ‖u2‖ ^ 2 := by ring
          _ = c ^ 2 * ‖u2‖ ^ 2 := by rw [h34]
      exact h33
    rw [h_inner, h_smul]
    have h_u1 : ‖u1‖ ^ 2 = 1 := by rw [h1] <;> norm_num
    have h_u2 : ‖u2‖ ^ 2 = 1 := by rw [h2] <;> norm_num
    have h_c1 : inner ℝ u1 u2 = c := by rw [inner_eq_dot, hc]
    rw [h_u1, h_u2, h_c1] <;> ring
  have h5 : 0 ≤ 1 - c ^ 2 := by
    have h6 : |c| ≤ ‖u1‖ * ‖u2‖ := abs_dot_le_norm u1 u2
    rw [h1, h2] at h6; simp at h6; nlinarith
  have h6 : ‖w‖ = Real.sqrt (1 - c ^ 2) := by
    have h7 : ‖w‖ ^ 2 = 1 - c ^ 2 := h4
    have h8 : 0 ≤ ‖w‖ := by positivity
    nlinarith [Real.sqrt_nonneg (1 - c ^ 2), Real.sq_sqrt h5]
  have h9 : ‖P1 - P2‖ * ‖u1‖ ≥ ‖(P1 - P2) u1‖ := ContinuousLinearMap.le_opNorm (P1 - P2) u1
  have h10 : ‖u1‖ = 1 := h1
  have h11 : ‖P1 - P2‖ ≥ ‖(P1 - P2) u1‖ := by
    rw [h10] at h9
    simpa using h9
  rw [h_eq] at h11
  rw [h6] at h11
  exact h11

/-- sin α ≥ 2α/π on [0, π/2]. -/
lemma sin_ge_two_div_pi (α : ℝ) (h1 : 0 ≤ α) (h2 : α ≤ Real.pi / 2) :
    Real.sin α ≥ 2 * α / Real.pi := by
  have h_sc : StrictConcaveOn ℝ (Set.Icc 0 Real.pi) Real.sin := strictConcaveOn_sin_Icc
  have h_cv : ConcaveOn ℝ (Set.Icc 0 Real.pi) Real.sin := h_sc.concaveOn
  have h0 : 0 ∈ Set.Icc (0 : ℝ) Real.pi := by exact ⟨by linarith, by linarith [Real.pi_pos]⟩
  have hpi2 : Real.pi / 2 ∈ Set.Icc (0 : ℝ) Real.pi := by
    exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  set t : ℝ := 2 * α / Real.pi with ht
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 := by
    rw [ht]
    have h : 2 * α ≤ Real.pi := by linarith
    have hpi : 0 < Real.pi := Real.pi_pos
    exact (div_le_one hpi).mpr h
  have h_main : Real.sin α ≥ t * Real.sin (Real.pi / 2) + (1 - t) * Real.sin 0 := by
    have h_eq : α = t * (Real.pi / 2) + (1 - t) * (0 : ℝ) := by
      rw [ht] <;> field_simp [Real.pi_pos.ne'] <;> ring
    rw [h_eq]
    exact h_cv.2 hpi2 h0 ht0 (by linarith) (by ring)
  have h_sin_pi2 : Real.sin (Real.pi / 2) = 1 := Real.sin_pi_div_two
  have h_sin0 : Real.sin 0 = 0 := by norm_num
  rw [h_sin_pi2, h_sin0] at h_main
  have h_final : t * (1 : ℝ) + (1 - t) * (0 : ℝ) = 2 * α / Real.pi := by
    rw [ht] <;> ring
  rw [h_final] at h_main
  exact h_main

/-- |(n : ℝ) - (m : ℝ)| ≥ 1 for distinct natural numbers. -/
lemma nat_abs_diff_ge_one {n m : ℕ} (h : n ≠ m) : |(n : ℝ) - (m : ℝ)| ≥ 1 := by
  by_cases h_le : n ≤ m
  · have h_lt : n < m := Nat.lt_of_le_of_ne h_le h
    have h1 : (m : ℝ) - (n : ℝ) ≥ 1 := by
      exact_mod_cast (show 1 ≤ m - n from Nat.one_le_iff_ne_zero.mpr (Nat.sub_ne_zero_iff_lt.mpr h_lt))
    have h2 : |(n : ℝ) - (m : ℝ)| = (m : ℝ) - (n : ℝ) := by
      rw [abs_of_nonpos] <;> linarith
    rw [h2]
    exact h1
  · have h_ge : m ≤ n := by omega
    have h_lt : m < n := Nat.lt_of_le_of_ne h_ge h.symm
    have h1 : (n : ℝ) - (m : ℝ) ≥ 1 := by
      exact_mod_cast (show 1 ≤ n - m from Nat.one_le_iff_ne_zero.mpr (Nat.sub_ne_zero_iff_lt.mpr h_lt))
    have h2 : |(n : ℝ) - (m : ℝ)| = (n : ℝ) - (m : ℝ) := by
      rw [abs_of_nonneg] <;> linarith
    rw [h2]
    exact h1

/-- Projective angle separation: distinct grid angles are ≥ π/nθ apart projectively. -/
lemma grid_angle_proj_sep (r : ℝ) (hr : 0 < r) (k1 k2 : ℕ) (hk1 : k1 < numAngles r)
    (hk2 : k2 < numAngles r) (hne : k1 ≠ k2) :
    let d := |angleVal r k1 - angleVal r k2|
    min d (Real.pi - d) ≥ Real.pi / numAngles r := by
  set nθ : ℕ := numAngles r with hnθ
  have h_pos : 0 < nθ := by
    dsimp only [nθ, numAngles]
    have hpi : 0 < Real.pi := Real.pi_pos
    have hd : 0 < delta r := by dsimp only [delta]; exact div_pos hr (by norm_num)
    exact Nat.ceil_pos.mpr (div_pos hpi hd)
  let d : ℝ := |angleVal r k1 - angleVal r k2|
  have h_d_eq : d = |(k1 : ℝ) - (k2 : ℝ)| * (Real.pi / nθ) := by
    simp [d, angleVal]
    have h : (k1 : ℝ) * Real.pi / nθ - (k2 : ℝ) * Real.pi / nθ =
        ((k1 : ℝ) - (k2 : ℝ)) * (Real.pi / nθ) := by ring
    rw [h, abs_mul]
    have hpos2 : 0 ≤ Real.pi / nθ := by positivity
    rw [abs_of_nonneg hpos2]
  have h_diff_ge_one : (1 : ℝ) ≤ |(k1 : ℝ) - (k2 : ℝ)| := nat_abs_diff_ge_one hne
  have h_d_ge : d ≥ Real.pi / nθ := by
    rw [h_d_eq]
    have h : |(k1 : ℝ) - (k2 : ℝ)| * (Real.pi / nθ) ≥ 1 * (Real.pi / nθ) := by gcongr
    simpa using h
  have h1' : (k1 : ℝ) ≤ (nθ : ℝ) - 1 := by
    have h : k1 + 1 ≤ nθ := by omega
    have h' : (k1 : ℝ) + 1 ≤ (nθ : ℝ) := by exact_mod_cast h
    linarith
  have h2' : (k2 : ℝ) ≤ (nθ : ℝ) - 1 := by
    have h : k2 + 1 ≤ nθ := by omega
    have h' : (k2 : ℝ) + 1 ≤ (nθ : ℝ) := by exact_mod_cast h
    linarith
  have h_diff_le : |(k1 : ℝ) - (k2 : ℝ)| ≤ (nθ : ℝ) - 1 := by
    rw [abs_le] <;> constructor <;> linarith [h1', h2']
  have h_d_le : d ≤ ((nθ : ℝ) - 1) * (Real.pi / nθ) := by
    rw [h_d_eq]; gcongr
  have h_pi_minus_d : Real.pi - d ≥ Real.pi / nθ := by
    have h5 : Real.pi - d ≥ Real.pi - ((nθ : ℝ) - 1) * (Real.pi / nθ) := by linarith
    have h6 : (nθ : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast h_pos)
    have h7 : Real.pi - ((nθ : ℝ) - 1) * (Real.pi / nθ) = Real.pi / nθ := by
      field_simp [h6] <;> ring
    linarith
  exact le_min h_d_ge h_pi_minus_d

/-- Direction distance ≥ 2/nθ for distinct grid angles. -/
lemma grid_dirDist (r : ℝ) (hr : 0 < r) (k1 k2 : ℕ) (hk1 : k1 < numAngles r)
    (hk2 : k2 < numAngles r) (hne : k1 ≠ k2) :
    lineDirDist (lineOfAngleOffset (angleVal r k1) 0) (lineOfAngleOffset (angleVal r k2) 0) ≥
      2 / (numAngles r : ℝ) := by
  set nθ : ℕ := numAngles r with hnθ
  let θ1 := angleVal r k1
  let θ2 := angleVal r k2
  let u1 := dirVec θ1
  let u2 := dirVec θ2
  have h_u1_norm : ‖u1‖ = 1 := norm_dirVec θ1
  have h_u2_norm : ‖u2‖ = 1 := norm_dirVec θ2
  let V1 := Submodule.span ℝ {u1}
  let V2 := Submodule.span ℝ {u2}
  have h_dir1 : (lineOfAngleOffset θ1 0).toAffine.direction = V1 :=
    lineOfAngleOffset_aff_direction θ1 0
  have h_dir2 : (lineOfAngleOffset θ2 0).toAffine.direction = V2 :=
    lineOfAngleOffset_aff_direction θ2 0
  have h_main : submoduleDirDist V1 V2 ≥ Real.sqrt (1 - (dot u1 u2) ^ 2) :=
    dirDist_lower u1 u2 h_u1_norm h_u2_norm
  let d := |θ1 - θ2|
  let α := min d (Real.pi - d)
  have h1d : 0 ≤ d := by positivity
  have h2d : d ≤ Real.pi := by
    dsimp only [d, θ1, θ2, angleVal]
    have h_pos2 : 0 < nθ := by
      dsimp only [nθ, numAngles]
      have hpi : 0 < Real.pi := Real.pi_pos
      have hd : 0 < delta r := by dsimp only [delta]; exact div_pos hr (by norm_num)
      exact Nat.ceil_pos.mpr (div_pos hpi hd)
    have h4 : |(k1 : ℝ) - (k2 : ℝ)| ≤ (nθ : ℝ) := by
      have h5 : (k1 : ℝ) < (nθ : ℝ) := by exact_mod_cast hk1
      have h6 : (k2 : ℝ) < (nθ : ℝ) := by exact_mod_cast hk2
      rw [abs_le] <;> constructor <;> linarith
    have h7 : |(k1 : ℝ) * Real.pi / nθ - (k2 : ℝ) * Real.pi / nθ| =
        |(k1 : ℝ) - (k2 : ℝ)| * (Real.pi / nθ) := by
      have h8 : (k1 : ℝ) * Real.pi / nθ - (k2 : ℝ) * Real.pi / nθ =
          ((k1 : ℝ) - (k2 : ℝ)) * (Real.pi / nθ) := by ring
      rw [h8, abs_mul]
      have hpos3 : 0 ≤ Real.pi / nθ := by positivity
      rw [abs_of_nonneg hpos3]
    rw [h7]
    have h9 : |(k1 : ℝ) - (k2 : ℝ)| * (Real.pi / nθ) ≤ (nθ : ℝ) * (Real.pi / nθ) := by gcongr
    have h10 : (nθ : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast h_pos2)
    have h11 : (nθ : ℝ) * (Real.pi / nθ) = Real.pi := by
      field_simp [h10] <;> ring
    rw [h11] at h9
    exact h9
  have hα1 : 0 ≤ α := by
    dsimp only [α]
    have h2 : 0 ≤ Real.pi - d := by linarith [Real.pi_pos]
    have h3 : 0 ≤ d := by positivity
    exact le_min h3 h2
  have hα2 : α ≤ Real.pi / 2 := by
    dsimp only [α]
    by_cases h : d ≤ Real.pi / 2
    · exact min_le_iff.mpr (Or.inl h)
    · exact min_le_iff.mpr (Or.inr (by linarith [Real.pi_pos]))
  have h_sep : α ≥ Real.pi / nθ := grid_angle_proj_sep r hr k1 k2 hk1 hk2 hne
  have h_dot : dot u1 u2 = Real.cos (θ1 - θ2) := by
    rw [dot_apply]
    rw [dirVec_component0 θ1, dirVec_component1 θ1, dirVec_component0 θ2, dirVec_component1 θ2]
    rw [Real.cos_sub] <;> ring
  rw [h_dot] at h_main
  have h_sin2 : 1 - Real.cos (θ1 - θ2) ^ 2 = Real.sin α ^ 2 := by
    have h1 : 1 - Real.cos (θ1 - θ2) ^ 2 = Real.sin (θ1 - θ2) ^ 2 := by
      rw [Real.sin_sq] <;> ring
    rw [h1]
    dsimp only [α]
    by_cases h4 : d ≤ Real.pi / 2
    · have h5 : min d (Real.pi - d) = d := by
        apply min_eq_left; linarith [Real.pi_pos]
      rw [h5]
      have h6 : d = |θ1 - θ2| := by rfl
      rw [h6]
      by_cases h7 : 0 ≤ θ1 - θ2
      · have h8 : |θ1 - θ2| = θ1 - θ2 := abs_of_nonneg h7
        rw [h8]
      · have h8 : |θ1 - θ2| = -(θ1 - θ2) := abs_of_neg (by linarith)
        rw [h8]
        have h9 : Real.sin (-(θ1 - θ2)) = -Real.sin (θ1 - θ2) := by
          rw [Real.sin_neg] <;> ring
        rw [h9] <;> ring
    · have h5 : min d (Real.pi - d) = Real.pi - d := by
        apply min_eq_right; linarith [Real.pi_pos]
      rw [h5]
      have h6 : d = |θ1 - θ2| := by rfl
      rw [h6]
      have h7 : Real.sin (Real.pi - |θ1 - θ2|) = Real.sin |θ1 - θ2| := by
        rw [Real.sin_pi_sub]
      rw [h7]
      by_cases h8 : 0 ≤ θ1 - θ2
      · have h9 : |θ1 - θ2| = θ1 - θ2 := abs_of_nonneg h8
        rw [h9]
      · have h9 : |θ1 - θ2| = -(θ1 - θ2) := abs_of_neg (by linarith)
        rw [h9]
        have h10 : Real.sin (-(θ1 - θ2)) = -Real.sin (θ1 - θ2) := by
          rw [Real.sin_neg] <;> ring
        rw [h10] <;> ring
  rw [h_sin2] at h_main
  have h_sin_nonneg : 0 ≤ Real.sin α := Real.sin_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  have h_sqrt : Real.sqrt (Real.sin α ^ 2) = Real.sin α := by
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg h_sin_nonneg]
  rw [h_sqrt] at h_main
  have h_sin_lower : Real.sin α ≥ 2 * α / Real.pi := sin_ge_two_div_pi α hα1 hα2
  have h_final : Real.sin α ≥ 2 / (nθ : ℝ) := by
    calc Real.sin α ≥ 2 * α / Real.pi := h_sin_lower
      _ ≥ 2 * (Real.pi / nθ) / Real.pi := by gcongr
      _ = 2 / (nθ : ℝ) := by field_simp [Real.pi_pos.ne'] <;> ring
  have h_goal : lineDirDist (lineOfAngleOffset θ1 0) (lineOfAngleOffset θ2 0) =
      submoduleDirDist V1 V2 := by
    rw [lineDirDist, h_dir1, h_dir2]
  rw [h_goal]
  exact le_trans h_final h_main

/-- Closest point of lineOfAngleOffset θ a is a • normalVec θ. -/
lemma lineOfAngleOffset_closestPoint (θ a : ℝ) :
    (lineOfAngleOffset θ a).closestPoint = a • normalVec θ := by
  let L := lineOfAngleOffset θ a
  let n := normalVec θ
  let p : Point := a • n
  have hp : p ∈ L.toAffine := lineOfAngleOffset_basePoint_mem θ a
  have h_orth : ∀ (v : Point), v ∈ L.toAffine.direction → inner ℝ ((0 : Point) -ᵥ p) v = 0 := by
    intro v hv
    have h4 : L.toAffine.direction = Submodule.span ℝ {dirVec θ} :=
      lineOfAngleOffset_aff_direction θ a
    rw [h4] at hv
    rcases (Submodule.mem_span_singleton).mp hv with ⟨c, rfl⟩
    have h5 : (0 : Point) -ᵥ p = -p := by simp [vsub_eq_sub]
    rw [h5]
    have h6 : inner ℝ (-p) (c • dirVec θ) = -c * inner ℝ p (dirVec θ) := by
      simp [inner_smul_right, inner_neg_left] <;> ring
    rw [h6]
    have h7 : inner ℝ p (dirVec θ) = 0 := by
      rw [inner_eq_dot]
      have h8 : p = a • n := by rfl
      rw [h8]
      have h9 : dot (a • n) (dirVec θ) = a * dot n (dirVec θ) := dot_smul_left a n (dirVec θ)
      rw [h9, normalVec_dot_dirVec] <;> ring
    rw [h7] <;> ring
  have h_orth2 : (0 : Point) -ᵥ p ∈ L.toAffine.directionᗮ := by
    rw [Submodule.mem_orthogonal]
    intro u hu
    have h_eq : inner ℝ u ((0 : Point) -ᵥ p) = inner ℝ ((0 : Point) -ᵥ p) u := by exact dot_comm u (0 -ᵥ p)
    rw [h_eq]
    exact h_orth u hu
  have h_main : (EuclideanGeometry.orthogonalProjection L.toAffine 0 : Point) = p := by
    rw [EuclideanGeometry.coe_orthogonalProjection_eq_iff_mem]
    exact ⟨hp, h_orth2⟩
  have h6 : L.closestPoint = EuclideanGeometry.orthogonalProjection L.toAffine 0 :=
    L.closestPoint_eq_orthogonalProjection
  rw [h6, h_main]

/-- Offset distance for same-angle lines equals |a1 - a2|. -/
lemma grid_offsetDist (θ a1 a2 : ℝ) :
    lineOffsetDist (lineOfAngleOffset θ a1) (lineOfAngleOffset θ a2) = |a1 - a2| := by
  rw [lineOffsetDist, lineOfAngleOffset_closestPoint, lineOfAngleOffset_closestPoint]
  have h2 : a1 • normalVec θ - a2 • normalVec θ = (a1 - a2) • normalVec θ := by
    ext i; simp <;> ring
  have h3 : dist (a1 • normalVec θ) (a2 • normalVec θ) =
      ‖a1 • normalVec θ - a2 • normalVec θ‖ := by rfl
  rw [h3, h2]
  have h4 : ‖(a1 - a2) • normalVec θ‖ = |a1 - a2| * ‖normalVec θ‖ := by
    rw [norm_smul] <;> simp
  rw [h4, normalVec_norm θ] <;> ring

/-- Main separation theorem: distinct lines in tubeFamily r are ≥ r/20 apart. -/
lemma tubeFamily_separation (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (L1 L2 : Line2) (h1 : L1 ∈ tubeFamily r) (h2 : L2 ∈ tubeFamily r)
    (hne : L1 ≠ L2) : lineDist L1 L2 ≥ r / 20 := by
  set Δ : ℝ := delta r with hΔ
  have hΔ_pos : 0 < Δ := by dsimp only [Δ, delta]; positivity
  set nθ : ℕ := numAngles r with hnθ
  set nA : ℕ := numOffsets r with hnA
  rcases Finset.mem_image.mp h1 with ⟨⟨k1, j1⟩, hk1, rfl⟩
  rcases Finset.mem_image.mp h2 with ⟨⟨k2, j2⟩, hk2, rfl⟩
  have h_prod1 : (k1, j1) ∈ angleSet r ×ˢ offsetSet r := hk1
  have h_prod2 : (k2, j2) ∈ angleSet r ×ˢ offsetSet r := hk2
  have h_k1 : k1 ∈ angleSet r := (Finset.mem_product.mp h_prod1).1
  have h_j1 : j1 ∈ offsetSet r := (Finset.mem_product.mp h_prod1).2
  have h_k2 : k2 ∈ angleSet r := (Finset.mem_product.mp h_prod2).1
  have h_j2 : j2 ∈ offsetSet r := (Finset.mem_product.mp h_prod2).2
  have hk1' : k1 < nθ := by simpa [angleSet] using h_k1
  have hj1' : j1 < nA := by simpa [offsetSet] using h_j1
  have hk2' : k2 < nθ := by simpa [angleSet] using h_k2
  have hj2' : j2 < nA := by simpa [offsetSet] using h_j2
  let θ1 := angleVal r k1
  let θ2 := angleVal r k2
  let a1 := offsetVal r j1
  let a2 := offsetVal r j2
  by_cases h_k : k1 = k2
  · -- Same angle
    subst h_k
    have h_j : j1 ≠ j2 := by
      intro h
      subst h
      exact hne rfl
    have h_off_ge : |a1 - a2| ≥ Δ := by
      simp only [a1, a2, offsetVal]
      have h_abs1 : 1 ≤ |(j1 : ℝ) - (j2 : ℝ)| := nat_abs_diff_ge_one h_j
      have h3 : |(-2 + (j1 : ℝ) * Δ) - (-2 + (j2 : ℝ) * Δ)| = |(j1 : ℝ) - (j2 : ℝ)| * Δ := by
        have h4 : (-2 + (j1 : ℝ) * Δ) - (-2 + (j2 : ℝ) * Δ) = ((j1 : ℝ) - (j2 : ℝ)) * Δ := by ring
        rw [h4, abs_mul] <;> rw [abs_of_pos hΔ_pos]
      rw [h3]
      calc |(j1 : ℝ) - (j2 : ℝ)| * Δ ≥ 1 * Δ := by gcongr
        _ = Δ := by ring
    have h4 : lineOffsetDist (lineOfAngleOffset θ1 a1) (lineOfAngleOffset θ1 a2) = |a1 - a2| :=
      grid_offsetDist θ1 a1 a2
    have h5 : lineDist (lineOfAngleOffset θ1 a1) (lineOfAngleOffset θ1 a2) ≥
        lineOffsetDist (lineOfAngleOffset θ1 a1) (lineOfAngleOffset θ1 a2) := by
      have h6 : lineDist (lineOfAngleOffset θ1 a1) (lineOfAngleOffset θ1 a2) =
          lineDirDist (lineOfAngleOffset θ1 a1) (lineOfAngleOffset θ1 a2) +
          lineOffsetDist (lineOfAngleOffset θ1 a1) (lineOfAngleOffset θ1 a2) := by
        rw [lineDist]
      rw [h6]
      have h7 : 0 ≤ lineDirDist (lineOfAngleOffset θ1 a1) (lineOfAngleOffset θ1 a2) := by
        exact norm_nonneg _
      linarith
    rw [h4] at h5
    have h6 : Δ = r / 10 := by rfl
    linarith
  · -- Different angles
    have h_k_ne : k1 ≠ k2 := h_k
    have h_dir1 : (lineOfAngleOffset θ1 a1).toAffine.direction =
        Submodule.span ℝ ({dirVec θ1} : Set Point) :=
      lineOfAngleOffset_aff_direction θ1 a1
    have h_dir1' : (lineOfAngleOffset θ1 0).toAffine.direction =
        Submodule.span ℝ ({dirVec θ1} : Set Point) :=
      lineOfAngleOffset_aff_direction θ1 0
    have h_dir2 : (lineOfAngleOffset θ2 a2).toAffine.direction =
        Submodule.span ℝ ({dirVec θ2} : Set Point) :=
      lineOfAngleOffset_aff_direction θ2 a2
    have h_dir2' : (lineOfAngleOffset θ2 0).toAffine.direction =
        Submodule.span ℝ ({dirVec θ2} : Set Point) :=
      lineOfAngleOffset_aff_direction θ2 0
    have h_dir_ge : lineDirDist (lineOfAngleOffset θ1 a1) (lineOfAngleOffset θ2 a2) ≥
        2 / (nθ : ℝ) := by
      have h1 : lineDirDist (lineOfAngleOffset θ1 a1) (lineOfAngleOffset θ2 a2) =
          lineDirDist (lineOfAngleOffset θ1 0) (lineOfAngleOffset θ2 0) := by
        simp only [lineDirDist]
        congr 1
        · exact h_dir1.trans h_dir1'.symm
        · exact h_dir2.trans h_dir2'.symm
      rw [h1]
      exact grid_dirDist r hr k1 k2 hk1' hk2' h_k_ne
    have h_nθ_pos : 0 < nθ := by
      dsimp only [nθ, numAngles]
      have hpi : 0 < Real.pi := Real.pi_pos
      have hd : 0 < Δ := hΔ_pos
      exact Nat.ceil_pos.mpr (div_pos hpi hd)
    have h_nθ_le : (nθ : ℝ) ≤ Real.pi / Δ + 1 := by
      have h : (nθ : ℝ) < Real.pi / Δ + 1 := nat_ceil_lt_add_one (Real.pi / Δ) (by positivity)
      linarith
    have h7 : 2 / (nθ : ℝ) ≥ 2 * Δ / (Real.pi + Δ) := by
      have h8 : 0 < (nθ : ℝ) := by exact_mod_cast h_nθ_pos
      have h9 : (nθ : ℝ) ≤ Real.pi / Δ + 1 := h_nθ_le
      have h10 : Real.pi / Δ + 1 = (Real.pi + Δ) / Δ := by
        field_simp [hΔ_pos.ne'] <;> ring
      rw [h10] at h9
      calc 2 / (nθ : ℝ) ≥ 2 / ((Real.pi + Δ) / Δ) := by gcongr
        _ = 2 * Δ / (Real.pi + Δ) := by field_simp [hΔ_pos.ne'] <;> ring
    have h11 : 2 * Δ / (Real.pi + Δ) ≥ r / 20 := by
      dsimp only [Δ, delta]
      have h12 : 0 < Real.pi + r / 10 := by positivity
      have h13 : Real.pi < 3.15 := Real.pi_lt_d2
      have h14 : 2 * (r / 10) / (Real.pi + r / 10) ≥ r / 20 := by
        have h15 : r / 10 ≤ 1 / 10 := by linarith
        have h16 : Real.pi + r / 10 < 4 := by linarith
        have h17 : 2 * (r / 10) / (Real.pi + r / 10) = r / (5 * (Real.pi + r / 10)) := by
          field_simp [h12.ne'] <;> ring
        rw [h17]
        gcongr
        nlinarith
      exact h14
    have h14 : lineDist (lineOfAngleOffset θ1 a1) (lineOfAngleOffset θ2 a2) ≥
        lineDirDist (lineOfAngleOffset θ1 a1) (lineOfAngleOffset θ2 a2) := by
      have h15 : lineDist (lineOfAngleOffset θ1 a1) (lineOfAngleOffset θ2 a2) =
          lineDirDist (lineOfAngleOffset θ1 a1) (lineOfAngleOffset θ2 a2) +
          lineOffsetDist (lineOfAngleOffset θ1 a1) (lineOfAngleOffset θ2 a2) := by
        rw [lineDist]
      rw [h15]
      have h16 : 0 ≤ lineOffsetDist (lineOfAngleOffset θ1 a1) (lineOfAngleOffset θ2 a2) := by
        exact dist_nonneg
      linarith
    linarith

end RadialBootstrapping
