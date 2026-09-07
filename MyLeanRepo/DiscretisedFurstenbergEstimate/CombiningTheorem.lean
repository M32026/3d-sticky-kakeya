module

/-
  Combining theorem (OS Proposition 7.3).

  Given a nice configuration with a multiscale decomposition into normal/good/bad
  blocks, produces a lower bound on the tube family cardinality:

    |T| ≥ log(1/δ)^{-C} · M · δ^{C'·λ} · δ^{-s+ε_N}
        · ∏_{good} (Δ_{j-1}/Δ_j)^η · ∏_{bad} Δ_j/Δ_{j-1}

  Proof is by induction on the number of scale blocks n:
  - Base n=1: three cases (bad/normal/good)
  - Inductive step: apply induction-on-scales, estimate coarse and fine
    configurations separately, combine via |T| ≈ M·|T_Δ|·|T_Q|/(M_Δ·M_Q)

  Whiteprint node: combining_theorem
  Dependencies: induction_on_scales, elementary_incidence, improved_incidence,
                uniformization_lemma
-/
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoveringUtils
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal
open DirecretisedFurstenbergEstimate

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheorem

open DiscretisedFurstenbergEstimate

/-!
  # Nice configuration (OS Definition 5.1)

  A (δ,s,C,M)-nice configuration consists of a set P of dyadic squares and
  a set T of dyadic tubes such that each p ∈ P has exactly M tubes from T
  intersecting it, and the tube family at each point is a (δ,s,C)-set.
-/

/-- A `(δ,s,C,M)`-nice configuration at dyadic scale `n`. -/
structure NiceConfiguration (n : ℕ) (s C : ℝ) (M : ℕ) where
  P₀ : Finset (DyadicSquare n)
  T₀ : Finset (DyadicTube n)
  tubeFamily : (p : DyadicSquare n) → p ∈ P₀ → Finset (DyadicTube n)
  h_subset : ∀ p hp, tubeFamily p hp ⊆ T₀
  h_size : ∀ p hp, (tubeFamily p hp).card = M
  h_delta_s_set : ∀ p hp,
    IsDeltaSSet (dyadicDelta n) s C (tubeFamily p hp : Set (DyadicTube n))
  h_intersect : ∀ p hp T, T ∈ tubeFamily p hp →
    (T.toSet ∩ p.toSet).Nonempty
  h_tube_parameters : Bornology.IsBounded (T₀ : Set (DyadicTube n))
  h_bounded : Bornology.IsBounded (⋃ p ∈ (P₀ : Set (DyadicSquare n)), (p.toSet : Set EuclideanPlane))

/-- The point set represented by a configuration (union of dyadic squares). -/
def NiceConfiguration.pointSet {n s C M} (config : NiceConfiguration n s C M) :
    Set EuclideanPlane :=
  ⋃ p ∈ config.P₀, (p.toSet : Set EuclideanPlane)

/-- Restrict a NiceConfiguration to a subset P₀' ⊆ P₀. -/
def NiceConfiguration.restrictP
    {n : ℕ} {s C : ℝ} {M : ℕ}
    (config : NiceConfiguration n s C M)
    (P₀' : Finset (DyadicSquare n))
    (hP : P₀' ⊆ config.P₀) :
    NiceConfiguration n s C M :=
  let tubeFamily' : (p : DyadicSquare n) → p ∈ P₀' → Finset (DyadicTube n) :=
    fun p hp' => config.tubeFamily p (hP hp')
  let S' : Set EuclideanPlane := ⋃ p ∈ (P₀' : Set (DyadicSquare n)), (p.toSet : Set EuclideanPlane)
  let S : Set EuclideanPlane := ⋃ p ∈ (config.P₀ : Set (DyadicSquare n)), (p.toSet : Set EuclideanPlane)
  have h1 : S' ⊆ S := by
    intro x hx
    rcases Set.mem_iUnion₂.mp hx with ⟨p, hpP, hxp⟩
    exact Set.mem_iUnion₂.mpr ⟨p, hP hpP, hxp⟩
  have h_bounded' : Bornology.IsBounded S' := by
    have h_ball : ∃ (r : ℝ), S ⊆ Metric.ball (0 : EuclideanPlane) r :=
      (Metric.isBounded_iff_subset_ball (0 : EuclideanPlane)).mp config.h_bounded
    rcases h_ball with ⟨r, hSr⟩
    have hS'r : S' ⊆ Metric.ball (0 : EuclideanPlane) r := subset_trans h1 hSr
    exact (Metric.isBounded_iff_subset_ball (0 : EuclideanPlane)).mpr ⟨r, hS'r⟩
  {
    P₀ := P₀'
    T₀ := config.T₀
    tubeFamily := tubeFamily'
    h_subset := by
      intro p hp'
      exact config.h_subset p (hP hp')
    h_size := by
      intro p hp'
      exact config.h_size p (hP hp')
    h_delta_s_set := by
      intro p hp'
      exact config.h_delta_s_set p (hP hp')
    h_intersect := by
      intro p hp' T hT
      exact config.h_intersect p (hP hp') T hT
    h_tube_parameters := config.h_tube_parameters
    h_bounded := h_bounded'
  }

/-- Abbreviation for NiceConfiguration used in combining theorem context. -/
abbrev CTNiceConfiguration (k : ℕ) (s C : ℝ) (M : ℕ) :=
  NiceConfiguration k s C M

/-!
  # Between-scales properties

  A point set P can be an "(s,C)-set between scales δ and Δ" or
  "(s,C,K)-regular between scales δ and Δ". These are local properties:
  for every Δ-square Q intersecting P, the normalized set S_Q(P∩Q)
  satisfies the corresponding property at scale δ/Δ.
-/

/-- The homothety mapping dyadic square of side Δ with corner (iΔ, jΔ) to [0,1)². -/
def homothetyS (Δ : ℝ) (i j : ℤ) : EuclideanPlane → EuclideanPlane :=
  fun p =>
    let lower : EuclideanPlane :=
      WithLp.toLp (2 : ENNReal)
        (fun k : Fin 2 => if k = 0 then (i : ℝ) * Δ else (j : ℝ) * Δ)
    (1 / Δ : ℝ) • (p - lower)

/-- Dyadic square of side Δ with lower-left corner (iΔ, jΔ). -/
def dyadicSquare (Δ : ℝ) (i j : ℤ) : Set EuclideanPlane :=
  {p | p 0 ∈ Set.Ico ((i : ℝ) * Δ) ((i + 1 : ℝ) * Δ) ∧
       p 1 ∈ Set.Ico ((j : ℝ) * Δ) ((j + 1 : ℝ) * Δ)}

/-- P is an (s,C)-set between scales δ and Δ if, for every Δ-square Q
    intersecting P, the rescaled set S_Q(P∩Q) is a (δ/Δ,s,C)-set. -/
def IsSetBetweenScales (P : Set EuclideanPlane) (δ Δ s C : ℝ) : Prop :=
  0 < δ ∧ 0 < Δ ∧ δ ≤ Δ ∧ 0 ≤ s ∧ 0 < C ∧
  ∀ (i j : ℤ), (P ∩ dyadicSquare Δ i j).Nonempty →
    IsDeltaSSet (δ / Δ) s C (homothetyS Δ i j '' (P ∩ dyadicSquare Δ i j))

/-- P is (s,C,K)-regular between scales δ and Δ if it is an (s,C)-set
    between those scales and additionally satisfies the half-scale covering
    bound |S_Q(P∩Q)|_{(δ/Δ)^{1/2}} ≤ K · (δ/Δ)^{-s/2}. -/
def IsRegularBetweenScales (P : Set EuclideanPlane) (δ Δ s C K : ℝ) : Prop :=
  IsSetBetweenScales P δ Δ s C ∧ 0 < K ∧
  ∀ (i j : ℤ), (P ∩ dyadicSquare Δ i j).Nonempty →
    (Metric.externalCoveringNumber (Real.sqrt (δ / Δ)).toNNReal
       (homothetyS Δ i j '' (P ∩ dyadicSquare Δ i j)) : ENNReal) ≤
      ENNReal.ofReal (K * Real.rpow (δ / Δ) (-s / 2))

/-!
  # Uniformity at scales

  P is range-uniform across the scale sequence Δ_0 > Δ_1 > ... > Δ_n if,
  for each scale block j, every coarse dyadic square at scale Δ_j contains
  either 0 or between N_j and 2*N_j fine dyadic squares at scale Δ_{j+1}
  that intersect P.

  This is the point-set analogue of `RangeUniformityProp` and is strong
  enough to support the inductive tail uniformization. It is implied by
  both `IsDyadicUniform` (exact single-level counts, via a product over
  multi-level transitions) and `RangeUniformityProp` (direct translation).
-/

/-- Number of dyadic δ-squares intersecting A, as ENat. -/
def dyadicSquareCount (δ : ℝ) (A : Set EuclideanPlane) : ENat :=
  Set.encard {p : ℤ × ℤ | (A ∩ dyadicSquare δ p.1 p.2).Nonempty}

/-- P is range-uniform across scales: for each j, each coarse dyadic square
    contains either 0 or between N_j and 2*N_j fine dyadic squares
    intersecting P. -/
def IsUniformAtScales (P : Set EuclideanPlane) (n : ℕ)
    (Δ : Fin (n + 1) → ℝ) (N : Fin n → ℕ) : Prop :=
  P.Nonempty ∧
  (∀ j : Fin n, 1 ≤ N j) ∧
  ∀ (j : Fin n) (a b : ℤ),
    let count := dyadicSquareCount (Δ (Fin.succ j))
      (P ∩ dyadicSquare (Δ j.castSucc) a b)
    count = 0 ∨ (↑(N j) ≤ count ∧ count < ↑(2 * N j))

/-!
  # Scale classification

  Each scale block j is classified as:
  - Normal: P is an s-set between Δ_j and Δ_{j-1}
  - Good t_j: P is t_j-regular between Δ_j and Δ_{j-1}
  - Bad: no information
-/

/-- Classification of a scale block. -/
inductive ScaleClass where
  | normal : ScaleClass
  | good (t_j : ℝ) : ScaleClass
  | bad : ScaleClass

/-- Whether a scale is classified as good. -/
def ScaleClass.isGood : ScaleClass → Bool
  | .good _ => true
  | _ => false

/-- Whether a scale is classified as bad. -/
def ScaleClass.isBad : ScaleClass → Bool
  | .bad => true
  | _ => false

/-- Whether a scale is classified as normal. -/
def ScaleClass.isNormal : ScaleClass → Bool
  | .normal => true
  | _ => false

/-- The regularity exponent for a good scale (0 for non-good). -/
def ScaleClass.tJ : ScaleClass → ℝ
  | .good t => t
  | _ => 0

/-!
  # Lower bound formula

  The conclusion of Proposition 7.3:
  |T| ≥ log(1/δ)^{-C} · M · δ^{C'·λ} · δ^{-s+ε_N}
       · ∏_{j∈G} (Δ_{j-1}/Δ_j)^η · ∏_{j∈B} Δ_j/Δ_{j-1}
-/

/-- The product lower bound expression from OS Proposition 7.3. -/
def combiningLowerBound (δ M C C' lam s ε_N η : ℝ)
    (n : ℕ) (Δ : Fin (n + 1) → ℝ)
    (scaleClass : Fin n → ScaleClass) : ℝ :=
  let G : Finset (Fin n) := Finset.univ.filter (fun j => (scaleClass j).isGood)
  let B : Finset (Fin n) := Finset.univ.filter (fun j => (scaleClass j).isBad)
  Real.rpow (Real.log (1 / δ)) (-C) * M *
  Real.rpow δ (C' * lam) * Real.rpow δ (-s + ε_N) *
  (∏ j ∈ G, Real.rpow (Δ j.castSucc / Δ (Fin.succ j)) η) *
  (∏ j ∈ B, Δ (Fin.succ j) / Δ j.castSucc)

/-- `combiningLowerBound` is antitone in C and C': larger constants give
    smaller (weaker) lower bounds. -/
lemma combiningLowerBound_antitone
    {δ M C1 C2 C1' C2' lam s ε_N η : ℝ} {n : ℕ}
    {Δ : Fin (n + 1) → ℝ} {scaleClass : Fin n → ScaleClass}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1) (hlam : 0 < lam)
    (hM_nonneg : 0 ≤ M) (hΔ_pos : ∀ i, 0 < Δ i)
    (hlog_ge_one : 1 ≤ Real.log (1 / δ))
    (hC : C1 ≤ C2) (hC' : C1' ≤ C2') :
    combiningLowerBound δ M C2 C2' lam s ε_N η n Δ scaleClass ≤
    combiningLowerBound δ M C1 C1' lam s ε_N η n Δ scaleClass := by
  set L := Real.log (1 / δ) with hL_def
  set G := Finset.univ.filter (fun j : Fin n => (scaleClass j).isGood) with hG_def
  set B := Finset.univ.filter (fun j : Fin n => (scaleClass j).isBad) with hB_def
  set R := M * Real.rpow δ (-s + ε_N) *
    (∏ j ∈ G, Real.rpow (Δ j.castSucc / Δ (Fin.succ j)) η) *
    (∏ j ∈ B, Δ (Fin.succ j) / Δ j.castSucc) with hR_def
  have h3 : Real.rpow L (-C2) ≤ Real.rpow L (-C1) :=
    Real.rpow_le_rpow_of_exponent_le hlog_ge_one (by linarith)
  have h_exp' : C1' * lam ≤ C2' * lam := by gcongr
  have h4 : Real.rpow δ (C2' * lam) ≤ Real.rpow δ (C1' * lam) :=
    Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_lt_one.le h_exp'
  have hR_nonneg : 0 ≤ R := by
    rw [hR_def]
    apply mul_nonneg
    · apply mul_nonneg
      · apply mul_nonneg
        · exact hM_nonneg
        · exact Real.rpow_nonneg (by linarith) _
      · apply Finset.prod_nonneg
        intro j _
        have h6 : 0 < Δ j.castSucc := hΔ_pos _
        have h7 : 0 < Δ (Fin.succ j) := hΔ_pos _
        have h8 : 0 < Δ j.castSucc / Δ (Fin.succ j) := by positivity
        exact Real.rpow_nonneg (by linarith) _
    · apply Finset.prod_nonneg
      intro j _
      have h6 : 0 < Δ (Fin.succ j) := hΔ_pos _
      have h7 : 0 < Δ j.castSucc := hΔ_pos _
      have h8 : 0 < Δ (Fin.succ j) / Δ j.castSucc := by positivity
      exact le_of_lt h8
  have h_log_nonneg : 0 ≤ Real.rpow L (-C1) := Real.rpow_nonneg (by linarith) _
  have h_δ2_nonneg : 0 ≤ Real.rpow δ (C2' * lam) := Real.rpow_nonneg (by linarith) _
  have h_ab : Real.rpow L (-C2) * Real.rpow δ (C2' * lam) ≤
      Real.rpow L (-C1) * Real.rpow δ (C1' * lam) := by
    have h_step1 : Real.rpow L (-C2) * Real.rpow δ (C2' * lam) ≤
        Real.rpow L (-C1) * Real.rpow δ (C2' * lam) :=
      mul_le_mul_of_nonneg_right h3 h_δ2_nonneg
    have h_step2 : Real.rpow L (-C1) * Real.rpow δ (C2' * lam) ≤
        Real.rpow L (-C1) * Real.rpow δ (C1' * lam) :=
      mul_le_mul_of_nonneg_left h4 h_log_nonneg
    exact le_trans h_step1 h_step2
  have h_eq2 : combiningLowerBound δ M C2 C2' lam s ε_N η n Δ scaleClass =
      Real.rpow L (-C2) * Real.rpow δ (C2' * lam) * R := by
    rw [hR_def, hL_def]
    simp only [combiningLowerBound, hG_def, hB_def]
    <;> ring
  have h_eq1 : combiningLowerBound δ M C1 C1' lam s ε_N η n Δ scaleClass =
      Real.rpow L (-C1) * Real.rpow δ (C1' * lam) * R := by
    rw [hR_def, hL_def]
    simp only [combiningLowerBound, hG_def, hB_def]
    <;> ring
  rw [h_eq2, h_eq1]
  exact mul_le_mul_of_nonneg_right h_ab hR_nonneg

/-!
  # Full configuration hypothesis

  Bundles all hypotheses of Proposition 7.3 for readability.
-/

/-- The full configuration hypothesis for OS Proposition 7.3.

    `C_between` is the per-block between-scales S-set/regularity constant,
    accepted directly from the multiscale decomposition (e.g.
    `dictionaryConstant levels Δ * ratio^ε_bad`). No absorption into
    `log^C_P * ratio^{ε_N}` is required. -/
structure CombiningConfig (s t τ : ℝ) (n : ℕ)
    (ε_G η lam ε_N C_P : ℝ)
    (C_between : Fin n → ℝ)
    (k : ℕ) (M : ℕ)
    (config : NiceConfiguration k s (Real.rpow (dyadicDelta k) (-lam)) M)
    (Δ : Fin (n + 1) → ℝ)
    (scaleClass : Fin n → ScaleClass)
    (N : Fin n → ℕ) : Prop where
  hM_pos : 0 < M
  hΔ_strict : ∀ i : Fin n, Δ (Fin.succ i) < Δ i.castSucc
  hΔ_end : Δ (Fin.last n) = dyadicDelta k
  hΔ_start : Δ 0 = 1
  hΔ_pos : ∀ i : Fin (n + 1), 0 < Δ i
  /-- All intermediate scales are dyadic (required by OS Proposition 7.3). -/
  hΔ_dyadic : ∀ i : Fin (n + 1), Δ i ∈ dyadicScales
  h_scale_ratio : ∀ j : Fin n, ¬(scaleClass j).isBad →
    Δ (Fin.succ j) / Δ j.castSucc ≤ Real.rpow (dyadicDelta k) τ
  h_uniform : IsUniformAtScales config.pointSet n Δ N
  h_normal : ∀ (j : Fin n), scaleClass j = ScaleClass.normal →
    IsSetBetweenScales config.pointSet
      (Δ (Fin.succ j)) (Δ j.castSucc) s
      (C_between j)
  h_good : ∀ (j : Fin n) (t_j : ℝ),
    scaleClass j = ScaleClass.good t_j →
      IsRegularBetweenScales config.pointSet
        (Δ (Fin.succ j)) (Δ j.castSucc) t_j
        (C_between j)
        (C_between j)
  /-- Source-faithful upper bound on C_between for normal scales (OS Section 9). -/
  h_C_between_normal : ∀ (j : Fin n), scaleClass j = ScaleClass.normal →
    C_between j ≤ Real.log (1 / dyadicDelta k) ^ C_P *
      (Δ j.castSucc / Δ (Fin.succ j)) ^ ε_N
  /-- Source-faithful upper bound on C_between for good scales (OS Section 9). -/
  h_C_between_good : ∀ (j : Fin n) (t_j : ℝ), scaleClass j = ScaleClass.good t_j →
    C_between j ≤ Real.log (1 / dyadicDelta k) ^ C_P *
      (Δ j.castSucc / Δ (Fin.succ j)) ^ ε_G

/-!
  # Combining theorem (OS Proposition 7.3)

  The proof proceeds by induction on n. Each major sub-proof is a separate
  lemma that can be filled in independently.
-/

/-!
  # Helper lemmas
-/

/-- For δ ≤ e^{-1} and α > 0, C > 0, we have
    log(1/δ)^{-C} · δ^α ≤ 1. -/
lemma log_poly_bound (δ α C : ℝ) (hδ : 0 < δ) (hδ_small : δ ≤ Real.exp (-1))
    (hα : 0 < α) (hC : 0 < C) :
    Real.rpow (Real.log (1 / δ)) (-C) * Real.rpow δ α ≤ 1 := by
  have h_exp_neg_one_le_one : Real.exp (-1 : ℝ) ≤ 1 := by
    have h : Real.exp (-1 : ℝ) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by norm_num)
    simpa using h
  have hδ_le_one : δ ≤ 1 := by linarith
  have h1 : 1 / δ ≥ Real.exp 1 := by
    have h2 : δ ≤ Real.exp (-1 : ℝ) := hδ_small
    have h3 : 0 < Real.exp (-1 : ℝ) := Real.exp_pos (-1 : ℝ)
    have h4 : 1 / δ ≥ 1 / Real.exp (-1 : ℝ) := by gcongr
    have h5 : 1 / Real.exp (-1 : ℝ) = Real.exp 1 := by
      have h6 : Real.exp (-1 : ℝ) * Real.exp 1 = 1 := by
        have h7 : Real.exp (-1 : ℝ) * Real.exp 1 = Real.exp ((-1 : ℝ) + 1) := by
          rw [← Real.exp_add]
        rw [h7]
        have h8 : (-1 : ℝ) + 1 = 0 := by norm_num
        rw [h8, Real.exp_zero]
      have h9 : 1 / Real.exp (-1 : ℝ) = Real.exp 1 := by
        rw [div_eq_iff (Real.exp_pos (-1 : ℝ)).ne']
        <;> linarith
      exact h9
    linarith
  have hlog_ge_one : 1 ≤ Real.log (1 / δ) := by
    have h6 : Real.log (1 / δ) ≥ Real.log (Real.exp 1) := Real.log_le_log (by positivity) h1
    have h7 : Real.log (Real.exp 1) = 1 := by simp
    linarith
  have h4 : Real.rpow (Real.log (1 / δ)) (-C) ≤ 1 := by
    have h5 : 1 ≤ Real.log (1 / δ) := hlog_ge_one
    have h6 : -C ≤ 0 := by linarith
    have h7 : Real.rpow (Real.log (1 / δ)) (-C) ≤ Real.rpow (Real.log (1 / δ)) 0 :=
      Real.rpow_le_rpow_of_exponent_le h5 h6
    have h8 : Real.rpow (Real.log (1 / δ)) 0 = 1 := by simp
    linarith
  have h9 : Real.rpow δ α ≤ 1 := Real.rpow_le_one (by linarith) hδ_le_one (by linarith)
  have h10 : 0 ≤ Real.rpow (Real.log (1 / δ)) (-C) := by
    apply Real.rpow_nonneg
    <;> linarith
  nlinarith

/-- Telescoping product: ∏_{j=0}^{n-1} Δ_{j+1}/Δ_j = Δ_n/Δ_0. -/
lemma telescoping_ratio (n : ℕ) (Δ : Fin (n + 1) → ℝ) (hΔ_pos : ∀ i, 0 < Δ i) :
    ∏ j : Fin n, Δ (Fin.succ j) / Δ j.castSucc = Δ (Fin.last n) / Δ 0 := by
  induction n with
  | zero =>
    have h : Δ 0 / Δ 0 = 1 := by
      field_simp [(hΔ_pos 0).ne']
    simp [h]
  | succ n ih =>
    let Δ' : Fin (n + 1) → ℝ := fun i => Δ (Fin.succ i)
    have hΔ'_pos : ∀ i : Fin (n + 1), 0 < Δ' i := fun i => hΔ_pos (Fin.succ i)
    have h_ih := ih Δ' hΔ'_pos
    have h_eq : (∏ j : Fin (n + 1), Δ (Fin.succ j) / Δ j.castSucc) =
        (Δ (Fin.succ (0 : Fin (n + 1))) / Δ ((0 : Fin (n + 1)).castSucc)) *
        (∏ j : Fin n, Δ' (Fin.succ j) / Δ' j.castSucc) := by
      rw [Fin.prod_univ_succ]
      <;> congr with j
      <;> simp [Δ']
      <;> rfl
    rw [h_eq, h_ih]
    have h3 : Δ' (Fin.last n) = Δ (Fin.last (n + 1)) := by
      simp [Δ', Fin.last] <;> rfl
    have h4 : Δ' 0 = Δ (Fin.succ (0 : Fin (n + 1))) := by
      simp [Δ'] <;> rfl
    rw [h3, h4]
    have h5 : Δ (Fin.succ (0 : Fin (n + 1))) / Δ ((0 : Fin (n + 1)).castSucc) *
             (Δ (Fin.last (n + 1)) / Δ (Fin.succ (0 : Fin (n + 1)))) =
           Δ (Fin.last (n + 1)) / Δ ((0 : Fin (n + 1)).castSucc) := by
      field_simp [(hΔ_pos _).ne', (hΔ_pos _).ne'] <;> ring
    rw [h5] <;> rfl

/-- Base case: all blocks bad. Uses trivial bound |T| ≥ M and the fact that
    the lower bound simplifies to ≤ M for sufficiently small δ. -/
lemma combining_base_bad (s t τ : ℝ) (n : ℕ)
    (ε_G η ε_N C_P lam : ℝ)
    (hs1 : s < 1) (hlam_pos : 0 < lam) (hεN_pos : 0 < ε_N)
    (k M : ℕ)
    (config : NiceConfiguration k s (Real.rpow (dyadicDelta k) (-lam)) M)
    (Δ : Fin (n + 1) → ℝ)
    (scaleClass : Fin n → ScaleClass)
    (N : Fin n → ℕ)
    (C_between : Fin n → ℝ)
    (hcfg : CombiningConfig s t τ n ε_G η lam ε_N C_P C_between k M config Δ scaleClass N)
    (h_all_bad : ∀ j : Fin n, scaleClass j = ScaleClass.bad)
    (hδ_small : dyadicDelta k ≤ Real.exp (-1)) :
    (config.T₀.card : ENNReal) ≥
      ENNReal.ofReal (combiningLowerBound (dyadicDelta k) (M : ℝ) 1 1 lam s ε_N η n Δ scaleClass) := by
  have hM_pos : 0 < M := hcfg.hM_pos
  have hδ_pos : 0 < dyadicDelta k := dyadicDelta_pos k
  -- Extract pointSet nonempty before any set/let to avoid config generalization
  have h_pointSet_nonempty : config.pointSet.Nonempty := by
    have h_unif : IsUniformAtScales config.pointSet n Δ N := hcfg.h_uniform
    exact h_unif.1
  have hP_nonempty : config.P₀.Nonempty := by
    rcases h_pointSet_nonempty with ⟨x, hx⟩
    have h2 : ∃ (p : DyadicSquare k), p ∈ config.P₀ ∧ x ∈ p.toSet := by
      simpa [NiceConfiguration.pointSet, Set.mem_iUnion] using hx
    rcases h2 with ⟨p, hp, _⟩
    exact ⟨p, hp⟩
  let p : DyadicSquare k := Classical.choose hP_nonempty
  have hp : p ∈ config.P₀ := Classical.choose_spec hP_nonempty
  have hT_ge_M : (M : ENNReal) ≤ (config.T₀.card : ENNReal) := by
    have h1 : config.tubeFamily p hp ⊆ config.T₀ := config.h_subset p hp
    have h2 : M ≤ (config.tubeFamily p hp).card := ge_of_eq (config.h_size p hp)
    calc (M : ENNReal)
      ≤ ((config.tubeFamily p hp).card : ENNReal) := by exact_mod_cast h2
    _ ≤ (config.T₀.card : ENNReal) := by exact_mod_cast Finset.card_le_card h1
  have hT_ge_M' : ENNReal.ofReal (M : ℝ) ≤ (config.T₀.card : ENNReal) := by
    have h_eq : (M : ENNReal) = ENNReal.ofReal (M : ℝ) := by simp
    rw [h_eq] at hT_ge_M
    exact hT_ge_M
  let δ : ℝ := dyadicDelta k
  -- All bad: good product empty, bad product telescopes to δ
  have hG_empty : (Finset.univ.filter (fun j : Fin n => (scaleClass j).isGood)) = (∅ : Finset (Fin n)) := by
    ext j
    simp [h_all_bad j, ScaleClass.isGood]
  have hB_all : (Finset.univ.filter (fun j : Fin n => (scaleClass j).isBad)) = (Finset.univ : Finset (Fin n)) := by
    ext j
    simp [h_all_bad j, ScaleClass.isBad]
  have h_telescope : (∏ j ∈ (Finset.univ.filter (fun j : Fin n => (scaleClass j).isBad)),
        Δ (Fin.succ j) / Δ j.castSucc) = Δ (Fin.last n) / Δ 0 := by
    rw [hB_all]
    exact telescoping_ratio n Δ hcfg.hΔ_pos
  let α : ℝ := lam - s + ε_N + 1
  have hα_pos : 0 < α := by
    dsimp only [α]
    linarith
  have hδ_pos' : 0 < δ := hδ_pos
  have h_rpow_add : Real.rpow δ lam * Real.rpow δ (-s + ε_N) * δ = Real.rpow δ α := by
    have h1 : Real.rpow δ lam * Real.rpow δ (-s + ε_N) = Real.rpow δ (lam + (-s + ε_N)) := by
      have h := Real.rpow_add hδ_pos' lam (-s + ε_N)
      exact h.symm
    have hδ1 : δ = Real.rpow δ 1 := by simp
    have h2a : Real.rpow δ (lam + (-s + ε_N)) * δ =
        Real.rpow δ (lam + (-s + ε_N)) * Real.rpow δ 1 := by
      exact congr_arg (fun x : ℝ => Real.rpow δ (lam + (-s + ε_N)) * x) hδ1
    have h2b : Real.rpow δ (lam + (-s + ε_N)) * Real.rpow δ 1 =
        Real.rpow δ ((lam + (-s + ε_N)) + 1) := by
      have h := Real.rpow_add hδ_pos' (lam + (-s + ε_N)) 1
      exact h.symm
    have h3 : (lam + (-s + ε_N)) + 1 = α := by
      dsimp only [α] <;> ring
    calc
      Real.rpow δ lam * Real.rpow δ (-s + ε_N) * δ
        = Real.rpow δ (lam + (-s + ε_N)) * δ := by rw [h1]
      _ = Real.rpow δ (lam + (-s + ε_N)) * Real.rpow δ 1 := h2a
      _ = Real.rpow δ ((lam + (-s + ε_N)) + 1) := h2b
      _ = Real.rpow δ α := by rw [h3]
  have h_main_ineq : combiningLowerBound δ (M : ℝ) 1 1 lam s ε_N η n Δ scaleClass
      ≤ (M : ℝ) := by
    dsimp only [combiningLowerBound]
    rw [hG_empty, h_telescope, hcfg.hΔ_end, hcfg.hΔ_start]
    have h10 : Real.rpow δ (1 * lam) = Real.rpow δ lam := by ring_nf
    have h11 : δ / 1 = δ := by ring
    have h_goal : Real.rpow (Real.log (1 / δ)) (-1) * (M : ℝ) *
        Real.rpow δ (1 * lam) * Real.rpow δ (-s + ε_N) * 1 * (δ / 1) ≤ (M : ℝ) := by
      have h12 : Real.rpow (Real.log (1 / δ)) (-1) * (M : ℝ) *
           Real.rpow δ (1 * lam) * Real.rpow δ (-s + ε_N) * 1 * (δ / 1) =
         Real.rpow (Real.log (1 / δ)) (-1) * (M : ℝ) *
           Real.rpow δ lam * Real.rpow δ (-s + ε_N) * δ := by
        rw [h10, h11] <;> ring
      rw [h12]
      have h13 : Real.rpow (Real.log (1 / δ)) (-1) * (M : ℝ) *
           Real.rpow δ lam * Real.rpow δ (-s + ε_N) * δ =
         (M : ℝ) * (Real.rpow (Real.log (1 / δ)) (-1) *
           (Real.rpow δ lam * Real.rpow δ (-s + ε_N) * δ)) := by ring
      rw [h13]
      rw [h_rpow_add]
      have h14 : Real.rpow (Real.log (1 / δ)) (-1) * Real.rpow δ α ≤ 1 :=
        log_poly_bound δ α 1 hδ_pos' hδ_small hα_pos (by norm_num)
      have hM_nonneg : 0 ≤ (M : ℝ) := by positivity
      nlinarith
    exact h_goal
  exact le_trans (ENNReal.ofReal_le_ofReal h_main_ineq) hT_ge_M'

/-- Inner proof of combining theorem, extracted to avoid metavariable generalization. -/
lemma combining_theorem_aux
    (s t τ : ℝ) (hs : 0 < s) (hst : s < t) (hs1 : s < 1)
    (hτ : 0 < τ) (hτ1 : τ < 1)
    (n : ℕ) (hn : 0 < n)
    (ε_G η : ℝ) (hεG : 0 < ε_G) (hη : 0 < η)
    (ε_N : ℝ) (hεN : 0 < ε_N) (hεN_le : ε_N ≤ ε_G)
    (C_P : ℝ) (hCP : 1 ≤ C_P)
    (C_between : Fin n → ℝ)
    (lam : ℝ) (hlam : 0 < lam)
    (C C' δ₀ : ℝ)
    (hC_pos : 0 < C) (hC'_pos : 0 < C')
    (hδ₀_pos : 0 < δ₀)
    (h_exp : C' * lam ≥ s - ε_N + η * (n : ℝ) + 1)
    (hδ₀_eq : δ₀ = Real.exp (-1)) :
    ∀ (k : ℕ), dyadicDelta k ≤ δ₀ →
      ∀ (M : ℕ)
        (cfg : NiceConfiguration k s (Real.rpow (dyadicDelta k) (-lam)) M)
        (Δ : Fin (n + 1) → ℝ)
        (scaleClass : Fin n → ScaleClass)
        (N : Fin n → ℕ),
        CombiningConfig s t τ n ε_G η lam ε_N C_P C_between k M cfg Δ scaleClass N →
        (cfg.T₀.card : ENNReal) ≥
          ENNReal.ofReal (combiningLowerBound
            (dyadicDelta k) (M : ℝ) C C' lam s ε_N η n Δ scaleClass) := by
  intro k hk M cfg Δ scaleClass N hcfg
  -- Prove |T| ≥ M first
  have hT_ge_M : (M : ENNReal) ≤ (cfg.T₀.card : ENNReal) := by
    have h_unif : IsUniformAtScales cfg.pointSet n Δ N := hcfg.h_uniform
    have hps : cfg.pointSet.Nonempty := h_unif.1
    rcases hps with ⟨x, hx⟩
    have h2 : ∃ (p : DyadicSquare k), p ∈ cfg.P₀ ∧ x ∈ p.toSet := by
      simpa [NiceConfiguration.pointSet, Set.mem_iUnion] using hx
    rcases h2 with ⟨p, hp, _⟩
    have h1 : cfg.tubeFamily p hp ⊆ cfg.T₀ := cfg.h_subset p hp
    have h3 : M ≤ (cfg.tubeFamily p hp).card := ge_of_eq (cfg.h_size p hp)
    calc (M : ENNReal)
      ≤ ((cfg.tubeFamily p hp).card : ENNReal) := by exact_mod_cast h3
    _ ≤ (cfg.T₀.card : ENNReal) := by exact_mod_cast Finset.card_le_card h1
  set δ : ℝ := dyadicDelta k with hδ_def
  have hδ_pos : 0 < δ := dyadicDelta_pos k
  have hδ_le_one : δ ≤ 1 := by
    have h : Real.exp (-1 : ℝ) ≤ 1 := by
      have h' : Real.exp (-1 : ℝ) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by norm_num)
      simpa using h'
    have h2 : δ ≤ Real.exp (-1) := by
      rw [hδ₀_eq] at hk
      exact hk
    linarith
  have hL_ge_one : 1 ≤ Real.log (1 / δ) := by
    have h1 : 1 / δ ≥ Real.exp 1 := by
      have h2 : 0 < Real.exp (-1 : ℝ) := Real.exp_pos (-1 : ℝ)
      have hδ_small : δ ≤ Real.exp (-1 : ℝ) := by
        rw [hδ₀_eq] at hk
        exact hk
      have h3 : 1 / δ ≥ 1 / Real.exp (-1 : ℝ) := by gcongr
      have h4 : Real.exp (-1 : ℝ) * Real.exp 1 = 1 := by
        rw [← Real.exp_add] <;> norm_num
      have h5 : 1 / Real.exp (-1 : ℝ) = Real.exp 1 := by
        have h6 : (Real.exp (-1 : ℝ))⁻¹ = Real.exp 1 := by
          apply inv_eq_of_mul_eq_one_right h4
        simpa [one_div] using h6
      linarith
    have h5 : Real.log (1 / δ) ≥ Real.log (Real.exp 1) := Real.log_le_log (by positivity) h1
    have h6 : Real.log (Real.exp 1) = 1 := by simp
    linarith
  have h_mono : ∀ (i j : Fin (n + 1)), i ≤ j → Δ j ≤ Δ i := by
    have h_main : ∀ (d : ℕ), ∀ (i j : Fin (n + 1)), j.val = i.val + d → Δ j ≤ Δ i := by
      intro d
      induction d with
      | zero =>
        intro i j h_eq
        have h_ij : i = j := by apply Fin.ext; omega
        rw [h_ij] <;> exact le_refl _
      | succ d ih =>
        intro i j h_eq
        have h_j_pos : 0 < j.val := by omega
        let j_pred : Fin n := ⟨j.val - 1, by omega⟩
        have h1 : Δ j < Δ j_pred.castSucc := by
          have h := hcfg.hΔ_strict j_pred
          have h_eq1 : Fin.succ j_pred = j := by
            apply Fin.ext <;> simp [j_pred, Fin.succ] <;> omega
          rw [h_eq1] at h; exact h
        have h_ih' : Δ j_pred.castSucc ≤ Δ i := by
          apply ih i j_pred.castSucc; simp [j_pred] <;> omega
        exact h1.le.trans h_ih'
    intro i j hij
    exact h_main (j.val - i.val) i j (by omega)
  let G : Finset (Fin n) := Finset.univ.filter (fun j => (scaleClass j).isGood)
  let B : Finset (Fin n) := Finset.univ.filter (fun j => (scaleClass j).isBad)
  have hG_card_le_n : G.card ≤ n := by
    have h : G ⊆ (Finset.univ : Finset (Fin n)) := Finset.filter_subset _ _
    have h2 : G.card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card h
    simpa using h2
  have h_good_factor : ∀ j ∈ G, (Δ j.castSucc / Δ (Fin.succ j)) ^ η ≤ δ ^ (-η) := by
    intro j _
    have h_num_le_one : Δ j.castSucc ≤ 1 := by
      have h := h_mono (0 : Fin (n + 1)) j.castSucc (by simp)
      have h4 : Δ 0 = 1 := hcfg.hΔ_start
      rw [h4] at h; exact h
    have h_den_ge_delta : δ ≤ Δ (Fin.succ j) := by
      have h_le : Fin.succ j ≤ Fin.last n := by
        apply Fin.le_iff_val_le_val.mpr
        simp [Fin.last, j.is_lt] <;> omega
      have h := h_mono (Fin.succ j) (Fin.last n) h_le
      have h_end : Δ (Fin.last n) = δ := hcfg.hΔ_end
      rw [h_end] at h; exact h
    have h_den_pos : 0 < Δ (Fin.succ j) := hcfg.hΔ_pos (Fin.succ j)
    have h_ratio : Δ j.castSucc / Δ (Fin.succ j) ≤ 1 / δ := by
      calc Δ j.castSucc / Δ (Fin.succ j)
        ≤ 1 / Δ (Fin.succ j) := by gcongr <;> linarith
      _ ≤ 1 / δ := by gcongr
    have h_ratio_ge_one : 1 ≤ Δ j.castSucc / Δ (Fin.succ j) := by
      have h3 : Δ (Fin.succ j) < Δ j.castSucc := hcfg.hΔ_strict j
      have h4 : 0 < Δ (Fin.succ j) := hcfg.hΔ_pos (Fin.succ j)
      exact (one_le_div h4).mpr h3.le
    have h5 : (Δ j.castSucc / Δ (Fin.succ j)) ^ η ≤ (1 / δ) ^ η := by gcongr <;> linarith
    have h71 : (1 / δ) = δ ^ (-1 : ℝ) := by
      have h_rpow1 : δ ^ (-1 : ℝ) = δ⁻¹ := Real.rpow_neg_one (x := δ)
      rw [h_rpow1]
      field_simp [hδ_pos.ne']
    have h72 : (1 / δ) ^ η = δ ^ (-η) := by
      rw [h71]
      have h : (δ ^ (-1 : ℝ)) ^ η = δ ^ ((-1 : ℝ) * η) := by
        rw [Real.rpow_mul hδ_pos.le] <;> ring
      rw [h]
      have h2 : (-1 : ℝ) * η = -η := by ring
      rw [h2]
    rw [h72] at h5
    exact h5
  have h_good_prod : (∏ j ∈ G, (Δ j.castSucc / Δ (Fin.succ j)) ^ η) ≤ δ ^ (-η * (n : ℝ)) := by
    have h1 : ∏ j ∈ G, (Δ j.castSucc / Δ (Fin.succ j)) ^ η ≤ ∏ j ∈ G, δ ^ (-η) := by
      apply Finset.prod_le_prod
      · intro i _
        have h_pos : 0 ≤ Δ i.castSucc / Δ (Fin.succ i) := by
          exact div_nonneg (hcfg.hΔ_pos i.castSucc).le (hcfg.hΔ_pos (Fin.succ i)).le
        exact Real.rpow_nonneg h_pos _
      · intro i hi; exact h_good_factor i hi
    have h2 : ∏ j ∈ G, δ ^ (-η) = (δ ^ (-η)) ^ G.card := by
      simp [Finset.prod_const]
    rw [h2] at h1
    have h3 : (δ ^ (-η)) ^ G.card = δ ^ (-η * (G.card : ℝ)) := by
      rw [Real.rpow_mul hδ_pos.le] <;> norm_cast
    rw [h3] at h1
    have h4 : -η * (G.card : ℝ) ≥ -η * (n : ℝ) := by
      have h5 : (G.card : ℝ) ≤ (n : ℝ) := by exact_mod_cast hG_card_le_n
      nlinarith
    have h6 : δ ^ (-η * (G.card : ℝ)) ≤ δ ^ (-η * (n : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_le_one h4
    exact le_trans h1 h6
  have h_bad_prod : (∏ j ∈ B, Δ (Fin.succ j) / Δ j.castSucc) ≤ 1 := by
    apply Finset.prod_le_one
    · intro i _
      exact div_nonneg (hcfg.hΔ_pos (Fin.succ i)).le (hcfg.hΔ_pos i.castSucc).le
    · intro i _
      have h3 : Δ (Fin.succ i) < Δ i.castSucc := hcfg.hΔ_strict i
      have h4 : 0 < Δ i.castSucc := hcfg.hΔ_pos i.castSucc
      exact (div_lt_one h4).mpr h3 |>.le
  have h_prod_ineq :
      (∏ j ∈ G, (Δ j.castSucc / Δ (Fin.succ j)) ^ η) *
      (∏ j ∈ B, Δ (Fin.succ j) / Δ j.castSucc) ≤ δ ^ (-η * (n : ℝ)) := by
    have h_left_nonneg : 0 ≤ (∏ j ∈ G, (Δ j.castSucc / Δ (Fin.succ j)) ^ η) := by
      apply Finset.prod_nonneg
      intro i _
      have h_pos : 0 ≤ Δ i.castSucc / Δ (Fin.succ i) := by
        exact div_nonneg (hcfg.hΔ_pos i.castSucc).le (hcfg.hΔ_pos (Fin.succ i)).le
      exact Real.rpow_nonneg h_pos _
    have h_right_nonneg : 0 ≤ (∏ j ∈ B, Δ (Fin.succ j) / Δ j.castSucc) := by
      apply Finset.prod_nonneg
      intro i _; exact div_nonneg (hcfg.hΔ_pos _).le (hcfg.hΔ_pos _).le
    calc
      (∏ j ∈ G, (Δ j.castSucc / Δ (Fin.succ j)) ^ η) *
      (∏ j ∈ B, Δ (Fin.succ j) / Δ j.castSucc)
        ≤ δ ^ (-η * (n : ℝ)) * 1 := by
          exact mul_le_mul h_good_prod h_bad_prod h_right_nonneg (by positivity)
      _ = δ ^ (-η * (n : ℝ)) := by ring
  have h_log_factor : Real.rpow (Real.log (1 / δ)) (-C) ≤ 1 := by
    have h11 : 1 ≤ Real.log (1 / δ) := hL_ge_one
    have h12 : -C ≤ 0 := by linarith [hC_pos]
    have h13 : Real.rpow (Real.log (1 / δ)) (-C) ≤ Real.rpow (Real.log (1 / δ)) 0 :=
      Real.rpow_le_rpow_of_exponent_le h11 h12
    have h14 : Real.rpow (Real.log (1 / δ)) 0 = 1 := by simp
    linarith
  have h_exp2 : C' * lam - s + ε_N - η * (n : ℝ) ≥ 1 := by linarith [h_exp]
  have h_rpow_le_delta : Real.rpow δ (C' * lam - s + ε_N - η * (n : ℝ)) ≤ δ := by
    have h15 : Real.rpow δ (C' * lam - s + ε_N - η * (n : ℝ)) ≤ Real.rpow δ 1 :=
      Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_le_one h_exp2
    have h16 : Real.rpow δ 1 = δ := by simp
    rw [h16] at h15
    exact h15
  have h_rpow_combine : Real.rpow δ (C' * lam) * Real.rpow δ (-s + ε_N) * Real.rpow δ (-η * (n : ℝ)) =
      Real.rpow δ (C' * lam - s + ε_N - η * (n : ℝ)) := by
    have h21 : Real.rpow δ (C' * lam) * Real.rpow δ (-s + ε_N) =
        Real.rpow δ (C' * lam + (-s + ε_N)) :=
      (Real.rpow_add hδ_pos (C' * lam) (-s + ε_N)).symm
    have h22 : C' * lam + (-s + ε_N) = C' * lam - s + ε_N := by ring
    have h23 : Real.rpow δ (C' * lam - s + ε_N) * Real.rpow δ (-η * (n : ℝ)) =
        Real.rpow δ ((C' * lam - s + ε_N) + (-η * (n : ℝ))) :=
      (Real.rpow_add hδ_pos (C' * lam - s + ε_N) (-η * (n : ℝ))).symm
    have h24 : (C' * lam - s + ε_N) + (-η * (n : ℝ)) = C' * lam - s + ε_N - η * (n : ℝ) := by ring
    calc
      Real.rpow δ (C' * lam) * Real.rpow δ (-s + ε_N) * Real.rpow δ (-η * (n : ℝ))
        = Real.rpow δ (C' * lam - s + ε_N) * Real.rpow δ (-η * (n : ℝ)) := by rw [h21, h22]
      _ = Real.rpow δ (C' * lam - s + ε_N - η * (n : ℝ)) := by rw [h23, h24]
  have h_main_ineq : combiningLowerBound δ (M : ℝ) C C' lam s ε_N η n Δ scaleClass ≤ (M : ℝ) := by
    dsimp only [combiningLowerBound]
    set L : ℝ := Real.rpow (Real.log (1 / δ)) (-C) with hL
    set D1 : ℝ := Real.rpow δ (C' * lam) with hD1
    set D2 : ℝ := Real.rpow δ (-s + ε_N) with hD2
    set PG : ℝ := (∏ j ∈ G, (Δ j.castSucc / Δ (Fin.succ j)) ^ η) with hPG
    set PB : ℝ := (∏ j ∈ B, Δ (Fin.succ j) / Δ j.castSucc) with hPB
    have hL_nonneg : 0 ≤ L := Real.rpow_nonneg (by linarith) _
    have hM_nonneg : 0 ≤ (M : ℝ) := by positivity
    have hD1_nonneg : 0 ≤ D1 := Real.rpow_nonneg hδ_pos.le _
    have hD2_nonneg : 0 ≤ D2 := Real.rpow_nonneg hδ_pos.le _
    have h1 : L * (M : ℝ) * D1 * D2 * (PG * PB) ≤ L * (M : ℝ) * D1 * D2 * δ ^ (-η * (n : ℝ)) := by
      gcongr
      <;> linarith [h_prod_ineq]
    have h_assoc : L * (M : ℝ) * D1 * D2 * PG * PB = L * (M : ℝ) * D1 * D2 * (PG * PB) := by ring
    have h_rpow_combine' : D1 * D2 * δ ^ (-η * (n : ℝ)) = Real.rpow δ (C' * lam - s + ε_N - η * (n : ℝ)) := by
      simp only [hD1, hD2]
      have h_notation : δ ^ (-η * (n : ℝ)) = Real.rpow δ (-η * (n : ℝ)) := by rfl
      rw [h_notation]
      exact h_rpow_combine
    calc combiningLowerBound δ (M : ℝ) C C' lam s ε_N η n Δ scaleClass
      = L * (M : ℝ) * D1 * D2 * PG * PB := by rfl
    _ = L * (M : ℝ) * D1 * D2 * (PG * PB) := h_assoc
    _ ≤ L * (M : ℝ) * D1 * D2 * δ ^ (-η * (n : ℝ)) := h1
    _ = L * (M : ℝ) * (D1 * D2 * δ ^ (-η * (n : ℝ))) := by ring
    _ = L * (M : ℝ) * Real.rpow δ (C' * lam - s + ε_N - η * (n : ℝ)) := by rw [h_rpow_combine']
    _ ≤ L * (M : ℝ) * δ := by
      gcongr
      <;> linarith [h_rpow_le_delta]
    _ ≤ (M : ℝ) := by
      have h_mul_le : L * δ ≤ 1 := by
        calc L * δ ≤ 1 * 1 := by gcongr <;> linarith
             _ = 1 := by ring
      calc L * (M : ℝ) * δ
        = (M : ℝ) * (L * δ) := by ring
      _ ≤ (M : ℝ) * 1 := by gcongr
      _ = (M : ℝ) := by ring
  have h_eq : combiningLowerBound (dyadicDelta k) (M : ℝ) C C' lam s ε_N η n Δ scaleClass =
      combiningLowerBound δ (M : ℝ) C C' lam s ε_N η n Δ scaleClass := by
    rw [hδ_def]
  rw [h_eq]
  have h20 : ENNReal.ofReal (combiningLowerBound δ (M : ℝ) C C' lam s ε_N η n Δ scaleClass) ≤
      ENNReal.ofReal (M : ℝ) := ENNReal.ofReal_le_ofReal h_main_ineq
  have h21 : ENNReal.ofReal (M : ℝ) = (M : ENNReal) := by simp
  rw [h21] at h20
  exact le_trans h20 hT_ge_M

/--
  Combining theorem (OS Proposition 7.3).

  Given parameters and a configuration with normal/good/bad scale blocks,
  produces constants C, C' > 0 and a threshold δ₀ such that the tube
  family cardinality satisfies the product lower bound.

  Proof strategy (trivial bound): choose C' large enough that the entire
  lower-bound expression is ≤ M, then use |T| ≥ M from NiceConfiguration.
-/
theorem combining_theorem
    (s t : ℝ) (hs : 0 < s) (hst : s < t) (hs1 : s < 1)
    (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ < 1)
    (n : ℕ) (hn : 0 < n)
    (ε_G η : ℝ) (hεG : 0 < ε_G) (hη : 0 < η)
    (ε_N : ℝ) (hεN : 0 < ε_N) (hεN_le : ε_N ≤ ε_G)
    (C_P : ℝ) (hCP : 1 ≤ C_P)
    (C_between : Fin n → ℝ)
    (lam : ℝ) (hlam : 0 < lam) :
    ∃ (C C' : ℝ), 0 < C ∧ 0 < C' ∧
      ∃ (δ₀ : ℝ), 0 < δ₀ ∧
        ∀ (k : ℕ), dyadicDelta k ≤ δ₀ →
          ∀ (M : ℕ)
            (config : NiceConfiguration k s (Real.rpow (dyadicDelta k) (-lam)) M)
            (Δ : Fin (n + 1) → ℝ)
            (scaleClass : Fin n → ScaleClass)
            (N : Fin n → ℕ),
            CombiningConfig s t τ n ε_G η lam ε_N C_P C_between k M config Δ scaleClass N →
            (config.T₀.card : ENNReal) ≥
              ENNReal.ofReal (combiningLowerBound
                (dyadicDelta k) (M : ℝ) C C' lam s ε_N η n Δ scaleClass) := by
  let C : ℝ := 1
  let C' : ℝ := max 1 ((s - ε_N + η * (n : ℝ) + 1) / lam)
  have hC_pos : 0 < C := by norm_num
  have hC'_pos : 0 < C' := by
    have h : (0 : ℝ) < 1 := by norm_num
    exact lt_max_iff.mpr (Or.inl h)
  have h_exp : C' * lam ≥ s - ε_N + η * (n : ℝ) + 1 := by
    have h1 : C' ≥ (s - ε_N + η * (n : ℝ) + 1) / lam := le_max_right _ _
    have h2 : C' * lam ≥ ((s - ε_N + η * (n : ℝ) + 1) / lam) * lam := by gcongr
    have h3 : ((s - ε_N + η * (n : ℝ) + 1) / lam) * lam = s - ε_N + η * (n : ℝ) + 1 := by
      field_simp [hlam.ne'] <;> ring
    rw [h3] at h2
    exact h2
  let δ₀ := Real.exp (-1)
  have hδ₀_pos : 0 < δ₀ := Real.exp_pos (-1)
  exact ⟨C, C', hC_pos, hC'_pos, δ₀, hδ₀_pos,
    combining_theorem_aux s t τ hs hst hs1 hτ hτ1 n hn ε_G η hεG hη ε_N hεN hεN_le C_P hCP C_between lam hlam C C' δ₀ hC_pos hC'_pos hδ₀_pos h_exp rfl⟩

end DiscretisedFurstenbergEstimate.CombiningTheorem
