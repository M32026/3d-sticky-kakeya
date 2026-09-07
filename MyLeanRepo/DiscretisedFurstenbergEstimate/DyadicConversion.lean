module

/-
  Conversion between DSquare/DTube (ElementaryIncidence) and
  DyadicSquare/DyadicTube (InductionOnScales).

  These types are structurally identical (same integer fields, same dyadic scale)
  but use different metrics:
  - DSquare: Euclidean distance between lower-left corners
  - DyadicSquare: no MetricSpace instance (not needed)
  - DTube: sup norm on (slope, intercept)
  - DyadicTube: L1 norm on (slope, intercept)

  The metrics are bilipschitz equivalent with constants 1 and 2.

  Whiteprint node: dyadic_conversion
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.ElementaryIncidence
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.DiscretisedFurstenbergEstimate.TubesAndSlopes
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open scoped ENNReal NNReal
open DirecretisedFurstenbergEstimate

namespace DiscretisedFurstenbergEstimate.DyadicConversion

variable {n : ℕ}

/-- The scale δ = 2^{-n} used by DSquare/DTube. -/
abbrev δEI (n : ℕ) : ℝ := (2 : ℝ)^(-(n : ℤ))

/-!
  # Bijection between DSquare and DyadicSquare
-/

/-- Convert DSquare to DyadicSquare. -/
def dSquareToDyadicSquare (p : DSquare n) : DyadicSquare n :=
  ⟨p.i, p.j⟩

/-- Convert DyadicSquare to DSquare. -/
def dyadicSquareToDSquare (p : DyadicSquare n) : DSquare n :=
  ⟨p.i, p.j⟩

lemma dSquareEquiv : Function.Bijective (dSquareToDyadicSquare (n := n)) := by
  constructor
  · intro p q h
    cases p; cases q; simp [dSquareToDyadicSquare] at h ⊢ <;> exact h
  · intro p
    refine' ⟨dyadicSquareToDSquare p, _⟩
    cases p; simp [dSquareToDyadicSquare, dyadicSquareToDSquare] <;> rfl

/-- DSquare.toSet uses ℝ × ℝ, DyadicSquare.toSet uses EuclideanPlane.
    They describe the same geometric set via the canonical equivalence. -/
lemma toSet_correspondence (p : DSquare n) (x : EuclideanPlane) :
    x ∈ (dSquareToDyadicSquare p).toSet ↔
    (x 0, x 1) ∈ p.toSet := by
  have hδ : δ n = dyadicDelta n := by
    simp [δ, dyadicDelta] <;> ring
  have h_iff : x ∈ (dSquareToDyadicSquare p).toSet ↔
      (p.i : ℝ) * dyadicDelta n ≤ x 0 ∧ x 0 < ((p.i : ℝ) + 1) * dyadicDelta n ∧
      (p.j : ℝ) * dyadicDelta n ≤ x 1 ∧ x 1 < ((p.j : ℝ) + 1) * dyadicDelta n := by
    simp [dSquareToDyadicSquare, DyadicSquare.toSet]
    <;> rfl
  have h_iff2 : (x 0, x 1) ∈ p.toSet ↔
      (p.i : ℝ) * δ n ≤ x 0 ∧ x 0 < ((p.i : ℝ) + 1) * δ n ∧
      (p.j : ℝ) * δ n ≤ x 1 ∧ x 1 < ((p.j : ℝ) + 1) * δ n := by
    simp [DSquare.toSet] <;> rfl
  rw [h_iff, h_iff2]
  rw [hδ]

/-!
  # Bijection between DTube and DyadicTube
-/

/-- Convert DTube to DyadicTube. -/
def dTubeToDyadicTube (T : DTube n) : DyadicTube n :=
  ⟨T.a, T.b⟩

/-- Convert DyadicTube to DTube. -/
def dyadicTubeToDTube (T : DyadicTube n) : DTube n :=
  ⟨T.a, T.b⟩

lemma dTubeEquiv : Function.Bijective (dTubeToDyadicTube (n := n)) := by
  constructor
  · intro T U h
    cases T; cases U; simp [dTubeToDyadicTube] at h ⊢ <;> exact h
  · intro T
    refine' ⟨dyadicTubeToDTube T, _⟩
    cases T; simp [dTubeToDyadicTube, dyadicTubeToDTube] <;> rfl

lemma scale_eq : δEI n = dyadicDelta n := by
  simp [δEI, dyadicDelta]
  <;> ring

lemma slope_eq (T : DTube n) :
    (dTubeToDyadicTube T).slope = T.slope := by
  have h : (dTubeToDyadicTube T).slope = (T.a : ℝ) * dyadicDelta n := by
    simp [dTubeToDyadicTube, DyadicTube.slope]
  rw [h]
  have h2 : T.slope = (T.a : ℝ) * δ n := by
    simp [DTube.slope]
  rw [h2]
  have h3 : δ n = dyadicDelta n := by
    simp [δ, dyadicDelta] <;> ring
  rw [h3]

lemma intercept_eq (T : DTube n) :
    (dTubeToDyadicTube T).intercept = T.intercept := by
  have h : (dTubeToDyadicTube T).intercept = (T.b : ℝ) * dyadicDelta n := by
    simp [dTubeToDyadicTube, DyadicTube.intercept]
  rw [h]
  have h2 : T.intercept = (T.b : ℝ) * δ n := by
    simp [DTube.intercept]
  rw [h2]
  have h3 : δ n = dyadicDelta n := by
    simp [δ, dyadicDelta] <;> ring
  rw [h3]

lemma slope_eq' (T : DyadicTube n) :
    (dyadicTubeToDTube T).slope = T.slope := by
  have h : (dyadicTubeToDTube T).slope = (T.a : ℝ) * δ n := by
    simp [dyadicTubeToDTube, DTube.slope]
  rw [h]
  have h2 : T.slope = (T.a : ℝ) * dyadicDelta n := by
    simp [DyadicTube.slope]
  rw [h2]
  have h3 : δ n = dyadicDelta n := by
    simp [δ, dyadicDelta] <;> ring
  rw [h3]

lemma intercept_eq' (T : DyadicTube n) :
    (dyadicTubeToDTube T).intercept = T.intercept := by
  have h : (dyadicTubeToDTube T).intercept = (T.b : ℝ) * δ n := by
    simp [dyadicTubeToDTube, DTube.intercept]
  rw [h]
  have h2 : T.intercept = (T.b : ℝ) * dyadicDelta n := by
    simp [DyadicTube.intercept]
  rw [h2]
  have h3 : δ n = dyadicDelta n := by
    simp [δ, dyadicDelta] <;> ring
  rw [h3]

/-!
  # Metric comparison

  DTube uses sup norm: dist_D = max(|Δslope|, |Δintercept|)
  DyadicTube uses L1 norm: dist_L1 = |Δslope| + |Δintercept|

  We have: dist_D ≤ dist_L1 ≤ 2 * dist_D
-/

lemma dist_dyadic_eq (T U : DTube n) :
    dist (dTubeToDyadicTube T) (dTubeToDyadicTube U) =
      |T.slope - U.slope| + |T.intercept - U.intercept| := by
  have hsl : (dTubeToDyadicTube T).slope = T.slope := slope_eq T
  have hsi : (dTubeToDyadicTube T).intercept = T.intercept := intercept_eq T
  have hul : (dTubeToDyadicTube U).slope = U.slope := slope_eq U
  have hui : (dTubeToDyadicTube U).intercept = U.intercept := intercept_eq U
  have h : dist (dTubeToDyadicTube T) (dTubeToDyadicTube U) =
      |(dTubeToDyadicTube T).slope - (dTubeToDyadicTube U).slope| +
      |(dTubeToDyadicTube T).intercept - (dTubeToDyadicTube U).intercept| := by
    exact Metric.mem_sphere.mp rfl
  rw [h, hsl, hsi, hul, hui]

lemma dist_dtube_eq (T U : DTube n) :
    dist T U = max (|T.slope - U.slope|) (|T.intercept - U.intercept|) := by
  have h : dist T U = dist T.toParam U.toParam := by rfl
  rw [h]
  have h2 : dist T.toParam U.toParam =
      max (dist (T.slope) (U.slope)) (dist (T.intercept) (U.intercept)) := by
    simp [DTube.toParam, Prod.dist_eq] <;> rfl
  rw [h2]
  have h3 : dist (T.slope) (U.slope) = |T.slope - U.slope| := by
    simp [Real.dist_eq]
  have h4 : dist (T.intercept) (U.intercept) = |T.intercept - U.intercept| := by
    simp [Real.dist_eq]
  rw [h3, h4] <;> ring

lemma dist_dtube_le_dyadic (T U : DTube n) :
    dist T U ≤ dist (dTubeToDyadicTube T) (dTubeToDyadicTube U) := by
  rw [dist_dyadic_eq, dist_dtube_eq]
  let a := |T.slope - U.slope|
  let b := |T.intercept - U.intercept|
  have h3 : 0 ≤ a := abs_nonneg _
  have h4 : 0 ≤ b := abs_nonneg _
  have h : max a b ≤ a + b := by
    have h5 : a ≤ a + b := by linarith
    have h6 : b ≤ a + b := by linarith
    exact max_le h5 h6
  exact h

lemma dist_dyadic_le_two_dtube (T U : DTube n) :
    dist (dTubeToDyadicTube T) (dTubeToDyadicTube U) ≤ 2 * dist T U := by
  rw [dist_dyadic_eq, dist_dtube_eq]
  let a := |T.slope - U.slope|
  let b := |T.intercept - U.intercept|
  have h3 : 0 ≤ a := abs_nonneg _
  have h4 : 0 ≤ b := abs_nonneg _
  have h : a + b ≤ 2 * max a b := by
    cases' le_total a b with h5 h5
    · rw [max_eq_right h5] <;> linarith
    · rw [max_eq_left h5] <;> linarith
  exact h

/-!
  # DyadicTube → AffineLine map

  Maps a DyadicTube to its center line as an AffineLine.
  Used to bridge discrete tube families with the continuous improved_incidence theorem.
-/

/-- Map a DyadicTube to its center line as an AffineLine.
    The tube has equation |y - slope*x - intercept| ≤ δ, so the center line
    is y = slope*x + intercept, passing through (0, intercept) with direction (1, slope). -/
noncomputable def dyadicTubeToAffineLine (T : DyadicTube n) : AffineLine :=
  let p0 := TubesAndSlopes.mkPlane 0 T.intercept
  let v := TubesAndSlopes.mkPlane 1 T.slope
  let aff := AffineSubspace.mk' p0 (Submodule.span ℝ {v})
  have h_v_ne_zero : v ≠ 0 := by
    intro h
    have h1 : v 0 = 0 := by rw [h] <;> simp
    have h2 : v 0 = 1 := TubesAndSlopes.mkPlane_apply0 1 T.slope
    rw [h2] at h1 <;> norm_num at h1
  have h_finrank : Module.finrank ℝ aff.direction = 1 := by
    have h_dir : aff.direction = Submodule.span ℝ {v} := by
      simp [aff, AffineSubspace.direction_mk'] <;> rfl
    rw [h_dir]
    exact finrank_span_singleton h_v_ne_zero
  ⟨aff, h_finrank⟩

/-- The underlying affine subspace of dyadicTubeToAffineLine. -/
lemma dyadicTubeToAffineLine_eq (T : DyadicTube n) :
    (dyadicTubeToAffineLine T).1 = AffineSubspace.mk'
      (TubesAndSlopes.mkPlane 0 T.intercept)
      (Submodule.span ℝ {TubesAndSlopes.mkPlane 1 T.slope}) := by
  simp [dyadicTubeToAffineLine] <;> rfl

/-- The DyadicTube → AffineLine map is injective (slope and intercept determine the line). -/
lemma dyadicTubeToAffineLine_injective :
    Function.Injective (dyadicTubeToAffineLine (n := n)) := by
  intro T U h
  have h_lines : (dyadicTubeToAffineLine T).1 = (dyadicTubeToAffineLine U).1 := by
    exact congr_arg Subtype.val h
  let pT := TubesAndSlopes.mkPlane 0 T.intercept
  let pU := TubesAndSlopes.mkPlane 0 U.intercept
  let vT := TubesAndSlopes.mkPlane 1 T.slope
  let vU := TubesAndSlopes.mkPlane 1 U.slope
  have hT : (dyadicTubeToAffineLine T).1 = AffineSubspace.mk' pT (Submodule.span ℝ {vT}) :=
    dyadicTubeToAffineLine_eq T
  have hU : (dyadicTubeToAffineLine U).1 = AffineSubspace.mk' pU (Submodule.span ℝ {vU}) :=
    dyadicTubeToAffineLine_eq U
  rw [hT, hU] at h_lines
  -- Both pT and pU are on the line (x=0 points), and the line has direction (1, slope),
  -- so the x=0 point is unique.
  have hpT : pT ∈ AffineSubspace.mk' pT (Submodule.span ℝ {vT}) := by
    rw [AffineSubspace.mem_mk'] <;> simp
  have hpU_in : pU ∈ AffineSubspace.mk' pT (Submodule.span ℝ {vT}) := by
    rw [h_lines] <;> rw [AffineSubspace.mem_mk'] <;> simp
  have h_exists : ∃ (c : ℝ), pU - pT = c • vT := by
    have h : pU -ᵥ pT ∈ (Submodule.span ℝ {vT}) := by
      rw [AffineSubspace.mem_mk'] at hpU_in <;> exact hpU_in
    have h' : pU -ᵥ pT = pU - pT := by exact PiLp.ext (congrFun rfl)
    rw [h'] at h
    have h'' : ∃ (a : ℝ), a • vT = pU - pT := by
      simpa [Submodule.mem_span_singleton] using h
    rcases h'' with ⟨c, hc⟩
    exact ⟨c, hc.symm⟩
  rcases h_exists with ⟨c, hc⟩
  have hc0 : c = 0 := by
    have h : (pU - pT) 0 = c := by
      simpa [hc, vT, TubesAndSlopes.mkPlane_apply0] using congr_arg (fun x : EuclideanPlane => x 0) hc
    have h' : (pU - pT) 0 = 0 := by
      simp [pT, pU, TubesAndSlopes.mkPlane_apply0]
    linarith
  have hsi : T.intercept = U.intercept := by
    have h : (pU - pT) 1 = U.intercept - T.intercept := by
      simp [pT, pU, TubesAndSlopes.mkPlane_apply1] <;> ring
    have h2 : (pU - pT) 1 = 0 := by
      rw [hc, hc0] <;> simp
    linarith
  have hsl : T.slope = U.slope := by
    have h1 : (AffineSubspace.mk' pT (Submodule.span ℝ {vT})).direction = (Submodule.span ℝ {vT}) := by
      simp [AffineSubspace.direction_mk'] <;> rfl
    have h2 : (AffineSubspace.mk' pU (Submodule.span ℝ {vU})).direction = (Submodule.span ℝ {vU}) := by
      simp [AffineSubspace.direction_mk'] <;> rfl
    have h3 : (AffineSubspace.mk' pT (Submodule.span ℝ {vT})).direction =
        (AffineSubspace.mk' pU (Submodule.span ℝ {vU})).direction := by
      rw [h_lines]
    have h_dir : (Submodule.span ℝ {vT}) = (Submodule.span ℝ {vU}) := by
      rw [h1, h2] at h3; exact h3
    have h_vU_in : vU ∈ (Submodule.span ℝ {vT}) := by
      rw [h_dir] <;> exact Submodule.subset_span (by simp)
    have h_exists2 : ∃ (d : ℝ), vU = d • vT := by
      have h : ∃ (a : ℝ), a • vT = vU := by
        simpa [Submodule.mem_span_singleton] using h_vU_in
      rcases h with ⟨d, hd⟩
      exact ⟨d, hd.symm⟩
    rcases h_exists2 with ⟨d, hd⟩
    have hd1 : d = 1 := by
      have h : (vU) 0 = d := by
        simpa [hd, vT, TubesAndSlopes.mkPlane_apply0] using congr_arg (fun x : EuclideanPlane => x 0) hd
      have h' : (vU) 0 = 1 := TubesAndSlopes.mkPlane_apply0 1 U.slope
      linarith
    have h : (vU) 1 = (vT) 1 := by
      rw [hd, hd1]
      simpa using one_smul ℝ vT
    have h_slope_eq : U.slope = T.slope := by
      simpa [vT, vU, TubesAndSlopes.mkPlane_apply1] using h
    exact h_slope_eq.symm
  have hδ_pos : 0 < dyadicDelta n := dyadicDelta_pos n
  have ha : T.a = U.a := by
    have h_eq1 : T.slope = (T.a : ℝ) * dyadicDelta n := by rfl
    have h_eq2 : U.slope = (U.a : ℝ) * dyadicDelta n := by rfl
    have h : (T.a : ℝ) * dyadicDelta n = (U.a : ℝ) * dyadicDelta n := by
      rw [←h_eq1, ←h_eq2, hsl]
    have h' : (T.a : ℝ) = (U.a : ℝ) := by
      apply (mul_right_inj' hδ_pos.ne').mp
      simpa [mul_comm] using h
    exact_mod_cast h'
  have hb : T.b = U.b := by
    have h_eq1 : T.intercept = (T.b : ℝ) * dyadicDelta n := by rfl
    have h_eq2 : U.intercept = (U.b : ℝ) * dyadicDelta n := by rfl
    have h : (T.b : ℝ) * dyadicDelta n = (U.b : ℝ) * dyadicDelta n := by
      rw [←h_eq1, ←h_eq2, hsi]
    have h' : (T.b : ℝ) = (U.b : ℝ) := by
      apply (mul_right_inj' hδ_pos.ne').mp
      simpa [mul_comm] using h
    exact_mod_cast h'
  cases T <;> cases U <;> congr <;> tauto

/-!
  # Covering number transfer

  Key fact: a 2δ-ball in the L1 metric contains at most 13 grid points.
  This lets us transfer external covering numbers between DTube (sup) and
  DyadicTube (L1) with a constant factor of 13.
-/

/-- Integer offsets (da, db) with |da| + |db| ≤ 2. Exactly 13 pairs. -/
def offsetsL1Two : Finset (ℤ × ℤ) :=
  {(0,0), (1,0), (-1,0), (0,1), (0,-1), (2,0), (-2,0), (0,2), (0,-2),
   (1,1), (1,-1), (-1,1), (-1,-1)}

local instance decidableEqDyadicTube : DecidableEq (DyadicTube n) := by
  intro T U
  exact decidable_of_iff (T.a = U.a ∧ T.b = U.b)
    ⟨by rintro ⟨h1, h2⟩; cases T; cases U; simp_all, by intro h; simp [h]⟩

lemma mem_offsetsL1Two (p : ℤ × ℤ) :
    p ∈ offsetsL1Two ↔ |p.1| + |p.2| ≤ 2 := by
  constructor
  · intro h
    simp only [offsetsL1Two, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> norm_num
  · intro h
    have h_abs1 : |p.1| ≤ 2 := by linarith [abs_nonneg p.2]
    have h_abs2 : |p.2| ≤ 2 := by linarith [abs_nonneg p.1]
    have h1 : -2 ≤ p.1 := (abs_le.mp h_abs1).1
    have h2 : p.1 ≤ 2 := (abs_le.mp h_abs1).2
    have h3 : -2 ≤ p.2 := (abs_le.mp h_abs2).1
    have h4 : p.2 ≤ 2 := (abs_le.mp h_abs2).2
    rcases p with ⟨p1, p2⟩
    interval_cases p1 <;> interval_cases p2 <;> simp [offsetsL1Two] at h ⊢ <;> (try omega) <;> decide

lemma card_offsetsL1Two : offsetsL1Two.card = 13 := by decide

/-- The set of DyadicTubes within L1 distance 2δ of a given tube is exactly
    the image of offsetsL1Two, hence has at most 13 elements. -/
lemma dyadicBallTwoDelta_eq (y : DyadicTube n) :
    {T : DyadicTube n | dist T y ≤ 2 * dyadicDelta n} =
      let img : Finset (DyadicTube n) := offsetsL1Two.image
        (fun p : ℤ × ℤ => DyadicTube.mk (y.a + p.1) (y.b + p.2))
      (img : Set (DyadicTube n)) := by
  ext T
  simp only [Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_image]
  constructor
  · intro h
    have h3 : dist T y = dyadicDelta n * ((|(T.a - y.a : ℤ)| : ℝ) + (|(T.b - y.b : ℤ)| : ℝ)) :=
      DyadicTube.dist_eq T y
    have h4 : 0 < dyadicDelta n := dyadicDelta_pos n
    rw [h3] at h
    have h5 : (|(T.a - y.a : ℤ)| : ℝ) + (|(T.b - y.b : ℤ)| : ℝ) ≤ 2 := by
      nlinarith
    have h2 : |(T.a - y.a : ℤ)| + |(T.b - y.b : ℤ)| ≤ 2 := by exact_mod_cast h5
    refine' ⟨(T.a - y.a, T.b - y.b), _ , _⟩
    · exact (mem_offsetsL1Two _).mpr h2
    · cases T <;> simp <;> ring
  · rintro ⟨p, hp, rfl⟩
    have h2 : |p.1| + |p.2| ≤ 2 := (mem_offsetsL1Two p).mp hp
    have h2' : (|p.1| : ℝ) + (|p.2| : ℝ) ≤ 2 := by exact_mod_cast h2
    have hpos : 0 < dyadicDelta n := dyadicDelta_pos n
    have h3 : dist (DyadicTube.mk (y.a + p.1) (y.b + p.2)) y =
        dyadicDelta n * ((|p.1| : ℝ) + (|p.2| : ℝ)) := by
      have h4 := DyadicTube.dist_eq (DyadicTube.mk (y.a + p.1) (y.b + p.2)) y
      simpa [dist, DyadicTube.a, DyadicTube.b] using h4
    rw [h3]
    calc dyadicDelta n * ((|p.1| : ℝ) + (|p.2| : ℝ))
      ≤ dyadicDelta n * 2 := by gcongr
    _ = 2 * dyadicDelta n := by ring

lemma covering_dyadic_le_13 (A : Set (DTube n)) :
    Metric.externalCoveringNumber (dyadicDelta n).toNNReal (dTubeToDyadicTube '' A) ≤
      13 * Metric.externalCoveringNumber (dyadicDelta n).toNNReal A := by
  let f : DTube n → DyadicTube n := fun x => dTubeToDyadicTube x
  let δnn := (dyadicDelta n).toNNReal
  have hδ_pos : 0 < dyadicDelta n := dyadicDelta_pos n
  let _i : DecidableEq (DyadicTube n) := decidableEqDyadicTube
  have h_main : ∀ (C : Set (DTube n)), Metric.IsCover δnn A C →
      Metric.externalCoveringNumber δnn (f '' A) ≤ 13 * C.encard := by
    intro C hC
    by_cases hfin : C.Finite
    · let Cf := hfin.toFinset
      have hC_set : (Cf : Set (DTube n)) = C := by exact Set.Finite.coe_toFinset hfin
      let C' : Finset (DyadicTube n) := Cf.biUnion (fun x =>
        offsetsL1Two.image (fun p : ℤ × ℤ => DyadicTube.mk ((f x).a + p.1) ((f x).b + p.2)))
      have h1 : Metric.IsCover δnn (f '' A) (C' : Set (DyadicTube n)) := by
        intro y hy
        rcases hy with ⟨z, hz, rfl⟩
        have hz' : z ∈ A := hz
        have hcov : ∃ x ∈ C, edist z x ≤ δnn := hC hz'
        rcases hcov with ⟨x, hx, hdist⟩
        have hx' : x ∈ Cf := by
          have h_x_in_C : x ∈ C := hx
          simpa [Cf, hC_set] using h_x_in_C
        have hdist' : dist z x ≤ dyadicDelta n := by
          have h_eq1 : edist z x = ENNReal.ofReal (dist z x) := by simp [edist_dist]
          have h_eq2 : (↑δnn : ENNReal) = ENNReal.ofReal (dyadicDelta n) := by
            simp [δnn, NNReal.coe_mk] <;> rfl
          rw [h_eq1, h_eq2] at hdist
          have h9 : ENNReal.ofReal (dist z x) ≤ ENNReal.ofReal (dyadicDelta n) := hdist
          have h10 : dist z x ≤ dyadicDelta n := by
            have hnz2 : 0 ≤ dyadicDelta n := by linarith
            have h_iff : ENNReal.ofReal (dist z x) ≤ ENNReal.ofReal (dyadicDelta n) ↔ dist z x ≤ dyadicDelta n :=
              ENNReal.ofReal_le_ofReal_iff (h := hnz2)
            exact h_iff.mp h9
          exact h10
        have h2 : dist (f z) (f x) ≤ 2 * dyadicDelta n := by
          calc dist (f z) (f x) ≤ 2 * dist z x := dist_dyadic_le_two_dtube z x
            _ ≤ 2 * dyadicDelta n := by gcongr
        have h5 : f z ∈ (C' : Set (DyadicTube n)) := by
          have h4 : f z ∈ {T : DyadicTube n | dist T (f x) ≤ 2 * dyadicDelta n} := h2
          rw [dyadicBallTwoDelta_eq (f x)] at h4
          exact Finset.mem_biUnion.mpr ⟨x, hx', h4⟩
        exact ⟨f z, h5, by simp [edist_dist, hδ_pos]⟩
      have h2 : C'.card ≤ 13 * Cf.card := by
        calc C'.card
          ≤ ∑ x ∈ Cf, (offsetsL1Two.image (fun p : ℤ × ℤ => DyadicTube.mk ((f x).a + p.1) ((f x).b + p.2))).card :=
            Finset.card_biUnion_le
          _ ≤ ∑ _ ∈ Cf, offsetsL1Two.card := by
            gcongr with x _
            exact Finset.card_image_le
          _ = ∑ _ ∈ Cf, 13 := by rw [card_offsetsL1Two] <;> rfl
          _ = 13 * Cf.card := by simp [Finset.sum_const] <;> ring
      have h31 : ((C' : Set (DyadicTube n)).encard) = (C'.card : ℕ∞) := by simp
      have h3 : Metric.externalCoveringNumber δnn (f '' A) ≤ (C'.card : ℕ∞) := by
        have h := Metric.IsCover.externalCoveringNumber_le_encard h1
        rw [h31] at h
        exact h
      have h5 : C.encard = (Cf.card : ℕ∞) := by
        have h51 : (Cf : Set (DTube n)) = C := hC_set
        have h52 : ((Cf : Set (DTube n)).encard) = (Cf.card : ℕ∞) := by simp
        rw [←h51, h52]
      have h4 : (C'.card : ℕ∞) ≤ 13 * C.encard := by
        rw [h5]
        exact_mod_cast h2
      exact h3.trans h4
    · have hC_inf : C.encard = ⊤ := Set.encard_eq_top_iff.mpr hfin
      rw [hC_inf] <;> simp
  set a := Metric.externalCoveringNumber δnn A with ha
  by_cases h_top : a = ⊤
  · rw [h_top] <;> simp
  · have h_lt_top : a < ⊤ := lt_top_iff_ne_top.mpr h_top
    obtain ⟨m, hm⟩ : ∃ m : ℕ, a = ↑m := by exact Option.ne_none_iff_exists'.mp h_top
    have h_exists : ∃ (C : Set (DTube n)), Metric.IsCover δnn A C ∧ C.encard ≤ ↑m := by
      by_contra h
      push Not at h
      have h1 : ∀ (S : Set (DTube n)), Metric.IsCover δnn A S → ↑(m + 1) ≤ S.encard := by
        intro S hS
        have h2 : ↑m < S.encard := h S hS
        by_cases h4 : S.encard = ⊤
        · rw [h4] <;> simp
        · have h5 : ∃ k : ℕ, S.encard = ↑k := by exact Option.ne_none_iff_exists'.mp h4
          rcases h5 with ⟨k, hk⟩
          rw [hk] at h2
          have h6 : m < k := by exact_mod_cast h2
          have h7 : m + 1 ≤ k := by linarith
          rw [hk]
          exact_mod_cast h7
      have h5 : a ≥ ↑(m + 1) := by
        dsimp only [a, Metric.externalCoveringNumber]
        exact le_iInf_iff.mpr (fun S => le_iInf_iff.mpr (fun hS => h1 S hS))
      rw [hm] at h5
      have h_false : (↑m : ℕ∞) < (↑m + 1 : ℕ∞) := by
        have h1 : (↑m + 1 : ℕ∞) = ↑(m + 1) := by norm_cast
        rw [h1]
        exact ENat.coe_lt_coe.mpr (Nat.lt_succ_self m)
      exact not_le.mpr h_false h5
    rcases h_exists with ⟨C, hC, hC_encard⟩
    have h6 := h_main C hC
    have h7 : Metric.externalCoveringNumber δnn (f '' A) ≤ 13 * (↑m : ℕ∞) := by
      calc Metric.externalCoveringNumber δnn (f '' A)
        ≤ 13 * C.encard := h6
      _ ≤ 13 * (↑m : ℕ∞) := by gcongr
    rw [hm]
    exact h7

/-- Round-trip: DTube → DyadicTube → DTube is identity. -/
lemma roundtrip_dtube (T : DTube n) :
    dyadicTubeToDTube (dTubeToDyadicTube T) = T := by
  cases T <;> simp [dyadicTubeToDTube, dTubeToDyadicTube] <;> rfl

/-- Round-trip: DyadicTube → DTube → DyadicTube is identity. -/
lemma roundtrip_dyadic (T : DyadicTube n) :
    dTubeToDyadicTube (dyadicTubeToDTube T) = T := by
  cases T <;> simp [dyadicTubeToDTube, dTubeToDyadicTube] <;> rfl

lemma covering_dtube_le_dyadic (A : Set (DTube n)) :
    Metric.externalCoveringNumber (dyadicDelta n).toNNReal A ≤
      Metric.externalCoveringNumber (dyadicDelta n).toNNReal (dTubeToDyadicTube '' A) := by
  let f : DTube n → DyadicTube n := fun x => dTubeToDyadicTube x
  let δnn := (dyadicDelta n).toNNReal
  have h_main : ∀ (C : Set (DyadicTube n)), Metric.IsCover δnn (f '' A) C →
      Metric.externalCoveringNumber δnn A ≤ C.encard := by
    intro C hC
    let C' : Set (DTube n) := f ⁻¹' C
    have h1 : Metric.IsCover δnn A C' := by
      intro z hz
      have h2 : f z ∈ f '' A := Set.mem_image_of_mem f hz
      have h3 : ∃ (y : DyadicTube n), y ∈ C ∧ edist (f z) y ≤ δnn := hC h2
      rcases h3 with ⟨y, hy, hdist⟩
      let x := dyadicTubeToDTube y
      have h_rt : f x = y := roundtrip_dyadic y
      have h_goal : f x ∈ C := by
        rw [h_rt]
        exact hy
      have hx : x ∈ C' := by
        simpa [C', Set.mem_preimage] using h_goal
      have h4 : edist z x ≤ edist (f z) y := by
        have h5 : dist z x ≤ dist (f z) y := dist_dtube_le_dyadic z x
        have h6 : edist z x = ENNReal.ofReal (dist z x) := by simp [edist_dist]
        have h7 : edist (f z) y = ENNReal.ofReal (dist (f z) y) := by simp [edist_dist]
        rw [h6, h7]
        gcongr
      have h6 : edist z x ≤ δnn := le_trans h4 hdist
      exact ⟨x, hx, h6⟩
    have h_inj : Function.Injective (dyadicTubeToDTube (n := n)) := by
      intro T U h
      have h1 : dTubeToDyadicTube (dyadicTubeToDTube T) = T := roundtrip_dyadic T
      have h2 : dTubeToDyadicTube (dyadicTubeToDTube U) = U := roundtrip_dyadic U
      have h3 : dTubeToDyadicTube (dyadicTubeToDTube T) = dTubeToDyadicTube (dyadicTubeToDTube U) := by
        rw [h]
      rw [h1, h2] at h3
      exact h3
    have h_img : dyadicTubeToDTube '' C = C' := by
      ext z
      simp only [C', Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨y, hy, rfl⟩
        have h_rt : f (dyadicTubeToDTube y) = y := roundtrip_dyadic y
        rw [h_rt]
        exact hy
      · intro hz
        refine' ⟨dTubeToDyadicTube z, hz, _⟩
        exact roundtrip_dtube z
    have h6 : C'.encard = C.encard := by
      rw [←h_img]
      exact h_inj.encard_image C
    exact (Metric.IsCover.externalCoveringNumber_le_encard h1).trans (le_of_eq h6)
  dsimp only [Metric.externalCoveringNumber]
  exact le_iInf_iff.mpr (fun C => le_iInf_iff.mpr (fun hC => h_main C hC))

/-- Transfer IsDeltaSSet from DTube (sup metric) to DyadicTube (L1 metric).
    The constant scales by 13. -/
lemma deltaSSet_dTubeToDyadic {s C : ℝ} (hs : 0 ≤ s) (hC : 0 < C)
    {T : Set (DTube n)}
    (h : IsDeltaSSet (dyadicDelta n) s C T) :
    IsDeltaSSet (dyadicDelta n) s (13 * C)
      (dTubeToDyadicTube '' T) := by
  let δ := dyadicDelta n
  let δnn := δ.toNNReal
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  have hne : (dTubeToDyadicTube '' T).Nonempty := h.1.image dTubeToDyadicTube
  have hC'_pos : 0 < 13 * C := by positivity
  refine' ⟨hne, by positivity, hC'_pos, hs, _⟩
  intro y r hr
  let x := dyadicTubeToDTube y
  have hball : dTubeToDyadicTube ⁻¹' (Metric.closedBall y r) ⊆ Metric.closedBall x r := by
    intro z hz
    have h : dist (dTubeToDyadicTube z) y ≤ r := hz
    have h2 : dist z x ≤ dist (dTubeToDyadicTube z) y := dist_dtube_le_dyadic z x
    exact le_trans h2 h
  let S := T ∩ dTubeToDyadicTube ⁻¹' (Metric.closedBall y r)
  have hS_sub : S ⊆ T ∩ Metric.closedBall x r := by
    intro z hz
    exact ⟨hz.1, hball hz.2⟩
  have himg : dTubeToDyadicTube '' S = dTubeToDyadicTube '' T ∩ Metric.closedBall y r := by
    ext z
    simp only [Set.mem_image, Set.mem_inter_iff]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨Set.mem_image_of_mem _ hw.1, hw.2⟩
    · rintro ⟨h1, h2⟩
      rcases h1 with ⟨w, hw, rfl⟩
      exact ⟨w, ⟨hw, h2⟩, rfl⟩
  set a := Metric.externalCoveringNumber δnn (dTubeToDyadicTube '' S) with ha
  set b := 13 * Metric.externalCoveringNumber δnn S with hb
  have h41 : a ≤ b := covering_dyadic_le_13 S
  have h4 : (a : ENNReal) ≤ (13 : ENNReal) * (Metric.externalCoveringNumber δnn S : ENNReal) := by
    have h43 : (a : ENNReal) ≤ (b : ENNReal) := by exact ENat.toENNReal_le.mpr h41
    have h44 : (b : ENNReal) = (13 : ENNReal) * (Metric.externalCoveringNumber δnn S : ENNReal) := by
      simp [hb]
      <;> norm_cast
    rw [h44] at h43
    exact h43
  have h5 : (Metric.externalCoveringNumber δnn S : ENNReal) ≤
      (Metric.externalCoveringNumber δnn (T ∩ Metric.closedBall x r) : ENNReal) := by
    have h51 : Metric.externalCoveringNumber δnn S ≤ Metric.externalCoveringNumber δnn (T ∩ Metric.closedBall x r) :=
    Metric.externalCoveringNumber_mono_set (ε := δnn) hS_sub
    exact ENat.toENNReal_le.mpr h51
  have h6 : (Metric.externalCoveringNumber δnn (T ∩ Metric.closedBall x r) : ENNReal) ≤
      ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (Metric.externalCoveringNumber δnn T : ENNReal) :=
    h.2.2.2.2 x r hr
  have h71 : Metric.externalCoveringNumber δnn T ≤ Metric.externalCoveringNumber δnn (dTubeToDyadicTube '' T) :=
    covering_dtube_le_dyadic T
  have h7 : (Metric.externalCoveringNumber δnn T : ENNReal) ≤
      (Metric.externalCoveringNumber δnn (dTubeToDyadicTube '' T) : ENNReal) := by
    exact ENat.toENNReal_le.mpr h71
  have h_goal : (Metric.externalCoveringNumber δnn (dTubeToDyadicTube '' T ∩ Metric.closedBall y r) : ENNReal) ≤
      ENNReal.ofReal (13 * C) * (ENNReal.ofReal r) ^ s *
        (Metric.externalCoveringNumber δnn (dTubeToDyadicTube '' T) : ENNReal) := by
    have h_img2 : dTubeToDyadicTube '' S = dTubeToDyadicTube '' T ∩ Metric.closedBall y r := himg
    rw [←h_img2]
    calc (Metric.externalCoveringNumber δnn (dTubeToDyadicTube '' S) : ENNReal)
      ≤ 13 * (Metric.externalCoveringNumber δnn S : ENNReal) := h4
    _ ≤ 13 * (Metric.externalCoveringNumber δnn (T ∩ Metric.closedBall x r) : ENNReal) := by gcongr
    _ ≤ 13 * (ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (Metric.externalCoveringNumber δnn T : ENNReal)) := by gcongr
    _ = ENNReal.ofReal (13 * C) * (ENNReal.ofReal r) ^ s * (Metric.externalCoveringNumber δnn T : ENNReal) := by
      have h_eq : (13 : ENNReal) * (ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (Metric.externalCoveringNumber δnn T : ENNReal)) =
          ENNReal.ofReal (13 * C) * (ENNReal.ofReal r) ^ s * (Metric.externalCoveringNumber δnn T : ENNReal) := by
        have h1 : ENNReal.ofReal (13 * C) = (13 : ENNReal) * ENNReal.ofReal C := by
          rw [ENNReal.ofReal_mul (by norm_num)] <;> norm_cast
        rw [h1]
        <;> simp [mul_assoc, mul_comm, mul_left_comm] <;> ring_nf
      exact h_eq
    _ ≤ ENNReal.ofReal (13 * C) * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber δnn (dTubeToDyadicTube '' T) : ENNReal) := by gcongr
  exact h_goal

/-- Transfer IsDeltaSSet from DyadicTube (L1 metric) to DTube (sup metric).
    The constant scales by 13 * 2^s. -/
lemma deltaSSet_dyadicToDTube {s C : ℝ} (hs : 0 ≤ s) (hC : 0 < C)
    {T : Set (DyadicTube n)}
    (h : IsDeltaSSet (dyadicDelta n) s C T) :
    IsDeltaSSet (dyadicDelta n) s (13 * C * 2 ^ s)
      (dTubeToDyadicTube ⁻¹' T) := by
  let δ := dyadicDelta n
  let δnn := δ.toNNReal
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  let A := dTubeToDyadicTube ⁻¹' T
  have hne : A.Nonempty := by
    rcases h.1 with ⟨y, hy⟩
    have h_rt : dTubeToDyadicTube (dyadicTubeToDTube y) = y := roundtrip_dyadic y
    exact ⟨dyadicTubeToDTube y, by simpa [A, h_rt] using hy⟩
  have hC'_pos : 0 < 13 * C * 2 ^ s := by positivity
  refine' ⟨hne, by positivity, hC'_pos, hs, _⟩
  intro x r hr
  let y := dTubeToDyadicTube x
  have hball1 : Metric.closedBall x r ⊆ dTubeToDyadicTube ⁻¹' (Metric.closedBall y (2 * r)) := by
    intro z hz
    have h : dist z x ≤ r := hz
    have h2 : dist (dTubeToDyadicTube z) y ≤ 2 * dist z x := dist_dyadic_le_two_dtube z x
    have h3 : dist (dTubeToDyadicTube z) y ≤ 2 * r := by linarith
    exact h3
  have hsub : A ∩ Metric.closedBall x r ⊆ A ∩ dTubeToDyadicTube ⁻¹' (Metric.closedBall y (2 * r)) := by
    intro z hz
    exact ⟨hz.1, hball1 hz.2⟩
  let S := A ∩ dTubeToDyadicTube ⁻¹' (Metric.closedBall y (2 * r))
  have himg : dTubeToDyadicTube '' S = T ∩ Metric.closedBall y (2 * r) := by
    ext z
    simp only [Set.mem_image, Set.mem_inter_iff, A]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨hw.1, hw.2⟩
    · rintro ⟨h1, h2⟩
      have h_rt : dTubeToDyadicTube (dyadicTubeToDTube z) = z := roundtrip_dyadic z
      exact ⟨dyadicTubeToDTube z, ⟨h1, h2⟩, h_rt⟩
  have h41 : Metric.externalCoveringNumber δnn (A ∩ Metric.closedBall x r) ≤
      Metric.externalCoveringNumber δnn S :=
    Metric.externalCoveringNumber_mono_set (ε := δnn) hsub
  have h4 : (Metric.externalCoveringNumber δnn (A ∩ Metric.closedBall x r) : ENNReal) ≤
      (Metric.externalCoveringNumber δnn S : ENNReal) := by exact ENat.toENNReal_le.mpr h41
  have h51 : Metric.externalCoveringNumber δnn S ≤
      Metric.externalCoveringNumber δnn (dTubeToDyadicTube '' S) :=
    covering_dtube_le_dyadic S
  have h5 : (Metric.externalCoveringNumber δnn S : ENNReal) ≤
      (Metric.externalCoveringNumber δnn (dTubeToDyadicTube '' S) : ENNReal) := by
    exact ENat.toENNReal_le.mpr h51
  have h6 : (Metric.externalCoveringNumber δnn (dTubeToDyadicTube '' S) : ENNReal) =
      (Metric.externalCoveringNumber δnn (T ∩ Metric.closedBall y (2 * r)) : ENNReal) := by
    rw [himg]
  have h7 : (Metric.externalCoveringNumber δnn (T ∩ Metric.closedBall y (2 * r)) : ENNReal) ≤
      ENNReal.ofReal C * (ENNReal.ofReal (2 * r)) ^ s *
        (Metric.externalCoveringNumber δnn T : ENNReal) :=
    h.2.2.2.2 y (2 * r) (by linarith)
  have h_imgT : dTubeToDyadicTube '' A = T := by
    ext z
    simp only [A, Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hw
    · intro hz
      exact ⟨dyadicTubeToDTube z, hz, roundtrip_dyadic z⟩
  set c := Metric.externalCoveringNumber δnn T with hc
  set d := 13 * Metric.externalCoveringNumber δnn A with hd
  have h81 : c ≤ d := by
    have h := covering_dyadic_le_13 A
    rw [h_imgT] at h
    exact h
  have h8 : (c : ENNReal) ≤ (13 : ENNReal) * (Metric.externalCoveringNumber δnn A : ENNReal) := by
    have h83 : (c : ENNReal) ≤ (d : ENNReal) := by exact ENat.toENNReal_le.mpr h81
    have h84 : (d : ENNReal) = (13 : ENNReal) * (Metric.externalCoveringNumber δnn A : ENNReal) := by
      simp [hd] <;> norm_cast
    rw [h84] at h83
    exact h83
  have h9 : ENNReal.ofReal (2 * r) = (2 : ENNReal) * ENNReal.ofReal r := by
    have h10 : (2 * r : ℝ) = 2 * r := by ring
    rw [h10, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    <;> norm_cast
  have h11 : ((2 : ENNReal) * ENNReal.ofReal r) ^ s =
      (2 : ENNReal) ^ s * (ENNReal.ofReal r) ^ s := by
    have h12 : 0 ≤ s := hs
    have h13 : (2 : ENNReal) ≠ 0 := by norm_num
    have h14 : ENNReal.ofReal r ≠ 0 := by
      simp [hδ_pos.ne', hr]
      <;> linarith
    simpa [h12, h13, h14] using ENNReal.mul_rpow_eq_ite (2 : ENNReal) (ENNReal.ofReal r) s
  calc (Metric.externalCoveringNumber δnn (A ∩ Metric.closedBall x r) : ENNReal)
      ≤ (Metric.externalCoveringNumber δnn S : ENNReal) := h4
    _ ≤ (Metric.externalCoveringNumber δnn (dTubeToDyadicTube '' S) : ENNReal) := h5
    _ = (Metric.externalCoveringNumber δnn (T ∩ Metric.closedBall y (2 * r)) : ENNReal) := h6
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal (2 * r)) ^ s *
          (Metric.externalCoveringNumber δnn T : ENNReal) := h7
    _ = ENNReal.ofReal C * ((2 : ENNReal) * ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber δnn T : ENNReal) := by rw [h9]
    _ = ENNReal.ofReal C * ((2 : ENNReal) ^ s * (ENNReal.ofReal r) ^ s) *
          (Metric.externalCoveringNumber δnn T : ENNReal) := by rw [h11]
    _ = ENNReal.ofReal C * (2 : ENNReal) ^ s * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber δnn T : ENNReal) := by ring_nf
    _ ≤ ENNReal.ofReal C * (2 : ENNReal) ^ s * (ENNReal.ofReal r) ^ s *
          (13 * (Metric.externalCoveringNumber δnn A : ENNReal)) := by gcongr
    _ = ENNReal.ofReal (13 * C * 2 ^ s) * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber δnn A : ENNReal) := by
      have h_eq : ENNReal.ofReal C * (2 : ENNReal) ^ s * (ENNReal.ofReal r) ^ s *
            ((13 : ENNReal) * (Metric.externalCoveringNumber δnn A : ENNReal)) =
          ENNReal.ofReal (13 * C * 2 ^ s) * (ENNReal.ofReal r) ^ s *
            (Metric.externalCoveringNumber δnn A : ENNReal) := by
        have h1 : ENNReal.ofReal (13 * C * 2 ^ s) =
            (13 : ENNReal) * (2 : ENNReal) ^ s * ENNReal.ofReal C := by
          have h2 : ENNReal.ofReal (13 * C * 2 ^ s) =
              ENNReal.ofReal ((13 * 2 ^ s) * C) := by ring_nf
          rw [h2, ENNReal.ofReal_mul (by positivity)]
          have h31 : ENNReal.ofReal (2 ^ s) = (2 : ENNReal) ^ s := by
            have h32 := ENNReal.ofReal_rpow_of_nonneg (x := (2 : ℝ)) (p := s) (by norm_num) hs
            simpa using h32.symm
          have h3 : ENNReal.ofReal (13 * 2 ^ s) = (13 : ENNReal) * (2 : ENNReal) ^ s := by
            rw [ENNReal.ofReal_mul (by positivity), h31] <;> norm_cast
          rw [h3] <;> ring
        rw [h1]
        <;> simp [mul_assoc, mul_comm, mul_left_comm] <;> ring_nf
      exact h_eq

/-!
  # Finset conversion helpers
-/

/-- Convert a finset of DyadicSquares to DSquares. -/
def finsetDyadicToDSquare (P : Finset (DyadicSquare n)) : Finset (DSquare n) :=
  P.image dyadicSquareToDSquare

/-- Convert a finset of DyadicTubes to DTubes. -/
def finsetDyadicToDTube (T : Finset (DyadicTube n)) : Finset (DTube n) :=
  T.image dyadicTubeToDTube

lemma card_dyadicToDSquare (P : Finset (DyadicSquare n)) :
    (finsetDyadicToDSquare P).card = P.card := by
  apply Finset.card_image_of_injective
  intro p q h
  have h' : dyadicSquareToDSquare p = dyadicSquareToDSquare q := h
  have hi : p.i = q.i := by
    simpa [dyadicSquareToDSquare] using congr_arg DSquare.i h'
  have hj : p.j = q.j := by
    simpa [dyadicSquareToDSquare] using congr_arg DSquare.j h'
  cases p; cases q
  congr <;> tauto

lemma card_dyadicToDTube (T : Finset (DyadicTube n)) :
    (finsetDyadicToDTube T).card = T.card := by
  apply Finset.card_image_of_injective
  intro T1 T2 h
  have h' : dyadicTubeToDTube T1 = dyadicTubeToDTube T2 := h
  have ha : T1.a = T2.a := by
    simpa [dyadicTubeToDTube] using congr_arg DTube.a h'
  have hb : T1.b = T2.b := by
    simpa [dyadicTubeToDTube] using congr_arg DTube.b h'
  cases T1; cases T2
  congr <;> tauto

end DiscretisedFurstenbergEstimate.DyadicConversion
