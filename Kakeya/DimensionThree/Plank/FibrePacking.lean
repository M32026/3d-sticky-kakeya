/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.SlabAssignment
public import Kakeya.DimensionThree.Plank.ThickenedGeometry

/-!
# Polynomial packing for the thickened-representative fibre

The fibre `repr⁻¹(repr i) ∩ s` of a `Plank.ThickenedRepr` consists of pairwise essentially
distinct `a × b × 1` planks all confined to one `cThk·(θb × b × 1)` prism. Reading each plank's
pose (frame plus centre) in the reference frame of one fibre member turns that into a metric
packing problem in the 12-dimensional pose space, which `Plank.card_le_of_pose_confined_separated`
solves. The output is the crude polynomial bound `phi i ≤ Cpack · a^(-12)`.
-/

@[expose] public section

open MeasureTheory Convexity
open scoped NNReal Real ENNReal

noncomputable section

namespace Plank

variable {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {ι : Type*}

/-! ## Frame comparison through a reference frame

The two lemmas below convert *pairwise* data between two planks into data measured in a single
reference frame `f`, which is what a one-pose packing argument needs. -/

/-- **Off-diagonal frame comparison through a reference frame.** For `p ≠ k` the inner product
`⟪e p, e' k⟫` vanishes when `e' = e` (orthonormality), so it is controlled by the reference-frame
coordinate differences of the two frames along the row `k`. -/
private lemma abs_inner_offdiag_le_sum_frame_diff
    (f e e' : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))) {p k : Fin 3} (hpk : p ≠ k) :
    |inner ℝ (e p) (e' k)|
      ≤ ∑ m : Fin 3, |inner ℝ (e' k) (f m) - inner ℝ (e k) (f m)| := by
  have hunit : ∀ m : Fin 3, |inner ℝ (e p) (f m)| ≤ 1 := by
    intro m
    have h := abs_real_inner_le_norm (e p) (f m)
    rwa [e.norm_eq_one p, f.norm_eq_one m, mul_one] at h
  have hcomm : ∀ (u : EuclideanSpace ℝ (Fin 3)) (m : Fin 3),
      (inner ℝ u (f m) : ℝ) = inner ℝ (f m) u := fun u m => real_inner_comm (f m) u
  have hexp : (inner ℝ (e p) (e' k) : ℝ)
      = ∑ m : Fin 3, (inner ℝ (e' k) (f m) - inner ℝ (e k) (f m)) * inner ℝ (e p) (f m) := by
    simp only [sub_mul, Finset.sum_sub_distrib, hcomm (e' k), hcomm (e k)]
    rw [← inner_eq_sum_frame f (e p) (e' k), ← inner_eq_sum_frame f (e p) (e k),
      e.inner_eq_zero hpk, sub_zero]
  rw [hexp]
  calc |∑ m : Fin 3, (inner ℝ (e' k) (f m) - inner ℝ (e k) (f m)) * inner ℝ (e p) (f m)|
      ≤ ∑ m : Fin 3, |(inner ℝ (e' k) (f m) - inner ℝ (e k) (f m)) * inner ℝ (e p) (f m)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m : Fin 3, |inner ℝ (e' k) (f m) - inner ℝ (e k) (f m)| := by
        refine Finset.sum_le_sum fun m _ => ?_
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (hunit m)

/-- **Centre-offset comparison through a reference frame.** A unit frame coordinate of a vector is
bounded by the sum of its reference-frame coordinates (termwise Cauchy-Schwarz, losing only the
absolute factor `3`). -/
private lemma abs_inner_center_le_sum_frame
    (f e' : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))) (k : Fin 3)
    (d : EuclideanSpace ℝ (Fin 3)) :
    |inner ℝ (e' k) d| ≤ ∑ m : Fin 3, |inner ℝ (f m) d| := by
  have hunit : ∀ m : Fin 3, |inner ℝ (e' k) (f m)| ≤ 1 := by
    intro m
    have h := abs_real_inner_le_norm (e' k) (f m)
    rwa [e'.norm_eq_one k, f.norm_eq_one m, mul_one] at h
  rw [inner_eq_sum_frame f (e' k) d]
  calc |∑ m : Fin 3, inner ℝ (f m) d * inner ℝ (e' k) (f m)|
      ≤ ∑ m : Fin 3, |inner ℝ (f m) d * inner ℝ (e' k) (f m)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m : Fin 3, |inner ℝ (f m) d| := by
        refine Finset.sum_le_sum fun m _ => ?_
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (hunit m)

/-- Every plank half-width is at most `1`. -/
private lemma plank_width_le_one {a b : ℝ≥0} (hab : a ≤ b) (hb1 : b ≤ 1) (p : Fin 3) :
    ((![a, b, 1] p : ℝ≥0) : ℝ) ≤ 1 := by
  have ha1 : a ≤ 1 := hab.trans hb1
  fin_cases p <;> simp [ha1, hb1]

/-- Every plank half-width is at least the shortest one, `a`. -/
private lemma plank_width_ge {a b : ℝ≥0} (hab : a ≤ b) (hb1 : b ≤ 1) (k : Fin 3) :
    (a : ℝ) ≤ ((![a, b, 1] k : ℝ≥0) : ℝ) := by
  have ha1 : a ≤ 1 := hab.trans hb1
  fin_cases k <;> simp [hab, ha1]

/-- Every thickened-plank half-width is at most `1`. -/
private lemma thickened_width_le_one {b θ : ℝ≥0} (hb1 : b ≤ 1) (hθ1 : θ ≤ 1) (k : Fin 3) :
    ((![θ * b, b, 1] k : ℝ≥0) : ℝ) ≤ 1 := by
  have h : (![θ * b, b, 1] k : ℝ≥0) ≤ 1 := by
    fin_cases k
    · simpa using mul_le_one' hθ1 hb1
    · simpa using hb1
    · simp
  exact_mod_cast h

/-- A prism contains its own centre. -/
private lemma center_mem_carrier {n : ℕ}
    (P : PrismNDim n (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3))) :
    P.center ∈ (P.carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
  rw [P.mem_carrier_iff]
  intro k
  simp

/-! ## The packing bound -/

open Classical in
/-- **Crude polynomial packing bound for the thickened-representative fibre**
(`lem:thickenedReprPhiPackingBound`).

For a `ThickenedRepr` with comparability constant `cThk ≥ 1` whose planks are pairwise essentially
distinct, the fibre size `phi i = |repr⁻¹(repr i) ∩ s|` obeys `phi i ≤ Cpack · a^(-12)` with
`Cpack = (2306 · cThk)^12`, uniformly in the configuration.

*Which form this is.* This is the `a^(-D)` fallback, not the sharp `(θb/a)^D`. The whole fibre is
confined to one `cThk·(θb × b × 1)` prism, so the plank centres are within `6·cThk` of each other;
but the *separation* input `plank_not_essentiallyDistinct_of_pose_close` only gives control at the
plank's **shortest** half-width `a` in every coordinate direction, so each of the twelve pose
coordinates is normalised by a multiple of `1/a`, and the confinement radius `K` is `O(cThk/a)`
rather than `O(θb/a)`. Recovering the sharp exponent would need an anisotropic separation statement;
the blueprint note on `lem:thickenedReprPhiPackingBound` records that the sharp bound does not
follow from pairwise essential distinctness alone. Since `θ ≤ 1` and `b ≤ 1` give `θb/a ≤ 1/a`, the
sharp form would imply this one, and this form is what the logarithmic consumer needs. -/
theorem ThickenedRepr.phi_packing_bound (cThk : ℝ≥0) (hcThk : 1 ≤ cThk) :
    ∃ (Cpack : ℝ≥0) (D : ℕ), 0 < Cpack ∧
      ∀ {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {ι : Type*}
        (s : Finset ι) (V : ι → Plank a b hab hb1) (θ : ℝ≥0) (hθ1 : θ ≤ 1)
        (R : ThickenedRepr s V θ hθ1 cThk),
        0 < a →
        (∀ i ∈ s, ∀ j ∈ s, i ≠ j →
          PrismNDim.IsEssentiallyDistinct (V i).toPrismNDim (V j).toPrismNDim) →
        ∀ i ∈ s, (R.phi i : ℝ≥0) ≤ Cpack * a ^ (-(D : ℝ)) := by
  classical
  have hcThkpos : (0 : ℝ≥0) < cThk := lt_of_lt_of_le zero_lt_one hcThk
  have hcThk0 : (0 : ℝ) < (cThk : ℝ) := by exact_mod_cast hcThkpos
  have hcThk1 : (1 : ℝ) ≤ (cThk : ℝ) := by exact_mod_cast hcThk
  refine ⟨(2306 * cThk) ^ 12, 12, pow_pos (by positivity) 12, ?_⟩
  intro a b hab hb1 ι s V θ hθ1 R ha0 hED i hi
  have ha0' : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha0
  have hane : (a : ℝ) ≠ 0 := ne_of_gt ha0'
  have hb0 : 0 < b := lt_of_lt_of_le ha0 hab
  have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  have hb1' : (b : ℝ) ≤ 1 := by exact_mod_cast hb1
  have ha1' : (a : ℝ) ≤ 1 := hab'.trans hb1'
  set F : Finset ι := s.filter (fun j => R.repr j = R.repr i) with hFdef
  have hphi : R.phi i = F.card := by rw [hFdef]; simp [ThickenedRepr.phi]
  have hiF : i ∈ F := by rw [hFdef]; exact Finset.mem_filter.mpr ⟨hi, rfl⟩
  set f : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)) := (V i).basis with hfdef
  set x₀ : EuclideanSpace ℝ (Fin 3) := (V i).center with hx₀def
  -- CONFINEMENT (geometry): every fibre plank centre is within `3·cThk` of the representative.
  have hQthick : ∀ k : Fin 3,
      ((R.repr i).thicknesses k : ℝ) = ((![θ * b, b, 1] k : ℝ≥0) : ℝ) := by
    intro k
    rw [R.repr_eq i hi]
    rfl
  have hthickle : ∀ k : Fin 3,
      (((R.repr i).dilation cThk).thicknesses k : ℝ) ≤ (cThk : ℝ) := by
    intro k
    have hd : (((R.repr i).dilation cThk).thicknesses k : ℝ)
        = (cThk : ℝ) * ((R.repr i).thicknesses k : ℝ) := by
      rw [PrismNDim.dilation_thicknesses]; push_cast; ring
    rw [hd, hQthick k]
    nlinarith [thickened_width_le_one hb1 hθ1 k,
      NNReal.coe_nonneg ((![θ * b, b, 1] k : ℝ≥0)), hcThk0.le]
  have hsumthick : ∑ k : Fin 3, (((R.repr i).dilation cThk).thicknesses k : ℝ)
      ≤ 3 * (cThk : ℝ) := by
    rw [Fin.sum_univ_three]
    linarith [hthickle 0, hthickle 1, hthickle 2]
  have hcenmem : ∀ j ∈ F, dist ((V j).center) (R.repr i).center ≤ 3 * (cThk : ℝ) := by
    intro j hj
    rw [hFdef, Finset.mem_filter] at hj
    have hsub := R.subset_repr j hj.1
    rw [hj.2] at hsub
    have hmem : (V j).center ∈ (((R.repr i).dilation cThk).carrier :
        Set (EuclideanSpace ℝ (Fin 3))) := hsub (center_mem_carrier (V j).toPrismNDim)
    have hball := ((R.repr i).dilation cThk).carrier_subset_closedBall hmem
    rw [Metric.mem_closedBall, PrismNDim.dilation_center] at hball
    exact hball.trans hsumthick
  have hnormle : ∀ j ∈ F, ‖(V j).center -ᵥ x₀‖ ≤ 6 * (cThk : ℝ) := by
    intro j hj
    have h1 := hcenmem j hj
    have h2 : dist x₀ (R.repr i).center ≤ 3 * (cThk : ℝ) := by
      rw [hx₀def]; exact hcenmem i hiF
    have htri := dist_triangle ((V j).center) ((R.repr i).center) x₀
    rw [dist_comm ((R.repr i).center) x₀] at htri
    have hd : dist ((V j).center) x₀ ≤ 6 * (cThk : ℝ) := by linarith
    rwa [dist_eq_norm_vsub (EuclideanSpace ℝ (Fin 3))] at hd
  -- THE POSE: twelve coordinates, all normalised at the shortest plank scale `a`.
  set α : ℝ := 96 / (a : ℝ) with hαdef
  set β : ℝ := 48 / (a : ℝ) with hβdef
  have hα0 : (0 : ℝ) < α := by rw [hαdef]; positivity
  have hβ0 : (0 : ℝ) < β := by rw [hβdef]; positivity
  set poseFun : ι → ((Fin 3 × Fin 3) ⊕ Fin 3) → ℝ := fun j =>
    Sum.elim (fun pq : Fin 3 × Fin 3 => α * inner ℝ ((V j).basis pq.1) (f pq.2))
      (fun q : Fin 3 => β * inner ℝ (f q) ((V j).center -ᵥ x₀)) with hposeFundef
  set pose : ι → EuclideanSpace ℝ ((Fin 3 × Fin 3) ⊕ Fin 3) :=
    fun j => (WithLp.toLp 2 (poseFun j)) with hposedef
  have hpose_app : ∀ (j : ι) (p : (Fin 3 × Fin 3) ⊕ Fin 3), pose j p = poseFun j p :=
    fun _ _ => rfl
  have hinl : ∀ (j : ι) (p q : Fin 3),
      poseFun j (Sum.inl (p, q)) = α * inner ℝ ((V j).basis p) (f q) := fun _ _ _ => rfl
  have hinr : ∀ (j : ι) (q : Fin 3),
      poseFun j (Sum.inr q) = β * inner ℝ (f q) ((V j).center -ᵥ x₀) := fun _ _ => rfl
  set K : ℝ := 288 * (cThk : ℝ) / (a : ℝ) with hKdef
  have hK0 : (0 : ℝ) ≤ K := by rw [hKdef]; positivity
  have hαK : α ≤ K := by
    have hinv : (0 : ℝ) < ((a : ℝ))⁻¹ := by positivity
    rw [hαdef, hKdef, div_eq_mul_inv, div_eq_mul_inv]
    nlinarith
  have hβK : β * (6 * (cThk : ℝ)) = K := by
    rw [hβdef, hKdef]; field_simp; ring
  -- CONFINEMENT (pose): every coordinate of every fibre pose is bounded by `K = 288·cThk/a`.
  have hconf : ∀ j ∈ F, ∀ p, |pose j p| ≤ K := by
    intro j hj p
    rw [hpose_app]
    rcases p with ⟨p, q⟩ | q
    · rw [hinl, abs_mul, abs_of_pos hα0]
      have h1 : |inner ℝ ((V j).basis p) (f q)| ≤ 1 := by
        have h := abs_real_inner_le_norm ((V j).basis p) (f q)
        rwa [(V j).basis.norm_eq_one p, f.norm_eq_one q, mul_one] at h
      nlinarith [abs_nonneg (inner ℝ ((V j).basis p) (f q))]
    · rw [hinr, abs_mul, abs_of_pos hβ0]
      have h1 : |inner ℝ (f q) ((V j).center -ᵥ x₀)| ≤ 6 * (cThk : ℝ) := by
        calc |inner ℝ (f q) ((V j).center -ᵥ x₀)| ≤ ‖f q‖ * ‖(V j).center -ᵥ x₀‖ :=
              abs_real_inner_le_norm _ _
          _ = ‖(V j).center -ᵥ x₀‖ := by rw [f.norm_eq_one q, one_mul]
          _ ≤ 6 * (cThk : ℝ) := hnormle j hj
      rw [← hβK]
      exact mul_le_mul_of_nonneg_left h1 hβ0.le
  -- SEPARATION: pairwise essentially distinct planks cannot have `1`-close poses.
  have hsep : ∀ j ∈ F, ∀ j' ∈ F, j ≠ j' → ((1 : ℝ≥0) : ℝ) < dist (pose j) (pose j') := by
    intro j hj j' hj' hne
    by_contra hcon0
    have hcon : dist (pose j) (pose j') ≤ ((1 : ℝ≥0) : ℝ) := not_lt.mp hcon0
    have hcoord : ∀ p, |poseFun j p - poseFun j' p| ≤ 1 := by
      intro p
      have h := PiLp.dist_apply_le (pose j) (pose j') p
      rw [Real.dist_eq, hpose_app, hpose_app] at h
      exact h.trans (by simpa using hcon)
    have hfrmdiff : ∀ p q : Fin 3,
        |inner ℝ ((V j).basis p) (f q) - inner ℝ ((V j').basis p) (f q)| ≤ (a : ℝ) / 96 := by
      intro p q
      have h := hcoord (Sum.inl (p, q))
      rw [hinl, hinl, ← mul_sub, abs_mul, abs_of_pos hα0, hαdef, div_mul_eq_mul_div,
        div_le_one ha0'] at h
      linarith
    have hcendiff : ∀ q : Fin 3,
        |inner ℝ (f q) ((V j).center -ᵥ (V j').center)| ≤ (a : ℝ) / 48 := by
      intro q
      have h := hcoord (Sum.inr q)
      rw [hinr, hinr, ← mul_sub, ← inner_sub_right,
        show ((V j).center -ᵥ x₀ : EuclideanSpace ℝ (Fin 3)) - ((V j').center -ᵥ x₀)
          = (V j).center -ᵥ (V j').center from vsub_sub_vsub_cancel_right _ _ _,
        abs_mul, abs_of_pos hβ0, hβdef, div_mul_eq_mul_div, div_le_one ha0'] at h
      linarith
    have hjs : j ∈ s := by
      have h := hj; rw [hFdef, Finset.mem_filter] at h; exact h.1
    have hj's : j' ∈ s := by
      have h := hj'; rw [hFdef, Finset.mem_filter] at h; exact h.1
    refine (plank_not_essentiallyDistinct_of_pose_close ha0 hb0 (V j) (V j') ?_ ?_)
      (hED j hjs j' hj's hne)
    · intro p k hpk
      have h1 : |inner ℝ ((V j).basis p) ((V j').basis k)|
          ≤ ∑ m : Fin 3, |inner ℝ ((V j').basis k) (f m) - inner ℝ ((V j).basis k) (f m)| :=
        abs_inner_offdiag_le_sum_frame_diff f (V j).basis (V j').basis hpk
      rw [Fin.sum_univ_three] at h1
      have e0 := hfrmdiff k 0
      have e1 := hfrmdiff k 1
      have e2 := hfrmdiff k 2
      rw [abs_sub_comm] at e0 e1 e2
      have h2 : |inner ℝ ((V j).basis p) ((V j').basis k)| ≤ (a : ℝ) / 32 := by linarith
      have hwp := plank_width_le_one hab hb1 p
      have hwk := plank_width_ge hab hb1 k
      nlinarith [mul_nonneg (sub_nonneg.mpr hwp)
        (abs_nonneg (inner ℝ ((V j).basis p) ((V j').basis k)))]
    · intro k
      have h1 := abs_inner_center_le_sum_frame f (V j').basis k
        ((V j).center -ᵥ (V j').center)
      rw [Fin.sum_univ_three] at h1
      have e0 := hcendiff 0
      have e1 := hcendiff 1
      have e2 := hcendiff 2
      have hwk := plank_width_ge hab hb1 k
      linarith
  -- PACKING: twelve confined, `1`-separated coordinates.
  have hcard := card_le_of_pose_confined_separated F pose hK0
    (r := 1) (by norm_num) hconf hsep
  have hsimp : (2 * (4 * K + ((1 : ℝ≥0) : ℝ)) / ((1 : ℝ≥0) : ℝ)) = 8 * K + 2 := by
    push_cast; ring
  rw [hsimp] at hcard
  have hcThka : (1 : ℝ) ≤ (cThk : ℝ) / (a : ℝ) := by
    rw [le_div_iff₀ ha0']; linarith
  have hfinal : 8 * K + 2 ≤ 2306 * ((cThk : ℝ) / (a : ℝ)) := by
    rw [hKdef, show 288 * (cThk : ℝ) / (a : ℝ) = 288 * ((cThk : ℝ) / (a : ℝ)) from by ring]
    linarith
  have h8K : (0 : ℝ) ≤ 8 * K + 2 := by linarith
  have hpow : (8 * K + 2) ^ 12 ≤ (2306 * ((cThk : ℝ) / (a : ℝ))) ^ 12 :=
    pow_le_pow_left₀ h8K hfinal 12
  rw [show ((a : ℝ≥0) ^ (-((12 : ℕ) : ℝ)) : ℝ≥0) = (a ^ (12 : ℕ))⁻¹ from by
    rw [NNReal.rpow_neg, NNReal.rpow_natCast], ← NNReal.coe_le_coe]
  push_cast
  rw [hphi]
  calc (F.card : ℝ) ≤ (8 * K + 2) ^ 12 := hcard
    _ ≤ (2306 * ((cThk : ℝ) / (a : ℝ))) ^ 12 := hpow
    _ = (2306 * (cThk : ℝ)) ^ 12 * ((a : ℝ) ^ 12)⁻¹ := by field_simp

/-! ## The logarithmic consequence

A polynomial bound `K ≤ Cpack · a^(-D)` costs only `log(1/a)` in a dyadic pigeonhole, and
`log(1/a) = O_η(a^(-η))` for every `η > 0`. So the pigeonhole loss `(log₂ K + 1)⁻¹` stays above
`cη · a^η` with `cη` independent of the configuration. -/

/-- **Logarithmic consequence of a polynomial packing bound.** For every `η > 0` there is a
uniform `cη > 0` such that any `K` obeying `K ≤ Cpack · a^(-D)` (with `0 < a ≤ 1`) satisfies
`cη · a^η ≤ (log₂ K + 1)⁻¹`. The constant is
`cη = (log Cpack' / log 2 + D / (η log 2) + 1)⁻¹` with `Cpack' = max Cpack 1`. -/
theorem exists_log_loss_lower_bound {η : ℝ} (hη : 0 < η) (Cpack : ℝ≥0) (D : ℕ) :
    ∃ cη : ℝ≥0, 0 < cη ∧ ∀ a : ℝ≥0, 0 < a → a ≤ 1 → ∀ K : ℕ,
      (K : ℝ≥0) ≤ Cpack * a ^ (-(D : ℝ)) →
        cη * a ^ η ≤ ((Nat.log 2 K : ℝ≥0) + 1)⁻¹ := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set C1 : ℝ := max (Cpack : ℝ) 1 with hC1def
  have hC1 : (1 : ℝ) ≤ C1 := le_max_right _ _
  have hC1pos : (0 : ℝ) < C1 := lt_of_lt_of_le one_pos hC1
  have hlogC1 : (0 : ℝ) ≤ Real.log C1 := Real.log_nonneg hC1
  set C : ℝ := Real.log C1 / Real.log 2 + (D : ℝ) / (η * Real.log 2) + 1 with hCdef
  have hA : (0 : ℝ) ≤ Real.log C1 / Real.log 2 := div_nonneg hlogC1 hlog2.le
  have hB : (0 : ℝ) ≤ (D : ℝ) / (η * Real.log 2) := by positivity
  have hCge1 : (1 : ℝ) ≤ C := by rw [hCdef]; linarith
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le one_pos hCge1
  have hCinv : (0 : ℝ) < C⁻¹ := inv_pos.mpr hCpos
  refine ⟨Real.toNNReal C⁻¹, Real.toNNReal_pos.mpr hCinv, ?_⟩
  intro a ha0 ha1 K hK
  have ha0' : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha0
  have hane : (a : ℝ) ≠ 0 := ne_of_gt ha0'
  have ha1' : (a : ℝ) ≤ 1 := by exact_mod_cast ha1
  have hxpos : (0 : ℝ) < ((a : ℝ))⁻¹ := inv_pos.mpr ha0'
  have hx1 : (1 : ℝ) ≤ ((a : ℝ))⁻¹ := by
    have h := mul_le_mul_of_nonneg_left ha1' hxpos.le
    rwa [mul_one, inv_mul_cancel₀ hane] at h
  have hxη1 : (1 : ℝ) ≤ ((a : ℝ))⁻¹ ^ η := by
    have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hx1 hη.le
    rwa [Real.one_rpow] at h
  have haη1 : (a : ℝ) ^ η ≤ 1 := Real.rpow_le_one ha0'.le ha1' hη.le
  -- The key real estimate: `(log₂ K + 1) · a^η ≤ C`.
  have hkey : ((Nat.log 2 K : ℝ) + 1) * (a : ℝ) ^ η ≤ C := by
    rcases Nat.eq_zero_or_pos K with hK0 | hKpos
    · rw [hK0]
      simp only [Nat.log_zero_right, Nat.cast_zero, zero_add, one_mul]
      linarith
    · have hnat : 2 ^ Nat.log 2 K ≤ K := Nat.pow_log_le_self 2 hKpos.ne'
      have h2L : ((2 : ℝ) ^ Nat.log 2 K) ≤ (K : ℝ) := by exact_mod_cast hnat
      have hKreal : (K : ℝ) ≤ C1 * ((a : ℝ))⁻¹ ^ (D : ℝ) := by
        have h' : (K : ℝ) ≤ (Cpack : ℝ) * (a : ℝ) ^ (-(D : ℝ)) := by
          have h := NNReal.coe_le_coe.mpr hK
          rwa [NNReal.coe_mul, NNReal.coe_rpow, NNReal.coe_natCast] at h
        rw [Real.rpow_neg ha0'.le, ← Real.inv_rpow ha0'.le] at h'
        have hpow : (0 : ℝ) ≤ ((a : ℝ))⁻¹ ^ (D : ℝ) := Real.rpow_nonneg hxpos.le _
        nlinarith [le_max_left (Cpack : ℝ) 1]
      have hlogK : (Nat.log 2 K : ℝ) * Real.log 2
          ≤ Real.log C1 + (D : ℝ) * Real.log ((a : ℝ))⁻¹ := by
        have hle : ((2 : ℝ) ^ Nat.log 2 K) ≤ C1 * ((a : ℝ))⁻¹ ^ (D : ℝ) := h2L.trans hKreal
        have hlog := Real.log_le_log (by positivity) hle
        rwa [Real.log_pow, Real.log_mul (ne_of_gt hC1pos)
          (ne_of_gt (Real.rpow_pos_of_pos hxpos _)), Real.log_rpow hxpos] at hlog
      have hlogx : Real.log ((a : ℝ))⁻¹ ≤ ((a : ℝ))⁻¹ ^ η / η :=
        Real.log_le_rpow_div hxpos.le hη
      have h1 : (Nat.log 2 K : ℝ) * Real.log 2
          ≤ Real.log C1 + (D : ℝ) * (((a : ℝ))⁻¹ ^ η / η) := by
        refine hlogK.trans ?_
        have h := mul_le_mul_of_nonneg_left hlogx (Nat.cast_nonneg (α := ℝ) D)
        linarith
      have hprodpos : (0 : ℝ) ≤ (Real.log C1 + Real.log 2) * (((a : ℝ))⁻¹ ^ η - 1) :=
        mul_nonneg (by linarith) (by linarith)
      have hMt : ((Nat.log 2 K : ℝ) + 1) * Real.log 2
          ≤ (Real.log C1 + (D : ℝ) / η + Real.log 2) * ((a : ℝ))⁻¹ ^ η := by
        rw [show (Real.log C1 + (D : ℝ) / η + Real.log 2) * ((a : ℝ))⁻¹ ^ η
            = (Real.log C1 + Real.log 2) * (((a : ℝ))⁻¹ ^ η - 1)
              + (Real.log C1 + Real.log 2) + (D : ℝ) * (((a : ℝ))⁻¹ ^ η / η) from by ring]
        linarith
      rw [← le_div_iff₀ hlog2] at hMt
      have hstep : (Nat.log 2 K : ℝ) + 1 ≤ C * ((a : ℝ))⁻¹ ^ η := by
        refine hMt.trans (le_of_eq ?_)
        rw [hCdef]
        field_simp
      have hprod : ((a : ℝ))⁻¹ ^ η * (a : ℝ) ^ η = 1 := by
        rw [← Real.mul_rpow hxpos.le ha0'.le, inv_mul_cancel₀ hane, Real.one_rpow]
      calc ((Nat.log 2 K : ℝ) + 1) * (a : ℝ) ^ η
          ≤ (C * ((a : ℝ))⁻¹ ^ η) * (a : ℝ) ^ η :=
            mul_le_mul_of_nonneg_right hstep (Real.rpow_nonneg ha0'.le η)
        _ = C * (((a : ℝ))⁻¹ ^ η * (a : ℝ) ^ η) := by ring
        _ = C := by rw [hprod, mul_one]
  -- Transfer to `ℝ≥0`.
  have hLpos : (0 : ℝ) < (Nat.log 2 K : ℝ) + 1 := by positivity
  rw [← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_rpow,
    Real.coe_toNNReal _ hCinv.le, NNReal.coe_inv]
  push_cast
  rw [inv_mul_eq_div, div_le_iff₀ hCpos, inv_mul_eq_div, le_div_iff₀ hLpos]
  linarith [hkey]

open Classical in
/-- **The uniform good-refinement constant supplied by fibre packing.** Wiring
`ThickenedRepr.phi_packing_bound` into `ThickenedRepr.pigeonholeThickenedMultiplicity` with the
concrete cap `K = ⌈Cpack · a^(-D)⌉₊` yields the constant-fibre pigeonhole with a retained-mass
constant bounded below by `cη · a^η`, uniformly in the configuration. This is the form the
red-plank-tube assembly needs to keep its final constant uniform. -/
theorem ThickenedRepr.pigeonhole_of_phi_packing (cThk : ℝ≥0) (hcThk : 1 ≤ cThk)
    {η : ℝ} (hη : 0 < η) :
    ∃ cη : ℝ≥0, 0 < cη ∧
      ∀ {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {ι : Type*}
        (s : Finset ι) (V : ι → Plank a b hab hb1) (θ : ℝ≥0) (hθ1 : θ ≤ 1)
        (R : ThickenedRepr s V θ hθ1 cThk)
        (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))),
        0 < a →
        (∀ i ∈ s, ∀ j ∈ s, i ≠ j →
          PrismNDim.IsEssentiallyDistinct (V i).toPrismNDim (V j).toPrismNDim) →
        ∃ (s₂ : Finset ι) (N : ℕ) (cGood cN : ℝ≥0),
          s₂ ⊆ s ∧ 1 ≤ N ∧ 1 ≤ cN ∧ cN ≤ 2 ∧ cη * a ^ η ≤ cGood ∧
          ShadedBody.IsCRefinement s₂ Y s Y cGood ∧
          (∀ Q ∈ R.indexSet, (s₂.filter (fun i => R.repr i = Q)).Nonempty →
            (N : ℝ) / (cN : ℝ) ≤ ((s₂.filter (fun i => R.repr i = Q)).card : ℝ) ∧
              ((s₂.filter (fun i => R.repr i = Q)).card : ℝ) ≤ (cN : ℝ) * (N : ℝ)) := by
  obtain ⟨Cpack, D, -, hbound⟩ := ThickenedRepr.phi_packing_bound cThk hcThk
  obtain ⟨cη, hcη0, hlog⟩ := exists_log_loss_lower_bound hη (2 * Cpack + 1) D
  refine ⟨cη, hcη0, ?_⟩
  intro a b hab hb1 ι s V θ hθ1 R Y ha0 hED
  have ha1 : a ≤ 1 := hab.trans hb1
  have hpow1 : (1 : ℝ≥0) ≤ a ^ (-(D : ℝ)) := by
    have h := NNReal.rpow_le_rpow_of_exponent_ge ha0 ha1 (neg_nonpos.mpr (Nat.cast_nonneg D))
    rwa [NNReal.rpow_zero] at h
  have hK : ∀ i ∈ s, R.phi i ≤ ⌈Cpack * a ^ (-(D : ℝ))⌉₊ := by
    intro i hi
    calc R.phi i = ⌈(R.phi i : ℝ≥0)⌉₊ := (Nat.ceil_natCast _).symm
      _ ≤ _ := Nat.ceil_mono (hbound s V θ hθ1 R ha0 hED i hi)
  obtain ⟨s₂, N, cGood, cN, hsub, hN, hcN, hcN2, hcGood, href, hfib⟩ :=
    R.pigeonholeThickenedMultiplicity Y _ hK
  refine ⟨s₂, N, cGood, cN, hsub, hN, hcN, hcN2, le_trans ?_ hcGood, href, hfib⟩
  refine hlog a ha0 ha1 _ ?_
  have hnn : (0 : ℝ≥0) ≤ Cpack * a ^ (-(D : ℝ)) := by simp
  have hceil : ((⌈Cpack * a ^ (-(D : ℝ))⌉₊ : ℕ) : ℝ≥0) ≤ Cpack * a ^ (-(D : ℝ)) + 1 :=
    (Nat.ceil_lt_add_one hnn).le
  refine hceil.trans ?_
  have h1 : Cpack * a ^ (-(D : ℝ)) ≤ 2 * Cpack * a ^ (-(D : ℝ)) := by
    rw [two_mul, add_mul]
    exact le_add_self
  rw [add_mul, one_mul]
  exact add_le_add h1 hpow1

end Plank

end
