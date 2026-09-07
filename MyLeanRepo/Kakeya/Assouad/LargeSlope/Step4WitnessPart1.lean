import MyLeanRepo.Kakeya.Assouad.Statements
import MyLeanRepo.Kakeya.Assouad.LargeSlope.SlabPerTubeMassPruning
import MyLeanRepo.Kakeya.Assouad.MultiplicityRefinement

/-!
# Step 4 witness — Part 1: parameter selection, rho, and fine subshading

This module extracts the first portion of the Step 4 witness:

* `rho := 64 * (b - a)^2` with all required inequalities;
* the slab-local per-tube-full subshading `fine` obtained by intersecting with
  `horizontalSlab a b` and applying `slab_per_tube_mass_pruning`;
* the quantitative lower bound on the remaining fine mass.

The prism/piece geometry and local AD data are constructed in later parts.
-/

namespace Kakeya.Assouad

/-- Multiply two `realRpowENN` with same positive base. -/
lemma step4_realRpowENN_mul_same {x : ℝ} (hx : 0 < x) (a b : ℝ) :
    Kakeya.realRpowENN x a * Kakeya.realRpowENN x b =
    Kakeya.realRpowENN x (a + b) := by
  simp only [Kakeya.realRpowENN]
  have h_pos : 0 ≤ Real.rpow x a := Real.rpow_nonneg hx.le _
  have h1 : ENNReal.ofReal (Real.rpow x a) * ENNReal.ofReal (Real.rpow x b) =
      ENNReal.ofReal (Real.rpow x a * Real.rpow x b) := by
    rw [← ENNReal.ofReal_mul h_pos]
  rw [h1]
  have h2 : Real.rpow x a * Real.rpow x b = Real.rpow x (a + b) :=
    (Real.rpow_add hx a b).symm
  rw [h2]

/-- Real power of a real power: `(x^a)^b = x^(a*b)` for `x > 0`. -/
lemma step4_real_rpow_rpow {x : ℝ} (hx : 0 < x) (a b : ℝ) :
    Real.rpow (Real.rpow x a) b = Real.rpow x (a * b) := by
  have hpos1 : 0 < Real.rpow x a := Real.rpow_pos_of_pos hx a
  have h1 : Real.log (Real.rpow (Real.rpow x a) b) =
      b * Real.log (Real.rpow x a) := Real.log_rpow hpos1 b
  have h2 : Real.log (Real.rpow x a) = a * Real.log x := Real.log_rpow hx a
  have h3 : Real.log (Real.rpow (Real.rpow x a) b) =
      (a * b) * Real.log x := by
    rw [h1, h2] <;> ring
  have h4 : Real.log (Real.rpow x (a * b)) = (a * b) * Real.log x :=
    Real.log_rpow hx (a * b)
  have hpos2 : 0 < Real.rpow (Real.rpow x a) b := Real.rpow_pos_of_pos hpos1 b
  have hpos3 : 0 < Real.rpow x (a * b) := Real.rpow_pos_of_pos hx (a * b)
  have h5 : Real.log (Real.rpow (Real.rpow x a) b) =
      Real.log (Real.rpow x (a * b)) := by rw [h3, h4]
  exact Real.log_injOn_pos (Set.mem_Ioi.mpr hpos2) (Set.mem_Ioi.mpr hpos3) h5

/--
Part 1 of the Step 4 witness: rho properties and the fine slab subshading.

Given the refined data and two explicit smallness hypotheses, construct `rho`
and the per-tube-full subshading `fine`, together with a lower bound on the
remaining slab mass.
-/
lemma large_slope_step4_part1
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C : ENNReal}
    {a b : ℝ}
    (epsilon sigma eta : ℝ)
    {G : C2GrainStructure Y sigma C}
    {refined : LargeSlopeRefinementData U Y sigma eta C G a b}
    (hdelta : 0 < delta)
    (heta_pos : 0 < eta)
    (hba_small : b - a ≤ 1 / 16)
    (hmass_small : 8 * Real.rpow delta (10 * eta - eta / 1000) ≤ 1 / 2) :
    ∃ (rho : ℝ) (fine : Kakeya.Streamlined.TubeShading F),
      rho = 64 * (b - a)^2 ∧
      0 < rho ∧
      delta ≤ rho ∧
      rho ≤ 1 / 4 ∧
      Real.sqrt rho = 8 * (b - a) ∧
      IsSubshading fine refined.shading ∧
      (∀ i, fine.carrier i ⊆ horizontalSlab a b) ∧
      HasPerTubeMassInSlab fine a b
        (ENNReal.ofReal (Real.rpow delta (11 * eta) * delta^2 * Real.sqrt rho)) ∧
      (1 / 2 : ENNReal) * Kakeya.realRpowENN delta eta *
        ENNReal.ofReal (b - a) ≤ shadedMassInSlab fine a b := by
  have hba_pos : 0 < b - a := by
    have h : a < b := refined.ordered
    linarith
  set rho : ℝ := 64 * (b - a)^2 with hrho_def
  have hrho_pos : 0 < rho := by
    dsimp only [rho]
    positivity
  have hdelta_le_rho : delta ≤ rho := by
    have h1 : Kakeya.realRpowENN delta (1 / 2 : ℝ) ≤ ENNReal.ofReal (b - a) :=
      refined.scale_lower
    have h2 : 0 ≤ b - a := by linarith
    have h3 : Real.sqrt delta ≤ b - a := by
      have h4 : ENNReal.ofReal (Real.sqrt delta) ≤ ENNReal.ofReal (b - a) := by
        simpa [Kakeya.realRpowENN, Real.sqrt_eq_rpow] using h1
      exact (ENNReal.ofReal_le_ofReal_iff h2).mp h4
    have h5 : delta ≤ (b - a)^2 := by
      calc delta
        = (Real.sqrt delta)^2 := by rw [Real.sq_sqrt (by linarith)]
      _ ≤ (b - a)^2 := by gcongr <;> linarith
    dsimp only [rho]
    nlinarith
  have hrho_le_quarter : rho ≤ 1 / 4 := by
    dsimp only [rho]
    nlinarith
  have hsqrt_rho : Real.sqrt rho = 8 * (b - a) := by
    dsimp only [rho]
    have h64 : Real.sqrt (64 : ℝ) = 8 := by
      rw [show (64 : ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
      norm_num
    have hsquare : Real.sqrt ((b - a)^2) = b - a := by
      rw [Real.sqrt_sq_eq_abs, abs_of_pos hba_pos]
    calc
      Real.sqrt (64 * (b - a)^2) =
          Real.sqrt 64 * Real.sqrt ((b - a)^2) :=
        Real.sqrt_mul (by norm_num) _
      _ = 8 * Real.sqrt ((b - a)^2) :=
        congrArg (fun x : ℝ => x * Real.sqrt ((b - a)^2)) h64
      _ = 8 * (b - a) :=
        congrArg (fun x : ℝ => 8 * x) hsquare
  -- Slab restriction
  let Z_slab : Kakeya.Streamlined.TubeShading F :=
    slabRestriction refined.shading a b
  have hZ_slab_sub : IsSubshading Z_slab refined.shading := by
    intro i
    dsimp only [Z_slab, slabRestriction, IsSubshading]
    intro x hx
    exact hx.1
  have hZ_slab_in_slab : ∀ i, Z_slab.carrier i ⊆ horizontalSlab a b := by
    intro i
    dsimp only [Z_slab, slabRestriction]
    intro x hx
    exact hx.2
  have hmass_Z_slab : shadedMassInSlab Z_slab a b = shadedMassInSlab refined.shading a b := by
    apply Finset.sum_congr rfl
    intro i _
    have h : Z_slab.carrier i ∩ horizontalSlab a b =
        refined.shading.carrier i ∩ horizontalSlab a b := by
      dsimp only [Z_slab, slabRestriction]
      ext x
      simp
      <;> tauto
    rw [h]
  -- Threshold
  let threshold : ENNReal :=
    ENNReal.ofReal (Real.rpow delta (11 * eta) * delta^2 * Real.sqrt rho)
  have hthreshold_eq : threshold =
      Kakeya.realRpowENN delta (11 * eta + 2) * ENNReal.ofReal (8 * (b - a)) := by
    dsimp only [threshold]
    rw [hsqrt_rho]
    have h21 : delta^2 = Real.rpow delta 2 := by
      have h22 : 0 ≤ delta := by linarith
      rw [← Real.rpow_natCast] <;> norm_num
    have h1 : Real.rpow delta (11 * eta) * delta^2 * (8 * (b - a)) =
        Real.rpow delta (11 * eta + 2) * (8 * (b - a)) := by
      rw [h21]
      have h3 : Real.rpow delta (11 * eta) * Real.rpow delta 2 =
          Real.rpow delta (11 * eta + 2) := by
        have h31 : (delta ^ (11 * eta + 2 : ℝ)) =
            (delta ^ (11 * eta : ℝ)) * (delta ^ (2 : ℝ)) :=
          Real.rpow_add hdelta (11 * eta) 2
        exact h31.symm
      rw [h3] <;> ring
    rw [h1]
    have h4 : 0 ≤ Real.rpow delta (11 * eta + 2) := Real.rpow_nonneg hdelta.le _
    rw [ENNReal.ofReal_mul h4] <;> rfl
  -- Apply pruning
  rcases slab_per_tube_mass_pruning F Z_slab a b threshold with
    ⟨fine, hfine_sub_Z, hmass_ineq, hper_tube⟩
  have hfine_sub : IsSubshading fine refined.shading := by
    intro i
    have h : fine.carrier i ⊆ Z_slab.carrier i := hfine_sub_Z i
    exact h.trans (hZ_slab_sub i)
  have hfine_in_slab : ∀ i, fine.carrier i ⊆ horizontalSlab a b := by
    intro i
    have h : fine.carrier i ⊆ Z_slab.carrier i := hfine_sub_Z i
    exact h.trans (hZ_slab_in_slab i)
  -- Discarded mass bound
  have hcard : F.enncard ≤ Kakeya.realRpowENN delta (-2 - eta / 1000) := by
    exact refined.cardinality_upper
  have hdiscarded_le : threshold * F.enncard ≤
      Kakeya.realRpowENN delta (11 * eta - eta / 1000) *
      ENNReal.ofReal (8 * (b - a)) := by
    have h1 : threshold * F.enncard =
        Kakeya.realRpowENN delta (11 * eta + 2) *
        ENNReal.ofReal (8 * (b - a)) * F.enncard := by
      rw [hthreshold_eq] <;> ring
    rw [h1]
    have h2 : Kakeya.realRpowENN delta (11 * eta + 2) * F.enncard ≤
        Kakeya.realRpowENN delta (11 * eta + 2) *
        Kakeya.realRpowENN delta (-2 - eta / 1000) := by gcongr
    have h3 : Kakeya.realRpowENN delta (11 * eta + 2) *
        Kakeya.realRpowENN delta (-2 - eta / 1000) =
        Kakeya.realRpowENN delta (11 * eta - eta / 1000) := by
      have h31 := step4_realRpowENN_mul_same hdelta (11 * eta + 2) (-2 - eta / 1000)
      have h32 : (11 * eta + 2) + (-2 - eta / 1000) = 11 * eta - eta / 1000 := by ring
      rw [h32] at h31
      exact h31
    calc
      Kakeya.realRpowENN delta (11 * eta + 2) *
          ENNReal.ofReal (8 * (b - a)) * F.enncard
        = Kakeya.realRpowENN delta (11 * eta + 2) * F.enncard *
            ENNReal.ofReal (8 * (b - a)) := by ring
      _ ≤ Kakeya.realRpowENN delta (11 * eta + 2) *
            Kakeya.realRpowENN delta (-2 - eta / 1000) *
            ENNReal.ofReal (8 * (b - a)) := by gcongr
      _ = Kakeya.realRpowENN delta (11 * eta - eta / 1000) *
            ENNReal.ofReal (8 * (b - a)) := by rw [h3] <;> ring
  let alpha : ℝ := 10 * eta - eta / 1000
  have halpha_pos : 0 < alpha := by
    dsimp only [alpha]
    linarith [heta_pos]
  have halpha_mass : 8 * Real.rpow delta alpha ≤ 1 / 2 := hmass_small
  let half : ENNReal := ENNReal.ofReal (1 / 2 : ℝ)
  have hdiscarded_half : threshold * F.enncard ≤
      half * Kakeya.realRpowENN delta eta * ENNReal.ofReal (b - a) := by
    have h4 : 11 * eta - eta / 1000 = eta + alpha := by
      dsimp only [alpha] <;> ring
    have h5 : Kakeya.realRpowENN delta (11 * eta - eta / 1000) *
        ENNReal.ofReal (8 * (b - a)) ≤
        half * Kakeya.realRpowENN delta eta * ENNReal.ofReal (b - a) := by
      rw [h4]
      have h6 : Kakeya.realRpowENN delta (eta + alpha) =
          Kakeya.realRpowENN delta eta * Kakeya.realRpowENN delta alpha := by
        exact (step4_realRpowENN_mul_same hdelta _ _).symm
      rw [h6]
      have h7 : ENNReal.ofReal (8 * (b - a)) =
          (8 : ENNReal) * ENNReal.ofReal (b - a) := by
        simp [ENNReal.ofReal_mul] <;> ring
      rw [h7]
      have h8 : Real.rpow delta alpha * 8 ≤ 1 / 2 := by
        linarith [halpha_mass]
      have h9 : Kakeya.realRpowENN delta alpha * (8 : ENNReal) ≤ half := by
        have h101 : (8 : ENNReal) = ENNReal.ofReal 8 := by simp
        have h102 : Kakeya.realRpowENN delta alpha =
            ENNReal.ofReal (Real.rpow delta alpha) := by rfl
        have h10 : Kakeya.realRpowENN delta alpha * (8 : ENNReal) =
            ENNReal.ofReal (Real.rpow delta alpha * 8) := by
          rw [h101, h102]
          have h103 : 0 ≤ Real.rpow delta alpha := Real.rpow_nonneg hdelta.le _
          rw [← ENNReal.ofReal_mul h103] <;> rfl
        rw [h10]
        dsimp only [half]
        exact ENNReal.ofReal_le_ofReal h8
      calc
        (Kakeya.realRpowENN delta eta * Kakeya.realRpowENN delta alpha) *
            ((8 : ENNReal) * ENNReal.ofReal (b - a))
          = Kakeya.realRpowENN delta eta *
              (Kakeya.realRpowENN delta alpha * (8 : ENNReal)) *
              ENNReal.ofReal (b - a) := by ring
        _ ≤ Kakeya.realRpowENN delta eta * half *
              ENNReal.ofReal (b - a) := by gcongr
        _ = half * Kakeya.realRpowENN delta eta *
              ENNReal.ofReal (b - a) := by ring
    exact hdiscarded_le.trans h5
  -- Fine mass lower bound
  have h_orig_mass : Kakeya.realRpowENN delta eta * ENNReal.ofReal (b - a) ≤
      shadedMassInSlab refined.shading a b := by
    exact refined.slab_mass
  rw [hmass_Z_slab] at hmass_ineq
  let X := Kakeya.realRpowENN delta eta * ENNReal.ofReal (b - a)
  have hX_ne_top : X ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · exact ENNReal.ofReal_ne_top
    · exact ENNReal.ofReal_ne_top
  have h10 : X ≤ shadedMassInSlab fine a b + threshold * F.enncard :=
    h_orig_mass.trans hmass_ineq
  have hdiscarded_half' : threshold * F.enncard ≤ half * X := by
    have h_eq : half * Kakeya.realRpowENN delta eta * ENNReal.ofReal (b - a) =
        half * X := by
      dsimp only [X]
      exact mul_assoc half (Kakeya.realRpowENN delta eta) (ENNReal.ofReal (b - a))
    rw [h_eq] at hdiscarded_half
    exact hdiscarded_half
  have h11 : X ≤ shadedMassInSlab fine a b + half * X := by
    have h111 : shadedMassInSlab fine a b + threshold * F.enncard ≤
        shadedMassInSlab fine a b + half * X :=
      add_le_add_right hdiscarded_half' (shadedMassInSlab fine a b)
    exact h10.trans h111
  have h12 : X = half * X + half * X := by
    have h13 : half + half = 1 := by
      have h14 : half + half = ENNReal.ofReal ((1 / 2 : ℝ) + (1 / 2 : ℝ)) := by
        rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)] <;> rfl
      rw [h14] <;> norm_num
    calc X
      = 1 * X := by simp
    _ = (half + half) * X := by rw [h13]
    _ = half * X + half * X := by rw [add_mul]
  have h11' : half * X + half * X ≤ shadedMassInSlab fine a b + half * X := by
    calc half * X + half * X
      = X := h12.symm
    _ ≤ shadedMassInSlab fine a b + half * X := h11
  have h14 : half * X ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hX_ne_top
  have hfine_mass_lower' : ENNReal.ofReal (1 / 2 : ℝ) * X ≤ shadedMassInSlab fine a b :=
    (ENNReal.add_le_add_iff_right h14).mp h11'
  have h_eq : (1 / 2 : ENNReal) * Kakeya.realRpowENN delta eta *
      ENNReal.ofReal (b - a) = ENNReal.ofReal (1 / 2 : ℝ) * X := by
    dsimp only [X]
    have h_conv : (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2 : ℝ) := by
      simp [div_eq_mul_inv] <;> norm_cast
    rw [h_conv, mul_assoc]
  have hfine_mass_lower : (1 / 2 : ENNReal) * Kakeya.realRpowENN delta eta *
      ENNReal.ofReal (b - a) ≤ shadedMassInSlab fine a b := by
    rw [h_eq]
    exact hfine_mass_lower'
  exact ⟨rho, fine, hrho_def, hrho_pos, hdelta_le_rho, hrho_le_quarter,
    hsqrt_rho, hfine_sub, hfine_in_slab, hper_tube, hfine_mass_lower⟩

end Kakeya.Assouad
