import MyLeanRepo.Kakeya.Assouad.WZ1.GridCellPruning
import MyLeanRepo.Kakeya.Assouad.WZ1.ShadingPruningMass
import MyLeanRepo.Kakeya.Assouad.TubeVolumeLowerBound

/-!
# Grid-pruning budget for WZ1 Lemma 17

The Property-(P) pruning deletes at most

`(ceil (1 / tau) + 1) * 13^3 * rho^(2+2*epsilon) * tau`

from each coarse-tube carrier.  For sufficiently small `rho^epsilon`, this is
at most one tenth of the natural per-tube mass floor `rho^(epsilon+2)`.
-/

namespace Kakeya.Assouad

noncomputable section

open MeasureTheory

private lemma lemma17_realRpowENN_mul
    {x : ℝ} (hx : 0 < x) (a b : ℝ) :
    Kakeya.realRpowENN x a * Kakeya.realRpowENN x b =
      Kakeya.realRpowENN x (a + b) := by
  simp only [Kakeya.realRpowENN]
  have hnonneg : 0 ≤ Real.rpow x a :=
    Real.rpow_nonneg hx.le _
  rw [← ENNReal.ofReal_mul hnonneg]
  congr 1
  exact (Real.rpow_add hx a b).symm

/--
An extremal radius-`rho` shading has aggregate mass at least
`#family * rho^(epsilon+2)`.
-/
lemma wz1_lemma17_coarse_mass_floor
    {rho sigma epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily rho}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    (hrho : 0 < rho)
    (hrhoHalf : rho ≤ 1 / 2)
    (hextremal : WZ1ExtremalPair sigma epsilon F U Y) :
    (F.card : ENNReal) *
        Kakeya.realRpowENN rho (epsilon + 2) ≤
      Y.mass := by
  have htube :
      ∀ index : Fin F.card,
        ENNReal.ofReal (rho ^ 2) ≤
          (F.tube index).volume :=
    fun index =>
      tube_volume_lower_bound hrho hrhoHalf (F.tube index)
  have hfamily :
      (F.card : ENNReal) * ENNReal.ofReal (rho ^ 2) ≤
        F.toBodyFamily.mass := by
    calc
      (F.card : ENNReal) * ENNReal.ofReal (rho ^ 2) =
          ∑ _index : Fin F.card,
            ENNReal.ofReal (rho ^ 2) := by
        simp [Finset.sum_const]
      _ ≤ ∑ index : Fin F.card, (F.tube index).volume :=
        Finset.sum_le_sum fun index _ => htube index
      _ = F.toBodyFamily.mass := rfl
  have hdense :
      Kakeya.realRpowENN rho epsilon *
          F.toBodyFamily.mass ≤
        Y.mass :=
    hextremal.2.2.2.2.2.2.2.1
  have hpowTwo :
      ENNReal.ofReal (rho ^ 2) =
        Kakeya.realRpowENN rho 2 := by
    simp [Kakeya.realRpowENN]
  calc
    (F.card : ENNReal) *
          Kakeya.realRpowENN rho (epsilon + 2) =
        Kakeya.realRpowENN rho epsilon *
          ((F.card : ENNReal) *
            ENNReal.ofReal (rho ^ 2)) := by
      rw [hpowTwo, ← lemma17_realRpowENN_mul hrho]
      ac_rfl
    _ ≤
        Kakeya.realRpowENN rho epsilon *
          F.toBodyFamily.mass := by
      gcongr
    _ ≤ Y.mass := hdense

private lemma lemma17_grid_pruning_per_tube_budget_of_bound
    {rho tau epsilon loss : ℝ}
    (hrho : 0 < rho)
    (htau : 0 < tau)
    (htauOne : tau ≤ 1)
    (hloss : 0 ≤ loss)
    (hsmall :
      3 * 13 ^ 3 * Real.rpow rho epsilon ≤ loss) :
    (((Nat.ceil (1 / tau) + 1) * 13 ^ 3 : ℕ) : ENNReal) *
        (Kakeya.realRpowENN rho (2 + 2 * epsilon) *
          ENNReal.ofReal tau) ≤
      ENNReal.ofReal loss *
        Kakeya.realRpowENN rho (epsilon + 2) := by
  let count : ℕ :=
    (Nat.ceil (1 / tau) + 1) * 13 ^ 3
  have hceil :
      (Nat.ceil (1 / tau) : ℝ) ≤ 1 / tau + 1 := by
    exact (Nat.ceil_lt_add_one (by positivity : 0 ≤ 1 / tau)).le
  have hcountTau :
      (count : ℝ) * tau ≤ 3 * (13 : ℝ) ^ 3 := by
    have hceilAdd :
        (Nat.ceil (1 / tau) : ℝ) + 1 ≤
          1 / tau + 2 := by
      linarith
    have hmain :
        ((Nat.ceil (1 / tau) : ℝ) + 1) * tau ≤ 3 := by
      calc
        ((Nat.ceil (1 / tau) : ℝ) + 1) * tau ≤
            (1 / tau + 2) * tau := by
          exact mul_le_mul_of_nonneg_right hceilAdd htau.le
        _ = 1 + 2 * tau := by
          field_simp [htau.ne']
        _ ≤ 3 := by linarith
    calc
      (count : ℝ) * tau =
          (((Nat.ceil (1 / tau) : ℝ) + 1) * tau) *
            (13 : ℝ) ^ 3 := by
        simp [count, Nat.cast_mul, Nat.cast_add,
          Nat.cast_one, Nat.cast_pow]
        ring
      _ ≤ 3 * (13 : ℝ) ^ 3 := by
        exact mul_le_mul_of_nonneg_right hmain (by positivity)
  have hfactor :
      Real.rpow rho (2 + 2 * epsilon) =
        Real.rpow rho epsilon *
          Real.rpow rho (epsilon + 2) := by
    calc
      Real.rpow rho (2 + 2 * epsilon) =
          Real.rpow rho (epsilon + (epsilon + 2)) := by
        congr 1
        ring
      _ =
          Real.rpow rho epsilon *
            Real.rpow rho (epsilon + 2) :=
        Real.rpow_add hrho _ _
  have hreal :
      (count : ℝ) *
          (Real.rpow rho (2 + 2 * epsilon) * tau) ≤
        loss *
          Real.rpow rho (epsilon + 2) := by
    rw [hfactor]
    have hpowNonneg :
        0 ≤ Real.rpow rho (epsilon + 2) :=
      Real.rpow_nonneg hrho.le _
    have hepsilonPowerNonneg :
        0 ≤ Real.rpow rho epsilon :=
      Real.rpow_nonneg hrho.le _
    calc
      (count : ℝ) *
            (Real.rpow rho epsilon *
              Real.rpow rho (epsilon + 2) * tau) =
          ((count : ℝ) * tau) *
            Real.rpow rho epsilon *
              Real.rpow rho (epsilon + 2) := by ring
      _ ≤
          (3 * (13 : ℝ) ^ 3) *
            Real.rpow rho epsilon *
              Real.rpow rho (epsilon + 2) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            hcountTau hepsilonPowerNonneg)
          hpowNonneg
      _ ≤
          loss *
            Real.rpow rho (epsilon + 2) := by
        exact mul_le_mul_of_nonneg_right hsmall hpowNonneg
  have hcountNonneg : 0 ≤ (count : ℝ) := by positivity
  have hthresholdNonneg :
      0 ≤ Real.rpow rho (2 + 2 * epsilon) * tau := by
    exact mul_nonneg (Real.rpow_nonneg hrho.le _) htau.le
  have hleft :
      (count : ENNReal) *
          (Kakeya.realRpowENN rho (2 + 2 * epsilon) *
            ENNReal.ofReal tau) =
        ENNReal.ofReal
          ((count : ℝ) *
            (Real.rpow rho (2 + 2 * epsilon) * tau)) := by
    simp only [Kakeya.realRpowENN]
    rw [show (count : ENNReal) =
        ENNReal.ofReal (count : ℝ) by simp]
    have hinner :
        ENNReal.ofReal (Real.rpow rho (2 + 2 * epsilon)) *
            ENNReal.ofReal tau =
          ENNReal.ofReal
            (Real.rpow rho (2 + 2 * epsilon) * tau) := by
      exact
        (ENNReal.ofReal_mul
          (Real.rpow_nonneg hrho.le _)).symm
    rw [hinner]
    rw [← ENNReal.ofReal_mul hcountNonneg]
  have hright :
      ENNReal.ofReal loss *
          Kakeya.realRpowENN rho (epsilon + 2) =
        ENNReal.ofReal
          (loss *
            Real.rpow rho (epsilon + 2)) := by
    simp only [Kakeya.realRpowENN]
    rw [← ENNReal.ofReal_mul hloss]
  rw [hleft, hright]
  exact ENNReal.ofReal_mono hreal

/--
The per-tube grid-pruning error is at most one tenth of the natural coarse
per-tube mass floor.
-/
lemma wz1_lemma17_grid_pruning_per_tube_budget
    {rho tau epsilon : ℝ}
    (hrho : 0 < rho)
    (htau : 0 < tau)
    (htauOne : tau ≤ 1)
    (hsmall :
      Real.rpow rho epsilon ≤ 1 / 100000) :
    (((Nat.ceil (1 / tau) + 1) * 13 ^ 3 : ℕ) : ENNReal) *
        (Kakeya.realRpowENN rho (2 + 2 * epsilon) *
          ENNReal.ofReal tau) ≤
      (1 / 10 : ENNReal) *
        Kakeya.realRpowENN rho (epsilon + 2) := by
  have hbound :
      3 * 13 ^ 3 * Real.rpow rho epsilon ≤
        (1 / 10 : ℝ) := by
    calc
      3 * 13 ^ 3 * Real.rpow rho epsilon ≤
          3 * 13 ^ 3 * (1 / 100000 : ℝ) := by
        exact mul_le_mul_of_nonneg_left hsmall (by positivity)
      _ ≤ 1 / 10 := by norm_num
  simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 10),
    ENNReal.ofReal_one, ENNReal.ofReal_ofNat] using
    (lemma17_grid_pruning_per_tube_budget_of_bound
      hrho htau htauOne (by norm_num) hbound)

/--
With four times the smallness budget, the per-tube error is at most one
fortieth of the natural coarse mass floor.  This is the version used after
the constant-multiplicity extraction retains one quarter of its reference
shading.
-/
lemma wz1_lemma17_grid_pruning_per_tube_quarter_reference_budget
    {rho tau epsilon : ℝ}
    (hrho : 0 < rho)
    (htau : 0 < tau)
    (htauOne : tau ≤ 1)
    (hsmall :
      Real.rpow rho epsilon ≤ 1 / 400000) :
    (((Nat.ceil (1 / tau) + 1) * 13 ^ 3 : ℕ) : ENNReal) *
        (Kakeya.realRpowENN rho (2 + 2 * epsilon) *
          ENNReal.ofReal tau) ≤
      (1 / 40 : ENNReal) *
        Kakeya.realRpowENN rho (epsilon + 2) := by
  have hbound :
      3 * 13 ^ 3 * Real.rpow rho epsilon ≤
        (1 / 40 : ℝ) := by
    calc
      3 * 13 ^ 3 * Real.rpow rho epsilon ≤
          3 * 13 ^ 3 * (1 / 400000 : ℝ) := by
        exact mul_le_mul_of_nonneg_left hsmall (by positivity)
      _ ≤ 1 / 40 := by norm_num
  simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 40),
    ENNReal.ofReal_one, ENNReal.ofReal_ofNat] using
    (lemma17_grid_pruning_per_tube_budget_of_bound
      hrho htau htauOne (by norm_num) hbound)

/--
The total grid-pruning error is at most one tenth of the source shading mass.
-/
lemma wz1_lemma17_grid_pruning_total_budget
    {rho tau sigma epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily rho}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    (hrho : 0 < rho)
    (hrhoHalf : rho ≤ 1 / 2)
    (htau : 0 < tau)
    (htauOne : tau ≤ 1)
    (hsmall :
      Real.rpow rho epsilon ≤ 1 / 100000)
    (hextremal : WZ1ExtremalPair sigma epsilon F U Y) :
    (F.card : ENNReal) *
        ((((Nat.ceil (1 / tau) + 1) * 13 ^ 3 : ℕ) : ENNReal) *
          (Kakeya.realRpowENN rho (2 + 2 * epsilon) *
            ENNReal.ofReal tau)) ≤
      (1 / 10 : ENNReal) * Y.mass := by
  calc
    (F.card : ENNReal) *
          ((((Nat.ceil (1 / tau) + 1) * 13 ^ 3 : ℕ) : ENNReal) *
            (Kakeya.realRpowENN rho (2 + 2 * epsilon) *
              ENNReal.ofReal tau)) ≤
        (F.card : ENNReal) *
          ((1 / 10 : ENNReal) *
            Kakeya.realRpowENN rho (epsilon + 2)) := by
      exact mul_le_mul_left'
        (wz1_lemma17_grid_pruning_per_tube_budget
          hrho htau htauOne hsmall)
        (F.card : ENNReal)
    _ =
        (1 / 10 : ENNReal) *
          ((F.card : ENNReal) *
            Kakeya.realRpowENN rho (epsilon + 2)) := by
      ac_rfl
    _ ≤ (1 / 10 : ENNReal) * Y.mass := by
      gcongr
      exact
        wz1_lemma17_coarse_mass_floor
          hrho hrhoHalf hextremal

/--
The total grid-pruning error is at most one fortieth of an extremal reference
shading.  This is the budget needed when the source of the pruning retains
one quarter of that reference mass.
-/
lemma wz1_lemma17_grid_pruning_total_quarter_reference_budget
    {rho tau sigma epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily rho}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    (hrho : 0 < rho)
    (hrhoHalf : rho ≤ 1 / 2)
    (htau : 0 < tau)
    (htauOne : tau ≤ 1)
    (hsmall :
      Real.rpow rho epsilon ≤ 1 / 400000)
    (hextremal : WZ1ExtremalPair sigma epsilon F U Y) :
    (F.card : ENNReal) *
        ((((Nat.ceil (1 / tau) + 1) * 13 ^ 3 : ℕ) : ENNReal) *
          (Kakeya.realRpowENN rho (2 + 2 * epsilon) *
            ENNReal.ofReal tau)) ≤
      (1 / 40 : ENNReal) * Y.mass := by
  calc
    (F.card : ENNReal) *
          ((((Nat.ceil (1 / tau) + 1) * 13 ^ 3 : ℕ) : ENNReal) *
            (Kakeya.realRpowENN rho (2 + 2 * epsilon) *
              ENNReal.ofReal tau)) ≤
        (F.card : ENNReal) *
          ((1 / 40 : ENNReal) *
            Kakeya.realRpowENN rho (epsilon + 2)) := by
      exact mul_le_mul_left'
        (wz1_lemma17_grid_pruning_per_tube_quarter_reference_budget
          hrho htau htauOne hsmall)
        (F.card : ENNReal)
    _ =
        (1 / 40 : ENNReal) *
          ((F.card : ENNReal) *
            Kakeya.realRpowENN rho (epsilon + 2)) := by
      ac_rfl
    _ ≤ (1 / 40 : ENNReal) * Y.mass := by
      gcongr
      exact
        wz1_lemma17_coarse_mass_floor
          hrho hrhoHalf hextremal

/-- Every shading of a finite equal-radius tube family has finite mass. -/
lemma tube_shading_mass_ne_top
    {rho : ℝ}
    {F : Kakeya.Streamlined.TubeFamily rho}
    (Y : Kakeya.Streamlined.TubeShading F)
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1) :
    Y.mass ≠ ⊤ := by
  have hcanonical :
      Kakeya.deltaTubeVolume rho ≠ ⊤ :=
    (tube_volume_scaling.2.1 rho hrho hrhoOne).2
  have hcarrier :
      ∀ index : Fin F.card,
        volume (Y.carrier index) ≠ ⊤ := by
    intro index
    have hle :
        volume (Y.carrier index) ≤
          (F.tube index).volume :=
      measure_mono (Y.subset_body index)
    have htube :
        (F.tube index).volume ≠ ⊤ := by
      rw [tube_volume_scaling.1 rho (F.tube index)]
      exact hcanonical
    exact ne_top_of_le_ne_top htube hle
  dsimp only [Kakeya.Streamlined.Shading.mass]
  exact ENNReal.sum_ne_top.mpr fun index _ => hcarrier index

private lemma lemma17_gridCellPrune_mass_retention_of_error
    {rho tau epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily rho}
    {Y : Kakeya.Streamlined.TubeShading F}
    (hrho : 0 < rho)
    (htau : 0 < tau)
    (hrhoTau : rho ≤ tau)
    (htauOne : tau ≤ 1)
    (herror :
      (F.card : ENNReal) *
          ((((Nat.ceil (1 / tau) + 1) * 13 ^ 3 : ℕ) : ENNReal) *
            (Kakeya.realRpowENN rho (2 + 2 * epsilon) *
              ENNReal.ofReal tau)) ≤
        (1 / 10 : ENNReal) * Y.mass) :
    (9 / 10 : ENNReal) * Y.mass ≤
      (gridCellPrune Y tau
        (Real.rpow rho (2 + 2 * epsilon) * tau)
        htau).mass := by
  let count : ℕ :=
    (Nat.ceil (1 / tau) + 1) * 13 ^ 3
  let threshold : ℝ :=
    Real.rpow rho (2 + 2 * epsilon) * tau
  let Z :=
    gridCellPrune Y tau threshold htau
  have hsub : IsSubshading Z Y :=
    gridCellPrune_subshading
  have hcount :
      ∀ index : Fin F.card,
        Set.ncard
            (gridCellsIntersecting tau (Y.carrier index)) ≤
          count := by
    intro index
    have hsubset :
        gridCellsIntersecting tau (Y.carrier index) ⊆
          gridCellsIntersecting tau (F.tube index).carrier := by
      intro cell hcell
      rcases hcell with
        ⟨point, hpointCell, hpointCarrier⟩
      exact
        ⟨point, hpointCell,
          Y.subset_body index hpointCarrier⟩
    have hfinite :
        (gridCellsIntersecting tau
          (F.tube index).carrier).Finite :=
      (gridCellsIntersecting_tube_bound
        htau hrho hrhoTau (F.tube index) htauOne).1
    exact
      (Set.ncard_le_ncard hsubset hfinite).trans
        (gridCellsIntersecting_tube_bound
          htau hrho hrhoTau (F.tube index) htauOne).2
  have hcarrierLoss :
      ∀ index : Fin F.card,
        volume (Y.carrier index \ Z.carrier index) ≤
          (count : ENNReal) * ENNReal.ofReal threshold := by
    intro index
    exact
      gridCellPrune_carrier_loss
        htau (by
          dsimp only [threshold]
          exact mul_nonneg
            (Real.rpow_nonneg hrho.le _) htau.le)
        hrho hrhoTau htauOne index (hcount index)
  have hmassRaw :
      Y.mass ≤
        Z.mass +
          (F.card : ENNReal) *
            ((count : ENNReal) * ENNReal.ofReal threshold) :=
    shading_mass_le_subshading_mass_add_error
      hsub _ hcarrierLoss
  have herror' :
      (F.card : ENNReal) *
          ((count : ENNReal) * ENNReal.ofReal threshold) ≤
        (1 / 10 : ENNReal) * Y.mass := by
    have hthreshold :
        ENNReal.ofReal threshold =
          Kakeya.realRpowENN rho (2 + 2 * epsilon) *
            ENNReal.ofReal tau := by
      dsimp only [threshold, Kakeya.realRpowENN]
      exact ENNReal.ofReal_mul
        (Real.rpow_nonneg hrho.le _)
    rw [hthreshold]
    simpa [count, mul_assoc] using herror
  have hsourceFinite : Y.mass ≠ ⊤ :=
    tube_shading_mass_ne_top Y hrho
      (hrhoTau.trans htauOne)
  have hpartition :
      (9 / 10 : ENNReal) + (1 / 10 : ENNReal) = 1 := by
    have hnine :
        (9 / 10 : ENNReal) = ENNReal.ofReal (9 / 10 : ℝ) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 10)]
      norm_num
    have hone :
        (1 / 10 : ENNReal) = ENNReal.ofReal (1 / 10 : ℝ) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 10)]
      norm_num
    rw [hnine, hone, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  exact
    retained_mass_of_error_le_fraction
      hsourceFinite (by norm_num) hpartition
      hmassRaw herror'

/--
At the Lemma 17 threshold, grid-cell pruning retains at least nine tenths of
the source shaded mass.
-/
lemma wz1_lemma17_gridCellPrune_mass_retention
    {rho tau sigma epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily rho}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    (hrho : 0 < rho)
    (hrhoHalf : rho ≤ 1 / 2)
    (htau : 0 < tau)
    (hrhoTau : rho ≤ tau)
    (htauOne : tau ≤ 1)
    (hsmall :
      Real.rpow rho epsilon ≤ 1 / 100000)
    (hextremal : WZ1ExtremalPair sigma epsilon F U Y) :
    (9 / 10 : ENNReal) * Y.mass ≤
      (gridCellPrune Y tau
        (Real.rpow rho (2 + 2 * epsilon) * tau)
        htau).mass := by
  exact
    lemma17_gridCellPrune_mass_retention_of_error
      hrho htau hrhoTau htauOne
      (wz1_lemma17_grid_pruning_total_budget
        hrho hrhoHalf htau htauOne hsmall hextremal)

/--
If a source shading retains one quarter of an extremal reference shading,
then the same grid-cell pruning retains nine tenths of the source.  This is
the second Property-(P) pruning budget after
`extract_constant_multiplicity`.
-/
lemma wz1_lemma17_gridCellPrune_mass_retention_of_quarter_reference
    {rho tau sigma epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily rho}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {reference source : Kakeya.Streamlined.TubeShading F}
    (hrho : 0 < rho)
    (hrhoHalf : rho ≤ 1 / 2)
    (htau : 0 < tau)
    (hrhoTau : rho ≤ tau)
    (htauOne : tau ≤ 1)
    (hsmall :
      Real.rpow rho epsilon ≤ 1 / 400000)
    (hextremal :
      WZ1ExtremalPair sigma epsilon F U reference)
    (hquarter :
      (1 / 4 : ENNReal) * reference.mass ≤ source.mass) :
    (9 / 10 : ENNReal) * source.mass ≤
      (gridCellPrune source tau
        (Real.rpow rho (2 + 2 * epsilon) * tau)
        htau).mass := by
  apply
    lemma17_gridCellPrune_mass_retention_of_error
      hrho htau hrhoTau htauOne
  calc
    (F.card : ENNReal) *
          ((((Nat.ceil (1 / tau) + 1) * 13 ^ 3 : ℕ) : ENNReal) *
            (Kakeya.realRpowENN rho (2 + 2 * epsilon) *
              ENNReal.ofReal tau)) ≤
        (1 / 40 : ENNReal) * reference.mass :=
      wz1_lemma17_grid_pruning_total_quarter_reference_budget
        hrho hrhoHalf htau htauOne hsmall hextremal
    _ =
        (1 / 10 : ENNReal) *
          ((1 / 4 : ENNReal) * reference.mass) := by
      have hcoeff :
          (1 / 40 : ENNReal) =
            (1 / 10 : ENNReal) * (1 / 4 : ENNReal) := by
        have hleft : (1 / 40 : ENNReal) ≠ ⊤ := by norm_num
        have hright :
            (1 / 10 : ENNReal) * (1 / 4 : ENNReal) ≠ ⊤ :=
          ENNReal.mul_ne_top (by norm_num) (by norm_num)
        apply (ENNReal.toReal_eq_toReal_iff' hleft hright).mp
        norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv]
      rw [hcoeff, mul_assoc]
    _ ≤ (1 / 10 : ENNReal) * source.mass := by
      exact mul_le_mul_left' hquarter _

/--
The second Property-(P) pruning retains nine fortieths of the original
extremal reference mass.  This is the coefficient used to restore the final
`epsilon₂` extremality directly from the robust reference shading.
-/
lemma wz1_lemma17_gridCellPrune_nine_fortieth_reference_mass
    {rho tau sigma epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily rho}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {reference source : Kakeya.Streamlined.TubeShading F}
    (hrho : 0 < rho)
    (hrhoHalf : rho ≤ 1 / 2)
    (htau : 0 < tau)
    (hrhoTau : rho ≤ tau)
    (htauOne : tau ≤ 1)
    (hsmall :
      Real.rpow rho epsilon ≤ 1 / 400000)
    (hextremal :
      WZ1ExtremalPair sigma epsilon F U reference)
    (hquarter :
      (1 / 4 : ENNReal) * reference.mass ≤ source.mass) :
    (9 / 40 : ENNReal) * reference.mass ≤
      (gridCellPrune source tau
        (Real.rpow rho (2 + 2 * epsilon) * tau)
        htau).mass := by
  have hretained :
      (9 / 10 : ENNReal) * source.mass ≤
        (gridCellPrune source tau
          (Real.rpow rho (2 + 2 * epsilon) * tau)
          htau).mass :=
    wz1_lemma17_gridCellPrune_mass_retention_of_quarter_reference
      hrho hrhoHalf htau hrhoTau htauOne hsmall hextremal hquarter
  have hcoeff :
      (9 / 40 : ENNReal) =
        (9 / 10 : ENNReal) * (1 / 4 : ENNReal) := by
    have hnine : (9 : ENNReal) ≠ ⊤ := by norm_num
    have hten : (10 : ENNReal) ≠ 0 := by norm_num
    have hforty : (40 : ENNReal) ≠ 0 := by norm_num
    have hleft : (9 / 40 : ENNReal) ≠ ⊤ :=
      ENNReal.div_ne_top hnine hforty
    have hnineTenths : (9 / 10 : ENNReal) ≠ ⊤ :=
      ENNReal.div_ne_top hnine hten
    have hright :
        (9 / 10 : ENNReal) * (1 / 4 : ENNReal) ≠ ⊤ :=
      ENNReal.mul_ne_top hnineTenths (by norm_num)
    apply (ENNReal.toReal_eq_toReal_iff' hleft hright).mp
    norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv]
  calc
    (9 / 40 : ENNReal) * reference.mass =
        (9 / 10 : ENNReal) *
          ((1 / 4 : ENNReal) * reference.mass) := by
      rw [hcoeff, mul_assoc]
    _ ≤ (9 / 10 : ENNReal) * source.mass := by
      exact mul_le_mul_left' hquarter _
    _ ≤
        (gridCellPrune source tau
          (Real.rpow rho (2 + 2 * epsilon) * tau)
          htau).mass := hretained

/--
The same pruning loses at most one tenth of the source shaded mass, in the
form consumed by `extract_constant_multiplicity`.
-/
lemma wz1_lemma17_gridCellPrune_dropped_mass
    {rho tau sigma epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily rho}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    (hrho : 0 < rho)
    (hrhoHalf : rho ≤ 1 / 2)
    (htau : 0 < tau)
    (hrhoTau : rho ≤ tau)
    (htauOne : tau ≤ 1)
    (hsmall :
      Real.rpow rho epsilon ≤ 1 / 100000)
    (hextremal : WZ1ExtremalPair sigma epsilon F U Y) :
    Y.mass -
        (gridCellPrune Y tau
          (Real.rpow rho (2 + 2 * epsilon) * tau)
          htau).mass ≤
      (1 / 10 : ENNReal) * Y.mass := by
  let Z :=
    gridCellPrune Y tau
      (Real.rpow rho (2 + 2 * epsilon) * tau)
      htau
  have hretained :
      (9 / 10 : ENNReal) * Y.mass ≤ Z.mass :=
    wz1_lemma17_gridCellPrune_mass_retention
      hrho hrhoHalf htau hrhoTau htauOne hsmall hextremal
  have hpartition :
      (9 / 10 : ENNReal) + (1 / 10 : ENNReal) = 1 := by
    have hnine :
        (9 / 10 : ENNReal) = ENNReal.ofReal (9 / 10 : ℝ) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 10)]
      norm_num
    have hone :
        (1 / 10 : ENNReal) = ENNReal.ofReal (1 / 10 : ℝ) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 10)]
      norm_num
    rw [hnine, hone, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  apply dropped_mass_of_mass_le_add_error
  calc
    Y.mass = ((9 / 10 : ENNReal) + (1 / 10 : ENNReal)) * Y.mass := by
      rw [hpartition, one_mul]
    _ =
        (9 / 10 : ENNReal) * Y.mass +
          (1 / 10 : ENNReal) * Y.mass := by
      rw [add_mul]
    _ ≤ Z.mass + (1 / 10 : ENNReal) * Y.mass := by
      exact add_le_add_left hretained _

end

end Kakeya.Assouad
