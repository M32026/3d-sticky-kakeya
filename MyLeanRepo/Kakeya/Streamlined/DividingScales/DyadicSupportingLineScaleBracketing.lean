import MyLeanRepo.Kakeya.Streamlined.DividingScales.PeriodicSupportingLineEDSelection

/-!
# Dyadic grid levels for supporting-line covers

Every runtime scale `rho ∈ (0,1]` is bracketed by one dyadic mesh

`mesh = 2⁻ˡᵉᵛᵉˡ`

with

`mesh < rho ≤ 2 * mesh`.

Consequently

`3000 * rho * 2^level + 1 < 6002`,

so the one-scale supporting-line ED producer can always use the fixed modulus
`6002`, independent of `rho`.
-/

noncomputable section

namespace Kakeya.Streamlined

/-- A dyadic grid level whose mesh is comparable with `rho`. -/
structure DyadicSupportingLineGridLevel (rho : ℝ) where
  level : ℕ
  mesh_lt : (2 ^ level : ℝ)⁻¹ < rho
  rho_le_two_mul_mesh :
    rho ≤ 2 * (2 ^ level : ℝ)⁻¹

/--
Ordered radii force any comparable dyadic mesh witnesses to have ordered
levels.  Thus independently chosen witnesses are automatically coherent at
the integer-grid level; no monotone choice principle is needed.
-/
theorem DyadicSupportingLineGridLevel.level_le_of_scale_le
    {coarseRho fineRho : ℝ}
    (coarse : DyadicSupportingLineGridLevel coarseRho)
    (fine : DyadicSupportingLineGridLevel fineRho)
    (hfineCoarse : fineRho ≤ coarseRho) :
    coarse.level ≤ fine.level := by
  by_contra hnot
  have hlevel : fine.level + 1 ≤ coarse.level := by
    omega
  have hpowNat :
      2 ^ (fine.level + 1) ≤ 2 ^ coarse.level :=
    Nat.pow_le_pow_right (by omega) hlevel
  have hpowReal :
      (2 ^ (fine.level + 1) : ℝ) ≤
        (2 ^ coarse.level : ℝ) := by
    exact_mod_cast hpowNat
  have hinv :
      (2 ^ coarse.level : ℝ)⁻¹ ≤
        (2 ^ (fine.level + 1) : ℝ)⁻¹ :=
    inv_anti₀ (by positivity) hpowReal
  have hmesh :
      2 * (2 ^ coarse.level : ℝ)⁻¹ ≤
        (2 ^ fine.level : ℝ)⁻¹ := by
    calc
      2 * (2 ^ coarse.level : ℝ)⁻¹ ≤
          2 * (2 ^ (fine.level + 1) : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_left hinv (by norm_num)
      _ = (2 ^ fine.level : ℝ)⁻¹ := by
        rw [pow_succ]
        have hpowNe : (2 ^ fine.level : ℝ) ≠ 0 := by
          positivity
        field_simp
  have hstrict :
      (2 ^ fine.level : ℝ)⁻¹ <
        2 * (2 ^ coarse.level : ℝ)⁻¹ :=
    fine.mesh_lt.trans_le
      (hfineCoarse.trans coarse.rho_le_two_mul_mesh)
  exact (not_lt_of_ge hmesh) hstrict

/-- Every positive scale at most one has a comparable dyadic mesh. -/
theorem exists_dyadicSupportingLineGridLevel
    {rho : ℝ} (hrho : 0 < rho) (hrhoOne : rho ≤ 1) :
    Nonempty (DyadicSupportingLineGridLevel rho) := by
  rcases
      exists_nat_pow_near_of_lt_one
        hrho hrhoOne (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1) with
    ⟨index, hfine, hcoarse⟩
  refine ⟨{
    level := index + 1
    mesh_lt := ?_
    rho_le_two_mul_mesh := ?_
  }⟩
  · have hpow :
        (1 / 2 : ℝ) ^ (index + 1) =
          (2 ^ (index + 1) : ℝ)⁻¹ := by
      rw [one_div, inv_pow]
    rwa [hpow] at hfine
  · have hcoarsePow :
        (1 / 2 : ℝ) ^ index =
          (2 ^ index : ℝ)⁻¹ := by
      rw [one_div, inv_pow]
    have hmeshRelation :
        (2 ^ index : ℝ)⁻¹ =
          2 * (2 ^ (index + 1) : ℝ)⁻¹ := by
      rw [pow_succ]
      have htwo : (2 : ℝ) ≠ 0 := by norm_num
      field_simp
    rw [hcoarsePow, hmeshRelation] at hcoarse
    exact hcoarse

/-- The fixed modulus `6002` dominates every dyadic conflict range. -/
theorem dyadicSupportingLine_fixedModulus
    {rho : ℝ}
    (grid : DyadicSupportingLineGridLevel rho) :
    (3000 * rho) * (2 ^ grid.level : ℝ) + 1 <
      (6002 : ℝ) := by
  have hpowPos : 0 < (2 ^ grid.level : ℝ) := by positivity
  have hbound :
      rho * (2 ^ grid.level : ℝ) ≤ 2 := by
    have hmul :=
      mul_le_mul_of_nonneg_right
        grid.rho_le_two_mul_mesh hpowPos.le
    have hinv :
        (2 ^ grid.level : ℝ)⁻¹ *
            (2 ^ grid.level : ℝ) = 1 := by
      exact inv_mul_cancel₀ hpowPos.ne'
    calc
      rho * (2 ^ grid.level : ℝ)
          ≤
        (2 * (2 ^ grid.level : ℝ)⁻¹) *
          (2 ^ grid.level : ℝ) := hmul
      _ = 2 := by rw [mul_assoc, hinv, mul_one]
  nlinarith

/-- The dyadic mesh is small enough for the local cover geometry. -/
theorem dyadicSupportingLine_mesh_le
    {rho : ℝ}
    (grid : DyadicSupportingLineGridLevel rho) :
    (2 ^ grid.level : ℝ)⁻¹ ≤ rho :=
  grid.mesh_lt.le

/--
At one dyadic runtime scale, equal fixed periodic colors force distinct
candidate parents to be essentially distinct.
-/
theorem dyadicSupportingLine_sameColor_essentiallyDistinct
    {delta rho : ℝ}
    (family : TubeFamily delta)
    (hfamilyBall : family.IsInUnitBall)
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (grid : DyadicSupportingLineGridLevel rho)
    {first second :
      Fin
        (occupiedProjectiveSupportingLineRepresentativeFamily
          (rho := rho) family 2 grid.level).card}
    (hne : first ≠ second)
    (hcolor :
      supportingLinePeriodicColor
          family 2 grid.level 6002 (by norm_num) first =
        supportingLinePeriodicColor
          family 2 grid.level 6002 (by norm_num) second) :
    ((occupiedProjectiveSupportingLineRepresentativeFamily
        (rho := rho) family 2 grid.level).tube first).EssentiallyDistinct
      ((occupiedProjectiveSupportingLineRepresentativeFamily
        (rho := rho) family 2 grid.level).tube second) := by
  let coarse :=
    occupiedProjectiveSupportingLineRepresentativeFamily
      (rho := rho) family 2 grid.level
  let label : Fin coarse.card → Fin 1 → Fin 12 → ℤ :=
    fun parentIndex _ =>
      integerGridLabel 2 grid.level
        (projectiveSupportingLineCoordinates
          (coarse.tube parentIndex))
  have hlabelInjective : Function.Injective label := by
    intro left right hlabel
    apply
      occupiedProjectiveSupportingLineRepresentativeFamily_gridLabel_injective
        family 2 grid.level
    exact congrFun hlabel 0
  let conflict : Fin coarse.card → Fin coarse.card → Prop :=
    fun left right =>
      ¬(coarse.tube left).EssentiallyDistinct
        (coarse.tube right)
  by_contra hnotED
  apply hne
  apply
    periodicIntegerGridColor_proper
      (modulus := 6002) (by norm_num)
      label hlabelInjective conflict
  · intro left right hconflict _gridLevel coordinate
    apply
      projectiveSupportingLineGridLabel_abs_sub_lt_of_not_essentiallyDistinct
        hrho hrhoOne
        (occupiedProjectiveSupportingLineRepresentativeFamily_midpoint_norm_le_one
          family hfamilyBall 2 grid.level left)
        hconflict
        (dyadicSupportingLine_fixedModulus grid)
        coordinate
  · exact hnotED
  · simpa [supportingLinePeriodicColor, label] using hcolor

/--
Fixed-modulus one-scale ED selection at every runtime scale.  The only
remaining scale parameters are the original bottom scale and `rho`; the grid
level and modulus are now canonical numerical witnesses.
-/
theorem exists_dyadicPeriodicSupportingLineEDSelection
    {delta rho : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hdeltaRho : delta ≤ rho)
    (family : TubeFamily delta)
    (hfamilyBall : family.IsInUnitBall) :
    ∃ grid : DyadicSupportingLineGridLevel rho,
      Nonempty
        (PeriodicSupportingLineEDSelectionPackage
          family 2 grid.level 6002
          (occupiedProjectiveSupportingLineLocalCover
            hdelta hrho hrhoOne hdeltaRho family hfamilyBall
            2 grid.level (by norm_num)
            (dyadicSupportingLine_mesh_le grid))) := by
  rcases
      exists_dyadicSupportingLineGridLevel hrho hrhoOne with
    ⟨grid⟩
  refine ⟨grid, ?_⟩
  apply
    exists_periodicSupportingLineEDSelection
      hdelta hrho hrhoOne hdeltaRho family hfamilyBall
      2 grid.level 6002 (by norm_num)
      (dyadicSupportingLine_mesh_le grid)
      (by norm_num)
      (dyadicSupportingLine_fixedModulus grid)

end Kakeya.Streamlined
