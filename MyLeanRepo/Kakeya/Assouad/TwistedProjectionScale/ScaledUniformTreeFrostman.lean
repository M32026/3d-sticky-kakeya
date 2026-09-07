import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.UniformTreeFrostman

/-!
# Frostman bound from a uniformly scaled tree

This version allows the level-`m` mesh to be
`1 / (scaleFactor * base^m)`, which is the normalization naturally produced
by a selected parameter cell.
-/

noncomputable section

namespace Kakeya.Assouad

lemma scaled_uniform_subtree_frostman
    (A : DiscreteSet 3)
    (base : ℕ)
    (hbase : 2 ≤ base)
    (scaleFactor : ℝ)
    (hscaleFactor : 1 ≤ scaleFactor)
    (maxLevel : ℕ)
    (hmaxLevel : 0 < maxLevel)
    (d : ℝ)
    (hd : 0 ≤ d)
    (fineScale : ℝ)
    (hfine_pos : 0 < fineScale)
    (hfine_mesh :
      1 / (scaleFactor * (base : ℝ) ^ maxLevel) ≤
        fineScale)
    (Cgeom : ℝ)
    (hCgeom : 1 ≤ Cgeom)
    (N M : ℕ → ℕ)
    (h_total :
      ∀ m, 0 < m → m ≤ maxLevel →
        N m * M m = A.card)
    (hN_pos :
      ∀ m, 0 < m → m ≤ maxLevel → 0 < N m)
    (h_ball_bound :
      ∀ m x r,
        0 < m →
        m ≤ maxLevel →
        1 / (scaleFactor * (base : ℝ) ^ m) ≤ r →
        r * scaleFactor * (base : ℝ) ^ m < base →
        (A.ballCount x r).toReal ≤
          Cgeom * (M m : ℝ))
    (h_branch :
      ∀ m, 0 < m → m ≤ maxLevel →
        (base : ℝ) ^ ((m : ℝ) * d) ≤ N m) :
    A.IsFrostman fineScale d
      (ENNReal.ofReal Cgeom *
        Kakeya.realRpowENN scaleFactor d) := by
  have hbase_pos : (0 : ℝ) < base := by
    exact_mod_cast (show 0 < base by omega)
  have hscaleFactor_pos : 0 < scaleFactor := by
    linarith
  let constant : ENNReal :=
    ENNReal.ofReal Cgeom *
      Kakeya.realRpowENN scaleFactor d
  have hconstant_top : constant ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (by simp [Kakeya.realRpowENN])
  intro x r hfine_r hr_one
  have hr_pos : 0 < r := hfine_pos.trans_le hfine_r
  by_cases hlarge :
      1 / scaleFactor ≤ r
  · have hcount :
        A.ballCount x r ≤ A.enncard := by
      dsimp only [DiscreteSet.ballCount, DiscreteSet.enncard]
      exact_mod_cast
        Finset.card_le_card (Finset.filter_subset _ _)
    have hscale_r :
        1 ≤ scaleFactor * r := by
      have hmul :=
        mul_le_mul_of_nonneg_left hlarge
          hscaleFactor_pos.le
      field_simp [hscaleFactor_pos.ne'] at hmul
      exact hmul
    have hrpow :
        (1 : ENNReal) ≤
          Kakeya.realRpowENN scaleFactor d *
            Kakeya.realRpowENN r d := by
      rw [← realRpowENN_mul
        hscaleFactor_pos hr_pos d]
      simp only [Kakeya.realRpowENN]
      rw [ENNReal.one_le_ofReal]
      exact Real.one_le_rpow hscale_r hd
    have hgeom :
        (1 : ENNReal) ≤ ENNReal.ofReal Cgeom := by
      rw [ENNReal.one_le_ofReal]
      exact hCgeom
    calc
      A.ballCount x r ≤ A.enncard := hcount
      _ = (1 : ENNReal) * A.enncard := by simp
      _ ≤
          (ENNReal.ofReal Cgeom *
            Kakeya.realRpowENN scaleFactor d *
            Kakeya.realRpowENN r d) *
            A.enncard := by
        gcongr
        calc
          (1 : ENNReal) ≤
              ENNReal.ofReal Cgeom *
                (Kakeya.realRpowENN scaleFactor d *
                  Kakeya.realRpowENN r d) := by
            exact one_le_mul hgeom hrpow
          _ =
              ENNReal.ofReal Cgeom *
                Kakeya.realRpowENN scaleFactor d *
                  Kakeya.realRpowENN r d := by ring
      _ =
          constant * Kakeya.realRpowENN r d *
            A.enncard := by rfl
  · have hr_small :
        scaleFactor * r < 1 := by
      have hnot : r < 1 / scaleFactor :=
        lt_of_not_ge hlarge
      have hmul :=
        mul_lt_mul_of_pos_left hnot hscaleFactor_pos
      field_simp [hscaleFactor_pos.ne'] at hmul
      exact hmul
    let scaledRadius := scaleFactor * r
    have hscaled_pos : 0 < scaledRadius := by
      dsimp only [scaledRadius]
      positivity
    have hscaled_lt : scaledRadius < 1 := hr_small
    have hterminal :
        1 / (base : ℝ) ^ maxLevel ≤
          scaledRadius := by
      calc
        1 / (base : ℝ) ^ maxLevel =
            scaleFactor *
              (1 /
                (scaleFactor *
                  (base : ℝ) ^ maxLevel)) := by
          field_simp [hscaleFactor_pos.ne']
        _ ≤ scaleFactor * fineScale := by gcongr
        _ ≤ scaleFactor * r := by gcongr
        _ = scaledRadius := rfl
    obtain ⟨m, hm_pos, hm_le, hm_lower, hm_upper⟩ :=
      find_rel_level hbase hscaled_pos hscaled_lt hterminal
    let mesh : ℝ :=
      1 / (scaleFactor * (base : ℝ) ^ m)
    have hmesh_pos : 0 < mesh := by
      dsimp only [mesh]
      positivity
    have hmesh_r : mesh ≤ r := by
      dsimp only [mesh]
      have hmul :=
        mul_le_mul_of_nonneg_left hm_lower
          (show 0 ≤ scaleFactor⁻¹ by positivity)
      have hrewrite :
          scaleFactor⁻¹ *
              (1 / (base : ℝ) ^ m) =
            1 /
              (scaleFactor * (base : ℝ) ^ m) := by
        field_simp [hscaleFactor_pos.ne']
      have hright :
          scaleFactor⁻¹ * scaledRadius = r := by
        dsimp only [scaledRadius]
        field_simp [hscaleFactor_pos.ne']
      rwa [hrewrite, hright] at hmul
    have hr_mesh :
        r * scaleFactor * (base : ℝ) ^ m <
          base := by
      have hidentity :
          1 / (base : ℝ) ^ (m - 1) =
            (base : ℝ) / (base : ℝ) ^ m := by
        cases m with
        | zero => contradiction
        | succ m' =>
            simp [pow_succ]
            field_simp
      rw [hidentity] at hm_upper
      have hpow : 0 < (base : ℝ) ^ m := by positivity
      have hscaled : scaleFactor * r = scaledRadius := rfl
      calc
        r * scaleFactor * (base : ℝ) ^ m =
            scaledRadius * (base : ℝ) ^ m := by
          rw [mul_comm r scaleFactor, hscaled]
        _ <
            ((base : ℝ) / (base : ℝ) ^ m) *
              (base : ℝ) ^ m := by gcongr
        _ = base := by field_simp [hpow.ne']
    have hgeom :
        (A.ballCount x r).toReal ≤
          Cgeom * (M m : ℝ) :=
      h_ball_bound m x r hm_pos hm_le
        hmesh_r hr_mesh
    have htotal :
        (N m : ℝ) * (M m : ℝ) ≤
          A.enncard.toReal := by
      rw [show A.enncard.toReal = (A.card : ℝ) by
        simp [DiscreteSet.enncard]]
      exact_mod_cast (h_total m hm_pos hm_le).le
    have hbranch :
        Real.rpow mesh (-d) ≤
          Real.rpow scaleFactor d * (N m : ℝ) := by
      have hmesh_eq :
          mesh =
            Real.rpow scaleFactor (-1) *
              Real.rpow (base : ℝ) (-(m : ℝ)) := by
        dsimp only [mesh]
        rw [show
          1 / (scaleFactor * (base : ℝ) ^ m) =
            scaleFactor⁻¹ * ((base : ℝ) ^ m)⁻¹ by
          field_simp [hscaleFactor_pos.ne']]
        have hscale_inv :
            scaleFactor⁻¹ =
              Real.rpow scaleFactor (-1) := by
          simpa using
            (Real.rpow_neg_one scaleFactor).symm
        have hbase_inv :
            ((base : ℝ) ^ m)⁻¹ =
              Real.rpow (base : ℝ) (-(m : ℝ)) := by
          calc
            ((base : ℝ) ^ m)⁻¹ =
                (Real.rpow (base : ℝ) (m : ℝ))⁻¹ := by
              congr 1
              exact (Real.rpow_natCast (base : ℝ) m).symm
            _ = Real.rpow (base : ℝ) (-(m : ℝ)) :=
              (Real.rpow_neg hbase_pos.le (m : ℝ)).symm
        rw [hscale_inv, hbase_inv]
      rw [hmesh_eq]
      have hrpow_mul :
          Real.rpow
              (Real.rpow scaleFactor (-1) *
                Real.rpow (base : ℝ) (-(m : ℝ)))
              (-d) =
            Real.rpow scaleFactor d *
              Real.rpow (base : ℝ) ((m : ℝ) * d) := by
        have hfirst :
            Real.rpow (Real.rpow scaleFactor (-1)) (-d) =
              Real.rpow scaleFactor d := by
          calc
            Real.rpow (Real.rpow scaleFactor (-1)) (-d) =
                Real.rpow scaleFactor ((-1 : ℝ) * (-d)) :=
              (Real.rpow_mul hscaleFactor_pos.le (-1) (-d)).symm
            _ = Real.rpow scaleFactor d := by
              congr 1
              ring
        have hsecond :
            Real.rpow
                (Real.rpow (base : ℝ) (-(m : ℝ))) (-d) =
              Real.rpow (base : ℝ) ((m : ℝ) * d) := by
          calc
            Real.rpow
                (Real.rpow (base : ℝ) (-(m : ℝ))) (-d) =
                Real.rpow (base : ℝ)
                  ((-(m : ℝ)) * (-d)) :=
              (Real.rpow_mul hbase_pos.le
                (-(m : ℝ)) (-d)).symm
            _ = Real.rpow (base : ℝ) ((m : ℝ) * d) := by
              congr 1
              ring
        calc
          Real.rpow
                (Real.rpow scaleFactor (-1) *
                  Real.rpow (base : ℝ) (-(m : ℝ)))
                (-d) =
              Real.rpow (Real.rpow scaleFactor (-1)) (-d) *
                Real.rpow
                  (Real.rpow (base : ℝ) (-(m : ℝ))) (-d) :=
            Real.mul_rpow
              (Real.rpow_nonneg hscaleFactor_pos.le _)
              (Real.rpow_nonneg hbase_pos.le _)
          _ = Real.rpow scaleFactor d *
                Real.rpow (base : ℝ) ((m : ℝ) * d) := by
            rw [hfirst, hsecond]
      rw [hrpow_mul]
      exact mul_le_mul_of_nonneg_left
        (h_branch m hm_pos hm_le)
        (Real.rpow_nonneg hscaleFactor_pos.le d)
    have hreal :=
      uniform_tree_frostman_core_real_with_loss
        hd hmesh_pos hmesh_r hr_one
        (by linarith) (Real.rpow_nonneg hscaleFactor_pos.le d)
        (by positivity)
        (by exact_mod_cast hN_pos m hm_pos hm_le)
        hgeom htotal hbranch
    have hlhs_top : A.ballCount x r ≠ ⊤ := by
      simp [DiscreteSet.ballCount]
    have hrhs_top :
        constant * Kakeya.realRpowENN r d *
            A.enncard ≠ ⊤ :=
      ENNReal.mul_ne_top
        (ENNReal.mul_ne_top hconstant_top
          (by simp [Kakeya.realRpowENN]))
        (by simp [DiscreteSet.enncard])
    apply
      (ENNReal.toReal_le_toReal hlhs_top hrhs_top).mp
    have hCgeom_real :
        (ENNReal.ofReal Cgeom).toReal = Cgeom := by
      exact ENNReal.toReal_ofReal (by linarith)
    simpa [constant, ENNReal.toReal_mul,
      Kakeya.realRpowENN, hCgeom_real,
      ENNReal.toReal_ofReal
        (Real.rpow_nonneg hscaleFactor_pos.le d),
      ENNReal.toReal_ofReal
        (Real.rpow_nonneg hr_pos.le d)]
      using hreal

end Kakeya.Assouad
