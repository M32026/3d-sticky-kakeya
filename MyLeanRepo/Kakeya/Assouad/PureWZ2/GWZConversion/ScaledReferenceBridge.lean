import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12Extremal

/-!
# Scaled reference-scale bridge

Convert covers at the actual radii
`B * delta * r^k`, `k = 0, ..., N - 1`, together with one top cover at
radius `B`, into literal nearby-scale CWA.  The first gap costs `B`; every
later gap costs `r`.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

theorem pureWZ2_nearby_from_scaled_reference_scales
    {delta : ℝ}
    (hdelta : 0 < delta)
    {family : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    (hCOne : 1 ≤ C)
    (hCTop : C ≠ ⊤)
    (familyDistinct :
      WZ2PaperOrdinaryIsEssentiallyDistinct family)
    (B r : ℝ)
    (hB : 1 ≤ B)
    (hBLt : ENNReal.ofReal B < C)
    (hr : 1 < r)
    (hrLt : ENNReal.ofReal r < C)
    (N : ℕ)
    (hlast : delta * r ^ N = 1)
    (smallCovers :
      ∀ coordinate : Fin N,
        WZ2PaperPureScaleCoverData family
          (B * delta * r ^ coordinate.val) C)
    (topCover :
      WZ2PaperPureScaleCoverData family B C) :
    WZ2PaperPureCWAAtNearbyScales family C := by
  refine
    ⟨hdelta, ⟨hCOne, hCTop⟩, familyDistinct, ?_⟩
  intro requested
  let target := requested.1
  let predicate : ℕ → Prop := fun index =>
    target ≤ B * delta * r ^ index
  have hpredicateN : predicate N := by
    dsimp only [predicate]
    rw [show B * delta * r ^ N =
      B * (delta * r ^ N) by ring, hlast, mul_one]
    exact requested.2.2.trans hB
  let index := Nat.find ⟨N, hpredicateN⟩
  have hindexProperty : predicate index :=
    Nat.find_spec ⟨N, hpredicateN⟩
  have hindexLe : index ≤ N :=
    Nat.find_min' ⟨N, hpredicateN⟩ hpredicateN
  have hwithinFormula :
      ENNReal.ofReal (B * delta * r ^ index) <
        C * ENNReal.ofReal target := by
    by_cases hindexZero : index = 0
    · have htargetPos : 0 < target :=
        hdelta.trans_le requested.2.1
      have hdeltaENN :
          ENNReal.ofReal delta ≤ ENNReal.ofReal target :=
        ENNReal.ofReal_mono requested.2.1
      have hBPositive : 0 < ENNReal.ofReal B := by
        apply ENNReal.ofReal_pos.mpr
        linarith
      have hBFinite : ENNReal.ofReal B ≠ ⊤ := by simp
      have htargetENNPositive :
          0 < ENNReal.ofReal target := by positivity
      have htargetENNFinite :
          ENNReal.ofReal target ≠ ⊤ := by simp
      have hstrict :
          ENNReal.ofReal B * ENNReal.ofReal target <
            C * ENNReal.ofReal target :=
        by
          simpa [mul_comm] using
            ENNReal.mul_lt_mul_right
              htargetENNPositive.ne' htargetENNFinite hBLt
      have hproduct :
          ENNReal.ofReal (B * delta) =
            ENNReal.ofReal B * ENNReal.ofReal delta := by
        rw [ENNReal.ofReal_mul]
        linarith
      rw [hindexZero, pow_zero, mul_one, hproduct]
      exact
        (mul_le_mul_left' hdeltaENN
          (ENNReal.ofReal B)).trans_lt hstrict
    · have hindexPos : 0 < index := Nat.pos_of_ne_zero hindexZero
      let previous := index - 1
      have hindexEq : index = previous + 1 := by omega
      have hpreviousNot :
          ¬predicate previous := by
        dsimp only [previous]
        exact Nat.find_min ⟨N, hpredicateN⟩ (by omega)
      have hpreviousLt :
          B * delta * r ^ previous < target := by
        simpa [predicate] using hpreviousNot
      have hformula :
          B * delta * r ^ index =
            r * (B * delta * r ^ previous) := by
        rw [hindexEq, pow_succ]
        ring
      rw [hformula]
      have hpreviousPos :
          0 < B * delta * r ^ previous := by positivity
      have hproduct :
          ENNReal.ofReal
              (r * (B * delta * r ^ previous)) =
            ENNReal.ofReal r *
              ENNReal.ofReal
                (B * delta * r ^ previous) := by
        rw [ENNReal.ofReal_mul]
        linarith
      rw [hproduct]
      have hpreviousENN :
          ENNReal.ofReal (B * delta * r ^ previous) <
            ENNReal.ofReal target := by
        rw [ENNReal.ofReal_lt_ofReal_iff
          (hdelta.trans_le requested.2.1)]
        exact hpreviousLt
      have hfirst :
          ENNReal.ofReal r *
              ENNReal.ofReal (B * delta * r ^ previous) <
            C * ENNReal.ofReal
              (B * delta * r ^ previous) := by
        simpa [mul_comm] using
          ENNReal.mul_lt_mul_right
            (by positivity : ENNReal.ofReal
              (B * delta * r ^ previous) ≠ 0)
            (by simp) hrLt
      exact hfirst.trans
        (by
          simpa [mul_comm] using
            ENNReal.mul_lt_mul_left
              (by
                have : (0 : ENNReal) < 1 := by norm_num
                exact this.trans_le hCOne |>.ne')
              hCTop hpreviousENN)
  by_cases hsmall : index < N
  · let coordinate : Fin N := ⟨index, hsmall⟩
    refine
      ⟨{
        rho := B * delta * r ^ coordinate.val
        requested_le := by
          simpa [coordinate, predicate] using hindexProperty
        within_factor := by
          simpa [coordinate] using hwithinFormula
        scaleData := smallCovers coordinate
      }⟩
  · have hindexEq : index = N := by omega
    have htopEq :
        B * delta * r ^ index = B := by
      rw [hindexEq, show B * delta * r ^ N =
        B * (delta * r ^ N) by ring, hlast, mul_one]
    refine
      ⟨{
        rho := B
        requested_le := by
          rw [← htopEq]
          exact hindexProperty
        within_factor := by
          rw [← htopEq]
          exact hwithinFormula
        scaleData := topCover
      }⟩

end Kakeya.Assouad

end
