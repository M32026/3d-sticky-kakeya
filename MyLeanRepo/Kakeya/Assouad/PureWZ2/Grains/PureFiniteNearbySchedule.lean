import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12Extremal

/-!
# Finite representative schedule for pure nearby-scale CWA

Choose finitely many requested scales and attach the pure actual-John
witness supplied by `WZ2PaperPureCWAAtNearbyScales` at each representative.
Every requested real scale is assigned to one representative whose actual
cover scale remains inside the enlarged output window.  No historical WZ
target family is introduced.
-/

noncomputable section

namespace Kakeya.Assouad

open Kakeya.Streamlined

/-- A finite representative list of actual-John nearby-scale witnesses. -/
structure WZ2PaperPureFiniteNearbyScheduleData
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (ambientConstant outputConstant : ENNReal)
    (levelCount : ℕ) where
  scaleCount : ℕ
  scaleCount_pos : 0 < scaleCount
  scaleCount_le : scaleCount ≤ levelCount + 1
  requested :
    Fin scaleCount → WZ2PaperRequestedScale delta
  witness :
    ∀ coordinate,
      WZ2PaperPureNearbyScaleCoverData
        fine (requested coordinate) ambientConstant
  representative :
    WZ2PaperRequestedScale delta → Fin scaleCount
  requested_le :
    ∀ rho₀,
      rho₀.1 ≤ (witness (representative rho₀)).rho
  within_output :
    ∀ rho₀,
      ENNReal.ofReal (witness (representative rho₀)).rho <
        outputConstant * ENNReal.ofReal rho₀.1

/--
Build the pure finite schedule directly from actual-John witnesses.  The
geometric grid uses ratio `ambientConstant`; one ambient window is paid when
rounding a requested scale to the grid and a second one when taking its
nearby witness.
-/
theorem paper_pure_finite_nearby_schedule
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant outputConstant : ENNReal}
    (levelCount : ℕ)
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    (hambientTwo : 2 < ambientConstant)
    (hambientTop : ambientConstant ≠ ⊤)
    (hlevels :
      ENNReal.ofReal (1 / delta) ≤
        ambientConstant ^ levelCount)
    (hwindow :
      ambientConstant * ambientConstant ≤ outputConstant)
    (hcwa :
      WZ2PaperPureCWAAtNearbyScales fine ambientConstant) :
    Nonempty
      (WZ2PaperPureFiniteNearbyScheduleData
        (fine := fine) ambientConstant outputConstant levelCount) := by
  classical
  set c : ℝ := ambientConstant.toReal with hc_def
  have hC_eq : ambientConstant = ENNReal.ofReal c := by
    rw [ENNReal.ofReal_toReal] <;> exact hambientTop
  have htwoENN :
      ENNReal.ofReal (2 : ℝ) < ENNReal.ofReal c := by
    simpa [hC_eq] using hambientTwo
  have hc_pos : 0 < c := by
    by_contra hnot
    have hc_nonpos : c ≤ 0 := by linarith
    have hzero : ENNReal.ofReal c = 0 :=
      ENNReal.ofReal_eq_zero.mpr hc_nonpos
    rw [hzero] at htwoENN
    simp at htwoENN
  have hc_two : (2 : ℝ) < c :=
    (ENNReal.ofReal_lt_ofReal_iff hc_pos).mp htwoENN
  have hc_one : (1 : ℝ) < c := by linarith
  have hpowEq : ∀ n : ℕ,
      ambientConstant ^ n = ENNReal.ofReal (c ^ n) := by
    intro n
    induction n with
    | zero => simp [hC_eq]
    | succ n ih =>
      have hmul :
          ENNReal.ofReal (c ^ n) * ENNReal.ofReal c =
            ENNReal.ofReal (c ^ (n + 1)) := by
        calc
          ENNReal.ofReal (c ^ n) * ENNReal.ofReal c =
              ENNReal.ofReal ((c ^ n) * c) := by
            rw [← ENNReal.ofReal_mul (by positivity)]
          _ = ENNReal.ofReal (c ^ (n + 1)) := by
            congr 1
      rw [pow_succ, ih, hC_eq, hmul]
  have hreachN : 1 ≤ delta * c ^ levelCount := by
    rw [hpowEq levelCount] at hlevels
    have hinverse : 1 / delta ≤ c ^ levelCount :=
      (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hlevels
    calc
      1 = delta * (1 / delta) := by
        field_simp [hdelta.ne']
      _ ≤ delta * c ^ levelCount := by gcongr
  let reaches : ℕ → Prop := fun n => 1 ≤ delta * c ^ n
  have hexists : ∃ n, reaches n := ⟨levelCount, hreachN⟩
  set topIndex : ℕ := Nat.find hexists with htop_def
  have htop : reaches topIndex := Nat.find_spec (H := hexists)
  have hbefore : ∀ n < topIndex, delta * c ^ n < 1 := by
    intro n hn
    have hnot : ¬reaches n :=
      Nat.find_min (H := hexists) (m := n) hn
    simpa [reaches] using hnot
  have htop_le : topIndex ≤ levelCount :=
    Nat.find_min' (H := hexists) (m := levelCount) hreachN
  let grid : ℕ → ℝ := fun n => min (delta * c ^ n) 1
  have hgridTop : grid topIndex = 1 :=
    min_eq_right htop
  have hgridBefore : ∀ n < topIndex,
      grid n = delta * c ^ n := by
    intro n hn
    exact min_eq_left (hbefore n hn).le
  have hgridZero : grid 0 = delta := by
    simp [grid, hdeltaOne]
  have hdeltaGrid : ∀ n, delta ≤ grid n := by
    intro n
    have hpowOne : 1 ≤ c ^ n := by
      exact one_le_pow₀ (by linarith)
    apply le_min
    · nlinarith
    · exact hdeltaOne
  have hgridOne : ∀ n, grid n ≤ 1 := by
    intro n
    exact min_le_right _ _
  let scaleCount : ℕ := topIndex + 1
  have hscaleCountPos : 0 < scaleCount := by
    simp [scaleCount]
  have hscaleCountLe : scaleCount ≤ levelCount + 1 := by
    simp [scaleCount, htop_le]
  let requested : Fin scaleCount → WZ2PaperRequestedScale delta :=
    fun coordinate =>
      ⟨grid coordinate.val,
        hdeltaGrid coordinate.val, hgridOne coordinate.val⟩
  let witness : ∀ coordinate : Fin scaleCount,
      WZ2PaperPureNearbyScaleCoverData
        fine (requested coordinate) ambientConstant :=
    fun coordinate =>
      Classical.choice (hcwa.2.2.2 (requested coordinate))
  let isAbove (rho₀ : WZ2PaperRequestedScale delta) : ℕ → Prop :=
    fun n => rho₀.1 ≤ grid n
  have htopAbove : ∀ rho₀, isAbove rho₀ topIndex := by
    intro rho₀
    dsimp only [isAbove]
    rw [hgridTop]
    exact rho₀.2.2
  let representativeIndex (rho₀ : WZ2PaperRequestedScale delta) : ℕ :=
    Nat.find ⟨topIndex, htopAbove rho₀⟩
  have hrepresentativeSpec : ∀ rho₀,
      rho₀.1 ≤ grid (representativeIndex rho₀) := by
    intro rho₀
    let hnonempty : ∃ n, isAbove rho₀ n :=
      ⟨topIndex, htopAbove rho₀⟩
    exact Nat.find_spec (H := hnonempty)
  have hrepresentativeMin : ∀ rho₀ n,
      n < representativeIndex rho₀ → grid n < rho₀.1 := by
    intro rho₀ n hn
    let hnonempty : ∃ m, isAbove rho₀ m :=
      ⟨topIndex, htopAbove rho₀⟩
    have hnot : ¬isAbove rho₀ n :=
      Nat.find_min (H := hnonempty) (m := n) hn
    simpa [isAbove] using hnot
  have hrepresentativeLe : ∀ rho₀,
      representativeIndex rho₀ ≤ topIndex := by
    intro rho₀
    let hnonempty : ∃ n, isAbove rho₀ n :=
      ⟨topIndex, htopAbove rho₀⟩
    exact Nat.find_min' (H := hnonempty)
      (m := topIndex) (htopAbove rho₀)
  have hgridWithin : ∀ rho₀,
      grid (representativeIndex rho₀) < c * rho₀.1 := by
    intro rho₀
    set index := representativeIndex rho₀ with hindexDef
    have hindexLe : index ≤ topIndex := hrepresentativeLe rho₀
    by_cases hindexZero : index = 0
    · have hrhoLe : rho₀.1 ≤ grid index :=
        hrepresentativeSpec rho₀
      rw [hindexZero, hgridZero] at hrhoLe
      have hrhoEq : rho₀.1 = delta := by
        exact le_antisymm hrhoLe rho₀.2.1
      rw [hindexZero, hgridZero, hrhoEq]
      nlinarith
    · have hindexPos : 0 < index := by omega
      have hprevious : grid (index - 1) < rho₀.1 :=
        hrepresentativeMin rho₀ (index - 1) (by omega)
      have hpreviousBefore : index - 1 < topIndex := by omega
      rw [hgridBefore (index - 1) hpreviousBefore] at hprevious
      by_cases hindexTop : index < topIndex
      · rw [hgridBefore index hindexTop]
        have hpower :
            delta * c ^ index =
              c * (delta * c ^ (index - 1)) := by
          have hsucc : index = (index - 1) + 1 := by omega
          conv_lhs => rw [hsucc, pow_succ]
          ring
        rw [hpower]
        exact mul_lt_mul_of_pos_left hprevious hc_pos
      · have hindexEq : index = topIndex := by omega
        rw [hindexEq, hgridTop]
        have htopPos : 0 < topIndex := by omega
        have hpreviousTop :
            delta * c ^ (topIndex - 1) < rho₀.1 := by
          simpa [hindexEq] using hprevious
        have hpower :
            c * (delta * c ^ (topIndex - 1)) =
              delta * c ^ topIndex := by
          have hsucc : topIndex = (topIndex - 1) + 1 := by omega
          conv_rhs => rw [hsucc, pow_succ]
          ring
        have hlt :
            delta * c ^ topIndex < c * rho₀.1 := by
          rw [← hpower]
          exact mul_lt_mul_of_pos_left hpreviousTop hc_pos
        exact lt_of_le_of_lt htop hlt
  have hrepresentativeLt : ∀ rho₀,
      representativeIndex rho₀ < scaleCount := by
    intro rho₀
    dsimp only [scaleCount]
    have hle := hrepresentativeLe rho₀
    omega
  let representative :
      WZ2PaperRequestedScale delta → Fin scaleCount :=
    fun rho₀ =>
      ⟨representativeIndex rho₀, hrepresentativeLt rho₀⟩
  have hrequestedLe : ∀ rho₀,
      rho₀.1 ≤ (witness (representative rho₀)).rho := by
    intro rho₀
    exact (hrepresentativeSpec rho₀).trans
      (witness (representative rho₀)).requested_le
  have hwithinOutput : ∀ rho₀,
      ENNReal.ofReal (witness (representative rho₀)).rho <
        outputConstant * ENNReal.ofReal rho₀.1 := by
    intro rho₀
    have hwitnessWindow :=
      (witness (representative rho₀)).within_factor
    have hgridWindowReal :
        (requested (representative rho₀)).1 < c * rho₀.1 := by
      simpa [requested, representative] using hgridWithin rho₀
    have hrhoPos : 0 < rho₀.1 :=
      hdelta.trans_le rho₀.2.1
    have hgridWindow :
        ENNReal.ofReal (requested (representative rho₀)).1 <
          ambientConstant * ENNReal.ofReal rho₀.1 := by
      have hright : 0 < c * rho₀.1 := by positivity
      have h :=
        (ENNReal.ofReal_lt_ofReal_iff hright).mpr hgridWindowReal
      rw [ENNReal.ofReal_mul (by positivity), ← hC_eq] at h
      exact h
    calc
      ENNReal.ofReal (witness (representative rho₀)).rho <
          ambientConstant *
            ENNReal.ofReal (requested (representative rho₀)).1 :=
        hwitnessWindow
      _ < ambientConstant *
            (ambientConstant * ENNReal.ofReal rho₀.1) := by
        have hmul := ENNReal.mul_lt_mul_left
          (by
            have hpos : 0 < ambientConstant :=
              (show (0 : ENNReal) < 2 by norm_num).trans hambientTwo
            exact hpos.ne') hambientTop hgridWindow
        simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
      _ = (ambientConstant * ambientConstant) *
            ENNReal.ofReal rho₀.1 := by ring
      _ ≤ outputConstant * ENNReal.ofReal rho₀.1 := by gcongr
  exact
    ⟨{
      scaleCount := scaleCount
      scaleCount_pos := hscaleCountPos
      scaleCount_le := hscaleCountLe
      requested := requested
      witness := witness
      representative := representative
      requested_le := hrequestedLe
      within_output := hwithinOutput
    }⟩

end Kakeya.Assouad

end
