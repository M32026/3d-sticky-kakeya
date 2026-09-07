import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyInputs
import MyLeanRepo.Kakeya.Cinematic.Targets.CoarseRectangleCount.MidpointPacking
import MyLeanRepo.Kakeya.Cinematic.Targets.RectanglePacking
import MyLeanRepo.Kakeya.Cinematic.Targets.RectangleRefinement.ShrinkingPreservesIncomparability

/-!
# Midpoint bounds for the large-ratio branch

These estimates use only the frozen rectangle geometry.  In particular, the
central-quarter arguments use the corrected ambient-clipped
`centeredCarrier` semantics through `central_quarter_length_bound`.
-/

noncomputable section

namespace Kakeya.Cinematic

open Classical Set Finset

lemma shared_tangent_close_midpoints_comparable
    {delta t : ℝ} (hdelta : 0 < delta) (hdt : delta ≤ t)
    (h100 : 100 * delta ≤ t)
    {family : Set C2Function} {w : C2Function} (hw : w ∈ family)
    {R S : CurvilinearRectangle delta t}
    (hRt : R.IsLambdaTangent w 5) (hSt : S.IsLambdaTangent w 5)
    (hmid : |R.interval.midpoint - S.interval.midpoint| ≤
      9 * Real.sqrt (delta / t)) :
    R.AreLambdaComparable S family 100 := by
  let L := Real.sqrt (delta / t)
  have ht : 0 < t := lt_of_lt_of_le hdelta hdt
  have hL_nonneg : 0 ≤ L := Real.sqrt_nonneg _
  have hR_len : R.interval.length = L := R.interval_length
  have hS_len : S.interval.length = L := S.interval_length
  let a := min R.interval.left S.interval.left
  let b := max R.interval.right S.interval.right
  have ha0 : 0 ≤ a :=
    le_min R.interval.left_mem.1 S.interval.left_mem.1
  have hb1 : b ≤ 1 :=
    max_le R.interval.right_mem.2 S.interval.right_mem.2
  have hab : a ≤ b :=
    (min_le_left _ _).trans
      (R.interval.left_le_right.trans (le_max_left _ _))
  have hR_left :
      R.interval.left = R.interval.midpoint - L / 2 := by
    have hlen : R.interval.right - R.interval.left = L := by
      simpa [ParameterInterval.length] using hR_len
    simp only [ParameterInterval.midpoint]
    linarith
  have hR_right :
      R.interval.right = R.interval.midpoint + L / 2 := by
    have hlen : R.interval.right - R.interval.left = L := by
      simpa [ParameterInterval.length] using hR_len
    rw [hR_left] at hlen
    linarith
  have hS_left :
      S.interval.left = S.interval.midpoint - L / 2 := by
    have hlen : S.interval.right - S.interval.left = L := by
      simpa [ParameterInterval.length] using hS_len
    simp only [ParameterInterval.midpoint]
    linarith
  have hS_right :
      S.interval.right = S.interval.midpoint + L / 2 := by
    have hlen : S.interval.right - S.interval.left = L := by
      simpa [ParameterInterval.length] using hS_len
    rw [hS_left] at hlen
    linarith
  have hhull : b - a ≤ 10 * L := by
    by_cases h : R.interval.midpoint ≤ S.interval.midpoint
    · have hleft : R.interval.left ≤ S.interval.left := by
        rw [hR_left, hS_left]
        linarith
      have hright : R.interval.right ≤ S.interval.right := by
        rw [hR_right, hS_right]
        linarith
      rw [show a = R.interval.left by simp [a, hleft],
        show b = S.interval.right by simp [b, hright],
        hR_left, hS_right]
      have habs :
          |R.interval.midpoint - S.interval.midpoint| =
            S.interval.midpoint - R.interval.midpoint := by
        rw [abs_of_nonpos (sub_nonpos.mpr h)]
        ring
      linarith
    · have h' : S.interval.midpoint ≤ R.interval.midpoint := by
        linarith
      have hleft : S.interval.left ≤ R.interval.left := by
        rw [hR_left, hS_left]
        linarith
      have hright : S.interval.right ≤ R.interval.right := by
        rw [hR_right, hS_right]
        linarith
      rw [show a = S.interval.left by simp [a, hleft],
        show b = R.interval.right by simp [b, hright],
        hS_left, hR_right]
      have habs :
          |R.interval.midpoint - S.interval.midpoint| =
            R.interval.midpoint - S.interval.midpoint := by
        rw [abs_of_nonneg]
        linarith
      linarith
  let targetLength := Real.sqrt ((100 * delta) / t)
  have htarget : targetLength = 10 * L := by
    dsimp only [targetLength, L]
    calc
      Real.sqrt ((100 * delta) / t) =
          Real.sqrt (100 * (delta / t)) := by congr 1 <;> ring
      _ = Real.sqrt 100 * Real.sqrt (delta / t) := by
        rw [Real.sqrt_mul (by norm_num)]
      _ = 10 * Real.sqrt (delta / t) := by
        have hsqrt : Real.sqrt (100 : ℝ) = 10 := by
          rw [Real.sqrt_eq_cases] <;> norm_num
        rw [hsqrt]
  have htarget_le_one : targetLength ≤ 1 := by
    rw [htarget]
    have hsq : L ^ 2 = delta / t :=
      Real.sq_sqrt (by positivity)
    have hratio : 100 * (delta / t) ≤ 1 := by
      rw [show 100 * (delta / t) = (100 * delta) / t by ring]
      exact (div_le_one ht).2 h100
    nlinarith
  obtain ⟨J, hJa, hJb, hJlen⟩ :=
    enclosing_interval_exists ha0 hb1 hab
      (hhull.trans_eq htarget.symm) htarget_le_one
  let U : CurvilinearRectangle (100 * delta) t :=
    { function := w
      interval := J
      interval_length := by
        simpa [targetLength] using hJlen }
  have hRsub : R.carrier ⊆ U.carrier := by
    intro p hp
    have hpJ : p.1 ∈ J.carrier := by
      exact ⟨hJa.trans (min_le_left _ _ |>.trans hp.1.1),
        hp.1.2.trans (le_max_left _ _ |>.trans hJb)⟩
    exact ⟨hpJ, (hRt p hp).trans (by nlinarith [hdelta])⟩
  have hSsub : S.carrier ⊆ U.carrier := by
    intro p hp
    have hpJ : p.1 ∈ J.carrier := by
      exact ⟨hJa.trans (min_le_right _ _ |>.trans hp.1.1),
        hp.1.2.trans (le_max_right _ _ |>.trans hJb)⟩
    exact ⟨hpJ, (hSt p hp).trans (by nlinarith [hdelta])⟩
  exact ⟨U, hw, Set.union_subset hRsub hSsub⟩

lemma hundred_delta_le_t_from_central_quarter
    {K : ℝ} (hK : 1 ≤ K)
    {I : ParameterInterval} (hI : I.IsControlled K)
    {delta t : ℝ} (hdelta : 0 < delta) (ht : 0 < t)
    {R : CurvilinearRectangle delta t}
    (hRquarter : R.IsOverCentralQuarterOf I) :
    100 * delta ≤ t := by
  have hlength : R.interval.length ≤ I.length / 4 :=
    central_quarter_length_bound hRquarter
  have hshort : I.length ≤ (6 * K)⁻¹ := hI.2
  have hsqrt : Real.sqrt (delta / t) ≤ 1 / (24 * K) := by
    rw [← R.interval_length]
    calc
      R.interval.length ≤ I.length / 4 := hlength
      _ ≤ (6 * K)⁻¹ / 4 := by gcongr
      _ = 1 / (24 * K) := by
        field_simp [show 6 * K ≠ 0 by linarith]
        ring
  have hratio : delta / t ≤ 1 / 100 := by
    have hsquare :
        delta / t ≤ (1 / (24 * K)) ^ 2 := by
      rw [← Real.sq_sqrt (show 0 ≤ delta / t by positivity)]
      gcongr
    have hconstant : (1 / (24 * K)) ^ 2 ≤ 1 / 100 := by
      have : 100 ≤ (24 * K) ^ 2 := by nlinarith
      have hpos : 0 < (24 * K) ^ 2 := by positivity
      rw [show (1 / (24 * K)) ^ 2 = 1 / (24 * K) ^ 2 by ring]
      exact (div_le_div_iff_of_pos_left (by norm_num) hpos
        (by norm_num : (0 : ℝ) < 100)).2 this
    exact hsquare.trans hconstant
  apply (div_le_one ht).mp
  calc
    100 * delta / t = 100 * (delta / t) := by ring
    _ ≤ 100 * (1 / 100 : ℝ) := by gcongr
    _ = 1 := by norm_num

lemma rectangle_midpoint_in_centered_range
    {I : ParameterInterval} {delta t : ℝ}
    {R : CurvilinearRectangle delta t}
    (hRquarter : R.IsOverCentralQuarterOf I) :
    |R.interval.midpoint - I.midpoint| ≤ I.length / 8 := by
  let leftPoint : UnitPoint :=
    ⟨R.interval.left, R.interval.left_mem⟩
  let rightPoint : UnitPoint :=
    ⟨R.interval.right, R.interval.right_mem⟩
  have hleft :
      |R.interval.left - I.midpoint| ≤ I.length / 8 := by
    have h := hRquarter
      (show leftPoint ∈ R.interval.carrier by
        exact ⟨le_rfl, R.interval.left_le_right⟩)
    change |R.interval.left - I.midpoint| ≤
      (1 / 4 : ℝ) * I.length / 2 at h
    convert h using 1 <;> ring
  have hright :
      |R.interval.right - I.midpoint| ≤ I.length / 8 := by
    have h := hRquarter
      (show rightPoint ∈ R.interval.carrier by
        exact ⟨R.interval.left_le_right, le_rfl⟩)
    change |R.interval.right - I.midpoint| ≤
      (1 / 4 : ℝ) * I.length / 2 at h
    convert h using 1 <;> ring
  simp only [ParameterInterval.midpoint]
  calc
    |(R.interval.left + R.interval.right) / 2 -
        (I.left + I.right) / 2| =
        |(R.interval.left - I.midpoint) / 2 +
          (R.interval.right - I.midpoint) / 2| := by
      simp [ParameterInterval.midpoint]
      ring_nf
    _ ≤ |R.interval.left - I.midpoint| / 2 +
        |R.interval.right - I.midpoint| / 2 := by
      simpa [abs_div] using abs_add_le
        ((R.interval.left - I.midpoint) / 2)
        ((R.interval.right - I.midpoint) / 2)
    _ ≤ I.length / 8 / 2 + I.length / 8 / 2 := by gcongr
    _ = I.length / 8 := by ring

lemma w_only_midpoint_bound
    {K : ℝ} (hK : 1 ≤ K)
    {family : Set C2Function}
    {I : ParameterInterval} (hI : I.IsControlled K)
    {delta t : ℝ} (hdelta : 0 < delta) (ht : 0 < t)
    (hdt : delta ≤ t)
    {W : FiniteFunctionFamily} (hW : W.carrier ⊆ family)
    {R : RectangleFamily delta t}
    (hRquarter : R.IsOverCentralQuarterOf I)
    (hR100 : R.IsPairwiseIncomparable family 100)
    {mu : ℕ} (hmu : 0 < mu)
    (hcounts : ∀ i,
      mu ≤ RectangleFamily.tangentCount (R.rectangle i) W 5) :
    (R.card : ℝ) ≤
      2 * Real.sqrt (t / delta) * (W.card : ℝ) / (mu : ℝ) := by
  classical
  by_cases hR0 : R.card = 0
  · rw [hR0]
    simp only [Nat.cast_zero]
    positivity
  let firstIndex : Fin R.card := ⟨0, Nat.pos_of_ne_zero hR0⟩
  let spacing : ℝ := 9 * Real.sqrt (delta / t)
  have hspacing : 0 < spacing := by positivity
  have h100 : 100 * delta ≤ t :=
    hundred_delta_le_t_from_central_quarter hK hI hdelta ht
      (hRquarter firstIndex)
  let tangentIndices (w : C2Function) : Finset (Fin R.card) :=
    Finset.univ.filter
      (fun i => (R.rectangle i).IsLambdaTangent w 5)
  let midpoints (w : C2Function) : Finset ℝ :=
    (tangentIndices w).image
      (fun i => (R.rectangle i).interval.midpoint)
  let leftEnd := I.midpoint - I.length / 8
  let rightEnd := I.midpoint + I.length / 8
  have hend : leftEnd ≤ rightEnd := by
    dsimp only [leftEnd, rightEnd]
    linarith [I.length_nonneg]
  have hmid_range : ∀ i : Fin R.card,
      (R.rectangle i).interval.midpoint ∈ Set.Icc leftEnd rightEnd := by
    intro i
    have h := abs_le.mp
      (rectangle_midpoint_in_centered_range (hRquarter i))
    exact ⟨by dsimp only [leftEnd]; linarith,
      by dsimp only [rightEnd]; linarith⟩
  have hsep : ∀ w ∈ W.toFinset, ∀ x ∈ midpoints w,
      ∀ y ∈ midpoints w, x ≠ y → spacing < |x - y| := by
    intro w hw x hx y hy hxy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
    have hij : i ≠ j := by
      intro h
      exact hxy (congrArg (fun k =>
        (R.rectangle k).interval.midpoint) h)
    have hitan :
        (R.rectangle i).IsLambdaTangent w 5 :=
      (Finset.mem_filter.mp hi).2
    have hjtan :
        (R.rectangle j).IsLambdaTangent w 5 :=
      (Finset.mem_filter.mp hj).2
    have hwf : w ∈ family :=
      hW (W.finite.mem_toFinset.mp hw)
    by_contra h
    have hclose :
        |(R.rectangle i).interval.midpoint -
          (R.rectangle j).interval.midpoint| ≤ spacing := by
      simpa [not_lt] using h
    exact hR100 i j hij
      (shared_tangent_close_midpoints_comparable
        hdelta hdt h100 hwf hitan hjtan hclose)
  have hmid_sub : ∀ w, ∀ x ∈ midpoints w,
      x ∈ Set.Icc leftEnd rightEnd := by
    intro w x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact hmid_range i
  have hpack : ∀ w ∈ W.toFinset,
      ((midpoints w).card : ℝ) ≤
        (rightEnd - leftEnd) / spacing + 1 := by
    intro w hw
    exact midpoint_packing_bound hspacing hend
      (midpoints w) (hmid_sub w) (hsep w hw)
  have hinjective : ∀ w ∈ W.toFinset,
      Set.InjOn
        (fun i : Fin R.card =>
          (R.rectangle i).interval.midpoint)
        (tangentIndices w) := by
    intro w hw i hi j hj heq
    by_contra hij
    have hwf : w ∈ family :=
      hW (W.finite.mem_toFinset.mp hw)
    have hclose :
        |(R.rectangle i).interval.midpoint -
          (R.rectangle j).interval.midpoint| ≤ spacing := by
      change (R.rectangle i).interval.midpoint =
        (R.rectangle j).interval.midpoint at heq
      rw [heq]
      simp
      positivity
    exact hR100 i j hij
      (shared_tangent_close_midpoints_comparable hdelta hdt h100 hwf
        (Finset.mem_filter.mp hi).2
        (Finset.mem_filter.mp hj).2 hclose)
  have hmid_card : ∀ w ∈ W.toFinset,
      (midpoints w).card = (tangentIndices w).card := by
    intro w hw
    exact Finset.card_image_of_injOn (hinjective w hw)
  have hdouble_count :
      ∑ i : Fin R.card,
          RectangleFamily.tangentCount (R.rectangle i) W 5 =
        ∑ w ∈ W.toFinset, (tangentIndices w).card := by
    have hi : ∀ i : Fin R.card,
        RectangleFamily.tangentCount (R.rectangle i) W 5 =
          ∑ w ∈ W.toFinset,
            if (R.rectangle i).IsLambdaTangent w 5 then 1 else 0 := by
      intro i
      simp [RectangleFamily.tangentCount, Finset.filter_eq']
    have hw : ∀ w : C2Function,
        (tangentIndices w).card =
          ∑ i : Fin R.card,
            if (R.rectangle i).IsLambdaTangent w 5 then 1 else 0 := by
      intro w
      simp [tangentIndices, Finset.filter_eq']
    calc
      ∑ i : Fin R.card,
          RectangleFamily.tangentCount (R.rectangle i) W 5 =
          ∑ i : Fin R.card, ∑ w ∈ W.toFinset,
            if (R.rectangle i).IsLambdaTangent w 5 then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        exact hi i
      _ = ∑ w ∈ W.toFinset, ∑ i : Fin R.card,
            if (R.rectangle i).IsLambdaTangent w 5 then 1 else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ w ∈ W.toFinset, (tangentIndices w).card := by
        apply Finset.sum_congr rfl
        intro w _
        exact (hw w).symm
  have hlower :
      R.card * mu ≤
        ∑ i : Fin R.card,
          RectangleFamily.tangentCount (R.rectangle i) W 5 := by
    calc
      R.card * mu = ∑ _i : Fin R.card, mu := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i _
        exact hcounts i
  have hupper :
      (∑ w ∈ W.toFinset, (tangentIndices w).card : ℝ) ≤
        (W.toFinset.card : ℝ) *
          ((rightEnd - leftEnd) / spacing + 1) := by
    calc
      (∑ w ∈ W.toFinset, (tangentIndices w).card : ℝ) =
          ∑ w ∈ W.toFinset, ((midpoints w).card : ℝ) := by
        exact_mod_cast Finset.sum_congr rfl
          (fun w hw => (hmid_card w hw).symm)
      _ ≤ ∑ _w ∈ W.toFinset,
          ((rightEnd - leftEnd) / spacing + 1) := by
        apply Finset.sum_le_sum
        intro w hw
        exact hpack w hw
      _ = _ := by
        simp [Finset.sum_const]
        ring
  have hfactor :
      (rightEnd - leftEnd) / spacing + 1 ≤
        2 * Real.sqrt (t / delta) := by
    have hlength : rightEnd - leftEnd = I.length / 4 := by
      simp [rightEnd, leftEnd]
      ring
    rw [hlength]
    let x := Real.sqrt (delta / t)
    have hx : 0 < x := by positivity
    have hx_bound : x ≤ 1 / (24 * K) := by
      have hlen := central_quarter_length_bound
        (hRquarter firstIndex)
      rw [(R.rectangle firstIndex).interval_length] at hlen
      calc
        x ≤ I.length / 4 := hlen
        _ ≤ (6 * K)⁻¹ / 4 := by
          gcongr
          exact hI.2
        _ = 1 / (24 * K) := by
          field_simp [show 6 * K ≠ 0 by linarith]
          ring
    have hs : spacing = 9 * x := rfl
    rw [hs]
    have hinverse : Real.sqrt (t / delta) = 1 / x := by
      have hproduct :
          Real.sqrt (t / delta) * Real.sqrt (delta / t) = 1 := by
        rw [← Real.sqrt_mul (by positivity)]
        have hratio : (t / delta) * (delta / t) = 1 := by
          field_simp [hdelta.ne', ht.ne']
        rw [hratio]
        norm_num
      have hproduct' : Real.sqrt (t / delta) * x = 1 := by
        simpa [x] using hproduct
      field_simp [hx.ne']
      linarith [hproduct']
    rw [hinverse]
    have hlength_bound : I.length / 4 ≤ 1 / (24 * K) := by
      calc
        I.length / 4 ≤ (6 * K)⁻¹ / 4 := by
          gcongr
          exact hI.2
        _ = 1 / (24 * K) := by
          field_simp [show 6 * K ≠ 0 by linarith]
          ring
    have hsmall : 1 / (216 * K) + x ≤ 2 := by
      have hx' : x ≤ 1 / 24 := by
        exact hx_bound.trans (by
          apply one_div_le_one_div_of_le <;> nlinarith)
      have hconst : 1 / (216 * K) ≤ 1 / 216 := by
        apply one_div_le_one_div_of_le <;> nlinarith
      linarith
    calc
      (I.length / 4) / (9 * x) + 1 ≤
          (1 / (24 * K)) / (9 * x) + 1 := by gcongr
      _ = (1 / (216 * K) + x) / x := by
        field_simp [hx.ne']
        ring
      _ ≤ 2 / x := by gcongr
      _ = 2 * (1 / x) := by ring
  have hWcard : W.toFinset.card = W.card :=
    (Set.ncard_eq_toFinset_card W.carrier W.finite).symm
  have hincidence :
      (R.card : ℝ) * (mu : ℝ) ≤
        (W.card : ℝ) *
          ((rightEnd - leftEnd) / spacing + 1) := by
    have hlower' :
        ((R.card * mu : ℕ) : ℝ) ≤
          (∑ i : Fin R.card,
            RectangleFamily.tangentCount (R.rectangle i) W 5 : ℕ) := by
      exact_mod_cast hlower
    rw [hdouble_count] at hlower'
    have hupper' :
        (∑ w ∈ W.toFinset, (tangentIndices w).card : ℝ) ≤
          (W.card : ℝ) *
            ((rightEnd - leftEnd) / spacing + 1) := by
      simpa [hWcard] using hupper
    have hdouble_real :
        ((∑ w ∈ W.toFinset, (tangentIndices w).card : ℕ) : ℝ) =
          ∑ w ∈ W.toFinset, ((tangentIndices w).card : ℝ) := by
      simp
    rw [hdouble_real] at hlower'
    simpa using hlower'.trans hupper'
  have hmu_real : (0 : ℝ) < (mu : ℝ) := by exact_mod_cast hmu
  have hproduct :
      (R.card : ℝ) * (mu : ℝ) ≤
        2 * Real.sqrt (t / delta) * (W.card : ℝ) := by
    calc
      (R.card : ℝ) * (mu : ℝ) ≤
          (W.card : ℝ) *
            ((rightEnd - leftEnd) / spacing + 1) := hincidence
      _ ≤ (W.card : ℝ) * (2 * Real.sqrt (t / delta)) := by
        gcongr
      _ = 2 * Real.sqrt (t / delta) * (W.card : ℝ) := by ring
  calc
    (R.card : ℝ) =
        ((R.card : ℝ) * (mu : ℝ)) / (mu : ℝ) := by
      field_simp [hmu_real.ne']
    _ ≤ (2 * Real.sqrt (t / delta) * (W.card : ℝ)) /
        (mu : ℝ) := by gcongr

end Kakeya.Cinematic
