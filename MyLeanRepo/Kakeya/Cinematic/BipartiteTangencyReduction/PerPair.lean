import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyInputs
import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.Midpoint
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Uniform bound for one tangent pair

For a fixed separated pair `(w,b)`, tangency geometry confines all common
tangent rectangle intervals to at most two short components.  Pairwise
incomparability makes those intervals disjoint, giving an `O_K(sqrt A)`
bound with no dependence on `delta` or `t`.
-/

noncomputable section

namespace Kakeya.Cinematic

open Classical Set Finset

private lemma enclosing_interval_of_length
    (a b L : ℝ) (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a ≤ b)
    (hL : 0 < L) (hL_one : L ≤ 1) (hull : b - a ≤ L) :
    ∃ J : ParameterInterval,
      J.length = L ∧ J.left ≤ a ∧ b ≤ J.right := by
  obtain ⟨J, hJa, hJb, hJlen⟩ :=
    enclosing_interval_exists ha hb hab hull hL_one
  exact ⟨J, hJlen, hJa, hJb⟩

lemma common_tangent_overlap_comparable
    {family : Set C2Function} {delta t Cc : ℝ}
    (hdelta : 0 < delta) (ht : 0 < t)
    (hCc : 10 ≤ Cc) (hadm : Cc * delta ≤ t)
    {w : C2Function} (hw : w ∈ family)
    {R S : CurvilinearRectangle delta t}
    (hRt : R.IsLambdaTangent w 5)
    (hSt : S.IsLambdaTangent w 5)
    (hoverlap :
      (R.interval.carrier ∩ S.interval.carrier).Nonempty) :
    R.AreLambdaComparable S family Cc := by
  let targetLength := Real.sqrt (Cc * delta / t)
  have htarget : 0 < targetLength := by positivity
  have htarget_one : targetLength ≤ 1 := by
    apply Real.sqrt_le_one.mpr
    exact (div_le_one ht).2 hadm
  let a := min R.interval.left S.interval.left
  let b := max R.interval.right S.interval.right
  have ha : 0 ≤ a :=
    le_min R.interval.left_mem.1 S.interval.left_mem.1
  have hb : b ≤ 1 :=
    max_le R.interval.right_mem.2 S.interval.right_mem.2
  have hab : a ≤ b :=
    (min_le_left _ _).trans
      (R.interval.left_le_right.trans (le_max_left _ _))
  obtain ⟨x, hxR, hxS⟩ := hoverlap
  have hhull : b - a ≤ 2 * Real.sqrt (delta / t) := by
    have hright : b - (x : ℝ) ≤ Real.sqrt (delta / t) := by
      have hR :
          R.interval.right - (x : ℝ) ≤ R.interval.length := by
        change R.interval.right - (x : ℝ) ≤
          R.interval.right - R.interval.left
        linarith [hxR.1]
      have hS :
          S.interval.right - (x : ℝ) ≤ S.interval.length := by
        change S.interval.right - (x : ℝ) ≤
          S.interval.right - S.interval.left
        linarith [hxS.1]
      rw [R.interval_length] at hR
      rw [S.interval_length] at hS
      rcases max_choice R.interval.right S.interval.right with h | h
      · rw [show b = R.interval.right by exact h]
        exact hR
      · rw [show b = S.interval.right by exact h]
        exact hS
    have hleft : (x : ℝ) - a ≤ Real.sqrt (delta / t) := by
      have hR :
          (x : ℝ) - R.interval.left ≤ R.interval.length := by
        change (x : ℝ) - R.interval.left ≤
          R.interval.right - R.interval.left
        linarith [hxR.2]
      have hS :
          (x : ℝ) - S.interval.left ≤ S.interval.length := by
        change (x : ℝ) - S.interval.left ≤
          S.interval.right - S.interval.left
        linarith [hxS.2]
      rw [R.interval_length] at hR
      rw [S.interval_length] at hS
      rcases min_choice R.interval.left S.interval.left with h | h
      · rw [show a = R.interval.left by exact h]
        exact hR
      · rw [show a = S.interval.left by exact h]
        exact hS
    linarith
  have hhull_target : b - a ≤ targetLength := by
    have hsqrtCc : 2 ≤ Real.sqrt Cc := by
      exact Real.le_sqrt_of_sq_le (by nlinarith)
    calc
      b - a ≤ 2 * Real.sqrt (delta / t) := hhull
      _ ≤ Real.sqrt Cc * Real.sqrt (delta / t) := by gcongr
      _ = targetLength := by
        dsimp only [targetLength]
        rw [← Real.sqrt_mul] <;> ring_nf <;> positivity
  obtain ⟨J, hJlen, hJa, hJb⟩ :=
    enclosing_interval_of_length a b targetLength ha hb hab
      htarget htarget_one hhull_target
  let U : CurvilinearRectangle (Cc * delta) t :=
    { function := w
      interval := J
      interval_length := hJlen }
  have hRsub : R.carrier ⊆ U.carrier := by
    intro p hp
    have hpJ : p.1 ∈ J.carrier := by
      exact ⟨hJa.trans ((min_le_left _ _).trans hp.1.1),
        hp.1.2.trans ((le_max_left _ _).trans hJb)⟩
    exact ⟨hpJ, (hRt p hp).trans (by
      have : 5 * delta ≤ Cc * delta := by gcongr <;> linarith
      exact this)⟩
  have hSsub : S.carrier ⊆ U.carrier := by
    intro p hp
    have hpJ : p.1 ∈ J.carrier := by
      exact ⟨hJa.trans ((min_le_right _ _).trans hp.1.1),
        hp.1.2.trans ((le_max_right _ _).trans hJb)⟩
    exact ⟨hpJ, (hSt p hp).trans (by
      have : 5 * delta ≤ Cc * delta := by gcongr <;> linarith
      exact this)⟩
  exact ⟨U, hw, Set.union_subset hRsub hSsub⟩

lemma fixed_pair_tangent_bound
    {K D : ℝ} (hK : 1 ≤ K) (hD : 1 ≤ D)
    {family : Set C2Function}
    (hfamily : IsCinematicFamily family K D)
    {I : ParameterInterval} (hI : I.IsControlled K)
    {delta t A : ℝ} (hdelta : 0 < delta) (ht : 0 < t)
    (hA : 1 ≤ A)
    (hsmall : delta / t ≤ 1 / (60 * K * A))
    {Cc : ℝ} (hCc : 100 ≤ Cc) (hadm : Cc * delta ≤ t)
    {w b : C2Function} (hw : w ∈ family) (hb : b ∈ family)
    (hwb : w ≠ b) (hsep : t / A ≤ c2Distance w b)
    (hTangency : TangencyGeometryCompletionStatement)
    {R : RectangleFamily delta t}
    (hRquarter : R.IsOverCentralQuarterOf I)
    (hRincomp : R.IsPairwiseIncomparable family Cc)
    (hcounts : ∀ i,
      (R.rectangle i).IsLambdaTangent w 5 ∧
        (R.rectangle i).IsLambdaTangent b 5) :
    ∃ C_pair : ℝ, 0 < C_pair ∧
      (R.card : ℝ) ≤ C_pair * Real.sqrt A := by
  obtain ⟨C_geometry, hC_geometry, hgeometry⟩ :=
    hTangency K D hK hD
  let enlargedDelta := 10 * delta
  have henlarged : 0 < enlargedDelta := by positivity
  have hdist : 0 < c2Distance w b := by
    have : 0 < t / A := by positivity
    linarith
  have hscale : enlargedDelta ≤ c2Distance w b / (6 * K) := by
    have hKA : 0 < 6 * K * A := by positivity
    have hfirst : 10 * delta ≤ t / (6 * K * A) := by
      have hratio : 10 * (delta / t) ≤ 1 / (6 * K * A) := by
        calc
          10 * (delta / t) ≤
              10 * (1 / (60 * K * A)) := by gcongr
          _ = 1 / (6 * K * A) := by
            field_simp [show K ≠ 0 by linarith,
              show A ≠ 0 by linarith]
            ring
      calc
        10 * delta = 10 * (delta / t) * t := by
          field_simp [ht.ne']
        _ ≤ (1 / (6 * K * A)) * t := by gcongr
        _ = t / (6 * K * A) := by ring
    have hsecond :
        t / (6 * K * A) ≤ c2Distance w b / (6 * K) := by
      have hKpos : 0 < 6 * K := by positivity
      calc
        t / (6 * K * A) = (t / A) / (6 * K) := by ring
        _ ≤ c2Distance w b / (6 * K) := by gcongr
    exact hfirst.trans hsecond
  obtain ⟨hpieces, _hextension⟩ :=
    hgeometry family hfamily I hI w hw b hb hwb
      enlargedDelta henlarged hscale
  obtain ⟨pieces, hpieces_card, hpieces_union, hpieces_length, _⟩ :=
    hpieces
  have htangency_nonneg : 0 ≤ tangencyParameterOn I w b := by
    apply Real.sInf_nonneg
    intro value hvalue
    rcases hvalue with ⟨x, _, rfl⟩
    positivity
  have hroot_lower :
      Real.sqrt (enlargedDelta * (t / A)) ≤
        Real.sqrt
          ((tangencyParameterOn I w b + enlargedDelta) *
            c2Distance w b) := by
    apply Real.sqrt_le_sqrt
    exact mul_le_mul (by linarith) hsep (by positivity) (by positivity)
  have htotal_length :
      ∑ j : Fin pieces.card, (pieces.interval j).length ≤
        2 * C_geometry *
          Real.sqrt (enlargedDelta * A / t) := by
    calc
      ∑ j : Fin pieces.card, (pieces.interval j).length ≤
          ∑ _j : Fin pieces.card,
            C_geometry * enlargedDelta /
              Real.sqrt
                ((tangencyParameterOn I w b + enlargedDelta) *
                  c2Distance w b) := by
        apply Finset.sum_le_sum
        intro j _
        exact hpieces_length j
      _ = (pieces.card : ℝ) *
          (C_geometry * enlargedDelta /
            Real.sqrt
              ((tangencyParameterOn I w b + enlargedDelta) *
                c2Distance w b)) := by simp
      _ ≤ 2 *
          (C_geometry * enlargedDelta /
            Real.sqrt (enlargedDelta * (t / A))) := by
        have hdenom :
            0 < Real.sqrt (enlargedDelta * (t / A)) := by
          positivity
        have hquot :
            C_geometry * enlargedDelta /
                Real.sqrt
                  ((tangencyParameterOn I w b + enlargedDelta) *
                    c2Distance w b) ≤
              C_geometry * enlargedDelta /
                Real.sqrt (enlargedDelta * (t / A)) := by
          exact div_le_div_of_nonneg_left
            (mul_nonneg hC_geometry.le henlarged.le)
            hdenom hroot_lower
        have hcard_real : (pieces.card : ℝ) ≤ 2 := by
          exact_mod_cast hpieces_card
        gcongr
      _ = 2 * C_geometry *
          Real.sqrt (enlargedDelta * A / t) := by
        have hidentity :
            enlargedDelta /
                Real.sqrt (enlargedDelta * (t / A)) =
              Real.sqrt (enlargedDelta * A / t) := by
          have hleft : 0 < enlargedDelta := henlarged
          have hright : 0 < t / A := by positivity
          have hsqrt_left :
              Real.sqrt (enlargedDelta * (t / A)) =
                Real.sqrt enlargedDelta * Real.sqrt (t / A) := by
            rw [Real.sqrt_mul] <;> positivity
          rw [hsqrt_left]
          have hcancel :
              enlargedDelta / Real.sqrt enlargedDelta =
                Real.sqrt enlargedDelta := by
            have hsq := Real.sq_sqrt hleft.le
            field_simp [Real.sqrt_ne_zero'.mpr hleft]
            nlinarith
          rw [show enlargedDelta /
              (Real.sqrt enlargedDelta * Real.sqrt (t / A)) =
              (enlargedDelta / Real.sqrt enlargedDelta) /
                Real.sqrt (t / A) by ring, hcancel]
          calc
            Real.sqrt enlargedDelta / Real.sqrt (t / A) =
                Real.sqrt (enlargedDelta / (t / A)) :=
              (Real.sqrt_div hleft.le (t / A)).symm
            _ = Real.sqrt (enlargedDelta * A / t) := by
              congr 1
              field_simp [ht.ne', show A ≠ 0 by linarith]
        calc
          2 * (C_geometry * enlargedDelta /
              Real.sqrt (enlargedDelta * (t / A))) =
              2 * C_geometry *
                (enlargedDelta /
                  Real.sqrt (enlargedDelta * (t / A))) := by ring
          _ = 2 * C_geometry *
              Real.sqrt (enlargedDelta * A / t) := by rw [hidentity]
  have hintervals_sub : ∀ i,
      (R.rectangle i).interval.carrier ⊆ pieces.union := by
    intro i x hx
    have hxquarter : x ∈ I.centeredCarrier (1 / 4) :=
      hRquarter i hx
    have hpoint :
        (x, (R.rectangle i).function x) ∈
          (R.rectangle i).carrier := by
      exact ⟨hx, by simpa using hdelta.le⟩
    have hw_bound :
        |w x - (R.rectangle i).function x| ≤ 5 * delta := by
      simpa [abs_sub_comm] using (hcounts i).1 _ hpoint
    have hb_bound :
        |(R.rectangle i).function x - b x| ≤ 5 * delta :=
      (hcounts i).2 _ hpoint
    have hwb_bound : |w x - b x| ≤ enlargedDelta := by
      calc
        |w x - b x| ≤
            |w x - (R.rectangle i).function x| +
              |(R.rectangle i).function x - b x| := by
          exact abs_sub_le _ _ _
        _ ≤ 10 * delta := by linarith
        _ = enlargedDelta := rfl
    have : x ∈ tangencySublevelSetOn I w b enlargedDelta :=
      ⟨hxquarter, hwb_bound⟩
    rwa [hpieces_union] at this
  have hdisjoint : ∀ i j, i ≠ j →
      Disjoint (R.rectangle i).interval.carrier
        (R.rectangle j).interval.carrier := by
    intro i j hij
    by_contra h
    have hoverlap :
        ((R.rectangle i).interval.carrier ∩
          (R.rectangle j).interval.carrier).Nonempty :=
      Set.not_disjoint_iff.mp h
    have hcomparable :
        (R.rectangle i).AreLambdaComparable
          (R.rectangle j) family Cc :=
      common_tangent_overlap_comparable hdelta ht (by linarith)
        hadm hw (hcounts i).1 (hcounts j).1 hoverlap
    exact hRincomp i j hij hcomparable
  let realCarrier (J : ParameterInterval) : Set ℝ :=
    Set.Icc J.left J.right
  have hmeasure : ∀ J : ParameterInterval,
      MeasureTheory.volume (realCarrier J) =
        ENNReal.ofReal J.length := by
    intro J
    rw [Real.volume_Icc]
    simp [realCarrier, ParameterInterval.length,
      J.left_le_right]
  have hreal_sub : ∀ i,
      realCarrier (R.rectangle i).interval ⊆
        ⋃ j : Fin pieces.card, realCarrier (pieces.interval j) := by
    intro i x hx
    let point : UnitPoint := ⟨x, by
      exact ⟨(R.rectangle i).interval.left_mem.1.trans hx.1,
        hx.2.trans (R.rectangle i).interval.right_mem.2⟩⟩
    have hpoint :
        point ∈ (R.rectangle i).interval.carrier := hx
    obtain ⟨j, hj⟩ := hintervals_sub i hpoint
    exact Set.mem_iUnion.mpr ⟨j, hj⟩
  have hreal_disjoint : ∀ i j, i ≠ j →
      Disjoint (realCarrier (R.rectangle i).interval)
        (realCarrier (R.rectangle j).interval) := by
    intro i j hij
    by_contra h
    have hoverlap :
        (realCarrier (R.rectangle i).interval ∩
          realCarrier (R.rectangle j).interval).Nonempty :=
      Set.not_disjoint_iff.mp h
    obtain ⟨x, hxi, hxj⟩ := hoverlap
    let point : UnitPoint := ⟨x, by
      exact ⟨(R.rectangle i).interval.left_mem.1.trans hxi.1,
        hxi.2.trans (R.rectangle i).interval.right_mem.2⟩⟩
    have hpoint_i : point ∈ (R.rectangle i).interval.carrier := by
      exact hxi
    have hpoint_j : point ∈ (R.rectangle j).interval.carrier := by
      exact hxj
    exact Set.disjoint_left.mp (hdisjoint i j hij)
      hpoint_i hpoint_j
  have hmeasure_union :
      MeasureTheory.volume
          (⋃ i : Fin R.card,
            realCarrier (R.rectangle i).interval) =
        ∑ i : Fin R.card,
          MeasureTheory.volume
            (realCarrier (R.rectangle i).interval) := by
    have hmeasurable : ∀ i : Fin R.card,
        MeasurableSet (realCarrier (R.rectangle i).interval) :=
      fun _ => measurableSet_Icc
    have hpairwise :
        Set.PairwiseDisjoint
          (↑(Finset.univ : Finset (Fin R.card)))
          (fun i => realCarrier (R.rectangle i).interval) := by
      intro i _ j _ hij
      exact hreal_disjoint i j hij
    have heq :
        (⋃ i : Fin R.card,
          realCarrier (R.rectangle i).interval) =
        ⋃ i ∈ (Finset.univ : Finset (Fin R.card)),
          realCarrier (R.rectangle i).interval := by
      ext x
      simp
    rw [heq]
    exact MeasureTheory.measure_biUnion_finset hpairwise
      (fun i _ => hmeasurable i)
  have hmeasure_bound :
      ∑ i : Fin R.card,
          MeasureTheory.volume
            (realCarrier (R.rectangle i).interval) ≤
        ∑ j : Fin pieces.card,
          MeasureTheory.volume
            (realCarrier (pieces.interval j)) := by
    rw [← hmeasure_union]
    exact (MeasureTheory.measure_mono
      (Set.iUnion_subset_iff.mpr hreal_sub)).trans
        (MeasureTheory.measure_iUnion_fintype_le _ _)
  have hlength_sum :
      (R.card : ℝ) * Real.sqrt (delta / t) ≤
        ∑ j : Fin pieces.card, (pieces.interval j).length := by
    have hleft : ∑ i : Fin R.card,
        MeasureTheory.volume (realCarrier (R.rectangle i).interval) =
        ENNReal.ofReal ((R.card : ℝ) * Real.sqrt (delta / t)) := by
      have hmeasure_sum : ∑ i : Fin R.card,
          MeasureTheory.volume (realCarrier (R.rectangle i).interval) =
        ∑ i : Fin R.card,
          ENNReal.ofReal (R.rectangle i).interval.length := by
        apply Finset.sum_congr rfl
        intro i _
        exact hmeasure _
      rw [hmeasure_sum]
      have hofreal :
          ∑ i : Fin R.card,
              ENNReal.ofReal (R.rectangle i).interval.length =
            ENNReal.ofReal
              (∑ i : Fin R.card,
                (R.rectangle i).interval.length) := by
        rw [ENNReal.ofReal_sum_of_nonneg
        (fun i _ => (R.rectangle i).interval.length_nonneg)]
      rw [hofreal]
      congr 1
      simp [(R.rectangle _).interval_length]
    have hright : ∑ j : Fin pieces.card,
        MeasureTheory.volume (realCarrier (pieces.interval j)) =
      ENNReal.ofReal
        (∑ j : Fin pieces.card, (pieces.interval j).length) := by
      have hmeasure_sum : ∑ j : Fin pieces.card,
          MeasureTheory.volume (realCarrier (pieces.interval j)) =
        ∑ j : Fin pieces.card,
          ENNReal.ofReal (pieces.interval j).length := by
        apply Finset.sum_congr rfl
        intro j _
        exact hmeasure _
      rw [hmeasure_sum]
      rw [ENNReal.ofReal_sum_of_nonneg
        (fun j _ => (pieces.interval j).length_nonneg)]
    rw [hleft, hright] at hmeasure_bound
    exact (ENNReal.ofReal_le_ofReal_iff
      (Finset.sum_nonneg
        (fun j _ => (pieces.interval j).length_nonneg))).mp
          hmeasure_bound
  have hcard_scaled :
      (R.card : ℝ) * Real.sqrt (delta / t) ≤
        2 * C_geometry *
          Real.sqrt (enlargedDelta * A / t) :=
    hlength_sum.trans htotal_length
  have hsqrt_factor :
      Real.sqrt (enlargedDelta * A / t) =
        Real.sqrt 10 * Real.sqrt (delta / t) * Real.sqrt A := by
    dsimp only [enlargedDelta]
    rw [show 10 * delta * A / t =
      10 * (delta / t) * A by ring]
    rw [Real.sqrt_mul (by positivity),
      Real.sqrt_mul (by positivity)]
  rw [hsqrt_factor] at hcard_scaled
  have hroot_pos : 0 < Real.sqrt (delta / t) := by positivity
  have hcard :
      (R.card : ℝ) ≤
        2 * C_geometry * Real.sqrt 10 * Real.sqrt A := by
    nlinarith
  exact ⟨2 * C_geometry * Real.sqrt 10, by positivity, hcard⟩

lemma product_scale_fixed_pair_tangent_bound_core
    {K D : ℝ} (hK : 1 ≤ K) (hD : 1 ≤ D)
    {family : Set C2Function}
    (hfamily : IsCinematicFamily family K D)
    {I : ParameterInterval} (hI : I.IsControlled K)
    {delta t metricLower tangencyLower : ℝ}
    (hdelta : 0 < delta) (ht : 0 < t)
    (hmetricLower : 0 < metricLower) (htangencyLower : 0 < tangencyLower)
    (hgeom_small : 10 * delta ≤ metricLower / (6 * K))
    {Cc : ℝ} (hCc : 100 ≤ Cc) (hadm : Cc * delta ≤ t)
    {w b : C2Function} (hw : w ∈ family) (hb : b ∈ family)
    (hwb : w ≠ b)
    (hmetric : metricLower ≤ c2Distance w b)
    (htangency : tangencyLower ≤ tangencyParameterOn I w b + delta)
    {C_geometry : ℝ} (hC_geometry : 0 < C_geometry)
    (hgeometry :
      ∀ family : Set C2Function, IsCinematicFamily family K D →
        ∀ I : ParameterInterval, I.IsControlled K →
          ∀ f ∈ family, ∀ g ∈ family, f ≠ g →
            ∀ delta : ℝ, 0 < delta →
              delta ≤ c2Distance f g / (6 * K) →
                (∃ pieces : IntervalFamily,
                  pieces.card ≤ 2 ∧
                  tangencySublevelSetOn I f g delta = pieces.union ∧
                  pieces.AllLengthsLE
                    (C_geometry * delta /
                      Real.sqrt
                        ((tangencyParameterOn I f g + delta) *
                          c2Distance f g)) ∧
                  ∀ x ∈ tangencySublevelSetOn I f g (delta / 2),
                    ∃ j : Fin pieces.card,
                      x ∈ (pieces.interval j).carrier ∧
                      delta ≤ C_geometry *
                        Real.sqrt
                          ((tangencyParameterOn I f g + delta) *
                            c2Distance f g) *
                        (pieces.interval j).length) ∧
                ∀ J : ParameterInterval,
                  J.carrier ⊆ I.centeredCarrier (1 / 4) →
                    (∀ x ∈ J.carrier, |f x - g x| ≤ delta) →
                      ∀ lambda : ℝ, 1 ≤ lambda →
                        ∀ x ∈ I.carrier,
                          x ∈ J.centeredCarrier lambda →
                            |f x - g x| ≤ C_geometry * lambda^2 * delta)
    {R : RectangleFamily delta t}
    (hRquarter : R.IsOverCentralQuarterOf I)
    (hRincomp : R.IsPairwiseIncomparable family Cc)
    (hcounts : ∀ i,
      (R.rectangle i).IsLambdaTangent w 5 ∧
        (R.rectangle i).IsLambdaTangent b 5) :
    (R.card : ℝ) ≤ (20 : ℝ) * C_geometry *
      Real.sqrt (delta * t / (metricLower * tangencyLower)) := by
  let enlargedDelta := 10 * delta
  have henlarged : 0 < enlargedDelta := by positivity
  have hdist : 0 < c2Distance w b := by
    exact hmetricLower.trans_le hmetric
  have hscale : enlargedDelta ≤ c2Distance w b / (6 * K) := by
    calc
      10 * delta ≤ metricLower / (6 * K) := hgeom_small
      _ ≤ c2Distance w b / (6 * K) := by
        gcongr
  obtain ⟨hpieces, _hextension⟩ :=
    hgeometry family hfamily I hI w hw b hb hwb
      enlargedDelta henlarged hscale
  obtain ⟨pieces, hpieces_card, hpieces_union, hpieces_length, _⟩ :=
    hpieces
  have htangency_nonneg : 0 ≤ tangencyParameterOn I w b := by
    apply Real.sInf_nonneg
    intro value hvalue
    rcases hvalue with ⟨x, _, rfl⟩
    positivity
  have htangency_lower :
      tangencyLower ≤ tangencyParameterOn I w b + enlargedDelta := by
    dsimp only [enlargedDelta]
    linarith
  have hdenom_lower :
      Real.sqrt (metricLower * tangencyLower) ≤
        Real.sqrt
          ((tangencyParameterOn I w b + enlargedDelta) *
            c2Distance w b) := by
    apply Real.sqrt_le_sqrt
    have h1a :
        metricLower * tangencyLower ≤
          c2Distance w b * tangencyLower := by
      exact mul_le_mul_of_nonneg_right hmetric (by positivity)
    have h1b :
        c2Distance w b * tangencyLower ≤
          c2Distance w b *
            (tangencyParameterOn I w b + enlargedDelta) := by
      exact mul_le_mul_of_nonneg_left htangency_lower (by positivity)
    calc
      metricLower * tangencyLower ≤
          c2Distance w b * tangencyLower := h1a
      _ ≤ c2Distance w b *
          (tangencyParameterOn I w b + enlargedDelta) := h1b
      _ = (tangencyParameterOn I w b + enlargedDelta) *
          c2Distance w b := by ring
  have htotal_length :
      ∑ j : Fin pieces.card, (pieces.interval j).length ≤
        2 * C_geometry * enlargedDelta /
          Real.sqrt (metricLower * tangencyLower) := by
    calc
      ∑ j : Fin pieces.card, (pieces.interval j).length ≤
          ∑ _j : Fin pieces.card,
            C_geometry * enlargedDelta /
              Real.sqrt
                ((tangencyParameterOn I w b + enlargedDelta) *
                  c2Distance w b) := by
        apply Finset.sum_le_sum
        intro j _
        exact hpieces_length j
      _ = (pieces.card : ℝ) *
          (C_geometry * enlargedDelta /
            Real.sqrt
              ((tangencyParameterOn I w b + enlargedDelta) *
                c2Distance w b)) := by simp
      _ ≤ 2 *
          (C_geometry * enlargedDelta /
            Real.sqrt (metricLower * tangencyLower)) := by
        have hdenom_pos :
            0 < Real.sqrt (metricLower * tangencyLower) := by positivity
        have hquot :
            C_geometry * enlargedDelta /
                Real.sqrt
                  ((tangencyParameterOn I w b + enlargedDelta) *
                    c2Distance w b) ≤
              C_geometry * enlargedDelta /
                Real.sqrt (metricLower * tangencyLower) := by
          exact div_le_div_of_nonneg_left
            (mul_nonneg hC_geometry.le henlarged.le)
            hdenom_pos hdenom_lower
        have hcard_real : (pieces.card : ℝ) ≤ 2 := by
          exact_mod_cast hpieces_card
        gcongr
      _ = 2 * C_geometry * enlargedDelta /
            Real.sqrt (metricLower * tangencyLower) := by ring
  have hintervals_sub : ∀ i,
      (R.rectangle i).interval.carrier ⊆ pieces.union := by
    intro i x hx
    have hxquarter : x ∈ I.centeredCarrier (1 / 4) :=
      hRquarter i hx
    have hpoint :
        (x, (R.rectangle i).function x) ∈
          (R.rectangle i).carrier := by
      exact ⟨hx, by simpa using hdelta.le⟩
    have hw_bound :
        |w x - (R.rectangle i).function x| ≤ 5 * delta := by
      simpa [abs_sub_comm] using (hcounts i).1 _ hpoint
    have hb_bound :
        |(R.rectangle i).function x - b x| ≤ 5 * delta :=
      (hcounts i).2 _ hpoint
    have hwb_bound : |w x - b x| ≤ enlargedDelta := by
      calc
        |w x - b x| ≤
            |w x - (R.rectangle i).function x| +
              |(R.rectangle i).function x - b x| := by
          exact abs_sub_le _ _ _
        _ ≤ 10 * delta := by linarith
        _ = enlargedDelta := rfl
    have : x ∈ tangencySublevelSetOn I w b enlargedDelta :=
      ⟨hxquarter, hwb_bound⟩
    rwa [hpieces_union] at this
  have hdisjoint : ∀ i j, i ≠ j →
      Disjoint (R.rectangle i).interval.carrier
        (R.rectangle j).interval.carrier := by
    intro i j hij
    by_contra h
    have hoverlap :
        ((R.rectangle i).interval.carrier ∩
          (R.rectangle j).interval.carrier).Nonempty :=
      Set.not_disjoint_iff.mp h
    have hcomparable :
        (R.rectangle i).AreLambdaComparable
          (R.rectangle j) family Cc :=
      common_tangent_overlap_comparable hdelta ht (by linarith)
        hadm hw (hcounts i).1 (hcounts j).1 hoverlap
    exact hRincomp i j hij hcomparable
  let realCarrier (J : ParameterInterval) : Set ℝ :=
    Set.Icc J.left J.right
  have hmeasure : ∀ J : ParameterInterval,
      MeasureTheory.volume (realCarrier J) =
        ENNReal.ofReal J.length := by
    intro J
    rw [Real.volume_Icc]
    simp [realCarrier, ParameterInterval.length,
      J.left_le_right]
  have hreal_sub : ∀ i,
      realCarrier (R.rectangle i).interval ⊆
        ⋃ j : Fin pieces.card, realCarrier (pieces.interval j) := by
    intro i x hx
    let point : UnitPoint := ⟨x, by
      exact ⟨(R.rectangle i).interval.left_mem.1.trans hx.1,
        hx.2.trans (R.rectangle i).interval.right_mem.2⟩⟩
    have hpoint :
        point ∈ (R.rectangle i).interval.carrier := hx
    obtain ⟨j, hj⟩ := hintervals_sub i hpoint
    exact Set.mem_iUnion.mpr ⟨j, hj⟩
  have hreal_disjoint : ∀ i j, i ≠ j →
      Disjoint (realCarrier (R.rectangle i).interval)
        (realCarrier (R.rectangle j).interval) := by
    intro i j hij
    by_contra h
    have hoverlap :
        (realCarrier (R.rectangle i).interval ∩
          realCarrier (R.rectangle j).interval).Nonempty :=
      Set.not_disjoint_iff.mp h
    obtain ⟨x, hxi, hxj⟩ := hoverlap
    let point : UnitPoint := ⟨x, by
      exact ⟨(R.rectangle i).interval.left_mem.1.trans hxi.1,
        hxi.2.trans (R.rectangle i).interval.right_mem.2⟩⟩
    have hpoint_i : point ∈ (R.rectangle i).interval.carrier := hxi
    have hpoint_j : point ∈ (R.rectangle j).interval.carrier := hxj
    exact Set.disjoint_left.mp (hdisjoint i j hij)
      hpoint_i hpoint_j
  have hmeasure_union :
      MeasureTheory.volume
          (⋃ i : Fin R.card,
            realCarrier (R.rectangle i).interval) =
        ∑ i : Fin R.card,
          MeasureTheory.volume
            (realCarrier (R.rectangle i).interval) := by
    have hmeasurable : ∀ i : Fin R.card,
        MeasurableSet (realCarrier (R.rectangle i).interval) :=
      fun _ => measurableSet_Icc
    have hpairwise :
        Set.PairwiseDisjoint
          (↑(Finset.univ : Finset (Fin R.card)))
          (fun i => realCarrier (R.rectangle i).interval) := by
      intro i _ j _ hij
      exact hreal_disjoint i j hij
    have heq :
        (⋃ i : Fin R.card,
          realCarrier (R.rectangle i).interval) =
        ⋃ i ∈ (Finset.univ : Finset (Fin R.card)),
          realCarrier (R.rectangle i).interval := by
      ext x
      simp
    rw [heq]
    exact MeasureTheory.measure_biUnion_finset hpairwise
      (fun i _ => hmeasurable i)
  have hmeasure_bound :
      ∑ i : Fin R.card,
          MeasureTheory.volume
            (realCarrier (R.rectangle i).interval) ≤
        ∑ j : Fin pieces.card,
          MeasureTheory.volume
            (realCarrier (pieces.interval j)) := by
    rw [← hmeasure_union]
    exact (MeasureTheory.measure_mono
      (Set.iUnion_subset_iff.mpr hreal_sub)).trans
        (MeasureTheory.measure_iUnion_fintype_le _ _)
  have hlength_sum :
      (R.card : ℝ) * Real.sqrt (delta / t) ≤
        ∑ j : Fin pieces.card, (pieces.interval j).length := by
    have hleft : ∑ i : Fin R.card,
        MeasureTheory.volume (realCarrier (R.rectangle i).interval) =
        ENNReal.ofReal ((R.card : ℝ) * Real.sqrt (delta / t)) := by
      have hmeasure_sum : ∑ i : Fin R.card,
          MeasureTheory.volume (realCarrier (R.rectangle i).interval) =
        ∑ i : Fin R.card,
          ENNReal.ofReal (R.rectangle i).interval.length := by
        apply Finset.sum_congr rfl
        intro i _
        exact hmeasure _
      rw [hmeasure_sum]
      have hofreal :
          ∑ i : Fin R.card,
              ENNReal.ofReal (R.rectangle i).interval.length =
            ENNReal.ofReal
              (∑ i : Fin R.card,
                (R.rectangle i).interval.length) := by
        rw [ENNReal.ofReal_sum_of_nonneg
        (fun i _ => (R.rectangle i).interval.length_nonneg)]
      rw [hofreal]
      congr 1
      simp [(R.rectangle _).interval_length]
    have hright : ∑ j : Fin pieces.card,
        MeasureTheory.volume (realCarrier (pieces.interval j)) =
      ENNReal.ofReal
        (∑ j : Fin pieces.card, (pieces.interval j).length) := by
      have hmeasure_sum : ∑ j : Fin pieces.card,
          MeasureTheory.volume (realCarrier (pieces.interval j)) =
        ∑ j : Fin pieces.card,
          ENNReal.ofReal (pieces.interval j).length := by
        apply Finset.sum_congr rfl
        intro j _
        exact hmeasure _
      rw [hmeasure_sum]
      rw [ENNReal.ofReal_sum_of_nonneg
        (fun j _ => (pieces.interval j).length_nonneg)]
    rw [hleft, hright] at hmeasure_bound
    exact (ENNReal.ofReal_le_ofReal_iff
      (Finset.sum_nonneg
        (fun j _ => (pieces.interval j).length_nonneg))).mp
          hmeasure_bound
  have hcard_scaled :
      (R.card : ℝ) * Real.sqrt (delta / t) ≤
        2 * C_geometry * enlargedDelta /
          Real.sqrt (metricLower * tangencyLower) :=
    hlength_sum.trans htotal_length
  have hdelta_div_sqrt :
      delta / Real.sqrt (delta / t) = Real.sqrt (delta * t) := by
    have hpos1 : 0 < delta := hdelta
    have h : Real.sqrt (delta * t) =
        Real.sqrt (delta ^ 2 / (delta / t)) := by
      have h_eq : delta * t = delta ^ 2 / (delta / t) := by
        field_simp [hpos1.ne', ht.ne'] <;> ring
      rw [h_eq]
    rw [h]
    have h2 : Real.sqrt (delta ^ 2 / (delta / t)) =
        Real.sqrt (delta ^ 2) / Real.sqrt (delta / t) := by
      rw [Real.sqrt_div (by positivity)]
    rw [h2]
    have h3 : Real.sqrt (delta ^ 2) = delta := by
      rw [Real.sqrt_sq_eq_abs]
      rw [abs_of_pos hpos1]
    rw [h3]
  have halgebra :
      (2 * C_geometry * enlargedDelta /
        Real.sqrt (metricLower * tangencyLower)) /
        Real.sqrt (delta / t) =
      (20 : ℝ) * C_geometry *
        Real.sqrt (delta * t / (metricLower * tangencyLower)) := by
    dsimp only [enlargedDelta]
    have hpos : 0 < Real.sqrt (metricLower * tangencyLower) := by
      positivity
    calc
      (2 * C_geometry * (10 * delta) /
        Real.sqrt (metricLower * tangencyLower)) /
        Real.sqrt (delta / t)
        = 2 * C_geometry * (10 * delta) /
            (Real.sqrt (metricLower * tangencyLower) *
              Real.sqrt (delta / t)) := by ring
      _ = 2 * C_geometry * (10 * (delta / Real.sqrt (delta / t))) /
            Real.sqrt (metricLower * tangencyLower) := by
          field_simp [hpos.ne'] <;> ring
      _ = 2 * C_geometry * (10 * Real.sqrt (delta * t)) /
            Real.sqrt (metricLower * tangencyLower) := by
          rw [hdelta_div_sqrt]
      _ = (20 : ℝ) * C_geometry *
            Real.sqrt (delta * t / (metricLower * tangencyLower)) := by
          have hsqrt_div :
              Real.sqrt (delta * t) /
                  Real.sqrt (metricLower * tangencyLower) =
                Real.sqrt
                  (delta * t / (metricLower * tangencyLower)) := by
            rw [← Real.sqrt_div (by positivity)] <;> ring
          have h :
              2 * C_geometry * (10 * Real.sqrt (delta * t)) /
                  Real.sqrt (metricLower * tangencyLower) =
                (20 : ℝ) * C_geometry *
                  (Real.sqrt (delta * t) /
                    Real.sqrt (metricLower * tangencyLower)) := by
            ring
          rw [h, hsqrt_div] <;> ring
  have hroot_pos : 0 < Real.sqrt (delta / t) := by positivity
  have hdiv :
      (R.card : ℝ) ≤
        (2 * C_geometry * enlargedDelta /
          Real.sqrt (metricLower * tangencyLower)) /
          Real.sqrt (delta / t) := by
    calc
      (R.card : ℝ) =
          ((R.card : ℝ) * Real.sqrt (delta / t)) /
            Real.sqrt (delta / t) := by
        field_simp [hroot_pos.ne'] <;> ring
      _ ≤ (2 * C_geometry * enlargedDelta /
            Real.sqrt (metricLower * tangencyLower)) /
            Real.sqrt (delta / t) := by
        gcongr
  rw [halgebra] at hdiv
  exact hdiv

lemma product_scale_fixed_pair_tangent_bound
    {K D : ℝ} (hK : 1 ≤ K) (hD : 1 ≤ D)
    {family : Set C2Function}
    (hfamily : IsCinematicFamily family K D)
    {I : ParameterInterval} (hI : I.IsControlled K)
    {delta t metricLower tangencyLower : ℝ}
    (hdelta : 0 < delta) (ht : 0 < t)
    (hmetricLower : 0 < metricLower) (htangencyLower : 0 < tangencyLower)
    (hgeom_small : 10 * delta ≤ metricLower / (6 * K))
    {Cc : ℝ} (hCc : 100 ≤ Cc) (hadm : Cc * delta ≤ t)
    {w b : C2Function} (hw : w ∈ family) (hb : b ∈ family)
    (hwb : w ≠ b)
    (hmetric : metricLower ≤ c2Distance w b)
    (htangency : tangencyLower ≤ tangencyParameterOn I w b + delta)
    (hTangency : TangencyGeometryCompletionStatement)
    {R : RectangleFamily delta t}
    (hRquarter : R.IsOverCentralQuarterOf I)
    (hRincomp : R.IsPairwiseIncomparable family Cc)
    (hcounts : ∀ i,
      (R.rectangle i).IsLambdaTangent w 5 ∧
        (R.rectangle i).IsLambdaTangent b 5) :
    ∃ C_pair : ℝ, 0 < C_pair ∧
      (R.card : ℝ) ≤ C_pair *
        Real.sqrt (delta * t / (metricLower * tangencyLower)) := by
  obtain ⟨C_geometry, hC_geometry, hgeometry⟩ :=
    hTangency K D hK hD
  have hbound := product_scale_fixed_pair_tangent_bound_core
    (hK := hK) (hD := hD) (hfamily := hfamily) (hI := hI)
    (hdelta := hdelta) (ht := ht)
    (hmetricLower := hmetricLower) (htangencyLower := htangencyLower)
    (hgeom_small := hgeom_small) (hCc := hCc) (hadm := hadm)
    (hw := hw) (hb := hb) (hwb := hwb)
    (hmetric := hmetric) (htangency := htangency)
    (hC_geometry := hC_geometry) (hgeometry := hgeometry)
    (hRquarter := hRquarter) (hRincomp := hRincomp)
    (hcounts := hcounts)
  exact ⟨(20 : ℝ) * C_geometry, by positivity, hbound⟩

end Kakeya.Cinematic
