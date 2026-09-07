import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.LipschitzStripBound
import Mathlib.Tactic

/-!
# Lipschitz Graph Lower Strip Bound

Derives the one-sided strip bound for the **lower** strip (points below
a Lipschitz graph) from the existing upper-strip bound by reflecting
the last coordinate.

## Main result

- `LipschitzGraph_lowerStripBound`: sharp volume bound for `lowerStrip`
- `rotated_LipschitzGraph_lowerStripBound`: rotated version
-/

open MeasureTheory Metric Set ENNReal
open scoped MeasureTheory
open GraphAreaFormula

namespace Geometry.Isoperimetric

variable {m : ℕ} [Nonempty (Fin m)]

section Reflection

/-- Reflect the last coordinate of a function on `Fin (m+1)`. -/
private def flipLast (f : Fin (m + 1) → ℝ) : Fin (m + 1) → ℝ :=
  fun i => if i = Fin.last m then -f i else f i

private lemma flipLast_involutive (f : Fin (m + 1) → ℝ) :
    flipLast (flipLast f) = f := by
  funext i
  simp [flipLast] <;> split_ifs <;> ring

private lemma flipLast_add (f g : Fin (m + 1) → ℝ) :
    flipLast (f + g) = flipLast f + flipLast g := by
  funext i
  simp [flipLast] <;> split_ifs <;> ring

private lemma flipLast_smul (c : ℝ) (f : Fin (m + 1) → ℝ) :
    flipLast (c • f) = c • flipLast f := by
  funext i
  simp [flipLast] <;> split_ifs <;> ring

private lemma flipLast_sum_sq (f : Fin (m + 1) → ℝ) :
    ∑ i : Fin (m + 1), (flipLast f i) ^ 2 = ∑ i : Fin (m + 1), (f i) ^ 2 := by
  apply Finset.sum_congr rfl
  intro i _
  simp [flipLast] <;> split_ifs <;> ring

/-- Reflect the last coordinate of `E (m + 1)`. -/
noncomputable def reflectLastFun (x : E (m + 1)) : E (m + 1) :=
  (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (flipLast x)

private lemma reflectLastFun_involutive (x : E (m + 1)) :
    reflectLastFun (reflectLastFun x) = x := by
  have h : flipLast (flipLast (x : Fin (m + 1) → ℝ)) = (x : Fin (m + 1) → ℝ) :=
    flipLast_involutive (x : Fin (m + 1) → ℝ)
  simpa [reflectLastFun] using congr_arg ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm) h

private lemma reflectLastFun_add (x y : E (m + 1)) :
    reflectLastFun (x + y) = reflectLastFun x + reflectLastFun y := by
  have h : flipLast ((x + y : E (m + 1)) : Fin (m + 1) → ℝ) =
      flipLast (x : Fin (m + 1) → ℝ) + flipLast (y : Fin (m + 1) → ℝ) :=
    flipLast_add (x : Fin (m + 1) → ℝ) (y : Fin (m + 1) → ℝ)
  simpa [reflectLastFun] using congr_arg ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm) h

private lemma reflectLastFun_smul (c : ℝ) (x : E (m + 1)) :
    reflectLastFun (c • x) = c • reflectLastFun x := by
  have h : flipLast ((c • x : E (m + 1)) : Fin (m + 1) → ℝ) =
      c • flipLast (x : Fin (m + 1) → ℝ) :=
    flipLast_smul c (x : Fin (m + 1) → ℝ)
  simpa [reflectLastFun] using congr_arg ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm) h

private lemma reflectLastFun_apply (x : E (m + 1)) (i : Fin (m + 1)) :
    (reflectLastFun x) i = flipLast x i := by
  simp [reflectLastFun]
  <;> rfl

private lemma reflectLastFun_norm (x : E (m + 1)) :
    ‖reflectLastFun x‖ = ‖x‖ := by
  let f : Fin (m + 1) → ℝ := x
  let f' := flipLast f
  have h_sum : ∑ i, (f' i)^2 = ∑ i, (f i)^2 := flipLast_sum_sq f
  have h1 : ‖reflectLastFun x‖ = Real.sqrt (∑ i : Fin (m + 1), ‖(reflectLastFun x) i‖ ^ 2) := by
    rw [EuclideanSpace.norm_eq]
  have h2 : ∑ i : Fin (m + 1), ‖(reflectLastFun x) i‖ ^ 2 = ∑ i : Fin (m + 1), (f' i)^2 := by
    apply Finset.sum_congr rfl
    intro i _
    have h_apply : (reflectLastFun x) i = f' i := reflectLastFun_apply x i
    rw [h_apply]
    simp [abs_pow]
  have h3 : ‖x‖ = Real.sqrt (∑ i : Fin (m + 1), ‖x i‖ ^ 2) := by
    rw [EuclideanSpace.norm_eq]
  have h4 : ∑ i : Fin (m + 1), ‖x i‖ ^ 2 = ∑ i : Fin (m + 1), (f i)^2 := by
    apply Finset.sum_congr rfl
    intro i _
    have h5 : ‖x i‖ ^ 2 = (x i)^2 := by
      have h6 : ‖x i‖ = |x i| := Real.norm_eq_abs (x i)
      rw [h6]
      have h7 : |x i| ^ 2 = (x i)^2 := by
        simp [sq_abs]
      exact h7
    exact h5
  rw [h1, h2, h3, h4, h_sum]

/-- Linear isometry reflecting the last coordinate of `E (m + 1)`. -/
noncomputable def reflectLast : E (m + 1) ≃ₗᵢ[ℝ] E (m + 1) :=
  { toFun := reflectLastFun
    invFun := reflectLastFun
    left_inv := reflectLastFun_involutive
    right_inv := reflectLastFun_involutive
    map_add' := reflectLastFun_add
    map_smul' := reflectLastFun_smul
    norm_map' := reflectLastFun_norm }

lemma reflectLast_apply_last (x : E (m + 1)) :
    (reflectLast x) (Fin.last m) = -x (Fin.last m) := by
  change (reflectLastFun x) (Fin.last m) = -x (Fin.last m)
  rw [reflectLastFun_apply]
  simp [flipLast]
  <;> rfl

lemma reflectLast_apply_castSucc (x : E (m + 1)) (j : Fin m) :
    (reflectLast x) (Fin.castSucc j) = x (Fin.castSucc j) := by
  change (reflectLastFun x) (Fin.castSucc j) = x (Fin.castSucc j)
  have h_ne : (Fin.castSucc j) ≠ (Fin.last m) := Fin.castSucc_ne_last j
  rw [reflectLastFun_apply]
  simp [flipLast, h_ne]
  <;> rfl

lemma reflectLast_proj (x : E (m + 1)) :
    GraphAreaFormula.proj (reflectLast x) = GraphAreaFormula.proj x := by
  ext j
  rw [GraphAreaFormula.proj_apply, GraphAreaFormula.proj_apply,
    reflectLast_apply_castSucc]

lemma reflectLast_involutive (x : E (m + 1)) :
    reflectLast (reflectLast x) = x :=
  reflectLast.left_inv x

lemma reflectLast_graphMap (g : E m → ℝ) (x : E m) :
    reflectLast (graphMap g x) = graphMap (fun y => -g y) x := by
  ext i
  by_cases h : i = Fin.last m
  · subst h
    rw [reflectLast_apply_last, graphMap_apply_last, graphMap_apply_last] <;> rfl
  · have h2 : ∃ j : Fin m, i = Fin.castSucc j := by
      refine ⟨⟨i.val, ?_⟩, ?_⟩
      · have h3 : i.val < m + 1 := i.is_lt
        have h4 : i.val ≠ m := by
          intro h5
          have h6 : i = Fin.last m := by
            apply Fin.ext
            simpa using h5
          exact h h6
        omega
      · apply Fin.ext
        simp
    rcases h2 with ⟨j, rfl⟩
    rw [reflectLast_apply_castSucc, graphMap_apply_castSucc, graphMap_apply_castSucc]

lemma reflectLast_graphMap_image (g : E m → ℝ) (A : Set (E m)) :
    reflectLast '' (graphMap g '' A) = graphMap (fun y => -g y) '' A := by
  have h_set_eq : (reflectLast '' (graphMap g '' A)) =
      (fun x => reflectLast (graphMap g x)) '' A := by
    ext z
    simp only [Set.mem_image]
    constructor
    · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨graphMap g x, ⟨x, hx, rfl⟩, rfl⟩
  rw [h_set_eq]
  have h_f_eq : (fun x : E m => reflectLast (graphMap g x)) = graphMap (fun y => -g y) := by
    funext x
    exact reflectLast_graphMap g x
  rw [h_f_eq]

lemma reflectLast_graph (g : E m → ℝ) :
    reflectLast '' (GraphAreaFormula.graph g) = GraphAreaFormula.graph (fun y => -g y) := by
  ext z
  simp only [Set.mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩
    have h4 : p (Fin.last m) = g (GraphAreaFormula.proj p) := by
      simpa [GraphAreaFormula.graph] using hp
    have h5 : (reflectLast p) (Fin.last m) = (fun y => -g y) (GraphAreaFormula.proj (reflectLast p)) := by
      rw [reflectLast_apply_last, reflectLast_proj, h4] <;> rfl
    simpa [GraphAreaFormula.graph] using h5
  · intro hz
    let p := reflectLast z
    have hp : p (Fin.last m) = g (GraphAreaFormula.proj p) := by
      have h5 : p (Fin.last m) = -z (Fin.last m) := reflectLast_apply_last z
      have h6 : z (Fin.last m) = -g (GraphAreaFormula.proj z) := by
        simpa [GraphAreaFormula.graph] using hz
      have h7 : GraphAreaFormula.proj p = GraphAreaFormula.proj z := reflectLast_proj z
      rw [h5, h6, h7] <;> ring
    have h8 : reflectLast p = z := by
      simpa [p] using reflectLast_involutive z
    exact ⟨p, by simpa [GraphAreaFormula.graph] using hp, h8⟩

lemma reflectLast_infDist (g : E m → ℝ) (p : E (m + 1)) :
    infDist (reflectLast p) (GraphAreaFormula.graph (fun y => -g y)) =
    infDist p (GraphAreaFormula.graph g) := by
  rw [← reflectLast_graph g]
  have h_iso : Isometry (reflectLast : E (m + 1) → E (m + 1)) :=
    reflectLast.isometry
  exact Metric.infDist_image h_iso

lemma reflectLast_lowerStrip (g : E m → ℝ) (A : Set (E m)) (t : ℝ) :
    reflectLast '' (lowerStrip g A t) = upperStrip (fun y => -g y) t A := by
  ext z
  simp only [Set.mem_image, upperStrip, lowerStrip, distanceStrip]
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hproj : GraphAreaFormula.proj (reflectLast p) ∈ A := by
      rw [reflectLast_proj]; exact hp.1
    have hdist : 0 < infDist (reflectLast p) (GraphAreaFormula.graph (fun y => -g y)) := by
      rw [reflectLast_infDist]; exact hp.2.1
    have hdist2 : infDist (reflectLast p) (GraphAreaFormula.graph (fun y => -g y)) < t := by
      rw [reflectLast_infDist]; exact hp.2.2.1
    have hside : (reflectLast p) (Fin.last m) > (fun y => -g y) (GraphAreaFormula.proj (reflectLast p)) := by
      rw [reflectLast_apply_last, reflectLast_proj]
      exact neg_lt_neg hp.2.2.2
    exact ⟨hproj, hdist, hdist2, hside⟩
  · intro hz
    let p := reflectLast z
    have hp : p ∈ lowerStrip g A t := by
      have hproj : GraphAreaFormula.proj p ∈ A := by
        rw [show GraphAreaFormula.proj p = GraphAreaFormula.proj z from reflectLast_proj z]
        exact hz.1
      have hdist : 0 < infDist p (GraphAreaFormula.graph g) := by
        have h_eq : infDist p (GraphAreaFormula.graph g) =
            infDist z (GraphAreaFormula.graph (fun y => -g y)) := by
          have h_p : p = reflectLast z := by rfl
          rw [h_p]
          have h := reflectLast_infDist (fun y => -g y) z
          have h_simp : (fun y : E m => -(-g y)) = g := by funext y; ring
          rw [h_simp] at h
          exact h
        rw [h_eq]
        exact hz.2.1
      have hdist2 : infDist p (GraphAreaFormula.graph g) < t := by
        have h_eq : infDist p (GraphAreaFormula.graph g) =
            infDist z (GraphAreaFormula.graph (fun y => -g y)) := by
          have h_p : p = reflectLast z := by rfl
          rw [h_p]
          have h := reflectLast_infDist (fun y => -g y) z
          have h_simp : (fun y : E m => -(-g y)) = g := by funext y; ring
          rw [h_simp] at h
          exact h
        rw [h_eq]
        exact hz.2.2.1
      have hside : p (Fin.last m) < g (GraphAreaFormula.proj p) := by
        have h9 : p (Fin.last m) = -z (Fin.last m) := reflectLast_apply_last z
        have h10 : GraphAreaFormula.proj p = GraphAreaFormula.proj z := reflectLast_proj z
        rw [h9, h10]
        exact neg_lt_neg hz.2.2.2 |>.trans_eq (by ring)
      exact ⟨hproj, hdist, hdist2, hside⟩
    refine ⟨p, hp, ?_⟩
    have h8 : reflectLast p = z := by
      simpa [p] using reflectLast_involutive z
    exact h8

/-- Measurability of the lower strip. -/
lemma lowerStrip_measurable (g : E m → ℝ) (hg : Continuous g)
    (A : Set (E m)) (hA : MeasurableSet A) (t : ℝ) :
    MeasurableSet (lowerStrip g A t) := by
  have h1 : Measurable (fun p : E (m + 1) => GraphAreaFormula.proj p) := by
    have h_cont : Continuous (fun p : E (m + 1) => GraphAreaFormula.proj p) := by
      have h11 : Continuous (fun p : E (m + 1) => (fun i : Fin m => p (Fin.castSucc i))) := by fun_prop
      have h12 : Continuous ((EuclideanSpace.equiv (Fin m) ℝ).symm : (Fin m → ℝ) → E m) :=
        (EuclideanSpace.equiv (Fin m) ℝ).symm.continuous
      exact h12.comp h11
    exact h_cont.measurable
  have h2 : Measurable (fun p : E (m + 1) => infDist p (graph g)) :=
    (Metric.continuous_infDist_pt (graph g)).measurable
  have h_last : Measurable (fun p : E (m + 1) => p (Fin.last m)) := by fun_prop
  have h_g : Measurable (fun p : E (m + 1) => g (GraphAreaFormula.proj p)) := by fun_prop
  have h4 : Measurable (fun p : E (m + 1) => g (GraphAreaFormula.proj p) - p (Fin.last m)) :=
    h_g.sub h_last
  have hs1 : MeasurableSet {p : E (m + 1) | GraphAreaFormula.proj p ∈ A} := hA.preimage h1
  have hs2 : MeasurableSet {p : E (m + 1) | 0 < infDist p (graph g)} :=
    measurableSet_Ioi.preimage h2
  have hs3 : MeasurableSet {p : E (m + 1) | infDist p (graph g) < t} :=
    measurableSet_Iio.preimage h2
  have hs4 : MeasurableSet {p : E (m + 1) | p (Fin.last m) < g (GraphAreaFormula.proj p)} := by
    have h_eq : {p : E (m + 1) | p (Fin.last m) < g (GraphAreaFormula.proj p)} =
        {p : E (m + 1) | g (GraphAreaFormula.proj p) - p (Fin.last m) > 0} := by
      ext p; simp [sub_pos]
    rw [h_eq]
    exact measurableSet_Ioi.preimage h4
  exact hs1.inter (hs2.inter (hs3.inter hs4))

end Reflection

/-- **Sharp lower strip bound for Lipschitz graphs.**

For Lipschitz `g` and bounded measurable `A`, for every `ε > 0` there
exists `t₀ > 0` such that for all `0 < t < t₀`:
`volume(lowerStrip g A t) ≤ (1+ε) · t · H^m(graphMap g '' A)` -/
theorem LipschitzGraph_lowerStripBound
    {g : E m → ℝ} {L : NNReal} (hg : LipschitzWith L g)
    (A : Set (E m)) (hA : MeasurableSet A) (hA_bdd : Bornology.IsBounded A)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (t₀ : ℝ), 0 < t₀ ∧ ∀ (t : ℝ), 0 < t → t < t₀ →
      volume (lowerStrip g A t) ≤
        ENNReal.ofReal (1 + ε) * ENNReal.ofReal t *
        μHE[m] (graphMap g '' A) := by
  let g' : E m → ℝ := fun x => -g x
  have hg' : LipschitzWith L g' := hg.neg
  rcases LipschitzGraph_stripBound g' hg' A hA hA_bdd ε hε with ⟨t₀, ht₀_pos, hbound⟩
  refine ⟨t₀, ht₀_pos, fun t ht_pos ht_lt => ?_⟩
  have h_meas : MeasurableSet (lowerStrip g A t) :=
    lowerStrip_measurable g hg.continuous A hA t
  have h1 : volume (lowerStrip g A t) = volume (upperStrip g' t A) := by
    have h_eq : reflectLast '' (lowerStrip g A t) = upperStrip g' t A :=
      reflectLast_lowerStrip g A t
    have h_vol : volume (reflectLast '' (lowerStrip g A t)) = volume (lowerStrip g A t) := by
      let e : E (m + 1) ≃ₗᵢ[ℝ] E (m + 1) := reflectLast
      have h_image_eq_preimage : e '' (lowerStrip g A t) = e.symm ⁻¹' (lowerStrip g A t) := by
        ext y
        simp only [Set.mem_image, Set.mem_preimage]
        constructor
        · rintro ⟨x, hx, rfl⟩; simpa using hx
        · intro hy; refine ⟨e.symm y, hy, ?_⟩; simp
      rw [h_image_eq_preimage]
      have hmp : MeasurePreserving e.symm volume volume := e.measurePreserving
      have h1 : (volume.map e.symm) (lowerStrip g A t) = volume (e.symm ⁻¹' (lowerStrip g A t)) :=
        Measure.map_apply e.symm.continuous.measurable h_meas
      have h2 : volume.map e.symm = volume := hmp.map_eq
      rw [h2] at h1
      exact h1.symm
    rw [h_eq] at h_vol
    exact h_vol.symm
  rw [h1]
  have h2 : μHE[m] (graphMap g' '' A) = μHE[m] (graphMap g '' A) := by
    have h3 : reflectLast '' (graphMap g '' A) = graphMap g' '' A :=
      reflectLast_graphMap_image g A
    have h4 : μHE[m] (reflectLast '' (graphMap g '' A)) = μHE[m] (graphMap g '' A) := by
      have h_iso : Isometry (reflectLast : E (m + 1) → E (m + 1)) := reflectLast.isometry
      have h5 : μH[m] (reflectLast '' (graphMap g '' A)) = μH[m] (graphMap g '' A) :=
        h_iso.hausdorffMeasure_image (Or.inl (by positivity)) _
      simpa [MeasureTheory.Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, h5] using rfl
    rw [h3] at h4
    exact h4
  have hbound' := hbound t ht_pos ht_lt
  rw [h2] at hbound'
  exact hbound'

/-- Rotated version of the lower strip bound. -/
lemma rotated_LipschitzGraph_lowerStripBound
    (φ : E (m + 1) ≃ₗᵢ[ℝ] E (m + 1))
    (g : E m → ℝ) {L : NNReal} (hg : LipschitzWith L g)
    (A : Set (E m)) (hA : MeasurableSet A) (hA_bdd : Bornology.IsBounded A)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (t₀ : ℝ), 0 < t₀ ∧ ∀ (t : ℝ), 0 < t → t < t₀ →
      volume (φ.symm '' (lowerStrip g A t)) ≤
        ENNReal.ofReal (1 + ε) * ENNReal.ofReal t *
        μHE[m] (φ.symm '' (graphMap g '' A)) := by
  rcases LipschitzGraph_lowerStripBound hg A hA hA_bdd ε hε with ⟨t₀, ht₀_pos, hbound⟩
  refine ⟨t₀, ht₀_pos, fun t ht_pos ht_lt => ?_⟩
  have h_meas : MeasurableSet (lowerStrip g A t) :=
    lowerStrip_measurable g hg.continuous A hA t
  have h1 : volume (φ.symm '' (lowerStrip g A t)) = volume (lowerStrip g A t) := by
      have h_image_eq_preimage : φ.symm '' (lowerStrip g A t) = φ ⁻¹' (lowerStrip g A t) := by
        ext y
        simp only [Set.mem_image, Set.mem_preimage]
        constructor
        · rintro ⟨x, hx, rfl⟩; simpa using hx
        · intro hy; refine ⟨φ y, hy, ?_⟩; simp
      rw [h_image_eq_preimage]
      have hmp : MeasurePreserving φ volume volume := φ.measurePreserving
      have h1' : (volume.map φ) (lowerStrip g A t) = volume (φ ⁻¹' (lowerStrip g A t)) :=
        Measure.map_apply φ.continuous.measurable h_meas
      have h2 : volume.map φ = volume := hmp.map_eq
      rw [h2] at h1'
      exact h1'.symm
  rw [h1]
  have h2 : μHE[m] (φ.symm '' (graphMap g '' A)) = μHE[m] (graphMap g '' A) := by
    have h_iso : Isometry (φ.symm : E (m + 1) → E (m + 1)) := φ.symm.isometry
    have h5 : μH[m] (φ.symm '' (graphMap g '' A)) = μH[m] (graphMap g '' A) :=
      h_iso.hausdorffMeasure_image (Or.inl (by positivity)) _
    simpa [MeasureTheory.Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, h5] using rfl
  rw [h2]
  exact hbound t ht_pos ht_lt

end Geometry.Isoperimetric
