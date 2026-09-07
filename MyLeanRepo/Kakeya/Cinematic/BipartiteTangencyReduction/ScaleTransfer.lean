import MyLeanRepo.Kakeya.Cinematic.Geometry

/-!
# Scale transfer lemmas for the small-ratio branch

Given rectangles at scale `(δ, t)`, we create corresponding rectangles at
scale `(δ' = δ/(2A), r = t/(2A))` with the SAME functions and intervals.
Since `δ'/r = δ/t`, the interval length condition is preserved.
-/

noncomputable section

namespace Kakeya.Cinematic

namespace CurvilinearRectangle

/-- Rescale a curvilinear rectangle to new scale parameters with the same ratio. -/
def rescale {δ t δ' r : ℝ} (R : CurvilinearRectangle δ t)
    (hratio : δ' / r = δ / t) : CurvilinearRectangle δ' r :=
  { function := R.function
    interval := R.interval
    interval_length := by
      rw [R.interval_length]
      rw [←hratio] }

@[simp]
lemma rescale_function {δ t δ' r : ℝ} (R : CurvilinearRectangle δ t)
    (hratio : δ' / r = δ / t) :
    (R.rescale hratio).function = R.function := rfl

@[simp]
lemma rescale_interval {δ t δ' r : ℝ} (R : CurvilinearRectangle δ t)
    (hratio : δ' / r = δ / t) :
    (R.rescale hratio).interval = R.interval := rfl

lemma rescale_carrier_subset {δ t δ' r : ℝ} (R : CurvilinearRectangle δ t)
    (hratio : δ' / r = δ / t) (hδ'_le : δ' ≤ δ) :
    (R.rescale hratio).carrier ⊆ R.carrier := by
  intro p hp
  exact ⟨hp.1, hp.2.trans hδ'_le⟩

lemma IsLambdaTangent.rescale {δ t δ' r : ℝ} {R : CurvilinearRectangle δ t}
    {f : C2Function} {lambda lambda' : ℝ}
    (hδ'_le : δ' ≤ δ)
    (hbound : lambda * δ ≤ lambda' * δ')
    (h : R.IsLambdaTangent f lambda)
    (hratio : δ' / r = δ / t) :
    (R.rescale hratio).IsLambdaTangent f lambda' := by
  intro p hp
  have h1 : p ∈ R.carrier := R.rescale_carrier_subset hratio hδ'_le hp
  have h2 : |p.2 - f p.1| ≤ lambda * δ := h p h1
  exact h2.trans hbound

lemma IsOverCentralQuarterOf.rescale {δ t δ' r : ℝ}
    {R : CurvilinearRectangle δ t} {I : ParameterInterval}
    (h : R.IsOverCentralQuarterOf I)
    (hratio : δ' / r = δ / t) :
    (R.rescale hratio).IsOverCentralQuarterOf I := h

lemma admissible_comparison_scale_rescale {δ t δ' r comparison : ℝ}
    (hratio : δ' / r = δ / t) (ht : 0 < t) (hr_pos : 0 < r)
    (h : IsAdmissibleComparisonScale δ t comparison) :
    IsAdmissibleComparisonScale δ' r comparison := by
  have h1 : 1 ≤ comparison := h.1
  have h2 : comparison * δ ≤ t := h.2
  have h3 : comparison * δ / t ≤ 1 := (div_le_one ht).mpr h2
  have h4 : comparison * δ' / r = comparison * δ / t := by
    calc
      comparison * δ' / r = comparison * (δ' / r) := by ring
      _ = comparison * (δ / t) := by rw [hratio]
      _ = comparison * δ / t := by ring
  have h5 : comparison * δ' / r ≤ 1 := by
    rw [h4]; exact h3
  have h6 : comparison * δ' ≤ r := (div_le_one hr_pos).mp h5
  exact ⟨h1, h6⟩

lemma AreLambdaIncomparable.rescale {δ t δ' r : ℝ}
    {R S : CurvilinearRectangle δ t} {family : Set C2Function}
    {comparison : ℝ}
    (_hδ : 0 < δ) (hδ' : 0 < δ') (hδ'_le : δ' ≤ δ)
    (hratio : δ' / r = δ / t)
    (hcomparison : 1 ≤ comparison)
    (h : R.AreLambdaIncomparable S family comparison) :
    (R.rescale hratio).AreLambdaIncomparable
      (S.rescale hratio) family comparison := by
  classical
  by_cases hcomparable : (R.rescale hratio).AreLambdaComparable
      (S.rescale hratio) family comparison
  · exfalso
    rcases hcomparable with ⟨U', hU'_fam, hU'_sub⟩
    let R' := R.rescale hratio
    let S' := S.rescale hratio
    have hR'sub : R'.carrier ⊆ U'.carrier := (Set.union_subset_iff.mp hU'_sub).1
    have hS'sub : S'.carrier ⊆ U'.carrier := (Set.union_subset_iff.mp hU'_sub).2
    have hVlen : (comparison * δ) / t = (comparison * δ') / r := by
      calc
        (comparison * δ) / t = comparison * (δ / t) := by ring
        _ = comparison * (δ' / r) := by rw [←hratio]
        _ = (comparison * δ') / r := by ring
    let V : CurvilinearRectangle (comparison * δ) t :=
      { function := U'.function
        interval := U'.interval
        interval_length := by rw [U'.interval_length, ←hVlen] }
    have htransfer : ∀ (Q : CurvilinearRectangle δ t),
        (Q.rescale hratio).carrier ⊆ U'.carrier → Q.carrier ⊆ V.carrier := by
      intro Q hQ'sub p hp
      have hpx : p.1 ∈ Q.interval.carrier := hp.1
      have hpxU : p.1 ∈ U'.interval.carrier := by
        let q : UnitPoint × ℝ := (p.1, Q.function p.1)
        have hqcarrier : q ∈ (Q.rescale hratio).carrier := by
          have hb : |q.2 - Q.function q.1| ≤ δ' := by
            change |Q.function p.1 - Q.function p.1| ≤ δ'
            simpa using hδ'.le
          exact ⟨hpx, hb⟩
        exact (hQ'sub hqcarrier).1
      set y := Q.function p.1 with hy_def
      set z := U'.function p.1 with hz_def
      set d := y - z with hd_def
      have hq1 : (p.1, y + δ') ∈ (Q.rescale hratio).carrier := by
        have hb : |(y + δ') - Q.function p.1| ≤ δ' := by
          have h_eq : (y + δ') - Q.function p.1 = δ' := by
            simp [hy_def]
          rw [h_eq]
          exact abs_of_pos hδ' |>.le
        exact ⟨hpx, hb⟩
      have hq2 : (p.1, y - δ') ∈ (Q.rescale hratio).carrier := by
        have hb : |(y - δ') - Q.function p.1| ≤ δ' := by
          have h_eq : (y - δ') - Q.function p.1 = -δ' := by
            simp [hy_def]
          rw [h_eq]
          have h_abs : |(-δ')| = |δ'| := abs_neg δ'
          rw [h_abs]
          exact abs_of_pos hδ' |>.le
        exact ⟨hpx, hb⟩
      have h1 : |(y + δ') - z| ≤ comparison * δ' := (hQ'sub hq1).2
      have h2 : |(y - δ') - z| ≤ comparison * δ' := (hQ'sub hq2).2
      have h1' : |d + δ'| ≤ comparison * δ' := by
        have h_eq : d + δ' = (y + δ') - z := by
          simp [hd_def, hy_def, hz_def]; ring
        rw [h_eq]; exact h1
      have h2' : |d - δ'| ≤ comparison * δ' := by
        have h_eq : d - δ' = (y - δ') - z := by
          simp [hd_def, hy_def, hz_def]; ring
        rw [h_eq]; exact h2
      have h_upper : d ≤ (comparison - 1) * δ' := by
        have h3 : d + δ' ≤ comparison * δ' := (abs_le.mp h1').2
        linarith
      have h_lower : -((comparison - 1) * δ') ≤ d := by
        have h4 : -(comparison * δ') ≤ d - δ' := (abs_le.mp h2').1
        have h5 : -((comparison - 1) * δ') = -(comparison * δ') + δ' := by ring
        rw [h5]
        linarith
      have hdist : |d| ≤ (comparison - 1) * δ' := by
        rw [abs_le]; exact ⟨h_lower, h_upper⟩
      have hsum1 : |p.2 - z| ≤ |p.2 - y| + |y - z| := abs_sub_le _ _ _
      have hsum2 : |p.2 - y| + |y - z| ≤ δ + (comparison - 1) * δ' := by
        have h6 : |p.2 - y| ≤ δ := hp.2
        have h7 : |y - z| ≤ (comparison - 1) * δ' := hdist
        linarith
      have hsum3 : δ + (comparison - 1) * δ' ≤ comparison * δ := by
        have h8 : (comparison - 1) * δ' ≤ (comparison - 1) * δ :=
          mul_le_mul_of_nonneg_left hδ'_le (by linarith)
        linarith
      have hfinal : |p.2 - z| ≤ comparison * δ := by
        calc
          |p.2 - z| ≤ |p.2 - y| + |y - z| := hsum1
          _ ≤ δ + (comparison - 1) * δ' := hsum2
          _ ≤ comparison * δ := hsum3
      exact ⟨hpxU, hfinal⟩
    have hRsub : R.carrier ⊆ V.carrier := htransfer R hR'sub
    have hSsub : S.carrier ⊆ V.carrier := htransfer S hS'sub
    exact h ⟨V, hU'_fam, Set.union_subset hRsub hSsub⟩
  · exact hcomparable

end CurvilinearRectangle

namespace RectangleFamily

def rescale {δ t δ' r : ℝ} (R : RectangleFamily δ t)
    (hratio : δ' / r = δ / t) : RectangleFamily δ' r :=
  { card := R.card
    rectangle := fun i => (R.rectangle i).rescale hratio }

lemma IsPairwiseIncomparable.rescale {δ t δ' r : ℝ}
    {R : RectangleFamily δ t} {family : Set C2Function} {comparison : ℝ}
    (hδ : 0 < δ) (hδ' : 0 < δ') (hδ'_le : δ' ≤ δ)
    (hratio : δ' / r = δ / t) (hcomparison : 1 ≤ comparison)
    (h : R.IsPairwiseIncomparable family comparison) :
    (R.rescale hratio).IsPairwiseIncomparable family comparison := by
  intro i j hij
  exact (h i j hij).rescale (by linarith) hδ' hδ'_le hratio hcomparison

lemma IsOverCentralQuarterOf.rescale {δ t δ' r : ℝ}
    {R : RectangleFamily δ t} {I : ParameterInterval}
    (h : R.IsOverCentralQuarterOf I)
    (hratio : δ' / r = δ / t) :
    (R.rescale hratio).IsOverCentralQuarterOf I := by
  intro i
  exact (h i).rescale hratio

lemma CentersIn.rescale {δ t δ' r : ℝ}
    {R : RectangleFamily δ t} {family : Set C2Function}
    (h : R.CentersIn family)
    (hratio : δ' / r = δ / t) :
    (R.rescale hratio).CentersIn family := by
  dsimp only [CentersIn]
  intro i
  have hcard : (R.rescale hratio).card = R.card := by rfl
  let j : Fin R.card := Fin.cast hcard i
  have h1 : (R.rescale hratio).rectangle i = (R.rectangle j).rescale hratio := by
    unfold RectangleFamily.rescale
    congr
  have h2 : ((R.rescale hratio).rectangle i).function = (R.rectangle j).function := by
    rw [h1]; rfl
  rw [h2]
  exact h j

lemma Nonempty.rescale {δ t δ' r : ℝ} {R : RectangleFamily δ t}
    (h : R.Nonempty) (hratio : δ' / r = δ / t) :
    (R.rescale hratio).Nonempty := h

lemma tangentCount_rescale_le {δ t δ' r : ℝ}
    {R : CurvilinearRectangle δ t} {F : FiniteFunctionFamily}
    {lambda lambda' : ℝ}
    (hδ'_le : δ' ≤ δ)
    (hbound : lambda * δ ≤ lambda' * δ')
    (hratio : δ' / r = δ / t) :
    RectangleFamily.tangentCount R F lambda ≤
      RectangleFamily.tangentCount (R.rescale hratio) F lambda' := by
  classical
  apply Finset.card_le_card
  intro f hf
  have h1 : f ∈ F.toFinset := (Finset.mem_filter.mp hf).1
  have h2 : R.IsLambdaTangent f lambda := (Finset.mem_filter.mp hf).2
  have h3 : (R.rescale hratio).IsLambdaTangent f lambda' :=
    h2.rescale hδ'_le hbound hratio
  exact Finset.mem_filter.mpr ⟨h1, h3⟩

end RectangleFamily

/--
Comparability is monotone in the comparison constant: if two rectangles fit
inside a `λ₁δ`-thick rectangle, they also fit inside a `λ₂δ`-thick rectangle
when `λ₁ ≤ λ₂` and the larger scale is admissible.
-/
lemma AreLambdaComparable.mono {δ t : ℝ}
    {R S : CurvilinearRectangle δ t} {family : Set C2Function}
    {lambda₁ lambda₂ : ℝ} (hle : lambda₁ ≤ lambda₂)
    (hδ : 0 < δ) (ht : 0 < t)
    (hadm : IsAdmissibleComparisonScale δ t lambda₂)
    (hcomp : R.AreLambdaComparable S family lambda₁) :
    R.AreLambdaComparable S family lambda₂ := by
  rcases hcomp with ⟨U, hUfam, hUsub⟩
  let l : ℝ := Real.sqrt (lambda₁ * δ / t)
  let L : ℝ := Real.sqrt (lambda₂ * δ / t)
  have hL_nonneg : 0 ≤ L := Real.sqrt_nonneg _
  have hle_L : l ≤ L := by
    apply Real.sqrt_le_sqrt
    gcongr
  have hL_le_one : L ≤ 1 := by
    have h : lambda₂ * δ / t ≤ 1 := by
      rw [div_le_one ht] <;> exact hadm.2
    exact Real.sqrt_le_one.mpr h
  let a := U.interval.left
  let b := U.interval.right
  have ha0 : 0 ≤ a := U.interval.left_mem.1
  have hb1 : b ≤ 1 := U.interval.right_mem.2
  have hUlen : b - a = l := U.interval_length
  have hlen_le : b - a ≤ L := hUlen ▸ hle_L
  let jleft : ℝ := max 0 (b - L)
  let jright : ℝ := jleft + L
  have hj0 : 0 ≤ jleft := by positivity
  have hj1 : jleft ≤ 1 := by
    have h : b - L ≤ 1 := by linarith
    exact max_le_iff.mpr ⟨by norm_num, h⟩
  have hjr1 : jright ≤ 1 := by
    dsimp only [jleft, jright]
    by_cases hcase : b - L ≤ 0
    · rw [max_eq_left hcase] <;> linarith
    · rw [max_eq_right (by linarith)] <;> linarith
  have hjle : jleft ≤ jright := by linarith [hL_nonneg]
  have h_a_ge : jleft ≤ a := by
    dsimp only [jleft]
    by_cases hcase : b - L ≤ 0
    · rw [max_eq_left hcase] <;> linarith
    · rw [max_eq_right (by linarith)] <;> linarith [hlen_le]
  have h_b_le : b ≤ jright := by
    dsimp only [jleft, jright]
    by_cases hcase : b - L ≤ 0
    · rw [max_eq_left hcase] <;> linarith
    · rw [max_eq_right (by linarith)] <;> linarith
  let J : ParameterInterval :=
    { left := jleft
      right := jright
      left_mem := ⟨hj0, hj1⟩
      right_mem := ⟨by linarith, hjr1⟩
      left_le_right := hjle }
  have hJlen : J.length = L := by
    dsimp only [J, ParameterInterval.length] <;> ring
  have hUcarrier_sub : U.interval.carrier ⊆ J.carrier := by
    intro x hx
    exact ⟨h_a_ge.trans hx.1, hx.2.trans h_b_le⟩
  let U' : CurvilinearRectangle (lambda₂ * δ) t :=
    { function := U.function
      interval := J
      interval_length := hJlen }
  have hsub : R.carrier ∪ S.carrier ⊆ U'.carrier := by
    intro p hp
    have hpinU : p ∈ U.carrier := hUsub hp
    have hpxJ : p.1 ∈ J.carrier := hUcarrier_sub hpinU.1
    have hpy : |p.2 - U.function p.1| ≤ lambda₁ * δ := hpinU.2
    have hpy' : |p.2 - U.function p.1| ≤ lambda₂ * δ :=
      hpy.trans (mul_le_mul_of_nonneg_right hle (by linarith))
    exact ⟨hpxJ, hpy'⟩
  exact ⟨U', hUfam, hsub⟩

/-- Pairwise incomparability at a larger λ implies incomparability at a smaller λ. -/
lemma IsPairwiseIncomparable.mono {δ t : ℝ}
    {R : RectangleFamily δ t} {family : Set C2Function}
    {lambda_small lambda_large : ℝ} (hle : lambda_small ≤ lambda_large)
    (hδ : 0 < δ) (ht : 0 < t)
    (hadm : IsAdmissibleComparisonScale δ t lambda_large)
    (h : R.IsPairwiseIncomparable family lambda_large) :
    R.IsPairwiseIncomparable family lambda_small := by
  intro i j hij
  have h' : (R.rectangle i).AreLambdaIncomparable (R.rectangle j) family lambda_large :=
    h i j hij
  intro hcomp
  exact h' (AreLambdaComparable.mono hle hδ ht hadm hcomp)

namespace FiniteFunctionFamily

lemma AreSeparated.scale_transfer {W B : FiniteFunctionFamily}
    {t r A : ℝ} (hr : r = t / (2 * A)) :
    W.AreSeparated B (2 * r) ↔ W.AreSeparated B (t / A) := by
  have h : 2 * r = t / A := by
    rw [hr]; ring
  rw [h]

end FiniteFunctionFamily

end Kakeya.Cinematic
