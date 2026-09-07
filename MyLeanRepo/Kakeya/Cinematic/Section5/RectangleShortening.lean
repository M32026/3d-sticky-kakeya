import MyLeanRepo.Kakeya.Cinematic.Section5.RectangleShorteningInputs

/-!
# Rectangle shortening for dyadic upper scales

Given a `(δ, h₁)` curvilinear rectangle and a larger scale `h₂ ≥ h₁`,
construct a centered `(δ, h₂)` rectangle with the same function and midpoint
but shorter horizontal interval. All containment and tangency certificates
are preserved by subset transitivity.
-/

namespace Kakeya.Cinematic

theorem rectangle_shortening :
    RectangleShorteningStatement := by
  intro delta h₁ h₂ hdelta hh₁ hh₂ hle R
  let L₂ : ℝ := Real.sqrt (delta / h₂)
  have hL₂_nonneg : 0 ≤ L₂ := Real.sqrt_nonneg _
  have hdiv : delta / h₂ ≤ delta / h₁ := by
    apply div_le_div_of_nonneg_left (by linarith) (by linarith)
    linarith
  have hL₂_le : L₂ ≤ R.interval.length := by
    have h1 : Real.sqrt (delta / h₂) ≤ Real.sqrt (delta / h₁) :=
      Real.sqrt_le_sqrt hdiv
    rw [R.interval_length] at *
    exact h1
  set left : ℝ := R.interval.midpoint - L₂ / 2 with hleft_def
  set right : ℝ := R.interval.midpoint + L₂ / 2 with hright_def
  have hmid_left : R.interval.midpoint - R.interval.length / 2 = R.interval.left := by
    simp [ParameterInterval.midpoint, ParameterInterval.length]
    ; linarith
  have hmid_right : R.interval.midpoint + R.interval.length / 2 = R.interval.right := by
    simp [ParameterInterval.midpoint, ParameterInterval.length]
    ; linarith
  have hleft_ge_Rleft : R.interval.left ≤ left := by
    rw [←hmid_left]
    linarith [hL₂_le]
  have hright_le_Rright : right ≤ R.interval.right := by
    rw [←hmid_right]
    linarith [hL₂_le]
  have hleft_mem : left ∈ unitInterval := by
    have h0 : 0 ≤ R.interval.left := R.interval.left_mem.1
    have h1 : R.interval.right ≤ 1 := R.interval.right_mem.2
    exact ⟨by linarith, by linarith [hright_le_Rright]⟩
  have hright_mem : right ∈ unitInterval := by
    have h0 : 0 ≤ R.interval.left := R.interval.left_mem.1
    have h1 : R.interval.right ≤ 1 := R.interval.right_mem.2
    exact ⟨by linarith [hleft_ge_Rleft], by linarith⟩
  have hleft_le_right : left ≤ right := by linarith [hL₂_nonneg]
  let S_interval : ParameterInterval :=
    { left := left
      right := right
      left_mem := hleft_mem
      right_mem := hright_mem
      left_le_right := hleft_le_right }
  have hS_length : S_interval.length = L₂ := by
    simp [S_interval, ParameterInterval.length, hleft_def, hright_def]
  have hS_midpoint : S_interval.midpoint = R.interval.midpoint := by
    simp [S_interval, ParameterInterval.midpoint, hleft_def, hright_def]
  let S : CurvilinearRectangle delta h₂ :=
    { function := R.function
      interval := S_interval
      interval_length := hS_length }
  refine' ⟨S, _⟩
  have hfunc : S.function = R.function := by rfl
  have hmid : S.interval.midpoint = R.interval.midpoint := hS_midpoint
  have hcarrier_subset : S.interval.carrier ⊆ R.interval.carrier := by
    intro x hx
    have h1 : S.interval.left ≤ (x : ℝ) := hx.1
    have h2 : (x : ℝ) ≤ S.interval.right := hx.2
    exact ⟨by linarith [hleft_ge_Rleft], by linarith [hright_le_Rright]⟩
  have hvertical_subset : S.carrier ⊆ R.carrier := by
    intro p hp
    have h1 : p.1 ∈ S.interval.carrier := hp.1
    have h2 : |p.2 - S.function p.1| ≤ delta := hp.2
    exact ⟨hcarrier_subset h1, by rwa [hfunc] at *⟩
  have hmidpoint_preserve : ∀ p ∈ R.carrier, (p.1 : ℝ) = R.interval.midpoint → p ∈ S.carrier := by
    intro p hp hpmid
    have h2 : |p.2 - R.function p.1| ≤ delta := hp.2
    have h3 : (p.1 : ℝ) = S.interval.midpoint := by
      rw [hS_midpoint]
      exact hpmid
    have h4 : p.1 ∈ S.interval.carrier := by
      have h5 : S.interval.left ≤ S.interval.midpoint := by
        simp [ParameterInterval.midpoint]
        linarith
      have h6 : S.interval.midpoint ≤ S.interval.right := by
        simp [ParameterInterval.midpoint]
        linarith
      exact ⟨by rw [h3]; exact h5, by rw [h3]; exact h6⟩
    exact ⟨h4, by rwa [hfunc]⟩
  have hcentral : ∀ (I : ParameterInterval), R.IsOverCentralQuarterOf I → S.IsOverCentralQuarterOf I := by
    intro I hI
    exact subset_trans hcarrier_subset hI
  have htangent : ∀ (f : C2Function) (lambda : ℝ), R.IsLambdaTangent f lambda → S.IsLambdaTangent f lambda := by
    intro f lambda hT p hp
    exact hT p (hvertical_subset hp)
  exact ⟨hfunc, hmid, hcarrier_subset, hvertical_subset, hmidpoint_preserve, hcentral, htangent⟩

end Kakeya.Cinematic
