module

/-
  Reusable utilities extracted from deprecated slope-splitting files.

  These lemmas are independent of the archived MainAppendix slope route and
  may be useful in the canonical integration.

  Contents:
  - External covering number: cover bound, isometry invariance, union subadditivity
  - IsDeltaSSet: half-subset lemma (subset with ≥ half covering inherits S-set)
  - Real analysis: δ^{-η} monotonicity in η for 0 < δ ≤ 1
-/
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

namespace SlopeUtilities

/-! ### External covering number utilities -/

/-- If `C` is an `ε`-cover of `A`, then the external covering number is at most `|C|`. -/
lemma externalCoveringNumber_le_of_cover {X : Type*} [PseudoMetricSpace X]
    {ε : NNReal} {A C : Set X} (hC : Metric.IsCover ε A C) :
    Metric.externalCoveringNumber ε A ≤ Set.encard C := by
  have h1 : Metric.externalCoveringNumber ε A ≤
      ⨅ (_ : Metric.IsCover ε A C), Set.encard C := by
    unfold Metric.externalCoveringNumber
    let f : Set X → ℕ∞ := fun C' => ⨅ (_ : Metric.IsCover ε A C'), Set.encard C'
    exact iInf_le f C
  have h2 : (⨅ (_ : Metric.IsCover ε A C), Set.encard C) ≤ Set.encard C := by
    let f : Metric.IsCover ε A C → ℕ∞ := fun _ => Set.encard C
    exact iInf_le f hC
  exact le_trans h1 h2

/-- External covering number is preserved under an isometry equivalence. -/
lemma externalCoveringNumber_equiv {X : Type*} [PseudoMetricSpace X]
    {ε : NNReal} {A : Set X} (e : X ≃ X) (he : Isometry e) :
    Metric.externalCoveringNumber ε (e '' A) = Metric.externalCoveringNumber ε A := by
  have h1 : ∀ (C : Set X), Metric.IsCover ε A C →
      Metric.IsCover ε (e '' A) (e '' C) := by
    intro C hC
    have h_iff : Metric.IsCover ε (e '' A) (e '' C) ↔ Metric.IsCover ε A C :=
      Isometry.isCover_image_iff (s := A) he C
    exact h_iff.mpr hC
  have h2 : ∀ (C : Set X), Metric.IsCover ε (e '' A) C →
      Metric.IsCover ε A (e.symm '' C) := by
    intro C hC
    have h_iff : Metric.IsCover ε (e.symm '' (e '' A)) (e.symm '' C) ↔
        Metric.IsCover ε (e '' A) C :=
      Isometry.isCover_image_iff (s := e '' A)
        (show Isometry e.symm from by
          intro x y
          have h4 : edist (e (e.symm x)) (e (e.symm y)) = edist (e.symm x) (e.symm y) := he (e.symm x) (e.symm y)
          have h5 : e (e.symm x) = x := by simp
          have h6 : e (e.symm y) = y := by simp
          rw [h5, h6] at h4
          exact h4.symm) C
    have h3 : e.symm '' (e '' A) = A := by
      ext x
      simp [Set.image_image] <;> tauto
    rw [h3] at h_iff
    exact h_iff.mpr hC
  have h3 : ∀ (C : Set X), Set.encard (e '' C) = Set.encard C := by
    intro C
    exact e.injective.encard_image C
  have h4 : ∀ (C : Set X), Set.encard (e.symm '' C) = Set.encard C := by
    intro C
    exact e.symm.injective.encard_image C
  have h_le1 : Metric.externalCoveringNumber ε (e '' A) ≤
      Metric.externalCoveringNumber ε A := by
    have h : ∀ (C : Set X) (hC : Metric.IsCover ε A C),
        Metric.externalCoveringNumber ε (e '' A) ≤ Set.encard C := by
      intro C hC
      have h5 : Metric.IsCover ε (e '' A) (e '' C) := h1 C hC
      have h6 : Metric.externalCoveringNumber ε (e '' A) ≤ Set.encard (e '' C) :=
        externalCoveringNumber_le_of_cover h5
      rw [h3 C] at h6
      exact h6
    exact le_iInf₂ h
  have h_le2 : Metric.externalCoveringNumber ε A ≤
      Metric.externalCoveringNumber ε (e '' A) := by
    have h : ∀ (C : Set X) (hC : Metric.IsCover ε (e '' A) C),
        Metric.externalCoveringNumber ε A ≤ Set.encard C := by
      intro C hC
      have h5 : Metric.IsCover ε A (e.symm '' C) := h2 C hC
      have h6 : Metric.externalCoveringNumber ε A ≤ Set.encard (e.symm '' C) :=
        externalCoveringNumber_le_of_cover h5
      rw [h4 C] at h6
      exact h6
    exact le_iInf₂ h
  exact le_antisymm h_le1 h_le2

/-- External covering number is subadditive over union. -/
lemma externalCoveringNumber_union_le {X : Type*} [PseudoMetricSpace X]
    {ε : NNReal} {A B : Set X} :
    Metric.externalCoveringNumber ε (A ∪ B) ≤
      Metric.externalCoveringNumber ε A + Metric.externalCoveringNumber ε B := by
  have h1 : ∀ (CA CB : Set X), Metric.IsCover ε A CA → Metric.IsCover ε B CB →
      Metric.IsCover ε (A ∪ B) (CA ∪ CB) := by
    intro CA CB hCA hCB
    have hCA' : ∀ (x : X), x ∈ A → ∃ (y : X), y ∈ CA ∧ edist x y ≤ ε := by
      intro x hx
      simpa [Metric.IsCover, SetRel.IsCover] using hCA (x := x) hx
    have hCB' : ∀ (x : X), x ∈ B → ∃ (y : X), y ∈ CB ∧ edist x y ≤ ε := by
      intro x hx
      simpa [Metric.IsCover, SetRel.IsCover] using hCB (x := x) hx
    have h : ∀ (x : X), x ∈ A ∪ B → ∃ (y : X), y ∈ CA ∪ CB ∧ edist x y ≤ ε := by
      intro x hx
      cases hx with
      | inl hxA =>
        rcases hCA' x hxA with ⟨y, hy1, hy2⟩
        exact ⟨y, Or.inl hy1, hy2⟩
      | inr hxB =>
        rcases hCB' x hxB with ⟨y, hy1, hy2⟩
        exact ⟨y, Or.inr hy1, hy2⟩
    simpa [Metric.IsCover, SetRel.IsCover] using h
  have h2 : ∀ (CA CB : Set X), Set.encard (CA ∪ CB) ≤ Set.encard CA + Set.encard CB :=
    fun CA CB => Set.encard_union_le CA CB
  let N := Metric.externalCoveringNumber ε (A ∪ B)
  have h3 : ∀ (CA : Set X) (hCA : Metric.IsCover ε A CA)
      (CB : Set X) (hCB : Metric.IsCover ε B CB),
      N ≤ Set.encard CA + Set.encard CB := by
    intro CA hCA CB hCB
    have h4 : Metric.IsCover ε (A ∪ B) (CA ∪ CB) := h1 CA CB hCA hCB
    have h5 : N ≤ Set.encard (CA ∪ CB) := externalCoveringNumber_le_of_cover h4
    exact le_trans h5 (h2 CA CB)
  exact ENat.le_iInf₂_add_iInf₂ h3

/-! ### IsDeltaSSet utilities -/

/-- A subset `S'` of a `(δ,s,C)`-set `S` with covering number at least half of `S`
    is itself a `(δ,s,2*C)`-set. -/
lemma IsDeltaSSet.half_subset {X : Type*} [PseudoMetricSpace X]
    {δ s C : ℝ} {S S' : Set X}
    (hS : IsDeltaSSet δ s C S)
    (hS'_sub : S' ⊆ S)
    (h_half : (Metric.externalCoveringNumber δ.toNNReal S : ENNReal) ≤
               2 * (Metric.externalCoveringNumber δ.toNNReal S')) :
    IsDeltaSSet δ s (2 * C) S' := by
  rcases hS with ⟨hS_nonempty, hδ_pos, hC_pos, hs_nonneg, h_main⟩
  have hC2_pos : 0 < 2 * C := by positivity
  have hS'_nonempty : S'.Nonempty := by
    by_contra h
    have h_empty : S' = ∅ := by
      simpa [Set.not_nonempty_iff_eq_empty] using h
    rw [h_empty] at h_half
    have h_zero' : (Metric.externalCoveringNumber δ.toNNReal S : ENNReal) ≤ 0 := by
      simpa [Metric.externalCoveringNumber_empty] using h_half
    have h_zero : Metric.externalCoveringNumber δ.toNNReal S = 0 := by
      have h_le : Metric.externalCoveringNumber δ.toNNReal S ≤ 0 := by exact_mod_cast h_zero'
      exact le_zero_iff.mp h_le
    have hS_empty : S = ∅ :=
      (Metric.externalCoveringNumber_eq_zero.mp h_zero)
    rw [hS_empty] at hS_nonempty
    simp at hS_nonempty
  refine' ⟨hS'_nonempty, hδ_pos, hC2_pos, hs_nonneg, _⟩
  intro x r hr
  have h_sub_set : S' ∩ Metric.closedBall x r ⊆ S ∩ Metric.closedBall x r := by
    intro y hy
    exact ⟨hS'_sub hy.1, hy.2⟩
  have h1 : Metric.externalCoveringNumber δ.toNNReal (S' ∩ Metric.closedBall x r) ≤
           Metric.externalCoveringNumber δ.toNNReal (S ∩ Metric.closedBall x r) :=
    Metric.externalCoveringNumber_mono_set h_sub_set
  have h2 : (Metric.externalCoveringNumber δ.toNNReal (S ∩ Metric.closedBall x r) : ENNReal) ≤
      ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
      (Metric.externalCoveringNumber δ.toNNReal S : ENNReal) := h_main x r hr
  have hC_nonneg : 0 ≤ C := by linarith
  calc
    (Metric.externalCoveringNumber δ.toNNReal (S' ∩ Metric.closedBall x r) : ENNReal)
      ≤ (Metric.externalCoveringNumber δ.toNNReal (S ∩ Metric.closedBall x r) : ENNReal) := by exact_mod_cast h1
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber δ.toNNReal S : ENNReal) := h2
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
          (2 * (Metric.externalCoveringNumber δ.toNNReal S')) := by gcongr
    _ = ENNReal.ofReal (2 * C) * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber δ.toNNReal S') := by
      have h_mul2 : ENNReal.ofReal C * (2 : ENNReal) = ENNReal.ofReal (2 * C) := by
        have h_two : (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) := by norm_cast
        have h3 : ENNReal.ofReal C * ENNReal.ofReal (2 : ℝ) = ENNReal.ofReal (C * (2 : ℝ)) :=
          (ENNReal.ofReal_mul hC_nonneg).symm
        have h4 : C * (2 : ℝ) = 2 * C := by ring
        calc
          ENNReal.ofReal C * (2 : ENNReal)
            = ENNReal.ofReal C * ENNReal.ofReal (2 : ℝ) := by rw [h_two]
          _ = ENNReal.ofReal (C * (2 : ℝ)) := h3
          _ = ENNReal.ofReal (2 * C) := by rw [h4]
      let X := Metric.externalCoveringNumber δ.toNNReal S'
      let b := (ENNReal.ofReal r) ^ s
      have h_comm : ENNReal.ofReal C * b * (2 * X) =
                       (ENNReal.ofReal C * (2 : ENNReal)) * b * X := by
        simp [mul_assoc, mul_comm, mul_left_comm] <;> ac_rfl
      calc
        ENNReal.ofReal C * b * (2 * X)
          = (ENNReal.ofReal C * (2 : ENNReal)) * b * X := h_comm
        _ = ENNReal.ofReal (2 * C) * b * X := by
          have h : ENNReal.ofReal C * (2 : ENNReal) = ENNReal.ofReal (2 * C) := h_mul2
          rw [h]

/-! ### Real analysis utilities -/

/-- For `0 < δ ≤ 1` and `η ≤ η'`, we have `δ^{-η} ≤ δ^{-η'}`.

    Since `0 < δ ≤ 1`, `Real.rpow δ` is antitone: larger exponent gives
    smaller value. So `-η' ≤ -η` implies `δ^{-η'} ≥ δ^{-η}`. -/
lemma rpow_delta_eta_weaken (δ η η' : ℝ)
    (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1) (hη_le : η ≤ η') :
    Real.rpow δ (-η) ≤ Real.rpow δ (-η') := by
  set a : ℝ := η' - η with ha_def
  have ha_nonneg : 0 ≤ a := by linarith
  have h_add : ∀ (x y : ℝ), Real.rpow δ (x + y) = Real.rpow δ x * Real.rpow δ y := by
    intro x y
    exact Real.rpow_add hδ_pos x y
  have h_eq : Real.rpow δ (-η) = Real.rpow δ (-η') * Real.rpow δ a := by
    have h1 : -η = -η' + a := by linarith
    rw [h1]
    exact h_add (-η') a
  have h_bound : Real.rpow δ a ≤ 1 := Real.rpow_le_one (by linarith) (by linarith) ha_nonneg
  have h_pos : 0 < Real.rpow δ (-η') := Real.rpow_pos_of_pos hδ_pos _
  rw [h_eq]
  have h : Real.rpow δ (-η') * Real.rpow δ a ≤ Real.rpow δ (-η') := by
    calc Real.rpow δ (-η') * Real.rpow δ a
      ≤ Real.rpow δ (-η') * 1 := by gcongr <;> linarith
    _ = Real.rpow δ (-η') := by ring
  exact h

end SlopeUtilities
