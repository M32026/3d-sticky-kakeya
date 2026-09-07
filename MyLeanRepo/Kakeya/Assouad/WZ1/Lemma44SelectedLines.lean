import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma44Coverage
import MyLeanRepo.Kakeya.Assouad.WZ1.MaximalSeparated

/-!
# Selected heavy lines for WZ1 Lemma 44

For each base point `b1 ∈ G₁`, construct a maximal scale-separated collection
of heavy lines through `b1`.  Every bad-pair witness line is either selected or
fails to be separated from a selected line, so the enlarged thickening of a
selected line covers the corresponding `b2`.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/--
Construct maximal separated heavy-line collections and the coverage/cardinality
properties needed by the single-scale bad-pair estimate.
-/
lemma construct_selected_lines
    (h_packing : WZ1HeavyLinePackingStatement)
    (delta lambda zeta alpha : ℝ)
    (hdelta : 0 < delta) (hdelta1 : delta < 1)
    (hlambda : 0 < lambda) (hzeta : 0 < zeta) (halpha : 0 < alpha)
    (G₁ G₂ : DiscreteSet 2)
    (hG1_nonempty : G₁.Nonempty) (hG2_nonempty : G₂.Nonempty)
    (hG1_ball : G₁.IsInUnitBall) (hG2_ball : G₂.IsInUnitBall)
    (hG1_sep : G₁.IsDeltaSeparated delta)
    (hG2_sep : G₂.IsDeltaSeparated delta)
    (hFrost1 : G₁.IsFrostman delta 1 (Kakeya.realRpowENN delta (-lambda)))
    (hFrost2 : G₂.IsFrostman delta 1 (Kakeya.realRpowENN delta (-lambda)))
    (h_mut_sep : WZ1MutuallySeparated G₁ G₂ (1 / 2))
    (h_nonconc : WZ1LineNonConcentration delta lambda zeta G₂)
    (K scale : ℝ)
    (hK : 1 ≤ K) (hscale_pos : 0 < scale) (hdelta_scale : delta ≤ scale)
    (hscale1 : scale ≤ 1)
    (hK_small : K * Real.rpow scale (1 / 4 : ℝ) < 1)
    (h13scale : 13 * scale ≤ 1) :
    ∃ (badLines : Point2 → Finset (AffineSubspace ℝ Point2))
      (M : ℕ),
      (∀ b1 ∈ G₁, (badLines b1).card ≤ M) ∧
      (∀ b1 ∈ G₁, ∀ ℓ ∈ badLines b1, b1 ∈ (ℓ : Set Point2)) ∧
      (∀ b1 ∈ G₁, ∀ ℓ ∈ badLines b1, Module.finrank ℝ ℓ.direction = 1) ∧
      (∀ b1 ∈ G₁, ∀ b2 ∈ G₂,
        WZ1BadAtScale G₁ G₂ scale K b1 b2 →
        ∃ ℓ ∈ badLines b1,
          b2 ∈ Metric.thickening (13 * scale) (ℓ : Set Point2)) ∧
      ((M : ℝ) ≤ 20 / (K ^ 2 * Real.rpow scale (1 / 2 : ℝ))) := by
  let B : ℝ := 20 / (K ^ 2 * Real.rpow scale (1 / 2 : ℝ))
  let N : ℕ := Nat.floor B
  have h_denom_pos : 0 < K ^ 2 * Real.rpow scale (1 / 2 : ℝ) := by
    have h1 : 0 < K ^ 2 := by positivity
    have h2 : 0 < Real.rpow scale (1 / 2 : ℝ) := Real.rpow_pos_of_pos hscale_pos _
    positivity
  have hB_pos : 0 < B := by
    dsimp only [B]
    positivity
  have hB_nonneg : 0 ≤ B := by linarith
  have hN_le : (N : ℝ) ≤ B := Nat.floor_le hB_nonneg
  have h_scale4 : scale ≤ 1 / 4 := by linarith
  have hK_pos : 0 < K := by linarith

  let heavy : AffineSubspace ℝ Point2 → Prop := fun ℓ =>
    ((G₂.filter fun point => point ∈ Metric.thickening scale (ℓ : Set Point2)).card : ENNReal) >
      ENNReal.ofReal (K * Real.rpow scale (1 / 4 : ℝ)) * G₂.enncard

  let P (b1 : Point2) : AffineSubspace ℝ Point2 → Prop := fun ℓ =>
    b1 ∈ (ℓ : Set Point2) ∧ Module.finrank ℝ ℓ.direction = 1 ∧ heavy ℓ

  let sep : AffineSubspace ℝ Point2 → AffineSubspace ℝ Point2 → Prop :=
    WZ1LinesSeparated scale

  have h_symm : ∀ (x y : AffineSubspace ℝ Point2), sep x y → sep y x := by
    intro x y h
    simp only [sep, WZ1LinesSeparated] at h ⊢
    intro n2 n1 hn2 hn1 horth2 horth1
    have h' := h n1 n2 hn1 hn2 horth1 horth2
    have h1 : ‖n2 - n1‖ = ‖n1 - n2‖ := by
      have h : n2 - n1 = -(n1 - n2) := by abel
      rw [h, norm_neg]
    have h2 : ‖n2 + n1‖ = ‖n1 + n2‖ := by
      have h : n2 + n1 = n1 + n2 := by abel
      rw [h]
    rw [h1, h2]
    exact h'

  have h_bound : ∀ (b1 : Point2), b1 ∈ G₁ →
      ∀ (s : Finset (AffineSubspace ℝ Point2)),
        (∀ ℓ ∈ s, P b1 ℓ) →
        (∀ ℓ1 ∈ s, ∀ ℓ2 ∈ s, ℓ1 ≠ ℓ2 → sep ℓ1 ℓ2) →
        s.card ≤ N := by
    intro b1 hb1 s hPs hseps
    have h1 : (s.card : ℝ) ≤ B :=
      h_packing delta scale K hdelta hdelta_scale h_scale4 hK_pos
        G₁ G₂ h_mut_sep b1 hb1 s
        (fun ℓ hℓ => (hPs ℓ hℓ).1)
        (fun ℓ hℓ => (hPs ℓ hℓ).2.1)
        (fun ℓ1 hℓ1 ℓ2 hℓ2 hne => hseps ℓ1 hℓ1 ℓ2 hℓ2 hne)
        (fun ℓ hℓ => (hPs ℓ hℓ).2.2)
    exact Nat.le_floor h1

  have h_exists : ∀ (b1 : Point2), b1 ∈ G₁ →
      ∃ (L : Finset (AffineSubspace ℝ Point2)),
        (∀ ℓ ∈ L, P b1 ℓ) ∧
        (∀ ℓ1 ∈ L, ∀ ℓ2 ∈ L, ℓ1 ≠ ℓ2 → sep ℓ1 ℓ2) ∧
        (∀ ℓ, P b1 ℓ → ∃ ℓ' ∈ L, ℓ = ℓ' ∨ ¬ sep ℓ ℓ') := by
    intro b1 hb1
    exact exists_maximal_separated (P b1) sep (fun {x y} h => h_symm x y h) N (h_bound b1 hb1)

  let L : Point2 → Finset (AffineSubspace ℝ Point2) := fun b1 =>
    if h : b1 ∈ G₁ then
      Classical.choose (h_exists b1 h)
    else
      ∅

  have hL_props : ∀ (b1 : Point2), b1 ∈ G₁ →
      (∀ ℓ ∈ L b1, P b1 ℓ) ∧
      (∀ ℓ1 ∈ L b1, ∀ ℓ2 ∈ L b1, ℓ1 ≠ ℓ2 → sep ℓ1 ℓ2) ∧
      (∀ ℓ, P b1 ℓ → ∃ ℓ' ∈ L b1, ℓ = ℓ' ∨ ¬ sep ℓ ℓ') := by
    intro b1 hb1
    have h3 : L b1 = Classical.choose (h_exists b1 hb1) := by
      simp [L, hb1] <;> rfl
    rw [h3]
    have h4 := Classical.choose_spec (h_exists b1 hb1)
    exact h4

  have h1_card : ∀ b1 ∈ G₁, (L b1).card ≤ N := by
    intro b1 hb1
    have hprops := hL_props b1 hb1
    exact h_bound b1 hb1 (L b1) hprops.1 hprops.2.1

  have h2_base : ∀ b1 ∈ G₁, ∀ ℓ ∈ L b1, b1 ∈ (ℓ : Set Point2) := by
    intro b1 hb1 ℓ hℓ
    exact (hL_props b1 hb1).1 ℓ hℓ |>.1

  have h3_finrank : ∀ b1 ∈ G₁, ∀ ℓ ∈ L b1, Module.finrank ℝ ℓ.direction = 1 := by
    intro b1 hb1 ℓ hℓ
    exact (hL_props b1 hb1).1 ℓ hℓ |>.2.1

  have h4_coverage : ∀ b1 ∈ G₁, ∀ b2 ∈ G₂,
      WZ1BadAtScale G₁ G₂ scale K b1 b2 →
      ∃ ℓ ∈ L b1, b2 ∈ Metric.thickening (13 * scale) (ℓ : Set Point2) := by
    intro b1 hb1 b2 hb2 hbad
    rcases hbad with ⟨ℓ_wit, hwit_base, hwit_fin, hwit_thick, hwit_heavy⟩
    have hP_wit : P b1 ℓ_wit := ⟨hwit_base, hwit_fin, hwit_heavy⟩
    have h_max := (hL_props b1 hb1).2.2 ℓ_wit hP_wit
    rcases h_max with ⟨ell, hell_in, h_case⟩
    have hP_ell : P b1 ell := (hL_props b1 hb1).1 ell hell_in
    have h_b1_ball : ‖b1‖ ≤ 1 := by
      have h : dist b1 0 ≤ 1 := hG1_ball b1 hb1
      simpa [dist_eq_norm] using h
    have h_b2_ball : ‖b2‖ ≤ 1 := by
      have h : dist b2 0 ≤ 1 := hG2_ball b2 hb2
      simpa [dist_eq_norm] using h
    rcases h_case with (h_eq | h_not_sep)
    · -- Case ℓ_wit = ell
      subst h_eq
      have h_mono : Metric.thickening scale (ℓ_wit : Set Point2) ⊆
          Metric.thickening (13 * scale) (ℓ_wit : Set Point2) :=
        Metric.thickening_mono (by linarith) (ℓ_wit : Set Point2)
      exact ⟨ℓ_wit, hell_in, h_mono hwit_thick⟩
    · -- Case ¬ sep ℓ_wit ell
      have h_cover : b2 ∈ Metric.thickening scale (ℓ_wit : Set Point2) →
          b2 ∈ Metric.thickening (13 * scale) (ell : Set Point2) :=
        coverage_enlarged_thickening hscale_pos
          h_b1_ball h_b2_ball
          hwit_base hP_ell.1
          hwit_fin hP_ell.2.1
          h_not_sep
      exact ⟨ell, hell_in, h_cover hwit_thick⟩

  exact ⟨L, N, h1_card, h2_base, h3_finrank, h4_coverage, hN_le⟩

end Kakeya.Assouad
