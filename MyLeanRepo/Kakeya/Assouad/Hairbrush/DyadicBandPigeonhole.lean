import MyLeanRepo.Kakeya.Assouad.Hairbrush.AcuteAngleHelpers
import MyLeanRepo.Kakeya.Hairbrush.Pigeonhole

/-!
# Dyadic angle-band pigeonhole

Given a tube family whose hairs all have acute angle at least `angleScale` from
the stem, pigeonhole a dyadic band `[σ, 2σ]` containing at least a `1/(K+1)`
fraction of the family cardinality.
-/

noncomputable section

open MeasureTheory Metric Set Finset Real

attribute [local instance] Classical.propDecidable

namespace Kakeya.Assouad

variable {δ : ℝ}

/--
Pigeonhole one dyadic acute-angle band from a family.

Every tube has acute angle at least `angleScale` and at most `π/2`.  The dyadic
bands `[2^k * angleScale, 2^(k+1) * angleScale]` for `k < K`, plus a final band
`[1, 2]`, cover all possible acute angles.  At least one band contains a
`1/(K+1)` fraction of the family.
-/
lemma dyadic_angle_band_pigeonhole {δ : ℝ} {B : Kakeya.TubeFamily δ}
    (stem : Kakeya.DeltaTube δ) (angleScale : ℝ)
    (h_as_pos : 0 < angleScale) (h_as_one : angleScale ≤ 1)
    (hB_nonempty : B.Nonempty)
    (h_angle : ∀ U ∈ B, angleScale ≤ hairbrushAcuteAngle stem U)
    (K : ℕ) (hK : K = Nat.ceil (Real.log (1 / angleScale) / Real.log 2)) :
    ∃ (k : ℕ), k ≤ K ∧
      let σ : ℕ → ℝ := fun j => if j < K then (2 : ℝ)^j * angleScale else 1
      let band : Kakeya.TubeFamily δ := B.filter (fun U => σ k ≤ hairbrushAcuteAngle stem U ∧ hairbrushAcuteAngle stem U ≤ 2 * σ k)
      band.Nonempty ∧
      (K + 1 : ENNReal) * Kakeya.TubeFamily.enncard band ≥ Kakeya.TubeFamily.enncard B := by
  let σ : ℕ → ℝ := fun j => if j < K then (2 : ℝ)^j * angleScale else 1
  let band : ℕ → Kakeya.TubeFamily δ := fun k =>
    B.filter (fun U => σ k ≤ hairbrushAcuteAngle stem U ∧ hairbrushAcuteAngle stem U ≤ 2 * σ k)
  let enncard : Kakeya.TubeFamily δ → ENNReal := Kakeya.TubeFamily.enncard
  -- The bands cover B.
  have h_cover : B ⊆ Finset.biUnion (Finset.range (K + 1)) band := by
    intro U hU
    have hα1 : angleScale ≤ hairbrushAcuteAngle stem U := h_angle U hU
    have hα2 : hairbrushAcuteAngle stem U ≤ Real.pi / 2 := hairbrushAcuteAngle_le_pi2 stem U
    rcases acute_angle_band_cover angleScale h_as_pos h_as_one K hK hα1 hα2 with ⟨k, hk_le, hk_band⟩
    have hk_in : k ∈ Finset.range (K + 1) := by
      simp only [Finset.mem_range] <;> omega
    have hU_in_band : U ∈ band k := by
      simp only [band, Finset.mem_filter] <;> exact ⟨hU, hk_band⟩
    exact Finset.mem_biUnion.mpr ⟨k, hk_in, hU_in_band⟩
  -- Cardinality of union ≤ sum of cardinalities.
  have h1 : B.card ≤ (Finset.biUnion (Finset.range (K + 1)) band).card :=
    Finset.card_le_card h_cover
  have h2 : (Finset.biUnion (Finset.range (K + 1)) band).card ≤ ∑ k ∈ Finset.range (K + 1), (band k).card :=
    Finset.card_biUnion_le
  have h3 : B.card ≤ ∑ k ∈ Finset.range (K + 1), (band k).card := by linarith
  have h_sum_cast : (↑(∑ k ∈ Finset.range (K + 1), (band k).card) : ENNReal) =
      ∑ k ∈ Finset.range (K + 1), ((band k).card : ENNReal) := by
    rw [Nat.cast_sum]
  have h3' : (B.card : ENNReal) ≤ ∑ k ∈ Finset.range (K + 1), ((band k).card : ENNReal) := by
    have h : (B.card : ENNReal) ≤ (↑(∑ k ∈ Finset.range (K + 1), (band k).card) : ENNReal) :=
      Nat.cast_le.mpr h3
    rw [h_sum_cast] at h
    exact h
  have h_sum : enncard B ≤ ∑ k ∈ Finset.range (K + 1), enncard (band k) := by
    simpa [enncard, Kakeya.TubeFamily.enncard] using h3'
  have hB_ne_top : enncard B ≠ ⊤ := by
    simp [enncard, Kakeya.TubeFamily.enncard] <;> exact ENNReal.natCast_ne_top _
  have hs_nonempty : (Finset.range (K + 1)).Nonempty := by
    simp
  -- ENNReal pigeonhole.
  rcases Kakeya.Hairbrush.ennreal_sum_pigeonhole hB_ne_top h_sum hs_nonempty with ⟨k, hk_in, hk_ge⟩
  have hk_le : k ≤ K := by
    simp only [Finset.mem_range] at hk_in <;> omega
  have h_card : (Finset.range (K + 1)).card = K + 1 := by simp
  have h4 : enncard B / ((K + 1 : ENNReal)) ≤ enncard (band k) := by
    have h5 : enncard (band k) ≥ enncard B / ↑(Finset.range (K + 1)).card := hk_ge
    rw [h_card] at h5
    have h_cast : (↑(K + 1) : ENNReal) = (↑K + 1 : ENNReal) := by norm_cast
    rw [h_cast] at h5
    exact h5.le
  have hK1_pos : (K + 1 : ENNReal) ≠ 0 := by simp
  have hK1_ne_top : (K + 1 : ENNReal) ≠ ⊤ := by simp
  have h_main : (K + 1 : ENNReal) * enncard (band k) ≥ enncard B := by
    have h6 : enncard B / ((K + 1 : ENNReal)) * (K + 1 : ENNReal) = enncard B :=
      ENNReal.div_mul_cancel hK1_pos hK1_ne_top
    have h7 : enncard B / ((K + 1 : ENNReal)) * (K + 1 : ENNReal) ≤ enncard (band k) * (K + 1 : ENNReal) := by
      gcongr
    rw [h6] at h7
    have h8 : enncard (band k) * (K + 1 : ENNReal) = (K + 1 : ENNReal) * enncard (band k) := by ring
    rw [h8] at h7
    exact h7
  have h_band_nonempty : (band k).Nonempty := by
    have h6 : 0 < enncard B := by
      simp [enncard, Kakeya.TubeFamily.enncard, hB_nonempty.card_pos]
    have h7 : 0 < enncard (band k) := by
      by_contra h8
      have h9 : enncard (band k) = 0 := by simpa using h8
      rw [h9] at h_main
      have h10 : enncard B ≤ 0 := by simpa using h_main
      have h11 : enncard B = 0 := by simpa using h10
      rw [h11] at h6
      simp at h6
    have h10 : 0 < (band k).card := by
      simpa [enncard, Kakeya.TubeFamily.enncard] using h7
    exact Finset.card_pos.mp h10
  refine ⟨k, hk_le, ?_⟩
  dsimp only
  exact ⟨h_band_nonempty, h_main⟩

end Kakeya.Assouad
