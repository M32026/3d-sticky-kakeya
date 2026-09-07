import MyLeanRepo.Kakeya.Hairbrush.TwoDKakeya

/-!
# Per-bin Córdoba bound

Given a subfamily `G ⊆ F` with density `λ * |G| * V ≤ ∑_{T∈G} |Y(T)|` and a
uniform off-diagonal intersection-sum bound `C * V * log(1/δ)`, the shaded
union over `G` has volume at least `λ² * |G| * V / (1 + C * log(1/δ))`.

This adapts the Córdoba L² argument from `TwoDKakeya.lean` to the stronger
density formulation used in the hairbrush gap assembly.
-/

noncomputable section

open MeasureTheory Metric Set Finset Real

namespace Kakeya.Hairbrush

variable {δ : ℝ} {F : TubeFamily δ} {Y : Shading F}

local instance perBinCordobaDecidableEq : DecidableEq (DeltaTube δ) :=
  Classical.decEq _

/-- Restrict a shading from `F` to a subfamily `G ⊆ F`. -/
def restrictShading (G : TubeFamily δ) (hG : G ⊆ F) : Shading G :=
  { carrier := Y.carrier
    measurable_carrier := fun {_} hT => Y.measurable_carrier (hG hT)
    subset_tube := fun {_} hT => Y.subset_tube (hG hT) }

/--
Per-bin Córdoba bound.

Given a subfamily `G` with density `λ * |G| * V ≤ ∑_{T∈G} |Y(T)|` and a
uniform intersection-sum bound `C * V * log(1/δ)`, the shaded union has
volume at least `λ² * |G| * V / (1 + C * log(1/δ))`.
-/
theorem per_bin_cordoba_bound
    (_hδ : 0 < δ) (_hδ1 : δ ≤ 1)
    (G : TubeFamily δ) (hG : G ⊆ F)
    (lambda V C : ENNReal)
    (hV : ∀ T ∈ G, T.volume ≤ V)
    (hV_ne_top : V ≠ ⊤)
    (h_density : lambda * G.enncard * V ≤ ∑ T ∈ G, volume (Y.carrier T))
    (_hlog_pos : 0 < Real.log (1 / δ))
    (h_inter_sum : ∀ T ∈ G,
        ∑ U ∈ G.erase T, volume (Y.carrier T ∩ Y.carrier U) ≤
          C * V * ENNReal.ofReal (Real.log (1 / δ))) :
    volume (⋃ T ∈ G, Y.carrier T) ≥
      lambda^2 * G.enncard * V / (1 + C * ENNReal.ofReal (Real.log (1 / δ))) := by
  let YG := restrictShading (Y := Y) G hG
  let L : ENNReal := ENNReal.ofReal (Real.log (1 / δ))
  let D : ENNReal := G.enncard * V * (1 + C * L)

  have hYG_union : YG.union = ⋃ T ∈ G, Y.carrier T := by
    ext x
    simp [Shading.union]
    <;> rfl

  have hYG_mass : YG.mass = ∑ T ∈ G, volume (Y.carrier T) := by rfl

  have hYG_mass_le : YG.mass ≤ G.enncard * V := by
    calc
      YG.mass = ∑ T ∈ G, volume (Y.carrier T) := by rfl
      _ ≤ ∑ T ∈ G, T.volume := Finset.sum_le_sum fun T hT =>
        MeasureTheory.measure_mono (Y.subset_tube (hG hT))
      _ ≤ ∑ T ∈ G, V := Finset.sum_le_sum fun T hT => hV T hT
      _ = G.enncard * V := by
        simp [Finset.sum_const, TubeFamily.enncard]

  have h_offdiag : ∑ T ∈ G, ∑ U ∈ G.erase T,
        volume (Y.carrier T ∩ Y.carrier U) ≤
      G.enncard * C * V * L := by
    calc
      ∑ T ∈ G, ∑ U ∈ G.erase T, _ ≤
        ∑ T ∈ G, (C * V * L) :=
          Finset.sum_le_sum fun T hT => h_inter_sum T hT
      _ = G.enncard * C * V * L := by
        simp [Finset.sum_const, TubeFamily.enncard] <;> ring

  have h_diag : ∑ T ∈ G, volume (Y.carrier T ∩ Y.carrier T) = YG.mass := by
    have h_eq1 : ∀ T ∈ G, volume (Y.carrier T ∩ Y.carrier T) = volume (YG.carrier T) := by
      intro T hT
      have h4 : Y.carrier T ∩ Y.carrier T = Y.carrier T := by ext x; simp
      rw [h4] <;> rfl
    calc
      ∑ T ∈ G, volume (Y.carrier T ∩ Y.carrier T)
        = ∑ T ∈ G, volume (YG.carrier T) := Finset.sum_congr rfl h_eq1
      _ = YG.mass := by rfl

  have h_per_T_sum : ∀ T ∈ G, ∑ U ∈ G,
        volume (Y.carrier T ∩ Y.carrier U) =
      volume (Y.carrier T ∩ Y.carrier T) +
      ∑ U ∈ G.erase T, volume (Y.carrier T ∩ Y.carrier U) := by
    intro T hT
    let f : DeltaTube δ → ENNReal := fun U =>
      volume (Y.carrier T ∩ Y.carrier U)
    have h_G_eq : G = insert T (G.erase T) := by
      rw [Finset.insert_erase hT]
    have h_notin : T ∉ G.erase T := by simp
    have h_erase : (insert T (G.erase T)).erase T = G.erase T := by
      rw [Finset.erase_insert h_notin]
    have h_sum : ∑ U ∈ G, f U = f T + ∑ U ∈ G.erase T, f U := by
      rw [h_G_eq]
      rw [Finset.sum_insert h_notin]
      rw [h_erase] <;> rfl
    exact h_sum

  have h_sum_eq : ∑ T ∈ G, ∑ U ∈ G,
        volume (Y.carrier T ∩ Y.carrier U) =
      YG.mass + ∑ T ∈ G, ∑ U ∈ G.erase T,
        volume (Y.carrier T ∩ Y.carrier U) := by
    calc
      ∑ T ∈ G, ∑ U ∈ G, _
        = ∑ T ∈ G, (volume (Y.carrier T ∩ Y.carrier T) +
            ∑ U ∈ G.erase T, _) := Finset.sum_congr rfl h_per_T_sum
      _ = (∑ T ∈ G, volume (Y.carrier T ∩ Y.carrier T)) +
            ∑ T ∈ G, ∑ U ∈ G.erase T, _ := by
          rw [Finset.sum_add_distrib]
      _ = YG.mass + ∑ T ∈ G, ∑ U ∈ G.erase T, _ := by rw [h_diag]

  have hL2 : (∫⁻ x, (multFun YG x)^(2 : ℝ)) ≤
      YG.mass + G.enncard * C * V * L := by
    have h_eq : (∫⁻ x, (multFun YG x)^(2 : ℝ)) =
        ∑ T ∈ G, ∑ U ∈ G, volume (Y.carrier T ∩ Y.carrier U) := by
      rw [lintegral_multFun_sq (Y := YG)]
      apply Finset.sum_congr rfl
      intro T _
      apply Finset.sum_congr rfl
      intro U _
      rfl
    rw [h_eq, h_sum_eq]
    <;> gcongr

  have h_denom_bound : YG.mass + G.enncard * C * V * L ≤ D := by
    dsimp only [D]
    calc
      YG.mass + G.enncard * C * V * L
        ≤ G.enncard * V + G.enncard * C * V * L := by gcongr
      _ = G.enncard * V * (1 + C * L) := by ring

  have h_cs : YG.mass^2 ≤ volume YG.union * (∫⁻ x, (multFun YG x)^(2 : ℝ)) :=
    cordoba_cauchy_schwarz (Y := YG)

  have h_density' : lambda * G.enncard * V ≤ YG.mass := by
    rw [hYG_mass] <;> exact h_density

  have h_mass_sq : (lambda * G.enncard * V)^2 ≤ YG.mass^2 := by
    gcongr

  have h_main : (lambda * G.enncard * V)^2 ≤ volume YG.union * D := by
    calc
      (lambda * G.enncard * V)^2
        ≤ YG.mass^2 := h_mass_sq
      _ ≤ volume YG.union *
            (YG.mass + G.enncard * C * V * L) :=
          h_cs.trans (mul_le_mul_right hL2 _)
      _ ≤ volume YG.union * D := mul_le_mul_right h_denom_bound _

  by_cases h_zero : G.enncard * V = 0
  · have h1 : lambda^2 * G.enncard * V = 0 := by
      simp [h_zero, mul_assoc]
    have h_goal : lambda^2 * G.enncard * V / (1 + C * L) = 0 := by
      rw [h1] <;> simp
    rw [h_goal]
    <;> simp
  · set b := G.enncard * V with hb
    have h_b_ne_zero : b ≠ 0 := h_zero
    have h_b_ne_top : b ≠ ⊤ := by
      simp [hb, hV_ne_top, ENNReal.mul_eq_top]
      <;> tauto
    have h9 : (lambda * b)^2 = lambda^2 * b * b := by
      simp [pow_two, mul_assoc, mul_comm, mul_left_comm] <;> ring
    have h_main_b : (lambda * b)^2 ≤ volume YG.union * D := by
      have h_eq : (lambda * b)^2 = (lambda * G.enncard * V)^2 := by
        simp [hb, pow_two, mul_comm, mul_left_comm] <;> ring
      rw [h_eq]
      exact h_main
    rw [h9] at h_main_b
    have h_main' : lambda^2 * b * b ≤ volume YG.union * (1 + C * L) * b := by
      have hD : D = b * (1 + C * L) := by
        dsimp only [D] <;> simp [hb, mul_assoc] <;> ring
      rw [hD] at h_main_b
      simpa [mul_assoc, mul_comm, mul_left_comm] using h_main_b
    have h10 : lambda^2 * b ≤ volume YG.union * (1 + C * L) := by
      have h_iff : lambda^2 * b * b ≤ volume YG.union * (1 + C * L) * b ↔
          lambda^2 * b ≤ volume YG.union * (1 + C * L) :=
        ENNReal.mul_le_mul_iff_left h_b_ne_zero h_b_ne_top
      exact h_iff.mp h_main'
    have h_final : lambda^2 * b / (1 + C * L) ≤ volume YG.union :=
      ENNReal.div_le_of_le_mul h10
    have h_final' : lambda^2 * b / (1 + C * L) ≤ volume (⋃ T ∈ G, Y.carrier T) := by
      have h_vol : volume YG.union = volume (⋃ T ∈ G, Y.carrier T) := by
        rw [hYG_union]
      rw [h_vol] at h_final
      exact h_final
    have h_eq1 : lambda^2 * (G.enncard * V) = lambda^2 * G.enncard * V := by ring
    have h_eq2 : (1 + C * L) =
        (1 + C * ENNReal.ofReal (Real.log (1 / δ))) := by
      dsimp only [L]
      <;> rfl
    rw [h_eq1, h_eq2] at h_final'
    exact h_final'

end Kakeya.Hairbrush
