import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientClusterKatzTaoCardinalityInputs

/-!
# Katz--Tao cardinality of a fixed ambient cluster
-/

namespace Kakeya.Cinematic

theorem ambient_cluster_katz_tao_cardinality :
    AmbientClusterKatzTaoCardinalityStatement := by
  intro F center delta t C_KT hdelta ht hdt H
  by_cases h : 3 * t ≤ 1
  · have h1 : delta ≤ 3 * t := by
      calc
        delta ≤ t := hdt
        _ ≤ 3 * t := by linarith
    have h2 :
        ((F.carrier ∩ c2Ball center (3 * t)).ncard : ℝ) ≤
          C_KT * (3 * t / delta) :=
      H.2 center (3 * t) h1 h
    simpa [FiniteFunctionFamily.card,
      FiniteFunctionFamily.cluster] using h2
  · have h' : 1 < 3 * t := by linarith
    have h3 :
        (F.cluster center (3 * t)).card ≤ F.card :=
      cluster_card_le F center (3 * t)
    have h4 :
        ((F.cluster center (3 * t)).card : ℝ) ≤
          (F.card : ℝ) := by
      exact_mod_cast h3
    have h5 : (F.card : ℝ) ≤ C_KT / delta := H.1
    have h6 : 0 ≤ C_KT := by
      have h7 : 0 ≤ (F.card : ℝ) := by positivity
      have h8 : 0 ≤ C_KT / delta := h7.trans h5
      have h9 :
          0 ≤ (C_KT / delta) * delta :=
        mul_nonneg h8 hdelta.le
      have h10 :
          (C_KT / delta) * delta = C_KT := by
        field_simp [hdelta.ne']
      rw [h10] at h9
      exact h9
    have h10 : 1 ≤ 3 * t := by linarith
    have h11 : C_KT ≤ C_KT * (3 * t) := by
      nlinarith
    have h12 :
        C_KT / delta ≤ (C_KT * (3 * t)) / delta :=
      div_le_div_of_nonneg_right h11 hdelta.le
    have h13 :
        (C_KT * (3 * t)) / delta =
          C_KT * (3 * t / delta) := by
      ring
    rw [h13] at h12
    calc
      ((F.cluster center (3 * t)).card : ℝ) ≤
          (F.card : ℝ) := h4
      _ ≤ C_KT / delta := h5
      _ ≤ C_KT * (3 * t / delta) := h12

end Kakeya.Cinematic
