import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushSelfContainedLeaves
import MyLeanRepo.Kakeya.Assouad.HairbrushBalancedBroadDecomposition.MaxScoreTubesWitness
import Mathlib.Tactic

/-!
# Two-broadness verification from max-score witness

Given a shading where at every point the retained through-family equals
a witness W, prove `IsTwoBroadAtScale`.

Two cases:
- Small scale: theta/2 ≤ r ≤ theta, set thetaLocal = r
- Large scale: theta ≤ r, set thetaLocal = theta
-/

noncomputable section

open Finset Real

attribute [local instance] Classical.propDecidable

namespace Kakeya.Assouad

/-- Two-broadness when the retained through-family at every point equals
a witness W with broadness at scale r, and theta/2 ≤ r ≤ theta.
Set thetaLocal = r. -/
lemma two_broadness_small_scale {δ : ℝ} {F : Kakeya.TubeFamily δ}
    (Y : Kakeya.Shading F) (theta eta : ℝ) (_hδ : 0 < δ) (_heta : 0 < eta)
    (h_main : ∀ (x : Point3), x ∈ Y.union →
      ∃ (w : Point3) (r : ℝ) (Wx : Finset (Kakeya.DeltaTube δ)),
        ‖w‖ = 1 ∧ δ ≤ r ∧ theta / 2 ≤ r ∧ r ≤ theta ∧
        (∀ (v : Point3), ‖v‖ = 1 → ∀ (s : ℝ), δ ≤ s → s ≤ r →
          ((Wx.filter (fun T => hairbrushAcuteDirectionAngle T.direction v ≤ s)).card : ℝ) ≤
            Real.rpow (s / r) eta * (Wx.card : ℝ)) ∧
        (F.filter (fun T => x ∈ Y.carrier T)) = Wx) :
    IsTwoBroadAtScale Y theta eta := by
  intro x hx
  rcases h_main x hx with ⟨w, r, Wx, hw_norm, hrδ, h_half_r, hrθ, h_broad, h_eq⟩
  refine ⟨r, hrδ, h_half_r, hrθ, ?_⟩
  intro v hv s hsδ hsr
  have h1 : (F.filter (fun T => x ∈ Y.carrier T)) = Wx := h_eq
  simpa [h1] using h_broad v hv s hsδ hsr

/-- Two-broadness when the retained through-family at every point equals
a witness W with broadness at scale r ≥ theta. Set thetaLocal = theta. -/
lemma two_broadness_large_scale {δ : ℝ} {F : Kakeya.TubeFamily δ}
    (Y : Kakeya.Shading F) (theta eta : ℝ) (hδ : 0 < δ) (heta : 0 < eta)
    (h_thetaδ : δ ≤ theta) (h_theta_pos : 0 < theta)
    (h_main : ∀ (x : Point3), x ∈ Y.union →
      ∃ (w : Point3) (r : ℝ) (Wx : Finset (Kakeya.DeltaTube δ)),
        ‖w‖ = 1 ∧ δ ≤ r ∧ r ≤ 1 ∧ theta ≤ r ∧
        (∀ (v : Point3), ‖v‖ = 1 → ∀ (s : ℝ), δ ≤ s → s ≤ r →
          ((Wx.filter (fun T => hairbrushAcuteDirectionAngle T.direction v ≤ s)).card : ℝ) ≤
            Real.rpow (s / r) eta * (Wx.card : ℝ)) ∧
        (F.filter (fun T => x ∈ Y.carrier T)) = Wx) :
    IsTwoBroadAtScale Y theta eta := by
  intro x hx
  rcases h_main x hx with ⟨w, r, Wx, hw_norm, hrδ, hr1, hθr, h_broad, h_eq⟩
  have h_half_theta : theta / 2 ≤ theta := by linarith
  refine ⟨theta, h_thetaδ, h_half_theta, by linarith, ?_⟩
  intro v hv s hsδ hstheta
  have h_s_le_r : s ≤ r := by linarith
  have h2 : ((Wx.filter (fun T => hairbrushAcuteDirectionAngle T.direction v ≤ s)).card : ℝ) ≤
      Real.rpow (s / r) eta * (Wx.card : ℝ) :=
    h_broad v hv s hsδ h_s_le_r
  have h4 : 0 < s := lt_of_lt_of_le hδ hsδ
  have h5 : 0 < theta := h_theta_pos
  have h6 : 0 < r := lt_of_lt_of_le hδ hrδ
  have h3 : s / r ≤ s / theta := by
    exact div_le_div_of_nonneg_left (by linarith) h5 hθr
  have h3' : 0 ≤ s / r := by positivity
  have h7 : Real.rpow (s / r) eta ≤ Real.rpow (s / theta) eta :=
    Real.rpow_le_rpow h3' h3 heta.le
  have h8 : Real.rpow (s / r) eta * (Wx.card : ℝ) ≤
      Real.rpow (s / theta) eta * (Wx.card : ℝ) := by
    gcongr
  have h9 : ((F.filter (fun T => x ∈ Y.carrier T)).filter
      (fun T => hairbrushAcuteDirectionAngle T.direction v ≤ s)).card =
      (Wx.filter (fun T => hairbrushAcuteDirectionAngle T.direction v ≤ s)).card := by
    rw [h_eq]
  have h10 : (F.filter (fun T => x ∈ Y.carrier T)).card = Wx.card := by
    rw [h_eq]
  simpa [h9, h10] using le_trans h2 h8

end Kakeya.Assouad
