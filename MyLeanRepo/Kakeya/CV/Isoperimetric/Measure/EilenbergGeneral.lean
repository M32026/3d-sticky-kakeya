import MyLeanRepo.Kakeya.CV.Isoperimetric.Measure.EilenbergMultidim
import MyLeanRepo.Kakeya.CV.Isoperimetric.Measure.EilenbergD0
import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.Tactic

/-!
# General and Projection Eilenberg Inequalities

Derives the projection Eilenberg inequality from
`eilenberg_inequality_multidim` plus the d=0 Banach indicatrix theorem.

## Main results

- `general_eilenberg_d_eq_k`: For 1-Lipschitz `f : E m → E k`,
  `∫⁻ z, μH[0] (A ∩ f⁻¹{z}) ≤ μH[k] A`.
- `projection_eilenberg_inequality`: For 1-Lipschitz `π : E n → E (n-1)`,
  `∫⁻ z, μH[0] (A ∩ π⁻¹{z}) ≤ μH[n-1] A`.
-/


namespace Geometry

open MeasureTheory Metric Set ENNReal Filter Classical
open scoped MeasureTheory

/-- **d=k Eilenberg inequality** by induction on k.

For a 1-Lipschitz map `f : E m → E k` and `A : Set (E m)`:
`∫⁻ (z : E k), μH[0] (A ∩ f ⁻¹' {z}) ≤ μH[k] A`.

Proof: induction on k. Base k=0 is trivial (E 0 is a point).
Step: split f=(g,h), apply d=0 Eilenberg on each fiber of g,
Tonelli, then kestrel's multidim Eilenberg (d=1) on g. -/
theorem general_eilenberg_d_eq_k
    {m : ℕ} [Nonempty (Fin m)] {A : Set (E m)} :
    ∀ (k : ℕ), ∀ {f : E m → E k}, LipschitzWith 1 f →
      ∫⁻ (z : E k), μH[0] (A ∩ f ⁻¹' {z}) ≤ μH[k] A := by
  intro k
  induction k with
  | zero =>
    intro f hf
    have h1 : ∀ (z : E 0), μH[0] (A ∩ f ⁻¹' {z}) = μH[0] A := by
      intro z
      have h2 : f ⁻¹' {z} = Set.univ := by
        ext x
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
        exact Subsingleton.elim (f x) z
      rw [h2] <;> simp
    have hvol : volume (Set.univ : Set (E 0)) = 1 := by
      let e : E 0 ≃ᵐ (Fin 0 → ℝ) := (MeasurableEquiv.toLp 2 (Fin 0 → ℝ)).symm
      have hmp : MeasurePreserving e volume volume :=
        EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (ι := Fin 0)
      have h9 : volume (Set.univ : Set (E 0)) = volume (Set.univ : Set (Fin 0 → ℝ)) := by
        have h10 : Measure.map e volume = volume := hmp.map_eq
        have h11 : volume (Set.univ : Set (Fin 0 → ℝ)) = volume (e ⁻¹' (Set.univ : Set (Fin 0 → ℝ))) := by
          rw [←h10, Measure.map_apply hmp.measurable (MeasurableSet.univ)]
        have h12 : e ⁻¹' (Set.univ : Set (Fin 0 → ℝ)) = Set.univ := by simp
        rw [h11, h12]
      rw [h9]
      have h13 : (volume : Measure (Fin 0 → ℝ)) = Measure.dirac (default : Fin 0 → ℝ) :=
        MeasureTheory.Measure.volume_pi_eq_dirac (default : Fin 0 → ℝ)
      rw [h13] <;> simp
    have h_eq : ∫⁻ (z : E 0), μH[0] (A ∩ f ⁻¹' {z}) = μH[0] A := by
      rw [lintegral_congr h1, lintegral_const, hvol] <;> ring
    have h_cast : μH[0] A = μH[(0 : ℕ)] A := by norm_cast
    rw [h_cast] at h_eq
    exact h_eq.le
  | succ k ih =>
    intro f hf
    let g : E m → E k := EilenbergInequality.proj k ∘ f
    let h : E m → ℝ := EilenbergInequality.lastCoord k ∘ f
    have hg_lip : LipschitzWith 1 g := by
      have h : LipschitzWith (1 * 1) g := (EilenbergInequality.proj_lipschitz k).comp hf
      simpa using h
    have hh_lip : LipschitzWith 1 h := by
      have h : LipschitzWith (1 * 1) h := (EilenbergInequality.lastCoord_lipschitz k).comp hf
      simpa using h
    let e : E (k + 1) ≃ᵐ E k × ℝ := EilenbergInequality.eSplit k
    have hmp : MeasurePreserving e volume volume :=
      EilenbergInequality.eSplit_measurePreserving k

    have h_e_f : ∀ (x : E m), e (f x) = (g x, h x) := by
      intro x
      simpa [g, h] using EilenbergInequality.eSplit_apply k (f x)

    let F : E k × ℝ → ENNReal := fun p => μH[0] (A ∩ f ⁻¹' {e.symm p})

    have h_change : ∫⁻ (w : E (k + 1)), μH[0] (A ∩ f ⁻¹' {w}) =
        ∫⁻ (p : E k × ℝ), F p := by
      have h_eq1 : ∫⁻ (p : E k × ℝ), F p =
          ∫⁻ (w : E (k + 1)), F (e w) :=
        MeasureTheory.MeasurePreserving.lintegral_map_equiv F e hmp
      have h2 : (fun w : E (k + 1) => F (e w)) =
          (fun w : E (k + 1) => μH[0] (A ∩ f ⁻¹' {w})) := by
        funext w
        simp [F] <;> rfl
      rw [h2] at h_eq1
      exact h_eq1.symm

    have h_tonelli : ∫⁻ (p : E k × ℝ), F p ≤
        ∫⁻ (z : E k), ∫⁻ (t : ℝ), F (z, t) :=
      MeasureTheory.lintegral_prod_le F

    have h_fiber : ∀ (z : E k),
        ∫⁻ (t : ℝ), μH[0] (A ∩ g ⁻¹' {z} ∩ h ⁻¹' {t}) ≤
        μH[1] (A ∩ g ⁻¹' {z}) := by
      intro z
      let A_z := A ∩ g ⁻¹' {z}
      simpa using EilenbergInequality.eilenberg_inequality_d0 (hf := hh_lip) (A := A_z)

    have h_level : ∀ (z : E k) (t : ℝ),
        F (z, t) = μH[0] (A ∩ g ⁻¹' {z} ∩ h ⁻¹' {t}) := by
      intro z t
      have h4 : A ∩ g ⁻¹' {z} ∩ h ⁻¹' {t} = A ∩ f ⁻¹' {e.symm (z, t)} := by
        apply Set.ext
        intro x
        have h5 : (g x = z ∧ h x = t) ↔ f x = e.symm (z, t) := by
          constructor
          · rintro ⟨hgz, hht⟩
            have h6 : e (f x) = (z, t) := by
              rw [h_e_f x, hgz, hht]
            have h7 : e.symm (e (f x)) = f x := e.left_inv (f x)
            have h8 : e.symm (e (f x)) = e.symm (z, t) := by rw [h6]
            rw [h7] at h8
            exact h8
          · intro hfeq
            have h6 : e (f x) = (z, t) := by
              rw [hfeq]
              exact e.apply_symm_apply (z, t)
            have hgz : g x = z := by simpa [h_e_f] using congr_arg Prod.fst h6
            have hht : h x = t := by simpa [h_e_f] using congr_arg Prod.snd h6
            exact ⟨hgz, hht⟩
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
        tauto
      simpa [F] using congr_arg (μH[0]) h4.symm

    have h_kestrel : ∫⁻ (z : E k), μH[1] (A ∩ g ⁻¹' {z}) ≤ μH[(k + 1 : ℕ)] A := by
      have h_helper := EilenbergInequality.eilenberg_helper (X := E m) (d := 1) (hd := by norm_num)
      have h2 := h_helper k g A 1 (1 : ENNReal) ((k + 1 : ℕ) : ℝ)
        (by simp) (by simp [add_comm] <;> ring) hg_lip
      simpa using h2

    have h1 : ∫⁻ (w : E (k + 1)), μH[0] (A ∩ f ⁻¹' {w}) ≤
        ∫⁻ (z : E k), ∫⁻ (t : ℝ), F (z, t) :=
      le_trans (le_of_eq h_change) h_tonelli

    have h21 : ∀ (z : E k), (∫⁻ (t : ℝ), F (z, t)) ≤ μH[1] (A ∩ g ⁻¹' {z}) := by
      intro z
      have h22 : (∫⁻ (t : ℝ), F (z, t)) =
          ∫⁻ (t : ℝ), μH[0] (A ∩ g ⁻¹' {z} ∩ h ⁻¹' {t}) := by
        apply lintegral_congr
        intro t
        exact h_level z t
      rw [h22]
      exact h_fiber z

    have h2 : ∫⁻ (z : E k), ∫⁻ (t : ℝ), F (z, t) ≤
        ∫⁻ (z : E k), μH[1] (A ∩ g ⁻¹' {z}) :=
      lintegral_mono h21

    exact le_trans (le_trans h1 h2) h_kestrel

/-- **Projection Eilenberg inequality**.

For a 1-Lipschitz map `π : E n → E (n - 1)` and `A : Set (E n)`:
`∫⁻ (z : E (n - 1)), μH[0] (A ∩ π ⁻¹' {z}) ≤ μH[n - 1] A`.
-/
lemma projection_eilenberg_inequality
    {n : ℕ} (hn : 1 ≤ n) [Nonempty (Fin n)] {A : Set (E n)}
    (π : E n → E (n - 1)) (hπ : LipschitzWith 1 π) :
    ∫⁻ (z : E (n - 1)), μH[0] (A ∩ π ⁻¹' {z}) ≤ μH[n - 1] A := by
  have h := general_eilenberg_d_eq_k (m := n) (A := A) (k := n - 1) (f := π) hπ
  have h_cast : μH[↑(n - 1)] A = μH[↑n - 1] A := by
    have h_eq : (↑(n - 1) : ℝ) = (↑n - 1 : ℝ) := by
      cases n with
      | zero => omega
      | succ n' => simp [Nat.cast_add] <;> ring
    rw [h_eq]
  rw [h_cast] at h
  exact h

end Geometry
