import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.BrunnMinkowski.OneDimPL
import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.BrunnMinkowski.PLInduction

open scoped Pointwise

namespace Geometry

open MeasureTheory ENNReal Metric Set

/-!
# Prékopa–Leindler Inequality

The n-dimensional Prékopa–Leindler inequality, proved by induction on dimension
using the 1D result and Fubini's theorem.

## Proof route

1. Base case `n = 0`: `E 0` is a one-point space, PL is trivial.
2. Inductive step: PL on `E n × ℝ` follows from `prekopa_leindler_prod`
   (PL on `E n` + PL on `ℝ` via Fubini).
3. Transfer PL from `E n × ℝ` to `E (n+1)` along `(eSplit n).symm`,
   which preserves Lebesgue volume and is linear.
-/

/-- Transfer PL along a measure-preserving measurable equivalence that is
linear (preserves addition and scalar multiplication). -/
lemma transfer_me {α β : Type*}
    [NormedAddCommGroup α] [NormedSpace ℝ α] [MeasurableSpace α] [BorelSpace α]
    [NormedAddCommGroup β] [NormedSpace ℝ β] [MeasurableSpace β] [BorelSpace β]
    {μ : Measure α} {ν : Measure β}
    (e : α ≃ᵐ β)
    (hme : MeasurePreserving e μ ν)
    (h_add : ∀ (x y : α), e (x + y) = e x + e y)
    (h_smul : ∀ (c : ℝ) (x : α), e (c • x) = c • e x)
    (hPL : PrekopaLeindlerProp μ) : PrekopaLeindlerProp ν := by
  intro lam hlam1 hlam2 f g h hf hg hh hcond
  let f' : α → ℝ≥0∞ := f ∘ e
  let g' : α → ℝ≥0∞ := g ∘ e
  let h' : α → ℝ≥0∞ := h ∘ e
  have hf' : Measurable f' := hf.comp e.measurable
  have hg' : Measurable g' := hg.comp e.measurable
  have hh' : Measurable h' := hh.comp e.measurable
  have hcond' : ∀ (x y : α),
      h' ((1 - lam) • x + lam • y) ≥ f' x ^ (1 - lam) * g' y ^ lam := by
    intro x y
    have h1 : e ((1 - lam) • x + lam • y) = (1 - lam) • e x + lam • e y := by
      rw [h_add, h_smul, h_smul]
    simpa [f', g', h', h1] using hcond (e x) (e y)
  have h_main := hPL lam hlam1 hlam2 f' g' h' hf' hg' hh' hcond'
  have h_int_f : ∫⁻ x, f' x ∂μ = ∫⁻ y, f y ∂ν := hme.lintegral_comp hf
  have h_int_g : ∫⁻ x, g' x ∂μ = ∫⁻ y, g y ∂ν := hme.lintegral_comp hg
  have h_int_h : ∫⁻ x, h' x ∂μ = ∫⁻ y, h y ∂ν := hme.lintegral_comp hh
  rw [h_int_h, h_int_f, h_int_g] at h_main
  exact h_main

/-- Measurable equiv from `E n` to `Fin n → ℝ`. -/
noncomputable def eOfLp (n : ℕ) : E n ≃ᵐ (Fin n → ℝ) :=
  (EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph.toMeasurableEquiv

/-- Measurable equiv from `Fin n → ℝ` to `E n`. -/
noncomputable def eToLp (n : ℕ) : (Fin n → ℝ) ≃ᵐ E n :=
  (eOfLp n).symm

/-- `eOfLp n` preserves Lebesgue volume. -/
lemma eOfLp_measurePreserving (n : ℕ) :
    MeasurePreserving (eOfLp n) volume volume :=
  PiLp.volume_preserving_ofLp (ι := Fin n)

/-- `eToLp n` preserves Lebesgue volume. -/
lemma eToLp_measurePreserving (n : ℕ) :
    MeasurePreserving (eToLp n) volume volume :=
  PiLp.volume_preserving_toLp (ι := Fin n)

/-- `eOfLp n` preserves addition. -/
lemma eOfLp_add (n : ℕ) : ∀ (x y : E n),
    eOfLp n (x + y) = eOfLp n x + eOfLp n y := by
  intro x y; exact (EuclideanSpace.equiv (Fin n) ℝ).map_add x y

/-- `eOfLp n` preserves scalar multiplication. -/
lemma eOfLp_smul (n : ℕ) : ∀ (c : ℝ) (x : E n),
    eOfLp n (c • x) = c • eOfLp n x := by
  intro c x; exact (EuclideanSpace.equiv (Fin n) ℝ).map_smul c x

/-- `eToLp n` preserves addition. -/
lemma eToLp_add (n : ℕ) : ∀ (x y : Fin n → ℝ),
    eToLp n (x + y) = eToLp n x + eToLp n y := by
  intro x y; exact (EuclideanSpace.equiv (Fin n) ℝ).symm.map_add x y

/-- `eToLp n` preserves scalar multiplication. -/
lemma eToLp_smul (n : ℕ) : ∀ (c : ℝ) (x : Fin n → ℝ),
    eToLp n (c • x) = c • eToLp n x := by
  intro c x; exact (EuclideanSpace.equiv (Fin n) ℝ).symm.map_smul c x

/-- Coordinate-splitting measurable equivalence:
`E (n+1) ≃ᵐ E n × ℝ`, separating the last coordinate. -/
noncomputable def eSplit (n : ℕ) : E (n + 1) ≃ᵐ (E n × ℝ) :=
  (eOfLp (n + 1)).trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n))
  |>.trans (MeasurableEquiv.prodComm : (ℝ × (Fin n → ℝ)) ≃ᵐ ((Fin n → ℝ) × ℝ))
  |>.trans ((eToLp n).prodCongr (MeasurableEquiv.refl ℝ))

/-- `eSplit n` preserves Lebesgue volume. -/
lemma eSplit_measurePreserving (n : ℕ) :
    MeasurePreserving (eSplit n) volume volume := by
  have h1 : MeasurePreserving (eOfLp (n + 1)) volume volume :=
    eOfLp_measurePreserving (n + 1)
  have h2 : MeasurePreserving
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n))
      volume volume :=
    MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)
  have h_vol1 : (volume : Measure (ℝ × (Fin n → ℝ))) = Measure.prod volume volume :=
    Measure.volume_eq_prod ℝ (Fin n → ℝ)
  have h_vol2 : (volume : Measure ((Fin n → ℝ) × ℝ)) = Measure.prod volume volume :=
    Measure.volume_eq_prod (Fin n → ℝ) ℝ
  have h3 : MeasurePreserving
      (MeasurableEquiv.prodComm : (ℝ × (Fin n → ℝ)) ≃ᵐ ((Fin n → ℝ) × ℝ))
      volume volume := by
    refine' ⟨MeasurableEquiv.prodComm.measurable, _⟩
    have h_e : ((MeasurableEquiv.prodComm : (ℝ × (Fin n → ℝ)) ≃ᵐ ((Fin n → ℝ) × ℝ)) :
        (ℝ × (Fin n → ℝ)) → ((Fin n → ℝ) × ℝ)) = Prod.swap := by
      funext x; rfl
    rw [h_e, h_vol1]
    exact MeasureTheory.Measure.measurePreserving_swap.map_eq.trans h_vol2.symm
  have h4 : MeasurePreserving
      ((eToLp n).prodCongr (MeasurableEquiv.refl ℝ)) volume volume := by
    have h_vol3 : (volume : Measure ((Fin n → ℝ) × ℝ)) = Measure.prod volume volume :=
      Measure.volume_eq_prod (Fin n → ℝ) ℝ
    have h_vol4 : (volume : Measure (E n × ℝ)) = Measure.prod volume volume :=
      Measure.volume_eq_prod (E n) ℝ
    have h_prod : MeasurePreserving
        ((eToLp n).prodCongr (MeasurableEquiv.refl ℝ))
        (Measure.prod volume volume) (Measure.prod volume volume) :=
      MeasurePreserving.prod (eToLp_measurePreserving n) (MeasurePreserving.id volume)
    refine' ⟨((eToLp n).prodCongr (MeasurableEquiv.refl ℝ)).measurable, _⟩
    rw [h_vol3]
    exact h_prod.map_eq.trans h_vol4.symm
  exact h1.trans h2 |>.trans h3 |>.trans h4

/-- `piFinSuccAbove` preserves addition. -/
lemma piFinSuccAbove_add (n : ℕ) :
    ∀ (x y : Fin (n + 1) → ℝ),
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)) (x + y)
      = (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)) x
      + (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)) y := by
  intro x y
  ext <;> simp [MeasurableEquiv.piFinSuccAbove, Fin.succAbove] <;> rfl

/-- `piFinSuccAbove` preserves scalar multiplication. -/
lemma piFinSuccAbove_smul (n : ℕ) :
    ∀ (c : ℝ) (x : Fin (n + 1) → ℝ),
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)) (c • x)
      = c • (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)) x := by
  intro c x
  ext <;> simp [MeasurableEquiv.piFinSuccAbove, Fin.succAbove] <;> rfl

/-- `eSplit n` preserves addition. -/
lemma eSplit_add (n : ℕ) : ∀ (x y : E (n + 1)),
    eSplit n (x + y) = eSplit n x + eSplit n y := by
  intro x y
  have h1 : eOfLp (n + 1) (x + y) = eOfLp (n + 1) x + eOfLp (n + 1) y :=
    eOfLp_add (n + 1) x y
  have h2 := piFinSuccAbove_add n (eOfLp (n + 1) x) (eOfLp (n + 1) y)
  simp only [eSplit, MeasurableEquiv.trans_apply] at *
  <;> rw [h1, h2] <;> rfl

/-- `eSplit n` preserves scalar multiplication. -/
lemma eSplit_smul (n : ℕ) : ∀ (c : ℝ) (x : E (n + 1)),
    eSplit n (c • x) = c • eSplit n x := by
  intro c x
  have h1 : eOfLp (n + 1) (c • x) = c • eOfLp (n + 1) x :=
    eOfLp_smul (n + 1) c x
  have h2 := piFinSuccAbove_smul n c (eOfLp (n + 1) x)
  simp only [eSplit, MeasurableEquiv.trans_apply] at *
  <;> rw [h1, h2] <;> rfl

/-- The inverse `(eSplit n).symm` preserves Lebesgue volume. -/
lemma eSplit_symm_measurePreserving (n : ℕ) :
    MeasurePreserving (eSplit n).symm volume volume :=
  (eSplit_measurePreserving n).symm

/-- `(eSplit n).symm` preserves addition. -/
lemma eSplit_symm_add (n : ℕ) : ∀ (x y : E n × ℝ),
    (eSplit n).symm (x + y) = (eSplit n).symm x + (eSplit n).symm y := by
  intro x y
  apply (eSplit n).injective
  have h : eSplit n ((eSplit n).symm (x + y)) = x + y :=
    (eSplit n).apply_symm_apply (x + y)
  rw [h]
  have h2 : eSplit n ((eSplit n).symm x + (eSplit n).symm y) =
      eSplit n ((eSplit n).symm x) + eSplit n ((eSplit n).symm y) :=
    eSplit_add n ((eSplit n).symm x) ((eSplit n).symm y)
  rw [h2]
  <;> simp

/-- `(eSplit n).symm` preserves scalar multiplication. -/
lemma eSplit_symm_smul (n : ℕ) : ∀ (c : ℝ) (x : E n × ℝ),
    (eSplit n).symm (c • x) = c • (eSplit n).symm x := by
  intro c x
  apply (eSplit n).injective
  have h : eSplit n ((eSplit n).symm (c • x)) = c • x :=
    (eSplit n).apply_symm_apply (c • x)
  rw [h]
  have h2 : eSplit n (c • (eSplit n).symm x) = c • eSplit n ((eSplit n).symm x) :=
    eSplit_smul n c ((eSplit n).symm x)
  rw [h2]
  <;> simp

/-- `PrekopaLeindlerProp` for `ℝ` from the 1D theorem. -/
lemma hPL1D : PrekopaLeindlerProp (volume : Measure ℝ) := by
  intro lam hlam1 hlam2 f g h hf hg hh hcond
  have hcond' : ∀ x y, h ((1 - lam) * x + lam * y) ≥ f x ^ (1 - lam) * g y ^ lam := by
    intro x y
    have hsmul : (1 - lam) • x + lam • y = (1 - lam) * x + lam * y := by
      simp [smul_eq_mul]
    simpa [hsmul] using hcond x y
  exact prekopa_leindler_one_dim hf hg hh (t := lam) hlam1 hlam2 hcond'

/-- `PrekopaLeindlerProp` for `E 0` (one-point space). -/
lemma hPL0 : PrekopaLeindlerProp (volume : Measure (E 0)) := by
  intro lam hlam1 hlam2 f g h hf hg hh hcond
  have h_unique : ∀ (x : E 0), x = 0 := by intro x; ext i; fin_cases i
  have h_vol_eq : (volume : Measure (E 0)) = Measure.dirac 0 :=
    volume_euclideanSpace_eq_dirac (Fin 0)
  have h_vol_univ : volume (Set.univ : Set (E 0)) = 1 := by
    rw [h_vol_eq]; simp
  have h_int_f : ∫⁻ x : E 0, f x = f 0 := by
    have h : ∫⁻ x : E 0, f x = ∫⁻ x : E 0, f 0 := by
      apply lintegral_congr; intro x; rw [h_unique x]
    rw [h, lintegral_const, h_vol_univ] <;> ring
  have h_int_g : ∫⁻ x : E 0, g x = g 0 := by
    have h : ∫⁻ x : E 0, g x = ∫⁻ x : E 0, g 0 := by
      apply lintegral_congr; intro x; rw [h_unique x]
    rw [h, lintegral_const, h_vol_univ] <;> ring
  have h_int_h : ∫⁻ x : E 0, h x = h 0 := by
    have h : ∫⁻ x : E 0, h x = ∫⁻ x : E 0, h 0 := by
      apply lintegral_congr; intro x; rw [h_unique x]
    rw [h, lintegral_const, h_vol_univ] <;> ring
  rw [h_int_h, h_int_f, h_int_g]
  have h_simp : (1 - lam) • (0 : E 0) + lam • (0 : E 0) = (0 : E 0) := by simp
  have h' := hcond 0 0
  rw [h_simp] at h'
  exact h'

/-- Inductive proof that `PrekopaLeindlerProp` holds for `E n` for all `n`. -/
lemma hPLn (n : ℕ) : PrekopaLeindlerProp (volume : Measure (E n)) := by
  induction n with
  | zero => exact hPL0
  | succ n ih =>
    have h_prod0 : PrekopaLeindlerProp (Measure.prod volume volume) :=
      prekopa_leindler_prod ih hPL1D
    have h_vol_eq : (volume : Measure (E n × ℝ)) = Measure.prod volume volume :=
      Measure.volume_eq_prod (E n) ℝ
    have h_prod : PrekopaLeindlerProp (volume : Measure (E n × ℝ)) := by
      rw [h_vol_eq] at *; exact h_prod0
    exact transfer_me (eSplit n).symm
      (eSplit_symm_measurePreserving n)
      (eSplit_symm_add n) (eSplit_symm_smul n) h_prod

/-- **Prékopa–Leindler inequality.** For nonnegative measurable functions
`f, g, h` on `ℝⁿ` and `t ∈ (0,1)`, if
`h((1-t) • x + t • y) ≥ f(x)^(1-t) * g(y)^t` for all `x, y`,
then `∫ h ≥ (∫ f)^(1-t) * (∫ g)^t`. -/
theorem prekopaLeindler (n : ℕ) (t : ℝ) (ht : 0 < t) (ht' : t < 1)
    (f g h : (E n) → ENNReal)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hcond : ∀ (x y : E n),
      h ((1 - t) • x + t • y) ≥ f x ^ (1 - t) * g y ^ t) :
    ∫⁻ z, h z ≥ (∫⁻ x, f x) ^ (1 - t) * (∫⁻ y, g y) ^ t :=
  hPLn n t ht ht' f g h hf hg hh hcond

end Geometry
