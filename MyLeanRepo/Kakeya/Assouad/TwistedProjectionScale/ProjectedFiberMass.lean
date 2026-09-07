import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberMassStatement

/-!
WZ2 Section 7: identify shaded mass with the integral of spatial
multiplicity along the fibers of the twisted projection.

## Proof route

For `q = (u,z) : Point2`, the projected fiber multiplicity is
`projectedFiberMultiplicity Y f q = ∫⁻ y, Y.pointMultiplicity (point3 (u - f z * y) y z)`.

1. **Measurability**: the fiber coordinate map `(q,y) ↦ point3 (...)` is continuous
   (since `f` is `ContDiff`), so `Y.pointMultiplicity` composed with it is measurable;
   `Measurable.lintegral_prod_right'` gives measurability in `q`.

2. **Integral identity**: by Fubini, the planar integral equals the integral over
   `Point2 × ℝ`. Change coordinates via `e23` and `e_assoc` to `ℝ × (ℝ × ℝ)` with
   coordinates `(u,(z,y))`. For each fixed `(z,y)`, translation invariance of Lebesgue
   measure in `u` removes the `f(z)*y` shift. Swap `(z,y)` to `(y,z)` and change
   coordinates back to `Point3` via `e3`. The result is `∫⁻ p, Y.pointMultiplicity p`,
   which equals `Y.mass` by `lintegral_pointMultiplicity`.

## Key lemmas

- `measurable_pointMultiplicity`, `lintegral_pointMultiplicity` from `MultiplicityRefinement`
- `lintegral_prod`, `lintegral_prod_symm'` for Fubini
- `measurePreserving_add_right` for 1D translation invariance
- `volume_preserving_piFinTwo`, `volume_preserving_piFinSuccAbove`, `volume_preserving_prodAssoc`
- `Measure.volume_eq_prod` to identify `volume` on products with `volume.prod volume`

## Whiteprint

Node: `Kakeya/Assouad/Targets/ProjectedFiberMass`
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

/-- Continuity of `point3` with continuous component functions. -/
private lemma continuous_point3_comp {α : Type*} [TopologicalSpace α]
    {x y z : α → ℝ} (hx : Continuous x) (hy : Continuous y) (hz : Continuous z) :
    Continuous (fun a : α => point3 (x a) (y a) (z a)) := by
  have h_eq : (fun a : α => point3 (x a) (y a) (z a)) =
      (fun a : α =>
        (x a) • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) +
        (y a) • EuclideanSpace.single (1 : Fin 3) (1 : ℝ) +
        (z a) • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) := by
    funext a
    simp [point3]
  rw [h_eq]
  have h1 : Continuous (fun a : α => (x a) • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) := by
    have h : Continuous (fun (t : ℝ) => t • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) := by fun_prop
    exact h.comp hx
  have h2 : Continuous (fun a : α => (y a) • EuclideanSpace.single (1 : Fin 3) (1 : ℝ)) := by
    have h : Continuous (fun (t : ℝ) => t • EuclideanSpace.single (1 : Fin 3) (1 : ℝ)) := by fun_prop
    exact h.comp hy
  have h3 : Continuous (fun a : α => (z a) • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) := by
    have h : Continuous (fun (t : ℝ) => t • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) := by fun_prop
    exact h.comp hz
  exact (h1.add h2).add h3

/-- Continuity of the fiber coordinate map `(q,y) ↦ point3 (q₀ - f(q₁)*y) y q₁`. -/
private lemma continuous_fiberCoord (f : SlopeFunction) :
    Continuous (fun p : Point2 × ℝ =>
      point3 (p.1 0 - f (p.1 1) * p.2) p.2 (p.1 1)) := by
  have hf : Continuous f := f.contDiff.continuous
  have hq0 : Continuous (fun p : Point2 × ℝ => p.1 0) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).comp continuous_fst
  have hq1 : Continuous (fun p : Point2 × ℝ => p.1 1) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1).comp continuous_fst
  have hy : Continuous (fun p : Point2 × ℝ => p.2) := continuous_snd
  have hx : Continuous (fun p : Point2 × ℝ => p.1 0 - f (p.1 1) * p.2) :=
    hq0.sub ((hf.comp hq1).mul hy)
  have h_e0 : Continuous (fun p : Point2 × ℝ => (p.1 0 - f (p.1 1) * p.2) • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) := by
    have h : Continuous (fun (x : ℝ) => x • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) := by fun_prop
    exact h.comp hx
  have h_e1 : Continuous (fun p : Point2 × ℝ => p.2 • EuclideanSpace.single (1 : Fin 3) (1 : ℝ)) := by
    have h : Continuous (fun (y : ℝ) => y • EuclideanSpace.single (1 : Fin 3) (1 : ℝ)) := by fun_prop
    exact h.comp hy
  have h_e2 : Continuous (fun p : Point2 × ℝ => p.1 1 • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) := by
    have h : Continuous (fun (z : ℝ) => z • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) := by fun_prop
    exact h.comp hq1
  have h_main : Continuous (fun p : Point2 × ℝ =>
      (p.1 0 - f (p.1 1) * p.2) • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) +
      p.2 • EuclideanSpace.single (1 : Fin 3) (1 : ℝ) +
      p.1 1 • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) :=
    (h_e0.add h_e1).add h_e2
  have h_eq : (fun p : Point2 × ℝ => point3 (p.1 0 - f (p.1 1) * p.2) p.2 (p.1 1)) =
      (fun p : Point2 × ℝ =>
        (p.1 0 - f (p.1 1) * p.2) • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) +
        p.2 • EuclideanSpace.single (1 : Fin 3) (1 : ℝ) +
        p.1 1 • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) := by
    funext p
    simp [point3]
  rw [h_eq]
  exact h_main

/-- Measure-preserving equivalence from `Point2` to `ℝ × ℝ`. -/
private def e2 : Point2 ≃ᵐ ℝ × ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans
    (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ))

private lemma e2_apply (q : Point2) : e2 q = (q 0, q 1) := by
  simp [e2, MeasurableEquiv.toLp, MeasurableEquiv.piFinTwo]

/-- Measure-preserving equivalence from `Point3` to `ℝ × (ℝ × ℝ)`. -/
private def e3 : Point3 ≃ᵐ ℝ × (ℝ × ℝ) :=
  let e31 : Point3 ≃ᵐ ℝ × (Fin 2 → ℝ) :=
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.trans
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0)
  e31.trans ((MeasurableEquiv.refl ℝ).prodCongr
    (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)))

private lemma e3_apply (p : Point3) : e3 p = (p 0, (p 1, p 2)) := by
  simp [e3, MeasurableEquiv.toLp, MeasurableEquiv.piFinSuccAbove,
    MeasurableEquiv.piFinTwo]
  aesop

/-- `e2` is volume-preserving. -/
private lemma h_e2 : MeasurePreserving e2 volume volume :=
  (PiLp.volume_preserving_ofLp (ι := Fin 2)).trans
    (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ))

/-- `e3` is volume-preserving. -/
private lemma h_e3 : MeasurePreserving e3 volume volume := by
  let e31 : Point3 ≃ᵐ ℝ × (Fin 2 → ℝ) :=
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.trans
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0)
  have h1 : MeasurePreserving e31 volume volume :=
    (PiLp.volume_preserving_ofLp (ι := Fin 3)).trans
      (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0)
  let e32 : (ℝ × (Fin 2 → ℝ)) ≃ᵐ ℝ × (ℝ × ℝ) :=
    (MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ))
  have h2 : MeasurePreserving e32 volume volume :=
    MeasurePreserving.prod (MeasurePreserving.id volume)
      (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ))
  exact h1.trans h2

theorem projected_fiber_mass :
    ProjectedFiberMassStatement := by
  intro delta F Y f

  have h_meas_pm : Measurable Y.pointMultiplicity :=
    measurable_pointMultiplicity Y

  have hf : Continuous f := f.contDiff.continuous
  have hfm : Measurable f := hf.measurable

  -- Define the fiber coordinate map
  let h : Point2 × ℝ → Point3 := fun p =>
    point3 (p.1 0 - f (p.1 1) * p.2) p.2 (p.1 1)

  have h_cont_h : Continuous h := continuous_fiberCoord f
  have h_meas_h : Measurable h := h_cont_h.measurable

  -- Part 1: Measurability of projectedFiberMultiplicity
  let g : Point2 × ℝ → ENNReal := fun p =>
    (Y.pointMultiplicity (h p) : ENNReal)

  have h_coe : Measurable (fun n : ℕ => (n : ENNReal)) :=
    measurable_from_nat
  have h_meas_g : Measurable g :=
    h_coe.comp (h_meas_pm.comp h_meas_h)

  have h1 : Measurable (projectedFiberMultiplicity Y f) := by
    have h_eq : projectedFiberMultiplicity Y f = fun q : Point2 => ∫⁻ y : ℝ, g (q, y) := by
      funext q
      rfl
    rw [h_eq]
    exact h_meas_g.lintegral_prod_right'

  -- Part 2: Integral identity
  -- Define H on ℝ × (ℝ × ℝ): H(u, (z, y)) = multiplicity(point3 (u - f(z)*y) y z)
  let H : ℝ × (ℝ × ℝ) → ENNReal := fun p =>
    (Y.pointMultiplicity (point3 (p.1 - f p.2.1 * p.2.2) p.2.2 p.2.1) : ENNReal)

  have h_meas_H : Measurable H := by
    have h_x : Continuous (fun p : ℝ × (ℝ × ℝ) => p.1 - f p.2.1 * p.2.2) := by fun_prop
    have h_y : Continuous (fun p : ℝ × (ℝ × ℝ) => p.2.2) := continuous_snd.snd
    have h_z : Continuous (fun p : ℝ × (ℝ × ℝ) => p.2.1) := continuous_snd.fst
    have h_cont : Continuous (fun p : ℝ × (ℝ × ℝ) => point3 (p.1 - f p.2.1 * p.2.2) p.2.2 p.2.1) :=
      continuous_point3_comp h_x h_y h_z
    exact h_coe.comp (h_meas_pm.comp h_cont.measurable)

  -- Define H' on ℝ × (ℝ × ℝ): H'(u, (z, y)) = multiplicity(point3 u y z)
  let H' : ℝ × (ℝ × ℝ) → ENNReal := fun p =>
    (Y.pointMultiplicity (point3 p.1 p.2.2 p.2.1) : ENNReal)

  have h_meas_H' : Measurable H' := by
    have h_u : Continuous (fun p : ℝ × (ℝ × ℝ) => p.1) := continuous_fst
    have h_y : Continuous (fun p : ℝ × (ℝ × ℝ) => p.2.2) := continuous_snd.snd
    have h_z : Continuous (fun p : ℝ × (ℝ × ℝ) => p.2.1) := continuous_snd.fst
    have h_cont : Continuous (fun p : ℝ × (ℝ × ℝ) => point3 p.1 p.2.2 p.2.1) :=
      continuous_point3_comp h_u h_y h_z
    exact h_coe.comp (h_meas_pm.comp h_cont.measurable)

  -- Define H'' on ℝ × (ℝ × ℝ): H''(u, (y, z)) = multiplicity(point3 u y z)
  let H'' : ℝ × (ℝ × ℝ) → ENNReal := fun p =>
    (Y.pointMultiplicity (point3 p.1 p.2.1 p.2.2) : ENNReal)

  have h_meas_H'' : Measurable H'' := by
    have h_u : Continuous (fun p : ℝ × (ℝ × ℝ) => p.1) := continuous_fst
    have h_y : Continuous (fun p : ℝ × (ℝ × ℝ) => p.2.1) := continuous_snd.fst
    have h_z : Continuous (fun p : ℝ × (ℝ × ℝ) => p.2.2) := continuous_snd.snd
    have h_cont : Continuous (fun p : ℝ × (ℝ × ℝ) => point3 p.1 p.2.1 p.2.2) :=
      continuous_point3_comp h_u h_y h_z
    exact h_coe.comp (h_meas_pm.comp h_cont.measurable)

  -- e_swap : ℝ × (ℝ × ℝ) ≃ᵐ ℝ × (ℝ × ℝ), maps (u, (z, y)) ↦ (u, (y, z))
  let e_swap : ℝ × (ℝ × ℝ) ≃ᵐ ℝ × (ℝ × ℝ) :=
    (MeasurableEquiv.refl ℝ).prodCongr
      (show (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) from MeasurableEquiv.prodComm)
  have h_swap2 : MeasurePreserving (Prod.swap : (ℝ × ℝ) → (ℝ × ℝ)) volume volume := by
    have hvol : (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod (volume : Measure ℝ) :=
      Measure.volume_eq_prod ℝ ℝ
    have h : MeasurePreserving (Prod.swap : (ℝ × ℝ) → (ℝ × ℝ))
        ((volume : Measure ℝ).prod (volume : Measure ℝ))
        ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
      Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    have h_map_eq : Measure.map Prod.swap (volume : Measure (ℝ × ℝ)) = (volume : Measure (ℝ × ℝ)) := by
      calc
        Measure.map Prod.swap (volume : Measure (ℝ × ℝ))
          = Measure.map Prod.swap ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by rw [hvol]
        _ = (volume : Measure ℝ).prod (volume : Measure ℝ) := h.map_eq
        _ = (volume : Measure (ℝ × ℝ)) := hvol.symm
    exact ⟨h.measurable, h_map_eq⟩
  have h_swap : MeasurePreserving e_swap volume volume :=
    MeasurePreserving.prod (MeasurePreserving.id volume) h_swap2

  -- H' (u, (z, y)) = H'' (u, (y, z)) = H'' (e_swap (u, (z, y)))
  have h_H'_H'' : ∀ (p : ℝ × (ℝ × ℝ)), H' p = H'' (e_swap p) := by
    intro ⟨u, z, y⟩
    simp [H', H'', e_swap, MeasurableEquiv.prodComm]
    rfl

  -- e23 : Point2 × ℝ ≃ᵐ (ℝ × ℝ) × ℝ
  let e23 : Point2 × ℝ ≃ᵐ (ℝ × ℝ) × ℝ :=
    e2.prodCongr (MeasurableEquiv.refl ℝ)
  have h_e23 : MeasurePreserving e23 volume volume :=
    MeasurePreserving.prod h_e2 (MeasurePreserving.id volume)

  -- e_assoc : (ℝ × ℝ) × ℝ ≃ᵐ ℝ × (ℝ × ℝ)
  let e_assoc : (ℝ × ℝ) × ℝ ≃ᵐ ℝ × (ℝ × ℝ) := MeasurableEquiv.prodAssoc
  have h_assoc : MeasurePreserving e_assoc volume volume :=
    volume_preserving_prodAssoc

  -- Show g(e23.symm(e_assoc.symm p)) = H(p) for p : ℝ × (ℝ × ℝ)
  have h_g_H : ∀ (p : ℝ × (ℝ × ℝ)),
      g (e23.symm (e_assoc.symm p)) = H p := by
    intro ⟨u, z, y⟩
    have h_e23_symm : e23.symm ((u, z), y) = (e2.symm (u, z), y) := by
      simp [e23, MeasurableEquiv.prodCongr]
    have h_eq1 : e2 (e2.symm (u, z)) = ((e2.symm (u, z)) 0, (e2.symm (u, z)) 1) := e2_apply (e2.symm (u, z))
    have h_eq2 : e2 (e2.symm (u, z)) = (u, z) := by
      rw [MeasurableEquiv.apply_symm_apply]
    have h_pair : ((e2.symm (u, z)) 0, (e2.symm (u, z)) 1) = (u, z) := h_eq1.symm.trans h_eq2
    have h1 : (e2.symm (u, z)) 0 = u := by
      exact congr_arg Prod.fst h_pair
    have h2 : (e2.symm (u, z)) 1 = z := by
      exact congr_arg Prod.snd h_pair
    simp [g, h, H]
    rfl

  -- Translation invariance: for fixed (z, y), integrate over u
  have h_translation : ∀ (zy : ℝ × ℝ),
      (∫⁻ u : ℝ, H (u, zy)) = ∫⁻ u : ℝ, H' (u, zy) := by
    intro ⟨z, y⟩
    let c : ℝ := f z * y
    dsimp only [H, H']
    have h1 : (fun u : ℝ => (Y.pointMultiplicity (point3 (u - c) y z) : ENNReal)) =
        fun u : ℝ => (Y.pointMultiplicity (point3 (u + (-c)) y z) : ENNReal) := by
      funext u; ring_nf
    rw [h1]
    have hmp : MeasurePreserving (fun u : ℝ => u + (-c)) volume volume :=
      measurePreserving_add_right volume (-c)
    have h_meas : Measurable (fun u : ℝ => (Y.pointMultiplicity (point3 u y z) : ENNReal)) :=
      h_coe.comp (h_meas_pm.comp ((continuous_point3_comp
        (continuous_id) (continuous_const) (continuous_const)).measurable))
    exact hmp.lintegral_comp h_meas

  -- Main calculation
  have h2 : (∫⁻ q : Point2, projectedFiberMultiplicity Y f q) = Y.mass := by
    calc
      (∫⁻ q : Point2, projectedFiberMultiplicity Y f q)
          = ∫⁻ q : Point2, ∫⁻ y : ℝ, g (q, y) := by
        apply lintegral_congr; intro q; rfl
      _ = ∫⁻ p : Point2 × ℝ, g p := by
        exact (lintegral_prod g h_meas_g.aemeasurable).symm
      _ = ∫⁻ p : (ℝ × ℝ) × ℝ, g (e23.symm p) := by
        let g2 : (ℝ × ℝ) × ℝ → ENNReal := fun p => g (e23.symm p)
        have h_meas_g2 : Measurable g2 := h_meas_g.comp e23.symm.measurable
        exact h_e23.lintegral_comp h_meas_g2
      _ = ∫⁻ p : ℝ × (ℝ × ℝ), g (e23.symm (e_assoc.symm p)) := by
        let g3 : ℝ × (ℝ × ℝ) → ENNReal := fun p => g (e23.symm (e_assoc.symm p))
        have h_meas_g3 : Measurable g3 := h_meas_g.comp (e23.symm.measurable.comp e_assoc.symm.measurable)
        exact h_assoc.lintegral_comp h_meas_g3
      _ = ∫⁻ p : ℝ × (ℝ × ℝ), H p := by
        rw [lintegral_congr h_g_H]
      _ = ∫⁻ zy : ℝ × ℝ, ∫⁻ u : ℝ, H (u, zy) := by
        exact lintegral_prod_symm' H h_meas_H
      _ = ∫⁻ zy : ℝ × ℝ, ∫⁻ u : ℝ, H' (u, zy) := by
        apply lintegral_congr
        exact h_translation
      _ = ∫⁻ p : ℝ × (ℝ × ℝ), H' p := by
        exact (lintegral_prod_symm' H' h_meas_H').symm
      _ = ∫⁻ p : ℝ × (ℝ × ℝ), H'' (e_swap p) := by
        rw [lintegral_congr h_H'_H'']
      _ = ∫⁻ p : ℝ × (ℝ × ℝ), H'' p := by
        exact h_swap.lintegral_comp h_meas_H''
      _ = ∫⁻ p : Point3, H'' (e3 p) := by
        exact (h_e3.lintegral_comp h_meas_H'').symm
      _ = ∫⁻ p : Point3, (Y.pointMultiplicity p : ENNReal) := by
        apply lintegral_congr
        intro p
        have h_e3_p : e3 p = (p 0, (p 1, p 2)) := e3_apply p
        rw [h_e3_p]
        dsimp only [H'']
        have h_point3 : point3 (p 0) (p 1) (p 2) = p := by
          ext i
          fin_cases i <;> simp [point3, EuclideanSpace.single]
        rw [h_point3]
      _ = Y.mass := lintegral_pointMultiplicity Y

  exact ⟨h1, h2⟩

end Kakeya.Assouad
