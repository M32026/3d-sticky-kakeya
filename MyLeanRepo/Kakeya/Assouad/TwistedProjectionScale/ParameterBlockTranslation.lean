import MyLeanRepo.Kakeya.Assouad.Inputs
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterClusterCinematic
import MyLeanRepo.Kakeya.Cinematic.Translation
import Mathlib.MeasureTheory.Group.Prod

/-!
# Cinematic translation of parameter blocks

Translating `(a,b,d)` by `(a₀,b₀,d₀)` adds the same cinematic curve to every
member of the block.  Common addition preserves the `C²` metric and hence
separation and Katz--Tao bounds.  On the projection plane it acts by the
fiberwise translation `(t,y) ↦ (t,y+h(t))`, which preserves planar Lebesgue
measure.
-/

noncomputable section

open MeasureTheory Set

namespace Kakeya.Cinematic

namespace C2Function

/-- Pointwise addition of two cinematic two-jets. -/
def add (g h : C2Function) : C2Function where
  value := g.value + h.value
  firstDeriv := g.firstDeriv + h.firstDeriv
  secondDeriv := g.secondDeriv + h.secondDeriv
  hasExtension := by
    let extension : ℝ → ℝ := fun x => g.extension x + h.extension x
    have hg : ContDiff ℝ 2 g.extension := g.extension_contDiff
    have hh : ContDiff ℝ 2 h.extension := h.extension_contDiff
    have hgh : ContDiff ℝ 2 extension := hg.add hh
    have hg_diff : Differentiable ℝ g.extension :=
      hg.differentiable (by norm_num)
    have hh_diff : Differentiable ℝ h.extension :=
      hh.differentiable (by norm_num)
    have hderiv :
        deriv extension =
          fun x => deriv g.extension x + deriv h.extension x := by
      funext x
      exact deriv_add (hg_diff.differentiableAt) (hh_diff.differentiableAt)
    have hg_deriv_cd : ContDiff ℝ 1 (deriv g.extension) :=
      hg.deriv'
    have hh_deriv_cd : ContDiff ℝ 1 (deriv h.extension) :=
      hh.deriv'
    have hg_deriv_diff : Differentiable ℝ (deriv g.extension) :=
      hg_deriv_cd.differentiable (by norm_num)
    have hh_deriv_diff : Differentiable ℝ (deriv h.extension) :=
      hh_deriv_cd.differentiable (by norm_num)
    refine ⟨extension, hgh, ?_, ?_, ?_⟩
    · intro x
      simp [extension]
    · intro x
      rw [hderiv]
      simp
    · intro x
      rw [hderiv]
      have hsecond :
          deriv
              (fun y =>
                deriv g.extension y + deriv h.extension y)
              (x : ℝ) =
            deriv (deriv g.extension) x +
              deriv (deriv h.extension) x :=
        deriv_add
          (hg_deriv_diff.differentiableAt)
          (hh_deriv_diff.differentiableAt)
      rw [hsecond]
      simp

@[simp]
lemma add_apply (g h : C2Function) (x : UnitPoint) :
    (g.add h) x = g x + h x := by
  rfl

@[simp]
lemma add_firstDeriv (g h : C2Function) :
    (g.add h).firstDeriv = g.firstDeriv + h.firstDeriv := by
  rfl

@[simp]
lemma add_secondDeriv (g h : C2Function) :
    (g.add h).secondDeriv = g.secondDeriv + h.secondDeriv := by
  rfl

@[simp]
lemma toJet_add (g h : C2Function) :
    toJet (g.add h) = toJet g + toJet h := by
  rfl

/-- Pointwise negation of a cinematic two-jet. -/
def neg (g : C2Function) : C2Function where
  value := -g.value
  firstDeriv := -g.firstDeriv
  secondDeriv := -g.secondDeriv
  hasExtension := by
    let extension : ℝ → ℝ := fun x => -g.extension x
    have hg : ContDiff ℝ 2 g.extension := g.extension_contDiff
    have hg_diff : Differentiable ℝ g.extension :=
      hg.differentiable (by norm_num)
    have hderiv :
        deriv extension = fun x => -deriv g.extension x := by
      funext x
      exact (hg_diff.differentiableAt.hasDerivAt.neg).deriv
    have hg_deriv_cd : ContDiff ℝ 1 (deriv g.extension) :=
      hg.deriv'
    have hg_deriv_diff : Differentiable ℝ (deriv g.extension) :=
      hg_deriv_cd.differentiable (by norm_num)
    refine ⟨extension, hg.neg, ?_, ?_, ?_⟩
    · intro x
      simp [extension]
    · intro x
      rw [hderiv]
      simp
    · intro x
      rw [hderiv]
      have hsecond :
          deriv (fun y => -deriv g.extension y) (x : ℝ) =
            -deriv (deriv g.extension) x :=
        (hg_deriv_diff.differentiableAt.hasDerivAt.neg).deriv
      rw [hsecond]
      simp

@[simp]
lemma neg_apply (g : C2Function) (x : UnitPoint) :
    g.neg x = -g x := by
  change (-g.value) x = -g.value x
  simp

@[simp]
lemma toJet_neg (g : C2Function) :
    toJet g.neg = -toJet g := by
  apply Prod.ext
  · rfl
  · apply Prod.ext <;> rfl

/-- Adding a jet and then its negative cancels. -/
lemma add_neg_right_cancel (g h : C2Function) :
    (g.add h.neg).add h = g := by
  apply toJet_injective
  simp only [toJet_add, toJet_neg]
  abel

/-- Common pointwise addition is an isometry of cinematic `C²` space. -/
lemma add_right_dist (g k h : C2Function) :
    dist (g.add h) (k.add h) = dist g k := by
  change
    dist (toJet (g.add h)) (toJet (k.add h)) =
      dist (toJet g) (toJet k)
  rw [toJet_add, toJet_add]
  exact dist_add_right _ _ _

lemma add_right_c2Distance (g k h : C2Function) :
    c2Distance (g.add h) (k.add h) = c2Distance g k :=
  add_right_dist g k h

lemma add_right_injective (h : C2Function) :
    Function.Injective (fun g : C2Function => g.add h) := by
  intro g k hgk
  apply toJet_injective
  have hjet := congrArg toJet hgk
  simp only [toJet_add] at hjet
  exact add_right_cancel hjet

end C2Function

namespace FiniteFunctionFamily

/-- Finite function families are determined by their carrier sets. -/
@[ext]
lemma ext {F G : FiniteFunctionFamily}
    (h : F.carrier = G.carrier) : F = G := by
  cases F with
  | mk Fcarrier Ffinite =>
      cases G with
      | mk Gcarrier Gfinite =>
          simp_all

/-- Add the same cinematic two-jet to every member of a finite family. -/
def addRight (F : FiniteFunctionFamily) (h : C2Function) :
    FiniteFunctionFamily where
  carrier := (fun g => g.add h) '' F.carrier
  finite := F.finite.image _

lemma addRight_card (F : FiniteFunctionFamily) (h : C2Function) :
    (F.addRight h).card = F.card := by
  change
    ((fun g : C2Function => g.add h) '' F.carrier).ncard =
      F.carrier.ncard
  exact Set.ncard_image_of_injective _
    (C2Function.add_right_injective h)

end FiniteFunctionFamily

lemma IsDeltaSeparated.addRight
    {F : FiniteFunctionFamily} {delta : ℝ}
    (hF : F.IsDeltaSeparated delta) (h : C2Function) :
    (F.addRight h).IsDeltaSeparated delta := by
  intro g hg k hk hne
  rcases hg with ⟨g0, hg0, rfl⟩
  rcases hk with ⟨k0, hk0, rfl⟩
  have hne0 : g0 ≠ k0 := by
    intro heq
    exact hne (by rw [heq])
  simpa [C2Function.add_right_dist] using hF hg0 hk0 hne0

lemma FiniteFunctionFamily.HasKatzTaoBound.addRight
    {F : FiniteFunctionFamily} {delta constant : ℝ}
    (hF : F.HasKatzTaoBound delta constant) (h : C2Function) :
    (F.addRight h).HasKatzTaoBound delta constant := by
  constructor
  · rw [FiniteFunctionFamily.addRight_card]
    exact hF.1
  · intro center r hdelta hr
    let originalCenter : C2Function := center.add h.neg
    have hcenter : originalCenter.add h = center :=
      C2Function.add_neg_right_cancel center h
    have hball :
        (fun g : C2Function => g.add h) ''
            (F.carrier ∩ c2Ball originalCenter r) =
          (F.addRight h).carrier ∩ c2Ball center r := by
      ext g
      constructor
      · rintro ⟨g0, ⟨hg0, hg0ball⟩, rfl⟩
        refine ⟨⟨g0, hg0, rfl⟩, ?_⟩
        rw [mem_c2Ball, ← hcenter, C2Function.add_right_c2Distance]
        rwa [mem_c2Ball] at hg0ball
      · rintro ⟨⟨g0, hg0, rfl⟩, hgball⟩
        refine ⟨g0, ⟨hg0, ?_⟩, rfl⟩
        rw [mem_c2Ball]
        rw [mem_c2Ball, ← hcenter,
          C2Function.add_right_c2Distance] at hgball
        exact hgball
    have hncard :
        ((F.addRight h).carrier ∩ c2Ball center r).ncard =
          (F.carrier ∩ c2Ball originalCenter r).ncard := by
      rw [← hball, Set.ncard_image_of_injective _
        (C2Function.add_right_injective h)]
    rw [hncard]
    exact hF.2 originalCenter r hdelta hr

/-- The WZ2-local cinematic Katz--Tao predicate is also translation-invariant. -/
lemma assouadHasCinematicKatzTaoBound_addRight
    {F : FiniteFunctionFamily} {delta constant : ℝ}
    (hF : Kakeya.Assouad.HasCinematicKatzTaoBound F delta constant)
    (h : C2Function) :
    Kakeya.Assouad.HasCinematicKatzTaoBound
      (F.addRight h) delta constant := by
  simpa only [Kakeya.Assouad.HasCinematicKatzTaoBound,
    FiniteFunctionFamily.HasKatzTaoBound] using
    (FiniteFunctionFamily.HasKatzTaoBound.addRight hF h)

/-- Fiberwise translation of the projection plane by a measurable graph. -/
def fiberwiseTranslate (h : ℝ → ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1, p.2 + h p.1)

/-- The measurable equivalence underlying a fiberwise graph translation. -/
def fiberwiseTranslateEquiv
    (h : ℝ → ℝ) (hh : Measurable h) :
    ℝ × ℝ ≃ᵐ ℝ × ℝ where
  toFun := fiberwiseTranslate h
  invFun := fun p => (p.1, p.2 - h p.1)
  left_inv := by
    intro p
    ext <;> simp [fiberwiseTranslate]
  right_inv := by
    intro p
    ext <;> simp [fiberwiseTranslate]
  measurable_toFun :=
    measurable_fst.prodMk
      (measurable_snd.add (hh.comp measurable_fst))
  measurable_invFun :=
    measurable_fst.prodMk
      (measurable_snd.sub (hh.comp measurable_fst))

/-- Fiberwise graph translation preserves planar Lebesgue measure. -/
lemma fiberwiseTranslate_measurePreserving
    (h : ℝ → ℝ) (hh : Measurable h) :
    MeasurePreserving (fiberwiseTranslate h) volume volume := by
  have hprod :
      MeasurePreserving (fiberwiseTranslate h)
        (volume.prod volume) (volume.prod volume) := by
    apply (MeasurePreserving.id volume).skew_product
      (g := fun x y => y + h x)
    · exact measurable_snd.add (hh.comp measurable_fst)
    · exact Filter.Eventually.of_forall fun x =>
        (measurePreserving_add_right volume (h x)).map_eq
  simpa [Measure.volume_eq_prod] using hprod

/-- Fiberwise graph translation preserves the volume of every set. -/
lemma volume_fiberwiseTranslate_image
    (h : ℝ → ℝ) (hh : Measurable h) (S : Set (ℝ × ℝ)) :
    volume (fiberwiseTranslate h '' S) = volume S := by
  let e := fiberwiseTranslateEquiv h hh
  have hmp : MeasurePreserving e volume volume := by
    simpa [e, fiberwiseTranslateEquiv] using
      fiberwiseTranslate_measurePreserving h hh
  have hpre :=
    MeasurePreserving.measure_preimage_equiv
      (f := e) hmp (e '' S)
  change volume (e ⁻¹' (e '' S)) = volume (e '' S) at hpre
  rw [e.injective.preimage_image] at hpre
  exact hpre.symm

/-- Adding a cinematic function translates its graph fiberwise. -/
lemma fiberwiseTranslate_functionGraph
    (g h : C2Function) :
    fiberwiseTranslate h.extension '' functionGraph g =
      functionGraph (g.add h) := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    refine ⟨hq.1, ?_⟩
    change q.2 + h.extension q.1 =
      (g.add h) ⟨q.1, hq.1⟩
    have hext :
        h.extension q.1 = h.value ⟨q.1, hq.1⟩ :=
      h.extension_eq_value ⟨q.1, hq.1⟩
    rw [hq.2, hext]
    rfl
  · rintro ⟨hp, hpval⟩
    let q : ℝ × ℝ := (p.1, p.2 - h.extension p.1)
    have hq : q ∈ functionGraph g := by
      refine ⟨hp, ?_⟩
      change p.2 - h.extension p.1 = g ⟨p.1, hp⟩
      have hext :
          h.extension p.1 = h.value ⟨p.1, hp⟩ :=
        h.extension_eq_value ⟨p.1, hp⟩
      have hpval' :
          p.2 = g.value ⟨p.1, hp⟩ +
            h.value ⟨p.1, hp⟩ := by
        exact hpval
      rw [hext, hpval']
      ring
    refine ⟨q, hq, ?_⟩
    apply Prod.ext
    · rfl
    · change p.2 - h.extension p.1 + h.extension p.1 = p.2
      ring

end Kakeya.Cinematic

namespace Kakeya.Assouad

/-- Translation of a normalized collapsed parameter point. -/
def translateParameterPoint (v p : Point 3) : Point 3 :=
  p + v

/-- Translate a finite normalized parameter pattern. -/
def translateParameterSet
    (points : DiscreteSet 3) (v : Point 3) : DiscreteSet 3 :=
  points.image (translateParameterPoint v)

/-- Slope-curve parameters add exactly as cinematic two-jets. -/
lemma slopeCurve_add
    (f : SlopeFunction) (a b d a0 b0 d0 : ℝ) :
    (slopeCurve f a b d).add (slopeCurve f a0 b0 d0) =
      slopeCurve f (a + a0) (b + b0) (d + d0) := by
  apply Kakeya.Cinematic.C2Function.toJet_injective
  apply Prod.ext
  · ext x
    simp [Kakeya.Cinematic.C2Function.toJet]
    ring
  · apply Prod.ext
    · ext x
      simp [Kakeya.Cinematic.C2Function.toJet]
      ring
    · ext x
      simp [Kakeya.Cinematic.C2Function.toJet]
      ring

/-- Normalized half-parameter translation is common cinematic addition. -/
lemma halfParameterSlopeCurve_add
    (f : SlopeFunction) (p v : Point 3) :
    halfParameterSlopeCurve f (p + v) =
      (halfParameterSlopeCurve f p).add
        (halfParameterSlopeCurve f v) := by
  simp only [halfParameterSlopeCurve, PiLp.add_apply]
  calc
    slopeCurve f
        (24 * (p 0 + v 0))
        (24 * (p 1 + v 1))
        (4 * (p 2 + v 2)) =
      slopeCurve f
        (24 * p 0 + 24 * v 0)
        (24 * p 1 + 24 * v 1)
        (4 * p 2 + 4 * v 2) := by
      congr 1 <;> ring
    _ =
      (slopeCurve f (24 * p 0) (24 * p 1) (4 * p 2)).add
        (slopeCurve f (24 * v 0) (24 * v 1) (4 * v 2)) :=
      (slopeCurve_add f
        (24 * p 0) (24 * p 1) (4 * p 2)
        (24 * v 0) (24 * v 1) (4 * v 2)).symm

/-- The half-parameter cinematic map is injective for a nonsingular slope. -/
lemma halfParameterSlopeCurve_injective
    (f : SlopeFunction) (h_ns : f.IsNonsingular) (h0 : f 0 = 0) :
    Function.Injective (halfParameterSlopeCurve f) := by
  intro p q hpq
  have hdist :
      dist p q ≤
        125 * Kakeya.Cinematic.c2Distance
          (halfParameterSlopeCurve f p)
          (halfParameterSlopeCurve f q) :=
    halfParameterSlopeCurve_dist_le f h_ns h0 p q
  have hcurve_zero :
      Kakeya.Cinematic.c2Distance
          (halfParameterSlopeCurve f p)
          (halfParameterSlopeCurve f q) = 0 := by
    rw [hpq]
    exact dist_self _
  rw [hcurve_zero, mul_zero] at hdist
  have hpqdist : dist p q = 0 := by
    exact le_antisymm
      hdist
      dist_nonneg
  exact dist_eq_zero.mp hpqdist

/-- The finite cinematic image has exactly the parameter-set cardinality. -/
lemma halfParameterCinematicFamily_card
    (f : SlopeFunction) (h_ns : f.IsNonsingular) (h0 : f 0 = 0)
    (points : DiscreteSet 3) :
    (halfParameterCinematicFamily f points).card = points.card := by
  have hcarrier :
      (halfParameterCinematicFamily f points).carrier =
        (halfParameterSlopeCurve f) '' (points : Set (Point 3)) := by
    simp [halfParameterCinematicFamily]
  rw [Kakeya.Cinematic.FiniteFunctionFamily.card, hcarrier]
  rw [Set.ncard_image_of_injective _
    (halfParameterSlopeCurve_injective f h_ns h0)]
  exact Set.ncard_coe_finset points

/-- Translating a parameter pattern translates its cinematic family. -/
lemma halfParameterCinematicFamily_translate
    (f : SlopeFunction) (points : DiscreteSet 3) (v : Point 3) :
    halfParameterCinematicFamily f (translateParameterSet points v) =
      (halfParameterCinematicFamily f points).addRight
        (halfParameterSlopeCurve f v) := by
  apply Kakeya.Cinematic.FiniteFunctionFamily.ext
  ext g
  simp only [halfParameterCinematicFamily, translateParameterSet,
    translateParameterPoint, Kakeya.Cinematic.FiniteFunctionFamily.addRight,
    Set.mem_image, Finset.mem_coe, Finset.mem_image]
  constructor
  · rintro ⟨p, ⟨q, hq, rfl⟩, rfl⟩
    exact ⟨halfParameterSlopeCurve f q, ⟨q, hq, rfl⟩,
      (halfParameterSlopeCurve_add f q v).symm⟩
  · rintro ⟨g0, ⟨q, hq, rfl⟩, rfl⟩
    exact ⟨q + v, ⟨q, hq, rfl⟩,
      halfParameterSlopeCurve_add f q v⟩

/--
The union of finitely many fiberwise translates has volume at most the number
of copies times the original volume.
-/
lemma volume_biUnion_fiberwiseTranslate_le
    (translations : DiscreteSet 3)
    (shift : Point 3 → ℝ → ℝ)
    (hshift : ∀ v ∈ translations, Measurable (shift v))
    (E : Set (ℝ × ℝ)) :
    volume
        (⋃ v ∈ translations,
          Kakeya.Cinematic.fiberwiseTranslate (shift v) '' E) ≤
      translations.card * volume E := by
  calc
    volume
        (⋃ v ∈ translations,
          Kakeya.Cinematic.fiberwiseTranslate (shift v) '' E) ≤
        ∑ v ∈ translations,
          volume
            (Kakeya.Cinematic.fiberwiseTranslate (shift v) '' E) :=
      measure_biUnion_finset_le translations _
    _ = ∑ _v ∈ translations, volume E := by
      apply Finset.sum_congr rfl
      intro v hv
      exact Kakeya.Cinematic.volume_fiberwiseTranslate_image
        (shift v) (hshift v hv) E
    _ = translations.card * volume E := by
      simp

end Kakeya.Assouad
