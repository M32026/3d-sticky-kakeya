import MyLeanRepo.Kakeya.Assouad.WZ1.ProjectionTheoremFirstLayerStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.FrostmanCoarseningHelpers

/-!
# Frostman and geometric transport under affine maps

Reusable conditional lemmas for the normalized geometry in PDF Lemma 8.13
and Proposition 8.9.
-/

namespace Kakeya.Assouad

open scoped ENNReal

/-- A nonexpansive map fixing the origin preserves the unit ball. -/
lemma DiscreteSet.isInUnitBall_map_nonexpansive
    {n : ℕ} {E : DiscreteSet n} {f : Point n → Point n}
    (hE : E.IsInUnitBall)
    (hNonexpansive : ∀ x y, dist (f x) (f y) ≤ dist x y)
    (hzero : f 0 = 0) :
    DiscreteSet.IsInUnitBall (E.image f) := by
  intro point hpoint
  rcases Finset.mem_image.mp hpoint with ⟨source, hsource, rfl⟩
  have hdist : dist (f source) 0 ≤ dist source 0 := by
    simpa [hzero] using hNonexpansive source 0
  exact hdist.trans (hE source hsource)

/-- A map with lower Lipschitz factor `m` sends `δ`-separated sets to
`m * δ`-separated sets. -/
lemma DiscreteSet.isDeltaSeparated_map_expansive
    {n : ℕ} {E : DiscreteSet n} {delta m : ℝ}
    {f : Point n → Point n}
    (hE : E.IsDeltaSeparated delta)
    (hm : 0 < m)
    (hExpand : ∀ x y, m * dist x y ≤ dist (f x) (f y)) :
    DiscreteSet.IsDeltaSeparated (E.image f) (m * delta) := by
  intro first hfirst second hsecond hne
  rcases Finset.mem_image.mp hfirst with
    ⟨sourceFirst, hsourceFirst, rfl⟩
  rcases Finset.mem_image.mp hsecond with
    ⟨sourceSecond, hsourceSecond, rfl⟩
  have hsourceNe : sourceFirst ≠ sourceSecond := by
    intro heq
    exact hne (congrArg f heq)
  calc
    m * delta ≤ m * dist sourceFirst sourceSecond := by
      gcongr
      exact hE hsourceFirst hsourceSecond hsourceNe
    _ ≤ dist (f sourceFirst) (f sourceSecond) :=
      hExpand sourceFirst sourceSecond

/-- An injective map with a nonexpansive left inverse preserves a Frostman
estimate with the same scale and constant. -/
lemma DiscreteSet.isFrostman_map_expansive
    {n : ℕ} {E : DiscreteSet n}
    {delta exponent : ℝ} {constant : ENNReal}
    {f inverse : Point n → Point n}
    (hE : E.IsFrostman delta exponent constant)
    (hleft : ∀ x, inverse (f x) = x)
    (hNonexpansive :
      ∀ x y, dist (inverse x) (inverse y) ≤ dist x y) :
    DiscreteSet.IsFrostman (E.image f)
      delta exponent constant := by
  have hinjective : Set.InjOn f (E : Set (Point n)) := by
    intro first _ second _ heq
    have := congrArg inverse heq
    simpa [hleft] using this
  have hcard :
      DiscreteSet.enncard (E.image f) = E.enncard := by
    simp [DiscreteSet.enncard,
      Finset.card_image_of_injOn hinjective]
  intro center radius hdelta hradius
  let sourceCenter := inverse center
  let source :=
    E.filter fun point => dist (f point) center ≤ radius
  have hsourceSubset :
      source ⊆
        E.filter fun point =>
          dist point sourceCenter ≤ radius := by
    intro point hpoint
    have hmem := (Finset.mem_filter.mp hpoint).1
    have hdist := (Finset.mem_filter.mp hpoint).2
    have hpullback :
        dist point sourceCenter ≤ dist (f point) center := by
      calc
        dist point sourceCenter =
            dist (inverse (f point)) (inverse center) := by
          rw [hleft]
        _ ≤ dist (f point) center :=
          hNonexpansive (f point) center
    exact Finset.mem_filter.mpr
      ⟨hmem, hpullback.trans hdist⟩
  have himageFilter :
      (E.image f).filter
          (fun point => dist point center ≤ radius) =
        source.image f := by
    ext point
    simp only [source, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨preimage, hpreimage, rfl⟩, hdist⟩
      exact ⟨preimage, ⟨hpreimage, hdist⟩, rfl⟩
    · rintro ⟨preimage, ⟨hpreimage, hdist⟩, rfl⟩
      exact ⟨⟨preimage, hpreimage, rfl⟩, hdist⟩
  rw [DiscreteSet.ballCount, himageFilter]
  have himageCard :
      (source.image f).card = source.card :=
    Finset.card_image_of_injOn
      (hinjective.mono (Finset.filter_subset _ _))
  rw [himageCard, hcard]
  have hcount :
      (source.card : ENNReal) ≤
        (E.filter fun point =>
          dist point sourceCenter ≤ radius).card := by
    exact_mod_cast Finset.card_le_card hsourceSubset
  exact hcount.trans
    (hE sourceCenter radius hdelta hradius)

/-- An equivalence with lower Lipschitz factor `m` transports a
one-dimensional Frostman estimate to scale `m * δ`, losing `m⁻¹` in the
constant. -/
lemma DiscreteSet.isFrostman_equiv_contraction_s1
    {n : ℕ} {E : DiscreteSet n}
    {delta m : ℝ} {constant : ENNReal}
    {f : Point n ≃ Point n}
    (hE : E.IsFrostman delta 1 constant)
    (hconstant : 1 ≤ constant)
    (hm : 0 < m)
    (hExpand : ∀ x y, m * dist x y ≤ dist (f x) (f y)) :
    DiscreteSet.IsFrostman (E.image f)
      (m * delta) 1 (constant / ENNReal.ofReal m) := by
  have hcard :
      DiscreteSet.enncard (E.image f) = E.enncard := by
    simp [DiscreteSet.enncard,
      Finset.card_image_of_injective _ f.injective]
  intro center radius hscale hradius
  let sourceCenter := f.symm center
  let source :=
    E.filter fun point => dist (f point) center ≤ radius
  have hsourceSubset :
      source ⊆
        E.filter fun point =>
          dist point sourceCenter ≤ radius / m := by
    intro point hpoint
    have hmem := (Finset.mem_filter.mp hpoint).1
    have hdist := (Finset.mem_filter.mp hpoint).2
    have hcenter : f sourceCenter = center :=
      f.right_inv center
    have hscaled :
        m * dist point sourceCenter ≤ radius := by
      calc
        m * dist point sourceCenter
            ≤ dist (f point) (f sourceCenter) :=
          hExpand point sourceCenter
        _ = dist (f point) center := by rw [hcenter]
        _ ≤ radius := hdist
    have hsourceDist :
        dist point sourceCenter ≤ radius / m := by
      exact (le_div_iff₀ hm).mpr
        (by simpa [mul_comm] using hscaled)
    exact Finset.mem_filter.mpr ⟨hmem, hsourceDist⟩
  have himageFilter :
      (E.image f).filter
          (fun point => dist point center ≤ radius) =
        source.image f := by
    ext point
    simp only [source, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨preimage, hpreimage, rfl⟩, hdist⟩
      exact ⟨preimage, ⟨hpreimage, hdist⟩, rfl⟩
    · rintro ⟨preimage, ⟨hpreimage, hdist⟩, rfl⟩
      exact ⟨⟨preimage, hpreimage, rfl⟩, hdist⟩
  rw [DiscreteSet.ballCount, himageFilter]
  rw [Finset.card_image_of_injective _ f.injective]
  by_cases hlarge : radius / m ≤ 1
  · have hdelta :
        delta ≤ radius / m := by
      apply (le_div_iff₀ hm).mpr
      simpa [mul_comm] using hscale
    have hcount :
        (source.card : ENNReal) ≤
          E.ballCount sourceCenter (radius / m) := by
      change
        (source.card : ENNReal) ≤
          ((E.filter fun point =>
            dist point sourceCenter ≤ radius / m).card : ENNReal)
      exact_mod_cast Finset.card_le_card hsourceSubset
    have hfrostman :=
      hE sourceCenter (radius / m) hdelta hlarge
    calc
      (source.card : ENNReal)
          ≤ constant *
              Kakeya.realRpowENN (radius / m) 1 *
              E.enncard :=
        hcount.trans hfrostman
      _ =
          (constant / ENNReal.ofReal m) *
            Kakeya.realRpowENN radius 1 *
            DiscreteSet.enncard (E.image f) := by
        rw [hcard]
        have hquotient :
            Kakeya.realRpowENN (radius / m) 1 =
              ENNReal.ofReal radius / ENNReal.ofReal m := by
          simp [Kakeya.realRpowENN,
            ENNReal.ofReal_div_of_pos hm]
        have hradius :
            Kakeya.realRpowENN radius 1 =
              ENNReal.ofReal radius := by
          simp [Kakeya.realRpowENN]
        rw [hquotient, hradius]
        simp only [div_eq_mul_inv]
        ac_rfl
  · have hradiusOverM : 1 < radius / m :=
      lt_of_not_ge hlarge
    have hcount :
        (source.card : ENNReal) ≤ E.enncard := by
      change (source.card : ENNReal) ≤ (E.card : ENNReal)
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
    have hone :
        (1 : ENNReal) ≤
          constant *
            (ENNReal.ofReal radius / ENNReal.ofReal m) := by
      have hratio :
          (1 : ENNReal) ≤
            ENNReal.ofReal radius / ENNReal.ofReal m := by
        rw [← ENNReal.ofReal_div_of_pos hm]
        exact ENNReal.one_le_ofReal.mpr hradiusOverM.le
      exact hconstant.trans
        (le_mul_of_one_le_right (by simp) hratio)
    calc
      (source.card : ENNReal) ≤ E.enncard := hcount
      _ ≤
          (constant / ENNReal.ofReal m) *
            Kakeya.realRpowENN radius 1 *
            DiscreteSet.enncard (E.image f) := by
        rw [hcard]
        have hradius :
            Kakeya.realRpowENN radius 1 =
              ENNReal.ofReal radius := by
          simp [Kakeya.realRpowENN]
        rw [hradius]
        have hcoefficient :
            (1 : ENNReal) ≤
              (constant / ENNReal.ofReal m) *
                ENNReal.ofReal radius := by
          simpa [div_eq_mul_inv, mul_comm, mul_left_comm,
            mul_assoc] using hone
        simpa using
          mul_le_mul_left hcoefficient E.enncard

/-- A linear equivalence with lower Lipschitz factor `m` transports a
one-dimensional Frostman estimate to scale `m * δ`, losing `m⁻¹` in the
constant. -/
lemma DiscreteSet.isFrostman_map_contraction_s1
    {n : ℕ} {E : DiscreteSet n}
    {delta m : ℝ} {constant : ENNReal}
    {f : Point n ≃ₗ[ℝ] Point n}
    (hE : E.IsFrostman delta 1 constant)
    (hconstant : 1 ≤ constant)
    (hm : 0 < m)
    (hLower : ∀ x, m * ‖x‖ ≤ ‖f x‖) :
    DiscreteSet.IsFrostman (E.image f)
      (m * delta) 1 (constant / ENNReal.ofReal m) := by
  have hExpand :
      ∀ x y, m * dist x y ≤ dist (f x) (f y) := by
    intro x y
    simpa [dist_eq_norm] using hLower (x - y)
  exact
    DiscreteSet.isFrostman_equiv_contraction_s1
      (f := f.toEquiv) hE hconstant hm hExpand

/-- An expansive map preserves mutual separation. -/
lemma WZ1MutuallySeparated.map_expansive
    {A B : DiscreteSet 2} {radius : ℝ}
    {f : Point2 → Point2}
    (h : WZ1MutuallySeparated A B radius)
    (hExpand : ∀ x y, dist x y ≤ dist (f x) (f y)) :
    WZ1MutuallySeparated (A.image f) (B.image f) radius := by
  intro first hfirst second hsecond
  rcases Finset.mem_image.mp hfirst with
    ⟨sourceFirst, hsourceFirst, rfl⟩
  rcases Finset.mem_image.mp hsecond with
    ⟨sourceSecond, hsourceSecond, rfl⟩
  exact
    (h sourceFirst hsourceFirst sourceSecond hsourceSecond).trans
      (hExpand sourceFirst sourceSecond)

/-- Grid centers of points in a strip remain in the strip enlarged by the
grid-cell radius. -/
lemma grid_coarsening_strip_bound
    {E : DiscreteSet 2} {base normal : Point2}
    {width rho : ℝ}
    (hrho : 0 < rho)
    (hnormal : ‖normal‖ = 1)
    (hstrip :
      ∀ point ∈ E,
        |inner ℝ (point - base) normal| ≤ width / 2) :
    ∀ index ∈ E.image (gridIndex2D rho),
      |inner ℝ
          (cellCenter2D rho index - base) normal| ≤
        width / 2 + rho / Real.sqrt 2 := by
  intro index hindex
  rcases Finset.mem_image.mp hindex with
    ⟨source, hsource, rfl⟩
  let center :=
    cellCenter2D rho (gridIndex2D rho source)
  have hclose :
      dist source center ≤ rho / Real.sqrt 2 :=
    grid_cell_close2D hrho rfl
  have herror :
      |inner ℝ (center - source) normal| ≤ dist source center := by
    calc
      |inner ℝ (center - source) normal|
          ≤ ‖center - source‖ * ‖normal‖ :=
        abs_real_inner_le_norm _ _
      _ = dist source center := by
        rw [hnormal, mul_one, dist_eq_norm, norm_sub_rev]
  have hdecomposition :
      inner ℝ (center - base) normal =
        inner ℝ (center - source) normal +
          inner ℝ (source - base) normal := by
    rw [show center - base =
      (center - source) + (source - base) by abel]
    exact inner_add_left _ _ _
  rw [hdecomposition]
  calc
    |inner ℝ (center - source) normal +
        inner ℝ (source - base) normal|
        ≤ |inner ℝ (center - source) normal| +
            |inner ℝ (source - base) normal| :=
      abs_add_le _ _
    _ ≤ dist source center + width / 2 := by
      gcongr
      exact hstrip source hsource
    _ ≤ rho / Real.sqrt 2 + width / 2 := by
      gcongr
    _ = width / 2 + rho / Real.sqrt 2 := by ring

end Kakeya.Assouad
