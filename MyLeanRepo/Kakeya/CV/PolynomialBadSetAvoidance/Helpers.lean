import MyLeanRepo.Kakeya.CV.Statements
import MyLeanRepo.Kakeya.CV.Geometry
import MyLeanRepo.Kakeya.CV.PolynomialMollification
import MyLeanRepo.Kakeya.CV.CenteredHomotheticVolumeComparison
import MyLeanRepo.Kakeya.CV.UniformFiniteBisectionStability
import MyLeanRepo.Kakeya.CV.FiniteDyadicPolynomialBadSetDecomposition
import MyLeanRepo.Kakeya.CV.Targets.AntipodalSignSeparation.TopologicalTools
import MyLeanRepo.Kakeya.CV.Targets.AntipodalSignSeparation.MeasureContinuity
import MyLeanRepo.Kakeya.CV.Targets.ManyBisections.AffineTools
import MyLeanRepo.Kakeya.CV.Targets.EllipsoidTranslatePacking.VolumeScaling
import MyLeanRepo.Kakeya.CV.Targets.UnitCubeEllipsoidPacking.VolumeLemmas

/-!
# Helper lemmas for polynomial bad-set avoidance

Aggregates all proved helper lemmas used in the final assembly:
- Homothetic radius and volume bounds
- Bad layer emptiness and sphere transport
- Local constancy of selected ellipsoid
- Sign class cover and separation premises
- Dimension margin derivation
- Volume scaling and translate cardinality
- Many-bisections contradiction
-/

noncomputable section

open MeasureTheory TopCat Set Finset Filter
open scoped BigOperators ENNReal NNReal Real

namespace Kakeya.CV

/-! ### Homothetic and volume bounds -/

/-- If `K ⊆ unitBall 3` and `E` is `α`-homothetically close to `K` at `0`,
then `E ⊆ Metric.closedBall 0 α`. -/
lemma homothetic_close_outer_radius {K E : Set (Point 3)} {α : ℝ}
    (hK : K ⊆ unitBall 3) (h : AreHomotheticallyCloseAt 0 α K E) (hα : 1 < α) :
    E ⊆ Metric.closedBall 0 α := by
  have hpos : 0 < α := by linarith
  have h1 : E ⊆ dilateAbout 0 α K := h.2
  have h2 : dilateAbout 0 α K ⊆ Metric.closedBall 0 α := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have h3 : x ∈ unitBall 3 := hK hx
    have h4 : ‖x‖ ≤ 1 := by
      simpa [unitBall, Metric.mem_closedBall] using h3
    let z := (AffineMap.homothety (0 : Point 3) α) x
    have h5 : ‖z‖ = α * ‖x‖ := by
      simp [z, AffineMap.homothety_apply, norm_smul, abs_of_pos hpos]
    have h6 : ‖z‖ ≤ α := by
      rw [h5]
      have h7 : α * ‖x‖ ≤ α * (1 : ℝ) := mul_le_mul_of_nonneg_left h4 hpos.le
      have h8 : α * (1 : ℝ) = α := by ring
      rw [h8] at h7
      exact h7
    simpa [z, Metric.mem_closedBall] using h6
  exact h1.trans h2

/-- The volume of the mollified visibility body equals the inverse cube
of the concrete mollified visibility. -/
lemma visibility_body_volume_from_visibility {k : ℕ}
    {P : PolynomialParameterization k} {ε : ℝ}
    {x : CoefficientSpace P.dim} {U : Set (Point 3)}
    (hvol_pos : 0 < volume (concreteMollifiedVisibilityBody P ε x U))
    (hvol_fin : volume (concreteMollifiedVisibilityBody P ε x U) ≠ ⊤) :
    (volume (concreteMollifiedVisibilityBody P ε x U)).toReal =
      Real.rpow (concreteMollifiedVisibility P ε x U) (-3 : ℝ) := by
  set V : ℝ := (volume (concreteMollifiedVisibilityBody P ε x U)).toReal with hV
  set vis : ℝ := concreteMollifiedVisibility P ε x U with hvis
  have hV_pos : 0 < V := ENNReal.toReal_pos hvol_pos.ne' hvol_fin
  have hV_nonneg : 0 ≤ V := by positivity
  have hdef : vis = Real.rpow V (-1 / 3 : ℝ) := by rfl
  have hmul : Real.rpow V ((-1 / 3 : ℝ) * (3 : ℝ)) =
      Real.rpow (Real.rpow V (-1 / 3 : ℝ)) 3 :=
    Real.rpow_mul hV_nonneg (-1 / 3) 3
  have hcalc : (-1 / 3 : ℝ) * (3 : ℝ) = (-1 : ℝ) := by norm_num
  rw [hcalc] at hmul
  have h1 : Real.rpow vis 3 = Real.rpow V (-1 : ℝ) := by
    rw [hdef]
    exact hmul.symm
  have h2 : Real.rpow V (-1 : ℝ) = 1 / V := by
    have h21 : Real.rpow V (-1 : ℝ) = (Real.rpow V (1 : ℝ))⁻¹ := by
      exact Real.rpow_neg hV_nonneg (1 : ℝ)
    rw [h21]
    have h22 : Real.rpow V (1 : ℝ) = V := by simp
    rw [h22]
    <;> field_simp [hV_pos.ne']
  have h3 : Real.rpow vis 3 = 1 / V := by
    rw [h1, h2]
  have hvis_pos : 0 < vis := by
    rw [hdef]
    exact Real.rpow_pos_of_pos hV_pos (-1 / 3 : ℝ)
  have h4 : Real.rpow vis (-3 : ℝ) = (Real.rpow vis 3)⁻¹ := by
    exact Real.rpow_neg hvis_pos.le (3 : ℝ)
  rw [h4, h3]
  <;> field_simp [hV_pos.ne'] <;> ring

/-- For a parameter in the `r`-th dyadic bad layer, the visibility body volume
is at least `(2^{-r} * M)^{-3}`. -/
lemma dyadic_layer_volume_lower_bound {k : ℕ}
    {P : PolynomialParameterization k} {ε : ℝ} {U : Set (Point 3)}
    {M : ℝ} {r : ℕ} {x : CoefficientSpace P.dim}
    (hx : x ∈ concretePolynomialBadLayer P ε U M r)
    (hM : 0 < M)
    (hvol_pos : 0 < volume (concreteMollifiedVisibilityBody P ε x U))
    (hvol_fin : volume (concreteMollifiedVisibilityBody P ε x U) ≠ ⊤) :
    (volume (concreteMollifiedVisibilityBody P ε x U)).toReal ≥
      Real.rpow (Real.rpow 2 (-(r : ℝ)) * M) (-3 : ℝ) := by
  let vis := concreteMollifiedVisibility P ε x U
  let bound := Real.rpow 2 (-(r : ℝ)) * M
  have hvis_le : vis ≤ bound := hx.2
  have h_rpow_pos1 : 0 < Real.rpow 2 (-(r : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hM2 : 0 < bound := mul_pos h_rpow_pos1 hM
  have h_rpow_pos2 : 0 < Real.rpow 2 (-(r : ℝ) - 1) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hpos_lower : 0 < Real.rpow 2 (-(r : ℝ) - 1) * M := mul_pos h_rpow_pos2 hM
  have hvis_pos : 0 < vis := by
    have h_lower : Real.rpow 2 (-(r : ℝ) - 1) * M < vis := hx.1
    exact lt_trans hpos_lower h_lower
  have hV_eq : (volume (concreteMollifiedVisibilityBody P ε x U)).toReal =
      Real.rpow vis (-3 : ℝ) :=
    visibility_body_volume_from_visibility hvol_pos hvol_fin
  rw [hV_eq]
  have h9 : Real.rpow bound (-3 : ℝ) = (bound ^ 3)⁻¹ := by
    have h : Real.rpow bound (-3 : ℝ) = (Real.rpow bound (3 : ℝ))⁻¹ :=
      Real.rpow_neg hM2.le 3
    rw [h]
    have h2 : Real.rpow bound (3 : ℝ) = bound ^ (3 : ℕ) := Real.rpow_natCast bound 3
    rw [h2] <;> rfl
  have h10 : Real.rpow vis (-3 : ℝ) = (vis ^ 3)⁻¹ := by
    have h : Real.rpow vis (-3 : ℝ) = (Real.rpow vis (3 : ℝ))⁻¹ :=
      Real.rpow_neg hvis_pos.le 3
    rw [h]
    have h2 : Real.rpow vis (3 : ℝ) = vis ^ (3 : ℕ) := Real.rpow_natCast vis 3
    rw [h2] <;> rfl
  rw [h9, h10]
  have h11 : vis ^ 3 ≤ bound ^ 3 := by gcongr
  have h12 : 0 < vis ^ 3 := by positivity
  have h13 : 1 / (bound ^ 3) ≤ 1 / (vis ^ 3) :=
    one_div_le_one_div_of_le h12 h11
  simpa [one_div] using h13

/-- Volume lower bound from centered homothetic closeness:
`volume E ≥ α^{-3} * volume K`. -/
lemma ellipsoid_volume_lower_bound {K : Set (Point 3)}
    {A : Point 3 ≃ₗ[ℝ] Point 3} {α : ℝ}
    (hα : 1 ≤ α) (hK : JohnEllipsoid.IsConvexBody K)
    (h : AreHomotheticallyCloseAt 0 α K (JohnEllipsoid.ellipsoid 0 A)) :
    ENNReal.ofReal (α⁻¹ ^ 3) * volume K ≤ volume (JohnEllipsoid.ellipsoid 0 A) :=
  (centered_homothetic_volume_comparison α K A hα hK h).1

/-- Combine the dyadic visibility-body lower bound with centered homothetic
comparison to obtain the expanded volume threshold used by translate counting. -/
lemma dyadic_ellipsoid_volume_lower_bound
    {k : ℕ} {P : PolynomialParameterization k} {ε : ℝ}
    {U : Set (Point 3)} {M α : ℝ} {r : ℕ}
    {x : CoefficientSpace P.dim} {E : EllipsoidParameter}
    (hx : x ∈ concretePolynomialBadLayer P ε U M r)
    (hM : 0 < M)
    (hbody :
      JohnEllipsoid.IsConvexBody
        (concreteMollifiedVisibilityBody P ε x U))
    (hα : 1 < α)
    (hcomp :
      ENNReal.ofReal (α⁻¹ ^ 3) *
          volume (concreteMollifiedVisibilityBody P ε x U) ≤
        volume (ellipsoidCarrier E)) :
    ENNReal.ofReal
        (α ^ (-3 : ℝ) * (2 : ℝ) ^ (3 * r) * M ^ (-3 : ℝ)) ≤
      volume (ellipsoidCarrier E) := by
  have hvol_pos :
      0 < volume (concreteMollifiedVisibilityBody P ε x U) :=
    Measure.measure_pos_of_nonempty_interior volume hbody.2.2
  have hvol_fin :
      volume (concreteMollifiedVisibilityBody P ε x U) ≠ ⊤ :=
    hbody.2.1.measure_lt_top.ne
  have hbody_real :
      Real.rpow (Real.rpow 2 (-(r : ℝ)) * M) (-3 : ℝ) ≤
        (volume (concreteMollifiedVisibilityBody P ε x U)).toReal :=
    dyadic_layer_volume_lower_bound hx hM hvol_pos hvol_fin
  have hdyadic :
      Real.rpow (Real.rpow 2 (-(r : ℝ)) * M) (-3 : ℝ) =
        (2 : ℝ) ^ (3 * r) * M ^ (-3 : ℝ) := by
    have htwo : 0 ≤ Real.rpow 2 (-(r : ℝ)) :=
      (Real.rpow_pos_of_pos (by norm_num) _).le
    calc
      Real.rpow (Real.rpow 2 (-(r : ℝ)) * M) (-3 : ℝ)
          = Real.rpow (Real.rpow 2 (-(r : ℝ))) (-3 : ℝ) *
              Real.rpow M (-3 : ℝ) :=
        Real.mul_rpow htwo hM.le
      _ = Real.rpow 2 ((-(r : ℝ)) * (-3 : ℝ)) *
              Real.rpow M (-3 : ℝ) := by
        congr 1
        exact
          (Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ))
            (-(r : ℝ)) (-3 : ℝ)).symm
      _ = (2 : ℝ) ^ (3 * r) * M ^ (-3 : ℝ) := by
        have hexp : (-(r : ℝ)) * (-3 : ℝ) = ((3 * r : ℕ) : ℝ) := by
          push_cast
          ring
        rw [hexp]
        congr 1
        exact Real.rpow_natCast 2 (3 * r)
  have hαpow : α ^ (-3 : ℝ) = α⁻¹ ^ (3 : ℕ) := by
    calc
      α ^ (-3 : ℝ) = α⁻¹ ^ (3 : ℝ) := by
        rw [show (-3 : ℝ) = -(3 : ℝ) by norm_num]
        exact Real.rpow_neg_eq_inv_rpow α 3
      _ = α⁻¹ ^ (3 : ℕ) := Real.rpow_natCast α⁻¹ 3
  have hbody_ne_top :
      volume (concreteMollifiedVisibilityBody P ε x U) ≠ ⊤ :=
    hbody.2.1.measure_lt_top.ne
  have hbody_enn :
      ENNReal.ofReal ((2 : ℝ) ^ (3 * r) * M ^ (-3 : ℝ)) ≤
        volume (concreteMollifiedVisibilityBody P ε x U) := by
    rw [hdyadic] at hbody_real
    rw [← ENNReal.ofReal_toReal hbody_ne_top]
    exact ENNReal.ofReal_le_ofReal hbody_real
  have hofReal_mul :
      ENNReal.ofReal
          (α ^ (-3 : ℝ) * ((2 : ℝ) ^ (3 * r) * M ^ (-3 : ℝ))) =
        ENNReal.ofReal (α⁻¹ ^ 3) *
          ENNReal.ofReal ((2 : ℝ) ^ (3 * r) * M ^ (-3 : ℝ)) := by
    rw [hαpow]
    exact ENNReal.ofReal_mul (by positivity)
  calc
    ENNReal.ofReal
        (α ^ (-3 : ℝ) * (2 : ℝ) ^ (3 * r) * M ^ (-3 : ℝ))
        = ENNReal.ofReal
            (α ^ (-3 : ℝ) * ((2 : ℝ) ^ (3 * r) * M ^ (-3 : ℝ))) := by
      rw [mul_assoc]
    _ = ENNReal.ofReal (α⁻¹ ^ 3) *
          ENNReal.ofReal ((2 : ℝ) ^ (3 * r) * M ^ (-3 : ℝ)) :=
      hofReal_mul
    _ ≤ ENNReal.ofReal (α⁻¹ ^ 3) *
          volume (concreteMollifiedVisibilityBody P ε x U) := by
      gcongr
    _ ≤ volume (ellipsoidCarrier E) := hcomp

/-! ### Bad layer emptiness and sphere transport -/

/-- When `M ≤ 0`, the dyadic bad layer is empty. -/
lemma badLayer_empty_when_M_nonpos {k : ℕ} {P : PolynomialParameterization k}
    {ε : ℝ} {U : Set (Point 3)} {M : ℝ} {r : ℕ}
    (hM : M ≤ 0) :
    concretePolynomialBadLayer P ε U M r = ∅ := by
  have h1 : ∀ x : CoefficientSpace P.dim,
      0 ≤ concreteMollifiedVisibility P ε x U := by
    intro x
    exact Real.rpow_nonneg (by positivity) _
  ext x
  simp only [concretePolynomialBadLayer, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro h
  have hlt := h.1
  have hle := h.2
  have hpos2 : 0 < Real.rpow 2 (-(r : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have h_vis_nonpos : concreteMollifiedVisibility P ε x U ≤ 0 :=
    hle.trans (mul_nonpos_of_nonneg_of_nonpos hpos2.le hM)
  have h_vis_eq_zero : concreteMollifiedVisibility P ε x U = 0 :=
    le_antisymm h_vis_nonpos (h1 x)
  have h_upper_nonneg : 0 ≤ Real.rpow 2 (-(r : ℝ)) * M := by
    rw [←h_vis_eq_zero]; exact hle
  have h_upper_nonpos : Real.rpow 2 (-(r : ℝ)) * M ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hpos2.le hM
  have h_upper_eq : Real.rpow 2 (-(r : ℝ)) * M = 0 :=
    le_antisymm h_upper_nonpos h_upper_nonneg
  have h_M_eq_zero : M = 0 := by
    apply (mul_eq_zero.mp h_upper_eq).resolve_left
    exact hpos2.ne'
  rw [h_M_eq_zero] at hlt
  rw [h_vis_eq_zero] at hlt
  norm_num at hlt

/-- A homeomorphism preserves closure of sets. -/
lemma homeomorph_image_closure {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (h : X ≃ₜ Y) (S : Set X) :
    h '' closure S = closure (h '' S) :=
  h.image_closure S

/-- Transport antipodal image through a homeomorphism. -/
lemma homeomorph_image_antipodal {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (h : X ≃ₜ Y) {negX : X → X} {negY : Y → Y}
    (hcomm : ∀ x, h (negX x) = negY (h x))
    (S : Set X) :
    h '' (negX '' S) = negY '' (h '' S) := by
  ext y
  simp only [Set.mem_image]
  constructor
  · rintro ⟨x, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨h z, ⟨z, hz, rfl⟩, (hcomm z).symm⟩
  · rintro ⟨y', ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨negX z, ⟨z, hz, rfl⟩, hcomm z⟩

/-- Transport antipodal closure-separation through a homeomorphism. -/
lemma transport_separation {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (h : X ≃ₜ Y) {negX : X → X} {negY : Y → Y}
    (hcomm : ∀ x, h (negX x) = negY (h x))
    {A : Set X} (hsep : A ∩ closure (negX '' A) = ∅) :
    (h '' A) ∩ closure (negY '' (h '' A)) = ∅ := by
  have h1 : h '' (closure (negX '' A)) = closure (negY '' (h '' A)) := by
    rw [homeomorph_image_closure h (negX '' A), homeomorph_image_antipodal h hcomm A]
  have h_disj : Disjoint (h '' A) (h '' (closure (negX '' A))) := by
    rw [Set.disjoint_left]
    intro y hy1 hy2
    rcases hy2 with ⟨x, hx, rfl⟩
    have h3 : x ∈ A := (h.injective.mem_set_image).mp hy1
    have h4 : x ∈ A ∩ closure (negX '' A) := ⟨h3, hx⟩
    rw [hsep] at h4
    exact h4
  rw [← h1]
  exact Set.disjoint_iff_inter_eq_empty.mp h_disj

/-- Transport a cover through a homeomorphism. -/
lemma transport_cover {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (h : X ≃ₜ Y) {negX : X → X} {negY : Y → Y}
    (hcomm : ∀ x, h (negX x) = negY (h x))
    {I : Type*} {A : I → Set X} {bad : Set X}
    (hcover : bad ⊆ ⋃ i, (A i ∪ negX '' A i)) :
    h '' bad ⊆ ⋃ i, (h '' A i ∪ negY '' (h '' A i)) := by
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  have h3 : x ∈ ⋃ i, (A i ∪ negX '' A i) := hcover hx
  rcases Set.mem_iUnion.mp h3 with ⟨i, hi⟩
  cases hi with
  | inl hA =>
    have h4 : h x ∈ h '' A i := ⟨x, hA, rfl⟩
    exact Set.mem_iUnion.mpr ⟨i, Or.inl h4⟩
  | inr hneg =>
    have h4 : h x ∈ h '' (negX '' A i) := ⟨x, hneg, rfl⟩
    have h5 : h '' (negX '' A i) = negY '' (h '' A i) :=
      homeomorph_image_antipodal h hcomm (A i)
    rw [h5] at h4
    exact Set.mem_iUnion.mpr ⟨i, Or.inr h4⟩

/-! ### Dimension margin -/

/-- From cardinality bound and strict dimension margin, derive card < dim. -/
lemma dimension_margin_implies_card_lt_dim
    {I : Type*} [Fintype I] {N : ℕ} {Cube : Type*} [Fintype Cube]
    {M : Cube → ℝ≥0} {dim : ℕ}
    (Ccount : ℝ)
    (hCcount : Ccount = (N : ℝ) * (8 / 7 : ℝ))
    (htotal_card : (Fintype.card I : ℝ≥0) ≤
        (Fintype.card (Fin N) : ℝ≥0) * ((8 : ℝ≥0) / 7) * ∑ q, M q ^ 3)
    (hDimMargin : Ccount * ∑ q, (M q : ℝ) ^ 3 < (dim : ℝ)) :
    (Fintype.card I : ℝ) < (dim : ℝ) := by
  have h1 : (Fintype.card I : ℝ) ≤
      (Fintype.card (Fin N) : ℝ) * ((8 : ℝ) / 7) * ∑ q, (M q : ℝ) ^ 3 := by
    exact_mod_cast htotal_card
  have h2 : (Fintype.card (Fin N) : ℝ) = (N : ℝ) := by simp
  rw [h2] at h1
  have h3 : (Fintype.card I : ℝ) ≤ Ccount * ∑ q, (M q : ℝ) ^ 3 := by
    rw [hCcount]; exact h1
  exact h3.trans_lt hDimMargin

/-! ### Sign volume and sign class cover -/

/-- Positive and negative sign region volumes sum to total region volume. -/
lemma sign_volumes_sum {p : MvPolynomial (Fin 3) ℝ} (hp : p ≠ 0)
    {R : Set (Point 3)} (hRmeas : MeasurableSet R) (_hRfin : volume R < ⊤) :
    volume (R ∩ {y | 0 < polynomialValue p y}) +
      volume (R ∩ {y | polynomialValue p y < 0}) = volume R := by
  let pos := R ∩ {y | 0 < polynomialValue p y}
  let neg := R ∩ {y | polynomialValue p y < 0}
  let zer := R ∩ polynomialZeroSet p
  have h_pos_meas : MeasurableSet pos := hRmeas.inter (posSignRegion_measurable p)
  have h_neg_meas : MeasurableSet neg := hRmeas.inter (negSignRegion_measurable p)
  have h_disj1 : Disjoint pos neg := by
    rw [Set.disjoint_left]; intro y h1 h2
    have hpos : 0 < polynomialValue p y := h1.2
    have hneg : polynomialValue p y < 0 := h2.2
    exact lt_irrefl 0 (by linarith)
  have h_disj2 : Disjoint pos zer := by
    rw [Set.disjoint_left]; intro y h1 h2
    have hpos : 0 < polynomialValue p y := h1.2
    have hzero : polynomialValue p y = 0 := h2.2
    rw [hzero] at hpos; exact lt_irrefl 0 hpos
  have h_disj3 : Disjoint neg zer := by
    rw [Set.disjoint_left]; intro y h1 h2
    have hneg : polynomialValue p y < 0 := h1.2
    have hzero : polynomialValue p y = 0 := h2.2
    rw [hzero] at hneg; exact lt_irrefl 0 hneg
  have h_disj4 : Disjoint (pos ∪ neg) zer :=
    Set.disjoint_union_left.mpr ⟨h_disj2, h_disj3⟩
  have h_union : R = (pos ∪ neg) ∪ zer := by
    ext y; simp only [pos, neg, zer, Set.mem_union, Set.mem_inter_iff]
    constructor
    · intro hy
      by_cases hpos : 0 < polynomialValue p y
      · exact Or.inl (Or.inl ⟨hy, hpos⟩)
      · by_cases hneg : polynomialValue p y < 0
        · exact Or.inl (Or.inr ⟨hy, hneg⟩)
        · have hzero : polynomialValue p y = 0 := by linarith
          exact Or.inr ⟨hy, hzero⟩
    · rintro ((h | h) | h) <;> exact h.1
  have h_vol0 : volume zer = 0 :=
    measure_mono_null inter_subset_right (polynomialZeroSet3_null p hp)
  have h_vol1 : volume (pos ∪ neg) = volume pos + volume neg :=
    MeasureTheory.measure_union' h_disj1 h_pos_meas
  have h_vol2 : volume ((pos ∪ neg) ∪ zer) = volume (pos ∪ neg) + volume zer :=
    MeasureTheory.measure_union' h_disj4 (h_pos_meas.union h_neg_meas)
  have h_main : volume R = volume pos + volume neg := by
    calc
      volume R = volume ((pos ∪ neg) ∪ zer) := by rw [h_union]
      _ = volume (pos ∪ neg) + volume zer := h_vol2
      _ = volume pos + volume neg + volume zer := by rw [h_vol1]
      _ = volume pos + volume neg := by rw [h_vol0, add_zero]
  exact h_main.symm

/-- Non-bisected region has one strict sign region larger than the other. -/
lemma not_bisects_implies_sign_strict {p : MvPolynomial (Fin 3) ℝ} (hp : p ≠ 0)
    {R : Set (Point 3)} (hRmeas : MeasurableSet R) (hRfin : volume R < ⊤)
    (h_nobisect : ¬PolynomialBisects p R) :
    (volume (R ∩ {y | 0 < polynomialValue p y}) >
       volume (R ∩ {y | polynomialValue p y < 0})) ∨
    (volume (R ∩ {y | polynomialValue p y < 0}) >
       volume (R ∩ {y | 0 < polynomialValue p y})) := by
  let pos := volume (R ∩ {y | 0 < polynomialValue p y})
  let neg := volume (R ∩ {y | polynomialValue p y < 0})
  have h_ne : pos ≠ neg := by
    intro h; exact h_nobisect h.symm
  by_cases h : pos < neg
  · exact Or.inr h
  · have h' : ¬pos < neg := h
    have h_gt : neg < pos := by
      exact lt_of_le_of_ne (le_of_not_gt h') h_ne.symm
    exact Or.inl h_gt

/-- Non-bisected parameter lies in positive sign class or its antipodal image. -/
lemma nonbisected_in_sign_class_cover
    {k : ℕ} {P : PolynomialParameterization k}
    {selectedRegion : CoefficientSpace P.dim → Set (Point 3)}
    {D : Set (CoefficientSpace P.dim)}
    (hD_antipodal : ∀ x, x ∈ D → -x ∈ D)
    (hRegion_antipodal : ∀ x, x ∈ D → selectedRegion (-x) = selectedRegion x)
    (hRegion_meas : ∀ x, x ∈ D → MeasurableSet (selectedRegion x))
    (hRegion_finite : ∀ x, x ∈ D → volume (selectedRegion x) < ⊤)
    (hPoly_nonzero : ∀ x, x ∈ D → parameterPolynomial P x ≠ 0)
    {x : CoefficientSpace P.dim} (hx_D : x ∈ D)
    (h_nobisect : ¬PolynomialBisects (parameterPolynomial P x) (selectedRegion x)) :
    x ∈ positiveSignClass P selectedRegion D ∨
      x ∈ (fun x : CoefficientSpace P.dim => -x) '' positiveSignClass P selectedRegion D := by
  have hp : parameterPolynomial P x ≠ 0 := hPoly_nonzero x hx_D
  have hRmeas : MeasurableSet (selectedRegion x) := hRegion_meas x hx_D
  have hRfin : volume (selectedRegion x) < ⊤ := hRegion_finite x hx_D
  have h_strict := not_bisects_implies_sign_strict hp hRmeas hRfin h_nobisect
  cases h_strict with
  | inl h_pos_gt =>
    exact Or.inl ⟨hx_D, h_pos_gt⟩
  | inr h_neg_gt =>
    have h_x_neg : x ∈ negativeSignClass P selectedRegion D := ⟨hx_D, h_neg_gt⟩
    have h_eq : negativeSignClass P selectedRegion D =
        (fun x : CoefficientSpace P.dim => -x) '' positiveSignClass P selectedRegion D :=
      negativeSignClass_eq_image P selectedRegion D hD_antipodal hRegion_antipodal
    rw [h_eq] at h_x_neg
    exact Or.inr h_x_neg

/-! ### Local constancy and separation premises -/

/-- Sequential local constancy of selected ellipsoid on a colour domain. -/
lemma selected_ellipsoid_locally_constant
    {k : ℕ} {P : PolynomialParameterization k}
    {α : ℝ} {N : ℕ} {net : Set EllipsoidParameter}
    {colour : EllipsoidParameter → Fin N}
    {selected : CoefficientSpace P.dim → EllipsoidParameter}
    {D : Set (CoefficientSpace P.dim)}
    {θ : Fin N} {c : Point 3} {ε : ℝ}
    (hα : 1 < α)
    (h_cont : ConcreteVisibilityHomotheticContinuityStatement)
    (h_stability : EllipsoidSelectionStabilityStatement)
    (h_close : ∀ x ∈ D, AreHomotheticallyCloseAt 0 α
        (concreteMollifiedVisibilityBody P ε x (unitCube c))
        (ellipsoidCarrier (selected x)))
    (h_colour : ∀ x ∈ D, colour (selected x) = θ)
    (h_selected_in_net : ∀ x ∈ D, selected x ∈ net)
    (h_separation : ∀ E₁ ∈ net, ∀ E₂ ∈ net,
        colour E₁ = colour E₂ →
        AreHomotheticallyCloseAt 0 (α ^ 3) (ellipsoidCarrier E₁) (ellipsoidCarrier E₂) →
        E₁ = E₂)
    (hU_meas : MeasurableSet (unitCube c))
    (hU_sub : unitCube c ⊆ Metric.closedBall c 1)
    (hε_pos : 0 < ε) :
    ∀ (xseq : ℕ → CoefficientSpace P.dim) (x : CoefficientSpace P.dim),
      (∀ m, xseq m ∈ D) → x ∈ D →
      Filter.Tendsto xseq Filter.atTop (nhds x) →
      ∀ᶠ m in Filter.atTop, selected (xseq m) = selected x := by
  intro xseq x hxseq_in_D hx_in_D hxseq_tendsto
  let K : Set (Point 3) := concreteMollifiedVisibilityBody P ε x (unitCube c)
  let Kseq : ℕ → Set (Point 3) := fun m =>
    concreteMollifiedVisibilityBody P ε (xseq m) (unitCube c)
  let E : EllipsoidParameter := selected x
  let Eseq : ℕ → EllipsoidParameter := fun m => selected (xseq m)
  have hconv : HomotheticConvergesAt 0 Kseq K :=
    h_cont k P (unitCube c) c ε x xseq hU_meas hU_sub hε_pos hxseq_tendsto
  have hE_net : E ∈ net := h_selected_in_net x hx_in_D
  have hEseq_net : ∀ m, Eseq m ∈ net := fun m =>
    h_selected_in_net (xseq m) (hxseq_in_D m)
  have hcolour_eq : ∀ m, colour (Eseq m) = colour E := by
    intro m
    have h1 : colour (Eseq m) = θ := h_colour (xseq m) (hxseq_in_D m)
    have h2 : colour E = θ := h_colour x hx_in_D
    rw [h1, h2]
  have hclose_E : AreHomotheticallyCloseAt 0 α K (ellipsoidCarrier E) :=
    h_close x hx_in_D
  have hclose_Eseq : ∀ m, AreHomotheticallyCloseAt 0 α (Kseq m) (ellipsoidCarrier (Eseq m)) :=
    fun m => h_close (xseq m) (hxseq_in_D m)
  exact h_stability α N net colour 0 K Kseq E Eseq hα hconv
    hE_net hEseq_net hcolour_eq hclose_E hclose_Eseq h_separation

/-- All 7 premises of `AntipodalSignSeparationStatement` for an atom. -/
lemma sign_separation_premises
    {k : ℕ} {P : PolynomialParameterization k}
    {α : ℝ} {N : ℕ} {net : Set EllipsoidParameter}
    {colour : EllipsoidParameter → Fin N}
    {selected : CoefficientSpace P.dim → EllipsoidParameter}
    {D : Set (CoefficientSpace P.dim)}
    {selectedRegion : CoefficientSpace P.dim → Set (Point 3)}
    {c : Point 3} {ε : ℝ} {_η : ℝ} {θ : Fin N}
    (hα : 1 < α)
    (h_cont : ConcreteVisibilityHomotheticContinuityStatement)
    (h_stability : EllipsoidSelectionStabilityStatement)
    (h_selected_in_net : ∀ x ∈ D, selected x ∈ net)
    (h_colour : ∀ x ∈ D, colour (selected x) = θ)
    (h_close : ∀ x ∈ D, AreHomotheticallyCloseAt 0 α
        (concreteMollifiedVisibilityBody P ε x (unitCube c))
        (ellipsoidCarrier (selected x)))
    (h_separation : ∀ E₁ ∈ net, ∀ E₂ ∈ net,
        colour E₁ = colour E₂ →
        AreHomotheticallyCloseAt 0 (α ^ 3) (ellipsoidCarrier E₁) (ellipsoidCarrier E₂) →
        E₁ = E₂)
    (hRegion_of_selected : ∀ x y, x ∈ D → y ∈ D →
      selected x = selected y → selectedRegion x = selectedRegion y)
    (hRegion_meas : ∀ x ∈ D, MeasurableSet (selectedRegion x))
    (hRegion_finite : ∀ x ∈ D, volume (selectedRegion x) < ⊤)
    (hD_subset_norm : ∀ x ∈ D, x ∈ normalizedPolynomialParameters P)
    (hD_antipodal : ∀ x, x ∈ D → -x ∈ D)
    (hRegion_antipodal : ∀ x, x ∈ D → selectedRegion (-x) = selectedRegion x)
    (hD_nobisect : ∀ x ∈ D, ¬PolynomialBisects (parameterPolynomial P x) (selectedRegion x))
    (hU_meas : MeasurableSet (unitCube c))
    (hU_sub : unitCube c ⊆ Metric.closedBall c 1)
    (hε_pos : 0 < ε) :
    (∀ x, x ∈ D → -x ∈ D) ∧
    (∀ x, x ∈ D → selectedRegion (-x) = selectedRegion x) ∧
    (∀ x, x ∈ D → MeasurableSet (selectedRegion x)) ∧
    (∀ x, x ∈ D → volume (selectedRegion x) < ⊤) ∧
    (∀ x, x ∈ D → parameterPolynomial P x ≠ 0) ∧
    (∀ x, x ∈ D → ¬PolynomialBisects (parameterPolynomial P x) (selectedRegion x)) ∧
    (∀ (xseq : ℕ → CoefficientSpace P.dim) (x : CoefficientSpace P.dim),
      (∀ m, xseq m ∈ D) → x ∈ D →
      Filter.Tendsto xseq Filter.atTop (nhds x) →
      ∀ᶠ m in Filter.atTop, selectedRegion (xseq m) = selectedRegion x) := by
  have h5 : ∀ x, x ∈ D → parameterPolynomial P x ≠ 0 := by
    intro x hx
    exact parameterPolynomial_ne_zero_of_normalized (hD_subset_norm x hx)
  have h7 : ∀ (xseq : ℕ → CoefficientSpace P.dim) (x : CoefficientSpace P.dim),
      (∀ m, xseq m ∈ D) → x ∈ D →
      Filter.Tendsto xseq Filter.atTop (nhds x) →
      ∀ᶠ m in Filter.atTop, selectedRegion (xseq m) = selectedRegion x := by
    intro xseq x hxseq_in_D hx_in_D hxseq_tendsto
    have h_ellipsoid_const : ∀ᶠ m in Filter.atTop, selected (xseq m) = selected x :=
      selected_ellipsoid_locally_constant
        hα h_cont h_stability
        h_close h_colour h_selected_in_net h_separation
        hU_meas hU_sub hε_pos
        xseq x hxseq_in_D hx_in_D hxseq_tendsto
    have h_main : ∀ᶠ m in Filter.atTop, selectedRegion (xseq m) = selectedRegion x := by
      filter_upwards [h_ellipsoid_const] with m h_eq
      exact hRegion_of_selected (xseq m) x (hxseq_in_D m) hx_in_D h_eq
    exact h_main
  exact ⟨hD_antipodal, hRegion_antipodal, hRegion_meas, hRegion_finite,
         h5, hD_nobisect, h7⟩

/-! ### Volume scaling and translate cardinality -/

/-- Volume of scaled ellipsoid scales by η³. -/
lemma volume_scaledEllipsoid_eq' (E : EllipsoidParameter) (hE_center : E.1 = 0)
    (η : ℝ) (hη : 0 < η) :
    volume (scaledEllipsoid E.2 η 0) =
      ENNReal.ofReal (η ^ 3) * volume (ellipsoidCarrier E) := by
  have h1 : volume (scaledEllipsoid E.2 η 0) =
      ENNReal.ofReal (η ^ 3 * |LinearMap.det (E.2 : Point 3 →ₗ[ℝ] Point 3)|) *
        volume (unitBall 3) :=
    volume_affine_ball E.2 η hη 0
  have h2 : volume (ellipsoidCarrier E) =
      ENNReal.ofReal (|LinearMap.det (E.2 : Point 3 →ₗ[ℝ] Point 3)|) *
        volume (unitBall 3) := by
    have hE : ellipsoidCarrier E = JohnEllipsoid.ellipsoid E.1 E.2 := by rfl
    rw [hE, hE_center]
    exact JohnEllipsoid.volume_ellipsoid_eq (0 : Point 3) E.2
  rw [h1, h2]
  have h3 : 0 ≤ η ^ 3 := by positivity
  have h4 : ENNReal.ofReal (η ^ 3 * |LinearMap.det (E.2 : Point 3 →ₗ[ℝ] Point 3)|) =
      ENNReal.ofReal (η ^ 3) * ENNReal.ofReal (|LinearMap.det (E.2 : Point 3 →ₗ[ℝ] Point 3)|) := by
    rw [ENNReal.ofReal_mul h3]
  rw [h4] <;> ring

/-- Algebra helper: inverse of volume lower bound product. -/
private lemma inverse_algebra
    {r : ℕ} {η α Cvis Mq : ℝ} (hη : 0 < η) (hα : 0 < α)
    (hCvis : 0 < Cvis) (hMq : 0 < Mq) :
    (η ^ 3 * (α^(-3 : ℝ) * (2 : ℝ)^(3 * r) * (Cvis * Mq)^(-3 : ℝ)))⁻¹ =
    η^(-3 : ℝ) * α^3 * (1 / 8 : ℝ)^r * Cvis^3 * Mq^3 := by
  have h1 : (2 : ℝ)^(3 * r) = (8 : ℝ)^r := by
    have h2 : (2 : ℝ)^(3 * r) = ((2 : ℝ)^3)^r := by
      rw [← pow_mul] <;> ring
    rw [h2] <;> norm_num
  have hη3 : η^(-3 : ℝ) = (η^3)⁻¹ := by
    rw [Real.rpow_neg hη.le] <;> norm_cast
  have hα3_neg : α^(-3 : ℝ) = (α^3)⁻¹ := by
    rw [Real.rpow_neg hα.le] <;> norm_cast
  have hcm3_neg : (Cvis * Mq)^(-3 : ℝ) = ((Cvis * Mq)^3)⁻¹ := by
    have hpos : 0 < Cvis * Mq := mul_pos hCvis hMq
    rw [Real.rpow_neg hpos.le] <;> norm_cast
  have hpos1 : 0 < η^3 := by positivity
  have hpos2 : 0 < α^3 := by positivity
  have hpos3 : 0 < (Cvis * Mq)^3 := by positivity
  have hpos4 : 0 < (8 : ℝ)^r := by positivity
  have h_main1 : (η ^ 3 * (α^(-3 : ℝ) * (2 : ℝ)^(3 * r) * (Cvis * Mq)^(-3 : ℝ)))⁻¹ =
      (η^3)⁻¹ * α^3 * ((8 : ℝ)^r)⁻¹ * (Cvis * Mq)^3 := by
    rw [hα3_neg, hcm3_neg, h1]
    field_simp [hpos1.ne', hpos2.ne', hpos3.ne', hpos4.ne'] <;> ring
  rw [h_main1]
  have h8inv : ((8 : ℝ)^r)⁻¹ = (1 / 8 : ℝ)^r := by
    have h : ((8 : ℝ)^r)⁻¹ = ((8 : ℝ)⁻¹)^r := by rw [← inv_pow]
    rw [h] <;> norm_num
  have hcm3 : (Cvis * Mq)^3 = Cvis^3 * Mq^3 := by ring
  rw [h8inv, hcm3, ← hη3] <;> ring

/-- Per-ellipsoid translate count bound. -/
lemma single_translate_bound
    {r : ℕ} {Mq : ℝ≥0}
    (hMq_pos : 0 < (Mq : ℝ))
    (C_pack : ℝ≥0) (hC_pack_pos : 0 < C_pack)
    (α : ℝ) (hα : 1 < α)
    (η : ℝ) (hη : 0 < η)
    (Cvis : ℝ) (hCvis_pos : 0 < Cvis)
    (hCvis_def : Cvis = η / (2 * (C_pack : ℝ) * α^3 + 1))
    (E : EllipsoidParameter) (hE_center : E.1 = 0)
    (volLower : ℝ) (hvolLower_pos : 0 < volLower)
    (hvolLower_eq : volLower = α^(-3 : ℝ) * (2 : ℝ)^(3 * r) * (Cvis * (Mq : ℝ))^(-3 : ℝ))
    (hEllip_lower : volume (ellipsoidCarrier E) ≥ ENNReal.ofReal volLower)
    (c : Point 3) (n : ℕ)
    (hPack : (n : ℝ≥0∞) ≤ (C_pack : ℝ≥0∞) * volume (unitCube c) / volume (scaledEllipsoid E.2 η 0)) :
    (n : ℝ≥0) ≤ (1 / 8 : ℝ≥0) ^ r * Mq ^ 3 := by
  have hα_pos : 0 < α := by linarith
  have hCube : volume (unitCube c) = 1 := volume_unitCube c
  have hScaled_eq : volume (scaledEllipsoid E.2 η 0) =
      ENNReal.ofReal (η ^ 3) * volume (ellipsoidCarrier E) :=
    volume_scaledEllipsoid_eq' E hE_center η hη
  set X : ℝ := η ^ 3 * volLower with hX
  have hX_pos : 0 < X := by positivity
  have hScaled_lower : volume (scaledEllipsoid E.2 η 0) ≥ ENNReal.ofReal X := by
    rw [hScaled_eq]
    have h9 : ENNReal.ofReal (η ^ 3) * volume (ellipsoidCarrier E) ≥
        ENNReal.ofReal (η ^ 3) * ENNReal.ofReal volLower := by
      gcongr
    have h10 : ENNReal.ofReal (η ^ 3) * ENNReal.ofReal volLower = ENNReal.ofReal X := by
      rw [ENNReal.ofReal_mul (by positivity)]
    rw [h10] at h9
    exact h9
  have h_inv : (volume (scaledEllipsoid E.2 η 0))⁻¹ ≤ (ENNReal.ofReal X)⁻¹ :=
    ENNReal.inv_le_inv.mpr hScaled_lower
  have hPack' : (n : ℝ≥0∞) ≤ (C_pack : ℝ≥0∞) * (volume (scaledEllipsoid E.2 η 0))⁻¹ := by
    have hdiv : (C_pack : ℝ≥0∞) * volume (unitCube c) / volume (scaledEllipsoid E.2 η 0) =
        (C_pack : ℝ≥0∞) * (volume (scaledEllipsoid E.2 η 0))⁻¹ := by
      rw [hCube] <;> simp [div_eq_mul_inv] <;> ring
    rw [hdiv] at hPack
    exact hPack
  have hPack3 : (n : ℝ≥0∞) ≤ (C_pack : ℝ≥0∞) * (ENNReal.ofReal X)⁻¹ := by
    calc
      (n : ℝ≥0∞)
        ≤ (C_pack : ℝ≥0∞) * (volume (scaledEllipsoid E.2 η 0))⁻¹ := hPack'
      _ ≤ (C_pack : ℝ≥0∞) * (ENNReal.ofReal X)⁻¹ := by gcongr
  have h_ofReal_inv : (ENNReal.ofReal X)⁻¹ = ENNReal.ofReal (X⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos hX_pos]
  rw [h_ofReal_inv] at hPack3
  have hX_inv_eq : X⁻¹ = η^(-3 : ℝ) * α^3 * (1 / 8 : ℝ)^r * Cvis^3 * (Mq : ℝ)^3 := by
    rw [hX, hvolLower_eq]
    exact inverse_algebra hη hα_pos hCvis_pos hMq_pos
  rw [hX_inv_eq] at hPack3
  set K : ℝ := (C_pack : ℝ) * α^3 * η^(-3 : ℝ) * Cvis^3 with hK
  have hK_nonneg : 0 ≤ K := by positivity
  have hK_le_one : K ≤ 1 := by
    dsimp only [K]
    rw [hCvis_def]
    set Y : ℝ := (C_pack : ℝ) * α^3 with hY
    have hY_pos : 0 < Y := by positivity
    have h_expr : (C_pack : ℝ) * α^3 * η^(-3 : ℝ) * (η / (2 * (C_pack : ℝ) * α^3 + 1))^3 =
        Y / (2 * Y + 1)^3 := by
      have hη3 : η^(-3 : ℝ) = (η^3)⁻¹ := by
        rw [Real.rpow_neg hη.le] <;> norm_cast
      rw [hη3]
      have h_denom : 2 * (C_pack : ℝ) * α^3 + 1 = 2 * Y + 1 := by
        simp [hY] <;> ring
      rw [h_denom]
      field_simp [hη.ne'] <;> ring
    rw [h_expr]
    have h1 : Y ≤ (2 * Y + 1)^3 := by
      have h2 : 2 * Y + 1 ≥ 1 := by linarith
      have h3 : (2 * Y + 1)^3 ≥ 2 * Y + 1 := by
        have h4 : (2 * Y + 1)^2 ≥ 1 := by nlinarith
        nlinarith
      linarith
    have h6 : 0 < (2 * Y + 1)^3 := by positivity
    exact (div_le_one h6).mpr h1
  set Bound : ℝ := (1 / 8 : ℝ)^r * (Mq : ℝ)^3 with hBound
  have hBound_nonneg : 0 ≤ Bound := by positivity
  set Yreal : ℝ := η^(-3 : ℝ) * α^3 * (1 / 8 : ℝ)^r * Cvis^3 * (Mq : ℝ)^3 with hYreal
  have hYreal_nonneg : 0 ≤ Yreal := by positivity
  have h_prod : (C_pack : ℝ≥0∞) * ENNReal.ofReal Yreal =
      ENNReal.ofReal ((C_pack : ℝ) * Yreal) := by
    have h_coe : (C_pack : ℝ≥0∞) = ENNReal.ofReal (C_pack : ℝ) := by simp
    rw [h_coe]
    have hCpack_nonneg : 0 ≤ (C_pack : ℝ) := by positivity
    have h : ENNReal.ofReal ((C_pack : ℝ) * Yreal) =
        ENNReal.ofReal (C_pack : ℝ) * ENNReal.ofReal Yreal :=
      ENNReal.ofReal_mul hCpack_nonneg
    exact h.symm
  rw [h_prod] at hPack3
  have h_eq_K : (C_pack : ℝ) * Yreal = K * Bound := by
    dsimp only [K, Bound, Yreal] <;> ring
  rw [h_eq_K] at hPack3
  have h_pos : 0 ≤ K * Bound := by positivity
  have h_bound_real : (n : ℝ) ≤ K * Bound := by
    have h2 : ((n : ℝ≥0∞) : ENNReal) = ENNReal.ofReal (n : ℝ) := by simp
    rw [h2] at hPack3
    exact (ENNReal.ofReal_le_ofReal_iff h_pos).mp hPack3
  have h_bound2 : (n : ℝ) ≤ Bound := by
    calc
      (n : ℝ) ≤ K * Bound := h_bound_real
      _ ≤ 1 * Bound := mul_le_mul_of_nonneg_right hK_le_one hBound_nonneg
      _ = Bound := by ring
  have h_goal : (n : ℝ≥0) ≤ (1 / 8 : ℝ≥0) ^ r * Mq ^ 3 := by
    have h_rhs : (((1 / 8 : ℝ≥0) ^ r * Mq ^ 3 : ℝ≥0) : ℝ) = Bound := by
      simp [Bound, NNReal.coe_mul, NNReal.coe_pow]
    have h_main : ((n : ℝ≥0) : ℝ) ≤ (((1 / 8 : ℝ≥0) ^ r * Mq ^ 3 : ℝ≥0) : ℝ) := by
      rw [h_rhs]
      exact h_bound2
    exact_mod_cast h_main
  exact h_goal

/-! ### Many-bisections contradiction -/

/-- Upper bound type for many-bisections. -/
def ManyBisectsUpperBound (n : ℕ) (η : ℝ) (prodℓ : ℝ) (C : ℝ≥0) (α : ℝ) : Prop :=
  (n : ℝ≥0∞) * ENNReal.ofReal (η ^ 2 * prodℓ) *
    codimensionOneMeasure 3 (unitSphere 3) ≤
  (C : ℝ≥0∞) * (3 : ℝ≥0∞) * ENNReal.ofReal α

/-- Contradiction threshold: η must be at least this large if all translates
are bisected. -/
def manyBisectsThreshold (C_mb C_pack : ℝ≥0) (α : ℝ)
    (U : Set (Point 3)) : ℝ≥0∞ :=
  volume U * codimensionOneMeasure 3 (unitSphere 3) /
    ((3 : ℝ≥0∞) * (C_mb : ℝ≥0∞) * ENNReal.ofReal α *
     (C_pack : ℝ≥0∞) * volume (unitBall 3))

/-- The many-bisections contradiction lemma. -/
lemma many_bisects_contradiction
    (n : ℕ) (η : ℝ) (prodℓ : ℝ)
    (C_mb C_pack : ℝ≥0) (α : ℝ)
    (U : Set (Point 3)) (A : Point 3 ≃ₗ[ℝ] Point 3)
    (hη_pos : 0 < η)
    (h_prodℓ_pos : 0 < prodℓ)
    (hα_pos : 0 < α)
    (hC_mb_pos : 0 < C_mb)
    (hC_pack_pos : 0 < C_pack)
    (h_upper : ManyBisectsUpperBound n η prodℓ C_mb α)
    (h_volume_formula : volume (scaledEllipsoid A η 0) =
        ENNReal.ofReal (η ^ 3 * prodℓ) * volume (unitBall 3))
    (h_pack : volume U / volume (scaledEllipsoid A η 0) ≤
        (C_pack : ℝ≥0∞) * (n : ℝ≥0∞))
    (hη_small : ENNReal.ofReal η < manyBisectsThreshold C_mb C_pack α U)
    : False := by
  let sphereArea := codimensionOneMeasure 3 (unitSphere 3)
  let ballVol := volume (unitBall 3)
  let V := volume (scaledEllipsoid A η 0)
  have hη3_pos : 0 < η ^ 3 * prodℓ := by positivity
  have hη_nonneg : 0 ≤ η := by linarith
  have hballVol_pos : 0 < ballVol := volume_unitBall_pos
  have hballVol_ne_top : ballVol ≠ ⊤ := volume_unitBall_lt_top.ne
  have hV_eq : V = ENNReal.ofReal (η ^ 3 * prodℓ) * ballVol := by
    simpa [V] using h_volume_formula
  have hV_pos : 0 < V := by
    rw [hV_eq]
    have h1 : 0 < ENNReal.ofReal (η ^ 3 * prodℓ) := ENNReal.ofReal_pos.mpr hη3_pos
    have h_ne_zero : ENNReal.ofReal (η ^ 3 * prodℓ) * ballVol ≠ 0 := by
      rw [mul_ne_zero_iff]
      exact ⟨h1.ne', hballVol_pos.ne'⟩
    exact pos_iff_ne_zero.mpr h_ne_zero
  have hV_ne_top : V ≠ ⊤ := by
    rw [hV_eq]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hballVol_ne_top
  have h1 : volume U ≤ (C_pack : ℝ≥0∞) * (n : ℝ≥0∞) * V := by
    have hdiv : volume U / V ≤ (C_pack : ℝ≥0∞) * (n : ℝ≥0∞) := h_pack
    have h : volume U ≤ ((C_pack : ℝ≥0∞) * (n : ℝ≥0∞)) * V :=
      (ENNReal.div_le_iff hV_pos.ne' hV_ne_top).mp hdiv
    simpa [mul_assoc] using h
  have h_upper' : (n : ℝ≥0∞) * ENNReal.ofReal (η ^ 2 * prodℓ) * sphereArea ≤
      (C_mb : ℝ≥0∞) * (3 : ℝ≥0∞) * ENNReal.ofReal α := h_upper
  have h_ofReal3 : ENNReal.ofReal (η ^ 3 * prodℓ) =
      ENNReal.ofReal η * ENNReal.ofReal (η ^ 2 * prodℓ) := by
    rw [← ENNReal.ofReal_mul hη_nonneg] <;> ring_nf
  set K : ℝ≥0∞ := (C_pack : ℝ≥0∞) * ENNReal.ofReal η * ballVol with hK
  have h2 : volume U * sphereArea ≤
      K * ((C_mb : ℝ≥0∞) * (3 : ℝ≥0∞) * ENNReal.ofReal α) := by
    calc
      volume U * sphereArea
        ≤ ((C_pack : ℝ≥0∞) * (n : ℝ≥0∞) * V) * sphereArea := by
          exact mul_le_mul' h1 (le_refl sphereArea)
      _ = K * ((n : ℝ≥0∞) * ENNReal.ofReal (η ^ 2 * prodℓ) * sphereArea) := by
        simp only [hK, V, hV_eq, h_ofReal3]
        simp [mul_assoc, mul_comm, mul_left_comm]
      _ ≤ K * ((C_mb : ℝ≥0∞) * (3 : ℝ≥0∞) * ENNReal.ofReal α) := by
        exact mul_le_mul' (le_refl K) h_upper'
  let denom : ℝ≥0∞ :=
      (3 : ℝ≥0∞) * (C_mb : ℝ≥0∞) * ENNReal.ofReal α *
      (C_pack : ℝ≥0∞) * ballVol
  have hdenom_pos : 0 < denom := by
    dsimp only [denom]
    have h1 : 0 < (3 : ℝ≥0∞) := by norm_num
    have h2 : 0 < (C_mb : ℝ≥0∞) := by exact_mod_cast hC_mb_pos
    have h3 : 0 < ENNReal.ofReal α := ENNReal.ofReal_pos.mpr hα_pos
    have h4 : 0 < (C_pack : ℝ≥0∞) := by exact_mod_cast hC_pack_pos
    positivity
  have hdenom_ne_top : denom ≠ ⊤ := by
    dsimp only [denom]
    have h3 : ((3 : ℝ≥0∞) * (C_mb : ℝ≥0∞)) ≠ ⊤ := by
      exact ENNReal.mul_ne_top (by simp) (by simp)
    have h4 : (((3 : ℝ≥0∞) * (C_mb : ℝ≥0∞)) * ENNReal.ofReal α) ≠ ⊤ := by
      exact ENNReal.mul_ne_top h3 ENNReal.ofReal_ne_top
    have h5 : ((((3 : ℝ≥0∞) * (C_mb : ℝ≥0∞)) * ENNReal.ofReal α) *
        (C_pack : ℝ≥0∞)) ≠ ⊤ := by
      exact ENNReal.mul_ne_top h4 (by simp)
    exact ENNReal.mul_ne_top h5 hballVol_ne_top
  have h3 : ENNReal.ofReal η * denom < volume U * sphereArea := by
    have h4 : ENNReal.ofReal η < (volume U * sphereArea) / denom := by
      simpa [manyBisectsThreshold, denom] using hη_small
    have h5 : ENNReal.ofReal η * denom < ((volume U * sphereArea) / denom) * denom := by
      exact ENNReal.mul_lt_mul_left hdenom_pos.ne' hdenom_ne_top h4
    have h6 : ((volume U * sphereArea) / denom) * denom = volume U * sphereArea := by
      rw [ENNReal.div_mul_cancel hdenom_pos.ne' hdenom_ne_top]
    rw [h6] at h5
    exact h5
  have h7 : ENNReal.ofReal η * denom =
      K * ((C_mb : ℝ≥0∞) * (3 : ℝ≥0∞) * ENNReal.ofReal α) := by
    simp only [denom, hK]
    simp [mul_assoc, mul_comm, mul_left_comm]
  rw [h7] at h3
  exact not_le.mpr h3 h2

end Kakeya.CV
