module

/-
  FurstenbergBridge.lean — Complete bridge between canonical definitions
  and the supplied axiom `discretised_furstenberg_estimate`.

  Bridges:
  1. IsometryEquiv: Line2 ≅ AffineLine
  2. externalCoveringNumber equality under IsometryEquiv
  3. IsDeltaSet → IsDeltaSSet (same space, ball→closedBall, factor 2^s)
  4. IsDeltaSSet transfer across IsometryEquiv (exact)
  5. Combined: IsDeltaSet Line2 → IsDeltaSSet AffineLine (factor 2^s)
  6. tube → cthickening
  7. ENNReal power conversion
-/

public import MyLeanRepo.RadialBootstrapping.Basic
public import MyLeanRepo.discretised_furstenberg_estimate

@[expose] public section

open MeasureTheory Metric Set

noncomputable section

namespace RadialBootstrapping

open DirecretisedFurstenbergEstimate

abbrev AffineLine' := DirecretisedFurstenbergEstimate.AffineLine

/-! ## 1. IsometryEquiv: Line2 ≅ AffineLine -/

/-- Convert a Line2 to the axiom's AffineLine type. -/
def Line2.toAffineLine (L : Line2) : AffineLine' :=
  ⟨L.val, L.property⟩

/-- Convert an AffineLine back to Line2. -/
def AffineLine'.toLine2 (ℓ : AffineLine') : Line2 :=
  ⟨ℓ.val, ℓ.property⟩

@[simp] lemma toAffineLine_toLine2 (L : Line2) :
    (Line2.toAffineLine L).toLine2 = L := by
  apply Subtype.ext; rfl

@[simp] lemma toLine2_toAffineLine (ℓ : AffineLine') :
    Line2.toAffineLine (ℓ.toLine2) = ℓ := by
  apply Subtype.ext; rfl

/-- The direction distance on Line2 equals the direction distance on AffineLine. -/
lemma lineDirDist_eq_affineDirDist (L₁ L₂ : Line2) :
    lineDirDist L₁ L₂ =
      ‖L₁.toAffine.direction.starProjection - L₂.toAffine.direction.starProjection‖ := by
  have h1 : submoduleProj L₁.toAffine.direction = L₁.toAffine.direction.starProjection :=
    submoduleProj_eq_starProjection _
  have h2 : submoduleProj L₂.toAffine.direction = L₂.toAffine.direction.starProjection :=
    submoduleProj_eq_starProjection _
  simp [lineDirDist, submoduleDirDist, h1, h2]

/-- `toAffineLine` is an isometry between Line2 and AffineLine. -/
lemma toAffineLine_isometry : Isometry Line2.toAffineLine := by
  refine Isometry.of_dist_eq fun L₁ L₂ => ?_
  have hd := lineDirDist_eq_affineDirDist L₁ L₂
  have h1 : L₁.closestPoint = (EuclideanGeometry.orthogonalProjection L₁.toAffine 0 : Point) :=
    L₁.closestPoint_eq_orthogonalProjection
  have h2 : L₂.closestPoint = (EuclideanGeometry.orthogonalProjection L₂.toAffine 0 : Point) :=
    L₂.closestPoint_eq_orthogonalProjection
  have h_off1 : (Line2.toAffineLine L₁).offset =
      EuclideanGeometry.orthogonalProjection L₁.toAffine 0 := by rfl
  have h_off2 : (Line2.toAffineLine L₂).offset =
      EuclideanGeometry.orthogonalProjection L₂.toAffine 0 := by rfl
  have ho : lineOffsetDist L₁ L₂ =
      ‖(Line2.toAffineLine L₁).offset - (Line2.toAffineLine L₂).offset‖ := by
    simp [lineOffsetDist, h1, h2, h_off1, h_off2, dist_eq_norm]
  have h_main : dist L₁ L₂ = lineDirDist L₁ L₂ + lineOffsetDist L₁ L₂ := by rfl
  have h_aff : dist (Line2.toAffineLine L₁) (Line2.toAffineLine L₂) =
      ‖L₁.toAffine.direction.starProjection - L₂.toAffine.direction.starProjection‖ +
        ‖(Line2.toAffineLine L₁).offset - (Line2.toAffineLine L₂).offset‖ := by rfl
  rw [h_main, h_aff, hd, ho] <;> ring

/-- The canonical isometry equivalence between Line2 and AffineLine. -/
def line2EquivAffineLine : Line2 ≃ᵢ AffineLine' :=
  { toFun := Line2.toAffineLine,
    invFun := AffineLine'.toLine2,
    left_inv := toAffineLine_toLine2,
    right_inv := toLine2_toAffineLine,
    isometry_toFun := toAffineLine_isometry }

/-! ## 2. externalCoveringNumber equality under IsometryEquiv -/

/-- Covering numbers are equal under an isometry equivalence. -/
lemma IsometryEquiv.externalCoveringNumber_image
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (e : X ≃ᵢ Y) {S : Set X} {ε : NNReal} :
    Metric.externalCoveringNumber ε (e '' S) = Metric.externalCoveringNumber ε S := by
  have h1 : Metric.externalCoveringNumber ε (e '' S) ≤ Metric.externalCoveringNumber ε S := by
    apply le_iInf
    intro C
    apply le_iInf
    intro hC
    have hC' : Metric.IsCover ε (e '' S) (e '' C) :=
      (e.isometry.isCover_image_iff C).mpr hC
    have h4 : Metric.externalCoveringNumber ε (e '' S) ≤ (e '' C).encard :=
      Metric.IsCover.externalCoveringNumber_le_encard hC'
    have h5 : (e '' C).encard ≤ C.encard := Set.encard_image_le e C
    exact le_trans h4 h5
  have h2 : Metric.externalCoveringNumber ε S ≤ Metric.externalCoveringNumber ε (e '' S) := by
    apply le_iInf
    intro C'
    apply le_iInf
    intro hC'
    let C : Set X := e.symm '' C'
    have h_eC : e '' C = C' := by
      ext z
      simp only [C, Set.mem_image]
      constructor
      · rintro ⟨y, ⟨c', hc', rfl⟩, rfl⟩
        have h_ec : e (e.symm c') = c' := e.apply_symm_apply c'
        rw [h_ec]
        exact hc'
      · intro hz
        refine ⟨e.symm z, ⟨z, hz, rfl⟩, e.apply_symm_apply z⟩
    have hC : Metric.IsCover ε S C := by
      have h : Metric.IsCover ε (e '' S) (e '' C) := by
        rw [h_eC] <;> exact hC'
      exact (e.isometry.isCover_image_iff C).mp h
    have h4 : Metric.externalCoveringNumber ε S ≤ C.encard :=
      Metric.IsCover.externalCoveringNumber_le_encard hC
    have h5 : C.encard ≤ C'.encard := Set.encard_image_le e.symm C'
    exact le_trans h4 h5
  exact le_antisymm h1 h2

/-! ## 3. IsDeltaSet → IsDeltaSSet (same space, ball→closedBall) -/

/-- Convert `IsDeltaSet` (using open balls) to `IsDeltaSSet` (using closed balls).
The constant degrades by `2^s` because `closedBall x r ⊆ ball x (r+δ) ⊆ ball x (2r)`. -/
lemma IsDeltaSet.toIsDeltaSSet_same
    {X : Type*} [PseudoMetricSpace X]
    {P : Set X} {δ s C : ℝ}
    {hδ : 0 < δ} {hs : 0 ≤ s} {hC : 0 ≤ C}
    (h : IsDeltaSet δ s C hδ hs hC P)
    (hP : P.Nonempty) (hCpos : 0 < C) :
    IsDeltaSSet δ s (C * Real.rpow 2 s) P := by
  let δn : NNReal := δ.toNNReal
  have hδn : (δn : ℝ) = δ := Real.coe_toNNReal δ hδ.le
  have hδn' : δn = ⟨δ, hδ.le⟩ := by
    apply NNReal.coe_injective
    have h1 : (δn : ℝ) = δ := hδn
    let b : NNReal := ⟨δ, hδ.le⟩
    have h2 : (b : ℝ) = δ := by
      exact Real.ext_cauchy rfl
    exact Eq.trans h1 h2.symm
  have h2pos : 0 < Real.rpow 2 s := Real.rpow_pos_of_pos (by norm_num) s
  have hC'pos : 0 < C * Real.rpow 2 s := mul_pos hCpos h2pos
  refine' ⟨hP, hδ, hC'pos, hs, _⟩
  intro x r hr
  have h_rpos : 0 < r := by linarith
  have h1 : Metric.closedBall x r ⊆ Metric.ball x (r + δ) :=
    Metric.closedBall_subset_ball (by linarith)
  have h2 : P ∩ Metric.closedBall x r ⊆ P ∩ Metric.ball x (r + δ) := by
    gcongr <;> tauto
  have h3 : (Metric.externalCoveringNumber δn (P ∩ Metric.closedBall x r) : ENNReal) ≤
      (Metric.externalCoveringNumber δn (P ∩ Metric.ball x (r + δ)) : ENNReal) := by
    exact_mod_cast Metric.externalCoveringNumber_mono_set h2
  have h4 : δ ≤ r + δ := by linarith
  have h5 : (Metric.externalCoveringNumber δn (P ∩ Metric.ball x (r + δ)) : ENNReal) ≤
      ENNReal.ofReal (C * Real.rpow (r + δ) s) *
        (Metric.externalCoveringNumber δn P : ENNReal) := by
    have h_spec2 := h.spec x (r + δ) h4
    rw [←hδn'] at h_spec2
    exact h_spec2
  have h6 : r + δ ≤ 2 * r := by linarith
  have h7 : Real.rpow (r + δ) s ≤ Real.rpow (2 * r) s :=
    Real.rpow_le_rpow (by linarith) h6 hs
  have h8 : Real.rpow (2 * r) s = Real.rpow 2 s * Real.rpow r s := by
    have h91 : Real.rpow (2 * r) s = Real.rpow ((2 : ℝ) * r) s := by ring_nf
    rw [h91]
    have h92 : Real.rpow ((2 : ℝ) * r) s = Real.rpow 2 s * Real.rpow r s :=
      Real.mul_rpow (by norm_num) (by linarith)
    exact h92
  have h9 : C * Real.rpow (r + δ) s ≤ C * Real.rpow 2 s * Real.rpow r s := by
    calc C * Real.rpow (r + δ) s
      ≤ C * Real.rpow (2 * r) s := by gcongr
    _ = C * (Real.rpow 2 s * Real.rpow r s) := by rw [h8]
    _ = C * Real.rpow 2 s * Real.rpow r s := by ring
  have h10 : ENNReal.ofReal (C * Real.rpow (r + δ) s) ≤
      ENNReal.ofReal (C * Real.rpow 2 s * Real.rpow r s) :=
    ENNReal.ofReal_le_ofReal h9
  have h12 : 0 ≤ C * Real.rpow 2 s := by positivity
  have h11 : ENNReal.ofReal (C * Real.rpow 2 s * Real.rpow r s) =
      ENNReal.ofReal (C * Real.rpow 2 s) * (ENNReal.ofReal r)^s := by
    have h14 : C * Real.rpow 2 s * Real.rpow r s = (C * Real.rpow 2 s) * Real.rpow r s := by ring
    rw [h14]
    rw [ENNReal.ofReal_mul h12]
    rw [ENNReal.ofReal_rpow_of_nonneg (by linarith) hs]
    <;> rfl
  calc (Metric.externalCoveringNumber δn (P ∩ Metric.closedBall x r) : ENNReal)
    ≤ (Metric.externalCoveringNumber δn (P ∩ Metric.ball x (r + δ)) : ENNReal) := h3
  _ ≤ ENNReal.ofReal (C * Real.rpow (r + δ) s) * (Metric.externalCoveringNumber δn P : ENNReal) := h5
  _ ≤ ENNReal.ofReal (C * Real.rpow 2 s * Real.rpow r s) * (Metric.externalCoveringNumber δn P : ENNReal) := by
      gcongr
  _ = ENNReal.ofReal (C * Real.rpow 2 s) * (ENNReal.ofReal r)^s *
        (Metric.externalCoveringNumber δn P : ENNReal) := by
      rw [h11] <;> ring

/-! ## 4. IsDeltaSSet transfer across IsometryEquiv -/

/-- `IsDeltaSSet` transfers exactly across an isometry equivalence. -/
lemma IsDeltaSSet.image_equiv
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (e : X ≃ᵢ Y) {P : Set X} {δ s C : ℝ}
    (h : IsDeltaSSet δ s C P) :
    IsDeltaSSet δ s C (e '' P) := by
  rcases h with ⟨hPne, hδpos, hCpos, hs, hspec⟩
  let δn : NNReal := δ.toNNReal
  have hPne' : (e '' P).Nonempty := hPne.image e
  refine' ⟨hPne', hδpos, hCpos, hs, _⟩
  intro y r hr
  let x : X := e.symm y
  have h_ball : e '' Metric.closedBall x r = Metric.closedBall y r := by
    ext z
    simp only [Set.mem_image, Metric.mem_closedBall]
    constructor
    · rintro ⟨w, hw, rfl⟩
      have h_dist : dist w x ≤ r := hw
      have h_eq1 : dist (e w) y = dist w x := by
        have h : dist (e w) (e x) = dist w x := e.dist_eq w x
        have h_y : e x = y := e.apply_symm_apply y
        rw [h_y] at h
        exact h
      exact h_eq1 ▸ h_dist
    · intro hz
      refine ⟨e.symm z, ?_, e.apply_symm_apply z⟩
      have h_eq : dist z y = dist (e.symm z) (e.symm y) := by
        have h : dist (e (e.symm z)) (e (e.symm y)) = dist (e.symm z) (e.symm y) := e.dist_eq (e.symm z) (e.symm y)
        simpa using h
      simpa [x] using h_eq ▸ hz
  have h_inter : e '' (P ∩ Metric.closedBall x r) = (e '' P) ∩ Metric.closedBall y r := by
    rw [Set.image_inter e.injective, h_ball]
  have h_cov1 : Metric.externalCoveringNumber δn ((e '' P) ∩ Metric.closedBall y r) =
      Metric.externalCoveringNumber δn (P ∩ Metric.closedBall x r) := by
    rw [←h_inter]
    exact IsometryEquiv.externalCoveringNumber_image e (S := P ∩ Metric.closedBall x r)
  have h_covP : Metric.externalCoveringNumber δn (e '' P) = Metric.externalCoveringNumber δn P :=
    IsometryEquiv.externalCoveringNumber_image e (S := P)
  have h_main := hspec x r hr
  rw [h_cov1, h_covP] at *
  exact h_main

/-! ## 5. Combined: IsDeltaSet Line2 → IsDeltaSSet AffineLine -/

/-- Bridge from `IsDeltaSet` on Line2 to `IsDeltaSSet` on AffineLine.
Only degradation is ball→closedBall factor `2^s`. -/
lemma IsDeltaSet.toIsDeltaSSet_affine
    {P : Set Line2} {δ s C : ℝ}
    {hδ : 0 < δ} {hs : 0 ≤ s} {hC : 0 ≤ C}
    (h : IsDeltaSet δ s C hδ hs hC P)
    (hP : P.Nonempty) (hCpos : 0 < C) :
    IsDeltaSSet δ s (C * Real.rpow 2 s)
      (Set.image Line2.toAffineLine P) := by
  have h1 : IsDeltaSSet δ s (C * Real.rpow 2 s) P :=
    h.toIsDeltaSSet_same hP hCpos
  exact IsDeltaSSet.image_equiv line2EquivAffineLine h1

/-! ## 6. tube → cthickening -/

lemma tube_subset_cthickening {L : Line2} {δ : ℝ} :
    tube δ L ⊆ Metric.cthickening δ L.toSet :=
  Metric.thickening_subset_cthickening δ L.toSet

/-! ## 7. ENNReal power conversion -/

lemma pow_bridge (r : ℝ) (hr : 0 ≤ r) (s : ℝ) (hs : 0 ≤ s) :
    (ENNReal.ofReal r)^s = ENNReal.ofReal (Real.rpow r s) :=
  ENNReal.ofReal_rpow_of_nonneg hr hs

end RadialBootstrapping
