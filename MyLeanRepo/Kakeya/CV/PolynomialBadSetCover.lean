import MyLeanRepo.Kakeya.CV.Statements

/-!
# Antipodal polynomial bad-set cover

Proof of `PolynomialBadSetCoverStatement` using Borsuk-Ulam with distance functions.
-/

open TopCat
open scoped TopCat

namespace Kakeya.CV

theorem polynomial_bad_set_cover :
    PolynomialBadSetCoverStatement := by
  intro N I _ h_card A bad h_sep h_cover
  let j := Fintype.card I
  have h_j : j ≤ N := h_card
  let e : I ≃ Fin j := Fintype.equivFin I

  let SphereType := TopCat.sphere.{0} N

  let F : I → Set SphereType := fun i =>
    closure (sphereAntipodal N '' A i)

  have hF_closed : ∀ i, IsClosed (F i) := fun i => isClosed_closure

  have hF_subset : ∀ i, sphereAntipodal N '' A i ⊆ F i :=
    fun i => subset_closure

  let down : SphereType → {v : EuclideanSpace ℝ (Fin (N + 1)) // v ∈ Metric.sphere (0 : _) 1} :=
    ULift.down

  let F' : I → Set {v : EuclideanSpace ℝ (Fin (N + 1)) // v ∈ Metric.sphere (0 : _) 1} :=
    fun i => down '' F i

  have hF'_closed : ∀ i, IsClosed (F' i) := by
    intro i
    let h_homeo : Homeomorph SphereType {v : EuclideanSpace ℝ (Fin (N + 1)) // v ∈ Metric.sphere (0 : _) 1} :=
      Homeomorph.ulift
    have h : IsClosed (h_homeo '' F i) := h_homeo.isClosed_image.mpr (hF_closed i)
    have h_eq : h_homeo '' F i = F' i := by
      ext z
      simp only [Set.mem_image, F']
      <;> aesop
    rw [h_eq] at h
    exact h

  let g : I → SphereType → ℝ := fun i x =>
    Metric.infDist (down x) (F' i)

  have hg_cont : ∀ i, Continuous (g i) := by
    intro i
    have h1 : Continuous down := continuous_uliftDown
    have h2 : Continuous (fun y => Metric.infDist y (F' i)) :=
      Metric.continuous_infDist_pt (F' i)
    exact h2.comp h1

  -- Negation on the metric sphere subtype
  let negSphere : {v : EuclideanSpace ℝ (Fin (N + 1)) // v ∈ Metric.sphere (0 : _) 1} →
      {v : EuclideanSpace ℝ (Fin (N + 1)) // v ∈ Metric.sphere (0 : _) 1} :=
    fun y => ⟨-y.1, by
      have hnorm : y.1 ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (N + 1))) 1 := y.property
      have h : ‖-y.1‖ = 1 := by
        have h' : ‖y.1‖ = 1 := mem_sphere_zero_iff_norm.mp hnorm
        rw [norm_neg] <;> exact h'
      exact mem_sphere_zero_iff_norm.mpr h⟩

  have h_negSphere_cont : Continuous negSphere := by
    apply Continuous.subtype_mk
    exact continuous_neg.comp continuous_subtype_val

  have h_antipodal_eq : ∀ (x : SphereType),
      sphereAntipodal N x = ULift.up (negSphere (down x)) := by
    intro x
    simp [sphereAntipodal, negSphere]
    <;> rfl

  have h_antipodal_cont : Continuous (sphereAntipodal N) := by
    have h_up : Continuous (ULift.up : {v : _ // _} → SphereType) := continuous_uliftUp
    have h : Continuous (fun x : SphereType => ULift.up (negSphere (down x))) :=
      h_up.comp (h_negSphere_cont.comp continuous_uliftDown)
    have h' : (sphereAntipodal N) = fun x : SphereType => ULift.up (negSphere (down x)) := by
      funext x
      exact h_antipodal_eq x
    rw [h']
    exact h

  have h_antipodal_invol : ∀ (x : SphereType),
      sphereAntipodal N (sphereAntipodal N x) = x := by
    intro x
    have h_down_inj : Function.Injective (down : SphereType → _) := ULift.down_injective
    apply h_down_inj
    have h1 : down (sphereAntipodal N (sphereAntipodal N x)) =
        negSphere (negSphere (down x)) := by
      rw [h_antipodal_eq, h_antipodal_eq]
    rw [h1]
    have h2 : negSphere (negSphere (down x)) = down x := by
      ext
      simp [negSphere]
    exact h2

  let h : I → SphereType → ℝ := fun i x =>
    g i x - g i (sphereAntipodal N x)

  have hh_cont : ∀ i, Continuous (h i) := by
    intro i
    exact (hg_cont i).sub ((hg_cont i).comp h_antipodal_cont)

  have hh_odd : ∀ i x, h i (sphereAntipodal N x) = -h i x := by
    intro i x
    have h1 : g i (sphereAntipodal N (sphereAntipodal N x)) = g i x := by
      rw [h_antipodal_invol x]
    dsimp only [h]
    rw [h1] <;> ring

  -- If F i is empty, then A i is empty
  have h_empty_implies : ∀ i, F i = ∅ → A i = ∅ := by
    intro i hF
    by_contra hA
    have h1 : Set.Nonempty (sphereAntipodal N '' A i) :=
      (Set.nonempty_iff_ne_empty.mpr hA).image _
    have h2 : Set.Nonempty (F i) := h1.closure
    rw [hF] at h2
    simp at h2

  -- g i x = 0 when x ∈ F i
  have h_g_zero_of_mem : ∀ i (x : SphereType), x ∈ F i → g i x = 0 := by
    intro i x hxF
    have h : down x ∈ F' i := ⟨x, hxF, rfl⟩
    exact Metric.infDist_zero_of_mem h

  -- g i x > 0 when x ∉ F i and F i nonempty
  have h_g_pos : ∀ i (x : SphereType), Set.Nonempty (F i) →
      x ∉ F i → 0 < g i x := by
    intro i x hF hnx
    have hF'_ne : Set.Nonempty (F' i) := hF.image down
    have h_down_not_in : down x ∉ F' i := by
      intro h
      rcases h with ⟨y, hyF, h_eq⟩
      have h_y_eq_x : y = x := ULift.down_injective h_eq
      rw [h_y_eq_x] at hyF
      exact hnx hyF
    exact (hF'_closed i).notMem_iff_infDist_pos hF'_ne |>.mp h_down_not_in

  -- Main property: h i x = 0 → x ∉ A i ∧ x ∉ sphereAntipodal N '' A i
  have h_main : ∀ i x, h i x = 0 →
      x ∉ A i ∧ x ∉ sphereAntipodal N '' A i := by
    intro i x h_eq
    by_cases hF : F i = ∅
    · have hA : A i = ∅ := h_empty_implies i hF
      constructor
      · rw [hA] <;> simp
      · rw [hA] <;> simp
    · have hF_ne : Set.Nonempty (F i) :=
        Set.nonempty_iff_ne_empty.mpr hF
      have h1 : g i x = g i (sphereAntipodal N x) := by linarith
      constructor
      · -- x ∉ A i
        intro hxA
        have h_x_not_F : x ∉ F i := by
          have h_disj : A i ∩ F i = ∅ := h_sep i
          have : x ∉ A i ∩ F i := by rw [h_disj] <;> simp
          exact fun h => this ⟨hxA, h⟩
        have h_pos : 0 < g i x := h_g_pos i x hF_ne h_x_not_F
        have h_antipodal_in_F : sphereAntipodal N x ∈ F i :=
          hF_subset i ⟨x, hxA, rfl⟩
        have h_zero : g i (sphereAntipodal N x) = 0 :=
          h_g_zero_of_mem i (sphereAntipodal N x) h_antipodal_in_F
        have h_h_pos : 0 < h i x := by
          dsimp only [h] at *
          linarith
        linarith [h_eq]
      · -- x ∉ sphereAntipodal N '' A i
        intro hx_img
        have h_x_in_F : x ∈ F i := hF_subset i hx_img
        have h_gx_zero : g i x = 0 := h_g_zero_of_mem i x h_x_in_F
        rcases hx_img with ⟨y, hyA, rfl⟩
        have h_y_not_F : y ∉ F i := by
          have h_disj : A i ∩ F i = ∅ := h_sep i
          have : y ∉ A i ∩ F i := by rw [h_disj] <;> simp
          exact fun h => this ⟨hyA, h⟩
        have h_g_y_pos : 0 < g i y := h_g_pos i y hF_ne h_y_not_F
        have h_h_neg : h i (sphereAntipodal N y) < 0 := by
          dsimp only [h]
          have h3 : g i (sphereAntipodal N (sphereAntipodal N y)) = g i y := by
            rw [h_antipodal_invol y]
          rw [h3, h_gx_zero]
          <;> linarith
        rw [h_eq] at h_h_neg <;> linarith

  -- Define f : SphereType → EuclideanSpace ℝ (Fin j)
  let piEquiv : EuclideanSpace ℝ (Fin j) ≃L[ℝ] (Fin j → ℝ) :=
    PiLp.continuousLinearEquiv 2 ℝ _

  let f : SphereType → EuclideanSpace ℝ (Fin j) := fun x =>
    piEquiv.symm (fun k : Fin j => h (e.symm k) x)

  have hf_cont : Continuous f := by
    fun_prop

  have hf_odd : ∀ x, f (sphereAntipodal N x) = -f x := by
    intro x
    have h4 : (fun k : Fin j => h (e.symm k) (sphereAntipodal N x)) =
        fun k : Fin j => -h (e.symm k) x := by
      funext k
      exact hh_odd (e.symm k) x
    have h5 : f (sphereAntipodal N x) =
        piEquiv.symm (fun k : Fin j => h (e.symm k) (sphereAntipodal N x)) := by rfl
    rw [h5, h4]
    have h6 : piEquiv.symm (fun k : Fin j => -h (e.symm k) x) =
        -piEquiv.symm (fun k : Fin j => h (e.symm k) x) := by
      exact piEquiv.symm.map_neg _
    rw [h6]

  have h_bu : 0 ∈ Set.range f := borsuk_ulam h_j f hf_cont hf_odd

  rcases h_bu with ⟨x, hx⟩
  have h_fx : f x = 0 := hx

  have h_all_zero : ∀ i : I, h i x = 0 := by
    intro i
    have h5 : piEquiv (f x) (e i) = 0 := by
      rw [h_fx] <;> simp [piEquiv]
    have h6 : piEquiv (f x) (e i) = h (e.symm (e i)) x := by
      simp [f, piEquiv]
    rw [h6] at h5
    have h7 : e.symm (e i) = i := e.left_inv i
    rw [h7] at h5
    exact h5

  have h_not_bad : x ∉ bad := by
    intro hxbad
    have h7 : x ∈ ⋃ i, (A i ∪ sphereAntipodal N '' A i) := h_cover hxbad
    rcases Set.mem_iUnion.mp h7 with ⟨i, hi⟩
    have h8 : h i x = 0 := h_all_zero i
    have h9 : x ∉ A i ∧ x ∉ sphereAntipodal N '' A i := h_main i x h8
    cases hi with
    | inl hxA => exact h9.1 hxA
    | inr hximg => exact h9.2 hximg

  exact ⟨x, h_not_bad⟩

end Kakeya.CV
