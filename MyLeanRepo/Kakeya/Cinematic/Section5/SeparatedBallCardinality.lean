import MyLeanRepo.Kakeya.Cinematic.Section5.FineFiberIncidenceGraph

/-!
# Cardinality of a small ball in a separated function family

If a finite family is `delta`-separated and `2r < delta`, every radius-`r`
ball contains at most one family element.  This is the complementary
small-radius branch to the two-ends metric nonconcentration estimate.
-/

namespace Kakeya.Cinematic

noncomputable local instance separatedBallCardinalityDecidableEq :
    DecidableEq C2Function := Classical.decEq _

lemma separated_family_ball_ncard_le_one
    (F : FiniteFunctionFamily)
    {delta radius : ℝ}
    (hsep : F.IsDeltaSeparated delta)
    (hradius : 2 * radius < delta)
    (center : C2Function) :
    ((F.carrier ∩ c2Ball center radius).ncard : ℝ) ≤ 1 := by
  classical
  have hfinite :
      (F.carrier ∩ c2Ball center radius).Finite :=
    F.finite.inter_of_left _
  let S : Finset C2Function :=
    hfinite.toFinset
  have hcard : S.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro f hf g hg
    have hf' :
        f ∈ F.carrier ∩ c2Ball center radius := by
      simpa [S] using hf
    have hg' :
        g ∈ F.carrier ∩ c2Ball center radius := by
      simpa [S] using hg
    by_contra hfg
    have hsep' : delta ≤ dist f g :=
      hsep hf'.1 hg'.1 hfg
    have htriangle :
        dist f g ≤ dist f center + dist center g :=
      dist_triangle f center g
    have hfball : dist f center ≤ radius := by
      simpa [c2Distance_eq_dist] using hf'.2
    have hgball : dist center g ≤ radius := by
      have h : dist g center ≤ radius := by
        simpa [c2Distance_eq_dist] using hg'.2
      simpa [dist_comm] using h
    linarith
  have hncard :
      (F.carrier ∩ c2Ball center radius).ncard = S.card := by
    exact Set.ncard_eq_toFinset_card _ hfinite
  rw [hncard]
  exact_mod_cast hcard

lemma selected_incidence_fiber_small_ball_ncard_le_one
    {β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (ambient : FiniteFunctionFamily)
    {delta radius : ℝ}
    (hsep : ambient.IsDeltaSeparated delta)
    (hradius : 2 * radius < delta)
    (rectangles : Finset β)
    (fiber : β → FiniteFunctionFamily)
    (selected : Finset (C2Function × β))
    (hselected :
      selected ⊆ fineFiberIncidenceEdgesOn rectangles fiber)
    (hfiber : ∀ rectangle ∈ rectangles,
      (fiber rectangle).carrier ⊆ ambient.carrier)
    (parent : β → γ) (coarse : γ)
    (rectangle : β)
    (hrectangle :
      rectangle ∈ incidenceRectangleSupport selected parent coarse)
    (center : C2Function) :
    (((incidenceRectangleFiber selected rectangle : Set C2Function) ∩
        c2Ball center radius).ncard : ℝ) ≤ 1 := by
  classical
  have hrectangle' : rectangle ∈ rectangles :=
    incidenceRectangleSupport_subset_selected
      rectangles fiber selected hselected parent coarse hrectangle
  have hsubset :
      (incidenceRectangleFiber selected rectangle : Set C2Function) ⊆
        ambient.carrier := by
    intro function hfunction
    have hfunction' :
        function ∈ (fiber rectangle).toFinset :=
      incidenceRectangleFiber_subset_fiber_on
        rectangles fiber selected hselected rectangle hfunction
    have hfunctionFiber : function ∈ (fiber rectangle).carrier := by
      simpa [FiniteFunctionFamily.toFinset] using hfunction'
    exact hfiber rectangle hrectangle' hfunctionFiber
  have hinter :
      ((incidenceRectangleFiber selected rectangle : Set C2Function) ∩
          c2Ball center radius) ⊆
        ambient.carrier ∩ c2Ball center radius :=
    Set.inter_subset_inter hsubset (Set.Subset.refl _)
  have hfinite :
      (ambient.carrier ∩ c2Ball center radius).Finite :=
    ambient.finite.inter_of_left _
  have hncard :
      ((incidenceRectangleFiber selected rectangle : Set C2Function) ∩
          c2Ball center radius).ncard ≤
        (ambient.carrier ∩ c2Ball center radius).ncard :=
    Set.ncard_le_ncard hinter hfinite
  have hcast :
      (((incidenceRectangleFiber selected rectangle : Set C2Function) ∩
          c2Ball center radius).ncard : ℝ) ≤
        ((ambient.carrier ∩ c2Ball center radius).ncard : ℝ) := by
    exact_mod_cast hncard
  exact hcast.trans <|
    separated_family_ball_ncard_le_one
      ambient hsep hradius center

end Kakeya.Cinematic
