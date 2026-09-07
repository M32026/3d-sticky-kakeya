import MyLeanRepo.Kakeya.Assouad.WZ1.ProjectionTheoremFirstLayerStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions
import MyLeanRepo.Kakeya.Assouad.WZ1.AngleGeometryBase
import MyLeanRepo.Kakeya.Assouad.Definitions
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Incidence graph construction for Kaufman projection in WZ1 Lemma 49

Given a tripartite graph `H` and a direction set `Λ` with assigned `G₁`/`G₂`
vertices, construct the corresponding bipartite incidence graph between `Λ`
and `F`.
-/

noncomputable section

namespace Kakeya.Assouad

open scoped ENNReal
attribute [local instance] Classical.propDecidable

/-- Fiber of `H` over a fixed `(b₁, b₂)` pair, projected to `F`. -/
def kaufmanFiber (H : Finset (Point2 × Point2 × Point2))
    (b1 b2 : Point2) : Finset Point2 :=
  (H.filter (fun e => e.2.1 = b1 ∧ e.2.2 = b2)).image (fun e => e.1)

/-- Fiber of `H` over fixed first and third coordinates, projected to `G₁`. -/
def kaufmanSecondFiber (H : Finset (Point2 × Point2 × Point2))
    (first third : Point2) : Finset Point2 :=
  (H.filter (fun e => e.1 = first ∧ e.2.2 = third)).image (fun e => e.2.1)

/-- Bipartite incidence graph with edges `(θ, f)` induced by triples in `H`. -/
def kaufmanIncidenceGraph
    (Λ : DiscreteSet 2) (b1 b2 : Point2 → Point2)
    (H : Finset (Point2 × Point2 × Point2)) : Finset (Point2 × Point2) :=
  Λ.biUnion (fun θ => (kaufmanFiber H (b1 θ) (b2 θ)).image (fun f => (θ, f)))

/-- Construct the Kaufman incidence graph from a uniform fiber-density input. -/
lemma kaufman_incidence_graph
    {F G₁ G₂ : DiscreteSet 2} {H : Finset (Point2 × Point2 × Point2)}
    {c : ENNReal} {Λ : DiscreteSet 2}
    (b1 b2 : Point2 → Point2)
    (hb1 : ∀ θ ∈ Λ, b1 θ ∈ G₁) (hb2 : ∀ θ ∈ Λ, b2 θ ∈ G₂)
    (hfiber : ∀ θ ∈ Λ,
      ((kaufmanFiber H (b1 θ) (b2 θ)).card : ENNReal) ≥ c * F.enncard)
    (hH_support : ∀ e ∈ H, e.1 ∈ F ∧ e.2.1 ∈ G₁ ∧ e.2.2 ∈ G₂) :
    ∃ (Hk : Finset (Point2 × Point2)),
      (∀ h ∈ Hk, h.1 ∈ Λ ∧ h.2 ∈ F) ∧
      (∀ θ ∈ Λ,
        ((Hk.filter (fun h => h.1 = θ)).card : ENNReal) ≥ c * F.enncard) ∧
      (∀ h ∈ Hk,
        ∃ e ∈ H, e.1 = h.2 ∧ e.2.1 = b1 h.1 ∧ e.2.2 = b2 h.1) := by
  let Hk := kaufmanIncidenceGraph Λ b1 b2 H
  have h1 : ∀ h ∈ Hk, h.1 ∈ Λ ∧ h.2 ∈ F := by
    intro h hh
    have h_ex : ∃ (θ : Point2), θ ∈ Λ ∧
        h ∈ (kaufmanFiber H (b1 θ) (b2 θ)).image (fun f => (θ, f)) := by
      simpa [Hk, kaufmanIncidenceGraph, Finset.mem_biUnion] using hh
    rcases h_ex with ⟨θ, hθ, h_in_image⟩
    rcases Finset.mem_image.mp h_in_image with ⟨f, hf, h_eq⟩
    have h_h_eq : h = (θ, f) := h_eq.symm
    rcases Finset.mem_image.mp hf with ⟨e, he, h_e_eq⟩
    have h2 : e.1 ∈ F := (hH_support e (Finset.mem_filter.mp he).1).1
    have h3 : h.1 = θ := by
      rw [h_h_eq] <;> rfl
    have h4 : h.2 = e.1 := by
      rw [h_h_eq, h_e_eq] <;> rfl
    exact ⟨by rw [h3]; exact hθ, by rw [h4]; exact h2⟩
  have h1b : ∀ h ∈ Hk,
      ∃ e ∈ H, e.1 = h.2 ∧ e.2.1 = b1 h.1 ∧ e.2.2 = b2 h.1 := by
    intro h hh
    have h_ex : ∃ (θ : Point2), θ ∈ Λ ∧
        h ∈ (kaufmanFiber H (b1 θ) (b2 θ)).image (fun f => (θ, f)) := by
      simpa [Hk, kaufmanIncidenceGraph, Finset.mem_biUnion] using hh
    rcases h_ex with ⟨θ, hθ, h_in_image⟩
    rcases Finset.mem_image.mp h_in_image with ⟨f, hf, h_eq⟩
    have h_h_eq : h = (θ, f) := h_eq.symm
    rcases Finset.mem_image.mp hf with ⟨e, he, h_e_eq⟩
    have he_in_H : e ∈ H := (Finset.mem_filter.mp he).1
    have h_e1 : e.1 = f := by simpa using h_e_eq
    have h_e21 : e.2.1 = b1 θ := (Finset.mem_filter.mp he).2.1
    have h_e22 : e.2.2 = b2 θ := (Finset.mem_filter.mp he).2.2
    have h_h1 : h.1 = θ := by rw [h_h_eq] <;> rfl
    have h_h2 : h.2 = f := by rw [h_h_eq] <;> rfl
    exact ⟨e, he_in_H, by rw [h_e1, h_h2], by rw [h_e21, h_h1],
      by rw [h_e22, h_h1]⟩
  have h2 : ∀ θ ∈ Λ, (Hk.filter (fun h => h.1 = θ)).card =
      (kaufmanFiber H (b1 θ) (b2 θ)).card := by
    intro θ hθ
    have h_eq : Hk.filter (fun h : Point2 × Point2 => h.1 = θ) =
        (kaufmanFiber H (b1 θ) (b2 θ)).image (fun f => (θ, f)) := by
      ext p
      simp only [Hk, kaufmanIncidenceGraph, Finset.mem_filter, Finset.mem_biUnion,
        Finset.mem_image]
      constructor
      · rintro ⟨⟨θ', hθ', f, hf, h_eq_pair⟩, hx1⟩
        have h_p1 : p.1 = θ' := (congr_arg Prod.fst h_eq_pair).symm
        have h_θ'_eq : θ' = θ := by
          rw [h_p1] at hx1
          exact hx1
        have hf' : f ∈ kaufmanFiber H (b1 θ) (b2 θ) := by
          rw [h_θ'_eq] at hf
          exact hf
        refine ⟨f, hf', ?_⟩
        have h_goal : (θ, f) = p := by
          have h : (θ, f) = (θ', f) := by
            ext <;> simp [h_θ'_eq] <;> rfl
          exact h.trans h_eq_pair
        exact h_goal
      · rintro ⟨f, hf, h_eq_pair⟩
        have h_p1 : p.1 = θ := (congr_arg Prod.fst h_eq_pair).symm
        exact ⟨⟨θ, hθ, f, hf, h_eq_pair⟩, h_p1⟩
    rw [h_eq]
    have h_inj : Set.InjOn (fun f : Point2 => (θ, f))
        (kaufmanFiber H (b1 θ) (b2 θ) : Set Point2) := by
      intro f1 _ f2 _ h
      simpa using h
    rw [Finset.card_image_of_injOn h_inj]
  refine ⟨Hk, h1, ?_, h1b⟩
  intro θ hθ
  rw [h2 θ hθ]
  exact hfiber θ hθ

/-- Uniform triple density gives the `F`-fiber bound over any edge's
fixed `(G₁, G₂)` coordinates. -/
lemma uniform_density_fiber_bound
    {F G₁ G₂ : DiscreteSet 2} {H : Finset (Point2 × Point2 × Point2)}
    {c : ENNReal} (hdensity : WZ1UniformTripleDensity c F G₁ G₂ H)
    (e0 : Point2 × Point2 × Point2) (he0 : e0 ∈ H) :
    ((kaufmanFiber H e0.2.1 e0.2.2).card : ENNReal) ≥ c * F.enncard := by
  let e_enc : Fin 3 → Point2 := wz1TripleCoordinate e0
  have he_enc : e_enc ∈ wz1EncodeTriples H :=
    Finset.mem_image.mpr ⟨e0, he0, rfl⟩
  let I : Finset (Fin 3) := {1, 2}
  have h_density := hdensity.2.2 e_enc he_enc I
  have h_univ_diff : (Finset.univ : Finset (Fin 3)) \ I = {0} := by decide
  have h_card_product :
      wz1VertexCardProduct (wz1TripleVertexClasses F G₁ G₂)
          ({0} : Finset (Fin 3)) = F.enncard := by
    simp [wz1VertexCardProduct, wz1TripleVertexClasses] <;> rfl
  rw [h_univ_diff, h_card_product] at h_density
  let hfiber := wz1HypergraphFiber (wz1EncodeTriples H) I e_enc
  let g : (Fin 3 → Point2) → Point2 := fun o => o 0
  have h_maps : ∀ other ∈ hfiber,
      g other ∈ kaufmanFiber H e0.2.1 e0.2.2 := by
    intro other hother
    have h1 : other ∈ wz1EncodeTriples H := (Finset.mem_filter.mp hother).1
    have h2 : ∀ i ∈ I, other i = e_enc i := (Finset.mem_filter.mp hother).2
    rcases Finset.mem_image.mp h1 with ⟨e, he, h_eq⟩
    have h_e1 : e.2.1 = e0.2.1 := by
      have h_step1 : (wz1TripleCoordinate e) 1 = other 1 := congr_fun h_eq 1
      have h_step2 : other 1 = e_enc 1 := h2 1 (by simp [I])
      have h_step3 : e_enc 1 = e0.2.1 := by rfl
      have h_step4 : (wz1TripleCoordinate e) 1 = e.2.1 := by rfl
      exact h_step4.symm.trans h_step1 |>.trans h_step2 |>.trans h_step3
    have h_e2 : e.2.2 = e0.2.2 := by
      have h_step1 : (wz1TripleCoordinate e) 2 = other 2 := congr_fun h_eq 2
      have h_step2 : other 2 = e_enc 2 := h2 2 (by simp [I])
      have h_step3 : e_enc 2 = e0.2.2 := by rfl
      have h_step4 : (wz1TripleCoordinate e) 2 = e.2.2 := by rfl
      exact h_step4.symm.trans h_step1 |>.trans h_step2 |>.trans h_step3
    have he_filtered :
        e ∈ H.filter (fun e => e.2.1 = e0.2.1 ∧ e.2.2 = e0.2.2) :=
      Finset.mem_filter.mpr ⟨he, ⟨h_e1, h_e2⟩⟩
    have h_goal : e.1 ∈ kaufmanFiber H e0.2.1 e0.2.2 := by
      simp only [kaufmanFiber, Finset.mem_image]
      exact ⟨e, he_filtered, rfl⟩
    have h_g : g other = e.1 := by
      dsimp only [g]
      have h1 : (wz1TripleCoordinate e) 0 = other 0 := congr_fun h_eq 0
      have h2 : (wz1TripleCoordinate e) 0 = e.1 := by rfl
      exact h1.symm.trans h2
    rw [h_g]
    exact h_goal
  have h_inj : Set.InjOn g (hfiber : Set (Fin 3 → Point2)) := by
    intro o1 ho1 o2 ho2 h
    have hcond1 : ∀ i ∈ I, o1 i = e_enc i := (Finset.mem_filter.mp ho1).2
    have hcond2 : ∀ i ∈ I, o2 i = e_enc i := (Finset.mem_filter.mp ho2).2
    have h0 : o1 0 = o2 0 := h
    have h1 : o1 1 = o2 1 := by
      have h11 : o1 1 = e_enc 1 := hcond1 1 (by simp [I])
      have h12 : o2 1 = e_enc 1 := hcond2 1 (by simp [I])
      exact h11.trans h12.symm
    have h2 : o1 2 = o2 2 := by
      have h21 : o1 2 = e_enc 2 := hcond1 2 (by simp [I])
      have h22 : o2 2 = e_enc 2 := hcond2 2 (by simp [I])
      exact h21.trans h22.symm
    have h_eq : ∀ (i : Fin 3), o1 i = o2 i := by
      intro i
      fin_cases i <;> tauto
    exact funext h_eq
  have h_image_sub :
      hfiber.image g ⊆ kaufmanFiber H e0.2.1 e0.2.2 := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨other, hother, rfl⟩
    exact h_maps other hother
  have h_card_image : (hfiber.image g).card = hfiber.card :=
    Finset.card_image_of_injOn h_inj
  have h_card_ge :
      (hfiber.card : ENNReal) ≤ (kaufmanFiber H e0.2.1 e0.2.2).card := by
    have h : (hfiber.image g).card ≤ (kaufmanFiber H e0.2.1 e0.2.2).card :=
      Finset.card_le_card h_image_sub
    rw [h_card_image] at h
    exact_mod_cast h
  exact h_density.trans h_card_ge

/-- Uniform triple density gives the `G₁`-fiber bound over any edge's fixed
`(F, G₂)` coordinates. -/
lemma uniform_density_second_fiber_bound
    {F G₁ G₂ : DiscreteSet 2} {H : Finset (Point2 × Point2 × Point2)}
    {c : ENNReal} (hdensity : WZ1UniformTripleDensity c F G₁ G₂ H)
    (e0 : Point2 × Point2 × Point2) (he0 : e0 ∈ H) :
    ((kaufmanSecondFiber H e0.1 e0.2.2).card : ENNReal) ≥
      c * G₁.enncard := by
  let e_enc : Fin 3 → Point2 := wz1TripleCoordinate e0
  have he_enc : e_enc ∈ wz1EncodeTriples H :=
    Finset.mem_image.mpr ⟨e0, he0, rfl⟩
  let I : Finset (Fin 3) := {0, 2}
  have h_density := hdensity.2.2 e_enc he_enc I
  have h_univ_diff : (Finset.univ : Finset (Fin 3)) \ I = {1} := by
    decide
  have h_card_product :
      wz1VertexCardProduct (wz1TripleVertexClasses F G₁ G₂)
          ({1} : Finset (Fin 3)) = G₁.enncard := by
    simp [wz1VertexCardProduct, wz1TripleVertexClasses] <;> rfl
  rw [h_univ_diff, h_card_product] at h_density
  let hypergraphFiber :=
    wz1HypergraphFiber (wz1EncodeTriples H) I e_enc
  let projectSecond : (Fin 3 → Point2) → Point2 := fun edge => edge 1
  have h_maps : ∀ other ∈ hypergraphFiber,
      projectSecond other ∈ kaufmanSecondFiber H e0.1 e0.2.2 := by
    intro other hother
    have hencoded : other ∈ wz1EncodeTriples H :=
      (Finset.mem_filter.mp hother).1
    have hfixed : ∀ i ∈ I, other i = e_enc i :=
      (Finset.mem_filter.mp hother).2
    rcases Finset.mem_image.mp hencoded with ⟨edge, hedge, hedgeEq⟩
    have hfirst : edge.1 = e0.1 := by
      calc
        edge.1 = (wz1TripleCoordinate edge) 0 := rfl
        _ = other 0 := congr_fun hedgeEq 0
        _ = e_enc 0 := hfixed 0 (by simp [I])
        _ = e0.1 := rfl
    have hthird : edge.2.2 = e0.2.2 := by
      calc
        edge.2.2 = (wz1TripleCoordinate edge) 2 := rfl
        _ = other 2 := congr_fun hedgeEq 2
        _ = e_enc 2 := hfixed 2 (by simp [I])
        _ = e0.2.2 := rfl
    have hfiltered :
        edge ∈ H.filter (fun current =>
          current.1 = e0.1 ∧ current.2.2 = e0.2.2) :=
      Finset.mem_filter.mpr ⟨hedge, hfirst, hthird⟩
    have hproject : projectSecond other = edge.2.1 := by
      exact (congr_fun hedgeEq 1).symm
    rw [hproject]
    exact Finset.mem_image.mpr ⟨edge, hfiltered, rfl⟩
  have hinjective :
      Set.InjOn projectSecond
        (hypergraphFiber : Set (Fin 3 → Point2)) := by
    intro first hfirst second hsecond heq
    have hfirstFixed : ∀ i ∈ I, first i = e_enc i :=
      (Finset.mem_filter.mp hfirst).2
    have hsecondFixed : ∀ i ∈ I, second i = e_enc i :=
      (Finset.mem_filter.mp hsecond).2
    apply funext
    intro i
    fin_cases i
    · exact (hfirstFixed 0 (by simp [I])).trans
        (hsecondFixed 0 (by simp [I])).symm
    · exact heq
    · exact (hfirstFixed 2 (by simp [I])).trans
        (hsecondFixed 2 (by simp [I])).symm
  have himage :
      hypergraphFiber.image projectSecond ⊆
        kaufmanSecondFiber H e0.1 e0.2.2 := by
    intro point hpoint
    rcases Finset.mem_image.mp hpoint with ⟨other, hother, rfl⟩
    exact h_maps other hother
  have hcard :
      hypergraphFiber.card ≤
        (kaufmanSecondFiber H e0.1 e0.2.2).card := by
    rw [← Finset.card_image_of_injOn hinjective]
    exact Finset.card_le_card himage
  exact h_density.trans (by exact_mod_cast hcard)

end Kakeya.Assouad
