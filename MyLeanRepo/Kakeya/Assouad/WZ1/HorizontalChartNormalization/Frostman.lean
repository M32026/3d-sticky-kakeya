import MyLeanRepo.Kakeya.Assouad.WZ1.HorizontalChartNormalization.Basic

noncomputable section

namespace Kakeya.Assouad

open Kakeya.Streamlined MeasureTheory Set Metric

-- ============================================================================
-- 4. Tube cover transport and Frostman
-- ============================================================================

/-- Transport a tube cover. -/
def transportCover (e : Point3 ≃ₗᵢ[ℝ] Point3) {δ ρ : ℝ}
    {F : Streamlined.TubeFamily δ} {G : Streamlined.TubeFamily ρ}
    (P : Streamlined.TubeCover F G) :
    Streamlined.TubeCover (transportFamily e F) (transportFamily e G) where
  parent := P.parent
  parent_surjective := P.parent_surjective
  nested i := by
    have h := P.nested i
    have h1 : ((transportFamily e F).tube i).carrier =
        e '' (F.tube i).carrier := transportFamily_carrier e F i
    have h2 : ((transportFamily e G).tube (P.parent i)).carrier =
        e '' (G.tube (P.parent i)).carrier :=
      transportFamily_carrier e G (P.parent i)
    rw [h1, h2]
    intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    exact ⟨x, h hx, rfl⟩

/-- Transport Frostman property through a tube cover. -/
lemma transportCover_frostman
    (e : Point3 ≃ₗᵢ[ℝ] Point3)
    (e_invol : ∀ x, e (e x) = x)
    (hvol : ∀ s, volume (e '' s) = volume s)
    {δ ρ : ℝ} {F : Streamlined.TubeFamily δ} {G : Streamlined.TubeFamily ρ}
    {P : Streamlined.TubeCover F G} {C : ENNReal}
    (h : P.toFactoring.FibersAreCFrostman C) :
    (transportCover e P).toFactoring.FibersAreCFrostman C := by
  classical
  intro j K hKconv hKsub
  let Ksrc := e '' K
  have hKsrc_conv : Convex ℝ Ksrc := hKconv.linear_image e.toLinearMap
  have hKsrc_sub : Ksrc ⊆ (G.toBodyFamily.body j).carrier := by
    have hcar : ((transportFamily e G).toBodyFamily.body j).carrier =
        e '' (G.toBodyFamily.body j).carrier := transportFamily_toBody e G j
    rw [hcar] at hKsub
    have h3 : e '' K ⊆ e '' (e '' (G.toBodyFamily.body j).carrier) := by
      intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      exact ⟨x, hKsub hx, rfl⟩
    have h4 : e '' (e '' (G.toBodyFamily.body j).carrier) =
        (G.toBodyFamily.body j).carrier := by
      ext z
      simp only [Set.mem_image]
      constructor
      · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
        rw [e_invol x] <;> exact hx
      · intro hz
        exact ⟨e z, ⟨z, hz, rfl⟩, e_invol z⟩
    rw [h4] at h3
    exact h3
  have hsrc := h j Ksrc hKsrc_conv hKsrc_sub
  have h_parent : ∀ i,
      (transportCover e P).toFactoring.parent i = P.toFactoring.parent i := by
    intro i
    rfl
  have h_contain : ∀ i,
      ((transportFamily e F).toBodyFamily.body i).carrier ⊆ K ↔
      (F.toBodyFamily.body i).carrier ⊆ Ksrc := by
    intro i
    have hcar : ((transportFamily e F).toBodyFamily.body i).carrier =
        e '' (F.toBodyFamily.body i).carrier := transportFamily_toBody e F i
    rw [hcar]
    constructor
    · intro h5
      intro x hx
      have h6 : e x ∈ e '' (F.toBodyFamily.body i).carrier := ⟨x, hx, rfl⟩
      have h7 : e x ∈ K := h5 h6
      refine ⟨e x, h7, ?_⟩
      exact e_invol x
    · intro h5
      intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      have h8 : x ∈ Ksrc := h5 hx
      rcases h8 with ⟨y, hy, hxy⟩
      have h9 : e x = y := by
        calc e x = e (e y) := by rw [← hxy]
             _ = y := e_invol y
      rw [h9]
      exact hy
  have h_inner_eq : (transportCover e P).toFactoring.fiberIndices j =
      P.toFactoring.fiberIndices j := by
    dsimp only [Factoring.fiberIndices]
    <;> congr
    <;> funext i
    <;> rfl
  have h_filter : ((transportCover e P).toFactoring.fiberIndices j).filter
        (fun i => ((transportFamily e F).toBodyFamily.body i).carrier ⊆ K) =
      (P.toFactoring.fiberIndices j).filter
        (fun i => (F.toBodyFamily.body i).carrier ⊆ Ksrc) := by
    rw [h_inner_eq]
    apply Finset.filter_congr
    intro i _
    exact h_contain i
  have h_fcm : (transportCover e P).toFactoring.fiberContainedMass j K =
      P.toFactoring.fiberContainedMass j Ksrc := by
    have h_sum : ∑ i ∈ ((transportCover e P).toFactoring.fiberIndices j).filter
          (fun i => ((transportFamily e F).toBodyFamily.body i).carrier ⊆ K),
        ((transportFamily e F).toBodyFamily.body i).volume =
        ∑ i ∈ (P.toFactoring.fiberIndices j).filter
          (fun i => (F.toBodyFamily.body i).carrier ⊆ Ksrc),
        (F.toBodyFamily.body i).volume := by
      rw [h_filter]
      apply Finset.sum_congr rfl
      intro i _
      exact transportFamily_volume e hvol F i
    simpa [Factoring.fiberContainedMass] using h_sum
  have h_cvol : ((transportFamily e G).toBodyFamily.body j).volume =
      (G.toBodyFamily.body j).volume := transportFamily_volume e hvol G j
  have h_fm : (transportCover e P).toFactoring.fiberMass j =
      P.toFactoring.fiberMass j := by
    have h_sum : ∑ i ∈ (transportCover e P).toFactoring.fiberIndices j,
        ((transportFamily e F).toBodyFamily.body i).volume =
        ∑ i ∈ P.toFactoring.fiberIndices j, (F.toBodyFamily.body i).volume := by
      rw [h_inner_eq]
      apply Finset.sum_congr rfl
      intro i _
      exact transportFamily_volume e hvol F i
    simpa [Factoring.fiberMass] using h_sum
  have h_Kvol : volume K = volume Ksrc := by
    have h9 : volume Ksrc = volume K := hvol K
    exact h9.symm
  rw [h_fcm, h_cvol, h_fm, h_Kvol]
  exact hsrc

-- ============================================================================
-- 5. Uniform structure transport
-- ============================================================================

/-- Transport preserves uniformity of the assigned parent-map fibers. -/
lemma transportCover_assigned_fiberCount
    (e : Point3 ≃ₗᵢ[ℝ] Point3)
    {δ ρ : ℝ} {F : Streamlined.TubeFamily δ}
    {G : Streamlined.TubeFamily ρ}
    (P : Streamlined.TubeCover F G)
    (j : Fin G.card) :
    (transportCover e P).fiberCount j = P.fiberCount j := by
  rfl

/-- Transport preserves uniformity of the assigned parent-map fibers. -/
lemma transportCover_assigned_uniform
    (e : Point3 ≃ₗᵢ[ℝ] Point3)
    {δ ρ : ℝ} {F : Streamlined.TubeFamily δ}
    {G : Streamlined.TubeFamily ρ}
    {P : Streamlined.TubeCover F G} {C : ENNReal}
    (h : P.toFactoring.FibersAreCUniform C) :
    (transportCover e P).toFactoring.FibersAreCUniform C := by
  refine ⟨h.1, ?_⟩
  intro j k
  rw [TubeCover.toFactoring_fiberCount,
    TubeCover.toFactoring_fiberCount,
    transportCover_assigned_fiberCount,
    transportCover_assigned_fiberCount]
  have h2 := h.2 j k
  rwa [TubeCover.toFactoring_fiberCount,
    TubeCover.toFactoring_fiberCount] at h2

def transportUniform (e : Point3 ≃ₗᵢ[ℝ] Point3)
    (hvol : ∀ s, volume (e '' s) = volume s)
    {δ : ℝ} {F : Streamlined.TubeFamily δ}
    (U : UniformTubeStructure F) :
    UniformTubeStructure (transportFamily e F) where
  coarse rho := transportFamily e (U.coarse rho)
  cover rho := transportCover e (U.cover rho)
  uniformity := U.uniformity
  one_le_uniformity := U.one_le_uniformity
  uniformity_ne_top := U.uniformity_ne_top
  uniform rho :=
    transportCover_assigned_uniform e (U.uniform rho)
  coarse_distinct rho i j hne := by
    have h := U.coarse_distinct rho i j hne
    simp only [Kakeya.DeltaTube.EssentiallyDistinct] at h ⊢
    let G := U.coarse rho
    have hcar1 : ((transportFamily e G).tube i).carrier =
        e '' (G.tube i).carrier := transportFamily_carrier e G i
    have hcar2 : ((transportFamily e G).tube j).carrier =
        e '' (G.tube j).carrier := transportFamily_carrier e G j
    have hvol1 : ((transportFamily e G).tube i).volume = (G.tube i).volume :=
      transportTube_volume e hvol (G.tube i)
    have hvol2 : ((transportFamily e G).tube j).volume = (G.tube j).volume :=
      transportTube_volume e hvol (G.tube j)
    have h_inter : volume (((transportFamily e G).tube i).carrier ∩ ((transportFamily e G).tube j).carrier) =
        volume ((G.tube i).carrier ∩ (G.tube j).carrier) := by
      have h_set : ((transportFamily e G).tube i).carrier ∩ ((transportFamily e G).tube j).carrier =
          e '' ((G.tube i).carrier ∩ (G.tube j).carrier) := by
        rw [hcar1, hcar2, Set.image_inter e.injective]
      rw [h_set]
      exact hvol ((G.tube i).carrier ∩ (G.tube j).carrier)
    rw [h_inter, hvol1, hvol2]
    exact h

lemma transportUniform_frostman (e : Point3 ≃ₗᵢ[ℝ] Point3)
    (e_invol : ∀ x, e (e x) = x)
    (hvol : ∀ s, volume (e '' s) = volume s)
    {δ : ℝ} {F : Streamlined.TubeFamily δ}
    {U : UniformTubeStructure F} {C : ENNReal}
    (h : U.IsFrostmanAtEveryScale C) :
    (transportUniform e hvol U).IsFrostmanAtEveryScale C := by
  intro rho
  exact transportCover_frostman e e_invol hvol (h rho)


end Kakeya.Assouad
