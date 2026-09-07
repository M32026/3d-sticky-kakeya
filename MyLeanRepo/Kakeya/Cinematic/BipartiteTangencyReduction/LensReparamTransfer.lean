import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.LensReparam

/-!
# Minimal reparametrization transfer lemmas for graph lenses

This module provides only the essential lemmas for transferring overlap
and equality between original and reparametrized graph lenses:

- `GraphLens.reparam_f`, `GraphLens.reparam_g`: field accessors
- `GraphLens.overlap_forward_reparam`: original overlap → reparam overlap
- `reparam_shifted_eq_imp_eq_from_no_tang`: reparam equality + no-tangency → equality
- `GraphLens.overlap_backward_reparam`: reparam overlap → original overlap

No convenience wrappers or non-overlap transfer lemmas are included.
-/

namespace Kakeya.Cinematic

open C2Function

/-- The f-field of a reparametrized lens. -/
lemma GraphLens.reparam_f (L : GraphLens) {I : ParameterInterval} {hI : 0 < I.length}
    {hleft hright} :
    (L.reparam I hI hleft hright).f = L.f.reparam I := by
  rfl

/-- The g-field of a reparametrized lens. -/
lemma GraphLens.reparam_g (L : GraphLens) {I : ParameterInterval} {hI : 0 < I.length}
    {hleft hright} :
    (L.reparam I hI hleft hright).g = L.g.reparam I := by
  rfl

/--
If two original graph lenses overlap, their reparametrizations also overlap.
-/
lemma GraphLens.overlap_forward_reparam
    {L1 L2 : GraphLens} {I : ParameterInterval} {hI : 0 < I.length}
    {hleft1 hright1 hleft2 hright2}
    (h : L1.Overlap L2) :
    (L1.reparam I hI hleft1 hright1).Overlap (L2.reparam I hI hleft2 hright2) := by
  let L1' := L1.reparam I hI hleft1 hright1
  let L2' := L2.reparam I hI hleft2 hright2
  rcases h with ⟨hshare, hinterval⟩
  have hshare' : L1'.f = L2'.f ∨ L1'.f = L2'.g ∨ L1'.g = L2'.f ∨ L1'.g = L2'.g := by
    rcases hshare with (h | h | h | h)
    · exact Or.inl (by rw [GraphLens.reparam_f, GraphLens.reparam_f, h])
    · exact Or.inr (Or.inl (by rw [GraphLens.reparam_f, GraphLens.reparam_g, h]))
    · exact Or.inr (Or.inr (Or.inl (by rw [GraphLens.reparam_g, GraphLens.reparam_f, h])))
    · exact Or.inr (Or.inr (Or.inr (by rw [GraphLens.reparam_g, GraphLens.reparam_g, h])))
  have h1 : (L1.left : ℝ) < (L1.right : ℝ) := L1.left_lt_right
  have h2 : (L1.left : ℝ) < (L2.right : ℝ) := by
    calc (L1.left : ℝ) ≤ max (L1.left : ℝ) (L2.left : ℝ) := le_max_left _ _
      _ < min (L1.right : ℝ) (L2.right : ℝ) := hinterval
      _ ≤ (L2.right : ℝ) := min_le_right _ _
  have h3 : (L2.left : ℝ) < (L1.right : ℝ) := by
    calc (L2.left : ℝ) ≤ max (L1.left : ℝ) (L2.left : ℝ) := le_max_right _ _
      _ < min (L1.right : ℝ) (L2.right : ℝ) := hinterval
      _ ≤ (L1.right : ℝ) := min_le_left _ _
  have h4 : (L2.left : ℝ) < (L2.right : ℝ) := L2.left_lt_right
  have hp1 : (L1'.left : ℝ) < (L1'.right : ℝ) :=
    invPhiMap_strictMono I hI L1.left L1.right hleft1 hright1 h1
  have hp2 : (L1'.left : ℝ) < (L2'.right : ℝ) :=
    invPhiMap_strictMono I hI L1.left L2.right hleft1 hright2 h2
  have hp3 : (L2'.left : ℝ) < (L1'.right : ℝ) :=
    invPhiMap_strictMono I hI L2.left L1.right hleft2 hright1 h3
  have hp4 : (L2'.left : ℝ) < (L2'.right : ℝ) :=
    invPhiMap_strictMono I hI L2.left L2.right hleft2 hright2 h4
  have hmax1 : max (L1'.left : ℝ) (L2'.left : ℝ) < (L1'.right : ℝ) := by
    rw [max_lt_iff] <;> exact ⟨hp1, hp3⟩
  have hmax2 : max (L1'.left : ℝ) (L2'.left : ℝ) < (L2'.right : ℝ) := by
    rw [max_lt_iff] <;> exact ⟨hp2, hp4⟩
  have hinterval' : max (L1'.left : ℝ) (L2'.left : ℝ) < min (L1'.right : ℝ) (L2'.right : ℝ) :=
    lt_min hmax1 hmax2
  exact ⟨hshare', hinterval'⟩

/--
If the reparametrizations of two shifted functions are equal, and the family
has no exact tangencies on `I`, then the original functions are equal.
-/
lemma reparam_shifted_eq_imp_eq_from_no_tang
    {F : FiniteFunctionFamily} {I : ParameterInterval} {shift : C2Function → ℝ}
    (h_no_tang : F.HasNoExactTangenciesOn I shift)
    (hI_pos : 0 < I.length)
    {f g : C2Function} (hf : f ∈ F.carrier) (hg : g ∈ F.carrier)
    (h_eq : (f.verticalTranslate (shift f)).reparam I =
            (g.verticalTranslate (shift g)).reparam I) :
    f = g := by
  by_contra h_ne
  let x0 : UnitPoint := ⟨0, ⟨by norm_num, by norm_num⟩⟩
  let y0 := phiMap I x0
  have hy0 : y0 ∈ I.carrier := phiMap_mem_carrier I x0
  have h_val : (f.verticalTranslate (shift f)) y0 =
               (g.verticalTranslate (shift g)) y0 := by
    have h1 : ((f.verticalTranslate (shift f)).reparam I) x0 =
              ((g.verticalTranslate (shift g)).reparam I) x0 := by
      rw [h_eq]
    exact (reparam_intersection_iff _ _ I x0).mp h1
  have h_deriv : (f.verticalTranslate (shift f)).firstDeriv y0 =
                 (g.verticalTranslate (shift g)).firstDeriv y0 := by
    have h1 : ((f.verticalTranslate (shift f)).reparam I).firstDeriv x0 =
              ((g.verticalTranslate (shift g)).reparam I).firstDeriv x0 := by
      rw [h_eq]
    exact (reparam_deriv_eq_iff _ _ I hI_pos x0).mp h1
  have h_contra := h_no_tang hf hg h_ne y0 hy0
  rcases h_contra with (h_contra | h_contra)
  · exact h_contra h_val
  · exact h_contra h_deriv

/--
If two reparametrized graph lenses overlap, and field equality transfers back
through reparam, then the original lenses overlap.
-/
lemma GraphLens.overlap_backward_reparam
    {L1 L2 : GraphLens} {I : ParameterInterval} {hI : 0 < I.length}
    {hleft1 hright1 hleft2 hright2}
    (h1 : L1.f.reparam I = L2.f.reparam I → L1.f = L2.f)
    (h2 : L1.f.reparam I = L2.g.reparam I → L1.f = L2.g)
    (h3 : L1.g.reparam I = L2.f.reparam I → L1.g = L2.f)
    (h4 : L1.g.reparam I = L2.g.reparam I → L1.g = L2.g)
    (h : (L1.reparam I hI hleft1 hright1).Overlap
         (L2.reparam I hI hleft2 hright2)) :
    L1.Overlap L2 := by
  let L1' := L1.reparam I hI hleft1 hright1
  let L2' := L2.reparam I hI hleft2 hright2
  rcases h with ⟨hshare, hinterval⟩
  have hshare_orig : L1.f = L2.f ∨ L1.f = L2.g ∨ L1.g = L2.f ∨ L1.g = L2.g := by
    rcases hshare with (h | h | h | h)
    · have h' : L1.f.reparam I = L2.f.reparam I := by
        have hfa : L1'.f = L1.f.reparam I := GraphLens.reparam_f L1
        have hfb : L2'.f = L2.f.reparam I := GraphLens.reparam_f L2
        rw [hfa, hfb] at h
        exact h
      exact Or.inl (h1 h')
    · have h' : L1.f.reparam I = L2.g.reparam I := by
        have hfa : L1'.f = L1.f.reparam I := GraphLens.reparam_f L1
        have hgb : L2'.g = L2.g.reparam I := GraphLens.reparam_g L2
        rw [hfa, hgb] at h
        exact h
      exact Or.inr (Or.inl (h2 h'))
    · have h' : L1.g.reparam I = L2.f.reparam I := by
        have hga : L1'.g = L1.g.reparam I := GraphLens.reparam_g L1
        have hfb : L2'.f = L2.f.reparam I := GraphLens.reparam_f L2
        rw [hga, hfb] at h
        exact h
      exact Or.inr (Or.inr (Or.inl (h3 h')))
    · have h' : L1.g.reparam I = L2.g.reparam I := by
        have hga : L1'.g = L1.g.reparam I := GraphLens.reparam_g L1
        have hgb : L2'.g = L2.g.reparam I := GraphLens.reparam_g L2
        rw [hga, hgb] at h
        exact h
      exact Or.inr (Or.inr (Or.inr (h4 h')))
  have hp1 : (L1'.left : ℝ) < (L1'.right : ℝ) := L1'.left_lt_right
  have hp2 : (L1'.left : ℝ) < (L2'.right : ℝ) := by
    calc (L1'.left : ℝ) ≤ max (L1'.left : ℝ) (L2'.left : ℝ) := le_max_left _ _
      _ < min (L1'.right : ℝ) (L2'.right : ℝ) := hinterval
      _ ≤ (L2'.right : ℝ) := min_le_right _ _
  have hp3 : (L2'.left : ℝ) < (L1'.right : ℝ) := by
    calc (L2'.left : ℝ) ≤ max (L1'.left : ℝ) (L2'.left : ℝ) := le_max_right _ _
      _ < min (L1'.right : ℝ) (L2'.right : ℝ) := hinterval
      _ ≤ (L1'.right : ℝ) := min_le_left _ _
  have hp4 : (L2'.left : ℝ) < (L2'.right : ℝ) := L2'.left_lt_right
  have hq1 : (L1.left : ℝ) < (L1.right : ℝ) := by
    have h_phi1 : phiMap I L1'.left = L1.left := phiMap_invPhiMap I hI L1.left hleft1
    have h_phi2 : phiMap I L1'.right = L1.right := phiMap_invPhiMap I hI L1.right hright1
    have h : (phiMap I L1'.left : ℝ) < (phiMap I L1'.right : ℝ) := phiMap_strictMono I hI hp1
    simpa [h_phi1, h_phi2] using h
  have hq2 : (L1.left : ℝ) < (L2.right : ℝ) := by
    have h_phi1 : phiMap I L1'.left = L1.left := phiMap_invPhiMap I hI L1.left hleft1
    have h_phi2 : phiMap I L2'.right = L2.right := phiMap_invPhiMap I hI L2.right hright2
    have h : (phiMap I L1'.left : ℝ) < (phiMap I L2'.right : ℝ) := phiMap_strictMono I hI hp2
    simpa [h_phi1, h_phi2] using h
  have hq3 : (L2.left : ℝ) < (L1.right : ℝ) := by
    have h_phi1 : phiMap I L2'.left = L2.left := phiMap_invPhiMap I hI L2.left hleft2
    have h_phi2 : phiMap I L1'.right = L1.right := phiMap_invPhiMap I hI L1.right hright1
    have h : (phiMap I L2'.left : ℝ) < (phiMap I L1'.right : ℝ) := phiMap_strictMono I hI hp3
    simpa [h_phi1, h_phi2] using h
  have hq4 : (L2.left : ℝ) < (L2.right : ℝ) := by
    have h_phi1 : phiMap I L2'.left = L2.left := phiMap_invPhiMap I hI L2.left hleft2
    have h_phi2 : phiMap I L2'.right = L2.right := phiMap_invPhiMap I hI L2.right hright2
    have h : (phiMap I L2'.left : ℝ) < (phiMap I L2'.right : ℝ) := phiMap_strictMono I hI hp4
    simpa [h_phi1, h_phi2] using h
  have hmax1 : max (L1.left : ℝ) (L2.left : ℝ) < (L1.right : ℝ) := by
    rw [max_lt_iff] <;> exact ⟨hq1, hq3⟩
  have hmax2 : max (L1.left : ℝ) (L2.left : ℝ) < (L2.right : ℝ) := by
    rw [max_lt_iff] <;> exact ⟨hq2, hq4⟩
  have hinterval_orig : max (L1.left : ℝ) (L2.left : ℝ) < min (L1.right : ℝ) (L2.right : ℝ) :=
    lt_min hmax1 hmax2
  exact ⟨hshare_orig, hinterval_orig⟩

end Kakeya.Cinematic
