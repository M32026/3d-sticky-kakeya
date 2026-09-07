import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.LensReparamTransfer

/-!
# Preserve graph-lens non-overlap under reparametrization

When every lens side is a perturbed member of one finite family with no exact
tangencies on the parameter interval, equality of reparametrized sides
recovers equality of the original sides. The existing backward-overlap
transport then preserves non-overlap.
-/

namespace Kakeya.Cinematic

lemma GraphLens.nonoverlap_reparam_of_no_tang
    {F : FiniteFunctionFamily}
    {I : ParameterInterval} {hI : 0 < I.length}
    {shift : C2Function → ℝ}
    (h_no_tang : F.HasNoExactTangenciesOn I shift)
    {L₁ L₂ : GraphLens}
    {hleft₁ hright₁ hleft₂ hright₂}
    {f₁ g₁ f₂ g₂ : C2Function}
    (hf₁ : f₁ ∈ F.carrier) (hg₁ : g₁ ∈ F.carrier)
    (hf₂ : f₂ ∈ F.carrier) (hg₂ : g₂ ∈ F.carrier)
    (hL₁f : L₁.f = f₁.verticalTranslate (shift f₁))
    (hL₁g : L₁.g = g₁.verticalTranslate (shift g₁))
    (hL₂f : L₂.f = f₂.verticalTranslate (shift f₂))
    (hL₂g : L₂.g = g₂.verticalTranslate (shift g₂))
    (h_orig : L₁.Nonoverlap L₂) :
    (L₁.reparam I hI hleft₁ hright₁).Nonoverlap
      (L₂.reparam I hI hleft₂ hright₂) := by
  intro h_overlap
  apply h_orig
  apply GraphLens.overlap_backward_reparam
      (L1 := L₁) (L2 := L₂)
      (hleft1 := hleft₁) (hright1 := hright₁)
      (hleft2 := hleft₂) (hright2 := hright₂)
  · intro h
    have h_eq : f₁ = f₂ := by
      apply reparam_shifted_eq_imp_eq_from_no_tang
          h_no_tang hI hf₁ hf₂
      simpa only [hL₁f, hL₂f] using h
    rw [hL₁f, hL₂f, h_eq]
  · intro h
    have h_eq : f₁ = g₂ := by
      apply reparam_shifted_eq_imp_eq_from_no_tang
          h_no_tang hI hf₁ hg₂
      simpa only [hL₁f, hL₂g] using h
    rw [hL₁f, hL₂g, h_eq]
  · intro h
    have h_eq : g₁ = f₂ := by
      apply reparam_shifted_eq_imp_eq_from_no_tang
          h_no_tang hI hg₁ hf₂
      simpa only [hL₁g, hL₂f] using h
    rw [hL₁g, hL₂f, h_eq]
  · intro h
    have h_eq : g₁ = g₂ := by
      apply reparam_shifted_eq_imp_eq_from_no_tang
          h_no_tang hI hg₁ hg₂
      simpa only [hL₁g, hL₂g] using h
    rw [hL₁g, hL₂g, h_eq]
  · exact h_overlap

end Kakeya.Cinematic
