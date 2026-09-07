import MyLeanRepo.Kakeya.Cinematic.Geometry
import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.PerturbationPreservation

/-!
# Transfer no-exact-tangency certificates

This module transfers a no-exact-tangency certificate along an injective map
from a perturbed finite family to its original representatives. The concrete
bipartite wrapper handles a fixed vertical shift on the white family.
-/

noncomputable section

namespace Kakeya.Cinematic

open Set

private lemma verticalTranslate_zero_local (f : C2Function) :
    f.verticalTranslate 0 = f := by
  apply C2Function.toJet_injective
  dsimp only [C2Function.toJet]
  apply Prod.ext
  · ext x
    change (f.verticalTranslate 0) x = f x
    simp [verticalTranslate_apply]
  · apply Prod.ext <;> rfl

lemma no_tangencies_transfer_of_embedding
    {F F_union : FiniteFunctionFamily} {I : ParameterInterval}
    {shift shift' : C2Function → ℝ}
    (orig : C2Function → C2Function)
    (h_orig_mem : ∀ h ∈ F.carrier, orig h ∈ F_union.carrier)
    (h_orig_inj : ∀ f ∈ F.carrier, ∀ g ∈ F.carrier,
      orig f = orig g → f = g)
    (h_curve : ∀ h ∈ F.carrier,
      h.verticalTranslate (shift' h) =
        (orig h).verticalTranslate (shift (orig h)))
    (h_no_tang : F_union.HasNoExactTangenciesOn I shift) :
    F.HasNoExactTangenciesOn I shift' := by
  intro f hf g hg hfg x hx
  have h_orig_ne : orig f ≠ orig g := by
    intro h
    exact hfg (h_orig_inj f hf g hg h)
  have h_tang :=
    h_no_tang (h_orig_mem f hf) (h_orig_mem g hg) h_orig_ne x hx
  have hf_value :=
    congrArg (fun q : C2Function => q x) (h_curve f hf)
  have hg_value :=
    congrArg (fun q : C2Function => q x) (h_curve g hg)
  have hf_deriv :=
    congrArg (fun q : C2Function => q.firstDeriv x) (h_curve f hf)
  have hg_deriv :=
    congrArg (fun q : C2Function => q.firstDeriv x) (h_curve g hg)
  rcases h_tang with hvalue | hderiv
  · left
    intro heq
    apply hvalue
    calc
      ((orig f).verticalTranslate (shift (orig f))) x =
          (f.verticalTranslate (shift' f)) x := hf_value.symm
      _ = (g.verticalTranslate (shift' g)) x := heq
      _ = ((orig g).verticalTranslate (shift (orig g))) x := hg_value
  · right
    intro heq
    apply hderiv
    calc
      ((orig f).verticalTranslate (shift (orig f))).firstDeriv x =
          (f.verticalTranslate (shift' f)).firstDeriv x := hf_deriv.symm
      _ = (g.verticalTranslate (shift' g)).firstDeriv x := heq
      _ = ((orig g).verticalTranslate (shift (orig g))).firstDeriv x :=
        hg_deriv

lemma no_tangencies_transfer
    {W B F F_union : FiniteFunctionFamily} {I : ParameterInterval}
    {shift0 shift shift' : C2Function → ℝ} {epsilon_dir : ℝ}
    (hF_union : F_union.carrier = W.carrier ∪ B.carrier)
    (h_W_B_disjoint : ∀ w ∈ W.carrier, w ∉ B.carrier)
    (h_disjoint : ∀ w ∈ W.carrier,
      w.verticalTranslate epsilon_dir ∉ B.carrier)
    (hF_W : ∀ f ∈ F.carrier,
      (∃ w ∈ W.carrier,
        f = w.verticalTranslate epsilon_dir) ∨
        f ∈ B.carrier)
    (h_shift'_W : ∀ w ∈ W.carrier,
      shift' (w.verticalTranslate epsilon_dir) = shift0 w)
    (h_shift'_B : ∀ b ∈ B.carrier, shift' b = shift0 b)
    (h_shift_W : ∀ w ∈ W.carrier,
      shift w = epsilon_dir + shift0 w)
    (h_shift_B : ∀ b ∈ B.carrier, shift b = shift0 b)
    (h_no_tang : F_union.HasNoExactTangenciesOn I shift) :
    F.HasNoExactTangenciesOn I shift' := by
  classical
  let orig (h : C2Function) : C2Function :=
    if h ∈ B.toFinset then h
    else h.verticalTranslate (-epsilon_dir)
  have hB_mem : ∀ b ∈ B.carrier, b ∈ B.toFinset := by
    intro b hb
    exact B.finite.mem_toFinset.mpr hb
  have hshift_not_B : ∀ w ∈ W.carrier,
      w.verticalTranslate epsilon_dir ∉ B.toFinset := by
    intro w hw hmem
    exact h_disjoint w hw (B.finite.mem_toFinset.mp hmem)
  have horigW : ∀ w ∈ W.carrier,
      orig (w.verticalTranslate epsilon_dir) = w := by
    intro w hw
    rw [show orig (w.verticalTranslate epsilon_dir) =
        (w.verticalTranslate epsilon_dir).verticalTranslate
          (-epsilon_dir) by
      simp [orig, hshift_not_B w hw]]
    rw [verticalTranslate_compose]
    have hsum : epsilon_dir + -epsilon_dir = 0 := by ring
    rw [hsum, verticalTranslate_zero_local]
  have horigB : ∀ b ∈ B.carrier, orig b = b := by
    intro b hb
    simp [orig, hB_mem b hb]
  have horig_mem : ∀ h ∈ F.carrier,
      orig h ∈ F_union.carrier := by
    intro h hh
    rcases hF_W h hh with ⟨w, hw, rfl⟩ | hb
    · rw [horigW w hw, hF_union]
      exact Or.inl hw
    · rw [horigB h hb, hF_union]
      exact Or.inr hb
  have horig_inj : ∀ f ∈ F.carrier, ∀ g ∈ F.carrier,
      orig f = orig g → f = g := by
    intro f hf g hg heq
    rcases hF_W f hf with ⟨w1, hw1, hfw1⟩ | hfB
    · rcases hF_W g hg with ⟨w2, hw2, hgw2⟩ | hgB
      · subst f
        subst g
        have hw : w1 = w2 := by
          calc
            w1 = orig (w1.verticalTranslate epsilon_dir) :=
              (horigW w1 hw1).symm
            _ = orig (w2.verticalTranslate epsilon_dir) := heq
            _ = w2 := horigW w2 hw2
        rw [hw]
      · subst f
        have hwg : w1 = g := by
          calc
            w1 = orig (w1.verticalTranslate epsilon_dir) :=
              (horigW w1 hw1).symm
            _ = orig g := heq
            _ = g := horigB g hgB
        exfalso
        exact h_W_B_disjoint w1 hw1 (by simpa [hwg] using hgB)
    · rcases hF_W g hg with ⟨w, hw, hgw⟩ | hgB
      · subst g
        have hfw : f = w := by
          calc
            f = orig f := (horigB f hfB).symm
            _ = orig (w.verticalTranslate epsilon_dir) := heq
            _ = w := horigW w hw
        exfalso
        exact h_W_B_disjoint w hw (by simpa [← hfw] using hfB)
      · calc
          f = orig f := (horigB f hfB).symm
          _ = orig g := heq
          _ = g := horigB g hgB
  have hcurve : ∀ h ∈ F.carrier,
      h.verticalTranslate (shift' h) =
        (orig h).verticalTranslate (shift (orig h)) := by
    intro h hh
    rcases hF_W h hh with ⟨w, hw, rfl⟩ | hb
    · rw [h_shift'_W w hw, horigW w hw, h_shift_W w hw]
      exact verticalTranslate_compose w epsilon_dir (shift0 w)
    · rw [horigB h hb, h_shift'_B h hb, h_shift_B h hb]
  exact
    no_tangencies_transfer_of_embedding
      orig horig_mem horig_inj hcurve h_no_tang

end Kakeya.Cinematic
