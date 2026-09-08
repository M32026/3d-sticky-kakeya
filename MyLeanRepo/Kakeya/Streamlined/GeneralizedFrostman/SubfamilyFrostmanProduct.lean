import MyLeanRepo.Kakeya.Streamlined.PlankFrostman.FromAuxiliaryScale.FrostmanPreservation
import MyLeanRepo.Kakeya.Streamlined.DividingScales.FrostmanContainerMonotonicity
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.DeterministicHelpers

/-!
# Subfamily Frostman-product bound

Restricting an equal-radius tube family may increase its relative Frostman
constant, but the loss cancels against the selected cardinality.  Changing
from the selected unit-size reference container to a larger ambient container
costs nothing when the selected family lies in both and the selected
container has no larger volume.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Streamlined.GeneralizedFrostman

lemma subfamily_frostman_product_bound
    {δ : ℝ} {G : TubeFamily δ} {H : BodyFamily}
    {embed : Fin H.card → Fin G.card}
    (hinj : Function.Injective embed)
    (hcarrier :
      ∀ i, (H.body i).carrier =
        (G.toBodyFamily.body (embed i)).carrier)
    {V U : Set Point3}
    (hδ : 0 < δ)
    (hV_convex : Convex ℝ V)
    (hU_convex : Convex ℝ U)
    (hG_in_V : ∀ i, (G.tube i).carrier ⊆ V)
    (hH_in_U : ∀ i, (H.body i).carrier ⊆ U)
    (hV_pos : 0 < volume V) (hV_top : volume V ≠ ⊤)
    (hU_pos : 0 < volume U) (hU_top : volume U ≠ ⊤)
    (hG_nonempty : G.Nonempty)
    (hvol_ratio : volume U ≤ volume V) :
    H.frostmanConstantIn U * H.enncard ≤
      G.toBodyFamily.frostmanConstantIn V * G.enncard := by
  classical
  by_cases hH_empty : H.card = 0
  · simp [BodyFamily.enncard, hH_empty]
  · let tv := Kakeya.deltaTubeVolume δ
    have hH_nonempty : 0 < H.card := Nat.pos_of_ne_zero hH_empty
    have htv_pos : 0 < tv :=
      RandomTranslation.deltaTubeVolume_pos hδ
    have htv_top : tv ≠ ⊤ :=
      RandomTranslation.deltaTubeVolume_ne_top
    have hG_card_zero : G.enncard ≠ 0 := by
      exact Nat.cast_ne_zero.mpr hG_nonempty.ne'
    have hG_card_top : G.enncard ≠ ⊤ :=
      ENNReal.natCast_ne_top G.card
    have hH_card_zero : H.enncard ≠ 0 := by
      exact Nat.cast_ne_zero.mpr hH_nonempty.ne'
    have hH_card_top : H.enncard ≠ ⊤ :=
      ENNReal.natCast_ne_top H.card
    have hG_volume : ∀ i,
        (G.toBodyFamily.body i).volume = tv := by
      intro i
      exact
        RandomTranslation.tube_volume_eq_deltaTubeVolume
          (G.tube i)
    have hH_volume : ∀ i, (H.body i).volume = tv := by
      intro i
      rw [show (H.body i).volume =
          (G.toBodyFamily.body (embed i)).volume by
        simp [Body.volume, hcarrier i]]
      exact hG_volume (embed i)
    have hG_mass :
        G.toBodyFamily.mass = G.enncard * tv := by
      calc
        G.toBodyFamily.mass
            = ∑ _i : Fin G.card, tv := by
          dsimp only [BodyFamily.mass]
          exact Finset.sum_congr rfl fun i _ => hG_volume i
        _ = (G.card : ENNReal) * tv := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            Fintype.card_fin]
        _ = G.enncard * tv := by rfl
    have hH_mass :
        H.mass = H.enncard * tv := by
      dsimp only [BodyFamily.mass]
      rw [Finset.sum_congr rfl fun i _ => hH_volume i]
      simp [BodyFamily.enncard, Finset.sum_const]
    have hG_mass_zero : G.toBodyFamily.mass ≠ 0 := by
      rw [hG_mass]
      exact mul_ne_zero hG_card_zero htv_pos.ne'
    have hG_mass_top : G.toBodyFamily.mass ≠ ⊤ := by
      rw [hG_mass]
      exact ENNReal.mul_ne_top hG_card_top htv_top
    have hH_mass_zero : H.mass ≠ 0 := by
      rw [hH_mass]
      exact mul_ne_zero hH_card_zero htv_pos.ne'
    have hH_mass_top : H.mass ≠ ⊤ := by
      rw [hH_mass]
      exact ENNReal.mul_ne_top hH_card_top htv_top
    have hH_in_V : ∀ i, (H.body i).carrier ⊆ V := by
      intro i
      rw [hcarrier i]
      exact hG_in_V (embed i)
    have hG_density_zero :
        G.toBodyFamily.density V ≠ 0 := by
      have hcontained :
          G.toBodyFamily.containedMass V =
            G.toBodyFamily.mass := by
        have hindices :
            G.toBodyFamily.containedIndices V = Finset.univ := by
          apply Finset.filter_true_of_mem
          intro i _
          exact hG_in_V i
        rw [BodyFamily.containedMass, hindices]
        rfl
      rw [BodyFamily.density, hcontained]
      exact ENNReal.div_ne_zero.mpr
        ⟨hG_mass_zero, hV_top⟩
    have hG_density_top :
        G.toBodyFamily.density V ≠ ⊤ := by
      have hcontained :
          G.toBodyFamily.containedMass V =
            G.toBodyFamily.mass := by
        have hindices :
            G.toBodyFamily.containedIndices V = Finset.univ := by
          apply Finset.filter_true_of_mem
          intro i _
          exact hG_in_V i
        rw [BodyFamily.containedMass, hindices]
        rfl
      rw [BodyFamily.density, hcontained]
      exact ENNReal.div_ne_top hG_mass_top hV_pos.ne'
    have hH_density_zero : H.density V ≠ 0 := by
      have hcontained : H.containedMass V = H.mass := by
        have hindices : H.containedIndices V = Finset.univ := by
          ext i
          simp [BodyFamily.mem_containedIndices_iff, hH_in_V i]
        rw [BodyFamily.containedMass, hindices]
        rfl
      rw [BodyFamily.density, hcontained]
      exact ENNReal.div_ne_zero.mpr
        ⟨hH_mass_zero, hV_top⟩
    have hH_density_top : H.density V ≠ ⊤ := by
      have hcontained : H.containedMass V = H.mass := by
        have hindices : H.containedIndices V = Finset.univ := by
          ext i
          simp [BodyFamily.mem_containedIndices_iff, hH_in_V i]
        rw [BodyFamily.containedMass, hindices]
        rfl
      rw [BodyFamily.density, hcontained]
      exact ENNReal.div_ne_top hH_mass_top hV_pos.ne'
    have hsub :
        H.frostmanConstantIn V ≤
          (G.toBodyFamily.mass / H.mass) *
            G.toBodyFamily.frostmanConstantIn V :=
      subfamily_frostman_upper_bound
        hinj hcarrier hG_in_V
        hG_density_zero hG_density_top
        hH_density_zero hH_density_top
        hH_mass_zero hH_mass_top
        hG_mass_zero hG_mass_top
    have hcontainer :
        H.frostmanConstantIn U ≤
          H.frostmanConstantIn V :=
      H.frostmanConstantIn_mono_of_all_contained
        hU_convex hV_convex hH_in_U hH_in_V hvol_ratio
        hU_pos.ne' hU_top hV_pos.ne' hV_top
        hH_mass_zero hH_mass_top
    calc
      H.frostmanConstantIn U * H.enncard
          ≤ H.frostmanConstantIn V * H.enncard := by
        gcongr
      _ ≤ ((G.toBodyFamily.mass / H.mass) *
            G.toBodyFamily.frostmanConstantIn V) *
          H.enncard := by
        gcongr
      _ = G.toBodyFamily.frostmanConstantIn V *
          G.enncard := by
        rw [hG_mass, hH_mass]
        rw [ENNReal.mul_div_mul_right
          G.enncard H.enncard htv_pos.ne' htv_top]
        have hcancel :
            G.enncard / H.enncard * H.enncard =
              G.enncard :=
          ENNReal.div_mul_cancel hH_card_zero hH_card_top
        calc
          (G.enncard / H.enncard *
              G.toBodyFamily.frostmanConstantIn V) *
              H.enncard
              = G.toBodyFamily.frostmanConstantIn V *
                  (G.enncard / H.enncard * H.enncard) := by
                ring
          _ = G.toBodyFamily.frostmanConstantIn V *
                G.enncard := by rw [hcancel]

/-- A finite-set specialization of `subfamily_frostman_product_bound`.

If `I ⊆ J` are index sets in one equal-radius tube family, the Frostman
constant-cardinality product of the smaller subfamily is bounded by that of
the larger subfamily, allowing the two families to use different common
containers with the displayed volume comparison. -/
lemma fromFinset_frostman_product_le_of_subset
    {δ : ℝ} {F : TubeFamily δ}
    {I J : Finset (Fin F.card)}
    (hIJ : I ⊆ J)
    {V U : Set Point3}
    (hδ : 0 < δ)
    (hV_convex : Convex ℝ V)
    (hU_convex : Convex ℝ U)
    (hJ_in_V : ∀ i : Fin (TubeSubfamily.fromFinset F J).family.card,
      ((TubeSubfamily.fromFinset F J).family.tube i).carrier ⊆ V)
    (hI_in_U : ∀ i : Fin (TubeSubfamily.fromFinset F I).family.card,
      ((TubeSubfamily.fromFinset F I).family.tube i).carrier ⊆ U)
    (hV_pos : 0 < volume V) (hV_top : volume V ≠ ⊤)
    (hU_pos : 0 < volume U) (hU_top : volume U ≠ ⊤)
    (hJ_nonempty : J.Nonempty)
    (hvol_ratio : volume U ≤ volume V) :
    (TubeSubfamily.fromFinset F I).family.toBodyFamily.frostmanConstantIn U *
          (I.card : ENNReal) ≤
      (TubeSubfamily.fromFinset F J).family.toBodyFamily.frostmanConstantIn V *
          (J.card : ENNReal) := by
  let large := TubeSubfamily.fromFinset F J
  let small := TubeSubfamily.fromFinset F I
  let inclusion := TubeSubfamily.fromFinsetInclusion F I J hIJ
  have hcarrier : ∀ i,
      (small.family.toBodyFamily.body i).carrier =
        (large.family.toBodyFamily.body (inclusion i)).carrier := by
    intro i
    change (small.family.tube i).carrier =
      (large.family.tube (inclusion i)).carrier
    rw [small.tube_eq, large.tube_eq]
    exact congrArg (fun tube => tube.carrier)
      (congrArg F.tube
        (TubeSubfamily.fromFinsetInclusion_ambient F I J hIJ i).symm)
  have hlargeNonempty : large.family.Nonempty := by
    change 0 < J.card
    exact Finset.card_pos.mpr hJ_nonempty
  have hmain := subfamily_frostman_product_bound
    (G := large.family) (H := small.family.toBodyFamily)
    (embed := inclusion) inclusion.injective hcarrier hδ
    hV_convex hU_convex hJ_in_V hI_in_U hV_pos hV_top hU_pos hU_top
    hlargeNonempty hvol_ratio
  change
    small.family.toBodyFamily.frostmanConstantIn U *
          small.family.toBodyFamily.enncard ≤
      large.family.toBodyFamily.frostmanConstantIn V *
          large.family.enncard
  exact hmain

end Kakeya.Streamlined.GeneralizedFrostman
