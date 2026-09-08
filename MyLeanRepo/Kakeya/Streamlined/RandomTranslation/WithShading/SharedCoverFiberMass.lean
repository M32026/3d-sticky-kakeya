import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.Multiscale
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.DeterministicHelpers

/-!
# Fiber mass identities for shared covers

If a translated-copy cover sends every pair `(j, i)` to the image of the
original parent of `i`, each shared fiber has exactly `J` times the original
cardinality and mass.
-/

noncomputable section

open MeasureTheory Kakeya.Streamlined Kakeya.Streamlined.RandomTranslation

namespace Kakeya.Streamlined.RandomTranslation.WithShading

variable {δ : ℝ} {F : TubeFamily δ} {J : ℕ} {shift : Fin J → Point3}

/-- For any cover of a `δ`-tube family, fiber mass is fiber count times the
common `δ`-tube volume. -/
lemma fiberMass_eq_fiberCount_mul_Vδ
    {δ ρ : ℝ} {fine : TubeFamily δ} {coarse : TubeFamily ρ}
    (P : TubeCover fine coarse) (j : Fin coarse.card) :
    P.toFactoring.fiberMass j =
      P.toFactoring.fiberCount j * Kakeya.deltaTubeVolume δ := by
  classical
  let Vδ := Kakeya.deltaTubeVolume δ
  have h_all : ∀ i ∈ P.toFactoring.fiberIndices j,
      (fine.toBodyFamily.body i).volume = Vδ := by
    intro i _
    change (fine.tube i).volume = Vδ
    exact tube_volume_eq_deltaTubeVolume (fine.tube i)
  calc
    P.toFactoring.fiberMass j
        = ∑ i ∈ P.toFactoring.fiberIndices j, Vδ := by
            apply Finset.sum_congr rfl
            intro i hi
            exact h_all i hi
    _ = ((P.toFactoring.fiberIndices j).card : ENNReal) * Vδ := by
          rw [Finset.sum_const]
          simp [nsmul_eq_mul]
    _ = P.toFactoring.fiberCount j * Kakeya.deltaTubeVolume δ := by rfl

/-- A shared parent map has `J` times the cardinality of the corresponding
original fiber. -/
lemma shared_parent_fiber_count
    {G_card H_card : ℕ}
    (parent_orig : Fin F.card → Fin G_card)
    (parent_shared : Fin (J * F.card) → Fin H_card)
    (f : Fin G_card → Fin H_card)
    (hf_inj : Function.Injective f)
    (h_parent : ∀ (j : Fin J) (i : Fin F.card),
      parent_shared (finProdFinEquiv (j, i)) = f (parent_orig i))
    (l : Fin G_card) :
    (Finset.univ.filter
        (fun k : Fin (J * F.card) => parent_shared k = f l)).card =
      J * (Finset.univ.filter
        (fun i : Fin F.card => parent_orig i = l)).card := by
  classical
  let e : (Fin J × Fin F.card) ≃ Fin (J * F.card) := finProdFinEquiv
  let S_orig :=
    Finset.univ.filter (fun i : Fin F.card => parent_orig i = l)
  let S_prod : Finset (Fin J × Fin F.card) := Finset.univ ×ˢ S_orig
  let S_shared :=
    Finset.univ.filter
      (fun k : Fin (J * F.card) => parent_shared k = f l)
  have h_image : Finset.image e S_prod = S_shared := by
    ext k
    constructor
    · intro hk
      rcases Finset.mem_image.mp hk with ⟨p, hp, rfl⟩
      have hp2 : parent_orig p.2 = l :=
        (Finset.mem_filter.mp (Finset.mem_product.mp hp).2).2
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (h_parent p.1 p.2).trans (congr_arg f hp2)⟩
    · intro hk
      have hk' : parent_shared k = f l := (Finset.mem_filter.mp hk).2
      let p := e.symm k
      have hep : e p = k := e.right_inv k
      have hp2 : parent_orig p.2 = l := by
        apply hf_inj
        rw [← h_parent p.1 p.2, hep]
        exact hk'
      have hp : p ∈ S_prod := by
        exact Finset.mem_product.mpr
          ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp2⟩⟩
      exact Finset.mem_image.mpr ⟨p, hp, hep⟩
  calc
    S_shared.card = (Finset.image e S_prod).card := congr_arg Finset.card h_image.symm
    _ = S_prod.card := Finset.card_image_of_injective _ e.injective
    _ = J * S_orig.card := by
      rw [Finset.card_product, Finset.card_univ]
      simp

/-- The corresponding shared fiber mass is `J` times the original mass. -/
lemma shared_parent_fiber_mass
    {ρ : ℝ} {G H : TubeFamily ρ}
    (P_orig : TubeCover F G)
    (P_shared : TubeCover (translatedCopies F J shift) H)
    (f : Fin G.card → Fin H.card)
    (hf_inj : Function.Injective f)
    (h_parent : ∀ (j : Fin J) (i : Fin F.card),
      P_shared.parent (finProdFinEquiv (j, i)) =
        f (P_orig.parent i))
    (l : Fin G.card) :
    P_shared.toFactoring.fiberMass (f l) =
      (J : ENNReal) * P_orig.toFactoring.fiberMass l := by
  have h_nat :=
    shared_parent_fiber_count P_orig.parent P_shared.parent
      f hf_inj h_parent l
  have h_count :
      P_shared.toFactoring.fiberCount (f l) =
        (J : ENNReal) * P_orig.toFactoring.fiberCount l := by
    change
      ((Finset.univ.filter
        (fun k => P_shared.parent k = f l)).card : ENNReal) =
      (J : ENNReal) *
        ((Finset.univ.filter
          (fun i => P_orig.parent i = l)).card : ENNReal)
    exact_mod_cast h_nat
  rw [fiberMass_eq_fiberCount_mul_Vδ P_shared (f l),
    fiberMass_eq_fiberCount_mul_Vδ P_orig l, h_count]
  ring

end Kakeya.Streamlined.RandomTranslation.WithShading

end
