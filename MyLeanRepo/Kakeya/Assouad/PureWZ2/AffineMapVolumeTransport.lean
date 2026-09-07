import MyLeanRepo.Kakeya.Streamlined.Families
import MyLeanRepo.Kakeya.Streamlined.VolumeHelpers
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12
import MyLeanRepo.Kakeya.Assouad.PropStickyStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2PaperStatements
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Affine-map volume and containedCount transport

Supporting lemmas for granite's TopCWA Lemma 1:
a BodyFamily ConvexWolff bound on affine-image bodies transfers back
to a TubeFamily ConvexWolff bound through the affine map.
-/

noncomputable section

open MeasureTheory Kakeya.Streamlined

namespace Kakeya.Assouad

variable (f : Point3 ≃ᵃ[ℝ] Point3)

/-- Volume of image under an affine equivalence scales by |det(linearPart)|. -/
theorem volume_affineEquiv_image (K : Set Point3) :
    volume (f '' K) =
    ENNReal.ofReal |LinearMap.det (f.linear : Point3 →ₗ[ℝ] Point3)| * volume K := by
  let p : Point3 := f 0
  let e : Point3 ≃ₗ[ℝ] Point3 := f.linear
  let eCLM : Point3 →L[ℝ] Point3 := e.toContinuousLinearEquiv.toContinuousLinearMap
  let g : Point3 → Point3 := fun x => x + p
  have h_decomp : ∀ x : Point3, f x = g (e x) := by
    intro x
    have h : f x = e x + p := by
      have h' := f.map_vadd (0 : Point3) x
      simpa using h'
    exact h
  have h_img : f '' K = g '' (e '' K) := by
    ext y
    simp only [Set.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h_eq : g (e x) = f x := (h_decomp x).symm
      exact ⟨e x, ⟨x, hx, rfl⟩, h_eq⟩
    · rintro ⟨z, ⟨x, hx, rfl⟩, hgz⟩
      have h_eq : f x = g (e x) := h_decomp x
      exact ⟨x, hx, by rw [h_eq]; exact hgz⟩
  rw [h_img]
  have h1 : MeasurePreserving g volume volume := measurePreserving_add_right volume p
  have h2 : MeasurePreserving (fun x => x - p) volume volume :=
    measurePreserving_add_right volume (-p)
  have hg_surj : Function.Surjective g := by
    intro y; refine ⟨y - p, ?_⟩; simp [g]
  have hg_inj : Function.Injective g := by
    intro a b h; simpa [g] using h
  have h_le1 : volume (g '' (e '' K)) ≤ volume (e '' K) := by
    have h : volume ((fun x => x - p) ⁻¹' (e '' K)) ≤ volume (e '' K) :=
      h2.measure_preimage_le (e '' K)
    have h' : (fun x : Point3 => x - p) ⁻¹' (e '' K) = g '' (e '' K) := by
      ext z
      simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · intro hz; exact ⟨z - p, hz, by simp [g]⟩
      · rintro ⟨w, hw, rfl⟩; simpa [g] using hw
    rw [h'] at h
    exact h
  have h_le2 : volume (e '' K) ≤ volume (g '' (e '' K)) := by
    have h : volume (g ⁻¹' (g '' (e '' K))) ≤ volume (g '' (e '' K)) :=
      h1.measure_preimage_le (g '' (e '' K))
    have h' : g ⁻¹' (g '' (e '' K)) = e '' K := by
      ext z
      simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · intro hz; rcases hz with ⟨w, hw, hgw⟩; have h_eq : z = w := hg_inj hgw.symm; rw [h_eq]; exact hw
      · intro hz; exact ⟨z, hz, rfl⟩
    rw [h'] at h
    exact h
  have h_trans : volume (g '' (e '' K)) = volume (e '' K) :=
    le_antisymm h_le1 h_le2
  rw [h_trans]
  have h_linear : volume (e '' K) =
      ENNReal.ofReal |LinearMap.det (e : Point3 →ₗ[ℝ] Point3)| * volume K :=
    MeasureTheory.Measure.addHaar_image_continuousLinearEquiv
      volume e.toContinuousLinearEquiv K
  exact h_linear

/-- Convexity is preserved under preimage by an affine equivalence. -/
theorem convex_preimage_affineEquiv {K : Set Point3} (hK : Convex ℝ K) :
    Convex ℝ (f ⁻¹' K) :=
  hK.affine_preimage f.toAffineMap

/-- Convexity is preserved under image by an affine equivalence. -/
theorem convex_image_affineEquiv {K : Set Point3} (hK : Convex ℝ K) :
    Convex ℝ (f '' K) :=
  hK.affine_image f.toAffineMap

/-- If body carriers are affine images of source carriers, then
`containedCount` at `f '' K` equals source `containedCount` at `K`. -/
theorem containedCount_affineImage
    {F G : BodyFamily}
    (hcard : F.card = G.card)
    (hcarrier : ∀ i : Fin F.card,
      (F.body i).carrier = f '' (G.body (Fin.castOrderIso hcard i)).carrier)
    (K : Set Point3) :
    F.containedCount (f '' K) = G.containedCount K := by
  let eqv : Fin F.card ≃ Fin G.card := (Fin.castOrderIso hcard).toEquiv
  have h_inj : Function.Injective f := f.injective
  have h_iff : ∀ (i : Fin F.card),
      (F.body i).carrier ⊆ f '' K ↔
      (G.body (eqv i)).carrier ⊆ K := by
    intro i
    rw [hcarrier i]
    constructor
    · intro h z hz
      have h5 : f z ∈ f '' (G.body (eqv i)).carrier := ⟨z, hz, rfl⟩
      have h6 : f z ∈ f '' K := h h5
      rcases h6 with ⟨w, hw, hfw⟩
      have h7 : z = w := h_inj hfw.symm
      rw [h7]; exact hw
    · intro h y hy
      rcases hy with ⟨z, hz, rfl⟩
      exact ⟨z, h hz, rfl⟩
  have h_indices : F.containedIndices (f '' K) =
      Finset.image eqv.symm (G.containedIndices K) := by
    ext i
    simp only [BodyFamily.mem_containedIndices_iff, Finset.mem_image]
    constructor
    · intro hi
      refine ⟨eqv i, ?_, by simp [eqv]⟩
      exact (h_iff i).mp hi
    · rintro ⟨j, hj, h_eq⟩
      have h9 : eqv.symm j = i := by simpa [eqv] using h_eq
      have h10 := (h_iff (eqv.symm j)).mpr hj
      rw [h9] at h10
      exact h10
  rw [BodyFamily.containedCount, h_indices]
  rw [Finset.card_image_of_injective _ eqv.symm.injective]
  ; rfl

/-- Transfer a ConvexWolff bound from an affine-image BodyFamily back
to the source BodyFamily, with the constant scaled by |det(linearPart)|. -/
theorem convexWolffBody_transfer_back
    {F G : BodyFamily} {C : ENNReal}
    (hcard : F.card = G.card)
    (hcarrier : ∀ i : Fin F.card,
      (F.body i).carrier = f '' (G.body (Fin.castOrderIso hcard i)).carrier)
    (hF : WZ2PaperBodyConvexWolffBound F C) :
    WZ2PaperBodyConvexWolffBound G
      (C * ENNReal.ofReal |LinearMap.det (f.linear : Point3 →ₗ[ℝ] Point3)|) := by
  let detFactor : ENNReal := ENNReal.ofReal |LinearMap.det (f.linear : Point3 →ₗ[ℝ] Point3)|
  intro convexSet hconv
  have h_img_conv : Convex ℝ (f '' convexSet) :=
    convex_image_affineEquiv f hconv
  have h_vol : volume (f '' convexSet) = detFactor * volume convexSet :=
    volume_affineEquiv_image f convexSet
  have h_count : F.containedCount (f '' convexSet) = G.containedCount convexSet :=
    containedCount_affineImage f hcard hcarrier convexSet
  have h_card : F.enncard = G.enncard := by
    simp [BodyFamily.enncard, hcard]
  have h_bound := hF (f '' convexSet) h_img_conv
  rw [h_count] at h_bound
  rw [h_vol, h_card] at h_bound
  have h_main : G.containedCount convexSet ≤
      (C * detFactor) * volume convexSet * G.enncard := by
    calc G.containedCount convexSet
      ≤ C * (detFactor * volume convexSet) * G.enncard := h_bound
    _ = (C * detFactor) * volume convexSet * G.enncard := by ring
  exact h_main

/-- Transfer a ConvexWolff bound from an affine-image BodyFamily back
to a TubeFamily, with the constant scaled by |det(linearPart)|. -/
theorem convexWolffTube_transfer_back
    {delta : ℝ} {tubeFamily : Kakeya.Streamlined.TubeFamily delta}
    {F : BodyFamily} {C : ENNReal}
    (hcard : F.card = tubeFamily.card)
    (hcarrier : ∀ i : Fin F.card,
      (F.body i).carrier =
        f '' (((wz1PaperBodyFamily tubeFamily).body (Fin.castOrderIso hcard i)).carrier))
    (hF : WZ2PaperBodyConvexWolffBound F C) :
    WZ2PaperConvexWolffBound tubeFamily
      (C * ENNReal.ofReal |LinearMap.det (f.linear : Point3 →ₗ[ℝ] Point3)|) := by
  let G : BodyFamily := wz1PaperBodyFamily tubeFamily
  have h_main : WZ2PaperBodyConvexWolffBound G _ :=
    convexWolffBody_transfer_back f hcard hcarrier hF
  intro convexSet hconv
  have h := h_main convexSet hconv
  have h_card : G.enncard = tubeFamily.enncard := by
    dsimp only [G, BodyFamily.enncard, TubeFamily.enncard]
    ; rfl
  rw [h_card] at h
  exact h

end Kakeya.Assouad

end
