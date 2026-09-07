import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12RescalingJacobian
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.TubeVolume

/-!
# Pure CWA to cardinality lower bound

Converts a pure Definition 2.12 CWA predicate into a direct cardinality lower
bound on the tube family.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- The inverse Jacobian of the Assouad normalization map is at most `4 / rho^2`. -/
theorem assouadNormalization_inverseJacobian
    {rho : ℝ}
    {parent : Kakeya.DeltaTube rho}
    (normalization : WZ2PaperAssouadUnitRescalingData parent)
    (hrho : 0 < rho)
    (targetSet : Set Point3) :
    volume (normalization.map '' targetSet) ≤
      ((4 : ENNReal) / ENNReal.ofReal (rho ^ 2)) * volume targetSet := by
  let convexBody := normalization.parent_convex_body
  let johnEquiv : Point3 ≃ₗ[ℝ] Point3 := convexBody.outerJohnEllipsoidMap
  let johnMap : Point3 →ₗ[ℝ] Point3 := johnEquiv
  have hdet_lower : rho ^ 2 / 4 ≤ |LinearMap.det johnMap| :=
    wz2Paper_outerJohn_abs_det_lower parent hrho
  have hdet_pos : 0 < |LinearMap.det johnMap| := by
    have hpos : 0 < rho ^ 2 / 4 := by positivity
    exact hpos.trans_le hdet_lower
  let normLinear : Point3 ≃ₗ[ℝ] Point3 := normalization.map.linear
  have h_eq : normLinear = johnEquiv.symm := by rfl
  have hcomp : (normLinear : Point3 →ₗ[ℝ] Point3).comp johnMap = .id := by
    rw [h_eq]
    exact johnEquiv.symm_comp
  have hdet_comp : LinearMap.det ((normLinear : Point3 →ₗ[ℝ] Point3).comp johnMap) = 1 := by
    rw [hcomp]
    simp
  have hdet_product : LinearMap.det (normLinear : Point3 →ₗ[ℝ] Point3) * LinearMap.det johnMap = 1 := by
    have h2 : LinearMap.det ((normLinear : Point3 →ₗ[ℝ] Point3).comp johnMap) =
        LinearMap.det (normLinear : Point3 →ₗ[ℝ] Point3) * LinearMap.det johnMap :=
      LinearMap.det_comp ..
    rw [h2] at hdet_comp
    exact hdet_comp
  have hdet_inv : |LinearMap.det (normLinear : Point3 →ₗ[ℝ] Point3)| =
      1 / |LinearMap.det johnMap| := by
    have h3 : |LinearMap.det (normLinear : Point3 →ₗ[ℝ] Point3) * LinearMap.det johnMap| = 1 := by
      rw [hdet_product] <;> norm_num
    have h4 : |LinearMap.det (normLinear : Point3 →ₗ[ℝ] Point3) * LinearMap.det johnMap| =
        |LinearMap.det (normLinear : Point3 →ₗ[ℝ] Point3)| * |LinearMap.det johnMap| := by
      rw [abs_mul]
    rw [h4] at h3
    field_simp [hdet_pos.ne'] at h3 ⊢ <;> linarith
  have hdet_upper : |LinearMap.det (normLinear : Point3 →ₗ[ℝ] Point3)| ≤ 4 / rho ^ 2 := by
    rw [hdet_inv]
    have h : 1 / |LinearMap.det johnMap| ≤ 1 / (rho ^ 2 / 4) := by gcongr
    have h2 : 1 / (rho ^ 2 / 4) = 4 / rho ^ 2 := by
      field_simp [hrho.ne']
    rw [h2] at h
    exact h
  have hvol : volume (normalization.map '' targetSet) =
      ENNReal.ofReal |LinearMap.det (normLinear : Point3 →ₗ[ℝ] Point3)| * volume targetSet := by
    exact wz2PaperAffineEquiv_volume_image_eq normalization.map targetSet
  rw [hvol]
  have hdiv : ENNReal.ofReal (4 / rho ^ 2) = (4 : ENNReal) / ENNReal.ofReal (rho ^ 2) := by
    have hpos : 0 < rho ^ 2 := by positivity
    have h1 : (4 / rho ^ 2 : ℝ) = 4 * (rho ^ 2)⁻¹ := by
      field_simp [hpos.ne']
    rw [h1]
    have h2 : ENNReal.ofReal (4 * (rho ^ 2)⁻¹) =
        ENNReal.ofReal (4 : ℝ) * ENNReal.ofReal ((rho ^ 2)⁻¹) := by
      rw [ENNReal.ofReal_mul] <;> positivity
    rw [h2]
    have h3 : ENNReal.ofReal ((rho ^ 2)⁻¹) = (ENNReal.ofReal (rho ^ 2))⁻¹ := by
      rw [ENNReal.ofReal_inv_of_pos hpos]
    rw [h3]
    simp [div_eq_mul_inv]
  have h6 : ENNReal.ofReal |LinearMap.det (normLinear : Point3 →ₗ[ℝ] Point3)| ≤
      (4 : ENNReal) / ENNReal.ofReal (rho ^ 2) := by
    have h8 : |LinearMap.det (normLinear : Point3 →ₗ[ℝ] Point3)| ≤ 4 / rho ^ 2 := hdet_upper
    have h9 : ENNReal.ofReal |LinearMap.det (normLinear : Point3 →ₗ[ℝ] Point3)| ≤
        ENNReal.ofReal (4 / rho ^ 2) := ENNReal.ofReal_le_ofReal h8
    rw [hdiv] at h9
    exact h9
  gcongr

/--
Pure CWA at nearby scales implies a cardinality lower bound on the family.
-/
theorem pure_cwa_to_cardinality_floor
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    (hcwa : WZ2PaperPureCWAAtNearbyScales family C)
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hnonempty : family.Nonempty) :
    1 ≤ (4 : ENNReal) * C * Kakeya.deltaTubeVolume delta * family.enncard := by
  let rho₀ : WZ2PaperRequestedScale delta := ⟨1, by linarith, by norm_num⟩
  rcases hcwa.2.2.2 rho₀ with ⟨nearbyData⟩
  let rho := nearbyData.rho
  let scaleData := nearbyData.scaleData
  have hrho_pos : 0 < rho := scaleData.rho_pos
  have hrho_ge_one : (1 : ℝ) ≤ rho := nearbyData.requested_le

  let invJac := (4 : ENNReal) / ENNReal.ofReal (rho ^ 2)
  let C' := invJac * C

  have h_rho2_ge_one : ENNReal.ofReal (rho ^ 2) ≥ 1 := by
    have h2 : rho ^ 2 ≥ 1 := by nlinarith
    have h3 : ENNReal.ofReal (rho ^ 2) ≥ ENNReal.ofReal (1 : ℝ) :=
      ENNReal.ofReal_le_ofReal h2
    simpa using h3
  have h_rho2_pos : 0 < rho ^ 2 := by positivity
  have h_invJac_ne_zero : ENNReal.ofReal (rho ^ 2) ≠ 0 := by
    simpa [ENNReal.ofReal_eq_zero] using h_rho2_pos.ne'
  have h_invJac_le : invJac ≤ 4 := by
    dsimp only [invJac]
    have h4 : (4 : ENNReal) ≤ 4 * ENNReal.ofReal (rho ^ 2) := by
      have h5 : (1 : ENNReal) ≤ ENNReal.ofReal (rho ^ 2) := h_rho2_ge_one
      calc
        (4 : ENNReal) = 4 * (1 : ENNReal) := by simp
        _ ≤ 4 * ENNReal.ofReal (rho ^ 2) := by gcongr
    have h6 : invJac ≤ 4 := by
      rw [ENNReal.div_le_iff h_invJac_ne_zero (by simp)]
      exact h4
    exact h6
  have hC'_le : C' ≤ (4 : ENNReal) * C := by
    dsimp only [C']
    calc
      invJac * C ≤ (4 : ENNReal) * C := by gcongr
      _ = (4 : ENNReal) * C := by rfl

  let fiberIndices := fun parent : Fin scaleData.coarse.card =>
    wz2PaperOrdinaryFullFiberIndices family scaleData.coarse parent

  have hcover : ∀ source : Fin family.card,
      ∃ parent : Fin scaleData.coarse.card, source ∈ fiberIndices parent :=
    scaleData.cover.covers

  have hfull_subset_doubled : ∀ parent,
      fiberIndices parent ⊆
        wz2PaperOrdinaryDilatedFiberIndices 2 family scaleData.coarse parent := by
    intro parent source hsource
    exact WZ2PaperPurePartitioningCover.mem_doubledFiber_of_mem_fullFiber
      hrho_pos.le hsource

  have hdisjoint : ∀ (first second : Fin scaleData.coarse.card), first ≠ second →
      Disjoint (fiberIndices first) (fiberIndices second) := by
    intro first second hne
    have h1 := scaleData.cover.doubled_fibers_disjoint first second hne
    exact Disjoint.mono (hfull_subset_doubled first) (hfull_subset_doubled second) h1

  have hunion : Finset.biUnion Finset.univ fiberIndices = (Finset.univ : Finset (Fin family.card)) := by
    apply Finset.eq_univ_of_forall
    intro source
    rcases hcover source with ⟨parent, hparent⟩
    exact Finset.mem_biUnion.mpr ⟨parent, Finset.mem_univ parent, hparent⟩

  -- Per-fiber bound
  have hfiber_bound : ∀ (parent : Fin scaleData.coarse.card) (K : Set Point3),
      Convex ℝ K →
        ((fiberIndices parent).filter (fun i => (family.tube i).carrier ⊆ K)).card
          ≤ C' * volume K * (fiberIndices parent).card := by
    intro parent K hK
    rcases scaleData.rescaledFiber parent with ⟨fiberData⟩
    let normalization := fiberData.normalization
    let rescaledFamily :=
      wz2PaperPureUnitRescaledFullFiberBodyFamily
        (fine := family) (coarse := scaleData.coarse) parent normalization
    set K' := normalization.map '' K with hK'_def
    have hK'_convex : Convex ℝ K' := by
      rw [hK'_def]
      exact hK.affine_image (normalization.map : Point3 →ᵃ[ℝ] Point3)
    have h_main_bound : rescaledFamily.containedCount K' ≤ C * volume K' * rescaledFamily.enncard :=
      fiberData.convex_wolff K' hK'_convex

    let idxEquiv := wz2PaperOrdinaryFullFiberIndexEquiv (fine := family) (coarse := scaleData.coarse) parent
    have h_inj_map : Function.Injective normalization.map := normalization.map.injective
    let f : Fin rescaledFamily.card → Fin family.card := fun target => (idxEquiv target).val
    have h_iff : ∀ (target : Fin rescaledFamily.card),
        (rescaledFamily.body target).carrier ⊆ K' ↔
          (family.tube (f target)).carrier ⊆ K := by
      intro target
      let originalCarrier := (family.tube (f target)).carrier
      have h_body : (rescaledFamily.body target).carrier = normalization.map '' originalCarrier := by rfl
      rw [h_body, hK'_def]
      constructor
      · intro h
        exact (Set.image_subset_image_iff h_inj_map).mp h
      · intro h
        have h' : normalization.map '' originalCarrier ⊆ normalization.map '' K := by gcongr
        exact h'
    let rescaledContained := rescaledFamily.containedIndices K'
    let originalFiltered := (fiberIndices parent).filter (fun i => (family.tube i).carrier ⊆ K)
    have h_inj_f : Set.InjOn f rescaledContained := by
      intro a _ b _ h
      have h' : (idxEquiv a).val = (idxEquiv b).val := h
      have h'' : idxEquiv a = idxEquiv b := by
        apply Subtype.ext
        exact h'
      exact idxEquiv.injective h''
    let rescaledImage : Finset (Fin family.card) := Finset.image f rescaledContained
    have h_image : rescaledImage = originalFiltered := by
      ext source
      simp only [rescaledImage, Finset.mem_image]
      constructor
      · rintro ⟨target, htarget, rfl⟩
        have h' : (rescaledFamily.body target).carrier ⊆ K' := by
          have h_filter : target ∈ Finset.univ.filter (fun i => (rescaledFamily.body i).carrier ⊆ K') := htarget
          exact (Finset.mem_filter.mp h_filter).2
        have h'' : (family.tube (f target)).carrier ⊆ K := (h_iff target).mp h'
        have h_f_in : f target ∈ fiberIndices parent := (idxEquiv target).property
        have h_goal : f target ∈ originalFiltered := by
          rw [show originalFiltered = (fiberIndices parent).filter _ from rfl]
          rw [Finset.mem_filter]
          exact ⟨h_f_in, h''⟩
        exact h_goal
      · intro hsource
        have h_in_fiber : source ∈ fiberIndices parent := by
          have h : source ∈ originalFiltered := hsource
          rw [show originalFiltered = (fiberIndices parent).filter _ from rfl] at h
          exact (Finset.mem_filter.mp h).1
        have h_carrier : (family.tube source).carrier ⊆ K := by
          have h : source ∈ originalFiltered := hsource
          rw [show originalFiltered = (fiberIndices parent).filter _ from rfl] at h
          exact (Finset.mem_filter.mp h).2
        let target : Fin rescaledFamily.card := idxEquiv.symm ⟨source, h_in_fiber⟩
        have h_f_eq : f target = source := by
          dsimp only [f, target]
          rw [Equiv.apply_symm_apply]
          <;> rfl
        have h_target_carrier : (family.tube (f target)).carrier ⊆ K := by
          rw [h_f_eq]
          exact h_carrier
        have h_target_in : target ∈ rescaledContained := by
          have h_body : (rescaledFamily.body target).carrier ⊆ K' := (h_iff target).mpr h_target_carrier
          have h_filter : target ∈ Finset.univ.filter (fun i => (rescaledFamily.body i).carrier ⊆ K') := by
            rw [Finset.mem_filter]
            exact ⟨Finset.mem_univ target, h_body⟩
          exact h_filter
        exact ⟨target, h_target_in, h_f_eq⟩
    have h_card_eq : rescaledContained.card = originalFiltered.card := by
      have h1 : rescaledImage.card = rescaledContained.card :=
        Finset.card_image_of_injOn h_inj_f
      have h2 : rescaledImage.card = originalFiltered.card := by
        rw [h_image]
      rw [← h1, h2]
    have h_vol : volume K' ≤ invJac * volume K :=
      assouadNormalization_inverseJacobian normalization hrho_pos K
    have h_enncard_eq : rescaledFamily.enncard = (fiberIndices parent).card := by
      simp [rescaledFamily, Kakeya.Streamlined.BodyFamily.enncard]
      <;> rfl
    calc
      (originalFiltered.card : ENNReal)
        = (rescaledContained.card : ENNReal) := by exact_mod_cast h_card_eq.symm
      _ = rescaledFamily.containedCount K' := by rfl
      _ ≤ C * volume K' * rescaledFamily.enncard := h_main_bound
      _ ≤ C * (invJac * volume K) * rescaledFamily.enncard := by gcongr
      _ = invJac * C * volume K * rescaledFamily.enncard := by ring
      _ = C' * volume K * (fiberIndices parent).card := by
        rw [h_enncard_eq] <;> rfl

  -- Top-level bound: for any convex K, count of tubes whose carrier ⊆ K ≤ C' * vol(K) * N
  have htop : ∀ (K : Set Point3), Convex ℝ K →
      ((Finset.univ.filter (fun i => (family.tube i).carrier ⊆ K)).card : ENNReal) ≤
        C' * volume K * family.enncard := by
    intro K hK
    let P : Fin family.card → Prop := fun i => (family.tube i).carrier ⊆ K
    let contained := Finset.univ.filter P
    let fiberContained := fun parent : Fin scaleData.coarse.card =>
      fiberIndices parent ∩ contained
    have h2 : contained = Finset.biUnion Finset.univ fiberContained := by
      apply Finset.ext
      intro x
      have h_iff : x ∈ Finset.biUnion Finset.univ fiberContained ↔
          ∃ (parent : Fin scaleData.coarse.card), x ∈ fiberIndices parent ∧ x ∈ contained := by
        simp [Finset.mem_biUnion, fiberContained]
        <;> tauto
      rw [h_iff]
      constructor
      · intro hx
        rcases hcover x with ⟨parent, hparent⟩
        exact ⟨parent, hparent, hx⟩
      · rintro ⟨parent, _, hx⟩
        exact hx
    have h3 : Set.Pairwise (Finset.univ : Finset (Fin scaleData.coarse.card))
        (fun first second => Disjoint (fiberContained first) (fiberContained second)) := by
      intro first _ second _ hne
      have hsub1 : fiberContained first ⊆ fiberIndices first := Finset.inter_subset_left
      have hsub2 : fiberContained second ⊆ fiberIndices second := Finset.inter_subset_left
      exact Disjoint.mono hsub1 hsub2 (hdisjoint first second hne)
    have h4 : contained.card = ∑ parent : Fin scaleData.coarse.card, (fiberContained parent).card := by
      rw [h2, Finset.card_biUnion h3]
    have h5 : ∀ parent : Fin scaleData.coarse.card,
        ((fiberContained parent).card : ENNReal) ≤
          C' * volume K * (fiberIndices parent).card := by
      intro parent
      have h6 : fiberContained parent = (fiberIndices parent).filter P := by
        ext x
        simp only [fiberContained, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨h1, h2⟩
          have hP : P x := by simpa [contained] using h2
          exact ⟨h1, hP⟩
        · rintro ⟨h1, hP⟩
          have h2 : x ∈ contained := by simp [contained, hP]
          exact ⟨h1, h2⟩
      rw [h6]
      exact_mod_cast hfiber_bound parent K hK
    have h_sum1 : (contained.card : ENNReal) =
        ∑ parent : Fin scaleData.coarse.card, ((fiberContained parent).card : ENNReal) := by
      exact_mod_cast h4
    have h_sum2 : ∑ parent : Fin scaleData.coarse.card, ((fiberContained parent).card : ENNReal) ≤
        ∑ parent : Fin scaleData.coarse.card, C' * volume K * (fiberIndices parent).card := by
      apply Finset.sum_le_sum
      intro i _
      exact h5 i
    have h_sum3 : ∑ parent : Fin scaleData.coarse.card, C' * volume K * (fiberIndices parent).card =
        C' * volume K * ∑ parent : Fin scaleData.coarse.card, ((fiberIndices parent).card : ENNReal) := by
      let a : ENNReal := C' * volume K
      let f : Fin scaleData.coarse.card → ENNReal := fun i => (fiberIndices i).card
      have h : ∑ i ∈ Finset.univ, a * f i = a * ∑ i ∈ Finset.univ, f i := by
        exact Eq.symm (Finset.mul_sum Finset.univ f a)
      exact h
    have h_sum4 : ∑ parent : Fin scaleData.coarse.card, ((fiberIndices parent).card : ENNReal) = family.enncard := by
      have h71 : ∑ parent, (fiberIndices parent).card = (Finset.biUnion Finset.univ fiberIndices).card := by
        rw [Finset.card_biUnion]
        <;> intro first _ second _ hne
        <;> exact hdisjoint first second hne
      have h72 : (↑(∑ parent, (fiberIndices parent).card) : ENNReal) =
          ∑ parent, ((fiberIndices parent).card : ENNReal) := by
        rw [Nat.cast_sum]
      rw [← h72, h71, hunion]
      simp [Kakeya.Streamlined.TubeFamily.enncard]
    calc
      (contained.card : ENNReal)
        = ∑ parent, ((fiberContained parent).card : ENNReal) := h_sum1
      _ ≤ ∑ parent, C' * volume K * (fiberIndices parent).card := h_sum2
      _ = C' * volume K * ∑ parent, ((fiberIndices parent).card : ENNReal) := h_sum3
      _ = C' * volume K * family.enncard := by rw [h_sum4]

  -- Pick one tube and apply the bound to its own carrier
  have h_card_pos : 0 < family.card := hnonempty
  let idx : Fin family.card := ⟨0, h_card_pos⟩
  let carrier := (family.tube idx).carrier
  have hcarrier_convex : Convex ℝ carrier := wz2_paper_ordinary_tube_carrier_convex (family.tube idx)
  have h_self : idx ∈ Finset.univ.filter (fun i => (family.tube i).carrier ⊆ carrier) := by
    simp [carrier]
  have h_count : (1 : ENNReal) ≤
      ((Finset.univ.filter (fun i => (family.tube i).carrier ⊆ carrier)).card : ENNReal) := by
    have h : 1 ≤ (Finset.univ.filter (fun i => (family.tube i).carrier ⊆ carrier)).card :=
      Finset.one_le_card.mpr ⟨idx, h_self⟩
    exact_mod_cast h
  have h_bound := htop carrier hcarrier_convex
  have h_main : (1 : ENNReal) ≤ C' * volume carrier * family.enncard := by
    calc
      (1 : ENNReal) ≤ _ := h_count
      _ ≤ C' * volume carrier * family.enncard := h_bound

  let e0 : Point3 := EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
  let T_canon : Kakeya.DeltaTube delta :=
    { base := 0
      direction := e0
      direction_unit := by simp [e0] <;> norm_num }
  have h_vol_eq : volume carrier = Kakeya.deltaTubeVolume delta := by
    have h1 : volume carrier = (family.tube idx).volume := by
      simp [carrier, Kakeya.DeltaTube.volume] <;> rfl
    have h2 : (family.tube idx).volume = T_canon.volume :=
      Kakeya.Streamlined.tube_volume_eq (family.tube idx) T_canon
    have h3 : T_canon.volume = Kakeya.deltaTubeVolume delta := by
      simp [Kakeya.DeltaTube.volume] <;> rfl
    rw [h1, h2, h3]

  have h_final : (1 : ENNReal) ≤ (4 : ENNReal) * C * Kakeya.deltaTubeVolume delta * family.enncard := by
    calc
      (1 : ENNReal) ≤ C' * volume carrier * family.enncard := h_main
      _ = C' * Kakeya.deltaTubeVolume delta * family.enncard := by rw [h_vol_eq]
      _ ≤ (4 : ENNReal) * C * Kakeya.deltaTubeVolume delta * family.enncard := by
        gcongr
        <;> exact hC'_le
  exact h_final

end Kakeya.Assouad

end
