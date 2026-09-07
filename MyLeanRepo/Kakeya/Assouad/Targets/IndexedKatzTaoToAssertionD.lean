import MyLeanRepo.Kakeya.Assouad.Subunit.Statements
import MyLeanRepo.Kakeya.Assouad.TubeVolumeScaling
import MyLeanRepo.Kakeya.Assouad.TubeVolumeLowerBound

/-!
Deterministic model-conversion leaf for the subunit admissible ceiling.

Starting from an indexed, essentially-distinct Katz--Tao subfamily with dense
restricted shading and near-critical cardinality, construct the finite-set
family and shading consumed by `Kakeya.AssertionD`.  The Frostman slab bound
must be derived from the Katz--Tao count and the cardinality lower bound.

This target contains no probabilistic argument and must not use
`StickyKakeyaHypothesis` or WZ2 Theorem 5.2.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Local ENNReal rpow additive law. -/
private lemma realRpowENN_add' {x : ℝ} (hx : 0 < x) (a b : ℝ) :
    Kakeya.realRpowENN x (a + b) =
      Kakeya.realRpowENN x a * Kakeya.realRpowENN x b := by
  have h : Real.rpow x (a + b) = Real.rpow x a * Real.rpow x b :=
    Real.rpow_add hx a b
  simp only [Kakeya.realRpowENN, h]
  exact ENNReal.ofReal_mul (Real.rpow_nonneg hx.le a)

/-- From `a * b⁻¹ ≤ c` with `0 < c < ⊤`, deduce `a ≤ c * b`. -/
private lemma ennreal_of_le_div {a b c : ENNReal}
    (hc_ne_top : c ≠ ⊤) (hc_pos : 0 < c)
    (h : a * b⁻¹ ≤ c) : a ≤ c * b := by
  by_cases hb : b = 0
  · have ha : a = 0 := by
      rw [hb] at h
      by_contra ha'
      have h_ne_zero : a ≠ 0 := ha'
      have h0inv : (0 : ENNReal)⁻¹ = ⊤ := by simp
      have h3 : a * (0 : ENNReal)⁻¹ = ⊤ := by
        rw [h0inv]
        exact ENNReal.mul_top h_ne_zero
      rw [h3] at h
      have h4 : c = ⊤ := by simpa [top_le_iff] using h
      exact hc_ne_top h4
    rw [ha] <;> simp
  · by_cases hbt : b = ⊤
    · rw [hbt]
      have h : c * ⊤ = ⊤ := ENNReal.mul_top hc_pos.ne'
      rw [h] <;> exact le_top
    · have h4 : b⁻¹ * b = 1 := ENNReal.inv_mul_cancel hb hbt
      have h3 : a * b⁻¹ * b ≤ c * b := by gcongr
      have h5 : a * b⁻¹ * b = a := by
        rw [mul_assoc, h4, mul_one]
      rw [h5] at h3
      exact h3

theorem indexed_katz_tao_to_assertionD :
    IndexedKatzTaoToAssertionDStatement := by
  intro requestedCardLoss coreCardLoss ktEta assertionEta
    hreq hcore hle hkt_pos hassert_pos hstrict
  refine ⟨1, by norm_num, by norm_num, ?_⟩
  intro delta hdelta hdelta1 F Y S
    hnonempty hunit hdistinct hdense hkt hcard

  let f : Fin S.family.card → Kakeya.DeltaTube delta :=
    fun i => S.family.tube i

  classical

  have hF_card : F.card = F.toBodyFamily.card := by
    simp [Kakeya.Streamlined.TubeFamily.toBodyFamily]
  have hS_card : S.family.card = S.family.toBodyFamily.card := by
    simp [Kakeya.Streamlined.TubeFamily.toBodyFamily]

  -- Step 1: f is injective
  have hf_inj : Function.Injective f := by
    intro i j h
    by_contra hne
    set T := S.family.tube i with hT_def
    have h_j : S.family.tube j = T := by
      simpa [f] using h.symm
    have h_ed_raw := hdistinct i j hne
    have h_ed : T.EssentiallyDistinct T := by
      have h1 : S.family.tube i = T := rfl
      rw [h1, h_j] at h_ed_raw
      exact h_ed_raw
    have hvol_pos : 0 < T.volume := by
      have h_eq : T.volume = Kakeya.deltaTubeVolume delta :=
        tube_volume_scaling.1 delta T
      rw [h_eq]
      exact (tube_volume_scaling.2.1 delta hdelta hdelta1).1
    have hvol_top : T.volume ≠ ⊤ := by
      have h_eq : T.volume = Kakeya.deltaTubeVolume delta :=
        tube_volume_scaling.1 delta T
      rw [h_eq]
      exact (tube_volume_scaling.2.1 delta hdelta hdelta1).2
    have h_contra : T.volume ≤ (2 : ENNReal)⁻¹ * T.volume := by
      have h_ed' : MeasureTheory.volume (T.carrier ∩ T.carrier) ≤
            (2 : ENNReal)⁻¹ * max T.volume T.volume := h_ed
      have h_inter : T.carrier ∩ T.carrier = T.carrier := by simp
      rw [h_inter] at h_ed'
      have hmax : max T.volume T.volume = T.volume := max_self T.volume
      rw [hmax] at h_ed'
      exact h_ed'
    let r := T.volume.toReal
    have hr_pos : 0 < r := ENNReal.toReal_pos hvol_pos.ne' hvol_top
    have h_eq : T.volume = ENNReal.ofReal r := by
      rw [ENNReal.ofReal_toReal hvol_top]
    have h_inv : (2 : ENNReal)⁻¹ = ENNReal.ofReal (1 / 2 : ℝ) := by simp
    have h13 : (2 : ENNReal)⁻¹ * T.volume =
        ENNReal.ofReal ((1 / 2 : ℝ) * r) := by
      rw [h_inv, h_eq]
      rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ (1 / 2 : ℝ) by norm_num)]
    have h14 : (1 / 2 : ℝ) * r < r := by linarith
    have h15 : ENNReal.ofReal ((1 / 2 : ℝ) * r) < ENNReal.ofReal r :=
      (ENNReal.ofReal_lt_ofReal_iff hr_pos).mpr h14
    rw [h13, h_eq] at h_contra
    exact not_le.mpr h15 h_contra

  let G : Kakeya.TubeFamily delta := Finset.image f Finset.univ

  let getIndex (T : Kakeya.DeltaTube delta) (hT : T ∈ G) : Fin S.family.card :=
    Classical.choose (show ∃ (i : Fin S.family.card), f i = T from
      by simpa [G, Finset.mem_image, Finset.mem_univ] using hT)

  have hgetIndex_spec : ∀ (T : Kakeya.DeltaTube delta) (hT : T ∈ G),
      f (getIndex T hT) = T := by
    intro T hT
    exact Classical.choose_spec (show ∃ (i : Fin S.family.card), f i = T from
      by simpa [G, Finset.mem_image, Finset.mem_univ] using hT)

  let source : ∀ (T : Kakeya.DeltaTube delta), T ∈ G → Fin F.card :=
    fun T hT => S.embedding (getIndex T hT)

  let Zcarrier : Kakeya.DeltaTube delta → Set Kakeya.Point3 :=
    fun T => if hT : T ∈ G then Y.carrier (Fin.cast hF_card (source T hT)) else ∅

  let Z : Kakeya.Shading G :=
    { carrier := Zcarrier
      measurable_carrier := by
        intro T hT
        have hZcarrier : Zcarrier T = Y.carrier (Fin.cast hF_card (source T hT)) := by
          unfold Zcarrier
          exact dif_pos hT
        exact hZcarrier ▸ Y.measurable_carrier (Fin.cast hF_card (source T hT))
      subset_tube := by
        intro T hT
        have hZcarrier : Zcarrier T = Y.carrier (Fin.cast hF_card (source T hT)) := by
          unfold Zcarrier
          exact dif_pos hT
        let j := Fin.cast hF_card (source T hT)
        have hZcarrier' : Zcarrier T = Y.carrier j := hZcarrier
        rw [hZcarrier']
        have hsub : Y.carrier j ⊆ (F.toBodyFamily.body j).carrier := Y.subset_body j
        have hbody : (F.toBodyFamily.body j).carrier = (F.tube (source T hT)).carrier := by
          simp [j, Kakeya.Streamlined.TubeFamily.toBodyFamily, Kakeya.Streamlined.tubeBody, Fin.cast]
          <;> rfl
        have hsrc : F.tube (source T hT) = T := by
          have h1 : S.family.tube (getIndex T hT) = T := hgetIndex_spec T hT
          have h2 : F.tube (S.embedding (getIndex T hT)) = S.family.tube (getIndex T hT) :=
            (S.tube_eq (getIndex T hT)).symm
          exact h2.trans h1
        rw [hbody, hsrc] at hsub
        exact hsub }

  have hG_card : G.card = S.family.card := by
    rw [Finset.card_image_of_injective _ hf_inj]
    <;> simp

  have hG_enncard : G.enncard = S.family.enncard := by
    simpa [Kakeya.TubeFamily.enncard, Streamlined.TubeFamily.enncard] using hG_card

  have hvs : TubeVolumeScalingStatement := tube_volume_scaling
  have hV_pos : 0 < Kakeya.deltaTubeVolume delta :=
    (hvs.2.1 delta hdelta hdelta1).1
  have hV_ne_top : Kakeya.deltaTubeVolume delta ≠ ⊤ :=
    (hvs.2.1 delta hdelta hdelta1).2
  have hV_eq : ∀ (T : Kakeya.DeltaTube delta), T.volume = Kakeya.deltaTubeVolume delta :=
    hvs.1 delta

  have hG_mass : G.mass = S.family.toBodyFamily.mass := by
    let eS : Fin S.family.card ≃ Fin S.family.toBodyFamily.card :=
      Equiv.cast (congr_arg Fin hS_card)
    have hsum : ∑ T ∈ G, T.volume = ∑ i : Fin S.family.card, (S.family.tube i).volume := by
      rw [Finset.sum_image (fun x _ y _ h => hf_inj h)] <;> rfl
    have h2 : ∀ (i : Fin S.family.card),
        (S.family.tube i).volume = (S.family.toBodyFamily.body (eS i)).volume := by
      intro i
      simp [Kakeya.Streamlined.TubeFamily.toBodyFamily, Kakeya.Streamlined.tubeBody, eS, Equiv.cast, Fin.cast]
      <;> rfl
    have h3 : ∑ i : Fin S.family.card, (S.family.tube i).volume =
        ∑ j : Fin S.family.toBodyFamily.card, (S.family.toBodyFamily.body j).volume := by
      have h4 : ∑ i : Fin S.family.card, (S.family.tube i).volume =
          ∑ i : Fin S.family.card, (S.family.toBodyFamily.body (eS i)).volume := by
        apply Finset.sum_congr rfl
        intro i _
        exact h2 i
      rw [h4]
      exact Fintype.sum_equiv eS
        (fun x : Fin S.family.card => (S.family.toBodyFamily.body (eS x)).volume)
        (fun j : Fin S.family.toBodyFamily.card => (S.family.toBodyFamily.body j).volume)
        (by intro x; rfl)
    simpa [Kakeya.TubeFamily.mass, Streamlined.BodyFamily.mass] using hsum.trans h3

  have hZ_mass : Z.mass = (S.restrictShading Y).mass := by
    let eS : Fin S.family.card ≃ Fin S.family.toBodyFamily.card :=
      Equiv.cast (congr_arg Fin hS_card)
    have hsum1 : ∑ T ∈ G, MeasureTheory.volume (Z.carrier T) =
        ∑ i : Fin S.family.card,
          MeasureTheory.volume ((S.restrictShading Y).carrier (eS i)) := by
      have h_sum_img : ∑ T ∈ G, MeasureTheory.volume (Z.carrier T) =
          ∑ i : Fin S.family.card, MeasureTheory.volume (Z.carrier (f i)) := by
        have h_inj : Set.InjOn f (Set.univ : Set (Fin S.family.card)) :=
          fun x _ y _ h => hf_inj h
        have h : ∑ T ∈ Finset.image f Finset.univ, MeasureTheory.volume (Z.carrier T) =
            ∑ i ∈ Finset.univ, MeasureTheory.volume (Z.carrier (f i)) :=
          Finset.sum_image (fun {x} _ {y} _ h => hf_inj h)
        simpa [G] using h
      rw [h_sum_img]
      apply Finset.sum_congr rfl
      intro i _
      let T := f i
      have hT : T ∈ G := Finset.mem_image_of_mem f (Finset.mem_univ i)
      have huniq : getIndex T hT = i := by
        have h : f (getIndex T hT) = f i := hgetIndex_spec T hT
        exact hf_inj h
      have h10 : Z.carrier T = Y.carrier (Fin.cast hF_card (S.embedding i)) := by
        have h_src : source T hT = S.embedding i := by
          simp [source, huniq]
        dsimp only [Z, Zcarrier]
        rw [dif_pos hT, h_src]
      have h11 : (S.restrictShading Y).carrier (eS i) = Y.carrier (S.embedding (eS i)) := by rfl
      have h12 : Y.carrier (Fin.cast hF_card (S.embedding i)) =
          Y.carrier (S.embedding (eS i)) := by
        apply congr_arg (fun (x : Fin F.toBodyFamily.card) => Y.carrier x)
        apply Fin.ext
        simp [eS, Equiv.cast, Fin.cast]
        <;> rfl
      rw [h10, h11, h12]
    have hsum2 : ∑ i : Fin S.family.card,
          MeasureTheory.volume ((S.restrictShading Y).carrier (eS i)) =
        (S.restrictShading Y).mass := by
      let g : Fin S.family.toBodyFamily.card → ENNReal :=
        fun j => MeasureTheory.volume ((S.restrictShading Y).carrier j)
      have h : ∑ i : Fin S.family.card, g (eS i) = ∑ j : Fin S.family.toBodyFamily.card, g j :=
        Fintype.sum_equiv eS (fun i : Fin S.family.card => g (eS i)) g
          (by intro x; rfl)
      simpa [g, Streamlined.Shading.mass] using h
    have h_goal : Z.mass = ∑ T ∈ G, MeasureTheory.volume (Z.carrier T) := by rfl
    rw [h_goal, hsum1, hsum2]

  have hcount_eq : ∀ (W : Set Kakeya.Point3),
      G.containedCount W = S.family.toBodyFamily.containedCount W := by
    intro W
    let P : Kakeya.DeltaTube delta → Prop := fun T => T.carrier ⊆ W
    let e : Fin S.family.toBodyFamily.card ≃ Fin S.family.card :=
      Equiv.cast (congr_arg Fin (by rfl))
    let I' : Finset (Fin S.family.toBodyFamily.card) :=
      S.family.toBodyFamily.containedIndices W
    let I : Finset (Fin S.family.card) := Finset.image e I'
    have hI_card : I.card = I'.card := by
      rw [Finset.card_image_of_injective _ e.injective]
    have hI_iff : ∀ (i : Fin S.family.card),
        i ∈ I ↔ (S.family.tube i).carrier ⊆ W := by
      intro i
      have h1 : i ∈ I ↔ ∃ (j : Fin S.family.toBodyFamily.card), j ∈ I' ∧ e j = i := by
        simp [I, Finset.mem_image]
        <;> rfl
      rw [h1]
      constructor
      · rintro ⟨j, hj, rfl⟩
        have h2 : (S.family.toBodyFamily.body j).carrier ⊆ W :=
          (Streamlined.BodyFamily.mem_containedIndices_iff).mp hj
        have h_eq : (S.family.toBodyFamily.body j).carrier = (S.family.tube (e j)).carrier := by rfl
        rw [h_eq] at h2
        exact h2
      · intro h
        refine ⟨e.symm i, ?_, e.apply_symm_apply i⟩
        have h_eq : (S.family.toBodyFamily.body (e.symm i)).carrier =
            (S.family.tube (e (e.symm i))).carrier := by rfl
        have h4 : (S.family.toBodyFamily.body (e.symm i)).carrier ⊆ W := by
          rw [h_eq, e.apply_symm_apply i]
          exact h
        exact (Streamlined.BodyFamily.mem_containedIndices_iff).mpr h4
    have h1 : G.filter P = Finset.image f I := by
      ext T
      simp only [G, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨i, rfl⟩, hPT⟩
        refine ⟨i, (hI_iff i).mpr hPT, rfl⟩
      · rintro ⟨i, hiI, rfl⟩
        have hPT : P (f i) := (hI_iff i).mp hiI
        exact ⟨⟨i, rfl⟩, hPT⟩
    have h2 : (G.filter P).card = I.card := by
      rw [h1, Finset.card_image_of_injective _ hf_inj]
    have h3 : G.containedCount W = ((G.filter P).card : ENNReal) := by rfl
    have h4 : S.family.toBodyFamily.containedCount W = ((I'.card : ENNReal)) := by
      rfl
    rw [h3, h4, ← hI_card, ← h2]

  have hmass_eq : ∀ (W : Set Kakeya.Point3),
      S.family.toBodyFamily.containedMass W =
        S.family.toBodyFamily.containedCount W * Kakeya.deltaTubeVolume delta := by
    intro W
    have h_all_vol : ∀ (i : Fin S.family.toBodyFamily.card),
        (S.family.toBodyFamily.body i).volume = Kakeya.deltaTubeVolume delta := by
      intro i
      have h7 : (S.family.toBodyFamily.body i).volume =
          (S.family.tube (Fin.cast hS_card.symm i)).volume := by
        simp [Kakeya.Streamlined.TubeFamily.toBodyFamily, Kakeya.Streamlined.tubeBody, Fin.cast]
        <;> rfl
      rw [h7]
      exact hV_eq (S.family.tube (Fin.cast hS_card.symm i))
    calc
      S.family.toBodyFamily.containedMass W
        = ∑ i ∈ S.family.toBodyFamily.containedIndices W,
            (S.family.toBodyFamily.body i).volume := by rfl
      _ = ∑ i ∈ S.family.toBodyFamily.containedIndices W,
            Kakeya.deltaTubeVolume delta := by
          apply Finset.sum_congr rfl
          intro i _
          exact h_all_vol i
      _ = (S.family.toBodyFamily.containedIndices W).card *
            Kakeya.deltaTubeVolume delta := by
          have hsum : ∑ i ∈ S.family.toBodyFamily.containedIndices W, Kakeya.deltaTubeVolume delta =
              (S.family.toBodyFamily.containedIndices W).card * Kakeya.deltaTubeVolume delta := by
            rw [Finset.sum_const]
            <;> simp [mul_comm]
            <;> ring
          exact hsum
      _ = S.family.toBodyFamily.containedCount W *
            Kakeya.deltaTubeVolume delta := by rfl

  let C_kt := Kakeya.realRpowENN delta (-ktEta)
  let C_assert := Kakeya.realRpowENN delta (-assertionEta)

  have hC_kt_ne_top : C_kt ≠ ⊤ := by
    simp [C_kt, Kakeya.realRpowENN] <;> exact ENNReal.ofReal_ne_top
  have hC_kt_pos : 0 < C_kt := by
    simp [C_kt, Kakeya.realRpowENN, Real.rpow_pos_of_pos hdelta]
    <;> positivity
  have hC_assert_pos : 0 < C_assert := by
    simp [C_assert, Kakeya.realRpowENN, Real.rpow_pos_of_pos hdelta]
    <;> positivity

  have hkt_lemma : C_kt ≤ C_assert := by
    have h : -ktEta ≥ -assertionEta := by linarith
    have h' : Real.rpow delta (-ktEta) ≤ Real.rpow delta (-assertionEta) :=
      Real.rpow_le_rpow_of_exponent_ge hdelta hdelta1 h
    simpa [C_kt, C_assert, Kakeya.realRpowENN] using ENNReal.ofReal_mono h'

  refine ⟨G, source, Z, ?_⟩

  constructor
  · -- G.IsInUnitBall
    intro T hT
    rcases Finset.mem_image.mp hT with ⟨i, _, rfl⟩
    exact hunit i

  constructor
  · -- G.IsEssentiallyDistinct
    intro T hT U hU hne
    rcases Finset.mem_image.mp hT with ⟨i, _, rfl⟩
    rcases Finset.mem_image.mp hU with ⟨j, _, rfl⟩
    have hine : i ≠ j := by
      intro h
      rw [h] at hne
      exact hne rfl
    exact hdistinct i j hine

  constructor
  · -- source property
    intro T hT
    have h1 : S.family.tube (getIndex T hT) = T := hgetIndex_spec T hT
    have h2 : F.tube (S.embedding (getIndex T hT)) = S.family.tube (getIndex T hT) :=
      (S.tube_eq (getIndex T hT)).symm
    exact h2.trans h1

  constructor
  · -- shading subset property
    intro T hT
    have hZcarrier : Z.carrier T = Y.carrier (Fin.cast hF_card (source T hT)) := by
      simp [Z, Zcarrier, dif_pos hT]
    rw [hZcarrier]
    have h9 : (Fin.cast hF_card (source T hT)) = (source T hT) := by
      apply Fin.ext
      simp [Fin.cast]
    rw [h9]
    <;> exact subset_refl _

  constructor
  · -- Z.IsLambdaDense
    have h : Kakeya.realRpowENN delta assertionEta * G.mass ≤ Z.mass := by
      rw [hG_mass, hZ_mass]
      exact hdense
    exact h

  constructor
  · -- KatzTaoConvexWolffBound
    intro W hWconv
    have hdensity : S.family.toBodyFamily.density W ≤ C_kt := by
      have h_mem : S.family.toBodyFamily.density W ∈
          {d : ENNReal | ∃ (K : Set Kakeya.Point3), Convex ℝ K ∧ d = S.family.toBodyFamily.density K} :=
        ⟨W, hWconv, rfl⟩
      have h_bdd : BddAbove {d : ENNReal | ∃ (K : Set Kakeya.Point3), Convex ℝ K ∧ d = S.family.toBodyFamily.density K} := by
        refine ⟨⊤, fun x _ => le_top⟩
      have h1 : S.family.toBodyFamily.density W ≤ S.family.toBodyFamily.deltaMax :=
        le_csSup h_bdd h_mem
      exact h1.trans hkt
    have hdiv : S.family.toBodyFamily.containedMass W *
        (MeasureTheory.volume W)⁻¹ ≤ C_kt := by
      have h : S.family.toBodyFamily.density W ≤ C_kt := hdensity
      convert h using 2
      <;> simp [Streamlined.BodyFamily.density] <;> rfl
    have hmass_le : S.family.toBodyFamily.containedMass W ≤
        C_kt * MeasureTheory.volume W :=
      ennreal_of_le_div hC_kt_ne_top hC_kt_pos hdiv
    have hcount_le : S.family.toBodyFamily.containedCount W *
        Kakeya.deltaTubeVolume delta ≤ C_kt * MeasureTheory.volume W := by
      rw [hmass_eq W] at hmass_le
      exact hmass_le
    have hfinal : S.family.toBodyFamily.containedCount W ≤
        C_kt * MeasureTheory.volume W * (Kakeya.deltaTubeVolume delta)⁻¹ := by
      have h : S.family.toBodyFamily.containedCount W *
            Kakeya.deltaTubeVolume delta * (Kakeya.deltaTubeVolume delta)⁻¹ ≤
          C_kt * MeasureTheory.volume W * (Kakeya.deltaTubeVolume delta)⁻¹ := by
        gcongr
      have h2 : Kakeya.deltaTubeVolume delta * (Kakeya.deltaTubeVolume delta)⁻¹ = 1 :=
        ENNReal.mul_inv_cancel hV_pos.ne' hV_ne_top
      have h3 : S.family.toBodyFamily.containedCount W *
            Kakeya.deltaTubeVolume delta * (Kakeya.deltaTubeVolume delta)⁻¹ =
          S.family.toBodyFamily.containedCount W := by
        rw [mul_assoc, h2, mul_one]
      rw [h3] at h
      exact h
    have h4 : C_kt ≤ C_assert := hkt_lemma
    have hfinal' : G.containedCount W ≤
        C_kt * MeasureTheory.volume W * (Kakeya.deltaTubeVolume delta)⁻¹ := by
      rw [hcount_eq W] <;> exact hfinal
    calc
      G.containedCount W
        ≤ C_kt * MeasureTheory.volume W * (Kakeya.deltaTubeVolume delta)⁻¹ := hfinal'
      _ ≤ C_assert * MeasureTheory.volume W * (Kakeya.deltaTubeVolume delta)⁻¹ := by
        gcongr

  constructor
  · -- FrostmanSlabWolffBound
    intro Sslab
    have hslab_conv : Convex ℝ Sslab.carrier := by
      apply Convex.inter
      · exact convex_closedBall (0 : Kakeya.Point3) 1
      · apply Convex.cthickening
        have h_hyperplane : Convex ℝ Sslab.hyperplane := by
          rw [convex_iff_forall_pos]
          intro x hx y hy a b ha hb hab
          have hix : inner ℝ x Sslab.normal = Sslab.offset := by
            exact hx
          have hiy : inner ℝ y Sslab.normal = Sslab.offset := by
            exact hy
          have h : inner ℝ (a • x + b • y) Sslab.normal = Sslab.offset := by
            calc
              inner ℝ (a • x + b • y) Sslab.normal
                = a * inner ℝ x Sslab.normal + b * inner ℝ y Sslab.normal := by
                  simp [inner_add_left, inner_smul_left] <;> ring
              _ = a * Sslab.offset + b * Sslab.offset := by rw [hix, hiy] <;> ring
              _ = Sslab.offset := by
                have hsum : a + b = 1 := hab
                have h_eq : a * Sslab.offset + b * Sslab.offset = Sslab.offset := by
                  calc
                    a * Sslab.offset + b * Sslab.offset
                      = (a + b) * Sslab.offset := by ring
                    _ = 1 * Sslab.offset := by rw [hsum]
                    _ = Sslab.offset := by ring
                exact h_eq
          have h_goal : a • x + b • y ∈ Sslab.hyperplane := by
            exact h
          exact h_goal
        exact h_hyperplane
    have hkt_bound : G.containedCount Sslab.carrier ≤
        C_kt * MeasureTheory.volume Sslab.carrier *
          (Kakeya.deltaTubeVolume delta)⁻¹ := by
      have hdensity : S.family.toBodyFamily.density Sslab.carrier ≤ C_kt := by
        have h_mem : S.family.toBodyFamily.density Sslab.carrier ∈
            {d : ENNReal | ∃ (K : Set Kakeya.Point3), Convex ℝ K ∧ d = S.family.toBodyFamily.density K} :=
          ⟨Sslab.carrier, hslab_conv, rfl⟩
        have h_bdd : BddAbove {d : ENNReal | ∃ (K : Set Kakeya.Point3), Convex ℝ K ∧ d = S.family.toBodyFamily.density K} := by
          refine ⟨⊤, fun x _ => le_top⟩
        have h1 : S.family.toBodyFamily.density Sslab.carrier ≤ S.family.toBodyFamily.deltaMax :=
          le_csSup h_bdd h_mem
        exact h1.trans hkt
      have hdiv : S.family.toBodyFamily.containedMass Sslab.carrier *
          (MeasureTheory.volume Sslab.carrier)⁻¹ ≤ C_kt := by
        have h : S.family.toBodyFamily.density Sslab.carrier ≤ C_kt := hdensity
        convert h using 2
        <;> simp [Streamlined.BodyFamily.density] <;> rfl
      have hmass_le : S.family.toBodyFamily.containedMass Sslab.carrier ≤
          C_kt * MeasureTheory.volume Sslab.carrier :=
        ennreal_of_le_div hC_kt_ne_top hC_kt_pos hdiv
      have hcount_le : S.family.toBodyFamily.containedCount Sslab.carrier *
          Kakeya.deltaTubeVolume delta ≤
          C_kt * MeasureTheory.volume Sslab.carrier := by
        rw [hmass_eq Sslab.carrier] at hmass_le
        exact hmass_le
      have hfinal : S.family.toBodyFamily.containedCount Sslab.carrier ≤
          C_kt * MeasureTheory.volume Sslab.carrier *
            (Kakeya.deltaTubeVolume delta)⁻¹ := by
        have h : S.family.toBodyFamily.containedCount Sslab.carrier *
              Kakeya.deltaTubeVolume delta * (Kakeya.deltaTubeVolume delta)⁻¹ ≤
            C_kt * MeasureTheory.volume Sslab.carrier *
              (Kakeya.deltaTubeVolume delta)⁻¹ := by gcongr
        have h2 : Kakeya.deltaTubeVolume delta *
              (Kakeya.deltaTubeVolume delta)⁻¹ = 1 :=
          ENNReal.mul_inv_cancel hV_pos.ne' hV_ne_top
        have h3 : S.family.toBodyFamily.containedCount Sslab.carrier *
              Kakeya.deltaTubeVolume delta * (Kakeya.deltaTubeVolume delta)⁻¹ =
            S.family.toBodyFamily.containedCount Sslab.carrier := by
          rw [mul_assoc, h2, mul_one]
        rw [h3] at h
        exact h
      rw [hcount_eq Sslab.carrier]
      exact hfinal
    set α : ℝ := assertionEta - ktEta with hα_def
    have hα_pos : 0 < α := by linarith
    set β : ℝ := assertionEta - ktEta - coreCardLoss with hβ_def
    have hβ_pos : 0 < β := by linarith
    have hV_lower : Kakeya.realRpowENN delta 2 ≤ Kakeya.deltaTubeVolume delta := by
      have h : ENNReal.ofReal (delta ^ 2) ≤ Kakeya.deltaTubeVolume delta :=
        canonical_volume_lower hdelta
      have h2 : Kakeya.realRpowENN delta 2 = ENNReal.ofReal (delta ^ 2) := by
        simp [Kakeya.realRpowENN, Real.rpow_two]
        <;> ring_nf
      rw [h2]
      exact h
    have hV_inv_upper : (Kakeya.deltaTubeVolume delta)⁻¹ ≤
        (Kakeya.realRpowENN delta 2)⁻¹ := by
      gcongr
    have hpos2 : 0 < Real.rpow delta 2 := Real.rpow_pos_of_pos hdelta 2
    have h_rpow2_inv : (Kakeya.realRpowENN delta 2)⁻¹ =
        Kakeya.realRpowENN delta (-2) := by
      have h3 : Kakeya.realRpowENN delta 2 = ENNReal.ofReal (Real.rpow delta 2) := by
        simp [Kakeya.realRpowENN] <;> rfl
      have h4 : Kakeya.realRpowENN delta (-2) = ENNReal.ofReal (Real.rpow delta (-2)) := by
        simp [Kakeya.realRpowENN] <;> rfl
      have h_inv : (ENNReal.ofReal (Real.rpow delta 2))⁻¹ =
          ENNReal.ofReal ((Real.rpow delta 2)⁻¹) :=
        (ENNReal.ofReal_inv_of_pos hpos2).symm
      have h2 : (Real.rpow delta 2)⁻¹ = Real.rpow delta (-2) :=
        (Real.rpow_neg hdelta.le (y := 2)).symm
      rw [h3, h4, h_inv, h2]
    have h_key1 : Kakeya.realRpowENN delta α *
        (Kakeya.deltaTubeVolume delta)⁻¹ ≤
        Kakeya.realRpowENN delta (-2 + α) := by
      calc
        Kakeya.realRpowENN delta α * (Kakeya.deltaTubeVolume delta)⁻¹
          ≤ Kakeya.realRpowENN delta α * (Kakeya.realRpowENN delta 2)⁻¹ := by
            gcongr
        _ = Kakeya.realRpowENN delta α * Kakeya.realRpowENN delta (-2) := by
            rw [h_rpow2_inv]
        _ = Kakeya.realRpowENN delta (α + (-2)) := by
            rw [realRpowENN_add' hdelta α (-2)]
        _ = Kakeya.realRpowENN delta (-2 + α) := by ring_nf
    have h_exp_le : -2 + α ≥ -2 + coreCardLoss := by linarith
    have h_rpow_le : Kakeya.realRpowENN delta (-2 + α) ≤
        Kakeya.realRpowENN delta (-2 + coreCardLoss) := by
      have h : Real.rpow delta (-2 + α) ≤ Real.rpow delta (-2 + coreCardLoss) := by
        exact Real.rpow_le_rpow_of_exponent_ge hdelta hdelta1 (by linarith)
      simpa [Kakeya.realRpowENN] using ENNReal.ofReal_mono h
    have hG_lower : Kakeya.realRpowENN delta (-2 + coreCardLoss) ≤ G.enncard := by
      rw [hG_enncard]
      exact hcard
    have h_key2 : Kakeya.realRpowENN delta α *
        (Kakeya.deltaTubeVolume delta)⁻¹ ≤ G.enncard := by
      calc
        Kakeya.realRpowENN delta α * (Kakeya.deltaTubeVolume delta)⁻¹
          ≤ Kakeya.realRpowENN delta (-2 + α) := h_key1
        _ ≤ Kakeya.realRpowENN delta (-2 + coreCardLoss) := h_rpow_le
        _ ≤ G.enncard := hG_lower
    have hC_kt_eq : C_kt = C_assert * Kakeya.realRpowENN delta α := by
      have h : C_assert * Kakeya.realRpowENN delta α =
          Kakeya.realRpowENN delta (-assertionEta + α) := by
        rw [realRpowENN_add' hdelta (-assertionEta) α]
        <;> ring_nf
      have h2 : -assertionEta + α = -ktEta := by
        simp [hα_def] <;> linarith
      rw [h, h2]
      <;> rfl
    have h_main : C_kt * (Kakeya.deltaTubeVolume delta)⁻¹ ≤
        C_assert * G.enncard := by
      rw [hC_kt_eq]
      have h : C_assert * (Kakeya.realRpowENN delta α *
            (Kakeya.deltaTubeVolume delta)⁻¹) ≤
          C_assert * G.enncard :=
        mul_le_mul_of_nonneg_left h_key2 (by positivity)
      rw [mul_assoc] at *
      <;> exact h
    calc
      G.containedCount Sslab.carrier
        ≤ C_kt * MeasureTheory.volume Sslab.carrier *
              (Kakeya.deltaTubeVolume delta)⁻¹ := hkt_bound
      _ = (C_kt * (Kakeya.deltaTubeVolume delta)⁻¹) *
              MeasureTheory.volume Sslab.carrier := by ring
      _ ≤ (C_assert * G.enncard) * MeasureTheory.volume Sslab.carrier := by
            exact mul_le_mul_of_nonneg_right h_main (by positivity)
      _ = C_assert * MeasureTheory.volume Sslab.carrier * G.enncard := by ring

  · -- Cardinality lower bound
    have h1 : G.enncard = S.family.enncard := hG_enncard
    have h2 : Kakeya.realRpowENN delta (-2 + coreCardLoss) ≤ G.enncard := by
      rw [h1] <;> exact hcard
    have h3 : -2 + requestedCardLoss ≥ -2 + coreCardLoss := by linarith
    have h4 : Kakeya.realRpowENN delta (-2 + requestedCardLoss) ≤
        Kakeya.realRpowENN delta (-2 + coreCardLoss) := by
      have h : Real.rpow delta (-2 + requestedCardLoss) ≤
          Real.rpow delta (-2 + coreCardLoss) := by
        exact Real.rpow_le_rpow_of_exponent_ge hdelta hdelta1 (by linarith)
      simpa [Kakeya.realRpowENN] using ENNReal.ofReal_mono h
    exact h4.trans h2

end Kakeya.Assouad
