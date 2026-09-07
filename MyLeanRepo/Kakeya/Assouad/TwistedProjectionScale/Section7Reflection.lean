import MyLeanRepo.Kakeya.Assouad.Statements

/-!
# Section 7 vertical reflection

Exact reflection of indexed tubes, shadings, line parameters, and twisted
projections across the horizontal plane `z = 0`.
-/

noncomputable section

open MeasureTheory Set

namespace Kakeya.Assouad

def section7Reflection3 : Point3 ≃ₗᵢ[ℝ] Point3 :=
  LinearIsometryEquiv.piLpCongrRight 2
    (fun i : Fin 3 =>
      if i = 2 then LinearIsometryEquiv.neg ℝ
      else LinearIsometryEquiv.refl ℝ ℝ)

def section7Reflection2 : Point2 ≃ₗᵢ[ℝ] Point2 :=
  LinearIsometryEquiv.piLpCongrRight 2
    (fun i : Fin 2 =>
      if i = 1 then LinearIsometryEquiv.neg ℝ
      else LinearIsometryEquiv.refl ℝ ℝ)

@[simp]
lemma section7Reflection3_apply (x : Point3) (i : Fin 3) :
    section7Reflection3 x i = if i = 2 then -x i else x i := by
  change
    (if i = 2 then LinearIsometryEquiv.neg ℝ
      else LinearIsometryEquiv.refl ℝ ℝ) (x i) =
      if i = 2 then -x i else x i
  by_cases h : i = 2 <;> simp [h]

@[simp]
lemma section7Reflection2_apply (x : Point2) (i : Fin 2) :
    section7Reflection2 x i = if i = 1 then -x i else x i := by
  change
    (if i = 1 then LinearIsometryEquiv.neg ℝ
      else LinearIsometryEquiv.refl ℝ ℝ) (x i) =
      if i = 1 then -x i else x i
  by_cases h : i = 1 <;> simp [h]

@[simp]
lemma section7Reflection3_involutive (x : Point3) :
    section7Reflection3 (section7Reflection3 x) = x := by
  ext i
  fin_cases i <;> simp

@[simp]
lemma section7Reflection2_involutive (x : Point2) :
    section7Reflection2 (section7Reflection2 x) = x := by
  ext i
  fin_cases i <;> simp

def section7ReflectTube {delta : ℝ}
    (T : Kakeya.DeltaTube delta) : Kakeya.DeltaTube delta :=
  ⟨section7Reflection3 T.base,
    section7Reflection3 T.direction,
    by rw [section7Reflection3.norm_map, T.direction_unit]⟩

lemma section7Reflection3_unitSegment
    (base direction : Point3) :
    section7Reflection3 ''
        Kakeya.unitSegment base direction =
      Kakeya.unitSegment
        (section7Reflection3 base)
        (section7Reflection3 direction) := by
  ext p
  constructor
  · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    exact ⟨t, ht, by simp [section7Reflection3.map_add,
      section7Reflection3.map_smul]⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨base + t • direction, ⟨t, ht, rfl⟩, ?_⟩
    simp [section7Reflection3.map_add,
      section7Reflection3.map_smul]

lemma section7Reflection3_cthickening (r : ℝ) (S : Set Point3) :
    section7Reflection3 '' Metric.cthickening r S =
      Metric.cthickening r (section7Reflection3 '' S) := by
  ext y
  simp only [Metric.mem_cthickening_iff, Set.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Metric.infEDist_image section7Reflection3.isometry]
    exact hx
  · intro hy
    refine
      ⟨section7Reflection3 y, ?_,
        section7Reflection3_involutive y⟩
    have himage :
        section7Reflection3 ''
            (section7Reflection3 '' S) = S := by
      rw [← Set.image_comp]
      simp [Function.comp_def]
    have hdist :=
      Metric.infEDist_image section7Reflection3.isometry
        (x := y) (t := section7Reflection3 '' S)
    rw [himage] at hdist
    rw [hdist]
    exact hy

@[simp]
lemma section7ReflectTube_carrier {delta : ℝ}
    (T : Kakeya.DeltaTube delta) :
    (section7ReflectTube T).carrier =
      section7Reflection3 '' T.carrier := by
  change
    Metric.cthickening delta
        (Kakeya.unitSegment
          (section7Reflection3 T.base)
          (section7Reflection3 T.direction)) =
      section7Reflection3 ''
        Metric.cthickening delta
          (Kakeya.unitSegment T.base T.direction)
  rw [← section7Reflection3_unitSegment]
  exact
    (section7Reflection3_cthickening delta
      (Kakeya.unitSegment T.base T.direction)).symm

@[simp]
lemma section7ReflectTube_volume {delta : ℝ}
    (T : Kakeya.DeltaTube delta) :
    (section7ReflectTube T).volume = T.volume := by
  rw [Kakeya.DeltaTube.volume, section7ReflectTube_carrier]
  have hmp : MeasurePreserving section7Reflection3 volume volume :=
    section7Reflection3.measurePreserving
  have h :=
    MeasurePreserving.measure_preimage_equiv
      (f := section7Reflection3.toMeasurableEquiv)
      hmp (section7Reflection3 '' T.carrier)
  change
    volume
        (section7Reflection3 ⁻¹'
          (section7Reflection3 '' T.carrier)) =
      volume (section7Reflection3 '' T.carrier) at h
  rw [section7Reflection3.injective.preimage_image] at h
  exact h.symm

lemma section7ReflectTube_essentiallyDistinct {delta : ℝ}
    {T U : Kakeya.DeltaTube delta}
    (h : T.EssentiallyDistinct U) :
    (section7ReflectTube T).EssentiallyDistinct
      (section7ReflectTube U) := by
  rw [Kakeya.DeltaTube.EssentiallyDistinct] at h ⊢
  rw [section7ReflectTube_carrier,
    section7ReflectTube_carrier,
    ← Set.image_inter section7Reflection3.injective,
    section7ReflectTube_volume,
    section7ReflectTube_volume]
  have hmp : MeasurePreserving section7Reflection3 volume volume :=
    section7Reflection3.measurePreserving
  have himage :
      volume
          (section7Reflection3 ''
            (T.carrier ∩ U.carrier)) =
        volume (T.carrier ∩ U.carrier) := by
    have hpre :=
      MeasurePreserving.measure_preimage_equiv
        (f := section7Reflection3.toMeasurableEquiv)
        hmp
        (section7Reflection3 '' (T.carrier ∩ U.carrier))
    change
      volume
          (section7Reflection3 ⁻¹'
            (section7Reflection3 ''
              (T.carrier ∩ U.carrier))) =
        volume
          (section7Reflection3 ''
            (T.carrier ∩ U.carrier)) at hpre
    rw [section7Reflection3.injective.preimage_image] at hpre
    exact hpre.symm
  rw [himage]
  exact h

@[simp]
lemma tubeParamsOfTube_section7ReflectTube {delta : ℝ}
    (T : Kakeya.DeltaTube delta) :
    tubeParamsOfTube (section7ReflectTube T) =
      { a := (tubeParamsOfTube T).a
        b := (tubeParamsOfTube T).b
        c := -(tubeParamsOfTube T).c
        d := -(tubeParamsOfTube T).d } := by
  ext <;>
    simp [section7ReflectTube, tubeParamsOfTube] <;>
    ring

lemma twistedProjection_section7Reflection
    (f : SlopeFunction) (p : Point3) :
    twistedProjection f.reflected (section7Reflection3 p) =
      section7Reflection2 (twistedProjection f p) := by
  ext i
  fin_cases i <;>
    simp [twistedProjection, SlopeFunction.reflected] <;>
    ring

private lemma section7Reflection3_volume_image (S : Set Point3) :
    volume (section7Reflection3 '' S) = volume S := by
  have hmp : MeasurePreserving section7Reflection3 volume volume :=
    section7Reflection3.measurePreserving
  have h :=
    MeasurePreserving.measure_preimage_equiv
      (f := section7Reflection3.toMeasurableEquiv)
      hmp (section7Reflection3 '' S)
  change
    volume
        (section7Reflection3 ⁻¹'
          (section7Reflection3 '' S)) =
      volume (section7Reflection3 '' S) at h
  rw [section7Reflection3.injective.preimage_image] at h
  exact h.symm

private lemma section7Reflection2_volume_image (S : Set Point2) :
    volume (section7Reflection2 '' S) = volume S := by
  have hmp : MeasurePreserving section7Reflection2 volume volume :=
    section7Reflection2.measurePreserving
  have h :=
    MeasurePreserving.measure_preimage_equiv
      (f := section7Reflection2.toMeasurableEquiv)
      hmp (section7Reflection2 '' S)
  change
    volume
        (section7Reflection2 ⁻¹'
          (section7Reflection2 '' S)) =
      volume (section7Reflection2 '' S) at h
  rw [section7Reflection2.injective.preimage_image] at h
  exact h.symm

theorem section7_vertical_reflection :
    Section7VerticalReflectionStatement := by
  intro delta F Y
  let reflectedFamily : Kakeya.Streamlined.TubeFamily delta :=
    { card := F.card
      tube := fun i => section7ReflectTube (F.tube i) }
  let reflectedShading :
      Kakeya.Streamlined.TubeShading reflectedFamily :=
    { carrier := fun i => section7Reflection3 '' Y.carrier i
      measurable_carrier := fun i =>
        section7Reflection3.toMeasurableEquiv.measurableSet_image.mpr
          (Y.measurable_carrier i)
      subset_body := by
        intro i p hp
        change p ∈ (section7ReflectTube (F.tube i)).carrier
        rw [section7ReflectTube_carrier]
        rcases hp with ⟨q, hq, rfl⟩
        exact ⟨q, Y.subset_body i hq, rfl⟩ }
  refine
    ⟨reflectedFamily, reflectedShading,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hF
    simpa [reflectedFamily, Kakeya.Streamlined.TubeFamily.Nonempty] using hF
  · intro R hbase i
    change ‖section7Reflection3 (F.tube i).base‖ ≤ R
    rw [section7Reflection3.norm_map]
    exact hbase i
  · intro hdistinct i j hij
    exact section7ReflectTube_essentiallyDistinct (hdistinct i j hij)
  · intro hvertical i
    change
      (1 / 2 : ℝ) ≤
        |(section7ReflectTube (F.tube i)).direction (2 : Fin 3)|
    simpa [section7ReflectTube] using hvertical i
  · intro hparams i
    change
      |(tubeParamsOfTube (section7ReflectTube (F.tube i))).a| ≤ 12 ∧
        |(tubeParamsOfTube (section7ReflectTube (F.tube i))).b| ≤ 12 ∧
        |(tubeParamsOfTube (section7ReflectTube (F.tube i))).c| ≤ 2 ∧
        |(tubeParamsOfTube (section7ReflectTube (F.tube i))).d| ≤ 2
    rw [tubeParamsOfTube_section7ReflectTube]
    rcases hparams i with ⟨ha, hb, hc, hd⟩
    exact
      ⟨by simpa [tubeParams] using ha,
        by simpa [tubeParams] using hb,
        by simpa [tubeParams] using hc,
        by simpa [tubeParams] using hd⟩
  · intro C hFrostman r hdr hrOne reference
    have hsource := hFrostman r hdr hrOne reference
    change
      ((Finset.univ.filter fun i : Fin F.card =>
        |(tubeParamsOfTube (section7ReflectTube (F.tube i))).a -
            (tubeParamsOfTube (section7ReflectTube (F.tube reference))).a| ≤ r ∧
        |(tubeParamsOfTube (section7ReflectTube (F.tube i))).b -
            (tubeParamsOfTube (section7ReflectTube (F.tube reference))).b| ≤ r ∧
        |(tubeParamsOfTube (section7ReflectTube (F.tube i))).c -
            (tubeParamsOfTube (section7ReflectTube (F.tube reference))).c| ≤ r ∧
        |(tubeParamsOfTube (section7ReflectTube (F.tube i))).d -
            (tubeParamsOfTube (section7ReflectTube (F.tube reference))).d| ≤ r).card :
          ENNReal) ≤
        C * Kakeya.realRpowENN r 2 * F.enncard
    simpa only [tubeParams, tubeParamsOfTube_section7ReflectTube,
      neg_sub_neg, abs_neg, abs_sub_comm] using hsource
  · intro lambda hYDense
    have hmass :
        reflectedShading.mass = Y.mass := by
      change
        (∑ i : Fin F.card,
          volume (section7Reflection3 '' Y.carrier i)) =
        ∑ i : Fin F.card, volume (Y.carrier i)
      apply Finset.sum_congr rfl
      intro i _
      exact section7Reflection3_volume_image (Y.carrier i)
    have hfamilyMass :
        reflectedFamily.toBodyFamily.mass = F.toBodyFamily.mass := by
      change
        (∑ i : Fin F.card,
          (section7ReflectTube (F.tube i)).volume) =
        ∑ i : Fin F.card, (F.tube i).volume
      apply Finset.sum_congr rfl
      intro i _
      exact section7ReflectTube_volume (F.tube i)
    change
      lambda * reflectedFamily.toBodyFamily.mass ≤
        reflectedShading.mass
    rw [hmass, hfamilyMass]
    exact hYDense
  · intro hwindow p hp
    rcases hp with ⟨i, q, hq, rfl⟩
    have hqWindow : q ∈ horizontalSlab (-1) 0 :=
      hwindow ⟨i, hq⟩
    change -1 ≤ q 2 ∧ q 2 ≤ 0 at hqWindow
    change 0 ≤ -q 2 ∧ -q 2 ≤ 1
    constructor <;> linarith
  · intro W hW
    let Z : Kakeya.Streamlined.TubeShading F :=
      { carrier := fun i => section7Reflection3 '' W.carrier i
        measurable_carrier := fun i =>
          section7Reflection3.toMeasurableEquiv.measurableSet_image.mpr
            (W.measurable_carrier i)
        subset_body := by
          intro i p hp
          rcases hp with ⟨q, hq, rfl⟩
          have hqReflected : q ∈ reflectedShading.carrier i :=
            hW i hq
          rcases hqReflected with ⟨x, hx, rfl⟩
          simpa using Y.subset_body i hx }
    have hZSub : IsSubshading Z Y := by
      intro i p hp
      rcases hp with ⟨q, hq, rfl⟩
      have hqReflected : q ∈ reflectedShading.carrier i :=
        hW i hq
      rcases hqReflected with ⟨x, hx, rfl⟩
      simpa using hx
    refine ⟨Z, hZSub, ?_, ?_⟩
    · intro lambda hWDense
      have hmass : Z.mass = W.mass := by
        change
          (∑ i : Fin F.card,
            volume (section7Reflection3 '' W.carrier i)) =
          ∑ i : Fin F.card, volume (W.carrier i)
        apply Finset.sum_congr rfl
        intro i _
        exact section7Reflection3_volume_image (W.carrier i)
      have hfamilyMass :
          F.toBodyFamily.mass = reflectedFamily.toBodyFamily.mass := by
        change
          (∑ i : Fin F.card, (F.tube i).volume) =
          ∑ i : Fin F.card,
            (section7ReflectTube (F.tube i)).volume
        apply Finset.sum_congr rfl
        intro i _
        exact (section7ReflectTube_volume (F.tube i)).symm
      change lambda * F.toBodyFamily.mass ≤ Z.mass
      rw [hmass, hfamilyMass]
      exact hWDense
    · intro f
      have hunion : Z.union = section7Reflection3 '' W.union := by
        ext p
        constructor
        · rintro ⟨i, q, hq, rfl⟩
          exact ⟨q, ⟨i, hq⟩, rfl⟩
        · rintro ⟨q, ⟨i, hq⟩, rfl⟩
          exact ⟨i, q, hq, rfl⟩
      have htwisted :
          twistedUnion W f.reflected =
            section7Reflection2 '' twistedUnion Z f := by
        ext p
        constructor
        · rintro ⟨q, hq, rfl⟩
          have hRq : section7Reflection3 q ∈ Z.union := by
            rw [hunion]
            exact ⟨q, hq, rfl⟩
          exact
            ⟨twistedProjection f (section7Reflection3 q),
              ⟨section7Reflection3 q, hRq, rfl⟩,
              by
                simpa using
                  (twistedProjection_section7Reflection f
                    (section7Reflection3 q)).symm⟩
        · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
          have hRx : section7Reflection3 x ∈ W.union := by
            have hx' : x ∈ section7Reflection3 '' W.union := by
              rw [← hunion]
              exact hx
            rcases hx' with ⟨q, hq, hqx⟩
            have : section7Reflection3 x = q := by
              rw [← hqx, section7Reflection3_involutive]
            simpa [this] using hq
          exact
            ⟨section7Reflection3 x,
              hRx,
              twistedProjection_section7Reflection f x⟩
      constructor
      · rw [htwisted]
        exact section7Reflection2_volume_image (twistedUnion Z f)
      · intro r
        rw [htwisted]
        have hthick :
            Metric.cthickening r
                (section7Reflection2 '' twistedUnion Z f) =
              section7Reflection2 ''
                Metric.cthickening r (twistedUnion Z f) := by
          exact
            (by
              ext y
              simp only [Metric.mem_cthickening_iff, Set.mem_image]
              constructor
              · intro hy
                refine
                  ⟨section7Reflection2 y, ?_,
                    section7Reflection2_involutive y⟩
                have himage :
                    section7Reflection2 ''
                        (section7Reflection2 '' twistedUnion Z f) =
                      twistedUnion Z f := by
                  rw [← Set.image_comp]
                  simp [Function.comp_def]
                have hdist :=
                  Metric.infEDist_image section7Reflection2.isometry
                    (x := y)
                    (t := section7Reflection2 '' twistedUnion Z f)
                rw [himage] at hdist
                rw [hdist]
                exact hy
              · rintro ⟨x, hx, rfl⟩
                rw [Metric.infEDist_image section7Reflection2.isometry]
                exact hx)
        rw [hthick]
        exact
          section7Reflection2_volume_image
            (Metric.cthickening r (twistedUnion Z f))

end Kakeya.Assouad
