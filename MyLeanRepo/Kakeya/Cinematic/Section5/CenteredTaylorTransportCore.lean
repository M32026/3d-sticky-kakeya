import MyLeanRepo.Kakeya.Cinematic.Section5.CenteredTaylorExtensionProperties
import MyLeanRepo.Kakeya.Cinematic.Section5.RestrictedFamily

/-!
# Cinematic transport for the centered Taylor extension

The concrete Taylor extension uses one physical base point and one
displacement for every source function at a fixed transported point.  This
module turns that common witness into the metric, doubling, and cinematic
curvature estimates required by the strengthened transport statement.
-/

noncomputable section

namespace Kakeya.Cinematic

open C2Function

lemma centeredTaylor_restrictedC2Distance_le_c2Distance
    {I : ParameterInterval} {transport : C2Function → C2Function}
    {f g : C2Function}
    (hf : IsCenteredJetCopy I f (transport f))
    (hg : IsCenteredJetCopy I g (transport g)) :
    restrictedC2Distance I f g ≤
      c2Distance (transport f) (transport g) := by
  have htransport_nonneg :
      0 ≤ c2Distance (transport f) (transport g) :=
    dist_nonneg
  have hvalue :
      dist (restrictedJet f I).1 (restrictedJet g I).1 ≤
        c2Distance (transport f) (transport g) := by
    rw [ContinuousMap.dist_le htransport_nonneg]
    intro x
    rcases hf.1 x with ⟨y, hy, hfy, _, _⟩
    rcases hg.1 x with ⟨z, hz, hgz, _, _⟩
    have hyz : y = z := by
      apply Subtype.ext
      linarith
    subst z
    change dist (f x.1) (g x.1) ≤
      c2Distance (transport f) (transport g)
    rw [← hfy, ← hgz]
    exact (ContinuousMap.dist_apply_le_dist y).trans
      (value_dist_le_c2Distance (transport f) (transport g))
  have hfirst :
      dist (restrictedJet f I).2.1 (restrictedJet g I).2.1 ≤
        c2Distance (transport f) (transport g) := by
    rw [ContinuousMap.dist_le htransport_nonneg]
    intro x
    rcases hf.1 x with ⟨y, hy, _, hfy, _⟩
    rcases hg.1 x with ⟨z, hz, _, hgz, _⟩
    have hyz : y = z := by
      apply Subtype.ext
      linarith
    subst z
    change dist (f.firstDeriv x.1) (g.firstDeriv x.1) ≤
      c2Distance (transport f) (transport g)
    rw [← hfy, ← hgz]
    exact (ContinuousMap.dist_apply_le_dist y).trans
      (firstDeriv_dist_le_c2Distance (transport f) (transport g))
  have hsecond :
      dist (restrictedJet f I).2.2 (restrictedJet g I).2.2 ≤
        c2Distance (transport f) (transport g) := by
    rw [ContinuousMap.dist_le htransport_nonneg]
    intro x
    rcases hf.1 x with ⟨y, hy, _, _, hfy⟩
    rcases hg.1 x with ⟨z, hz, _, _, hgz⟩
    have hyz : y = z := by
      apply Subtype.ext
      linarith
    subst z
    change dist (f.secondDeriv x.1) (g.secondDeriv x.1) ≤
      c2Distance (transport f) (transport g)
    rw [← hfy, ← hgz]
    exact (ContinuousMap.dist_apply_le_dist y).trans
      (secondDeriv_dist_le_c2Distance (transport f) (transport g))
  rw [restrictedC2Distance]
  simp only [Prod.dist_eq]
  exact max_le hvalue (max_le hfirst hsecond)

lemma centeredTaylor_c2Distance_le_three_mul_restrictedC2Distance
    {I : ParameterInterval} {transport : C2Function → C2Function}
    (hcommon : IsCommonCenteredQuadraticJetExtension I transport)
    (f g : C2Function) :
    c2Distance (transport f) (transport g) ≤
      3 * restrictedC2Distance I f g := by
  let d := restrictedC2Distance I f g
  have hd : 0 ≤ d := dist_nonneg
  have h3d : 0 ≤ 3 * d := by positivity
  change dist (C2Function.toJet (transport f))
      (C2Function.toJet (transport g)) ≤ 3 * d
  simp only [C2Function.toJet, Prod.dist_eq]
  apply max_le
  · rw [ContinuousMap.dist_le h3d]
    intro y
    rcases hcommon y with ⟨x, t, ht, hall⟩
    rcases hall f with ⟨hf0, _, _⟩
    rcases hall g with ⟨hg0, _, _⟩
    have h0 := abs_value_sub_le_restrictedC2Distance I f g x
    have h1 := abs_firstDeriv_sub_le_restrictedC2Distance I f g x
    have h2 := abs_secondDeriv_sub_le_restrictedC2Distance I f g x
    have hbound :=
      quadraticTaylorJet_abs_le_two_mul hd ht h0 h1 h2
    change dist (transport f y) (transport g y) ≤ 3 * d
    rw [Real.dist_eq]
    calc
      |transport f y - transport g y| =
          |(f x.1 - g x.1) +
            (f.firstDeriv x.1 - g.firstDeriv x.1) * t +
            ((f.secondDeriv x.1 - g.secondDeriv x.1) / 2) * t ^ 2| := by
              rw [hf0, hg0]
              congr 1
              ring
      _ ≤ 2 * d := hbound.1
      _ ≤ 3 * d := by linarith
  · apply max_le
    · rw [ContinuousMap.dist_le h3d]
      intro y
      rcases hcommon y with ⟨x, t, ht, hall⟩
      rcases hall f with ⟨_, hf1, _⟩
      rcases hall g with ⟨_, hg1, _⟩
      have h0 := abs_value_sub_le_restrictedC2Distance I f g x
      have h1 := abs_firstDeriv_sub_le_restrictedC2Distance I f g x
      have h2 := abs_secondDeriv_sub_le_restrictedC2Distance I f g x
      have hbound :=
        quadraticTaylorJet_abs_le_two_mul hd ht h0 h1 h2
      change dist ((transport f).firstDeriv y)
          ((transport g).firstDeriv y) ≤ 3 * d
      rw [Real.dist_eq]
      calc
        |(transport f).firstDeriv y -
            (transport g).firstDeriv y| =
            |(f.firstDeriv x.1 - g.firstDeriv x.1) +
              (f.secondDeriv x.1 - g.secondDeriv x.1) * t| := by
                rw [hf1, hg1]
                congr 1
                ring
        _ ≤ 2 * d := hbound.2.1
        _ ≤ 3 * d := by linarith
    · rw [ContinuousMap.dist_le h3d]
      intro y
      rcases hcommon y with ⟨x, _, _, hall⟩
      rcases hall f with ⟨_, _, hf2⟩
      rcases hall g with ⟨_, _, hg2⟩
      have h2 := abs_secondDeriv_sub_le_restrictedC2Distance I f g x
      change dist ((transport f).secondDeriv y)
          ((transport g).secondDeriv y) ≤ 3 * d
      rw [Real.dist_eq, hf2, hg2]
      dsimp only [d] at hd h2 ⊢
      linarith

lemma quadraticTaylorJet_inverse_sum_le_two_mul
    {t v₀ v₁ v₂ : ℝ} (ht : |t| ≤ 1 / 2) :
    |v₀ - t * v₁ + (t ^ 2 / 2) * v₂| +
        |v₁ - t * v₂| + |v₂| ≤
      2 * (|v₀| + |v₁| + |v₂|) := by
  have htProduct :
      0 ≤ ((1 / 2 : ℝ) - |t|) * ((1 / 2 : ℝ) + |t|) :=
    mul_nonneg (sub_nonneg.mpr ht) (by positivity)
  have htSqDiv : t ^ 2 / 2 ≤ 1 / 8 := by
    nlinarith [sq_abs t]
  have hvalue :
      |v₀ - t * v₁ + (t ^ 2 / 2) * v₂| ≤
        |v₀| + (1 / 2 : ℝ) * |v₁| + (1 / 8 : ℝ) * |v₂| := by
    calc
      |v₀ - t * v₁ + (t ^ 2 / 2) * v₂| ≤
          |v₀| + |-(t * v₁)| + |(t ^ 2 / 2) * v₂| :=
        abs_add_three _ _ _
      _ = |v₀| + |t| * |v₁| + (t ^ 2 / 2) * |v₂| := by
        have hquad : |t ^ 2 / 2| = t ^ 2 / 2 :=
          abs_of_nonneg (by positivity)
        rw [abs_neg, abs_mul, abs_mul, hquad]
      _ ≤ |v₀| + (1 / 2 : ℝ) * |v₁| +
          (1 / 8 : ℝ) * |v₂| := by
        gcongr
  have hfirst :
      |v₁ - t * v₂| ≤ |v₁| + (1 / 2 : ℝ) * |v₂| := by
    calc
      |v₁ - t * v₂| ≤ |v₁| + |-(t * v₂)| := abs_add_le _ _
      _ = |v₁| + |t| * |v₂| := by rw [abs_neg, abs_mul]
      _ ≤ |v₁| + (1 / 2 : ℝ) * |v₂| := by gcongr
  calc
    |v₀ - t * v₁ + (t ^ 2 / 2) * v₂| +
          |v₁ - t * v₂| + |v₂| ≤
        (|v₀| + (1 / 2 : ℝ) * |v₁| + (1 / 8 : ℝ) * |v₂|) +
          (|v₁| + (1 / 2 : ℝ) * |v₂|) + |v₂| := by
      gcongr
    _ ≤ 2 * (|v₀| + |v₁| + |v₂|) := by
      linarith [abs_nonneg v₀, abs_nonneg v₁, abs_nonneg v₂]

lemma centeredTaylor_sourceJetGap_le_two_mul_transportJetGap
    {I : ParameterInterval} {transport : C2Function → C2Function}
    (hcommon : IsCommonCenteredQuadraticJetExtension I transport)
    (f g : C2Function) (y : UnitPoint) :
    ∃ x : I.LocalPoint,
      jetGap f g x.1 ≤ 2 * jetGap (transport f) (transport g) y := by
  rcases hcommon y with ⟨x, t, ht, hall⟩
  rcases hall f with ⟨hf0, hf1, hf2⟩
  rcases hall g with ⟨hg0, hg1, hg2⟩
  let v₀ := transport f y - transport g y
  let v₁ := (transport f).firstDeriv y - (transport g).firstDeriv y
  let v₂ := (transport f).secondDeriv y - (transport g).secondDeriv y
  have hsecond :
      f.secondDeriv x.1 - g.secondDeriv x.1 = v₂ := by
    dsimp only [v₂]
    rw [hf2, hg2]
  have hfirst :
      f.firstDeriv x.1 - g.firstDeriv x.1 = v₁ - t * v₂ := by
    dsimp only [v₁, v₂]
    rw [hf1, hg1, hf2, hg2]
    ring
  have hvalue :
      f x.1 - g x.1 =
        v₀ - t * v₁ + (t ^ 2 / 2) * v₂ := by
    have hf0' :
        (transport f).value y =
          f.value x.1 + f.firstDeriv x.1 * t +
            (f.secondDeriv x.1 / 2) * t ^ 2 :=
      hf0
    have hg0' :
        (transport g).value y =
          g.value x.1 + g.firstDeriv x.1 * t +
            (g.secondDeriv x.1 / 2) * t ^ 2 :=
      hg0
    dsimp only [v₀, v₁, v₂]
    change f.value x.1 - g.value x.1 =
      (transport f).value y - (transport g).value y -
        t * ((transport f).firstDeriv y -
          (transport g).firstDeriv y) +
        t ^ 2 / 2 * ((transport f).secondDeriv y -
          (transport g).secondDeriv y)
    rw [hf0', hg0', hf1, hg1, hf2, hg2]
    ring
  refine ⟨x, ?_⟩
  rw [jetGap, jetGap, hvalue, hfirst, hsecond]
  exact quadraticTaylorJet_inverse_sum_le_two_mul ht

lemma restricted_iterated_doubling
    {family : Set C2Function} {I : ParameterInterval} {K D : ℝ}
    (hfamily : IsRestrictedCinematicFamily family I K D)
    (hD : 0 ≤ D)
    (f : C2Function) (hf : f ∈ family)
    (r : ℝ) (hr : 0 < r) (n : ℕ) :
    ∃ centers : Set C2Function,
      centers.Finite ∧
        centers ⊆ family ∧
        (centers.ncard : ℝ) ≤ D ^ n ∧
        ∀ g ∈ family, restrictedC2Distance I f g ≤ r →
          ∃ h ∈ centers,
            restrictedC2Distance I h g ≤ r / (2 ^ n) := by
  classical
  induction n with
  | zero =>
      refine ⟨{f}, Set.finite_singleton f,
        Set.singleton_subset_iff.mpr hf, ?_, ?_⟩
      · simp
      · intro g hg hdist
        exact ⟨f, by simp, by simpa using hdist⟩
  | succ n ih =>
      rcases ih with
        ⟨centers_n, hfin_n, hsub_n, hcard_n, hcover_n⟩
      let centersFinset : Finset C2Function := hfin_n.toFinset
      have hchoose :
          ∀ h ∈ centersFinset,
            ∃ centers_h : Set C2Function,
              centers_h.Finite ∧
                centers_h ⊆ family ∧
                (centers_h.ncard : ℝ) ≤ D ∧
                ∀ g ∈ family,
                  restrictedC2Distance I h g ≤ r / (2 ^ n) →
                    ∃ h' ∈ centers_h,
                      restrictedC2Distance I h' g ≤
                        r / (2 ^ (n + 1)) := by
        intro h hh
        have hh_family : h ∈ family :=
          hsub_n (hfin_n.mem_toFinset.mp hh)
        have hrn : 0 < r / (2 ^ n : ℝ) := by positivity
        rcases hfamily.2.1 hh_family (r / (2 ^ n : ℝ)) hrn with
          ⟨centers_h, hfin_h, hsub_h, hcard_h, hcover_h⟩
        refine ⟨centers_h, hfin_h, hsub_h, hcard_h, ?_⟩
        intro g hg hdist
        rcases hcover_h hg hdist with ⟨h', hh', hdist'⟩
        refine ⟨h', hh', ?_⟩
        convert hdist' using 1 <;>
          field_simp [pow_succ] <;> ring
      choose centers_h hfin_h hsub_h hcard_h hcover_h using hchoose
      let selected (h : C2Function) : Finset C2Function :=
        if hh : h ∈ centersFinset
        then (hfin_h h hh).toFinset
        else ∅
      let centersNextFinset : Finset C2Function :=
        centersFinset.biUnion selected
      let centersNext : Set C2Function := centersNextFinset
      have hselected (h : C2Function) (hh : h ∈ centersFinset) :
          selected h = (hfin_h h hh).toFinset := by
        simp [selected, hh]
      have hfin : centersNext.Finite :=
        centersNextFinset.finite_toSet
      have hsub : centersNext ⊆ family := by
        intro x hx
        have hx' : x ∈ centersNextFinset := by exact_mod_cast hx
        rcases Finset.mem_biUnion.mp hx' with ⟨h, hh, hxh⟩
        have hxh' : x ∈ centers_h h hh := by
          rw [hselected h hh] at hxh
          simpa using hxh
        exact hsub_h h hh hxh'
      have hcard :
          (centersNext.ncard : ℝ) ≤ D ^ (n + 1) := by
        have hcardUnion :
            centersNextFinset.card ≤
              ∑ h ∈ centersFinset, (selected h).card :=
          Finset.card_biUnion_le
        have hcardEach :
            ∀ h ∈ centersFinset, ((selected h).card : ℝ) ≤ D := by
          intro h hh
          rw [hselected h hh]
          have hcardEq :
              ((hfin_h h hh).toFinset.card : ℝ) =
                ((centers_h h hh).ncard : ℝ) := by
            norm_cast
            exact
              (Set.ncard_eq_toFinset_card
                (centers_h h hh) (hfin_h h hh)).symm
          rw [hcardEq]
          exact hcard_h h hh
        have hsum :
            (∑ h ∈ centersFinset, (selected h).card : ℝ) ≤
              (centersFinset.card : ℝ) * D := by
          calc
            (∑ h ∈ centersFinset, (selected h).card : ℝ)
                ≤ ∑ h ∈ centersFinset, D :=
              Finset.sum_le_sum hcardEach
            _ = (centersFinset.card : ℝ) * D := by
              simp [Finset.sum_const]
        have hcentersCard :
            (centersFinset.card : ℝ) =
              (centers_n.ncard : ℝ) := by
          exact_mod_cast
            (Set.ncard_eq_toFinset_card centers_n hfin_n).symm
        have hnextCard :
            (centersNext.ncard : ℝ) =
              (centersNextFinset.card : ℝ) := by
          simp [centersNext]
        rw [hnextCard]
        calc
          (centersNextFinset.card : ℝ) ≤
              (∑ h ∈ centersFinset, (selected h).card : ℝ) := by
            exact_mod_cast hcardUnion
          _ ≤ (centersFinset.card : ℝ) * D := hsum
          _ = (centers_n.ncard : ℝ) * D := by
            rw [hcentersCard]
          _ ≤ (D ^ n) * D :=
            mul_le_mul_of_nonneg_right hcard_n hD
          _ = D ^ (n + 1) := by rw [pow_succ]
      have hcover :
          ∀ g ∈ family, restrictedC2Distance I f g ≤ r →
            ∃ h ∈ centersNext,
              restrictedC2Distance I h g ≤
                r / (2 ^ (n + 1)) := by
        intro g hg hdist
        rcases hcover_n g hg hdist with ⟨h, hh, hdist_h⟩
        have hhFinset : h ∈ centersFinset :=
          hfin_n.mem_toFinset.mpr hh
        rcases hcover_h h hhFinset g hg hdist_h with
          ⟨h', hh', hdist'⟩
        have hhNext : h' ∈ centersNext := by
          have hhSelected : h' ∈ selected h := by
            rw [hselected h hhFinset]
            simpa using hh'
          have hhUnion : h' ∈ centersNextFinset :=
            Finset.mem_biUnion.mpr ⟨h, hhFinset, hhSelected⟩
          exact_mod_cast hhUnion
        exact ⟨h', hhNext, hdist'⟩
      exact ⟨centersNext, hfin, hsub, hcard, hcover⟩

lemma centeredTaylor_transport_injOn
    {family : Set C2Function} {K D : ℝ}
    (hK : 1 ≤ K) (hfamily : IsCinematicFamily family K D)
    (I : ParameterInterval) (transport : C2Function → C2Function)
    (hcopy : ∀ f ∈ family, IsCenteredJetCopy I f (transport f)) :
    Set.InjOn transport family := by
  intro f hf g hg hfg
  have himage :
      c2Distance (transport f) (transport g) = 0 := by
    rw [hfg]
    exact dist_self _
  have hlocal_le :
      restrictedC2Distance I f g ≤
        c2Distance (transport f) (transport g) :=
    centeredTaylor_restrictedC2Distance_le_c2Distance
      (hcopy f hf) (hcopy g hg)
  have hlocal_nonneg : 0 ≤ restrictedC2Distance I f g :=
    dist_nonneg
  have hlocal : restrictedC2Distance I f g = 0 := by
    rw [himage] at hlocal_le
    linarith
  have hglobal_le :
      c2Distance f g ≤ 3 * K * restrictedC2Distance I f g :=
    c2Distance_le_three_mul_restrictedC2Distance
      hK hfamily hf hg I
  have hglobal_nonneg : 0 ≤ c2Distance f g :=
    dist_nonneg
  have hglobal : c2Distance f g = 0 := by
    rw [hlocal] at hglobal_le
    linarith
  exact dist_eq_zero.mp hglobal

theorem centeredTaylor_image_isCinematicFamily
    {family : Set C2Function} {K D : ℝ}
    (hK : 1 ≤ K) (hD : 1 ≤ D)
    (hfamily : IsCinematicFamily family K D)
    (I : ParameterInterval) (transport : C2Function → C2Function)
    (hcopy : ∀ f ∈ family, IsCenteredJetCopy I f (transport f))
    (hcommon : IsCommonCenteredQuadraticJetExtension I transport) :
    IsCinematicFamily
      (transport '' family)
      (12 * K)
      ((D * Real.rpow (6 * K)
        (Real.log D / Real.log 2)) ^ 3) := by
  let D₀ : ℝ :=
    D * Real.rpow (6 * K) (Real.log D / Real.log 2)
  have hKpos : 0 < K := by linarith
  have hDpos : 0 < D := by linarith
  have hD₀pos : 0 < D₀ := by
    dsimp only [D₀]
    exact mul_pos hDpos (Real.rpow_pos_of_pos (by positivity) _)
  have hrestricted :
      IsRestrictedCinematicFamily family I K D₀ := by
    dsimp only [D₀]
    exact isRestrictedCinematicFamily_of_global hK hD hfamily I
  have hmetricLower :
      ∀ f ∈ family, ∀ g ∈ family,
        restrictedC2Distance I f g ≤
          c2Distance (transport f) (transport g) := by
    intro f hf g hg
    exact centeredTaylor_restrictedC2Distance_le_c2Distance
      (hcopy f hf) (hcopy g hg)
  have hmetricUpper :
      ∀ f ∈ family, ∀ g ∈ family,
        c2Distance (transport f) (transport g) ≤
          3 * restrictedC2Distance I f g := by
    intro f _ g _
    exact
      centeredTaylor_c2Distance_le_three_mul_restrictedC2Distance
        hcommon f g
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨f, hf, rfl⟩ _ ⟨g, hg, rfl⟩
    calc
      c2Distance (transport f) (transport g) ≤
          3 * restrictedC2Distance I f g :=
        hmetricUpper f hf g hg
      _ ≤ 3 * K := by
        gcongr
        exact hrestricted.1 hf hg
      _ ≤ 12 * K := by nlinarith
  · rintro _ ⟨f, hf, rfl⟩ r hr
    rcases restricted_iterated_doubling
        hrestricted hD₀pos.le f hf r hr 3 with
      ⟨centers, hcentersFinite, hcentersSub,
        hcentersCard, hcentersCover⟩
    let transportedCenters : Set C2Function := transport '' centers
    refine ⟨transportedCenters,
      hcentersFinite.image transport, ?_, ?_, ?_⟩
    · intro H hH
      rcases hH with ⟨h, hh, rfl⟩
      exact ⟨h, hcentersSub hh, rfl⟩
    · have hcardImage :
          (transport '' centers).ncard ≤ centers.ncard :=
        Set.ncard_image_le hcentersFinite
      dsimp only [transportedCenters]
      calc
        ((transport '' centers).ncard : ℝ) ≤
            (centers.ncard : ℝ) := by
          exact_mod_cast hcardImage
        _ ≤ D₀ ^ 3 := hcentersCard
        _ = (D * Real.rpow (6 * K)
            (Real.log D / Real.log 2)) ^ 3 := by
          rfl
    · rintro _ ⟨g, hg, rfl⟩ hdist
      have hlocal :
          restrictedC2Distance I f g ≤ r :=
        (hmetricLower f hf g hg).trans hdist
      rcases hcentersCover g hg hlocal with
        ⟨h, hh, hhg⟩
      refine ⟨transport h, ⟨h, hh, rfl⟩, ?_⟩
      calc
        c2Distance (transport h) (transport g) ≤
            3 * restrictedC2Distance I h g :=
          hmetricUpper h (hcentersSub hh) g hg
        _ ≤ 3 * (r / (2 ^ (3 : ℕ))) := by
          gcongr
        _ ≤ r / 2 := by
          norm_num
          linarith
  · rintro _ ⟨f, hf, rfl⟩ _ ⟨g, hg, rfl⟩ y
    rcases
        centeredTaylor_sourceJetGap_le_two_mul_transportJetGap
          hcommon f g y with
      ⟨x, hsourceGap⟩
    have hsourceCinematic :
        K⁻¹ * restrictedC2Distance I f g ≤ jetGap f g x.1 :=
      hrestricted.2.2 hf hg x
    have himageUpper :
        c2Distance (transport f) (transport g) ≤
          3 * restrictedC2Distance I f g :=
      hmetricUpper f hf g hg
    have htransportGapNonneg :
        0 ≤ jetGap (transport f) (transport g) y := by
      simp only [jetGap]
      positivity
    calc
      (12 * K)⁻¹ * c2Distance (transport f) (transport g) ≤
          (12 * K)⁻¹ *
            (3 * restrictedC2Distance I f g) := by
        gcongr
      _ = (1 / 4 : ℝ) *
          (K⁻¹ * restrictedC2Distance I f g) := by
        field_simp [hKpos.ne']
        ring
      _ ≤ (1 / 4 : ℝ) * jetGap f g x.1 := by
        gcongr
      _ ≤ (1 / 4 : ℝ) *
          (2 * jetGap (transport f) (transport g) y) := by
        gcongr
      _ ≤ jetGap (transport f) (transport g) y := by
        nlinarith

theorem centeredTaylor_quadratic_cinematic_transport :
    CenteredTaylorQuadraticCinematicTransportStatement := by
  intro K D hK hD family hfamily I hlen hshort
  let transport : C2Function → C2Function :=
    fun f => taylorExtend f I K hK hlen hshort
  have hcommon :
      IsCommonCenteredQuadraticJetExtension I transport := by
    simpa only [transport] using
      taylorExtend_commonQuadraticJetExtension I K hK hlen hshort
  have hcopy :
      ∀ f ∈ family, IsCenteredJetCopy I f (transport f) := by
    intro f _
    simpa only [transport] using
      taylorExtend_isCenteredJetCopy f I K hK hlen hshort
  have hquadratic :
      ∀ f ∈ family,
        IsCenteredQuadraticJetExtension I f (transport f) := by
    intro f _
    exact
      commonCenteredQuadraticJetExtension_implies_pointwise
        hcommon f
  have hmetric :
      ∀ f ∈ family, ∀ g ∈ family,
        restrictedC2Distance I f g ≤
            c2Distance (transport f) (transport g) ∧
          c2Distance (transport f) (transport g) ≤
            3 * restrictedC2Distance I f g := by
    intro f hf g hg
    exact
      ⟨centeredTaylor_restrictedC2Distance_le_c2Distance
          (hcopy f hf) (hcopy g hg),
        centeredTaylor_c2Distance_le_three_mul_restrictedC2Distance
          hcommon f g⟩
  exact
    ⟨transport,
      centeredTaylor_transport_injOn hK hfamily I transport hcopy,
      centeredTaylor_image_isCinematicFamily
        hK hD hfamily I transport hcopy hcommon,
      hcopy, hquadratic, hmetric⟩

end Kakeya.Cinematic
