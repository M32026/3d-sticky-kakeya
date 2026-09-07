import MyLeanRepo.Kakeya.Cinematic.Section5.LocalAssembly.TwoEndsBridge
import MyLeanRepo.Kakeya.Cinematic.Section5.LocalAssembly.Infrastructure

/-!
# Pointwise two-ends localization with fine rectangle assignment

This closed module applies the two-ends bridge **pointwise** to the set of
functions whose graph neighborhoods contain a given point `p`, then invokes
the fine rectangle assignment to produce a curvilinear rectangle through `p`
that is tangent to a retained subfamily.

## Scale conventions

- `δ_base`: graph-neighborhood (metric) scale from the multiplicity hypothesis.
- `δ_vert := (1 + L) * δ_base`: vertical scale used for the fine rectangle,
  where `L` is the uniform first-derivative bound of the cinematic family.
- `t`: C² localization scale from the metric two-ends selection.
- `t_fine := 4 * t`: scale passed to `FineRectangleAssignment`, so that the
  tangency two-ends output `Delta ≤ 4 * t` automatically satisfies `Delta ≤ t_fine`.
- `t_fine := 4 * t` is permitted at every positive scale; the rectangle
  construction itself does not require `t_fine ≤ 1`.
-/

noncomputable section

open Set MeasureTheory Metric

attribute [local instance] Classical.propDecidable

namespace Kakeya.Cinematic

/-- The subfamily of `F` whose `δ`-graph neighborhoods contain `p`. -/
def functionsNearPoint (F : FiniteFunctionFamily) (δ : ℝ)
    (p : ℝ × ℝ) : Finset C2Function :=
  F.toFinset.filter (fun f => p ∈ graphNeighborhood f δ)

lemma functionsNearPoint_card_eq_multiplicity
    {F : FiniteFunctionFamily} {δ : ℝ} {p : ℝ × ℝ} :
    ((functionsNearPoint F δ p).card : ℝ) = multiplicity F δ p := by
  unfold functionsNearPoint multiplicity
  have h : ∑ f ∈ F.toFinset, (graphNeighborhood f δ).indicator (fun _ => (1 : ℝ)) p =
      ∑ f ∈ F.toFinset, if p ∈ graphNeighborhood f δ then (1 : ℝ) else 0 := by
    apply Finset.sum_congr rfl
    intro f _
    simp [Set.indicator_apply]
    <;> split_ifs <;> norm_num
  rw [h]
  have h2 : ((F.toFinset.filter (fun f => p ∈ graphNeighborhood f δ)).card : ℝ) =
      ∑ f ∈ F.toFinset, if p ∈ graphNeighborhood f δ then (1 : ℝ) else 0 := by
    rw [Finset.sum_ite] <;> simp
  exact h2

lemma multiplicity_le_family_card
    (F : FiniteFunctionFamily) (δ : ℝ) (p : ℝ × ℝ) :
    multiplicity F δ p ≤ (F.card : ℝ) := by
  rw [← functionsNearPoint_card_eq_multiplicity]
  have hcard :
      (functionsNearPoint F δ p).card ≤ F.toFinset.card :=
    Finset.card_filter_le _ _
  have htoFinset : F.toFinset.card = F.card := by
    change F.finite.toFinset.card = F.carrier.ncard
    exact
      (Set.ncard_eq_toFinset_card F.carrier F.finite).symm
  rw [htoFinset] at hcard
  exact_mod_cast hcard

lemma functionsNearPoint_nonempty
    {F : FiniteFunctionFamily} {δ : ℝ} {p : ℝ × ℝ} {μ : ℕ}
    (hmu : 0 < μ)
    (hmult : (μ : ℝ) ≤ multiplicity F δ p) :
    (functionsNearPoint F δ p).Nonempty := by
  have h1 : (μ : ℝ) ≤ ((functionsNearPoint F δ p).card : ℝ) := by
    rw [functionsNearPoint_card_eq_multiplicity]; exact hmult
  have h2 : 0 < (functionsNearPoint F δ p).card := by
    have h3 : (μ : ℝ) ≤ ((functionsNearPoint F δ p).card : ℝ) := h1
    have h4 : (μ : ℝ) > 0 := by exact_mod_cast hmu
    exact_mod_cast (lt_of_lt_of_le h4 h3)
  exact Finset.card_pos.mp h2

lemma measurableSet_functionsNearPoint_eq
    (F : FiniteFunctionFamily) (delta : ℝ) (S : Finset C2Function) :
    MeasurableSet {p : ℝ × ℝ | functionsNearPoint F delta p = S} := by
  by_cases hsub : S ⊆ F.toFinset
  · have h_eq :
        {p : ℝ × ℝ | functionsNearPoint F delta p = S} =
          (⋂ f ∈ (S : Set C2Function), graphNeighborhood f delta) ∩
            (⋂ f ∈
                ((F.toFinset \ S : Finset C2Function) : Set C2Function),
              (graphNeighborhood f delta)ᶜ) := by
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter,
        Set.mem_compl_iff, Finset.mem_sdiff, Finset.mem_coe]
      constructor
      · intro h
        constructor
        · intro f hfS
          have hfnear : f ∈ functionsNearPoint F delta p := by
            rw [h]
            exact hfS
          exact (Finset.mem_filter.mp hfnear).2
        · intro f hfDiff hmem
          have hfnear : f ∈ functionsNearPoint F delta p :=
            Finset.mem_filter.mpr ⟨hfDiff.1, hmem⟩
          rw [h] at hfnear
          exact hfDiff.2 hfnear
      · rintro ⟨hin, hout⟩
        ext f
        constructor
        · intro hfnear
          by_contra hfnS
          exact
            (hout f ⟨(Finset.mem_filter.mp hfnear).1, hfnS⟩)
              (Finset.mem_filter.mp hfnear).2
        · intro hfS
          exact Finset.mem_filter.mpr ⟨hsub hfS, hin f hfS⟩
    rw [h_eq]
    apply MeasurableSet.inter
    · exact S.measurableSet_biInter fun f _ =>
        measurableSet_graphNeighborhood f delta
    · exact (F.toFinset \ S).measurableSet_biInter fun f _ =>
        (measurableSet_graphNeighborhood f delta).compl
  · have h_empty :
        {p : ℝ × ℝ | functionsNearPoint F delta p = S} = ∅ := by
      ext p
      constructor
      · intro h
        exfalso
        apply hsub
        intro f hfS
        have hfnear : f ∈ functionsNearPoint F delta p := by
          rw [h]
          exact hfS
        exact (Finset.mem_filter.mp hfnear).1
      · intro h
        exact False.elim h
    rw [h_empty]
    exact MeasurableSet.empty

lemma measurableSet_functionsNearPoint_label_eq
    {ι : Type*} [DecidableEq ι]
    (F : FiniteFunctionFamily) (delta : ℝ)
    (label : Finset C2Function → ι) (value : ι) :
    MeasurableSet
      {p : ℝ × ℝ |
        label (functionsNearPoint F delta p) = value} := by
  let candidates : Finset (Finset C2Function) :=
    F.toFinset.powerset
  let chosen :=
    candidates.filter fun S => label S = value
  have h_eq :
      {p : ℝ × ℝ |
          label (functionsNearPoint F delta p) = value} =
        ⋃ S ∈ (chosen : Set (Finset C2Function)),
          {p : ℝ × ℝ | functionsNearPoint F delta p = S} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_coe]
    constructor
    · intro hp
      let S := functionsNearPoint F delta p
      have hS_sub : S ⊆ F.toFinset :=
        Finset.filter_subset _ _
      have hS_candidates : S ∈ candidates := by
        simp [candidates, Finset.mem_powerset, hS_sub]
      have hS_chosen : S ∈ chosen := by
        rw [Finset.mem_filter]
        exact ⟨hS_candidates, by simpa [S] using hp⟩
      exact ⟨S, hS_chosen, rfl⟩
    · rintro ⟨S, hS, hEq⟩
      have hlabel : label S = value :=
        (Finset.mem_filter.mp hS).2
      rw [hEq]
      exact hlabel
  rw [h_eq]
  exact chosen.measurableSet_biUnion fun S _ =>
    measurableSet_functionsNearPoint_eq F delta S

lemma measurableSet_functionsNearPoint_label_mem
    {ι : Type*}
    (F : FiniteFunctionFamily) (delta : ℝ)
    (label : Finset C2Function → ι) (values : Set ι) :
    MeasurableSet
      {p : ℝ × ℝ |
        label (functionsNearPoint F delta p) ∈ values} := by
  let candidates : Finset (Finset C2Function) :=
    F.toFinset.powerset
  let chosen :=
    candidates.filter fun S => label S ∈ values
  have h_eq :
      {p : ℝ × ℝ |
          label (functionsNearPoint F delta p) ∈ values} =
        ⋃ S ∈ (chosen : Set (Finset C2Function)),
          {p : ℝ × ℝ | functionsNearPoint F delta p = S} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_coe]
    constructor
    · intro hp
      let S := functionsNearPoint F delta p
      have hS_sub : S ⊆ F.toFinset :=
        Finset.filter_subset _ _
      have hS_candidates : S ∈ candidates := by
        simp [candidates, Finset.mem_powerset, hS_sub]
      have hS_chosen : S ∈ chosen := by
        rw [Finset.mem_filter]
        exact ⟨hS_candidates, by simpa [S] using hp⟩
      exact ⟨S, hS_chosen, rfl⟩
    · rintro ⟨S, hS, hEq⟩
      have hlabel : label S ∈ values :=
        (Finset.mem_filter.mp hS).2
      rw [hEq]
      exact hlabel
  rw [h_eq]
  exact chosen.measurableSet_biUnion fun S _ =>
    measurableSet_functionsNearPoint_eq F delta S

/-- Construct a `FiniteFunctionFamily` from a `Finset C2Function`. -/
def finsetToFFF (s : Finset C2Function) : FiniteFunctionFamily :=
  { carrier := (s : Set C2Function)
    finite := by exact_mod_cast s.finite_toSet }

/--
**Inner lemma: fine rectangle from two-ends output.**

Given the output of the two-ends bridge applied to the pointwise family,
produce a fine rectangle through `p` tangent to every `f ∈ H`.

All scale conversions are explicit:
- `δ_vert = (1+L)*δ_base` handles metric→vertical conversion.
- `t_fine = 4*t` handles `Delta ≤ 4*t` → `Delta ≤ t_fine`.
-/
lemma fine_rectangle_from_two_ends
    (hFine : FineRectangleAssignmentStatement)
    {K D : ℝ} (hK : 1 ≤ K) (hD : 1 ≤ D)
    {family : Set C2Function} (hfamily : IsCinematicFamily family K D)
    {F : FiniteFunctionFamily} (hF : F.carrier ⊆ family)
    {I : ParameterInterval} (hI : I.IsControlled K)
    {δ_base δ_vert t Delta t_fine : ℝ}
    (hδ_base_pos : 0 < δ_base)
    (L : ℝ) (hL_nonneg : 0 ≤ L)
    (hbounds : ∀ f ∈ family, ∀ z : UnitPoint, |f.firstDeriv z| ≤ L)
    (hδ_vert_eq : δ_vert = (1 + L) * δ_base)
    (hδ_vert_pos : 0 < δ_vert)
    (hδ_vert_le_t : δ_vert ≤ t)
    (hδ_vert_le_Delta : δ_vert ≤ Delta)
    (hDelta_le_tfine : Delta ≤ t_fine)
    (ht_fine_eq : t_fine = 4 * t)
    {μ : ℕ} (hmu : 0 < μ)
    {p : UnitPoint × ℝ}
    (hp_centered : p.1 ∈ I.centeredCarrier (1 / 8))
    (center : C2Function)
    (G H : FiniteFunctionFamily)
    (k : C2Function)
    (hG_sub_F : G.carrier ⊆ F.carrier ∩ c2Ball center t)
    (hH : H.carrier = G.carrier ∩ {f | tangencyParameterOn I f k ≤ Delta})
    (hk_in_H : k ∈ H.carrier)
    (hH_graph : ∀ f ∈ H.carrier,
      ((p.1 : ℝ), p.2) ∈ graphNeighborhood f δ_base) :
    ∃ (C_R : ℝ)
      (R : CurvilinearRectangle δ_vert (C_R * t_fine * Delta / δ_vert)),
      9216 * K^2 ≤ C_R ∧
      R.interval.midpoint = (p.1 : ℝ) ∧
      p ∈ R.carrier ∧
      R.IsOverCentralQuarterOf I ∧
      ∀ f ∈ H.carrier, R.IsLambdaTangent f 5 := by
  let p' : ℝ × ℝ := ((p.1 : ℝ), p.2)
  have hp1 : p'.1 ∈ unitInterval := p.1.property

  -- Vertical closeness for k
  have hk_graph : p' ∈ graphNeighborhood k δ_base := hH_graph k hk_in_H
  have hk_in_G : k ∈ G.carrier := by rw [hH] at hk_in_H; exact hk_in_H.1
  have hk_in_F : k ∈ F.carrier := (hG_sub_F hk_in_G).1
  have hk_in_family : k ∈ family := hF hk_in_F
  have hk_vert : |p.2 - k p.1| ≤ δ_vert := by
    rw [hδ_vert_eq]
    exact localAssembly_graphNeighborhood_to_vertical
      (fun z => hbounds k hk_in_family z) hp1 hk_graph

  -- Vertical closeness for all f ∈ H
  have hH_vert : ∀ f ∈ H.carrier, |p.2 - f p.1| ≤ δ_vert := by
    intro f hf
    have hf_in_G : f ∈ G.carrier := by rw [hH] at hf; exact hf.1
    have hf_in_F : f ∈ F.carrier := (hG_sub_F hf_in_G).1
    have hf_in_family : f ∈ family := hF hf_in_F
    rw [hδ_vert_eq]
    exact localAssembly_graphNeighborhood_to_vertical
      (fun z => hbounds f hf_in_family z) hp1 (hH_graph f hf)

  -- c2Distance bounds: ≤ 2*t ≤ 6*t_fine
  have hH_dist : ∀ f ∈ H.carrier, c2Distance f k ≤ 6 * t_fine := by
    intro f hf
    have hf_in_G : f ∈ G.carrier := by rw [hH] at hf; exact hf.1
    have hk_in_G : k ∈ G.carrier := by rw [hH] at hk_in_H; exact hk_in_H.1
    have hG_ball : G.carrier ⊆ c2Ball center t := by
      intro x hx; exact (hG_sub_F hx).2
    have hf_ball : f ∈ c2Ball center t := hG_ball hf_in_G
    have hk_ball : k ∈ c2Ball center t := hG_ball hk_in_G
    have h : c2Distance f k ≤ 2 * t :=
      localAssembly_dist_le_two_mul_of_mem_ball hf_ball hk_ball
    rw [ht_fine_eq]; linarith

  -- Tangency parameter bounds
  have hH_tangency : ∀ f ∈ H.carrier, tangencyParameterOn I f k ≤ Delta := by
    intro f hf
    rw [hH] at hf
    exact hf.2

  -- Apply FineRectangleAssignment
  rcases hFine K D hK hD with ⟨C_R, hC_R_large, hFine_main⟩
  have hH_sub_family : H.carrier ⊆ family := by
    intro f hf
    have h1 : f ∈ G.carrier := by rw [hH] at hf; exact hf.1
    have h2 : f ∈ F.carrier := (hG_sub_F h1).1
    exact hF h2

  have h_main_result := hFine_main family hfamily I hI
    δ_vert t_fine Delta
    hδ_vert_pos hδ_vert_le_Delta hDelta_le_tfine
    p hp_centered
    k hk_in_family hk_vert
    H hH_sub_family
    (by intro f hf
        exact ⟨hH_dist f hf, hH_tangency f hf, hH_vert f hf⟩)

  rcases h_main_result with
    ⟨R, _hR_function, hR_midpoint, hR_p, hR_over, hR_tangent⟩
  exact
    ⟨C_R, R, hC_R_large, hR_midpoint, hR_p, hR_over, hR_tangent⟩

/--
Self-tangency parameter is zero: `tangencyParameterOn I f f = 0`.
-/
lemma tangencyParameterOn_self (I : ParameterInterval) (f : C2Function) :
    tangencyParameterOn I f f = 0 := by
  let midpoint : UnitPoint := ⟨I.midpoint, by
    simp only [unitInterval, Set.mem_Icc, ParameterInterval.midpoint]
    constructor <;> linarith [I.left_mem.1, I.left_mem.2,
      I.right_mem.1, I.right_mem.2, I.left_le_right]⟩
  have hmid : midpoint ∈ I.centeredCarrier (1 / 2) := by
    have h_coe : (midpoint : ℝ) = I.midpoint := by rfl
    simp only [ParameterInterval.centeredCarrier, Set.mem_setOf_eq]
    have h : |(midpoint : ℝ) - I.midpoint| ≤ (1 / 2 : ℝ) * I.length / 2 := by
      rw [h_coe, sub_self, abs_zero]
      have hlen : 0 ≤ I.length := I.length_nonneg
      positivity
    exact h
  have h0_in_set : (0 : ℝ) ∈ {r : ℝ | ∃ x ∈ I.centeredCarrier (1 / 2),
      r = |f x - f x| + |f.firstDeriv x - f.firstDeriv x|} := by
    refine ⟨midpoint, hmid, ?_⟩
    simp [sub_self, abs_zero] <;> ring
  have h_bdd : BddBelow {r : ℝ | ∃ x ∈ I.centeredCarrier (1 / 2),
      r = |f x - f x| + |f.firstDeriv x - f.firstDeriv x|} := by
    use 0
    intro r hr
    rcases hr with ⟨x, _, rfl⟩
    simp [abs_nonneg]
    <;> positivity
  have h_csInf_le_0 : tangencyParameterOn I f f ≤ 0 :=
    csInf_le h_bdd h0_in_set
  have h0_le_csInf : 0 ≤ tangencyParameterOn I f f :=
    localAssembly_tangencyParameterOn_nonneg I f f
  linarith

/--
**Pointwise fine rectangle existence (PYZ Lemma 41 + two-ends).**

Applies two-ends to the pointwise family and then invokes
`fine_rectangle_from_two_ends`.

Returns the two-ends output together with a fine rectangle at scale
`t_fine = 4 * t`.

Requires `hδ_vert_le_K : (1 + L) * δ_base ≤ K` so that the vertical scale
is within the diameter bound for the two-ends selection.
-/
lemma pointwise_fine_rectangle_exists_with_certificate
    (hTwoEnds : TwoEndsSelectionStatement)
    (hTangencyTwoEnds : TangencyTwoEndsSelectionStatement)
    (hFine : FineRectangleAssignmentStatement)
    {K D C_KT lambda epsilon : ℝ}
    (hK : 1 ≤ K) (hD : 1 ≤ D)
    (hC_KT : 1 ≤ C_KT) (hlambda : 1 ≤ lambda)
    {family : Set C2Function} (hfamily : IsCinematicFamily family K D)
    {F : FiniteFunctionFamily} (hF : F.carrier ⊆ family)
    (hepsilon : 0 < epsilon)
    {I : ParameterInterval} (hI : I.IsControlled K)
    {δ_base : ℝ} (hδ_base_pos : 0 < δ_base)
    (hδ_base_le_K : δ_base ≤ K)
    {μ : ℕ} (hmu : 0 < μ)
    {p : UnitPoint × ℝ}
    (hp_centered : p.1 ∈ I.centeredCarrier (1 / 8))
    (hmult : (μ : ℝ) ≤ multiplicity F δ_base ((p.1 : ℝ), p.2))
    (L : ℝ) (hL_nonneg : 0 ≤ L)
    (hbounds : ∀ f ∈ family, ∀ z : UnitPoint, |f.firstDeriv z| ≤ L)
    (hδ_vert_le_K : (1 + L) * δ_base ≤ K) :
    ∃ (δ_vert t Delta : ℝ) (center k : C2Function)
      (G H : FiniteFunctionFamily),
      δ_vert = (1 + L) * δ_base ∧
      δ_vert ≤ t ∧ t ≤ K ∧
      δ_vert ≤ Delta ∧ Delta ≤ 4 * t ∧
      G.carrier ⊆ F.carrier ∩ c2Ball center t ∧
      H.carrier = G.carrier ∩ {f | tangencyParameterOn I f k ≤ Delta} ∧
      k ∈ H.carrier ∧
      (∀ f ∈ H.carrier, ((p.1 : ℝ), p.2) ∈ graphNeighborhood f δ_base) ∧
      TwoEndsCertificate I δ_vert K epsilon epsilon t Delta
        (finsetToFFF
          (functionsNearPoint F δ_base ((p.1 : ℝ), p.2)))
        G H center k ∧
      ∃ (t_fine C_R : ℝ)
        (R : CurvilinearRectangle δ_vert (C_R * t_fine * Delta / δ_vert)),
        t_fine = 4 * t ∧
        9216 * K^2 ≤ C_R ∧
        R.interval.midpoint = (p.1 : ℝ) ∧
        p ∈ R.carrier ∧
        R.IsOverCentralQuarterOf I ∧
        ∀ f ∈ H.carrier, R.IsLambdaTangent f 5 := by
  let p' : ℝ × ℝ := ((p.1 : ℝ), p.2)
  let S := functionsNearPoint F δ_base p'
  let S_FFF := finsetToFFF S

  -- S is nonempty
  have hS_nonempty : S.Nonempty := functionsNearPoint_nonempty hmu hmult
  have hS_FFF_nonempty : S_FFF.carrier.Nonempty := by
    exact_mod_cast hS_nonempty

  -- S has diameter ≤ K (since S ⊆ F ⊆ family and family has diameter ≤ K)
  have hS_diameter : S_FFF.DiameterLE K := by
    intro f hf g hg
    have hf_F : f ∈ F.carrier := by
      have h1 : f ∈ S_FFF.carrier := hf
      have h2 : f ∈ S := by exact_mod_cast h1
      have h3 : f ∈ F.toFinset := (Finset.mem_filter.mp h2).1
      exact F.finite.mem_toFinset.mp h3
    have hg_F : g ∈ F.carrier := by
      have h1 : g ∈ S_FFF.carrier := hg
      have h2 : g ∈ S := by exact_mod_cast h1
      have h3 : g ∈ F.toFinset := (Finset.mem_filter.mp h2).1
      exact F.finite.mem_toFinset.mp h3
    exact hfamily.1 (hF hf_F) (hF hg_F)

  -- S_FFF.carrier ⊆ F.carrier
  have hS_sub_F : S_FFF.carrier ⊆ F.carrier := by
    intro f hf
    have h2 : f ∈ S := by exact_mod_cast hf
    have h3 : f ∈ F.toFinset := (Finset.mem_filter.mp h2).1
    exact F.finite.mem_toFinset.mp h3

  -- δ_vert
  let δ_vert := (1 + L) * δ_base
  have hδ_vert_pos : 0 < δ_vert := by
    have h1 : 0 < 1 + L := by linarith
    positivity

  -- Apply two-ends bridge with delta = δ_vert, diameter = K
  rcases localAssembly_two_ends_bridge_with_certificate
      hTwoEnds hTangencyTwoEnds
      hepsilon hepsilon hδ_vert_pos hδ_vert_le_K I S_FFF
      hS_FFF_nonempty hS_diameter with
    ⟨t, center, G, Delta, k, H, hcertificate⟩
  have hδ_vert_le_t := hcertificate.delta_le_t
  have ht_le_K := hcertificate.t_le_diameter
  have hG_sub_S := hcertificate.metric_subset
  have hδ_vert_le_Delta := hcertificate.delta_le_Delta
  have hDelta_le_4t := hcertificate.Delta_le_four_t
  have hk_in_G := hcertificate.tangencyCenter_mem
  have hH_eq := hcertificate.tangencyFiber_eq

  -- G ⊆ F.carrier ∩ c2Ball center t
  have hG_sub_F : G.carrier ⊆ F.carrier ∩ c2Ball center t := by
    intro f hf
    have h1 : f ∈ S_FFF.carrier ∩ c2Ball center t := hG_sub_S hf
    have h2 : f ∈ S_FFF.carrier := h1.1
    have h3 : f ∈ c2Ball center t := h1.2
    have h4 : f ∈ F.carrier := hS_sub_F h2
    exact ⟨h4, h3⟩

  -- k ∈ H.carrier (needs tangencyParameterOn I k k = 0 ≤ Delta)
  have h_tang_self : tangencyParameterOn I k k = 0 :=
    tangencyParameterOn_self I k
  have hDelta_nonneg : 0 ≤ Delta := by
    have h : 0 < δ_vert := hδ_vert_pos
    linarith [hδ_vert_le_Delta]
  have hk_in_H : k ∈ H.carrier := by
    rw [hH_eq]
    have h_tang_le : tangencyParameterOn I k k ≤ Delta := by
      rw [h_tang_self]
      linarith
    exact ⟨hk_in_G, h_tang_le⟩

  -- H graph neighborhood membership (since H ⊆ G ⊆ S)
  have hH_graph : ∀ f ∈ H.carrier, p' ∈ graphNeighborhood f δ_base := by
    intro f hf
    have h1 : f ∈ G.carrier := by
      rw [hH_eq] at hf; exact hf.1
    have h2 : f ∈ S_FFF.carrier := (hG_sub_S h1).1
    have h3 : f ∈ S := by exact_mod_cast h2
    have h4 : p' ∈ graphNeighborhood f δ_base := by
      simp only [S, functionsNearPoint, Finset.mem_filter] at h3
      exact h3.2
    exact h4

  let t_fine := 4 * t
  have ht_fine_eq : t_fine = 4 * t := by rfl
  have hDelta_le_tfine : Delta ≤ t_fine := by
    rw [ht_fine_eq]
    exact hDelta_le_4t

  rcases fine_rectangle_from_two_ends hFine hK hD hfamily hF hI
      hδ_base_pos L hL_nonneg hbounds rfl hδ_vert_pos
      hδ_vert_le_t hδ_vert_le_Delta hDelta_le_tfine ht_fine_eq
      hmu hp_centered center G H k hG_sub_F hH_eq hk_in_H hH_graph
    with
      ⟨C_R, R, hC_R, hR_midpoint, hR_p, hR_over, hR_tangent⟩

  refine ⟨δ_vert, t, Delta, center, k, G, H, ?_⟩
  exact ⟨rfl, hδ_vert_le_t, ht_le_K, hδ_vert_le_Delta, hDelta_le_4t,
    hG_sub_F, hH_eq, hk_in_H, hH_graph, hcertificate,
    ⟨t_fine, C_R, R, rfl, hC_R, hR_midpoint, hR_p,
      hR_over, hR_tangent⟩⟩

lemma pointwise_fine_rectangle_exists
    (hTwoEnds : TwoEndsSelectionStatement)
    (hTangencyTwoEnds : TangencyTwoEndsSelectionStatement)
    (hFine : FineRectangleAssignmentStatement)
    {K D C_KT lambda epsilon : ℝ}
    (hK : 1 ≤ K) (hD : 1 ≤ D)
    (hC_KT : 1 ≤ C_KT) (hlambda : 1 ≤ lambda)
    {family : Set C2Function} (hfamily : IsCinematicFamily family K D)
    {F : FiniteFunctionFamily} (hF : F.carrier ⊆ family)
    (hepsilon : 0 < epsilon)
    {I : ParameterInterval} (hI : I.IsControlled K)
    {δ_base : ℝ} (hδ_base_pos : 0 < δ_base)
    (hδ_base_le_K : δ_base ≤ K)
    {μ : ℕ} (hmu : 0 < μ)
    {p : UnitPoint × ℝ}
    (hp_centered : p.1 ∈ I.centeredCarrier (1 / 8))
    (hmult : (μ : ℝ) ≤ multiplicity F δ_base ((p.1 : ℝ), p.2))
    (L : ℝ) (hL_nonneg : 0 ≤ L)
    (hbounds : ∀ f ∈ family, ∀ z : UnitPoint, |f.firstDeriv z| ≤ L)
    (hδ_vert_le_K : (1 + L) * δ_base ≤ K) :
    ∃ (δ_vert t Delta : ℝ) (center k : C2Function)
      (G H : FiniteFunctionFamily),
      δ_vert = (1 + L) * δ_base ∧
      δ_vert ≤ t ∧ t ≤ K ∧
      δ_vert ≤ Delta ∧ Delta ≤ 4 * t ∧
      G.carrier ⊆ F.carrier ∩ c2Ball center t ∧
      H.carrier = G.carrier ∩ {f | tangencyParameterOn I f k ≤ Delta} ∧
      k ∈ H.carrier ∧
      (∀ f ∈ H.carrier, ((p.1 : ℝ), p.2) ∈ graphNeighborhood f δ_base) ∧
      ∃ (t_fine C_R : ℝ)
        (R : CurvilinearRectangle δ_vert (C_R * t_fine * Delta / δ_vert)),
        t_fine = 4 * t ∧
        9216 * K^2 ≤ C_R ∧
        R.interval.midpoint = (p.1 : ℝ) ∧
        p ∈ R.carrier ∧
        R.IsOverCentralQuarterOf I ∧
        ∀ f ∈ H.carrier, R.IsLambdaTangent f 5 := by
  rcases pointwise_fine_rectangle_exists_with_certificate
      hTwoEnds hTangencyTwoEnds hFine hK hD hC_KT hlambda
      hfamily hF hepsilon hI hδ_base_pos hδ_base_le_K hmu
      hp_centered hmult L hL_nonneg hbounds hδ_vert_le_K with
    ⟨δ_vert, t, Delta, center, k, G, H,
      hδ_vert_eq, hδ_vert_t, ht_K, hδ_vert_Delta, hDelta,
      hG, hH, hk, hgraph, _hcertificate, hregime⟩
  exact
    ⟨δ_vert, t, Delta, center, k, G, H,
      hδ_vert_eq, hδ_vert_t, ht_K, hδ_vert_Delta, hDelta,
      hG, hH, hk, hgraph, hregime⟩

end Kakeya.Cinematic
