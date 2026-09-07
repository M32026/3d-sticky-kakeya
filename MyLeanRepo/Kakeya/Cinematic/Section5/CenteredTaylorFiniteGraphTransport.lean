import MyLeanRepo.Kakeya.Cinematic.Section5.CenteredTaylorFiniteGraphTransportInputs

/-!
# Finite graph transport through a centered Taylor extension

Apply the centered Taylor cinematic transport, then preserve finite-family
cardinality, separation, Katz--Tao bounds, graph neighborhoods, and
multiplicity on the centered sixteenth.
-/

noncomputable section

namespace Kakeya.Cinematic

open C2Function Set Metric

lemma centeredHorizontalPoint_dist_eq
    (I : ParameterInterval) (p q : ℝ × ℝ) :
    dist (centeredHorizontalPoint I p) (centeredHorizontalPoint I q) =
      dist p q := by
  unfold centeredHorizontalPoint centeredHorizontalShift
  have h1 : dist (p.1 + (1 / 2 - I.midpoint))
        (q.1 + (1 / 2 - I.midpoint)) = dist p.1 q.1 := by
    simp [Real.dist_eq] <;> ring
  simp [Prod.dist_eq, h1]

lemma graphNeighborhood_centered_equiv
    {I : ParameterInterval} {f transported : C2Function}
    (hjet : IsCenteredJetCopy I f transported)
    {rho : ℝ} (hrho : 0 < rho) (hlen : 4 * rho ≤ I.length)
    (hI_len : 0 < I.length)
    {p : ℝ × ℝ} (hp_center : p.1 ∈ I.realCenteredCarrier (1 / 16)) :
    p ∈ graphNeighborhood f rho ↔
      centeredHorizontalPoint I p ∈ graphNeighborhood transported rho := by
  let p' := centeredHorizontalPoint I p
  have h_p'_center : |p'.1 - 1 / 2| ≤ I.length / 32 := by
    have h1 : p'.1 - 1 / 2 = p.1 - I.midpoint := by
      simp [p', centeredHorizontalPoint, centeredHorizontalShift] <;> ring
    rw [h1]
    have h_eq : (1 / 16 : ℝ) * I.length / 2 = I.length / 32 := by
      ring
    have h5 : |p.1 - I.midpoint| ≤ I.length / 32 := by
      rw [← h_eq]
      exact hp_center.2
    exact h5
  constructor
  · intro hp
    have h_res : p ∈ restrictedGraphNeighborhood f I rho :=
      graphNeighborhood_mem_restricted_of_centered hrho hlen hp_center hp
    rcases Metric.mem_thickening_iff.mp h_res with ⟨q, hq, hpq⟩
    rcases hq with ⟨hq_unit, hq_carrier, hq_value⟩
    let x : I.LocalPoint := ⟨⟨q.1, hq_unit⟩, hq_carrier⟩
    rcases hjet.1 x with ⟨y, hy_eq, hy_val, _, _⟩
    let q' : ℝ × ℝ := ((y : ℝ), transported y)
    have hq'_graph : q' ∈ functionGraph transported :=
      ⟨y.property, rfl⟩
    have hq'_eq : q' = centeredHorizontalPoint I q := by
      apply Prod.ext
      · simp [q', centeredHorizontalPoint, centeredHorizontalShift, hy_eq] <;>
          ring
      · have h_q'2 : q'.2 = f.value ↑x := by
          dsimp only [q']
          exact hy_val
        have h3 : (centeredHorizontalPoint I q).2 = q.2 := by
          simp [centeredHorizontalPoint]
        have h4 : f.value ↑x = q.2 := hq_value.symm
        calc
          q'.2 = f.value ↑x := h_q'2
          _ = q.2 := h4
          _ = (centeredHorizontalPoint I q).2 := h3.symm
    have hdist : dist p' q' < rho := by
      rw [hq'_eq, centeredHorizontalPoint_dist_eq I p q]
      exact hpq
    exact Metric.mem_thickening_iff.mpr ⟨q', hq'_graph, hdist⟩
  · intro hp'
    rcases Metric.mem_thickening_iff.mp hp' with
      ⟨q', hq'_graph, hp'q'⟩
    rcases hq'_graph with ⟨hq'_unit, hq'_value⟩
    let y : UnitPoint := ⟨q'.1, hq'_unit⟩
    have h_q'_x : |q'.1 - p'.1| < rho := by
      have h : dist q'.1 p'.1 ≤ dist q' p' := by
        rw [Prod.dist_eq]
        exact le_max_left _ _
      have hp'q'_symm : dist q' p' < rho := by
        rw [dist_comm]
        exact hp'q'
      have h' : dist q'.1 p'.1 < rho := h.trans_lt hp'q'_symm
      simpa [Real.dist_eq] using h'
    have h_q'_center : |q'.1 - 1 / 2| ≤ I.length / 2 := by
      have htri :
          |q'.1 - 1 / 2| ≤
            |q'.1 - p'.1| + |p'.1 - 1 / 2| := by
        calc
          |q'.1 - 1 / 2| =
              |(q'.1 - p'.1) + (p'.1 - 1 / 2)| := by ring_nf
          _ ≤ |q'.1 - p'.1| + |p'.1 - 1 / 2| :=
            abs_add_le _ _
      have hrho_len : rho ≤ I.length / 4 := by linarith
      have hstrict : |q'.1 - 1 / 2| < I.length / 2 := by
        calc
          |q'.1 - 1 / 2| ≤
              |q'.1 - p'.1| + |p'.1 - 1 / 2| := htri
          _ < rho + I.length / 32 := by linarith
          _ ≤ I.length / 4 + I.length / 32 := by linarith
          _ ≤ I.length / 2 := by linarith
      exact hstrict.le
    rcases hjet.2 y h_q'_center with ⟨x, hx_eq, hx_val, _, _⟩
    let q : ℝ × ℝ := ((x.1 : ℝ), f x.1)
    have hq_graph : q ∈ functionGraph f :=
      ⟨x.1.property, rfl⟩
    have hq'_eq : q' = centeredHorizontalPoint I q := by
      apply Prod.ext
      · simp [q, centeredHorizontalPoint, centeredHorizontalShift, hx_eq] <;>
          ring
      · have h1 : q'.2 = f x.1 := by
          rw [hq'_value, hx_val]
        have h2 : (centeredHorizontalPoint I q).2 = f x.1 := by
          simp [q, centeredHorizontalPoint]
        rw [h1, h2]
    have hdist : dist p q < rho := by
      rw [hq'_eq] at hp'q'
      rw [centeredHorizontalPoint_dist_eq I p q] at hp'q'
      exact hp'q'
    exact Metric.mem_thickening_iff.mpr ⟨q, hq_graph, hdist⟩

theorem centered_taylor_finite_graph_transport_of_witness
    {K D C_KT lambda : ℝ}
    (hK : 1 ≤ K) (hD : 1 ≤ D) (hC_KT : 1 ≤ C_KT)
    (hlambda : 1 ≤ lambda)
    {family : Set C2Function}
    (hfamily : IsCinematicFamily family K D)
    {I : ParameterInterval}
    (hI_len : 0 < I.length) (hI_short : I.IsShort (12 * K))
    {delta : ℝ}
    (hdelta : 0 < delta) (h4rho : 4 * (lambda * delta) ≤ I.length)
    {F : FiniteFunctionFamily}
    (hF_sub : F.carrier ⊆ family)
    (hsep : F.IsDeltaSeparated delta)
    (hKT : F.HasKatzTaoBound delta C_KT)
    (transport : C2Function → C2Function)
    (hinj : Set.InjOn transport family)
    (hcinematic :
      IsCinematicFamily
        (transport '' family)
        (12 * K)
        ((D *
            Real.rpow (6 * K)
              (Real.log D / Real.log 2)) ^ 3))
    (hjet : ∀ f ∈ family, IsCenteredJetCopy I f (transport f))
    (hmetric :
      ∀ f ∈ family, ∀ g ∈ family,
        restrictedC2Distance I f g ≤
            c2Distance (transport f) (transport g) ∧
          c2Distance (transport f) (transport g) ≤
            3 * restrictedC2Distance I f g) :
    CenteredTaylorFiniteGraphTransportData
      K D C_KT lambda family I delta F transport := by
  classical
  set rho : ℝ := lambda * delta with hrho_def
  set imageFamily : Set C2Function := transport '' family with
    himageFamily_def
  set transportedF : FiniteFunctionFamily :=
    F.transportImage transport with htransportedF_def
  have hKpos : 0 < K := by linarith
  have hC_KT_nonneg : 0 ≤ C_KT := by linarith
  have hlambda_pos : 0 < lambda := by linarith
  have hrho : 0 < rho := mul_pos hlambda_pos hdelta
  have h_inj_F : Set.InjOn transport F.carrier :=
    hinj.mono hF_sub
  constructor
  · exact hinj
  constructor
  · exact hcinematic
  constructor
  · exact Set.image_mono hF_sub
  constructor
  · exact h_inj_F.ncard_image
  constructor
  · intro f' hf' g' hg' hne
    rcases hf' with ⟨f, hf, rfl⟩
    rcases hg' with ⟨g, hg, rfl⟩
    have hfg_ne : f ≠ g := by
      intro h
      apply hne
      rw [h]
    have h1 : delta ≤ c2Distance f g :=
      hsep hf hg hfg_ne
    have h2 :
        c2Distance f g ≤
          3 * K * restrictedC2Distance I f g :=
      c2Distance_le_three_mul_restrictedC2Distance
        hK hfamily (hF_sub hf) (hF_sub hg) I
    have h3 :
        restrictedC2Distance I f g ≤
          c2Distance (transport f) (transport g) :=
      (hmetric f (hF_sub hf) g (hF_sub hg)).1
    have h4 :
        delta ≤
          3 * K * c2Distance (transport f) (transport g) := by
      calc
        delta ≤ c2Distance f g := h1
        _ ≤ 3 * K * restrictedC2Distance I f g := h2
        _ ≤ 3 * K * c2Distance (transport f) (transport g) := by
          gcongr
    have h5 :
        delta / (3 * K) ≤
          c2Distance (transport f) (transport g) := by
      calc
        delta / (3 * K) ≤
            (3 * K * c2Distance (transport f) (transport g)) /
              (3 * K) := by
          gcongr
        _ = c2Distance (transport f) (transport g) := by
          field_simp [hKpos.ne'] <;> ring
    exact h5
  constructor
  · constructor
    · have h_card_eq :
          (transportedF.card : ℝ) = (F.card : ℝ) := by
        exact_mod_cast h_inj_F.ncard_image
      rw [h_card_eq]
      have h2 : (F.card : ℝ) ≤ C_KT / delta := hKT.1
      have h3 :
          C_KT / delta ≤
            (2 * C_KT) / (delta / (3 * K)) := by
        have h4 :
            (2 * C_KT) / (delta / (3 * K)) =
              6 * K * C_KT / delta := by
          field_simp [hdelta.ne', hKpos.ne']
          ring
        rw [h4]
        have h5 : C_KT ≤ 6 * K * C_KT := by
          have h6 : 1 ≤ 6 * K := by linarith
          calc
            C_KT = C_KT * 1 := by ring
            _ ≤ C_KT * (6 * K) := by
              gcongr <;> linarith
            _ = 6 * K * C_KT := by ring
        exact div_le_div_of_nonneg_right h5 hdelta.le
      exact h2.trans h3
    · intro center r hr1 hr2
      let A : Set C2Function :=
        transportedF.carrier ∩ c2Ball center r
      by_cases hA_empty : A = ∅
      · have h_ncard_zero : A.ncard = 0 := by
          rw [hA_empty]
          simp
        have h_r_nonneg : 0 ≤ r := by
          have h_pos : 0 < delta / (3 * K) := by positivity
          linarith
        have h_nonneg :
            0 ≤
              (2 * C_KT) * (r / (delta / (3 * K))) := by
          positivity
        have h_goal :
            (A.ncard : ℝ) ≤
              (2 * C_KT) * (r / (delta / (3 * K))) := by
          rw [h_ncard_zero]
          simpa using h_nonneg
        exact h_goal
      · have hA_nonempty : A.Nonempty :=
          Set.nonempty_iff_ne_empty.mpr hA_empty
        rcases hA_nonempty with ⟨g0', hg0'_in⟩
        have hg0'_carrier : g0' ∈ transportedF.carrier :=
          hg0'_in.1
        have hg0'_ball : g0' ∈ c2Ball center r :=
          hg0'_in.2
        rcases hg0'_carrier with ⟨g0, hg0, rfl⟩
        let B : Set C2Function :=
          {h | h ∈ F.carrier ∧ transport h ∈ c2Ball center r}
        have hB_sub_F : B ⊆ F.carrier := fun h hh => hh.1
        have hB_finite : B.Finite :=
          F.finite.subset hB_sub_F
        have h_image_B : transport '' B = A := by
          ext y
          simp only [B, Set.mem_image, Set.mem_inter_iff,
            Set.mem_setOf_eq]
          constructor
          · rintro ⟨h, hh, rfl⟩
            exact ⟨⟨h, hh.1, rfl⟩, hh.2⟩
          · rintro ⟨⟨h, hh, rfl⟩, hball⟩
            exact ⟨h, ⟨hh, hball⟩, rfl⟩
        have h_inj_B : Set.InjOn transport B :=
          h_inj_F.mono hB_sub_F
        have h_ncard_A : A.ncard = B.ncard := by
          rw [← h_image_B]
          exact h_inj_B.ncard_image
        have hB_sub_ball :
            B ⊆ F.carrier ∩ c2Ball g0 (6 * K * r) := by
          intro h hh
          have h_hF : h ∈ F.carrier := hh.1
          have h_hball : transport h ∈ c2Ball center r := hh.2
          have h_dist1 :
              c2Distance (transport h) (transport g0) ≤
                2 * r := by
            have h1 : c2Distance (transport h) center ≤ r :=
              by simpa [mem_c2Ball] using h_hball
            have h2 : c2Distance (transport g0) center ≤ r :=
              by simpa [mem_c2Ball] using hg0'_ball
            have h2' : c2Distance center (transport g0) ≤ r := by
              have h_comm :
                  c2Distance center (transport g0) =
                    c2Distance (transport g0) center :=
                dist_comm _ _
              rw [h_comm]
              exact h2
            calc
              c2Distance (transport h) (transport g0) ≤
                  c2Distance (transport h) center +
                    c2Distance center (transport g0) :=
                dist_triangle _ _ _
              _ ≤ r + r := by gcongr
              _ = 2 * r := by ring
          have h_restricted :
              restrictedC2Distance I h g0 ≤
                c2Distance (transport h) (transport g0) :=
            (hmetric h (hF_sub h_hF) g0 (hF_sub hg0)).1
          have h_global :
              c2Distance h g0 ≤
                3 * K * restrictedC2Distance I h g0 :=
            c2Distance_le_three_mul_restrictedC2Distance
              hK hfamily (hF_sub h_hF) (hF_sub hg0) I
          have h_final :
              c2Distance h g0 ≤ 6 * K * r := by
            calc
              c2Distance h g0 ≤
                  3 * K * restrictedC2Distance I h g0 :=
                h_global
              _ ≤
                  3 * K *
                    c2Distance (transport h) (transport g0) := by
                gcongr
              _ ≤ 3 * K * (2 * r) := by gcongr
              _ = 6 * K * r := by ring
          exact ⟨h_hF, by simpa [mem_c2Ball] using h_final⟩
        have h_inter_sub :
            F.carrier ∩ c2Ball g0 (6 * K * r) ⊆
              F.carrier := by
          intro x hx
          exact hx.1
        have h_target_finite :
            (F.carrier ∩ c2Ball g0 (6 * K * r)).Finite :=
          F.finite.subset h_inter_sub
        have h_ncard_le :
            B.ncard ≤
              (F.carrier ∩ c2Ball g0 (6 * K * r)).ncard :=
          Set.ncard_le_ncard hB_sub_ball h_target_finite
        have h_main_bound :
            A.ncard ≤
              (F.carrier ∩ c2Ball g0 (6 * K * r)).ncard := by
          rw [h_ncard_A]
          exact h_ncard_le
        by_cases h6K : 6 * K * r ≤ 1
        · have hdelta' : delta ≤ 6 * K * r := by
            have h : delta ≤ 3 * K * r := by
              calc
                delta = 3 * K * (delta / (3 * K)) := by
                  field_simp [hKpos.ne'] <;> ring
                _ ≤ 3 * K * r := by gcongr
            linarith
          have hbound := hKT.2 g0 (6 * K * r) hdelta' h6K
          have hcast :
              (A.ncard : ℝ) ≤
                ((F.carrier ∩
                    c2Ball g0 (6 * K * r)).ncard : ℝ) :=
            Nat.cast_le.mpr h_main_bound
          have h_eq :
              C_KT * ((6 * K * r) / delta) =
                (2 * C_KT) *
                  (r / (delta / (3 * K))) := by
            field_simp [hdelta.ne', hKpos.ne']
            ring
          calc
            (A.ncard : ℝ) ≤
                ((F.carrier ∩
                    c2Ball g0 (6 * K * r)).ncard : ℝ) :=
              hcast
            _ ≤ C_KT * ((6 * K * r) / delta) := hbound
            _ =
                (2 * C_KT) * (r / (delta / (3 * K))) :=
              h_eq
        · have h6K' : 1 < 6 * K * r := by linarith
          have h_A_sub : A ⊆ transportedF.carrier := by
            intro x hx
            exact hx.1
          have h_card : A.ncard ≤ transportedF.card :=
            Set.ncard_le_ncard h_A_sub transportedF.finite
          have h_card' :
              (A.ncard : ℝ) ≤ (transportedF.card : ℝ) :=
            Nat.cast_le.mpr h_card
          have h_card_eq :
              (transportedF.card : ℝ) = (F.card : ℝ) :=
            congr_arg (fun n : ℕ => (n : ℝ))
              h_inj_F.ncard_image
          have h_final :
              (F.card : ℝ) ≤
                (2 * C_KT) *
                  (r / (delta / (3 * K))) := by
            have h1 : (F.card : ℝ) ≤ C_KT / delta := hKT.1
            have h3 :
                (2 * C_KT) *
                    (r / (delta / (3 * K))) =
                  6 * K * C_KT * r / delta := by
              field_simp [hdelta.ne', hKpos.ne']
              ring
            have h4 : C_KT ≤ 6 * K * C_KT * r := by
              have h5 : 1 ≤ 6 * K * r := by linarith
              calc
                C_KT = C_KT * 1 := by ring
                _ ≤ C_KT * (6 * K * r) := by
                  gcongr <;> linarith
                _ = 6 * K * C_KT * r := by ring
            have h6 :
                C_KT / delta ≤
                  (6 * K * C_KT * r) / delta := by
              apply div_le_div_of_nonneg_right h4 hdelta.le
            rw [h3]
            exact h1.trans h6
          calc
            (A.ncard : ℝ) ≤ (transportedF.card : ℝ) :=
              h_card'
            _ = (F.card : ℝ) := h_card_eq
            _ ≤
                (2 * C_KT) *
                  (r / (delta / (3 * K))) :=
              h_final
  constructor
  · exact hjet
  constructor
  · exact hmetric
  constructor
  · intro f hf p hp_center
    have hjet_f : IsCenteredJetCopy I f (transport f) :=
      hjet f (hF_sub hf)
    exact graphNeighborhood_centered_equiv
      hjet_f hrho h4rho hI_len hp_center
  · intro p hp_center
    let p' := centeredHorizontalPoint I p
    have hF_coe :
        (F.toFinset : Set C2Function) = F.carrier :=
      Set.Finite.coe_toFinset F.finite
    have hTF_coe :
        (transportedF.toFinset : Set C2Function) =
          transportedF.carrier :=
      Set.Finite.coe_toFinset transportedF.finite
    have h_carrier_eq :
        transportedF.carrier = transport '' F.carrier := by
      simp [transportedF, FiniteFunctionFamily.transportImage]
    have h_toFinset_eq :
        transportedF.toFinset =
          Finset.image transport F.toFinset := by
      apply Finset.coe_inj.mp
      calc
        (transportedF.toFinset : Set C2Function) =
            transportedF.carrier :=
          hTF_coe
        _ = transport '' F.carrier := h_carrier_eq
        _ = transport '' (F.toFinset : Set C2Function) := by
          rw [hF_coe]
        _ =
            (Finset.image transport
              F.toFinset : Set C2Function) := by
          exact Finset.coe_image.symm
    have h_inj_on_finset :
        Set.InjOn transport
          (F.toFinset : Set C2Function) := by
      rw [hF_coe]
      exact h_inj_F
    have hsum1 :
        ∑ g ∈ transportedF.toFinset,
            (graphNeighborhood g rho).indicator
              (fun _ => (1 : ℝ)) p' =
          ∑ f ∈ F.toFinset,
            (graphNeighborhood (transport f) rho).indicator
              (fun _ => (1 : ℝ)) p' := by
      rw [h_toFinset_eq, Finset.sum_image h_inj_on_finset]
    have hsum2 :
        ∑ f ∈ F.toFinset,
            (graphNeighborhood (transport f) rho).indicator
              (fun _ => (1 : ℝ)) p' =
          ∑ f ∈ F.toFinset,
            (graphNeighborhood f rho).indicator
              (fun _ => (1 : ℝ)) p := by
      apply Finset.sum_congr rfl
      intro f hf
      have hf' : f ∈ F.carrier := by
        rw [← hF_coe]
        exact hf
      have hequiv :
          p ∈ graphNeighborhood f rho ↔
            p' ∈ graphNeighborhood (transport f) rho :=
        graphNeighborhood_centered_equiv
          (hjet f (hF_sub hf')) hrho h4rho hI_len hp_center
      simp [Set.indicator_apply, hequiv]
    rw [multiplicity, multiplicity, hsum1, hsum2]

theorem centered_taylor_finite_graph_transport :
    CenteredTaylorFiniteGraphTransportStatement := by
  intro h_main K D C_KT lambda hK hD hC_KT hlambda
    family hfamily I hI_len hI_short delta hdelta h4rho
    F hF_sub hsep hKT
  rcases h_main K D hK hD family hfamily I hI_len hI_short with
    ⟨transport, hinj, hcinematic, hjet, hmetric⟩
  exact ⟨transport,
    centered_taylor_finite_graph_transport_of_witness
      hK hD hC_KT hlambda hfamily hI_len hI_short hdelta h4rho
      hF_sub hsep hKT transport hinj hcinematic hjet hmetric⟩

end Kakeya.Cinematic
