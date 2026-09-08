module

public import Kakeya.DimensionThree.MainLemma1.CoarseBallUpstreamW50
public import Kakeya.DimensionThree.MainLemma1.ScalarFactorization
public import Kakeya.Factoring.RhoFreeParentCount

@[expose] public section

open MeasureTheory Convexity ConvexSpaceBody ShadedBody Filter Topology
open scoped NNReal ENNReal

namespace Kakeya.ml1Boot.W48EndpointPacketCoarseModule

noncomputable section

universe u v w

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E] [MeasurableSpace E]
  [BorelSpace E]

/- The parent ambient singleton forces the active family to be the selected singleton. -/
theorem selected_active_eq_singleton_w48
    {iota : Type u} {kappa : Type w} [DecidableEq iota] [DecidableEq kappa]
    {sigma rho : NNReal} {c L : ENNReal}
    {amb act act' : Finset iota} {V Z' : iota → ShadedTube sigma E}
    {pMap : iota → kappa} {p k0 : kappa}
    {Vrho : kappa → Tube rho E} {tAct : Finset kappa}
    {Zrho : kappa → ShadedTube rho E} {lamP lamF : NNReal}
    (h2 : IsOneScaleSelected c L amb act V ({p} : Finset kappa) Vrho pMap
      act' Z' tAct Zrho k0 lamP lamF) :
    tAct = ({p} : Finset kappa) := by
  apply Finset.Subset.antisymm h2.parent_subset
  rw [Finset.singleton_subset_iff]
  have hk0p : k0 = p := Finset.mem_singleton.mp (h2.parent_subset h2.sel_mem)
  simpa [hk0p] using h2.sel_mem

theorem selected_coarse_pairwiseED_w48
    {iota : Type u} {kappa : Type w} [DecidableEq iota] [DecidableEq kappa]
    {sigma rho : NNReal} {c L : ENNReal}
    {amb act act' : Finset iota} {V Z' : iota → ShadedTube sigma E}
    {pMap : iota → kappa} {p k0 : kappa}
    {Vrho : kappa → Tube rho E} {tAct : Finset kappa}
    {Zrho : kappa → ShadedTube rho E} {lamP lamF : NNReal}
    (h2 : IsOneScaleSelected c L amb act V ({p} : Finset kappa) Vrho pMap
      act' Z' tAct Zrho k0 lamP lamF)
    (Yc : kappa → ShadedTube rho E) :
    (tAct : Set kappa).Pairwise
      (fun l l' => IsEssentiallyDistinct (Yc l).carrier (Yc l').carrier) := by
  intro l hl l' hl' hll'
  have hlp : l = p := Finset.mem_singleton.mp (h2.parent_subset hl)
  have hl'p : l' = p := Finset.mem_singleton.mp (h2.parent_subset hl')
  exact (hll' (hlp.trans hl'p.symm)).elim

theorem selected_coarse_frostman_le_one_w48
    {iota : Type u} {kappa : Type w} [DecidableEq iota] [DecidableEq kappa]
    {sigma rho : NNReal} {c L : ENNReal}
    {amb act act' : Finset iota} {V Z' : iota → ShadedTube sigma E}
    {pMap : iota → kappa} {p k0 : kappa}
    {Vrho : kappa → Tube rho E} {tAct : Finset kappa}
    {Zrho : kappa → ShadedTube rho E} {lamP lamF : NNReal}
    (h2 : IsOneScaleSelected c L amb act V ({p} : Finset kappa) Vrho pMap
      act' Z' tAct Zrho k0 lamP lamF)
    (Yc : kappa → ShadedTube rho E)
    (hYtube : (Yc p).toTube = Vrho p)
    (hrho0 : 0 < rho) :
    frostmanConstIn tAct (fun l => (Yc l).toConvexSpaceBody)
      (Vrho p).toConvexSpaceBody ≤ 1 := by
  rw [selected_active_eq_singleton_w48 h2]
  apply ConvexSpaceBody.frostmanConstIn_le
  apply ConvexSpaceBody.IsFrostmanIn.of_maxDensity_le
  have hbody : (Yc p).toConvexSpaceBody = (Vrho p).toConvexSpaceBody := by
    rw [hYtube]
  rw [← hbody]
  have hvol := tube_volume_pos_ne_top (E := E) hrho0 (Vrho p)
  rw [Kakeya.densityIn_singleton_self
    (fun l => (Yc l).toConvexSpaceBody) p (by simpa [hbody] using hvol.1)
      (by simpa [hbody] using hvol.2)]
  have hKT := Kakeya.isKatzTao_singleton
    (fun l => (Yc l).toConvexSpaceBody) p (C := (1 : ENNReal)) le_rfl
  calc
    Kakeya.maxDensity ({p} : Finset kappa)
        (fun l => (Yc l).toConvexSpaceBody) ≤ (1 : ENNReal) := hKT
    _ = 1 * 1 := by norm_num

/- Small-scale consumer for a selected singleton.  It is module-safe and retains the
literal `tAct`/`Zrho` witness; all geometric hypotheses are proved from the selected
parent fields, with only the standard ambient-ball ratio and fullness payments exposed. -/
set_option maxHeartbeats 16000000 in
theorem eventually_selected_singleton_coarse_module_w48
    (hdim : Module.finrank Real E = 3) {gamma : Real}
    (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma ≤ 1)
    (hKF : FrostmanEstimate.{u} E gamma)
    (e : Real) (he : 0 < e) (R : Real) (hR : 1 ≤ R) :
    ∃ etaS > (0 : Real), ∃ M : Nat, 0 < M ∧
      ∀ Lf : NNReal, 1 ≤ Lf → ∀ n0 A : Real, 0 ≤ n0 → 0 < A →
      ∀ᶠ (delta : NNReal) in nhdsWithin 0 (Set.Ioi 0),
        ∀ rho : NNReal, delta ≤ rho → rho ≤ 1 →
        ∀ {sigma : NNReal} {iota : Type u} [DecidableEq iota]
          {c L : ENNReal} {amb act act' : Finset iota}
          {V Z' : iota → ShadedTube sigma E}
          {pMap : iota → iota} {p k0 : iota}
          {Vrho : iota → Tube rho E} {tAct : Finset iota}
          {Zrho : iota → ShadedTube rho E} {lamP lamF : NNReal},
        IsOneScaleSelected c L amb act V ({p} : Finset iota) Vrho pMap
            act' Z' tAct Zrho k0 lamP lamF →
        (Vrho p).carrier ⊆ Metric.closedBall 0 R →
        volume (ConvexSpaceBody.closedBall (0 : E) R
          (le_trans zero_le_one hR)).carrier / volume (Vrho p).carrier
          ≤ (Lf : ENNReal) * (delta : ENNReal) ^ (-n0) →
        (2 : ENNReal) * (delta : ENNReal) ^ etaS ≤ (lamP : ENNReal) →
        (2 * (M : ENNReal) * (Lf : ENNReal)) *
            (delta : ENNReal) ^ (-n0 - e) ≤ (delta : ENNReal) ^ (-4 * A) →
        (rho : Real) ≤ 1 / 4 →
        ShadedBody.multiplicity tAct (fun l => (Zrho l).toShadedBody) ≤
          (delta : ENNReal) ^ (-4 * A) * (rho : ENNReal) ^ (-2 * gamma) *
            ((tAct.card : ENNReal) * (rho : ENNReal) ^ (2 : Nat)) ^
              (1 - gamma / 2) := by
  obtain ⟨etaS, hetaS, M, hM, hcoarse⟩ :=
    Kakeya.ml1Boot.multiplicity_le_coarse_ball
      (E := E) hdim hgamma0 hgamma1 hKF R hR e he
  refine ⟨etaS, hetaS, M, hM, ?_⟩
  intro Lf hLf n0 A hn0 hA
  filter_upwards [hcoarse Lf hLf n0 A hn0 hA.le,
      self_mem_nhdsWithin, eventually_le_one_nhdsGT]
    with delta hcoarseDelta hdelta0 hdelta1
  intro rho hdeltaRho hrho1 sigma iota _ c L amb act act' V Z' pMap p k0
    Vrho tAct Zrho lamP lamF h2 hparentBall hratio hrich habsorb hrho4
  have hrho0 : 0 < rho := lt_of_lt_of_le hdelta0 hdeltaRho
  have hpAct : p ∈ tAct := by
    rw [selected_active_eq_singleton_w48 h2]
    simp
  have hpTube : (Zrho p).toTube = Vrho p := h2.parent_tube p hpAct
  have hparentLe : (Vrho p).toConvexSpaceBody ≤
      ConvexSpaceBody.closedBall (0 : E) R (le_trans zero_le_one hR) := by
    exact SetLike.coe_subset_coe.mpr hparentBall
  have hparentVol : volume (Vrho p).toConvexSpaceBody.carrier ≠ 0 :=
    (tube_volume_pos_ne_top (E := E) hrho0 (Vrho p)).1.ne'
  have hmembers : ∀ l, l ∈ tAct →
      (Zrho l).toConvexSpaceBody ≤ (Vrho p).toConvexSpaceBody := by
    intro l hl
    have hlp : l = p := Finset.mem_singleton.mp (h2.parent_subset hl)
    change (Zrho l).toTube.toConvexSpaceBody ≤ (Vrho p).toConvexSpaceBody
    rw [hlp, hpTube]
  have hfrost0 := frostmanConstIn_ambient_mono hparentLe hparentVol hmembers
  have hfrost : frostmanConstIn tAct
      (fun l => (Zrho l).toConvexSpaceBody)
      (ConvexSpaceBody.closedBall (0 : E) R (le_trans zero_le_one hR)) ≤
      (Lf : ENNReal) * (delta : ENNReal) ^ (-n0) := by
    calc
      _ ≤ volume (ConvexSpaceBody.closedBall (0 : E) R
            (le_trans zero_le_one hR)).carrier / volume (Vrho p).carrier *
            frostmanConstIn tAct (fun l => (Zrho l).toConvexSpaceBody)
              (Vrho p).toConvexSpaceBody := hfrost0
      _ ≤ volume (ConvexSpaceBody.closedBall (0 : E) R
            (le_trans zero_le_one hR)).carrier / volume (Vrho p).carrier * 1 := by
          gcongr
          exact selected_coarse_frostman_le_one_w48 h2 Zrho hpTube hrho0
      _ ≤ (Lf : ENNReal) * (delta : ENNReal) ^ (-n0) := by simpa using hratio
  have hne : tAct.Nonempty := by
    exact ⟨k0, h2.sel_mem⟩
  have hball : ∀ l ∈ tAct, (Zrho l).carrier ⊆
      Metric.closedBall (0 : E) R := by
    intro l hl
    have hlp : l = p := Finset.mem_singleton.mp (h2.parent_subset hl)
    rw [hlp]
    simpa [hpTube] using hparentBall
  have hED := selected_coarse_pairwiseED_w48 h2 Zrho
  have hfull : (2 : ENNReal) * (delta : ENNReal) ^ etaS ≤
      (ShadedBody.fullness tAct (fun l => (Zrho l).toShadedBody) : ENNReal) :=
    hrich.trans h2.parent_fullness
  exact hcoarseDelta rho hdeltaRho hrho4 Zrho hne hball hED hfrost hfull habsorb

end

end Kakeya.ml1Boot.W48EndpointPacketCoarseModule

#print axioms Kakeya.ml1Boot.W48EndpointPacketCoarseModule.eventually_selected_singleton_coarse_module_w48

end
