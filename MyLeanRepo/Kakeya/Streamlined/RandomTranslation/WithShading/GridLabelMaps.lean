import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.WithShading.MultiscaleShiftData
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.WithShading.EnlargementContainment

/-!
# Grid label maps: per-scale label maps from multiscale shifts

Combines `MultiscaleShiftData` with prefix grouping to produce label maps at
every grid cut.

At each grid cut `k`, the multiscale shift decomposes into prefix groups
(shared cumulative shift) and residual shifts. The label map assigns to every
translated tube a pair `(group_id, coarse_parent)`.
-/

noncomputable section

open BigOperators MeasureTheory Finset
open Kakeya.Streamlined
open Kakeya.Streamlined.RandomTranslation

namespace Kakeya.Streamlined.RandomTranslation.WithShading

/-- Combined grid label maps at every scale cut. -/
structure GridLabelMaps
    {δ : ℝ} {F : TubeFamily δ} {M : ℕ}
    (U : UniformTubeStructure F)
    (Y : TubeShading F)
    (data : MultiscaleShiftData δ M) where
  fineScale : Fin M → AdmissibleScale δ
  coarseScale : Fin M → ℝ
  hscale : ∀ k, (fineScale k).1 ≤ coarseScale k
  htail : ∀ (k : Fin M),
      (∑ j ∈ Finset.univ.filter (fun j : Fin M => k.val ≤ j.val),
         data.radius j) ≤
        coarseScale k - (fineScale k).1
  groupCount : Fin (M + 1) → ℕ
  group : (k : Fin (M + 1)) → Fin data.totalJ → Fin (groupCount k)
  cumulative : (k : Fin (M + 1)) → Fin (groupCount k) → Point3
  residual : (k : Fin (M + 1)) → Fin data.totalJ → Point3
  hgroup_pos : ∀ k, 0 < groupCount k
  hgroup_surj : ∀ k, Function.Surjective (group k)
  hgroup_balanced : ∀ k g h,
      (Finset.univ.filter fun i => group k i = g).card =
      (Finset.univ.filter fun i => group k i = h).card
  hgroup_eq : ∀ (k : Fin (M + 1)) i j,
      group k i = group k j ↔
        ∀ l : Fin M, l.val < k.val →
          (finPiFinEquiv.symm i) l =
            (finPiFinEquiv.symm j) l
  hshift_decomp : ∀ (k : Fin (M + 1)) i,
      data.shift i = cumulative k (group k i) + residual k i
  hresidual_bound : ∀ (k : Fin (M + 1)) i,
      ‖residual k i‖ ≤
        ∑ j ∈ Finset.univ.filter (fun j : Fin M => k.val ≤ j.val),
          data.radius j

namespace GridLabelMaps

variable {δ : ℝ} {F : TubeFamily δ} {M : ℕ}
  {U : UniformTubeStructure F} {Y : TubeShading F}
  {data : MultiscaleShiftData δ M}
  (gm : GridLabelMaps U Y data)

/-- The flat translated family. -/
abbrev translatedFamily : TubeFamily δ :=
  translatedCopies F data.totalJ data.shift

/-- The combined label map at scale cut `k`. -/
def label (k : Fin M) (v : Fin (data.totalJ * F.card)) :
    Option (Fin (gm.groupCount (Fin.castSucc k)) ×
              Fin (U.coarse (gm.fineScale k)).card) :=
  let p : Fin data.totalJ × Fin F.card := finProdFinEquiv.symm v
  some (gm.group (Fin.castSucc k) p.1,
        (U.cover (gm.fineScale k)).parent p.2)

/-- Every tube has a label. -/
lemma hlabel_some (k : Fin M) (v : Fin (data.totalJ * F.card)) :
    ∃ (g : Fin (gm.groupCount (Fin.castSucc k)))
      (p : Fin (U.coarse (gm.fineScale k)).card),
      gm.label k v = some (g, p) := by
  dsimp only [label]
  let q : Fin data.totalJ × Fin F.card := finProdFinEquiv.symm v
  exact ⟨gm.group (Fin.castSucc k) q.1,
    (U.cover (gm.fineScale k)).parent q.2, rfl⟩

/-- Group consistency of the label. -/
lemma hlabel_group (k : Fin M) (v : Fin (data.totalJ * F.card))
    (g : Fin (gm.groupCount (Fin.castSucc k)))
    (p : Fin (U.coarse (gm.fineScale k)).card) :
    gm.label k v = some (g, p) →
    gm.group (Fin.castSucc k) (finProdFinEquiv.symm v).1 = g := by
  intro h
  dsimp only [label] at h
  injection h with h'
  exact congr_arg Prod.fst h'

/-- The shared coarse family for a given group at cut `k`. -/
abbrev sharedCoarseFor (k : Fin M)
    (g : Fin (gm.groupCount (Fin.castSucc k))) :
    TubeFamily (gm.coarseScale k) :=
  translatedCopies
    (sameAxisEnlargedFamily (rho := gm.coarseScale k)
       (U.coarse (gm.fineScale k)))
    1 (fun _ => gm.cumulative (Fin.castSucc k) g)

/-- Every labeled tube is contained in its shared coarse parent tube. -/
lemma hlabel_nested (hδ : 0 < δ) (k : Fin M)
    (v : Fin (data.totalJ * F.card))
    (g : Fin (gm.groupCount (Fin.castSucc k)))
    (p : Fin (U.coarse (gm.fineScale k)).card)
    (h : gm.label k v = some (g, p)) :
    ((translatedCopies F data.totalJ data.shift).tube v).carrier ⊆
      ((gm.sharedCoarseFor k g).tube
        (finProdFinEquiv ((0 : Fin 1), p))).carrier := by
  let q : Fin data.totalJ × Fin F.card := finProdFinEquiv.symm v
  have hg : gm.group (Fin.castSucc k) q.1 = g := by
    dsimp only [label] at h
    injection h with h'
    exact congr_arg Prod.fst h'
  have hp : (U.cover (gm.fineScale k)).parent q.2 = p := by
    dsimp only [label] at h
    injection h with h'
    exact congr_arg Prod.snd h'
  have hsigma_nonneg : 0 ≤ (gm.fineScale k).1 := by
    have h1 : δ ≤ (gm.fineScale k).1 := (gm.fineScale k).2.1
    linarith
  have h_res : ‖gm.residual (Fin.castSucc k) q.1‖ ≤
      gm.coarseScale k - (gm.fineScale k).1 := by
    calc
      ‖gm.residual (Fin.castSucc k) q.1‖
        ≤ ∑ j ∈ Finset.univ.filter
            (fun j : Fin M => (Fin.castSucc k).val ≤ j.val),
            data.radius j :=
          gm.hresidual_bound (Fin.castSucc k) q.1
      _ ≤ gm.coarseScale k - (gm.fineScale k).1 := gm.htail k
  let enlarged := sameAxisEnlargedFamily (rho := gm.coarseScale k)
    (U.coarse (gm.fineScale k))
  have h_cont : (translateTube (F.tube q.2)
        (gm.residual (Fin.castSucc k) q.1)).carrier ⊆
      (enlarged.tube p).carrier := by
    rw [←hp]
    exact enlargement_containment (U.cover (gm.fineScale k))
      hsigma_nonneg (gm.hscale k)
      (gm.residual (Fin.castSucc k) q.1) h_res q.2
  have h_decomp' : data.shift q.1 =
      gm.cumulative (Fin.castSucc k) g +
        gm.residual (Fin.castSucc k) q.1 := by
    rw [gm.hshift_decomp (Fin.castSucc k) q.1, hg]
  have h_tube : (translatedCopies F data.totalJ data.shift).tube v =
      translateTube (F.tube q.2) (data.shift q.1) := by
    dsimp only [translatedCopies]
  have h_pk2 :
      (finProdFinEquiv.symm
        (finProdFinEquiv ((0 : Fin 1), p))).2 = p := by
    have h_pk :
        finProdFinEquiv.symm (finProdFinEquiv ((0 : Fin 1), p)) =
          ((0 : Fin 1), p) :=
      finProdFinEquiv.left_inv ((0 : Fin 1), p)
    rw [h_pk]
  have h_coarse_tube : (gm.sharedCoarseFor k g).tube
        (finProdFinEquiv ((0 : Fin 1), p)) =
      translateTube (enlarged.tube p)
        (gm.cumulative (Fin.castSucc k) g) := by
    dsimp only [sharedCoarseFor, translatedCopies]
    let E := sameAxisEnlargedFamily (rho := gm.coarseScale k)
      (U.coarse (gm.fineScale k))
    have h1 :
        E.tube
            (finProdFinEquiv.symm
              (finProdFinEquiv ((0 : Fin 1), p))).2 =
          E.tube p := by
      exact congr_arg
        (fun x : Fin (U.coarse (gm.fineScale k)).card => E.tube x)
        h_pk2
    calc
      translateTube
          (E.tube
            (finProdFinEquiv.symm
              (finProdFinEquiv ((0 : Fin 1), p))).2)
          (gm.cumulative (Fin.castSucc k) g)
        = translateTube (E.tube p)
            (gm.cumulative (Fin.castSucc k) g) := by
          exact congr_arg
            (fun T => translateTube T
              (gm.cumulative (Fin.castSucc k) g)) h1
      _ = translateTube (enlarged.tube p)
          (gm.cumulative (Fin.castSucc k) g) := by rfl
  rw [h_tube, h_decomp', h_coarse_tube]
  have h_trans_add : ∀ {r : ℝ} (T : Kakeya.DeltaTube r)
      (v1 v2 : Point3),
      (translateTube T (v1 + v2)).carrier =
        (fun x : Point3 => x + v1) '' (translateTube T v2).carrier := by
    intro r T v1 v2
    rw [translateTube_carrier T (v1 + v2), translateTube_carrier T v2]
    ext y
    simp only [Set.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x + v2, ⟨x, hx, rfl⟩, ?_⟩
      simp [add_comm, add_left_comm]
    · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨x, hx, ?_⟩
      simp [add_comm, add_left_comm]
  rw [h_trans_add (F.tube q.2)
      (gm.cumulative (Fin.castSucc k) g)
      (gm.residual (Fin.castSucc k) q.1)]
  have h_image :
      (fun x : Point3 => x + gm.cumulative (Fin.castSucc k) g) ''
        (enlarged.tube p).carrier =
      (translateTube (enlarged.tube p)
        (gm.cumulative (Fin.castSucc k) g)).carrier := by
    rw [translateTube_carrier _ _]
    rfl
  have h_mono :
      (fun x : Point3 => x + gm.cumulative (Fin.castSucc k) g) ''
          (translateTube (F.tube q.2)
            (gm.residual (Fin.castSucc k) q.1)).carrier ⊆
      (fun x : Point3 => x + gm.cumulative (Fin.castSucc k) g) ''
          (enlarged.tube p).carrier := by
    intro y hy
    rcases hy with ⟨z, hz, rfl⟩
    exact ⟨z, h_cont hz, rfl⟩
  rw [h_image] at *
  exact h_mono

/-- Construct grid label maps by choosing prefix grouping at every cut. -/
def exists_gridLabelMaps {δ : ℝ} {F : TubeFamily δ} {M : ℕ}
    {U : UniformTubeStructure F} {Y : TubeShading F}
    {data : MultiscaleShiftData δ M}
    (fineScale : Fin M → AdmissibleScale δ)
    (coarseScale : Fin M → ℝ)
    (hscale : ∀ k, (fineScale k).1 ≤ coarseScale k)
    (htail : ∀ (k : Fin M),
      (∑ j ∈ Finset.univ.filter (fun j : Fin M => k.val ≤ j.val),
         data.radius j) ≤
        coarseScale k - (fineScale k).1) :
    GridLabelMaps U Y data := by
  let P := fun (cut : Fin (M + 1)) => data.prefixGrouping cut
  let gc := fun (cut : Fin (M + 1)) => Classical.choose (P cut)
  let h1 := fun (cut : Fin (M + 1)) => Classical.choose_spec (P cut)
  let grp := fun (cut : Fin (M + 1)) => Classical.choose (h1 cut)
  let h2 := fun (cut : Fin (M + 1)) => Classical.choose_spec (h1 cut)
  let cum := fun (cut : Fin (M + 1)) => Classical.choose (h2 cut)
  let h3 := fun (cut : Fin (M + 1)) => Classical.choose_spec (h2 cut)
  let res := fun (cut : Fin (M + 1)) => Classical.choose (h3 cut)
  let h4 := fun (cut : Fin (M + 1)) => Classical.choose_spec (h3 cut)
  exact {
    fineScale, coarseScale, hscale, htail,
    groupCount := gc,
    group := grp,
    cumulative := cum,
    residual := res,
    hgroup_pos := fun k => (h4 k).1,
    hgroup_surj := fun k => (h4 k).2.1,
    hgroup_balanced := fun k => (h4 k).2.2.1,
    hgroup_eq := fun k => (h4 k).2.2.2.2.1,
    hshift_decomp := fun k => (h4 k).2.2.2.2.2.1,
    hresidual_bound := fun k => (h4 k).2.2.2.2.2.2
  }

/--
At every cut, the number of prefix groups times the common group-fiber
cardinality is exactly the total flat copy count.
-/
lemma groupCount_mul_groupFiber_card
    {δ : ℝ} {F : TubeFamily δ} {M : ℕ}
    {U : UniformTubeStructure F} {Y : TubeShading F}
    {data : MultiscaleShiftData δ M}
    (gm : GridLabelMaps U Y data)
    (cut : Fin (M + 1))
    (g : Fin (gm.groupCount cut)) :
    gm.groupCount cut *
        (Finset.univ.filter fun i =>
          gm.group cut i = g).card =
      data.totalJ := by
  let fiber (h : Fin (gm.groupCount cut)) :
      Finset (Fin data.totalJ) :=
    Finset.univ.filter fun i => gm.group cut i = h
  have h_disj :
      ∀ a ∈ (Finset.univ :
          Finset (Fin (gm.groupCount cut))),
        ∀ b ∈ (Finset.univ :
            Finset (Fin (gm.groupCount cut))),
          a ≠ b → Disjoint (fiber a) (fiber b) := by
    intro a _ b _ hab
    rw [Finset.disjoint_left]
    intro i hia hib
    have ha : gm.group cut i = a := by
      simpa [fiber] using hia
    have hb : gm.group cut i = b := by
      simpa [fiber] using hib
    exact hab (ha.symm.trans hb)
  have h_union :
      Finset.biUnion
          (Finset.univ :
            Finset (Fin (gm.groupCount cut)))
          fiber =
        Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro i
    simp only [Finset.mem_biUnion, Finset.mem_univ,
      true_and]
    exact ⟨gm.group cut i, by simp [fiber]⟩
  have h_sum_card :
      ∑ h : Fin (gm.groupCount cut),
          (fiber h).card =
        data.totalJ := by
    rw [← Finset.card_biUnion h_disj, h_union]
    simp
  have h_const :
      ∀ h : Fin (gm.groupCount cut),
        (fiber h).card = (fiber g).card := by
    intro h
    exact gm.hgroup_balanced cut h g
  calc
    gm.groupCount cut * (fiber g).card =
        ∑ _h : Fin (gm.groupCount cut),
          (fiber g).card := by
            simp [Finset.sum_const]
    _ = ∑ h : Fin (gm.groupCount cut),
          (fiber h).card := by
            apply Finset.sum_congr rfl
            intro h _
            exact (h_const h).symm
    _ = data.totalJ := h_sum_card

end GridLabelMaps

end Kakeya.Streamlined.RandomTranslation.WithShading

end
