import MyLeanRepo.Kakeya.Streamlined.DividingScales.ConditionalFactorStopping
import MyLeanRepo.Kakeya.Streamlined.DividingScales.ReferenceDensity
import MyLeanRepo.Kakeya.Streamlined.DividingScales.TubeSubfamilyImage
import MyLeanRepo.Kakeya.Streamlined.DividingScales.BodySubfamilyImage
import MyLeanRepo.Kakeya.Streamlined.DividingScales.JointRelationFrostmanUpward

/-!
# Canonical Frostman profiles for conditional factor scopes

The profile of an all-branch factor must not depend on a chosen reindexing of
its restricted cover system.  We therefore define it directly in the ambient
cover coordinates.

For one represented historical cell and one endpoint parent at scale `s`,
take the image of that cell's fine indices under the independent scale-`r`
parent map.  This is the canonical assigned scale-`r` relation family inside
that scale-`s` parent.  At the root scope it is exactly `relatedIndices r s k`.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Streamlined

namespace FrostmanConditionalFactorScope

variable {depth : ℕ} {delta A C : ℝ} {F : TubeFamily delta}
variable {hdelta_le_one : delta ≤ 1}
variable {U : ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure
  depth (A := A) (C := C) F hdelta_le_one}

/-- Fine indices in one historical cell and one scale-`s` parent fiber. -/
def endpointCell
    (P : FrostmanConditionalFactorScope U)
    (i : Fin F.card)
    (s : UniformScaleIndex delta) :
    Finset (Fin F.card) :=
  (conditionalParentCell U.coarse U.cover P.scale (P.parentOf i)).filter
    fun original => (U.cover s).parent original = (U.cover s).parent i

@[simp] lemma mem_endpointCell_iff
    (P : FrostmanConditionalFactorScope U)
    (i original : Fin F.card)
    (s : UniformScaleIndex delta) :
    original ∈ P.endpointCell i s ↔
      original ∈
        conditionalParentCell U.coarse U.cover P.scale (P.parentOf i) ∧
      (U.cover s).parent original = (U.cover s).parent i := by
  simp [endpointCell]

/-- The representing fine index belongs to its endpoint cell. -/
lemma mem_endpointCell_self
    (P : FrostmanConditionalFactorScope U)
    (i : Fin F.card)
    (s : UniformScaleIndex delta) :
    i ∈ P.endpointCell i s := by
  rw [mem_endpointCell_iff]
  exact ⟨P.mem_cell_parentOf i, rfl⟩

/-- Canonical scale-`r` parent image inside one conditional endpoint cell. -/
def relationIndices
    (P : FrostmanConditionalFactorScope U)
    (i : Fin F.card)
    (r s : UniformScaleIndex delta) :
    Finset (Fin (U.coarse r).card) :=
  (P.endpointCell i s).image (U.cover r).parent

@[simp] lemma mem_relationIndices_iff
    (P : FrostmanConditionalFactorScope U)
    (i : Fin F.card)
    (r s : UniformScaleIndex delta)
    (j : Fin (U.coarse r).card) :
    j ∈ P.relationIndices i r s ↔
      ∃ original : Fin F.card,
        original ∈
          conditionalParentCell U.coarse U.cover P.scale (P.parentOf i) ∧
        (U.cover s).parent original = (U.cover s).parent i ∧
        (U.cover r).parent original = j := by
  classical
  simp [relationIndices, endpointCell, and_assoc]

/-- Every canonical conditional relation image is nonempty. -/
lemma relationIndices_nonempty
    (P : FrostmanConditionalFactorScope U)
    (i : Fin F.card)
    (r s : UniformScaleIndex delta) :
    (P.relationIndices i r s).Nonempty := by
  refine ⟨(U.cover r).parent i, ?_⟩
  rw [mem_relationIndices_iff]
  exact ⟨i, P.mem_cell_parentOf i, rfl, rfl⟩

/-- The canonical conditional relation tube subfamily. -/
def relationSubfamily
    (P : FrostmanConditionalFactorScope U)
    (i : Fin F.card)
    (r s : UniformScaleIndex delta) :
    TubeSubfamily (U.coarse r) :=
  TubeSubfamily.fromFinset (U.coarse r) (P.relationIndices i r s)

/-- Frostman constant of one represented conditional relation family. -/
def representedRelationFrostmanConstant
    (P : FrostmanConditionalFactorScope U)
    (i : Fin F.card)
    (r s : UniformScaleIndex delta) : ENNReal :=
  (P.relationSubfamily i r s).family.toBodyFamily.frostmanConstantIn
    (dilatedTubeCarrier (independentCoverParentDilation A)
      ((U.coarse s).tube ((U.cover s).parent i)))

/--
The ambient image of the branch-local related family is the canonical scope
relation image.
-/
lemma address_relatedSubfamily_image_eq_relationIndices
    (P : FrostmanConditionalFactorScope U)
    (i : Fin F.card)
    (r s : UniformScaleIndex delta) :
    let address := P.address i
    let endpoint := P.addressEndpointParent i s
    Finset.image
        (address.branchSystem.selectedCoarse r).embedding
        (address.dilated.relatedIndices r s endpoint) =
      P.relationIndices i r s := by
  classical
  let address := P.address i
  let endpoint := P.addressEndpointParent i s
  ext j
  constructor
  · intro hj
    rcases Finset.mem_image.mp hj with ⟨jlocal, hjlocal, rfl⟩
    have hrelation := hjlocal
    dsimp only [DilatedDiscreteUniformTubeStructure.relatedIndices,
      DilatedDiscreteUniformTubeStructure.ParentRelation,
      FrostmanConditionalFactor.dilated,
      FrostmanConditionalFactor.branchLocal,
      ConditionalBranchSystem.toLocal,
      LocalDilatedDiscreteUniformTubeStructure.toDilated] at hrelation
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hrelation
    rcases hrelation with ⟨localIndex, hr, hs⟩
    let S := TubeSubfamily.fromFinset F
      (conditionalParentCell U.coarse U.cover P.scale (P.parentOf i))
    let original : Fin F.card := S.embedding localIndex
    rw [mem_relationIndices_iff]
    refine ⟨original, ?_, ?_, ?_⟩
    · exact Finset.orderEmbOfFin_mem
        (conditionalParentCell U.coarse U.cover
          P.scale (P.parentOf i)) rfl localIndex
    · have hcompat :=
        address.branchSystem.parent_compatible s localIndex
      change
        (address.branchSystem.selectedCoarse s).embedding
            ((address.branchSystem.restrictedCover s).parent localIndex) =
          (U.cover s).parent (S.embedding localIndex) at hcompat
      rw [hs, P.addressEndpointParent_ambient i s] at hcompat
      exact hcompat.symm
    · have hcompat :=
        address.branchSystem.parent_compatible r localIndex
      change
        (address.branchSystem.selectedCoarse r).embedding
            ((address.branchSystem.restrictedCover r).parent localIndex) =
          (U.cover r).parent (S.embedding localIndex) at hcompat
      rw [hr] at hcompat
      exact hcompat.symm
  · intro hj
    have hcanonical :=
      (mem_relationIndices_iff P i r s j).mp hj
    rcases hcanonical with ⟨original, hhistory, hs, hr⟩
    let S := TubeSubfamily.fromFinset F
      (conditionalParentCell U.coarse U.cover P.scale (P.parentOf i))
    have horiginalImage :
        original ∈ Finset.image S.embedding Finset.univ := by
      change original ∈ Finset.image
        ((conditionalParentCell U.coarse U.cover
          P.scale (P.parentOf i)).orderEmbOfFin rfl) Finset.univ
      rw [Finset.image_orderEmbOfFin_univ
        (conditionalParentCell U.coarse U.cover
          P.scale (P.parentOf i)) rfl]
      exact hhistory
    rcases Finset.mem_image.mp horiginalImage with
      ⟨localIndex, _hlocal, hlocalOriginal⟩
    let jlocal := (address.branchSystem.restrictedCover r).parent localIndex
    refine Finset.mem_image.mpr ⟨jlocal, ?_, ?_⟩
    · dsimp only [DilatedDiscreteUniformTubeStructure.relatedIndices,
        DilatedDiscreteUniformTubeStructure.ParentRelation,
        FrostmanConditionalFactor.dilated,
        FrostmanConditionalFactor.branchLocal,
        ConditionalBranchSystem.toLocal,
        LocalDilatedDiscreteUniformTubeStructure.toDilated]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨localIndex, rfl, ?_⟩
      apply (address.branchSystem.selectedCoarse s).embedding.injective
      have hcompat :=
        address.branchSystem.parent_compatible s localIndex
      change
        (address.branchSystem.selectedCoarse s).embedding
            ((address.branchSystem.restrictedCover s).parent localIndex) =
          (U.cover s).parent (S.embedding localIndex) at hcompat
      rw [hcompat,
        hlocalOriginal, hs,
        P.addressEndpointParent_ambient i s]
    · have hcompat :=
        address.branchSystem.parent_compatible r localIndex
      change
        (address.branchSystem.selectedCoarse r).embedding
            ((address.branchSystem.restrictedCover r).parent localIndex) =
          (U.cover r).parent (S.embedding localIndex) at hcompat
      rw [hcompat, hlocalOriginal, hr]

/-- Branch-local related parents, composed into the ambient coarse family. -/
abbrev addressLocalRelationSubfamily
    (P : FrostmanConditionalFactorScope U)
    (i : Fin F.card)
    (r s : UniformScaleIndex delta) :
    TubeSubfamily
      ((P.address i).branchSystem.selectedCoarse r).family :=
  (P.address i).dilated.relatedSubfamily r s
    (P.addressEndpointParent i s)

/-- Branch-local related parents, composed into the ambient coarse family. -/
def addressRelationAmbientSubfamily
    (P : FrostmanConditionalFactorScope U)
    (i : Fin F.card)
    (r s : UniformScaleIndex delta) :
    TubeSubfamily (U.coarse r) :=
  let address := P.address i
  TubeSubfamily.comp
    (address.branchSystem.selectedCoarse r)
    (P.addressLocalRelationSubfamily i r s)

/-- Branch-local and canonical scope relation families have the same ambient image. -/
lemma addressRelationAmbientSubfamily_image_eq
    (P : FrostmanConditionalFactorScope U)
    (i : Fin F.card)
    (r s : UniformScaleIndex delta) :
    Finset.image
        (P.addressRelationAmbientSubfamily i r s).embedding Finset.univ =
      Finset.image (P.relationSubfamily i r s).embedding Finset.univ := by
  classical
  let address := P.address i
  let endpoint := P.addressEndpointParent i s
  have hlocalImage :
      Finset.image
          (P.addressLocalRelationSubfamily i r s).embedding Finset.univ =
        address.dilated.relatedIndices r s endpoint := by
    change
      Finset.image
          ((address.dilated.relatedIndices r s endpoint).orderEmbOfFin rfl)
          Finset.univ =
        address.dilated.relatedIndices r s endpoint
    exact Finset.image_orderEmbOfFin_univ
      (address.dilated.relatedIndices r s endpoint) rfl
  have hcanonicalImage :
      Finset.image (P.relationSubfamily i r s).embedding Finset.univ =
        P.relationIndices i r s := by
    change
      Finset.image ((P.relationIndices i r s).orderEmbOfFin rfl)
          Finset.univ =
        P.relationIndices i r s
    exact Finset.image_orderEmbOfFin_univ
      (P.relationIndices i r s) rfl
  dsimp only [addressRelationAmbientSubfamily, TubeSubfamily.comp]
  change
    Finset.image
        (fun localIndex =>
          (address.branchSystem.selectedCoarse r).embedding
            ((P.addressLocalRelationSubfamily i r s).embedding
              localIndex))
        Finset.univ =
      Finset.image (P.relationSubfamily i r s).embedding Finset.univ
  calc
    Finset.image
          (fun localIndex =>
            (address.branchSystem.selectedCoarse r).embedding
              ((P.addressLocalRelationSubfamily i r s).embedding
                localIndex))
          Finset.univ
        =
      Finset.image
        (address.branchSystem.selectedCoarse r).embedding
        (Finset.image
          (P.addressLocalRelationSubfamily i r s).embedding
          Finset.univ) := by
            exact Finset.image_image.symm
    _ =
      Finset.image
        (address.branchSystem.selectedCoarse r).embedding
        (address.dilated.relatedIndices r s endpoint) := by
          rw [hlocalImage]
    _ = P.relationIndices i r s :=
      P.address_relatedSubfamily_image_eq_relationIndices i r s
    _ =
      Finset.image (P.relationSubfamily i r s).embedding Finset.univ := by
        rw [hcanonicalImage]

/-- Canonical scope profile equals the branch-local assigned relation profile. -/
lemma representedRelationFrostmanConstant_eq_address
    (P : FrostmanConditionalFactorScope U)
    (i : Fin F.card)
    (r s : UniformScaleIndex delta) :
    P.representedRelationFrostmanConstant i r s =
      (P.address i).dilated.assignedRelationFrostmanConstant r s
        (P.addressEndpointParent i s) := by
  let address := P.address i
  let endpoint := P.addressEndpointParent i s
  let V :=
    dilatedTubeCarrier (independentCoverParentDilation A)
      ((U.coarse s).tube ((U.cover s).parent i))
  have hparentTube :
      ((address.branchLocal.coarse s).tube endpoint) =
        (U.coarse s).tube ((U.cover s).parent i) := by
    change
      (address.branchSystem.selectedCoarse s).family.tube endpoint =
        (U.coarse s).tube ((U.cover s).parent i)
    rw [(address.branchSystem.selectedCoarse s).tube_eq endpoint]
    rw [P.addressEndpointParent_ambient i s]
  unfold representedRelationFrostmanConstant
  unfold DilatedDiscreteUniformTubeStructure.assignedRelationFrostmanConstant
  change
    (P.relationSubfamily i r s).family.toBodyFamily.frostmanConstantIn V =
      (address.dilated.relatedSubfamily r s endpoint).family.toBodyFamily.frostmanConstantIn
          (dilatedTubeCarrier (independentCoverParentDilation A)
            ((address.branchLocal.coarse s).tube endpoint))
  rw [hparentTube]
  have himage :=
    P.addressRelationAmbientSubfamily_image_eq i r s
  exact
    (P.relationSubfamily i r s).frostmanConstantIn_eq_of_image_eq
      (P.addressRelationAmbientSubfamily i r s) himage.symm V

/-- Maximum represented relation profile on a scope. -/
def relationFrostmanMax
    (hF : F.Nonempty)
    (P : FrostmanConditionalFactorScope U)
    (r s : UniformScaleIndex delta) : ENNReal :=
  Finset.univ.sup' (by
    let i : Fin F.card := ⟨0, hF⟩
    exact ⟨i, Finset.mem_univ i⟩)
    fun i => P.representedRelationFrostmanConstant i r s

/-- Every represented relation constant is bounded by the scope maximum. -/
lemma representedRelationFrostmanConstant_le_max
    (hF : F.Nonempty)
    (P : FrostmanConditionalFactorScope U)
    (i : Fin F.card)
    (r s : UniformScaleIndex delta) :
    P.representedRelationFrostmanConstant i r s ≤
      P.relationFrostmanMax hF r s := by
  exact Finset.le_sup'
    (fun original : Fin F.card =>
      P.representedRelationFrostmanConstant original r s)
    (Finset.mem_univ i)

/-- A uniform represented upper bound is equivalent to the scope maximum. -/
lemma relationFrostmanMax_le_iff
    (hF : F.Nonempty)
    (P : FrostmanConditionalFactorScope U)
    (r s : UniformScaleIndex delta)
    (bound : ENNReal) :
    P.relationFrostmanMax hF r s ≤ bound ↔
      ∀ i : Fin F.card,
        P.representedRelationFrostmanConstant i r s ≤ bound := by
  constructor
  · intro h i
    exact (P.representedRelationFrostmanConstant_le_max hF i r s).trans h
  · intro h
    exact Finset.sup'_le _ _ fun i _ => h i

/-- A lower bound for the scope maximum has a represented-cell witness. -/
lemma le_relationFrostmanMax_iff
    (hF : F.Nonempty)
    (P : FrostmanConditionalFactorScope U)
    (r s : UniformScaleIndex delta)
    (bound : ENNReal) :
    bound ≤ P.relationFrostmanMax hF r s ↔
      ∃ i : Fin F.card,
        bound ≤ P.representedRelationFrostmanConstant i r s := by
  let indices : Finset (Fin F.card) := Finset.univ
  have hindices : indices.Nonempty := by
    let i : Fin F.card := ⟨0, hF⟩
    exact ⟨i, Finset.mem_univ i⟩
  rcases Finset.exists_mem_eq_sup' hindices
      (fun i => P.representedRelationFrostmanConstant i r s) with
    ⟨imax, _himax, himax⟩
  constructor
  · intro h
    refine ⟨imax, ?_⟩
    rw [← himax]
    exact h
  · rintro ⟨i, hi⟩
    exact hi.trans <| Finset.le_sup'
      (fun original : Fin F.card =>
        P.representedRelationFrostmanConstant original r s)
      (Finset.mem_univ i)

/-- Scope profile used by the abstract stopping logic. -/
def intermediateProfile
    (hF : F.Nonempty)
    (P : FrostmanConditionalFactorScope U)
    (q : UniformScaleIndex delta) : ENNReal :=
  P.relationFrostmanMax hF P.fine q

/--
For the inner child, the represented fine-to-middle relation image is exactly
the parent scope's fine-to-middle relation image.
-/
lemma innerChild_relationIndices
    (P : FrostmanConditionalFactorScope U)
    (hroom : P.coordinateCount < depth)
    (middle : UniformScaleIndex delta)
    (hfine_middle :
      (uniformScale delta hdelta_le_one P.fine).1 ≤
        (uniformScale delta hdelta_le_one middle).1)
    (i : Fin F.card) :
    (P.innerChild hroom middle hfine_middle).relationIndices
        i P.fine middle =
      P.relationIndices i P.fine middle := by
  classical
  ext j
  rw [mem_relationIndices_iff]
  rw [mem_relationIndices_iff]
  constructor
  · rintro ⟨original, hhistory, hmiddle, hfine⟩
    refine ⟨original, ?_, hmiddle, hfine⟩
    rw [mem_conditionalParentCell_iff] at hhistory ⊢
    intro t
    have h := hhistory t.castSucc
    rw [P.innerChild_scale_castSucc,
      P.innerChild_parentOf_castSucc] at h
    exact h
  · rintro ⟨original, hhistory, hmiddle, hfine⟩
    refine ⟨original, ?_, hmiddle, hfine⟩
    rw [mem_conditionalParentCell_iff]
    intro t
    refine Fin.lastCases ?_ (fun old => ?_) t
    · rw [P.innerChild_scale_last,
        P.innerChild_parentOf_last]
      exact congrArg Fin.val hmiddle
    · rw [P.innerChild_scale_castSucc,
        P.innerChild_parentOf_castSucc]
      exact
        (mem_conditionalParentCell_iff
          U.coarse U.cover P.scale (P.parentOf i) original).mp
            hhistory old

/-- Inner-child represented profile equals the parent intermediate profile. -/
lemma innerChild_representedRelationFrostmanConstant
    (P : FrostmanConditionalFactorScope U)
    (hroom : P.coordinateCount < depth)
    (middle : UniformScaleIndex delta)
    (hfine_middle :
      (uniformScale delta hdelta_le_one P.fine).1 ≤
        (uniformScale delta hdelta_le_one middle).1)
    (i : Fin F.card) :
    representedRelationFrostmanConstant
        (P.innerChild hroom middle hfine_middle) i P.fine middle =
      P.representedRelationFrostmanConstant i P.fine middle := by
  unfold representedRelationFrostmanConstant
  unfold relationSubfamily
  congr 2
  rw [innerChild_relationIndices]

/-- Inner-child maximum equals the parent intermediate maximum. -/
lemma innerChild_relationFrostmanMax
    (hF : F.Nonempty)
    (P : FrostmanConditionalFactorScope U)
    (hroom : P.coordinateCount < depth)
    (middle : UniformScaleIndex delta)
    (hfine_middle :
      (uniformScale delta hdelta_le_one P.fine).1 ≤
        (uniformScale delta hdelta_le_one middle).1) :
    relationFrostmanMax hF
        (P.innerChild hroom middle hfine_middle) P.fine middle =
      P.relationFrostmanMax hF P.fine middle := by
  apply le_antisymm
  · rw [relationFrostmanMax_le_iff]
    intro i
    rw [innerChild_representedRelationFrostmanConstant]
    exact P.representedRelationFrostmanConstant_le_max
      hF i P.fine middle
  · rw [relationFrostmanMax_le_iff]
    intro i
    rw [← innerChild_representedRelationFrostmanConstant]
    exact
      representedRelationFrostmanConstant_le_max hF
        (P.innerChild hroom middle hfine_middle) i P.fine middle

/--
The outer child relation profile is bounded by the parent profile with one
per-split geometric loss.
-/
lemma outerChild_representedRelationFrostmanConstant_le
    (hA : 1 ≤ A) (hdelta : 0 < delta)
    (hF_ball : F.IsInUnitBall)
    (P : FrostmanConditionalFactorScope U)
    (hdepth : P.coordinateCount + 1 ≤ depth)
    (middle : UniformScaleIndex delta)
    (hfine_middle :
      (uniformScale delta hdelta_le_one P.fine).1 ≤
        (uniformScale delta hdelta_le_one middle).1)
    (hmiddle_coarse :
      (uniformScale delta hdelta_le_one middle).1 ≤
        (uniformScale delta hdelta_le_one P.coarse).1)
    (i : Fin F.card) :
    representedRelationFrostmanConstant
        (P.outerChild middle hmiddle_coarse) i middle P.coarse ≤
      U.uniformity ^ 2 * parentEnvelopeVolumeFactor A *
        P.representedRelationFrostmanConstant i P.fine P.coarse := by
  have haddress :=
    (P.jointAddress hdepth i).assignedRelationFrostmanConstant_upward
      hA hdelta (P.address_family_isInUnitBall i hF_ball)
      P.fine middle P.coarse hfine_middle hmiddle_coarse
      (P.addressEndpointParent i P.coarse)
  rw [P.jointAddress_uniformity hdepth i,
    P.jointAddress_assignedRelationFrostmanConstant
      hdepth i middle P.coarse (P.addressEndpointParent i P.coarse),
    P.jointAddress_assignedRelationFrostmanConstant
      hdepth i P.fine P.coarse (P.addressEndpointParent i P.coarse)]
      at haddress
  have hparentAddress :=
    P.representedRelationFrostmanConstant_eq_address
      i P.fine P.coarse
  have houterAddress :
      representedRelationFrostmanConstant
          (P.outerChild middle hmiddle_coarse) i middle P.coarse =
        (P.address i).dilated.assignedRelationFrostmanConstant
          middle P.coarse (P.addressEndpointParent i P.coarse) := by
    rw [representedRelationFrostmanConstant_eq_address]
    rfl
  rw [houterAddress, hparentAddress]
  exact haddress

/-- Outer-child maximum inherits the parent maximum with the same loss. -/
lemma outerChild_relationFrostmanMax_le
    (hA : 1 ≤ A) (hdelta : 0 < delta)
    (hF : F.Nonempty) (hF_ball : F.IsInUnitBall)
    (P : FrostmanConditionalFactorScope U)
    (hdepth : P.coordinateCount + 1 ≤ depth)
    (middle : UniformScaleIndex delta)
    (hfine_middle :
      (uniformScale delta hdelta_le_one P.fine).1 ≤
        (uniformScale delta hdelta_le_one middle).1)
    (hmiddle_coarse :
      (uniformScale delta hdelta_le_one middle).1 ≤
        (uniformScale delta hdelta_le_one P.coarse).1) :
    relationFrostmanMax hF
        (P.outerChild middle hmiddle_coarse) middle P.coarse ≤
      U.uniformity ^ 2 * parentEnvelopeVolumeFactor A *
        P.relationFrostmanMax hF P.fine P.coarse := by
  rw [relationFrostmanMax_le_iff]
  intro i
  exact
    (P.outerChild_representedRelationFrostmanConstant_le
      hA hdelta hF_ball hdepth middle
      hfine_middle hmiddle_coarse i).trans <| by
        gcongr
        exact P.representedRelationFrostmanConstant_le_max
          hF i P.fine P.coarse

/--
At the root scope, the canonical conditional relation image is exactly the
existing common-child relation fiber.
-/
lemma root_relationIndices_eq_relatedIndices
    (hdelta : 0 < delta)
    (i : Fin F.card)
    (r s : UniformScaleIndex delta) :
    ((FrostmanConditionalFactorState.rootFactor
      (U := U) hdelta).relationIndices i r s) =
      U.toLocalDilatedDiscreteUniformTubeStructure.toDilated.relatedIndices
        r s ((U.cover s).parent i) := by
  classical
  ext j
  rw [mem_relationIndices_iff]
  dsimp only [DilatedDiscreteUniformTubeStructure.relatedIndices,
    DilatedDiscreteUniformTubeStructure.ParentRelation,
    LocalDilatedDiscreteUniformTubeStructure.toDilated]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨original, _history, hs, hr⟩
    exact ⟨original, hr, hs⟩
  · rintro ⟨original, hr, hs⟩
    refine ⟨original, ?_, hs, hr⟩
    rw [mem_conditionalParentCell_iff]
    intro t
    exact Fin.elim0 t

/-- Root represented profile is the existing assigned relation constant. -/
lemma root_representedRelationFrostmanConstant
    (hdelta : 0 < delta)
    (i : Fin F.card)
    (r s : UniformScaleIndex delta) :
    (FrostmanConditionalFactorState.rootFactor
        (U := U) hdelta).representedRelationFrostmanConstant i r s =
      DilatedDiscreteUniformTubeStructure.assignedRelationFrostmanConstant
        U.toLocalDilatedDiscreteUniformTubeStructure.toDilated
        r s ((U.cover s).parent i) := by
  unfold representedRelationFrostmanConstant
  unfold DilatedDiscreteUniformTubeStructure.assignedRelationFrostmanConstant
  unfold relationSubfamily
  unfold DilatedDiscreteUniformTubeStructure.relatedSubfamily
  dsimp only [LocalDilatedDiscreteUniformTubeStructure.toDilated]
  congr 2
  rw [root_relationIndices_eq_relatedIndices]
  rfl

/--
The root scope maximum is exactly the existing global assigned relation
profile.  Surjectivity of the endpoint cover ensures every parent is
represented by some original fine index.
-/
lemma root_relationFrostmanMax
    (hdelta : 0 < delta)
    (hF : F.Nonempty)
    (r s : UniformScaleIndex delta) :
    (FrostmanConditionalFactorState.rootFactor
        (U := U) hdelta).relationFrostmanMax hF r s =
      DilatedDiscreteUniformTubeStructure.relationFrostmanMax
        U.toLocalDilatedDiscreteUniformTubeStructure.toDilated hF r s := by
  apply le_antisymm
  · rw [relationFrostmanMax_le_iff]
    intro i
    rw [root_representedRelationFrostmanConstant]
    exact
      DilatedDiscreteUniformTubeStructure.relationFrostmanConstant_le_max
        U.toLocalDilatedDiscreteUniformTubeStructure.toDilated
        hF r s ((U.cover s).parent i)
  · rw [DilatedDiscreteUniformTubeStructure.relationFrostmanMax_le_iff
      U.toLocalDilatedDiscreteUniformTubeStructure.toDilated hF r s]
    intro k
    rcases (U.cover s).parent_surjective k with ⟨i, hi⟩
    rw [← hi, ← root_representedRelationFrostmanConstant]
    exact
      (FrostmanConditionalFactorState.rootFactor
        (U := U) hdelta).representedRelationFrostmanConstant_le_max
          hF i r s

/-- At the finest endpoint, the selected coarse family is the identity family. -/
lemma finest_coarse_card_eq
    (hF : F.Nonempty) :
    (U.coarse (Fin.last (uniformScaleSteps delta))).card = F.card := by
  let r := Fin.last (uniformScaleSteps delta)
  have hsurj :=
    (U.cover r).parent_surjective
  have hbij :
      Function.Bijective (U.cover r).parent :=
    ⟨U.finest_parent_injective, hsurj⟩
  simpa [r] using
    (Fintype.card_congr
      (Equiv.ofBijective (U.cover r).parent hbij)).symm

/-- The unit endpoint selected coarse family has exactly one parent. -/
lemma coarsest_coarse_card_eq_one
    (hF : F.Nonempty) :
    (U.coarse
      (⟨0, Nat.succ_pos _⟩ : UniformScaleIndex delta)).card = 1 := by
  let s : UniformScaleIndex delta := ⟨0, Nat.succ_pos _⟩
  have hpos :
      0 < (U.coarse s).card := by
    let i : Fin F.card := ⟨0, hF⟩
    exact lt_of_le_of_lt (Nat.zero_le _) ((U.cover s).parent i).isLt
  have hle : (U.coarse s).card ≤ 1 := by
    by_contra h
    have htwo : 2 ≤ (U.coarse s).card := by omega
    let j : Fin (U.coarse s).card := ⟨0, by omega⟩
    let k : Fin (U.coarse s).card := ⟨1, by omega⟩
    have hjk := U.coarsest_parent_unique j k
    have hval := congrArg Fin.val hjk
    dsimp only [j, k] at hval
    omega
  exact Nat.le_antisymm hle hpos

/-- The canonical finest coarse family, viewed as a body subfamily of the input. -/
def finestCoarseAsBodySubfamily :
    Subfamily F.toBodyFamily := by
  let r := Fin.last (uniformScaleSteps delta)
  let e :
      Fin F.card ≃ Fin (U.coarse r).card :=
    Equiv.ofBijective (U.cover r).parent
      ⟨U.finest_parent_injective, (U.cover r).parent_surjective⟩
  exact {
    family := (U.coarse r).toBodyFamily
    embedding := e.symm.toEmbedding
    carrier_eq := by
      intro j
      change ((U.coarse r).tube j).carrier =
        (F.tube (e.symm j)).carrier
      have h := U.finest_parent_carrier_eq (e.symm j)
      rw [show (U.cover r).parent (e.symm j) = j by
        exact e.apply_symm_apply j] at h
      exact h
  }

/-- The finest coarse body subfamily uses every ambient input index. -/
lemma finestCoarseAsBodySubfamily_image :
    Finset.image
        (finestCoarseAsBodySubfamily (U := U)).embedding Finset.univ =
      (Finset.univ : Finset (Fin F.card)) := by
  classical
  ext i
  constructor
  · intro _
    exact Finset.mem_univ i
  · intro _
    let r := Fin.last (uniformScaleSteps delta)
    let e :
        Fin F.card ≃ Fin (U.coarse r).card :=
      Equiv.ofBijective (U.cover r).parent
        ⟨U.finest_parent_injective, (U.cover r).parent_surjective⟩
    refine Finset.mem_image.mpr ⟨e i, Finset.mem_univ _, ?_⟩
    change e.symm (e i) = i
    exact e.symm_apply_apply i

/-- At the canonical endpoints, every finest parent is related to the unique unit parent. -/
lemma root_endpoint_relationIndices_eq_univ
    (hdelta : 0 < delta)
    (hF : F.Nonempty)
    (i : Fin F.card) :
    (FrostmanConditionalFactorState.rootFactor
        (U := U) hdelta).relationIndices i
          (Fin.last (uniformScaleSteps delta))
          (⟨0, Nat.succ_pos _⟩ : UniformScaleIndex delta) =
      (Finset.univ :
        Finset (Fin
          (U.coarse (Fin.last (uniformScaleSteps delta))).card)) := by
  classical
  ext j
  simp only [Finset.mem_univ, iff_true]
  rw [mem_relationIndices_iff]
  rcases (U.cover (Fin.last (uniformScaleSteps delta))).parent_surjective j with
    ⟨original, hparent⟩
  refine ⟨original, ?_, ?_, hparent⟩
  · rw [mem_conditionalParentCell_iff]
    intro t
    exact Fin.elim0 t
  · exact U.coarsest_parent_unique _ _

/-- Root endpoint relation family has every finest coarse parent. -/
lemma root_endpoint_relationSubfamily_image
    (hdelta : 0 < delta)
    (hF : F.Nonempty)
    (i : Fin F.card) :
    Finset.image
        ((FrostmanConditionalFactorState.rootFactor
          (U := U) hdelta).relationSubfamily i
            (Fin.last (uniformScaleSteps delta))
            (⟨0, Nat.succ_pos _⟩ : UniformScaleIndex delta)).embedding
        Finset.univ =
      (Finset.univ :
        Finset (Fin
          (U.coarse (Fin.last (uniformScaleSteps delta))).card)) := by
  change
    Finset.image
        (((FrostmanConditionalFactorState.rootFactor
          (U := U) hdelta).relationIndices i
            (Fin.last (uniformScaleSteps delta))
            (⟨0, Nat.succ_pos _⟩ : UniformScaleIndex delta)).orderEmbOfFin rfl)
        Finset.univ = _
  rw [Finset.image_orderEmbOfFin_univ]
  exact root_endpoint_relationIndices_eq_univ hdelta hF i

/-- Root endpoint relation family, embedded back into the original body family. -/
def rootEndpointAsBodySubfamily
    (hdelta : 0 < delta)
    (i : Fin F.card) :
    Subfamily F.toBodyFamily :=
  let relation :=
    (FrostmanConditionalFactorState.rootFactor
      (U := U) hdelta).relationSubfamily i
        (Fin.last (uniformScaleSteps delta))
        (⟨0, Nat.succ_pos _⟩ : UniformScaleIndex delta)
  Subfamily.comp
    (finestCoarseAsBodySubfamily (U := U))
    relation.toBodySubfamily

/-- The embedded root endpoint relation family uses every input index. -/
lemma rootEndpointAsBodySubfamily_image
    (hdelta : 0 < delta)
    (hF : F.Nonempty)
    (i : Fin F.card) :
    Finset.image
        (rootEndpointAsBodySubfamily (U := U) hdelta i).embedding
        Finset.univ =
      (Finset.univ : Finset (Fin F.card)) := by
  classical
  let r := Fin.last (uniformScaleSteps delta)
  let s : UniformScaleIndex delta := ⟨0, Nat.succ_pos _⟩
  let relation :=
    (FrostmanConditionalFactorState.rootFactor
      (U := U) hdelta).relationSubfamily i
        r s
  let finest := finestCoarseAsBodySubfamily (U := U)
  let e :
      Fin F.card ≃ Fin (U.coarse r).card :=
    Equiv.ofBijective (U.cover r).parent
      ⟨U.finest_parent_injective, (U.cover r).parent_surjective⟩
  ext original
  constructor
  · intro _
    exact Finset.mem_univ original
  · intro _
    have hcoarse :
        e original ∈ Finset.image relation.embedding Finset.univ := by
      rw [show Finset.image relation.embedding Finset.univ =
          (Finset.univ : Finset (Fin (U.coarse r).card)) by
        exact root_endpoint_relationSubfamily_image hdelta hF i]
      exact Finset.mem_univ _
    rcases Finset.mem_image.mp hcoarse with
      ⟨localIndex, _hlocal, hlocalImage⟩
    refine Finset.mem_image.mpr
      ⟨localIndex, Finset.mem_univ _, ?_⟩
    change e.symm (relation.embedding localIndex) = original
    rw [hlocalImage, e.symm_apply_apply]

/-- The embedded root endpoint relation family is a reindexing of `F`. -/
lemma rootEndpoint_frostmanConstantIn_eq
    (hdelta : 0 < delta)
    (hF : F.Nonempty)
    (i : Fin F.card)
    (V : Set Point3) :
    (rootEndpointAsBodySubfamily (U := U) hdelta i).family.frostmanConstantIn V =
      F.toBodyFamily.frostmanConstantIn V := by
  let identity := Subfamily.identity F.toBodyFamily
  apply Subfamily.frostmanConstantIn_eq_of_image_eq
    (rootEndpointAsBodySubfamily (U := U) hdelta i) identity
  · rw [rootEndpointAsBodySubfamily_image hdelta hF i]
    ext j
    constructor
    · intro _
      exact Finset.mem_image.mpr
        ⟨j, Finset.mem_univ j, rfl⟩
    · intro _
      exact Finset.mem_univ j

end FrostmanConditionalFactorScope

end Kakeya.Streamlined
