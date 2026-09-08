import MyLeanRepo.Kakeya.Streamlined.DividingScales.ReferenceDensity
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.Submultiplicativity

/-!
# Full containment fibers as ambient restrictions

Inside their reference parent, the full fine and parent containment fibers
have exactly the same contained mass as the corresponding ambient family.
This records the literal paper semantics of `T[T_rho]`.
-/

noncomputable section

namespace Kakeya.Streamlined

namespace TubeFamily

/-- Ambient tube indices whose carriers lie in `K`. -/
def indicesIn {rho : ℝ} (G : TubeFamily rho) (K : Set Point3) :
    Finset (Fin G.card) := by
  classical
  exact Finset.univ.filter fun i => (G.tube i).carrier ⊆ K

@[simp] lemma mem_indicesIn_iff
    {rho : ℝ} (G : TubeFamily rho) (K : Set Point3)
    (i : Fin G.card) :
    i ∈ G.indicesIn K ↔ (G.tube i).carrier ⊆ K := by
  simp [indicesIn]

end TubeFamily

namespace TubeSubfamily

/-- Contained mass of a tube subfamily is the ambient-volume sum over the
embedded contained indices. -/
lemma containedMass_eq_ambient_sum
    {rho : ℝ} {G : TubeFamily rho}
    (S : TubeSubfamily G) (K : Set Point3) :
    S.family.toBodyFamily.containedMass K =
      ∑ i ∈ Finset.image S.embedding
          (S.family.indicesIn K),
        (G.tube i).volume := by
  classical
  let J := S.family.indicesIn K
  change (∑ j ∈ J, (S.family.tube j).volume) =
    ∑ i ∈ Finset.image S.embedding J, (G.tube i).volume
  have hsum :
      ∑ j ∈ J, (S.family.tube j).volume =
        ∑ j ∈ J, (G.tube (S.embedding j)).volume := by
    apply Finset.sum_congr rfl
    intro j _
    rw [S.tube_eq j]
  rw [hsum]
  rw [Finset.sum_image]
  exact fun i _ j _ hij => S.embedding.injective hij

/-- If the ambient image of a tube subfamily is exactly the tubes contained
in `U`, then inside every `K ⊆ U` its contained mass equals ambient contained
mass. -/
lemma containedMass_eq_ambient_of_image_eq
    {rho : ℝ} {G : TubeFamily rho}
    (S : TubeSubfamily G) (U K : Set Point3)
    (himage :
      Finset.image S.embedding Finset.univ =
        G.indicesIn U)
    (hKU : K ⊆ U) :
    S.family.toBodyFamily.containedMass K =
      G.toBodyFamily.containedMass K := by
  classical
  have hfilter :
      Finset.image S.embedding
          (S.family.indicesIn K) =
        G.indicesIn K := by
    apply Finset.ext
    intro i
    constructor
    · intro hi
      rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
      have hjK :
          (S.family.tube j).carrier ⊆ K :=
        (Finset.mem_filter.mp hj).2
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, by
          rw [← S.tube_eq j]
          exact hjK⟩
    · intro hi
      have hiK :
          (G.tube i).carrier ⊆ K :=
        (Finset.mem_filter.mp hi).2
      have hiU :
          i ∈ G.indicesIn U :=
        (G.mem_indicesIn_iff U i).2 (hiK.trans hKU)
      have hi_image :
          i ∈ Finset.image S.embedding Finset.univ := by
        rw [himage]
        exact hiU
      rcases Finset.mem_image.mp hi_image with
        ⟨j, _hj, hj_embed⟩
      refine Finset.mem_image.mpr ⟨j, ?_, hj_embed⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, by
          rw [S.tube_eq j, hj_embed]
          exact hiK⟩
  rw [S.containedMass_eq_ambient_sum K, hfilter]
  change
    (∑ i ∈ G.indicesIn K, (G.tube i).volume) =
    G.toBodyFamily.containedMass K
  rfl

end TubeSubfamily

namespace DilatedDiscreteUniformTubeStructure

variable {delta A : ℝ} {F : TubeFamily delta}
variable {hdelta_le_one : delta ≤ 1}
variable (U : DilatedDiscreteUniformTubeStructure
  (A := A) F hdelta_le_one)

/-- In a subset of the reference parent, the full fine fiber has exactly the
ambient fine contained mass. -/
lemma containedFineMass_restrict
    (r : UniformScaleIndex delta)
    (j : Fin (U.coarse r).card)
    {K : Set Point3}
    (hK :
      K ⊆ dilatedTubeCarrier A ((U.coarse r).tube j)) :
    (U.containedFineSubfamily r j).family.toBodyFamily.containedMass K =
      F.toBodyFamily.containedMass K := by
  apply
    (U.containedFineSubfamily r j).containedMass_eq_ambient_of_image_eq
      (dilatedTubeCarrier A ((U.coarse r).tube j)) K
  · have himage :
      Finset.image (U.containedFineSubfamily r j).embedding Finset.univ =
        U.containedFineIndices r j :=
    Finset.image_orderEmbOfFin_univ
      (U.containedFineIndices r j) rfl
    rw [himage]
    rfl
  · exact hK

/-- In a subset of the relation reference parent, the full parent fiber and
the ambient scale-`r` family have identical contained mass. -/
lemma containedParentMass_restrict
    (r s : UniformScaleIndex delta)
    (k : Fin (U.coarse s).card)
    {K : Set Point3}
    (hK :
      K ⊆
        dilatedTubeCarrier (independentCoverParentDilation A)
          ((U.coarse s).tube k)) :
    (U.containedParentSubfamily r s k).family.toBodyFamily.containedMass K =
      (U.coarse r).toBodyFamily.containedMass K := by
  let R := U.containedParentSubfamily r s k
  apply R.containedMass_eq_ambient_of_image_eq
    (dilatedTubeCarrier (independentCoverParentDilation A)
      ((U.coarse s).tube k)) K
  · have himage :
      Finset.image R.embedding Finset.univ =
        U.containedParentIndices r s k :=
    Finset.image_orderEmbOfFin_univ
      (U.containedParentIndices r s k) rfl
    rw [himage]
    rfl
  · exact hK

/-- The full fine-fiber Frostman constant is exactly the ambient fine-family
Frostman constant relative to the same parent. -/
lemma fineFiberFrostmanConstant_eq_ambient
    (r : UniformScaleIndex delta)
    (j : Fin (U.coarse r).card) :
    U.fineFiberFrostmanConstant r j =
      F.toBodyFamily.frostmanConstantIn
        (dilatedTubeCarrier A ((U.coarse r).tube j)) := by
  let S := U.containedFineSubfamily r j
  let V := dilatedTubeCarrier A ((U.coarse r).tube j)
  have hmassV :
      S.family.toBodyFamily.containedMass V =
        F.toBodyFamily.containedMass V :=
    U.containedFineMass_restrict r j Set.Subset.rfl
  have hdensityV :
      S.family.toBodyFamily.density V =
        F.toBodyFamily.density V := by
    dsimp only [BodyFamily.density]
    rw [hmassV]
  have hsets :
      {c : ENNReal |
        ∃ K : Set Point3, Convex ℝ K ∧ K ⊆ V ∧
          c = S.family.toBodyFamily.density K /
            S.family.toBodyFamily.density V} =
      {c : ENNReal |
        ∃ K : Set Point3, Convex ℝ K ∧ K ⊆ V ∧
          c = F.toBodyFamily.density K /
            F.toBodyFamily.density V} := by
    ext c
    constructor
    · rintro ⟨K, hK, hKV, rfl⟩
      have hmassK :
          S.family.toBodyFamily.containedMass K =
            F.toBodyFamily.containedMass K :=
        U.containedFineMass_restrict r j hKV
      refine ⟨K, hK, hKV, ?_⟩
      dsimp only [BodyFamily.density]
      rw [hmassK, hmassV]
    · rintro ⟨K, hK, hKV, rfl⟩
      have hmassK :
          S.family.toBodyFamily.containedMass K =
            F.toBodyFamily.containedMass K :=
        U.containedFineMass_restrict r j hKV
      refine ⟨K, hK, hKV, ?_⟩
      dsimp only [BodyFamily.density]
      rw [hmassK, hmassV]
  dsimp only [fineFiberFrostmanConstant,
    BodyFamily.frostmanConstantIn]
  exact congrArg sSup hsets

/-- The full relation-fiber Frostman constant is exactly the ambient
scale-`r` coarse-family Frostman constant relative to the same scale-`s`
parent. -/
lemma relationFrostmanConstant_eq_ambient
    (r s : UniformScaleIndex delta)
    (k : Fin (U.coarse s).card) :
    U.relationFrostmanConstant r s k =
      (U.coarse r).toBodyFamily.frostmanConstantIn
        (dilatedTubeCarrier (independentCoverParentDilation A)
          ((U.coarse s).tube k)) := by
  let R := U.containedParentSubfamily r s k
  let V :=
    dilatedTubeCarrier (independentCoverParentDilation A)
      ((U.coarse s).tube k)
  have hmassV :
      R.family.toBodyFamily.containedMass V =
        (U.coarse r).toBodyFamily.containedMass V :=
    U.containedParentMass_restrict r s k Set.Subset.rfl
  have hsets :
      {c : ENNReal |
        ∃ K : Set Point3, Convex ℝ K ∧ K ⊆ V ∧
          c = R.family.toBodyFamily.density K /
            R.family.toBodyFamily.density V} =
      {c : ENNReal |
        ∃ K : Set Point3, Convex ℝ K ∧ K ⊆ V ∧
          c = (U.coarse r).toBodyFamily.density K /
            (U.coarse r).toBodyFamily.density V} := by
    ext c
    constructor
    · rintro ⟨K, hK, hKV, rfl⟩
      have hmassK :
          R.family.toBodyFamily.containedMass K =
            (U.coarse r).toBodyFamily.containedMass K :=
        U.containedParentMass_restrict r s k hKV
      refine ⟨K, hK, hKV, ?_⟩
      dsimp only [BodyFamily.density]
      rw [hmassK, hmassV]
    · rintro ⟨K, hK, hKV, rfl⟩
      have hmassK :
          R.family.toBodyFamily.containedMass K =
            (U.coarse r).toBodyFamily.containedMass K :=
        U.containedParentMass_restrict r s k hKV
      refine ⟨K, hK, hKV, ?_⟩
      dsimp only [BodyFamily.density]
      rw [hmassK, hmassV]
  dsimp only [relationFrostmanConstant,
    BodyFamily.frostmanConstantIn]
  exact congrArg sSup hsets

end DilatedDiscreteUniformTubeStructure

end Kakeya.Streamlined
