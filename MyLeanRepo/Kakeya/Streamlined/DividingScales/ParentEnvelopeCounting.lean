import MyLeanRepo.Kakeya.Streamlined.DividingScales.ParentEnvelope
import MyLeanRepo.Kakeya.Streamlined.IndependentDilatedCoverFullFiberMass
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.FrostmanFromDeltaMax
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.Submultiplicativity

/-!
# Counting assigned parents through the common envelope

For a convex set `K`, retain the distinguished-scale parents assigned to fine
tubes contained in `K`.  The common parent envelope turns the coarse
`deltaMax` bound into an explicit estimate for the total mass of those
parents.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Streamlined

namespace BodyFamily

/-- A maximal-density bound gives the cross-multiplied contained-mass bound
inside a positive finite-volume convex set. -/
lemma containedMass_le_deltaMax_mul_volume
    (G : BodyFamily) {W : Set Point3}
    (hW : Convex ℝ W)
    (hW_zero : volume W ≠ 0)
    (hW_top : volume W ≠ ⊤) :
    G.containedMass W ≤ G.deltaMax * volume W := by
  have hdensity :
      G.density W ≤ G.deltaMax :=
    density_le_of_deltaMax_le le_rfl hW
  exact (ENNReal.div_le_iff hW_zero hW_top).mp hdensity

end BodyFamily

namespace DilatedDiscreteUniformTubeStructure

variable {delta A : ℝ} {F : TubeFamily delta}
variable {hdelta_le_one : delta ≤ 1}
variable (U : DilatedDiscreteUniformTubeStructure
  (A := A) F hdelta_le_one)

/-- Any finite set of fine indices is covered by the selected parent fibers
over the image of that set. -/
lemma fineIndexSet_subset_biUnion_fineFiberIndices
    (r : UniformScaleIndex delta)
    (I : Finset (Fin F.card)) :
    I ⊆ (I.image (U.cover r).parent).biUnion
      (U.fineFiberIndices r) := by
  classical
  intro i hi
  let j := (U.cover r).parent i
  exact Finset.mem_biUnion.mpr
    ⟨j, Finset.mem_image.mpr ⟨i, hi, rfl⟩,
      by rw [U.mem_fineFiberIndices_iff r j i]⟩

/-- Uniformity controls an arbitrary fine index set by the cardinality of its
parent image and one reference fiber count. -/
lemma fineIndexSet_count_le_parentImage_mul_fiberCount
    (r : UniformScaleIndex delta)
    (I : Finset (Fin F.card))
    (j₀ : Fin (U.coarse r).card) :
    (I.card : ENNReal) ≤
      ((I.image (U.cover r).parent).card : ENNReal) *
        (U.assignedUniformity *
          (U.cover r).toFactoring.fiberCount j₀) := by
  classical
  let parents := I.image (U.cover r).parent
  let fibers := U.fineFiberIndices r
  have hsubset :
      I ⊆ parents.biUnion fibers :=
    U.fineIndexSet_subset_biUnion_fineFiberIndices r I
  have hcard_subset :
      (I.card : ENNReal) ≤
        ((parents.biUnion fibers).card : ENNReal) := by
    exact_mod_cast Finset.card_le_card hsubset
  have hcard_union :
      ((parents.biUnion fibers).card : ENNReal) ≤
        ∑ j ∈ parents, ((fibers j).card : ENNReal) := by
    exact_mod_cast Finset.card_biUnion_le
  have hfiber :
      ∀ j ∈ parents,
        ((fibers j).card : ENNReal) ≤
          U.assignedUniformity *
            (U.cover r).toFactoring.fiberCount j₀ := by
    intro j _hj
    have h := (U.assignedUniform r).2 j j₀
    have hj :
        ((fibers j).card : ENNReal) =
          (U.cover r).toFactoring.fiberCount j := by
      rfl
    rw [hj]
    exact h
  calc
    (I.card : ENNReal)
        ≤ ((parents.biUnion fibers).card : ENNReal) := hcard_subset
    _ ≤ ∑ j ∈ parents, ((fibers j).card : ENNReal) := hcard_union
    _ ≤ ∑ _j ∈ parents,
        U.assignedUniformity *
          (U.cover r).toFactoring.fiberCount j₀ := by
      exact Finset.sum_le_sum hfiber
    _ = (parents.card : ENNReal) *
        (U.assignedUniformity *
          (U.cover r).toFactoring.fiberCount j₀) := by
      simp [Finset.sum_const, nsmul_eq_mul]

/-- Fine indices whose carriers lie in an arbitrary set `K`. -/
def fineIndicesIn
    (U : DilatedDiscreteUniformTubeStructure
      (A := A) F hdelta_le_one)
    (K : Set Point3) :
    Finset (Fin F.card) := by
  classical
  exact Finset.univ.filter fun i => (F.tube i).carrier ⊆ K

@[simp] lemma mem_fineIndicesIn_iff
    (K : Set Point3) (i : Fin F.card) :
    i ∈ U.fineIndicesIn K ↔ (F.tube i).carrier ⊆ K := by
  simp [fineIndicesIn]

/-- Assigned scale-`r` parents used by fine tubes contained in `K`. -/
def assignedParentIndicesIn
    (r : UniformScaleIndex delta) (K : Set Point3) :
    Finset (Fin (U.coarse r).card) :=
  (U.fineIndicesIn K).image (U.cover r).parent

@[simp] lemma mem_assignedParentIndicesIn_iff
    (r : UniformScaleIndex delta) (K : Set Point3)
    (j : Fin (U.coarse r).card) :
    j ∈ U.assignedParentIndicesIn r K ↔
      ∃ i : Fin F.card,
        (F.tube i).carrier ⊆ K ∧ (U.cover r).parent i = j := by
  classical
  simp [assignedParentIndicesIn]

/-- The selected family of assigned parents used over `K`. -/
def assignedParentSubfamilyIn
    (r : UniformScaleIndex delta) (K : Set Point3) :
    TubeSubfamily (U.coarse r) :=
  TubeSubfamily.fromFinset
    (U.coarse r) (U.assignedParentIndicesIn r K)

lemma assignedParentSubfamilyIn_nonempty
    (r : UniformScaleIndex delta) {K : Set Point3}
    (i : Fin F.card) (hiK : (F.tube i).carrier ⊆ K) :
    (U.assignedParentSubfamilyIn r K).Nonempty := by
  classical
  have hparent :
      (U.cover r).parent i ∈ U.assignedParentIndicesIn r K := by
    rw [U.mem_assignedParentIndicesIn_iff r K]
    exact ⟨i, hiK, rfl⟩
  exact Finset.card_pos.mpr ⟨_, hparent⟩

/-- Every tube of the assigned-parent subfamily lies in a set containing all
assigned parents over `K`. -/
lemma assignedParentSubfamilyIn_all_contained
    (r : UniformScaleIndex delta) (K W : Set Point3)
    (hW :
      ∀ i : Fin F.card, (F.tube i).carrier ⊆ K →
        ((U.coarse r).tube ((U.cover r).parent i)).carrier ⊆ W) :
    ∀ j,
      ((U.assignedParentSubfamilyIn r K).family.tube j).carrier ⊆ W := by
  intro j
  rw [(U.assignedParentSubfamilyIn r K).tube_eq j]
  have hj :
      (U.assignedParentSubfamilyIn r K).embedding j ∈
        U.assignedParentIndicesIn r K :=
    Finset.orderEmbOfFin_mem
      (U.assignedParentIndicesIn r K) rfl j
  rcases (U.mem_assignedParentIndicesIn_iff r K
    ((U.assignedParentSubfamilyIn r K).embedding j)).mp hj with
    ⟨i, hiK, hi⟩
  simpa [hi] using hW i hiK

/-- The assigned-parent subfamily has the expected equal-radius tube mass. -/
lemma assignedParentSubfamilyIn_mass
    (r : UniformScaleIndex delta) (K : Set Point3) :
    (U.assignedParentSubfamilyIn r K).family.toBodyFamily.mass =
      ((U.assignedParentIndicesIn r K).card : ENNReal) *
        Kakeya.deltaTubeVolume
          (uniformScale delta hdelta_le_one r).1 := by
  rw [TubeFamily.bodyMass_eq_nominalMass]
  simp [TubeFamily.nominalMass, TubeFamily.enncard,
    assignedParentSubfamilyIn, TubeSubfamily.fromFinset]

/--
The mass of assigned scale-`r` parents used over a convex set `K` is bounded
by coarse maximal density times the volume of `N_rho(K)`, with the explicit
common-envelope loss.
-/
lemma assignedParentMass_le
    (hA : 1 ≤ A) (hdelta : 0 < delta)
    (hF_ball : F.IsInUnitBall)
    (r : UniformScaleIndex delta)
    {K : Set Point3} (hK : Convex ℝ K)
    (i₀ : Fin F.card) (hi₀K : (F.tube i₀).carrier ⊆ K)
    (hne_top :
      volume (Metric.cthickening
        (uniformScale delta hdelta_le_one r).1 K) ≠ ⊤) :
    ((U.assignedParentIndicesIn r K).card : ENNReal) *
        Kakeya.deltaTubeVolume
          (uniformScale delta hdelta_le_one r).1 ≤
      (U.coarse r).toBodyFamily.deltaMax *
        parentEnvelopeVolumeFactor A *
          volume (Metric.cthickening
            (uniformScale delta hdelta_le_one r).1 K) := by
  rcases U.exists_assigned_parent_envelope
      hA hdelta hF_ball r hK i₀ hi₀K hne_top with
    ⟨W, hW_convex, hparents_W, hW_volume⟩
  let P := U.assignedParentSubfamilyIn r K
  have hP_all : ∀ j, (P.family.tube j).carrier ⊆ W :=
    U.assignedParentSubfamilyIn_all_contained r K W hparents_W
  have hP_mass_in :
      P.family.toBodyFamily.containedMass W =
        P.family.toBodyFamily.mass :=
    BodyFamily.containedMass_eq_mass_of_all_contained _ _ hP_all
  have hP_le :
      P.family.toBodyFamily.containedMass W ≤
        (U.coarse r).toBodyFamily.containedMass W := by
    exact BodyFamily.subfamily_containedMass_le
      P.embedding.injective (fun j => by
        exact congrArg
          (fun T : Kakeya.DeltaTube
            (uniformScale delta hdelta_le_one r).1 => T.carrier)
          (P.tube_eq j)) W
  have hrho :
      0 < (uniformScale delta hdelta_le_one r).1 :=
    lt_of_lt_of_le hdelta
      (uniformScale delta hdelta_le_one r).property.1
  have hW_zero : volume W ≠ 0 := by
    have hparent :
        ((U.coarse r).tube ((U.cover r).parent i₀)).carrier ⊆ W :=
      hparents_W i₀ hi₀K
    have htube :
        0 <
          ((U.coarse r).tube ((U.cover r).parent i₀)).volume := by
      rw [RandomTranslation.tube_volume_eq_deltaTubeVolume]
      exact RandomTranslation.deltaTubeVolume_pos hrho
    exact (htube.trans_le (measure_mono hparent)).ne'
  have hfactor_top : parentEnvelopeVolumeFactor A ≠ ⊤ := by
    dsimp only [parentEnvelopeVolumeFactor]
    exact ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
  have hW_top : volume W ≠ ⊤ := by
    have hrhs_top :
        parentEnvelopeVolumeFactor A *
            volume (Metric.cthickening
              (uniformScale delta hdelta_le_one r).1 K) ≠ ⊤ :=
      ENNReal.mul_ne_top hfactor_top hne_top
    exact ne_top_of_le_ne_top hrhs_top hW_volume
  have hcoarse :
      (U.coarse r).toBodyFamily.containedMass W ≤
        (U.coarse r).toBodyFamily.deltaMax * volume W :=
    BodyFamily.containedMass_le_deltaMax_mul_volume
      (U.coarse r).toBodyFamily hW_convex hW_zero hW_top
  calc
    ((U.assignedParentIndicesIn r K).card : ENNReal) *
          Kakeya.deltaTubeVolume
            (uniformScale delta hdelta_le_one r).1
        = P.family.toBodyFamily.mass :=
      (U.assignedParentSubfamilyIn_mass r K).symm
    _ = P.family.toBodyFamily.containedMass W := hP_mass_in.symm
    _ ≤ (U.coarse r).toBodyFamily.containedMass W := hP_le
    _ ≤ (U.coarse r).toBodyFamily.deltaMax * volume W := hcoarse
    _ ≤ (U.coarse r).toBodyFamily.deltaMax *
          (parentEnvelopeVolumeFactor A *
            volume (Metric.cthickening
              (uniformScale delta hdelta_le_one r).1 K)) := by
        exact mul_le_mul_left' hW_volume _
    _ = (U.coarse r).toBodyFamily.deltaMax *
          parentEnvelopeVolumeFactor A *
            volume (Metric.cthickening
              (uniformScale delta hdelta_le_one r).1 K) := by
        ring

/-- The fine mass contained in `K` is its contained index count times the
common fine-tube volume. -/
lemma fineContainedMass_eq
    (K : Set Point3) :
    F.toBodyFamily.containedMass K =
      ((U.fineIndicesIn K).card : ENNReal) *
        Kakeya.deltaTubeVolume delta := by
  have hindices :
      F.toBodyFamily.containedIndices K = U.fineIndicesIn K := by
    rfl
  rw [BodyFamily.containedMass, hindices]
  calc
    ∑ i ∈ U.fineIndicesIn K, (F.toBodyFamily.body i).volume
        = ∑ _i ∈ U.fineIndicesIn K,
            Kakeya.deltaTubeVolume delta := by
          apply Finset.sum_congr rfl
          intro i _
          change (F.tube i).volume = Kakeya.deltaTubeVolume delta
          exact RandomTranslation.tube_volume_eq_deltaTubeVolume _
    _ = ((U.fineIndicesIn K).card : ENNReal) *
        Kakeya.deltaTubeVolume delta := by
      simp [Finset.sum_const, nsmul_eq_mul]

/-- Fine indices in `K` are covered by the assigned fibers of the parents
that occur over `K`. -/
lemma fineIndicesIn_subset_biUnion_fineFiberIndices
    (r : UniformScaleIndex delta) (K : Set Point3) :
    U.fineIndicesIn K ⊆
      (U.assignedParentIndicesIn r K).biUnion
        (U.fineFiberIndices r) := by
  classical
  intro i hi
  let j := (U.cover r).parent i
  have hj : j ∈ U.assignedParentIndicesIn r K := by
    rw [U.mem_assignedParentIndicesIn_iff r K]
    exact ⟨i, (U.mem_fineIndicesIn_iff K i).mp hi, rfl⟩
  exact Finset.mem_biUnion.mpr
    ⟨j, hj, by rw [U.mem_fineFiberIndices_iff r j i]⟩

/-- Uniformity bounds the number of fine indices in `K` by the number of
assigned parents times one reference branching number. -/
lemma fineCount_le_assignedParentCount_mul_fiberCount
    (r : UniformScaleIndex delta) (K : Set Point3)
    (j₀ : Fin (U.coarse r).card) :
    ((U.fineIndicesIn K).card : ENNReal) ≤
      ((U.assignedParentIndicesIn r K).card : ENNReal) *
        (U.assignedUniformity *
          (U.cover r).toFactoring.fiberCount j₀) := by
  classical
  let parents := U.assignedParentIndicesIn r K
  let fibers := U.fineFiberIndices r
  have hsubset :
      U.fineIndicesIn K ⊆ parents.biUnion fibers :=
    U.fineIndicesIn_subset_biUnion_fineFiberIndices r K
  have hcard_subset :
      ((U.fineIndicesIn K).card : ENNReal) ≤
        ((parents.biUnion fibers).card : ENNReal) := by
    exact_mod_cast Finset.card_le_card hsubset
  have hcard_union :
      ((parents.biUnion fibers).card : ENNReal) ≤
        ∑ j ∈ parents, ((fibers j).card : ENNReal) := by
    exact_mod_cast Finset.card_biUnion_le
  have hfiber :
      ∀ j ∈ parents,
        ((fibers j).card : ENNReal) ≤
          U.assignedUniformity *
            (U.cover r).toFactoring.fiberCount j₀ := by
    intro j _hj
    have h := (U.assignedUniform r).2 j j₀
    have hj :
        ((fibers j).card : ENNReal) =
          (U.cover r).toFactoring.fiberCount j := by
      rfl
    rw [hj]
    exact h
  calc
    ((U.fineIndicesIn K).card : ENNReal)
        ≤ ((parents.biUnion fibers).card : ENNReal) := hcard_subset
    _ ≤ ∑ j ∈ parents, ((fibers j).card : ENNReal) := hcard_union
    _ ≤ ∑ _j ∈ parents,
        U.assignedUniformity *
          (U.cover r).toFactoring.fiberCount j₀ := by
      exact Finset.sum_le_sum hfiber
    _ = (parents.card : ENNReal) *
        (U.assignedUniformity *
          (U.cover r).toFactoring.fiberCount j₀) := by
      simp [Finset.sum_const, nsmul_eq_mul]

/--
One-step cross-multiplied submultiplicativity.

The fine mass in `K`, multiplied by one coarse-tube volume, is controlled by
one reference branching number, the coarse `deltaMax`, and the volume of the
`rho`-neighborhood of `K`.  The statement avoids division and records every
loss needed by the finite stopping-time iteration.
-/
lemma oneStepAssignedSubmultiplicativity
    (hA : 1 ≤ A) (hdelta : 0 < delta)
    (hF_ball : F.IsInUnitBall)
    (r : UniformScaleIndex delta)
    {K : Set Point3} (hK : Convex ℝ K)
    (i₀ : Fin F.card) (hi₀K : (F.tube i₀).carrier ⊆ K)
    (hne_top :
      volume (Metric.cthickening
        (uniformScale delta hdelta_le_one r).1 K) ≠ ⊤) :
    F.toBodyFamily.containedMass K *
        Kakeya.deltaTubeVolume
          (uniformScale delta hdelta_le_one r).1 ≤
      (U.assignedUniformity *
          (U.cover r).toFactoring.fiberCount ((U.cover r).parent i₀) *
          Kakeya.deltaTubeVolume delta) *
        ((U.coarse r).toBodyFamily.deltaMax *
          parentEnvelopeVolumeFactor A *
            volume (Metric.cthickening
              (uniformScale delta hdelta_le_one r).1 K)) := by
  have hcount :=
    U.fineCount_le_assignedParentCount_mul_fiberCount
      r K ((U.cover r).parent i₀)
  have hparents :=
    U.assignedParentMass_le
      hA hdelta hF_ball r hK i₀ hi₀K hne_top
  rw [U.fineContainedMass_eq K]
  calc
    ((U.fineIndicesIn K).card : ENNReal) *
          Kakeya.deltaTubeVolume delta *
          Kakeya.deltaTubeVolume
            (uniformScale delta hdelta_le_one r).1
        ≤ (((U.assignedParentIndicesIn r K).card : ENNReal) *
            (U.assignedUniformity *
              (U.cover r).toFactoring.fiberCount ((U.cover r).parent i₀))) *
          Kakeya.deltaTubeVolume delta *
          Kakeya.deltaTubeVolume
            (uniformScale delta hdelta_le_one r).1 := by
      gcongr
    _ = (U.assignedUniformity *
            (U.cover r).toFactoring.fiberCount ((U.cover r).parent i₀) *
            Kakeya.deltaTubeVolume delta) *
          (((U.assignedParentIndicesIn r K).card : ENNReal) *
            Kakeya.deltaTubeVolume
              (uniformScale delta hdelta_le_one r).1) := by
      ring
    _ ≤ (U.assignedUniformity *
            (U.cover r).toFactoring.fiberCount ((U.cover r).parent i₀) *
            Kakeya.deltaTubeVolume delta) *
          ((U.coarse r).toBodyFamily.deltaMax *
            parentEnvelopeVolumeFactor A *
              volume (Metric.cthickening
                (uniformScale delta hdelta_le_one r).1 K)) := by
      exact mul_le_mul_left' hparents _

end DilatedDiscreteUniformTubeStructure

namespace TubeFamily

/-- Contained mass of an equal-radius tube family is contained cardinality
times the common tube volume. -/
lemma containedMass_eq_card_mul_deltaTubeVolume
    {rho : ℝ} (G : TubeFamily rho) (W : Set Point3) :
    G.toBodyFamily.containedMass W =
      ((G.toBodyFamily.containedIndices W).card : ENNReal) *
        Kakeya.deltaTubeVolume rho := by
  calc
    G.toBodyFamily.containedMass W
        = ∑ i ∈ G.toBodyFamily.containedIndices W,
            (G.tube i).volume := by
          rfl
    _ = ∑ _i ∈ G.toBodyFamily.containedIndices W,
          Kakeya.deltaTubeVolume rho := by
        apply Finset.sum_congr rfl
        intro i _
        exact RandomTranslation.tube_volume_eq_deltaTubeVolume _
    _ = ((G.toBodyFamily.containedIndices W).card : ENNReal) *
        Kakeya.deltaTubeVolume rho := by
      simp [Finset.sum_const, nsmul_eq_mul]

end TubeFamily

namespace TubeSubfamily

/-- If ambient indices belong to a tube subfamily and all selected ambient
tubes lie in `W`, their total equal-radius mass is bounded by the subfamily's
contained mass in `W`. -/
lemma ambientFinset_mass_le_containedMass
    {rho : ℝ} {G : TubeFamily rho}
    (S : TubeSubfamily G)
    (I : Finset (Fin G.card))
    (hindices :
      I ⊆ Finset.image S.embedding Finset.univ)
    (W : Set Point3)
    (hcontained : ∀ i ∈ I, (G.tube i).carrier ⊆ W) :
    (I.card : ENNReal) * Kakeya.deltaTubeVolume rho ≤
      S.family.toBodyFamily.containedMass W := by
  classical
  let J : Finset (Fin S.family.card) :=
    Finset.univ.filter fun j => (S.family.tube j).carrier ⊆ W
  have hsubset :
      I ⊆ Finset.image S.embedding J := by
    intro i hi
    rcases Finset.mem_image.mp (hindices hi) with
      ⟨j, _hj, rfl⟩
    refine Finset.mem_image.mpr ⟨j, ?_, rfl⟩
    change j ∈ J
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ j, ?_⟩
    rw [S.tube_eq j]
    exact hcontained (S.embedding j) hi
  have hcard_image :
      (Finset.image S.embedding J).card = J.card :=
    Finset.card_image_of_injective _ S.embedding.injective
  have hcard_nat : I.card ≤ J.card := by
    calc
      I.card ≤ (Finset.image S.embedding J).card :=
        Finset.card_le_card hsubset
      _ = J.card := hcard_image
  have hcard : (I.card : ENNReal) ≤ (J.card : ENNReal) := by
    exact_mod_cast hcard_nat
  have hJ :
      S.family.toBodyFamily.containedIndices W = J := by
    rfl
  rw [S.family.containedMass_eq_card_mul_deltaTubeVolume W, hJ]
  exact mul_le_mul_right' hcard _

end TubeSubfamily

end Kakeya.Streamlined
