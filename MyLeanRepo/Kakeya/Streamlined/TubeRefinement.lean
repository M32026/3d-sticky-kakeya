import MyLeanRepo.Kakeya.Streamlined.Estimates

/-!
# Indexed tube subfamilies and shading restriction

The generic `Subfamily` API forgets the tube parametrization.  This module
keeps tube identities, directions, and multiplicities while selecting an
indexed subfamily.
-/

noncomputable section

namespace Kakeya.Streamlined

/-- A subfamily of an indexed tube family. -/
structure TubeSubfamily {δ : ℝ} (F : TubeFamily δ) where
  family : TubeFamily δ
  embedding : Fin family.card ↪ Fin F.card
  tube_eq : ∀ i, family.tube i = F.tube (embedding i)

namespace TubeSubfamily

/-- Construct a tube subfamily from a finite set of original indices. -/
def fromFinset {δ : ℝ} (F : TubeFamily δ)
    (I : Finset (Fin F.card)) : TubeSubfamily F :=
  { family :=
    { card := I.card
      tube := fun i => F.tube (I.orderEmbOfFin rfl i) }
    embedding := (I.orderEmbOfFin rfl).toEmbedding
    tube_eq := fun _ => rfl }

/--
The tube subfamily selected by `I` embeds in the one selected by `J`
whenever `I ⊆ J`.
-/
def fromFinsetInclusion {δ : ℝ} (F : TubeFamily δ)
    (I J : Finset (Fin F.card)) (hIJ : I ⊆ J) :
    Fin (fromFinset F I).family.card ↪
      Fin (fromFinset F J).family.card := by
  let eI := I.orderIsoOfFin rfl
  let eJ := J.orderIsoOfFin rfl
  let inclusion :
      Fin (fromFinset F I).family.card →
        Fin (fromFinset F J).family.card := fun i =>
    eJ.symm ⟨eI i, hIJ (eI i).property⟩
  refine ⟨inclusion, ?_⟩
  intro i j hij
  have hsub :
      (⟨eI i, hIJ (eI i).property⟩ : J) =
        ⟨eI j, hIJ (eI j).property⟩ :=
    eJ.symm.injective hij
  have hambient :
      (eI i : Fin F.card) = eI j :=
    congrArg (fun x : J => (x : Fin F.card)) hsub
  exact eI.injective (Subtype.ext hambient)

/-- The inclusion of finite-set subfamilies preserves ambient indices. -/
lemma fromFinsetInclusion_ambient {δ : ℝ} (F : TubeFamily δ)
    (I J : Finset (Fin F.card)) (hIJ : I ⊆ J)
    (i : Fin (fromFinset F I).family.card) :
    (fromFinset F J).embedding
        (fromFinsetInclusion F I J hIJ i) =
      (fromFinset F I).embedding i := by
  let eI := I.orderIsoOfFin rfl
  let eJ := J.orderIsoOfFin rfl
  change (J.orderEmbOfFin rfl)
      (eJ.symm ⟨eI i, hIJ (eI i).property⟩) =
    I.orderEmbOfFin rfl i
  exact congrArg Subtype.val
    (eJ.apply_symm_apply ⟨eI i, hIJ (eI i).property⟩)

/-- Compose two nested tube subfamilies. -/
def comp {δ : ℝ} {F : TubeFamily δ}
    (outer : TubeSubfamily F) (inner : TubeSubfamily outer.family) :
    TubeSubfamily F where
  family := inner.family
  embedding := inner.embedding.trans outer.embedding
  tube_eq i := by
    have htrans :
        (inner.embedding.trans outer.embedding) i =
          outer.embedding (inner.embedding i) :=
      Function.Embedding.trans_apply inner.embedding outer.embedding i
    rw [htrans, inner.tube_eq i, outer.tube_eq (inner.embedding i)]

/-- Forget tube data and obtain the corresponding body subfamily. -/
def toBodySubfamily {δ : ℝ} {F : TubeFamily δ}
    (S : TubeSubfamily F) : Subfamily F.toBodyFamily where
  family := S.family.toBodyFamily
  embedding := S.embedding
  carrier_eq i := by
    change (S.family.tube i).carrier =
      (F.tube (S.embedding i)).carrier
    rw [S.tube_eq i]

/-- Restrict a tube shading to a tube subfamily. -/
def restrictShading {δ : ℝ} {F : TubeFamily δ}
    (S : TubeSubfamily F) (Y : TubeShading F) :
    TubeShading S.family where
  carrier i := Y.carrier (S.embedding i)
  measurable_carrier i := Y.measurable_carrier (S.embedding i)
  subset_body i := by
    have h := Y.subset_body (S.embedding i)
    change Y.carrier (S.embedding i) ⊆
      (S.family.tube i).carrier
    rw [S.tube_eq i]
    exact h

/-- The selected tube family is nonempty. -/
def Nonempty {δ : ℝ} {F : TubeFamily δ} (S : TubeSubfamily F) : Prop :=
  S.family.Nonempty

/-- The restricted shading retains a fraction `c` of the original mass. -/
def RetainsShadedMass {δ : ℝ} {F : TubeFamily δ}
    (S : TubeSubfamily F) (Y : TubeShading F) (c : ENNReal) : Prop :=
  c * Y.mass ≤ (S.restrictShading Y).mass

/-- A subfamily of an essentially-distinct family is essentially distinct. -/
lemma isEssentiallyDistinct {δ : ℝ} {F : TubeFamily δ}
    (S : TubeSubfamily F) (hF : F.IsEssentiallyDistinct) :
    S.family.IsEssentiallyDistinct := by
  intro i j hne
  have h_emb_ne : S.embedding i ≠ S.embedding j :=
    fun h => hne (S.embedding.inj' h)
  rw [S.tube_eq i, S.tube_eq j]
  exact hF (S.embedding i) (S.embedding j) h_emb_ne

end TubeSubfamily

end Kakeya.Streamlined
