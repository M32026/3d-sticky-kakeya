/-
Instantiation of the generic transfer sequence for the antipodal action
on singular chains of S^n with Z/2 coefficients.

Provides:
- pHash2_rangePi_eq_ker: im(p) = ker(p) degreewise
- sphereTransferShortExact: 0 → D → C(S^n;Z/2) → D → 0
- oddMap_comm_pHash: an odd map between spheres commutes with p
- oddMapInducedOnD: induced map on image subcomplex D
-/
import MyLeanRepo.Kakeya.BorsukUlam.TransferFull
import MyLeanRepo.Kakeya.BorsukUlam.BackupRoute.TransferSequence

noncomputable section

namespace BorsukUlamBackup

open AlgebraicTopology CategoryTheory Limits HomologicalComplex Simplicial Preadditive
open SeedMathlib.AlgebraicTopology.Degree

variable {n : ℕ}

/-- The h_eq hypothesis for pHash2: im(p) = ker(p) degreewise. -/
lemma pHash2_rangePi_eq_ker (n k : ℕ) :
    trangePi (pHash2 n) k = LinearMap.ker (tLin (pHash2 n) k) := by
  have h := pHash2_ker_eq_range n k
  simpa [trangePi, tLin] using h.symm

/-- The transfer short exact sequence for the singular chains of S^n. -/
theorem sphereTransferShortExact (n : ℕ) :
    (ttransferShortComplex (pHash2 n) (pHash2_rangePi_eq_ker n)).ShortExact :=
  ttransferShortExact (pHash2 n) (pHash2_rangePi_eq_ker n)

/-- An odd map between spheres induces a chain map commuting with pHash. -/
lemma oddMap_comm_pHash {n m : ℕ}
    (g : C(Sphere n, Sphere m))
    (hg_odd : ∀ (x : Sphere n), g (ap x) = ap (g x)) :
    chainFunctor2.map (TopCat.ofHom g) ≫ pHash2 m =
    pHash2 n ≫ chainFunctor2.map (TopCat.ofHom g) := by
  let gHash := chainFunctor2.map (TopCat.ofHom g)
  have h1 : g.comp (apCmap (n := n)) = (apCmap (n := m)).comp g := by
    apply ContinuousMap.ext
    intro x
    exact hg_odd x
  have h_ap_comm :
      TopCat.ofHom (apCmap (n := n)) ≫ TopCat.ofHom g =
      TopCat.ofHom g ≫ TopCat.ofHom (apCmap (n := m)) := by
    simpa [TopCat.ofHom_comp] using congr_arg TopCat.ofHom h1
  have h_chain_comm : aHash2 n ≫ gHash = gHash ≫ aHash2 m := by
    have h2 := congr_arg chainFunctor2.map h_ap_comm
    simpa [aHash2, Functor.map_comp] using h2
  calc
    gHash ≫ pHash2 m
      = gHash ≫ (𝟙 (ChainSphere2 m) + aHash2 m) := by rfl
    _ = gHash + gHash ≫ aHash2 m := by
      simp [Preadditive.comp_add]
    _ = gHash + aHash2 n ≫ gHash := by rw [h_chain_comm]
    _ = (𝟙 (ChainSphere2 n) + aHash2 n) ≫ gHash := by
      simp [Preadditive.add_comp]
    _ = pHash2 n ≫ gHash := by rfl

/-- An odd map g induces a map on the image subcomplex D.

Since gHash commutes with p, it maps im(p_n) into im(p_m), so it restricts
to a chain map D_n → D_m. -/
def oddMapInducedOnD {n m : ℕ}
    (g : C(Sphere n, Sphere m))
    (hg_odd : ∀ (x : Sphere n), g (ap x) = ap (g x)) :
    timageSubcomplex (pHash2 n) ⟶ timageSubcomplex (pHash2 m) :=
  let gHash := chainFunctor2.map (TopCat.ofHom g)
  let h_comm := oddMap_comm_pHash g hg_odd
  let gOnD : ∀ i, trangePi (pHash2 n) i →ₗ[ZMod 2] trangePi (pHash2 m) i := fun i =>
    { toFun := fun (x : trangePi (pHash2 n) i) =>
        ⟨gHash.f i (x : (ChainSphere2 n).X i),
         by
          rcases x with ⟨z, hz⟩
          rcases LinearMap.mem_range.mp hz with ⟨y, rfl⟩
          have h_eq : gHash ≫ pHash2 m = pHash2 n ≫ gHash := h_comm
          have h_comp : gHash.f i ≫ (pHash2 m).f i = (pHash2 n).f i ≫ gHash.f i := by
            have h := congr_arg (fun (f : ChainSphere2 n ⟶ ChainSphere2 m) => f.f i) h_eq
            simpa [HomologicalComplex.comp_f] using h
          have h_lin : (gHash.f i).hom ∘ₗ ((pHash2 n).f i).hom =
              ((pHash2 m).f i).hom ∘ₗ (gHash.f i).hom := by
            have h2 := congr_arg ModuleCat.Hom.hom h_comp
            rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at h2
            exact h2.symm
          have h_goal : gHash.f i ((pHash2 n).f i y) = (pHash2 m).f i (gHash.f i y) := by
            exact LinearMap.congr_fun h_lin y
          exact LinearMap.mem_range.mpr ⟨gHash.f i y, h_goal.symm⟩⟩
      map_add' := by intro a b; ext; simp
      map_smul' := by intro c a; ext; simp }
  { f := fun i => ModuleCat.ofHom (gOnD i)
    comm' := by
      intro i j hij
      have h_chain : gHash.f i ≫ (ChainSphere2 m).d i j =
          (ChainSphere2 n).d i j ≫ gHash.f j := gHash.comm i j
      have h_lin : ((ChainSphere2 m).d i j).hom ∘ₗ (gHash.f i).hom =
          (gHash.f j).hom ∘ₗ ((ChainSphere2 n).d i j).hom := by
        have h3 := congr_arg ModuleCat.Hom.hom h_chain
        rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at h3
        exact h3
      have h_onD : tdRestricted (pHash2 m) i j ∘ₗ gOnD i =
          gOnD j ∘ₗ tdRestricted (pHash2 n) i j := by
        ext x
        simpa [gOnD, tdRestricted, LinearMap.comp_apply] using
          LinearMap.congr_fun h_lin (x : (ChainSphere2 n).X i)
      have h_goal : ModuleCat.ofHom (gOnD i) ≫ ModuleCat.ofHom (tdRestricted (pHash2 m) i j) =
          ModuleCat.ofHom (tdRestricted (pHash2 n) i j) ≫ ModuleCat.ofHom (gOnD j) := by
        have h5 := congr_arg ModuleCat.ofHom h_onD
        simpa [ModuleCat.ofHom_comp] using h5
      have h_d_m : (timageSubcomplex (pHash2 m)).d i j =
          ModuleCat.ofHom (tdRestricted (pHash2 m) i j) := by rfl
      have h_d_n : (timageSubcomplex (pHash2 n)).d i j =
          ModuleCat.ofHom (tdRestricted (pHash2 n) i j) := by rfl
      rw [h_d_m, h_d_n]
      exact h_goal }

end BorsukUlamBackup
