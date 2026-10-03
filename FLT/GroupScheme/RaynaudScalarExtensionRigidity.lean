/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudScalarFiltrationBaseChange
public import FLT.GroupScheme.RaynaudScalarFilteredRigidity
public import FLT.GroupScheme.FiniteFlatScalarExtension

/-!
# Faithful descent of scalar-filtered rigidity

Generic bijections remain bijections under actual scalar extension. Faithful
flatness then descends the surjectivity supplied by strict-Henselian rigidity.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
namespace ThreeAdicPlan

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K]
  (S L : Type) [CommRing S] [Field L] [PerfectField L] [Algebra R S]
  [Algebra R L] [Algebra S L] [IsScalarTower R S L]
  [Algebra K L] [IsScalarTower R K L]

omit [PerfectField L] in
set_option maxRecDepth 4000 in
/-- The integral tensor-product map retains generic bijectivity. -/
theorem ModelHom.generic_bijective_scalarExtension {X Y : FF R K}
    (g : ModelHom X Y) (hg : Function.Bijective (genericHom g)) :
    Function.Bijective (genericHom (g.scalarExtension S L)) := by
  have formula (Z : FF R K) (z : Z.CoordinateRing) :
      Z.scalarExtensionGenericEquiv S L (1 ⊗ₜ[S] (1 ⊗ₜ[R] z)) =
        (1 : L) ⊗ₜ[K] ((1 : K) ⊗ₜ[R] z) := by
    change (Algebra.TensorProduct.cancelBaseChange R K L L Z.CoordinateRing).symm
      ((Algebra.TensorProduct.cancelBaseChange R S L L Z.CoordinateRing)
        (1 ⊗ₜ[S] (1 ⊗ₜ[R] z))) = _
    apply (Algebra.TensorProduct.cancelBaseChange R K L L Z.CoordinateRing).injective
    simp
  let e := BialgEquiv.ofBijective (genericHom g).toBialgHom
    ⟨(genericHom g).toBialgHom_injective hg.2, (genericHom g).toBialgHom_surjective hg.1⟩
  let E := (Y.scalarExtensionGenericEquiv S L).trans
    ((bialgebraBaseChangeEquiv K L (K ⊗[R] Y.CoordinateRing)
      (K ⊗[R] X.CoordinateRing) e).trans (X.scalarExtensionGenericEquiv S L).symm)
  have he : (g.scalarExtension S L).baseChange = E.toBialgHom := by
    apply DFunLike.ext'
    change ⇑(g.scalarExtension S L).baseChange.toAlgHom = ⇑E.toAlgEquiv.toAlgHom
    congr 1
    apply Algebra.TensorProduct.ext_ring
    apply Algebra.TensorProduct.ext_ring
    ext y
    apply (X.scalarExtensionGenericEquiv S L).injective
    change X.scalarExtensionGenericEquiv S L (1 ⊗ₜ[S] (1 ⊗ₜ[R] g y)) =
      X.scalarExtensionGenericEquiv S L (E (1 ⊗ₜ[S] (1 ⊗ₜ[R] y)))
    change X.scalarExtensionGenericEquiv S L (1 ⊗ₜ[S] (1 ⊗ₜ[R] g y)) =
      X.scalarExtensionGenericEquiv S L ((X.scalarExtensionGenericEquiv S L).symm
        ((bialgebraBaseChangeEquiv K L (K ⊗[R] Y.CoordinateRing)
          (K ⊗[R] X.CoordinateRing) e)
            (Y.scalarExtensionGenericEquiv S L (1 ⊗ₜ[S] (1 ⊗ₜ[R] y)))))
    rw [BialgEquiv.apply_symm_apply]
    rw [formula, formula]
    change (1 : L) ⊗ₜ[K] (1 ⊗ₜ[R] g y) =
      (1 : L) ⊗ₜ[K] (genericHom g).toBialgHom (1 ⊗ₜ[R] y)
    rw [g.toBialgHom_genericHom]
    rfl
  change Function.Bijective (GenericGaloisHom.ofBialgHom
    (X := X.scalarExtension S L) (Y := Y.scalarExtension S L)
    (g.scalarExtension S L).baseChange)
  rw [he]
  exact GenericGaloisHom.ofBialgHom_bijective
    (X := X.scalarExtension S L) (Y := Y.scalarExtension S L) E

/-- A scalar filtration transports to the geometric points of the actual tensor model. -/
theorem FF.HasScalarFiltration.scalarExtension {p n : ℕ} {X : FF R K}
    (hX : X.HasScalarFiltration p n) : (X.scalarExtension S L).HasScalarFiltration p n := by
  let e : GenericGaloisHom (X.restrictedScalarExtension S L) (X.scalarExtension S L) :=
    (X.restrictedScalarExtension S L).inversePoints
  exact (hX.restrictScalars S L).of_generic_bijective e
    (X.restrictedScalarExtension S L).pointsEquiv.symm.bijective

omit [PerfectField L] in
/-- Strict-Henselian rigidity after faithful scalar extension implies original surjectivity. -/
theorem ModelHom.surjective_of_scalarFiltration_baseChange
    [IsDomain S] [IsDiscreteValuationRing S] [HenselianLocalRing S]
    [IsSepClosed (IsLocalRing.ResidueField S)] [CharZero L]
    [IsFractionRing S L] [Module.FaithfullyFlat R S]
    (p : ℕ) [CharP (IsLocalRing.ResidueField S) p]
    (he : RaynaudParameters.order (p : S) < p - 1)
    {n : ℕ} {X Y : FF R K}
    (hX : (X.scalarExtension S L).HasScalarFiltration p n)
    (g : ModelHom X Y) (hg : Function.Bijective (genericHom g)) : Function.Surjective g := by
  have h := (g.scalarExtension S L).surjective_of_scalarFiltration p he hX
    (g.generic_bijective_scalarExtension S L hg)
  exact (Module.FaithfullyFlat.lTensor_surjective_iff_surjective R S g.toAlgHom.toLinearMap).mp h

end ThreeAdicPlan
