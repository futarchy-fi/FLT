/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineGeometricDatumComparison
public import FLT.Mazur.AffineTensorCoalgebraComparison
public import FLT.Mazur.AffineLineCoalgebraDescent

/-!
# Effective descent of geometric affine overlap data

The geometric overlap defines a coalgebra. Faithfully flat descent constructs
its coefficient module and sheaf, with a pullback isomorphism to the original
sheaf. Converting the recovered tensor datum back to geometry recovers the
specified overlap exactly.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineGeometricDescent
open AffineOverlapPullback AffineGeometricOverlap AffineOverlapDiagonal
open AffineTripleOverlapPullback AffineTensorCocycle
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S : CommRingCat.{u}} (φ : R ⟶ S)
variable (M : (Spec S).Modules) [M.IsQuasicoherent]

/-- An overlap with its actual geometric diagonal and cocycle equations. -/
abbrev Data :=
  letI := φ.hom.toAlgebra
  {e : Overlap R S M // DiagonalCompatible R S M e ∧ CocycleCompatible R S M e}

variable (D : Data φ M)

/-- The coalgebra defined by the actual overlap and its geometric equations. -/
def coalgebra : AffineModuleCoalgebraDescent.Data φ := by
  let := φ.hom.toAlgebra
  exact toCoalgebra φ (coefficients S M) (toDatum R S M D.val D.property.1 D.property.2)

variable (hφ : φ.hom.FaithfullyFlat)

/-- The sheaf on the base constructed by effective coefficient descent. -/
def descendedSheaf : (Spec R).Modules :=
  AffineModuleCoalgebraDescent.descendedSheaf φ hφ (coalgebra φ M D)

instance : (descendedSheaf φ M D hφ).IsQuasicoherent :=
  inferInstanceAs (AffineModuleCoalgebraDescent.descendedSheaf φ hφ
    (coalgebra φ M D)).IsQuasicoherent

/-- Pullback reconstructs the original quasi-coherent sheaf. -/
def reconstruction :
    (pullback (Spec.map φ)).obj (descendedSheaf φ M D hφ) ≅ M :=
  AffineModuleCoalgebraDescent.pullbackDescentIso φ hφ (coalgebra φ M D) ≪≫
    asIso M.fromTildeΓ

/-- The canonical tensor datum transported along coefficient reconstruction. -/
@[irreducible] def recoveredDatum :
    letI := φ.hom.toAlgebra
    letI := Module.compHom (coefficients S M) φ.hom
    letI : IsScalarTower R S (coefficients S M) :=
      IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
    Datum R S (coefficients S M) :=
  fromCoalgebra φ hφ (coalgebra φ M D)

/-- The reconstructed tensor datum is exactly the one supplied by the geometry. -/
theorem recoveredDatum_eq :
    letI := φ.hom.toAlgebra
    recoveredDatum φ M D hφ = toDatum R S M D.val D.property.1 D.property.2 := by
  let := φ.hom.toAlgebra
  apply datum_ext_overlap R S M
  unfold recoveredDatum coalgebra
  exact fromCoalgebra_toCoalgebra_overlap φ hφ (coefficients S M)
    (toDatum R S M D.val D.property.1 D.property.2)

/-- Reverse geometric comparison recovers the specified sheaf overlap exactly. -/
theorem recoveredOverlap_eq :
    letI := φ.hom.toAlgebra
    fromDatum R S M (recoveredDatum φ M D hφ) = D.val := by
  let := φ.hom.toAlgebra
  rw [recoveredDatum_eq]
  exact fromDatum_toDatum R S M D.val D.property.1 D.property.2

/-- Invertible coefficients descend to an actual line bundle on the base. -/
theorem descendedSheaf_locallyFreeRankOne [Module.Invertible S (coefficients S M)] :
    FCurve.LocallyFreeRankOne (descendedSheaf φ M D hφ) := by
  have : Module.Invertible S (coalgebra φ M D).A :=
    inferInstanceAs (Module.Invertible S (coefficients S M))
  exact AffineModuleCoalgebraDescent.descendedSheaf_locallyFreeRankOne φ hφ (coalgebra φ M D)

end FLT.Mazur.AffineGeometricDescent
