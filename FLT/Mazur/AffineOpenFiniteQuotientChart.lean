/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineOpenFinitePolynomialPresentation

/-!
# Finite polynomial quotient charts of the original ambient

The full finite-variable quotient spectrum embeds as exactly the chosen affine
open. Its structure morphism agrees with the original coefficient map.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] {Z : Scheme.{u}} (z : Z ⟶ Spec (.of R))
  [LocallyOfFiniteType z]
variable (U : Z.affineOpens)

/-- The quotient spectrum is the original affine-open spectrum. -/
def affineOpenFiniteQuotientIso :
    Spec (.of (MvPolynomial (AffineOpenFiniteVars z U) R ⧸ affineOpenFiniteRelations z U)) ≅
      Spec Γ(Z, U.val) := by
  let _ := affineOpenCoefficientAlgebra z U
  exact Scheme.Spec.mapIso
    ((affineOpenFiniteQuotientEquiv z U).toRingEquiv.toCommRingCatIso).op.symm

/-- The presented chart embedding into the actual ambient scheme. -/
def affineOpenFiniteQuotientChart :
    Spec (.of (MvPolynomial (AffineOpenFiniteVars z U) R ⧸ affineOpenFiniteRelations z U)) ⟶ Z :=
  (affineOpenFiniteQuotientIso z U).hom ≫ U.property.fromSpec

instance : IsOpenImmersion (affineOpenFiniteQuotientChart z U) := by
  unfold affineOpenFiniteQuotientChart
  infer_instance

/-- Its image is exactly the chosen original affine open. -/
theorem affineOpenFiniteQuotientChart_opensRange :
    (affineOpenFiniteQuotientChart z U).opensRange = U.val := by
  unfold affineOpenFiniteQuotientChart
  rw [Scheme.Hom.opensRange_comp_of_isIso,
    IsAffineOpen.opensRange_fromSpec]

/-- The constructed chart respects the original coefficient map. -/
theorem affineOpenFiniteQuotientChart_over : affineOpenFiniteQuotientChart z U ≫ z =
    Spec.map (CommRingCat.ofHom
      (algebraMap R
        (MvPolynomial (AffineOpenFiniteVars z U) R ⧸ affineOpenFiniteRelations z U))) := by
  let _ := affineOpenCoefficientAlgebra z U
  rw [affineOpenFiniteQuotientChart, Category.assoc]
  change Spec.map (CommRingCat.ofHom (affineOpenFiniteQuotientEquiv z U).symm.toRingHom) ≫
    U.property.fromSpec ≫ z = _
  rw [← Spec.map_preimage (U.property.fromSpec ≫ z), ← Spec.map_comp]
  congr 1
  ext r
  exact (affineOpenFiniteQuotientEquiv z U).symm.commutes r

end FLT.Mazur.HilbertChart
