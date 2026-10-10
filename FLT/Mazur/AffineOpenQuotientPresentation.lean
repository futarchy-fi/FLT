/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmbientHilbertChartSystem
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Polynomial quotient presentations of all affine ambient opens

Use every element of the actual section ring as a variable. Evaluation is
surjective without finite-presentation assumptions. The quotient spectrum
is isomorphic to the original affine chart and preserves its base map.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] {Z : Scheme.{u}} (z : Z ⟶ Spec (.of R))
variable (U : Z.affineOpens)

/-- The coefficient algebra on the actual affine-open section ring. -/
@[instance_reducible]
def affineOpenCoefficientAlgebra : Algebra R Γ(Z, U.val) :=
  (Spec.preimage (U.property.fromSpec ≫ z)).hom.toAlgebra

/-- The relations of the polynomial presentation indexed by every actual section. -/
def affineOpenRelations : Ideal (MvPolynomial Γ(Z, U.val) R) :=
  let _ := affineOpenCoefficientAlgebra z U
  RingHom.ker (aeval (R := R) (id : Γ(Z, U.val) → Γ(Z, U.val))).toRingHom

/-- Evaluation gives the actual coefficient-linear quotient isomorphism. -/
def affineOpenQuotientEquiv :
    let _ := affineOpenCoefficientAlgebra z U
    (MvPolynomial Γ(Z, U.val) R ⧸ affineOpenRelations z U) ≃ₐ[R] Γ(Z, U.val) := by
  let _ := affineOpenCoefficientAlgebra z U
  exact Ideal.quotientKerAlgEquivOfSurjective (fun x ↦ ⟨X x, aeval_X id x⟩)

/-- The quotient spectrum is the original affine-open spectrum. -/
def affineOpenQuotientIso :
    Spec (.of (MvPolynomial Γ(Z, U.val) R ⧸ affineOpenRelations z U)) ≅ Spec Γ(Z, U.val) := by
  let _ := affineOpenCoefficientAlgebra z U
  exact Scheme.Spec.mapIso ((affineOpenQuotientEquiv z U).toRingEquiv.toCommRingCatIso).op.symm

/-- The presented chart embedding into the actual ambient scheme. -/
def affineOpenQuotientChart :
    Spec (.of (MvPolynomial Γ(Z, U.val) R ⧸ affineOpenRelations z U)) ⟶ Z :=
  (affineOpenQuotientIso z U).hom ≫ U.property.fromSpec

instance : IsOpenImmersion (affineOpenQuotientChart z U) := by
  unfold affineOpenQuotientChart
  infer_instance

/-- Its image is exactly the chosen original affine open. -/
theorem affineOpenQuotientChart_opensRange : (affineOpenQuotientChart z U).opensRange = U.val := by
  unfold affineOpenQuotientChart
  rw [Scheme.Hom.opensRange_comp_of_isIso,
    IsAffineOpen.opensRange_fromSpec]

/-- The constructed chart respects the original coefficient map. -/
theorem affineOpenQuotientChart_over : affineOpenQuotientChart z U ≫ z =
    Spec.map (CommRingCat.ofHom
      (algebraMap R (MvPolynomial Γ(Z, U.val) R ⧸ affineOpenRelations z U))) := by
  let _ := affineOpenCoefficientAlgebra z U
  rw [affineOpenQuotientChart, Category.assoc]
  change Spec.map (CommRingCat.ofHom (affineOpenQuotientEquiv z U).symm.toRingHom) ≫
    U.property.fromSpec ≫ z = _
  rw [← Spec.map_preimage (U.property.fromSpec ≫ z), ← Spec.map_comp]
  congr 1
  ext r
  exact (affineOpenQuotientEquiv z U).symm.commutes r

end FLT.Mazur.HilbertChart
