/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveIdealVanishingScheme
public import FLT.Mazur.FiniteFlatAffineLocalFree

/-!
# Actual vanishing charts for an ideal in a finite locally free family

On each original affine base open, the finite family has a projective
coordinate algebra. The coefficient scheme is a closed base chart representing
vanishing of the full ideal on its scalar extension, with no reducedness,
Noetherian or free-frame hypothesis.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace FLT.Mazur.FiniteFlatIdealVanishing
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {D S : Scheme} (g : D ⟶ S) [IsFinite g] [Flat g]
  [LocallyOfFinitePresentation g] (J : D.IdealSheafData) (U : S.affineOpens)
set_option quotPrecheck false in
local notation "R" => Γ(S, U.1)
set_option quotPrecheck false in
local notation "B" => Γ(D, g ⁻¹ᵁ U.1)
/-- The actual ring map on the chosen base open supplies the scalar action. -/
local instance sectionAlgebra : Algebra R B := (g.app U.1).hom.toAlgebra
/-- The finite locally free family supplies projectivity on this affine open. -/
local instance sectionProjective : Module.Projective R B := FCurve.finiteFlat_app_projective g U

/-- The full ideal on the actual finite affine preimage. -/
def preimageIdeal : Ideal B := J.ideal ⟨g ⁻¹ᵁ U.1, U.2.preimage g⟩

/-- The base coefficients representing the vanishing condition. -/
def coefficientIdeal : Ideal R := ProjectiveIdealVanishing.ideal R B (preimageIdeal g J U)

/-- The actual closed coefficient scheme on this original affine base open. -/
def chart : Scheme := ProjectiveIdealVanishing.scheme R B (preimageIdeal g J U)

/-- The closed immersion into the spectrum of the original base sections. -/
def chartInclusion : chart g J U ⟶ Spec (.of R) := ProjectiveIdealVanishing.inclusion _ _ _

instance chartInclusion_closed : IsClosedImmersion (chartInclusion g J U) :=
  ProjectiveIdealVanishing.inclusion_closed _ _ _

/-- Every test algebra is represented precisely when its actual extended ideal is zero. -/
theorem chart_factorization_iff (A : Type) [CommRing A] [Algebra Γ(S, U.1) A] :
    (∃ k : Spec (.of A) ⟶ chart g J U,
      k ≫ chartInclusion g J U = Spec.map (CommRingCat.ofHom (algebraMap R A))) ↔
        (preimageIdeal g J U).map
          (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom = ⊥ :=
  ProjectiveIdealVanishing.factorization_iff R B (preimageIdeal g J U) A

/-- The coefficient quotient kills the actual ideal on the entire finite family. -/
theorem quotient_preimageIdeal_eq_bot :
    (preimageIdeal g J U).map (Algebra.TensorProduct.includeRight :
      B →ₐ[R] (R ⧸ coefficientIdeal g J U) ⊗[R] B).toRingHom = ⊥ :=
  ProjectiveIdealVanishing.quotient_extendedIdeal_eq_bot R B (preimageIdeal g J U)

end FLT.Mazur.FiniteFlatIdealVanishing
