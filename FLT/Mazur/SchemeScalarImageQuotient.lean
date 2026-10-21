/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FlatScalarFunctionPushout
public import FLT.Mazur.SchemeScalarIntegralBadCover
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# The full scalar image quotient

Factor an actual scalar morphism through the quotient by its exact kernel.
This retains nilpotents: no radical or reduced image replaces the kernel.
The closed immersion preserves the whole kernel pair of the scalar morphism.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeScalarImageQuotient
open SchemeScalarPrincipalNeighborhood FlatScalarFunctionPushout
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Type} [CommRing S] {X : Scheme.{0}} (b : X ⟶ Spec (.of S))

/-- The exact scalar equations on the full scheme. -/
def equations : Ideal S := RingHom.ker (scalarMap b)

/-- The original scalars modulo precisely the functions vanishing on the full scheme. -/
abbrev Scalars := S ⧸ equations b

/-- The surjection from the original scalars. -/
def quotient : S →+* Scalars b := Ideal.Quotient.mk (equations b)

/-- The full image embeds as a closed subscheme of the original scalar base. -/
def inclusion : Spec (.of (Scalars b)) ⟶ Spec (.of S) :=
  Spec.map (CommRingCat.ofHom (quotient b))

/-- The constructed projection to the exact scalar image. -/
def projection : X ⟶ Spec (.of (Scalars b)) :=
  scalarMorphism (RingHom.kerLift (scalarMap b))

/-- The coefficient map of the image projection is the injective kernel lift. -/
theorem projection_coefficients :
    scalarMap (projection b) = RingHom.kerLift (scalarMap b) := by
  exact congrArg CommRingCat.Hom.hom
    (ΓSpecIso_inv_ΓSpec_adjunction_homEquiv
      (CommRingCat.ofHom (RingHom.kerLift (scalarMap b))))

/-- All image scalars remain detectable on the actual scheme. -/
theorem projection_coefficients_injective : Function.Injective (scalarMap (projection b)) := by
  rw [projection_coefficients]
  exact RingHom.kerLift_injective _

/-- The image factorization recovers the literal original scheme morphism. -/
@[reassoc] theorem projection_inclusion : projection b ≫ inclusion b = b := by
  apply ext_of_isAffine
  apply (cancel_epi (Scheme.ΓSpecIso (.of S)).inv).mp
  rw [Scheme.Hom.comp_appTop, inclusion, ← Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
  change CommRingCat.ofHom ((scalarMap (projection b)).comp (quotient b)) = _
  rw [projection_coefficients]
  rfl

/-- The scalar quotient is surjective, without any geometric assumption. -/
theorem quotient_surjective : Function.Surjective (quotient b) := Ideal.Quotient.mk_surjective

instance inclusion_isClosedImmersion : IsClosedImmersion (inclusion b) :=
  IsClosedImmersion.spec_of_surjective _ (quotient_surjective b)

/-- Factoring by the full scalar image changes no pairs of arrows identified by the base. -/
theorem projection_eq_iff {Y : Scheme.{0}} (a c : Y ⟶ X) :
    a ≫ projection b = c ≫ projection b ↔ a ≫ b = c ≫ b := by
  rw [← cancel_mono (inclusion b), Category.assoc, Category.assoc, projection_inclusion]

/-- For an affine source, the constructed image has the exact original image closure. -/
theorem inclusion_range [IsAffine X] :
    Set.range (inclusion b) = closure (Set.range b) := by
  have hb : scalarMorphism (scalarMap b) = b := by
    apply ext_of_isAffine
    apply (cancel_epi (Scheme.ΓSpecIso (.of S)).inv).mp
    exact ΓSpecIso_inv_ΓSpec_adjunction_homEquiv _
  conv_rhs => rw [← hb, scalarMorphism_range_eq_comap, PrimeSpectrum.closure_range_comap]
  change Set.range (PrimeSpectrum.comap (quotient b)) = _
  rw [range_comap_of_surjective _ _ (quotient_surjective b), quotient, Ideal.mk_ker]
  rfl

end FLT.Mazur.SchemeScalarImageQuotient
