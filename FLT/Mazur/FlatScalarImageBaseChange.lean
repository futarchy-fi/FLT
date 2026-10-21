/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FlatScalarImageEquations
public import FLT.Mazur.ScalarQuotientPushout

/-!
# The exact scalar image commutes with flat base change

The new full image is the cartesian scalar extension of the original full
image. This is a scheme statement retaining the original equation ideals.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.FlatScalarImageBaseChange
open FlatScalarSchemeBaseChange SchemeScalarImageQuotient
set_option backward.isDefEq.respectTransparency false
variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
  (X : Scheme.{0}) [Algebra R Γ(X, ⊤)] [CompactSpace X] [QuasiSeparatedSpace X]
set_option quotPrecheck false
local notation "b₀" =>
  SchemeScalarPrincipalNeighborhood.scalarMorphism (algebraMap R Γ(X, ⊤))
local notation "b₁" => base R S X

/-- The original full-image equations vanish in the new exact image quotient. -/
theorem equations_le_comap :
    equations b₀ ≤ (equations b₁).comap (algebraMap R S) := by
  apply Ideal.map_le_iff_le_comap.mp
  exact (FlatScalarImageEquations.equations_eq_original_map R S X).ge

/-- The induced coefficient map between the two exact image rings. -/
def coefficients : Scalars b₀ →+* Scalars b₁ :=
  Ideal.quotientMap (equations b₁) (algebraMap R S) (equations_le_comap R S X)

/-- The induced map uses the unchanged original scalar map. -/
theorem coefficients_quotient :
    (coefficients R S X).comp (quotient b₀) = (quotient b₁).comp (algebraMap R S) := rfl

/-- The original and new full image rings form the scalar pushout. -/
theorem coefficients_isPushout :
    IsPushout (CommRingCat.ofHom (quotient b₀)) (CommRingCat.ofHom (algebraMap R S))
      (CommRingCat.ofHom (coefficients R S X)) (CommRingCat.ofHom (quotient b₁)) := by
  have aux (I : Ideal R) (K : Ideal S)
      (h : I ≤ K.comap (algebraMap R S)) (he : K = I.map (algebraMap R S)) :
      IsPushout (CommRingCat.ofHom (Ideal.Quotient.mk I))
        (CommRingCat.ofHom (algebraMap R S))
        (CommRingCat.ofHom (Ideal.quotientMap K (algebraMap R S) h))
        (CommRingCat.ofHom (Ideal.Quotient.mk K)) := by
    subst K
    exact ScalarQuotientPushout.isPushout (algebraMap R S) I
  exact aux _ _ (equations_le_comap R S X)
    (FlatScalarImageEquations.equations_eq_original_map R S X)

/-- The actual map from the new full image to the original full image. -/
def imageMap : Spec (.of (Scalars b₁)) ⟶ Spec (.of (Scalars b₀)) :=
  Spec.map (CommRingCat.ofHom (coefficients R S X))

/-- The exact image square is cartesian under every flat scalar extension. -/
theorem image_isPullback : IsPullback (imageMap R S X) (inclusion b₁)
    (inclusion b₀) (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (coefficients_isPushout R S X)

end FLT.Mazur.FlatScalarImageBaseChange
