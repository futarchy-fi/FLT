/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineCoefficientUnitLaws
public import FLT.Mazur.AffineTripleOverlapMaps

/-!
# Scalar multiples of conjugated pullback sections

Keep the rings and sheaves abstract while proving the scalar transport law.
It applies to the normalized pair pullbacks used in the geometric cocycle.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineScaledPullbackSections
open AffineIteratedPullbackSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {A B : CommRingCat.{u}} (φ : A ⟶ B)
variable {P P' : (Spec A).Modules} {Q Q' : (Spec B).Modules}

/-- Conjugated pullbacks transport scalar multiples of normalized coefficient units. -/
theorem mappedUnit_map_smul
    (c : (pullback (Spec.map φ)).obj P ≅ Q)
    (c' : (pullback (Spec.map φ)).obj P' ≅ Q') (e : P ⟶ P')
    (b : B) (x : moduleSpecΓFunctor.obj P) :
    moduleSpecΓFunctor.map (c.inv ≫ (pullback (Spec.map φ)).map e ≫ c'.hom)
      (b • mappedUnit φ P c.hom x) =
        b • mappedUnit φ P' c'.hom (moduleSpecΓFunctor.map e x) := by
  rw [(moduleSpecΓFunctor.map _).hom.map_smul, mappedUnit_map]

/-- The scalar law with tensor-ring instances, keeping the target sheaves abstract. -/
theorem mappedUnit_map_smul_triple (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    {A : CommRingCat.{u}} (φ : A ⟶ CommRingCat.of (AffineTripleOverlapMaps.Triple R S))
    {P P' : (Spec A).Modules}
    {Q Q' : (Spec (.of (AffineTripleOverlapMaps.Triple R S))).Modules}
    (c : (pullback (Spec.map φ)).obj P ≅ Q)
    (c' : (pullback (Spec.map φ)).obj P' ≅ Q') (e : P ⟶ P')
    (b : AffineTripleOverlapMaps.Triple R S) (x : moduleSpecΓFunctor.obj P) :
    moduleSpecΓFunctor.map (c.inv ≫ (pullback (Spec.map φ)).map e ≫ c'.hom)
      (b • mappedUnit φ P c.hom x) =
        b • mappedUnit φ P' c'.hom (moduleSpecΓFunctor.map e x) :=
  mappedUnit_map_smul φ c c' e b x

end FLT.Mazur.AffineScaledPullbackSections
