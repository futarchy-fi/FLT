/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Global functions on proper geometrically integral fibers

Universal closedness makes the actual map on global sections integral.
Over an algebraically closed field an integral scheme therefore has exactly
the base field as its global functions. This applies to every geometric fiber.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeProperGeometricFiberSections
variable {K : Type u} [Field K] {X : Scheme.{u}}

/-- The actual scalar map from the base field into scheme global sections. -/
def scalarMap (f : X ⟶ Spec (.of K)) : CommRingCat.of K ⟶ Γ(X, ⊤) :=
  (Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop

/-- Universal closedness makes the scalar map on global functions integral. -/
lemma scalarMap_integral (f : X ⟶ Spec (.of K)) [UniversallyClosed f] :
    (scalarMap f).hom.IsIntegral := by
  apply RingHom.isIntegral_respectsIso.2
    (e := (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv)
  exact isIntegral_appTop_of_universallyClosed f

/-- An integral universally closed scheme over an algebraically closed field has H0 = K. -/
lemma scalarMap_bijective (f : X ⟶ Spec (.of K))
    [IsIntegral X] [UniversallyClosed f] [IsAlgClosed K] :
    Function.Bijective (scalarMap f).hom :=
  IsAlgClosed.ringHom_bijective_of_isIntegral _ (scalarMap_integral f)

/-- The H0 comparison is the actual scalar map, bundled as a ring isomorphism. -/
def sectionsIso (f : X ⟶ Spec (.of K))
    [IsIntegral X] [UniversallyClosed f] [IsAlgClosed K] :
    CommRingCat.of K ≅ Γ(X, ⊤) :=
  (RingEquiv.ofBijective (scalarMap f).hom (scalarMap_bijective f)).toCommRingCatIso

/-- The isomorphism retains the original pullback of global functions. -/
lemma sectionsIso_hom (f : X ⟶ Spec (.of K))
    [IsIntegral X] [UniversallyClosed f] [IsAlgClosed K] :
    (sectionsIso f).hom = scalarMap f := rfl

variable {S : Scheme.{u}} (f : X ⟶ S) [UniversallyClosed f] [GeometricallyIntegral f]

/-- Every algebraically closed field base change has the actual H0 comparison. -/
def geometricFiberSectionsIso [IsAlgClosed K] (s : Spec (.of K) ⟶ S) :
    CommRingCat.of K ≅ Γ(Limits.pullback f s, ⊤) := by
  let _ := GeometricallyIntegral.isIntegral_of_subsingleton (Limits.pullback.snd f s)
  exact sectionsIso (Limits.pullback.snd f s)

/-- Geometric fiber comparison uses the original base-change projection on sections. -/
lemma geometricFiberSectionsIso_hom [IsAlgClosed K] (s : Spec (.of K) ⟶ S) :
    (geometricFiberSectionsIso f s).hom = scalarMap (Limits.pullback.snd f s) := rfl

end FLT.Mazur.SchemeProperGeometricFiberSections
