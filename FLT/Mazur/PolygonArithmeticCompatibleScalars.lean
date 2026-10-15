/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticCompatibleRing
public import FLT.Mazur.PolygonArithmeticCompleteBaseSquare

/-!
# Original-base scalars on compatible polygon sections

The integral action comes from the actual structure morphisms of every
stage. Compatibility is proved on those morphisms, with no lifting assumption.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonArithmeticStages

open SectionGradedSum SectionGradedMultiplication

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (A : Type) [CommRing A] (π : A) (n : ℕ) (h : 2 ≤ n)

/-- Integral scalars in each actual stage section ring, placed in degree zero. -/
def boundaryIntegralScalars (m : ℕ) : A →+* boundaryGradedSections A π n h m :=
  (algebraMap Γ((family A π m n h).left, ⊤) (boundaryGradedSections A π n h m)).comp
    (((family A π m n h).hom ≫ baseToIntegral A π m).appTop.hom.comp
      (Scheme.ΓSpecIso (.of A)).inv.hom)

/-- Original-base scalars have the specified degree-zero section in every stage. -/
theorem boundaryIntegralScalars_eq (m : ℕ) (r : A) :
    boundaryIntegralScalars A π n h m r =
      of (boundaryLine A π m n h) ⊤ 0
        (((family A π m n h).hom ≫ baseToIntegral A π m).appTop
          ((Scheme.ΓSpecIso (.of A)).inv r)) := rfl

/-- All actual stage transitions preserve the integral-base scalars. -/
theorem boundarySectionsMap_integral {a b : ℕ} (f : a ⟶ b) :
    (boundarySectionsMap A π n h f).comp (boundaryIntegralScalars A π n h b) =
      boundaryIntegralScalars A π n h a := by
  apply RingHom.ext
  intro r
  change boundarySectionsMap A π n h f (boundaryIntegralScalars A π n h b r) = _
  rw [boundaryIntegralScalars_eq, boundarySectionsMap_of, SectionGradedIso.pieceMap_zero,
    SectionGradedPullback.pull_zero, boundaryIntegralScalars_eq]
  congr 1
  have hh := congrArg (fun k : (family A π a n h).left ⟶ Spec (.of A) ↦
    k.appTop ((Scheme.ΓSpecIso (.of A)).inv r)) ((stageIntegralStructure A π n h).naturality f)
  change ((stageSystem A π n h).map f ≫
    ((family A π b n h).hom ≫ baseToIntegral A π b)).appTop
      ((Scheme.ΓSpecIso (.of A)).inv r) =
    (((family A π a n h).hom ≫ baseToIntegral A π a) ≫ 𝟙 _).appTop
      ((Scheme.ΓSpecIso (.of A)).inv r) at hh
  rw [Category.comp_id, Scheme.Hom.comp_appTop] at hh
  exact hh

/-- The integral coefficient ring acts on the compatible-section ring. -/
def compatibleIntegralScalars : A →+* compatibleSectionRing A π n h :=
  compatibleSectionLift A π n h (boundaryIntegralScalars A π n h)
    (fun f ↦ boundarySectionsMap_integral A π n h f)

/-- The compatible ring is an algebra over the actual integral coefficient base. -/
instance compatibleSectionAlgebra : Algebra A (compatibleSectionRing A π n h) :=
  (compatibleIntegralScalars A π n h).toAlgebra

/-- The integral-base algebra map evaluates to the original stage structure map. -/
theorem compatibleSectionEval_algebraMap (m : ℕ) (r : A) :
    compatibleSectionEval A π n h m (algebraMap A (compatibleSectionRing A π n h) r) =
      boundaryIntegralScalars A π n h m r := rfl

end FLT.Mazur.PolygonArithmeticStages
