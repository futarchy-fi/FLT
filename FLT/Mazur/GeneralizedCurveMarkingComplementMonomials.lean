/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingComplementCoordinates
public import FLT.Mazur.GeneralizedCurveMarkingMonomialBasis

/-!
# The actual functions of the relative monomial basis

The retained low vectors and original pole transitions identify all six
basis functions with 1, x, y, x squared, xy and x cubed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ModuleSheafTensor.tensor divisorLineBundle
  sectionPoleMultiplicativeCoordinates Scheme.Modules.pullback
  relativePoleFunction smoothMarkingMonomialFourBasis smoothMarkingMonomialFiveBasis
  smoothMarkingMonomialSixBasis smoothMarkingFramedThreeBasis

variable {S : Scheme} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (E : GeneralizedEllipticCurve S) (s : 𝟙_ (Over S) ⟶ E.group)

local notation "t" => s ≫ E.inclusion
local notation "hI" => And.left (smoothMarking_relativeCartier E s)

/-- The structure morphism is proper for the original family. -/
local instance generalizedCurveMarkingComplementMonomialsProper :
    IsProper E.curve.hom := E.family.family.1

variable (e : (pullback (s ≫ E.inclusion).left).obj
  (divisorLineBundle (s ≫ E.inclusion).left.ker
    (smoothMarking_relativeCartier E s).1) ≅ structureModule S)

/-- The first three ordered monomials, indexed like the original low-pole basis. -/
def smoothMarkingLowMonomial {R : Type*} [CommRing R] (x y : R) :
    ((Unit ⊕ Unit) ⊕ Unit) → R :=
  Sum.elim (Sum.elim (fun _ ↦ 1) (fun _ ↦ x)) (fun _ ↦ y)

/-- The five lower monomials in the original cubic coefficient order. -/
def smoothMarkingLowerMonomial {R : Type*} [CommRing R] (x y : R) :
    ((((Unit ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) → R :=
  Sum.elim (Sum.elim (smoothMarkingLowMonomial x y) (fun _ ↦ x ^ 2)) (fun _ ↦ x * y)

/-- The retained first three basis vectors represent exactly 1, x and y. -/
theorem smoothMarkingComplement_threeBasis (i : (Unit ⊕ Unit) ⊕ Unit) :
    relativePoleFunction E.curve.hom (t).left (hI) 3 (smoothMarkingFramedThreeBasis E s e i) =
      smoothMarkingLowMonomial (smoothMarkingComplementX E s e)
        (smoothMarkingComplementY E s e) i := by
  rcases i with ((u | u) | u) <;> cases u
  · rw [smoothMarkingFramedThreeBasis_one, relativePoleFunction_step,
      relativePoleFunction_step, smoothMarkingComplement_oneBasis]
    rfl
  · rw [smoothMarkingFramedThreeBasis_x, relativePoleFunction_step]
    rfl
  · rw [smoothMarkingFramedThreeBasis_y]
    rfl

/-- The fourth basis vector adds the square of the actual x function. -/
theorem smoothMarkingComplement_fourBasis (i : ((Unit ⊕ Unit) ⊕ Unit) ⊕ Unit) :
    relativePoleFunction E.curve.hom (t).left (hI) 4 (smoothMarkingMonomialFourBasis E s e i) =
      Sum.elim (smoothMarkingLowMonomial (smoothMarkingComplementX E s e)
        (smoothMarkingComplementY E s e))
        (fun _ ↦ smoothMarkingComplementX E s e ^ 2) i := by
  rcases i with i | u
  · rw [smoothMarkingMonomialFourBasis_old, relativePoleFunction_step,
      smoothMarkingComplement_threeBasis]
    rfl
  · cases u
    rw [smoothMarkingMonomialFourBasis_new, smoothMarkingComplement_square]
    rfl

/-- The original order-five basis represents exactly the five lower monomials. -/
theorem smoothMarkingComplement_fiveBasis (i : (((Unit ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) :
    relativePoleFunction E.curve.hom (t).left (hI) 5 (smoothMarkingMonomialFiveBasis E s e i) =
      smoothMarkingLowerMonomial (smoothMarkingComplementX E s e)
        (smoothMarkingComplementY E s e) i := by
  rcases i with i | u
  · rw [smoothMarkingMonomialFiveBasis_old, relativePoleFunction_step,
      smoothMarkingComplement_fourBasis]
    rfl
  · cases u
    rw [smoothMarkingMonomialFiveBasis_new, smoothMarkingComplement_mixed]
    rfl

/-- All six actual order-six basis functions are the expected monomials. -/
theorem smoothMarkingComplement_sixBasis
    (i : ((((Unit ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) :
    relativePoleFunction E.curve.hom (t).left (hI) 6 (smoothMarkingMonomialSixBasis E s e i) =
      Sum.elim (smoothMarkingLowerMonomial (smoothMarkingComplementX E s e)
        (smoothMarkingComplementY E s e))
        (fun _ ↦ smoothMarkingComplementX E s e ^ 3) i := by
  rcases i with i | u
  · rw [smoothMarkingMonomialSixBasis_old, relativePoleFunction_step,
      smoothMarkingComplement_fiveBasis]
    rfl
  · cases u
    rw [smoothMarkingMonomialSixBasis_new, smoothMarkingComplement_cube]
    rfl

end FLT.Mazur.GeneralizedEllipticCurve
