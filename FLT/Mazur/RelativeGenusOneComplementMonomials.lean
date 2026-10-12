/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeGenusOneComplementCoordinates
public import FLT.Mazur.RelativeGenusOneMonomialBasis

/-!
# The actual functions of the relative monomial basis

The retained low vectors and original pole transitions identify all six
basis functions with 1, x, y, x squared, xy and x cubed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle sectionPoleMultiplicativeCoordinates
  relativePoleFunction relativePointMonomialFourBasis relativePointMonomialFiveBasis
  relativePointMonomialSixBasis relativePointFramedThreeBasis

variable {S : Scheme} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (G : Over S) [GrpObj G] [IsProper G.hom]
  [SmoothOfRelativeDimension 1 G.hom] [GeometricallyIntegral G.hom]
  (hg : CurveFiberHypotheses.NodalGenusOneGeometricFibers G.hom)
  (s : 𝟙_ (Over S) ⟶ G) (hI : EffectiveCartier s.left.ker)
  (e : (pullback s.left).obj (divisorLineBundle s.left.ker hI) ≅ structureModule S)

/-- The first three ordered monomials, indexed like the original low-pole basis. -/
def relativePointLowMonomial {R : Type*} [CommRing R] (x y : R) :
    ((Unit ⊕ Unit) ⊕ Unit) → R :=
  Sum.elim (Sum.elim (fun _ ↦ 1) (fun _ ↦ x)) (fun _ ↦ y)

/-- The five lower monomials in the original cubic coefficient order. -/
def relativePointLowerMonomial {R : Type*} [CommRing R] (x y : R) :
    ((((Unit ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) → R :=
  Sum.elim (Sum.elim (relativePointLowMonomial x y) (fun _ ↦ x ^ 2)) (fun _ ↦ x * y)

/-- The retained first three basis vectors represent exactly 1, x and y. -/
theorem relativePointComplement_threeBasis (i : (Unit ⊕ Unit) ⊕ Unit) :
    relativePoleFunction G.hom s.left hI 3 (relativePointFramedThreeBasis G hg s hI e i) =
      relativePointLowMonomial (relativePointComplementX G hg s hI e)
        (relativePointComplementY G hg s hI e) i := by
  rcases i with ((u | u) | u) <;> cases u
  · rw [relativePointFramedThreeBasis_one, relativePoleFunction_step,
      relativePoleFunction_step, relativePointComplement_oneBasis]
    rfl
  · rw [relativePointFramedThreeBasis_x, relativePoleFunction_step]
    rfl
  · rw [relativePointFramedThreeBasis_y]
    rfl

/-- The fourth basis vector adds the square of the actual x function. -/
theorem relativePointComplement_fourBasis (i : ((Unit ⊕ Unit) ⊕ Unit) ⊕ Unit) :
    relativePoleFunction G.hom s.left hI 4 (relativePointMonomialFourBasis G hg s hI e i) =
      Sum.elim (relativePointLowMonomial (relativePointComplementX G hg s hI e)
        (relativePointComplementY G hg s hI e))
        (fun _ ↦ relativePointComplementX G hg s hI e ^ 2) i := by
  rcases i with i | u
  · rw [relativePointMonomialFourBasis_old, relativePoleFunction_step,
      relativePointComplement_threeBasis]
    rfl
  · cases u
    rw [relativePointMonomialFourBasis_new, relativePointComplement_square]
    rfl

/-- The original order-five basis represents exactly the five lower monomials. -/
theorem relativePointComplement_fiveBasis (i : (((Unit ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) :
    relativePoleFunction G.hom s.left hI 5 (relativePointMonomialFiveBasis G hg s hI e i) =
      relativePointLowerMonomial (relativePointComplementX G hg s hI e)
        (relativePointComplementY G hg s hI e) i := by
  rcases i with i | u
  · rw [relativePointMonomialFiveBasis_old, relativePoleFunction_step,
      relativePointComplement_fourBasis]
    rfl
  · cases u
    rw [relativePointMonomialFiveBasis_new, relativePointComplement_mixed]
    rfl

/-- All six actual order-six basis functions are the expected monomials. -/
theorem relativePointComplement_sixBasis
    (i : ((((Unit ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) :
    relativePoleFunction G.hom s.left hI 6 (relativePointMonomialSixBasis G hg s hI e i) =
      Sum.elim (relativePointLowerMonomial (relativePointComplementX G hg s hI e)
        (relativePointComplementY G hg s hI e))
        (fun _ ↦ relativePointComplementX G hg s hI e ^ 3) i := by
  rcases i with i | u
  · rw [relativePointMonomialSixBasis_old, relativePoleFunction_step,
      relativePointComplement_fiveBasis]
    rfl
  · cases u
    rw [relativePointMonomialSixBasis_new, relativePointComplement_cube]
    rfl

end FLT.Mazur.FCurve
