/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicMarkingSingularFinitePresentation
public import FLT.Mazur.GeneralizedCurveUnrestrictedChartFiniteness

/-!
# Finite closed equations in every original unrestricted boundary parameter

The full cyclic equation locus has a finitely presented closed immersion
in the independent marking parameter, on arbitrary coefficient schemes.
Its affine equations include the actual nilpotent and repeated-label structure.
The ample chart remains locally of finite presentation in that same parameter.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicBoundaryParameter
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (E : GeneralizedEllipticCurve S) (n : ℕ) [NeZero n]

/-- The full original closed coefficient equations are finitely generated on each affine chart. -/
theorem unrestrictedMultiplicationCoefficientIdeal_fg
    (U : (parameter E.group n).left.affineOpens) :
    ((unrestrictedMultiplicationCoefficientIdeal E n).ideal U).FG :=
  (unrestrictedUniversalCurve E n).singularOrbitCoefficientIdeal_fg
    (unrestrictedUniversalMarking E n) U

/-- The original closed locus is finitely presented inside the full marking parameter. -/
instance unrestrictedMultiplicationLocusInclusion_locallyOfFinitePresentation :
    LocallyOfFinitePresentation (unrestrictedMultiplicationLocusInclusion E n) :=
  (unrestrictedUniversalCurve E n).singularOrbitLocusInclusion_locallyOfFinitePresentation
    (unrestrictedUniversalMarking E n)

/-- The actual ample parameter maps to the original independent marking scheme. -/
def unrestrictedAmpleParameterInclusion : (unrestrictedAmpleOpen E n).toScheme ⟶
    (parameter E.group n).left :=
  (unrestrictedAmpleOpen E n).ι ≫ unrestrictedMultiplicationLocusInclusion E n

/-- The ample chart is locally finitely presented in the independent marking parameter. -/
instance unrestrictedAmpleParameterInclusion_locallyOfFinitePresentation :
    LocallyOfFinitePresentation (unrestrictedAmpleParameterInclusion E n) :=
  inferInstanceAs (LocallyOfFinitePresentation
    ((unrestrictedAmpleOpen E n).ι ≫ unrestrictedMultiplicationLocusInclusion E n))

/-- The actual ample parameter inclusion recovers the original coefficient structure map. -/
theorem unrestrictedAmpleParameterInclusion_base :
    unrestrictedAmpleParameterInclusion E n ≫ (parameter E.group n).hom =
      unrestrictedAmpleBase E n :=
  Category.assoc _ _ _

end FLT.Mazur.CyclicBoundaryParameter
