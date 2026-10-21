/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AuxiliaryMarkingFinitePresentation
public import FLT.Mazur.CyclicBoundaryUnrestrictedFiniteEquations

/-!
# Locally finitely presented relative charts for every generalized curve

Both the marking relations and the full cyclic closure equations have finite
presentation. The unrestricted closed chart and its ample open are therefore
locally finitely presented over every original base, with no Noetherian or
characteristic hypothesis. Versality for varying curves is a separate construction.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicBoundaryParameter
variable {S : Scheme} (E : GeneralizedEllipticCurve S) (n : ℕ) [NeZero n]

/-- The full original independent marking parameter is locally finitely presented. -/
instance originalParameter_locallyOfFinitePresentation :
    LocallyOfFinitePresentation (parameter E.group n).hom :=
  AuxiliaryLevel.homScheme_locallyOfFinitePresentation E.group (Label n)

/-- The actual closed cyclic chart is locally finitely presented over every original base. -/
instance unrestrictedLocusBase_finitePresentation :
    LocallyOfFinitePresentation (unrestrictedLocusBase E n) :=
  inferInstanceAs (LocallyOfFinitePresentation
    (unrestrictedMultiplicationLocusInclusion E n ≫ (parameter E.group n).hom))

/-- The ample chart is locally finitely presented even on arbitrary singular degenerations. -/
instance unrestrictedAmpleBase_finitePresentation :
    LocallyOfFinitePresentation (unrestrictedAmpleBase E n) :=
  inferInstanceAs (LocallyOfFinitePresentation
    ((unrestrictedAmpleOpen E n).ι ≫ unrestrictedLocusBase E n))

end FLT.Mazur.CyclicBoundaryParameter
