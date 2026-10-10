/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LineSheafDualEvaluation
public import FLT.Mazur.ModuleSheafTensorAssociator
public import FLT.Mazur.ProjectiveTwistTensor

/-!
# Comparing actual tensor inverses

Two successive tensor inverses recover the original module by an explicit
composition of unitors, the associator and the given evaluation isomorphisms.
In particular the double intrinsic dual of a line is isomorphic to that line.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve

open ModuleSheafTensor ModuleSheafTensorAssociator

variable {X : Scheme.{u}}

/-- An explicit comparison between successive tensor inverses. -/
def tensorInverseComparison {L N K : X.Modules}
    (e : tensor N L ≅ structureModule X) (d : tensor K N ≅ structureModule X) : K ≅ L :=
  (rightUnitor K).symm ≪≫ congr (Iso.refl K) e.symm ≪≫
    (associator K N L).symm ≪≫ congr d (Iso.refl L) ≪≫ leftUnitor L

/-- The double dual of a line recovers the original line through actual evaluations. -/
def lineSheafDoubleDualIso {L : X.Modules} (hL : LocallyFreeRankOne L) :
    moduleSheafDual (moduleSheafDual L) ≅ L :=
  tensorInverseComparison (lineSheafDualEvaluationIso hL) (lineSheafDualEvaluationIso hL.dual)

/-- The explicit comparison transfers local rank one through two tensor inverses. -/
theorem locallyFreeRankOne_of_tensorInverses {L N K : X.Modules}
    (hL : LocallyFreeRankOne L) (e : tensor N L ≅ structureModule X)
    (d : tensor K N ≅ structureModule X) : LocallyFreeRankOne K :=
  hL.of_iso (tensorInverseComparison e d).symm

end FLT.Mazur.FCurve
