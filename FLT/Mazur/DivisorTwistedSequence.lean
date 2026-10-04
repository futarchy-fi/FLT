/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorClosedCokernel
public import FLT.Mazur.ModuleLineBundleTensorPullback

/-!
# The divisor sequence with a line coefficient

Tensor the canonical divisor sequence by an arbitrary line sheaf. Its quotient
is the closed pushforward of the restriction of O(D) tensored with that line.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve

open ModuleSheafTensor

variable {X : Scheme.{u}} {I : X.IdealSheafData} (hI : EffectiveCartier I)
  (L : X.Modules)

/-- The actual divisor exact sequence tensored by a coefficient sheaf. -/
def divisorTwistedComplex : ShortComplex X.Modules :=
  (divisorSectionComplex hI).map (ModuleSheafTensorCurrying.tensoring L)

/-- A line coefficient preserves short exactness of the divisor sequence. -/
theorem divisorTwistedComplex_shortExact (hL : LocallyFreeRankOne L) :
    (divisorTwistedComplex hI L).ShortExact :=
  ModuleLineTensorExact.shortExact _ (divisorSectionComplex_shortExact hI) L hL

/-- The quotient is canonically the closed pushforward of the restricted tensor line. -/
def divisorTwistedQuotientIso (hL : LocallyFreeRankOne L) :
    (divisorTwistedComplex hI L).X₃ ≅
      (pushforward I.subschemeι).obj ((pullback I.subschemeι).obj
        (tensor (divisorLineBundle I hI) L)) :=
  congr (divisorCokernelClosedIso hI) (Iso.refl L) ≪≫
    (ClosedLineProjectionFormula.projectionIso I.subschemeι
      ((pullback I.subschemeι).obj (divisorLineBundle I hI)) L hL).symm ≪≫
    (pushforward I.subschemeι).mapIso
      (ModuleLineBundleTensorPullback.tensorIso I.subschemeι _ _).symm

end FLT.Mazur.FCurve
