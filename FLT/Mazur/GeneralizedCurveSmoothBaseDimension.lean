/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveBaseChange
public import FLT.Mazur.ProperSmoothBaseLocus
public import FLT.Mazur.SmoothNodalFamilyDimension

/-!
# The original generalized curve on its smooth base locus

The smooth base open now carries relative dimension one, as a consequence
of the original nodal fibers. No relative dimension hypothesis is added.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {S : Scheme.{0}} (E : GeneralizedEllipticCurve S)

/-- A smooth original generalized curve has relative dimension one from its own fiber data. -/
theorem smooth_relativeDimension [Smooth E.curve.hom] :
    SmoothOfRelativeDimension 1 E.curve.hom :=
  E.family.toNodalFamilyCore.fibers.smooth_relativeDimension

/-- The original base open where every point of the original curve is smooth. -/
def smoothBaseOpen : S.Opens := by
  let _ : IsProper E.curve.hom := E.family.family.1
  exact properSmoothBaseLocus E.curve.hom

/-- The original curve over every open contained in its smooth base has relative dimension one. -/
theorem baseChange_open_relativeDimension (U : S.Opens) (hU : U ≤ smoothBaseOpen E) :
    SmoothOfRelativeDimension 1 (E.baseChange U.ι).curve.hom := by
  let _ : IsProper E.curve.hom := E.family.family.1
  let _ : Smooth (E.curve.hom ∣_ U) :=
    (smooth_restrict_iff_le_properSmoothBaseLocus E.curve.hom U).mpr hU
  let _ : Smooth (E.baseChange U.ι).curve.hom := by
    change Smooth (pullback.snd E.curve.hom U.ι)
    rw [← pullbackRestrictIsoRestrict_hom_morphismRestrict]
    infer_instance
  exact smooth_relativeDimension (E.baseChange U.ι)

/-- The actual base change to the maximal smooth base open is a relative curve. -/
instance smoothBase_relativeDimension :
    SmoothOfRelativeDimension 1 (E.baseChange (smoothBaseOpen E).ι).curve.hom :=
  baseChange_open_relativeDimension E _ le_rfl

end FLT.Mazur.GeneralizedEllipticCurve
