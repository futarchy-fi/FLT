/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveGroupRelativeDimension
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Finiteness of the original smooth group

The smooth group is separated because it is the actual open of a proper
curve. Over a Noetherian base that open is Noetherian and quasi-compact,
including when the original curve has singular fibers.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (E : GeneralizedEllipticCurve S)

/-- The original smooth group is separated, without any extra curve hypothesis. -/
instance smoothGroup_separated : IsSeparated E.group.hom := by
  let _ : IsProper E.curve.hom := E.family.family.1
  rw [← E.inclusion.w]
  infer_instance

/-- The entire proper curve is Noetherian over a Noetherian base. -/
theorem curve_isNoetherian [IsNoetherian S] : IsNoetherian E.curve.left := by
  let _ : IsProper E.curve.hom := E.family.family.1
  exact {
    toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian E.curve.hom
    toCompactSpace := QuasiCompact.compactSpace_of_compactSpace E.curve.hom }

/-- The actual smooth group is Noetherian even along singular degenerations. -/
theorem smoothGroup_isNoetherian [IsNoetherian S] : IsNoetherian E.group.left := by
  let _ := curve_isNoetherian E
  let _ : NoetherianSpace E.group.left :=
    E.inclusion.left.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  exact {
    toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian E.group.hom
    toCompactSpace := inferInstance }

/-- The smooth group of an arbitrary original Noetherian family is quasi-compact. -/
instance smoothGroup_quasiCompact [IsNoetherian S] : QuasiCompact E.group.hom := by
  let _ := smoothGroup_isNoetherian E
  infer_instance

end FLT.Mazur.GeneralizedEllipticCurve
