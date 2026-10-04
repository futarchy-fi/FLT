/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveFiniteSubgroup

/-!
# The closed subscheme of a finite subgroup in the whole curve

Finiteness over the base makes the subgroup closed even in the whole curve.
Its actual kernel ideal commutes with arbitrary base change.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
variable {S T : Scheme} {E : GeneralizedEllipticCurve S} {n : ℕ}
  (H : E.FiniteSubgroup n)

instance curveMap_closed : IsClosedImmersion H.curveMap.left := by
  have : IsIso E.smoothIso.hom.left :=
    inferInstanceAs (IsIso ((Over.forget S).map E.smoothIso.hom))
  have : IsOpenImmersion E.smoothIso.hom.left := inferInstance
  have : IsOpenImmersion E.inclusion.left := by
    change IsOpenImmersion (E.smoothIso.hom.left ≫ E.curve.hom.smoothLocus.ι)
    infer_instance
  have : IsPreimmersion H.curveMap.left := by
    change IsPreimmersion (H.inclusion.left ≫ E.inclusion.left)
    infer_instance
  have : IsProper E.curve.hom := E.family.family.1
  have : IsProper (H.curveMap.left ≫ E.curve.hom) := by
    rw [Over.w]
    infer_instance
  have : IsProper H.curveMap.left := IsProper.of_comp _ E.curve.hom
  exact IsClosedImmersion.of_isPreimmersion _ H.curveMap.left.isClosedMap.isClosed_range

/-- The ideal of the subgroup as a closed subscheme of the entire curve. -/
def ideal : E.curve.left.IdealSheafData := H.curveMap.left.ker

/-- Arbitrary base change preserves the actual closed-subgroup ideal. -/
@[simp]
theorem baseChange_ideal (g : T ⟶ S) :
    (H.baseChange g).ideal = H.ideal.comap (pullback.fst E.curve.hom g) := by
  let q := OverPullbackLocalPushout.map_isPullback g H.curveMap
  rw [ideal, baseChange_curveMap, ← q.isoPullback_hom_fst,
    Scheme.Hom.ker_comp_of_isIso]
  exact Scheme.IdealSheafData.ker_fst_of_isClosedImmersion _ _

/-- The subgroup is canonically its own closed subscheme. -/
def idealIso : H.carrier ≅ Over.mk (H.ideal.subschemeι ≫ E.curve.hom) :=
  Over.isoMk (asIso H.curveMap.left.toImage) (by simp [ideal])

/-- The subgroup ideal defines a finite locally free divisor candidate of rank `n`. -/
theorem ideal_degree :
    FCurve.FiniteLocallyFreeDegree (H.ideal.subschemeι ≫ E.curve.hom) n :=
  H.degree.of_overIso H.idealIso

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
