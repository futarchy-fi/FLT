/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluGlobalRestrictions
public import FLT.FreyCurve.Serre.VeluSchemeFunctionFieldHom
public import FLT.Mazur.WeierstrassIntegralProper

/-!
# Properness and surjectivity of the original global Vélu morphism

The original function-field injection shows that the generic point maps to
the generic point. Properness then upgrades dominance to scheme surjectivity.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type} [Field K] [CharZero K] [IsAlgClosed K] [DecidableEq K]
  (E : WeierstrassCurve K) [E.IsElliptic]
  (G : AddSubgroup E.toAffine.Point) [Fintype G]
  (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q)

/-- The global morphism sends the actual source generic point to the actual target generic point. -/
theorem veluGlobalMorphism_genericPoint :
    veluGlobalMorphism E G hodd (genericPoint (integralCurve E)) =
      genericPoint (integralCurve (curve E G)) := by
  have h := (veluGlobalMorphism_generic E G hodd).trans
    (veluSchemeFunctionFieldHom_generic E G hodd).symm
  have he := congrArg (fun f : Spec (integralCurve E).functionField ⟶
    integralCurve (curve E G) => f (IsLocalRing.closedPoint (integralCurve E).functionField)) h
  have hpoint (X : Scheme) [IsIntegral X] (z : Spec X.functionField) :
      X.fromSpecStalk (genericPoint X) z = genericPoint X := by
    have hz : z = IsLocalRing.closedPoint (X.presheaf.stalk (genericPoint X)) :=
      Subsingleton.elim (α := PrimeSpectrum X.functionField) _ _
    rw [hz]
    exact Scheme.fromSpecStalk_closedPoint
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at he
  exact (congrArg (veluGlobalMorphism E G hodd) (hpoint _ _)).symm.trans
    (he.trans (hpoint _ _))

/-- The original global Vélu morphism is dominant. -/
instance veluGlobalMorphism_isDominant : IsDominant (veluGlobalMorphism E G hodd) := by
  constructor
  rw [denseRange_iff_closure_range]
  apply Set.Subset.antisymm (Set.subset_univ _)
  rw [← genericPoint_closure (integralCurve (curve E G))]
  apply closure_mono
  exact Set.singleton_subset_iff.mpr
    ⟨genericPoint (integralCurve E), veluGlobalMorphism_genericPoint E G hodd⟩

/-- Properness follows from the proper source and separated original target over the field. -/
instance veluGlobalMorphism_isProper : IsProper (veluGlobalMorphism E G hodd) := by
  let _ : IsProper (veluGlobalMorphism E G hodd ≫ integralCurveStructure (curve E G)) := by
    rw [veluGlobalMorphism_base]
    infer_instance
  exact IsProper.of_comp _ (integralCurveStructure (curve E G))

/-- Every scheme point of the exact original target has a preimage. -/
instance veluGlobalMorphism_surjective : Surjective (veluGlobalMorphism E G hodd) :=
  surjective_of_isDominant_of_isClosed_range _
    (veluGlobalMorphism E G hodd).isClosedMap.isClosed_range

end WeierstrassCurve.Velu
