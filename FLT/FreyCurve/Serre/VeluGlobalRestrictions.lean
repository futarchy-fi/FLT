/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluGlobalMorphism

/-!
# Original local restrictions of the global Vélu morphism

The affine denominator open, infinity open and every translated kernel open
retain their original regular maps. The global map preserves the base field.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type} [Field K] [CharZero K] [IsAlgClosed K] [DecidableEq K]
  (E : WeierstrassCurve K) [E.IsElliptic]
  (G : AddSubgroup E.toAffine.Point) [Fintype G]
  (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q)

/-- The global map restricts to the original affine regular formula. -/
@[reassoc] theorem veluGlobalMorphism_affine :
    veluAffineOpenImmersion E G ≫ veluGlobalMorphism E G hodd =
      veluAffineRegularMorphism E G hodd := by
  apply (cancel_epi (veluAffineOpenImmersion E G).isoOpensRange.inv).mp
  rw [← Category.assoc, Scheme.Hom.isoOpensRange_inv_comp]
  exact veluGlobalMorphism_representative E G hodd (veluAffinePartialMap E G hodd)
    (veluAffinePartialMap_toRationalMap E G hodd)

/-- The global map restricts to the original regular extension at infinity. -/
@[reassoc] theorem veluGlobalMorphism_infinity :
    veluInfinityOpenImmersion E G ≫ veluGlobalMorphism E G hodd =
      veluInfinityRegularMorphism E G hodd := by
  apply (cancel_epi (veluInfinityOpenImmersion E G).isoOpensRange.inv).mp
  rw [← Category.assoc, Scheme.Hom.isoOpensRange_inv_comp]
  exact veluGlobalMorphism_representative E G hodd (veluInfinityPartialMap E G hodd)
    (veluInfinityPartialMap_toRationalMap E G hodd)

/-- The global map retains the actual regular extension at every original kernel point. -/
@[reassoc] theorem veluGlobalMorphism_translatedInfinity {u v : K}
    (hQ : E.toAffine.Nonsingular u v) (hQG : Affine.Point.some u v hQ ∈ G) :
    veluTranslatedInfinityOpenImmersion E G (.some u v hQ) ≫ veluGlobalMorphism E G hodd =
      veluInfinityRegularMorphism E G hodd := by
  apply (cancel_epi
    (veluTranslatedInfinityOpenImmersion E G (.some u v hQ)).isoOpensRange.inv).mp
  rw [← Category.assoc, Scheme.Hom.isoOpensRange_inv_comp]
  exact veluGlobalMorphism_representative E G hodd
    (veluTranslatedInfinityPartialMap E G hodd hQ)
    (veluTranslatedInfinityPartialMap_toRationalMap E G hodd hQ hQG)

/-- The global morphism is over the original coefficient field. -/
@[reassoc] theorem veluGlobalMorphism_base :
    veluGlobalMorphism E G hodd ≫ integralCurveStructure (curve E G) =
      integralCurveStructure E := by
  let _ : IsDominant (veluAffineOpenImmersion E G) := ⟨veluAffineOpenImmersion_dense E G⟩
  apply ext_of_isDominant (veluAffineOpenImmersion E G)
  rw [← Category.assoc, veluGlobalMorphism_affine, veluAffineRegularMorphism_base]

end WeierstrassCurve.Velu
