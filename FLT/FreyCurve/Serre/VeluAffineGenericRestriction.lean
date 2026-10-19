/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluAffineRegularMorphism
public import FLT.FreyCurve.Serre.VeluSchemeRationalMap

/-!
# The actual generic point factors through the explicit Vélu open

The principal-open field comparison factors the canonical generic-point map
of the actual source cubic, and retains the original generic Vélu formulas.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type} [Field K] [CharZero K] [DecidableEq K]
  (E : WeierstrassCurve K) (G : AddSubgroup E.toAffine.Point) [Fintype G]

/-- The original generic chart factors through the explicit denominator open. -/
@[reassoc] theorem veluAffineOpenImmersion_generic :
    Spec.map (CommRingCat.ofHom (veluAffineLocalizationHom E G).toRingHom) ≫
        veluAffineOpenImmersion E G =
      Spec.map (CommRingCat.ofHom (sourceGenericChart E).toRingHom) ≫
        integralCurveChart E 2 := by
  rw [veluAffineOpenImmersion, ← Spec.map_comp_assoc]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact veluAffineLocalizationHom_algebraMap E G a

/-- The actual source function field maps into the explicit principal-open scheme. -/
def veluAffineGenericPoint :
    Spec (integralCurve E).functionField ⟶ Spec (.of (VeluAffineLocalization E G)) :=
  Spec.map (CommRingCat.ofHom (sourceSchemeFunctionFieldEquiv E).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (veluAffineLocalizationHom E G).toRingHom)

/-- This factorization retains the canonical generic-point morphism of the actual cubic. -/
@[reassoc] theorem veluAffineGenericPoint_source :
    veluAffineGenericPoint E G ≫ veluAffineOpenImmersion E G =
      (integralCurve E).fromSpecStalk (genericPoint (integralCurve E)) := by
  rw [veluAffineGenericPoint, Category.assoc, veluAffineOpenImmersion_generic]
  exact sourceSchemeFunctionFieldEquiv_spec E

/-- The regular morphism restricts to the actual scheme generic Vélu map. -/
@[reassoc] theorem veluAffineGenericPoint_target (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q) :
    veluAffineGenericPoint E G ≫ veluAffineRegularMorphism E G hodd =
      veluSchemeGenericMorphism E G hodd := by
  rw [veluAffineGenericPoint, Category.assoc, veluAffineRegularMorphism_generic]
  rfl

/-- The denominator open is dense in the actual integral source cubic. -/
theorem veluAffineOpenImmersion_dense :
    Dense ((veluAffineOpenImmersion E G).opensRange : Set (integralCurve E)) := by
  apply (veluAffineOpenImmersion E G).opensRange.isOpen.dense
  let z : Spec (integralCurve E).functionField := Classical.choice inferInstance
  exact ⟨_, ⟨veluAffineGenericPoint E G z, rfl⟩⟩

end WeierstrassCurve.Velu
