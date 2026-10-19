/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluInfinityGenericMorphism
public import FLT.FreyCurve.Serre.VeluSchemeRationalMap

/-!
# The actual generic point factors through the explicit Vélu open

The iterated principal-open field comparison factors the canonical generic-point map
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

/-- The actual source function field maps into the explicit iterated principal-open scheme. -/
def veluInfinityGenericPoint :
    Spec (integralCurve E).functionField ⟶ Spec (.of (InfinityTargetRing E G)) :=
  Spec.map (CommRingCat.ofHom (sourceSchemeFunctionFieldEquiv E).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (infinityTargetHom E G).toRingHom)

/-- This factorization retains the canonical generic-point morphism of the actual cubic. -/
@[reassoc] theorem veluInfinityGenericPoint_source :
    veluInfinityGenericPoint E G ≫ veluInfinityOpenImmersion E G =
      (integralCurve E).fromSpecStalk (genericPoint (integralCurve E)) := by
  rw [veluInfinityGenericPoint, Category.assoc, veluInfinityOpenImmersion_generic]
  exact sourceSchemeFunctionFieldEquiv_spec E

/-- The regular morphism restricts to the actual scheme generic Vélu map. -/
@[reassoc] theorem veluInfinityGenericPoint_target (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q) :
    veluInfinityGenericPoint E G ≫ veluInfinityRegularMorphism E G hodd =
      veluSchemeGenericMorphism E G hodd := by
  rw [veluInfinityGenericPoint, Category.assoc, veluInfinityRegularMorphism_generic]
  rfl

/-- The infinity neighborhood is dense in the actual integral source cubic. -/
theorem veluInfinityOpenImmersion_dense :
    Dense ((veluInfinityOpenImmersion E G).opensRange : Set (integralCurve E)) := by
  apply (veluInfinityOpenImmersion E G).opensRange.isOpen.dense
  let z : Spec (integralCurve E).functionField := Classical.choice inferInstance
  exact ⟨_, ⟨veluInfinityGenericPoint E G z, rfl⟩⟩

end WeierstrassCurve.Velu
