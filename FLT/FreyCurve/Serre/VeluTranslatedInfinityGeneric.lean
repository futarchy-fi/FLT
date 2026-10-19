/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluKernelGenericMorphismInvariant
public import FLT.FreyCurve.Serre.VeluTranslatedInfinityOpen

/-!
# The original generic map through a translated infinity neighborhood

Translation followed by its actual inverse retains the original source generic
point. Kernel invariance retains the original generic target morphism.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type} [Field K] [CharZero K] [DecidableEq K]
  (E : WeierstrassCurve K) [E.IsElliptic]
  (G : AddSubgroup E.toAffine.Point) [Fintype G]
  {u v : K} (hQ : E.toAffine.Nonsingular u v)

/-- The original source generic field maps into the translated neighborhood. -/
def veluTranslatedInfinityGenericPoint :
    Spec (integralCurve E).functionField ⟶ Spec (.of (InfinityTargetRing E G)) :=
  Spec.map (CommRingCat.ofHom (sourceSchemeFunctionFieldEquiv E).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (translationFieldHom E hQ).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (infinityTargetHom E G).toRingHom)

/-- The translated factorization retains the canonical source generic-stalk morphism. -/
@[reassoc] theorem veluTranslatedInfinityGenericPoint_source :
    veluTranslatedInfinityGenericPoint E G hQ ≫
        veluTranslatedInfinityOpenImmersion E G (.some u v hQ) =
      (integralCurve E).fromSpecStalk (genericPoint (integralCurve E)) := by
  simp only [veluTranslatedInfinityGenericPoint, veluTranslatedInfinityOpenImmersion,
    Category.assoc, veluInfinityOpenImmersion_generic_assoc]
  simp only [translationFieldHom_source_assoc,
    Iso.hom_inv_id, Category.comp_id]
  exact sourceSchemeFunctionFieldEquiv_spec E

/-- The translated open is dense in the actual source cubic. -/
theorem veluTranslatedInfinityOpenImmersion_dense :
    Dense ((veluTranslatedInfinityOpenImmersion E G (.some u v hQ)).opensRange :
      Set (integralCurve E)) := by
  apply (veluTranslatedInfinityOpenImmersion E G (.some u v hQ)).opensRange.isOpen.dense
  let z : Spec (integralCurve E).functionField := Classical.choice inferInstance
  exact ⟨_, ⟨veluTranslatedInfinityGenericPoint E G hQ z, rfl⟩⟩

variable [IsAlgClosed K] (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q)
  (hQG : Affine.Point.some u v hQ ∈ G)

include hQG

/-- The regular map on the transported open retains the original generic Vélu map. -/
@[reassoc] theorem veluTranslatedInfinityGenericPoint_target :
    veluTranslatedInfinityGenericPoint E G hQ ≫ veluInfinityRegularMorphism E G hodd =
      veluSchemeGenericMorphism E G hodd := by
  simp only [veluTranslatedInfinityGenericPoint, Category.assoc,
    veluInfinityRegularMorphism_generic, translationFieldHom_veluMorphism E G hodd hQ hQG]
  rfl

end WeierstrassCurve.Velu
