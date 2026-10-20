/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicCharacterGroupEffectivity

/-!
# Uniqueness of the effective original smooth character map

Any original smooth morphism with the constructed finite reductions is the
effective map. The comparison does not assume that the competing map lands
in the Y chart: the Jacobson criterion proves that factorization.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.OneGonAdicCharacterTower

open OneGonSmoothing WeierstrassIntegralChart CharacterSchemeBaseChange

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R G : Type} [CommRing R] [AddCommGroup G] [Finite G]
  (I : Ideal R) [IsAdicComplete I R] (t : R) (ht : t ∈ I)
  (g : stageSource I G 0 ⟶ stageGroup I t 0)

/-- The full finite reductions uniquely determine an original smooth morphism. -/
theorem effectiveSmooth_unique
    (q : Spec (.of (AddMonoidAlgebra R G)) ⟶ (integralSmoothOpen (equation t)).toScheme)
    (hq : ∀ m, Spec.map
      (CommRingCat.ofHom (FiniteCharacterAdicElements.reduction (G := G) I m)) ≫ q =
        (tower I t ht g m).hom.hom.hom.left ≫ smoothProjection I t m) :
    q = effectiveSmooth I t ht g := by
  apply (cancel_mono (integralSmoothOpen (equation t)).ι).mp
  symm
  apply FiniteCharacterAdicElements.schemeMap_ext_of_chart I
    (integralCurveChart (equation t) 1)
  · rw [effectiveSmooth_inclusion]
    rintro _ ⟨x, rfl⟩
    exact ⟨_, rfl⟩
  · intro m
    rw [← Category.assoc, ← Category.assoc, effectiveSmooth_reduction, hq m]

/-- The complete original group homomorphism is uniquely determined by its constructed tower. -/
theorem effectiveCharacterHom_unique
    (q : CommGrp.mk (model R G) ⟶ integralSmoothGroup (equation t))
    (hq : ∀ m, Spec.map
      (CommRingCat.ofHom (FiniteCharacterAdicElements.reduction (G := G) I m)) ≫
        q.hom.hom.hom.left =
          (tower I t ht g m).hom.hom.hom.left ≫ smoothProjection I t m) :
    q = effectiveCharacterHom I t ht g := by
  apply CommGrp.hom_ext
  apply Over.OverMorphism.ext
  exact effectiveSmooth_unique I t ht g q.hom.hom.hom.left hq

end FLT.Mazur.OneGonAdicCharacterTower
