/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperFamilyRigidifiedTransitions
public import FLT.Mazur.SchemeIndependentPairNormalization

/-!
# Rigidified transitions at named coordinates

Equality transport retains the prescribed normalization formula when further
restriction lands at named coordinates instead of syntactic composites.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.SchemePicard
open FCurve.LineSheafSectionRigidity
variable {X S : Scheme.{0}}
  (f : X ⟶ S) (e : S ⟶ X) (he : e ≫ f = 𝟙 S)

/-- The original normalized rigidified isomorphism at two named coordinates. -/
def rigidifiedBaseIsoNormalizeNamed {T U V W : Over S}
    (k : T ⟶ U) (g : U ⟶ V) (h : U ⟶ W) (g' : T ⟶ V) (h' : T ⟶ W)
    (wg : k ≫ g = g') (wh : k ≫ h = h')
    (L : RigidifiedBundle (pointedBaseSection f e he V))
    (M : RigidifiedBundle (pointedBaseSection f e he W))
    (i : RigidifiedIso (pointedBaseSection f e he U)
      (rigidifiedBasePullback f e he g L).2 (rigidifiedBasePullback f e he h M).2) :
    RigidifiedIso (pointedBaseSection f e he T)
      (rigidifiedBasePullback f e he g' L).2 (rigidifiedBasePullback f e he h' M).2 := by
  subst g' h'
  exact rigidifiedBaseIsoNormalize f e he k g h L M i

/-- Named transport retains the exact independent-pair normalization formula. -/
theorem rigidifiedBaseIsoNormalizeNamed_val {T U V W : Over S}
    (k : T ⟶ U) (g : U ⟶ V) (h : U ⟶ W) (g' : T ⟶ V) (h' : T ⟶ W)
    (wg : k ≫ g = g') (wh : k ≫ h = h')
    (L : RigidifiedBundle (pointedBaseSection f e he V))
    (M : RigidifiedBundle (pointedBaseSection f e he W))
    (i : RigidifiedIso (pointedBaseSection f e he U)
      (rigidifiedBasePullback f e he g L).2 (rigidifiedBasePullback f e he h M).2) :
    (rigidifiedBaseIsoNormalizeNamed f e he k g h g' h' wg wh L M i).val =
      SchemeIndependentPairNormalization.normalize
        (relativeTotalMap f g) (relativeTotalMap f h) (relativeTotalMap f k)
        (relativeTotalMap f g') (relativeTotalMap f h')
        ((relativeTotalMap_comp f k g).symm.trans (congrArg (relativeTotalMap f) wg))
        ((relativeTotalMap_comp f k h).symm.trans (congrArg (relativeTotalMap f) wh))
        L.1.val M.1.val i.val := by
  subst g' h'
  rfl

/-- Restricted class equalities remain valid at the original named coordinates. -/
theorem rigidifiedTransition_class_named {T U V W : Over S}
    (k : T ⟶ U) (g : U ⟶ V) (h : U ⟶ W) (g' : T ⟶ V) (h' : T ⟶ W)
    (wg : k ≫ g = g') (wh : k ≫ h = h')
    (L : RigidifiedBundle (pointedBaseSection f e he V))
    (M : RigidifiedBundle (pointedBaseSection f e he W))
    (a : rigidifiedBaseClass f e he g L = rigidifiedBaseClass f e he h M) :
    rigidifiedBaseClass f e he g' L = rigidifiedBaseClass f e he h' M := by
  subst g' h'
  exact rigidifiedTransition_class_pullback f e he k g h L M a

variable [IsLocallyNoetherian S] [IsProper f] [Flat f]
  [GeometricallyConnected f] [GeometricallyReduced f]

/-- The prescribed normalized transition equals the unique transition at named endpoints. -/
theorem rigidifiedTransition_normalize_named {T U V W : Over S}
    (k : T ⟶ U) (g : U ⟶ V) (h : U ⟶ W) (g' : T ⟶ V) (h' : T ⟶ W)
    (wg : k ≫ g = g') (wh : k ≫ h = h')
    (L : RigidifiedBundle (pointedBaseSection f e he V))
    (M : RigidifiedBundle (pointedBaseSection f e he W))
    (a : rigidifiedBaseClass f e he g L = rigidifiedBaseClass f e he h M)
    (b : rigidifiedBaseClass f e he g' L = rigidifiedBaseClass f e he h' M) :
    SchemeIndependentPairNormalization.normalize
        (relativeTotalMap f g) (relativeTotalMap f h) (relativeTotalMap f k)
        (relativeTotalMap f g') (relativeTotalMap f h')
        ((relativeTotalMap_comp f k g).symm.trans (congrArg (relativeTotalMap f) wg))
        ((relativeTotalMap_comp f k h).symm.trans (congrArg (relativeTotalMap f) wh))
        L.1.val M.1.val (rigidifiedTransition f e he g h L M a).val =
      (rigidifiedTransition f e he g' h' L M b).val := by
  rw [← rigidifiedBaseIsoNormalizeNamed_val f e he k g h g' h' wg wh]
  exact congrArg Subtype.val
    ((pointedFamily_rigidifiedIso_subsingleton f e he T _ _).elim _ _)

end FLT.Mazur.SchemePicard
