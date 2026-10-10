/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIntegralProjectiveClosed
public import FLT.Mazur.IdealQuotientExact

/-!
# The actual cubic structure-sheaf quotient

The original closed immersion gives a canonical morphism from the ambient
structure module to the pushforward of the cubic's structure module.
Surjectivity on affine opens proves this morphism is an epimorphism.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open FLT.Mazur.FCurve FLT.Mazur.ProjectiveSpace

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [CommRing R] (W : WeierstrassCurve R)

/-- The original cubic's structure module, pushed forward along its projective embedding. -/
def cubicStructurePushforward : (space R (Fin 3)).Modules :=
  (Scheme.Modules.pushforward (integralProjectiveMap W)).obj (structureModule (integralCurve W))

/-- The canonical structure-sheaf morphism associated with the actual closed immersion. -/
def cubicStructureQuotient : structureModule (space R (Fin 3)) ⟶ cubicStructurePushforward W :=
  ⟨PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom ((integralProjectiveMap W).app U.unop).hom.toAddMonoidHom
      naturality := fun _ _ f => by
        ext x
        exact congr($((integralProjectiveMap W).naturality f) x) }
    (fun U r m => ((integralProjectiveMap W).app U.unop).hom.map_mul r m)⟩

/-- On sections the quotient is exactly the original scheme morphism's ring map. -/
@[simp] theorem cubicStructureQuotient_app (U : (space R (Fin 3)).Opens)
    (s : Γ(space R (Fin 3), U)) :
    (cubicStructureQuotient W).app U s = (integralProjectiveMap W).app U s := rfl

/-- The actual quotient is surjective on every affine open of the ambient plane. -/
theorem cubicStructureQuotient_affine_surjective (U : (space R (Fin 3)).affineOpens) :
    Function.Surjective ((cubicStructureQuotient W).app U.1) :=
  (integralProjectiveMap W).app_surjective U.1 U.2

/-- The right-hand arrow of the cubic sequence is an epimorphism over every base ring. -/
instance cubicStructureQuotient_epi : Epi (cubicStructureQuotient W) where
  left_cancellation g h he := by
    apply moduleHom_ext_affine
    intro U
    ext s
    obtain ⟨r, rfl⟩ := cubicStructureQuotient_affine_surjective W U s
    exact congrArg (fun k => k.app U.1 r) he

end FLT.Mazur.WeierstrassIntegralChart
