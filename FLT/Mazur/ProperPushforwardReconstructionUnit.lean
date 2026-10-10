/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperLinePushforwardTilde

/-!
# Unit sections in proper direct-image reconstruction

The proper direct-image tilde isomorphism recovers each original section
from its affine adjunction unit. This normalization also survives pullback.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FLT.Mazur.LineSectionBaseChange
open FCurve Chow AffineModuleGlobalSections
variable {X S : Scheme.{0}} [IsAffine S] (f : X ⟶ S) [IsProper f]
  (M : X.Modules) [M.IsQuasicoherent]

/-- Reconstruction of the unit of a base-linear section recovers that same section. -/
lemma properPushforwardTildeIso_unit (s : baseSections M f.appTop.hom ⊤) :
    (properPushforwardTildeIso f M).hom.app ⊤
        ((affineAdjunction S).unit.app _ s) = s := by
  have hn := congrArg (fun k ↦ k s) ((affineAdjunction S).unit.naturality
    (properPushforwardSectionsEquiv f M).symm.toModuleIso.hom)
  have ht := congrArg (fun k ↦ k ((properPushforwardSectionsEquiv f M).symm s))
    ((affineAdjunction S).right_triangle_components ((pushforward f).obj M))
  change ((affineAdjunction S).counit.app ((pushforward f).obj M)).app ⊤
    (((affineTilde S).map (properPushforwardSectionsEquiv f M).symm.toModuleIso.hom).app ⊤
      ((affineAdjunction S).unit.app _ s)) = _
  change (affineAdjunction S).unit.app _ ((properPushforwardSectionsEquiv f M).symm s) =
    ((affineTilde S).map (properPushforwardSectionsEquiv f M).symm.toModuleIso.hom).app ⊤
      ((affineAdjunction S).unit.app _ s) at hn
  rw [← hn]
  exact ht

/-- Pulling back the reconstruction retains the original pulled section. -/
lemma properPushforwardTildeIso_pull_unit {T : Scheme.{0}} (g : T ⟶ S)
    (s : baseSections M f.appTop.hom ⊤) :
    ((pullback g).map (properPushforwardTildeIso f M).hom).app ⊤
        (pullGlobal g _ ((affineAdjunction S).unit.app _ s)) =
      pullGlobal g ((pushforward f).obj M) s := by
  rw [pullGlobal_naturality, properPushforwardTildeIso_unit]

end FLT.Mazur.LineSectionBaseChange
