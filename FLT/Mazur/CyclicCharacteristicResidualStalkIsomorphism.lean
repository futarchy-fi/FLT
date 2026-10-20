/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAffineResidualIsomorphism

/-!
# Stalk isomorphisms of the original residual comparison

These are the stalk maps of the proved locally ringed comparison, with their
original section pullbacks and germ equations retained.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (i : InvariantAffineIndex n)
  (z : affineOrbitOpen n i)

/-- The actual residual comparison induces an isomorphism on every stalk. -/
instance affineResidualRingedComparison_stalkMap_isIso :
    IsIso ((affineResidualRingedComparison n i).stalkMap z) := by
  let F := LocallyRingedSpace.forgetToSheafedSpace ⋙
    SheafedSpace.forgetToPresheafedSpace
  have : IsIso (F.map (affineResidualRingedComparison n i)) := inferInstance
  exact PresheafedSpace.stalkMap.isIso (F.map (affineResidualRingedComparison n i)) z

/-- The stalk comparison is the original sheaf pullback, bundled as an isomorphism. -/
def affineResidualStalkIso :
    (affineResidualSpectrum n i).presheaf.stalk
      ((affineResidualRingedComparison n i).base z) ≅
        (invariantOpenSpace n (affineOrbitOpen n i)).presheaf.stalk z :=
  asIso ((affineResidualRingedComparison n i).stalkMap z)

/-- The stalk isomorphism preserves the original section pullback and germs. -/
theorem affineResidualStalkIso_germ
    (V : (affineResidualSpectrum n i).Opens)
    (hz : (affineResidualRingedComparison n i).base z ∈ V)
    (s : (affineResidualSpectrum n i).presheaf.obj (Opposite.op V)) :
    (affineResidualStalkIso n i z).hom
      ((affineResidualSpectrum n i).presheaf.germ V _ hz s) =
        (invariantOpenSpace n (affineOrbitOpen n i)).presheaf.germ _ z hz
          ((affineResidualRingedComparison n i).c.app (Opposite.op V) s) :=
  LocallyRingedSpace.stalkMap_germ_apply (affineResidualRingedComparison n i) V z hz s

end FLT.Mazur.CyclicCharacteristicOrbit
