/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperAtlasAbelNaturality
public import FLT.Mazur.ProperLineIteratedFiberVanishing

/-!
# Abel-fiber naturality with derived changed-base acyclicity

The original residue vanishing alone supplies the changed-base residue
vanishing. On affine Noetherian test bases the independently constructed
geometric pullback commutes with the atlas/Abel-fiber equivalence in both
directions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.CartierAbel
open FCurve LineSectionBaseChange
variable {X S T : Scheme.{0}} (f : X ⟶ S) (g : T ⟶ S) (L : X.Modules)
  [IsAffine S] [IsAffine T] [IsNoetherianRing Γ(S, ⊤)] [IsNoetherianRing Γ(T, ⊤)]
  [IsProper f] [Flat f] [Surjective f] [GeometricallyIntegral f]
  (hL : LocallyFreeRankOne L)
  (hV : ∀ (z : PrimeSpectrum Γ(S, ⊤)) n,
    Subsingleton (ModuleH (residueAlgebraFiberLine f L z) (n + 1)))

/-- The geometric atlas map using only the original family's cohomological data. -/
@[irreducible] def properAtlasPullback (p : DirectImageAtlasSection f L hL hV) :
    DirectImageAtlasSection (Limits.pullback.snd f g) _
      (hL.pullback (Limits.pullback.fst f g))
      (baseChanged_residue_fiber_vanishing (IsPullback.of_hasPullback f g) L hL hV) :=
  properAtlasBaseChange f g L hL hV
    (baseChanged_residue_fiber_vanishing (IsPullback.of_hasPullback f g) L hL hV) p

/-- Forward naturality requires no independent changed-base vanishing hypothesis. -/
theorem atlasRelativeFiberEquiv_pullback (p : DirectImageAtlasSection f L hL hV) :
    atlasRelativeFiberEquiv (Limits.pullback.snd f g) _
        (hL.pullback (Limits.pullback.fst f g))
        (baseChanged_residue_fiber_vanishing (IsPullback.of_hasPullback f g) L hL hV)
        (properAtlasPullback f g L hL hV p) =
      fiberBaseChange f g L hL (atlasRelativeFiberEquiv f L hL hV p) := by
  unfold properAtlasPullback
  exact atlasRelativeFiberEquiv_baseChange f g L hL hV _ p

/-- Recovering geometric atlas sections from divisors commutes with actual base change. -/
theorem atlasRelativeFiberEquiv_symm_pullback (D : RelativeFiber f L hL) :
    properAtlasPullback f g L hL hV ((atlasRelativeFiberEquiv f L hL hV).symm D) =
      (atlasRelativeFiberEquiv (Limits.pullback.snd f g) _
        (hL.pullback (Limits.pullback.fst f g))
        (baseChanged_residue_fiber_vanishing (IsPullback.of_hasPullback f g) L hL hV)).symm
        (fiberBaseChange f g L hL D) := by
  apply (atlasRelativeFiberEquiv (Limits.pullback.snd f g) _
    (hL.pullback (Limits.pullback.fst f g)) _).injective
  rw [atlasRelativeFiberEquiv_pullback, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

end FLT.Mazur.CartierAbel
