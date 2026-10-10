/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperAffineSectionCartier
public import FLT.Mazur.SectionCartierOpenDescent

/-!
# The relative Cartier divisor of a proper locally split section

Affine frames of the original source line cover the total space. Proper
cohomological base change supplies their residue regularity, constructing
local Cartier divisors with flat full quotients. Open descent then gives
monicity of the original section and flatness of its full zero subscheme.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open Scheme.Modules
namespace FLT.Mazur.ProperSplitSectionRelativeCartier
open FCurve ModuleSheafTensor
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] tensor twistedSectionPushforwardEquiv
variable {X S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (f : X ⟶ S) [IsProper f] [Flat f] [GeometricallyIntegral f]
  (L : X.Modules) (hL : LocallyFreeRankOne L)
  (hV : ∀ (z : PrimeSpectrum Γ(S, ⊤)) n,
    Subsingleton (ModuleH (LineSectionBaseChange.residueAlgebraFiberLine f L z) (n + 1)))
  {B : S.Modules} (hB : LocallyFreeRankOne B)
  (s : Γ(tensor L ((pullback f).obj B), ⊤))
  (hs : SplitLineAffineNeighborhood.LocallySplit (twistedSectionPushforwardEquiv f L hB s))

include hV hs in
/-- A locally split proper direct-image line constructs a regular section with flat full zeros. -/
theorem regular_and_relativeCartier :
    Mono (globalSectionHom _ s) ∧
      RelativeEffectiveCartier f (lineSectionZeroIdeal (hL.tensor (hB.pullback f)) s) := by
  classical
  let _ : IsLocallyNoetherian S := isLocallyNoetherian_of_isOpenImmersion S.isoSpec.hom
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let M := tensor L ((pullback f).obj B)
  have hM : LocallyFreeRankOne M := hL.tensor (hB.pullback f)
  choose U hx hU e using hM.exists_affine_trivialization
  have hcover : iSup U = ⊤ := top_unique (fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hx x⟩)
  apply SectionCartierOpenDescent.relativeCartier_of_cover f hM s U hcover
  intro x
  let _ : IsAffine (U x).toScheme := hU x
  let _ : IsNoetherianRing Γ((U x).toScheme, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top (U x).toScheme⟩
  exact ProperAffineSectionCartier.chart_relativeCartier f L hL hV hB s hs (U x).ι
    (((restrictFunctorIsoPullback (U x).ι).app M).symm ≪≫ (e x).some)

end FLT.Mazur.ProperSplitSectionRelativeCartier
