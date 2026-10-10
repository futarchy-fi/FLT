/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperSectionAffineCoverCartier
public import FLT.Mazur.TwistedSectionLocalSplitting

/-!
# The global direct-image Cartier criterion on a Noetherian affine cover

The original global direct-image map is locally split exactly when the
original tensor section is regular and its full zero divisor is flat.
The base need not be affine; the cohomological data are checked on its cover.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.ProperGlobalSectionCartier
open FCurve ModuleSheafTensor SplitLineAffineNeighborhood TwistedSectionBaseChangeRegularity
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] tensor twistedSectionPushforwardEquiv
  TwistedSectionBaseChangeRegularity.section_
variable {X S : Scheme.{0}} {ι : Type*} (f : X ⟶ S)
  [IsProper f] [Flat f] [GeometricallyIntegral f]
  (L : X.Modules) (hL : LocallyFreeRankOne L)
  {B : S.Modules} (hB : LocallyFreeRankOne B)
  (s : Γ(tensor L ((pullback f).obj B), ⊤))
  (U : ι → S.Opens) [∀ i, IsAffine (U i).toScheme]
  [∀ i, IsNoetherianRing Γ((U i).toScheme, ⊤)]
  (hV : ∀ i (z : PrimeSpectrum Γ((U i).toScheme, ⊤)) n,
    Subsingleton (ModuleH (LineSectionBaseChange.residueAlgebraFiberLine
      (f ∣_ U i) ((pullback (f ⁻¹ᵁ U i).ι).obj L) z) (n + 1)))

include hV in
/-- The single original global map detects the full relative Cartier section. -/
lemma locallySplit_iff (hU : iSup U = ⊤) :
    LocallySplit (twistedSectionPushforwardEquiv f L hB s) ↔
      Mono (globalSectionHom _ s) ∧
        RelativeEffectiveCartier f (lineSectionZeroIdeal (hL.tensor (hB.pullback f)) s) := by
  rw [locallySplit_openCover_iff _ U hU]
  refine Iff.trans ?_ (ProperSectionAffineCoverCartier.locallySplit_iff
    f L hL hB s U hV hU)
  exact forall_congr' (fun i ↦ (section_open_locallySplit_iff f L hB (U i) s).symm)

end FLT.Mazur.ProperGlobalSectionCartier
