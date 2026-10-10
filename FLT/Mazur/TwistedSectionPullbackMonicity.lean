/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperSplitSectionFiberRegularity
public import FLT.Mazur.LineSectionPullbackCoordinates

/-!
# Monicity before and after the twisted-section comparison

The independently defined section on a base change is transported through an
actual isomorphism. Its regularity therefore applies to the unmodified sheaf
pullback, which can then be evaluated in a pulled affine frame.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.TwistedSectionPullbackMonicity
open FCurve ModuleSheafTensor SchemePullbackSquare TwistedSectionBaseChangeRegularity
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] tensor ModuleLineBundleTensorPullback.tensorIso
variable {P X T S : Scheme.{0}}
  (p : P ⟶ X) (q : P ⟶ T) (f : X ⟶ S) (g : T ⟶ S)
  (w : q ≫ g = p ≫ f) (L : X.Modules) {B : S.Modules}

/-- The comparison used in the independently defined twisted section. -/
def sectionIso : (pullback p).obj (tensor L ((pullback f).obj B)) ≅
    tensor ((pullback p).obj L) ((pullback q).obj ((pullback g).obj B)) :=
  ModuleLineBundleTensorPullback.tensorIso p L ((pullback f).obj B) ≪≫
    congr (Iso.refl _) ((squareIso f q g p w).app B).symm

/-- The geometric section is the image of the original pullback under this comparison. -/
lemma sectionIso_section (s : Γ(tensor L ((pullback f).obj B), ⊤)) :
    (sectionIso p q f g w L).hom.app ⊤ (pullGlobal p _ s) =
      section_ p q f g w L s := rfl

/-- The independent twisted section detects monicity of the original pulled section. -/
theorem mono_iff (s : Γ(tensor L ((pullback f).obj B), ⊤)) :
    Mono (globalSectionHom _ (section_ p q f g w L s)) ↔
      Mono (globalSectionHom _ (pullGlobal p _ s)) := by
  rw [← sectionIso_section, ← globalSectionHom_naturality]
  exact mono_comp_iff_of_mono _ (sectionIso p q f g w L).hom

/-- Proper locally split sections have monic unmodified pullbacks on integral fibers. -/
theorem proper_integral_pullback [IsAffine S] [IsAffine T]
    [IsNoetherianRing Γ(S, ⊤)] [IsProper f] [Flat f] [IsIntegral P] [Nonempty T]
    (h : IsPullback p q f g) (hL : LocallyFreeRankOne L)
    (hV : ∀ (z : PrimeSpectrum Γ(S, ⊤)) n,
      Subsingleton (ModuleH (LineSectionBaseChange.residueAlgebraFiberLine f L z) (n + 1)))
    (hB : LocallyFreeRankOne B) (s : Γ(tensor L ((pullback f).obj B), ⊤))
    (hs : SplitLineAffineNeighborhood.LocallySplit
      (twistedSectionPushforwardEquiv f L hB s)) :
    Mono (globalSectionHom _ (pullGlobal p _ s)) :=
  (mono_iff p q f g h.w.symm L s).mp
    (ProperSplitSectionFiberRegularity.regular_on_integral_baseChange f L hL hV hB s hs h)

end FLT.Mazur.TwistedSectionPullbackMonicity
