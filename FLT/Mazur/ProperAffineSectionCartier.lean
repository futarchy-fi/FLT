/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineFiberwiseSectionCartier
public import FLT.Mazur.AffineSectionTensorSquare
public import FLT.Mazur.OpenFiberSectionRegularity
public import FLT.Mazur.TwistedSectionPullbackMonicity

/-!
# Proper locally split sections give relative Cartier divisors on affine frames

Proper cohomological base change and geometric integrality supply regularity
on the actual field fiber. Its open tensor chart then supplies the residue
equation criterion, constructing monicity and flatness of the full zero ideal
of the original section on each affine frame.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
namespace FLT.Mazur.ProperAffineSectionCartier
open FCurve ModuleSheafTensor AffineChartResidueEquation
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
/-- Every actual affine frame of the source section carries a relative Cartier zero divisor. -/
theorem chart_relativeCartier {U : Scheme.{0}} [IsAffine U]
    [IsNoetherianRing Γ(U, ⊤)] (j : U ⟶ X) [IsOpenImmersion j]
    (e : (pullback j).obj (tensor L ((pullback f).obj B)) ≅ structureModule U) :
    Mono (globalSectionHom _ (pullGlobal j _ s)) ∧
      RelativeEffectiveCartier (j ≫ f)
        (lineSectionZeroIdeal ((hL.tensor (hB.pullback f)).pullback j) (pullGlobal j _ s)) := by
  apply AffineFiberwiseSectionCartier.relativeCartier (j ≫ f)
    ((hL.tensor (hB.pullback f)).pullback j) e (pullGlobal j _ s)
  dsimp only
  let _ := (j ≫ f).appTop.hom.toAlgebra
  intro p _
  let g := chartMap (X := S) (algebraMap Γ(S, ⊤) p.ResidueField)
  have hr := ProperSplitSectionFiberRegularity.regular_on_field_fiber f L hL hV hB s hs
    p.ResidueField g
  have : Mono (globalSectionHom _ (pullGlobal (Limits.pullback.fst f g) _ s)) :=
    (TwistedSectionPullbackMonicity.mono_iff (Limits.pullback.fst f g)
      (Limits.pullback.snd f g) f g Limits.pullback.condition.symm L s).mp hr
  exact OpenFiberSectionRegularity.chart_mono j f g
    (AffineSectionTensorSquare.isPullback (j ≫ f) p.ResidueField) _ s

end FLT.Mazur.ProperAffineSectionCartier
