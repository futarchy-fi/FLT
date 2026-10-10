/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperUniversalCartierDivisor
public import FLT.Mazur.CartierTensorRank

/-!
# The varying universal-divisor line with a fixed twist

The full universal Cartier ideal on the actual projective parameter family
defines its positive divisor bundle. Tensoring with a pulled original line
gives the varying line used for cohomology-locus charts.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.ProperUniversalDirectImage
open FCurve LineSectionBaseChange LocallyFreeDualProjectiveAtlas
attribute [local irreducible] ModuleSheafTensor.tensor
attribute [local irreducible] LocallyFreeDualProjectiveAtlas.space
  LocallyFreeDualProjectiveAtlas.projection
variable {X S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (f : X ⟶ S) [IsProper f] [Flat f] [GeometricallyIntegral f]
  (L : X.Modules) (hL : LocallyFreeRankOne L)
  (hV : ∀ (z : PrimeSpectrum Γ(S, ⊤)) n,
    Subsingleton (ModuleH (residueAlgebraFiberLine f L z) (n + 1)))

local notation "M" => Functor.obj (pushforward f) L
local notation "hM" => properLinePushforward_locallyFiniteFree f L hL hV
local notation "π" => projection M hM
local notation "p" => Limits.pullback.fst f π
local notation "q" => Limits.pullback.snd f π

/-- The actual universal divisor bundle, twisted by the pullback of an original line. -/
@[irreducible] def divisorTwistedLine (K : X.Modules) : (Limits.pullback f π).Modules :=
  ModuleSheafTensor.tensor
    (divisorLineBundle (universalIdeal f L hL hV) (universalIdeal_relativeCartier f L hL hV).1)
    ((pullback p).obj K)

/-- Local rank one follows from the constructed full universal Cartier ideal. -/
theorem divisorTwistedLine_rankOne (K : X.Modules) (hK : LocallyFreeRankOne K) :
    LocallyFreeRankOne (divisorTwistedLine f L hL hV K) := by
  unfold divisorTwistedLine
  exact (universalIdeal_relativeCartier f L hL hV).1.divisorLineBundle_locallyFreeRankOne.tensor
    (hK.pullback p)

/-- The varying line on an actual affine open of the original parameter atlas. -/
@[irreducible] def divisorTwistedChartLine (K : X.Modules)
    (U : (space M hM).affineOpens) : (q ⁻¹ᵁ U.1).toScheme.Modules :=
  (pullback (q ⁻¹ᵁ U.1).ι).obj (divisorTwistedLine f L hL hV K)

/-- Every parameter chart retains an actual line bundle on its actual total family. -/
theorem divisorTwistedChartLine_rankOne (K : X.Modules) (hK : LocallyFreeRankOne K)
    (U : (space M hM).affineOpens) :
    LocallyFreeRankOne (divisorTwistedChartLine f L hL hV K U) := by
  unfold divisorTwistedChartLine
  exact (divisorTwistedLine_rankOne f L hL hV K hK).pullback _

end FLT.Mazur.ProperUniversalDirectImage
