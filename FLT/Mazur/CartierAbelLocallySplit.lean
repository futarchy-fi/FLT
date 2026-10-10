/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierAbelResidueNonvanishing
public import FLT.Mazur.ProperLinePushforwardLocalFree
public import FLT.Mazur.ResidueNonvanishingLocallySplit

/-!
# Relative Cartier sections give actual locally split direct-image lines

Surjectivity supplies residue nonvanishing. Actual vector-bundle charts of
the direct image then construct local retractions of the original map from
the dual twisting line. Proper flat residue-acyclic families supply those charts.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.CartierAbel
open FCurve SplitLineAffineNeighborhood LineSectionBaseChange
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X S : Scheme.{0}} (f : X ⟶ S) [Surjective f]
  (L : X.Modules) (hL : LocallyFreeRankOne L)

/-- The original relative Cartier map is locally split in the actual vector-bundle direct image. -/
theorem relativeSection_directImage_locallySplit
    (hN : LocallyFiniteFree ((pushforward f).obj L)) (s : RelativeSection f L hL) :
    LocallySplit (s.val.toDirectImage f L).map :=
  ResidueNonvanishingLocallySplit.locallySplit _ s.val.baseLine.property.dual hN
    (relativeSection_residue_directImage_ne_zero f L hL s)

variable [IsAffine S] [IsNoetherianRing Γ(S, ⊤)] [IsProper f] [Flat f]

/-- Residue acyclicity constructs the ambient charts and hence the original Cartier splitting. -/
theorem relativeSection_proper_directImage_locallySplit
    (hV : ∀ (z : PrimeSpectrum Γ(S, ⊤)) n,
      Subsingleton (ModuleH (residueAlgebraFiberLine f L z) (n + 1)))
    (s : RelativeSection f L hL) : LocallySplit (s.val.toDirectImage f L).map :=
  relativeSection_directImage_locallySplit f L hL
    (properLinePushforward_locallyFiniteFree f L hL hV) s

end FLT.Mazur.CartierAbel
