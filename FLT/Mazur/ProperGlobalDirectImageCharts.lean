/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocallyFiniteFreeOpenCover
public import FLT.Mazur.DirectImageOpenBaseChange
public import FLT.Mazur.ProperLinePushforwardLocalFree

/-!
# Finite free charts of the original global proper direct image

Residue acyclicity on a Noetherian affine cover constructs finite free
charts for the single global direct-image sheaf. The open base-change
comparison identifies the locally computed sheaves with its actual pullbacks.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.LineSectionBaseChange
open FCurve DirectImageBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X S : Scheme.{0}} {ι : Type*} (f : X ⟶ S) [IsProper f] [Flat f]
  (L : X.Modules) (hL : LocallyFreeRankOne L)
  (U : ι → S.Opens) [∀ i, IsAffine (U i).toScheme]
  [∀ i, IsNoetherianRing Γ((U i).toScheme, ⊤)]
  (hV : ∀ i (z : PrimeSpectrum Γ((U i).toScheme, ⊤)) n,
    Subsingleton (ModuleH (residueAlgebraFiberLine
      (f ∣_ U i) ((pullback (f ⁻¹ᵁ U i).ι).obj L) z) (n + 1)))

include hL hV in
/-- Chartwise residue acyclicity makes the original global direct image locally finite free. -/
theorem globalLinePushforward_locallyFiniteFree (hU : iSup U = ⊤) :
    LocallyFiniteFree ((pushforward f).obj L) := by
  apply locallyFiniteFree_of_openCover _ U hU
  intro i
  exact (properLinePushforward_locallyFiniteFree (f ∣_ U i)
    ((pullback (f ⁻¹ᵁ U i).ι).obj L) (hL.pullback (f ⁻¹ᵁ U i).ι) (hV i)).of_iso
      (openIso f (U i) L).symm

end FLT.Mazur.LineSectionBaseChange
