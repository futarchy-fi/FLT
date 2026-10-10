/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmpleAffineBase
public import FLT.Mazur.ClosedPointQuotientFiber

/-!
# Ampleness on the maximal-ideal closed source

The fiber comparison transports the actual restricted line sheaf and its
ampleness. No ampleness on the total space is assumed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.FCurve

/-- Pullback along a scheme isomorphism preserves and reflects section ampleness. -/
theorem ampleLineBundle_pullback_iso_iff {X Y : Scheme.{u}} (j : Y ⟶ X) [IsIso j]
    (L : X.Modules) : AmpleLineBundle ((pullback j).obj L) ↔ AmpleLineBundle L := by
  constructor
  · intro h
    exact (ampleLineBundle_restrict_iso_iff j).mp
      (h.of_iso ((restrictFunctorIsoPullback j).app L))
  · intro h
    exact h.pullback_affine j

end FLT.Mazur.FCurve

namespace FLT.Mazur.BaseAdicThickening

open FLT.Mazur.FCurve

variable {R : CommRingCat.{u}} (p : Spec R) [p.asIdeal.IsMaximal]
  {X : Scheme.{u}} (f : X ⟶ Spec R) (L : X.Modules)

/-- The closed-source line is the actual fiber line transported by the comparison. -/
def closedSourceFiberLineIso :
    (pullback ((baseIdeal R p.asIdeal).comap f).subschemeι).obj L ≅
      (pullback (closedSourceFiberIso R p f).hom).obj ((pullback (f.fiberι p)).obj L) :=
  ((pullbackCongr (closedSourceFiberIso_hom_ι R p f)).app L).symm ≪≫
    ((pullbackComp (closedSourceFiberIso R p f).hom (f.fiberι p)).app L).symm

/-- Ampleness on the closed fiber is exactly ampleness on the maximal-ideal closed source. -/
theorem closedSource_ample_iff_fiber :
    AmpleLineBundle ((pullback ((baseIdeal R p.asIdeal).comap f).subschemeι).obj L) ↔
      AmpleLineBundle ((pullback (f.fiberι p)).obj L) := by
  constructor
  · intro h
    exact (ampleLineBundle_pullback_iso_iff _ _).mp
      (h.of_iso (closedSourceFiberLineIso p f L).symm)
  · intro h
    exact (h.pullback_affine (closedSourceFiberIso R p f).hom).of_iso
      (closedSourceFiberLineIso p f L)

end FLT.Mazur.BaseAdicThickening
