/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperLineFiberVanishing
public import FLT.Mazur.ModuleOpenCohomologyRestriction

/-!
# Residue acyclicity after changing the original base

Paste two actual cartesian squares and use the original family's universal
vanishing theorem. The pullback-composition isomorphism then transfers
vanishing to the iterated sheaf. No Noetherian hypothesis is imposed on the
intermediate or final base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.LineSectionBaseChange
open FCurve
variable {X S P T Q U : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  {f : X ⟶ S} [IsProper f] [Flat f]
  {p : P ⟶ X} {q : P ⟶ T} {g : T ⟶ S}
  (h : IsPullback p q f g) (L : X.Modules) (hL : LocallyFreeRankOne L)
  (hV : ∀ (z : PrimeSpectrum Γ(S, ⊤)) n,
    Subsingleton (ModuleH (residueAlgebraFiberLine f L z) (n + 1)))

include h hL hV in
/-- Iterated pullback is acyclic whenever the final test base is affine. -/
theorem iterated_baseChange_vanishing [IsAffine U]
    {r : Q ⟶ P} {t : Q ⟶ U} {k : U ⟶ T}
    (h' : IsPullback r t q k) (n : ℕ) :
    Subsingleton (ModuleH ((pullback r).obj ((pullback p).obj L)) (n + 1)) := by
  let _ := baseChange_vanishing_of_residue_fibers f L hL hV (h'.paste_horiz h) n
  exact (moduleHIsoOfIso ((pullbackComp r p).app L) (n + 1)).injective.subsingleton

include h hL hV in
/-- Every residue fiber over the new affine base inherits the original vanishing. -/
theorem baseChanged_residue_fiber_vanishing [IsAffine T]
    (z : PrimeSpectrum Γ(T, ⊤)) (n : ℕ) :
    Subsingleton (ModuleH (residueAlgebraFiberLine q ((pullback p).obj L) z) (n + 1)) :=
  iterated_baseChange_vanishing h L hL hV
    (IsPullback.of_hasPullback q (AffineBaseChangeCoefficients.baseMap T z.asIdeal.ResidueField)) n

end FLT.Mazur.LineSectionBaseChange
