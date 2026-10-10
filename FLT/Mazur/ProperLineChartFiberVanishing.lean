/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperLineIteratedFiberVanishing

/-!
# Residue acyclicity on charts of an arbitrary changed base

After an unrestricted base change, each affine chart inherits residue
acyclicity from the original family. Pullback composition transfers the
vanishing to the actual twice-pulled line used by the global Cartier criterion.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.LineSectionBaseChange
open FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X S P T Q U : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  {f : X ⟶ S} [IsProper f] [Flat f]
  {p : P ⟶ X} {q : P ⟶ T} {g : T ⟶ S}
  (h : IsPullback p q f g) (L : X.Modules) (hL : LocallyFreeRankOne L)
  (hV : ∀ (z : PrimeSpectrum Γ(S, ⊤)) n,
    Subsingleton (ModuleH (residueAlgebraFiberLine f L z) (n + 1)))

include h hL hV in
/-- Affine charts of an arbitrary changed base inherit residue acyclicity. -/
theorem iterated_residue_fiber_vanishing [IsAffine U]
    {r : Q ⟶ P} {t : Q ⟶ U} {k : U ⟶ T} (h' : IsPullback r t q k)
    (z : PrimeSpectrum Γ(U, ⊤)) (n : ℕ) :
    Subsingleton (ModuleH
      (residueAlgebraFiberLine t ((pullback r).obj ((pullback p).obj L)) z) (n + 1)) := by
  let b := AffineBaseChangeCoefficients.baseMap U z.asIdeal.ResidueField
  let _ := iterated_baseChange_vanishing h L hL hV
    ((IsPullback.of_hasPullback t b).paste_horiz h') n
  exact (moduleHIsoOfIso
    ((pullbackComp (Limits.pullback.fst t b) r).app ((pullback p).obj L))
      (n + 1)).injective.subsingleton

include h hL hV in
/-- The exact line sheaf on each affine open of the new base has acyclic residue fibers. -/
theorem open_residue_fiber_vanishing (V : T.Opens) [IsAffine V.toScheme]
    (z : PrimeSpectrum Γ(V.toScheme, ⊤)) (n : ℕ) :
    Subsingleton (ModuleH (residueAlgebraFiberLine (q ∣_ V)
      ((pullback (q ⁻¹ᵁ V).ι).obj ((pullback p).obj L)) z) (n + 1)) :=
  iterated_residue_fiber_vanishing h L hL hV (isPullback_morphismRestrict q V).flip z n

end FLT.Mazur.LineSectionBaseChange
