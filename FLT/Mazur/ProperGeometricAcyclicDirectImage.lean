/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperLineAcyclicOpenRepresentation
public import FLT.Mazur.ProperGlobalDirectImageCharts

/-!
# Actual locally finite free direct images on the global acyclic locus

Intrinsic residue-fiber acyclicity supplies the affine chart hypotheses for
the original global direct image. Applying this to the constructed acyclic
open gives a locally finite free sheaf without a global vanishing assumption.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.LineSectionBaseChange
open FCurve

variable {X S : Scheme.{0}} (f : X ⟶ S) [IsProper f]
  (L : X.Modules) (hL : LocallyFreeRankOne L)
  (hV : ∀ s : S, ∀ n, Subsingleton (ModuleH ((pullback (f.fiberι s)).obj L) (n + 1)))

include hL hV in
/-- Intrinsic acyclicity gives all the affine residue-algebra hypotheses, with no choices. -/
theorem residueAlgebra_vanishing_of_geometric [IsAffine S]
    (z : PrimeSpectrum Γ(S, ⊤)) (n : ℕ) :
    Subsingleton (ModuleH (residueAlgebraFiberLine f L z) (n + 1)) := by
  have hs : S.isoSpec.hom (S.isoSpec.inv z) = z := by
    rw [← Scheme.Hom.comp_apply, S.isoSpec.inv_hom_id]
    rfl
  have hv := (residueAlgebraFiber_vanishing_iff f L hL (S.isoSpec.inv z) (n + 1)).mpr
    (hV (S.isoSpec.inv z) n)
  rwa [hs] at hv

include hL hV in
/-- Geometric acyclicity constructs local frames for the original global direct image. -/
theorem geometricAcyclic_pushforward_locallyFiniteFree [IsLocallyNoetherian S] [Flat f] :
    LocallyFiniteFree ((pushforward f).obj L) := by
  let _ (U : S.affineOpens) : IsAffine U.1.toScheme := U.2
  let _ (U : S.affineOpens) : IsNoetherianRing Γ(U.1.toScheme, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top U.1.toScheme⟩
  apply globalLinePushforward_locallyFiniteFree f L hL
    (fun U : S.affineOpens ↦ U.1) ?_ (iSup_affineOpens_eq_top S)
  intro U z n
  apply residueAlgebra_vanishing_of_geometric (f ∣_ U.1)
    ((pullback (f ⁻¹ᵁ U.1).ι).obj L) (hL.pullback _) ?_ z n
  intro t m
  exact (properLine_fiber_vanishing_iff (isPullback_morphismRestrict f U.1).flip
    L hL t (m + 1)).mpr (hV (U.1.ι t) m)

/-- The actual restricted family's direct image is locally finite free on the assembled open. -/
theorem globalAcyclicOpen_pushforward_locallyFiniteFree [IsLocallyNoetherian S] [Flat f] :
    LocallyFiniteFree
      ((pushforward (f ∣_ properLineGlobalAcyclicOpen f L hL)).obj
        ((pullback (f ⁻¹ᵁ properLineGlobalAcyclicOpen f L hL).ι).obj L)) :=
  geometricAcyclic_pushforward_locallyFiniteFree _ _ (hL.pullback _)
    (properLineGlobalAcyclicOpen_fibers f L hL)

end FLT.Mazur.LineSectionBaseChange
