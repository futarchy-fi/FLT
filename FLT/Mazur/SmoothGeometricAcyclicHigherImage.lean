/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperLineAcyclicHigherImage
public import FLT.Mazur.RelativeSerreVanishing
public import FLT.Mazur.SmoothAffineLineNoetherianModel

/-!
# Higher direct image vanishing over unrestricted smooth bases

Approximation and the acyclic model-chart basis kill every positive actual
higher direct image. Open restriction assembles the statement on any base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.LineSectionBaseChange
open FCurve CartierAbel
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X S : Scheme.{0}} (f : X ⟶ S) [IsProper f] [Smooth f]
  (L : X.Modules) (hL : LocallyFreeRankOne L)
  (hV : ∀ s : S, ∀ n, Subsingleton (ModuleH ((pullback (f.fiberι s)).obj L) (n + 1)))

include hL hV in
/-- All positive actual higher direct images vanish over an arbitrary affine smooth base. -/
theorem smoothAffine_geometricAcyclic_higherImage [IsAffine S] :
    ModulePushforwardAcyclic f L := by
  obtain ⟨Y, B, q, a, b, M, hB, hq, hsm, hM, h, ⟨e⟩⟩ :=
    smoothAffineLine_noetherian_model f L hL
  have hv : ModulePushforwardAcyclic f ((pullback a).obj M) :=
    properLineAcyclicBaseChanged_higherImage h M hM (fun s n ↦
      (Equiv.subsingleton_congr
        (moduleHIsoOfIso ((pullback (f.fiberι s)).mapIso e) (n + 1)).toEquiv).mpr (hV s n))
  intro n
  exact (hv n).of_iso (((pushforward f).rightDerived (n + 1)).mapIso e).symm

include hL hV in
/-- Fiber acyclicity kills actual higher direct images on every proper smooth family. -/
theorem smooth_geometricAcyclic_higherImage : ModulePushforwardAcyclic f L := by
  let _ (U : S.affineOpens) : IsAffine U.1.toScheme := U.2
  apply ProjectiveSpace.modulePushforwardAcyclic_of_openCover f L
    (fun U : S.affineOpens ↦ U.1) (iSup_affineOpens_eq_top S)
  intro U
  let e := (restrictFunctorIsoPullback (f ⁻¹ᵁ U.1).ι).app L
  have hv : ModulePushforwardAcyclic (f ∣_ U.1)
      ((pullback (f ⁻¹ᵁ U.1).ι).obj L) :=
    smoothAffine_geometricAcyclic_higherImage _ _ (hL.pullback _) (fun t n ↦
      (properLine_fiber_vanishing_iff (isPullback_morphismRestrict f U.1).flip
        L hL t (n + 1)).mpr (hV (U.1.ι t) n))
  intro n
  exact (hv n).of_iso (((pushforward (f ∣_ U.1)).rightDerived (n + 1)).mapIso e)

end FLT.Mazur.LineSectionBaseChange
