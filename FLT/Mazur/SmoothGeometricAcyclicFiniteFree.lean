/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperLineAcyclicFiniteFree
public import FLT.Mazur.SmoothAffineLineNoetherianModel

/-!
# Finite free actual direct images on unrestricted smooth families

Noetherian approximation of each affine restriction carries the original line
and its acyclic fibers. Model-chart descent then constructs local finite frames
for the single original direct image on any base scheme.
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
/-- Acyclic line fibers give actual finite free direct images over any affine smooth base. -/
theorem smoothAffine_geometricAcyclic_locallyFiniteFree [IsAffine S] :
    LocallyFiniteFree ((pushforward f).obj L) := by
  obtain ⟨Y, B, q, a, b, M, hB, hq, hsm, hM, h, ⟨e⟩⟩ :=
    smoothAffineLine_noetherian_model f L hL
  apply (properLineAcyclicBaseChanged_locallyFiniteFree h M hM ?_).of_iso
    ((pushforward f).mapIso e)
  intro s n
  exact (Equiv.subsingleton_congr
    (moduleHIsoOfIso ((pullback (f.fiberι s)).mapIso e) (n + 1)).toEquiv).mpr (hV s n)

include hL hV in
/-- Fiber acyclicity constructs finite free charts on the actual direct image on every base. -/
theorem smooth_geometricAcyclic_locallyFiniteFree :
    LocallyFiniteFree ((pushforward f).obj L) := by
  let _ (U : S.affineOpens) : IsAffine U.1.toScheme := U.2
  apply locallyFiniteFree_of_openCover _ (fun U : S.affineOpens ↦ U.1)
    (iSup_affineOpens_eq_top S)
  intro U
  apply (smoothAffine_geometricAcyclic_locallyFiniteFree (f ∣_ U.1)
    ((pullback (f ⁻¹ᵁ U.1).ι).obj L) (hL.pullback _) ?_).of_iso
      (DirectImageBaseChange.openIso f U.1 L).symm
  intro t n
  exact (properLine_fiber_vanishing_iff (isPullback_morphismRestrict f U.1).flip
    L hL t (n + 1)).mpr (hV (U.1.ι t) n)

end FLT.Mazur.LineSectionBaseChange
