/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineLineCoefficients
public import FLT.Mazur.ModuleLineBundleOpenCover
public import FLT.Mazur.SchemeAffineOpenGluingRecovery

/-!
# Local rank one of the glued descent sheaf

The original line bundle has invertible affine coefficients. Faithfully flat
descent makes every affine base chart a line bundle, and the proved chart
recovery isomorphisms detect local rank one of the actual glued object.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent
open FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} {p : Y ⟶ X} {M : Y.Modules}
variable (D : SchemeGeometricDescent.Data p M)

/-- Effective descent on an affine chart preserves an original line bundle. -/
theorem Chart.sheaf_locallyFreeRankOne (C : Chart p)
    [((pullback C.cover).obj M).IsQuasicoherent] (hM : LocallyFreeRankOne M) :
    LocallyFreeRankOne (C.sheaf D) :=
  AffineGeometricDescent.descendedSheaf_line C.ringMap ((pullback C.cover).obj M)
    (D.affineChart C.ringMap p C.base C.cover C.square) C.faithfullyFlat
    (hM.pullback C.cover)

variable {ι : Type u} (C : ι → Chart p)
variable [∀ i, ((pullback (C i).cover).obj M).IsQuasicoherent]
variable [∀ i, IsOpenImmersion (C i).base]
attribute [local irreducible] Chart.sheaf openGlued

/-- Gluing the effectively descended charts constructs a line bundle on the base. -/
theorem openGlued_locallyFreeRankOne
    (hC : iSup (fun i ↦ (C i).base.opensRange) = ⊤) (hM : LocallyFreeRankOne M) :
    LocallyFreeRankOne (openGlued C D) := by
  apply LocallyFreeRankOne.of_openPullbackCover
    (fun i ↦ Spec (C i).baseRing) (fun i ↦ (C i).base)
  · intro x
    have hx : x ∈ iSup (fun i ↦ (C i).base.opensRange) := by rw [hC]; trivial
    exact TopologicalSpace.Opens.mem_iSup.mp hx
  · intro i
    exact ((C i).sheaf_locallyFreeRankOne D hM).of_iso (openGluedChartIso C D i).symm

end FLT.Mazur.SchemeAffineDescent
