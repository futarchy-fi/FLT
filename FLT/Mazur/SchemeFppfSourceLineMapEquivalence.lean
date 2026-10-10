/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFppfSourceLineMapPreimage
public import FLT.Mazur.SchemeFppfLinePullbackFaithful

/-!
# Fullness of fppf line-bundle gluing

Faithful fppf pullback proves the remaining map round trip. Thus compatible
source morphisms are equivalent to all morphisms of the constructed glued objects.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent
open FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme.{u}} (p : Y ⟶ X)
variable [Flat p] [Surjective p] [LocallyOfFinitePresentation p]
variable {M N : Y.Modules}
variable (D : SchemeGeometricDescent.Data p M) (E : SchemeGeometricDescent.Data p N)
variable (hM : LocallyFreeRankOne M) (hN : LocallyFreeRankOne N)

/-- Gluing the recovered source map returns every map of the glued objects. -/
lemma fppfSourceLineMap_mapPreimage
    (g : fppfSourceLineGlued p D hM ⟶ fppfSourceLineGlued p E hN) :
    fppfSourceLineMap p D E hM hN (fppfSourceLineMapPreimage p D E hM hN g)
        (fppfSourceLineMapPreimage_compatible p D E hM hN g) = g := by
  apply fppfLine_pullback_map_injective p
    (fppfSourceLineGlued_locallyFreeRankOne p D hM)
    (fppfSourceLineGlued_locallyFreeRankOne p E hN)
  apply (cancel_mono (fppfSourceLineGlobalRecoveryIso p E hN).hom).mp
  rw [fppfSourceLineGlobalRecoveryIso_naturality, fppfSourceLineMapPreimage_recovery]

/-- Gluing is a bijection from compatible source maps to maps of reconstructed line bundles. -/
def fppfSourceLineMapEquiv :
    { f : M ⟶ N // D.MapCompatible p E f } ≃
      (fppfSourceLineGlued p D hM ⟶ fppfSourceLineGlued p E hN) where
  toFun f := fppfSourceLineMap p D E hM hN f.val f.property
  invFun g := ⟨fppfSourceLineMapPreimage p D E hM hN g,
    fppfSourceLineMapPreimage_compatible p D E hM hN g⟩
  left_inv f := Subtype.ext (fppfSourceLineMapPreimage_map p D E hM hN f.val f.property)
  right_inv g := fppfSourceLineMap_mapPreimage p D E hM hN g

end FLT.Mazur.SchemeAffineDescent
