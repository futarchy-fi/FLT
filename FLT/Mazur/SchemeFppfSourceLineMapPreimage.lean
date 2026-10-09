/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFppfSourceLineGlobalOverlap
public import FLT.Mazur.SchemeCanonicalMapRecognition

/-!
# Recovering compatible source maps from maps of glued line bundles

Conjugate the pullback of a base map by the constructed global recoveries.
Their proved original-overlap equations make the resulting source map compatible.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent
open FCurve SchemePullbackOverlap
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme.{u}} (p : Y ⟶ X)
variable [Flat p] [Surjective p] [LocallyOfFinitePresentation p]
variable {M N : Y.Modules}
variable (D : SchemeGeometricDescent.Data p M) (E : SchemeGeometricDescent.Data p N)
variable (hM : LocallyFreeRankOne M) (hN : LocallyFreeRankOne N)

/-- Recover a source map from any map between the actual glued line bundles. -/
def fppfSourceLineMapPreimage (g : fppfSourceLineGlued p D hM ⟶ fppfSourceLineGlued p E hN) :
    M ⟶ N :=
  (fppfSourceLineGlobalRecoveryIso p D hM).inv ≫ (pullback p).map g ≫
    (fppfSourceLineGlobalRecoveryIso p E hN).hom

/-- The recovered map satisfies its global reconstruction square. -/
@[reassoc]
lemma fppfSourceLineMapPreimage_recovery
    (g : fppfSourceLineGlued p D hM ⟶ fppfSourceLineGlued p E hN) :
    (fppfSourceLineGlobalRecoveryIso p D hM).hom ≫
        fppfSourceLineMapPreimage p D E hM hN g =
      (pullback p).map g ≫ (fppfSourceLineGlobalRecoveryIso p E hN).hom := by
  simp only [fppfSourceLineMapPreimage, Iso.hom_inv_id_assoc]

/-- Original-overlap recovery makes every recovered source map compatible. -/
lemma fppfSourceLineMapPreimage_compatible
    (g : fppfSourceLineGlued p D hM ⟶ fppfSourceLineGlued p E hN) :
    D.MapCompatible p E (fppfSourceLineMapPreimage p D E hM hN g) := by
  exact compatible_of_chartOverlap_eq p _ _ _ rfl Limits.pullback.condition.symm
    (fppfSourceLineGlobalRecoveryIso p D hM) (fppfSourceLineGlobalRecoveryIso p E hN)
    D.overlap E.overlap (fppfSourceLineGlobalRecoveryIso_overlap p D hM)
    (fppfSourceLineGlobalRecoveryIso_overlap p E hN) g _
    (fppfSourceLineMapPreimage_recovery p D E hM hN g).symm

/-- Recovering a glued compatible map returns the original source map. -/
lemma fppfSourceLineMapPreimage_map (f : M ⟶ N) (hf : D.MapCompatible p E f) :
    fppfSourceLineMapPreimage p D E hM hN (fppfSourceLineMap p D E hM hN f hf) = f := by
  unfold fppfSourceLineMapPreimage
  rw [fppfSourceLineGlobalRecoveryIso_naturality]
  simp only [Iso.inv_hom_id_assoc]

end FLT.Mazur.SchemeAffineDescent
