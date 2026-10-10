/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineBaseSourceRecovery
public import FLT.Mazur.SchemeFppfLineBaseRecoveryNaturality
public import FLT.Mazur.SchemeFppfLineSourceRecovery

/-!
# The triangle for fppf line-bundle descent

The actual base and source recovery isomorphisms satisfy the triangle required
by the canonical pullback and the constructed gluing functor.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent
open FCurve SchemeGeometricDescent SchemePicard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} (p : Y ⟶ X)
variable [Flat p] [Surjective p] [LocallyOfFinitePresentation p]
/-- The actual global recovery after base recovery is the identity on the pullback. -/
@[reassoc]
lemma fppfLineBaseRecoveryIso_triangle (A : X.Modules) (hA : LocallyFreeRankOne A) :
    (pullback p).map (fppfLineBaseRecoveryIso p A hA).hom ≫
        (fppfSourceLineGlobalRecoveryIso p (canonical p A) (hA.pullback p)).hom =
      𝟙 ((pullback p).obj A) := by
  let _ := fppfBaseLineCharts_quasicoherent p A hA
  let _ := fppfSourceCharts_quasicoherent p (hA.pullback p)
  exact baseRecoveryIso_sourceGlued (fppfSourceCharts p) (canonical p A) A (Iso.refl _)
    (canonical_overlap_chart p A) (fppfSourceCharts_baseCover_range p)
    (fun y ↦ ⟨y, fppfSourceCharts_mem p y⟩)

/-- The chosen natural base and source recoveries satisfy the categorical triangle. -/
@[reassoc]
lemma lineBaseRecovery_triangle (L : LineBundleCat X) :
    (lineCanonical p).map ((lineBaseRecovery p).hom.app L) ≫
        (lineSourceRecovery p).hom.app ((lineCanonical p).obj L) =
      𝟙 ((lineCanonical p).obj L) := by
  apply LineData.hom_ext
  exact fppfLineBaseRecoveryIso_triangle p L.1 L.2

end FLT.Mazur.SchemeAffineDescent
