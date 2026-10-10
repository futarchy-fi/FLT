/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineBaseRecoveryNaturality
public import FLT.Mazur.SchemeFppfLineBaseRecovery
public import FLT.Mazur.SchemeFppfLineGluingFunctor
public import FLT.Mazur.SchemeLineCanonicalFunctor

/-!
# Natural base-object recovery for fppf line descent

The constructed base recovery is natural in actual line-bundle morphisms.
Its components define the unit isomorphism for canonical descent and gluing.
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
variable {A B : X.Modules} (hA : LocallyFreeRankOne A) (hB : LocallyFreeRankOne B)

/-- The fppf base recovery commutes with the pullback and gluing of any base map. -/
@[reassoc]
lemma fppfLineBaseRecoveryIso_naturality (f : A ⟶ B) :
    f ≫ (fppfLineBaseRecoveryIso p B hB).hom =
      (fppfLineBaseRecoveryIso p A hA).hom ≫
        fppfSourceLineMap p (canonical p A) (canonical p B)
          (hA.pullback p) (hB.pullback p) ((pullback p).map f)
          (canonical_mapCompatible p f) := by
  let _ := fppfBaseLineCharts_quasicoherent p A hA
  let _ := fppfBaseLineCharts_quasicoherent p B hB
  let _ := fppfSourceCharts_quasicoherent p (hA.pullback p)
  let _ := fppfSourceCharts_quasicoherent p (hB.pullback p)
  exact baseRecoveryIso_naturality (fun y ↦ (fppfSourceCharts p y).chart)
    (canonical p A) A (Iso.refl _) (canonical_overlap_chart p A)
    (fppfSourceCharts_baseCover_range p) (canonical p B) B (Iso.refl _)
    (canonical_overlap_chart p B) (fppfSourceCharts_baseCovers p)
    f ((pullback p).map f) (canonical_mapCompatible p f) (by simp)

/-- Canonical descent followed by actual gluing recovers base line bundles naturally. -/
def lineBaseRecovery : 𝟭 (LineBundleCat X) ≅ lineCanonical p ⋙ lineGluing p :=
  NatIso.ofComponents (lineBaseRecoveryIso p) (fun {A B} f ↦ by
    apply InducedCategory.hom_ext
    exact fppfLineBaseRecoveryIso_naturality p A.2 B.2 f.hom)

end FLT.Mazur.SchemeAffineDescent
