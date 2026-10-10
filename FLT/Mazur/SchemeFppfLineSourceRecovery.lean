/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFppfLineGluingFunctor
public import FLT.Mazur.SchemeLineCanonicalFunctor
public import FLT.Mazur.SchemeCanonicalRecoveryCompatibility

/-!
# The source-object round trip for categorical fppf line descent

The actual glued object pulls back to the original descent datum, respecting
its original overlap. This recovery is natural for every compatible source map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent
open SchemePicard SchemeGeometricDescent
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} (p : Y ⟶ X)
variable [Flat p] [Surjective p] [LocallyOfFinitePresentation p]

/-- Global recovery is an isomorphism of the original geometric descent objects. -/
def lineSourceRecoveryIso (D : LineData p) :
    (lineCanonical p).obj ((lineGluing p).obj D) ≅ D :=
  LineData.isoMk p (fppfSourceLineGlobalRecoveryIso p D.datum D.rankOne)
    (canonical_recovery_compatible p D.datum _
      (fppfSourceLineGlobalRecoveryIso p D.datum D.rankOne)
      (fppfSourceLineGlobalRecoveryIso_overlap p D.datum D.rankOne))

/-- Pullback after gluing recovers the original descent datum naturally. -/
def lineSourceRecovery : lineGluing p ⋙ lineCanonical p ≅ 𝟭 (LineData p) :=
  NatIso.ofComponents (lineSourceRecoveryIso p) (fun {D E} f ↦ by
    apply LineData.hom_ext
    exact fppfSourceLineGlobalRecoveryIso_naturality p D.datum D.rankOne
      E.datum E.rankOne f.val f.property)

end FLT.Mazur.SchemeAffineDescent
