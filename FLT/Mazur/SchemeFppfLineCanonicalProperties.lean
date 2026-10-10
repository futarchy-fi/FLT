/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFppfLineSourceRecovery
public import Mathlib.CategoryTheory.EssentialImage

/-!
# Faithfulness and essential surjectivity of canonical fppf line descent

Faithful fppf pullback detects base maps. Every geometric line descent datum is
isomorphic to the canonical pullback of its constructed glued line bundle.
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

instance : (lineCanonical p).Faithful where
  map_injective {A B} {f g} h := by
    apply InducedCategory.hom_ext
    exact fppfLine_pullback_map_injective p A.property B.property f.hom g.hom
      (congrArg Subtype.val h)

instance : (lineCanonical p).EssSurj where
  mem_essImage D := ⟨(lineGluing p).obj D, ⟨lineSourceRecoveryIso p D⟩⟩

end FLT.Mazur.SchemeAffineDescent
