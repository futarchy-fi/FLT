/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationInvariantSpectrum

/-!
# Invariant spectra under genuine changes of full relations

A source map and a map of entire relations induce a map of invariant spectra.
Both endpoint equations are required and all coefficient maps are retained.
The resulting square is not asserted Cartesian.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationInvariantSpectrum
open SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
variable {E A E' A' : Scheme.{u}} (p q : E ⟶ A) (p' q' : E' ⟶ A')
  (u : A' ⟶ A) (v : E' ⟶ E) (hp : v ≫ p = p' ≫ u) (hq : v ≫ q = q' ≫ u)

/-- Pull back full original invariants through the actual source map. -/
def relationPullback : compatibleFunctions p q →+* compatibleFunctions p' q' :=
  (u.appTop.hom.comp (compatibleFunctions p q).subtype).codRestrict _ (fun s ↦ by
    change (p' ≫ u).appTop s.val = (q' ≫ u).appTop s.val
    rw [← hp, ← hq, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]
    exact congrArg v.appTop s.property)

/-- The coefficient map is literally pullback of the original source function. -/
theorem relationPullback_val (s : compatibleFunctions p q) :
    (relationPullback p q p' q' u v hp hq s).val = u.appTop s.val := rfl

/-- The induced target map compares freshly computed invariant spectra. -/
def relationMap : target p' q' ⟶ target p q :=
  Spec.map (CommRingCat.ofHom (relationPullback p q p' q' u v hp hq))

/-- The square commutes on schemes, including structure sheaf maps. -/
@[reassoc]
theorem projection_relationMap : projection p' q' ≫ relationMap p q p' q' u v hp hq =
    u ≫ projection p q := by
  simp only [projection, relationMap, Category.assoc, ← Spec.map_comp]
  rw [← Category.assoc u, Scheme.toSpecΓ_naturality, Category.assoc, ← Spec.map_comp]
  rfl

/-- Surjectivity on functions is not required: epimorphic source maps detect coefficients. -/
theorem relationPullback_injective [Epi u] :
    Function.Injective (relationPullback p q p' q' u v hp hq) := by
  intro s t h
  apply Subtype.ext
  exact appTop_injective u (congrArg Subtype.val h)

end FLT.Mazur.SchemeRelationInvariantSpectrum
