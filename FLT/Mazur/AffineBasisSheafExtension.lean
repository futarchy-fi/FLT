/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Ring.Colimits

/-!
# Extending sheaves from the affine basis

The affine opens are a cover-dense full subcategory of the open sets. The
comparison lemma extends sheaves for the induced topology to the whole scheme.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u v w

namespace FLT.Mazur.AffineBasis

variable (X : Scheme.{u})

/-- Inclusion of the actual affine opens in all opens. -/
def inclusion : X.affineOpens ⥤ X.Opens where
  obj U := U.1
  map i := homOfLE i.le

instance : (inclusion X).Full where
  map_surjective i := ⟨homOfLE i.le, rfl⟩

instance : (inclusion X).Faithful where

/-- Every open is covered by actual affine opens. -/
instance : (inclusion X).IsCoverDense (Opens.grothendieckTopology X) where
  is_cover U := by
    intro x hx
    obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset hx
    exact ⟨V, homOfLE hVU, Presieve.in_coverByImage (inclusion X)
      (Y := ⟨V, hV⟩) (homOfLE hVU), hxV⟩

/-- The topology on affine charts induced by ordinary open covers. -/
abbrev topology := (inclusion X).inducedTopology (Opens.grothendieckTopology X)

/-- Sheaves on the affine basis extend uniquely to sheaves on the scheme. -/
def sheafEquivalence (A : Type v) [Category.{w} A]
    [∀ U, Limits.HasLimitsOfShape (StructuredArrow U (inclusion X).op) A] :
    Sheaf (topology X) A ≌ Sheaf (Opens.grothendieckTopology X) A :=
  (inclusion X).sheafInducedTopologyEquivOfIsCoverDense
    (Opens.grothendieckTopology X) A

end FLT.Mazur.AffineBasis
