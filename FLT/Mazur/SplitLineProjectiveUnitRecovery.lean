/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SplitLineProjectivePullback

/-!
# Recovering original affine points from the principal-cover construction

When a generator already has a unit coordinate, the glued reverse morphism
is its original affine point. In particular the normalized generator of an
actual section line recovers the point of that same section submodule.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.SplitLinePrincipalPoints
open ProjectiveSpace NormalizedSectionLine
variable {X : Scheme.{u}} [IsAffine X] {ι : Type u} [Finite ι]

/-- A globally invertible coordinate recovers the original affine generator point. -/
lemma morphism_eq_affineGeneratorPoint (v : ι → Γ(X, ⊤))
    (r : (ι → Γ(X, ⊤)) →ₗ[Γ(X, ⊤)] Γ(X, ⊤)) (hr : r v = 1)
    (j : ι) (a : Γ(X, ⊤)ˣ) (hj : v j = a) :
    morphism v r hr = affineGeneratorPoint (.id _) v j a hj := by
  apply (openCover v r hr).hom_ext
  intro i
  change ι at i
  change (X.basicOpen (v i)).ι ≫ morphism v r hr =
    (X.basicOpen (v i)).ι ≫ affineGeneratorPoint (.id _) v j a hj
  rw [ι_morphism, affineGeneratorPoint_pullback]
  exact affineGeneratorPoint_eq _ _ i j _ _ _ _

/-- The point of a normalized section generator is the point of its original line. -/
lemma morphism_generator_eq_sectionPoint (i : ι) (L : Chart Γ(X, ⊤) ι i)
    (r : (ι → Γ(X, ⊤)) →ₗ[Γ(X, ⊤)] Γ(X, ⊤))
    (hr : r (generator Γ(X, ⊤) ι i L) = 1) :
    morphism (generator Γ(X, ⊤) ι i L) r hr = affineSectionLinePoint (.id _) i L := by
  rw [morphism_eq_affineGeneratorPoint _ r hr i 1 (generator_coordinate _ _ i L)]
  apply (affineSectionLinePoint_eq_iff _ i i _ _).mpr
  exact congrArg Subtype.val (ofTuple_generator Γ(X, ⊤) ι i L)

end FLT.Mazur.SplitLinePrincipalPoints
