/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveUniversalLineComparison

/-!
# Actual universal line pullbacks on homogeneous triple intersections

The three direct chart pullbacks have inclusion-preserving comparisons on
one actual triple homogeneous localization. The proved ring-map identities
identify all intermediate routes, and these comparisons satisfy the cocycle.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.ProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
open NormalizedSectionLine
variable (R : Type u) [CommRing R] (ι : Type u)

/-- The fixed first chart map to the actual triple homogeneous localization. -/
abbrev universalTripleMap₁ (i j k : ι) : chartRing R ι i →+* tripleRing R ι i j k :=
  (toTriple₁₂ R ι i j k).comp (chartOverlapLeft R ι i j).toRingHom

/-- The fixed middle chart map to the same triple localization. -/
abbrev universalTripleMap₂ (i j k : ι) : chartRing R ι j →+* tripleRing R ι i j k :=
  (toTriple₁₂ R ι i j k).comp (chartOverlapRight R ι i j).toRingHom

/-- The fixed last chart map to the same triple localization. -/
abbrev universalTripleMap₃ (i j k : ι) : chartRing R ι k →+* tripleRing R ι i j k :=
  (toTriple₂₃ R ι i j k).comp (chartOverlapRight R ι j k).toRingHom

/-- Compare the actual first and middle chart pullbacks on the triple localization. -/
def universalTripleCompare₁₂ (i j k : ι) :=
  universalLineCompare R ι i j (universalTripleMap₁ R ι i j k)
    (universalTripleMap₂ R ι i j k) (universalTripleLine_val₁₂ R ι i j k)

/-- Compare the actual middle and last pullbacks, using the middle ring-path identity. -/
def universalTripleCompare₂₃ (i j k : ι) :=
  universalLineCompare R ι j k (universalTripleMap₂ R ι i j k)
    (universalTripleMap₃ R ι i j k) (universalTripleLine_val₂₃ R ι i j k)

/-- Compare the actual outer chart pullbacks, using both outer ring-path identities. -/
def universalTripleCompare₁₃ (i j k : ι) :=
  universalLineCompare R ι i k (universalTripleMap₁ R ι i j k)
    (universalTripleMap₃ R ι i j k) (universalTripleLine_val₁₃ R ι i j k)

attribute [local irreducible] universalLineCompare Scheme.Modules.pullback

/-- The comparisons between actual direct chart pullbacks satisfy the triple cocycle. -/
lemma universalTripleCompare_cocycle [Finite ι] (i j k : ι) :
    universalTripleCompare₁₂ R ι i j k ≪≫ universalTripleCompare₂₃ R ι i j k =
      universalTripleCompare₁₃ R ι i j k :=
  universalLineCompare_cocycle R ι i j k _ _ _ _ _

/-- The first comparison preserves the ambient inclusion on the actual triple intersection. -/
lemma universalTripleCompare₁₂_inclusion [Finite ι] (i j k : ι) :
    (universalTripleCompare₁₂ R ι i j k).hom ≫
        universalLinePullbackInclusion R ι j (universalTripleMap₂ R ι i j k) =
      universalLinePullbackInclusion R ι i (universalTripleMap₁ R ι i j k) :=
  universalLineCompare_inclusion R ι i j _ _ _

/-- The second comparison preserves that same ambient inclusion. -/
lemma universalTripleCompare₂₃_inclusion [Finite ι] (i j k : ι) :
    (universalTripleCompare₂₃ R ι i j k).hom ≫
        universalLinePullbackInclusion R ι k (universalTripleMap₃ R ι i j k) =
      universalLinePullbackInclusion R ι j (universalTripleMap₂ R ι i j k) :=
  universalLineCompare_inclusion R ι j k _ _ _

/-- The direct outer comparison preserves the same ambient inclusion as the composite route. -/
lemma universalTripleCompare₁₃_inclusion [Finite ι] (i j k : ι) :
    (universalTripleCompare₁₃ R ι i j k).hom ≫
        universalLinePullbackInclusion R ι k (universalTripleMap₃ R ι i j k) =
      universalLinePullbackInclusion R ι i (universalTripleMap₁ R ι i j k) :=
  universalLineCompare_inclusion R ι i k _ _ _

end FLT.Mazur.ProjectiveSpace
