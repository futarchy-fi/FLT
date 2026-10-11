/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeometricAcyclicFppfLocus
public import FLT.Mazur.RelativeFppfLocalSubfunctor

/-!
# The intrinsic acyclic Picard locus is an fppf subsheaf

For proper pointed families the actual geometric acyclic classes satisfy
descent on all test schemes. Their image inside the Picard sheaf is already
a sheaf, without enlarging its values by a formal local closure.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CartierAbel
open SchemePicard
variable {X S : Scheme.{0}} (f : X ⟶ S) (e : S ⟶ X) (he : e ≫ f = 𝟙 S)
  [IsLocallyNoetherian S] [IsProper f] [Flat f]
  [GeometricallyConnected f] [GeometricallyReduced f]

include e he in
/-- The geometric subfunctor has effective and unique fppf descent on arbitrary tests. -/
theorem properPointed_geometricAcyclicPicard_isSheaf :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S)
      (geometricAcyclicPicardSubfunctor f).toFunctor := by
  apply relativeFppf_subfunctor_isSheaf
  · exact (Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget CommGrpCat.{1})).mp
      (properPointed_relativePresheaf_isSheaf f e he)
  · intro T 𝒰 c hc
    exact (relativeGeometricAcyclicRankOne_fppf_iff f T 𝒰 c).mpr hc

include e he in
/-- The represented acyclic sections form an actual subsheaf of the fppf Picard sheaf. -/
theorem properPointed_geometricAcyclicFppf_isSheaf :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S)
      (geometricAcyclicFppfSubfunctor f).toFunctor :=
  (Presheaf.isSheaf_of_iso_iff (geometricAcyclicFppfIso f e he)).mp
    (properPointed_geometricAcyclicPicard_isSheaf f e he)

/-- The actual acyclic Picard subsheaf with its original section values and restrictions. -/
def properPointedAcyclicFppfSheaf : Sheaf (Scheme.fppfTopology.over S) (Type 1) :=
  ⟨(geometricAcyclicFppfSubfunctor f).toFunctor,
    properPointed_geometricAcyclicFppf_isSheaf f e he⟩

/-- The subsheaf inclusion is the inclusion of the original actual Picard-sheaf sections. -/
def properPointedAcyclicFppfInclusion :
    properPointedAcyclicFppfSheaf f e he ⟶
      (sheafCompose (Scheme.fppfTopology.over S) (forget CommGrpCat.{1})).obj
        (relativeFppfSheaf f) :=
  ⟨(geometricAcyclicFppfSubfunctor f).ι⟩

end FLT.Mazur.CartierAbel
