/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteTypeAbelNaturalIso
public import FLT.Mazur.ProperPointedAcyclicFppfSheaf

/-!
# Full divisors and the actual acyclic Picard subsheaf

For proper flat geometrically integral pointed families over a finite-type
integer ring, the intrinsic Abel correspondence is an isomorphism of fppf
sheaves on ALL test schemes. It retains the actual positive-line class map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.CartierAbel
open SchemePicard
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme.{0}} (f : X ⟶ Spec (.of R))
  [IsProper f] [Flat f] [GeometricallyIntegral f]
  (e : Spec (.of R) ⟶ X) (he : e ≫ f = 𝟙 _)

local instance : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R

local instance : GeometricallyConnected f := ⟨by
  intro K _ a Y p q H
  let _ := GeometricallyIntegral.geometrically_isIntegral (f := f) a p q H
  infer_instance⟩

/-- The natural Abel isomorphism into the original actual Picard-sheaf acyclic locus. -/
def finiteTypePointedAbelFppfIso : finiteTypeAcyclicDivisorPresheaf f ⋙ uliftFunctor.{1} ≅
    (geometricAcyclicFppfSubfunctor f).toFunctor :=
  finiteTypeAbelNaturalIso f ≪≫ geometricAcyclicFppfIso f e he

/-- The comparison is exactly the canonical fppf class of the positive divisor line. -/
lemma finiteTypePointedAbelFppfIso_class (T : Over (Spec (.of R)))
    (D : AcyclicRankOneRelativeDivisor (Limits.pullback.snd f T.hom)) :
    ((finiteTypePointedAbelFppfIso f e he).hom.app (op T) (ULift.up D)).val =
      relativeFppfClass f T (abel (Limits.pullback.snd f T.hom) D.val) := rfl

include e he in
/-- Full acyclic relative Cartier divisors satisfy effective unique fppf descent. -/
theorem finiteTypeAcyclicDivisorPresheaf_isSheaf :
    Presheaf.IsSheaf (Scheme.fppfTopology.over (Spec (.of R)))
      (finiteTypeAcyclicDivisorPresheaf f) := by
  apply Presheaf.isSheaf_of_isSheaf_comp _ _ uliftFunctor.{1}
  exact (Presheaf.isSheaf_of_iso_iff (finiteTypeAbelNaturalIso f)).mpr
    (properPointed_geometricAcyclicPicard_isSheaf f e he)

/-- The sheaf of actual full divisors, with the previously constructed ideal-comap maps. -/
def finiteTypePointedAcyclicDivisorSheaf :
    Sheaf (Scheme.fppfTopology.over (Spec (.of R))) (Type 1) :=
  ⟨finiteTypeAcyclicDivisorPresheaf f ⋙ uliftFunctor.{1},
    (Presheaf.isSheaf_of_iso_iff (finiteTypeAbelNaturalIso f)).mpr
      (properPointed_geometricAcyclicPicard_isSheaf f e he)⟩

/-- Abel is an isomorphism of actual sheaves, not just a correspondence of test values. -/
def finiteTypePointedAbelSheafIso :
    finiteTypePointedAcyclicDivisorSheaf f e he ≅ properPointedAcyclicFppfSheaf f e he where
  hom := ⟨(finiteTypePointedAbelFppfIso f e he).hom⟩
  inv := ⟨(finiteTypePointedAbelFppfIso f e he).inv⟩
  hom_inv_id := by
    apply Sheaf.hom_ext
    exact (finiteTypePointedAbelFppfIso f e he).hom_inv_id
  inv_hom_id := by
    apply Sheaf.hom_ext
    exact (finiteTypePointedAbelFppfIso f e he).inv_hom_id

end FLT.Mazur.CartierAbel
