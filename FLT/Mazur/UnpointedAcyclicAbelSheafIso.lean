/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UnpointedLocalAcyclicEffectiveDescent

/-!
# The unpointed full Abel isomorphism of actual fppf sheaves

Effective full-divisor descent identifies the divisor presheaf with the
local acyclic Picard subsheaf. The comparison retains the actual positive
line class on every test, and requires no section of the original family.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.CartierAbel
open SchemePicard
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme.{0}} (f : X ⟶ Spec (.of R))
  [IsProper f] [Flat f] [GeometricallyIntegral f]

/-- The original acyclic divisor presheaf is an fppf sheaf without a family section. -/
theorem finiteTypeUnpointedAcyclicDivisorPresheaf_isSheaf :
    Presheaf.IsSheaf (Scheme.fppfTopology.over (Spec (.of R)))
      (finiteTypeAcyclicDivisorPresheaf f) := by
  apply Presheaf.isSheaf_of_isSheaf_comp _ _ uliftFunctor.{1}
  exact (Presheaf.isSheaf_of_iso_iff (finiteTypeUnpointedAbelFppfImageIso f)).mpr
    (finiteTypeUnpointedGeometricAcyclicFppf_isSheaf f)

/-- The full Abel comparison with the locally defined acyclic subsheaf. -/
def finiteTypeUnpointedAbelLocalFppfIso :
    finiteTypeAcyclicDivisorPresheaf f ⋙ uliftFunctor.{1} ≅
      (localGeometricAcyclicFppfSubfunctor f).toFunctor :=
  finiteTypeUnpointedAbelFppfImageIso f ≪≫
    { hom := Subfunctor.homOfLe ((geometricAcyclicFppfSubfunctor f).le_sheafify _)
      inv := Subfunctor.homOfLe (finiteTypeLocalGeometricAcyclicFppf_eq f).le
      hom_inv_id := by ext; rfl
      inv_hom_id := by ext; rfl }

/-- The full local comparison uses the original positive-divisor line class. -/
lemma finiteTypeUnpointedAbelLocalFppfIso_class (T : Over (Spec (.of R)))
    (D : AcyclicRankOneRelativeDivisor (Limits.pullback.snd f T.hom)) :
    ((finiteTypeUnpointedAbelLocalFppfIso f).hom.app (op T) (ULift.up D)).val =
      relativeFppfClass f T (abel (Limits.pullback.snd f T.hom) D.val) := rfl

/-- The actual sheaf of full divisors, with the original ideal-comap restriction maps. -/
def finiteTypeUnpointedAcyclicDivisorSheaf :
    Sheaf (Scheme.fppfTopology.over (Spec (.of R))) (Type 1) :=
  ⟨finiteTypeAcyclicDivisorPresheaf f ⋙ uliftFunctor.{1},
    (Presheaf.isSheaf_of_iso_iff (finiteTypeUnpointedAbelLocalFppfIso f)).mpr
      (localGeometricAcyclicFppf_isSheaf f)⟩

/-- Full Abel is an isomorphism of actual sheaves without an original family section. -/
def finiteTypeUnpointedAbelSheafIso :
    finiteTypeUnpointedAcyclicDivisorSheaf f ≅ localGeometricAcyclicFppfSheaf f where
  hom := ⟨(finiteTypeUnpointedAbelLocalFppfIso f).hom⟩
  inv := ⟨(finiteTypeUnpointedAbelLocalFppfIso f).inv⟩
  hom_inv_id := by
    apply Sheaf.hom_ext
    exact (finiteTypeUnpointedAbelLocalFppfIso f).hom_inv_id
  inv_hom_id := by
    apply Sheaf.hom_ext
    exact (finiteTypeUnpointedAbelLocalFppfIso f).inv_hom_id

end FLT.Mazur.CartierAbel
