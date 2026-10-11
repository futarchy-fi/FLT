/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UnpointedLocalAcyclicEffectiveDescent
public import FLT.Mazur.FiniteTypeUnpointedFppfOpenYoneda

/-!
# The actual full divisor on each unpointed acyclic test open

The representing open of an arbitrary Picard-sheaf section carries its own
constructed acyclic relative divisor. Pullback along every map into that
open gives the unique full divisor of the restricted original section.
This constructs universal divisors on test opens, not a global parameter scheme.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.CartierAbel
open SchemePicard
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme.{0}} (f : X ⟶ Spec (.of R))
  [IsProper f] [Flat f] [GeometricallyIntegral f]
  (T : Over (Spec (.of R))) (s : (relativeFppfSheaf f).obj.obj (op T))

/-- The restricted original section is acyclic on its actual representing open. -/
theorem finiteTypeUnpointedOpenSection_mem :
    (relativeFppfSheaf f).obj.map (finiteTypeUnpointedFppfOpenArrow f T s).op s ∈
      (localGeometricAcyclicFppfSubfunctor f).obj
        (op (finiteTypeUnpointedFppfOpenTest f T s)) := by
  have h := (finiteTypeFppfOpenYonedaMap f T s _ (𝟙 _)).property
  change (relativeFppfSheaf f).obj.map
    (𝟙 _ ≫ finiteTypeUnpointedFppfOpenArrow f T s).op s ∈
      (localGeometricAcyclicFppfSubfunctor f).obj
        (op (finiteTypeUnpointedFppfOpenTest f T s)) at h
  simpa only [Category.id_comp] using h

/-- The unique full acyclic divisor on the original section's actual acyclic open. -/
def finiteTypeUnpointedOpenDivisor : AcyclicRankOneRelativeDivisor
    (Limits.pullback.snd f (finiteTypeUnpointedFppfOpenTest f T s).hom) :=
  (finiteTypeUnpointedLocalAcyclicFppf_existsUnique f _ _
    (finiteTypeUnpointedOpenSection_mem f T s)).choose

/-- The constructed open divisor represents precisely the restricted original section. -/
theorem finiteTypeUnpointedOpenDivisor_class :
    relativeFppfClass f _ (abel _ (finiteTypeUnpointedOpenDivisor f T s).val) =
      (relativeFppfSheaf f).obj.map (finiteTypeUnpointedFppfOpenArrow f T s).op s :=
  (finiteTypeUnpointedLocalAcyclicFppf_existsUnique f _ _
    (finiteTypeUnpointedOpenSection_mem f T s)).choose_spec.1

/-- Every map into the open pulls its full divisor back to the original restricted section. -/
theorem finiteTypeUnpointedOpenDivisor_map_class {U : Over (Spec (.of R))}
    (k : U ⟶ finiteTypeUnpointedFppfOpenTest f T s) :
    relativeFppfClass f U
      (abel _ (finiteTypeAcyclicDivisorMap f k (finiteTypeUnpointedOpenDivisor f T s)).val) =
        (relativeFppfSheaf f).obj.map (k ≫ finiteTypeUnpointedFppfOpenArrow f T s).op s := by
  rw [finiteTypeAcyclicDivisorMap_class, ← relativeFppfClass_naturality,
    finiteTypeUnpointedOpenDivisor_class]
  simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

/-- Any independently supplied full divisor of that section is this actual pullback. -/
theorem finiteTypeUnpointedOpenDivisor_unique {U : Over (Spec (.of R))}
    (k : U ⟶ finiteTypeUnpointedFppfOpenTest f T s)
    (D : AcyclicRankOneRelativeDivisor (Limits.pullback.snd f U.hom))
    (hD : relativeFppfClass f U (abel _ D.val) =
      (relativeFppfSheaf f).obj.map (k ≫ finiteTypeUnpointedFppfOpenArrow f T s).op s) :
    D = finiteTypeAcyclicDivisorMap f k (finiteTypeUnpointedOpenDivisor f T s) :=
  finiteTypeAcyclicAbelFppf_injective f U
    (hD.trans (finiteTypeUnpointedOpenDivisor_map_class f T s k).symm)

/-- Recovery identifies the entire ideal comap, including multiplicities and nilpotents. -/
theorem finiteTypeUnpointedOpenDivisor_unique_ideal {U : Over (Spec (.of R))}
    (k : U ⟶ finiteTypeUnpointedFppfOpenTest f T s)
    (D : AcyclicRankOneRelativeDivisor (Limits.pullback.snd f U.hom))
    (hD : relativeFppfClass f U (abel _ D.val) =
      (relativeFppfSheaf f).obj.map (k ≫ finiteTypeUnpointedFppfOpenArrow f T s).op s) :
    D.val.val = (finiteTypeUnpointedOpenDivisor f T s).val.val.comap (relativeTotalMap f k) := by
  rw [finiteTypeUnpointedOpenDivisor_unique f T s k D hD, finiteTypeAcyclicDivisorMap_ideal]

end FLT.Mazur.CartierAbel
