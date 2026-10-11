/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothEtaleResidueLift
public import FLT.Mazur.SmoothOrderedTranslationTests

/-!
# Actual ordered translations on constructed étale neighborhoods

A point of an original ordered translation test over a field quotient of the
base extends to an étale test. Its original translation class is pulled back
along the constructed arrow and recovers the original class at the given point.
No constancy of the translation on the whole ordered test is asserted.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.OrderedCurvePower
open FCurve SchemePicard
set_option backward.isDefEq.respectTransparency false
variable {R K : Type} [CommRing R] [Field K] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [SmoothOfRelativeDimension 1 f] [IsSeparated f]
  (i : SmoothTranslationIndex) (φ : R →+* K) (hφ : Function.Surjective φ)
  (x : Over.mk (Spec.map (CommRingCat.ofHom φ)) ⟶ smoothTranslationTest f i)

omit [IsSeparated f] in
include hφ in
/-- An actual ordered translation point extends to a constructed étale original test. -/
theorem exists_orderedTranslation_etale_lift :
    ∃ (E : Over (Spec (.of R))) (b : E ⟶ smoothTranslationTest f i)
      (a : Over.mk (Spec.map (CommRingCat.ofHom φ)) ⟶ E),
      Etale E.hom ∧ a ≫ b = x := by
  obtain ⟨E, e, v, z, he, hv, hz, hvz⟩ := SmoothEtaleResidueLift.exists_lift
    (smoothTranslationTest f i).hom φ hφ x.left (Over.w x)
  refine ⟨Over.mk e, Over.homMk v hv, Over.homMk z hz, he, ?_⟩
  exact Over.OverMorphism.ext hvz

/-- The original relative Picard class is recovered, without replacing sheafification. -/
theorem orderedTranslation_etale_class {B : X.Modules} (hB : LocallyFreeRankOne B)
    {E : Over (Spec (.of R))} (b : E ⟶ smoothTranslationTest f i)
    (a : Over.mk (Spec.map (CommRingCat.ofHom φ)) ⟶ E) (ha : a ≫ b = x) :
    (relativeFppfSheaf f).obj.map a.op
      ((relativeFppfSheaf f).obj.map b.op (smoothTranslationClass f hB i)) =
        (relativeFppfSheaf f).obj.map x.op (smoothTranslationClass f hB i) := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, ha]

omit [IsSeparated f] in
/-- Each local-ring residue point supplies an actual étale neighborhood of its translation. -/
theorem exists_orderedTranslation_etale_residue [IsLocalRing R]
    (x : Over.mk (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) ⟶
      smoothTranslationTest f i) :
    ∃ (E : Over (Spec (.of R))) (b : E ⟶ smoothTranslationTest f i)
      (a : Over.mk (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) ⟶ E),
      Etale E.hom ∧ a ≫ b = x :=
  exists_orderedTranslation_etale_lift f i (IsLocalRing.residue R)
    IsLocalRing.residue_surjective x

end FLT.Mazur.OrderedCurvePower
