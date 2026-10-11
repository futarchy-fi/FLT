/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothEtaleSeparableLift
public import FLT.Mazur.SmoothOrderedTranslationTests

/-!
# Ordered translations over separable residue extensions

A point of an original ordered translation test over a separable extension
of a base residue field extends to an actual étale neighborhood of the
original base. Its pulled-back original Picard section is recovered exactly.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.OrderedCurvePower
open FCurve SchemePicard
set_option backward.isDefEq.respectTransparency false
variable {R k K : Type} [CommRing R] [Field k] [Field K] [Algebra k K]
  [Algebra.IsSeparable k K] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [SmoothOfRelativeDimension 1 f] [IsSeparated f]
  (i : SmoothTranslationIndex) (φ : R →+* k) (hφ : φ.SurjectiveOnStalks)
  (x : Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap k K).comp φ))) ⟶ smoothTranslationTest f i)

omit [IsSeparated f] in
include hφ in
/-- An actual ordered translation point extends to a constructed étale original test. -/
theorem exists_orderedTranslation_etale_separable_lift :
    ∃ (E : Over (Spec (.of R))) (b : E ⟶ smoothTranslationTest f i)
      (a : Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap k K).comp φ))) ⟶ E),
      Etale E.hom ∧ a ≫ b = x := by
  obtain ⟨E, e, v, z, he, hv, hz, hvz⟩ := SmoothEtaleSeparableLift.exists_lift
    (smoothTranslationTest f i).hom φ hφ x.left (Over.w x)
  refine ⟨Over.mk e, Over.homMk v hv, Over.homMk z hz, he, ?_⟩
  exact Over.OverMorphism.ext hvz

omit [Algebra.IsSeparable k K] in
/-- The original relative Picard class is recovered, without replacing sheafification. -/
theorem orderedTranslation_etale_separable_class {B : X.Modules} (hB : LocallyFreeRankOne B)
    {E : Over (Spec (.of R))} (b : E ⟶ smoothTranslationTest f i)
    (a : Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap k K).comp φ))) ⟶ E) (ha : a ≫ b = x) :
    (relativeFppfSheaf f).obj.map a.op
      ((relativeFppfSheaf f).obj.map b.op (smoothTranslationClass f hB i)) =
        (relativeFppfSheaf f).obj.map x.op (smoothTranslationClass f hB i) := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, ha]

end FLT.Mazur.OrderedCurvePower
