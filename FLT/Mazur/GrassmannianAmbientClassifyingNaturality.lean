/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianAmbientClassifyingMap

/-!
# Naturality of the global ambient quotient classification

Every coefficient map carrying an original quotient into an ambient chart
recovers that chart's classifying morphism. Pulling back the actual principal
cover proves the global construction natural under all coefficient maps.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R A B M κ : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [AddCommGroup M] [Module R M] [Fintype κ] {d : ℕ}
variable {ι : Type u} [Fintype ι] (b : Module.Basis ι R M)
  (N : Module.Grassmannian A (A ⊗[R] M) d) (hκ : Fintype.card κ = Fintype.card ι - d)

/-- An arbitrary coefficient test in a chart recovers its actual chart classification. -/
theorem ambientClassifyingMap_chartTest (s : A →ₐ[R] B) (i : AmbientChartIndex R M κ d)
    (P : AmbientChartPoint (ambientChartBaseChange B i))
    (hP : P.val = Module.Grassmannian.map s N) :
    Spec.map (CommRingCat.ofHom s.toRingHom) ≫ ambientClassifyingMap b N hκ =
      ambientGluedChartPoint i P := by
  let C := ambientPointPrincipalCover b N hκ
  let f := Spec.map (CommRingCat.ofHom s.toRingHom)
  apply (show (Spec (.of B)).OpenCover from C.pullback₁ f).hom_ext
  intro p
  change pullback.fst f (C.f p) ≫ f ≫ ambientClassifyingMap b N hκ =
    pullback.fst f (C.f p) ≫ ambientGluedChartPoint i P
  rw [pullback.condition_assoc]
  change pullback.snd f (C.f p) ≫ Spec.algebraMap A (Localization.Away p.2.val) ≫
    ambientClassifyingMap b N hκ = _
  refine (congrArg (fun z ↦ pullback.snd f (C.f p) ≫ z)
    (ambientClassifyingMap_local b N hκ p)).trans ?_
  exact ambientGluedChartPoint_commonTest
    (IsScalarTower.toAlgHom R A (Localization.Away p.2.val)) s N p.1 i
    (ambientPointCoverChartPoint N p) P rfl hP _ _ pullback.condition.symm

/-- The global map classifying the original quotient is natural for every coefficient map. -/
theorem ambientClassifyingMap_natural (s : A →ₐ[R] B) :
    ambientClassifyingMap b (Module.Grassmannian.map s N) hκ =
      Spec.map (CommRingCat.ofHom s.toRingHom) ≫ ambientClassifyingMap b N hκ := by
  symm
  apply ambientClassifyingMap_unique
  intro p
  let t := IsScalarTower.toAlgHom R B (Localization.Away p.2.val)
  have hp : (ambientPointCoverChartPoint (Module.Grassmannian.map s N) p).val =
      Module.Grassmannian.map (t.comp s) N := (Module.Grassmannian.map_comp d s t N).symm
  have he := ambientClassifyingMap_chartTest b N hκ (t.comp s) p.1
    (ambientPointCoverChartPoint (Module.Grassmannian.map s N) p) hp
  change Spec.map (CommRingCat.ofHom s.toRingHom ≫ CommRingCat.ofHom t.toRingHom) ≫
    ambientClassifyingMap b N hκ = _ at he
  rw [Spec.map_comp, Category.assoc] at he
  exact he

end FLT.Mazur.GrassmannianChart
