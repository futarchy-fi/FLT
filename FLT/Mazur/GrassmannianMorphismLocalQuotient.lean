/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianMorphismPrincipalCover
public import FLT.Mazur.GrassmannianAmbientClassifyingInjective

/-!
# Recovering local original quotients from an arbitrary scheme morphism

Each principal chart refinement gives an actual finite projective quotient of the
original scalar-extended ambient module, with rank d. Equal maps from arbitrary
common coefficient algebras recover equal full relations on intersections.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R A M κ : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Fintype κ] {d : ℕ}
variable (f : Spec (.of A) ⟶ ambientGrassmannianScheme R M κ d)
  (hf : f ≫ ambientGrassmannianStructure R M κ d = Spec.algebraMap R A)

include hf in
/-- Each lifted local morphism preserves the original coefficient base. -/
@[reassoc] theorem ambientMorphismChartLift_over (q : AmbientMorphismCoverIndex f) :
    ambientMorphismChartLift f q ≫ splitChartStructure R κ d =
      Spec.algebraMap R (Localization.Away q.2.val) := by
  rw [← ambientGrassmannianChart_over R M κ d q.1, ← Category.assoc,
    ambientMorphismChartLift_fac, Category.assoc, hf]
  rw [Spec.algebraMap, Spec.algebraMap, Spec.algebraMap, ← Spec.map_comp]
  congr 1

/-- The original chart quotient recovered from the principal-local test morphism. -/
def ambientMorphismLocalPoint (q : AmbientMorphismCoverIndex f) :
    AmbientChartPoint (ambientChartBaseChange (Localization.Away q.2.val) q.1) :=
  ambientChartSchemePointEquiv q.1
    ⟨ambientMorphismChartLift f q, ambientMorphismChartLift_over f hf q⟩

/-- The recovered quotient really classifies the restriction of the original scheme morphism. -/
theorem ambientMorphismLocalPoint_classifies (q : AmbientMorphismCoverIndex f) :
    ambientGluedChartPoint q.1 (ambientMorphismLocalPoint f hf q) =
      Spec.algebraMap A (Localization.Away q.2.val) ≫ f := by
  unfold ambientGluedChartPoint ambientMorphismLocalPoint
  rw [Equiv.symm_apply_apply]
  exact ambientMorphismChartLift_fac f q

/-- Local recovered quotients agree after every pair of compatible coefficient maps. -/
theorem ambientMorphismLocalPoint_compatible {B : Type u} [CommRing B] [Algebra R B]
    (p q : AmbientMorphismCoverIndex f)
    (s : Localization.Away p.2.val →ₐ[R] B) (t : Localization.Away q.2.val →ₐ[R] B)
    (h : s.comp (IsScalarTower.toAlgHom R A (Localization.Away p.2.val)) =
      t.comp (IsScalarTower.toAlgHom R A (Localization.Away q.2.val))) :
    Module.Grassmannian.map s (ambientMorphismLocalPoint f hf p).val =
      Module.Grassmannian.map t (ambientMorphismLocalPoint f hf q).val := by
  apply (ambientGluedChartPoint_eq_iff p.1 q.1
    (ambientChartMap s p.1 (ambientMorphismLocalPoint f hf p))
    (ambientChartMap t q.1 (ambientMorphismLocalPoint f hf q))).mp
  rw [ambientGluedChartPoint_natural, ambientGluedChartPoint_natural,
    ambientMorphismLocalPoint_classifies, ambientMorphismLocalPoint_classifies,
    ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  apply congrArg (fun z ↦ z ≫ f)
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact congrArg (fun e : A →ₐ[R] B ↦ e a) h

/-- Applying recovery to a global classification recovers every original localized quotient. -/
theorem ambientMorphismLocalPoint_ofClassifying {ι : Type u} [Fintype ι]
    (b : Module.Basis ι R M) (N : Module.Grassmannian A (A ⊗[R] M) d)
    (hκ : Fintype.card κ = Fintype.card ι - d)
    (q : AmbientMorphismCoverIndex (ambientClassifyingMap b N hκ)) :
    (ambientMorphismLocalPoint (ambientClassifyingMap b N hκ)
      (ambientClassifyingMap_over b N hκ) q).val =
        Module.Grassmannian.map (IsScalarTower.toAlgHom R A (Localization.Away q.2.val)) N := by
  symm
  apply (ambientClassifyingMap_eq_chart_iff b hκ _ q.1 _).mp
  rw [ambientClassifyingMap_natural, ambientMorphismLocalPoint_classifies]
  rfl

end FLT.Mazur.GrassmannianChart
