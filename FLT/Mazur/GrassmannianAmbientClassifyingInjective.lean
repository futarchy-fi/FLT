/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianAmbientChartRecovery
public import FLT.Mazur.GrassmannianPrincipalSeparation

/-!
# Global injectivity of original ambient quotient classification

Compare a global quotient with a chart point on the quotient's principal cover.
A second use of that separation argument proves injectivity for arbitrary global
quotients, retaining the entire submodule of relations over every coefficient ring.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R A M κ : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Fintype κ] {d : ℕ}
variable {ι : Type u} [Fintype ι] (b : Module.Basis ι R M)
  (hκ : Fintype.card κ = Fintype.card ι - d)

/-- A chart classification identifies a global original quotient uniquely. -/
theorem ambientClassifyingMap_eq_chart_iff
    (N : Module.Grassmannian A (A ⊗[R] M) d) (i : AmbientChartIndex R M κ d)
    (P : AmbientChartPoint (ambientChartBaseChange A i)) :
    ambientClassifyingMap b N hκ = ambientGluedChartPoint i P ↔ N = P.val := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ ambientClassifyingMap_ofChart b hκ i P⟩
  apply grassmannian_eq_of_pointCover b N N P.val hκ
  intro q
  let s := IsScalarTower.toAlgHom R A (Localization.Away q.2.val)
  apply (ambientGluedChartPoint_eq_iff q.1 i (ambientPointCoverChartPoint N q)
    (ambientChartMap s i P)).mp
  rw [ambientGluedChartPoint_natural]
  change ambientPointCoverClassifyingMap N q = _
  rw [← ambientClassifyingMap_local b N hκ q, h]
  rfl

/-- The global classifying map detects equality of complete original Grassmannian points. -/
theorem ambientClassifyingMap_injective :
    Function.Injective (fun N : Module.Grassmannian A (A ⊗[R] M) d ↦
      ambientClassifyingMap b N hκ) := by
  intro N P h
  apply grassmannian_eq_of_pointCover b N N P hκ
  intro q
  let s := IsScalarTower.toAlgHom R A (Localization.Away q.2.val)
  symm
  apply (ambientClassifyingMap_eq_chart_iff b hκ
    (Module.Grassmannian.map s P) q.1 (ambientPointCoverChartPoint N q)).mp
  rw [ambientClassifyingMap_natural]
  exact (congrArg (fun z ↦ Spec.map (CommRingCat.ofHom s.toRingHom) ≫ z) h).symm.trans
    (ambientClassifyingMap_local b N hκ q)

/-- Equality of global scheme classifications is precisely equality of original quotients. -/
theorem ambientClassifyingMap_eq_iff
    (N P : Module.Grassmannian A (A ⊗[R] M) d) :
    ambientClassifyingMap b N hκ = ambientClassifyingMap b P hκ ↔ N = P :=
  (ambientClassifyingMap_injective b hκ).eq_iff

end FLT.Mazur.GrassmannianChart
