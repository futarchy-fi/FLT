/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianQuotientImageRecovery
public import FLT.Mazur.GrassmannianAmbientChartNormalization
public import FLT.Mazur.GrassmannianSheafQuotientTest

/-!
# Global recovery from constructed original quotient charts

Local original relation presentations give the required recovery isomorphism for
the actual descended quotient image. Its projection is the original global
quotient, transported only along equality of its original base morphism.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
namespace FLT.Mazur.GrassmannianOpenChartDescent
open GrassmannianChart
universe u
variable {R M ι κ : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  [Fintype ι] [Fintype κ] {d : ℕ}
variable (b : Module.Basis ι R M) (hκ : Fintype.card κ = Fintype.card ι - d)
variable {X : Scheme.{u}} (β : X ⟶ Spec (.of R))
  {P : X.Modules} (p : grassmannianSchemeAmbient (M := M) β ⟶ P)
variable (C : X.AffineOpenCover.{u}) [∀ j, Algebra R (C.X j)]
  (hC : ∀ j, C.f j ≫ β = Spec.algebraMap R (C.X j))
variable (N : ∀ j, Module.Grassmannian (C.X j) ((C.X j) ⊗[R] M) d)
variable (f : X ⟶ ambientGrassmannianScheme R M κ d)
  (hf : f ≫ ambientGrassmannianStructure R M κ d = β)
  (h : ∀ j, C.f j ≫ f = ambientClassifyingMap b (N j) hκ)
variable (e : ∀ j, grassmannianQuotientSheaf (N j) ≅ (pullback (C.f j)).obj P)
  (he : ∀ j, grassmannianQuotientSheafMap (N j) ≫ (e j).hom =
    sheafQuotientTestMap β p (C.f j) (hC j))
attribute [local irreducible] Scheme.Modules.pullback grassmannianQuotientSheaf

/-- The original classifying charts, with their original coefficient algebras retained. -/
def presentedQuotientCharts (j : C.I₀) :
    {a : Spec (C.X j) ⟶ ambientGrassmannianScheme R M κ d //
      a ≫ ambientGrassmannianStructure R M κ d = Spec.algebraMap R (C.X j)} :=
  ⟨ambientClassifyingMap b (N j) hκ, ambientClassifyingMap_over b (N j) hκ⟩

/-- The recovered point on each classifying chart is identified with its original quotient. -/
def presentedQuotientChartIso (j : C.I₀) :
    grassmannianQuotientSheaf (ambientMorphismPoint
      (presentedQuotientCharts b hκ C N j).val (presentedQuotientCharts b hκ C N j).property) ≅
        (pullback (C.f j)).obj P :=
  grassmannianQuotientSheafCongr (ambientMorphismPoint_ofClassifying b hκ (N j)) ≪≫ e j

include he in
/-- The original projection is retained after normalization to the classifying map's base. -/
theorem presentedQuotientChartIso_projection (j : C.I₀) :
    quotientAmbientChartMap f (fun j ↦ C.X j) C.f (presentedQuotientCharts b hκ C N) h j ≫
        (presentedQuotientChartIso b hκ C N e j).hom =
      (pullback (C.f j)).map
        ((eqToIso (congrArg (grassmannianSchemeAmbient (M := M)) hf)).hom ≫ p) := by
  rw [quotientAmbientChartMap_normalized]
  unfold presentedQuotientChartIso
  dsimp only [Iso.trans_hom]
  rw [Category.assoc, ← Category.assoc (grassmannianQuotientSheafMap _),
    grassmannianQuotientSheafCongr_projection, he j]
  unfold sheafQuotientTestMap
  rw [← grassmannianSchemeAmbientTestIso_congr _ β hf (C.f j) _ (hC j)]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Functor.map_comp]

/-- The actual descended quotient is isomorphic to the original global sheaf quotient. -/
@[irreducible] def presentedQuotientRecoveryIso :
    quotientImageSheaf b hκ f (fun j ↦ C.X j) C.f (presentedQuotientCharts b hκ C N) h ≅ P :=
  quotientImageRecoveryIso b hκ f (fun j ↦ C.X j) C.f
    (presentedQuotientCharts b hκ C N) h (fun x ↦ ⟨C.idx x, C.covers x⟩) P
    ((eqToIso (congrArg (grassmannianSchemeAmbient (M := M)) hf)).hom ≫ p)
    (presentedQuotientChartIso b hκ C N e)
    (presentedQuotientChartIso_projection b hκ β p C hC N f hf h e he)

/-- Global recovery preserves the entire original ambient projection. -/
@[reassoc] theorem presentedQuotientRecoveryIso_projection :
    quotientImageAmbientMap b hκ f (fun j ↦ C.X j) C.f (presentedQuotientCharts b hκ C N) h ≫
        (presentedQuotientRecoveryIso b hκ β p C hC N f hf h e he).hom =
      (eqToIso (congrArg (grassmannianSchemeAmbient (M := M)) hf)).hom ≫ p := by
  unfold presentedQuotientRecoveryIso
  exact quotientImageRecoveryIso_projection _ _ _ _ _ _ _ _ _ _ _ _

end FLT.Mazur.GrassmannianOpenChartDescent
