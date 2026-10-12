/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianPresentedQuotientRecovery

/-!
# A sealed global quotient recovery statement

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

/-- Recovery means an actual isomorphism preserving the entire ambient projection. -/
@[irreducible] def PresentedQuotientRecovers : Prop :=
  ∃ e : quotientImageSheaf b hκ f (fun j ↦ C.X j) C.f
      (presentedQuotientCharts b hκ C N) h ≅ P,
    quotientImageAmbientMap b hκ f (fun j ↦ C.X j) C.f
        (presentedQuotientCharts b hκ C N) h ≫ e.hom =
      (eqToIso (congrArg (grassmannianSchemeAmbient (M := M)) hf)).hom ≫ p

include hC e he in
/-- Local original presentations construct the sealed global recovery assertion. -/
theorem presentedQuotientRecovers_of_charts :
    PresentedQuotientRecovers b hκ β p C N f hf h := by
  unfold PresentedQuotientRecovers
  exact ⟨presentedQuotientRecoveryIso b hκ β p C hC N f hf h e he,
    presentedQuotientRecoveryIso_projection b hκ β p C hC N f hf h e he⟩

end FLT.Mazur.GrassmannianOpenChartDescent
