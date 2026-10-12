/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianQuotientSheafFaithful

/-!
# Full quotient charts detect arbitrary-scheme Grassmannian morphisms

The original affine cover detects equality of scheme morphisms. On every chart,
isomorphism of the full ambient quotients detects the complete original point.
No affineness of the source or of its chart intersections is required.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R M ι κ : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  [Fintype ι] [Fintype κ] {d : ℕ}
variable (b : Module.Basis ι R M) (hκ : Fintype.card κ = Fintype.card ι - d)

include b hκ in
/-- The full ambient quotient of an affine test determines its entire scheme morphism. -/
theorem ambientMorphism_eq_of_quotientSheafIso
    {A : Type u} [CommRing A] [Algebra R A]
    (f g : Spec (.of A) ⟶ ambientGrassmannianScheme R M κ d)
    (hf : f ≫ ambientGrassmannianStructure R M κ d = Spec.algebraMap R A)
    (hg : g ≫ ambientGrassmannianStructure R M κ d = Spec.algebraMap R A)
    (e : grassmannianQuotientSheaf (ambientMorphismPoint f hf) ≅
      grassmannianQuotientSheaf (ambientMorphismPoint g hg))
    (he : grassmannianQuotientSheafMap (ambientMorphismPoint f hf) ≫ e.hom =
      grassmannianQuotientSheafMap (ambientMorphismPoint g hg)) : f = g := by
  have hp := grassmannianPoint_eq_of_quotientSheafIso _ _ e he
  rw [← ambientMorphismPoint_classifies f hf b hκ,
    ← ambientMorphismPoint_classifies g hg b hκ, hp]

variable {X : Scheme.{u}} (C : X.AffineOpenCover) [∀ j, Algebra R (C.X j)]
variable (f g : X ⟶ ambientGrassmannianScheme R M κ d)
  (hf : ∀ j, (C.f j ≫ f) ≫ ambientGrassmannianStructure R M κ d =
    Spec.algebraMap R (C.X j))
  (hg : ∀ j, (C.f j ≫ g) ≫ ambientGrassmannianStructure R M κ d =
    Spec.algebraMap R (C.X j))

include b hκ in
/-- Original full quotient charts determine a Grassmannian morphism on any source scheme. -/
theorem schemeMorphism_eq_of_quotientSheafCharts
    (e : ∀ j, grassmannianQuotientSheaf (ambientMorphismPoint (C.f j ≫ f) (hf j)) ≅
      grassmannianQuotientSheaf (ambientMorphismPoint (C.f j ≫ g) (hg j)))
    (he : ∀ j, grassmannianQuotientSheafMap (ambientMorphismPoint (C.f j ≫ f) (hf j)) ≫
      (e j).hom = grassmannianQuotientSheafMap (ambientMorphismPoint (C.f j ≫ g) (hg j))) :
    f = g := by
  apply C.openCover.hom_ext
  intro j
  exact ambientMorphism_eq_of_quotientSheafIso b hκ _ _ (hf j) (hg j) (e j) (he j)

end FLT.Mazur.GrassmannianChart
