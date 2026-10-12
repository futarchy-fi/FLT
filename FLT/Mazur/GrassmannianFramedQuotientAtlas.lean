/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianFramedSheafQuotient
public import FLT.Mazur.GrassmannianSheafQuotientTest
public import FLT.Mazur.GrassmannianQuotientAtlasEquivalence

/-!
# The original quotient atlas of a globally defined sheaf quotient

Finite frames of the target on an affine cover construct all original algebraic
relations. Their compatibility on actual intersections follows from the global
ambient projection, and gives a genuine classifying scheme morphism.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry TensorProduct
open CategoryTheory.Limits Scheme.Modules
namespace FLT.Mazur.GrassmannianChart
open GrassmannianOverlapAffineCoordinates
universe u
variable {R M ι κ τ : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  [Fintype ι] [Fintype κ] [Fintype τ] {d : ℕ}
variable (b : Module.Basis ι R M) (hκ : Fintype.card κ = Fintype.card ι - d)
variable {X : Scheme.{u}} (C : X.AffineOpenCover) [∀ j, Algebra R (C.X j)]
variable (β : X ⟶ Spec (.of R)) (hC : ∀ j, C.f j ≫ β = Spec.algebraMap R (C.X j))
variable {P : X.Modules} (p : grassmannianSchemeAmbient (M := M) β ⟶ P) [Epi p]
variable (e : ∀ j, (Scheme.Modules.pullback (C.f j)).obj P ≅ SheafOfModules.free τ)
  (hd : Fintype.card τ = d)
attribute [local irreducible] Scheme.Modules.pullback grassmannianQuotientSheaf

/-- The full original relation on each affine chart, constructed from the target frame. -/
def framedQuotientAtlasPoint (j : C.I₀) :
    Module.Grassmannian (C.X j) ((C.X j) ⊗[R] M) d :=
  framedSheafQuotientPoint (sheafQuotientTestMap β p (C.f j) (hC j)) (e j) hd

/-- The global projection forces equality of full original relations on all overlap tests. -/
theorem framedQuotientAtlasPoint_compatible :
    QuotientAtlasCompatible C β hC (framedQuotientAtlasPoint C β hC p e hd) := by
  intro j k D z
  let _ := coefficientAlgebra (R := R) (pullback.fst (C.f j) (C.f k)) z
  let w := z ≫ pullback.fst (C.f j) (C.f k) ≫ C.f j
  have hw : w ≫ β = Spec.algebraMap R D := by
    dsimp only [w]
    rw [Category.assoc, Category.assoc, hC j, coefficientAlgebra_spec]
  let l := left (R := R) (pullback.fst (C.f j) (C.f k)) z
  let r := right (pullback.fst (C.f j) (C.f k)) (pullback.snd (C.f j) (C.f k))
    (quotientAtlas_overlapBase C β hC j k) z
  have hl : Spec.map (CommRingCat.ofHom l.toRingHom) ≫ C.f j = w := by
    rw [left_spec, Category.assoc]
  have hr : Spec.map (CommRingCat.ofHom r.toRingHom) ≫ C.f k = w := by
    rw [right_spec, Category.assoc, ← pullback.condition]
  exact sheafQuotientTest_commonRelation β p (C.f j) (hC j) w hw l hl
    (framedQuotientAtlasPoint C β hC p e hd j)
    (framedSheafQuotientIso _ (e j) hd) (framedSheafQuotientIso_projection _ (e j) hd)
    (C.f k) (hC k) r hr (framedQuotientAtlasPoint C β hC p e hd k)
    (framedSheafQuotientIso _ (e k) hd) (framedSheafQuotientIso_projection _ (e k) hd)

/-- The global sheaf quotient with local finite frames constructs a scheme morphism. -/
@[irreducible] def framedQuotientClassifyingMap : X ⟶ ambientGrassmannianScheme R M κ d :=
  quotientAtlasClassifyingMap b hκ C β hC (framedQuotientAtlasPoint C β hC p e hd)
    (framedQuotientAtlasPoint_compatible C β hC p e hd)

/-- The constructed scheme classification retains the given base morphism. -/
@[reassoc] theorem framedQuotientClassifyingMap_over :
    framedQuotientClassifyingMap b hκ C β hC p e hd ≫
      ambientGrassmannianStructure R M κ d = β := by
  unfold framedQuotientClassifyingMap
  exact quotientAtlasClassifyingMap_over _ _ _ _ _ _ _

/-- The global classifying morphism recovers every original affine relation point. -/
@[reassoc] theorem framedQuotientClassifyingMap_chart (j : C.I₀) :
    C.f j ≫ framedQuotientClassifyingMap b hκ C β hC p e hd =
      ambientClassifyingMap b (framedQuotientAtlasPoint C β hC p e hd j) hκ := by
  unfold framedQuotientClassifyingMap
  exact quotientAtlasClassifyingMap_chart _ _ _ _ _ _ _ j

end FLT.Mazur.GrassmannianChart
