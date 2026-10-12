/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianFramedQuotientAtlas
public import FLT.Mazur.ModuleSheafFramedAffineCover

/-!
# Quotient atlases from pointwise fixed-rank local freeness

No affine charts or algebraic relations are inputs. The original quotient and
pointwise local frames construct a compatible original algebraic atlas, retaining
the complete ambient projection on every member of an actual affine cover.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R M τ : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  [Fintype τ] {d : ℕ}
variable {X : Scheme.{u}} (β : X ⟶ Spec (.of R))
  {P : X.Modules} (p : grassmannianSchemeAmbient (M := M) β ⟶ P) [Epi p]
variable (hP : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
  Nonempty (P.restrict U.ι ≅ SheafOfModules.free τ)) (hd : Fintype.card τ = d)
attribute [local irreducible] Scheme.Modules.pullback grassmannianQuotientSheaf

include hP hd in
/-- Pointwise fixed-rank frames construct a compatible atlas of full original relations. -/
theorem exists_originalQuotientAtlas :
    ∃ (C : X.AffineOpenCover.{u}) (a : ∀ j, Algebra R (C.X j)),
      let _ := a
      ∃ (hC : ∀ j, C.f j ≫ β = Spec.algebraMap R (C.X j))
        (N : ∀ j, Module.Grassmannian (C.X j) ((C.X j) ⊗[R] M) d),
        QuotientAtlasCompatible C β hC N ∧
        ∀ j, ∃ e : grassmannianQuotientSheaf (N j) ≅ (pullback (C.f j)).obj P,
          grassmannianQuotientSheafMap (N j) ≫ e.hom =
            sheafQuotientTestMap β p (C.f j) (hC j) := by
  obtain ⟨C, he⟩ := ModuleSheafFramedAffineCover.exists_affineFrameCover P τ hP
  let a : ∀ j, Algebra R (C.X j) := fun j ↦
    (Spec.preimage (C.f j ≫ β)).hom.toAlgebra
  let _ := a
  let hC : ∀ j, C.f j ≫ β = Spec.algebraMap R (C.X j) := fun j ↦
    (Spec.map_preimage (C.f j ≫ β)).symm
  let e := fun j ↦ (he j).some
  refine ⟨C, a, hC, framedQuotientAtlasPoint C β hC p e hd,
    framedQuotientAtlasPoint_compatible C β hC p e hd, ?_⟩
  intro j
  exact ⟨framedSheafQuotientIso _ (e j) hd, framedSheafQuotientIso_projection _ (e j) hd⟩

variable {ι κ : Type u} [Fintype ι] [Fintype κ]
  (b : Module.Basis ι R M) (hκ : Fintype.card κ = Fintype.card ι - d)

include hP hd in
/-- A locally framed global quotient constructs an actual scheme classification over its base. -/
theorem exists_locallyFramedQuotientClassifying :
    ∃ f : X ⟶ ambientGrassmannianScheme R M κ d,
      f ≫ ambientGrassmannianStructure R M κ d = β ∧
      ∃ (C : X.AffineOpenCover.{u}) (a : ∀ j, Algebra R (C.X j)),
        let _ := a
        ∃ (hC : ∀ j, C.f j ≫ β = Spec.algebraMap R (C.X j))
          (N : ∀ j, Module.Grassmannian (C.X j) ((C.X j) ⊗[R] M) d),
          (∀ j, C.f j ≫ f = ambientClassifyingMap b (N j) hκ) ∧
          ∀ j, ∃ e : grassmannianQuotientSheaf (N j) ≅ (pullback (C.f j)).obj P,
            grassmannianQuotientSheafMap (N j) ≫ e.hom =
              sheafQuotientTestMap β p (C.f j) (hC j) := by
  obtain ⟨C, a, hC, N, hN, he⟩ := exists_originalQuotientAtlas β p hP hd
  let _ := a
  exact ⟨quotientAtlasClassifyingMap b hκ C β hC N hN,
    quotientAtlasClassifyingMap_over b hκ C β hC N hN, C, a, hC, N,
    quotientAtlasClassifyingMap_chart b hκ C β hC N hN, he⟩

end FLT.Mazur.GrassmannianChart
