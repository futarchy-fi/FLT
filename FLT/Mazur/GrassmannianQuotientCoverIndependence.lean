/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianSheafQuotientTest
public import FLT.Mazur.GrassmannianQuotientAtlasEquivalence

/-!
# Independence of original quotient presentations from their source covers

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
variable {R M ι κ : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  [Fintype ι] [Fintype κ] {d : ℕ}
variable (b : Module.Basis ι R M) (hκ : Fintype.card κ = Fintype.card ι - d)
variable {X : Scheme.{u}} (β : X ⟶ Spec (.of R))
  {P : X.Modules} (p : grassmannianSchemeAmbient (M := M) β ⟶ P)
attribute [local irreducible] Scheme.Modules.pullback grassmannianQuotientSheaf

/-- Any two original local presentations classify identically on their full intersection. -/
theorem sheafQuotientClassifying_overlap {A B : Type u} [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    (i : Spec (.of A) ⟶ X) (hi : i ≫ β = Spec.algebraMap R A)
    (k : Spec (.of B) ⟶ X) (hk : k ≫ β = Spec.algebraMap R B)
    (N : Module.Grassmannian A (A ⊗[R] M) d)
    (N' : Module.Grassmannian B (B ⊗[R] M) d)
    (e : grassmannianQuotientSheaf N ≅ (Scheme.Modules.pullback i).obj P)
    (e' : grassmannianQuotientSheaf N' ≅ (Scheme.Modules.pullback k).obj P)
    (he : grassmannianQuotientSheafMap N ≫ e.hom = sheafQuotientTestMap β p i hi)
    (he' : grassmannianQuotientSheafMap N' ≫ e'.hom = sheafQuotientTestMap β p k hk) :
    pullback.fst i k ≫ ambientClassifyingMap b N hκ =
      pullback.snd i k ≫ ambientClassifyingMap b N' hκ := by
  have w : pullback.fst i k ≫ Spec.algebraMap R A =
      pullback.snd i k ≫ Spec.algebraMap R B := by
    rw [← hi, ← hk, ← Category.assoc, pullback.condition, Category.assoc]
  apply (pullback i k).affineOpenCover.openCover.hom_ext
  intro t
  let T := (pullback i k).affineOpenCover.X t
  let z : Spec T ⟶ pullback i k := (pullback i k).affineOpenCover.f t
  let _ : Algebra R T := coefficientAlgebra (R := R) (pullback.fst i k) z
  let v := z ≫ pullback.fst i k ≫ i
  have hv : v ≫ β = Spec.algebraMap R T := by
    dsimp only [v]
    rw [Category.assoc, Category.assoc, hi, coefficientAlgebra_spec]
  let l := left (R := R) (pullback.fst i k) z
  let r := right (pullback.fst i k) (pullback.snd i k) w z
  have hl : Spec.map (CommRingCat.ofHom l.toRingHom) ≫ i = v := by
    rw [left_spec, Category.assoc]
  have hr : Spec.map (CommRingCat.ofHom r.toRingHom) ≫ k = v := by
    rw [right_spec, Category.assoc, ← pullback.condition]
  have hn := sheafQuotientTest_commonRelation (B := T) β p i hi v hv l hl N e he
    k hk r hr N' e' he'
  have hleft := ambientClassifyingMap_natural (B := T) b N hκ l
  have hright := ambientClassifyingMap_natural (B := T) b N' hκ r
  rw [left_spec, Category.assoc] at hleft
  rw [right_spec, Category.assoc] at hright
  exact hleft.symm.trans ((congrArg (fun Q ↦ ambientClassifyingMap (A := T) b Q hκ) hn).trans
    hright)

/-- Classifications of one original global quotient agree across arbitrary affine covers. -/
theorem sheafQuotientClassifying_eq_of_covers
    (C D : X.AffineOpenCover.{u}) [∀ j, Algebra R (C.X j)] [∀ k, Algebra R (D.X k)]
    (hC : ∀ j, C.f j ≫ β = Spec.algebraMap R (C.X j))
    (hD : ∀ k, D.f k ≫ β = Spec.algebraMap R (D.X k))
    (N : ∀ j, Module.Grassmannian (C.X j) ((C.X j) ⊗[R] M) d)
    (N' : ∀ k, Module.Grassmannian (D.X k) ((D.X k) ⊗[R] M) d)
    (e : ∀ j, grassmannianQuotientSheaf (N j) ≅ (Scheme.Modules.pullback (C.f j)).obj P)
    (e' : ∀ k, grassmannianQuotientSheaf (N' k) ≅ (Scheme.Modules.pullback (D.f k)).obj P)
    (he : ∀ j, grassmannianQuotientSheafMap (N j) ≫ (e j).hom =
      sheafQuotientTestMap β p (C.f j) (hC j))
    (he' : ∀ k, grassmannianQuotientSheafMap (N' k) ≫ (e' k).hom =
      sheafQuotientTestMap β p (D.f k) (hD k))
    (f g : X ⟶ ambientGrassmannianScheme R M κ d)
    (hf : ∀ j, C.f j ≫ f = ambientClassifyingMap b (N j) hκ)
    (hg : ∀ k, D.f k ≫ g = ambientClassifyingMap b (N' k) hκ) : f = g := by
  apply C.openCover.hom_ext
  intro j
  apply (show (Spec (C.X j)).OpenCover from D.openCover.pullback₁ (C.f j)).hom_ext
  intro k
  change pullback.fst (C.f j) (D.f k) ≫ C.f j ≫ f =
    pullback.fst (C.f j) (D.f k) ≫ C.f j ≫ g
  rw [pullback.condition_assoc g, hf j, hg k]
  exact sheafQuotientClassifying_overlap b hκ β p (C.f j) (hC j) (D.f k) (hD k)
    (N j) (N' k) (e j) (e' k) (he j) (he' k)

end FLT.Mazur.GrassmannianChart
