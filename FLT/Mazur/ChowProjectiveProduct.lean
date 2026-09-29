/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ChowChartData
public import FLT.Mazur.ProjectiveSpaceProper

/-!
# The finite projective product for Chow chart data

Finite relative products of proper schemes are constructed by iterated
pullbacks, starting with the base for the empty family. The construction
includes its universal maps and their uniqueness. Applied to the projective
spaces of the affine charts, it gives the common-open tuple over the field.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.Chow

/-- A relative product with its universal property and a proper structure map. -/
structure ProperRelativeProduct {ι : Type*} (S : Scheme.{u}) (Y : ι → Scheme.{u})
    (p : ∀ i, Y i ⟶ S) where
  /-- The scheme underlying the product. -/
  obj : Scheme.{u}
  /-- Its structure morphism to the base. -/
  base : obj ⟶ S
  proper : IsProper base
  /-- The coordinate projections. -/
  π : ∀ i, obj ⟶ Y i
  π_base : ∀ i, π i ≫ p i = base
  /-- The universal map for a family of morphisms over the same base map. -/
  lift : ∀ {T : Scheme.{u}} (b : T ⟶ S) (g : ∀ i, T ⟶ Y i),
    (∀ i, g i ≫ p i = b) → (T ⟶ obj)
  lift_base : ∀ {T : Scheme.{u}} (b : T ⟶ S) (g : ∀ i, T ⟶ Y i)
    (w : ∀ i, g i ≫ p i = b), lift b g w ≫ base = b
  lift_π : ∀ {T : Scheme.{u}} (b : T ⟶ S) (g : ∀ i, T ⟶ Y i)
    (w : ∀ i, g i ≫ p i = b) (i), lift b g w ≫ π i = g i
  hom_ext : ∀ {T : Scheme.{u}} (r s : T ⟶ obj),
    r ≫ base = s ≫ base → (∀ i, r ≫ π i = s ≫ π i) → r = s

/-- The empty product is the base, and adjoining a factor is a pullback. -/
def finProperProduct (S : Scheme.{u}) : (n : ℕ) → (Y : Fin n → Scheme.{u}) →
    (p : ∀ i, Y i ⟶ S) → (∀ i, IsProper (p i)) → ProperRelativeProduct S Y p
  | 0, _, _, _ =>
    { obj := S
      base := 𝟙 S
      proper := inferInstance
      π := fun i ↦ Fin.elim0 i
      π_base := fun i ↦ Fin.elim0 i
      lift := fun b _ _ ↦ b
      lift_base := fun b _ _ ↦ Category.comp_id b
      lift_π := fun _ _ _ i ↦ Fin.elim0 i
      hom_ext := fun r s h _ ↦ by simpa using h }
  | n + 1, Y, p, hp => by
    let Q := finProperProduct S n (fun i ↦ Y i.succ) (fun i ↦ p i.succ)
      (fun i ↦ hp i.succ)
    let := Q.proper
    let := hp 0
    refine
      { obj := pullback (p 0) Q.base
        base := pullback.fst (p 0) Q.base ≫ p 0
        proper := inferInstance
        π := Fin.cases (pullback.fst _ _) (fun i ↦ pullback.snd _ _ ≫ Q.π i)
        π_base := ?_
        lift := fun b g w ↦ pullback.lift (g 0)
          (Q.lift b (fun i ↦ g i.succ) (fun i ↦ w i.succ))
          ((w 0).trans (Q.lift_base b _ _).symm)
        lift_base := ?_
        lift_π := ?_
        hom_ext := ?_ }
    · intro i
      refine Fin.cases rfl (fun j ↦ ?_) i
      rw [Fin.cases_succ, Category.assoc, Q.π_base, pullback.condition]
    · intro T b g w
      rw [← Category.assoc, pullback.lift_fst, w 0]
    · intro T b g w i
      refine Fin.cases (pullback.lift_fst _ _ _) (fun j ↦ ?_) i
      rw [Fin.cases_succ, ← Category.assoc, pullback.lift_snd, Q.lift_π]
    · intro T r s hb hπ
      apply pullback.hom_ext
      · exact hπ 0
      · apply Q.hom_ext
        · simpa only [Category.assoc, ← pullback.condition] using hb
        · intro i
          simpa only [Fin.cases_succ, Category.assoc] using hπ i.succ

/-- For an empty index type, the constructed universal property gives the base. -/
def ProperRelativeProduct.emptyIso {ι : Type*} [IsEmpty ι] {S : Scheme.{u}}
    {Y : ι → Scheme.{u}} {p : ∀ i, Y i ⟶ S} (Q : ProperRelativeProduct S Y p) :
    Q.obj ≅ S where
  hom := Q.base
  inv := Q.lift (𝟙 S) (fun i ↦ isEmptyElim i) (fun i ↦ isEmptyElim i)
  hom_inv_id := by
    apply Q.hom_ext
    · simp only [Category.assoc, Q.lift_base, Category.comp_id, Category.id_comp]
    · exact fun i ↦ isEmptyElim i
  inv_hom_id := Q.lift_base _ _ _

namespace ChartData

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)} (D : ChartData f)

/-- Enumerate the actual chart projective spaces and construct their relative product. -/
def projectiveProductData :=
  finProperProduct (Spec (.of k)) (Fintype.card D.Index)
    (fun j ↦ ProjectiveSpace.space k
      (Fin (D.dimension ((Fintype.equivFin D.Index).symm j) + 1)))
    (fun j ↦ ProjectiveSpace.baseProjection k
      (Fin (D.dimension ((Fintype.equivFin D.Index).symm j) + 1)))
    (fun _ ↦ inferInstance)

/-- The product of the chart projective spaces over the original field spectrum. -/
def projectiveProduct : Scheme.{u} := D.projectiveProductData.obj

/-- The structure map of the finite relative projective product. -/
def projectiveProductProjection : D.projectiveProduct ⟶ Spec (.of k) :=
  D.projectiveProductData.base

instance projectiveProductProjection_isProper : IsProper D.projectiveProductProjection :=
  D.projectiveProductData.proper

/-- The projection to a chart's original projective space. -/
def projectiveProductπ (i : D.Index) :
    D.projectiveProduct ⟶ ProjectiveSpace.space k (Fin (D.dimension i + 1)) :=
  D.projectiveProductData.π (Fintype.equivFin D.Index i) ≫ eqToHom (by simp)

/-- Every coordinate projection is over the original base. -/
@[reassoc (attr := simp)]
lemma projectiveProductπ_baseProjection (i : D.Index) :
    D.projectiveProductπ i ≫ ProjectiveSpace.baseProjection k (Fin (D.dimension i + 1)) =
      D.projectiveProductProjection := by
  rw [projectiveProductπ, Category.assoc, ← eqToHom_naturality
    (fun i ↦ ProjectiveSpace.baseProjection k (Fin (D.dimension i + 1)))
    ((Fintype.equivFin D.Index).symm_apply_apply i)]
  simpa only [eqToHom_refl, Category.comp_id, projectiveProductProjection,
    projectiveProduct] using
    D.projectiveProductData.π_base (Fintype.equivFin D.Index i)

/-- The universal tuple into the finite projective product. -/
def projectiveProductLift {T : Scheme.{u}} (b : T ⟶ Spec (.of k))
    (g : ∀ i, T ⟶ ProjectiveSpace.space k (Fin (D.dimension i + 1)))
    (w : ∀ i, g i ≫ ProjectiveSpace.baseProjection k (Fin (D.dimension i + 1)) = b) :
    T ⟶ D.projectiveProduct :=
  D.projectiveProductData.lift b (fun j ↦ g ((Fintype.equivFin D.Index).symm j))
    (fun j ↦ w ((Fintype.equivFin D.Index).symm j))

@[reassoc (attr := simp)]
lemma projectiveProductLift_projection {T : Scheme.{u}} (b : T ⟶ Spec (.of k))
    (g : ∀ i, T ⟶ ProjectiveSpace.space k (Fin (D.dimension i + 1)))
    (w : ∀ i, g i ≫ ProjectiveSpace.baseProjection k (Fin (D.dimension i + 1)) = b) :
    D.projectiveProductLift b g w ≫ D.projectiveProductProjection = b :=
  D.projectiveProductData.lift_base _ _ _

@[reassoc (attr := simp)]
lemma projectiveProductLift_π {T : Scheme.{u}} (b : T ⟶ Spec (.of k))
    (g : ∀ i, T ⟶ ProjectiveSpace.space k (Fin (D.dimension i + 1)))
    (w : ∀ i, g i ≫ ProjectiveSpace.baseProjection k (Fin (D.dimension i + 1)) = b)
    (i : D.Index) : D.projectiveProductLift b g w ≫ D.projectiveProductπ i = g i := by
  unfold projectiveProductLift projectiveProductπ
  rw [← Category.assoc, ProperRelativeProduct.lift_π]
  simp

/-- The base and coordinate maps determine a map to the product uniquely. -/
@[ext]
lemma projectiveProduct_hom_ext {T : Scheme.{u}} (r s : T ⟶ D.projectiveProduct)
    (hb : r ≫ D.projectiveProductProjection = s ≫ D.projectiveProductProjection)
    (hπ : ∀ i, r ≫ D.projectiveProductπ i = s ≫ D.projectiveProductπ i) : r = s := by
  apply D.projectiveProductData.hom_ext r s hb
  intro j
  have h := hπ ((Fintype.equivFin D.Index).symm j)
  simp only [projectiveProductπ, ← Category.assoc, cancel_mono] at h
  rw [Equiv.apply_symm_apply] at h
  exact h

/-- An empty family has the field spectrum as its relative product. -/
def projectiveProductEmptyIso [IsEmpty D.Index] : D.projectiveProduct ≅ Spec (.of k) := by
  have : IsEmpty (Fin (Fintype.card D.Index)) := by
    simpa only [Fintype.card_eq_zero] using (inferInstance : IsEmpty (Fin 0))
  exact D.projectiveProductData.emptyIso

/-- The common open maps to the product by all its projective component maps. -/
def commonToProduct : D.common.toScheme ⟶ D.projectiveProduct :=
  D.projectiveProductLift (D.common.ι ≫ f) D.commonToProjective
    D.commonToProjective_baseProjection

/-- The tuple has exactly the prescribed chart components. -/
@[reassoc (attr := simp)]
lemma commonToProduct_π (i : D.Index) :
    D.commonToProduct ≫ D.projectiveProductπ i = D.commonToProjective i :=
  D.projectiveProductLift_π _ _ _ i

/-- The tuple retains the structure morphism of the original common open. -/
@[reassoc (attr := simp)]
lemma commonToProduct_projection :
    D.commonToProduct ≫ D.projectiveProductProjection = D.common.ι ≫ f :=
  D.projectiveProductLift_projection _ _ _

end ChartData

end FLT.Mazur.Chow
