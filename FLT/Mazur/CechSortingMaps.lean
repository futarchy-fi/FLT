/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CechSortingCoordinates

/-!
# Natural retraction onto increasing Cech tuples

Restriction and integral signed sorting define chain maps. Their composite
on the increasing complex is the identity, naturally in the coefficient sheaf.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace FLT.Mazur.CechSortingMaps

open IncreasingCechComplex CechSortingCoordinates

variable {X : TopCat.{u}} {ι : Type u} [LinearOrder ι]
variable (U : ι → Opens X) (F : TopCat.Sheaf AddCommGrpCat.{u} X)

/-- Integral signed sorting as an additive map on coordinates. -/
def sortingHom (n : ℕ) : Term U F n →+ FullTerm U F n where
  toFun x := signedSort U F n x
  map_zero' := by
    funext a
    simp [signedSort]
  map_add' x y := by
    funext a
    by_cases h : Function.Injective a <;> simp [signedSort, h, map_add, smul_add]

/-- Restrict the full Cech complex to increasing tuples. -/
def restriction : CechSheafHZero.C U F ⟶ complex U F where
  f n := AddCommGrpCat.ofHom
    ((restrict U F n).comp (CechSheafHZero.termEquiv U F n).toAddMonoidHom)
  comm' i j h := by
    obtain rfl : i + 1 = j := h
    simp only [complex, CochainComplex.of_d]
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    exact (restrict_differential U F i x).symm

/-- Extend increasing coordinates by signed sorting, zero on repeated tuples. -/
def sorting : complex U F ⟶ CechSheafHZero.C U F where
  f n := AddCommGrpCat.ofHom
    ((CechSheafHZero.termEquiv U F n).symm.toAddMonoidHom.comp (sortingHom U F n))
  comm' i j h := by
    obtain rfl : i + 1 = j := h
    simp only [complex, CochainComplex.of_d]
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    apply (CechSheafHZero.termEquiv U F (i + 1)).injective
    funext a
    change CechSheafHZero.termEquiv U F (i + 1)
      ((CechSheafHZero.C U F).d i (i + 1)
        ((CechSheafHZero.termEquiv U F i).symm (sortingHom U F i x))) a =
        CechSheafHZero.termEquiv U F (i + 1)
          ((CechSheafHZero.termEquiv U F (i + 1)).symm
            (sortingHom U F (i + 1) (differential U F i x))) a
    rw [full_differential]
    simp only [AddEquiv.apply_symm_apply]
    exact (signedSort_differential U F i x a).symm

/-- Sorting followed by restriction is the identity on the increasing complex. -/
lemma sorting_restriction : sorting U F ≫ restriction U F = 𝟙 (complex U F) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  funext a
  change restrict U F n (CechSheafHZero.termEquiv U F n
    ((CechSheafHZero.termEquiv U F n).symm (sortingHom U F n x))) a = x a
  rw [AddEquiv.apply_symm_apply]
  exact signedSort_increasing U F n x a

variable {F} {G H : TopCat.Sheaf AddCommGrpCat.{u} X}

omit [LinearOrder ι] in
/-- The full term coordinates commute with coefficient morphisms in every degree. -/
lemma termEquiv_naturality (f : F ⟶ G) (n : ℕ)
    (x : (CechSheafHZero.C U F).X n) (a : Fin (n + 1) → ι) :
    CechSheafHZero.termEquiv U G n (((cechComplexFunctor U).map f.hom).f n x) a =
      f.hom.app (op (CechSheafHZero.V U n a)) (CechSheafHZero.termEquiv U F n x a) := by
  rw [CechSheafHZero.termEquiv_apply, CechSheafHZero.termEquiv_apply]
  change G.obj.map _ (Pi.π (fun b : Fin (n + 1) → ι ↦ G.obj.obj (op (∏ᶜ (U ∘ b))))
    a ((Limits.Pi.map (fun b : Fin (n + 1) → ι ↦ f.hom.app (op (∏ᶜ (U ∘ b))))) x)) = _
  erw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply]
  apply ConcreteCategory.congr_hom
  rw [← Category.assoc, Pi.map_π, Category.assoc, f.hom.naturality]

/-- Coefficient morphisms act on increasing coordinates. -/
def coefficientHom (f : F ⟶ G) (n : ℕ) : Term U F n →+ Term U G n where
  toFun x a := f.hom.app (op (CechSheafHZero.V U n a.val)) (x a)
  map_zero' := by ext; exact map_zero _
  map_add' x y := by ext; exact map_add _ _ _

/-- Coefficient morphisms commute with the increasing differential. -/
lemma coefficientHom_differential (f : F ⟶ G) (n : ℕ) (x : Term U F n) :
    coefficientHom U f (n + 1) (differential U F n x) =
      differential U G n (coefficientHom U f n x) := by
  funext a
  change f.hom.app _ (differential U F n x a) = _
  rw [differential_apply, map_sum, differential_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_zsmul]
  congr 1
  exact ConcreteCategory.congr_hom (f.hom.naturality
    (homOfLE (face_le U n a.val k)).op) (x (face a k))

/-- The induced chain map on increasing Cech complexes. -/
def coefficientMap (f : F ⟶ G) : complex U F ⟶ complex U G where
  f n := AddCommGrpCat.ofHom (coefficientHom U f n)
  comm' i j h := by
    obtain rfl : i + 1 = j := h
    simp only [complex, CochainComplex.of_d]
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    exact (coefficientHom_differential U f i x).symm

/-- Restriction is natural in the coefficient sheaf. -/
lemma restriction_naturality (f : F ⟶ G) :
    (cechComplexFunctor U).map f.hom ≫ restriction U G =
      restriction U F ≫ coefficientMap U f := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  funext a
  exact termEquiv_naturality U f n x a.val

/-- Signed sorting is natural on coordinates. -/
lemma sortingHom_naturality (f : F ⟶ G) (n : ℕ) (x : Term U F n)
    (a : Fin (n + 1) → ι) :
    sortingHom U G n (coefficientHom U f n x) a =
      f.hom.app (op (CechSheafHZero.V U n a)) (sortingHom U F n x a) := by
  change signedSort U G n _ a = f.hom.app _ (signedSort U F n x a)
  by_cases h : Function.Injective a
  · rw [signedSort_of_injective U G n _ a h, signedSort_of_injective U F n _ a h,
      map_zsmul]
    congr 1
    exact (ConcreteCategory.congr_hom (f.hom.naturality
      (homOfLE (perm_le U a (Tuple.sort a))).op) (x (sortTuple a h))).symm
  · rw [signedSort_of_not_injective U G n _ a h,
      signedSort_of_not_injective U F n _ a h, map_zero]

/-- The sorting chain map is natural in the coefficient sheaf. -/
lemma sorting_naturality (f : F ⟶ G) :
    coefficientMap U f ≫ sorting U G = sorting U F ≫ (cechComplexFunctor U).map f.hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  apply (CechSheafHZero.termEquiv U G n).injective
  funext a
  change CechSheafHZero.termEquiv U G n
    ((CechSheafHZero.termEquiv U G n).symm (sortingHom U G n (coefficientHom U f n x))) a =
      CechSheafHZero.termEquiv U G n (((cechComplexFunctor U).map f.hom).f n
        ((CechSheafHZero.termEquiv U F n).symm (sortingHom U F n x))) a
  rw [AddEquiv.apply_symm_apply, termEquiv_naturality, AddEquiv.apply_symm_apply]
  exact sortingHom_naturality U f n x a

end FLT.Mazur.CechSortingMaps
