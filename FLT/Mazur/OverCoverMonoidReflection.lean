/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OverDirectedCoverGluing
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.CategoryTheory.Monoidal.Grp

/-!
# Monoid morphisms are detected on a base open cover

The multiplication and identity equations descend on the original relative
objects. No choice of a replacement group law is involved.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.OverDirectedCoverGluing
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (C : S.OpenCover) {G H : Over S} [MonObj G] [MonObj H]
  (f : G ⟶ H)

/-- The actual local monoid-homomorphism conditions imply the global ones. -/
theorem isMonHom_of_cover
    (h : ∀ i, let _ : MonObj ((Over.pullback (C.f i)).obj G) := Functor.monObjObj _
      let _ : MonObj ((Over.pullback (C.f i)).obj H) := Functor.monObjObj _
      IsMonHom ((Over.pullback (C.f i)).map f)) : IsMonHom f where
  one_hom := by
    apply hom_ext C
    intro i
    let F := Over.pullback (C.f i)
    let _ : MonObj (F.obj G) := Functor.monObjObj _
    let _ : MonObj (F.obj H) := Functor.monObjObj _
    let _ := h i
    apply (cancel_epi (Functor.LaxMonoidal.ε F)).mp
    rw [Functor.map_comp, ← Category.assoc]
    exact IsMonHom.one_hom (F.map f)
  mul_hom := by
    apply hom_ext C
    intro i
    let F := Over.pullback (C.f i)
    let _ : MonObj (F.obj G) := Functor.monObjObj _
    let _ : MonObj (F.obj H) := Functor.monObjObj _
    let _ := h i
    apply (cancel_epi (Functor.LaxMonoidal.μ F G G)).mp
    rw [Functor.map_comp, Functor.map_comp, ← Category.assoc,
      ← Category.assoc, ← Functor.LaxMonoidal.μ_natural]
    have hm := IsMonHom.mul_hom (F.map f)
    change (Functor.LaxMonoidal.μ F G G ≫ F.map μ[G]) ≫ F.map f =
      (F.map f ⊗ₘ F.map f) ≫ (Functor.LaxMonoidal.μ F H H ≫ F.map μ[H]) at hm
    simpa only [Category.assoc] using hm

end FLT.Mazur.OverDirectedCoverGluing
