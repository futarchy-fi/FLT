/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OverDirectedCoverGluing

/-!
# Gluing isomorphisms of subobjects on a directed base cover

Monomorphisms into the base force refinement compatibility. Thus local
isomorphisms of the actual pullbacks give an isomorphism of the original subobjects.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.OverDirectedCoverGluing
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (C : S.OpenCover) [Category* C.I₀] [C.LocallyDirected]
  {X Y : Over S}

/-- Maps into a subobject automatically agree under the actual base refinements. -/
theorem compatible_of_mono [Mono Y.hom]
    (a : ∀ i, (Over.pullback (C.f i)).obj X ⟶ (Over.pullback (C.f i)).obj Y) :
    Compatible C a := by
  have hw (i : C.I₀) : (a i).left ≫ pullback.fst Y.hom (C.f i) ≫ Y.hom =
      pullback.fst X.hom (C.f i) ≫ X.hom := by
    rw [pullback.condition, ← Category.assoc]
    change ((a i).left ≫ ((Over.pullback (C.f i)).obj Y).hom) ≫ _ = _
    rw [(a i).w]
    exact pullback.condition.symm
  intro i j h
  apply (cancel_mono Y.hom).mp
  simp only [Category.assoc, hw]
  rw [← Category.assoc]
  exact congrArg (fun k ↦ k ≫ X.hom) (Scheme.Cover.trans_map (C.pullback₁ X.hom) h)

variable [Mono X.hom] [Mono Y.hom]
  (a : ∀ i, (Over.pullback (C.f i)).obj X ≅ (Over.pullback (C.f i)).obj Y)

attribute [local irreducible] glue

/-- Actual local subobject isomorphisms descend to an original subobject isomorphism. -/
def glueMonoIso : X ≅ Y where
  hom := glue C (X := X) (Y := Y) (fun i ↦ (a i).hom)
    (compatible_of_mono C (X := X) (Y := Y) (fun i ↦ (a i).hom))
  inv := glue C (X := Y) (Y := X) (fun i ↦ (a i).inv)
    (compatible_of_mono C (X := Y) (Y := X) (fun i ↦ (a i).inv))
  hom_inv_id := by
    apply hom_ext C
    intro i
    rw [Functor.map_comp, CategoryTheory.Functor.map_id, glue_map, glue_map, Iso.hom_inv_id]
  inv_hom_id := by
    apply hom_ext C
    intro i
    rw [Functor.map_comp, CategoryTheory.Functor.map_id, glue_map, glue_map, Iso.inv_hom_id]

/-- The descended comparison recovers every prescribed local subobject isomorphism. -/
theorem glueMonoIso_map (i : C.I₀) :
    (Over.pullback (C.f i)).mapIso (glueMonoIso C a) = a i := by
  apply Iso.ext
  exact glue_map C (X := X) (Y := Y) (fun i ↦ (a i).hom)
    (compatible_of_mono C (X := X) (Y := Y) (fun i ↦ (a i).hom)) i

end FLT.Mazur.OverDirectedCoverGluing
