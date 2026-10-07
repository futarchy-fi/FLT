/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineDescentChart

/-!
# Transitions on a common faithfully flat affine refinement

For any family of charts with a common geometric refinement, effective descent
constructs the transition isomorphisms between their pulled-back sheaves.
Their cocycle and compatibility with descended maps are consequences of the
constructed comparison isomorphisms.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} {p : Y ⟶ X} {ι : Type u}
variable (C : ι → Chart p) (T : Chart p) (ρ : ∀ i, (C i).Refinement T)
variable {M N : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable (E : SchemeGeometricDescent.Data p N)
variable [∀ i, ((pullback (C i).cover).obj M).IsQuasicoherent]
variable [((pullback T.cover).obj M).IsQuasicoherent]

/-- Actual transition between two chart sheaves on their common affine refinement. -/
def commonTransition (i j : ι) :
    (pullback (Spec.map (ρ i).base)).obj ((C i).sheaf D) ≅
      (pullback (Spec.map (ρ j).base)).obj ((C j).sheaf D) :=
  (C i).comparison T D (ρ i) ≪≫ ((C j).comparison T D (ρ j)).symm

/-- The transition from a chart to itself is the identity. -/
@[simp]
theorem commonTransition_self (i : ι) : commonTransition C T ρ D i i = Iso.refl _ := by
  simp [commonTransition]

/-- Reversing a transition gives its inverse. -/
theorem commonTransition_symm (i j : ι) :
    commonTransition C T ρ D j i = (commonTransition C T ρ D i j).symm := by
  simp [commonTransition]

/-- The actual transitions satisfy the cocycle on a common affine refinement. -/
@[reassoc]
theorem commonTransition_cocycle (i j k : ι) :
    (commonTransition C T ρ D i j).hom ≫ (commonTransition C T ρ D j k).hom =
      (commonTransition C T ρ D i k).hom := by
  simp [commonTransition]

/-- Each transition is uniquely determined by its comparison to the common chart. -/
theorem commonTransition_unique (i j : ι)
    (f : (pullback (Spec.map (ρ i).base)).obj ((C i).sheaf D) ⟶
      (pullback (Spec.map (ρ j).base)).obj ((C j).sheaf D))
    (hf : f ≫ ((C j).comparison T D (ρ j)).hom = ((C i).comparison T D (ρ i)).hom) :
    f = (commonTransition C T ρ D i j).hom := by
  apply (cancel_mono ((C j).comparison T D (ρ j)).hom).mp
  simpa [commonTransition] using hf

variable [∀ i, ((pullback (C i).cover).obj N).IsQuasicoherent]
variable [((pullback T.cover).obj N).IsQuasicoherent]

/-- Descended chart maps commute with the actual common-refinement transitions. -/
@[reassoc]
theorem commonTransition_naturality (i j : ι) (f : M ⟶ N) (hf : D.MapCompatible p E f) :
    (pullback (Spec.map (ρ i).base)).map ((C i).map D E f hf) ≫
        (commonTransition C T ρ E i j).hom =
      (commonTransition C T ρ D i j).hom ≫
        (pullback (Spec.map (ρ j).base)).map ((C j).map D E f hf) := by
  apply (cancel_mono ((C j).comparison T E (ρ j)).hom).mp
  dsimp only [commonTransition, Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [(C j).comparison_naturality T D E (ρ j) f hf]
  simp only [Iso.inv_hom_id_assoc]
  exact (C i).comparison_naturality T D E (ρ i) f hf

end FLT.Mazur.SchemeAffineDescent
