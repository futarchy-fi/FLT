/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineGenericFlatOpen
public import FLT.Mazur.SpecGenericFiniteOpen
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# Generic finiteness of the full original affine source

The existing generic flatness coefficient also makes a quasi-finite source
finite. The source is the actual Cartesian pullback; every branch is retained.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.AffineGenericFlatOpen
open Approximation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [IsDomain R] {X : Scheme}
  (g : X ⟶ Spec (.of R)) [IsAffine X] [LocallyOfFinitePresentation g]
  [LocallyQuasiFinite g]
local instance : IsAffine (Over.mk g).left := inferInstanceAs (IsAffine X)
local instance : LocallyOfFinitePresentation (Over.mk g).hom :=
  inferInstanceAs (LocallyOfFinitePresentation g)
local notation "B" => affineBaseSections R (Over.mk g)

omit [IsDomain R] [LocallyOfFinitePresentation g] in
/-- The original section algebra inherits quasi-finiteness from the original morphism. -/
theorem sectionAlgebra_quasiFinite : Algebra.QuasiFinite R B := by
  let v := Spec.map (CommRingCat.ofHom (algebraMap R B))
  have hv : X.isoSpec.hom ≫ v = g := affineBaseSectionsSpecIso_over R (Over.mk g)
  have he : v = X.isoSpec.inv ≫ g := by rw [← hv, Iso.inv_hom_id_assoc]
  have hvq : LocallyQuasiFinite v := by rw [he]; infer_instance
  exact (HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite)).mp hvq

/-- The same nonzero scalar makes the full original affine pullback finite. -/
instance projection_isFinite : IsFinite (pullback.fst (targetMap g) g) := by
  let _ := sectionAlgebra_quasiFinite g
  let _ := affineBaseSections_finitePresentation R (Over.mk g)
  let v := Spec.map (CommRingCat.ofHom (algebraMap R B))
  have hv : X.isoSpec.hom ≫ v = g := affineBaseSectionsSpecIso_over R (Over.mk g)
  let e := pullback.map (targetMap g) g (targetMap g) v
    (𝟙 _) X.isoSpec.hom (𝟙 _) (by simp) (by simpa using hv.symm)
  let _ : IsIso e := inferInstanceAs (IsIso (pullback.map _ _ _ _ _ _ _ _ _))
  let _ : IsFinite (pullback.fst (targetMap g) v) :=
    SpecGenericFlatOpen.projection_isFinite R B
  have he : pullback.fst (targetMap g) g = e ≫ pullback.fst (targetMap g) v := by
    simp only [e, pullback.map, pullback.lift_fst, Category.comp_id]
  rw [he]
  infer_instance

end FLT.Mazur.AffineGenericFlatOpen
