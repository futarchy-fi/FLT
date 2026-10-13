/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SpecGenericFlatOpen
public import FLT.Mazur.AffineBaseSectionFunctor

/-!
# Generic flatness with the original affine source retained

The section-algebra construction gives a nonzero coefficient in the original
domain base. The resulting actual pullback of the original affine source is
flat. Its local finite presentation and surjectivity are retained, rather than
replaced by properties of an unrelated presentation scheme.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.AffineGenericFlatOpen
open Approximation
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {X : Scheme}
  (g : X ⟶ Spec (.of R)) [IsAffine X] [LocallyOfFinitePresentation g]
local instance : IsAffine (Over.mk g).left := inferInstanceAs (IsAffine X)
local instance : LocallyOfFinitePresentation (Over.mk g).hom :=
  inferInstanceAs (LocallyOfFinitePresentation g)
local notation "B" => affineBaseSections R (Over.mk g)
local instance : Algebra.FiniteType R B := by
  let _ := affineBaseSections_finitePresentation R (Over.mk g)
  infer_instance

/-- The denominator belongs to the original coefficient base, not the source algebra. -/
def coefficient : R := SpecGenericFlatOpen.coefficient R B

theorem coefficient_ne_zero : coefficient g ≠ 0 :=
  SpecGenericFlatOpen.coefficient_ne_zero R B

/-- A dense principal target inclusion constructed from the actual source section algebra. -/
def targetMap : Spec (.of (Localization.Away (coefficient g))) ⟶ Spec (.of R) :=
  SpecGenericFlatOpen.targetMap R B

instance targetMap_isOpenImmersion : IsOpenImmersion (targetMap g) :=
  inferInstanceAs (IsOpenImmersion (SpecGenericFlatOpen.targetMap R B))

instance targetMap_isDominant : IsDominant (targetMap g) :=
  inferInstanceAs (IsDominant (SpecGenericFlatOpen.targetMap R B))

/-- Generic flatness holds for the full original-source pullback. -/
instance projection_flat : Flat (pullback.fst (targetMap g) g) := by
  let v := Spec.map (CommRingCat.ofHom (algebraMap R B))
  have hv : X.isoSpec.hom ≫ v = g :=
    affineBaseSectionsSpecIso_over R (Over.mk g)
  let e := pullback.map (targetMap g) g (targetMap g) v
    (𝟙 _) X.isoSpec.hom (𝟙 _) (by simp) (by simpa using hv.symm)
  let _ : IsIso e := inferInstanceAs (IsIso (pullback.map _ _ _ _ _ _ _ _ _))
  let _ : Flat (pullback.fst (targetMap g) v) :=
    SpecGenericFlatOpen.projection_flat R B
  have he : pullback.fst (targetMap g) g = e ≫ pullback.fst (targetMap g) v := by
    simp only [e, pullback.map, pullback.lift_fst, Category.comp_id]
  rw [he]
  infer_instance

/-- Finite presentation survives on the whole constructed source. -/
instance projection_locallyOfFinitePresentation :
    LocallyOfFinitePresentation (pullback.fst (targetMap g) g) := inferInstance

/-- No source preimages are removed, so an originally surjective map stays surjective. -/
instance projection_surjective [Surjective g] :
    Surjective (pullback.fst (targetMap g) g) := inferInstance

end FLT.Mazur.AffineGenericFlatOpen
