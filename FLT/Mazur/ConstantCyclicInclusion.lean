/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ConstantCyclicGroup

/-!
# The constant cyclic subgroup of the split polygon group

Send each base component to the unit in its Laurent component. The resulting
map respects group operations and has a retraction, hence is a monomorphism.
-/

open CategoryTheory Limits AlgebraicGeometry MonObj MonoidalCategory CartesianMonoidalCategory
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.ConstantCyclicInclusion
universe u
variable (R : Type u) [CommRing R] (n : ℕ) [NeZero n]
local notation "S" => Spec (CommRingCat.of R)
local notation "D" => ConstantCyclicGroup.model S n
local notation "G" => PolygonSplitGroup.model R n
local notation "U" => (𝟙_ (Over S))
local notation "M" => MultiplicativeGroupScheme.gm R

/-- Include the unit section in every Laurent component. -/
def inclusion : D ⟶ G :=
  Sigma.desc fun i ↦ η[M] ≫ PolygonSplitGroup.component R n i

omit [NeZero n] in
/-- The inclusion has the specified identity-section formula. -/
@[reassoc (attr := simp)]
theorem component_inclusion (i : ZMod n) :
    ConstantCyclicGroup.component S n i ≫ inclusion R n =
      η[M] ≫ PolygonSplitGroup.component R n i := by
  simp [inclusion, ConstantCyclicGroup.component]

/-- Forget the multiplicative coordinate and retain the component. -/
def retraction : G ⟶ D :=
  Sigma.desc fun i ↦ toUnit M ≫ ConstantCyclicGroup.component S n i

omit [NeZero n] in
/-- Retraction on each Laurent component is its map to the base. -/
@[reassoc (attr := simp)]
theorem component_retraction (i : ZMod n) :
    PolygonSplitGroup.component R n i ≫ retraction R n =
      toUnit M ≫ ConstantCyclicGroup.component S n i := by
  simp [retraction, PolygonSplitGroup.component]

omit [NeZero n] in
/-- The component retraction is a left inverse to the inclusion. -/
@[reassoc (attr := simp)]
theorem inclusion_retraction : inclusion R n ≫ retraction R n = 𝟙 D := by
  apply Sigma.hom_ext
  intro i
  change ConstantCyclicGroup.component S n i ≫ _ = _
  rw [component_inclusion_assoc, component_retraction]
  simp

instance inclusion_mono : Mono (inclusion R n) :=
  mono_of_mono_fac (inclusion_retraction R n)

instance inclusion_isMonHom : IsMonHom (inclusion R n) where
  one_hom := by
    change ConstantCyclicGroup.identity S n ≫ inclusion R n = PolygonSplitGroup.identity R n
    rw [ConstantCyclicGroup.identity, Category.assoc, component_inclusion]
    simp [PolygonSplitGroup.identity]
  mul_hom := by
    change ConstantCyclicGroup.multiplication S n ≫ inclusion R n =
      (inclusion R n ⊗ₘ inclusion R n) ≫ PolygonSplitGroup.multiplication R n
    apply PolygonSplitGroup.tensor_hom_ext (fun _ : ZMod n ↦ U) (fun _ : ZMod n ↦ U)
    intro i j
    change (ConstantCyclicGroup.component S n i ⊗ₘ ConstantCyclicGroup.component S n j) ≫ _ = _
    rw [ConstantCyclicGroup.component_multiplication_assoc, component_inclusion,
      tensorHom_comp_tensorHom_assoc, component_inclusion, component_inclusion,
      ← tensorHom_comp_tensorHom_assoc, PolygonSplitGroup.component_multiplication]
    rw [MonObj.one_mul_hom_assoc]
    rfl

/-- The inclusion commutes with inversion. -/
@[reassoc]
theorem inclusion_inversion :
    ConstantCyclicGroup.inversion S n ≫ inclusion R n =
      inclusion R n ≫ PolygonSplitGroup.inversion R n := by
  exact GrpObj.inv_hom (inclusion R n)
end FLT.Mazur.ConstantCyclicInclusion
