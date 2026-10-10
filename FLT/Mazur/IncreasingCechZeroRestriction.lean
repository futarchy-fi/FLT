/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IncreasingCechScalars

/-!
# Actual degree-zero chart comparison

Restriction to increasing tuples is an isomorphism in degree zero. Signed
sorting is its inverse, and both maps retain coefficient multiplication.
They identify the actual zero-cycle kernels, not just abstract cohomology.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.IncreasingCechScalars
open IncreasingCechComplex CechSortingMaps CechSheafHZero FCurve

universe u
variable {X : Scheme.{u}} {ι : Type u} [LinearOrder ι]
  (M : X.Modules) (U : ι → X.Opens)

/-- The actual signed sorting map respects coefficient multiplication. -/
def linearSorting (n : ℕ) :
    Term U (moduleAbelianSheaf M) n →ₗ[Γ(X, ⊤)] (C U (moduleAbelianSheaf M)).X n where
  toFun := (sorting U (moduleAbelianSheaf M)).f n
  map_add' := map_add _
  map_smul' r x := ConcreteCategory.congr_hom
    (HomologicalComplex.congr_hom (sorting_naturality U (moduleMultiply M r)) n) x

/-- Restriction after sorting is the identity on every actual increasing term. -/
lemma linearRestriction_linearSorting (n : ℕ) :
    (linearRestriction M U n).comp (linearSorting M U n) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  exact ConcreteCategory.congr_hom
    (HomologicalComplex.congr_hom (sorting_restriction U (moduleAbelianSheaf M)) n) x

/-- All singleton tuples are increasing, so restriction in degree zero is injective. -/
lemma linearRestriction_zero_injective : Function.Injective (linearRestriction M U 0) := by
  intro x y h
  apply (termEquiv U (moduleAbelianSheaf M) 0).injective
  funext a
  have ha : StrictMono a := by
    intro i j hij
    omega
  exact congrFun h ⟨a, ha⟩

/-- The degree-zero comparison uses the original chart restrictions and signed sorting. -/
def zeroRestrictionEquiv :
    (C U (moduleAbelianSheaf M)).X 0 ≃ₗ[Γ(X, ⊤)] Term U (moduleAbelianSheaf M) 0 :=
  LinearEquiv.ofLinearMap (linearRestriction M U 0) (linearSorting M U 0)
    (linearRestriction_linearSorting M U 0) (by
      apply LinearMap.ext
      intro x
      apply linearRestriction_zero_injective M U
      exact LinearMap.congr_fun (linearRestriction_linearSorting M U 0)
        (linearRestriction M U 0 x))

/-- Sorting commutes with the actual differentials. -/
lemma linearSorting_differential (n : ℕ) :
    (finiteCechDifferential M U n (n + 1)).comp (linearSorting M U n) =
      (linearSorting M U (n + 1)).comp (linearDifferential M U n) := by
  apply LinearMap.ext
  intro x
  have h := ConcreteCategory.congr_hom
    ((sorting U (moduleAbelianSheaf M)).comm n (n + 1)) x
  change (C U (moduleAbelianSheaf M)).d n (n + 1)
      ((sorting U (moduleAbelianSheaf M)).f n x) =
    (sorting U (moduleAbelianSheaf M)).f (n + 1)
      ((complex U (moduleAbelianSheaf M)).d n (n + 1) x) at h
  have hd : (complex U (moduleAbelianSheaf M)).d n (n + 1) =
      AddCommGrpCat.ofHom (differential U (moduleAbelianSheaf M) n) := by
    simp only [complex, CochainComplex.of_d]
  rw [hd] at h
  exact h

/-- Vanishing of the full degree-zero differential is detected by increasing tuples. -/
lemma zeroRestriction_mem_ker (x : (C U (moduleAbelianSheaf M)).X 0) :
    linearRestriction M U 0 x ∈ (linearDifferential M U 0).ker ↔
      x ∈ (finiteCechDifferential M U 0 1).ker := by
  constructor
  · intro hx
    have h := LinearMap.congr_fun (linearSorting_differential M U 0)
      (linearRestriction M U 0 x)
    have hi := (zeroRestrictionEquiv M U).left_inv x
    change linearSorting M U 0 (linearRestriction M U 0 x) = x at hi
    change finiteCechDifferential M U 0 1 x = 0
    simpa only [LinearMap.comp_apply, hi, LinearMap.mem_ker.mp hx, map_zero] using h
  · intro hx
    have h := restrict_differential U (moduleAbelianSheaf M) 0 x
    change _ = linearDifferential M U 0 (linearRestriction M U 0 x) at h
    rw [show (C U (moduleAbelianSheaf M)).d 0 1 x = 0 from hx, map_zero, map_zero] at h
    exact h.symm

/-- The actual full and bounded zero-cycle kernels agree linearly. -/
def zeroKernelRestrictionEquiv :
    (finiteCechDifferential M U 0 1).ker ≃ₗ[Γ(X, ⊤)] (linearDifferential M U 0).ker :=
  (zeroRestrictionEquiv M U).submoduleMap (finiteCechDifferential M U 0 1).ker |>.trans
    (LinearEquiv.ofEq _ _ (by
      rw [Submodule.map_equiv_eq_comap_symm]
      ext x
      have h := (zeroRestriction_mem_ker M U ((zeroRestrictionEquiv M U).symm x)).symm
      change _ ↔ (zeroRestrictionEquiv M U) ((zeroRestrictionEquiv M U).symm x) ∈ _ at h
      change (zeroRestrictionEquiv M U).symm x ∈
        (finiteCechDifferential M U 0 1).ker ↔ x ∈ (linearDifferential M U 0).ker
      simpa only [LinearEquiv.apply_symm_apply] using h))

end FLT.Mazur.IncreasingCechScalars
