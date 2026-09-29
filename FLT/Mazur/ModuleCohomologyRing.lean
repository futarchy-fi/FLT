/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ModuleCohomologyExact
public import FLT.Mazur.ModuleStalkExact
public import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-! # Base-ring cohomology and finite quotient arguments -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace FLT.Mazur.FCurve

local instance ringCohomologyHasExt (X : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  HasExt.standard _

variable {X : Scheme.{u}} {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤))

/-- Module cohomology retaining the specified base-ring action in its type. -/
def ModuleRingH (_ρ : R →+* Γ(X, ⊤)) (M : X.Modules) (n : ℕ) : Type (u + 1) :=
  ModuleH M n

instance moduleRingHAddCommGroup (M : X.Modules) (n : ℕ) :
    AddCommGroup (ModuleRingH ρ M n) :=
  inferInstanceAs (AddCommGroup (ModuleH M n))

instance moduleRingHModule (M : X.Modules) (n : ℕ) : Module R (ModuleRingH ρ M n) :=
  Module.compHom (ModuleH M n) ρ

/-- Actual cohomology, with scalars restricted along a specified base-ring map. -/
def moduleRingHFunctor (n : ℕ) : X.Modules ⥤ ModuleCat.{u + 1} R where
  obj M := ModuleCat.of R (ModuleRingH ρ M n)
  map {M N} g := ModuleCat.ofHom
    { toFun := moduleHMap g n
      map_add' := (moduleHMap g n).map_add
      map_smul' := fun r x ↦ (moduleHMap g n).map_smul (ρ r) x }
  map_id M := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact LinearMap.congr_fun (moduleHMap_id M n) x
  map_comp g h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact LinearMap.congr_fun (moduleHMap_comp g h n) x

instance moduleRingHFunctor_additive (n : ℕ) : (moduleRingHFunctor ρ n).Additive where
  map_add {M N} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact Sheaf.H.map_add_apply
      ((SheafOfModules.toSheaf X.ringCatSheaf).map f)
      ((SheafOfModules.toSheaf X.ringCatSheaf).map g) x

/-- Cohomology of a finite coproduct is finite when each summand's cohomology is finite. -/
theorem moduleRingH_finite_coproduct {κ : Type u} [Finite κ]
    (M : κ → X.Modules) (n : ℕ)
    [∀ i, Module.Finite R ((moduleRingHFunctor ρ n).obj (M i))] :
    Module.Finite R ((moduleRingHFunctor ρ n).obj (∐ M)) := by
  let G := moduleRingHFunctor ρ n
  let e := PreservesCoproduct.iso G M ≪≫
    (biproduct.isoCoproduct (fun i ↦ G.obj (M i))).symm ≪≫
      IsLimit.conePointUniqueUpToIso (biproduct.isLimit (fun i ↦ G.obj (M i)))
        (ModuleCat.HasLimit.productLimitCone.{u, u + 1, u} (fun i : κ ↦ G.obj (M i))).isLimit
  let _finiteProduct :
      Module.Finite R
        (ModuleCat.HasLimit.productLimitCone.{u, u + 1, u}
          (fun i : κ ↦ G.obj (M i))).cone.pt :=
    inferInstanceAs (Module.Finite R (∀ i, G.obj (M i)))
  exact Module.Finite.equiv e.symm.toLinearEquiv

/-- In a short exact sequence, finite middle cohomology and finite next kernel
cohomology imply finite quotient cohomology over a Noetherian base ring. -/
theorem moduleRingH_finite_right [IsNoetherianRing R]
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (n : ℕ)
    [Module.Finite R ((moduleRingHFunctor ρ n).obj S.X₂)]
    [Module.Finite R ((moduleRingHFunctor ρ (n + 1)).obj S.X₁)] :
    Module.Finite R ((moduleRingHFunctor ρ n).obj S.X₃) := by
  have hAb : (moduleAbelianComplex S).ShortExact :=
    CoherentDevissage.moduleToSheaf_shortExact hS
  let δ : (moduleRingHFunctor ρ n).obj S.X₃ →ₗ[R]
      (moduleRingHFunctor ρ (n + 1)).obj S.X₁ :=
    { toFun := moduleHConnecting S hAb n
      map_add' := (moduleHConnecting S hAb n).map_add
      map_smul' := fun r x ↦ (moduleHConnecting S hAb n).map_smul (ρ r) x }
  exact moduleFinite_of_exact_pair ((moduleRingHFunctor ρ n).map S.g).hom δ
    ((ShortComplex.ab_exact_iff_function_exact _).mp
      (Sheaf.H.longSequence_exact₃' hAb n (n + 1) rfl))

end FLT.Mazur.FCurve
