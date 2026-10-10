/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealPowerReesSections
public import FLT.Mazur.ReesModuleMap

/-!
# Restriction maps for affine ideal-power Rees modules

The local Rees modules restrict through the actual structure-sheaf and
coefficient-sheaf maps. These semilinear maps compose and preserve identity,
so the finite affine modules have the required restriction coherence.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.IdealPowerRees

variable {X : Scheme.{u}}
  (I : X.IdealSheafData) (M : X.Modules)
  {U V W : X.affineOpens}

/-- Actual structure-sheaf restriction on the local Rees algebras. -/
def ringRestriction (h : U.1 ≤ V.1) : reesAlgebra (I.ideal V) →+* reesAlgebra (I.ideal U) :=
  Rees.algebraMap _ _ (X.presheaf.map (homOfLE h).op).hom (I.map_ideal h).le

/-- Actual coefficient-sheaf restriction with its original scalar change. -/
def sectionRestriction (h : U.1 ≤ V.1) :
    Γ(M, V.1) →ₛₗ[(X.presheaf.map (homOfLE h).op).hom] Γ(M, U.1) where
  toFun := M.presheaf.map (homOfLE h).op
  map_add' := map_add _
  map_smul' := M.map_smul (homOfLE h)

/-- Actual restriction preserves every ideal-power multiple. -/
lemma sectionRestriction_mem (h : U.1 ≤ V.1) (n : ℕ) (x : Γ(M, V.1))
    (hx : x ∈ (I.ideal V) ^ n • (⊤ : Submodule Γ(X, V.1) Γ(M, V.1))) :
    sectionRestriction M h x ∈ (I.ideal U) ^ n • (⊤ : Submodule Γ(X, U.1) Γ(M, U.1)) := by
  refine Submodule.smul_induction_on hx (fun r hr m _ ↦ ?_) (fun x y hx hy ↦ ?_)
  · rw [map_smulₛₗ]
    exact Submodule.smul_mem_smul
      (Rees.map_pow_le _ _ _ (I.map_ideal h).le n (Ideal.mem_map_of_mem _ hr)) (by trivial)
  · rw [map_add]
    exact Submodule.add_mem _ hx hy

/-- The affine Rees modules restrict semilinearly over the actual local Rees rings. -/
def moduleRestriction (h : U.1 ≤ V.1) :
    affineModule I M V →ₛₗ[ringRestriction I h] affineModule I M U :=
  Rees.moduleMap (sectionRestriction M h) _ _ (I.map_ideal h).le
    ((I.ideal V).stableFiltration ⊤) ((I.ideal U).stableFiltration ⊤)
    (sectionRestriction_mem I M h)

/-- Restriction on every polynomial coefficient is the original sheaf restriction. -/
lemma moduleRestriction_coeff (h : U.1 ≤ V.1) (s : affineModule I M V) (n : ℕ) :
    (moduleRestriction I M h s).val.coeff n =
      M.presheaf.map (homOfLE h).op (s.val.coeff n) := rfl

/-- Identity restriction fixes the full affine Rees module. -/
lemma moduleRestriction_id (s : affineModule I M U) :
    moduleRestriction I M le_rfl s = s := by
  apply Subtype.ext
  ext n
  exact ConcreteCategory.congr_hom (M.presheaf.map_id (.op U.1)) (s.val.coeff n)

/-- The original affine restrictions compose in every degree at once. -/
lemma moduleRestriction_comp (h : U.1 ≤ V.1) (k : V.1 ≤ W.1) (s : affineModule I M W) :
    moduleRestriction I M h (moduleRestriction I M k s) =
      moduleRestriction I M (h.trans k) s := by
  apply Subtype.ext
  ext n
  exact (ConcreteCategory.congr_hom
    (M.presheaf.map_comp (homOfLE k).op (homOfLE h).op) (s.val.coeff n)).symm

end FLT.Mazur.IdealPowerRees
