/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoherentCohomologyFinite
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Euler-characteristic degree for curves

The degree is the difference of h⁰ − h¹ for the sheaf and the structure sheaf.
Additivity follows from the actual cohomology long exact sequence, with finite
cohomology and vanishing H² hypotheses stated explicitly. This module does not
assert the geometric vanishing theorem or the ample-degree criterion.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry

universe u v

namespace FLT.Mazur.FCurve

private theorem sixTerm_finrank {k : Type u} [Field k]
    {A B C D E F : Type v}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup D] [AddCommGroup E] [AddCommGroup F]
    [Module k A] [Module k B] [Module k C] [Module k D] [Module k E] [Module k F]
    [Module.Finite k A] [Module.Finite k B] [Module.Finite k C]
    [Module.Finite k D] [Module.Finite k E]
    (a : A →ₗ[k] B) (b : B →ₗ[k] C) (c : C →ₗ[k] D)
    (d : D →ₗ[k] E) (e : E →ₗ[k] F)
    (ha : Function.Injective a) (he : Function.Surjective e)
    (hab : Function.Exact a b) (hbc : Function.Exact b c)
    (hcd : Function.Exact c d) (hde : Function.Exact d e) :
    Module.finrank k A + Module.finrank k C + Module.finrank k E =
      Module.finrank k B + Module.finrank k D + Module.finrank k F := by
  have h₁ := a.finrank_range_add_finrank_ker
  have h₂ := b.finrank_range_add_finrank_ker
  have h₃ := c.finrank_range_add_finrank_ker
  have h₄ := d.finrank_range_add_finrank_ker
  have h₅ := e.finrank_range_add_finrank_ker
  rw [LinearMap.ker_eq_bot.mpr ha, finrank_bot, add_zero] at h₁
  rw [hab.linearMap_ker_eq] at h₂
  rw [hbc.linearMap_ker_eq] at h₃
  rw [hcd.linearMap_ker_eq] at h₄
  rw [hde.linearMap_ker_eq, LinearMap.range_eq_top.mpr he, finrank_top] at h₅
  omega

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k))

/-- The curve Euler characteristic, with actual scalar sheaf cohomology. -/
def curveEulerCharacteristic (M : X.Modules) : ℤ :=
  (Module.finrank k (ModuleScalarH f M 0) : ℤ) - Module.finrank k (ModuleScalarH f M 1)

/-- Euler-characteristic degree; for an invertible sheaf this is the usual curve degree. -/
def curveSheafDegree (M : X.Modules) : ℤ :=
  curveEulerCharacteristic f M - curveEulerCharacteristic f (structureUnitModule X)

/-- Isomorphic actual sheaves have the same curve Euler characteristic. -/
theorem curveEulerCharacteristic_iso {M N : X.Modules} (e : M ≅ N) :
    curveEulerCharacteristic f M = curveEulerCharacteristic f N := by
  have h (n : ℕ) : Module.finrank k (ModuleScalarH f M n) =
      Module.finrank k (ModuleScalarH f N n) :=
    ((moduleScalarHFunctor f n).mapIso e).toLinearEquiv.finrank_eq
  unfold curveEulerCharacteristic
  rw [h 0, h 1]

/-- Degree is invariant under sheaf isomorphism. -/
theorem curveSheafDegree_iso {M N : X.Modules} (e : M ≅ N) :
    curveSheafDegree f M = curveSheafDegree f N := by
  rw [curveSheafDegree, curveSheafDegree, curveEulerCharacteristic_iso f e]

/-- Additivity when the degree-one cohomology map onto the quotient is surjective. -/
theorem curveEulerCharacteristic_add_of_surjective
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [Module.Finite k (ModuleScalarH f S.X₁ 0)]
    [Module.Finite k (ModuleScalarH f S.X₂ 0)]
    [Module.Finite k (ModuleScalarH f S.X₃ 0)]
    [Module.Finite k (ModuleScalarH f S.X₁ 1)]
    [Module.Finite k (ModuleScalarH f S.X₂ 1)]
    (he : Function.Surjective (moduleScalarHMap f S.g 1)) :
    curveEulerCharacteristic f S.X₂ =
      curveEulerCharacteristic f S.X₁ + curveEulerCharacteristic f S.X₃ := by
  have hs := moduleAbelianComplex_shortExact hS
  have h := sixTerm_finrank
    (moduleScalarHMap f S.f 0) (moduleScalarHMap f S.g 0)
    (moduleScalarHConnecting S hs f 0)
    (moduleScalarHMap f S.f 1) (moduleScalarHMap f S.g 1)
    (moduleScalarHMap_zero_injective S hs f) he
    (moduleScalarH_exact₂ S hs f 0) (moduleScalarH_exact₃ S hs f 0)
    (moduleScalarH_exact₁ S hs f 0) (moduleScalarH_exact₂ S hs f 1)
  change Module.finrank k (ModuleScalarH f S.X₁ 0) +
      Module.finrank k (ModuleScalarH f S.X₃ 0) +
      Module.finrank k (ModuleScalarH f S.X₂ 1) =
    Module.finrank k (ModuleScalarH f S.X₂ 0) +
      Module.finrank k (ModuleScalarH f S.X₁ 1) +
      Module.finrank k (ModuleScalarH f S.X₃ 1) at h
  unfold curveEulerCharacteristic
  omega

/-- Vanishing H² of the subobject supplies the surjectivity required for additivity. -/
theorem curveEulerCharacteristic_add (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [Module.Finite k (ModuleScalarH f S.X₁ 0)]
    [Module.Finite k (ModuleScalarH f S.X₂ 0)]
    [Module.Finite k (ModuleScalarH f S.X₃ 0)]
    [Module.Finite k (ModuleScalarH f S.X₁ 1)]
    [Module.Finite k (ModuleScalarH f S.X₂ 1)]
    [Subsingleton (ModuleScalarH f S.X₁ 2)] :
    curveEulerCharacteristic f S.X₂ =
      curveEulerCharacteristic f S.X₁ + curveEulerCharacteristic f S.X₃ := by
  apply curveEulerCharacteristic_add_of_surjective f S hS
  intro y
  exact (moduleScalarH_exact₃ S (moduleAbelianComplex_shortExact hS) f 1 y).mp
    (Subsingleton.elim _ _)

end FLT.Mazur.FCurve
