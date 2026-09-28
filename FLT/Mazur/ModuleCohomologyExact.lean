/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleCohomology
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.Finiteness.Finsupp
public import Mathlib.RingTheory.Noetherian.Basic

/-!+# Exact sequences for module-coefficient cohomology

Short exactness is required after forgetting to abelian sheaves. The connecting
maps are linear because coefficient multiplication is an endomorphism of the
short exact sequence. The resulting long exact sequence gives finiteness in
each of the three adjacent degree patterns, including the degree-zero endpoint.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace FLT.Mazur.FCurve

local instance moduleExactHasExt (X : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  HasExt.standard _

variable {X : Scheme.{u}}

/-- The underlying short complex of abelian sheaves. -/
def moduleAbelianComplex (S : ShortComplex X.Modules) :
    ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  ShortComplex.mk ((SheafOfModules.toSheaf X.ringCatSheaf).map S.f)
    ((SheafOfModules.toSheaf X.ringCatSheaf).map S.g) (by
      rw [← Functor.map_comp, S.zero]
      rfl)

variable (S : ShortComplex X.Modules) (hS : (moduleAbelianComplex S).ShortExact)

/-- Multiplication by a global section on all three terms of the sequence. -/
def moduleComplexMultiply (r : Γ(X, ⊤)) :
    moduleAbelianComplex S ⟶ moduleAbelianComplex S where
  τ₁ := moduleMultiply S.X₁ r
  τ₂ := moduleMultiply S.X₂ r
  τ₃ := moduleMultiply S.X₃ r
  comm₁₂ := moduleMultiply_naturality S.f r
  comm₂₃ := moduleMultiply_naturality S.g r

/-- The Ext connecting homomorphism is linear over global sections. -/
def moduleHConnecting (n : ℕ) : ModuleH S.X₃ n →ₗ[Γ(X, ⊤)] ModuleH S.X₁ (n + 1) where
  toFun := Sheaf.H.δ hS n (n + 1) rfl
  map_add' := (Sheaf.H.δ hS n (n + 1) rfl).map_add
  map_smul' r x :=
    Sheaf.H.δ_naturality n (n + 1) rfl hS hS (moduleComplexMultiply S r) x

section Scalars

variable {k : Type u} [Field k] (f : X ⟶ Spec (CommRingCat.of k))

/-- Restriction of the connecting map to the specified base field. -/
def moduleScalarHConnecting (n : ℕ) :
    ModuleScalarH f S.X₃ n →ₗ[k] ModuleScalarH f S.X₁ (n + 1) where
  toFun := moduleHConnecting S hS n
  map_add' := (moduleHConnecting S hS n).map_add
  map_smul' a x := (moduleHConnecting S hS n).map_smul (structureScalarMap f a) x

include hS in
/-- Exactness at the middle coefficient in every degree. -/
lemma moduleScalarH_exact₂ (n : ℕ) :
    Function.Exact (moduleScalarHMap f S.f n) (moduleScalarHMap f S.g n) :=
  (ShortComplex.ab_exact_iff_function_exact _).mp (Sheaf.H.longSequence_exact₂' hS n)

/-- Exactness at the quotient coefficient, before the connecting map. -/
lemma moduleScalarH_exact₃ (n : ℕ) :
    Function.Exact (moduleScalarHMap f S.g n) (moduleScalarHConnecting S hS f n) :=
  (ShortComplex.ab_exact_iff_function_exact _).mp
    (Sheaf.H.longSequence_exact₃' hS n (n + 1) rfl)

/-- Exactness at the subobject coefficient in positive degree. -/
lemma moduleScalarH_exact₁ (n : ℕ) :
    Function.Exact (moduleScalarHConnecting S hS f n) (moduleScalarHMap f S.f (n + 1)) :=
  (ShortComplex.ab_exact_iff_function_exact _).mp
    (Sheaf.H.longSequence_exact₁' hS n (n + 1) rfl)

include hS in
/-- The initial map on degree-zero cohomology is injective. -/
lemma moduleScalarHMap_zero_injective : Function.Injective (moduleScalarHMap f S.f 0) := by
  have := hS.mono_f
  exact Abelian.Ext.postcomp_mk₀_injective_of_mono _ (moduleAbelianComplex S).f

/-- A six-term segment of the long sequence, with every arrow a linear map. -/
def moduleScalarHLongSequence (n : ℕ) : ComposableArrows (ModuleCat.{u + 1} k) 5 :=
  ComposableArrows.mk₅
    (ModuleCat.ofHom (moduleScalarHMap f S.f n))
    (ModuleCat.ofHom (moduleScalarHMap f S.g n))
    (ModuleCat.ofHom (moduleScalarHConnecting S hS f n))
    (ModuleCat.ofHom (moduleScalarHMap f S.f (n + 1)))
    (ModuleCat.ofHom (moduleScalarHMap f S.g (n + 1)))

private lemma linearPair_exact {A B C : ModuleCat.{u + 1} k}
    (a : A ⟶ B) (b : B ⟶ C) (h : Function.Exact a b) :
    (ComposableArrows.mk₂ a b).Exact := by
  have hz : a ≫ b = 0 := ModuleCat.hom_ext h.linearMap_comp_eq_zero
  exact ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
    (ShortComplex.mk a b hz)).mpr h).exact_toComposableArrows

/-- Every overlapping six-term segment is exact in the category of vector spaces. -/
lemma moduleScalarHLongSequence_exact (n : ℕ) :
    (moduleScalarHLongSequence S hS f n).Exact := by
  apply ComposableArrows.exact_of_δ₀
    (linearPair_exact _ _ (moduleScalarH_exact₂ S hS f n))
  apply ComposableArrows.exact_of_δ₀
    (linearPair_exact _ _ (moduleScalarH_exact₃ S hS f n))
  apply ComposableArrows.exact_of_δ₀
    (linearPair_exact _ _ (moduleScalarH_exact₁ S hS f n))
  exact linearPair_exact _ _ (moduleScalarH_exact₂ S hS f (n + 1))

end Scalars

/-- Finite outer terms force a finite middle term in an exact pair over a Noetherian ring.
No surjectivity onto the right-hand term is needed. -/
lemma moduleFinite_of_exact_pair {R A B C : Type*} [Ring R] [IsNoetherianRing R]
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module R A] [Module R B] [Module R C]
    (a : A →ₗ[R] B) (b : B →ₗ[R] C) (h : Function.Exact a b)
    [Module.Finite R A] [Module.Finite R C] : Module.Finite R B := by
  have he : Function.Exact a b.rangeRestrict := by
    rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict]
    exact h.linearMap_ker_eq
  exact Module.Finite.of_exact he b.surjective_rangeRestrict

section Scalars

variable {k : Type u} [Field k] (f : X ⟶ Spec (CommRingCat.of k))

include hS in
/-- Finiteness of `Hⁿ(M₁)` and `Hⁿ(M₃)` implies finiteness of `Hⁿ(M₂)`. -/
lemma moduleScalarH_finite_middle (n : ℕ)
    [Module.Finite k (ModuleScalarH f S.X₁ n)]
    [Module.Finite k (ModuleScalarH f S.X₃ n)] :
    Module.Finite k (ModuleScalarH f S.X₂ n) :=
  moduleFinite_of_exact_pair _ _ (moduleScalarH_exact₂ S hS f n)

include hS in
/-- Finiteness of `Hⁿ(M₂)` and `Hⁿ⁺¹(M₁)` implies finiteness of `Hⁿ(M₃)`. -/
lemma moduleScalarH_finite_right (n : ℕ)
    [Module.Finite k (ModuleScalarH f S.X₂ n)]
    [Module.Finite k (ModuleScalarH f S.X₁ (n + 1))] :
    Module.Finite k (ModuleScalarH f S.X₃ n) :=
  moduleFinite_of_exact_pair _ _ (moduleScalarH_exact₃ S hS f n)

include hS in
/-- Finiteness of `Hⁿ(M₃)` and `Hⁿ⁺¹(M₂)` implies finiteness of `Hⁿ⁺¹(M₁)`. -/
lemma moduleScalarH_finite_left_succ (n : ℕ)
    [Module.Finite k (ModuleScalarH f S.X₃ n)]
    [Module.Finite k (ModuleScalarH f S.X₂ (n + 1))] :
    Module.Finite k (ModuleScalarH f S.X₁ (n + 1)) :=
  moduleFinite_of_exact_pair _ _ (moduleScalarH_exact₁ S hS f n)

include hS in
/-- At degree zero only finiteness of the middle coefficient is required. -/
lemma moduleScalarH_finite_left_zero [Module.Finite k (ModuleScalarH f S.X₂ 0)] :
    Module.Finite k (ModuleScalarH f S.X₁ 0) :=
  Module.Finite.of_injective _ (moduleScalarHMap_zero_injective S hS f)

end Scalars

end FLT.Mazur.FCurve
