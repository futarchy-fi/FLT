/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FilteredFiniteModuleFlatFamily
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Uniform flatness descent for finite finitely presented algebras

The original finite algebra is extended along the actual transition maps.
Finite presentation as an algebra gives a finite module presentation because
the algebra is also module finite. This last hypothesis is essential to this
argument; affine charts of a relative curve need not satisfy it.
-/

@[expose] public noncomputable section
open CategoryTheory Limits TensorProduct
namespace FLT.Mazur.Approximation

/-- Flatness of the structure ring map of the actual extended algebra. -/
def ScalarAlgebraFlat {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (B : Type*) [CommRing B] [Algebra R B] : Prop :=
  let _ := φ.toAlgebra
  (algebraMap S (S ⊗[R] B)).Flat

/-- The ring-map and module formulations use the same scalar-extended algebra. -/
theorem scalarAlgebraFlat_iff {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (B : Type*) [CommRing B] [Algebra R B] :
    ScalarAlgebraFlat φ B ↔ ScalarFlat φ B := by
  let _ := φ.toAlgebra
  exact RingHom.flat_algebraMap_iff

universe u v w z
variable {I : Type v} [Category.{w} I] [IsFiltered I]
  (F : I ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
  [PreservesColimit F (forget CommRingCat)]

include hc in
/-- A finite family of finite presented finite algebras becomes flat at one actual stage. -/
theorem exists_flat_finite_algebra_family_stage {T : Type*} [Finite T]
    (i : I) (B : T → Type z) [∀ t, CommRing (B t)] [∀ t, Algebra (F.obj i) (B t)]
    [∀ t, Module.Finite (F.obj i) (B t)]
    [∀ t, Algebra.FinitePresentation (F.obj i) (B t)]
    (h : ∀ t, ScalarAlgebraFlat (c.ι.app i).hom (B t)) :
    ∃ (j : I) (g : i ⟶ j), ∀ (k : I) (e : j ⟶ k) (t : T),
      ScalarAlgebraFlat (F.map (g ≫ e)).hom (B t) := by
  let _ (t : T) : Module.FinitePresentation (F.obj i) (B t) :=
    Module.FinitePresentation.of_finite_of_finitePresentation (F.obj i) (B t)
  obtain ⟨j, g, hg⟩ := exists_flat_finite_module_family_stage F c hc i B
    (fun t ↦ (scalarAlgebraFlat_iff _ _).mp (h t))
  exact ⟨j, g, fun k e t ↦ (scalarAlgebraFlat_iff _ _).mpr (hg k e t)⟩

end FLT.Mazur.Approximation
