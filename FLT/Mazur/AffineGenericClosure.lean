/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Affine closure in a generic algebra

The integral equations of a generic closed subscheme cut out the kernel of its
coordinate map. The quotient embeds in the generic algebra and is flat over a
Dedekind domain. Neither finiteness nor an ambient group law is required here.
-/

@[expose] public section

open scoped TensorProduct nonZeroDivisors

namespace FLT.Mazur.AffineGenericClosure

variable {R K A B : Type*} [CommRing R] [Field K] [Algebra R K]
  [CommRing A] [Algebra R A] [CommRing B] [Algebra K B]
  [Algebra R B] [IsScalarTower R K B]

/-- The coordinate algebra of the affine schematic closure. -/
abbrev Coordinate (f : A →ₐ[R] B) := A ⧸ RingHom.ker f.toRingHom

/-- The closure embeds into the prescribed generic algebra. -/
noncomputable def inclusion (f : A →ₐ[R] B) : Coordinate f →ₐ[R] B :=
  Ideal.Quotient.liftₐ _ f (by intro x hx; exact hx)

/-- No new relation appears in the closure's inclusion. -/
theorem inclusion_injective (f : A →ₐ[R] B) : Function.Injective (inclusion f) :=
  RingHom.kerLift_injective f.toRingHom

/-- The closure inclusion recovers the original coordinate map. -/
theorem inclusion_mk (f : A →ₐ[R] B) (a : A) :
    inclusion f (Ideal.Quotient.mk _ a) = f a := rfl

/-- The closure coordinate algebra is exactly the integral coordinate image. -/
noncomputable def imageEquiv (f : A →ₐ[R] B) : Coordinate f ≃ₐ[R] f.range :=
  AlgEquiv.ofInjective (inclusion f) (inclusion_injective f) |>.trans
    (Subalgebra.equivOfEq _ _ (by
      ext b
      constructor
      · rintro ⟨x, rfl⟩
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
        exact ⟨a, rfl⟩
      · rintro ⟨a, rfl⟩
        exact ⟨Ideal.Quotient.mk _ a, rfl⟩))

variable (K) [IsFractionRing R K]

include K in
/-- The closure has no scalar torsion because its generic algebra has none. -/
theorem isTorsionFree [IsDomain R] (f : A →ₐ[R] B) : Module.IsTorsionFree R (Coordinate f) := by
  let _ : Module.IsTorsionFree R B := Module.IsTorsionFree.trans K
  exact Function.Injective.moduleIsTorsionFree (inclusion f) (inclusion_injective f)
    (fun r x ↦ (inclusion f).toLinearMap.map_smul r x)

include K in
/-- In particular every such affine closure over a DVR is flat. -/
theorem flat [IsDedekindDomain R] (f : A →ₐ[R] B) : Module.Flat R (Coordinate f) := by
  let _ := isTorsionFree K f
  infer_instance

/-- The generic comparison is obtained by extending scalars in the inclusion. -/
noncomputable def genericMap (f : A →ₐ[R] B) : K ⊗[R] Coordinate f →ₐ[K] B :=
  AlgHom.liftEquiv R K _ B (inclusion f)

/-- Localization preserves the injection into the generic algebra. -/
theorem genericMap_injective (f : A →ₐ[R] B) : Function.Injective (genericMap K f) := by
  apply IsLocalizedModule.injective_of_map_eq R⁰
    (TensorProduct.mk R K (Coordinate f) 1)
    (g := (genericMap K f).toLinearMap.restrictScalars R)
  intro x y hxy
  have h : inclusion f x = inclusion f y := by
    change (1 : K) • inclusion f x = (1 : K) • inclusion f y at hxy
    simpa only [one_smul] using hxy
  exact congrArg (fun z ↦ 1 ⊗ₜ[R] z) (inclusion_injective f h)

omit [IsFractionRing R K] in
/-- A generically surjective chart recovers the whole generic subgroup algebra. -/
theorem genericMap_surjective (f : A →ₐ[R] B)
    (hf : Function.Surjective (AlgHom.liftEquiv R K A B f)) :
    Function.Surjective (genericMap K f) := by
  let q : K ⊗[R] A →ₐ[K] K ⊗[R] Coordinate f :=
    Algebra.TensorProduct.map (AlgHom.id K K) (Ideal.Quotient.mkₐ R _)
  have hq : (genericMap K f).comp q = AlgHom.liftEquiv R K A B f := by
    ext a
    change (1 : K) • inclusion f (Ideal.Quotient.mk _ a) = (1 : K) • f a
    rfl
  intro b
  obtain ⟨x, rfl⟩ := hf b
  exact ⟨q x, AlgHom.congr_fun hq x⟩

end FLT.Mazur.AffineGenericClosure
