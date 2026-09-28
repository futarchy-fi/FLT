/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PadicTensorPatching
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Patching finite projective algebras

The intersection of an away algebra with a full local algebra lattice inherits
multiplication and unit. Module patching proves its finite projectivity, and the
module comparisons upgrade to algebra comparisons.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct

namespace ThreeAdicPlan.PadicPatching

variable (p : ℕ) [Fact p.Prime] (d : ℤ) [Fact (¬ (p : ℤ) ∣ d)]
    (A : Type) [CommRing A] [Algebra (Away d p) A]
    [Algebra (Base d) A] [IsScalarTower (Base d) (Away d p) A]
    (L : Subalgebra ℤ_[p] (ℚ_[p] ⊗[Away d p] A))

/-- The global algebra intersection inside the away algebra. -/
def algebraIntersection : Subalgebra (Base d) A :=
  (L.restrictScalars (Base d)).comap (Algebra.TensorProduct.includeRight.restrictScalars (Base d))

@[simp] theorem mem_algebraIntersection (a : A) :
    a ∈ algebraIntersection p d A L ↔ (1 : ℚ_[p]) ⊗ₜ[Away d p] a ∈ L := Iff.rfl

variable (P : ModulePatch p d A L.toSubmodule)

/-- The away map from the patched module, before extending scalars. -/
def ModulePatch.toAway : P.Carrier →ₗ[Base d] A :=
  (P.awayEquiv.toLinearMap.restrictScalars (Base d)).comp
    (TensorProduct.mk (Base d) (Away d p) P.Carrier 1)

/-- The away map embeds the global patched module. -/
theorem ModulePatch.toAway_injective : Function.Injective (P.toAway p d A L) := by
  let : NeZero d := ⟨denominator_ne_zero p d⟩
  exact P.awayEquiv.injective.comp
    (Module.Flat.tensorProduct_mk_injective (R := Base d) (S := Away d p) (M := P.Carrier))

/-- The module patch takes values in the algebra intersection. -/
def ModulePatch.toAlgebraIntersection : P.Carrier →ₗ[Base d] algebraIntersection p d A L :=
  (algebraIntersection p d A L).toSubmoduleEquiv.toLinearMap.comp
    ((P.toAway p d A L).codRestrict (algebraIntersection p d A L).toSubmodule (fun x ↦ by
    change (1 : ℚ_[p]) ⊗ₜ[Away d p] P.awayEquiv (1 ⊗ₜ[Base d] x) ∈ L
    rw [P.compatible]
    exact (P.localEquiv (1 ⊗ₜ[Base d] x)).property))

/-- The algebra intersection is linearly equivalent to the constructed module patch. -/
def ModulePatch.algebraIntersectionEquiv :
    P.Carrier ≃ₗ[Base d] algebraIntersection p d A L :=
  LinearEquiv.ofBijective (P.toAlgebraIntersection p d A L) (by
    constructor
    · intro x y h
      apply P.toAway_injective p d A L
      exact congrArg Subtype.val h
    · intro a
      obtain ⟨x, hx⟩ := P.intersection a.val |>.2 a.property
      exact ⟨x, Subtype.ext hx⟩)

include P in
/-- The intersection algebra is finite as a module over the global ring. -/
theorem algebraIntersection_finite : Module.Finite (Base d) (algebraIntersection p d A L) :=
  Module.Finite.equiv (P.algebraIntersectionEquiv p d A L)

include P in
/-- The intersection algebra is projective as a module over the global ring. -/
theorem algebraIntersection_projective : Module.Projective (Base d) (algebraIntersection p d A L) :=
  Module.Projective.of_equiv' (P.algebraIntersectionEquiv p d A L)

/-- Base change of the algebra intersection to the away coefficient ring. -/
def algebraIntersectionAwayMap :
    Away d p ⊗[Base d] algebraIntersection p d A L →ₐ[Away d p] A :=
  Algebra.TensorProduct.liftEquivRight (Base d) (Away d p) _ _
    (algebraIntersection p d A L).val

@[simp] theorem algebraIntersectionAwayMap_tmul (s : Away d p)
    (a : algebraIntersection p d A L) :
    algebraIntersectionAwayMap p d A L (s ⊗ₜ[Base d] a) = s • a.val := by
  simp [algebraIntersectionAwayMap, Algebra.TensorProduct.liftEquivRight, Algebra.smul_def]

include P in
/-- The away algebra map is the module patch comparison under the intersection
identification, so it is bijective. -/
theorem algebraIntersectionAwayMap_bijective :
    Function.Bijective (algebraIntersectionAwayMap p d A L) := by
  let e := ((P.algebraIntersectionEquiv p d A L).symm.baseChange
    (Base d) (Away d p) _ _).trans P.awayEquiv
  have he : (algebraIntersectionAwayMap p d A L).toLinearMap = e.toLinearMap := by
    ext a
    have h := congrArg Subtype.val ((P.algebraIntersectionEquiv p d A L).apply_symm_apply a)
    change P.awayEquiv (1 ⊗ₜ[Base d] (P.algebraIntersectionEquiv p d A L).symm a) = a.val at h
    simpa [e, TensorProduct.AlgebraTensorModule.curry_apply] using h.symm
  change Function.Bijective (algebraIntersectionAwayMap p d A L).toLinearMap
  rw [he]
  exact e.bijective

/-- Inverting `p` recovers the prescribed away algebra as an algebra, including
multiplication and unit. -/
def algebraIntersectionAwayEquiv :
    Away d p ⊗[Base d] algebraIntersection p d A L ≃ₐ[Away d p] A :=
  AlgEquiv.ofBijective (algebraIntersectionAwayMap p d A L)
    (algebraIntersectionAwayMap_bijective p d A L P)

/-- The local restriction of an element of the algebra intersection. -/
def algebraIntersectionToLocal : algebraIntersection p d A L →ₐ[Base d] L :=
  (((Algebra.TensorProduct.includeRight : A →ₐ[Away d p] ℚ_[p] ⊗[Away d p] A).restrictScalars
      (Base d)).comp (algebraIntersection p d A L).val).codRestrict
    (L.restrictScalars (Base d)) (fun a ↦ a.property)

/-- Base change of the algebra intersection to the local coefficient ring. -/
def algebraIntersectionLocalMap :
    ℤ_[p] ⊗[Base d] algebraIntersection p d A L →ₐ[ℤ_[p]] L :=
  Algebra.TensorProduct.liftEquivRight (Base d) ℤ_[p] _ _
    (algebraIntersectionToLocal p d A L)

@[simp] theorem algebraIntersectionLocalMap_tmul (s : ℤ_[p])
    (a : algebraIntersection p d A L) :
    algebraIntersectionLocalMap p d A L (s ⊗ₜ[Base d] a) =
      s • algebraIntersectionToLocal p d A L a := by
  simp [algebraIntersectionLocalMap, Algebra.TensorProduct.liftEquivRight, Algebra.smul_def]

/-- The algebraic local restriction is the local comparison of the module patch. -/
theorem ModulePatch.algebraIntersectionEquiv_local (x : P.Carrier) :
    algebraIntersectionToLocal p d A L (P.algebraIntersectionEquiv p d A L x) =
      (P.localEquiv (1 ⊗ₜ[Base d] x) : L.toSubmodule) := by
  apply Subtype.ext
  exact P.compatible x

include P in
/-- The local algebra map is bijective by the local comparison in module patching. -/
theorem algebraIntersectionLocalMap_bijective :
    Function.Bijective (algebraIntersectionLocalMap p d A L) := by
  let e := ((P.algebraIntersectionEquiv p d A L).symm.baseChange
    (Base d) ℤ_[p] _ _).trans (P.localEquiv.trans L.toSubmoduleEquiv)
  have he : (algebraIntersectionLocalMap p d A L).toLinearMap = e.toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro s a
    simp only [AlgHom.toLinearMap_apply, algebraIntersectionLocalMap_tmul]
    change s • algebraIntersectionToLocal p d A L a =
      P.localEquiv (s ⊗ₜ[Base d] (P.algebraIntersectionEquiv p d A L).symm a)
    have h := P.algebraIntersectionEquiv_local p d A L
      ((P.algebraIntersectionEquiv p d A L).symm a)
    rw [LinearEquiv.apply_symm_apply] at h
    rw [h]
    apply Subtype.ext
    have hh := P.localEquiv.map_smul s
      ((1 : ℤ_[p]) ⊗ₜ[Base d] (P.algebraIntersectionEquiv p d A L).symm a)
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one] at hh
    exact congrArg Subtype.val hh.symm
  change Function.Bijective (algebraIntersectionLocalMap p d A L).toLinearMap
  rw [he]
  exact e.bijective

/-- Completing the algebra intersection recovers the prescribed local algebra,
including its multiplication and unit. -/
def algebraIntersectionLocalEquiv :
    ℤ_[p] ⊗[Base d] algebraIntersection p d A L ≃ₐ[ℤ_[p]] L :=
  AlgEquiv.ofBijective (algebraIntersectionLocalMap p d A L)
    (algebraIntersectionLocalMap_bijective p d A L P)


/-- The module patch realized on the actual intersection algebra, with both
comparisons given by algebra maps. -/
def algebraIntersectionModulePatch : ModulePatch p d A L.toSubmodule where
  Carrier := algebraIntersection p d A L
  finite := algebraIntersection_finite p d A L P
  projective := algebraIntersection_projective p d A L P
  awayEquiv := (algebraIntersectionAwayEquiv p d A L P).toLinearEquiv
  localEquiv := (algebraIntersectionLocalEquiv p d A L P).toLinearEquiv.trans
    L.toSubmoduleEquiv.symm
  compatible a := by
    change (1 : ℚ_[p]) ⊗ₜ[Away d p]
      algebraIntersectionAwayMap p d A L (1 ⊗ₜ[Base d] a) =
        (algebraIntersectionLocalMap p d A L (1 ⊗ₜ[Base d] a)).val
    simp only [algebraIntersectionAwayMap_tmul, algebraIntersectionLocalMap_tmul, one_smul]
    rfl

/-- The tensor square of the intersection algebra maps to the away tensor square. -/
def algebraIntersectionTensorMap :
    algebraIntersection p d A L ⊗[Base d] algebraIntersection p d A L →ₐ[Base d]
      A ⊗[Away d p] A :=
  Algebra.TensorProduct.lift
    (((Algebra.TensorProduct.includeLeft : A →ₐ[Away d p] A ⊗[Away d p] A).restrictScalars
      (Base d)).comp
      (algebraIntersection p d A L).val)
    (((Algebra.TensorProduct.includeRight : A →ₐ[Away d p] A ⊗[Away d p] A).restrictScalars
      (Base d)).comp
      (algebraIntersection p d A L).val) (fun _ _ ↦ Commute.all _ _)

@[simp] theorem algebraIntersectionTensorMap_tmul (a b : algebraIntersection p d A L) :
    algebraIntersectionTensorMap p d A L (a ⊗ₜ[Base d] b) = a.val ⊗ₜ[Away d p] b.val := by
  simp [algebraIntersectionTensorMap]

/-- The algebraic tensor map is the away tensor comparison of the module patch. -/
theorem algebraIntersectionTensorMap_eq
    (z : algebraIntersection p d A L ⊗[Base d] algebraIntersection p d A L) :
    algebraIntersectionTensorMap p d A L z =
      (algebraIntersectionModulePatch p d A L P).tensorAwayEquiv (1 ⊗ₜ[Base d] z) := by
  induction z using TensorProduct.inductionOn with
  | add a b ha hb => simp [TensorProduct.tmul_add, ha, hb]
  | tmul a b =>
    simp [ModulePatch.tensorAwayEquiv, tensorScalarExtensionEquiv,
      algebraIntersectionModulePatch, algebraIntersectionAwayEquiv]

include P in
/-- The tensor square of the intersection injects into the away tensor square. -/
theorem algebraIntersectionTensorMap_injective :
    Function.Injective (algebraIntersectionTensorMap p d A L) := by
  let : NeZero d := ⟨denominator_ne_zero p d⟩
  let Q := algebraIntersectionModulePatch p d A L P
  let : Module.Projective (Base d) (algebraIntersection p d A L) :=
    algebraIntersection_projective p d A L P
  intro x y h
  apply Module.Flat.tensorProduct_mk_injective (Base d)
    (algebraIntersection p d A L ⊗[Base d] algebraIntersection p d A L) (Away d p)
  apply Q.tensorAwayEquiv.injective
  simpa only [algebraIntersectionTensorMap_eq p d A L P, Q, TensorProduct.mk_apply] using h

include P in
/-- Membership in the tensor square of the intersection is detected by the actual
local tensor-square lattice, not merely by scalar integrality. -/
theorem algebraIntersectionTensorMap_range (a : A ⊗[Away d p] A) :
    (∃ z, algebraIntersectionTensorMap p d A L z = a) ↔
    ∃ b : L.toSubmodule ⊗[ℤ_[p]] L.toSubmodule,
      awayTensorMap (p := p) (d := d) a = latticeTensorMap (L := L.toSubmodule) b := by
  constructor
  · rintro ⟨z, hz⟩
    have hz' : (algebraIntersectionModulePatch p d A L P).tensorAwayEquiv
        (1 ⊗ₜ[Base d] z) = a := (algebraIntersectionTensorMap_eq p d A L P z).symm.trans hz
    obtain ⟨b, hb⟩ := ((algebraIntersectionModulePatch p d A L P).tensor_intersection_native a).1
      ⟨z, hz'⟩
    exact ⟨b, hb⟩
  · rintro ⟨b, hb⟩
    obtain ⟨z, hz⟩ := ((algebraIntersectionModulePatch p d A L P).tensor_intersection_native a).2
      ⟨b, hb⟩
    exact ⟨z, (algebraIntersectionTensorMap_eq p d A L P z).trans hz⟩

end ThreeAdicPlan.PadicPatching
