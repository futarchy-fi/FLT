/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonComponentHZeroEndpoints

/-!
# Linear gluing of actual component H0 classes

The original polygon H0 is the kernel of the difference of actual endpoint
restrictions on component H0. The equivalence retains the normalization map
and is linear; it applies in particular to the original single-point powers.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules

universe u

namespace FLT.Mazur.PolygonComponentHZeroMatching

open FCurve PolygonPinching LinePullbackRestriction PolygonNormalizationLinearSections
open PolygonComponentHZeroEndpoints

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (L : C.left.Modules) (hL : LocallyFreeRankOne L)

omit [NeZero n] in
/-- The discrepancy of the two component endpoints in each common node H0. -/
def difference :
    (∀ i : Fin n, ModuleScalarH (component K).hom (componentLine K n p L i) 0) →ₗ[K]
      (∀ i : Fin n, ModuleScalarH (point K).hom (nodeLine K n q L i) 0) :=
  LinearMap.pi fun i ↦
    (zeroMap K n hn p q h L i).comp (LinearMap.proj i) -
      (infinityMap K n hn p q h L i).comp (LinearMap.proj (next hn i))

omit [NeZero n] in
/-- Kernel membership says the two actual component endpoint classes agree. -/
theorem mem_kernel_iff (v : ∀ i : Fin n,
    ModuleScalarH (component K).hom (componentLine K n p L i) 0) :
    v ∈ LinearMap.ker (difference K n hn p q h L) ↔
      ∀ i, zeroMap K n hn p q h L i (v i) =
        infinityMap K n hn p q h L i (v (next hn i)) := by
  simp only [LinearMap.mem_ker, difference, LinearMap.pi_apply, LinearMap.sub_apply,
    LinearMap.comp_apply, LinearMap.proj_apply, funext_iff, Pi.zero_apply, sub_eq_zero]

omit [NeZero n] in
/-- The intrinsic normalization kernel is exactly component endpoint matching. -/
theorem kernel_iff_component
    (x : ModuleScalarH C.hom
      ((pushforward p.left).obj ((Scheme.Modules.pullback p.left).obj L)) 0) :
    moduleScalarHMap C.hom (PolygonLineNormalization.complex K n hn p q h L hL).g 0 x = 0 ↔
      componentEquiv K n p L x ∈ LinearMap.ker (difference K n hn p q h L) := by
  rw [PolygonLineHZero.matching_iff, mem_kernel_iff]
  constructor
  · intro he i
    apply (moduleScalarH0Equiv (point K).hom (nodeLine K n q L i)).injective
    rw [zeroMap_component K n hn p q h L hL, infinityMap_component K n hn p q h L hL]
    have hs := congrArg (moduleScalarH0Equiv C.hom _) he
    rw [moduleScalarH0Equiv_naturality, moduleScalarH0Equiv_naturality] at hs
    exact congrArg (fun s ↦ (sealedAlong (nodeι K n i).left q.left
      (nodeι K n i ≫ q).left rfl L).app ⊤ s) hs
  · intro he
    apply (moduleScalarH0Equiv C.hom _).injective
    rw [moduleScalarH0Equiv_naturality, moduleScalarH0Equiv_naturality]
    apply PolygonPowerBranchValues.nodeRestriction_injective K n q L
    funext i
    have hs := congrArg (moduleScalarH0Equiv (point K).hom (nodeLine K n q L i)) (he i)
    rw [zeroMap_component K n hn p q h L hL, infinityMap_component K n hn p q h L hL] at hs
    exact hs

/-- Linear component restriction identifies the two actual normalization kernels. -/
def normalizationKernelEquiv :
    LinearMap.ker (moduleScalarHMap C.hom
      (PolygonLineNormalization.complex K n hn p q h L hL).g 0) ≃ₗ[K]
        LinearMap.ker (difference K n hn p q h L) :=
  { toEquiv := (componentEquiv K n p L).toEquiv.subtypeEquiv
      (kernel_iff_component K n hn p q h L hL)
    map_add' := fun x y ↦ Subtype.ext ((componentEquiv K n p L).map_add x.val y.val)
    map_smul' := fun a x ↦ Subtype.ext ((componentEquiv K n p L).map_smul a x.val) }

/-- The whole polygon H0 is linearly the matching space of actual component H0 classes. -/
def h0Equiv : ModuleScalarH C.hom L 0 ≃ₗ[K]
    LinearMap.ker (difference K n hn p q h L) :=
  (PolygonLineHZero.kernelEquiv K n hn p q h L hL).trans
    (normalizationKernelEquiv K n hn p q h L hL)

/-- The gluing equivalence retains the original normalization pullback on every component. -/
theorem h0Equiv_val (x : ModuleScalarH C.hom L 0) :
    (h0Equiv K n hn p q h L hL x).val =
      componentEquiv K n p L (moduleScalarHMap C.hom
        ((pullbackPushforwardAdjunction p.left).unit.app L) 0 x) :=
  congrArg (componentEquiv K n p L)
    (PolygonLineHZero.kernelEquiv_val K n hn p q h L hL x)

end FLT.Mazur.PolygonComponentHZeroMatching
