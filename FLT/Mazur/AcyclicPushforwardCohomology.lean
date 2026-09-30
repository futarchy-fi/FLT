/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AbsoluteDirectImageCohomology
public import FLT.Mazur.ModuleDerivedAbelianComparison
public import FLT.Mazur.ModuleCohomologyRing
public import FLT.Mazur.PushforwardCech

/-!
# Scalar cohomology of acyclic module direct images

Vanishing of the actual positive module higher direct images gives an absolute
cohomology comparison, linear over target global sections and any specified base
ring. The comparison is natural in the coefficient module. Compatibility with
restriction to open subschemes is a separate construction.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

universe u v

namespace FLT.Mazur.FCurve

local instance acyclicPushforwardHasExt (X : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  HasExt.standard _

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Acyclicity for the actual module direct-image functor. -/
abbrev ModulePushforwardAcyclic (M : X.Modules) : Prop :=
  ∀ q : ℕ, IsZero (((pushforward f).rightDerived (q + 1)).obj M)

variable (M : X.Modules) (hM : ModulePushforwardAcyclic f M)

include hM

/-- The module vanishing hypothesis gives the abelian vanishing used to compute Ext. -/
lemma modulePushforwardAcyclic_abelian :
    AbsoluteDirectImageCohomology.Acyclic f.base (moduleAbelianSheaf M) :=
  fun q ↦ ModuleDerivedAbelianComparison.isZero_abelian_of_module f M q (hM q)

/-- The underlying additive comparison, using module-derived vanishing. -/
def acyclicPushforwardAddEquiv (n : ℕ) :
    ModuleH ((pushforward f).obj M) n ≃+ ModuleH M n :=
  AbsoluteDirectImageCohomology.cohomologyEquiv f.base
    (moduleAbelianSheaf M) (modulePushforwardAcyclic_abelian f M hM) n

omit hM in
/-- Multiplication agrees under the identity on direct-image sections. -/
lemma acyclicPushforward_multiply (r : Γ(Y, ⊤)) :
    moduleMultiply ((pushforward f).obj M) r =
      (TopCat.Sheaf.pushforward AddCommGrpCat f.base).map
        (moduleMultiply M (f.appTop r)) := by
  apply Sheaf.hom_ext
  exact PushforwardCech.pushforward_multiply f M r

/-- Direct-image comparison is linear over the target's global sections. -/
def acyclicPushforwardModuleHEquiv (n : ℕ) :
    letI _sourceScalars := Module.compHom (ModuleH M n) f.appTop.hom
    ModuleH ((pushforward f).obj M) n ≃ₗ[Γ(Y, ⊤)] ModuleH M n := by
  letI _sourceScalars := Module.compHom (ModuleH M n) f.appTop.hom
  refine
    { toAddEquiv := acyclicPushforwardAddEquiv f M hM n
      map_smul' := ?_ }
  intro r x
  exact (congrArg (fun a : moduleAbelianSheaf ((pushforward f).obj M) ⟶
      moduleAbelianSheaf ((pushforward f).obj M) ↦
    AbsoluteDirectImageCohomology.cohomologyEquiv f.base
    (moduleAbelianSheaf M) (modulePushforwardAcyclic_abelian f M hM) n
    (Sheaf.H.map a n x)) (acyclicPushforward_multiply f M r)).trans
      (AbsoluteDirectImageCohomology.cohomologyEquiv_moduleMultiply f.base M
        (modulePushforwardAcyclic_abelian f M hM) (f.appTop r) n x)

/-- Scalar comparison commutes with every coefficient morphism between acyclic modules. -/
lemma acyclicPushforwardModuleHEquiv_naturality {N : X.Modules}
    (hN : ModulePushforwardAcyclic f N) (a : M ⟶ N) (n : ℕ)
    (x : ModuleH ((pushforward f).obj M) n) :
    acyclicPushforwardModuleHEquiv f N hN n (moduleHMap ((pushforward f).map a) n x) =
      moduleHMap a n (acyclicPushforwardModuleHEquiv f M hM n x) :=
  AbsoluteDirectImageCohomology.cohomologyEquiv_naturality f.base
    ((SheafOfModules.toSheaf X.ringCatSheaf).map a)
    (modulePushforwardAcyclic_abelian f M hM) (modulePushforwardAcyclic_abelian f N hN) n x

/-- Degree zero is the identity on actual global sections. -/
lemma acyclicPushforwardModuleHEquiv_zero (x : ModuleH ((pushforward f).obj M) 0) :
    moduleH0Equiv M (acyclicPushforwardModuleHEquiv f M hM 0 x) =
      moduleH0Equiv ((pushforward f).obj M) x :=
  (Sheaf.H.equiv₀ (moduleAbelianSheaf M) isTerminalTop).apply_symm_apply
    (Sheaf.H.equiv₀ (moduleAbelianSheaf ((pushforward f).obj M)) isTerminalTop x)

/-- Restriction of scalars gives acyclic-direct-image comparison over any base ring. -/
def acyclicPushforwardRingHEquiv {R : Type v} [Ring R]
    (ρ : R →+* Γ(Y, ⊤)) (n : ℕ) :
    letI _targetScalars := Module.compHom (ModuleH ((pushforward f).obj M) n) ρ
    letI _sourceScalars := Module.compHom (ModuleH M n) (f.appTop.hom.comp ρ)
    ModuleH ((pushforward f).obj M) n ≃ₗ[R] ModuleH M n := by
  letI _sourceTargetScalars := Module.compHom (ModuleH M n) f.appTop.hom
  letI _targetScalars := Module.compHom (ModuleH ((pushforward f).obj M) n) ρ
  letI _sourceScalars := Module.compHom (ModuleH M n) (f.appTop.hom.comp ρ)
  exact
    { toAddEquiv := (acyclicPushforwardModuleHEquiv f M hM n).toAddEquiv
      map_smul' := fun r x ↦ (acyclicPushforwardModuleHEquiv f M hM n).map_smul (ρ r) x }

/-- The comparison retains the specified structure morphisms over a field. -/
def acyclicPushforwardScalarHEquiv {k : Type u} [Field k]
    (g : Y ⟶ Spec (CommRingCat.of k)) (n : ℕ) :
    ModuleScalarH g ((pushforward f).obj M) n ≃ₗ[k] ModuleScalarH (f ≫ g) M n := by
  letI _sourceTargetScalars := Module.compHom (ModuleH M n) f.appTop.hom
  refine
    { toAddEquiv := (acyclicPushforwardModuleHEquiv f M hM n).toAddEquiv
      map_smul' := ?_ }
  intro r x
  change ModuleH ((pushforward f).obj M) n at x
  have h : structureScalarMap (f ≫ g) r = f.appTop (structureScalarMap g r) := by
    simp [structureScalarMap]
  change acyclicPushforwardModuleHEquiv f M hM n
      (structureScalarMap g r • (x : ModuleH ((pushforward f).obj M) n)) =
    structureScalarMap (f ≫ g) r • (acyclicPushforwardModuleHEquiv f M hM n x : ModuleH M n)
  rw [h]
  exact (acyclicPushforwardModuleHEquiv f M hM n).map_smul (structureScalarMap g r) x

/-- Restriction to any specified base ring retains naturality. -/
lemma acyclicPushforwardRingHEquiv_naturality {R : Type v} [Ring R]
    (ρ : R →+* Γ(Y, ⊤)) {N : X.Modules} (hN : ModulePushforwardAcyclic f N)
    (a : M ⟶ N) (n : ℕ) (x : ModuleH ((pushforward f).obj M) n) :
    acyclicPushforwardRingHEquiv f N hN ρ n (moduleHMap ((pushforward f).map a) n x) =
      moduleHMap a n (acyclicPushforwardRingHEquiv f M hM ρ n x) :=
  acyclicPushforwardModuleHEquiv_naturality f M hM hN a n x

/-- The field-valued comparison commutes with the existing scalar cohomology maps. -/
lemma acyclicPushforwardScalarHEquiv_naturality {k : Type u} [Field k]
    (g : Y ⟶ Spec (CommRingCat.of k)) {N : X.Modules} (hN : ModulePushforwardAcyclic f N)
    (a : M ⟶ N) (n : ℕ) (x : ModuleScalarH g ((pushforward f).obj M) n) :
    acyclicPushforwardScalarHEquiv f N hN g n
        (moduleScalarHMap g ((pushforward f).map a) n x) =
      moduleScalarHMap (f ≫ g) a n (acyclicPushforwardScalarHEquiv f M hM g n x) :=
  acyclicPushforwardModuleHEquiv_naturality f M hM hN a n x

/-- The comparison in the existing base-ring cohomology functor's codomain. -/
def acyclicPushforwardRingHIso {R : Type u} [CommRing R]
    (ρ : R →+* Γ(Y, ⊤)) (n : ℕ) :
    (moduleRingHFunctor ρ n).obj ((pushforward f).obj M) ≅
      (moduleRingHFunctor (f.appTop.hom.comp ρ) n).obj M :=
  (acyclicPushforwardRingHEquiv f M hM ρ n).toModuleIso

/-- The bundled comparison commutes with the existing base-ring cohomology functors. -/
lemma acyclicPushforwardRingHIso_naturality {R : Type u} [CommRing R]
    (ρ : R →+* Γ(Y, ⊤)) {N : X.Modules} (hN : ModulePushforwardAcyclic f N)
    (a : M ⟶ N) (n : ℕ) :
    (moduleRingHFunctor ρ n).map ((pushforward f).map a) ≫
        (acyclicPushforwardRingHIso f N hN ρ n).hom =
      (acyclicPushforwardRingHIso f M hM ρ n).hom ≫
        (moduleRingHFunctor (f.appTop.hom.comp ρ) n).map a := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact acyclicPushforwardRingHEquiv_naturality f M hM ρ hN a n x

/-- Finite generation over the specified base ring is preserved in both directions. -/
theorem acyclicPushforward_moduleRingH_finite_iff {R : Type u} [CommRing R]
    (ρ : R →+* Γ(Y, ⊤)) (n : ℕ) :
    Module.Finite R (ModuleRingH ρ ((pushforward f).obj M) n) ↔
      Module.Finite R (ModuleRingH (f.appTop.hom.comp ρ) M n) := by
  constructor
  · intro h
    let _finite : Module.Finite R
        ((moduleRingHFunctor ρ n).obj ((pushforward f).obj M)) := h
    exact Module.Finite.equiv (acyclicPushforwardRingHIso f M hM ρ n).toLinearEquiv
  · intro h
    let _finite : Module.Finite R
        ((moduleRingHFunctor (f.appTop.hom.comp ρ) n).obj M) := h
    exact Module.Finite.equiv (acyclicPushforwardRingHIso f M hM ρ n).symm.toLinearEquiv

/-- Acyclic direct image also preserves vanishing of the actual module cohomology. -/
theorem acyclicPushforward_moduleH_subsingleton_iff (n : ℕ) :
    Subsingleton (ModuleH ((pushforward f).obj M) n) ↔ Subsingleton (ModuleH M n) := by
  constructor
  · intro h
    let _vanishing := h
    exact (acyclicPushforwardModuleHEquiv f M hM n).symm.injective.subsingleton
  · intro h
    let _vanishing := h
    exact (acyclicPushforwardModuleHEquiv f M hM n).injective.subsingleton

end FLT.Mazur.FCurve
