/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorComplementFaithful

/-!
# Base-field linear pole functions

The scalar action is induced by the actual composite map from the divisor
complement to the specified base field. The pole filtration consists of
linear subspaces, each linearly equivalent to the original H0 space.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {k : Type} [Field k] {X : Scheme} (f : X ⟶ Spec (.of k))
  (I : X.IdealSheafData)

/-- Complement functions with scalars from the actual base morphism. -/
def divisorComplementModule : ModuleCat k := by
  let _ := Module.compHom Γ((Scheme.Opens.toScheme (X := X) I.support.compl), ⊤)
    (structureScalarMap ((Scheme.Opens.ι (X := X) I.support.compl) ≫ f))
  exact ModuleCat.of k Γ((Scheme.Opens.toScheme (X := X) I.support.compl), ⊤)

variable {I} (hI : EffectiveCartier I)

/-- Complement coordinates preserve the action of ambient global regular functions. -/
theorem divisorComplementFunction_smul (m : ℕ) (r : Γ(X, ⊤))
    (s : Γ(tensorPower (divisorLineBundle I hI) m, ⊤)) :
    divisorComplementFunction hI m (r • s) =
      (Scheme.Opens.ι (X := X) I.support.compl).appTop r * divisorComplementFunction hI m s := by
  unfold divisorComplementFunction
  rw [Scheme.Modules.map_smul, SectionGradedLocalCoordinates.coordinate_smul]
  rfl

/-- The original H0 function map respects the specified base-field scalars. -/
def divisorPowerH0FunctionLinear (m : ℕ) :
    ModuleScalarH f (tensorPower (divisorLineBundle I hI) m) 0 →ₗ[k]
      divisorComplementModule f I where
  toFun := divisorPowerH0Function f hI m
  map_add' x y := by
    unfold divisorPowerH0Function
    rw [map_add, divisorComplementFunction_add]
  map_smul' a x := by
    let _ := Module.compHom
      ((tensorPower (divisorLineBundle I hI) m).val.obj (Opposite.op ⊤))
      (structureScalarMap f)
    change divisorComplementFunction hI m
        (moduleScalarH0Equiv f _ (a • x)) =
      structureScalarMap ((Scheme.Opens.ι (X := X) I.support.compl) ≫ f) a *
        divisorPowerH0Function f hI m x
    rw [map_smul]
    change divisorComplementFunction hI m
        (structureScalarMap f a • moduleScalarH0Equiv f _ x) = _
    rw [divisorComplementFunction_smul]
    have hs : structureScalarMap ((Scheme.Opens.ι (X := X) I.support.compl) ≫ f) a =
        (Scheme.Opens.ι (X := X) I.support.compl).appTop (structureScalarMap f a) := by
      simp [structureScalarMap]
    rw [hs]
    rfl

/-- Original pole bounds form subspaces for the actual field action. -/
def divisorPoleSubmodule (m : ℕ) : Submodule k (divisorComplementModule f I) :=
  (divisorPowerH0FunctionLinear f hI m).range

/-- The linear pole space has exactly the previously constructed functions as its elements. -/
theorem mem_divisorPoleSubmodule (m : ℕ) (a : divisorComplementModule f I) :
    a ∈ divisorPoleSubmodule f hI m ↔ a ∈ divisorPoleFunctions hI m :=
  (mem_divisorPoleFunctions_iff_h0 f hI m a).symm

/-- Original degree-zero cohomology and its function space are linearly equivalent. -/
def divisorPowerH0PoleEquiv (m : ℕ) :
    ModuleScalarH f (tensorPower (divisorLineBundle I hI) m) 0 ≃ₗ[k]
      divisorPoleSubmodule f hI m :=
  LinearEquiv.ofInjective (divisorPowerH0FunctionLinear f hI m)
    (divisorPowerH0Function_injective hI f m)

/-- The faithful function space retains the exact H0 dimension. -/
theorem divisorPoleSubmodule_finrank (m : ℕ) :
    Module.finrank k (divisorPoleSubmodule f hI m) =
      Module.finrank k (ModuleScalarH f (tensorPower (divisorLineBundle I hI) m) 0) :=
  (divisorPowerH0PoleEquiv f hI m).finrank_eq.symm

/-- The base-field pole subspaces form an increasing filtration. -/
theorem divisorPoleSubmodule_mono : Monotone (divisorPoleSubmodule f hI) := by
  intro m n h a ha
  exact (mem_divisorPoleSubmodule f hI n a).mpr
    (divisorPoleFunctions_mono hI h ((mem_divisorPoleSubmodule f hI m a).mp ha))

end FLT.Mazur.FCurve
