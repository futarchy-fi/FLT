/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativePoleComplementFunctions

/-!
# Faithful base-ring linear relative pole functions

The actual relative function maps are injective and linear for the original
composite scalar map. Their ranges form the original increasing pole filtration.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle

variable {X S : Scheme.{0}} (f : X ⟶ S) (s : S ⟶ X) (hI : EffectiveCartier s.ker)

/-- The original complement ring viewed as a module over the base section ring. -/
def relativePoleComplementModule : ModuleCat Γ(S, ⊤) := by
  let φ := (Scheme.Opens.ι (X := X) s.ker.support.compl).appTop.hom.comp f.appTop.hom
  let _ := Module.compHom Γ(Scheme.Opens.toScheme (X := X) s.ker.support.compl, ⊤) φ
  exact ModuleCat.of Γ(S, ⊤) Γ(Scheme.Opens.toScheme (X := X) s.ker.support.compl, ⊤)

/-- The original complement function map with its base-ring linear structure. -/
def relativePoleFunctionLinear (m : ℕ) :
    ModuleRingH f.appTop.hom (tensorPower (divisorLineBundle s.ker hI) m) 0 →ₗ[Γ(S, ⊤)]
      relativePoleComplementModule f s where
  toFun := relativePoleFunction f s hI m
  map_add' := relativePoleFunction_add f s hI m
  map_smul' := relativePoleFunction_smul f s hI m

/-- The actual complement function determines the entire original H0 section. -/
theorem relativePoleFunction_injective (m : ℕ) :
    Function.Injective (relativePoleFunction f s hI m) :=
  (divisorComplementFunction_injective hI m).comp (moduleH0Equiv _).injective

/-- The original relative pole functions of a fixed degree form a base-ring submodule. -/
def relativePoleSubmodule (m : ℕ) : Submodule Γ(S, ⊤) (relativePoleComplementModule f s) :=
  (relativePoleFunctionLinear f s hI m).range

/-- The original H0 module is linearly equivalent to its actual function image. -/
def relativePoleFunctionEquiv (m : ℕ) :
    ModuleRingH f.appTop.hom (tensorPower (divisorLineBundle s.ker hI) m) 0 ≃ₗ[Γ(S, ⊤)]
      relativePoleSubmodule f s hI m :=
  LinearEquiv.ofInjective (relativePoleFunctionLinear f s hI m)
    (relativePoleFunction_injective f s hI m)

/-- The original divisor transition includes each function space in the next one. -/
theorem relativePoleSubmodule_le_succ (m : ℕ) :
    relativePoleSubmodule f s hI m ≤ relativePoleSubmodule f s hI (m + 1) := by
  rintro z ⟨w, rfl⟩
  exact ⟨divisorPowerRingStep f.appTop.hom hI m w, relativePoleFunction_step f s hI m w⟩

/-- The actual base-ring pole submodules form an increasing filtration. -/
theorem relativePoleSubmodule_mono : Monotone (relativePoleSubmodule f s hI) :=
  monotone_nat_of_le_succ (relativePoleSubmodule_le_succ f s hI)

end FLT.Mazur.FCurve
