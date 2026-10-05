/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteSupportEulerCharacteristic
public import FLT.Mazur.AffineModuleGlobalSections

/-!
# Positivity of finite-support Euler characteristic

Global sections detect a coherent sheaf supported on finitely many points:
closed descent reduces this to the affine section reconstruction. Its positive
cohomology vanishes, so every nonzero such sheaf has positive Euler characteristic.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open Scheme.Modules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FLT.Mazur.FCurve

open FLT.Mazur.AffineModuleGlobalSections CoherentDevissage

variable {k : Type} [Field k] {X : Scheme}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]

include f in
/-- A finite-support coherent sheaf with zero global sections is zero. -/
theorem finiteSupport_isZero_of_sections (M : X.Modules) [M.IsFinitePresentation]
    (hM : (support M).Finite) [Subsingleton Γ(M, ⊤)] : IsZero M := by
  obtain ⟨I, N, hI, hN, ⟨e⟩⟩ := exists_finiteClosed_descent f M hM
  have : IsAffine I.subscheme := isAffine_of_isAffineHom (I.subschemeι ≫ f)
  have : Subsingleton ((sections X).obj M) := inferInstanceAs (Subsingleton Γ(M, ⊤))
  have : Subsingleton ((sections X).obj ((pushforward I.subschemeι).obj N)) :=
    ((sections X).mapIso e).toLinearEquiv.injective.subsingleton
  have : Subsingleton ((sections I.subscheme).obj N) :=
    inferInstanceAs (Subsingleton ((sections X).obj ((pushforward I.subschemeι).obj N)))
  have hz : IsZero N :=
    ((affineTilde I.subscheme).map_isZero (ModuleCat.isZero_of_subsingleton
      ((sections I.subscheme).obj N))).of_iso
        (asIso ((affineAdjunction I.subscheme).counit.app N)).symm
  exact ((pushforward I.subschemeι).map_isZero hz).of_iso e.symm

/-- A nonzero finite-support coherent sheaf has positive H⁰ dimension. -/
theorem finiteSupport_h0_pos (M : X.Modules) [M.IsFinitePresentation]
    (hM : (support M).Finite) (hne : ¬ IsZero M) :
    0 < Module.finrank k (ModuleScalarH f M 0) := by
  have := proper_coherent_hasFiniteCohomology f M 0
  by_contra h
  have hz : Module.finrank k (ModuleScalarH f M 0) = 0 := Nat.eq_zero_of_not_pos h
  have := (Module.finrank_zero_iff (R := k) (M := ModuleScalarH f M 0)).mp hz
  have : Subsingleton Γ(M, ⊤) := (moduleScalarH0Equiv f M).symm.injective.subsingleton
  exact hne (finiteSupport_isZero_of_sections f M hM)

/-- A nonzero finite-support coherent coefficient has positive Euler characteristic. -/
theorem finiteSupport_euler_pos (M : X.Modules) [M.IsFinitePresentation]
    (hM : (support M).Finite) (hne : ¬ IsZero M) : 0 < curveEulerCharacteristic f M := by
  have := finiteSupport_cohomology_subsingleton f M hM 1 (by decide)
  have hp := finiteSupport_h0_pos f M hM hne
  unfold curveEulerCharacteristic
  rw [Module.finrank_zero_of_subsingleton (R := k) (M := ModuleScalarH f M 1),
    Nat.cast_zero, sub_zero]
  exact_mod_cast hp

end FLT.Mazur.FCurve
