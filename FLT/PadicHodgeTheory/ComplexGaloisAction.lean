/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.FieldTheory.KrullTopology

/-! # The Galois action on the completed algebraic closure -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
open UniformSpace
variable (p : ℕ) [Fact p.Prime]

/-- The algebraic Galois group, with its Krull topology. -/
abbrev PadicGalois := Gal(PadicAlgCl p/ℚ_[p])

/-- Algebraic automorphisms preserve the spectral norm. -/
theorem padicGalois_isometry (σ : PadicGalois p) : Isometry σ := by
  apply AddMonoidHomClass.isometry_of_norm σ
  intro x
  exact (spectralNorm_eq_of_equiv σ x).symm

/-- Extend an algebraic automorphism to the actual completion. -/
def complexGalois (σ : PadicGalois p) : ℂ_[p] →+* ℂ_[p] :=
  Completion.mapRingHom σ.toRingHom (padicGalois_isometry p σ).continuous

/-- The extension agrees with the original automorphism on algebraic points. -/
@[simp] theorem complexGalois_coe (σ : PadicGalois p) (x : PadicAlgCl p) :
    complexGalois p σ (x : ℂ_[p]) = (σ x : PadicAlgCl p) :=
  Completion.mapRingHom_coe _ _

/-- Every completed automorphism is an isometry. -/
theorem complexGalois_isometry (σ : PadicGalois p) : Isometry (complexGalois p σ) :=
  Completion.isometry_mapRingHom (padicGalois_isometry p σ)

/-- The identity extends to the identity. -/
@[simp] theorem complexGalois_one : complexGalois p 1 = RingHom.id _ :=
  Completion.mapRingHom_id

/-- Composition of algebraic automorphisms extends to composition. -/
theorem complexGalois_mul (σ τ : PadicGalois p) :
    complexGalois p (σ * τ) = (complexGalois p σ).comp (complexGalois p τ) := by
  ext x
  induction x using Completion.induction_on with
  | hp =>
    exact isClosed_eq (complexGalois_isometry p (σ * τ)).continuous
      ((complexGalois_isometry p σ).continuous.comp (complexGalois_isometry p τ).continuous)
  | ih a => simp only [RingHom.comp_apply, complexGalois_coe]; rfl

/-- The extended action preserves all ring operations. -/
instance instMulSemiringActionComplex : MulSemiringAction (PadicGalois p) ℂ_[p] where
  smul σ x := complexGalois p σ x
  one_smul x := congrArg (fun f : ℂ_[p] →+* ℂ_[p] ↦ f x) (complexGalois_one p)
  mul_smul σ τ x := congrArg (fun f : ℂ_[p] →+* ℂ_[p] ↦ f x)
    (complexGalois_mul p σ τ)
  smul_zero σ := map_zero (complexGalois p σ)
  smul_add σ := map_add (complexGalois p σ)
  smul_one σ := map_one (complexGalois p σ)
  smul_mul σ := map_mul (complexGalois p σ)

/-- Scalar notation denotes the constructed completion map. -/
theorem complex_smul_def (σ : PadicGalois p) (x : ℂ_[p]) :
    σ • x = complexGalois p σ x := rfl

/-- The completed action preserves the norm. -/
@[simp] theorem complexGalois_norm (σ : PadicGalois p) (x : ℂ_[p]) :
    ‖complexGalois p σ x‖ = ‖x‖ :=
  (complexGalois_isometry p σ).norm_map_of_map_zero (map_zero _) x

end PadicHodgeTheory
