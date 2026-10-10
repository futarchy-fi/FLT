/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesModelHZeroHomogeneous

/-!
# Rees linearity of the original H0 comparison

Finite addition in both the scalar Rees algebra and the original power
cohomology sum extends the homogeneous comparison to all elements.
Both module structures are the original ones, constructed before this equivalence.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules FLT.Mazur.BaseAdicThickening FLT.Mazur.Chow.AffineBase
open FLT.Mazur.FCurve FLT.Mazur.IdealAdicQuotient
open scoped DirectSum

namespace FLT.Mazur.BaseAdicRees

variable {R : CommRingCat.{0}} [IsNoetherianRing R]
  {X : Scheme.{0}} [X.IsSeparated] (f : X ⟶ Spec R) (J : Ideal R)
  [IsLocallyNoetherian X] [TopologicalSpace.NoetherianSpace X]
  (M : X.Modules) [M.IsFinitePresentation]

attribute [local irreducible] modelPowerHZeroToModelEquiv globalModelSheaf
  modelCohomologyScalars powerReesRepresentation

/-- Homogeneous scalars act compatibly on every finite sum of original power classes. -/
lemma modelPowerHZeroToModelEquiv_monomial (a : ℕ) (r : ↥(J ^ a))
    (s : PowerCohomologySum (baseCohomologyScalars f) ((baseIdeal R J).comap f) M 0) :
    let _ := powerReesModule (baseCohomologyScalars f) ((baseIdeal R J).comap f)
      M J (BaseAdicCohomology.scalar_mem f J) 0
    modelPowerHZeroToModelEquiv f J M (Rees.monomial J a r • s) =
      Rees.monomial J a r • modelPowerHZeroToModelEquiv f J M s := by
  let _ := powerReesModule (baseCohomologyScalars f) ((baseIdeal R J).comap f)
    M J (BaseAdicCohomology.scalar_mem f J) 0
  induction s using DirectSum.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  | of n s => exact modelPowerHZeroToModelEquiv_monomial_of f J M a n r s

/-- Every original Rees scalar is retained by the actual H0 comparison. -/
lemma modelPowerHZeroToModelEquiv_smul (p : reesAlgebra J)
    (s : PowerCohomologySum (baseCohomologyScalars f) ((baseIdeal R J).comap f) M 0) :
    let _ := powerReesModule (baseCohomologyScalars f) ((baseIdeal R J).comap f)
      M J (BaseAdicCohomology.scalar_mem f J) 0
    modelPowerHZeroToModelEquiv f J M (p • s) =
      p • modelPowerHZeroToModelEquiv f J M s := by
  let _ := powerReesModule (baseCohomologyScalars f) ((baseIdeal R J).comap f)
    M J (BaseAdicCohomology.scalar_mem f J) 0
  obtain ⟨p, rfl⟩ := (Rees.sumRingEquiv J).surjective p
  induction p using DirectSum.induction_on with
  | zero => simp only [map_zero, zero_smul]
  | add p t hp ht => simp only [map_add, add_smul, hp, ht]
  | of a r =>
    change modelPowerHZeroToModelEquiv f J M
      (Rees.sumRingHom J (DirectSum.of (fun n ↦ ↥(J ^ n)) a r) • s) =
      Rees.sumRingHom J (DirectSum.of (fun n ↦ ↥(J ^ n)) a r) •
        modelPowerHZeroToModelEquiv f J M s
    rw [Rees.sumRingHom_of]
    exact modelPowerHZeroToModelEquiv_monomial f J M a r s

/-- The original H0 comparison admits the already proved Rees-linear structure. -/
theorem modelPowerHZeroReesEquiv_exists :
    let _ := powerReesModule (baseCohomologyScalars f) ((baseIdeal R J).comap f)
      M J (BaseAdicCohomology.scalar_mem f J) 0
    ∃ e : PowerCohomologySum (baseCohomologyScalars f) ((baseIdeal R J).comap f) M 0
        ≃ₗ[reesAlgebra J]
          ModuleRingH (modelCohomologyScalars f J) (globalModelSheaf f J M) 0,
      e.toAddEquiv = modelPowerHZeroToModelEquiv f J M := by
  let _ := powerReesModule (baseCohomologyScalars f) ((baseIdeal R J).comap f)
    M J (BaseAdicCohomology.scalar_mem f J) 0
  exact ⟨(modelPowerHZeroToModelEquiv f J M).toLinearEquiv
    (modelPowerHZeroToModelEquiv_smul f J M), rfl⟩

/-- The original power H0 sum is Rees-linearly equivalent to the actual model H0. -/
def modelPowerHZeroReesEquiv :
    let _ := powerReesModule (baseCohomologyScalars f) ((baseIdeal R J).comap f)
      M J (BaseAdicCohomology.scalar_mem f J) 0
    PowerCohomologySum (baseCohomologyScalars f) ((baseIdeal R J).comap f) M 0 ≃ₗ[reesAlgebra J]
      ModuleRingH (modelCohomologyScalars f J) (globalModelSheaf f J M) 0 :=
  Classical.choose (modelPowerHZeroReesEquiv_exists f J M)

/-- The Rees-linear comparison keeps the original additive comparison exactly. -/
lemma modelPowerHZeroReesEquiv_toAddEquiv :
    let _ := powerReesModule (baseCohomologyScalars f) ((baseIdeal R J).comap f)
      M J (BaseAdicCohomology.scalar_mem f J) 0
    (modelPowerHZeroReesEquiv f J M).toAddEquiv = modelPowerHZeroToModelEquiv f J M :=
  Classical.choose_spec (modelPowerHZeroReesEquiv_exists f J M)

end FLT.Mazur.BaseAdicRees
