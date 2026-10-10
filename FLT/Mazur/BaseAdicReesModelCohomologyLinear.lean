/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesModelCohomologyHomogeneous

/-!
# Rees linearity of the original cohomology comparison

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
  (M : X.Modules) [M.IsFinitePresentation] (q : ℕ)

attribute [local irreducible] modelPowerToModelEquiv globalModelSheaf
  modelCohomologyScalars powerReesRepresentation

/-- Homogeneous scalars act compatibly on every finite sum of original power classes. -/
lemma modelPowerToModelEquiv_monomial (a : ℕ) (r : ↥(J ^ a))
    (s : PowerCohomologySum (baseCohomologyScalars f) ((baseIdeal R J).comap f) M q) :
    let _ := powerReesModule (baseCohomologyScalars f) ((baseIdeal R J).comap f)
      M J (BaseAdicCohomology.scalar_mem f J) q
    modelPowerToModelEquiv f J M q (Rees.monomial J a r • s) =
      Rees.monomial J a r • modelPowerToModelEquiv f J M q s := by
  let _ := powerReesModule (baseCohomologyScalars f) ((baseIdeal R J).comap f)
    M J (BaseAdicCohomology.scalar_mem f J) q
  induction s using DirectSum.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  | of n s => exact modelPowerToModelEquiv_monomial_of f J M q a n r s

/-- Every original Rees scalar is retained by the actual all-degree cohomology comparison. -/
lemma modelPowerToModelEquiv_smul (p : reesAlgebra J)
    (s : PowerCohomologySum (baseCohomologyScalars f) ((baseIdeal R J).comap f) M q) :
    let _ := powerReesModule (baseCohomologyScalars f) ((baseIdeal R J).comap f)
      M J (BaseAdicCohomology.scalar_mem f J) q
    modelPowerToModelEquiv f J M q (p • s) =
      p • modelPowerToModelEquiv f J M q s := by
  let _ := powerReesModule (baseCohomologyScalars f) ((baseIdeal R J).comap f)
    M J (BaseAdicCohomology.scalar_mem f J) q
  obtain ⟨p, rfl⟩ := (Rees.sumRingEquiv J).surjective p
  induction p using DirectSum.induction_on with
  | zero => simp only [map_zero, zero_smul]
  | add p t hp ht => simp only [map_add, add_smul, hp, ht]
  | of a r =>
    change modelPowerToModelEquiv f J M q
      (Rees.sumRingHom J (DirectSum.of (fun n ↦ ↥(J ^ n)) a r) • s) =
      Rees.sumRingHom J (DirectSum.of (fun n ↦ ↥(J ^ n)) a r) •
        modelPowerToModelEquiv f J M q s
    rw [Rees.sumRingHom_of]
    exact modelPowerToModelEquiv_monomial f J M q a r s

/-- The original additive comparison admits the proved Rees-linear structure. -/
theorem modelPowerReesEquiv_exists :
    let _ := powerReesModule (baseCohomologyScalars f) ((baseIdeal R J).comap f)
      M J (BaseAdicCohomology.scalar_mem f J) q
    ∃ e : PowerCohomologySum (baseCohomologyScalars f) ((baseIdeal R J).comap f) M q
        ≃ₗ[reesAlgebra J]
          ModuleRingH (modelCohomologyScalars f J) (globalModelSheaf f J M) q,
      e.toAddEquiv = modelPowerToModelEquiv f J M q := by
  let _ := powerReesModule (baseCohomologyScalars f) ((baseIdeal R J).comap f)
    M J (BaseAdicCohomology.scalar_mem f J) q
  exact ⟨(modelPowerToModelEquiv f J M q).toLinearEquiv
    (modelPowerToModelEquiv_smul f J M q), rfl⟩

/-- The original power sum is Rees-linearly equivalent to actual model cohomology. -/
def modelPowerReesEquiv :
    let _ := powerReesModule (baseCohomologyScalars f) ((baseIdeal R J).comap f)
      M J (BaseAdicCohomology.scalar_mem f J) q
    PowerCohomologySum (baseCohomologyScalars f) ((baseIdeal R J).comap f) M q ≃ₗ[reesAlgebra J]
      ModuleRingH (modelCohomologyScalars f J) (globalModelSheaf f J M) q :=
  Classical.choose (modelPowerReesEquiv_exists f J M q)

/-- The Rees-linear comparison keeps the original additive comparison exactly. -/
lemma modelPowerReesEquiv_toAddEquiv :
    let _ := powerReesModule (baseCohomologyScalars f) ((baseIdeal R J).comap f)
      M J (BaseAdicCohomology.scalar_mem f J) q
    (modelPowerReesEquiv f J M q).toAddEquiv = modelPowerToModelEquiv f J M q :=
  Classical.choose_spec (modelPowerReesEquiv_exists f J M q)

end FLT.Mazur.BaseAdicRees
