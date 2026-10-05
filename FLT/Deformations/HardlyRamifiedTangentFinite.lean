/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.HardlyRamifiedParameterFiniteness
public import FLT.Deformations.ContinuousTangent

/-!
# Finite continuous tangent spaces for the actual HR rings

The arithmetic parameter-finiteness theorem applies to the original
residue-field dual numbers. Via the tangent equivalence this gives finite
dimensional continuous tangent spaces for the framed quotient and trace image.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory GaloisRepresentation
namespace Deformation
open ProartinianCat GaloisRepresentation.Extensions
variable (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)]
  {p : ℕ} [Fact p.Prime] (hp : Odd p)
  [Algebra ℤ_[p] (residueField (𝓞 := O))] [Algebra ℤ_[p] O]
  [IsScalarTower ℤ_[p] O (residueField (𝓞 := O))]
  {V : Type} [AddCommGroup V] [Module (residueField (𝓞 := O)) V]
  [Module.Finite (residueField (𝓞 := O)) V] [Module.Free (residueField (𝓞 := O)) V]
  (hdim : Module.rank (residueField (𝓞 := O)) V = 2)
  (ρ : GaloisRep ℚ (residueField (𝓞 := O)) V) (hρ : IsHardlyRamified hp hdim ρ)
local notation "G" => Field.absoluteGaloisGroup ℚ
local notation "H" => hardlyFlatObject O hp hdim ρ hρ

local notation "T" => hardlyTraceImageObject O hp hdim ρ hρ

variable (hirr : ρ.IsIrreducible)

/-- The continuous tangent space of the actual framed ring is a finite set. -/
theorem finite_hardlyFramedContinuousTangent : Finite (continuousTangent O H) := by
  let := finite_hardlyFramedParameters O hp hdim ρ hρ (dualNumberTest O)
  exact finite_continuousTangent O H

/-- Arithmetic finiteness gives finite dimension over the original residue field. -/
theorem finiteDimensional_hardlyFramedContinuousTangent :
    Module.Finite (residueField (𝓞 := O)) (continuousTangent O H) := by
  let := finite_hardlyFramedContinuousTangent O hp hdim ρ hρ
  exact Module.Finite.of_finite

include hirr in
/-- The continuous tangent space of the actual trace ring is a finite set. -/
theorem finite_hardlyTraceContinuousTangent : Finite (continuousTangent O T) := by
  let := finite_hardlyTraceParameters O hp hdim ρ hρ hirr (dualNumberTest O)
  exact finite_continuousTangent O T

include hirr in
/-- Arithmetic finiteness gives finite dimension over the original residue field. -/
theorem finiteDimensional_hardlyTraceContinuousTangent :
    Module.Finite (residueField (𝓞 := O)) (continuousTangent O T) := by
  let := finite_hardlyTraceContinuousTangent O hp hdim ρ hρ hirr
  exact Module.Finite.of_finite

end Deformation
