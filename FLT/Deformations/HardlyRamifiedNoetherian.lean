/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.HardlyRamifiedTangentFinite
public import FLT.Deformations.ContinuousTangentAdic
public import FLT.Deformations.PowerSeriesPresentation

/-!
# Noetherianity of the actual hardly ramified parameter rings

Arithmetic parameter finiteness supplies finite continuous tangents. The
proved topology comparison and finite-variable power-series presentation
then give Noetherianity of the framed quotient and the matched trace image.
No Noetherianity of the unrestricted trace source or of a subring is used.
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

/-- The actual maximal ideal is finitely generated. -/
theorem hardlyFramed_maximalIdeal_fg : (IsLocalRing.maximalIdeal H).FG := by
  let := finite_hardlyFramedContinuousTangent O hp hdim ρ hρ
  exact maximalIdeal_fg_of_finite_continuousTangent H

/-- The given topology is the maximal-ideal-adic topology. -/
theorem hardlyFramed_isAdicTopology : IsLocalRing.IsAdicTopology H := by
  let := finite_hardlyFramedContinuousTangent O hp hdim ρ hρ
  exact isAdicTopology_of_finite_continuousTangent H

/-- The actual ring is adically complete. -/
theorem hardlyFramed_isAdicComplete : IsAdicComplete (IsLocalRing.maximalIdeal H) H := by
  let := finite_hardlyFramedContinuousTangent O hp hdim ρ hρ
  exact isAdicComplete_of_finite_continuousTangent H

/-- A finite-variable power-series presentation over the original coefficients. -/
theorem hardlyFramed_exists_powerSeries_surjection :
    ∃ n : ℕ, ∃ f : MvPowerSeries (Fin n) O →ₐ[O] H, Function.Surjective f :=
  exists_powerSeries_surjection_of_maximalIdeal_fg H
    (hardlyFramed_maximalIdeal_fg O hp hdim ρ hρ)

/-- The actual framed HR ring is Noetherian. -/
theorem hardlyFramed_isNoetherianRing : IsNoetherianRing H :=
  isNoetherianRing_of_maximalIdeal_fg H
    (hardlyFramed_maximalIdeal_fg O hp hdim ρ hρ)

include hirr in
/-- The actual maximal ideal is finitely generated. -/
theorem hardlyTrace_maximalIdeal_fg : (IsLocalRing.maximalIdeal T).FG := by
  let := finite_hardlyTraceContinuousTangent O hp hdim ρ hρ hirr
  exact maximalIdeal_fg_of_finite_continuousTangent T

include hirr in
/-- The given topology is the maximal-ideal-adic topology. -/
theorem hardlyTrace_isAdicTopology : IsLocalRing.IsAdicTopology T := by
  let := finite_hardlyTraceContinuousTangent O hp hdim ρ hρ hirr
  exact isAdicTopology_of_finite_continuousTangent T

include hirr in
/-- The actual ring is adically complete. -/
theorem hardlyTrace_isAdicComplete : IsAdicComplete (IsLocalRing.maximalIdeal T) T := by
  let := finite_hardlyTraceContinuousTangent O hp hdim ρ hρ hirr
  exact isAdicComplete_of_finite_continuousTangent T

include hirr in
/-- A finite-variable power-series presentation over the original coefficients. -/
theorem hardlyTrace_exists_powerSeries_surjection :
    ∃ n : ℕ, ∃ f : MvPowerSeries (Fin n) O →ₐ[O] T, Function.Surjective f :=
  exists_powerSeries_surjection_of_maximalIdeal_fg T
    (hardlyTrace_maximalIdeal_fg O hp hdim ρ hρ hirr)

include hirr in
/-- The actual trace HR ring is Noetherian. -/
theorem hardlyTrace_isNoetherianRing : IsNoetherianRing T :=
  isNoetherianRing_of_maximalIdeal_fg T
    (hardlyTrace_maximalIdeal_fg O hp hdim ρ hρ hirr)

end Deformation
