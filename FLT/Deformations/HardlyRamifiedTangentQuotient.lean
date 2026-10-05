/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.HardlyRamifiedTangentFinite
public import FLT.Deformations.ContinuousTangentQuotient

/-!
# Finite quotients retaining the actual HR continuous tangent spaces

Each actual HR ring has a proper open finite quotient whose continuous tangent
space pulls back isomorphically over the original residue field. Every finer
open quotient retains the same tangent space. No Noetherianity is asserted.
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

/-- A finite quotient of the actual framed HR ring retains every continuous tangent. -/
theorem exists_hardlyFramedTangentQuotient :
    ∃ I : OpenIdeal H, ∀ J : OpenIdeal H, I ≤ J → Function.Bijective
      (continuousTangentPullback (openIdealQuotientHom H J)) := by
  let := finite_hardlyFramedContinuousTangent O hp hdim ρ hρ
  exact ⟨tangentOpenIdeal H, tangentOpenIdeal_finer_pullback_bijective H⟩

include hirr in
/-- The trace image has a finite quotient retaining every continuous tangent. -/
theorem exists_hardlyTraceTangentQuotient :
    ∃ I : OpenIdeal T, ∀ J : OpenIdeal T, I ≤ J → Function.Bijective
      (continuousTangentPullback (openIdealQuotientHom T J)) := by
  let := finite_hardlyTraceContinuousTangent O hp hdim ρ hρ hirr
  exact ⟨tangentOpenIdeal T, tangentOpenIdeal_finer_pullback_bijective T⟩

end Deformation
