/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudCyclicCharacterEquations

/-!
# Nonvanishing of actual character coordinates at nonzero points

The nonzero points of a scalar line form one orbit. An augmentation
character coordinate vanishing on that orbit vanishes everywhere, contradicting
injectivity of generic evaluation and the proved rank-one generator property.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open IsLocalRing

variable {R K F : Type} [CommRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] [Field F]
  (X : FF R K) [Module F X.Points]
  (lift : F → ModelHom X X) (h1 : lift 1 = BialgHom.id R X.CoordinateRing)
  (hmul : ∀ a b, lift (a * b) = (lift b).comp (lift a))
  (hlift : ∀ a x, genericHom (lift a) x = a • x)

include hlift

omit [IsFractionRing R K] in
/-- Evaluation of an actual integral character vector respects its scalar character. -/
theorem FF.integralCharacter_eval_scalar (χ : Fˣ →* Rˣ)
    (c : X.integralCharacter lift h1 hmul χ) (u : Fˣ) (x : X.Points) :
    X.characterCoordinates (c.val : X.CoordinateRing) ((u : F) • x) =
      algebraMap R (AlgebraicClosure K) (χ u : R) *
        X.characterCoordinates (c.val : X.CoordinateRing) x := by
  rw [← hlift, ← ModelHom.characterCoordinates_apply,
    X.integralCharacter_scalar lift h1 hmul χ c u, map_smul]
  change (MulActionHom.evalAlgHom _ R X.Points (AlgebraicClosure K) x)
    ((χ u : R) • X.characterCoordinates (c.val : X.CoordinateRing)) = _
  rw [map_smul, Algebra.smul_def]
  rfl

/-- Every nonzero integral character vector is nonzero at every nonzero point of a scalar line. -/
theorem FF.integralCharacter_eval_ne_zero (hdim : Module.finrank F X.Points = 1)
    (χ : Fˣ →* Rˣ) (c : X.integralCharacter lift h1 hmul χ) (hc : c ≠ 0)
    (x : X.Points) (hx : x ≠ 0) :
    X.characterCoordinates (c.val : X.CoordinateRing) x ≠ 0 := by
  intro hzero
  apply hc
  apply Subtype.ext
  apply Subtype.ext
  apply X.characterCoordinates_injective
  simp only [ZeroMemClass.coe_zero, map_zero]
  ext y
  change X.characterCoordinates (c.val : X.CoordinateRing) y = 0
  by_cases hy : y = 0
  · rw [hy, X.characterCoordinates_counit, c.val.property, map_zero]
  · obtain ⟨u, rfl⟩ := CharacterRank.scalar_orbit hdim x y hx hy
    rw [X.integralCharacter_eval_scalar lift h1 hmul hlift χ c u x, hzero, mul_zero]

variable [IsDomain R] [IsPrincipalIdealRing R] [HenselianLocalRing R]
  [IsSepClosed (ResidueField R)] [Fintype F] [DecidableEq F]
  (p : ℕ) [CharP F p] [CharP (ResidueField R) p]
  (hdim : Module.finrank F X.Points = 1)

/-- The actual fundamental coordinate is nonzero at any nonidentity generic point. -/
theorem FF.fundamentalCoordinate_eval_ne_zero (e : F →+* ResidueField R)
    (i : ℕ) (x : X.Points) (hx : x ≠ 0) :
    X.characterCoordinates (X.fundamentalCoordinate p lift h1 hmul hdim hlift e i) x ≠ 0 := by
  exact X.integralCharacter_eval_ne_zero lift h1 hmul hlift hdim
    (fundamentalCharacter p e ^ (p ^ i))
    (X.characterBasis lift h1 hmul p hdim hlift _ ())
    ((X.characterBasis lift h1 hmul p hdim hlift _).ne_zero ()) x hx

end ThreeAdicPlan
