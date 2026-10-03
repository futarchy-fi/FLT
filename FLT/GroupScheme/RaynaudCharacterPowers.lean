/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudCharacterRankOne

/-!
# Power relations in the derived character spaces

Scalar maps are algebra maps, so a positive power of a character vector
belongs to the corresponding power character. The rank-one theorem then
expresses it in the actual generator of that space.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open CharacterProjector IsLocalRing

variable {R K F : Type} [CommRing R] [Field K] [Algebra R K] [Field F]
  (X : FF R K) (lift : F → ModelHom X X)
  (h1 : lift 1 = BialgHom.id R X.CoordinateRing)
  (hmul : ∀ a b, lift (a * b) = (lift b).comp (lift a))

/-- Products of augmentation eigenvectors have the product character. -/
def FF.integralCharacterMul (χ ψ : Fˣ →* Rˣ)
    (a : X.integralCharacter lift h1 hmul χ) (b : X.integralCharacter lift h1 hmul ψ) :
    X.integralCharacter lift h1 hmul (χ * ψ) :=
  ⟨⟨(a.val : X.CoordinateRing) * b.val, by
    change (Bialgebra.counitAlgHom R X.CoordinateRing)
      ((a.val : X.CoordinateRing) * b.val) = 0
    rw [map_mul]
    change Coalgebra.counit (a.val : X.CoordinateRing) * _ = 0
    rw [a.val.property, zero_mul]⟩, by
    apply (mem_eigenspace_iff _ _ _).mpr
    intro u
    apply Subtype.ext
    change lift u ((a.val : X.CoordinateRing) * b.val) = ((χ * ψ) u : R) • _
    rw [map_mul, X.integralCharacter_scalar lift h1 hmul χ a u,
      X.integralCharacter_scalar lift h1 hmul ψ b u]
    simp [Algebra.smul_def, mul_mul_mul_comm]⟩

/-- Positive powers of integral character vectors have the power character. -/
def FF.integralCharacterPow (χ : Fˣ →* Rˣ)
    (a : X.integralCharacter lift h1 hmul χ) (n : ℕ) (hn : n ≠ 0) :
    X.integralCharacter lift h1 hmul (χ ^ n) :=
  ⟨⟨(a.val : X.CoordinateRing) ^ n, by
    change Coalgebra.counit ((a.val : X.CoordinateRing) ^ n) = 0
    change (Bialgebra.counitAlgHom R X.CoordinateRing) ((a.val : X.CoordinateRing) ^ n) = 0
    rw [map_pow]
    change (Coalgebra.counit (a.val : X.CoordinateRing)) ^ n = 0
    rw [a.val.property, zero_pow hn]⟩, by
    apply (mem_eigenspace_iff _ _ _).mpr
    intro u
    apply Subtype.ext
    change lift u ((a.val : X.CoordinateRing) ^ n) = ((χ ^ n) u : R) • _
    rw [map_pow, X.integralCharacter_scalar lift h1 hmul χ a u]
    simp [Algebra.smul_def, mul_pow]⟩

variable [IsDomain R] [IsPrincipalIdealRing R] [HenselianLocalRing R]
  [IsSepClosed (ResidueField R)] [PerfectField K] [IsFractionRing R K]
  [Finite F] [Module F X.Points]
  (p : ℕ) [CharP F p] [CharP (ResidueField R) p]
  (hdim : Module.finrank F X.Points = 1)
  (hlift : ∀ a x, genericHom (lift a) x = a • x)

/-- Choose the generator from the proved rank-one eigenspace. -/
def FF.characterBasis (χ : Fˣ →* Rˣ) :
    Module.Basis Unit R (X.integralCharacter lift h1 hmul χ) :=
  (X.exists_integralCharacter_basis p lift h1 hmul hdim hlift χ).some

/-- The chosen character generator viewed in the actual coordinate ring. -/
def FF.characterGenerator (χ : Fˣ →* Rˣ) : X.CoordinateRing :=
  (X.characterBasis lift h1 hmul p hdim hlift χ ()).val

/-- Every positive power of the chosen generator has an actual integral coefficient. -/
theorem FF.character_power_relation (χ : Fˣ →* Rˣ) (n : ℕ) (hn : n ≠ 0) :
    ∃ c : R,
      X.characterGenerator lift h1 hmul p hdim hlift χ ^ n =
        c • X.characterGenerator lift h1 hmul p hdim hlift (χ ^ n) := by
  let b := X.characterBasis lift h1 hmul p hdim hlift (χ ^ n)
  let a := X.integralCharacterPow lift h1 hmul χ
    (X.characterBasis lift h1 hmul p hdim hlift χ ()) n hn
  refine ⟨b.repr a (), ?_⟩
  have h : b.repr a () • b () = a := by simpa using b.sum_repr a
  exact (congrArg (fun z : X.integralCharacter lift h1 hmul (χ ^ n) ↦
    (z.val : X.CoordinateRing)) h).symm

end ThreeAdicPlan
