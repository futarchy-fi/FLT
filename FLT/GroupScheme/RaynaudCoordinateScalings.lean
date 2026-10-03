/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudCharacterMorphism
public import FLT.GroupScheme.RaynaudPairedCharacterBases

/-!
# Derived integral coordinate scalings

Pullback on the actual rank-one character lines determines integral
coefficients. Generic bijectivity makes them nonzero, and the actual
power equations imply their cyclic compatibility relation.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open IsLocalRing

variable {R K F : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [HenselianLocalRing R] [IsSepClosed (ResidueField R)] [Field K] [Algebra R K]
  [CharZero K] [IsFractionRing R K] [Field F] [Finite F] [Fintype Fˣ]
  [Invertible (Fintype.card Fˣ : R)] {X Y : FF R K}
  [Module F X.Points] [Module F Y.Points] (f : ModelHom X Y)
  (sx : F → ModelHom X X) (sy : F → ModelHom Y Y)
  (hx1 : sx 1 = BialgHom.id R X.CoordinateRing)
  (hy1 : sy 1 = BialgHom.id R Y.CoordinateRing)
  (hxm : ∀ a b, sx (a * b) = (sx b).comp (sx a))
  (hym : ∀ a b, sy (a * b) = (sy b).comp (sy a))
  (hcomm : ∀ a, f.comp (sy a) = (sx a).comp f)
  (p : ℕ) [CharP F p] [CharP (ResidueField R) p]
  (hdx : Module.finrank F X.Points = 1) (hdy : Module.finrank F Y.Points = 1)
  (hsx : ∀ a x, genericHom (sx a) x = a • x)
  (hsy : ∀ a y, genericHom (sy a) y = a • y)

/-- The integral scaling determined by the actual character bases and coordinate pullback. -/
def ModelHom.characterScaling (χ : Fˣ →* Rˣ) : R :=
  (X.characterBasis sx hx1 hxm p hdx hsx χ).repr
    (f.integralCharacterMap sx sy hx1 hy1 hxm hym hcomm χ
      (Y.characterBasis sy hy1 hym p hdy hsy χ ())) ()

omit [Fintype Fˣ] [Invertible (Fintype.card Fˣ : R)] in
/-- Pullback of a character generator is its derived scaling times the target generator. -/
theorem ModelHom.characterScaling_spec (χ : Fˣ →* Rˣ) :
    f (Y.characterGenerator sy hy1 hym p hdy hsy χ) =
      f.characterScaling sx sy hx1 hy1 hxm hym hcomm p hdx hdy hsx hsy χ •
        X.characterGenerator sx hx1 hxm p hdx hsx χ := by
  let b := X.characterBasis sx hx1 hxm p hdx hsx χ
  let v := f.integralCharacterMap sx sy hx1 hy1 hxm hym hcomm χ
    (Y.characterBasis sy hy1 hym p hdy hsy χ ())
  have h : b.repr v () • b () = v := by simpa using b.sum_repr v
  exact (congrArg (fun z : X.integralCharacter sx hx1 hxm χ ↦
    (z.val : X.CoordinateRing)) h).symm

omit [Fintype Fˣ] [Invertible (Fintype.card Fˣ : R)] in
/-- Generic surjectivity forces every integral character scaling to be nonzero. -/
theorem ModelHom.characterScaling_ne_zero (hf : Function.Surjective (genericHom f))
    (χ : Fˣ →* Rˣ) :
    f.characterScaling sx sy hx1 hy1 hxm hym hcomm p hdx hdy hsx hsy χ ≠ 0 := by
  intro hz
  have he := f.characterScaling_spec sx sy hx1 hy1 hxm hym hcomm p hdx hdy hsx hsy χ
  rw [hz, zero_smul] at he
  have hgen : Y.characterGenerator sy hy1 hym p hdy hsy χ = 0 :=
    f.injective_of_generic_surjective hf (he.trans (map_zero f).symm)
  apply (Y.characterBasis sy hy1 hym p hdy hsy χ).ne_zero ()
  apply Subtype.ext
  apply Subtype.ext
  exact hgen

/-- Comparing actual power equations gives the cyclic scaling relation. -/
theorem ModelHom.characterScaling_power (χ : Fˣ →* Rˣ) (n : ℕ) (ax ay : R)
    (hx : X.characterGenerator sx hx1 hxm p hdx hsx χ ^ n =
      ax • X.characterGenerator sx hx1 hxm p hdx hsx (χ ^ n))
    (hy : Y.characterGenerator sy hy1 hym p hdy hsy χ ^ n =
      ay • Y.characterGenerator sy hy1 hym p hdy hsy (χ ^ n)) :
    f.characterScaling sx sy hx1 hy1 hxm hym hcomm p hdx hdy hsx hsy χ ^ n * ax =
      ay * f.characterScaling sx sy hx1 hy1 hxm hym hcomm p hdx hdy hsx hsy (χ ^ n) := by
  have he := congrArg f hy
  rw [map_pow, map_smul,
    f.characterScaling_spec sx sy hx1 hy1 hxm hym hcomm p hdx hdy hsx hsy χ,
    f.characterScaling_spec sx sy hx1 hy1 hxm hym hcomm p hdx hdy hsx hsy (χ ^ n),
    smul_pow, hx, smul_smul, smul_smul] at he
  let φ : HopfAlgebra.CartierDual R X.CoordinateRing :=
    X.dualCharacterGenerator sx hx1 hxm p hdx hsx (χ ^ n)
  have hp : φ.ofConv (X.characterGenerator sx hx1 hxm p hdx hsx (χ ^ n)) = 1 :=
    X.characterGenerator_pairing sx hx1 hxm p hdx hsx (χ ^ n)
  have h := congrArg φ.ofConv he
  simpa only [map_smul, hp, smul_eq_mul, mul_one] using h

end ThreeAdicPlan
