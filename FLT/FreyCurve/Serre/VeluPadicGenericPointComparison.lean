/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluLocalGenericPointComparison
public import FLT.Mazur.RationalPadicProjectiveSchemeTransport

/-!
# The prime quotient on the original rational p-adic projective sections

The actual local generic map agrees with the specified rational projective
transport at every prime, including the quotient prime. Both source and target
use their original local equations and actual variable changes.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ) [Fact p.Prime]
  (q : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p →ₗ[ZMod p] ZMod p)
  (hp : Odd p) (V : WeierstrassCurve ℚ)
  (hcurve : TorsionQuotientEquation E p (Nat.Prime.pos Fact.out) q V)
  (hfixed : ∀ g t, q (E.torsionGaloisRepresentation p g t) = q t)

local notation "EQ" => E.map (algebraMap ℚ (AlgebraicClosure ℚ))
local notation "GQ" => torsionKernel E p q

/-- Use the same canonical finite enumeration as the original point quotient. -/
local instance padicPointComparisonFintype : Fintype (torsionKernel E p q) :=
  @Fintype.ofFinite _ (torsionKernel_finite E p q (Nat.Prime.pos Fact.out))

/-- Cache the original enumeration on the actual mapped cubic. -/
local instance padicPointComparisonMappedFintype :
    Fintype (show AddSubgroup (EQ).toAffine.Point from GQ) :=
  padicPointComparisonFintype E p q



variable (l : ℕ) [Fact l.Prime] [DecidableEq ℚ_[l]]
  (W U : WeierstrassCurve (padicIntegerSubring l)) (C D : VariableChange ℚ_[l])
  (hC : C • E.map (algebraMap ℚ ℚ_[l]) =
    W.map (algebraMap (padicIntegerSubring l) ℚ_[l]))
  (hD : D • V.map (algebraMap ℚ ℚ_[l]) =
    U.map (algebraMap (padicIntegerSubring l) ℚ_[l]))

/-- The actual local prime quotient retains both specified original projective sections. -/
@[reassoc] theorem primeLocalGenericGroupHom_padicProjectivePoint
    (φ : (E.toAffine.baseChange ℚ).Point →+ (V.toAffine.baseChange ℚ).Point)
    (hφ : ∀ a, Affine.Point.baseChange (W' := V.toAffine) ℚ (AlgebraicClosure ℚ) (φ a) =
      torsionQuotientPointHom E p (Nat.Prime.pos Fact.out) q hp V hcurve
        (Affine.Point.baseChange (W' := E.toAffine) ℚ (AlgebraicClosure ℚ) a))
    (a : (E.toAffine.baseChange ℚ).Point) :
    let _ := torsionQuotient_isElliptic E p q hp V hcurve
    (projectiveToIntegral (W.map (algebraMap (padicIntegerSubring l) ℚ_[l]))
        (rationalPadicProjectiveHom l E W C hC a)).left ≫
          (primeLocalGenericGroupHom E p q hp V hcurve hfixed W U C D hC hD).hom.hom.hom.left =
      (projectiveToIntegral (U.map (algebraMap (padicIntegerSubring l) ℚ_[l]))
        (rationalPadicProjectiveHom l V U D hD (φ a))).left := by
  let _ := torsionQuotient_isElliptic E p q hp V hcurve
  dsimp only
  rw [rationalPadicProjectiveHom_genericScheme, rationalPadicProjectiveHom_genericScheme]
  exact primeLocalGenericGroupHom_rationalPoint E p q hp V hcurve hfixed W U C D hC hD φ hφ a

end WeierstrassCurve.Velu
