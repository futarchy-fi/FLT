/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluDescendedGroupMorphism
public import FLT.FreyCurve.Serre.VeluPrimeRationalMorphism
public import FLT.FreyCurve.Serre.VeluPrimeExactTarget

/-!
# The original prime rational Vélu group homomorphism

The degree-p rational morphism now has its original group compatibility,
with the exact rational target equation and the original scheme carrier.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
open FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ) [Fact p.Prime]
  (q : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p →ₗ[ZMod p] ZMod p)
  [Fintype (torsionKernel E p q)] (hp : Odd p)

local notation "EQ" => E.map (algebraMap ℚ (AlgebraicClosure ℚ))
local notation "GQ" => torsionKernel E p q

/-- Cache the same original finite subgroup on the mapped source cubic. -/
local instance primeRationalGroupFintype :
    Fintype (show AddSubgroup (EQ).toAffine.Point from GQ) :=
  inferInstanceAs (Fintype (torsionKernel E p q))

variable (V : WeierstrassCurve ℚ)
  (hcurve : V.map (algebraMap ℚ (AlgebraicClosure ℚ)) =
    @curve (AlgebraicClosure ℚ) inferInstance inferInstance
      (E.map (algebraMap ℚ (AlgebraicClosure ℚ))) (torsionKernel E p q)
      (primeRationalGroupFintype E p q))
  (hfixed : ∀ g t, q (E.torsionGaloisRepresentation p g t) = q t)

local notation "SG" => integralCurveGroup E IsElliptic.isUnit
local notation "TG" => integralCurveGroup V
  (IsElliptic.isUnit (self := torsionQuotient_isElliptic E p q hp V hcurve))

/-- The original rational prime morphism as a map between the original group objects. -/
def primeRationalOverMorphism : (SG).X ⟶ (TG).X :=
  veluDescendedOverMorphism E GQ (torsionKernel_ne_neg E p q hp) V hcurve
    (torsionKernel_stable E p q hfixed)

/-- Its underlying scheme morphism is the original rational prime morphism. -/
theorem primeRationalOverMorphism_left :
    (primeRationalOverMorphism E p q hp V hcurve hfixed).left =
      primeRationalMorphism E p q hp V hcurve hfixed := rfl

/-- The rational prime morphism respects the actual original group laws. -/
instance primeRationalOverMorphism_isMonHom :
    IsMonHom (primeRationalOverMorphism E p q hp V hcurve hfixed) :=
  veluDescendedOverMorphism_isMonHom E GQ (torsionKernel_ne_neg E p q hp) V hcurve
    (torsionKernel_stable E p q hfixed)

/-- The prime morphism bundled as a homomorphism of the original commutative group schemes. -/
def primeRationalGroupHom : SG ⟶ TG :=
  ⟨⟨⟨primeRationalOverMorphism E p q hp V hcurve hfixed⟩⟩⟩

/-- Forgetting the group homomorphism retains the original scheme morphism. -/
theorem primeRationalGroupHom_left :
    (primeRationalGroupHom E p q hp V hcurve hfixed).hom.hom.hom.left =
      primeRationalMorphism E p q hp V hcurve hfixed := rfl

/-- Multiplication compatibility holds on the original rational cubics. -/
@[reassoc] theorem primeRationalMorphism_multiplication :
    integralCurveAddition E IsElliptic.isUnit ≫ primeRationalMorphism E p q hp V hcurve hfixed =
      (primeRationalOverMorphism E p q hp V hcurve hfixed ⊗ₘ
        primeRationalOverMorphism E p q hp V hcurve hfixed).left ≫
          integralCurveAddition V (torsionQuotient_isElliptic E p q hp V hcurve).isUnit :=
  congrArg Over.Hom.left (IsMonHom.mul_hom (primeRationalOverMorphism E p q hp V hcurve hfixed))

end WeierstrassCurve.Velu
