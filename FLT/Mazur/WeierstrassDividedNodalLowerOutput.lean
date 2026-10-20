/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalLowerCoefficients
public import FLT.Mazur.WeierstrassDividedTangentLowerScheme
public import FLT.Mazur.WeierstrassDividedDepthMaps

/-!
# Shallow nodal outputs in the actual lower-depth chart

The original exact node conditions construct both branch quotients. The
supplied datum at depth m - 2k receives an actual output morphism whose
contraction is the original tangent sum on the whole branch source.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsLocalRing R] [Module.Flat R S] {W : WeierstrassCurve R} {π : R} {m k : ℕ}
  (D : SplitNodeDepth W π m) (d : Data W π k) (hdepth : 2 * k ≤ m)
  (hm : m ≤ 3 * k) (e : Data W π (m - 2 * k))
  (a2 : R) (h2 : W.a₂ = π ^ (m - 2 * k) * a2)
  (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "s" => π ^ k
local notation "t" => π ^ (m - 2 * k)
local notation "w" => π ^ (k - (m - 2 * k))
local notation "B" => DividedTangentBranchRing W s d.b3 d.b4 d.b6 a c
local notation "ht" => isRegular_iff_ne_zero.mpr (pow_ne_zero _ D.uniformizer_ne_zero)
local notation "hs" => nodalLower_scale_factor (π := π) hm
local notation "b4'" => nodalLowerFourth D d hdepth
local notation "b6'" => nodalLowerConstant D d hdepth
local notation "h4'" => nodalLowerFourth_factor D d hdepth
local notation "h6'" => nodalLowerConstant_factor D d hdepth

/-- Construct the shallow nodal output in any supplied datum at its actual depth. -/
def nodalLowerOutput : Coordinate W t e.b3 e.b4 e.b6 →ₐ[R] B :=
  dividedTangentLowerOutput W s d.b3 d.b4 d.b6 a c t w a2 b4' b6' e.b3 e.b4 e.b6
    ht hs h2 d.factor3 d.factor4 d.factor6 h4' h6' e.factor3 e.factor4 e.factor6

/-- The abscissa generator evaluates to the explicit lower-depth branch formula. -/
theorem nodalLowerOutput_x :
    nodalLowerOutput D d hdepth hm e a2 h2 a c (x W t e.b3 e.b4 e.b6) =
      dividedTangentLowerX W s d.b3 d.b4 d.b6 a c t w a2 b4' b6' :=
  dividedTangentLowerOutput_x ..

/-- The ordinate generator evaluates to the explicit lower-depth branch formula. -/
theorem nodalLowerOutput_y :
    nodalLowerOutput D d hdepth hm e a2 h2 a c (y W t e.b3 e.b4 e.b6) =
      dividedTangentLowerY W s d.b3 d.b4 d.b6 a c t w a2 b4' b6' :=
  dividedTangentLowerOutput_y ..

/-- The actual shallow output morphism, before restricting to smooth points. -/
def nodalLowerLift : Spec (.of B) ⟶ chart e :=
  Spec.map (CommRingCat.ofHom (nodalLowerOutput D d hdepth hm e a2 h2 a c).toRingHom)

/-- The whole shallow branch morphism contracts to the original tangent sum. -/
@[reassoc] theorem nodalLowerLift_contraction :
    nodalLowerLift D d hdepth hm e a2 h2 a c ≫ toCurve e =
      Spec.map (CommRingCat.ofHom
        (dividedTangentBranchRestriction W s d.b3 d.b4 d.b6 a c).toRingHom) ≫
        dividedTangentToCurve W s d.b3 d.b4 d.b6 a c d.factor3 d.factor4 d.factor6 :=
  dividedTangentLowerLift_contraction ..

/-- The entire shallow branch output has the original coefficient map. -/
@[reassoc] theorem nodalLowerLift_structure :
    nodalLowerLift D d hdepth hm e a2 h2 a c ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (Coordinate W t e.b3 e.b4 e.b6))) =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) :=
  WeierstrassIntegralChart.specAlgHom_structure _

end FLT.Mazur.WeierstrassDividedDepth
