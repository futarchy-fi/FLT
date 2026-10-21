/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedCommonSumContraction

/-!
# Actual common-scale sum output from original node depth

Construct all branch coefficient quotients from k + 2*l ≤ node depth,
then construct the sum-depth output on the actual original principal open.
The output contracts to the whole original cubic secant. Smooth promotion
and closed-fiber coverage for this wider range remain separate steps.
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
  [IsLocalRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {k l m : ℕ} (D : SplitNodeDepth W π m)
  (d : Data W π k) (e : Data W π l) (hkl : k ≤ l) (hm : k + 2 * l ≤ m)
  (z : Data W π (k + l)) (h2 : W.a₂ = 0)
  (a : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
  (c : Coordinate W (π ^ l) e.b3 e.b4 e.b6 →ₐ[R] S)
local notation "hπ" => D.uniformizer_ne_zero
local notation "dd" => tripleBranchData D d (by omega)
local notation "ee" => commonBranchData D e hm
local notation "B" => SumDepthSourceRing d e a c
local notation "res" => sumDepthSourceRestriction d e a c hπ hkl
local notation "c₀" => unequalDepthRight hπ d e hkl c

/-- Every coefficient quotient is constructed from the original mixed node-depth bound. -/
def nodeCommonSumOutput : Coordinate W (π ^ (k + l)) z.b3 z.b4 z.b6 →ₐ[R] B :=
  commonSumDepthSourceOutput d e a c hπ hkl dd ee z h2

/-- The actual principal-open source maps to the supplied sum-depth chart. -/
def nodeCommonSumLift : Spec (.of B) ⟶ chart z :=
  commonSumDepthSourceLift d e a c hπ hkl dd ee z h2

/-- The mixed-depth construction keeps the original coefficient point. -/
@[reassoc] theorem nodeCommonSumLift_structure :
    nodeCommonSumLift D d e hkl hm z h2 a c ≫ Spec.map (CommRingCat.ofHom
        (algebraMap R (Coordinate W (π ^ (k + l)) z.b3 z.b4 z.b6))) =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) :=
  commonSumDepthSourceLift_structure d e a c hπ hkl dd ee z h2

/-- The entire cubic contraction is the original secant of the unmodified inputs. -/
@[reassoc] theorem nodeCommonSumLift_contraction :
    nodeCommonSumLift D d e hkl hm z h2 a c ≫ toCurve z =
      Spec.map (CommRingCat.ofHom (res).toRingHom) ≫
        dividedSecantToCurve W (π ^ k) d.b3 d.b4 d.b6 a c₀
          d.factor3 d.factor4 d.factor6 :=
  commonSumDepthSourceLift_contraction d e a c hπ hkl dd ee z h2

end FLT.Mazur.WeierstrassDividedDepth
