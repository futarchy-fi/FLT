/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXLaurentNodeDenominator
public import FLT.Mazur.WeierstrassModificationXNodeRestriction
public import FLT.Mazur.WeierstrassModificationXOppositeNodeGeometry

/-!
# Both original Laurent boundaries factor through the full initial nodes

The map is constructed on every node function. Its composites with the two
full node charts are exactly the two original Laurent evaluations.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (I : Ideal R) (hI : IsNilpotent I) (ha : IsUnit W.a₁) (hs : s ∈ I)
  (h2 : W.a₂ ∈ I) (h3 : b3 ∈ I) (h4 : b4 ∈ I) (h6 : b6 ∈ I)
local notation "A" => Coordinate W s b3 b4 b6
local notation "B" => R[T;T⁻¹]
local notation "L" => PolynomialNodeOpen W s
local notation "E" => laurentBranchEvaluation W s b3 b4 b6 I hI ha hs h2 h3 h4 h6
local notation "r₀" => polynomialSlopeRoot W b3 b4 b6 I hI ha h2 h3 h4 h6
local notation "hr₀" => polynomialSlopeRoot_equation W b3 b4 b6 I hI ha h2 h3 h4 h6
local notation "hm₀" => polynomialSlopeRoot_mem W b3 b4 b6 I hI ha h2 h3 h4 h6
local notation "F" => polynomialNodeForwardBase W s b3 b4 b6 r₀ hr₀ I hI hm₀ h3

/-- The original small Laurent branch evaluates the full smoothing-node functions. -/
def laurentNodeRestriction : L →ₐ[R] B :=
  polynomialNodeRestriction W s b3 b4 b6 r₀ (E false)
    (laurentBranchEvaluation_node_unit W s b3 b4 b6 I hI ha hs h2 h3 h4 h6 r₀ hm₀)
    hr₀ I hI hm₀ h3

local notation "G" => laurentNodeRestriction W s b3 b4 b6 I hI ha hs h2 h3 h4 h6

/-- The first full node chart recovers every function of the original small Laurent boundary. -/
theorem laurentNodeRestriction_first : (G).comp F = E false :=
  polynomialNodeRestriction_forward ..

/-- The reflected full chart recovers every function of the original opposite Laurent boundary. -/
theorem laurentNodeRestriction_opposite :
    (G).comp ((F).comp ((initialReflection W s b3 b4 b6).restrictScalars R).toAlgHom) =
      E true := by
  rw [← AlgHom.comp_assoc, laurentNodeRestriction_first]
  exact laurentBranchEvaluation_reflection W s b3 b4 b6 I hI ha hs h2 h3 h4 h6

/-- The small original Laurent scheme map is the actual restriction of the full first node. -/
@[reassoc] theorem laurentNodeRestriction_first_spec :
    Spec.map (CommRingCat.ofHom (G).toRingHom) ≫
      polynomialNodeChart W s b3 b4 b6 r₀ hr₀ I hI hm₀ h3 =
        Spec.map (CommRingCat.ofHom (E false).toRingHom) := by
  rw [polynomialNodeChart_eq_spec, ← Spec.map_comp]
  exact congrArg (fun f : A →ₐ[R] B ↦ Spec.map (CommRingCat.ofHom f.toRingHom))
    (laurentNodeRestriction_first W s b3 b4 b6 I hI ha hs h2 h3 h4 h6)

/-- The opposite Laurent scheme map is the actual restriction of the reflected full node. -/
@[reassoc] theorem laurentNodeRestriction_opposite_spec :
    Spec.map (CommRingCat.ofHom (G).toRingHom) ≫
      polynomialOppositeNodeChart W s b3 b4 b6 r₀ hr₀ I hI hm₀ h3 =
        Spec.map (CommRingCat.ofHom (E true).toRingHom) := by
  rw [polynomialOppositeNodeChart_eq_spec, ← Spec.map_comp]
  exact congrArg (fun f : A →ₐ[R] B ↦ Spec.map (CommRingCat.ofHom f.toRingHom))
    (laurentNodeRestriction_opposite W s b3 b4 b6 I hI ha hs h2 h3 h4 h6)

/-- The original Laurent incidence times the opposite factor is the first node parameter. -/
theorem laurentNodeRestriction_p :
    G (algebraMap (NodalFiber.Coordinate s) L (NodalFiber.p s)) =
      LaurentPolynomial.T (-1) * E false (polynomialOppositeFactor W s b3 b4 b6 r₀) := by
  change polynomialNodeRestriction W s b3 b4 b6 r₀ (E false) _ hr₀ I hI hm₀ h3 _ = _
  rw [polynomialNodeRestriction_p, map_mul]
  rw [show E false (t W s b3 b4 b6) = LaurentPolynomial.T (-1) from
    laurentSlopeEvaluation_t ..]

/-- The original small Laurent factor is the second node parameter. -/
theorem laurentNodeRestriction_q :
    G (algebraMap (NodalFiber.Coordinate s) L (NodalFiber.q s)) =
      E false (polynomialSmallFactor W s b3 b4 b6 r₀) :=
  polynomialNodeRestriction_q ..

end FLT.Mazur.WeierstrassModificationX
