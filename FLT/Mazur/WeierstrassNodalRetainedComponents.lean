/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassNodalDividedFamily
public import FLT.Mazur.WeierstrassCoefficientShearResidueRetained
import all FLT.Mazur.WeierstrassCoefficientShearResidueRetained

/-!
# Actual nonsplit retained components from original coefficient bounds

Construct the finite divided family from the original nodal bounds and
specialize each retained conic and tangent line into its integral tangent
model. Neither divided membership proofs nor a component comparison are inputs.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0)
  (hm : maximalIdeal R = Ideal.span {π}) {depth start n : ℕ}
  (hbound : 2 * (start + n) ≤ depth)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6 : W.a₆ ∈ maximalIdeal R ^ depth)
  (j : ℕ) (hj : j ≤ n) (i : Fin j) (hstart : 0 < start)
local notation "data" => nodalDepthFamily hm hbound h3 h4 h6
local notation "d" => data (Fin.mk (i.val + 1) (by omega))
local notation "A" => AdjoinRoot (nodeTangentPolynomial W)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))
local notation "rA" => AdjoinRoot.root (nodeTangentPolynomial W)
local notation "rQ" => AdjoinRoot.root (nodeTangentPolynomial (W.map (residue R)))
local notation "a" => WeierstrassCurve.a₁ (rootShearCurve (W.map (algebraMap R Q)) rQ)
local notation "c" => algebraMap R Q (Data.b6 d)
local notation "g3" => And.left
  (nodalDepthFamily_linear_mem hm hbound h3 h4 h6 hπ (Fin.mk (i.val + 1) (by omega)))
local notation "g4" => And.right
  (nodalDepthFamily_linear_mem hm hbound h3 h4 h6 hπ (Fin.mk (i.val + 1) (by omega)))
local notation "hres" => nodalDepth_residue_uniformizer hm
local notation "b" => Spec.map (CommRingCat.ofHom (nodeTangentCoefficientMap W (residue R)))
local notation "sA" => coefficientShearGluedStructure hπ data A rA j hj

/-- The whole original nonsplit retained conic in the constructed integral tangent model. -/
def nodalDepthRetainedConic : Spec (.of (ConicCoordinate a c)) ⟶
    coefficientShearGlued hπ data A rA j hj :=
  coefficientShearResidueRetainedConic hπ data j hj i hres hstart g3 g4

/-- The actual coefficient specialization of the constructed conic. -/
theorem nodalDepthRetainedConic_structure :
    nodalDepthRetainedConic hπ hm hbound h3 h4 h6 j hj i hstart ≫ sA =
      conicStructure a c ≫ b :=
  coefficientShearResidueRetainedConic_structure hπ data j hj i hres hstart g3 g4

variable (v : AdjoinRoot (nodeTangentPolynomial (W.map (residue R))))
  (hv : v * (v + (rootShearCurve (W.map (algebraMap R _))
    (AdjoinRoot.root (nodeTangentPolynomial (W.map (residue R))))).a₁) = 0)

/-- The entire retained tangent line, built without separately assumed divided bounds. -/
def nodalDepthRetainedLine : Spec (.of (Polynomial Q)) ⟶
    coefficientShearGlued hπ data A rA j hj :=
  coefficientShearResidueRetainedLine hπ data j hj i hres hstart g3 g4 v hv

/-- The whole constructed line specializes through the same original tangent algebra map. -/
theorem nodalDepthRetainedLine_structure :
    nodalDepthRetainedLine hπ hm hbound h3 h4 h6 j hj i hstart v hv ≫ sA =
      Spec.map (CommRingCat.ofHom (algebraMap Q (Polynomial Q))) ≫ b :=
  coefficientShearResidueRetainedLine_structure hπ data j hj i hres hstart g3 g4 v hv

end FLT.Mazur.WeierstrassDividedDepth
