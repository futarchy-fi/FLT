/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassNodalDividedFamily
public import FLT.Mazur.WeierstrassCoefficientShearSpecializationMono
public import FLT.Mazur.WeierstrassCoefficientShearRetainedFiber
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber

/-!
# Later retained components in the depth-zero nonsplit family

Every retained chart after the first has positive incidence depth even when
the family starts at zero. Construct its full conic and either tangent line
using this local depth, without the previous global positive-start condition.
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
  (hm : maximalIdeal R = Ideal.span {π}) {depth n : ℕ}
  (hbound : 2 * (0 + n) ≤ depth)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6 : W.a₆ ∈ maximalIdeal R ^ depth)
  (j : ℕ) (hj : j ≤ n) (i : Fin j) (hi : 0 < i.val)
local notation "data" => nodalDepthFamily hm hbound h3 h4 h6
local notation "d" => data (Fin.mk (i.val + 1) (by omega))
local notation "A" => AdjoinRoot (nodeTangentPolynomial W)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))
local notation "rA" => AdjoinRoot.root (nodeTangentPolynomial W)
local notation "rQ" => AdjoinRoot.root (nodeTangentPolynomial (W.map (residue R)))
local notation "a" => WeierstrassCurve.a₁ (rootShearCurve (W.map (algebraMap R Q)) rQ)
local notation "c" => algebraMap R Q (Data.b6 d)
local notation "g3" => And.left
  (nodalDepthFamily_tangent_linear_zero hm hbound h3 h4 h6 hπ (Fin.mk (i.val + 1) (by omega)))
local notation "g4" => And.right
  (nodalDepthFamily_tangent_linear_zero hm hbound h3 h4 h6 hπ (Fin.mk (i.val + 1) (by omega)))
local notation "hs" => nodalDepth_tangent_scale_zero (W := W) hm (k := 0 + i.val) (by omega)
local notation "hp" => residueTangentEquation_zero W π
  (Iff.mp (residue_eq_zero_iff π) (nodalDepth_residue_uniformizer hm))
local notation "hr" => residueTangentEquation_root W
local notation "b" => Spec.map (CommRingCat.ofHom (nodeTangentCoefficientMap W (residue R)))
local notation "sA" => coefficientShearGluedStructure hπ data A rA j hj

/-- The whole original nonsplit retained conic in the constructed integral tangent model. -/
def nodalDepthZeroLaterConic : Spec (.of (ConicCoordinate a c)) ⟶
    coefficientShearGlued hπ data A rA j hj :=
  coefficientShearRetainedConic hπ data Q rQ j hj i hs hp g3 g4 hr ≫
    coefficientShearTangentSpecialization hπ data j hj

/-- The actual coefficient specialization of the constructed conic. -/
theorem nodalDepthZeroLaterConic_structure :
    nodalDepthZeroLaterConic hπ hm hbound h3 h4 h6 j hj i hi ≫ sA =
      conicStructure a c ≫ b := by
  rw [nodalDepthZeroLaterConic, Category.assoc, coefficientShearTangentSpecialization,
    coefficientShearSpecialization_structure, ← Category.assoc,
    coefficientShearRetainedConic_structure]
  rfl

variable (v : AdjoinRoot (nodeTangentPolynomial (W.map (residue R))))
  (hv : v * (v + (rootShearCurve (W.map (algebraMap R _))
    (AdjoinRoot.root (nodeTangentPolynomial (W.map (residue R))))).a₁) = 0)

/-- The entire retained tangent line, built without separately assumed divided bounds. -/
def nodalDepthZeroLaterLine : Spec (.of (Polynomial Q)) ⟶
    coefficientShearGlued hπ data A rA j hj :=
  coefficientShearRetainedLine hπ data Q rQ j hj i hs hp g3 g4 hr v hv ≫
    coefficientShearTangentSpecialization hπ data j hj

/-- The whole constructed line specializes through the same original tangent algebra map. -/
theorem nodalDepthZeroLaterLine_structure :
    nodalDepthZeroLaterLine hπ hm hbound h3 h4 h6 j hj i hi v hv ≫ sA =
      Spec.map (CommRingCat.ofHom (algebraMap Q (Polynomial Q))) ≫ b := by
  rw [nodalDepthZeroLaterLine, Category.assoc, coefficientShearTangentSpecialization,
    coefficientShearSpecialization_structure, ← Category.assoc,
    coefficientShearRetainedLine_structure]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
