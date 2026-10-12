/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRetainedFiber
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber
public import FLT.Mazur.WeierstrassCoefficientShearSpecialization
public import FLT.Mazur.WeierstrassResidueTangentEquationData

/-!
# The actual retained residue conic in the integral tangent equation gluing

The complete conic is constructed from the original retained middle equation
and mapped along the real integral-root specialization. Its coefficient leg and
its original integral-model projection are both retained.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n) (i : Fin j)
  (hres : residue R π = 0) (hstart : 0 < start)
  (h3 : Data.b3 (data ⟨i.val + 1, by omega⟩) ∈ maximalIdeal R)
  (h4 : Data.b4 (data ⟨i.val + 1, by omega⟩) ∈ maximalIdeal R)
local notation "d" => data (Fin.mk (i.val + 1) (by omega))
local notation "A" => AdjoinRoot (nodeTangentPolynomial W)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))
local notation "rA" => AdjoinRoot.root (nodeTangentPolynomial W)
local notation "rQ" => AdjoinRoot.root (nodeTangentPolynomial (W.map (residue R)))
local notation "a" => WeierstrassCurve.a₁ (rootShearCurve (W.map (algebraMap R Q)) rQ)
local notation "c" => algebraMap R Q (Data.b6 d)
local notation "sA" => coefficientShearGluedStructure hπ data A rA j hj
local notation "pA" => coefficientShearGluedProjection hπ data A rA j hj
local notation "pQ" => coefficientShearGluedProjection hπ data Q rQ j hj
local notation "b" => Spec.map (CommRingCat.ofHom (nodeTangentCoefficientMap W (residue R)))
local notation "C" => coefficientShearRetainedConic hπ data Q rQ j hj i
  (residueTangentEquation_scale W hres (start + i.val) (by omega))
  (residueTangentEquation_zero W π (Iff.mp (residue_eq_zero_iff π) hres))
  (residueTangentEquation_zero W (Data.b3 d) h3)
  (residueTangentEquation_zero W (Data.b4 d) h4) (residueTangentEquation_root W)
variable (v : AdjoinRoot (nodeTangentPolynomial (W.map (residue R))))
  (hv : v * (v + (rootShearCurve (W.map (algebraMap R _))
    (AdjoinRoot.root (nodeTangentPolynomial (W.map (residue R))))).a₁) = 0)
local notation "L" => coefficientShearRetainedLine hπ data Q rQ j hj i
  (residueTangentEquation_scale W hres (start + i.val) (by omega))
  (residueTangentEquation_zero W π (Iff.mp (residue_eq_zero_iff π) hres))
  (residueTangentEquation_zero W (Data.b3 d) h3)
  (residueTangentEquation_zero W (Data.b4 d) h4) (residueTangentEquation_root W) v hv

/-- The original retained residue conic in the actual integral tangent equation model. -/
def coefficientShearResidueRetainedConic :
    Spec (.of (ConicCoordinate a c)) ⟶ coefficientShearGlued hπ data A rA j hj :=
  C ≫ coefficientShearTangentSpecialization hπ data j hj

/-- The complete retained line specializes by the same actual root-algebra morphism. -/
def coefficientShearResidueRetainedLine :
    Spec (.of (Polynomial Q)) ⟶ coefficientShearGlued hπ data A rA j hj :=
  L ≫ coefficientShearTangentSpecialization hπ data j hj

/-- The entire conic has the actual integral-root specialization as its coefficient leg. -/
theorem coefficientShearResidueRetainedConic_structure :
    coefficientShearResidueRetainedConic hπ data j hj i hres hstart h3 h4 ≫ sA =
      conicStructure a c ≫ b := by
  rw [coefficientShearResidueRetainedConic, Category.assoc,
    coefficientShearTangentSpecialization, coefficientShearSpecialization_structure,
    ← Category.assoc, coefficientShearRetainedConic_structure]
  rfl

/-- The whole retained line retains its true coefficient specialization as well. -/
theorem coefficientShearResidueRetainedLine_structure :
    coefficientShearResidueRetainedLine hπ data j hj i hres hstart h3 h4 v hv ≫ sA =
      Spec.map (CommRingCat.ofHom (algebraMap Q (Polynomial Q))) ≫ b := by
  rw [coefficientShearResidueRetainedLine, Category.assoc,
    coefficientShearTangentSpecialization, coefficientShearSpecialization_structure,
    ← Category.assoc, coefficientShearRetainedLine_structure]
  rfl

/-- Integral-root specialization preserves every original finite-model function on the conic. -/
theorem coefficientShearResidueRetainedConic_projection :
    coefficientShearResidueRetainedConic hπ data j hj i hres hstart h3 h4 ≫ pA = C ≫ pQ := by
  rw [coefficientShearResidueRetainedConic, Category.assoc,
    coefficientShearTangentSpecialization, coefficientShearSpecialization_projection]

/-- Integral-root specialization preserves the full original retained-line projection. -/
theorem coefficientShearResidueRetainedLine_projection :
    coefficientShearResidueRetainedLine hπ data j hj i hres hstart h3 h4 v hv ≫ pA = L ≫ pQ := by
  rw [coefficientShearResidueRetainedLine, Category.assoc,
    coefficientShearTangentSpecialization, coefficientShearSpecialization_projection]

/-- These two original projections uniquely determine the complete exceptional conic map. -/
theorem coefficientShearResidueRetainedConic_unique
    (f : Spec (.of (ConicCoordinate a c)) ⟶ coefficientShearGlued hπ data A rA j hj)
    (hs : f ≫ sA = conicStructure a c ≫ b) (hp : f ≫ pA = C ≫ pQ) :
    f = coefficientShearResidueRetainedConic hπ data j hj i hres hstart h3 h4 := by
  apply (coefficientShearGlued_isPullback hπ data A rA j hj).hom_ext
  · rw [hs, coefficientShearResidueRetainedConic_structure]
  · rw [hp, coefficientShearResidueRetainedConic_projection]

end FLT.Mazur.WeierstrassDividedDepth
