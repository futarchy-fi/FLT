/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearInitialFiber
public import FLT.Mazur.WeierstrassCoefficientShearSpecialization
public import FLT.Mazur.WeierstrassResidueTangentEquationData

/-!
# The actual initial residue conic in the integral tangent equation gluing

The complete conic is constructed from the original initial incidence equation
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
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
  (hres : residue R π = 0) (hstart : 0 < start)
  (h3 : Data.b3 (data ⟨0, Nat.zero_lt_succ n⟩) ∈ maximalIdeal R)
  (h4 : Data.b4 (data ⟨0, Nat.zero_lt_succ n⟩) ∈ maximalIdeal R)
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
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
local notation "C" => coefficientShearInitialConic hπ data Q rQ j hj
  (residueTangentEquation_scale W hres start hstart)
  (residueTangentEquation_zero W (Data.b3 d) h3)
  (residueTangentEquation_zero W (Data.b4 d) h4) (residueTangentEquation_root W)
local notation "L" => coefficientShearInitialLine hπ data Q rQ j hj
  (residueTangentEquation_scale W hres start hstart)
  (residueTangentEquation_zero W (Data.b3 d) h3)
  (residueTangentEquation_zero W (Data.b4 d) h4) (residueTangentEquation_root W)

/-- The original initial residue conic in the actual integral tangent equation model. -/
def coefficientShearResidueInitialConic :
    Spec (.of (ConicCoordinate a c)) ⟶ coefficientShearGlued hπ data A rA j hj :=
  C ≫ coefficientShearTangentSpecialization hπ data j hj

/-- The complete incidence line specializes by the same actual root-algebra morphism. -/
def coefficientShearResidueInitialLine :
    Spec (.of (Polynomial Q)) ⟶ coefficientShearGlued hπ data A rA j hj :=
  L ≫ coefficientShearTangentSpecialization hπ data j hj

/-- The entire conic has the actual integral-root specialization as its coefficient leg. -/
@[reassoc] theorem coefficientShearResidueInitialConic_structure :
    coefficientShearResidueInitialConic hπ data j hj hres hstart h3 h4 ≫ sA =
      conicStructure a c ≫ b := by
  rw [coefficientShearResidueInitialConic, Category.assoc,
    coefficientShearTangentSpecialization, coefficientShearSpecialization_structure,
    ← Category.assoc, coefficientShearInitialConic_structure]
  rfl

/-- The whole incidence line retains its true coefficient specialization as well. -/
@[reassoc] theorem coefficientShearResidueInitialLine_structure :
    coefficientShearResidueInitialLine hπ data j hj hres hstart h3 h4 ≫ sA =
      Spec.map (CommRingCat.ofHom (algebraMap Q (Polynomial Q))) ≫ b := by
  rw [coefficientShearResidueInitialLine, Category.assoc,
    coefficientShearTangentSpecialization, coefficientShearSpecialization_structure,
    ← Category.assoc, coefficientShearInitialLine_structure]
  rfl

/-- Integral-root specialization preserves every original finite-model function on the conic. -/
@[reassoc] theorem coefficientShearResidueInitialConic_projection :
    coefficientShearResidueInitialConic hπ data j hj hres hstart h3 h4 ≫ pA = C ≫ pQ := by
  rw [coefficientShearResidueInitialConic, Category.assoc,
    coefficientShearTangentSpecialization, coefficientShearSpecialization_projection]

/-- Integral-root specialization preserves the full original incidence-line projection. -/
@[reassoc] theorem coefficientShearResidueInitialLine_projection :
    coefficientShearResidueInitialLine hπ data j hj hres hstart h3 h4 ≫ pA = L ≫ pQ := by
  rw [coefficientShearResidueInitialLine, Category.assoc,
    coefficientShearTangentSpecialization, coefficientShearSpecialization_projection]

/-- These two original projections uniquely determine the complete exceptional conic map. -/
theorem coefficientShearResidueInitialConic_unique
    (f : Spec (.of (ConicCoordinate a c)) ⟶ coefficientShearGlued hπ data A rA j hj)
    (hs : f ≫ sA = conicStructure a c ≫ b) (hp : f ≫ pA = C ≫ pQ) :
    f = coefficientShearResidueInitialConic hπ data j hj hres hstart h3 h4 := by
  apply (coefficientShearGlued_isPullback hπ data A rA j hj).hom_ext
  · rw [hs, coefficientShearResidueInitialConic_structure]
  · rw [hp, coefficientShearResidueInitialConic_projection]

end FLT.Mazur.WeierstrassDividedDepth
