/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueZeroEqualityCoproduct
public import FLT.Mazur.ProjectiveLineCoefficientEndpoints
public import FLT.Mazur.ProjectiveLineScaledReversalConjugation
public import FLT.Mazur.NodeTangentGluedCoefficients

/-!
# Full scaled residue reflection in the original cyclic positions

The exterior, both branches and the equality terminal retain their complete
projective parameters. The reversed terminal uses the inverse original constant.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0)
  (hm : maximalIdeal R = Ideal.span {π}) {n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (s : ℕ) (hs : s + 1 ≤ n) (he : 2 * (0 + (s + 1)) = depth)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6next : W.a₆ ∉ maximalIdeal R ^ (depth + 1)) (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
local notation "g" => coefficientShearGluedStructure hπ data Q r (s + 1) hs
local notation "hk" => Nat.le_of_eq he
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "d" => data ⟨1, by omega⟩
local notation "hres" => nodalDepth_residue_uniformizer hm
local notation "F" => coefficientShearResidueExteriorLift hπ data (s + 1) hs d
  (by dsimp; omega) hres a
local notation "B" => coefficientShearResidueAdjacentComponent
  hπ hm data s hs hk h3 h4 hc
local notation "T" => coefficientShearResidueEqualityComponent
  hπ hm data s hs he h3 h4 h6next hc
local notation "ρ" => ProjectiveLine.endpointReversal Q

local notation "C" => coefficientShearResidueZeroEqualityCycleComponent
  hπ hm data s hs he h3 h4 h6next hc
local notation "σ" => coefficientShearResidueTangentConjugation hπ data (s + 1) hs
local notation "f" => tangentResidueConjugationAlgHom (W := W)
local notation "P" => ProjectiveLine.coefficientMap (f).toRingHom
local notation "e" => data ⟨s + 1, Nat.lt_succ_of_le hs⟩
local notation "cunit" => nodalDepth_tangent_constant_isUnit hm e he h6next

/-- Position zero is the entire actual ordered exterior. -/
theorem coefficientShearResidueZeroEqualityCycleComponent_exterior : C 0 = F := by
  simp only [coefficientShearResidueZeroEqualityCycleComponent, Fin.val_zero, dite_true]

/-- The full first branch occurs with reversed parameter at the original forward index. -/
theorem coefficientShearResidueZeroEqualityCycleComponent_first (j : Fin s) :
    C ⟨j.val + 1, by omega⟩ = ρ ≫ B j 0 := by
  simp only [coefficientShearResidueZeroEqualityCycleComponent,
    show ¬j.val + 1 = 0 from by omega, show j.val + 1 ≤ s from by omega,
    dite_false, dite_true, Nat.add_sub_cancel]

/-- The full opposite branch retains its parameter at the original backward index. -/
theorem coefficientShearResidueZeroEqualityCycleComponent_second (j : Fin s) :
    C ⟨2 * s + 1 - j.val, by omega⟩ = B j 1 := by
  simp only [coefficientShearResidueZeroEqualityCycleComponent,
    show ¬2 * s + 1 - j.val = 0 from by omega,
    show ¬2 * s + 1 - j.val ≤ s from by omega,
    show ¬2 * s + 1 - j.val = s + 1 from by omega, dite_false,
    show 2 * s + 1 - (2 * s + 1 - j.val) = j.val from by omega]

/-- The unique terminal position reverses the entire independent equality component. -/
theorem coefficientShearResidueZeroEqualityCycleComponent_terminal :
    C ⟨s + 1, by omega⟩ = ρ ≫ T := by
  simp only [coefficientShearResidueZeroEqualityCycleComponent, show ¬s + 1 = 0 from by omega,
    show ¬s + 1 ≤ s from by omega, dite_false, dite_true]

/-- The complete exterior uses precisely the same coefficient operation as both branches. -/
@[reassoc] theorem coefficientShearResidueZeroEqualityCycleComponent_exterior_conjugation :
    C 0 ≫ σ = P ≫ ρ ≫ C 0 := by
  have hP : nodeTangentLineCoefficients V = P :=
    nodeTangentLineCoefficients_eq_coefficientMap V
  rw [coefficientShearResidueZeroEqualityCycleComponent_exterior]
  calc
    F ≫ σ = (nodeTangentLineCoefficients V ≫ ρ) ≫ F :=
      coefficientShearResidueExteriorLift_conjugation
        hπ data (s + 1) hs d (by dsimp; omega) hres a
        (residueTangentComponentUnit_val W h3 h4 hc)
    _ = (P ≫ ρ) ≫ F := congrArg
      (fun (q : ProjectiveLine.scheme Q ⟶ ProjectiveLine.scheme Q) => (q ≫ ρ) ≫ F) hP
    _ = P ≫ ρ ≫ F := Category.assoc _ _ _

/-- Actual conjugation exchanges complete first-branch parameters at the reflected index. -/
@[reassoc] theorem coefficientShearResidueZeroEqualityCycleComponent_first_conjugation
    (j : Fin s) :
    C ⟨j.val + 1, by omega⟩ ≫ σ = P ≫ ρ ≫ C ⟨2 * s + 1 - j.val, by omega⟩ := by
  rw [coefficientShearResidueZeroEqualityCycleComponent_first,
    coefficientShearResidueZeroEqualityCycleComponent_second, Category.assoc,
    coefficientShearResidueAdjacentComponent_conjugation,
    ProjectiveLine.endpointReversal_coefficientMap_assoc]
  rfl

/-- The opposite full branch has the same semilinear reflected parameter formula. -/
@[reassoc] theorem coefficientShearResidueZeroEqualityCycleComponent_second_conjugation
    (j : Fin s) :
    C ⟨2 * s + 1 - j.val, by omega⟩ ≫ σ = P ≫ ρ ≫ C ⟨j.val + 1, by omega⟩ := by
  rw [coefficientShearResidueZeroEqualityCycleComponent_first,
    coefficientShearResidueZeroEqualityCycleComponent_second,
    coefficientShearResidueAdjacentComponent_conjugation,
    ← Category.assoc ρ, ProjectiveLine.endpointReversal_involutive, Category.id_comp]
  rfl

/-- Reversing the terminal coordinate retains c inverse over T, on the full projective line. -/
@[reassoc] theorem coefficientShearResidueZeroEqualityCycleComponent_terminal_conjugation :
    C ⟨s + 1, by omega⟩ ≫ σ =
      P ≫ ProjectiveLine.scaledEndpointReversal Q (cunit).unit⁻¹ ≫ C ⟨s + 1, by omega⟩ := by
  rw [coefficientShearResidueZeroEqualityCycleComponent_terminal, Category.assoc,
    coefficientShearResidueEqualityComponent_conjugation,
    ProjectiveLine.endpointReversal_coefficientMap_assoc,
    ProjectiveLine.endpointReversal_scaledEndpointReversal_assoc]

end FLT.Mazur.WeierstrassDividedDepth
