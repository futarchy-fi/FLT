/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueCycleCoproduct
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
  (hm : maximalIdeal R = Ideal.span {π}) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (s : ℕ) (hs : s + 1 ≤ n) (he : 2 * (start + (s + 1)) = depth)
  (hstart : 0 < start)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6 : W.a₆ ∈ maximalIdeal R ^ depth)
  (h6next : W.a₆ ∉ maximalIdeal R ^ (depth + 1)) (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
local notation "g" => coefficientShearGluedStructure hπ data Q r (s + 1) hs
local notation "hk" => Nat.le_of_eq he
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "d" => data ⟨0, Nat.zero_lt_succ n⟩
local notation "hres" => nodalDepth_residue_uniformizer hm
local notation "F" => coefficientShearResidueExteriorLift hπ data (s + 1) hs d
  (by dsimp; omega) hres a
local notation "B" => coefficientShearResidueBranchComponent
  hπ hm data s hs hk hstart h3 h4 h6 hc
local notation "T" => coefficientShearResidueEqualityComponent
  hπ hm data s hs he h3 h4 h6next hc
local notation "ρ" => ProjectiveLine.endpointReversal Q

local notation "C" => coefficientShearResidueCycleComponent
  hπ hm data s hs he hstart h3 h4 h6 h6next hc
local notation "σ" => coefficientShearResidueTangentConjugation hπ data (s + 1) hs
local notation "f" => tangentResidueConjugationAlgHom (W := W)
local notation "P" => ProjectiveLine.coefficientMap (f).toRingHom
local notation "e" => data ⟨s + 1, Nat.lt_succ_of_le hs⟩
local notation "cunit" => nodalDepth_tangent_constant_isUnit hm e he h6next

/-- Position zero is the entire actual ordered exterior. -/
theorem coefficientShearResidueCycleComponent_exterior : C 0 = F := by
  simp only [coefficientShearResidueCycleComponent, Fin.val_zero, ite_true]

/-- The full first branch occurs with reversed parameter at the original forward index. -/
theorem coefficientShearResidueCycleComponent_first (j : Fin (s + 1)) :
    C ⟨j.val + 1, by omega⟩ = ρ ≫ B j 0 := by
  simp only [coefficientShearResidueCycleComponent,
    show ¬j.val + 1 = 0 from by omega, show j.val + 1 ≤ s + 1 from by omega,
    ↓reduceIte, dite_true, Nat.add_sub_cancel]

/-- The full opposite branch retains its parameter at the original backward index. -/
theorem coefficientShearResidueCycleComponent_second (j : Fin (s + 1)) :
    C ⟨2 * s + 3 - j.val, by omega⟩ = B j 1 := by
  simp only [coefficientShearResidueCycleComponent,
    show ¬2 * s + 3 - j.val = 0 from by omega,
    show ¬2 * s + 3 - j.val ≤ s + 1 from by omega,
    show ¬2 * s + 3 - j.val = s + 2 from by omega, ↓reduceIte, dite_false,
    show 2 * s + 3 - (2 * s + 3 - j.val) = j.val from by omega]

/-- The unique terminal position reverses the entire independent equality component. -/
theorem coefficientShearResidueCycleComponent_terminal : C ⟨s + 2, by omega⟩ = ρ ≫ T := by
  simp only [coefficientShearResidueCycleComponent, show ¬s + 2 = 0 from by omega,
    show ¬s + 2 ≤ s + 1 from by omega, ↓reduceIte, dite_false, dite_true]

/-- The complete exterior uses precisely the same coefficient operation as both branches. -/
@[reassoc] theorem coefficientShearResidueCycleComponent_exterior_conjugation :
    C 0 ≫ σ = P ≫ ρ ≫ C 0 := by
  have hP : nodeTangentLineCoefficients V = P :=
    nodeTangentLineCoefficients_eq_coefficientMap V
  rw [coefficientShearResidueCycleComponent_exterior]
  calc
    F ≫ σ = (nodeTangentLineCoefficients V ≫ ρ) ≫ F :=
      coefficientShearResidueExteriorLift_conjugation
        hπ data (s + 1) hs d (by dsimp; omega) hres a
        (residueTangentComponentUnit_val W h3 h4 hc)
    _ = (P ≫ ρ) ≫ F := congrArg
      (fun (q : ProjectiveLine.scheme Q ⟶ ProjectiveLine.scheme Q) => (q ≫ ρ) ≫ F) hP
    _ = P ≫ ρ ≫ F := Category.assoc _ _ _

/-- Actual conjugation exchanges complete first-branch parameters at the reflected index. -/
@[reassoc] theorem coefficientShearResidueCycleComponent_first_conjugation
    (j : Fin (s + 1)) :
    C ⟨j.val + 1, by omega⟩ ≫ σ = P ≫ ρ ≫ C ⟨2 * s + 3 - j.val, by omega⟩ := by
  rw [coefficientShearResidueCycleComponent_first,
    coefficientShearResidueCycleComponent_second, Category.assoc,
    coefficientShearResidueBranchComponent_conjugation,
    ProjectiveLine.endpointReversal_coefficientMap_assoc]
  rfl

/-- The opposite full branch has the same semilinear reflected parameter formula. -/
@[reassoc] theorem coefficientShearResidueCycleComponent_second_conjugation
    (j : Fin (s + 1)) :
    C ⟨2 * s + 3 - j.val, by omega⟩ ≫ σ = P ≫ ρ ≫ C ⟨j.val + 1, by omega⟩ := by
  rw [coefficientShearResidueCycleComponent_first,
    coefficientShearResidueCycleComponent_second,
    coefficientShearResidueBranchComponent_conjugation,
    ← Category.assoc ρ, ProjectiveLine.endpointReversal_involutive, Category.id_comp]
  rfl

/-- Reversing the terminal coordinate retains c inverse over T, on the full projective line. -/
@[reassoc] theorem coefficientShearResidueCycleComponent_terminal_conjugation :
    C ⟨s + 2, by omega⟩ ≫ σ =
      P ≫ ProjectiveLine.scaledEndpointReversal Q (cunit).unit⁻¹ ≫ C ⟨s + 2, by omega⟩ := by
  rw [coefficientShearResidueCycleComponent_terminal, Category.assoc,
    coefficientShearResidueEqualityComponent_conjugation,
    ProjectiveLine.endpointReversal_coefficientMap_assoc,
    ProjectiveLine.endpointReversal_scaledEndpointReversal_assoc]

end FLT.Mazur.WeierstrassDividedDepth
