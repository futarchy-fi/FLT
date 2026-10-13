/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictPositiveCycleCoproduct
public import FLT.Mazur.ProjectiveLineCoefficientEndpoints
public import FLT.Mazur.NodeTangentGluedCoefficients
public import FLT.Mazur.CyclicPinchingReflectionIndices
public import FLT.Mazur.CyclicPinchingSemilinearScaledSources
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictPositiveCycleCoproduct

/-!
# Full original positive-start strict-depth cyclic reflection

Every complete component retains its original cyclic position. Conjugation
reflects all full parameters, including both separate terminal components.
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
  (s : ℕ) (hs : s + 1 ≤ n) (hk : 2 * (start + (s + 1)) < depth)
  (hstart : 0 < start)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6 : W.a₆ ∈ maximalIdeal R ^ depth)
  (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
local notation "g" => coefficientShearGluedStructure hπ data Q r (s + 1) hs
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "d" => data ⟨0, Nat.zero_lt_succ n⟩
local notation "hres" => nodalDepth_residue_uniformizer hm
local notation "F" => coefficientShearResidueExteriorLift hπ data (s + 1) hs d
  (by dsimp; omega) hres a
local notation "B" => coefficientShearResidueStrictPositiveBranch
  hπ hm data s hs hk h3 h4 h6 hc hstart
local notation "ρ" => ProjectiveLine.endpointReversal Q

local notation "C" => coefficientShearResidueStrictPositiveCycleComponent
  hπ hm data s hs hk hstart h3 h4 h6 hc
local notation "σ" => coefficientShearResidueTangentConjugation hπ data (s + 1) hs
local notation "f" => tangentResidueConjugationAlgHom (W := W)
local notation "P" => ProjectiveLine.coefficientMap (f).toRingHom

/-- The identity position is the entire original ordered exterior. -/
theorem coefficientShearResidueStrictPositiveCycleComponent_exterior : C 0 = F := by
  simp only [coefficientShearResidueStrictPositiveCycleComponent, Fin.val_zero, ite_true]

/-- Each first branch retains its original full reversed projective parameter. -/
theorem coefficientShearResidueStrictPositiveCycleComponent_first (j : Fin (s + 2)) :
    C ⟨j.val + 1, by omega⟩ = ρ ≫ B j 0 := by
  simp only [coefficientShearResidueStrictPositiveCycleComponent,
    show ¬j.val + 1 = 0 from by omega, show j.val + 1 ≤ s + 2 from by omega,
    dite_true, ite_false, Nat.add_sub_cancel]

/-- Each opposite branch retains its original complete projective parameter. -/
theorem coefficientShearResidueStrictPositiveCycleComponent_second (j : Fin (s + 2)) :
    C ⟨2 * s + 4 - j.val, by omega⟩ = B j 1 := by
  simp only [coefficientShearResidueStrictPositiveCycleComponent,
    show ¬2 * s + 4 - j.val = 0 from by omega,
    show ¬2 * s + 4 - j.val ≤ s + 2 from by omega,
    dite_false, ite_false,
    show 2 * s + 4 - (2 * s + 4 - j.val) = j.val from by omega]

/-- The full exterior and every complete branch intertwine the actual reflected parameter. -/
@[reassoc] theorem coefficientShearResidueStrictPositiveCycleComponent_reflection
    (i : Fin (2 * s + 5)) :
    C i ≫ σ = P ≫ ρ ≫ C (PolygonPinching.reflectIndex i) := by
  by_cases hz : i.val = 0
  · have hi : i = 0 := Fin.ext hz
    subst i
    rw [PolygonPinching.reflectIndex_zero,
      coefficientShearResidueStrictPositiveCycleComponent_exterior]
    have hP : nodeTangentLineCoefficients V = P :=
      nodeTangentLineCoefficients_eq_coefficientMap V
    calc
      F ≫ σ = (nodeTangentLineCoefficients V ≫ ρ) ≫ F :=
        coefficientShearResidueExteriorLift_conjugation
          hπ data (s + 1) hs d (by dsimp; omega) hres a
          (residueTangentComponentUnit_val W h3 h4 hc)
      _ = (P ≫ ρ) ≫ F := congrArg
        (fun (q : ProjectiveLine.scheme Q ⟶ ProjectiveLine.scheme Q) => (q ≫ ρ) ≫ F) hP
      _ = P ≫ ρ ≫ F := Category.assoc _ _ _
  have hv : (PolygonPinching.reflectIndex i).val = 2 * s + 5 - i.val :=
    PolygonPinching.reflectIndex_val i (by intro h; exact hz (congrArg Fin.val h))
  by_cases hb : i.val ≤ s + 2
  · let j : Fin (s + 2) := ⟨i.val - 1, by omega⟩
    have hi : i = ⟨j.val + 1, by omega⟩ := Fin.ext (by dsimp [j]; omega)
    have hr : PolygonPinching.reflectIndex i = ⟨2 * s + 4 - j.val, by omega⟩ :=
      Fin.ext (by dsimp [j]; omega)
    rw [hr]
    conv_lhs => rw [hi]
    rw [coefficientShearResidueStrictPositiveCycleComponent_first,
      coefficientShearResidueStrictPositiveCycleComponent_second, Category.assoc,
      coefficientShearResidueStrictPositiveBranch_conjugation,
      ProjectiveLine.endpointReversal_coefficientMap_assoc]
    rfl
  · let j : Fin (s + 2) := ⟨2 * s + 4 - i.val, by omega⟩
    have hi : i = ⟨2 * s + 4 - j.val, by omega⟩ := Fin.ext (by dsimp [j]; omega)
    have hr : PolygonPinching.reflectIndex i = ⟨j.val + 1, by omega⟩ :=
      Fin.ext (by dsimp [j]; omega)
    rw [hr]
    conv_lhs => rw [hi]
    rw [coefficientShearResidueStrictPositiveCycleComponent_first,
      coefficientShearResidueStrictPositiveCycleComponent_second,
      coefficientShearResidueStrictPositiveBranch_conjugation,
      ← Category.assoc ρ, ProjectiveLine.endpointReversal_involutive, Category.id_comp]
    rfl

end FLT.Mazur.WeierstrassDividedDepth
