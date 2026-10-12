/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRootEqualityComponent
public import FLT.Mazur.WeierstrassCoefficientShearScaleOneEqualityComponent
public import FLT.Mazur.WeierstrassCoefficientShearTerminalLaurentRootChange
public import FLT.Mazur.ProjectiveLineScaledEndpointReversal
public import FLT.Mazur.WeierstrassDividedGlobalFiniteProper
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber

/-!
# Full root exchange on independent equality-terminal projective components

The entire Laurent comparison extends across the independent completion.
Both positive preceding scale and scale one retain the actual final index
and the divided-constant factor in the projective reciprocal map.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [Field S] [Algebra R S] (r : S) (j : ℕ) (hj : j + 1 ≤ n)
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
variable (hs : algebraMap R S (π ^ (start + j)) = 0)
  (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b3 = 0)
  (h4 : algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b4 = 0)
  (hc : IsUnit (algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6))
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
  (a : Sˣ) (ha : (a : S) = (rootShearCurve (W.map (algebraMap R S)) r).a₁)
local notation "hsNext" => show algebraMap R S (π ^ (start + (j + 1))) = 0 from by
  rw [← Nat.add_assoc, pow_succ, map_mul, hp, mul_zero]
variable (t : S)
  (ht : t ^ 2 + algebraMap R S W.a₁ * t - algebraMap R S W.a₂ = 0)
  (b : Sˣ) (hb : (b : S) = (rootShearCurve (W.map (algebraMap R S)) t).a₁)
  (hrt : r + t = -algebraMap R S W.a₁)
local notation "C" => coefficientShearRootChange hπ data S r t (j + 1) hj
local notation "G" => coefficientShearGluedIso hπ data S t (j + 1) hj
include hrt

local notation "base" => coefficientShearGluedStructure hπ data S t (j + 1) hj

/-- The complete root equality terminal exchanges roots by the scaled reciprocal. -/
@[reassoc] theorem coefficientShearRootEqualityComponent_rootChange :
    coefficientShearRootEqualityComponent
        hπ data S r j hj hs hp h3 h4 hc hr a ha ≫ (C).hom =
      ProjectiveLine.scaledEndpointReversal S hc.unit ≫
        coefficientShearRootEqualityComponent
          hπ data S t j hj hs hp h3 h4 hc ht b hb := by
  let _ : IsSeparated base := by
    unfold coefficientShearGluedStructure
    infer_instance
  apply ProjectiveLine.torus_hom_ext S base
  · rw [Category.assoc, coefficientShearRootChange_structure,
      coefficientShearRootEqualityComponent_structure, Category.assoc,
      coefficientShearRootEqualityComponent_structure,
      ProjectiveLine.scaledEndpointReversal_toBase]
  · rw [coefficientShearRootEqualityComponent_torus_assoc,
      ProjectiveLine.torus_scaledEndpointReversal_assoc,
      coefficientShearRootEqualityComponent_torus]
    exact coefficientShearRootChange_terminalLaurent
      hπ data S r j hj hp h3 h4 hc hr a ha t ht b hb hrt

variable (hsOne : algebraMap R S (π ^ (start + j)) = 1)

/-- The complete scaleone equality terminal exchanges roots by the scaled reciprocal. -/
@[reassoc] theorem coefficientShearScaleOneEqualityComponent_rootChange :
    coefficientShearScaleOneEqualityComponent
        hπ data S r j hj hsOne hp h3 h4 hc hr a ha ≫ (C).hom =
      ProjectiveLine.scaledEndpointReversal S hc.unit ≫
        coefficientShearScaleOneEqualityComponent
          hπ data S t j hj hsOne hp h3 h4 hc ht b hb := by
  let _ : IsSeparated base := by
    unfold coefficientShearGluedStructure
    infer_instance
  apply ProjectiveLine.torus_hom_ext S base
  · rw [Category.assoc, coefficientShearRootChange_structure,
      coefficientShearScaleOneEqualityComponent_structure, Category.assoc,
      coefficientShearScaleOneEqualityComponent_structure,
      ProjectiveLine.scaledEndpointReversal_toBase]
  · rw [coefficientShearScaleOneEqualityComponent_torus_assoc,
      ProjectiveLine.torus_scaledEndpointReversal_assoc,
      coefficientShearScaleOneEqualityComponent_torus]
    exact coefficientShearRootChange_terminalLaurent
      hπ data S r j hj hp h3 h4 hc hr a ha t ht b hb hrt

end FLT.Mazur.WeierstrassDividedDepth
