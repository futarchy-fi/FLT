/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRetainedLineProjection
import all FLT.Mazur.WeierstrassCoefficientShearRetainedLineProjection
public import FLT.Mazur.WeierstrassSuccessiveShearConicCoefficient
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber
import all FLT.Mazur.WeierstrassCoefficientShearRetainedIntersections

/-!
# The full original projection of the retained conic

The complete conic retains its actual integral chart embedding and all its
original functions, before composing with any cubic contraction.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S] (r : S)
  (j : ℕ) (hj : j + 1 ≤ n) (m : ℕ) (hm : j + 1 + m ≤ n)
  (hs : algebraMap R S (π ^ (start + j)) = 0) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S (data ⟨j + 1, by omega⟩).b3 = 0)
  (h4 : algebraMap R S (data ⟨j + 1, by omega⟩).b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "C" => coefficientShearRetainedConic hπ data S r (j + 1 + m) hm
  ⟨j, by omega⟩ hs hp h3 h4 hr
local notation "P" => coefficientShearGluedProjection hπ data S r (j + 1 + m) hm
local notation "c" => originalShearConicMap W (π ^ (start + j)) π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr
local notation "F" => olderSuccessiveChart hπ data j hj m hm ≫
  finiteLocalChart hπ data (j + 1 + m) hm

/-- The entire retained conic projects by the actual original integral coordinate map. -/
theorem coefficientShearRetainedConic_projection :
    C ≫ P = Spec.map (CommRingCat.ofHom (c).toRingHom) ≫ F := by
  rw [← coefficientShearRetainedTensorChart_conic, Category.assoc,
    coefficientShearRetainedTensorChart_projection hπ data S r j hj m hm]
  rw [tensorShearConicImmersion_eq_spec, ← Category.assoc]
  apply congrArg (· ≫ F)
  exact originalShearConicMap_spec W (π ^ (start + j)) π
    (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr

end FLT.Mazur.WeierstrassDividedDepth
