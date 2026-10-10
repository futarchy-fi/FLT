/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderGlobalMiddleComponents
public import FLT.Mazur.WeierstrassDividedOlderGlobalSections
public import FLT.Mazur.WeierstrassSuccessiveXResidueComponentPoints

/-!
# The global middle component incidence sections

The original ordered conic markings and the origins of both horizontal lines
are the same global sections as the full middle-node origins.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (r : ℕ) (hr : j + 1 + r ≤ n)
  (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
open WeierstrassSuccessiveX
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "c" => residue R (Data.b6 e)
local notation "T" => ScalarExtension W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) K
local notation "o" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (middleNodeOrigin c)))
local notation "g" => olderGlobalTensorChart hπ data K j hj r hr
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))
local notation "f" => finiteGlobalStructure hπ data (j + 1 + r) hr
local notation "first" => residueFirstIncidencePoint D (start + j) hk0 hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "second" => residueSecondIncidencePoint D (start + j) hk0 hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)

open WeierstrassModificationX
local notation "a" => residue R W.a₁
local notation "ha" => D.a₁_unit.map (residue R)

/-- The first conic marking gives exactly the first ordered global section. -/
@[reassoc] theorem olderGlobalFirstSection_conic :
    Spec.map (CommRingCat.ofHom (conicFirstIncidencePoint a c ha).toRingHom) ≫
      olderGlobalMiddleConic hπ data D j hj r hr hk0 hk =
        olderGlobalFirstSection hπ data D j hj r hr hk0 hk := by
  rw [olderGlobalFirstSection,
    ← residueFirstIncidencePoint_conic D (start + j) hk0 hk
      (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e),
    olderGlobalMiddleConic, residueSuccessiveConicImmersion_eq_spec,
    ← Category.assoc, ← Spec.map_comp]
  rfl

/-- The opposite conic marking gives exactly the second ordered global section. -/
@[reassoc] theorem olderGlobalSecondSection_conic :
    Spec.map (CommRingCat.ofHom (conicSecondIncidencePoint a c ha).toRingHom) ≫
      olderGlobalMiddleConic hπ data D j hj r hr hk0 hk =
        olderGlobalSecondSection hπ data D j hj r hr hk0 hk := by
  rw [olderGlobalSecondSection,
    ← residueSecondIncidencePoint_conic D (start + j) hk0 hk
      (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e),
    olderGlobalMiddleConic, residueSuccessiveConicImmersion_eq_spec,
    ← Category.assoc, ← Spec.map_comp]
  rfl

/-- The zero-slope line's parameter origin is the first ordered global section. -/
@[reassoc] theorem olderGlobalFirstSection_line :
    Spec.map (CommRingCat.ofHom (Polynomial.aeval (0 : K)).toRingHom) ≫
      olderGlobalMiddleFirstLine hπ data D j hj r hr hk0 hk =
        olderGlobalFirstSection hπ data D j hj r hr hk0 hk := by
  rw [olderGlobalFirstSection,
    ← residueFirstIncidencePoint_line D (start + j) hk0 hk
      (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e),
    olderGlobalMiddleFirstLine, residueSuccessiveLineImmersion_eq_spec,
    ← Category.assoc, ← Spec.map_comp]
  rfl

/-- The opposite line's parameter origin is the second ordered global section. -/
@[reassoc] theorem olderGlobalSecondSection_line :
    Spec.map (CommRingCat.ofHom (Polynomial.aeval (0 : K)).toRingHom) ≫
      olderGlobalMiddleSecondLine hπ data D j hj r hr hk0 hk =
        olderGlobalSecondSection hπ data D j hj r hr hk0 hk := by
  rw [olderGlobalSecondSection,
    ← residueSecondIncidencePoint_line D (start + j) hk0 hk
      (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e),
    olderGlobalMiddleSecondLine, residueSuccessiveLineImmersion_eq_spec,
    ← Category.assoc, ← Spec.map_comp]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
