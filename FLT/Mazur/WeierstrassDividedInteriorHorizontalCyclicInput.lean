/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInteriorConicPunctures
public import FLT.Mazur.WeierstrassSmoothSuccessiveTensorInput
public import FLT.Mazur.WeierstrassDividedAdjacentParameterStructure

/-!
# Actual independent tensor inputs on the interior cyclic components

The original successive tensor algebra gives points of the actual retained
finite model. Both conic inputs are identified with their labeled projective
punctures, keeping the independent smooth parameter and coefficient morphism.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) = depth) (j : Fin s)
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (j.val + 1) (by omega))
local notation "C" => SmoothHorizontalResidueRing D
local notation "A" => ScalarExtension W (π ^ (start + j.val)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) K
local notation "g" => olderGlobalTensorChart hπ data K j.val (by omega)
  (s - j.val) (by omega)
local notation "transport" => eqToHom (finiteGlobalTensorModel_index_congr hπ data K
  (by omega : j.val + 1 + (s - j.val) ≤ n) hs (by omega))
local notation "c" => Spec.map (CommRingCat.ofHom (algebraMap K C))
local notation "p" => pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  (finiteGlobalStructure hπ data (s + 1) hs)
local notation "Z" => positiveEqualityCycleComponent hπ data D s hs hstart hk hp
local notation "b" => Spec.map
  (CommRingCat.ofHom (AlgHom.toRingHom (smoothHorizontalResidueConic D)))

omit hstart hk hp in
/-- Every algebra point of the original retained chart preserves the residue coefficients. -/
theorem interiorHorizontalTensorPoint_structure (f : A →ₐ[K] C) :
    (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ g ≫ transport) ≫ p = c := by
  rw [Category.assoc, Category.assoc,
    finiteGlobalTensorModel_structure_transport hπ data K _ _ (by omega),
    olderGlobalTensorChart_structure, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact RingHom.ext f.commutes

omit hstart hk hp in
/-- An actual successive tensor point over the final residue coefficient scheme. -/
def interiorHorizontalTensorOverPoint (f : A →ₐ[K] C) : Over.mk c ⟶ Over.mk p :=
  Over.homMk (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ g ≫ transport)
    (interiorHorizontalTensorPoint_structure hπ data D s hs j f)

/-- The first independent input is the original puncture of its interior cyclic component. -/
theorem interiorHorizontalFirstTensorInput_cycle :
    Spec.map (CommRingCat.ofHom
        (smoothSuccessiveFirstTensorInput (k := start + j.val) D e
          (by omega) (by omega)).toRingHom) ≫ g ≫ transport =
      b ≫ ProjectiveLine.overlapLeft K ≫ ProjectiveLine.right K ≫
        (Z ⟨j.val + 2, by omega⟩).left := by
  rw [smoothSuccessiveFirstTensorInput_spec]
  have h := congrArg (b ≫ ·)
    (interiorConicFirstPuncture_cycle hπ data D s hs hstart hk hp j)
  simpa only [olderGlobalMiddleConic, Category.assoc] using h

/-- The opposite independent input retains its original second-chain component label. -/
theorem interiorHorizontalSecondTensorInput_cycle :
    Spec.map (CommRingCat.ofHom
        (smoothSuccessiveSecondTensorInput (k := start + j.val) D e
          (by omega) (by omega)).toRingHom) ≫ g ≫ transport =
      b ≫ ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K ≫
        (Z ⟨2 * s + 2 - j.val, by omega⟩).left := by
  rw [smoothSuccessiveSecondTensorInput_spec]
  have h := congrArg (b ≫ ·)
    (interiorConicSecondPuncture_cycle hπ data D s hs hstart hk hp j)
  simpa only [olderGlobalMiddleConic, Category.assoc] using h

end FLT.Mazur.WeierstrassDividedDepth
