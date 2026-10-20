/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteTripleBranchLift
public import FLT.Mazur.WeierstrassDividedNodalSecondNormalization
public import FLT.Mazur.WeierstrassDividedShearGlobalIso

/-!
# Normalized branch outputs in the original finite model

The original node conditions construct a finite shear, its second coefficient
quotient, and a first output. The global shear isomorphism returns that
output to the original model and retains its original coefficient map.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation WeierstrassIntegralChart
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] rootShearCurve nodalSecondShear nodalSecondQuotient
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsLocalRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {start k n : ℕ} (D : SplitNodeDepth W π (3 * (start + k)))
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (hj : k ≤ n)
local notation "d" => data ⟨k, Nat.lt_succ_of_le hj⟩
local notation "r" => nodalSecondShear D (start + k)
local notation "V" => rootShearCurve W r
local notation "sd" => shearData d r
local notation "dat" => fun i => shearData (data i) r
local notation "hπ" => D.uniformizer_ne_zero
variable (a c : WeierstrassDilatation.Coordinate
  (rootShearCurve W (nodalSecondShear D (start + k))) (π ^ (start + k))
  (data ⟨k, Nat.lt_succ_of_le hj⟩).b3
  ((data ⟨k, Nat.lt_succ_of_le hj⟩).b4 - nodalSecondShear D (start + k) *
    (data ⟨k, Nat.lt_succ_of_le hj⟩).b3)
  (data ⟨k, Nat.lt_succ_of_le hj⟩).b6 →ₐ[R] S)
local notation "B" => DividedTangentBranchRing V (π ^ (start + k)) (sd).b3 (sd).b4 (sd).b6 a c
local notation "g" => finiteTripleBranchLift (nodalSecondShear_depth D (start + k)) dat hj
  (nodalSecondQuotient D (start + k)) (nodalSecondQuotient_factor D (start + k)) a c
local notation "e" => shearFiniteGlobalIso hπ data r k hj
local notation "b" => finiteGlobalStructure hπ data k hj
local notation "i" => integralVariableChangeIso W V (⟨1, 0, r, 0⟩)
  (by unfold rootShearCurve; rfl)
local notation "res" =>
  dividedTangentBranchRestriction V (π ^ (start + k)) (sd).b3 (sd).b4 (sd).b6 a c

/-- The first normalized output returned to the entire original finite model. -/
def finiteTripleNormalizedBranchLift : Spec (.of B) ⟶ finiteGlobalModel hπ data k hj :=
  g ≫ (e).hom

/-- The returned output has the original coefficient map on its whole branch source. -/
@[reassoc] theorem finiteTripleNormalizedBranchLift_structure :
    finiteTripleNormalizedBranchLift D data hj a c ≫ b =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
  rw [finiteTripleNormalizedBranchLift, Category.assoc, shearFiniteGlobalIso_structure]
  exact finiteTripleBranchLift_structure ..

/-- The returned contraction is the actual normalized tangent sum in original coordinates. -/
@[reassoc] theorem finiteTripleNormalizedBranchLift_contraction :
    finiteTripleNormalizedBranchLift D data hj a c ≫
        finiteGlobalContraction hπ data k hj =
      Spec.map (CommRingCat.ofHom (res).toRingHom) ≫
        dividedTangentToCurve V (π ^ (start + k)) (sd).b3 (sd).b4 (sd).b6 a c
          (sd).factor3 (sd).factor4 (sd).factor6 ≫ (i).hom := by
  rw [finiteTripleNormalizedBranchLift, Category.assoc, shearFiniteGlobalIso_contraction,
    finiteTripleBranchLift_contraction_assoc]

variable [IsNoetherianRing R]

/-- Every special-fiber prime maps to the smooth locus of the original finite model. -/
theorem finiteTripleNormalizedBranchLift_nodal_smooth (p : PrimeSpectrum B)
    (hp : algebraMap R B π ∈ p.asIdeal) :
    finiteTripleNormalizedBranchLift D data hj a c p ∈ (b).smoothLocus := by
  have h := Scheme.Hom.preimage_smoothLocus_eq (e).hom b
  simp only [shearFiniteGlobalIso_structure] at h
  apply h.ge
  exact finiteTripleBranchLift_smooth (nodalSecondShear_depth D (start + k)) dat hj
    (nodalSecondQuotient D (start + k)) (nodalSecondQuotient_factor D (start + k)) a c p hp

end FLT.Mazur.WeierstrassDividedDepth
