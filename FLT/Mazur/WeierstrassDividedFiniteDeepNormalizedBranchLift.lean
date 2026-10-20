/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteDoubledBranchDeepSmooth
public import FLT.Mazur.WeierstrassDividedNodalSecondNormalization
public import FLT.Mazur.WeierstrassDividedShearGlobalIso

/-!
# Deep normalized branch outputs in the supplied finite model

The original node conditions construct a finite shear, its second coefficient
quotient, and a deeper output. The global shear isomorphism returns that
output to the supplied original model and retains its coefficient map.
Above quadruple node depth every closed-fiber output is smooth.
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
  {W : WeierstrassCurve R} {π : R} {k n m : ℕ} (D : SplitNodeDepth W π m)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (hj : k + k ≤ n) (d : Data W π k)
local notation "r" => nodalSecondShear D k
local notation "V" => rootShearCurve W r
local notation "sd" => shearData d r
local notation "dat" => fun i => shearData (data i) r
local notation "hπ" => D.uniformizer_ne_zero
variable (a c : WeierstrassDilatation.Coordinate
  (rootShearCurve W (nodalSecondShear D k)) (π ^ k)
  d.b3 (d.b4 - nodalSecondShear D k * d.b3) d.b6 →ₐ[R] S)
local notation "B" => DividedTangentBranchRing V (π ^ k) (sd).b3 (sd).b4 (sd).b6 a c
local notation "g" => finiteFactoredBranchLift hπ dat (k + k) hj sd (Nat.zero_add _)
  (nodalSecondQuotient D k) (nodalSecondQuotient_factor D k) a c
local notation "e" => shearFiniteGlobalIso hπ data r (k + k) hj
local notation "b" => finiteGlobalStructure hπ data (k + k) hj
local notation "i" => integralVariableChangeIso W V (⟨1, 0, r, 0⟩)
  (by unfold rootShearCurve; rfl)
local notation "res" => dividedTangentBranchRestriction V (π ^ k) (sd).b3 (sd).b4 (sd).b6 a c

/-- The deeper normalized output returned to the entire original finite model. -/
def finiteDeepNormalizedBranchLift : Spec (.of B) ⟶ finiteGlobalModel hπ data (k + k) hj :=
  g ≫ (e).hom

/-- The returned output has the original coefficient map on its whole branch source. -/
@[reassoc] theorem finiteDeepNormalizedBranchLift_structure :
    finiteDeepNormalizedBranchLift D data hj d a c ≫ b =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
  rw [finiteDeepNormalizedBranchLift, Category.assoc, shearFiniteGlobalIso_structure]
  exact finiteFactoredBranchLift_structure ..

/-- The returned contraction is the actual normalized tangent sum in original coordinates. -/
@[reassoc] theorem finiteDeepNormalizedBranchLift_contraction :
    finiteDeepNormalizedBranchLift D data hj d a c ≫
        finiteGlobalContraction hπ data (k + k) hj =
      Spec.map (CommRingCat.ofHom (res).toRingHom) ≫
        dividedTangentToCurve V (π ^ k) (sd).b3 (sd).b4 (sd).b6 a c
          (sd).factor3 (sd).factor4 (sd).factor6 ≫ (i).hom := by
  rw [finiteDeepNormalizedBranchLift, Category.assoc, shearFiniteGlobalIso_contraction,
    finiteFactoredBranchLift_contraction_assoc]

variable [IsNoetherianRing R]

/-- Every special-fiber prime maps to the smooth locus of the original finite model. -/
theorem finiteDeepNormalizedBranchLift_nodal_smooth (hk : 0 < k) (hm : 4 * k < m)
    (p : PrimeSpectrum B)
    (hp : algebraMap R B π ∈ p.asIdeal) :
    finiteDeepNormalizedBranchLift D data hj d a c p ∈ (b).smoothLocus := by
  have h := Scheme.Hom.preimage_smoothLocus_eq (e).hom b
  simp only [shearFiniteGlobalIso_structure] at h
  apply h.ge
  exact finiteDoubledBranch_deep_smooth (nodalSecondShear_depth D k) dat (k + k) hj sd
    (Nat.zero_add _) (nodalSecondQuotient D k) (nodalSecondQuotient_factor D k)
    a c hk hm p hp

end FLT.Mazur.WeierstrassDividedDepth
