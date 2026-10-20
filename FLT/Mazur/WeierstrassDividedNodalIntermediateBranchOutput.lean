/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteNodalRefinedBranchLift
public import FLT.Mazur.WeierstrassDividedNodalSecondNormalization
public import FLT.Mazur.WeierstrassDividedShearGlobalIso
public import FLT.Mazur.WeierstrassDividedShearTangentScheme

/-!
# Return intermediate-depth nodal outputs to the original finite model

A finite shear constructs the second-coefficient factor. The refined output
returns through the original finite-model isomorphism, retaining the original
ordered tangent sum on every common domain, including nonreduced domains.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] rootShearCurve nodalSecondShear nodalSecondQuotient
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsLocalRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {n k m r : ℕ} (D : SplitNodeDepth W π m)
  (hdepth : 3 * k ≤ m) (hrk : r ≤ k) (hrm : r ≤ m - 3 * k)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hj : k + r ≤ n)
  (d : Data W π k) (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "σ" => nodalSecondShear D k
local notation "V" => rootShearCurve W σ
local notation "sd" => shearData d σ
local notation "a'" => branchShearInput W (π ^ k) (d).b3 (d).b4 (d).b6 σ a
local notation "c'" => branchShearInput W (π ^ k) (d).b3 (d).b4 (d).b6 σ c
local notation "B" => DividedTangentBranchRing V (π ^ k) (sd).b3 (sd).b4 (sd).b6 a' c'
local notation "T" => DividedTangentRing W (π ^ k) (d).b3 (d).b4 (d).b6 a c
local notation "T'" => DividedTangentRing V (π ^ k) (sd).b3 (sd).b4 (sd).b6 a' c'
local notation "res" => dividedTangentBranchRestriction
  V (π ^ k) (sd).b3 (sd).b4 (sd).b6 a' c'
local notation "hπ" => D.uniformizer_ne_zero

local notation "dat" => fun i => shearData (data i) σ
local notation "g" => finiteNodalRefinedBranchLift (nodalSecondShear_depth D k)
  hdepth hrk hrm dat hj sd (nodalSecondQuotient D k)
  (nodalSecondQuotient_factor D k) a' c'
local notation "iso" => shearFiniteGlobalIso hπ (start := 0) data σ (k + r) hj
local notation "cur" => WeierstrassIntegralChart.integralVariableChangeIso W V (⟨1, 0, σ, 0⟩)
  (by unfold rootShearCurve; rfl)

/-- Construct the normalized intermediate-depth output from the original input maps. -/
def nodalIntermediateBranchOutput :
    Spec (.of B) ⟶ finiteGlobalModel hπ (start := 0) data (k + r) hj :=
  g ≫ (iso).hom

/-- The constructed output retains the original coefficient point. -/
@[reassoc] theorem nodalIntermediateBranchOutput_structure :
    nodalIntermediateBranchOutput D hdepth hrk hrm data hj d a c ≫
      finiteGlobalStructure hπ (start := 0) data (k + r) hj =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
  rw [nodalIntermediateBranchOutput, Category.assoc, shearFiniteGlobalIso_structure]
  exact finiteNodalRefinedBranchLift_structure ..

/-- The normalized branch output is returned through the actual original cubic isomorphism. -/
@[reassoc] theorem nodalIntermediateBranchOutput_sheared_contraction :
    nodalIntermediateBranchOutput D hdepth hrk hrm data hj d a c ≫
      finiteGlobalContraction hπ (start := 0) data (k + r) hj =
      Spec.map (CommRingCat.ofHom (res).toRingHom) ≫
        dividedTangentToCurve V (π ^ k) (sd).b3 (sd).b4 (sd).b6 a' c'
          (sd).factor3 (sd).factor4 (sd).factor6 ≫ (cur).hom := by
  rw [nodalIntermediateBranchOutput, Category.assoc, shearFiniteGlobalIso_contraction,
    finiteNodalRefinedBranchLift_contraction_assoc]

/-- The normalized output is the original unsheared tangent sum on every common domain. -/
theorem nodalIntermediateBranchOutput_original_contraction {X : Scheme}
    (p : X ⟶ Spec (.of B)) (q : X ⟶ Spec (.of T))
    (hpq : p ≫ Spec.map (CommRingCat.ofHom (algebraMap S B)) =
      q ≫ Spec.map (CommRingCat.ofHom (algebraMap S T))) :
    p ≫ nodalIntermediateBranchOutput D hdepth hrk hrm data hj d a c ≫
      finiteGlobalContraction hπ (start := 0) data (k + r) hj =
      q ≫ dividedTangentToCurve W (π ^ k) (d).b3 (d).b4 (d).b6 a c
        (d).factor3 (d).factor4 (d).factor6 := by
  have hres : Spec.map (CommRingCat.ofHom (res).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap S T')) =
        Spec.map (CommRingCat.ofHom (algebraMap S B)) := by
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    ext z
    exact dividedTangentBranchRestriction_source V (π ^ k) (sd).b3 (sd).b4 (sd).b6 a' c' z
  have hpair : (p ≫ Spec.map (CommRingCat.ofHom (res).toRingHom)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap S T')) =
        q ≫ Spec.map (CommRingCat.ofHom (algebraMap S T)) := by
    rw [Category.assoc, hres, hpq]
  have hout := dividedShearTangent_scheme W (π ^ k) (d).b3 (d).b4 (d).b6 σ a c
    (d).factor3 (d).factor4 (d).factor6 (sd).factor3 (sd).factor4 (sd).factor6
    (p ≫ Spec.map (CommRingCat.ofHom (res).toRingHom)) q hpair
  simpa only [nodalIntermediateBranchOutput_sheared_contraction, Category.assoc, shearData]
    using hout

end FLT.Mazur.WeierstrassDividedDepth
