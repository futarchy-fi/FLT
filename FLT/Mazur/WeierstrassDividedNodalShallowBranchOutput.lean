/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteNodalLowerLift
public import FLT.Mazur.WeierstrassDividedNodalLowerNormalization
public import FLT.Mazur.WeierstrassDividedShearGlobalIso
public import FLT.Mazur.WeierstrassDividedShearTangentScheme

/-!
# Return shallow nodal outputs to the original finite model

A finite shear constructs the second-coefficient factor. The shallow output
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
  {W : WeierstrassCurve R} {π : R} {n k m : ℕ} (D : SplitNodeDepth W π m)
  (hdepth : 2 * k ≤ m) (hm : m ≤ 3 * k)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hj : m - 2 * k ≤ n)
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
local notation "g" => finiteNodalLowerLift (nodalSecondShear_depth D k)
  hdepth hm dat hj sd (nodalLowerSecondQuotient D (k := k))
  (nodalLowerSecondQuotient_factor D hm) a' c'
local notation "iso" => shearFiniteGlobalIso hπ (start := 0) data σ (m - 2 * k) hj
local notation "cur" => WeierstrassIntegralChart.integralVariableChangeIso W V (⟨1, 0, σ, 0⟩)
  (by unfold rootShearCurve; rfl)

/-- Construct the normalized shallow output from the original input maps. -/
def nodalShallowBranchOutput :
    Spec (.of B) ⟶ finiteGlobalModel hπ (start := 0) data (m - 2 * k) hj :=
  g ≫ (iso).hom

/-- The constructed output retains the original coefficient point. -/
@[reassoc] theorem nodalShallowBranchOutput_structure :
    nodalShallowBranchOutput D hdepth hm data hj d a c ≫
      finiteGlobalStructure hπ (start := 0) data (m - 2 * k) hj =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
  rw [nodalShallowBranchOutput, Category.assoc, shearFiniteGlobalIso_structure]
  exact finiteNodalLowerLift_structure ..

/-- The normalized branch output is returned through the actual original cubic isomorphism. -/
@[reassoc] theorem nodalShallowBranchOutput_sheared_contraction :
    nodalShallowBranchOutput D hdepth hm data hj d a c ≫
      finiteGlobalContraction hπ (start := 0) data (m - 2 * k) hj =
      Spec.map (CommRingCat.ofHom (res).toRingHom) ≫
        dividedTangentToCurve V (π ^ k) (sd).b3 (sd).b4 (sd).b6 a' c'
          (sd).factor3 (sd).factor4 (sd).factor6 ≫ (cur).hom := by
  rw [nodalShallowBranchOutput, Category.assoc, shearFiniteGlobalIso_contraction,
    finiteNodalLowerLift_contraction_assoc]

/-- The normalized output is the original unsheared tangent sum on every common domain. -/
theorem nodalShallowBranchOutput_original_contraction {X : Scheme}
    (p : X ⟶ Spec (.of B)) (q : X ⟶ Spec (.of T))
    (hpq : p ≫ Spec.map (CommRingCat.ofHom (algebraMap S B)) =
      q ≫ Spec.map (CommRingCat.ofHom (algebraMap S T))) :
    p ≫ nodalShallowBranchOutput D hdepth hm data hj d a c ≫
      finiteGlobalContraction hπ (start := 0) data (m - 2 * k) hj =
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
  simpa only [nodalShallowBranchOutput_sheared_contraction, Category.assoc, shearData]
    using hout

variable [IsNoetherianRing R]

/-- Every nodal shallow branch output is smooth in the original supplied finite model. -/
theorem nodalShallowBranchOutput_smooth
    (hlo : 2 * k < m) (hhi : m < 3 * k)
    (p : PrimeSpectrum B) (hp : algebraMap R B π ∈ p.asIdeal) :
    nodalShallowBranchOutput D hdepth hm data hj d a c p ∈
      (finiteGlobalStructure hπ (start := 0) data (m - 2 * k) hj).smoothLocus := by
  have h := Scheme.Hom.preimage_smoothLocus_eq (iso).hom
    (finiteGlobalStructure hπ (start := 0) data (m - 2 * k) hj)
  simp only [shearFiniteGlobalIso_structure] at h
  rw [nodalShallowBranchOutput, Scheme.Hom.comp_apply]
  apply h.ge
  exact finiteNodalLower_nodal_smooth (nodalSecondShear_depth D k) hdepth hm dat hj sd
    (nodalLowerSecondQuotient D (k := k)) (nodalLowerSecondQuotient_factor D hm)
    a' c' hlo hhi (nodalLowerSecondQuotient_mem D hhi) p hp

end FLT.Mazur.WeierstrassDividedDepth
