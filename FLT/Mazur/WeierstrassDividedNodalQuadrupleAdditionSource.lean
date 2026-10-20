/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalQuadrupleSecantGluing
public import FLT.Mazur.WeierstrassDividedNodalTangentGluing

/-!
# Quadruple-depth tangent and secant domains in their common input source

Both constructed output domains embed as actual opens of the same original
input source and have outputs in the same depth-2k finite-model smooth locus.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] rootShearCurve nodalSecondShear nodalSecondQuotient
  nodalBranchCommonOutput nodalNegativeBranchOutput
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsLocalRing R] [IsNoetherianRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {k : ℕ} (D : SplitNodeDepth W π (4 * k))
  (d : Data W π k) (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "s" => π ^ k
local notation "T" => DividedTangentRing W s d.b3 d.b4 d.b6 a c
local notation "V" => DividedSecantRing W s d.b3 d.b4 d.b6 a c
local notation "t" => Spec.map (CommRingCat.ofHom (algebraMap S T))
local notation "v" => Spec.map (CommRingCat.ofHom (algebraMap S V))
local notation "hπ" => D.uniformizer_ne_zero
local notation "base" => finiteGlobalStructure hπ (splitNodeDoubledFamily D) (k + k) le_rfl
local notation "U" => (base).smoothLocus
local notation "Ot" => nodalTangentBranchOutputOpen D d a c
local notation "Os" => ⨆ i, nodalQuadrupleSecantLocalOpen D d a c i
local notation "ft" => nodalTangentGluedOutput D d a c
local notation "fs" => nodalQuadrupleSecantGluedOutput D d a c

/-- The tangent and secant output domains before taking their images in the input source. -/
def nodalQuadrupleAdditionSource : Bool → Scheme
  | true => (Ot).toScheme
  | false => (Os).toScheme

/-- Each actual smooth-output domain embeds in the unchanged input source. -/
def nodalQuadrupleAdditionInclusion (i : Bool) :
    nodalQuadrupleAdditionSource D d a c i ⟶ Spec (.of S) :=
  match i with
  | true => (Ot).ι ≫ t
  | false => (Os).ι ≫ v

instance nodalQuadrupleAdditionInclusion_open (i : Bool) :
    IsOpenImmersion
      (nodalQuadrupleAdditionInclusion D d a c i) := by
  let _ : IsOpenImmersion t :=
    IsOpenImmersion.of_isLocalization (dividedTangentDenominator W s d.b3 d.b4 d.b6 a c)
  let _ : IsOpenImmersion v :=
    IsOpenImmersion.of_isLocalization (a (x W s d.b3 d.b4 d.b6) - c (x W s d.b3 d.b4 d.b6))
  cases i <;> unfold nodalQuadrupleAdditionInclusion <;> infer_instance

/-- Both output formulas now take values in precisely the same resolved smooth locus. -/
def nodalQuadrupleAdditionOutput (i : Bool) :
    nodalQuadrupleAdditionSource D d a c i ⟶ (U).toScheme :=
  match i with
  | true => ft
  | false => fs

/-- Both entire output domains retain the coefficient structure of the input source. -/
@[reassoc] theorem nodalQuadrupleAdditionOutput_structure (i : Bool) :
    nodalQuadrupleAdditionOutput D d a c i ≫ (U).ι ≫ base =
      nodalQuadrupleAdditionInclusion D d a c i ≫
        Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  have ht : t ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) =
      Spec.map (CommRingCat.ofHom (algebraMap R T)) := by
    rw [← Spec.map_comp]
    rfl
  have hv : v ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) =
      Spec.map (CommRingCat.ofHom (algebraMap R V)) := by
    rw [← Spec.map_comp]
    rfl
  cases i with
  | true =>
    simp only [nodalQuadrupleAdditionOutput, nodalQuadrupleAdditionInclusion,
      Category.assoc, ht, nodalTangentGluedOutput_structure]
  | false =>
    change fs ≫ (U).ι ≫ finiteGlobalContraction hπ (splitNodeDoubledFamily D) (k + k) le_rfl ≫
      WeierstrassIntegralChart.integralCurveStructure W = _
    rw [nodalQuadrupleSecantGluedOutput_contraction_assoc, dividedSecantToCurve_structure]
    simp only [nodalQuadrupleAdditionInclusion, Category.assoc, hv]

end FLT.Mazur.WeierstrassDividedDepth
