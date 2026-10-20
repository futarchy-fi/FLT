/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalIntermediateSecantGluing
public import FLT.Mazur.WeierstrassDividedNodalIntermediateTangentGluing

/-!
# Intermediate tangent and secant domains in their common input source

Both constructed output domains embed as actual opens of the same original
input source and have outputs in the same depth-k+r finite-model smooth locus.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] rootShearCurve nodalSecondShear nodalSecondQuotient
  nodalIntermediateBranchCommonOutput nodalIntermediateNegativeBranchOutput
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsLocalRing R] [IsNoetherianRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {n k m r : ℕ} (D : SplitNodeDepth W π m)
  (hdepth : 3 * k ≤ m) (hrk : r ≤ k) (hrm : r ≤ m - 3 * k)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (hj : k + r ≤ n)
  (d : Data W π k) (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "s" => π ^ k
local notation "T" => DividedTangentRing W s d.b3 d.b4 d.b6 a c
local notation "V" => DividedSecantRing W s d.b3 d.b4 d.b6 a c
local notation "t" => Spec.map (CommRingCat.ofHom (algebraMap S T))
local notation "v" => Spec.map (CommRingCat.ofHom (algebraMap S V))
local notation "hπ" => D.uniformizer_ne_zero
local notation "base" => finiteGlobalStructure hπ (start := 0) data (k + r) hj
local notation "U" => (base).smoothLocus
local notation "Ot" => nodalIntermediateTangentBranchOutputOpen D hdepth hrk hrm data hj d a c
local notation "Os" => ⨆ i, nodalIntermediateSecantLocalOpen D hdepth hrk hrm data hj d a c i
local notation "ft" => nodalIntermediateTangentGluedOutput D hdepth hrk hrm data hj d a c
local notation "fs" => nodalIntermediateSecantGluedOutput D hdepth hrk hrm data hj d a c

/-- The tangent and secant output domains before taking their images in the input source. -/
def nodalIntermediateAdditionSource : Bool → Scheme
  | true => (Ot).toScheme
  | false => (Os).toScheme

/-- Each actual smooth-output domain embeds in the unchanged input source. -/
def nodalIntermediateAdditionInclusion (i : Bool) :
    nodalIntermediateAdditionSource D hdepth hrk hrm data hj d a c i ⟶ Spec (.of S) :=
  match i with
  | true => (Ot).ι ≫ t
  | false => (Os).ι ≫ v

instance nodalIntermediateAdditionInclusion_open (i : Bool) :
    IsOpenImmersion
      (nodalIntermediateAdditionInclusion D hdepth hrk hrm data hj d a c i) := by
  let _ : IsOpenImmersion t :=
    IsOpenImmersion.of_isLocalization (dividedTangentDenominator W s d.b3 d.b4 d.b6 a c)
  let _ : IsOpenImmersion v :=
    IsOpenImmersion.of_isLocalization (a (x W s d.b3 d.b4 d.b6) - c (x W s d.b3 d.b4 d.b6))
  cases i <;> unfold nodalIntermediateAdditionInclusion <;> infer_instance

/-- Both output formulas now take values in precisely the same resolved smooth locus. -/
def nodalIntermediateAdditionOutput (i : Bool) :
    nodalIntermediateAdditionSource D hdepth hrk hrm data hj d a c i ⟶ (U).toScheme :=
  match i with
  | true => ft
  | false => fs

/-- Both entire output domains retain the coefficient structure of the input source. -/
@[reassoc] theorem nodalIntermediateAdditionOutput_structure (i : Bool) :
    nodalIntermediateAdditionOutput D hdepth hrk hrm data hj d a c i ≫ (U).ι ≫ base =
      nodalIntermediateAdditionInclusion D hdepth hrk hrm data hj d a c i ≫
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
    simp only [nodalIntermediateAdditionOutput, nodalIntermediateAdditionInclusion,
      Category.assoc, ht, nodalIntermediateTangentGluedOutput_structure]
  | false =>
    change fs ≫ (U).ι ≫ finiteGlobalContraction hπ (start := 0) data (k + r) hj ≫
      WeierstrassIntegralChart.integralCurveStructure W = _
    rw [nodalIntermediateSecantGluedOutput_contraction_assoc, dividedSecantToCurve_structure]
    simp only [nodalIntermediateAdditionInclusion, Category.assoc, hv]

end FLT.Mazur.WeierstrassDividedDepth
