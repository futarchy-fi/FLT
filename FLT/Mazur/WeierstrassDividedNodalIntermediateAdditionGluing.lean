/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalIntermediateAdditionOverlap

/-!
# Glue intermediate tangent and secant outputs over the original input source

Full-overlap compatibility glues both actual domains into a single partial
addition map with values in the same resolved smooth locus.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
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

local notation "inc" => nodalIntermediateAdditionInclusion D hdepth hrk hrm data hj d a c
local notation "out" => nodalIntermediateAdditionOutput D hdepth hrk hrm data hj d a c
local notation "O" => fun i : Bool => (inc i).opensRange
local notation "C" => Scheme.Opens.iSupOpenCover O

/-- The actual union of tangent and secant smooth-output domains in the original input source. -/
def nodalIntermediateAdditionOpen : (Spec (.of S)).Opens := ⨆ i, O i

/-- Transport each actual output to its image open in the unchanged input source. -/
def nodalIntermediateAdditionLocalOutput (i : Bool) : (O i).toScheme ⟶ (U).toScheme :=
  (inc i).isoOpensRange.inv ≫ out i

local notation "F" => nodalIntermediateAdditionLocalOutput D hdepth hrk hrm data hj d a c

/-- The entire image-open overlap carries equal resolved outputs. -/
theorem nodalIntermediateAdditionLocalOutput_compatible (i j : Bool) :
    pullback.fst ((C).f i) ((C).f j) ≫ F i =
      pullback.snd ((C).f i) ((C).f j) ≫ F j := by
  have hi : (C).f i ≫ (⨆ i, O i).ι = (O i).ι := Scheme.homOfLE_ι _ (le_iSup O i)
  have hjc : (C).f j ≫ (⨆ i, O i).ι = (O j).ι := Scheme.homOfLE_ι _ (le_iSup O j)
  have hp : pullback.fst ((C).f i) ((C).f j) ≫ (O i).ι =
      pullback.snd ((C).f i) ((C).f j) ≫ (O j).ι := by
    simpa only [Category.assoc, hi, hjc] using
      congrArg (fun z => z ≫ (⨆ i, O i).ι)
        (pullback.condition (f := (C).f i) (g := (C).f j))
  have h := nodalIntermediateAdditionOutput_overlap D hdepth hrk hrm data hj d a c i j
    (pullback.fst ((C).f i) ((C).f j) ≫ (inc i).isoOpensRange.inv)
    (pullback.snd ((C).f i) ((C).f j) ≫ (inc j).isoOpensRange.inv)
    (by simpa only [Category.assoc, Scheme.Hom.isoOpensRange_inv_comp] using hp)
  simpa only [nodalIntermediateAdditionLocalOutput, Category.assoc] using h

/-- The tangent and secant constructions glue to an actual partial addition map. -/
def nodalIntermediateAddition :
    (nodalIntermediateAdditionOpen D hdepth hrk hrm data hj d a c).toScheme ⟶ (U).toScheme :=
  (C).glueMorphisms F
    (nodalIntermediateAdditionLocalOutput_compatible D hdepth hrk hrm data hj d a c)

/-- The glued map recovers each whole local output. -/
@[reassoc] theorem nodalIntermediateAddition_restrict (i : Bool) :
    (C).f i ≫ nodalIntermediateAddition D hdepth hrk hrm data hj d a c = F i :=
  (C).ι_glueMorphisms F
    (nodalIntermediateAdditionLocalOutput_compatible D hdepth hrk hrm data hj d a c) i

/-- On either original formula domain, gluing recovers the constructed resolved output. -/
@[reassoc] theorem nodalIntermediateAddition_formula (i : Bool) :
    (inc i).isoOpensRange.hom ≫ (C).f i ≫
        nodalIntermediateAddition D hdepth hrk hrm data hj d a c = out i := by
  rw [nodalIntermediateAddition_restrict]
  exact Iso.hom_inv_id_assoc _ _

/-- The single partial addition map retains the coefficient point on the entire union. -/
@[reassoc] theorem nodalIntermediateAddition_structure :
    nodalIntermediateAddition D hdepth hrk hrm data hj d a c ≫ (U).ι ≫ base =
      (nodalIntermediateAdditionOpen D hdepth hrk hrm data hj d a c).ι ≫
        Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  apply (C).hom_ext
  intro i
  rw [nodalIntermediateAddition_restrict_assoc]
  simp only [nodalIntermediateAdditionLocalOutput, Category.assoc,
    nodalIntermediateAdditionOutput_structure, Scheme.Hom.isoOpensRange_inv_comp_assoc]
  exact (Scheme.homOfLE_ι_assoc (Spec (.of S)) (le_iSup O i) _).symm

end FLT.Mazur.WeierstrassDividedDepth
