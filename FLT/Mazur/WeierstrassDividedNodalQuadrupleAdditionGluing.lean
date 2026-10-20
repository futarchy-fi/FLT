/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalQuadrupleAdditionOverlap

/-!
# Glue quadruple-depth tangent and secant outputs over the original input source

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

local notation "inc" => nodalQuadrupleAdditionInclusion D d a c
local notation "out" => nodalQuadrupleAdditionOutput D d a c
local notation "O" => fun i : Bool => (inc i).opensRange
local notation "C" => Scheme.Opens.iSupOpenCover O

/-- The actual union of tangent and secant smooth-output domains in the original input source. -/
def nodalQuadrupleAdditionOpen : (Spec (.of S)).Opens := ⨆ i, O i

/-- Transport each actual output to its image open in the unchanged input source. -/
def nodalQuadrupleAdditionLocalOutput (i : Bool) : (O i).toScheme ⟶ (U).toScheme :=
  (inc i).isoOpensRange.inv ≫ out i

local notation "F" => nodalQuadrupleAdditionLocalOutput D d a c

/-- The entire image-open overlap carries equal resolved outputs. -/
theorem nodalQuadrupleAdditionLocalOutput_compatible (i j : Bool) :
    pullback.fst ((C).f i) ((C).f j) ≫ F i =
      pullback.snd ((C).f i) ((C).f j) ≫ F j := by
  have hi : (C).f i ≫ (⨆ i, O i).ι = (O i).ι := Scheme.homOfLE_ι _ (le_iSup O i)
  have hjc : (C).f j ≫ (⨆ i, O i).ι = (O j).ι := Scheme.homOfLE_ι _ (le_iSup O j)
  have hp : pullback.fst ((C).f i) ((C).f j) ≫ (O i).ι =
      pullback.snd ((C).f i) ((C).f j) ≫ (O j).ι := by
    simpa only [Category.assoc, hi, hjc] using
      congrArg (fun z => z ≫ (⨆ i, O i).ι)
        (pullback.condition (f := (C).f i) (g := (C).f j))
  have h := nodalQuadrupleAdditionOutput_overlap D d a c i j
    (pullback.fst ((C).f i) ((C).f j) ≫ (inc i).isoOpensRange.inv)
    (pullback.snd ((C).f i) ((C).f j) ≫ (inc j).isoOpensRange.inv)
    (by simpa only [Category.assoc, Scheme.Hom.isoOpensRange_inv_comp] using hp)
  simpa only [nodalQuadrupleAdditionLocalOutput, Category.assoc] using h

/-- The tangent and secant constructions glue to an actual partial addition map. -/
def nodalQuadrupleAddition :
    (nodalQuadrupleAdditionOpen D d a c).toScheme ⟶ (U).toScheme :=
  (C).glueMorphisms F
    (nodalQuadrupleAdditionLocalOutput_compatible D d a c)

/-- The glued map recovers each whole local output. -/
@[reassoc] theorem nodalQuadrupleAddition_restrict (i : Bool) :
    (C).f i ≫ nodalQuadrupleAddition D d a c = F i :=
  (C).ι_glueMorphisms F
    (nodalQuadrupleAdditionLocalOutput_compatible D d a c) i

/-- On either original formula domain, gluing recovers the constructed resolved output. -/
@[reassoc] theorem nodalQuadrupleAddition_formula (i : Bool) :
    (inc i).isoOpensRange.hom ≫ (C).f i ≫
        nodalQuadrupleAddition D d a c = out i := by
  rw [nodalQuadrupleAddition_restrict]
  exact Iso.hom_inv_id_assoc _ _

/-- The single partial addition map retains the coefficient point on the entire union. -/
@[reassoc] theorem nodalQuadrupleAddition_structure :
    nodalQuadrupleAddition D d a c ≫ (U).ι ≫ base =
      (nodalQuadrupleAdditionOpen D d a c).ι ≫
        Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  apply (C).hom_ext
  intro i
  rw [nodalQuadrupleAddition_restrict_assoc]
  simp only [nodalQuadrupleAdditionLocalOutput, Category.assoc,
    nodalQuadrupleAdditionOutput_structure, Scheme.Hom.isoOpensRange_inv_comp_assoc]
  exact (Scheme.homOfLE_ι_assoc (Spec (.of S)) (le_iSup O i) _).symm

end FLT.Mazur.WeierstrassDividedDepth
