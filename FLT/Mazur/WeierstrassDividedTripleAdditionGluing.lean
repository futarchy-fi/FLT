/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTripleAdditionOverlap

/-!
# Glue exact-triple tangent and secant outputs over the original input source

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
  tripleBranchCommonOutput tripleNegativeBranchOutput
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsBezout R] [IsLocalRing R] [IsNoetherianRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {start n k : ℕ}
  (D : SplitNodeDepth W π (3 * (start + k)))
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (hk : k ≤ n)
  (a c : Coordinate W (π ^ (start + k))
    (data ⟨k, Nat.lt_succ_of_le hk⟩).b3 (data ⟨k, Nat.lt_succ_of_le hk⟩).b4
    (data ⟨k, Nat.lt_succ_of_le hk⟩).b6 →ₐ[R] S)
local notation "d" => data ⟨k, Nat.lt_succ_of_le hk⟩
local notation "s" => π ^ (start + k)
local notation "T" => DividedTangentRing W s (d).b3 (d).b4 (d).b6 a c
local notation "V" => DividedSecantRing W s (d).b3 (d).b4 (d).b6 a c
local notation "t" => Spec.map (CommRingCat.ofHom (algebraMap S T))
local notation "v" => Spec.map (CommRingCat.ofHom (algebraMap S V))
local notation "hπ" => D.uniformizer_ne_zero
local notation "base" => finiteGlobalStructure hπ data k hk
local notation "U" => (base).smoothLocus
local notation "Ot" => tripleTangentBranchOutputOpen D data hk a c
local notation "Os" => ⨆ i, tripleSecantLocalOpen D data hk a c i
local notation "ft" => tripleTangentGluedOutput D data hk a c
local notation "fs" => tripleSecantGluedOutput D data hk a c

local notation "inc" => tripleAdditionInclusion D data hk a c
local notation "out" => tripleAdditionOutput D data hk a c
local notation "O" => fun i : Bool => (inc i).opensRange
local notation "C" => Scheme.Opens.iSupOpenCover O

/-- The actual union of tangent and secant smooth-output domains in the original input source. -/
def tripleAdditionOpen : (Spec (.of S)).Opens := ⨆ i, O i

/-- Transport each actual output to its image open in the unchanged input source. -/
def tripleAdditionLocalOutput (i : Bool) : (O i).toScheme ⟶ (U).toScheme :=
  (inc i).isoOpensRange.inv ≫ out i

local notation "F" => tripleAdditionLocalOutput D data hk a c

/-- The entire image-open overlap carries equal resolved outputs. -/
theorem tripleAdditionLocalOutput_compatible (i j : Bool) :
    pullback.fst ((C).f i) ((C).f j) ≫ F i =
      pullback.snd ((C).f i) ((C).f j) ≫ F j := by
  have hi : (C).f i ≫ (⨆ i, O i).ι = (O i).ι := Scheme.homOfLE_ι _ (le_iSup O i)
  have hjc : (C).f j ≫ (⨆ i, O i).ι = (O j).ι := Scheme.homOfLE_ι _ (le_iSup O j)
  have hp : pullback.fst ((C).f i) ((C).f j) ≫ (O i).ι =
      pullback.snd ((C).f i) ((C).f j) ≫ (O j).ι := by
    simpa only [Category.assoc, hi, hjc] using
      congrArg (fun z => z ≫ (⨆ i, O i).ι)
        (pullback.condition (f := (C).f i) (g := (C).f j))
  have h := tripleAdditionOutput_overlap D data hk a c i j
    (pullback.fst ((C).f i) ((C).f j) ≫ (inc i).isoOpensRange.inv)
    (pullback.snd ((C).f i) ((C).f j) ≫ (inc j).isoOpensRange.inv)
    (by simpa only [Category.assoc, Scheme.Hom.isoOpensRange_inv_comp] using hp)
  simpa only [tripleAdditionLocalOutput, Category.assoc] using h

/-- The tangent and secant constructions glue to an actual partial addition map. -/
def tripleAddition :
    (tripleAdditionOpen D data hk a c).toScheme ⟶ (U).toScheme :=
  (C).glueMorphisms F
    (tripleAdditionLocalOutput_compatible D data hk a c)

/-- The glued map recovers each whole local output. -/
@[reassoc] theorem tripleAddition_restrict (i : Bool) :
    (C).f i ≫ tripleAddition D data hk a c = F i :=
  (C).ι_glueMorphisms F
    (tripleAdditionLocalOutput_compatible D data hk a c) i

/-- On either original formula domain, gluing recovers the constructed resolved output. -/
@[reassoc] theorem tripleAddition_formula (i : Bool) :
    (inc i).isoOpensRange.hom ≫ (C).f i ≫
        tripleAddition D data hk a c = out i := by
  rw [tripleAddition_restrict]
  exact Iso.hom_inv_id_assoc _ _

/-- The single partial addition map retains the coefficient point on the entire union. -/
@[reassoc] theorem tripleAddition_structure :
    tripleAddition D data hk a c ≫ (U).ι ≫ base =
      (tripleAdditionOpen D data hk a c).ι ≫
        Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  apply (C).hom_ext
  intro i
  rw [tripleAddition_restrict_assoc]
  simp only [tripleAdditionLocalOutput, Category.assoc,
    tripleAdditionOutput_structure, Scheme.Hom.isoOpensRange_inv_comp_assoc]
  exact (Scheme.homOfLE_ι_assoc (Spec (.of S)) (le_iSup O i) _).symm

end FLT.Mazur.WeierstrassDividedDepth
