/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTripleSecantGluing
public import FLT.Mazur.WeierstrassDividedTripleTangentGluing

/-!
# Exact-triple tangent and secant domains in their common input source

Both constructed output domains embed as actual opens of the same original
input source and have outputs in the same input-depth finite-model smooth locus.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
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

/-- The tangent and secant output domains before taking their images in the input source. -/
def tripleAdditionSource : Bool → Scheme
  | true => (Ot).toScheme
  | false => (Os).toScheme

/-- Each actual smooth-output domain embeds in the unchanged input source. -/
def tripleAdditionInclusion (i : Bool) :
    tripleAdditionSource D data hk a c i ⟶ Spec (.of S) :=
  match i with
  | true => (Ot).ι ≫ t
  | false => (Os).ι ≫ v

instance tripleAdditionInclusion_open (i : Bool) :
    IsOpenImmersion
      (tripleAdditionInclusion D data hk a c i) := by
  let _ : IsOpenImmersion t :=
    IsOpenImmersion.of_isLocalization (dividedTangentDenominator W s (d).b3 (d).b4 (d).b6 a c)
  let _ : IsOpenImmersion v :=
    IsOpenImmersion.of_isLocalization
      (a (x W s (d).b3 (d).b4 (d).b6) - c (x W s (d).b3 (d).b4 (d).b6))
  cases i <;> unfold tripleAdditionInclusion <;> infer_instance

/-- Both output formulas now take values in precisely the same resolved smooth locus. -/
def tripleAdditionOutput (i : Bool) :
    tripleAdditionSource D data hk a c i ⟶ (U).toScheme :=
  match i with
  | true => ft
  | false => fs

/-- Both entire output domains retain the coefficient structure of the input source. -/
@[reassoc] theorem tripleAdditionOutput_structure (i : Bool) :
    tripleAdditionOutput D data hk a c i ≫ (U).ι ≫ base =
      tripleAdditionInclusion D data hk a c i ≫
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
    simp only [tripleAdditionOutput, tripleAdditionInclusion,
      Category.assoc, ht, tripleTangentGluedOutput_structure]
  | false =>
    change fs ≫ (U).ι ≫ finiteGlobalContraction hπ data k hk ≫
      WeierstrassIntegralChart.integralCurveStructure W = _
    rw [tripleSecantGluedOutput_contraction_assoc, dividedSecantToCurve_structure]
    simp only [tripleAdditionInclusion, Category.assoc, hv]

end FLT.Mazur.WeierstrassDividedDepth
