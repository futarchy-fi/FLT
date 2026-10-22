/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedReciprocalChordOutput
public import FLT.Mazur.WeierstrassDividedResolvedSecant

/-!
# ReciprocalChord smooth outputs over arbitrary divided inputs

The image of the two localizations and the original smooth-output restriction
is an actual open of the unchanged input scheme. Its constructed output lifts
to any finite resolved stage, independently of the divided input depth.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation WeierstrassIntegralChart
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  {W : WeierstrassCurve R} {π : R} {k : ℕ} (d : Data W π k)
  (a c : WeierstrassDilatation.Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "T" => DividedReciprocalChordRing W (π ^ k) d.b3 d.b4 d.b6 a c
local notation "B" => DividedReciprocalChordOutputRing W (π ^ k) d.b3 d.b4 d.b6 a c
local notation "v" => dividedReciprocalChordCoordinates W (π ^ k) d.b3 d.b4 d.b6 a c
local notation "out" => dividedReciprocalChordToCurve W (π ^ k) d.b3 d.b4 d.b6 a c
  d.factor3 d.factor4 d.factor6

/-- The two genuine localization inclusions into the original source. -/
def suppliedReciprocalChordInclusion : Spec (.of B) ⟶ Spec (.of S) :=
  Spec.map (CommRingCat.ofHom (algebraMap T B)) ≫
    Spec.map (CommRingCat.ofHom (algebraMap S T))

instance suppliedReciprocalChordInclusion_open :
    IsOpenImmersion (suppliedReciprocalChordInclusion d a c) := by
  let _ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap T B))) :=
    IsOpenImmersion.of_isLocalization (v 1)
  let _ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap S T))) :=
    IsOpenImmersion.of_isLocalization
      (dividedTangentNumerator W (π ^ k) d.b3 d.b4 d.b6 a c)
  unfold suppliedReciprocalChordInclusion
  infer_instance

/-- Restrict only the constructed output to the original smooth locus. -/
def suppliedReciprocalChordSmoothOpen : (Spec (.of B)).Opens := out ⁻¹ᵁ integralSmoothOpen W

local notation "V" => suppliedReciprocalChordSmoothOpen d a c

/-- The smooth-output source remains an open inside the entire input scheme. -/
def suppliedReciprocalChordSmoothInclusion : (V).toScheme ⟶ Spec (.of S) :=
  (V).ι ≫ suppliedReciprocalChordInclusion d a c

instance suppliedReciprocalChordSmoothInclusion_open :
    IsOpenImmersion (suppliedReciprocalChordSmoothInclusion d a c) := by
  unfold suppliedReciprocalChordSmoothInclusion
  infer_instance

/-- The actual reciprocal chord domain in the unchanged input scheme. -/
def suppliedReciprocalChordDomain : (Spec (.of S)).Opens :=
  (suppliedReciprocalChordSmoothInclusion d a c).opensRange

local notation "O" => suppliedReciprocalChordDomain d a c

/-- Transport the constructed original smooth output to the image open. -/
def suppliedReciprocalChordOriginalSmooth : (O).toScheme ⟶ (integralSmoothOpen W).toScheme :=
  (suppliedReciprocalChordSmoothInclusion d a c).isoOpensRange.inv ≫
    (out ∣_ integralSmoothOpen W)

/-- Image-open transport recovers the original formula on its complete smooth source. -/
@[reassoc] theorem suppliedReciprocalChordOriginalSmooth_formula :
    (suppliedReciprocalChordSmoothInclusion d a c).isoOpensRange.hom ≫
      suppliedReciprocalChordOriginalSmooth d a c ≫ (integralSmoothOpen W).ι = (V).ι ≫ out := by
  unfold suppliedReciprocalChordOriginalSmooth suppliedReciprocalChordDomain
    suppliedReciprocalChordSmoothOpen
  rw [Category.assoc, Iso.hom_inv_id_assoc, morphismRestrict_ι]

/-- The transported output has the unchanged coefficient point. -/
@[reassoc] theorem suppliedReciprocalChordOriginalSmooth_structure :
    suppliedReciprocalChordOriginalSmooth d a c ≫ (integralSmoothOpen W).ι ≫
      integralCurveStructure W = (O).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  apply (cancel_epi (suppliedReciprocalChordSmoothInclusion d a c).isoOpensRange.hom).mp
  rw [suppliedReciprocalChordOriginalSmooth_formula_assoc, dividedReciprocalChordToCurve_structure]
  unfold suppliedReciprocalChordDomain
  rw [Scheme.Hom.isoOpensRange_hom_ι_assoc]
  simp only [suppliedReciprocalChordSmoothInclusion, suppliedReciprocalChordInclusion,
    Category.assoc, ← Spec.map_comp]
  congr 2
  ext z
  exact (IsScalarTower.algebraMap_apply R T B z).symm.trans
    (congrArg (algebraMap T B) (IsScalarTower.algebraMap_apply R S T z))

variable [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus

/-- Lift to the full smooth locus at any chosen finite stage. -/
def suppliedReciprocalChordResolvedAddition : (O).toScheme ⟶ (U).toScheme :=
  suppliedReciprocalChordOriginalSmooth d a c ≫ finiteOriginalToResolved hπ data j hj

/-- The actual resolved output contracts to the constructed original smooth output. -/
@[reassoc] theorem suppliedReciprocalChordResolvedAddition_contraction :
    suppliedReciprocalChordResolvedAddition d a c hπ data j hj ≫ (U).ι ≫
      finiteGlobalContraction hπ data j hj =
        suppliedReciprocalChordOriginalSmooth d a c ≫ (integralSmoothOpen W).ι := by
  rw [suppliedReciprocalChordResolvedAddition, Category.assoc,
    finiteOriginalToResolved_inclusion_assoc, finiteGlobalSmoothEmbedding_contraction]

/-- The resolved output remains over the coefficient point of its entire input domain. -/
@[reassoc] theorem suppliedReciprocalChordResolvedAddition_structure :
    suppliedReciprocalChordResolvedAddition d a c hπ data j hj ≫ (U).ι ≫ base =
      (O).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  change _ ≫ (U).ι ≫ finiteGlobalContraction hπ data j hj ≫ integralCurveStructure W = _
  rw [suppliedReciprocalChordResolvedAddition_contraction_assoc,
    suppliedReciprocalChordOriginalSmooth_structure]

end FLT.Mazur.WeierstrassDividedDepth
