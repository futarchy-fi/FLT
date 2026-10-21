/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedReciprocalOutput
public import FLT.Mazur.WeierstrassDividedResolvedSecant

/-!
# Reciprocal smooth outputs over arbitrary divided inputs

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
local notation "T" => DividedReciprocalRing W (π ^ k) d.b3 d.b4 d.b6 a c
local notation "B" => DividedReciprocalOutputRing W (π ^ k) d.b3 d.b4 d.b6 a c
local notation "v" => dividedReciprocalCoordinates W (π ^ k) d.b3 d.b4 d.b6 a c
local notation "out" => dividedReciprocalToCurve W (π ^ k) d.b3 d.b4 d.b6 a c
  d.factor3 d.factor4 d.factor6

/-- The two genuine localization inclusions into the original source. -/
def suppliedReciprocalInclusion : Spec (.of B) ⟶ Spec (.of S) :=
  Spec.map (CommRingCat.ofHom (algebraMap T B)) ≫
    Spec.map (CommRingCat.ofHom (algebraMap S T))

instance suppliedReciprocalInclusion_open :
    IsOpenImmersion (suppliedReciprocalInclusion d a c) := by
  let _ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap T B))) :=
    IsOpenImmersion.of_isLocalization (v 1)
  let _ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap S T))) :=
    IsOpenImmersion.of_isLocalization
      (a (y W (π ^ k) d.b3 d.b4 d.b6) - c (y W (π ^ k) d.b3 d.b4 d.b6))
  unfold suppliedReciprocalInclusion
  infer_instance

/-- Restrict only the constructed output to the original smooth locus. -/
def suppliedReciprocalSmoothOpen : (Spec (.of B)).Opens := out ⁻¹ᵁ integralSmoothOpen W

local notation "V" => suppliedReciprocalSmoothOpen d a c

/-- The smooth-output source remains an open inside the entire input scheme. -/
def suppliedReciprocalSmoothInclusion : (V).toScheme ⟶ Spec (.of S) :=
  (V).ι ≫ suppliedReciprocalInclusion d a c

instance suppliedReciprocalSmoothInclusion_open :
    IsOpenImmersion (suppliedReciprocalSmoothInclusion d a c) := by
  unfold suppliedReciprocalSmoothInclusion
  infer_instance

/-- The actual reciprocal domain in the unchanged input scheme. -/
def suppliedReciprocalDomain : (Spec (.of S)).Opens :=
  (suppliedReciprocalSmoothInclusion d a c).opensRange

local notation "O" => suppliedReciprocalDomain d a c

/-- Transport the constructed original smooth output to the image open. -/
def suppliedReciprocalOriginalSmooth : (O).toScheme ⟶ (integralSmoothOpen W).toScheme :=
  (suppliedReciprocalSmoothInclusion d a c).isoOpensRange.inv ≫
    (out ∣_ integralSmoothOpen W)

/-- Image-open transport recovers the original formula on its complete smooth source. -/
@[reassoc] theorem suppliedReciprocalOriginalSmooth_formula :
    (suppliedReciprocalSmoothInclusion d a c).isoOpensRange.hom ≫
      suppliedReciprocalOriginalSmooth d a c ≫ (integralSmoothOpen W).ι = (V).ι ≫ out := by
  unfold suppliedReciprocalOriginalSmooth suppliedReciprocalDomain
    suppliedReciprocalSmoothOpen
  rw [Category.assoc, Iso.hom_inv_id_assoc, morphismRestrict_ι]

/-- The transported output has the unchanged coefficient point. -/
@[reassoc] theorem suppliedReciprocalOriginalSmooth_structure :
    suppliedReciprocalOriginalSmooth d a c ≫ (integralSmoothOpen W).ι ≫
      integralCurveStructure W = (O).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  apply (cancel_epi (suppliedReciprocalSmoothInclusion d a c).isoOpensRange.hom).mp
  rw [suppliedReciprocalOriginalSmooth_formula_assoc, dividedReciprocalToCurve_structure]
  unfold suppliedReciprocalDomain
  rw [Scheme.Hom.isoOpensRange_hom_ι_assoc]
  simp only [suppliedReciprocalSmoothInclusion, suppliedReciprocalInclusion, Category.assoc,
    ← Spec.map_comp]
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
def suppliedReciprocalResolvedAddition : (O).toScheme ⟶ (U).toScheme :=
  suppliedReciprocalOriginalSmooth d a c ≫ finiteOriginalToResolved hπ data j hj

/-- The actual resolved output contracts to the constructed original smooth output. -/
@[reassoc] theorem suppliedReciprocalResolvedAddition_contraction :
    suppliedReciprocalResolvedAddition d a c hπ data j hj ≫ (U).ι ≫
      finiteGlobalContraction hπ data j hj =
        suppliedReciprocalOriginalSmooth d a c ≫ (integralSmoothOpen W).ι := by
  rw [suppliedReciprocalResolvedAddition, Category.assoc,
    finiteOriginalToResolved_inclusion_assoc, finiteGlobalSmoothEmbedding_contraction]

/-- The resolved output remains over the coefficient point of its entire input domain. -/
@[reassoc] theorem suppliedReciprocalResolvedAddition_structure :
    suppliedReciprocalResolvedAddition d a c hπ data j hj ≫ (U).ι ≫ base =
      (O).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  change _ ≫ (U).ι ≫ finiteGlobalContraction hπ data j hj ≫ integralCurveStructure W = _
  rw [suppliedReciprocalResolvedAddition_contraction_assoc,
    suppliedReciprocalOriginalSmooth_structure]

end FLT.Mazur.WeierstrassDividedDepth
