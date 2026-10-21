/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentSource
public import FLT.Mazur.WeierstrassDividedResolvedOriginalOpen

/-!
# The original-input domain of smooth tangent addition

The actual smooth tangent output transports along its localization to an open
of the unchanged input source. It then lifts to any finite resolved stage.
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
local notation "T" => DividedTangentRing W (π ^ k) d.b3 d.b4 d.b6 a c
local notation "out" => dividedTangentToCurve W (π ^ k) d.b3 d.b4 d.b6 a c
  d.factor3 d.factor4 d.factor6

/-- The genuine tangent localization inclusion into the original input source. -/
def suppliedSmoothTangentInclusion : Spec (.of T) ⟶ Spec (.of S) :=
  Spec.map (CommRingCat.ofHom (algebraMap S T))

instance suppliedSmoothTangentInclusion_open :
    IsOpenImmersion (suppliedSmoothTangentInclusion d a c) :=
  IsOpenImmersion.of_isLocalization
    (dividedTangentDenominator W (π ^ k) d.b3 d.b4 d.b6 a c)

/-- Restrict only the constructed output to the original smooth locus. -/
def suppliedSmoothTangentSmoothOpen : (Spec (.of T)).Opens := out ⁻¹ᵁ integralSmoothOpen W

local notation "V" => suppliedSmoothTangentSmoothOpen d a c

/-- The smooth-output source remains an open inside the entire input scheme. -/
def suppliedSmoothTangentSmoothInclusion : (V).toScheme ⟶ Spec (.of S) :=
  (V).ι ≫ suppliedSmoothTangentInclusion d a c

instance suppliedSmoothTangentSmoothInclusion_open :
    IsOpenImmersion (suppliedSmoothTangentSmoothInclusion d a c) := by
  unfold suppliedSmoothTangentSmoothInclusion
  infer_instance

/-- The actual tangent domain in the unchanged input scheme. -/
def suppliedSmoothTangentDomain : (Spec (.of S)).Opens :=
  (suppliedSmoothTangentSmoothInclusion d a c).opensRange

local notation "O" => suppliedSmoothTangentDomain d a c

/-- Transport the constructed original smooth output to the image open. -/
def suppliedSmoothTangentOriginalSmooth : (O).toScheme ⟶ (integralSmoothOpen W).toScheme :=
  (suppliedSmoothTangentSmoothInclusion d a c).isoOpensRange.inv ≫
    (out ∣_ integralSmoothOpen W)

/-- Image-open transport recovers the original formula on its complete smooth source. -/
@[reassoc] theorem suppliedSmoothTangentOriginalSmooth_formula :
    (suppliedSmoothTangentSmoothInclusion d a c).isoOpensRange.hom ≫
      suppliedSmoothTangentOriginalSmooth d a c ≫ (integralSmoothOpen W).ι = (V).ι ≫ out := by
  unfold suppliedSmoothTangentOriginalSmooth suppliedSmoothTangentDomain
    suppliedSmoothTangentSmoothOpen
  rw [Category.assoc, Iso.hom_inv_id_assoc, morphismRestrict_ι]

/-- The transported output has the unchanged coefficient point. -/
@[reassoc] theorem suppliedSmoothTangentOriginalSmooth_structure :
    suppliedSmoothTangentOriginalSmooth d a c ≫ (integralSmoothOpen W).ι ≫
      integralCurveStructure W = (O).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  apply (cancel_epi (suppliedSmoothTangentSmoothInclusion d a c).isoOpensRange.hom).mp
  rw [suppliedSmoothTangentOriginalSmooth_formula_assoc, dividedTangentToCurve_structure]
  unfold suppliedSmoothTangentDomain
  rw [Scheme.Hom.isoOpensRange_hom_ι_assoc]
  simp only [suppliedSmoothTangentSmoothInclusion, suppliedSmoothTangentInclusion, Category.assoc,
    ← Spec.map_comp]
  congr 2
  ext z
  exact IsScalarTower.algebraMap_apply R S T z

variable [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus

/-- Lift to the full smooth locus at any chosen finite stage. -/
def suppliedSmoothTangentResolvedAddition : (O).toScheme ⟶ (U).toScheme :=
  suppliedSmoothTangentOriginalSmooth d a c ≫ finiteOriginalToResolved hπ data j hj

/-- The actual resolved output contracts to the constructed original smooth output. -/
@[reassoc] theorem suppliedSmoothTangentResolvedAddition_contraction :
    suppliedSmoothTangentResolvedAddition d a c hπ data j hj ≫ (U).ι ≫
      finiteGlobalContraction hπ data j hj =
        suppliedSmoothTangentOriginalSmooth d a c ≫ (integralSmoothOpen W).ι := by
  rw [suppliedSmoothTangentResolvedAddition, Category.assoc,
    finiteOriginalToResolved_inclusion_assoc, finiteGlobalSmoothEmbedding_contraction]

/-- The resolved output remains over the coefficient point of its entire input domain. -/
@[reassoc] theorem suppliedSmoothTangentResolvedAddition_structure :
    suppliedSmoothTangentResolvedAddition d a c hπ data j hj ≫ (U).ι ≫ base =
      (O).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  change _ ≫ (U).ι ≫ finiteGlobalContraction hπ data j hj ≫ integralCurveStructure W = _
  rw [suppliedSmoothTangentResolvedAddition_contraction_assoc,
    suppliedSmoothTangentOriginalSmooth_structure]

end FLT.Mazur.WeierstrassDividedDepth
