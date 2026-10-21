/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSecantSource
public import FLT.Mazur.WeierstrassDividedResolvedOriginalOpen

/-!
# The original-input domain of smooth secant addition

The actual smooth secant output transports along its localization to an open
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
local notation "T" => DividedSecantRing W (π ^ k) d.b3 d.b4 d.b6 a c
local notation "out" => dividedSecantToCurve W (π ^ k) d.b3 d.b4 d.b6 a c
  d.factor3 d.factor4 d.factor6

/-- The genuine secant localization inclusion into the original input source. -/
def suppliedSmoothSecantInclusion : Spec (.of T) ⟶ Spec (.of S) :=
  Spec.map (CommRingCat.ofHom (algebraMap S T))

instance suppliedSmoothSecantInclusion_open :
    IsOpenImmersion (suppliedSmoothSecantInclusion d a c) :=
  IsOpenImmersion.of_isLocalization
    (a (x W (π ^ k) d.b3 d.b4 d.b6) - c (x W (π ^ k) d.b3 d.b4 d.b6))

/-- Restrict only the constructed output to the original smooth locus. -/
def suppliedSmoothSecantSmoothOpen : (Spec (.of T)).Opens := out ⁻¹ᵁ integralSmoothOpen W

local notation "V" => suppliedSmoothSecantSmoothOpen d a c

/-- The smooth-output source remains an open inside the entire input scheme. -/
def suppliedSmoothSecantSmoothInclusion : (V).toScheme ⟶ Spec (.of S) :=
  (V).ι ≫ suppliedSmoothSecantInclusion d a c

instance suppliedSmoothSecantSmoothInclusion_open :
    IsOpenImmersion (suppliedSmoothSecantSmoothInclusion d a c) := by
  unfold suppliedSmoothSecantSmoothInclusion
  infer_instance

/-- The actual secant domain in the unchanged input scheme. -/
def suppliedSmoothSecantDomain : (Spec (.of S)).Opens :=
  (suppliedSmoothSecantSmoothInclusion d a c).opensRange

local notation "O" => suppliedSmoothSecantDomain d a c

/-- Transport the constructed original smooth output to the image open. -/
def suppliedSmoothSecantOriginalSmooth : (O).toScheme ⟶ (integralSmoothOpen W).toScheme :=
  (suppliedSmoothSecantSmoothInclusion d a c).isoOpensRange.inv ≫
    (out ∣_ integralSmoothOpen W)

/-- Image-open transport recovers the original formula on its complete smooth source. -/
@[reassoc] theorem suppliedSmoothSecantOriginalSmooth_formula :
    (suppliedSmoothSecantSmoothInclusion d a c).isoOpensRange.hom ≫
      suppliedSmoothSecantOriginalSmooth d a c ≫ (integralSmoothOpen W).ι = (V).ι ≫ out := by
  unfold suppliedSmoothSecantOriginalSmooth suppliedSmoothSecantDomain
    suppliedSmoothSecantSmoothOpen
  rw [Category.assoc, Iso.hom_inv_id_assoc, morphismRestrict_ι]

/-- The transported output has the unchanged coefficient point. -/
@[reassoc] theorem suppliedSmoothSecantOriginalSmooth_structure :
    suppliedSmoothSecantOriginalSmooth d a c ≫ (integralSmoothOpen W).ι ≫
      integralCurveStructure W = (O).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  apply (cancel_epi (suppliedSmoothSecantSmoothInclusion d a c).isoOpensRange.hom).mp
  rw [suppliedSmoothSecantOriginalSmooth_formula_assoc, dividedSecantToCurve_structure]
  unfold suppliedSmoothSecantDomain
  rw [Scheme.Hom.isoOpensRange_hom_ι_assoc]
  simp only [suppliedSmoothSecantSmoothInclusion, suppliedSmoothSecantInclusion, Category.assoc,
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
def suppliedSmoothSecantResolvedAddition : (O).toScheme ⟶ (U).toScheme :=
  suppliedSmoothSecantOriginalSmooth d a c ≫ finiteOriginalToResolved hπ data j hj

/-- The actual resolved output contracts to the constructed original smooth output. -/
@[reassoc] theorem suppliedSmoothSecantResolvedAddition_contraction :
    suppliedSmoothSecantResolvedAddition d a c hπ data j hj ≫ (U).ι ≫
      finiteGlobalContraction hπ data j hj =
        suppliedSmoothSecantOriginalSmooth d a c ≫ (integralSmoothOpen W).ι := by
  rw [suppliedSmoothSecantResolvedAddition, Category.assoc,
    finiteOriginalToResolved_inclusion_assoc, finiteGlobalSmoothEmbedding_contraction]

/-- The resolved output remains over the coefficient point of its entire input domain. -/
@[reassoc] theorem suppliedSmoothSecantResolvedAddition_structure :
    suppliedSmoothSecantResolvedAddition d a c hπ data j hj ≫ (U).ι ≫ base =
      (O).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  change _ ≫ (U).ι ≫ finiteGlobalContraction hπ data j hj ≫ integralCurveStructure W = _
  rw [suppliedSmoothSecantResolvedAddition_contraction_assoc,
    suppliedSmoothSecantOriginalSmooth_structure]

end FLT.Mazur.WeierstrassDividedDepth
