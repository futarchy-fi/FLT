/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalTensorEmbedding
public import FLT.Mazur.WeierstrassDividedAdjacentRetainedTensor
public import FLT.Mazur.WeierstrassModificationAffineContraction
public import FLT.Mazur.ProjectiveLineAffineRigidity

/-!
# Complete local projective components have constant original cubic contraction

The actual finite local modification contracts through the original affine
cubic. Global functions on a projective line are constant, so every complete
component factoring through that local modification contracts to its endpoint
value. This applies before any choice of nodal tangent coordinates.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (j : ℕ) (hj : j ≤ n)
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))

/-- The entire finite local iteration contracts to the original affine cubic chart. -/
def finiteToOriginalAffine : finiteModification hπ data j hj ⟶ chartScheme W 2 :=
  finiteContraction hπ data (initialExterior d) j hj ≫ (initialExteriorIso d).hom ≫
    WeierstrassModificationX.affineContraction W (π ^ (start + 0))
      (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d)

/-- The affine factorization retains exactly the original finite cubic contraction. -/
@[reassoc] theorem finiteToOriginalAffine_toCurve :
    finiteToOriginalAffine hπ data j hj ≫ integralCurveChart W 2 =
      finiteToCurve hπ data j hj := by
  simp only [finiteToOriginalAffine, finiteToCurve, initialToCurve, Category.assoc,
    WeierstrassModificationX.affineContraction_toCurve]

variable [IsBezout R] (K : Type u) [Field K] [Algebra R K]
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))
local notation "f" => finiteGlobalStructure hπ data j hj
local notation "g" => finiteGlobalContraction hπ data j hj
local notation "e" => finiteLocalTensorEmbedding hπ data K j hj

/-- Equality of stage indices retains the entire original cubic contraction. -/
@[reassoc] theorem finiteGlobalTensorModel_cubic_transport {a b : ℕ}
    (ha : a ≤ n) (hb : b ≤ n) (h : a = b) :
    eqToHom (finiteGlobalTensorModel_index_congr hπ data K ha hb h) ≫
        pullback.snd q (finiteGlobalStructure hπ data b hb) ≫
          finiteGlobalContraction hπ data b hb =
      pullback.snd q (finiteGlobalStructure hπ data a ha) ≫
        finiteGlobalContraction hπ data a ha := by
  subst b
  simp only [eqToHom_refl, Category.id_comp]

/-- A whole projective component in the local modification has constant original contraction. -/
theorem localProjectiveComponent_contraction_constant
    (a : ProjectiveLine.scheme K ⟶ finiteTensorModel hπ data K j hj) :
    a ≫ e ≫ pullback.snd q f ≫ g =
      ProjectiveLine.toBase K ≫ ProjectiveLine.zero K ≫
        a ≫ e ≫ pullback.snd q f ≫ g := by
  simp only [finiteLocalTensorEmbedding_toCurve]
  rw [← finiteToOriginalAffine_toCurve hπ data j hj]
  have H := ProjectiveLineAffineRigidity.comp_eq_constant K
    (a ≫ pullback.snd q (finiteStructure hπ data j hj) ≫
      finiteToOriginalAffine hπ data j hj) (integralCurveChart W 2)
  simpa only [Category.assoc] using H

/-- Its two original projective endpoints have equal original cubic images. -/
theorem localProjectiveComponent_contraction_endpoints
    (a : ProjectiveLine.scheme K ⟶ finiteTensorModel hπ data K j hj) :
    ProjectiveLine.zero K ≫ a ≫ e ≫ pullback.snd q f ≫ g =
      ProjectiveLine.infinity K ≫ a ≫ e ≫ pullback.snd q f ≫ g := by
  conv_rhs => rw [localProjectiveComponent_contraction_constant]
  rw [ProjectiveLine.infinity_toBase_assoc]

/-- Containment in the actual local open suffices for constancy of the original contraction. -/
theorem projectiveComponent_contraction_constant_of_range
    (a : ProjectiveLine.scheme K ⟶ finiteGlobalTensorModel hπ data K j hj)
    (ha : Set.range a ⊆ Set.range e) :
    a ≫ pullback.snd q f ≫ g =
      ProjectiveLine.toBase K ≫ ProjectiveLine.zero K ≫ a ≫ pullback.snd q f ≫ g := by
  let b := IsOpenImmersion.lift e a ha
  have hb : b ≫ e = a := IsOpenImmersion.lift_fac _ _ _
  have H := localProjectiveComponent_contraction_constant hπ data j hj K b
  simpa only [← Category.assoc, hb] using H

end FLT.Mazur.WeierstrassDividedDepth
