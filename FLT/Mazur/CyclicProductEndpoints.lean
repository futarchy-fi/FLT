/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicProductNormalization
public import FLT.Mazur.RelativePinchingDescent
/-!
# Endpoints of the base-changed cyclic normalization

The origins of the two affine branches are the pulled-back zero and infinity
sections on adjacent components. Their relation gives unique node descent.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Polynomial
universe u
namespace FLT.Mazur.CyclicProductEndpoints
open CyclicProductNormalization PolygonCyclicNormalizationPullback PinchingChartBaseChange
variable (K S : Type u) [Field K] [CommRing S] [Algebra K S]
variable (n : ℕ) (hn : 2 ≤ n)
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- One of the two polynomial branches of the normalization. -/
def branch (R : Type u) [CommRing R] (b : Bool) :
    Spec (.of R[X]) ⟶ Spec (.of (R[X] × R[X])) :=
  Spec.map (CommRingCat.ofHom (if b then RingHom.snd R[X] R[X] else RingHom.fst R[X] R[X]))

/-- The selected affine branch in the base-changed normalization. -/
def branchLift (j : Fin n) (b : Bool) :
    Spec (.of S[X]) ⟶ componentsProduct K S n :=
  branch S b ≫ affineNormalizationLift K S n hn j

/-- Zero or the adjacent infinity in the normalization coproduct. -/
def originalEndpoint (j : Fin n) (b : Bool) :
    Spec (.of K) ⟶ components K n :=
  if b then ProjectiveLine.infinity K ≫ Sigma.ι (fun _ : Fin n ↦ ProjectiveLine.scheme K)
    (finRotate n j)
  else ProjectiveLine.zero K ≫ Sigma.ι (fun _ : Fin n ↦ ProjectiveLine.scheme K) j

@[reassoc (attr := simp)] theorem originalEndpoint_toBase (j : Fin n) (b : Bool) :
    originalEndpoint K n j b ≫ componentsBase K n = 𝟙 _ := by
  cases b <;> simp [originalEndpoint, componentsBase]

/-- The actual endpoint section after parameter base change. -/
def endpoint (j : Fin n) (b : Bool) : Spec (.of S) ⟶ componentsProduct K S n :=
  pullback.lift (𝟙 _) (parameter K S ≫ originalEndpoint K n j b) (by simp)

@[reassoc (attr := simp)] theorem endpoint_fst (j : Fin n) (b : Bool) :
    endpoint K S n j b ≫ pullback.fst _ _ = 𝟙 _ := by simp [endpoint]
@[reassoc (attr := simp)] theorem endpoint_snd (j : Fin n) (b : Bool) :
    endpoint K S n j b ≫ pullback.snd _ _ = parameter K S ≫ originalEndpoint K n j b := by
  simp [endpoint]

theorem branch_coeff (b : Bool) :
    branch S b ≫ Spec.map (CommRingCat.ofHom (NodeNormalizationBaseChange.coeff K S)) =
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap K S))) ≫ branch K b := by
  cases b <;> rw [branch, branch, ← Spec.map_comp, ← Spec.map_comp] <;> rfl

@[reassoc] theorem zero_branch_affineLift (j : Fin n) (b : Bool) :
    ProjectiveLine.chartZero K ≫ branch K b ≫ affineLift K n hn j =
      originalEndpoint K n j b := by
  cases b
  · have he : branch K false = coprod.inl ≫ coprodSpec K[X] K[X] :=
      (coprodSpec_inl K[X] K[X]).symm
    rw [he, affineLift]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    simp [chartLift, firstLift, originalEndpoint, ProjectiveLine.zero]
  · have he : branch K true = coprod.inr ≫ coprodSpec K[X] K[X] :=
      (coprodSpec_inr K[X] K[X]).symm
    rw [he, affineLift]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    simp [chartLift, secondLift, originalEndpoint, ProjectiveLine.infinity]

@[reassoc] theorem zero_branchLift (j : Fin n) (b : Bool) :
    Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom 0)) ≫ branchLift K S n hn j b =
      endpoint K S n j b := by
  apply pullback.hom_ext
  · simp only [branchLift, Category.assoc, affineNormalizationLift_fst, endpoint_fst]
    rw [branch, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_id]
    congr 1
    cases b <;> ext <;> simp
  · simp only [branchLift, Category.assoc, affineNormalizationLift_snd, endpoint_snd]
    rw [← Category.assoc (branch S b), branch_coeff, Category.assoc,
      ← Category.assoc]
    have hc : Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : S))) ≫
        Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap K S))) =
        parameter K S ≫ ProjectiveLine.chartZero K := by
      rw [parameter, ProjectiveLine.chartZero, ← Spec.map_comp, ← Spec.map_comp]
      congr 1
      apply CommRingCat.hom_ext
      apply Polynomial.ringHom_ext <;> simp
    rw [hc, Category.assoc, zero_branch_affineLift]

theorem node_desc {Y : Scheme.{u}} (h : componentsProduct K S n ⟶ Y)
    (j : Fin n) (w : endpoint K S n j false ≫ h = endpoint K S n j true ≫ h) :
    ∃! d : PolygonNodeBranches.node S ⟶ Y,
      NodeNormalizationBaseChange.normalization S ≫ d = affineNormalizationLift K S n hn j ≫ h := by
  apply RelativePinchingDescent.node_product_desc
  have h0 := zero_branchLift K S n hn j false
  have h1 := zero_branchLift K S n hn j true
  rw [← h0, ← h1] at w
  simpa only [branchLift, branch, Bool.false_eq_true, ↓reduceIte,
    ← Category.assoc, ← Spec.map_comp, RelativePinchingLocalDescent.nodeFirst,
    RelativePinchingLocalDescent.nodeSecond, CommRingCat.ofHom_comp] using w
end FLT.Mazur.CyclicProductEndpoints
