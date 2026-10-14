/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearFaithfulDescent
public import FLT.Mazur.WeierstrassCoefficientShearActionTransport
public import FLT.Mazur.WeierstrassCoefficientShearTangentTransport
public import FLT.Mazur.CartesianCoefficientTransportKernelPair

/-!
# Effective nonsplit tangent descent on the actual coefficient Cech scheme

The original quadratic tangent cover is faithfully flat. Its full equation
model and action domain descend effectively; the action commutes with their
actual Cech comparisons and recovers the original integral action uniquely.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
local notation "S" => AdjoinRoot (nodeTangentPolynomial W)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial W)
local notation "q" => nodeTangentCover W
local notation "a" => pullback.fst q q
local notation "b" => pullback.snd q q
local notation "f" => integralSmoothStructure (W.map (algebraMap R S))
local notation "g" => coefficientShearGluedStructure hπ data S r j hj
local notation "p" => coefficientShearGluedProjection hπ data S r j hj
local notation "P" => coefficientShearOriginalActionProduct hπ data S r j hj
local notation "d" => pullback.fst f g ≫ f
local notation "A" => coefficientShearAction hπ data S r j hj
local notation "M" => coefficientShearTransport hπ data S r j hj a b pullback.condition
local notation "D" => coefficientShearActionDomainTransport
  hπ data S r j hj a b pullback.condition

/-- The actual tangent equation model effectively covers the original integral model. -/
theorem coefficientShearTangentProjection_effectiveEpi : EffectiveEpi p :=
  coefficientShearGluedProjection_effectiveEpi
    hπ data S r j hj (nodeTangentAlgebra_faithfullyFlat W)

/-- The actual quadratic Cech comparison presents the full integral model's kernel pair. -/
theorem coefficientShearTangentCech_isPullback :
    IsPullback (pullback.snd a g) ((M).hom ≫ pullback.snd b g) p p :=
  CartesianCoefficientTransport.cech_isPullback
    (coefficientShearGlued_isPullback hπ data S r j hj).flip

/-- Compatibility with the actual model Cech transport is sufficient for unique descent. -/
theorem coefficientShearTangentCech_existsUnique {Y : Scheme.{u}}
    (k : coefficientShearGlued hπ data S r j hj ⟶ Y)
    (hk : pullback.snd a g ≫ k = (M).hom ≫ pullback.snd b g ≫ k) :
    ∃! t : finiteGlobalModel hπ data j hj ⟶ Y, p ≫ t = k := by
  let _ := coefficientShearTangentProjection_effectiveEpi hπ data j hj
  let H := coefficientShearTangentCech_isPullback hπ data j hj
  let C := isColimitCoforkOfEffectiveEpi p H.cone H.isLimit
  have hk' : pullback.snd a g ≫ k = ((M).hom ≫ pullback.snd b g) ≫ k := by
    simpa only [Category.assoc] using hk
  exact ⟨C.desc (Cofork.ofπ k hk'), Cofork.IsColimit.π_desc C,
    fun _ ht => (cancel_epi p).mp
      (ht.trans (Cofork.IsColimit.π_desc (t := Cofork.ofπ k hk') C).symm)⟩

/-- The whole original two-input domain is effectively recovered from the tangent equations. -/
theorem coefficientShearTangentActionProduct_effectiveEpi : EffectiveEpi P :=
  coefficientShearOriginalActionProduct_effectiveEpi
    hπ data S r j hj (nodeTangentAlgebra_faithfullyFlat W)

/-- The action-domain Cech comparison is its actual integral kernel pair. -/
theorem coefficientShearTangentActionCech_isPullback :
    IsPullback (pullback.snd a d) ((D).hom ≫ pullback.snd b d) P P :=
  CartesianCoefficientTransport.cech_isPullback
    (coefficientShearActionDomain_coefficient_isPullback hπ data S r j hj)

/-- The full action intertwines the original quadratic domain and model comparisons. -/
@[reassoc] theorem coefficientShearTangentCech_action :
    (D).hom ≫ coefficientShearOverlapAction hπ data S r j hj b =
      coefficientShearOverlapAction hπ data S r j hj a ≫ (M).hom :=
  coefficientShearAction_transport hπ data S r j hj a b pullback.condition

/-- The genuine nonsplit integral action is the unique descent of the equation action. -/
theorem coefficientShearTangentAction_unique :
    ∃! t : finiteGlobalActionProduct hπ data j hj ⟶ finiteGlobalModel hπ data j hj,
      P ≫ t = A ≫ p := by
  let _ := coefficientShearTangentActionProduct_effectiveEpi hπ data j hj
  refine ⟨finiteGlobalAction hπ data j hj,
    (coefficientShearAction_projection hπ data S r j hj).symm, ?_⟩
  intro t ht
  exact (cancel_epi P).mp (ht.trans (coefficientShearAction_projection hπ data S r j hj))

end FLT.Mazur.WeierstrassDividedDepth
