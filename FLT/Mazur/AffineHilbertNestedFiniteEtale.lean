/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertNestedFiniteKernel
public import FLT.Mazur.SchemeRelationJointModelEtaleImage

/-!
# Actual effective regions of recomputed nested finite Hilbert models

An etale old coefficient map with the full recomputed Picard kernel constructs
an etale joint finite projection and a scheme isomorphism from its old quotient
onto its actual fppf region. Both finite coefficient systems are retained.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
attribute [local irreducible] relation fst snd
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
  {B : Over (Spec (.of R))} [IsAffine B.left] (v : B ⟶ A) [IsOpenImmersion v.left]
local notation "p" => Over.Hom.left (fst f hL d V c (v ≫ k))
local notation "q" => Over.Hom.left (snd f hL d V c (v ≫ k))
local instance nestedEtaleChartOpen : IsOpenImmersion (v ≫ k).left :=
  inferInstanceAs (IsOpenImmersion (v.left ≫ k.left))
/-- The recomputed full invariants carry their unchanged original ground-base algebra. -/
local instance nestedEtaleInvariantAlgebra : Algebra R
    (SchemeEffectiveEpiSections.compatibleFunctions p q) :=
  (invariantCoefficientBase f hL d V c (v ≫ k)).toAlgebra
local notation "w₀" => Over.Hom.left (finiteKernelProjection f hL d V c k)

local notation "w" => v.left ≫ w₀
local notation "j" => nestedFiniteProjection f hL d V c k v
local notation "r" => nestedFiniteToOld f hL d V c k v
local notation "α" => nestedOldFiniteCoefficients f hL d V c k v
local notation "β" => AlgHom.toRingHom
  (Subalgebra.val (finiteKernelCoefficientAlgebra f hL d V c (v ≫ k)))

instance nestedFiniteProjection_schematicallyDominant :
    IsSchemeTheoreticallyDominant (nestedFiniteProjection f hL d V c k v) :=
  SchemeRelationJointModel.projection_schematicallyDominant p q α β

instance nestedFiniteProjection_quasiCompact :
    QuasiCompact (nestedFiniteProjection f hL d V c k v) := by infer_instance

instance nestedFiniteProjection_locallyOfFiniteType :
    LocallyOfFiniteType (nestedFiniteProjection f hL d V c k v) := by
  have : LocallyOfFiniteType (j ≫ nestedFiniteToNew f hL d V c k v) := by
    rw [nestedFiniteProjection_toNew]
    infer_instance
  exact locallyOfFiniteType_of_comp j (nestedFiniteToNew f hL d V c k v)

instance nestedFiniteProjection_locallyOfFinitePresentation :
    LocallyOfFinitePresentation (nestedFiniteProjection f hL d V c k v) := by infer_instance

attribute [local irreducible] finiteKernelProjection finiteKernelModel
  nestedFiniteProjection nestedFiniteTarget nestedFiniteToOld nestedFiniteToNew

variable [Etale (v.left ≫ (finiteKernelProjection f hL d V c k).left)]
  (H : IsPullback (fst f hL d V c (v ≫ k)).left (snd f hL d V c (v ≫ k)).left
    (v.left ≫ (finiteKernelProjection f hL d V c k).left)
    (v.left ≫ (finiteKernelProjection f hL d V c k).left))

include H in
/-- The actual recomputed joint projection is etale on the entire selected source. -/
theorem nestedFiniteProjection_etale : Etale (nestedFiniteProjection f hL d V c k v) :=
  SchemeEtaleImageDenseModel.projection_etale w H j
    (nestedFiniteProjection_condition f hL d V c k v) r
    (nestedFiniteProjection_toOld f hL d V c k v)

/-- The effective old coefficient image maps into the actual recomputed joint scheme. -/
def nestedFiniteImageComparison : (SchemeEtaleImageQuotient.image w).toScheme ⟶
    nestedFiniteTarget f hL d V c k v :=
  SchemeEtaleImageDenseModel.comparison w H j (nestedFiniteProjection_condition f hL d V c k v)

/-- The comparison is an open immersion with nilpotents retained. -/
instance nestedFiniteImageComparison_isOpenImmersion :
    IsOpenImmersion (nestedFiniteImageComparison f hL d V c k v H) :=
  SchemeEtaleImageDenseModel.comparison_isOpenImmersion w H j
    (nestedFiniteProjection_condition f hL d V c k v) r
    (nestedFiniteProjection_toOld f hL d V c k v)

/-- Both the original and freshly recomputed coefficients survive descent on the entire source. -/
theorem nestedFiniteImageComparison_coefficients :
    SchemeEtaleImageQuotient.projection w ≫ nestedFiniteImageComparison f hL d V c k v H ≫
      nestedFiniteToOld f hL d V c k v = w ∧
    SchemeEtaleImageQuotient.projection w ≫ nestedFiniteImageComparison f hL d V c k v H ≫
      nestedFiniteToNew f hL d V c k v =
        (finiteKernelProjection f hL d V c (v ≫ k)).left := by
  have he := SchemeEtaleImageDenseModel.projection_comparison w H j
    (nestedFiniteProjection_condition f hL d V c k v)
  constructor
  · change _ ≫ SchemeEtaleImageDenseModel.comparison w H j _ ≫ _ = _
    rw [← Category.assoc, he, nestedFiniteProjection_toOld]
  · change _ ≫ SchemeEtaleImageDenseModel.comparison w H j _ ≫ _ = _
    rw [← Category.assoc, he, nestedFiniteProjection_toNew]

/-- The actual joint effective region is isomorphic to the constructed old quotient open. -/
def nestedFiniteEffectiveIso : (SchemeEtaleImageQuotient.image w).toScheme ≅
    (SchemeFppfTargetOpen.locus j).toScheme :=
  SchemeEtaleImageDenseModel.effectiveIso w H j
    (nestedFiniteProjection_condition f hL d V c k v) r
    (nestedFiniteProjection_toOld f hL d V c k v)

end FLT.Mazur.HilbertChart.AffineRestriction
