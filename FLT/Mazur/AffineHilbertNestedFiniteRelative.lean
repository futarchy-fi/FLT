/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertNestedFiniteEtale

/-!
# Relative scheme comparison of the actual nested effective region

The constructed isomorphism retains the original ground-base morphism and
both old and freshly recomputed coefficient maps. This is an isomorphism in
schemes over the original base, including all structure-sheaf maps.
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
local instance nestedRelativeChartOpen : IsOpenImmersion (v ≫ k).left :=
  inferInstanceAs (IsOpenImmersion (v.left ≫ k.left))
local notation "w" => v.left ≫ Over.Hom.left (finiteKernelProjection f hL d V c k)
local notation "j" => nestedFiniteProjection f hL d V c k v
local notation "r₀" => nestedFiniteToOld f hL d V c k v
local notation "r₁" => nestedFiniteToNew f hL d V c k v
local notation "hj" => nestedFiniteProjection_condition f hL d V c k v
local notation "hr" => nestedFiniteProjection_toOld f hL d V c k v
attribute [local irreducible] finiteKernelProjection finiteKernelModel
  nestedFiniteProjection nestedFiniteTarget nestedFiniteToOld nestedFiniteToNew
variable [Etale (v.left ≫ (finiteKernelProjection f hL d V c k).left)]

/-- The original quotient open as a scheme over the original coefficient ground base. -/
def nestedFiniteImageOver : Over (Spec (.of R)) :=
  Over.mk ((SchemeEtaleImageQuotient.image w).ι ≫ (finiteKernelModel f hL d V c k).hom)

/-- The actual joint effective open retains its constructed original ground-base map. -/
def nestedFiniteEffectiveOver : Over (Spec (.of R)) :=
  Over.mk ((SchemeFppfTargetOpen.locus j).ι ≫ (nestedFiniteOver f hL d V c k v).hom)

variable (H : IsPullback (fst f hL d V c (v ≫ k)).left (snd f hL d V c (v ≫ k)).left
  (v.left ≫ (finiteKernelProjection f hL d V c k).left)
  (v.left ≫ (finiteKernelProjection f hL d V c k).left))

/-- The effective-region comparison is an actual relative scheme isomorphism. -/
def nestedFiniteRelativeEffectiveIso : nestedFiniteImageOver f hL d V c k v ≅
    nestedFiniteEffectiveOver f hL d V c k v :=
  Over.isoMk (nestedFiniteEffectiveIso f hL d V c k v H) (by
    change (nestedFiniteEffectiveIso f hL d V c k v H).hom ≫
      (SchemeFppfTargetOpen.locus j).ι ≫
        (r₁ ≫ (finiteKernelModel f hL d V c (v ≫ k)).hom) = _
    rw [← nestedFinite_base_condition]
    simpa only [Category.assoc, nestedFiniteEffectiveIso, nestedFiniteImageOver,
      Over.mk_hom] using congrArg
      (fun g ↦ g ≫ (finiteKernelModel f hL d V c k).hom)
      (SchemeEtaleImageDenseModel.effectiveIso_toOld w H j hj r₀ hr))

/-- The relative comparison retains the entire original joint scheme morphism. -/
@[reassoc]
theorem nestedFiniteRelativeEffectiveIso_ι :
    (nestedFiniteRelativeEffectiveIso f hL d V c k v H).hom.left ≫
      (SchemeFppfTargetOpen.locus j).ι = nestedFiniteImageComparison f hL d V c k v H :=
by
  change (SchemeEtaleImageDenseModel.effectiveIso w H j hj r₀ hr).hom ≫ _ =
    SchemeEtaleImageDenseModel.comparison w H j hj
  exact SchemeEtaleImageDenseModel.effectiveIso_ι w H j hj r₀ hr

/-- Fresh coefficients remain the actual scheme map through the relative isomorphism. -/
@[reassoc]
theorem nestedFiniteRelativeEffectiveIso_toNew :
    (nestedFiniteRelativeEffectiveIso f hL d V c k v H).hom.left ≫
      (SchemeFppfTargetOpen.locus j).ι ≫ r₁ =
        nestedFiniteImageComparison f hL d V c k v H ≫ r₁ := by
  rw [nestedFiniteRelativeEffectiveIso_ι_assoc]

end FLT.Mazur.HilbertChart.AffineRestriction
