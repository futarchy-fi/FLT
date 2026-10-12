/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertTensorMatchingRing

/-!
# Pullback and counit on glued literal tensor coefficients

Matching localization families can be evaluated along every actual scheme
morphism into the full relation. On a chart this is the earlier literal local
evaluation. The original identity gives a global counit for both endpoint maps.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TensorProduct
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve Approximation AffineProductTensorCoordinates
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left] (k : A ⟶ variableHilbertTest f d V)
  [IsOpenImmersion k.left]
local notation "Z" => relation f hL d V c k
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
/-- The algebra induced by the original source structural morphism. -/
local instance pullbackSourceAlgebra : Algebra R Γ(A.left, ⊤) :=
  affineBaseSectionAlgebra A.hom
/-- The algebra induced by the original translation structural morphism. -/
local instance pullbackTranslationAlgebra : Algebra R Γ(V.left, ⊤) :=
  affineBaseSectionAlgebra V.hom


namespace TensorChart

/-- Evaluate a glued localization family along any actual map into the original relation. -/
def matchingPullback {B : Scheme} (g : B ⟶ (Z).left) :
    matchingRing f hL d V c k →+* Γ(B, ⊤) :=
  g.appTop.hom.comp (globalEquiv f hL d V c k).symm.toRingHom

/-- Evaluation of original global functions is their original geometric pullback. -/
theorem matchingPullback_toMatching {B : Scheme} (g : B ⟶ (Z).left)
    (a : Γ((Z).left, ⊤)) :
    matchingPullback f hL d V c k g (toMatching f hL d V c k a) = g.appTop a := by
  change g.appTop ((globalEquiv f hL d V c k).symm (globalEquiv f hL d V c k a)) = _
  rw [RingEquiv.symm_apply_apply]

/-- Reconstructing a matching family preserves each of its literal localization coefficients. -/
theorem globalMap_reconstruction (z : matchingRing f hL d V c k)
    (T : TensorChart f hL d V c k) :
    globalMap f hL d V c k T ((globalEquiv f hL d V c k).symm z) = z.val T :=
  congrArg (fun w : matchingRing f hL d V c k ↦ w.val T)
    ((globalEquiv f hL d V c k).apply_symm_apply z)

/-- Glued evaluation agrees with the literal local evaluation on every original chart. -/
theorem matchingPullback_local (T : TensorChart f hL d V c k)
    {B : Scheme} (g : B ⟶ T.domain.toScheme) (z : matchingRing f hL d V c k) :
    matchingPullback f hL d V c k (g ≫ T.domain.ι) z =
      localizedEvaluation f hL d V c k T.denominator T.domain T.image_eq g (z.val T) := by
  rw [← globalMap_reconstruction f hL d V c k z T]
  change g.appTop (T.domain.ι.appTop _) =
    g.appTop ((sectionsIso f hL d V c k T).inv ((sectionsIso f hL d V c k T).hom _))
  rw [Iso.hom_inv_id_apply]
  rfl

/-- Glued evaluation is functorial in arbitrary original scheme test morphisms. -/
theorem matchingPullback_comp {B C : Scheme} (g : B ⟶ (Z).left) (h : C ⟶ B) :
    matchingPullback f hL d V c k (h ≫ g) =
      h.appTop.hom.comp (matchingPullback f hL d V c k g) := rfl

/-- The first matching endpoint always evaluates to the actual first endpoint. -/
theorem matchingPullback_source {B : Scheme} (g : B ⟶ (Z).left) (a : Γ(A.left, ⊤)) :
    matchingPullback f hL d V c k g (matchingSource f hL d V c k a) =
      (g ≫ (p).left).appTop a :=
  matchingPullback_toMatching f hL d V c k g ((p).left.appTop a)

/-- The second matching endpoint always evaluates to the actual second endpoint. -/
theorem matchingPullback_test {B : Scheme} (g : B ⟶ (Z).left) (a : Γ(A.left, ⊤)) :
    matchingPullback f hL d V c k g (matchingTest f hL d V c k a) =
      (g ≫ (q).left).appTop a :=
  matchingPullback_toMatching f hL d V c k g ((q).left.appTop a)

local notation "r" =>
  Over.Hom.left (ReflexiveRelation.r
    (EquivalenceRelation.toReflexiveRelation (equivalence f hL d V c k)))

/-- The original full identity section defines a global counit on matching tensor families. -/
def matchingCounit : matchingRing f hL d V c k →+* Γ(A.left, ⊤) :=
  matchingPullback f hL d V c k r

/-- The global counit splits the actual first endpoint coefficient map. -/
theorem matchingCounit_source (a : Γ(A.left, ⊤)) :
    matchingCounit f hL d V c k (matchingSource f hL d V c k a) = a := by
  rw [matchingCounit, matchingPullback_source]
  have h := congrArg Over.Hom.left (equivalence f hL d V c k).reflexivity₁
  change (r) ≫ (p).left = 𝟙 A.left at h
  rw [h, Scheme.Hom.id_appTop, CommRingCat.id_apply]

/-- The same global counit splits the actual second endpoint coefficient map. -/
theorem matchingCounit_test (a : Γ(A.left, ⊤)) :
    matchingCounit f hL d V c k (matchingTest f hL d V c k a) = a := by
  rw [matchingCounit, matchingPullback_test]
  have h := congrArg Over.Hom.left (equivalence f hL d V c k).reflexivity₂
  change (r) ≫ (q).left = 𝟙 A.left at h
  rw [h, Scheme.Hom.id_appTop, CommRingCat.id_apply]

end TensorChart
end FLT.Mazur.HilbertChart.AffineRestriction
