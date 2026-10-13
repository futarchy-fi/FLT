/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFiniteFreeGroundBase
public import FLT.Mazur.HilbertFullInteriorQuotientChart

/-!
# Constructed affine quotient neighborhoods after finite-free ground refinement

An original full-fiber point has an actual finite faithful translation
refinement and an affine scheme chart of the refined original invariant
quotient containing its lift. The lift still maps to the prescribed old point.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open FCurve CartierAbel SchemePicard Approximation Module RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R))
  [IsProper f] [Flat f] [GeometricallyIntegral f] [SmoothOfRelativeDimension 1 f]
  {L : X.Modules} (hL : AmpleLineBundle L) (d : ℕ)
  (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left] (k : A ⟶ variableHilbertTest f d V)
  [IsOpenImmersion k.left]
/-- Ground refinement preserves the original smooth relative dimension. -/
local instance {S : Type} [CommRing S] (a : Spec (.of S) ⟶ Spec (.of R)) :
    SmoothOfRelativeDimension 1 (Limits.pullback.snd f a) :=
  MorphismProperty.pullback_snd _ _ inferInstance

/-- A full-fiber point lifts into an actual affine scheme chart of the refined original quotient. -/
theorem exists_finite_free_groundBase_quotient_chart (x : A.left)
    (hx : x ∈ fullEnvelopeLocus f hL d V c k) :
    ∃ (S : Type) (_ : CommRing S) (_ : Algebra.FiniteType ℤ S)
      (a : Spec (.of S) ⟶ Spec (.of R)) (W : Over (Spec (.of S)))
      (_ : IsAffine W.left) (_ : Etale W.hom) (_ : IsFinite W.hom)
      (_ : Surjective W.hom) (t : (Over.map a).obj W ⟶ V),
      Etale a ∧ Etale t.left ∧
      (let _ := affineBaseSectionAlgebra W.hom
       ∃ n : ℕ, Nonempty (Basis (Fin n) S Γ(W.left, ⊤))) ∧
      IsAffine (groundBaseSource f a hL d V W t k).left ∧
      ∃ y : (groundBaseSource f a hL d V W t k).left,
        (groundBaseSourceMap f a hL d V W t k).left y = x ∧
        ∃ (Q : Scheme) (q : Q.toLocallyRingedSpace ⟶ invariantLocallyRingedSpace
          (variableChartEquivalenceRelation (Limits.pullback.snd f a)
            (fixedBaseAmple f a hL) d W (fixedBaseTranslationClass f a V W t c))),
          IsAffine Q ∧ LocallyRingedSpace.IsOpenImmersion q ∧
            projection (variableChartEquivalenceRelation (Limits.pullback.snd f a)
              (fixedBaseAmple f a hL) d W (fixedBaseTranslationClass f a V W t c))
              ((groundBaseSourceChart f a hL d V W t k).left y) ∈ Set.range q.base := by
  obtain ⟨S, hS, hZ, a, W, hW, hEt, hfin, hsurj, t, ha, ht, hb, hA, y, hy, hyU⟩ :=
    exists_finite_free_groundBase_fullInterior f hL d V c k x hx
  let _ := affineBaseSectionAlgebra W.hom
  obtain ⟨n, ⟨b⟩⟩ := hb
  refine ⟨S, hS, hZ, a, W, hW, hEt, hfin, hsurj, t, ha, ht, ⟨n, ⟨b⟩⟩, hA, y, hy, ?_⟩
  exact exists_fullInterior_affine_quotient_chart (Limits.pullback.snd f a)
    (fixedBaseAmple f a hL) d W (fixedBaseTranslationClass f a V W t c)
    (groundBaseSourceChart f a hL d V W t k) b y hyU

end FLT.Mazur.HilbertChart.AffineRestriction
