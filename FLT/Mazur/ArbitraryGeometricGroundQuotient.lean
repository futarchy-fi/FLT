/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArbitraryGeometricFiniteGroundInterior
public import FLT.Mazur.GeometricFullInteriorQuotient

/-!
# Constructed affine ground-quotient charts for arbitrary original classes

An arbitrary original geometric class constructs a finite-free ground
refinement and an actual affine open in its invariant quotient. The whole
geometric quotient morphism factors through that open. The retained original
chart and geometric map identify the input class without extending it.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Module
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve Approximation RelativeRelationOrbit
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R K : Type} [CommRing R] [Algebra.FiniteType ℤ R] [Field K] [IsAlgClosed K]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f]
  [GeometricallyIntegral f] [SmoothOfRelativeDimension 1 f]
  {L : X.Modules} (hL : AmpleLineBundle L)
  (t : Spec (.of K) ⟶ Spec (.of R))
local notation "η" => (default : Spec (CommRingCat.of K))
local instance arbitraryGroundQuotientSmooth {S : Type} [CommRing S]
    (a : Spec (.of S) ⟶ Spec (.of R)) : SmoothOfRelativeDimension 1 (pullback.snd f a) :=
  MorphismProperty.pullback_snd _ _ inferInstance

include hL in
/-- Arbitrary original classes construct affine ground-quotient charts and whole geometric lifts. -/
theorem exists_arbitrary_geometric_ground_quotient
    (s : (relativeFppfSheaf f).obj.obj (op (Over.mk t))) :
    ∃ (d : ℕ) (V : Over (Spec (.of R)))
      (c : (relativeFppfSheaf f).obj.obj (op V))
      (A : Over (Spec (.of R))) (k : A ⟶ variableHilbertTest f d V)
      (b : Over.mk t ⟶ A), IsAffine V.left ∧ Etale V.hom ∧ IsAffine A.left ∧
      ∃ hk : IsOpenImmersion k.left, let _ := hk
      (relativeFppfSheaf f).obj.map b.op (sectionAt f hL d V c k) = s ∧
      b.left η ∈ fullEnvelopeLocus f hL d V c k ∧
      ∃ (S : Type) (_ : CommRing S) (_ : Algebra.FiniteType ℤ S)
        (a : Spec (.of S) ⟶ Spec (.of R)) (W : Over (Spec (.of S)))
        (_ : IsAffine W.left) (_ : Etale W.hom) (_ : IsFinite W.hom)
        (_ : Surjective W.hom) (v : (Over.map a).obj W ⟶ V),
        Etale a ∧ Etale v.left ∧
        ∃ z : Spec (.of K) ⟶ (groundBaseSource f a hL d V W v k).left,
          z ≫ (groundBaseSourceMap f a hL d V W v k).left = b.left ∧
          z ≫ (groundBaseSource f a hL d V W v k).hom ≫ a = t ∧
          ∃ (Q : Scheme)
            (j : Q.toLocallyRingedSpace ⟶ invariantLocallyRingedSpace
              (variableChartEquivalenceRelation (pullback.snd f a) (fixedBaseAmple f a hL)
                d W (fixedBaseTranslationClass f a V W v c)))
            (w : Spec (.of K) ⟶ Q), IsAffine Q ∧ LocallyRingedSpace.IsOpenImmersion j ∧
            w.toLRSHom ≫ j =
              (z ≫ (groundBaseSourceChart f a hL d V W v k).left).toLRSHom ≫
                invariantLocallyRingedProjection
                  (variableChartEquivalenceRelation (pullback.snd f a) (fixedBaseAmple f a hL)
                    d W (fixedBaseTranslationClass f a V W v c)) := by
  obtain ⟨d, V, c, A, k, b, hV, he, hA, hk, hb, hx,
    S, hS, hZ, a, W, hW, hWe, hWf, hWs, v, ha, hv, hB, z, hz, hzt, hi⟩ :=
    exists_arbitrary_geometric_finite_ground_interior f hL t s
  let _ := hV
  let _ := he
  let _ := hA
  let _ := hk
  let B := groundBaseSource f a hL d V W v k
  let z' : Over.mk (z ≫ B.hom) ⟶ B := Over.homMk z
  obtain ⟨n, ⟨e⟩⟩ := hB
  refine ⟨d, V, c, A, k, b, hV, he, hA, hk, hb, hx,
    S, hS, hZ, a, W, hW, hWe, hWf, hWs, v, ha, hv, z, hz, hzt, ?_⟩
  exact exists_geometric_fullInterior_quotient (pullback.snd f a) (fixedBaseAmple f a hL)
    d W (fixedBaseTranslationClass f a V W v c)
    (groundBaseSourceChart f a hL d V W v k) e z' hi

end FLT.Mazur.HilbertChart.AffineRestriction
