/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArbitraryGeometricAffineFullFiber
public import FLT.Mazur.AffineHilbertGeometricFiniteGround

/-!+# Finite-free full interiors retaining arbitrary original Picard classes

Construct the initial original chart and its full fiber, then construct a
finite-free ground refinement and lift the whole original geometric map.
The interior is for the changed family; the original section and full fiber
remain explicit, so this makes no original-interior descent assertion.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Module
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve Approximation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R K : Type} [CommRing R] [Algebra.FiniteType ℤ R] [Field K] [IsAlgClosed K]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f]
  [GeometricallyIntegral f] [SmoothOfRelativeDimension 1 f]
  {L : X.Modules} (hL : AmpleLineBundle L)
  (t : Spec (.of K) ⟶ Spec (.of R))
local notation "η" => (default : Spec (CommRingCat.of K))
local instance {S : Type} [CommRing S] (a : Spec (.of S) ⟶ Spec (.of R)) :
    SmoothOfRelativeDimension 1 (pullback.snd f a) :=
  MorphismProperty.pullback_snd _ _ inferInstance

include hL in
/-- An arbitrary original geometric class has a constructed finite-free full-interior refinement. -/
theorem exists_arbitrary_geometric_finite_ground_interior
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
        (let _ := affineBaseSectionAlgebra W.hom
         ∃ n : ℕ, Nonempty (Basis (Fin n) S Γ(W.left, ⊤))) ∧
        ∃ z : Spec (.of K) ⟶ (groundBaseSource f a hL d V W v k).left,
          z ≫ (groundBaseSourceMap f a hL d V W v k).left = b.left ∧
          z ≫ (groundBaseSource f a hL d V W v k).hom ≫ a = t ∧
          z η ∈ fullEnvelopeInterior (pullback.snd f a) (fixedBaseAmple f a hL) d W
            (fixedBaseTranslationClass f a V W v c)
            (groundBaseSourceChart f a hL d V W v k) := by
  obtain ⟨d, V, c, A, k, b, hV, he, hA, hk, hb, hx⟩ :=
    exists_arbitrary_geometric_affine_full_fiber f hL t s
  let _ := hV
  let _ := he
  let _ := hA
  let _ := hk
  exact ⟨d, V, c, A, k, b, hV, he, hA, hk, hb, hx,
    exists_geometric_finite_free_groundInterior f hL d V c k b hx⟩

end FLT.Mazur.HilbertChart.AffineRestriction
