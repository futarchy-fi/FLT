/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFiniteFreeGroundBase
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-!+# Whole geometric maps retained in finite-free ground refinements

The finite-free ground refinement lifts the specified original geometric
morphism, not just its topological image. The new interior point therefore
retains the original Picard class without identifying unrelated field maps.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Module
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve Approximation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R K : Type} [CommRing R] [Algebra.FiniteType ℤ R] [Field K] [IsSepClosed K]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f]
  [GeometricallyIntegral f] [SmoothOfRelativeDimension 1 f]
  {L : X.Modules} (hL : AmpleLineBundle L) (d : ℕ)
  (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left] (k : A ⟶ variableHilbertTest f d V)
  [IsOpenImmersion k.left] {t : Spec (.of K) ⟶ Spec (.of R)} (b : Over.mk t ⟶ A)
local notation "η" => (default : Spec (CommRingCat.of K))
local instance {S : Type} [CommRing S] (a : Spec (.of S) ⟶ Spec (.of R)) :
    SmoothOfRelativeDimension 1 (pullback.snd f a) :=
  MorphismProperty.pullback_snd _ _ inferInstance

/-- A finite-free full interior retains the entire given original geometric source morphism. -/
theorem exists_geometric_finite_free_groundInterior
    (hx : b.left η ∈ fullEnvelopeLocus f hL d V c k) :
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
          (fixedBaseTranslationClass f a V W v c) (groundBaseSourceChart f a hL d V W v k) := by
  obtain ⟨S, hS, hZ, a, W, hW, he, hf, hs, v, ha, hv, hB, _, y, hy, hi⟩ :=
    exists_finite_free_groundBase_fullInterior f hL d V c k (b.left η) hx
  let _ := hv
  obtain ⟨z, hz, hzy⟩ := Scheme.exists_fac_of_etale_of_isSepClosed
    (groundBaseSourceMap f a hL d V W v k).left b.left y hy
  refine ⟨S, hS, hZ, a, W, hW, he, hf, hs, v, ha, hv, hB, z, hz, ?_, ?_⟩
  · change z ≫ ((Over.map a).obj (groundBaseSource f a hL d V W v k)).hom = t
    rw [← (groundBaseSourceMap f a hL d V W v k).w, ← Category.assoc, hz]
    exact b.w
  · exact hzy.symm ▸ hi

end FLT.Mazur.HilbertChart.AffineRestriction
