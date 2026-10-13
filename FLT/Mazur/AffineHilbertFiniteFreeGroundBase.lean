/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineEtaleFiniteFreeSpectrum
public import FLT.Mazur.AffineHilbertGroundBaseFullFiber

/-!
# Finite-free translations retaining original full-fiber Hilbert chart points

Start with a point of an original open affine Hilbert chart whose entire
independent envelope fiber is present. Construct a new coefficient spectrum,
a finite faithful etale translation with a section basis and a point of the transported affine
open chart in its full-fiber interior. No branch or local coverage witness
is assumed. Initial coverage by full-fiber charts is separate work.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open FCurve CartierAbel SchemePicard EtaleTranslationBranch Approximation Module
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
local instance {S : Type} [CommRing S] (a : Spec (.of S) ⟶ Spec (.of R)) :
    SmoothOfRelativeDimension 1 (Limits.pullback.snd f a) :=
  MorphismProperty.pullback_snd _ _ inferInstance

/-- Every original full-fiber chart point has a constructed finite-free faithful refinement. -/
theorem exists_finite_free_groundBase_fullInterior (x : A.left)
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
        y ∈ fullEnvelopeInterior (Limits.pullback.snd f a) (fixedBaseAmple f a hL) d W
          (fixedBaseTranslationClass f a V W t c) (groundBaseSourceChart f a hL d V W t k) := by
  obtain ⟨S, hS, hZ, a, W, hW, hEt, hfin, hsurj, t₀, ha, ht, hb, _, z, hz⟩ :=
    exists_finite_free_faithful_spectrum V.hom ((k ≫ variableHilbertBase f d V).left x)
      ⊤ trivial
  let t : (Over.map a).obj W ⟶ V := Over.homMk t₀.left (Over.w t₀)
  obtain ⟨y, hy, _⟩ := Scheme.exists_preimage_of_isPullback
    (groundBaseSource_isPullback f a hL d V W t k) x z hz.symm
  refine ⟨S, hS, hZ, a, W, inferInstance, inferInstance, inferInstance,
    inferInstance, t, ha, ht, hb, inferInstance, y, hy, ?_⟩
  apply groundBaseSource_mem_interior_of_finite f a hL d V W t c k y
  rwa [hy]

end FLT.Mazur.HilbertChart.AffineRestriction
