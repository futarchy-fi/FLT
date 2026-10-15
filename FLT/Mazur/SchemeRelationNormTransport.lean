/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeNormIndependentGroundTests

/-!
# Full-relation compatibility from affine envelope transport

Equality of regular norms can be checked on an affine cover of the entire
relation scheme. Each endpoint keeps its independent ground map. The input is
geometric transport of envelopes and source sections, not invariance of norms.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Module
universe u v w w'
namespace FLT.Mazur.SchemeTranslationNorm
open Approximation SchemeEffectiveEpiSections
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R S : Type u} [CommRing R] [CommRing S]
  (Y V : Over (Spec (.of R))) (Z W : Over (Spec (.of S)))
  [IsAffine V.left] [IsAffine W.left]
/-- The first norm retains its own ground algebra. -/
local instance relationNormLeftAlgebra : Algebra R Γ(V.left, ⊤) :=
  affineBaseSectionAlgebra V.hom
/-- The second norm retains its independent ground algebra. -/
local instance relationNormRightAlgebra : Algebra S Γ(W.left, ⊤) :=
  affineBaseSectionAlgebra W.hom
variable {ι : Type v} {κ : Type w} [Finite ι] [Finite κ]
  (b : Basis ι R Γ(V.left, ⊤)) (c : Basis κ S Γ(W.left, ⊤))
  (s : Γ((prod Y V).left, ⊤)) (r : Γ((prod Z W).left, ⊤))
  {D : Scheme.{u}} (p : D ⟶ Y.left) (q : D ⟶ Z.left)
  (C : D.OpenCover.{w'}) [∀ i, IsAffine (C.X i)]

/-- Norm comparison is detected on whole affine tests covering the original relation. -/
theorem regularNorm_eq_of_affineTransport
    (h : ∀ i, ∃ e : independentTestEnvelope Y V (C.f i ≫ p) ≅
        independentTestEnvelope Z W (C.f i ≫ q),
      e.hom ≫ independentTestProjection Z W (C.f i ≫ q) =
        independentTestProjection Y V (C.f i ≫ p) ∧
      e.hom.appTop ((independentTestEnvelopeMap Z W (C.f i ≫ q)).appTop r) =
        (independentTestEnvelopeMap Y V (C.f i ≫ p)).appTop s) :
    p.appTop (regularNorm Y V b s) = q.appTop (regularNorm Z W c r) := by
  apply (functionEquiv D).symm.injective
  apply C.hom_ext
  intro i
  apply (functionEquiv (C.X i)).injective
  simp only [functionEquiv_comp, Equiv.apply_symm_apply]
  obtain ⟨e, he, hs⟩ := h i
  exact regularNorm_independentTransport Y V b s Z W c r (C.f i ≫ p) (C.f i ≫ q)
    e he hs

/-- Whole source-map compatibility proves the norm equation for every coefficient at once. -/
theorem regularNorm_eq_of_sourceTransport {H : Scheme.{u}}
    (a : (prod Y V).left ⟶ H) (a' : (prod Z W).left ⟶ H)
    (h : ∀ i, ∃ e : independentTestEnvelope Y V (C.f i ≫ p) ≅
        independentTestEnvelope Z W (C.f i ≫ q),
      e.hom ≫ independentTestProjection Z W (C.f i ≫ q) =
        independentTestProjection Y V (C.f i ≫ p) ∧
      e.hom ≫ independentTestEnvelopeMap Z W (C.f i ≫ q) ≫ a' =
        independentTestEnvelopeMap Y V (C.f i ≫ p) ≫ a) (v : Γ(H, ⊤)) :
    p.appTop (regularNorm Y V b (a.appTop v)) =
      q.appTop (regularNorm Z W c (a'.appTop v)) := by
  apply regularNorm_eq_of_affineTransport Y V Z W b c _ _ p q C
  intro i
  obtain ⟨e, he, ha⟩ := h i
  exact ⟨e, he, congrArg (fun g ↦ g.appTop v) ha⟩

end FLT.Mazur.SchemeTranslationNorm
