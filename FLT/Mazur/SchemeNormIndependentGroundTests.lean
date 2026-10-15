/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineEnvelopeNormTransport
public import FLT.Mazur.SchemeTranslationNormNaturality

/-!
# Regular norm comparisons on tests with independent ground maps

Two source maps induce two ground maps on the same affine test. Compare their
whole envelopes over that test, without identifying either ground coordinate.
This comparison detects regular functions, including nilpotent coefficients.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Module
universe u v w
namespace FLT.Mazur.SchemeTranslationNorm
open Approximation AffineProductTranslationNorm AffineEnvelopeNormTransport
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type u} [CommRing R] (Y V : Over (Spec (.of R))) [IsAffine V.left]
/-- Keep the actual ground algebra for the first translation scheme. -/
local instance independentTestTranslationAlgebra : Algebra R Γ(V.left, ⊤) :=
  affineBaseSectionAlgebra V.hom
variable {ι : Type v} [Finite ι] (b : Basis ι R Γ(V.left, ⊤))
  (s : Γ((prod Y V).left, ⊤))

/-- An arbitrary scheme map acquires its own actual ground coordinate. -/
def independentTest {T : Scheme.{u}} (x : T ⟶ Y.left) : Over (Spec (.of R)) :=
  Over.mk (x ≫ Y.hom)

instance independentTest_affine {T : Scheme.{u}} [IsAffine T] (x : T ⟶ Y.left) :
    IsAffine (independentTest Y x).left := inferInstanceAs (IsAffine T)

/-- Keep the entire original test morphism in the category over its induced ground. -/
def independentTestArrow {T : Scheme.{u}} (x : T ⟶ Y.left) : independentTest Y x ⟶ Y :=
  Over.homMk x

/-- The genuine envelope on a test remembers that test's ground coordinate. -/
def independentTestEnvelope {T : Scheme.{u}} (x : T ⟶ Y.left) : Scheme.{u} :=
  (prod (independentTest Y x) V).left

/-- The unchanged projection to the test scheme. -/
def independentTestProjection {T : Scheme.{u}} (x : T ⟶ Y.left) :
    independentTestEnvelope Y V x ⟶ T :=
  (prod.fst : prod (independentTest Y x) V ⟶ independentTest Y x).left

/-- Pull the whole envelope back along the specified source test. -/
def independentTestEnvelopeMap {T : Scheme.{u}} (x : T ⟶ Y.left) :
    independentTestEnvelope Y V x ⟶ (prod Y V).left :=
  (prod.map (independentTestArrow Y x) (𝟙 V)).left

/-- Norms restrict along every affine scheme test, with its own induced ground map. -/
theorem regularNorm_independentTest {T : Scheme.{u}} [IsAffine T] (x : T ⟶ Y.left) :
    x.appTop (regularNorm Y V b s) =
      envelopeNorm (independentTest Y x) V b ((independentTestEnvelopeMap Y V x).appTop s) :=
  norm_test Y V b s Y.left.affineCover (independentTestArrow Y x)

variable {S : Type u} [CommRing S] (Z W : Over (Spec (.of S))) [IsAffine W.left]
/-- The second translation algebra may have a different ground ring. -/
local instance otherTestTranslationAlgebra : Algebra S Γ(W.left, ⊤) :=
  affineBaseSectionAlgebra W.hom
variable {κ : Type w} [Finite κ] (c : Basis κ S Γ(W.left, ⊤))
  (r : Γ((prod Z W).left, ⊤))

/-- Whole envelope transport compares norms even across unrelated ground presentations. -/
theorem regularNorm_independentTransport {T : Scheme.{u}} [IsAffine T]
    (x : T ⟶ Y.left) (y : T ⟶ Z.left)
    (e : independentTestEnvelope Y V x ≅ independentTestEnvelope Z W y)
    (he : e.hom ≫ independentTestProjection Z W y = independentTestProjection Y V x)
    (hs : e.hom.appTop ((independentTestEnvelopeMap Z W y).appTop r) =
      (independentTestEnvelopeMap Y V x).appTop s) :
    x.appTop (regularNorm Y V b s) = y.appTop (regularNorm Z W c r) := by
  rw [regularNorm_independentTest, regularNorm_independentTest, ← hs]
  exact envelopeNorm_transport (x ≫ Y.hom) (y ≫ Z.hom) V W b c e he _

/-- A whole source-map equation supplies compatibility for every regular coefficient. -/
theorem regularNorm_independentTransport_source {T H : Scheme.{u}} [IsAffine T]
    (x : T ⟶ Y.left) (y : T ⟶ Z.left)
    (e : independentTestEnvelope Y V x ≅ independentTestEnvelope Z W y)
    (he : e.hom ≫ independentTestProjection Z W y = independentTestProjection Y V x)
    (a : (prod Y V).left ⟶ H) (a' : (prod Z W).left ⟶ H)
    (ha : e.hom ≫ independentTestEnvelopeMap Z W y ≫ a' =
      independentTestEnvelopeMap Y V x ≫ a) (v : Γ(H, ⊤)) :
    x.appTop (regularNorm Y V b (a.appTop v)) =
      y.appTop (regularNorm Z W c (a'.appTop v)) := by
  apply regularNorm_independentTransport Y V b _ Z W c _ x y e he
  exact congrArg (fun h ↦ h.appTop v) ha

end FLT.Mazur.SchemeTranslationNorm
