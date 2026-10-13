/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertEnvelopeSourceTransport
public import FLT.Mazur.SchemeTranslationNormNaturality

/-!
# Constructed invariant regular norms on full Hilbert domains

Take the genuine finite-free norm of the source section on the complete
envelope. Naturality and the original composition map prove invariance. On
the actual full good open the envelope isomorphism is already constructed;
neither an affine good open nor an extension to the old source is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Module
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve Approximation SchemeTranslationNorm
open SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
/-- The original translation section algebra supplies the norm basis. -/
local instance invariantNormTranslationAlgebra : Algebra R Γ(V.left, ⊤) :=
  affineBaseSectionAlgebra V.hom
variable {ι : Type} [Finite ι] (b : Basis ι R Γ(V.left, ⊤))
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
local notation "j" => toEnvelope f hL d V c k
variable [IsIso (toEnvelope f hL d V c k).left]

/-- The genuine regular norm of the original source coefficient on the whole envelope. -/
def fullEnvelopeRegularNorm (s : Γ(A.left, ⊤)) : Γ(A.left, ⊤) :=
  regularNorm A V b (fullEnvelopeSourceSection f hL d V c k s)

/-- Invariance follows from original composition, with no compatibility hypothesis on `s`. -/
theorem fullEnvelopeRegularNorm_invariant (s : Γ(A.left, ⊤)) :
    (p).left.appTop (fullEnvelopeRegularNorm f hL d V c k b s) =
      (q).left.appTop (fullEnvelopeRegularNorm f hL d V c k b s) := by
  dsimp only [fullEnvelopeRegularNorm]
  rw [regularNorm_natural, regularNorm_natural, fullEnvelopeSourceSection_transport]

/-- The constructed coefficient in the original relation's actual invariant subring. -/
def fullEnvelopeInvariantNorm (s : Γ(A.left, ⊤)) :
    compatibleFunctions (p).left (q).left :=
  ⟨fullEnvelopeRegularNorm f hL d V c k b s, fullEnvelopeRegularNorm_invariant f hL d V c k b s⟩

omit [IsIso (toEnvelope f hL d V c k).left] in
/-- The original full good open has invariant regular norms without any affineness assumption. -/
def fullInteriorInvariantNorm [IsOpenImmersion k.left] [Etale V.hom]
    (s : Γ((fullInteriorSource f hL d V c k).left, ⊤)) :
    compatibleFunctions
      (fst f hL d V c (fullInteriorChart f hL d V c k)).left
      (snd f hL d V c (fullInteriorChart f hL d V c k)).left :=
  fullEnvelopeInvariantNorm f hL d V c (fullInteriorChart f hL d V c k) b s

end FLT.Mazur.HilbertChart.AffineRestriction
