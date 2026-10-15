/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineProductNormFiber

/-!
# Norm transport across independent ground presentations

An isomorphism of envelopes over the actual source preserves the norm of an
actual section. The two presentations may use different ground rings and
unrelated translation bases. Only the source projection must be preserved.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Module
universe u v w
namespace FLT.Mazur.AffineEnvelopeNormTransport
open Approximation AffineProductTranslationNorm
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {T E F : Scheme.{u}} (p : E ⟶ T) (q : F ⟶ T)

/-- A whole envelope isomorphism gives an equivalence of its actual section algebras. -/
def sectionAlgEquiv (e : E ≅ F) (he : e.hom ≫ q = p) :
    let _ := p.appTop.hom.toAlgebra
    let _ := q.appTop.hom.toAlgebra
    Γ(F, ⊤) ≃ₐ[Γ(T, ⊤)] Γ(E, ⊤) := by
  let _ := p.appTop.hom.toAlgebra
  let _ := q.appTop.hom.toAlgebra
  exact { (Scheme.Γ.mapIso e.op).commRingCatIsoToRingEquiv with
    commutes' := by
      intro x
      exact congrArg (fun h : E ⟶ T ↦ h.appTop x) he }

/-- Envelope transport preserves determinants in the unchanged source section ring. -/
theorem norm_transport (e : E ≅ F) (he : e.hom ≫ q = p) (s : Γ(F, ⊤)) :
    let _ := p.appTop.hom.toAlgebra
    let _ := q.appTop.hom.toAlgebra
    Algebra.norm Γ(T, ⊤) (e.hom.appTop s) = Algebra.norm Γ(T, ⊤) s := by
  let _ := p.appTop.hom.toAlgebra
  let _ := q.appTop.hom.toAlgebra
  exact Algebra.norm_eq_of_algEquiv (sectionAlgEquiv p q e he) s

variable {R S : Type u} [CommRing R] [CommRing S]
  (t : T ⟶ Spec (.of R)) (z : T ⟶ Spec (.of S))
  (V : Over (Spec (.of R))) (W : Over (Spec (.of S)))
  [IsAffine T] [IsAffine V.left] [IsAffine W.left]
local instance mkAffine {C : Scheme.{u}} (a : T ⟶ C) : IsAffine (Over.mk a).left :=
  inferInstanceAs (IsAffine T)
/-- The left presentation uses its actual structural section algebra. -/
local instance leftTranslationAlgebra : Algebra R Γ(V.left, ⊤) :=
  affineBaseSectionAlgebra V.hom
/-- The right presentation retains its independent ground algebra. -/
local instance rightTranslationAlgebra : Algebra S Γ(W.left, ⊤) :=
  affineBaseSectionAlgebra W.hom
variable {ι : Type v} {κ : Type w} [Finite ι] [Finite κ]
  (b : Basis ι R Γ(V.left, ⊤)) (c : Basis κ S Γ(W.left, ⊤))

/-- Independent ground presentations of the same envelope compute the same regular norm. -/
theorem envelopeNorm_transport
    (e : (prod (Over.mk t) V).left ≅ (prod (Over.mk z) W).left)
    (he : e.hom ≫ (prod.fst : prod (Over.mk z) W ⟶ Over.mk z).left =
      (prod.fst : prod (Over.mk t) V ⟶ Over.mk t).left)
    (s : Γ((prod (Over.mk z) W).left, ⊤)) :
    envelopeNorm (Over.mk t) V b (e.hom.appTop s) =
      envelopeNorm (Over.mk z) W c s := by
  rw [envelopeNorm_eq_section_norm, envelopeNorm_eq_section_norm]
  exact norm_transport _ _ e he s

end FLT.Mazur.AffineEnvelopeNormTransport
