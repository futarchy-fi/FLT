/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineCartesianNorm
public import FLT.Mazur.AffineEnvelopeNormTransport
public import FLT.Mazur.FiniteFreeAlgebraCharpoly

/-!
# Characteristic equations on actual affine cartesian squares

The full section pushout transports the multiplication polynomial. Both
presentations retain their actual target algebra and may use different bases.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Module Polynomial
namespace FLT.Mazur.AffineCartesianCharpoly
universe u v w
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type v} [Finite ι]

/-- The multiplication polynomial in the section algebra of the actual morphism. -/
def sectionCharpoly :
    let _ := f.appTop.hom.toAlgebra
    Basis ι Γ(Y, ⊤) Γ(X, ⊤) → Γ(X, ⊤) → (Γ(Y, ⊤))[X] := by
  let _ := f.appTop.hom.toAlgebra
  exact FiniteFreeAlgebraCharpoly.charpoly

/-- Changing the displayed basis does not change the polynomial. -/
theorem sectionCharpoly_basis {κ : Type w} [Finite κ] :
    let _ := f.appTop.hom.toAlgebra
    ∀ (b : Basis ι Γ(Y, ⊤) Γ(X, ⊤)) (c : Basis κ Γ(Y, ⊤) Γ(X, ⊤)) (s : Γ(X, ⊤)),
      sectionCharpoly f b s = sectionCharpoly f c s := by
  let _ := f.appTop.hom.toAlgebra
  dsimp only
  intro b c s
  exact FiniteFreeAlgebraCharpoly.transport c b (AlgEquiv.refl) s

/-- The original section satisfies this monic equation. -/
theorem sectionCharpoly_equation :
    let _ := f.appTop.hom.toAlgebra
    ∀ (b : Basis ι Γ(Y, ⊤) Γ(X, ⊤)) (s : Γ(X, ⊤)),
      (sectionCharpoly f b s).Monic ∧ aeval s (sectionCharpoly f b s) = 0 := by
  let _ := f.appTop.hom.toAlgebra
  dsimp only
  intro b s
  exact ⟨FiniteFreeAlgebraCharpoly.monic b s, FiniteFreeAlgebraCharpoly.aeval_eq_zero b s⟩

variable {P T : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine T]
  {a : P ⟶ X} {b : P ⟶ T} {g : T ⟶ Y} (H : IsPullback a b f g)

/-- Arbitrary affine base change preserves the full characteristic equation. -/
theorem sectionCharpoly_pullback :
    let _ := f.appTop.hom.toAlgebra
    ∀ (basis : Basis ι Γ(Y, ⊤) Γ(X, ⊤)) (s : Γ(X, ⊤)),
      sectionCharpoly b (AffineCartesianNorm.sectionBasis a b f g H basis) (a.appTop s) =
        (sectionCharpoly f basis s).map g.appTop.hom := by
  let _ := f.appTop.hom.toAlgebra
  let _ := g.appTop.hom.toAlgebra
  let _ := b.appTop.hom.toAlgebra
  dsimp only
  intro basis s
  rw [← AffineCartesianNorm.tensorIso_right a b f g H]
  exact (FiniteFreeAlgebraCharpoly.transport (basis.baseChange Γ(T, ⊤))
    (AffineCartesianNorm.sectionBasis a b f g H basis)
    (AffineCartesianNorm.tensorAlgEquiv a b f g H) _).trans
      (FiniteFreeAlgebraCharpoly.baseChange basis Γ(T, ⊤) s)

omit [IsAffine X] [IsAffine Y] [IsAffine T] in
/-- Isomorphic section algebras over the original target have identical equations. -/
theorem sectionCharpoly_transport {E F : Scheme.{u}} (p : E ⟶ T) (q : F ⟶ T)
    (i : E ≅ F) (hi : i.hom ≫ q = p) {κ : Type w} [Finite κ] :
    let _ := p.appTop.hom.toAlgebra
    let _ := q.appTop.hom.toAlgebra
    ∀ (bp : Basis ι Γ(T, ⊤) Γ(E, ⊤)) (bq : Basis κ Γ(T, ⊤) Γ(F, ⊤)) (s : Γ(F, ⊤)),
      sectionCharpoly p bp (i.hom.appTop s) = sectionCharpoly q bq s := by
  let _ := p.appTop.hom.toAlgebra
  let _ := q.appTop.hom.toAlgebra
  dsimp only
  intro bp bq s
  exact FiniteFreeAlgebraCharpoly.transport bq bp
    (AffineEnvelopeNormTransport.sectionAlgEquiv p q i hi) s

end FLT.Mazur.AffineCartesianCharpoly
