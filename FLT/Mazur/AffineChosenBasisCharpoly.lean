/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineCartesianCharpoly
public import FLT.Mazur.AffineOpenNorm

/-!
# Characteristic polynomials without a chosen global basis

A finite free section algebra has a characteristic polynomial independent of
its displayed basis. This interface lets unrelated local charts use different
ranks and bases while preserving cartesian coefficient transport.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Module Polynomial
namespace FLT.Mazur.AffineChosenBasisCharpoly
universe u v
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Finite freeness of the full section algebra, without choosing its rank. -/
def HasBasis : Prop :=
  let _ := f.appTop.hom.toAlgebra
  ∃ n : ℕ, Nonempty (Basis (Fin n) Γ(Y, ⊤) Γ(X, ⊤))

/-- The section polynomial computed using any one of the existing finite bases. -/
def charpoly (h : HasBasis f) (s : Γ(X, ⊤)) : (Γ(Y, ⊤))[X] :=
  AffineCartesianCharpoly.sectionCharpoly f h.choose_spec.some s

/-- The choice of basis, including its indexing type, has no effect. -/
theorem charpoly_eq (h : HasBasis f) {ι : Type v} [Finite ι] :
    let _ := f.appTop.hom.toAlgebra
    ∀ (b : Basis ι Γ(Y, ⊤) Γ(X, ⊤)) (s : Γ(X, ⊤)),
      charpoly f h s = AffineCartesianCharpoly.sectionCharpoly f b s := by
  let _ := f.appTop.hom.toAlgebra
  dsimp only
  intro b s
  exact AffineCartesianCharpoly.sectionCharpoly_basis f _ b s

/-- Cayley-Hamilton holds for the chosen presentation of the entire algebra. -/
theorem equation (h : HasBasis f) (s : Γ(X, ⊤)) :
    (charpoly f h s).Monic ∧ (charpoly f h s).eval₂ f.appTop.hom s = 0 :=
  AffineCartesianCharpoly.sectionCharpoly_equation f _ s

variable {P T : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine T]
  {a : P ⟶ X} {b : P ⟶ T} {g : T ⟶ Y} (H : IsPullback a b f g)

include H in
/-- The changed full section algebra is again finite free. -/
theorem hasBasis_pullback (h : HasBasis f) : HasBasis b := by
  let _ := f.appTop.hom.toAlgebra
  let _ := b.appTop.hom.toAlgebra
  obtain ⟨n, ⟨basis⟩⟩ := h
  exact ⟨n, ⟨AffineCartesianNorm.sectionBasis _ _ _ _ H basis⟩⟩

include H in
/-- Cartesian transport compares arbitrary independent finite bases. -/
theorem charpoly_pullback (hf : HasBasis f) (hb : HasBasis b) (s : Γ(X, ⊤)) :
    charpoly b hb (a.appTop s) = (charpoly f hf s).map g.appTop.hom := by
  let _ := f.appTop.hom.toAlgebra
  let _ := b.appTop.hom.toAlgebra
  rw [charpoly_eq b hb (AffineCartesianNorm.sectionBasis _ _ _ _ H hf.choose_spec.some)]
  exact AffineCartesianCharpoly.sectionCharpoly_pullback f H _ s

omit [IsAffine X] [IsAffine Y] [IsAffine T] in
/-- An isomorphism of full source algebras preserves the polynomial. -/
theorem charpoly_transport {E F : Scheme.{u}} (p : E ⟶ T) (q : F ⟶ T)
    (i : E ≅ F) (hi : i.hom ≫ q = p) (hp : HasBasis p) (hq : HasBasis q)
    (s : Γ(F, ⊤)) : charpoly p hp (i.hom.appTop s) = charpoly q hq s :=
  AffineCartesianCharpoly.sectionCharpoly_transport p q i hi _ _ s

end FLT.Mazur.AffineChosenBasisCharpoly
