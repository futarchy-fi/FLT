/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineCartesianNorm
public import FLT.Mazur.AffineEnvelopeNormTransport
public import FLT.Mazur.EquivalenceRelationFiberRebase

/-!
# Invariant norms for the whole original affine relation

A genuine finite basis for the first projection defines the norm of the second
pullback of any original function. Whole-fiber rebasing proves its invariance.
The basis concerns the original relation, not a moving finite group action.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Module
namespace FLT.Mazur.AffineRelationNorm
universe u v
set_option backward.isDefEq.respectTransparency false

/-- The norm on actual section rings, with scalars supplied by the given morphism. -/
def sectionNorm {X Y : Scheme.{u}} (f : X ⟶ Y) (s : Γ(X, ⊤)) : Γ(Y, ⊤) :=
  let _ := f.appTop.hom.toAlgebra
  Algebra.norm Γ(Y, ⊤) s

/-- The norm under an arbitrary affine cartesian change of target. -/
theorem sectionNorm_pullback {P X T Y : Scheme.{u}}
    [IsAffine X] [IsAffine T] [IsAffine Y]
    {a : P ⟶ X} {b : P ⟶ T} {f : X ⟶ Y} {g : T ⟶ Y}
    (H : IsPullback a b f g) {ι : Type v} [Finite ι] :
    let _ := f.appTop.hom.toAlgebra
    ∀ (_basis : Basis ι Γ(Y, ⊤) Γ(X, ⊤)) (s : Γ(X, ⊤)),
      sectionNorm b (a.appTop s) = g.appTop (sectionNorm f s) := by
  let _ := f.appTop.hom.toAlgebra
  dsimp only
  intro basis s
  exact AffineCartesianNorm.norm_pullback a b f g H basis s

/-- An isomorphism over the actual target preserves the full norm. -/
theorem sectionNorm_transport {E F T : Scheme.{u}} (p : E ⟶ T) (q : F ⟶ T)
    (i : E ≅ F) (hi : i.hom ≫ q = p) (s : Γ(F, ⊤)) :
    sectionNorm p (i.hom.appTop s) = sectionNorm q s :=
  AffineEnvelopeNormTransport.norm_transport p q i hi s

variable {D A : Scheme.{u}} (p q : D ⟶ A)

/-- A function on the original source gives a norm along all original relation arrows. -/
def relationNorm (s : Γ(A, ⊤)) : Γ(A, ⊤) := sectionNorm p (q.appTop s)

variable [IsAffine D] [IsAffine A] (e : CategoryTheory.EquivalenceRelation p q)

include e in
/-- Whole-fiber rebasing proves the norm equation on every affine relation test. -/
theorem relationNorm_test {T : Scheme.{u}} [IsAffine T] (a : T ⟶ D)
    {ι : Type v} [Finite ι] :
    let _ := p.appTop.hom.toAlgebra
    ∀ (_basis : Basis ι Γ(A, ⊤) Γ(D, ⊤)) (s : Γ(A, ⊤)),
      (a ≫ p).appTop (relationNorm p q s) =
        (a ≫ q).appTop (relationNorm p q s) := by
  let _ := p.appTop.hom.toAlgebra
  dsimp only
  intro basis s
  let i := EquivalenceRelationFiber.rebaseIso e a
  have hi : i.hom ≫ pullback.snd p (a ≫ q) = pullback.snd p (a ≫ p) :=
    EquivalenceRelationFiber.rebase_snd e a
  have hq : i.hom ≫ pullback.fst p (a ≫ q) ≫ q =
      pullback.fst p (a ≫ p) ≫ q := by
    change EquivalenceRelationFiber.rebase e a ≫ pullback.fst p (a ≫ q) ≫ q = _
    rw [EquivalenceRelationFiber.rebase_fst_assoc,
      EquivalenceRelationFiber.rebaseArrow_snd]
  have hs := congrArg (fun h ↦ h.appTop s) hq
  change i.hom.appTop ((pullback.fst p (a ≫ q)).appTop (q.appTop s)) =
    (pullback.fst p (a ≫ p)).appTop (q.appTop s) at hs
  unfold relationNorm
  rw [← sectionNorm_pullback (IsPullback.of_hasPullback p (a ≫ p)) basis,
    ← sectionNorm_pullback (IsPullback.of_hasPullback p (a ≫ q)) basis, ← hs]
  exact sectionNorm_transport _ _ i hi _

include e in
/-- The constructed norm is invariant under both original projections. -/
theorem relationNorm_invariant {ι : Type v} [Finite ι] :
    let _ := p.appTop.hom.toAlgebra
    ∀ (_basis : Basis ι Γ(A, ⊤) Γ(D, ⊤)) (s : Γ(A, ⊤)),
      p.appTop (relationNorm p q s) = q.appTop (relationNorm p q s) := by
  let _ := p.appTop.hom.toAlgebra
  dsimp only
  intro basis s
  simpa only [Category.id_comp] using relationNorm_test p q e (𝟙 D) basis s

end FLT.Mazur.AffineRelationNorm
