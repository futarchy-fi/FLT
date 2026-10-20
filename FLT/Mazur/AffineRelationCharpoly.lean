/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineCartesianCharpoly
public import FLT.Mazur.EquivalenceRelationFiberRebase

/-!
# Invariant characteristic polynomials of the full original relation

Rebasing entire relation fibers preserves multiplication polynomials. Thus
the coefficients are original invariants. Reflexivity makes the original
source section a root, without passing to reduced rings or geometric points.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Module Polynomial
namespace FLT.Mazur.AffineRelationCharpoly
open AffineCartesianCharpoly AffineCartesianNorm
universe u v
set_option backward.isDefEq.respectTransparency false
variable {D A : Scheme.{u}} (p q : D ⟶ A) {ι : Type v} [Finite ι]

/-- The multiplication polynomial along all original arrows with the given first endpoint. -/
def relationCharpoly :
    let _ := p.appTop.hom.toAlgebra
    Basis ι Γ(A, ⊤) Γ(D, ⊤) → Γ(A, ⊤) → (Γ(A, ⊤))[X] := by
  let _ := p.appTop.hom.toAlgebra
  exact fun basis s ↦ sectionCharpoly p basis (q.appTop s)

variable [IsAffine D] [IsAffine A] (e : CategoryTheory.EquivalenceRelation p q)

include e in
/-- Whole-fiber rebasing proves equality of every coefficient on an affine relation test. -/
theorem relationCharpoly_test {T : Scheme.{u}} [IsAffine T] (a : T ⟶ D) :
    let _ := p.appTop.hom.toAlgebra
    ∀ (basis : Basis ι Γ(A, ⊤) Γ(D, ⊤)) (s : Γ(A, ⊤)),
      (relationCharpoly p q basis s).map (a ≫ p).appTop.hom =
        (relationCharpoly p q basis s).map (a ≫ q).appTop.hom := by
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
  unfold relationCharpoly
  rw [← sectionCharpoly_pullback p (IsPullback.of_hasPullback p (a ≫ p)) basis,
    ← sectionCharpoly_pullback p (IsPullback.of_hasPullback p (a ≫ q)) basis, ← hs]
  exact sectionCharpoly_transport _ _ i hi _ _ _

include e in
/-- Every coefficient belongs to the unchanged full relation equalizer. -/
theorem relationCharpoly_invariant :
    let _ := p.appTop.hom.toAlgebra
    ∀ (basis : Basis ι Γ(A, ⊤) Γ(D, ⊤)) (s : Γ(A, ⊤)) (n : ℕ),
      p.appTop ((relationCharpoly p q basis s).coeff n) =
        q.appTop ((relationCharpoly p q basis s).coeff n) := by
  let _ := p.appTop.hom.toAlgebra
  dsimp only
  intro basis s n
  have h := congrArg (fun z ↦ z.coeff n) (relationCharpoly_test p q e (𝟙 D) basis s)
  simpa only [Category.id_comp, coeff_map] using h

omit [IsAffine D] [IsAffine A] in
include e in
/-- Reflexivity turns Cayley-Hamilton on arrows into an equation for the source section. -/
theorem relationCharpoly_equation :
    let _ := p.appTop.hom.toAlgebra
    ∀ (basis : Basis ι Γ(A, ⊤) Γ(D, ⊤)) (s : Γ(A, ⊤)),
      (relationCharpoly p q basis s).Monic ∧ (relationCharpoly p q basis s).eval s = 0 := by
  let _ := p.appTop.hom.toAlgebra
  dsimp only
  intro basis s
  have h := sectionCharpoly_equation p basis (q.appTop s)
  refine ⟨h.1, ?_⟩
  have hrp : e.r.appTop.hom.comp p.appTop.hom = RingHom.id _ := by
    ext t
    change (e.r ≫ p).appTop t = t
    rw [e.reflexivity₁]
    rfl
  have hrq : e.r.appTop (q.appTop s) = s := by
    change (e.r ≫ q).appTop s = s
    rw [e.reflexivity₂]
    rfl
  have hz := congrArg e.r.appTop.hom h.2
  change e.r.appTop.hom ((sectionCharpoly p basis (q.appTop s)).eval₂ p.appTop.hom
    (q.appTop s)) = e.r.appTop.hom 0 at hz
  rw [hom_eval₂, hrp, hrq, map_zero] at hz
  exact hz

end FLT.Mazur.AffineRelationCharpoly
