/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.InvariantAffineOpenNormCoefficient
public import FLT.Mazur.InvariantOpenCoefficientGluing
public import FLT.Mazur.FiniteRelationAffinePrincipalCore

/-!
# Global invariant norms from actual affine invariant covers

Compatible local finite-flat norms glue on the original nonaffine source.
Their principal opens are exactly the whole-orbit cores. The cover provides
no partition of unity in global functions; no such assertion is used here.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.InvariantAffineCoverNorm
open SchemeEffectiveEpiSections InvariantOpenCoefficientRestriction
open InvariantAffineOpenNormCoefficient
set_option backward.isDefEq.respectTransparency false
variable {D X : Scheme.{0}} (p q : D ⟶ X)
  [IsFinite p] [Flat p] [LocallyOfFinitePresentation p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {ι : Type} (U : ι → X.Opens) (hU : ∀ j, p ⁻¹ᵁ U j = q ⁻¹ᵁ U j)
  (haU : ∀ j, IsAffineOpen (U j))
  (haUV : ∀ j l, IsAffineOpen (U j ⊓ U l)) (hcover : iSup U = ⊤)

include haUV hcover in
/-- The full local norms construct a unique original global invariant coefficient. -/
theorem existsUnique_coefficient (a : Γ(X, ⊤)) :
    ∃! t : compatibleFunctions p q, ∀ j, (U j).ι.appTop t.val =
      (coefficient p q e (U j) (hU j) (haU j) a).val := by
  apply InvariantOpenCoefficientGluing.existsUnique_invariant p q U hU hcover
  intro j l
  rw [coefficient_restrict p q e (U j) (hU j) (haU j) (U j ⊓ U l)
      (inf_invariant p q (U j) (U l) (hU j) (hU l)) (haUV j l) inf_le_left,
    coefficient_restrict p q e (U l) (hU l) (haU l) (U j ⊓ U l)
      (inf_invariant p q (U j) (U l) (hU j) (hU l)) (haUV j l) inf_le_right]

/-- A global invariant scalar, without affineness of the original source. -/
def globalCoefficient (a : Γ(X, ⊤)) : compatibleFunctions p q :=
  (existsUnique_coefficient p q e U hU haU haUV hcover a).choose

/-- The global scalar retains each actual local finite-flat norm. -/
theorem globalCoefficient_restrict (a : Γ(X, ⊤)) (j : ι) :
    (U j).ι.appTop (globalCoefficient p q e U hU haU haUV hcover a).val =
      (coefficient p q e (U j) (hU j) (haU j) a).val :=
  (existsUnique_coefficient p q e U hU haU haUV hcover a).choose_spec.1 j

/-- The global principal locus tests every original arrow over a point. -/
theorem mem_basicOpen_globalCoefficient (a : Γ(X, ⊤)) (x : X) :
    x ∈ X.basicOpen (globalCoefficient p q e U hU haU haUV hcover a).val ↔
      ∀ z : D, p z = x → q z ∈ X.basicOpen a := by
  obtain ⟨j, hx⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (show x ∈ iSup U from hcover.symm ▸ trivial)
  let y : (U j).toScheme := ⟨x, hx⟩
  have he := mem_basicOpen_coefficient p q e (U j) (hU j) (haU j) a y
  rw [← globalCoefficient_restrict p q e U hU haU haUV hcover a j,
    ← Scheme.preimage_basicOpen_top] at he
  exact he

/-- Actual affine cores become principal opens of global full invariant scalars. -/
theorem basicOpen_globalCoefficient (a : Γ(X, ⊤)) (ha : IsAffineOpen (X.basicOpen a)) :
    X.basicOpen (globalCoefficient p q e U hU haU haUV hcover a).val =
      FiniteRelationAffinePrincipalCore.core (p := p) (q := q) a ha := by
  ext x
  exact (mem_basicOpen_globalCoefficient p q e U hU haU haUV hcover a x).trans
    (FiniteRelationAffinePrincipalCore.mem_core_iff e a ha x).symm

end FLT.Mazur.InvariantAffineCoverNorm
