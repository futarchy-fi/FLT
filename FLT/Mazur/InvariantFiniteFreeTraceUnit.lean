/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineFiniteFreeRelationTraceUnit
public import FLT.Mazur.InvariantFiniteDomainTrace

/-!
# Trace unit generation in the original orbit-open invariant sheaf

On an affine finite domain with a global finite basis for the entire original
relation, geometric endpoint spanning and étaleness prove that its constructed
trace ideal is one. The comparison uses the exact original invariant sheaf.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite Module
namespace FLT.Mazur.RelativeRelationOrbit
open InvariantOpenRelationDiagram SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme} [IsAffine S] {A D : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q)
  (W : TopologicalSpace.Opens (Orbit e))
  (es : CategoryTheory.EquivalenceRelation p.left q.left)
  [Etale p.left] [IsSeparated A.hom]
set_option quotPrecheck false
local notation "U" => (pullOpen e W).val
local notation "p₀" => (fst p U).left
local notation "q₀" => (snd p q U (pullOpen_preimage_eq e W)).left
local notation "Ω" => (invariantSheaf e).obj.obj (op W)
variable (hW : IsAffineOpen (pullOpen e W).val)
  (hfin : (pullOpen e W).val ≤ finiteTargetOpen p.left)
  {ι : Type} [Finite ι]
attribute [local irreducible] invariantSheaf orbitFunctions schemeEquivalence

/-- A basis for every original arrow yields a unit trace ideal in the original scalar ring. -/
theorem finiteDomainTraceIdeal_eq_top_of_basis :
    let _ := (fst p (pullOpen e W).val).left.appTop.hom.toAlgebra
    Basis ι Γ((source U).left, ⊤) Γ((relation p U).left, ⊤) →
      Ideal.span (Set.range (finiteDomainTrace e W es hW hfin)) = ⊤ := by
  let _ : IsAffine (source U).left := hW
  let _ := relation_affine_of_le_finiteTarget p U hfin hW
  let _ := fst_finite_of_le_finiteTarget p U hfin
  let _ : Etale p₀ := MorphismProperty.of_isPullback (fst_isPullback p U)
    (inferInstanceAs (Etale p.left))
  let _ : IsSeparated (source U).hom :=
    inferInstanceAs (IsSeparated ((U).ι ≫ A.hom))
  let _ := (p₀).appTop.hom.toAlgebra
  dsimp only
  intro basis
  let hf := (p₀).finite_appTop
  let hp := fst_projective_of_le_finiteTarget p U hfin hW
  let F := FiniteProjectiveAffineNorm.chart p₀ hf hp
  let hF := FiniteProjectiveAffineNorm.chart_basis p₀ hf hp
  let hc := FiniteProjectiveAffineNorm.chart_cover p₀ hf hp
  let er := schemeEquivalence p q es U (pullOpen_preimage_eq e W)
  have hh : p₀ ≫ (source U).hom = q₀ ≫ (source U).hom :=
    (fst p U).w.trans (snd p q U (pullOpen_preimage_eq e W)).w.symm
  have ht := AffineFiniteFreeRelationTraceUnit.invariantTraceIdeal_eq_top
    p₀ q₀ (source U).hom hh er F hF hc basis
  apply (Ideal.map_eq_top_iff (orbitFunctions e W).toRingHom
    (orbitFunctions e W).injective (orbitFunctions e W).finite.to_isIntegral).mp
  rw [Ideal.map_span, ← Set.range_comp]
  have he : (orbitFunctions e W).toRingHom ∘ finiteDomainTrace e W es hW hfin =
      AffineLocallyFreeRelationTrace.invariantTrace p₀ q₀ F hF hc er := by
    funext a
    apply Subtype.ext
    unfold finiteDomainTrace
    exact openInvariantTrace_val e W es F hF hc a
  rw [he]
  exact ht

end FLT.Mazur.RelativeRelationOrbit
