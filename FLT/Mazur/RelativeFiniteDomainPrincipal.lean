/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.InvariantFiniteRelationPrincipal
public import FLT.Mazur.InvariantOpenRelationFunctions
public import FLT.Mazur.RelativeRelationInvariantPrincipal

/-!
# Actual invariant-sheaf principal neighborhoods on finite affine domains

Norm scalars on the whole restricted relation are transported back through
the original section equalizer. Their principal opens are actual original
orbit neighborhoods; global finiteness of the ambient relation is unnecessary.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
namespace FLT.Mazur.RelativeRelationOrbit
open InvariantOpenRelationDiagram SchemeOpenEnvelope SchemeFunctionGroundChange
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] SchemeFunctionGroundChange.sectionAlgebra
variable {S : Scheme.{0}} {D A : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q)
  (es : CategoryTheory.EquivalenceRelation p.left q.left)
  [Flat p.left] [LocallyOfFinitePresentation p.left]
  (W : Opens (Orbit e)) (hf : (pullOpen e W).val ≤ finiteTargetOpen p.left)
  (ha : IsAffineOpen (pullOpen e W).val)

include es hf ha in
/-- An affine invariant domain in the exact finite locus has actual sheaf principal coverage. -/
theorem exists_invariantPrincipal_on_finiteOrbit (O : Opens (Orbit e)) (hOW : O ≤ W)
    (x : Orbit e) (hx : x ∈ O) :
    ∃ t : (invariantSheaf e).obj.obj (op W),
      x ∈ invariantPrincipal e W t ∧ invariantPrincipal e W t ≤ O := by
  let U := (pullOpen e W).val
  let hU := pullOpen_preimage_eq e W
  obtain ⟨a, rfl⟩ := projection_surjective e x
  let a' : (source U).left := ⟨a, hOW hx⟩
  obtain ⟨s, hs, has, hsub⟩ := exists_invariantPrincipal_on_finiteDomain p q es U hU hf ha
    (U.ι ⁻¹ᵁ (pullOpen e O).val) a' (by
      intro z hz
      change projection e ((sourceInclusion U).left ((snd p q U hU).left z)) ∈ O
      have hp := congrArg (fun t ↦ t z) (congrArg Over.Hom.left (inclusion_fst p U))
      have hq := congrArg (fun t ↦ t z) (congrArg Over.Hom.left (inclusion_snd p q U hU))
      simp only [Over.comp_left, Scheme.Hom.comp_apply] at hp hq
      rw [← hq, ← projection_pair e ((relationInclusion p U).left z), hp, hz]
      exact hx)
  let s' : AlgHom.equalizer (sectionMap (fst p U)) (sectionMap (snd p q U hU)) := ⟨s, hs⟩
  let t := (orbitFunctions e W).symm s'
  have ht : (orbitFunctions e W t).val = s :=
    congrArg Subtype.val ((orbitFunctions e W).apply_symm_apply s')
  have hv : U.topIso.inv ((invariantInclusion e).hom.app (op W) t) = s := by
    exact ht
  have hb : A.left.basicOpen ((invariantInclusion e).hom.app (op W) t) =
      U.ι ''ᵁ U.toScheme.basicOpen s := by
    rw [← U.ι_image_basicOpen_topIso_inv, hv]
  refine ⟨t, ?_, ?_⟩
  · change a ∈ (pullOpen e (invariantPrincipal e W t)).val
    rw [pullOpen_invariantPrincipal, hb]
    exact ⟨a', has, rfl⟩
  · intro y hy
    obtain ⟨b, rfl⟩ := projection_surjective e y
    change b ∈ (pullOpen e (invariantPrincipal e W t)).val at hy
    rw [pullOpen_invariantPrincipal, hb] at hy
    obtain ⟨b', hb', rfl⟩ := hy
    exact hsub hb'

end FLT.Mazur.RelativeRelationOrbit
