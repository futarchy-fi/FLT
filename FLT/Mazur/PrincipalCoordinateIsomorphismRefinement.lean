/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalFamilyIsomorphismRefinement
public import FLT.Mazur.PrincipalIsomorphismSourceExtension

/-!
# Commuting isomorphism refinements of a single coordinate stage

The singleton incoming-family construction supplies an isomorphic refinement
of any chosen lift. Once bijective, its source may be enlarged to any specified
relation set while preserving bijectivity and the old coordinate square.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteTypeRelationModel

universe u

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra.FiniteType R A] [Algebra.FiniteType R B]
  {a : A} {b : B} {f : Localization.Away a →ₐ[R] Localization.Away b}

/-- An arbitrary coordinate lift of a bijection has a commuting bijective refinement. -/
theorem exists_principalMapStage_bijective (hf : Function.Bijective f)
    (x : PrincipalMapStage a b f) :
    ∃ y : PrincipalMapStage a b f, x ≤ y ∧ Function.Bijective y.hom := by
  let z : PrincipalFamilyStage (fun _ : Unit ↦ a) b (fun _ ↦ f) :=
    ⟨fun _ ↦ x.source, x.target, fun _ ↦ x.hom, fun _ ↦ x.fac⟩
  obtain ⟨w, hzw, hw⟩ := exists_principalFamily_bijective (fun _ ↦ hf) z
  obtain ⟨hs, ht, hc⟩ := hzw
  exact ⟨⟨w.source (), w.target, w.hom (), w.fac ()⟩,
    ⟨hs (), ht, hc ()⟩, hw ()⟩

/-- An isomorphic lift extends to exactly any prescribed larger source relation set. -/
theorem exists_principalMapStage_bijective_source_extension
    (e : Localization.Away a ≃ₐ[R] Localization.Away b)
    (x : PrincipalMapStage a b e.toAlgHom) (hx : Function.Bijective x.hom)
    (s : Finset (relationIdeal R A)) (hs : x.source ≤ s) :
    ∃ y : PrincipalMapStage a b e.toAlgHom,
      x ≤ y ∧ y.source = s ∧ Function.Bijective y.hom := by
  obtain ⟨t, ht, d, hd, hfac⟩ := exists_principal_equiv_source_extension e
    (AlgEquiv.ofBijective x.hom hx) x.fac hs
  exact ⟨⟨s, t, d.toAlgHom, hfac⟩, ⟨hs, ht, hd⟩, rfl, d.bijective⟩

end FLT.Mazur.FiniteTypeRelationModel
