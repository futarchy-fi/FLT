/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationOpenSelectorGround

/-!
# Original orbits in the glued selector fibers

Equality of glued points forces an original relation arrow. This topological
fact will only be used to lift morphisms into open charts; the scheme kernel
is recovered separately on arbitrary, possibly nonreduced, scheme tests.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationOpenSelector
open RelativeRelationOrbit
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme.{u}} {D A : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q) [Etale q.left]

/-- Equal glued images of original chart points lie in the same original orbit. -/
theorem related_of_sourceMap_eq {U V : Chart p q}
    (x : U.val.val.toScheme) (y : V.val.val.toScheme)
    (h : sourceMap e U x = sourceMap e V y) : Related p q x.val y.val := by
  obtain ⟨W, hU, hV, z, hzU, hzV⟩ :=
    (chartMap_eq_iff e ((selector p q U).projection x)
      ((selector p q V).projection y)).mp h
  obtain ⟨w, rfl⟩ := (selector p q W).projection.surjective z
  rw [transition_projection] at hzU hzV
  have hu := (selector p q U).related_of_projection_eq e
    (A.left.homOfLE hU w) x hzU
  have hv := (selector p q V).related_of_projection_eq e
    (A.left.homOfLE hV w) y hzV
  have hwU : U.val.val.ι (A.left.homOfLE hU w) = w.val :=
    congrArg (fun a ↦ a w) (Scheme.homOfLE_ι A.left hU)
  have hwV : V.val.val.ι (A.left.homOfLE hV w) = w.val :=
    congrArg (fun a ↦ a w) (Scheme.homOfLE_ι A.left hV)
  rw [hwU] at hu
  rw [hwV] at hv
  exact related_trans e (related_symm e hu) hv

omit [Etale q.left] in
/-- Each glued source point is an actual point of one original chart. -/
theorem exists_source_chart (x : (sourceOpen (p := p) (q := q)).toScheme) :
    ∃ (U : Chart p q) (z : U.val.val.toScheme),
      openImageUnionMap (fun V : Chart p q ↦ V.val.val.ι) U z = x :=
  (openImageUnionCover (fun U : Chart p q ↦ U.val.val.ι)).exists_eq x

/-- The full original point relation detects equality in an assembled projection fiber. -/
theorem related_of_projection_eq
    (x y : (sourceOpen (p := p) (q := q)).toScheme)
    (h : projection e x = projection e y) : Related p q x.val y.val := by
  obtain ⟨U, z, rfl⟩ := exists_source_chart x
  obtain ⟨V, w, rfl⟩ := exists_source_chart y
  have hz := congrArg (fun a ↦ a z) (chart_projection e U)
  have hw := congrArg (fun a ↦ a w) (chart_projection e V)
  have hr := related_of_sourceMap_eq e z w (hz.symm.trans (h.trans hw))
  have hz' := congrArg (fun a ↦ a z)
    (openImageUnionMap_fac (fun T : Chart p q ↦ T.val.val.ι) U)
  have hw' := congrArg (fun a ↦ a w)
    (openImageUnionMap_fac (fun T : Chart p q ↦ T.val.val.ι) V)
  change (openImageUnionMap (fun T : Chart p q ↦ T.val.val.ι) U z).val = z.val at hz'
  change (openImageUnionMap (fun T : Chart p q ↦ T.val.val.ι) V w).val = w.val at hw'
  rw [hz', hw']
  exact hr

/-- An invariant original chart contains an entire assembled projection fiber. -/
theorem mem_chart_of_projection_eq (U : Chart p q)
    (x y : (sourceOpen (p := p) (q := q)).toScheme)
    (h : projection e x = projection e y) (hx : x.val ∈ U.val.val) :
    y.val ∈ U.val.val :=
  (invariant_mem_iff U.val (related_of_projection_eq e x y h)).mp hx

end FLT.Mazur.SchemeRelationOpenSelector
