/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationOpenFunctionMap
public import FLT.Mazur.RelativeRelationClosedSections
public import FLT.Mazur.AffineNormCartesianCharts

/-!
# Cartesian full relations on the exact orbit-open domains

An ambient cartesian first-endpoint square stays cartesian on the original
orbit opens. Closed source restriction is surjective in these actual scheme
coordinates whenever the original source domain is affine.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.RelativeRelationOrbit
open InvariantOpenRelationDiagram SchemeFunctionGroundChange
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme} {A D B E : Over S} {p q : D ⟶ A} {r s : E ⟶ B}
  (e : CategoryTheory.EquivalenceRelation p q) (ec : CategoryTheory.EquivalenceRelation r s)
  (u : B ⟶ A) (v : E ⟶ D) (hp : v ≫ p = r ≫ u) (hq : v ≫ q = s ≫ u)
  (W : TopologicalSpace.Opens (Orbit e))
set_option quotPrecheck false
local notation "hp'" => congrArg Over.Hom.left hp
local notation "hq'" => congrArg Over.Hom.left hq
local notation "m" => invariantMap e ec u.left v.left hp' hq'
local notation "Wc" => (TopologicalSpace.Opens.map (m).base).obj W
local notation "U" => (pullOpen e W).val
local notation "V" => (pullOpen ec Wc).val
local notation "hUV" => invariantMap_sourceOpen_le e ec u.left v.left hp' hq' W

/-- Restriction retains the entire cartesian relation over the original orbit domain. -/
theorem openMap_isPullback (H : IsPullback v.left r.left p.left u.left) :
    IsPullback (openRelationMap e ec u v hp hq W).left (fst r V).left
      (fst p U).left (openSourceMap e ec u v hp hq W).left := by
  have hd := relationMap_domain p r u v hp U V hUV
  change IsPullback (v.left.resLE _ _ hd) (r.left.resLE _ _ le_rfl)
    (p.left.resLE _ _ le_rfl) (u.left.resLE _ _ hUV)
  exact Scheme.Hom.isPullback_resLE H hUV le_rfl (inf_eq_right.mpr hd).symm

attribute [local instance] sectionAlgebra

/-- The actual open scheme source map lifts all boundary source functions. -/
theorem openSourceMap_surjective [IsClosedImmersion u.left] (hW : IsAffineOpen U) :
    Function.Surjective (openSourceMap e ec u v hp hq W).left.appTop := by
  intro t
  obtain ⟨a, ha⟩ := closedSourceRestriction_surjective e ec u.left v.left hp' hq' W hW
    ((sourceFunctions V).symm t)
  refine ⟨sourceFunctions U a, ?_⟩
  change sectionMap (sourceMap u U V hUV) (sourceFunctions U a) = t
  rw [sourceMap_function]
  change sourceFunctions V (closedSourceRestriction e ec u.left v.left hp' hq' W a) = t
  rw [ha, RingEquiv.apply_symm_apply]

end FLT.Mazur.RelativeRelationOrbit
