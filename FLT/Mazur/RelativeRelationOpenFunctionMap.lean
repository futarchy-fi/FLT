/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.InvariantOpenRelationMap
public import FLT.Mazur.RelativeRelationInvariantMapSections
public import FLT.Mazur.CanonicalSchemeRelationGround

/-!
# Full restricted function diagrams for maps of orbit sheaves

Every orbit open constructs a geometric diagram with the original source and
relation restricted to their exact inverse images. Its invariant function map
is the actual sheaf map, including the source coefficient ring of certificates.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.RelativeRelationOrbit
open InvariantOpenRelationDiagram SchemeFunctionGroundChange
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme.{0}} {A D B E : Over S} {p q : D ⟶ A} {r s : E ⟶ B}
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
local notation "hU" => pullOpen_preimage_eq e W
local notation "hV" => pullOpen_preimage_eq ec Wc
attribute [local instance] SchemeFunctionGroundChange.sectionAlgebra

/-- The restricted geometric source map on an arbitrary orbit domain. -/
def openSourceMap : source V ⟶ source U := sourceMap u U V hUV

/-- The restricted geometric relation map on the whole inverse-image arrow domain. -/
def openRelationMap : relation r V ⟶ relation p U := relationMap p r u v hp U V hUV

/-- The first endpoint square on the exact orbit-open domains. -/
theorem openMap_fst : openRelationMap e ec u v hp hq W ≫ fst p U =
    fst r V ≫ openSourceMap e ec u v hp hq W := map_fst p r u v hp U V hUV

/-- The second endpoint square on the same complete restricted relations. -/
theorem openMap_snd : openRelationMap e ec u v hp hq W ≫ snd p q U hU =
    snd r s V hV ≫ openSourceMap e ec u v hp hq W :=
  map_snd p q r s u v hp hq U V hU hV hUV

/-- The full function map of the actual open scheme diagram. -/
def openFunctionMap :
    AlgHom.equalizer (sectionMap (fst p U)) (sectionMap (snd p q U hU)) →ₐ[Γ(S, ⊤)]
      AlgHom.equalizer (sectionMap (fst r V)) (sectionMap (snd r s V hV)) :=
  SchemeRelationFunctionDiagram.invariantMap _ _ _ _ (openSourceMap e ec u v hp hq W)
    (openRelationMap e ec u v hp hq W) (openMap_fst e ec u v hp hq W)
    (openMap_snd e ec u v hp hq W)

/-- The constructed geometric map is precisely the original invariant-sheaf pullback. -/
theorem openFunctionMap_natural (a : (invariantSheaf e).obj.obj (op W)) :
    openFunctionMap e ec u v hp hq W (orbitFunctions e W a) =
      orbitFunctions ec Wc ((m).c.app (op W) a) := by
  apply Subtype.ext
  change sectionMap (sourceMap u U V hUV)
      (sourceFunctions U ((invariantInclusion e).hom.app (op W) a)) = _
  rw [sourceMap_function, orbitFunctions_val,
    invariantMap_source_apply e ec u.left v.left hp' hq' W a]

/-- Original sheaf certificates use exactly the constructed restricted source coefficients. -/
theorem openFunctionMap_certified_iff (t : (invariantSheaf ec).obj.obj (op Wc)) :
    orbitFunctions ec Wc t ∈ sourceCertifiedSections
      (openFunctionMap e ec u v hp hq W).toRingHom
      (AlgHom.equalizer (sectionMap (fst r V))
        (sectionMap (snd r s V hV))).val.toRingHom ↔
    t ∈ sourceCertifiedSections ((m).c.app (op W)).hom
      ((invariantInclusion ec).hom.app (op Wc)).hom :=
  SectionLiftCertificateEquiv.certified_iff _ _ _ _
    (orbitFunctions e W) (orbitFunctions ec Wc) (sourceFunctions V)
    (openFunctionMap_natural e ec u v hp hq W) (orbitFunctions_val ec Wc) t

variable [A.left.IsSeparated] [D.left.IsSeparated] [B.left.IsSeparated] [E.left.IsSeparated]
  [CompactSpace (source (pullOpen e W).val).left]
  [CompactSpace (relation p (pullOpen e W).val).left]
  [CompactSpace (source (pullOpen ec ((TopologicalSpace.Opens.map
    (invariantMap e ec u.left v.left (congrArg Over.Hom.left hp)
      (congrArg Over.Hom.left hq)).base).obj W)).val).left]
  [CompactSpace (relation r (pullOpen ec ((TopologicalSpace.Opens.map
    (invariantMap e ec u.left v.left (congrArg Over.Hom.left hp)
      (congrArg Over.Hom.left hq)).base).obj W)).val).left]
  {T : Scheme} [IsAffine T] [IsAffine S] (g : T ⟶ S) [Flat g]
open CanonicalSchemeRelationGround TensorProduct

/-- A section on any orbit domain as an actual function on its geometric ground test. -/
def openGeometricSection (t : (invariantSheaf ec).obj.obj (op Wc)) :
    AlgHom.equalizer (sectionMap (groundMap g (fst r V)))
      (sectionMap (groundMap g (snd r s V hV))) := by
  let _ := FlatGlobalFunctionBaseChange.sectionAlgebra g
  exact CanonicalSchemeRelationGround.invariantsEquiv g (fst r V) (snd r s V hV)
    (1 ⊗ₜ[Γ(S, ⊤)] orbitFunctions ec Wc t)

/-- Actual geometric restriction between the full ground-changed open relations. -/
def openGeometricFunctionMap :
    AlgHom.equalizer (sectionMap (groundMap g (fst p U)))
      (sectionMap (groundMap g (snd p q U hU))) →ₐ[Γ(T, ⊤)]
    AlgHom.equalizer (sectionMap (groundMap g (fst r V)))
      (sectionMap (groundMap g (snd r s V hV))) :=
  CanonicalSchemeRelationGround.invariantMap g (fst p U) (snd p q U hU)
    (fst r V) (snd r s V hV) (openSourceMap e ec u v hp hq W)
    (openRelationMap e ec u v hp hq W) (openMap_fst e ec u v hp hq W)
    (openMap_snd e ec u v hp hq W)

/-- Flat surjective geometric tests detect the original certificate on every orbit domain. -/
theorem openGeometric_certified_iff [Surjective g]
    (t : (invariantSheaf ec).obj.obj (op Wc)) :
    openGeometricSection e ec u v hp hq W g t ∈ sourceCertifiedSections
      (openGeometricFunctionMap e ec u v hp hq W g).toRingHom
      (AlgHom.equalizer (sectionMap (groundMap g (fst r V)))
        (sectionMap (groundMap g (snd r s V hV)))).val.toRingHom ↔
    t ∈ sourceCertifiedSections ((m).c.app (op W)).hom
      ((invariantInclusion ec).hom.app (op Wc)).hom := by
  exact (CanonicalSchemeRelationGround.certified_iff g (fst p U) (snd p q U hU)
    (fst r V) (snd r s V hV) (openSourceMap e ec u v hp hq W)
    (openRelationMap e ec u v hp hq W) (openMap_fst e ec u v hp hq W)
    (openMap_snd e ec u v hp hq W) (orbitFunctions ec Wc t)).trans
      (openFunctionMap_certified_iff e ec u v hp hq W t)

end FLT.Mazur.RelativeRelationOrbit
