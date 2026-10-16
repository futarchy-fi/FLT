/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationGeometricCertificate
public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# Canonical geometric ground changes of full scheme relations

The actual pullback functor constructs source, relation, both endpoint maps,
and their cartesian comparison squares. Under flatness, its full invariant
function algebra is identified with the tensor of the original invariant algebra.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
namespace FLT.Mazur.CanonicalSchemeRelationGround
open SchemeFunctionGroundChange SchemeRelationGeometricGround
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S T : Scheme.{0}} (g : T ⟶ S)

/-- The actual geometric change of ground for an object over the base. -/
abbrev ground (A : Over S) : Over T := (Over.pullback g).obj A

/-- The projection to the unchanged original source or relation scheme. -/
def projection (A : Over S) : (ground g A).left ⟶ A.left := pullback.fst A.hom g

/-- The structural diagram of the canonical ground change is cartesian. -/
theorem square (A : Over S) :
    IsPullback (projection g A) (ground g A).hom A.hom g := IsPullback.of_hasPullback _ _

/-- Every source, relation, or boundary map has its canonical geometric base change. -/
abbrev groundMap {A B : Over S} (a : A ⟶ B) : ground g A ⟶ ground g B :=
  (Over.pullback g).map a

/-- The canonical projections commute with every original geometric morphism. -/
theorem projection_natural {A B : Over S} (a : A ⟶ B) :
    (groundMap g a).left ≫ projection g B = projection g A ≫ a.left := by
  simp [groundMap, projection, Over.pullback_map_left]

variable {A D : Over S} (p q : D ⟶ A)
attribute [local instance] SchemeFunctionGroundChange.sectionAlgebra

variable [CompactSpace A.left] [A.left.IsSeparated]
  [CompactSpace D.left] [D.left.IsSeparated] [IsAffine T] [IsAffine S] [Flat g]

/-- Actual canonical ground-change invariants, with both endpoint squares constructed. -/
def invariantsEquiv :
    let _ := FlatGlobalFunctionBaseChange.sectionAlgebra g
    Γ(T, ⊤) ⊗[Γ(S, ⊤)] AlgHom.equalizer (sectionMap p) (sectionMap q) ≃ₐ[Γ(T, ⊤)]
      AlgHom.equalizer (sectionMap (groundMap g p)) (sectionMap (groundMap g q)) :=
  SchemeRelationGeometricGround.invariantsEquiv g (square g A) (square g D)
    p q (groundMap g p) (groundMap g q)
    (projection_natural g p).symm (projection_natural g q).symm

/-- Canonical invariant comparison keeps exactly the original projection on functions. -/
theorem invariantsEquiv_tmul (b : Γ(T, ⊤))
    (a : AlgHom.equalizer (sectionMap p) (sectionMap q)) :
    let _ := FlatGlobalFunctionBaseChange.sectionAlgebra g
    (invariantsEquiv g p q (b ⊗ₜ[Γ(S, ⊤)] a)).val =
      (ground g A).hom.appTop b * (projection g A).appTop a.val := rfl

/-- Every invariant function on the actual ground-changed relation has tensor coordinates. -/
theorem exists_invariant_tensor
    (a : AlgHom.equalizer (sectionMap (groundMap g p)) (sectionMap (groundMap g q))) :
    let _ := FlatGlobalFunctionBaseChange.sectionAlgebra g
    ∃ t : Γ(T, ⊤) ⊗[Γ(S, ⊤)] AlgHom.equalizer (sectionMap p) (sectionMap q),
      invariantsEquiv g p q t = a := (invariantsEquiv g p q).surjective a

variable {B E : Over S} (r s : E ⟶ B) (u : B ⟶ A) (v : E ⟶ D)
  (hp : v ≫ p = r ≫ u) (hq : v ≫ q = s ≫ u)

include hp in
omit [CompactSpace A.left] [A.left.IsSeparated] [CompactSpace D.left]
  [D.left.IsSeparated] [IsAffine T] [IsAffine S] [Flat g] in
/-- The actual ground-change functor constructs every boundary endpoint square. -/
theorem groundMap_square :
    groundMap g v ≫ groundMap g p = groundMap g r ≫ groundMap g u := by
  simp only [groundMap, ← Functor.map_comp, hp]

/-- Restriction on the actual canonical ground-changed invariant function rings. -/
def invariantMap :
    AlgHom.equalizer (sectionMap (groundMap g p)) (sectionMap (groundMap g q)) →ₐ[Γ(T, ⊤)]
      AlgHom.equalizer (sectionMap (groundMap g r)) (sectionMap (groundMap g s)) :=
  SchemeRelationFunctionDiagram.invariantMap _ _ _ _ (groundMap g u) (groundMap g v)
    (groundMap_square g p r u v hp) (groundMap_square g q s u v hq)

variable [CompactSpace B.left] [B.left.IsSeparated]
  [CompactSpace E.left] [E.left.IsSeparated] [Surjective g]

/-- A geometric flat surjective test detects precisely the original source certificate. -/
theorem certified_iff (t : AlgHom.equalizer (sectionMap r) (sectionMap s)) :
    let _ := FlatGlobalFunctionBaseChange.sectionAlgebra g
    invariantsEquiv g r s (1 ⊗ₜ[Γ(S, ⊤)] t) ∈ sourceCertifiedSections
      (invariantMap g p q r s u v hp hq).toRingHom
      (AlgHom.equalizer (sectionMap (groundMap g r))
        (sectionMap (groundMap g s))).val.toRingHom ↔
    t ∈ sourceCertifiedSections
      (SchemeRelationFunctionDiagram.invariantMap p q r s u v hp hq).toRingHom
      (AlgHom.equalizer (sectionMap r) (sectionMap s)).val.toRingHom := by
  let _ := FlatGlobalFunctionBaseChange.sectionAlgebra g
  have hf : Module.FaithfullyFlat Γ(S, ⊤) Γ(T, ⊤) :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine g).mp
      ⟨inferInstance, inferInstance⟩
  exact SchemeRelationGeometricCertificate.certified_iff g
    (square g A) (square g D) (square g B) (square g E)
    p q r s (groundMap g p) (groundMap g q) (groundMap g r) (groundMap g s)
    (projection_natural g p).symm (projection_natural g q).symm
    (projection_natural g r).symm (projection_natural g s).symm
    u v (groundMap g u) (groundMap g v) hp hq
    (groundMap_square g p r u v hp) (groundMap_square g q s u v hq)
    (projection_natural g u) hf t

end FLT.Mazur.CanonicalSchemeRelationGround
