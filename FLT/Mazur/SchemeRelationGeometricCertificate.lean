/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationGeometricGround
public import FLT.Mazur.SchemeRelationFunctionDiagram
public import FLT.Mazur.GroundFlatEqualizerCertificate

/-!
# Descent of certificates tested on geometric ground changes

The full tensor comparison commutes with restriction between two geometric
relations. Faithful flatness therefore descends a certificate from the actual
geometric source and relation rings to a finite identity on the original source.
The existence of the tested certificate is a separate geometric problem.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
namespace FLT.Mazur.SchemeRelationGeometricCertificate
open SchemeFunctionGroundChange SchemeRelationGeometricGround SchemeRelationFunctionDiagram
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S T : Scheme.{0}} (g : T ⟶ S)
  {A D B E : Over S} {A' D' B' E' : Over T}
  {i : A'.left ⟶ A.left} {z : D'.left ⟶ D.left}
  {j : B'.left ⟶ B.left} {w : E'.left ⟶ E.left}
  (hA : IsPullback i A'.hom A.hom g) (hD : IsPullback z D'.hom D.hom g)
  (hB : IsPullback j B'.hom B.hom g) (hE : IsPullback w E'.hom E.hom g)
  (p q : D ⟶ A) (r s : E ⟶ B) (p' q' : D' ⟶ A') (r' s' : E' ⟶ B')
  (hi : z ≫ p.left = p'.left ≫ i) (hz : z ≫ q.left = q'.left ≫ i)
  (hj : w ≫ r.left = r'.left ≫ j) (hw : w ≫ s.left = s'.left ≫ j)
  (u : B ⟶ A) (v : E ⟶ D) (u' : B' ⟶ A') (v' : E' ⟶ D')
  (hp : v ≫ p = r ≫ u) (hq : v ≫ q = s ≫ u)
  (hp' : v' ≫ p' = r' ≫ u') (hq' : v' ≫ q' = s' ≫ u')
  (hu : u'.left ≫ i = j ≫ u.left)
  [CompactSpace A.left] [A.left.IsSeparated] [CompactSpace D.left] [D.left.IsSeparated]
  [CompactSpace B.left] [B.left.IsSeparated] [CompactSpace E.left] [E.left.IsSeparated]
  [IsAffine T] [IsAffine S] [Flat g]

attribute [local instance] SchemeFunctionGroundChange.sectionAlgebra
local notation "f" => invariantMap p q r s u v hp hq
local notation "f'" => invariantMap p' q' r' s' u' v' hp' hq'
local notation "ea" => tensorEquiv g hA hD p q p' q' hi hz
local notation "eb" => tensorEquiv g hB hE r s r' s' hj hw

include hu hA hD hi hz in
/-- Geometric restriction agrees with restriction of the complete tensor relation equations. -/
theorem tensorEquiv_natural :
    let _ := FlatGlobalFunctionBaseChange.sectionAlgebra g
    ∀ a : AlgHom.equalizer (FlatAlgebraEqualizer.tensorMap Γ(T, ⊤) (sectionMap p))
      (FlatAlgebraEqualizer.tensorMap Γ(T, ⊤) (sectionMap q)),
      f' (ea a) = eb (tensorInvariantMap p q r s u v hp hq Γ(T, ⊤) a) := by
  let _ := FlatGlobalFunctionBaseChange.sectionAlgebra g
  dsimp only
  intro a
  apply Subtype.ext
  exact (comparison_natural g hB hA u u' hu a.val).symm

include hu hA hD hi hz in
/-- Certification in actual geometric function rings is exactly tensor certification. -/
theorem geometric_certified_iff :
    let _ := FlatGlobalFunctionBaseChange.sectionAlgebra g
    ∀ t : AlgHom.equalizer (FlatAlgebraEqualizer.tensorMap Γ(T, ⊤) (sectionMap r))
      (FlatAlgebraEqualizer.tensorMap Γ(T, ⊤) (sectionMap s)),
      eb t ∈ sourceCertifiedSections (f').toRingHom
        (AlgHom.equalizer (sectionMap r') (sectionMap s')).val.toRingHom ↔
      t ∈ sourceCertifiedSections
        (tensorInvariantMap p q r s u v hp hq Γ(T, ⊤)).toRingHom
        (AlgHom.equalizer (FlatAlgebraEqualizer.tensorMap Γ(T, ⊤) (sectionMap r))
          (FlatAlgebraEqualizer.tensorMap Γ(T, ⊤) (sectionMap s))).val.toRingHom := by
  let _ := FlatGlobalFunctionBaseChange.sectionAlgebra g
  dsimp only
  intro t
  exact SectionLiftCertificateEquiv.certified_iff _ _ _ _
    (ea).toRingEquiv (eb).toRingEquiv (sectionsEquiv g hB).toRingEquiv
    (tensorEquiv_natural g hA hD hB hE p q r s p' q' r' s' hi hz hj hw
      u v u' v' hp hq hp' hq' hu) (fun _ ↦ rfl) t

include hu hA hD hi hz in
/-- Faithful flatness detects original certification using actual geometric relation sections. -/
theorem certified_iff
    (hfaith : let _ := FlatGlobalFunctionBaseChange.sectionAlgebra g
      Module.FaithfullyFlat Γ(S, ⊤) Γ(T, ⊤))
    (t : AlgHom.equalizer (sectionMap r) (sectionMap s)) :
    let _ := FlatGlobalFunctionBaseChange.sectionAlgebra g
    invariantsEquiv g hB hE r s r' s' hj hw (1 ⊗ₜ[Γ(S, ⊤)] t) ∈
      sourceCertifiedSections (f').toRingHom
        (AlgHom.equalizer (sectionMap r') (sectionMap s')).val.toRingHom ↔
      t ∈ sourceCertifiedSections (f).toRingHom
        (AlgHom.equalizer (sectionMap r) (sectionMap s)).val.toRingHom := by
  let _ := FlatGlobalFunctionBaseChange.sectionAlgebra g
  let _ := hfaith
  exact (geometric_certified_iff g hA hD hB hE p q r s p' q' r' s' hi hz hj hw
    u v u' v' hp hq hp' hq' hu _).trans
      (GroundFlatEqualizerCertificate.certified_iff (sectionMap p) (sectionMap q)
        (sectionMap r) (sectionMap s) (sectionMap u) (sectionMap v)
        (SchemeRelationFunctionDiagram.endpoint_square p r u v hp)
        (SchemeRelationFunctionDiagram.endpoint_square q s u v hq) Γ(T, ⊤) t)

include hu hA hD hi hz in
/-- A geometric test certificate constructs an actual finite identity on the original source. -/
theorem certificate_descends
    (hfaith : let _ := FlatGlobalFunctionBaseChange.sectionAlgebra g
      Module.FaithfullyFlat Γ(S, ⊤) Γ(T, ⊤))
    (t : AlgHom.equalizer (sectionMap r) (sectionMap s))
    (ht : let _ := FlatGlobalFunctionBaseChange.sectionAlgebra g
      invariantsEquiv g hB hE r s r' s' hj hw (1 ⊗ₜ[Γ(S, ⊤)] t) ∈
        sourceCertifiedSections (f').toRingHom
          (AlgHom.equalizer (sectionMap r') (sectionMap s')).val.toRingHom) :
    ∃ c : sectionLiftIdeal (f).toRingHom t →₀ Γ(B.left, ⊤),
      c.sum (fun a b ↦ b * (f a.val).val) = 1 :=
  (mem_sourceCertifiedSections_iff (f).toRingHom
    (AlgHom.equalizer (sectionMap r) (sectionMap s)).val.toRingHom t).mp
      ((certified_iff g hA hD hB hE p q r s p' q' r' s' hi hz hj hw
        u v u' v' hp hq hp' hq' hu hfaith t).mp ht)

end FLT.Mazur.SchemeRelationGeometricCertificate
