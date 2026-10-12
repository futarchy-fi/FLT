/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertTensorAtlas

/-!
# Actual restriction maps between literal tensor localizations

Transport original open restriction through the constructed coordinate
isomorphisms. Identity, composition and tensor formulas hold for these actual
maps. In particular both original endpoint coefficient maps commute with them.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TensorProduct
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve Approximation AffineProductTensorCoordinates
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left] (k : A ⟶ variableHilbertTest f d V)
  [IsOpenImmersion k.left]
local notation "Z" => relation f hL d V c k
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
/-- The algebra induced by the original source structural morphism. -/
local instance restrictionSourceAlgebra : Algebra R Γ(A.left, ⊤) :=
  affineBaseSectionAlgebra A.hom
/-- The algebra induced by the original translation structural morphism. -/
local instance restrictionTranslationAlgebra : Algebra R Γ(V.left, ⊤) :=
  affineBaseSectionAlgebra V.hom


namespace TensorChart
variable (T S Q : TensorChart f hL d V c k)

/-- Restriction along an inclusion of original charts, in literal localization coordinates. -/
def restrict (h : S.domain ≤ T.domain) :
    Localization.Away T.denominator →+* Localization.Away S.denominator :=
  (sectionsIso f hL d V c k S).hom.hom.comp
    (((Z).left.homOfLE h).appTop.hom.comp (sectionsIso f hL d V c k T).inv.hom)

/-- Restriction is the actual geometric pullback after returning to original sections. -/
theorem restrict_sections (h : S.domain ≤ T.domain) (z : Γ(T.domain.toScheme, ⊤)) :
    restrict f hL d V c k T S h ((sectionsIso f hL d V c k T).hom z) =
      (sectionsIso f hL d V c k S).hom (((Z).left.homOfLE h).appTop z) := by
  change (sectionsIso f hL d V c k S).hom
    (((Z).left.homOfLE h).appTop ((sectionsIso f hL d V c k T).inv
      ((sectionsIso f hL d V c k T).hom z))) = _
  rw [Iso.hom_inv_id_apply]

/-- The coordinate restriction of an identity inclusion is the identity ring homomorphism. -/
theorem restrict_self : restrict f hL d V c k T T le_rfl = RingHom.id _ := by
  ext z
  change (sectionsIso f hL d V c k T).hom
    (((Z).left.homOfLE le_rfl).appTop ((sectionsIso f hL d V c k T).inv z)) = z
  rw [Scheme.homOfLE_rfl, Scheme.Hom.id_appTop, CommRingCat.id_apply, Iso.inv_hom_id_apply]

/-- The actual localization restrictions obey the full three-chart cocycle law. -/
theorem restrict_comp (hST : S.domain ≤ T.domain) (hQS : Q.domain ≤ S.domain) :
    (restrict f hL d V c k S Q hQS).comp (restrict f hL d V c k T S hST) =
      restrict f hL d V c k T Q (hQS.trans hST) := by
  ext z
  change (sectionsIso f hL d V c k Q).hom
    (((Z).left.homOfLE hQS).appTop ((sectionsIso f hL d V c k S).inv
      ((sectionsIso f hL d V c k S).hom _))) = _
  rw [Iso.hom_inv_id_apply]
  change (sectionsIso f hL d V c k Q).hom
    (((Z).left.homOfLE hQS ≫ (Z).left.homOfLE hST).appTop _) = _
  rw [Scheme.homOfLE_homOfLE]
  rfl

/-- On every original tensor coefficient the overlap map is literal localization. -/
theorem restrict_tensor (h : S.domain ≤ T.domain)
    (z : Γ(A.left, ⊤) ⊗[R] Γ(V.left, ⊤)) :
    restrict f hL d V c k T S h (algebraMap _ (Localization.Away T.denominator) z) =
      algebraMap _ (Localization.Away S.denominator) z := by
  rw [← principalTensorSectionsIso_tensor f hL d V c k T.denominator T.domain T.image_eq]
  change restrict f hL d V c k T S h ((sectionsIso f hL d V c k T).hom _) = _
  rw [restrict_sections]
  change (sectionsIso f hL d V c k S).hom
    (((Z).left.homOfLE h ≫ T.domain.ι).appTop _) = _
  rw [Scheme.homOfLE_ι]
  exact principalTensorSectionsIso_tensor f hL d V c k S.denominator S.domain S.image_eq z

/-- The original R-algebra structures are preserved by the constructed overlap map. -/
def restrictAlgHom (h : S.domain ≤ T.domain) :
    Localization.Away T.denominator →ₐ[R] Localization.Away S.denominator := by
  refine ⟨restrict f hL d V c k T S h, ?_⟩
  intro r
  change restrict f hL d V c k T S h (algebraMap R _ r) = algebraMap R _ r
  rw [IsScalarTower.algebraMap_apply R (Γ(A.left, ⊤) ⊗[R] Γ(V.left, ⊤)),
    restrict_tensor, ← IsScalarTower.algebraMap_apply]

/-- Original first-endpoint coefficients agree on every atlas refinement. -/
theorem restrict_source (h : S.domain ≤ T.domain) (a : Γ(A.left, ⊤)) :
    restrict f hL d V c k T S h
      (localizedSourceMap f hL d V c k T.denominator T.domain T.image_eq a) =
        localizedSourceMap f hL d V c k S.denominator S.domain S.image_eq a := by
  change restrict f hL d V c k T S h
    ((sectionsIso f hL d V c k T).hom ((T.domain.ι ≫ (p).left).appTop a)) = _
  rw [restrict_sections]
  change (sectionsIso f hL d V c k S).hom
    (((Z).left.homOfLE h ≫ T.domain.ι ≫ (p).left).appTop a) = _
  rw [Scheme.homOfLE_ι_assoc]
  rfl

/-- Original second-endpoint coefficients agree on every atlas refinement. -/
theorem restrict_test (h : S.domain ≤ T.domain) (a : Γ(A.left, ⊤)) :
    restrict f hL d V c k T S h
      (localizedTestMap f hL d V c k T.denominator T.domain T.image_eq a) =
        localizedTestMap f hL d V c k S.denominator S.domain S.image_eq a := by
  rw [localizedTestMap_eq_localization, restrict_tensor, localizedTestMap_eq_localization]

end TensorChart
end FLT.Mazur.HilbertChart.AffineRestriction
