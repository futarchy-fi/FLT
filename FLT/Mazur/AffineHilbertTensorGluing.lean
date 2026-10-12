/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertTensorRestrictions
public import FLT.Mazur.OpenSectionTopComparison

/-!
# Gluing actual localized tensor coefficients

A family in the literal localization rings glues uniquely to a regular
function on the entire original relation exactly when its members agree
under the constructed restriction maps to product-denominator intersections.
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
local instance gluingSourceAlgebra : Algebra R Γ(A.left, ⊤) :=
  affineBaseSectionAlgebra A.hom
/-- The algebra induced by the original translation structural morphism. -/
local instance gluingTranslationAlgebra : Algebra R Γ(V.left, ⊤) :=
  affineBaseSectionAlgebra V.hom


namespace TensorChart
variable (T S : TensorChart f hL d V c k)

/-- Decode literal localized coordinates into sections on the original relation open. -/
def decode : Localization.Away T.denominator →+* Γ((Z).left, T.domain) :=
  T.domain.topIso.hom.hom.comp (sectionsIso f hL d V c k T).inv.hom

/-- Decoding a chart coefficient is injective. -/
theorem decode_injective : Function.Injective (decode f hL d V c k T) :=
  T.domain.topIso.commRingCatIsoToRingEquiv.injective.comp
    (sectionsIso f hL d V c k T).symm.commRingCatIsoToRingEquiv.injective

/-- The localized overlap map is precisely the original sheaf restriction under decoding. -/
theorem decode_restrict (h : S.domain ≤ T.domain) (z : Localization.Away T.denominator) :
    (Z).left.presheaf.map (homOfLE h).op (decode f hL d V c k T z) =
      decode f hL d V c k S (restrict f hL d V c k T S h z) := by
  change (Z).left.presheaf.map (homOfLE h).op
    (T.domain.topIso.hom ((sectionsIso f hL d V c k T).inv z)) = _
  rw [topIso_hom_restriction]
  change S.domain.topIso.hom _ = S.domain.topIso.hom
    ((sectionsIso f hL d V c k S).inv ((sectionsIso f hL d V c k S).hom _))
  rw [Iso.hom_inv_id_apply]
  rfl

/-- Restrict an actual global relation function into one literal localization ring. -/
def globalMap : Γ((Z).left, ⊤) →+* Localization.Away T.denominator :=
  (sectionsIso f hL d V c k T).hom.hom.comp T.domain.ι.appTop.hom

/-- Decoding a global coefficient is exactly the original ambient sheaf restriction. -/
theorem decode_global (z : Γ((Z).left, ⊤)) :
    decode f hL d V c k T (globalMap f hL d V c k T z) =
      (Z).left.presheaf.map (homOfLE (show T.domain ≤ ⊤ from le_top)).op z := by
  change T.domain.topIso.hom
    ((sectionsIso f hL d V c k T).inv ((sectionsIso f hL d V c k T).hom _)) = _
  rw [Iso.hom_inv_id_apply]
  simp only [Scheme.Opens.topIso_hom, Scheme.Opens.ι_appTop,
    ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/-- Actual global coefficients are compatible with every original atlas refinement. -/
theorem restrict_global (h : S.domain ≤ T.domain) (z : Γ((Z).left, ⊤)) :
    restrict f hL d V c k T S h (globalMap f hL d V c k T z) =
      globalMap f hL d V c k S z := by
  change restrict f hL d V c k T S h ((sectionsIso f hL d V c k T).hom _) = _
  rw [restrict_sections]
  change (sectionsIso f hL d V c k S).hom
    (((Z).left.homOfLE h ≫ T.domain.ι).appTop z) = _
  rw [Scheme.homOfLE_ι]
  rfl

/-- Compatible literal localized coefficients glue uniquely on the FULL original relation. -/
theorem existsUnique_global
    (z : (T : TensorChart f hL d V c k) → Localization.Away T.denominator)
    (hz : ∀ T S, restrict f hL d V c k T (inter f hL d V c k T S) inf_le_left (z T) =
      restrict f hL d V c k S (inter f hL d V c k T S) inf_le_right (z S)) :
    ∃! a : Γ((Z).left, ⊤), ∀ T, globalMap f hL d V c k T a = z T := by
  let s := fun T ↦ decode f hL d V c k T (z T)
  have hs : TopCat.Presheaf.IsCompatible (Z).left.presheaf
      (fun T : TensorChart f hL d V c k ↦ T.domain) s := by
    intro T S
    change (Z).left.presheaf.map (homOfLE inf_le_left).op
      (decode f hL d V c k T (z T)) =
        (Z).left.presheaf.map (homOfLE inf_le_right).op (decode f hL d V c k S (z S))
    exact (decode_restrict f hL d V c k T (inter f hL d V c k T S) inf_le_left (z T)).trans
      ((congrArg (decode f hL d V c k (inter f hL d V c k T S)) (hz T S)).trans
        (decode_restrict f hL d V c k S (inter f hL d V c k T S) inf_le_right (z S)).symm)
  obtain ⟨a, ha, hu⟩ := (Z).left.sheaf.existsUnique_gluing'
    (fun T : TensorChart f hL d V c k ↦ T.domain) ⊤ (fun _ ↦ homOfLE le_top)
    (ge_of_eq (iSup_domain f hL d V c k)) s hs
  refine ⟨a, ?_, ?_⟩
  · intro T
    apply decode_injective f hL d V c k T
    rw [decode_global]
    exact ha T
  · intro b hb
    apply hu b
    intro T
    exact (decode_global f hL d V c k T b).symm.trans
      (congrArg (decode f hL d V c k T) (hb T))

end TensorChart
end FLT.Mazur.HilbertChart.AffineRestriction
