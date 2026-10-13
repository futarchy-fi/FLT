/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFiniteModelImageRelation
public import FLT.Mazur.FinitePrincipalImageCover

/-!
# Finite affine principal models over the actual dense image

Choose finitely many actual finite-model coefficients covering its dense image
interior. Their pullbacks are full original invariant functions. On every patch
the actual original-source projection is affine, surjective and locally finitely
presented. These patches cover the image interior, not the whole Picard sheaf;
flatness and relation-kernel equality are not asserted.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "Q" => finiteKernelModel f hL d V c k
local notation "v" => finiteKernelProjection f hL d V c k
local notation "U" => finiteModelImageInterior f hL d V c k

/-- Noetherianity supplies a finite cover of the dense image open by actual coefficients. -/
theorem finiteModelImage_exists_principal_cover :
    ∃ s : Finset Γ((Q).left, ⊤), (∀ r ∈ s, (Q).left.basicOpen r ≤ U) ∧
      (⨆ r : s, (Q).left.basicOpen r.val) = U := by
  let _ := finiteKernelModel_isNoetherian f hL d V c k
  exact FinitePrincipalImageCover.exists_coefficients U (NoetherianSpace.isCompact _)

/-- A selected finite family of actual global coefficients, not extra model data. -/
def finiteModelPrincipalCoefficients : Finset Γ((Q).left, ⊤) :=
  (finiteModelImage_exists_principal_cover f hL d V c k).choose

local notation "S" => finiteModelPrincipalCoefficients f hL d V c k

/-- Every chosen principal open stays inside the actual source image. -/
theorem finiteModelPrincipalCoefficients_le (r : S) : (Q).left.basicOpen r.val ≤ U :=
  (finiteModelImage_exists_principal_cover f hL d V c k).choose_spec.1 r.val r.property

/-- The finite family covers exactly the constructed dense image interior. -/
theorem finiteModelPrincipalCoefficients_cover : (⨆ r : S, (Q).left.basicOpen r.val) = U :=
  (finiteModelImage_exists_principal_cover f hL d V c k).choose_spec.2

/-- The original invariant denominators cover the entire constructed saturated source open. -/
theorem finiteModelPrincipalSources_cover :
    (⨆ r : S, A.left.basicOpen ((v).left.appTop r.val)) =
      finiteModelImageSourceOpen f hL d V c k := by
  unfold finiteModelImageSourceOpen
  rw [← finiteModelPrincipalCoefficients_cover f hL d V c k, Scheme.Hom.preimage_iSup]
  simp only [Scheme.preimage_basicOpen_top]

variable (r : Γ((finiteKernelModel f hL d V c k).left, ⊤))
  (hr : r ∈ finiteModelPrincipalCoefficients f hL d V c k)

/-- The actual projection above a selected principal target open. -/
def finiteModelPrincipalProjection :
    ((v).left ⁻¹ᵁ (Q).left.basicOpen r).toScheme ⟶ ((Q).left.basicOpen r).toScheme :=
  (v).left ∣_ (Q).left.basicOpen r

local notation "g" => finiteModelPrincipalProjection f hL d V c k r

/-- The selected target is an actual affine open of the finite coefficient model. -/
instance finiteModelPrincipalTarget_isAffine : IsAffine ((Q).left.basicOpen r).toScheme :=
  inferInstanceAs (IsAffine ((Q).left.basicOpen r))

/-- Its complete original-source inverse image is affine as well. -/
instance finiteModelPrincipalSource_isAffine :
    IsAffine ((v).left ⁻¹ᵁ (Q).left.basicOpen r).toScheme := by
  rw [Scheme.preimage_basicOpen_top]
  infer_instance

include hr in
/-- Every chosen affine patch has a surjective actual source projection. -/
theorem finiteModelPrincipalProjection_surjective : Surjective g :=
  FinitePrincipalImageCover.restriction_surjective (v).left _ (fun _ hx ↦
    finiteModelImageInterior_subset_range f hL d V c k
      (finiteModelPrincipalCoefficients_le f hL d V c k ⟨r, hr⟩ hx))

/-- Finite presentation is inherited by the actual principal base change. -/
instance finiteModelPrincipalProjection_locallyOfFinitePresentation :
    LocallyOfFinitePresentation g :=
  MorphismProperty.of_isPullback
    (isPullback_morphismRestrict (v).left ((Q).left.basicOpen r)).flip inferInstance

/-- The complete projection on a principal patch is quasi-compact. -/
instance finiteModelPrincipalProjection_quasiCompact : QuasiCompact g := by
  infer_instance

/-- Each source denominator is invariant under the full original two-endpoint relation. -/
theorem finiteModelPrincipalCoefficient_invariant :
    (v).left.appTop r ∈
      compatibleFunctions (fst f hL d V c k).left (snd f hL d V c k).left := by
  have he : (fst f hL d V c k).left ≫ (v).left =
      (snd f hL d V c k).left ≫ (v).left :=
    congrArg Over.Hom.left (finiteKernelProjection_condition f hL d V c k)
  exact congrArg (fun t ↦ t.appTop r) he

end FLT.Mazur.HilbertChart.AffineRestriction
