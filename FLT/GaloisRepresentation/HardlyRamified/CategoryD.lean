/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.GlobalModel
public import FLT.GroupScheme.RaynaudExtension
public import Mathlib.FieldTheory.Galois.Infinite

/-!
# Finite-flat objects in category D

An object retains its finite-flat Hopf algebra and its full geometric point action.
Category D imposes three-primary order and square-zero inertia at two. The point
field is the fixed field of the kernel of that full action.
-/

@[expose] public noncomputable section

attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion

namespace ThreeAdicPlan

/-- A finite flat commutative model over `R`, together with its rational geometric points. -/
structure FiniteFlatObject (R : Type) [CommRing R] [Algebra R ℚ] where
  /-- The finite continuous Galois module of geometric points. -/
  points : FiniteContinuousGaloisModule
  /-- The coordinate Hopf algebra and its equivariant generic point comparison. -/
  model : HasFiniteFlatModel R points

/-- View an existing model over `ℤ[1/2]` as a finite-flat object. -/
def FiniteFlatObject.ofModel {W : FiniteContinuousGaloisModule}
    (M : ModelOverZInvTwo W) : FiniteFlatObject ZInvTwo :=
  ⟨W, M.toHasFiniteFlatModel⟩

/-- Forget the bundled point-module record to obtain the finite-flat model used by R1. -/
def FiniteFlatObject.toFF {R : Type} [CommRing R] [Algebra R ℚ]
    (H : FiniteFlatObject R) : FF R ℚ where
  CoordinateRing := H.model.CoordinateRing
  Points := H.points
  points := H.model.points
  points_bijective := H.model.points_bijective

/-- Package an R1 model over a rational fraction-field base as a finite-flat object.
The coordinate algebra and point comparison are preserved. -/
def FF.toFiniteFlatObject {R : Type} [CommRing R] [Algebra R ℚ] [IsFractionRing R ℚ]
    (H : FF R ℚ) : FiniteFlatObject R where
  points := { Carrier := H.Points }
  model :=
    { CoordinateRing := H.CoordinateRing
      cocomm := cocomm_of_injective_points H.points.toAddMonoidHom H.points_bijective.1
      points := H.points
      points_bijective := H.points_bijective }

/-- Multiplication by `n` vanishes on all geometric points. -/
def KilledByQ {R : Type} [CommRing R] [Algebra R ℚ] (n : ℕ) (H : FiniteFlatObject R) : Prop :=
  ∀ w : H.points, n • w = 0

/-- A subgroup of points is preserved by every rational Galois automorphism. -/
def GaloisStable (W : FiniteContinuousGaloisModule) (A : AddSubgroup W) : Prop :=
  ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (w : W), w ∈ A → σ • w ∈ A

/-- A nonzero finite-flat object with no nonzero proper Galois-stable point subgroup.
Over the Dedekind base, these are precisely the subobjects obtained by schematic closure. -/
def Simple {R : Type} [CommRing R] [Algebra R ℚ] (H : FiniteFlatObject R) : Prop :=
  Nontrivial H.points ∧ ∀ A : AddSubgroup H.points, GaloisStable H.points A → A = ⊥ ∨ A = ⊤

/-- Three-primary finite-flat models whose inertia at two acts with square-zero difference
from the identity on the full point group. -/
structure InCategoryD (H : FiniteFlatObject ZInvTwo) : Prop where
  /-- The order of the point group is a power of three. -/
  threePrimary : ∃ n : ℕ, Nat.card H.points = 3 ^ n
  /-- For each inertia element, `(σ - 1)²` vanishes pointwise. -/
  inertiaSquareZero : ∀ σ ∈ localInertiaGroup
    Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat, ∀ w : H.points,
    let τ := Field.absoluteGaloisGroup.map (algebraMap ℚ
      (Nat.prime_two.toHeightOneSpectrumRingOfIntegersRat.adicCompletion ℚ)) σ
    τ • (τ • w - w) - (τ • w - w) = 0

/-- A category-D model with a prescribed geometric Galois module. -/
structure DModel (W : FiniteContinuousGaloisModule) extends ModelOverZInvTwo W where
  /-- The chosen model satisfies the category-D conditions. -/
  inCategoryD : InCategoryD (FiniteFlatObject.ofModel toModelOverZInvTwo)

namespace FiniteContinuousGaloisModule

/-- The componentwise product of finite continuous Galois modules. -/
def prod (W V : FiniteContinuousGaloisModule) : FiniteContinuousGaloisModule :=
  { Carrier := W × V }

/-- The kernel of the action on every point, without choosing a constituent or quotient. -/
def pointActionKernel (W : FiniteContinuousGaloisModule) :
    Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
  (MulAction.toPermHom _ W).ker

/-- Membership in the full point-action kernel means fixing every point. -/
theorem mem_pointActionKernel (W : FiniteContinuousGaloisModule)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    σ ∈ W.pointActionKernel ↔ ∀ w : W, σ • w = w := by
  change MulAction.toPermHom _ W σ = 1 ↔ _
  exact Equiv.ext_iff

/-- A finite continuous point action has open kernel. -/
theorem pointActionKernel_isOpen (W : FiniteContinuousGaloisModule) :
    IsOpen (W.pointActionKernel : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) := by
  have he : (W.pointActionKernel : Set _) =
      ⋂ w : W, {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ | σ • w = w} := by
    ext σ
    simp [mem_pointActionKernel]
  rw [he]
  exact isOpen_iInter_of_finite fun w ↦ ContinuousSMulDiscrete.isOpen_smul_eq _ w w

/-- The full point-action kernel as a closed subgroup. -/
def closedPointActionKernel (W : FiniteContinuousGaloisModule) :
    ClosedSubgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
  ⟨W.pointActionKernel, W.pointActionKernel.isClosed_of_isOpen W.pointActionKernel_isOpen⟩

instance (W : FiniteContinuousGaloisModule) : W.pointActionKernel.Normal :=
  inferInstanceAs (MulAction.toPermHom _ W).ker.Normal

/-- The intermediate field fixed by the kernel of the full point action. -/
def pointField (W : FiniteContinuousGaloisModule) : IntermediateField ℚ (AlgebraicClosure ℚ) :=
  IntermediateField.fixedField W.pointActionKernel

/-- The point field cuts out exactly the kernel of the full point action. -/
theorem pointField_fixingSubgroup (W : FiniteContinuousGaloisModule) :
    W.pointField.fixingSubgroup = W.pointActionKernel :=
  InfiniteGalois.fixingSubgroup_fixedField W.closedPointActionKernel

instance (W : FiniteContinuousGaloisModule) : FiniteDimensional ℚ W.pointField := by
  apply (InfiniteGalois.isOpen_iff_finite W.pointField).mp
  rw [pointField_fixingSubgroup]
  exact W.pointActionKernel_isOpen

instance (W : FiniteContinuousGaloisModule) : IsGalois ℚ W.pointField := by
  unfold pointField
  infer_instance

instance (W : FiniteContinuousGaloisModule) : NumberField W.pointField where
  to_finiteDimensional := inferInstance

/-- A product action is trivial exactly when both factor actions are trivial. -/
theorem pointActionKernel_prod (W V : FiniteContinuousGaloisModule) :
    (W.prod V).pointActionKernel = W.pointActionKernel ⊓ V.pointActionKernel := by
  ext σ
  simp only [Subgroup.mem_inf, mem_pointActionKernel]
  constructor
  · intro h
    exact ⟨fun w ↦ congrArg Prod.fst (h (w, 0)),
      fun v ↦ congrArg Prod.snd (h (0, v))⟩
  · rintro ⟨hW, hV⟩ ⟨w, v⟩
    exact Prod.ext (hW w) (hV v)

/-- The product point field contains the point field of its first factor. -/
theorem pointField_le_prod_left (W V : FiniteContinuousGaloisModule) :
    W.pointField ≤ (W.prod V).pointField := by
  apply IntermediateField.fixedField_le
  rw [pointActionKernel_prod]
  exact inf_le_left

/-- The product point field contains the point field of its second factor. -/
theorem pointField_le_prod_right (W V : FiniteContinuousGaloisModule) :
    V.pointField ≤ (W.prod V).pointField := by
  apply IntermediateField.fixedField_le
  rw [pointActionKernel_prod]
  exact inf_le_right

end FiniteContinuousGaloisModule

/-- The number field cut out by the complete geometric point action of a model. -/
abbrev PointField {R : Type} [CommRing R] [Algebra R ℚ] (H : FiniteFlatObject R) : Type :=
  H.points.pointField

/-- A rational field is a point field when it is isomorphic to the full-action fixed field. -/
def IsPointField {R : Type} [CommRing R] [Algebra R ℚ] (H : FiniteFlatObject R)
    (L : Type) [Field L] [Algebra ℚ L] : Prop := Nonempty (PointField H ≃ₐ[ℚ] L)

/-- The canonical point field is a realization of itself. -/
theorem isPointField_self {R : Type} [CommRing R] [Algebra R ℚ] (H : FiniteFlatObject R) :
    IsPointField H (PointField H) := ⟨AlgEquiv.refl⟩

/-- The product finite-flat object, using the tensor-product Hopf-algebra construction. -/
def FiniteFlatObject.prod {R : Type} [CommRing R] [Algebra R ℚ] [IsFractionRing R ℚ]
    (H J : FiniteFlatObject R) : FiniteFlatObject R :=
  ⟨H.points.prod J.points, Classical.choice
    ((nonempty_hasFiniteFlatModel_iff (H.points.prod J.points)).mpr
      (GaloisModule.IsFiniteFlat.prod R ℚ (AlgebraicClosure ℚ) H.points
        H.model.isFiniteFlat J.model.isFiniteFlat))⟩

/-- A common annihilator kills the product. -/
theorem KilledByQ.prod {R : Type} [CommRing R] [Algebra R ℚ] [IsFractionRing R ℚ]
    {n : ℕ} {H J : FiniteFlatObject R} (hH : KilledByQ n H) (hJ : KilledByQ n J) :
    KilledByQ n (H.prod J) := fun ⟨w, v⟩ ↦ Prod.ext (hH w) (hJ v)

/-- Category D is closed under products. -/
theorem InCategoryD.prod {H J : FiniteFlatObject ZInvTwo}
    (hH : InCategoryD H) (hJ : InCategoryD J) :
    InCategoryD (H.prod J) := by
  constructor
  · obtain ⟨m, hm⟩ := hH.threePrimary
    obtain ⟨n, hn⟩ := hJ.threePrimary
    refine ⟨m + n, ?_⟩
    change Nat.card (H.points × J.points) = _
    rw [Nat.card_prod, hm, hn, pow_add]
  · intro σ hσ ⟨w, v⟩
    exact Prod.ext (hH.inertiaSquareZero σ hσ w) (hJ.inertiaSquareZero σ hσ v)

end ThreeAdicPlan
