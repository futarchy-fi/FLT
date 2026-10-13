/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFiniteKernelAlgebra

/-!
# An actual Noetherian coefficient model of the full invariant candidate kernel

Take the spectrum of the constructed finite coefficient algebra. Its projection
retains the original base and is locally finitely presented. This constructs
an actual finite type scheme model; its flatness and Picard effectivity are
still separate geometric tasks.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
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
/-- Use the literal original base algebra on invariant coefficients. -/
local instance finiteModelInvariantAlgebra : Algebra R
    (compatibleFunctions (fst f hL d V c k).left (snd f hL d V c k).left) :=
  (invariantCoefficientBase f hL d V c k).toAlgebra
local notation "C" => finiteKernelCoefficientAlgebra f hL d V c k

/-- The finite coefficient model is an actual affine scheme over the original base. -/
def finiteKernelModel : Over (Spec (.of R)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R C)))

instance finiteKernelModel_isAffine : IsAffine (finiteKernelModel f hL d V c k).left :=
  inferInstanceAs (IsAffine (Spec _))

instance finiteKernelModel_isNoetherian : IsNoetherian (finiteKernelModel f hL d V c k).left :=
  inferInstanceAs (IsNoetherian (Spec (.of C)))

/-- The model structure map is locally of finite type over the unchanged original base. -/
instance finiteKernelModel_locallyOfFiniteType :
    LocallyOfFiniteType (finiteKernelModel f hL d V c k).hom :=
  HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr inferInstance)

/-- The finite model includes its coefficients literally in the original source functions. -/
def finiteKernelCoefficientInclusion : CommRingCat.of C ⟶ Γ(A.left, ⊤) :=
  CommRingCat.ofHom
    ((compatibleFunctions (fst f hL d V c k).left (snd f hL d V c k).left).subtype.comp
      (C).val.toRingHom)

/-- The actual source projection, including its original relative structure. -/
def finiteKernelProjection : A ⟶ finiteKernelModel f hL d V c k :=
  Over.homMk (A.left.toSpecΓ ≫ Spec.map (finiteKernelCoefficientInclusion f hL d V c k)) (by
    change (A.left.toSpecΓ ≫ Spec.map (finiteKernelCoefficientInclusion f hL d V c k)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R C)) = A.hom
    rw [Category.assoc, ← Spec.map_comp]
    change A.left.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (.of R)).inv ≫ A.hom.appTop) = A.hom
    rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
      ← Scheme.isoSpec_Spec_inv, ← Scheme.isoSpec_hom, Iso.hom_inv_id, Category.comp_id])

local notation "v" => finiteKernelProjection f hL d V c k

/-- Normalization recovers the unchanged inclusion of finite invariant coefficients. -/
theorem finiteKernelProjection_coefficients :
    (Scheme.ΓSpecIso (.of C)).inv ≫ (v).left.appTop =
      finiteKernelCoefficientInclusion f hL d V c k :=
  ΓSpecIso_inv_ΓSpec_adjunction_homEquiv (finiteKernelCoefficientInclusion f hL d V c k)

/-- The actual source map to the finite model is locally of finite type. -/
instance finiteKernelProjection_locallyOfFiniteType : LocallyOfFiniteType (v).left := by
  have h : LocallyOfFiniteType ((v).left ≫ (finiteKernelModel f hL d V c k).hom) := by
    rw [(v).w]
    exact selectedSource_locallyOfFiniteType f d V k
  exact locallyOfFiniteType_of_comp (v).left (finiteKernelModel f hL d V c k).hom

/-- Noetherianity of the constructed target now proves local finite presentation. -/
instance finiteKernelProjection_locallyOfFinitePresentation :
    LocallyOfFinitePresentation (v).left := by
  infer_instance

/-- Both actual source and target are affine, so the complete projection is quasi-compact. -/
instance finiteKernelProjection_quasiCompact : QuasiCompact (v).left := by
  infer_instance

/-- The finite model and the original invariant candidate have exactly the same scheme kernel. -/
theorem finiteKernelProjection_test_iff {T : Over (Spec (.of R))} (a b : T ⟶ A) :
    a ≫ v = b ≫ v ↔ a ≫ invariantAffineProjection f hL d V c k =
      b ≫ invariantAffineProjection f hL d V c k := by
  have hn (t : T ⟶ A) :
      (Scheme.ΓSpecIso (.of C)).inv ≫ (t ≫ v).left.appTop =
        finiteKernelCoefficientInclusion f hL d V c k ≫ t.left.appTop := by
    rw [Over.comp_left, Scheme.Hom.comp_appTop, ← Category.assoc,
      finiteKernelProjection_coefficients]
  rw [finiteKernelCoefficientAlgebra_test]
  constructor
  · intro h s
    have he := congrArg (fun t : T ⟶ finiteKernelModel f hL d V c k ↦
      (Scheme.ΓSpecIso (.of C)).inv ≫ t.left.appTop) h
    rw [hn, hn] at he
    exact ConcreteCategory.congr_hom he s
  · intro h
    apply Over.OverMorphism.ext
    apply ext_of_isAffine
    apply (cancel_epi (Scheme.ΓSpecIso (.of C)).inv).mp
    rw [hn, hn]
    ext s
    exact h s

/-- The actual finite model projection coequalizes the full original Picard relation. -/
@[reassoc]
theorem finiteKernelProjection_condition :
    fst f hL d V c k ≫ v = snd f hL d V c k ≫ v :=
  (finiteKernelProjection_test_iff f hL d V c k _ _).mpr
    (invariantAffineProjection_condition f hL d V c k)

/-- An actual isomorphism of the finite-model and invariant-candidate scheme kernels.
This does not identify either kernel with the original Picard relation. -/
def finiteKernelProjectionOriginalKernelIso :
    pullback v v ≅ pullback (invariantAffineProjection f hL d V c k)
      (invariantAffineProjection f hL d V c k) where
  hom := pullback.lift (pullback.fst v v) (pullback.snd v v)
    ((finiteKernelProjection_test_iff f hL d V c k _ _).mp pullback.condition)
  inv := pullback.lift (pullback.fst _ _) (pullback.snd _ _)
    ((finiteKernelProjection_test_iff f hL d V c k _ _).mpr pullback.condition)
  hom_inv_id := by
    apply pullback.hom_ext <;>
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext <;>
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.id_comp]

end FLT.Mazur.HilbertChart.AffineRestriction
