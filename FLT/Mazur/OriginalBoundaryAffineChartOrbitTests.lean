/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryCoefficientOrbitTests

/-!
# Original boundary arrows from actual affine chart morphisms

The two coefficient characters are constructed by pullback of sections from
actual chart morphisms. Full invariant agreement makes the second character
linear over the same original scalars. The resulting boundary arrow lives on
the entire affine test scheme and retains both prescribed endpoints.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient SchemeScalarOrbitComparison
open EquivalenceRelationOrderedFrames RingPairInvariantFlatScalars
open SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] source action restrictedAction
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q) (n : ℕ) (o : Fin n)
  (U : (source p q (Fin n) o).Opens)
  (hU : ∀ g : Equiv.Perm (Fin n), (action e (Fin n) o g).hom ⁻¹ᵁ U = U)
  [IsAffine U.toScheme] (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
attribute [local instance] RingPairInvariantFlatScalars.sourceAlgebra
  targetAlgebra originalBoundaryAlgebra
set_option quotPrecheck false
local notation "ρ" => restrictedAction (action e (Fin n) o) U hU
local notation "s" => originalChartScalars e (Fin n) o U hU
local notation "R₀" => invariants p.appTop.hom q.appTop.hom
local notation "f" => scalarMorphism (algebraMap R₀ Γ(J.subscheme, ⊤))
local notation "c" => originalBoundaryComparison p q J hJ
attribute [local irreducible] scalarMorphism

/-- Section pullbacks construct the two scalar characters and the unique original arrow. -/
theorem originalBoundary_of_affine_chart_maps {T : Scheme.{0}} [IsAffine T]
    (u v : T ⟶ U.toScheme)
    (huv : ∀ a : invariantCoordinates ρ, u.appTop a.val = v.appTop a.val)
    (z : T ⟶ pullback f f)
    (hx : u ≫ U.ι ≫ first p q (Fin n) o = z ≫ pullback.fst f f ≫ J.subschemeι)
    (hy : v ≫ U.ι ≫ first p q (Fin n) o = z ≫ pullback.snd f f ≫ J.subschemeι) :
    ∃! d : T ⟶ pullback p J.subschemeι, d ≫ c = z := by
  let _ := SchemeScalarOrbitComparison.sourceAlgebra ρ s
  let r : R₀ →+* Γ(T, ⊤) := u.appTop.hom.comp (algebraMap R₀ Γ(U.toScheme, ⊤))
  let _ := r.toAlgebra
  let a : Γ(U.toScheme, ⊤) →ₐ[R₀] Γ(T, ⊤) :=
    { u.appTop.hom with commutes' := fun _ ↦ rfl }
  let b : Γ(U.toScheme, ⊤) →ₐ[R₀] Γ(T, ⊤) :=
    { v.appTop.hom with commutes' := fun t ↦ (huv (s t)).symm }
  have ha : Spec.map (CommRingCat.ofHom a.toRingHom) ≫ U.toScheme.isoSpec.inv =
      T.isoSpec.inv ≫ u := Scheme.isoSpec_inv_naturality u
  have hb : Spec.map (CommRingCat.ofHom b.toRingHom) ≫ U.toScheme.isoSpec.inv =
      T.isoSpec.inv ≫ v := Scheme.isoSpec_inv_naturality v
  obtain ⟨d, hd, _⟩ := originalBoundary_of_coefficient_characters e n o U hU J hJ
    a b huv (T.isoSpec.inv ≫ z) (by
      rw [← Category.assoc, ha]
      simpa only [Category.assoc] using congrArg (fun t ↦ T.isoSpec.inv ≫ t) hx) (by
      rw [← Category.assoc, hb]
      simpa only [Category.assoc] using congrArg (fun t ↦ T.isoSpec.inv ≫ t) hy)
  have h : (T.isoSpec.hom ≫ d) ≫ c = z := by
    rw [Category.assoc, hd, T.isoSpec.hom_inv_id_assoc]
  let _ := originalBoundaryComparison_mono e J hJ
  exact ⟨T.isoSpec.hom ≫ d, h, fun d' hd' ↦ (cancel_mono c).mp (hd'.trans h.symm)⟩

end FLT.Mazur.EquivalenceRelationNormalizedFrames
