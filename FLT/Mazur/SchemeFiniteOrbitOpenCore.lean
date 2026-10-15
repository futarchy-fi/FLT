/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteOrbitOpenCore
public import FLT.Mazur.SmoothGeometricOpenEtaleLift

/-!
# Original étale witnesses satisfying every automorphism translate

A finite orbit of a geometric open condition on an irreducible smooth fiber
constructs an original affine étale witness. Every automorphism translate
of its geometric point factors through the prescribed open as a whole
scheme morphism. Neither the acting group nor its point orbits need be finite.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeFiniteOrbitOpenCore
set_option backward.isDefEq.respectTransparency false
variable {G : Type} [Group G] {Y : Scheme} (ρ : G →* Aut Y)

/-- The action on points induced by actual scheme automorphisms. -/
@[instance_reducible] def pointAction : MulAction G Y where
  smul g x := (ρ g).hom x
  one_smul x := by
    change (ρ 1).hom x = x
    rw [map_one]
    rfl
  mul_smul g h x := by
    change (ρ (g * h)).hom x = (ρ g).hom ((ρ h).hom x)
    rw [map_mul]
    rfl

/-- Every automorphism in the point action is continuous. -/
theorem pointAction_continuous : @ContinuousConstSMul G Y _ (pointAction ρ).toSMul :=
  by
    let _ := pointAction ρ
    exact ⟨fun g ↦ (ρ g).hom.continuous⟩

variable (U : Y.Opens)
  (hf : (Set.range (fun g : G ↦ (ρ g).hom ⁻¹' (U : Set Y))).Finite)

/-- The original geometric open restricted to points satisfying all conjugate conditions. -/
def invariantOpen : Y.Opens := by
  let _ := pointAction ρ
  let _ := pointAction_continuous ρ
  exact ⟨FiniteOrbitOpenCore.core (G := G) (U : Set Y),
    FiniteOrbitOpenCore.isOpen_core U.isOpen hf⟩

/-- The defining condition retains all acting automorphisms. -/
theorem mem_invariantOpen (x : Y) :
    x ∈ invariantOpen ρ U hf ↔ ∀ g, (ρ g).hom x ∈ U := Iff.rfl

/-- A nonempty geometric open with finite orbit has a nonempty invariant refinement. -/
theorem invariantOpen_nonempty [IrreducibleSpace Y] (hne : (U : Set Y).Nonempty) :
    Nonempty (invariantOpen ρ U hf).toScheme := by
  let _ := pointAction ρ
  let _ := pointAction_continuous ρ
  obtain ⟨x, hx⟩ := FiniteOrbitOpenCore.core_nonempty U.isOpen hne hf
  exact ⟨⟨x, hx⟩⟩

variable {R K : Type} [CommRing R] [Field K] [IsSepClosed K] {V : Scheme}

include hf in
/-- An actual original étale witness meets every conjugate of the geometric condition. -/
theorem exists_etale_orbit_lift [IrreducibleSpace Y]
    (f : V ⟶ Spec (.of R)) [Smooth f] (t : Spec (.of K) ⟶ Spec (.of R))
    (a : Y ⟶ V) (b : Y ⟶ Spec (.of K)) (H : IsPullback a b f t)
    (hne : (U : Set Y).Nonempty) :
    ∃ (E : Scheme) (e : E ⟶ Spec (.of R)) (v : E ⟶ V)
      (z : Spec (.of K) ⟶ E) (w : Spec (.of K) ⟶ Y),
      IsAffine E ∧ Etale e ∧ v ≫ f = e ∧ z ≫ e = t ∧
      w ≫ b = 𝟙 _ ∧ z ≫ v = w ≫ a ∧
      ∀ g : G, ∃ u : Spec (.of K) ⟶ U.toScheme, u ≫ U.ι = w ≫ (ρ g).hom := by
  let W := invariantOpen ρ U hf
  obtain ⟨E, e, v, z, u, hE, he, hv, hz, hub, hua⟩ :=
    SmoothGeometricOpenEtaleLift.exists_lift f t a b H W.ι
      (invariantOpen_nonempty ρ U hf hne)
  refine ⟨E, e, v, z, u ≫ W.ι, hE, he, hv, hz,
    by simpa only [Category.assoc] using hub, by simpa only [Category.assoc] using hua,
    fun g ↦ ?_⟩
  have hr : Set.range ((u ≫ W.ι) ≫ (ρ g).hom) ⊆ Set.range U.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact (mem_invariantOpen ρ U hf _).mp (u x).property g
  exact ⟨IsOpenImmersion.lift U.ι _ hr, IsOpenImmersion.lift_fac _ _ _⟩

end FLT.Mazur.SchemeFiniteOrbitOpenCore
