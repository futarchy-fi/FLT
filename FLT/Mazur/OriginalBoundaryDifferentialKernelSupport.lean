/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryLocalImageKernelDetection
public import FLT.Mazur.ScalarDifferentialPrincipalRigidity
public import FLT.Mazur.SchemeNoetherianUniformKernelPower

/-!
# Differential annihilators kill original comparison equations

Actual differential annihilators construct unramified opens of the exact
scalar image projection. On any locally Noetherian test covered by the actual
comparison image, the full comparison equations vanish above these opens.
Compactness then gives power annihilators on the entire nonreduced test.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
open SchemeScalarImageQuotient FlatScalarFunctionPushout
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
private theorem rigidity_on_preimage {B T X S : Scheme.{0}}
    (t : B ⟶ T) (y : T ⟶ X) (f : X ⟶ S) (U : X.Opens)
    [FormallyUnramified (U.ι ≫ f)] :
    ∀ u : (((t ≫ y) ⁻¹ᵁ U).toScheme : Scheme), ∃ V : X.Opens,
      (((t ≫ y) ⁻¹ᵁ U).ι ≫ t ≫ y) u ∈ V ∧ FormallyUnramified (V.ι ≫ f) :=
  fun u ↦ ⟨U, u.property, inferInstance⟩

private theorem coverage_precomp {C T B V : Scheme.{0}}
    (c : C ⟶ T) (t : B ⟶ T) (v : V ⟶ B) (h : Set.range t ⊆ Set.range c) :
    Set.range (v ≫ t) ⊆ Set.range c := by
  rintro _ ⟨u, rfl⟩
  exact h (Set.mem_range_self (v u))

private theorem open_kernel_power {C T B : Scheme.{0}} [CompactSpace B]
    (c : C ⟶ T) (t : B ⟶ T) (V : B.Opens) (a : Γ(B, ⊤))
    (ha : B.basicOpen a ≤ V)
    (h : RingHom.ker c.appTop.hom ≤ RingHom.ker (V.ι ≫ t).appTop.hom)
    (r : Γ(T, ⊤)) (hr : c.appTop r = 0) : ∃ k : ℕ, a ^ k * t.appTop r = 0 := by
  apply SchemeQuasiCompactOpenKernelPower.exists_pow_mul_eq_zero V.ι
  · simpa only [Scheme.Opens.opensRange_ι] using ha
  · have hz : (V.ι ≫ t).appTop r = 0 := h hr
    rwa [Scheme.Hom.comp_appTop] at hz

private theorem open_kernel_uniform {C T B : Scheme.{0}} [IsNoetherian B]
    (c : C ⟶ T) (t : B ⟶ T) (V : B.Opens) (a : Γ(B, ⊤))
    (ha : B.basicOpen a ≤ V)
    (h : RingHom.ker c.appTop.hom ≤ RingHom.ker (V.ι ≫ t).appTop.hom) :
    ∃ k : ℕ, ∀ r : Γ(T, ⊤), c.appTop r = 0 → a ^ k * t.appTop r = 0 := by
  obtain ⟨k, hk⟩ := SchemeNoetherianUniformKernelPower.exists_uniform_power V a ha
  refine ⟨k, fun r hr ↦ hk _ ?_⟩
  have hz : (V.ι ≫ t).appTop r = 0 := h hr
  rwa [Scheme.Hom.comp_appTop] at hz

variable {D A B : Scheme.{0}} {p q : D ⟶ A} [IsAffine A]
  [Etale p] [IsSeparated p] [QuasiCompact p] [LocallyQuasiFinite p]
  [IsLocallyNoetherian B]
  (e : CategoryTheory.EquivalenceRelation p q) (J : A.IdealSheafData)
  (hJ : J.comap p = J.comap q)
local instance differentialKernelBoundary_affine : IsAffine J.subscheme :=
  isAffine_of_isAffineHom J.subschemeι
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
set_option quotPrecheck false
local notation "R₀" => invariants p.appTop.hom q.appTop.hom
local notation "f" => scalarMorphism (algebraMap R₀ Γ(J.subscheme, ⊤))
local notation "c" => originalBoundaryComparison p q J hJ
local notation "s" => RingHom.kerLift (scalarMap f)
attribute [local irreducible] scalarMorphism

include e

/-- Constructed differential opens kill all full comparison equations on their preimages. -/
theorem originalBoundary_differential_open_kernel
    (t : B ⟶ pullback f f) (h : Set.range t ⊆ Set.range c)
    (a : Γ(J.subscheme, ⊤))
    (ha : let _ : Algebra (Scalars f) Γ(J.subscheme, ⊤) := (s).toAlgebra
      a ∈ Module.annihilator Γ(J.subscheme, ⊤)
        (KaehlerDifferential (Scalars f) Γ(J.subscheme, ⊤))) :
    RingHom.ker (c).appTop.hom ≤
      RingHom.ker (((t ≫ pullback.snd f f) ⁻¹ᵁ J.subscheme.basicOpen a).ι ≫ t).appTop.hom := by
  let U := J.subscheme.basicOpen a
  let V := (t ≫ pullback.snd f f) ⁻¹ᵁ U
  let _ : FormallyUnramified (U.ι ≫ projection f) :=
    ScalarDifferentialPrincipalRigidity.principal_formallyUnramified s a ha
  apply originalBoundary_kernel_zero_of_local_image_coverage e J hJ (V.ι ≫ t)
  · simpa only [Category.assoc] using
      rigidity_on_preimage t (pullback.snd f f) (projection f) U
  · exact coverage_precomp c t V.ι h

/-- Each full equation has a power annihilator from every scalar differential annihilator. -/
theorem originalBoundary_differential_power_kernel [CompactSpace B]
    (t : B ⟶ pullback f f) (h : Set.range t ⊆ Set.range c)
    (a : Γ(J.subscheme, ⊤))
    (ha : let _ : Algebra (Scalars f) Γ(J.subscheme, ⊤) := (s).toAlgebra
      a ∈ Module.annihilator Γ(J.subscheme, ⊤)
        (KaehlerDifferential (Scalars f) Γ(J.subscheme, ⊤)))
    (r : Γ(pullback f f, ⊤)) (hr : (c).appTop r = 0) :
    ∃ k : ℕ, ((t ≫ pullback.snd f f).appTop a) ^ k * t.appTop r = 0 := by
  let V := (t ≫ pullback.snd f f) ⁻¹ᵁ J.subscheme.basicOpen a
  exact open_kernel_power c t V ((t ≫ pullback.snd f f).appTop a)
    (by rw [← Scheme.preimage_basicOpen_top])
    (originalBoundary_differential_open_kernel e J hJ t h a ha) r hr

omit [IsLocallyNoetherian B] in
/-- Noetherian tests give one exponent for the entire full comparison kernel. -/
theorem originalBoundary_differential_uniform_kernel [IsNoetherian B]
    (t : B ⟶ pullback f f) (h : Set.range t ⊆ Set.range c)
    (a : Γ(J.subscheme, ⊤))
    (ha : let _ : Algebra (Scalars f) Γ(J.subscheme, ⊤) := (s).toAlgebra
      a ∈ Module.annihilator Γ(J.subscheme, ⊤)
        (KaehlerDifferential (Scalars f) Γ(J.subscheme, ⊤))) :
    ∃ k : ℕ, ∀ r : Γ(pullback f f, ⊤), (c).appTop r = 0 →
      ((t ≫ pullback.snd f f).appTop a) ^ k * t.appTop r = 0 := by
  let V := (t ≫ pullback.snd f f) ⁻¹ᵁ J.subscheme.basicOpen a
  exact open_kernel_uniform c t V ((t ≫ pullback.snd f f).appTop a)
    (by rw [← Scheme.preimage_basicOpen_top])
    (originalBoundary_differential_open_kernel e J hJ t h a ha)

end FLT.Mazur.EquivalenceRelationOrderedFrames
