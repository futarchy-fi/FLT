/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeIndependentCanonicalSourceNaturality
public import FLT.Mazur.SchemeIndependentFamilyAssemblyFullyFaithful

/-!
# Fully faithful canonical independent descent

The canonical assembly comparison is natural. Canceling the fully faithful
assembly functor proves full faithfulness for the original member restrictions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeFppfFamily.IndependentLineData
open SchemePicard SchemeGeometricDescent
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme.{u}} (𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage X)

/-- The existing canonical assembly comparisons form a natural isomorphism. -/
def canonicalAssemblyNatIso :
    (familyLineEquivalence 𝒰).functor ≅ canonical 𝒰 ⋙ assemble :=
  NatIso.ofComponents (canonicalAssemblyIso 𝒰) (fun a ↦ by
    apply LineData.hom_ext
    exact canonicalSourceIso_naturality 𝒰 a)

instance canonical_faithful : (canonical 𝒰).Faithful :=
  Functor.Faithful.of_comp_iso (canonicalAssemblyNatIso 𝒰).symm

instance canonical_full : (canonical 𝒰).Full :=
  Functor.Full.of_comp_faithful_iso (canonicalAssemblyNatIso 𝒰).symm

/-- Lifting a compatible family map recovers every specified original member map. -/
lemma canonical_preimage_member {L K : LineBundleCat X}
    (a : (canonical 𝒰).obj L ⟶ (canonical 𝒰).obj K) (i : 𝒰.I₀) :
    (Scheme.Modules.pullback (𝒰.f i)).map ((canonical 𝒰).preimage a).hom = a.val i :=
  congrArg (fun b ↦ b.val i) ((canonical 𝒰).map_preimage a)

end FLT.Mazur.SchemeFppfFamily.IndependentLineData
