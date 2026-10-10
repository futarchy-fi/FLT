/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.Connected.Clopen

/-!
# Connectedness detected by global functions

A nontrivial clopen decomposition splits the actual global section ring into
a product of two nontrivial rings. Consequently a scheme whose global
functions form a domain is preconnected. This needs no affineness or
properness hypothesis and is the converse direction needed for fiber criteria.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- If the actual ring of global sections is a domain, the scheme is preconnected. -/
theorem preconnectedSpace_of_globalSections_domain (X : Scheme.{u})
    [IsDomain Γ(X, ⊤)] : PreconnectedSpace X := by
  apply preconnectedSpace_iff_clopen.mpr
  intro s hs
  by_contra! hn
  let U : X.Opens := ⟨s, hs.isOpen⟩
  let V : X.Opens := ⟨sᶜ, hs.isClosed.isOpen_compl⟩
  have : Nonempty U := Set.nonempty_coe_sort.mpr hn.1
  have : Nonempty V := by
    obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem s).mp hn.2
    exact ⟨⟨x, hx⟩⟩
  have hc : U ⊔ V = ⊤ := by ext x; simp [U, V]
  have hd : U ⊓ V = ⊥ := by ext x; simp [U, V]
  let e : Γ(X, U ⊔ V) ≅ CommRingCat.of (Γ(X, U) × Γ(X, V)) :=
    (X.sheaf.isProductOfDisjoint U V hd).conePointUniqueUpToIso
      (CommRingCat.prodFanIsLimit _ _)
  have : IsDomain Γ(X, U ⊔ V) := by rw [hc]; infer_instance
  have : IsDomain (Γ(X, U) × Γ(X, V)) :=
    e.symm.commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
  exact false_of_nontrivial_of_product_domain Γ(X, U) Γ(X, V)

/-- An injective evaluation into a domain forces a nonempty scheme to be connected. -/
theorem connectedSpace_of_injective_global_evaluation (X : Scheme.{u}) [Nonempty X]
    {R : Type*} [CommRing R] [IsDomain R] (ε : Γ(X, ⊤) →+* R)
    (hε : Function.Injective ε) : ConnectedSpace X := by
  have : IsDomain Γ(X, ⊤) := hε.isDomain ε
  have := preconnectedSpace_of_globalSections_domain X
  exact ⟨inferInstance⟩

end FLT.Mazur.Approximation
