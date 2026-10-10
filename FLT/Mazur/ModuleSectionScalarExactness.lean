/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealPowerScalarLift
public import FLT.Mazur.ModuleSectionTransport

/-!
# Scalar kernels from actual quotient-image factorizations

A quotient-image isomorphism retaining scalar multiplication identifies
section kernels with scalar multiples as soon as quotient sections lift.
The generic proofs keep concrete tensor and quotient constructions sealed.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.FCurve

open IdealPowerScalarLift

set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}}

/-- The scalar sheaf endomorphism has the original action on global sections. -/
theorem moduleSection_scalarEnd_top (M : X.Modules) (r : Γ(X, ⊤)) (s : Γ(M, ⊤)) :
    (scalarEnd M r).app ⊤ s = r • s := by
  change X.presheaf.map (𝟙 _) r • s = _
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- Quotient-image scalar factorization and section lifting identify the exact scalar kernel. -/
theorem moduleSections_scalar_exact (S : ShortComplex X.Modules) (hS : S.ShortExact)
    {Q : X.Modules} (p : S.X₂ ⟶ Q) (e : Q ≅ S.X₁) (r : Γ(X, ⊤))
    (hr : p ≫ e.hom ≫ S.f = scalarEnd S.X₂ r)
    (hp : Function.Surjective (p.app ⊤)) :
    Function.Exact (fun s : Γ(S.X₂, ⊤) ↦ r • s) (S.g.app ⊤) := by
  have hc (s : Γ(S.X₂, ⊤)) : S.f.app ⊤ (e.hom.app ⊤ (p.app ⊤ s)) = r • s :=
    (congr($(hr).app ⊤ s)).trans (moduleSection_scalarEnd_top S.X₂ r s)
  intro s
  constructor
  · intro hs
    obtain ⟨t, ht⟩ := (moduleSections_exact S hS s).mp hs
    obtain ⟨u, hu⟩ := hp (e.inv.app ⊤ t)
    refine ⟨u, (hc u).symm.trans ?_⟩
    rw [hu]
    have he : e.hom.app ⊤ (e.inv.app ⊤ t) = t := congr($(e.inv_hom_id).app ⊤ t)
    rw [he, ht]
  · rintro ⟨t, rfl⟩
    change S.g.app ⊤ (r • t) = 0
    rw [← hc]
    exact (moduleSections_exact S hS _).mpr ⟨e.hom.app ⊤ (p.app ⊤ t), rfl⟩

/-- An injective image factor detects zero before the image inclusion. -/
theorem moduleSections_factor_zero_iff {M N P : X.Modules} (p : M ⟶ N) (i : N ⟶ P)
    [Mono i] (s : Γ(M, ⊤)) : (p ≫ i).app ⊤ s = 0 ↔ p.app ⊤ s = 0 := by
  change i.app ⊤ (p.app ⊤ s) = 0 ↔ _
  constructor
  · intro hs
    apply ModuleSubobjectCoverEquality.app_injective i ⊤
    simpa only [map_zero] using hs
  · intro hs
    rw [hs, map_zero]

/-- A monomorphic scalar factor identifies the scalar annihilator on global sections. -/
theorem moduleSections_scalar_zero_iff {M N : X.Modules} (p : M ⟶ N) (i : N ⟶ M)
    [Mono i] (r : Γ(X, ⊤)) (hr : p ≫ i = scalarEnd M r) (s : Γ(M, ⊤)) :
    r • s = 0 ↔ p.app ⊤ s = 0 := by
  rw [← moduleSection_scalarEnd_top, ← hr]
  exact moduleSections_factor_zero_iff p i s

end FLT.Mazur.FCurve
