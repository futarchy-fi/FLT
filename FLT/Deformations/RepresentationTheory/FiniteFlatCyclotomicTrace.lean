/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudCoefficientTrace
public import FLT.Deformations.RepresentationTheory.CyclotomicGeneratorTrace
public import FLT.Deformations.RepresentationTheory.GaloisRep

/-!
# The original global representation's nonzero cyclotomic-generator trace

Unpack the actual local finite-flat witness using the same point module and
its canonical local Galois action. No comparison model is supplied by the caller.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GaloisRep
open NumberField ThreeAdicPlan

variable (p : ℕ) [Fact p.Prime]
local notation "v" => LocalCyclotomic.rationalPlace p
local notation "Kv" => IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v
local notation "O" => IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v
local notation "j" => Field.absoluteGaloisGroup.map (algebraMap ℚ Kv)

/-- The actual flat global representation has nonzero trace at a cyclotomic inertia generator. -/
theorem flat_cyclotomic_generator_trace {k V : Type} [Field k] [TopologicalSpace k]
    [CharP k p] [AddCommGroup V] [Module k V]
    (ρ : GaloisRep ℚ k V) (hp : 3 < p)
    (hflat : ρ.HasFlatProlongationAt v) (hdim : Module.finrank k V = 2)
    (hdet : ∀ g, (ρ g).det = ZMod.castHom (dvd_refl p) k (CyclotomicQuadratic.character p g)) :
    ∃ σ : localInertiaGroup v, orderOf (LocalRoot.modCyclotomic p σ.1) = p - 1 ∧
      LinearMap.trace k V (ρ (j σ.1)) ≠ 0 := by
  rcases hflat with ⟨H, hH, hHopf, hFF, hE, f, hf⟩
  let : Module k (ρ.toLocal v).Space := inferInstanceAs (Module k V)
  let M : FF O Kv := {
    CoordinateRing := H
    Points := (ρ.toLocal v).Space
    points := f
    points_bijective := hf }
  let e : M.Points ≃ₗ[k] V := LinearEquiv.refl k V
  let ρI : Representation k (localInertiaGroup v) M.Points :=
    (ρ.toLocal v).toRepresentation.comp (localInertiaGroup v).subtype
  have hρI (σ : localInertiaGroup v) : e.conj (ρI σ) = ρ (j σ.1) := by
    change (ρ.toLocal v) σ.1 = ρ (j σ.1)
    apply congrArg ρ
    exact congrArg (fun f : ℚ →+* Kv ↦ Field.absoluteGaloisGroup.map f σ.1)
      (Subsingleton.elim _ _)
  have hd (σ : localInertiaGroup v) : (ρI σ).det = ZMod.castHom (dvd_refl p) k
      (LocalRoot.modCyclotomic p σ.1 : ZMod p) := by
    have he : (e.conj (ρI σ)).det = (ρI σ).det := LinearMap.det_conj (ρI σ) e
    rw [← he, hρI, hdet, CyclotomicQuadratic.character_map_local]
    rfl
  obtain ⟨σ, hσ, ht⟩ := coefficient_flat_trace_ne_zero p M ρI hp (fun _ _ ↦ rfl)
    (e.finrank_eq.trans hdim) hd
  refine ⟨σ, hσ, ?_⟩
  rwa [← hρI, LinearMap.trace_conj']

end GaloisRep
