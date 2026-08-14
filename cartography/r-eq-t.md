# R = T / modularity-lifting core: repository map

Scope: read-only inspection of `/Users/kas/FLT` (blueprint text and Lean source).  No
network or literature lookup was used.  Statements about the mathematical literature or
future upstream intent are marked `(literature-verify)` when they are not directly evidenced
by repository text.  The citations below are to the read-only reference tree, not to this
working directory.

## Search audit and blueprint boundary

The initial audit was:

```text
rg -n -i --glob '*.lean' --glob '*.tex' --glob '*.md' \
  -e 'deformation' -e 'deformation ring' -e 'Hecke algebra' \
  -e 'R[[:space:]]*=[[:space:]]*T' -e 'R equals T' \
  -e 'modularity lifting' -e 'modularity-lifting' -e 'Taylor[- ]Wiles' \
  -e 'patching' -e 'numerical criterion' -e 'Poitou' -e 'Tate dual' -e 'TODO' \
  /Users/kas/FLT
```

The relevant blueprint hits, grouped so that the status can be judged from surrounding
text, are:

* `blueprint/src/chapter/ch04overview.tex:32,36-38` lists modularity lifting as a required
  ingredient and starts a dedicated section; `:40-60` defines an “S-good” lift by cyclotomic
  determinant, ramification, tame-inertia trace, and flatness; `:62-77` states the theorem but
  labels it `\notready`; `:79-91` says it is “very far from even stating ... in Lean” and
  sketches the minimal case as the Taylor–Wiles trick with Kisin refinements; `:93-98` says
  the theorem is applied to an auxiliary curve to obtain modularity over a totally real field
  and hence modularity of the residual representation; `:112` calls stating it in Lean the
  first target.
* `blueprint/src/chapter/ch05automorphicformexample.tex:5-9` identifies modularity lifting
  with an `R=T` theorem; `:11-25` says the project uses quaternionic Hecke algebras and that
  the immediate goal was only to formalise the *statement* of modularity lifting.
* `blueprint/src/chapter/ch06automorphicrepresentations.tex:1-8` says there are two lifting
  theorems (minimal Taylor–Wiles case and a later deduction) and that this chapter is work in
  progress.
* `blueprint/src/chapter/HeckeOperatorProject.tex:5-22` says the abstract Hecke theory is
  completely formalised, while concrete theory had sorried proofs in the prose snapshot;
  `:581-590` defines the intended Hecke algebra and its commutative/Noetherian theorem;
  `:621-625` explains the Noetherian argument via finite-dimensional automorphic forms.
* `blueprint/src/chapter/QuaternionAlgebraProject.tex:7-11` says finite-dimensional
  quaternionic forms control the Hecke `T` in `R=T`; `:147-165` identifies the Hecke algebra
  as endomorphisms of these spaces and states finite-dimensionality.
* `blueprint/src/chapter/chtopbestiary.tex:38-77` records local cohomological dimension,
  local duality, and Euler–Poincare as `\notready`; `:96` says, verbatim, “We also need
  Poitou-Tate duality; I'll refrain from writing it down for now, because we don't even have
  Galois cohomology in Lean yet.”
* `blueprint/src/chapter/ch03freyreduction.tex:274-276` contains “Poitou” only in the
  citation “Odlyzko and Poitou” for a discriminant bound, and `:276` mentions modern variants
  of Wiles' `R=T`; this is not a Poitou–Tate invocation.
* `GENERAL.md:37` says the modern Khare–Wintenberger/Kisin route still has the central theme
  that a deformation ring is isomorphic to a Hecke algebra.  `FLT/Assumptions/README.md:46-49`
  says a p-adic representation attached to a quaternionic form could not yet be stated because
  Hecke algebras were missing; `:65-68` lists Poitou–Tate as forthcoming once Galois
  cohomology exists.

The following direct quotations are the status-bearing hits (the surrounding line ranges are
included so a hit is not being treated as a mere filename match):

* `blueprint/src/chapter/ch04overview.tex:66-79`: “`\notready` ... If `\rhobar` is modular ...
  then `\rho` is also modular ... Right now we are very far from even stating this theorem in
  Lean.”
* `blueprint/src/chapter/ch04overview.tex:86-91`: “In the minimal case, the argument is the
  usual Taylor--Wiles trick, using refinements due to Kisin and others.”
* `blueprint/src/chapter/ch05automorphicformexample.tex:5-14`: “The key ingredient ... is a
  modularity lifting theorem, sometimes called an `$R=T$` theorem ... the `$T$` ... will be
  associated ... to quaternionic modular forms.”
* `blueprint/src/chapter/HeckeOperatorProject.tex:5-22`: “The abstract theory is completely
  formalized ... [concrete theory] ... has some sorried proofs ... Hecke algebras ... are the
  rings called `$T$` ... or `$R=T$` theorems.”
* `blueprint/src/chapter/chtopbestiary.tex:38-77,96`: each local duality/Euler--Poincare
  theorem is `\notready`; “We also need Poitou-Tate duality; I'll refrain from writing it down
  for now, because we don't even have Galois cohomology in Lean yet.”
* `FLT/Deformations/LiftFunctor.lean:114-118`: `flatFunctor` has `map := sorry`; the adjacent
  declarations at `:120-163` give proved unramified, trace, narrow-trace, and determinant
  subfunctors.
* `FLT/Deformations/Representable.lean:15-18,36-38,101-116`: the file calls its contents
  “mostly placeholders”; both corepresentability lemmas end in `sorry`, and the universal ring
  is selected from that unproved result.
* `FLT/AutomorphicForm/QuaternionAlgebra/HeckeOperators/Concrete.lean:374-385,850-876,878-912`:
  `U₁Data.Q` is an input “set of taylor wiles primes”; `U₁(S,Q)` and the generated `HeckeAlgebra`
  are defined, with a proved commutative-ring instance.
* `FLT/AutomorphicForm/QuaternionAlgebra/HeckeOperators/Concrete.lean:1062-1077`:
  `IsNoetherian`/`IsNoetherianRing` instances for `HeckeAlgebra` are proved.
* `FLT/Patching/Algebra.lean:18-23,42-60,109-159,214-248,496-513`: “Following the
  Taylor--Wiles--Kisin patching method” the ultraproduct/inverse-limit algebra, its local
  topology, lifted map, surjectivity, and constant-family equivalence are implemented.
* `FLT/Patching/Module.lean:531-587,611-645`: the patching-system map is proved bijective and
  the resulting module is free/finite with the stated rank.
* `FLT/Patching/REqualsT.lean:11-15,78-101`: “the kernel of the surjection `R → T` is contained
  in the nilradical”; the theorem assumes an abstract `RtoT` and proves only that containment.
* `FLT/GaloisRepresentation/Automorphic.lean:80-95,127-184`: automorphy assumes a Hecke
  character and matches good-prime traces; `cyclic_base_change` is a theorem statement whose
  proof is `sorry`.
* `FLT/GlobalLanglandsConjectures/GLzero.lean:26-27`: “Wiles' work used ... global Tate
  duality ... [to prove] a deformation ring `R` was isomorphic to a Hecke algebra `T`.”

For Lean hits, the exact source clusters are `FLT/Deformations/Representable.lean:12-18,36-38,48-116`,
`FLT/Deformations/LiftFunctor.lean:14-18,102-163`,
`FLT/AutomorphicForm/QuaternionAlgebra/HeckeOperators/Concrete.lean:15-22,374-385,848-912`,
`FLT/AutomorphicForm/QuaternionAlgebra/InnerProduct.lean:675-707`,
`FLT/Patching/Algebra.lean:18-23,42-60,109-159,496-503`,
`FLT/Patching/Module.lean:23-28,531-587,611-645`,
`FLT/Patching/Over.lean:292-376`,
`FLT/Patching/System.lean:13-18,110-118,244-284,420-457`, and
`FLT/Patching/REqualsT.lean:11-15,83-101`.
`FLT/GaloisRepresentation/Automorphic.lean:15-26,67-95,109-184` supplies the automorphic
interface and a sorry-backed cyclic-base-change theorem.  `FLT/GlobalLanglandsConjectures/GLzero.lean:22-27`
is the only direct Lean prose hit saying that Wiles used global Tate duality centrally.

The absence checks used below were:

```text
rg -n -i --glob '*.lean' \
  -e 'numerical[ -]?criterion' -e 'Wiles numerical' -e 'dual Selmer' -e 'Selmer' \
  -e 'universal.*Hecke' -e 'Hecke.*universal' -e 'modularity[_ -]?lifting' \
  /Users/kas/FLT/FLT/Patching /Users/kas/FLT/FLT/Deformations \
  /Users/kas/FLT/FLT/AutomorphicForm /Users/kas/FLT/FLT/GaloisRepresentation
```

This returned no numerical-criterion, Selmer, universal-Hecke, or modularity-lifting hit;
the separate inspection of `FLT/Patching/REqualsT.lean:11-15,83-101` found only the abstract
nilradical theorem and no `RingEquiv`/`AlgEquiv` endpoint;
the only Taylor–Wiles hits were comments naming `U₁Data.Q` as “the set of taylor wiles
primes” (`Concrete.lean:379`) and describing `Q` (`Concrete.lean:861`).  Likewise,

```text
rg -n -i --glob '*.lean' -e 'Poitou' -e 'Tate dual' -e 'global dual' \
  -e 'Selmer' -e 'cohomology' \
  /Users/kas/FLT/FLT/Patching /Users/kas/FLT/FLT/Deformations
```

returned no matches.  Thus generic patching is present, but no arithmetic duality edge is
wired into it.

## 1. Repo-state inventory

“Done” means a Lean declaration whose body contains no `sorry`; “partial(sorry)” means a
statement or definition exists but its body contains `sorry`; “absent” means the searched
component has no declaration (a negative search is recorded rather than inferred silently).

| R=T-relevant component | Status | Evidence and boundary |
|---|---|---|
| Continuous Galois-representation and framed-`GL₂` API | **done** | `FLT/Deformations/RepresentationTheory/GaloisRep.lean:47-59` defines continuous `GaloisRep` and conversion from `G →ₜ* GL n R`; `:161-172` proves the framed-representation/`GL` equivalence. These are reusable inputs, not deformation rings. |
| Pro-artinian coefficient category and residue algebra | **done** | `FLT/Deformations/Categories.lean:17-21,34-40,68-79` defines the local pro-artinian category and its class; `FLT/Deformations/IsResidueAlgebra.lean:30-55` proves the residue-field algebra equivalence. |
| Lift/deformation functors and local conditions | **partial(sorry)** | `FLT/Deformations/LiftFunctor.lean:102-112` defines lifts modulo conjugacy; `:120-163` gives unramified, trace, narrow-trace, and determinant subfunctors, but `:114-118` defines `flatFunctor` with `map := sorry`. |
| Representability / universal deformation ring | **partial(sorry)** | General corepresentability is stated with `sorry` at `FLT/Deformations/Representable.lean:36-38`; narrow `S`-lift representability is `sorry` at `:101-106`; the universal ring is merely selected from that proof at `:108-116`. No completed global deformation ring for the FLT residual representation is instantiated. |
| Abstract Hecke operators | **done** | `FLT/AutomorphicForm/QuaternionAlgebra/HeckeOperators/Abstract.lean:194-218` defines the additive and `R`-linear double-coset operators; `:256-284` proves the commutation criterion. The blueprint also calls the abstract theory completely formalised (`HeckeOperatorProject.tex:5-7,16-22`). |
| Concrete quaternionic Hecke operators and `T,U` algebra | **done** | `Concrete.lean:374-385` defines `U₁Data`, including `S` and a *field* `Q` of Taylor–Wiles primes; `:878-912` defines `HeckeAlgebra` as the adjoin of `Tᵥ` and `Uᵥ,ₐ` and proves a commutative ring; `:942-954` proves the generators adjoin to the top; `:1062-1077` proves Noetherian-ring instances. `InnerProduct.lean:675-707` adds integrality and the eigenform product embedding. |
| Finite-dimensional automorphic module | **done** | `FLT/AutomorphicForm/QuaternionAlgebra/FiniteDimensional.lean:49-70` proves finite double cosets and installs `IsFinite`; the blueprint theorem is recorded at `QuaternionAlgebraProject.tex:160-183`. |
| Taylor–Wiles level data and auxiliary-prime theory | **absent (data scaffold only)** | Only the data structure and level operators exist (`Concrete.lean:374-385,389-413,850-876`); these declarations contain no `sorry`, but they take `Q` as input. The absence search found no theorem selecting auxiliary primes, no dual-Selmer killing, and no Taylor–Wiles congruence/level-lowering statement. |
| Generic Taylor–Wiles–Kisin patching algebra | **done** | `FLT/Patching/Algebra.lean:18-23` states the ultraproduct construction; `:42-60` proves uniform finite components; `:109-159` constructs the inverse-limit algebra and its topological/local instances; `:214-248` proves the lifted map and surjectivity; `:496-513` proves the constant-family equivalence. No `sorry` occurs in this file. |
| Generic patching module, coefficient change, and compatibility system | **done** | `FLT/Patching/Module.lean:531-587` defines `IsPatchingSystem`, component equivalences, and the canonical map; `:611-645` proves bijectivity, freeness, finiteness, and rank. `FLT/Patching/Over.lean:292-318` proves quotient-to-patching linear equivalences and `:324-376` supplies coefficient-ring quotient maps. `System.lean:110-118,166-202,244-284` supplies scalar data, finite module structure, and faithful scalar action. |
| Instantiated patching data from FLT deformation/Hecke systems | **absent** | The generic files quantify over arbitrary families `R i`, `M i`, an ultrafilter, and compatibility hypotheses (`REqualsT.lean:23-81`); no file constructs these from `U₁Data.Q`, Hecke modules, a residual maximal ideal, or deformation conditions. The negative search above found no such construction. |
| Numerical criterion / Selmer-dimension input | **absent** | No `numerical criterion`, `Selmer`, `dual Selmer`, or dimension formula declaration was found in the core Lean search. The blueprint only has local Euler–Poincare and a future Poitou–Tate note (`chtopbestiary.tex:38-77,96`). |
| Final `R → T` map and full `R ≅ T` theorem | **done (abstract endpoint); absent (FLT theorem)** | `FLT/Patching/REqualsT.lean:11-15` says the file proves only nilpotent-kernel control; `:78-86` assumes an abstract `RtoT : R₀ →+* T₀`; `:83-101` proves `ker RtoT ≤ nilradical R₀` with no `sorry`. There is no FLT-specific `R` or `T`, no arithmetic surjection construction, and no `RingEquiv`/`AlgEquiv` upgrading this to `R ≅ T` (negative search above). |
| Hecke–Galois attachment and local-global comparison | **partial(sorry)** | `FLT/GaloisRepresentation/Automorphic.lean:67-95` defines automorphy by *assuming* a Hecke-algebra character `π` and matching Frobenius traces; it does not construct `π` from a deformation ring or attach a representation to an eigenform. The same file's cyclic base-change theorem is stated at `:109-183` but ends `sorry` at `:184`. `FLT/Assumptions/README.md:46-49` is a stale roadmap statement that this attachment was not yet stateable. |
| Modularity-lifting theorem and Frey-spine wiring | **absent** | The only precise theorem is blueprint prose `ch04overview.tex:66-77`, marked `\notready`; `:79-91` says it is far from Lean. The current spine leaves `B4_proof` as `sorry` (`FLT/Proof.lean:98-105`), and `FLT/FreyCurve/FreyPackage.lean:69-73` describes modularity as historical context rather than a Lean theorem. |
| Dedicated R=T/PT assumption or axiom | **absent** (generic axiom is not a substitute) | `rg -n 'axiom.*(R|Hecke|modularity|Poitou)' /Users/kas/FLT/FLT` finds no dedicated axiom. The only generic escape hatch is `knownin1980s`, explicitly arbitrary at `FLT/Assumptions/KnownIn1980s.lean:60-79`; it is an assumption/axiom category item, not an R=T result. |
| Generic `knownin1980s` escape hatch (non-specific) | **assumption/axiom** | `FLT/Assumptions/KnownIn1980s.lean:60-79` declares `axiom knownin1980s {P : Prop} : P`, i.e. a proof of an arbitrary proposition. No invocation is an R=T theorem; this is recorded separately so it is not misclassified as a proof. |

The `done` entries above are genuine proofs in the named files: `rg -n 'sorry|axiom'`
over the corresponding Hecke and generic-patching files is empty (the one unrelated
topological exception is `FLT/Patching/Utils/CompactHausdorffRings.lean:27-42`, whose
Pontryagin-duality lemma is `sorry`).

## 2. Absent pieces for a Taylor–Wiles–Kisin route to R=T

These are the smallest missing nodes after treating the generic patching algebra/module as
already supplied.  Sizes are incremental Lean effort: S < M < L < XL.  “Present edge” means
there is an actual declaration today; “absent edge” means an interface still has to be made.

1. **Complete global deformation rings and local deformation conditions — L/XL.**
   Finish the `flatFunctor` functoriality and both representability proofs, then instantiate
   the narrow `S`-deformation ring for the residual `\barρ`.  Edges: present
   `hub-lsb1u.10`-type inputs are the continuous framed representations, determinant, local
   restriction, and irreducibility APIs (`GaloisRep.lean:47-59,161-172`; functors at
   `LiftFunctor.lean:114-163`); absent are the global residual representation's completed
   local conditions and a usable universal ring (`Representable.lean:36-38,101-116`).
   This node feeds the `R i` family required by `Patching/Algebra.lean:20-23`.

2. **Poitou–Tate/Selmer duality and the deformation-dimension formula — XL.**
   Provide the finite residual and adjoint-module local pairings, Selmer/dual-Selmer
   orthogonality, and the dimension/Euler-characteristic corollary used to make the number of
   Taylor–Wiles variables match the obstruction dimension.  Edges: the blueprint explicitly
   names local duality/Euler–Poincare as not ready (`chtopbestiary.tex:38-77`) and says PT is
   still unwritten (`:96`); `FLT/Assumptions/README.md:65-68` lists it as forthcoming.  The
   `hub-lsb1u.7` branch report (`cartography/poitou-tate.md:55-58,79-93,154-155`) identifies
   the weakest R=T interface as this Selmer corollary, but the current R=T/deformation search
   has no PT/Selmer hit.  The actual edge to node 1 is via the deformation tangent/obstruction
   spaces; the edge to node 3 is auxiliary-prime selection.  The claim that this is the
   standard Wiles numerical input is `(literature-verify)`; the repository evidence only
   establishes that Wiles used global Tate duality (`GLzero.lean:26-27`).

3. **Taylor–Wiles auxiliary-prime existence and level/congruence theorems — XL.**
   Turn `U₁Data.Q` from an input finset into a theorem-produced Taylor–Wiles datum: primes
   satisfying the required Frobenius/dual-Selmer conditions, local deformation rings at `Q`,
   level-change maps, and compatible Hecke operators.  Present edge: `Concrete.lean:374-385`
   and `:850-876` define `Q`, `U₁(S,Q)`, and `Uᵥ,ₐ`; absent edge: the search found only those
   comments/data declarations, not existence, adequacy, level lowering, or congruence maps.
   Inputs from `hub-lsb1u.10` are the residual representation and its local Frobenius/inertia
   data; node 2 supplies the dual-Selmer dimension to kill.  The exact prime-existence theorem
   is `(literature-verify)`.

4. **Hecke–Galois comparison and a usable localized/completed `T` — XL.**
   Construct the Galois representation attached to the relevant quaternionic eigenform/Hecke
   algebra, prove characteristic-polynomial/trace compatibility at good places, and localize
   or complete `T` at the residual maximal ideal.  Present edges: concrete `HeckeAlgebra` and
   its Noetherian/commutative structure (`Concrete.lean:878-912,1062-1077`) and the automorphy
   predicate using a character `π` (`GaloisRepresentation/Automorphic.lean:67-95`).  Absent
   edges: no construction from `T` to a universal Galois representation, no residual maximal
   ideal/localization, and the cyclic-base-change theorem is still `sorry` (`:127-184`).
   This consumes `hub-lsb1u.10`'s Galois-representation outputs and is the bridge needed to
   define the actual `R → T` map.

5. **Instantiation of the generic patching system — XL.**
   Build the families `R_i` (deformation rings with `Q_i`) and `M_i` (finite Hecke modules),
   prove uniform bounded ranks, freeness over the coefficient quotients, quotient
   identifications, and the `IsPatchingSystem`/`smulData` hypotheses.  Generic edges are
   already real proofs: `Module.lean:531-587,611-645`, `Over.lean:292-376`, and
   `System.lean:110-202`; the missing edge is any FLT construction supplying the abstract
   variables in `REqualsT.lean:23-81`.  Node 3 supplies level-change systems and node 4
   supplies Hecke actions; without both, the generic patching code cannot be applied.

6. **Numerical criterion plus reduced `R=T` upgrade — L/XL.**
   Supply the numerical/depth criterion for the instantiated patched module, a surjective
   `R → T`, and the reducedness/nilradical argument that turns the existing kernel theorem
   into an actual isomorphism (or state exactly the reduced-quotient conclusion consumed by
   the application).  Present edge: `REqualsT.lean:83-101` proves only nilradical containment
   under abstract hypotheses; `System.lean:422-457` proves the support/faithful-action lemma
   used by that endpoint.  Absent edge: no FLT `R`, `T`, map, numerical criterion, or
   `RingEquiv` was found.  The minimal theorem should avoid proving a stronger global R=T than
   the Frey application consumes.

7. **Modularity-lifting statement and Frey application boundary — XL.**
   State and connect the weakest lifting implication below to the potential-modularity/Frey
   chain.  The blueprint gives the exact residual/lift hypotheses and conclusion at
   `ch04overview.tex:40-77`, but marks it `\notready`; the application sketch is `:93-98`.
   The current main spine still has `B4_proof := sorry` (`FLT/Proof.lean:98-105`).  This node
   depends on node 4's automorphic Galois attachment and node 6's R=T result, and consumes
   `hub-lsb1u.10`'s residual Galois-representation data.  It is a downstream interface rather
   than additional patching algebra.

## 3. Weakest sufficient modularity-lifting statement consumed by the Frey argument

The minimal statement to expose is the theorem already written in the blueprint, not a
general theorem for every representation:

> Let `ℓ ≥ 5` be prime, let `F` be totally real of even degree with `ℓ` unramified, and let
> `S` be a finite set of finite places not dividing `ℓ`.  Let
> `\barρ : G_F → GL₂(k)` be continuous, absolutely irreducible after restriction to
> `F(ζ_ℓ)`, and `S`-good.  If `\barρ` is modular of level `Γ₁(S)` and
> `ρ : G_F → GL₂(𝓞)` is an `S`-good lift to the integers of a finite extension of `ℚ_ℓ`,
> then `ρ` is modular of level `Γ₁(S)`.

This is a direct transcription of `blueprint/src/chapter/ch04overview.tex:40-77`; “S-good”
is explicitly the four bullets at `:49-60` (cyclotomic determinant, unramified outside
`S ∪ {ℓ}`, tame-inertia trace 2 at `S`, and flat at `v|ℓ`).  The Frey/potential-modularity
sketch uses only the implication “modular residual representation + S-good lift ⇒ modular
lift,” then specializes/compares to obtain the desired residual modularity
(`ch04overview.tex:93-98`).  It does not consume a strongest-possible R=T theorem, a full
nine-term PT sequence, or arbitrary weights/levels.

The existence of a proof under exactly these hypotheses, and the compatibility step from the
auxiliary lift to the original residual representation, are `(literature-verify)`: the
blueprint itself says the author is unsure of a precise reference (`ch04overview.tex:79-82`)
and labels the theorem `\notready`.

## 4. Risks

* **Statement/interface risk.** “S-good”, flatness, `Γ₁(S)`, and “modular” must be made
  type-correct and match the quaternionic `HeckeAlgebra` definition.  The blueprint currently
  uses temporary notation (`ch04overview.tex:58-60`) while Lean's local functors split these
  conditions (`LiftFunctor.lean:114-163`).
* **Deformation-theory risk.** Representability and flatness are still `sorry`
  (`Representable.lean:36-38,101-106`; `LiftFunctor.lean:114-118`).  Without a universal ring,
  the generic `R i` variables in patching have no arithmetic source.
* **Arithmetic-duality risk.** No PT/Selmer code is imported by `Patching` or `Deformations`;
  the blueprint explicitly postpones it (`chtopbestiary.tex:96`).  A finite-flat local
  condition at `v|ℓ` is not automatically ordinary finite Galois-module cohomology
  `(literature-verify)`.
* **Hecke/automorphic risk.** The Hecke algebra is robustly defined, but attaching Galois
  representations and localizing at a residual system is not.  `IsAutomorphicOfLevel` is an
  existential trace-matching predicate (`GaloisRepresentation/Automorphic.lean:67-95`), not
  the comparison map required by R=T.
* **Patching-instantiation risk.** The generic modules require uniform rank, freeness,
  quotient identifications, and faithful scalar action (`REqualsT.lean:23-81`).  None is
  proved for Taylor–Wiles Hecke modules; this is the largest technical gap even though the
  ultraproduct machinery itself is done.
* **Endpoint risk.** `ker_RtoT_le_nilradical` is not an isomorphism.  Treating it as full
  `R=T` would silently assume the missing map, surjectivity, and reducedness.
* **Roadmap/age risk.** The blueprint prose is stale relative to the 2025 Lean Hecke/patching
  files (for example it still says Hecke algebras were needed in `Assumptions/README.md:46-49`),
  while `ch06automorphicrepresentations.tex:3-8` remains explicitly WIP.  The patching algebra
  itself still carries a design TODO about the coefficient ring and boundedness hypotheses
  (`FLT/Patching/Algebra.lean:38-41`).  Do not infer a delivery date from prose.

## 5. Explicit size verdict and upstream trajectory

At row granularity the table has 16 R=T capability rows (plus the separately listed generic
axiom): 7 are fully proved infrastructure, 3 are
stated-with-`sorry`, and 6 are absent (the mixed final-endpoint row is counted absent for the
FLT-specific theorem). Thus 10/16, or about **63%**, has a declaration of some kind; weighting
the absent XL arithmetic nodes rather than counting rows gives a more realistic **about 55–60%**
of the R=T core.
The done fraction is concentrated in reusable infrastructure: the Hecke algebra and its
Noetherian API (`Concrete.lean:878-912,1062-1077`), ultraproduct patching algebra/module
(`Patching/Algebra.lean:18-23`; `Patching/Module.lean:531-645`), coefficient-change lemmas
(`Patching/Over.lean:292-376`), and the nilradical endpoint (`REqualsT.lean:11-15,83-101`).
The missing fraction is the arithmetic instantiation and the theorem that connects it to
Frey.

**Verdict: monitoring + gap-filling, not greenfield formalization.**  This is directly
evidenced by the upstream code already implementing the Taylor–Wiles–Kisin generic algebra
(`Patching/Algebra.lean:18-23`) and a final R=T endpoint (`REqualsT.lean:11-15`), with copyright
dates 2025 in those files and 2025 in the Hecke/deformation files.  The blueprint's own
roadmap still calls modularity lifting the first target (`ch04overview.tex:112`) and marks the
statement `\notready` (`:66-79`), so this campaign should track and fill the arithmetic
interfaces above rather than duplicate the generic patching work.  That upstream will finish
all seven absent nodes on its own 2029 timeline is **(literature-verify)**: the repository
only states the broad September-2029 project goal (`GENERAL.md:31-33`,
`Assumptions/KnownIn1980s.lean:43-54`), not a committed schedule for R=T completion.

The `hub-lsb1u.10` edge is therefore: residual Galois representations, irreducibility,
determinant, local inertia/Frobenius and flat/unramified conditions feed node 1 and node 4;
the current Lean API is present but the global automorphic attachment remains partial.  The
`hub-lsb1u.7` claim is only partly realized in this repo: its checked-in report identifies
Wiles R=T as a consumer (`cartography/poitou-tate.md:55-58`), and `GLzero.lean:26-27` says
global Tate duality was central, but the actual `Patching/REqualsT.lean` route has no Poitou,
Selmer, or cohomology import.  Thus PT is a required *future arithmetic edge* to the
Taylor–Wiles numerical criterion (node 2), not a dependency currently proved or invoked by
the R=T code.
