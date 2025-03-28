# Urs: Equivariant Super HoTT

## Abstract

We present a layered type theory that integrates three foundational frameworks:
Homotopy Type System (HTS), de Rham Cohesive Modal Type Theory (CMTT), and Equivariant Super Type Theory (ESTT).
This system builds a progressive structure for formalizing
mathematical and physical concepts, from homotopy and higher categorical
structures, through geometric cohesion and differential properties,
to the rich graded and equivariant world of supergeometry.
Inspired by Urs Schreiber’s work on equivariant super homotopy theory,
this layered approach offers a modular, type-theoretic foundation for
synthetic supergeometry and beyond.

Type theory has emerged as a powerful language for mathematics and physics,
unifying computation, logic, and structure. This article introduces
a three-layered type theory that extends Martin-Löf’s intensional
type theory into a framework capable of capturing homotopy, cohesion, and supergeometry:

* Homotopy Type System (HTS): foundation for higher categorical structures via types as ∞-groupoids.
* Cohesive Modal Type Theory: modal operators for geometric cohesion and differential structure.
* Equivariant Super Type Theory (ESTT): Thegraded universes/tensors, group actions, and super-modality.

Each layer builds on the previous, culminating in a system tailored to
formalize superpoints `(ℝᵐ|ⁿ)`, supersymmetry, and equivariant structures,
as exemplified in Schreiber’s "Equivariant Super Homotopy Theory" (2012).

## Syntax

```OCaml
type grade = Bos | Ferm (* Universe grades: bosonic (0) or fermionic (1) *)

type exp =
  (* MLTT/HoTT Core *)
  | Universe of int * grade           (* U i g *)
  | Var of string                     (* x *)
  | Forall of string * exp * exp      (* Π(x:A).B *)
  | Lam of string * exp * exp         (* λx:A. b *)
  | App of exp * exp                  (* f a *)
  | Path of exp * exp * exp           (* Id_A(u,v) *)
  | Transport of exp * exp * exp      (* transport A p t *)

  (* Cohesive Types *)
  | SmthSet                           (* SmthSet *)
  | Plot of int * exp * exp           (* plt n X φ *)
  | Flat of exp                       (* ♭ A *)
  | Sharp of exp                      (* ♯ A *)
  | Shape of exp                      (* ℑ A *)
  | Bosonic of exp                    (* ◯ A *)

  (* Graded and Supergeometry *)
  | Tensor of exp * exp               (* A ⊗ B *)
  | SupSmthSet                        (* SupSmthSet *)

  (* Groupoids *)
  | Grpd of int                       (* Grpd n *)
  | Comp of int * exp * exp * exp     (* comp n G a b *)

  (* Spectra and Stable Homotopy *)
  | Spectrum                          (* Spectrum *)
  | Susp of exp                       (* Susp A *)
  | Wedge of exp * exp                (* A ∧ B *)
  | HomSpec of exp * exp              (* [A, B] *)

  (* TED-K *)
  | KU_G of exp * exp * exp           (* KU_G^τ(X; τ) *)
  | Qubit of exp * exp                (* [Config, Fred^0 H] *)
  | Config of int * exp               (* Config^n(X) *)
  | Braid of int * exp                (* BB_n *)

  (* Differential Cohomology *)
  | Forms of int * exp                (* Ω^n(X) *)
  | Diff of int * exp                 (* d ω *)
  | DiffKU_G of exp * exp * exp * exp (* DiffKU_G^τ(X; τ, conn) *)
```

## Semantics

### Formation

* Graded Universes: ⊢ Uᵢᴵ⁰ᴵ : Uᵢ₊₁ᴵ⁰ᴵ, ⊢ Uᵢᴵ¹ᴵ : Uᵢ₊₁ᴵ⁰ᴵ.
* Graded Tensor: Γ ⊢ A : Uᵢ^g₁, Γ ⊢ B : Uᵢ^g₂ → Γ ⊢ A ⊗ B : Uᵢ^(g₁ + g₂) Γ ⊢ a : A, Γ ⊢ b : B → Γ ⊢ a ⊗ b : A ⊗ B Γ ⊢ a : A^g₁, Γ ⊢ b : B^g₂ → Γ ⊢ a ⊗ b = (−1)^(g₁ g₂) b ⊗ a : A ⊗ B.
* Group Action: Γ, g : 𝔾 ⊢ A : Uᵢ^g → Γ ⊢ 𝔾 → A : Uᵢ^g.
* Super Type Theory: Uᵍᵢ`|` 𝖘 A `|` 𝔾 → A.
* Super Modality: Γ ⊢ A : Uᵢ^g → Γ ⊢ 𝖘 A : Uᵢ^g.
* Cohesive Type Theory: ♭ `|` ♯ `|` ℑ `|` ◯ (four built-in modalities).
* Flat Codiscrete: Γ ⊢ A : Uᵢ^g → Γ ⊢ ♭ A : Uᵢ^g
* Sharp Discrete:  Γ ⊢ A : Uᵢ^g → Γ ⊢ ♯ A : Uᵢ^g
* Bosonic: Γ ⊢ A : Uᵢ⁽ᵍ⁾  →  Γ ⊢ ◯ A : Uᵢ⁽⁰⁾
* Fermionic: Γ ⊢ A : Uᵢ⁽ᵍ⁾  →  Γ ⊢ ℑ A : Uᵢ⁽¹⁾

### Introduction

* Graded Tensor: Γ ⊢ a : A, Γ ⊢ b : B → Γ ⊢ a ⊗ b : A ⊗ B.
* Group Action: Γ, g : 𝔾 ⊢ a : A → Γ ⊢ λg.a : 𝔾 → A.
* Super Modality: Γ ⊢ a : A → Γ ⊢ 𝖘-intro(a) : 𝖘 A.
* Bosinic: Γ ⊢ a : A  →  Γ ⊢ ◯ a : ◯ A, Γ ⊢ a : A  →  Γ ⊢ ◯ a : ◯ A,  ◯ a := η_◯ a, Γ ⊢ η_◯ : A → ◯ A, Γ ⊢ μ_◯ : ◯ (◯ A) → ◯ A,  μ_◯ ≃ id_◯A
* Fermionic: Γ ⊢ a : A  →  Γ ⊢ ℑ a : ℑ A, Γ ⊢ a : A  →  Γ ⊢ ℑ a : ℑ A,  ℑ a := η_ℑ a, Γ ⊢ ε_ℑ : ℑ A → A, Γ ⊢ δ_ℑ : ℑ A → ℑ (ℑ A),  δ_ℑ ≃ id_ℑA

### Elimation

* Graded Tensor: Γ ⊢ t : A ⊗ B, Γ, x : A, y : B ⊢ C : Uᵢ^g → Γ ⊢ ⊗-elim(t, x.y.C) : C[fst(t)/x, snd(t)/y].
* Group Action: Γ ⊢ t : 𝔾 → A, Γ ⊢ g : 𝔾 → Γ ⊢ t g : A.
* Super Modality: Γ ⊢ t : 𝖘 A, Γ, x : A ⊢ B : Uᵢ^g, Γ, x : A ⊢ f : B → Γ ⊢ 𝖘-elim(t, x.B, f) : B[𝖘-intro(t)/x].
* Bosonic: Γ ⊢ ◯ A : Uᵢ⁽⁰⁾  →  Γ ⊢ η_◯ : A → ◯ A, Γ ⊢ ◯ (◯ A) : Uᵢ⁽⁰⁾  →  Γ ⊢ μ_◯ : ◯ (◯ A) → ◯ A, μ_◯ ≃ id_◯A
* Fermionic: Γ ⊢ ℑ A : Uᵢ⁽¹⁾  →  Γ ⊢ δ_ℑ : ℑ A → ℑ (ℑ A), δ_ℑ ≃ id_ℑA

### Computation

* Graded Tensor: Γ ⊢ a : A, Γ ⊢ b : B, Γ, x : A, y : B ⊢ C : Uᵢ^g → Γ ⊢ ⊗-elim(a ⊗ b, x.y.C) = C[a/x, b/y] : C[a/x, b/y].
* Graded Commutativity: Γ ⊢ a : A^g₁, Γ ⊢ b : B^g₂ → Γ ⊢ a ⊗ b = (−1)^(g₁ g₂) b ⊗ a : A ⊗ B.
* Group Action: Γ, g : 𝔾 ⊢ a : A, Γ ⊢ h : 𝔾 → Γ ⊢ (λg.a) h = a[h/g] : A.
* Super Modality: Γ ⊢ a : A, Γ, x : A ⊢ B : Uᵢ^g, Γ, x : A ⊢ f : B → Γ ⊢ 𝖘-elim(𝖘-intro(a), x.B, f) = f[a/x] : B[a/x], ℑ (A ⊗ B) ≃ ℑ A ⊗ ◯ B ⊕ ◯ A ⊗ ℑ B.
* Bosonic: Γ ⊢ a : A  →  Γ ⊢ ◯ a = η_◯ a : ◯ A, Γ ⊢ b : ◯ (◯ A)  →  Γ ⊢ μ_◯ b = b : ◯ A
* Fermionic: Γ ⊢ a : A⁽¹⁾  →  Γ ⊢ ε_ℑ (ℑ a) = a : A, Γ ⊢ d : ℑ A  →  Γ ⊢ δ_ℑ d = d : ℑ A

### Uniqueness

* Graded Tensor: Γ ⊢ t : A ⊗ B, Γ ⊢ u : A ⊗ B, Γ ⊢ fst(t) = fst(u) : A, snd(t) = snd(u) : B → Γ ⊢ t = u : A ⊗ B.
* Group Action Γ ⊢ t, u : 𝔾 → A, Γ, g : 𝔾 ⊢ t g = u g : A → Γ ⊢ t = u : 𝔾 → A.
* Super Modality:  Γ ⊢ t,u : 𝖘 A, Γ ⊢ s-elim(t, x.A, x) = 𝖘-elim(u, x.A, x) : A → Γ ⊢ t = u : 𝖘 A.
* Bosonic: Γ ⊢ f : ◯ A → B, Γ ⊢ g : ◯ A → B, Γ ⊢ ∀ (a : A), f (η_◯ a) = g (η_◯ a)  →  Γ ⊢ f = g : ◯ A → B
* Fermionic: Γ ⊢ f : B → ℑ A, Γ ⊢ g : B → ℑ A, Γ ⊢ ∀ (b : B), ε_ℑ (f b) = ε_ℑ (g b)  →  Γ ⊢ f = g : B → ℑ A

### Coherenses

Tensor and Modalities:

```
Γ ⊢ A : Uᵢ⁽ᵍ¹⁾, Γ ⊢ B : Uᵢ⁽ᵍ²⁾  →  Γ ⊢ ◯ (A ⊗ B) ≃ ◯ A ⊗ ◯ B : Uᵢ⁽⁰⁾
Γ ⊢ A : Uᵢ⁽ᵍ¹⁾, Γ ⊢ B : Uᵢ⁽ᵍ²⁾  →  Γ ⊢ ℑ (A ⊗ B) ≃ ℑ A ⊗ ◯ B ⊕ ◯ A ⊗ ℑ B : Uᵢ⁽¹⁾ ⊕ Uᵢ⁽¹⁾
Γ ⊢ 𝖘 (A ⊗ B) ≃ 𝖘 A ⊗ 𝖘 B : Uᵢ⁽ᵍ¹ + ᵍ²⁾
```

Idempodence:

```
◯ (◯ (𝖘 ℝ¹|¹)) ≃ ◯ (𝖘 ℝ¹|¹) ≃ ℝ¹.
ℑ (ℑ (𝖘 ℝ¹|¹)) ≃ ℑ (𝖘 ℝ¹|¹) ≃ ℝ⁰|¹.
```

Projections:

```
π_◯ : 𝖘 ℝ¹|¹ → ◯ (𝖘 ℝ¹|¹) (x ↦ x).
π_ℑ : 𝖘 ℝ¹|¹ → ℑ (𝖘 ℝ¹|¹) (ψ ↦ ψ).
```

Tensor:

```
◯ (𝖘 ℝ¹|¹ ⊗ 𝖘 ℝ¹|¹) ≃ ◯ (𝖘 ℝ¹|¹) ⊗ ◯ (𝖘 ℝ¹|¹) ≃ ℝ¹ ⊗ ℝ¹.
ℑ (𝖘 ℝ¹|¹ ⊗ 𝖘 ℝ¹|¹) ≃ ℝ⁰|¹ ⊗ ℝ¹ ⊕ ℝ¹ ⊗ ℝ⁰|¹ (two odd terms).
```

Adjuncion:

```
Hom(◯ (𝖘 ℝ¹|¹), 𝖘 ℝ¹|¹) ≅ Hom(𝖘 ℝ¹|¹, ℑ (𝖘 ℝ¹|¹)) (e.g., maps ℝ¹ → ℝ¹|¹ vs. ℝ¹|¹ → ℝ⁰|¹).
Γ ⊢ Hom(◯ (𝖘 A), 𝖘 B) ≅ Hom(𝖘 A, ℑ (𝖘 B))
Γ ⊢ 𝖘 A : Uᵢ⁽ᵍ⁾ →  Γ ⊢ η : 𝖘 A → ℑ (𝖘 A)
Γ ⊢ 𝖘 B : Uᵢ⁽ᵍ⁾ →  Γ ⊢ ε : ◯ (𝖘 B) → 𝖘 B
```

## TED-S (Supergeormetry, Felix) Examples

* Graded Universes: ⊢ Uᵢ⁰ : Uᵢ₊₁⁰, ⊢ Uᵢ¹ : Uᵢ₊₁⁰.
* Graded Tensor: Γ ⊢ A : Uᵢ^g₁, Γ ⊢ B : Uᵢ^g₂ → Γ ⊢ A ⊗ B : Uᵢ^(g₁ + g₂) Γ ⊢ a : A, Γ ⊢ b : B → Γ ⊢ a ⊗ b : A ⊗ B Γ ⊢ a : A^g₁, Γ ⊢ b : B^g₂ → Γ ⊢ a ⊗ b = (−1)^(g₁ g₂) b ⊗ a : A ⊗ B.
* Group Action: Γ, g : 𝔾 ⊢ A : Uᵢ^g → Γ ⊢ 𝔾 → A : Uᵢ^g.
* Super Type Theory: Uᵍᵢ`|` 𝖘 A `|` 𝔾 → A.
* Super Modality: Γ ⊢ A : Uᵢ^g → Γ ⊢ 𝖘 A : Uᵢ^g.
* Cohesive Type Theory: ♭ `|` ♯ `|` ℑ `|` ◯ (four built-in modalities).
* Flat Codiscrete: Γ ⊢ A : Uᵢ^g → Γ ⊢ ♭ A : Uᵢ^g
* Sharp Discrete:  Γ ⊢ A : Uᵢ^g → Γ ⊢ ♯ A : Uᵢ^g
* Bosonic: Γ ⊢ A : Uᵢ⁽ᵍ⁾  →  Γ ⊢ ◯ A : Uᵢ⁽⁰⁾
* Fermionic: Γ ⊢ A : Uᵢ⁽ᵍ⁾  →  Γ ⊢ ℑ A : Uᵢ⁽¹⁾

∫ modality:

```
Γ ⊢ A : Uᵢ⁽ᵍ⁾  →  Γ ⊢ ∫ A : Uᵢ⁽ᵍ⁾,  ∫ A := Π (X : Uᵢ⁽ᵍ⁾), (♯ X → A) → ♭ X
Γ ⊢ a : A  →  Γ ⊢ ∫ a : ∫ A,  ∫ a := η_∫ a,  η_∫ a := λ X. λ f. ♭ (f (η_♯ a))
Γ ⊢ ε_♭ : ∫ (♭ A) → ♭ A
Γ ⊢ Hom(∫ A, B) ≅ Hom(A, ♭ B)
Γ ⊢ ∫ (∫ A) ≃ ∫ A
```

∇ modality:

```
Γ ⊢ A : Uᵢ⁽ᵍ⁾  →  Γ ⊢ ∇ A : Uᵢ⁽ᵍ⁾,  ∇ A := Σ (X : Uᵢ⁽ᵍ⁾), (A → ♭ X) × (♯ X → A)
Γ ⊢ a : A  →  Γ ⊢ ∇ a : ∇ A,  ∇ a := η_∇ a,  η_∇ a := (𝟙, λ _ : ♭ 𝟙. ♭ a, λ x : ♯ 𝟙. a)
Γ ⊢ η_♯ : ♯ A → A
Γ ⊢ ε_∇ : ♯ (∇ A) → A
Γ ⊢ ∇ (∇ A) ≃ ∇ A
```

𝖘 `ℝ¹ᴵ¹` lifts `ℝ¹ᴵ¹` to a super-context, expected to be isomorphic (𝖘 `ℝ¹ᴵ¹` ≃ `ℝ¹ᴵ¹`), as it’s already a supertype:

```
Γ ⊢ ℝ¹|¹ : U₀^|0| → Γ ⊢ 𝖘 ℝ¹|¹ : U₀^|0|.
```

Even part, ◯ (𝖘 `ℝ¹|¹`) ≃ ℝ¹ (bosonic coordinate space):

```
Γ ⊢ 𝖘 ℝ¹|¹ : U₀^|0| → Γ ⊢ ◯ (𝖘 ℝ¹|¹) : U₀^|0|.
```

Odd part, ℑ (𝖘 `ℝ¹|¹`) ≃ `ℝ⁰|¹` (fermionic coordinate):

```
Γ ⊢ 𝖘 ℝ¹|¹ : U₀^|0| → Γ ⊢ ℑ (𝖘 ℝ¹|¹) : U₀^|1|.
```

Tensor Product:

```
Γ ⊢ ◯ (𝖘 ℝ¹|¹ ⊗ 𝖘 ℝ¹|¹) : U₀^|0| ≃ ℝ¹ ⊗ ℝ¹ (even part) 
ℑ(𝖘 ℝ¹|¹) ⊗ ◯(𝖘 ℝ¹|¹) ⊕ ◯(𝖘 ℝ¹|¹) ⊗ ℑ(𝖘 ℝ¹|¹) ≃ ℝ⁰|¹ ⊗ ℝ¹ ⊕ ℝ¹ ⊗ ℝ⁰|¹ : U₀^|1| ⊕ U₀^|1|.
Γ ⊢ θ₁ : ℝ^|1|, Γ ⊢ θ₂ : ℝ^|1| → Γ ⊢ θ₁ ⊗ θ₂ = −θ₂ ⊗ θ₁ : ℝ^|1| ⊗ ℝ^|1|
Γ ⊢ θ : ℝ^|1| → Γ ⊢ θ ⊗ θ = 0 : ℝ^|1| ⊗ ℝ^|1|
Γ ⊢ θ₁ : ℝ^|1|, Γ ⊢ θ₂ : ℝ^|1| → Γ ⊢ θ₁ ⊗ θ₂ : ℝ^|1| ⊗ ℝ^|1|
Γ ⊢ θ₁ : ℝ^|1|, Γ ⊢ θ₂ : ℝ^|1| → Γ ⊢ θ₁ ⊗ θ₂ = (−1)^(|1| |1|) θ₂ ⊗ θ₁ : ℝ^|1| ⊗ ℝ^|1|
Γ ⊢ θ₁ ⊗ θ₂ = −θ₂ ⊗ θ₁ : ℝ^|1| ⊗ ℝ^|1|
Γ ⊢ θ₁ ⊗ θ₂ = (−1)^(|1| |1|) θ₂ ⊗ θ₁ = −θ₂ ⊗ θ₁ : ℝ^|1| ⊗
Γ ⊢ ℝ^|0| : Uᵢ^|0|
Γ ⊢ ℝ^|1| : Uᵢ^|1|
Γ ⊢ ℝ^|0| ⊗ ℝ^|1| : Uᵢ^|1|
|0| + |1| = |1|
Γ ⊢ x : ℝ^|0| Γ ⊢ θ : ℝ^|1| Γ ⊢ x ⊗ θ : ℝ^|0| ⊗ ℝ^|1|
Γ ⊢ g : G → Γ ⊢ t g : ℝ^|0| ⊗ ℝ^|1| ⊗ ℝ^|1|
⊢ Γ, g : G, a : ℝ^|0| ⊗ ℝ^|1| ⊗ ℝ^|1| → Γ
  ⊢ λg.a : G → ℝ^|0| ⊗ ℝ^|1| ⊗ ℝ^|1|
  ⊢ t : G → ℝ^|0| ⊗ ℝ^|1| ⊗ ℝ^|1|
```

### TED-K (K-Theory, Jack) Examples

* Stable Homotopy Primitives: Fib^n, Susp(A), Trunc^n, Π(x:A).B, Σ(x:A).B, Id_A(u,v), Spec, πₙ^S(A), S⁰[p], Group, A ∧ B, [A, B], Hⁿ(X; G), G ⊗ H, SS(E, r).
* Cohesive Spectra: Linear types like H (Hilbert spaces),  PU(H), Fred^0(H).
* Parameterized Spectra: X: Type ⊢ E(X):Spec, e.g., KU_G^τ(X;C).
* Qubit Type: KU_G^τ(Config;C) := [Config,Fred^0(H)].
* Modalities: ♭, ♯, ℑ, ◯, with ℑ(Config)≃BB_n (braid group delooping).
* Key Feature: KU_G^τ encodes su(2)-anyonic ground states, with linear types for braiding.

Fibonacci Anions:

```
def FibAnyon : Type_{lin} := 1 + τ
def FibState (c : Config) : Type_{lin} := Σ (a : FibAnyon), KUᶿ(c; ℂ)
def FibFusionRule : FibAnyon → FibAnyon → Type_{lin}
def FibFusionRule (1 a : FibAnyon) := Id_{FibAnyon}(a, a)
def FibFusionRule (τ τ : FibAnyon) := 1 + τ
def fuseFib (a b: FibAnyon) : Type := Σ (c: FibAnyon), FibFusionRule a b
def fuseFib (τ τ: FibAnyon) : Type ≡ (c, proof) where c : 1 + τ, proof : Id_{FibAnyon}(c, 1 + τ)
def fuseFibState (s₁ s₂ : FibState c) : FibState c := \ (a₁, q₁) (a₂, q₂), (c, fuseQubit(q₁, q₂, c))
def measureFib : Σ(c : FibAnyon).FibFusionRule a b → FibState Config := (c, qubit_c)

def τ₁ : FibAnyon :≡ τ
def τ₂ : FibAnyon :≡ τ
def s₁ : FibState c :≡ (τ₁, q₁)
def s₂ : FibState c :≡ (τ₂, q₂)
def fused : Σ(c : FibAnyon), FibFusionRule τ τ :≡ fuseFib τ₁ τ₂
def resolved : FibState c :≡ measureFib fused
```

Fusion for su(2) k-Anyonic States:

```
def j₀ : Su2Anyon 2 :≡ 0
def j₁ : Su2Anyon 2 :≡ 1/2
def state : Su2State c 2 :≡ (j₁, qubit)
def braid 2 j₁ j₁ : KU^\tau_G(c; ℂ)
def Su2Anyon : ℕ → Type_{lin}
def Su2Anyon k :≡ { j : ℝ | 0 ≤ j ≤ k/2 ∧ 2j ∈ ℕ }
def Su2FusionRule : ℕ → Su2Anyon k → Su2Anyon k → Type
def Su2FusionRule k j₁ j₂ ≡ Σ(j : Su2Anyon k).(|j₁ - j₂| ≤ j ≤ min(j₁ + j₂, k - j₁ - j₂))
def braid (k : ℕ) (a b : Su2Anyon k) : KU^\tau_G(Config; ℂ)
def braid k a b :≡ R_{ab} · state(a, b)
def fuseSu2State (k : ℕ) (s₁ s₂ : Su2State c k) : Su2State c k
def fuseSu2State k (j₁, q₁) (j₂, q₂) :≡ (j, fuseQubit(q₁, q₂, j))
def fuse (k : ℕ) (j₁ j₂ : Su2Anyon k) := Σ(j : Su2Anyon k), Id_{Su2Anyon k}(j, fuseRule(j₁, j₂))
def fuse k j₁ j₂ :≡ (j, proof) where j ∈ {|j₁ - j₂|, ..., min(j₁ + j₂, k - j₁ - j₂)}
def fuseSu2 (k : ℕ)(j₁ j₂ : Su2Anyon k) : Su2FusionRule k j₁ j₂
def fuseSu2 k j₁ j₂ :≡ (j, proof)
    where j = choose(|j₁ - j₂|, min(j₁ + j₂, k - j₁ - j₂)),
    proof : Id_{Su2Anyon k}(j, fusionTerm(j₁, j₂))
```

Majorana Zero Modes:

```
def MZM : Type_{lin} := γ
def MZMState (c: Config) : Type_{lin} := Σ(m : MZM), KU¹(c; ℂ)
def fuseMZM (m₁ m₂ : MZM) := Σ (c : FibAnyon), MZMFusionRule m₁ m₂
def fuseMZM (γ γ : MZM) ≡ (1, refl)
def resolveMZM : Σ(c : FibAnyon), MZMFusionRule γ γ → FibState Config
def resolveMZM (1, refl) ≡ (1, qubit_1)
def fuseMZMState (s₁ s₂ : MZMState c) : FibState c := \ (γ, q₁) (γ, q₂), (1, fuseQubit(q₁, q₂, 1))
```

## Bibliography

* Felix Cherubini. <a href="https://d-nb.info/1138708615/34">Formalizing Cartan Geometry in Modal Homotopy Type Theory</a>. PhD.
* Daniel R. Licata, Michael Shulman, Mitchell Riley. <a href="https://github.com/mikeshulman/cohesivett">A Fibrational Framework for Substructural and Modal Logics</a>.
* Branislav Jurco, Christian Sämann, Urs Schreiber, Martin Wolf. <a href="https://arxiv.org/pdf/1903.02807">Higher Structures in M-Theory</a>.
* Urs Schreiber. <a href="https://arxiv.org/pdf/1310.7930">Differential cohomology in a cohesive ∞-topos</a>.
* John Huerta, Urs Schreiber. <a href="https://arxiv.org/pdf/1702.01774">M-theory from the Superpoint</a>.
* Namdak Tonpa, <a href="https://tonpa.guru/stream/2018/2018-06-09 Cohesive Type Theory.htm">2018-06-09 Cohesive Type Theory</a>.
* Namdak Tonpa, <a href="https://tonpa.guru/stream/2019/2019-03-16 Geometry in Modal HoTT.htm">2019-03-16 Geometry in Modal HoTT</a>.
* Namdak Tonpa, <a href="https://tonpa.guru/stream/2020/2020-03-24 Modal Homotopy Type Theory.htm">2020-03-24 Modal Homotopy Type Theory</a>.
* Namdak Tonpa, <a href="https://tonpa.guru/stream/2023/2023-04-04%20%D0%A1%D1%83%D0%BF%D0%B5%D1%80%D0%BF%D1%80%D0%BE%D1%81%D1%82%D1%96%D1%80.htm">2023-04-04 Суперпростір</a>.
* Namdak Tonpa, <a href="https://urs.groupoid.space">Urs: Equivariant Super Type Theory</a>.
* Kac, V. G. <a href="https://core.ac.uk/download/pdf/81957395.pdf"> Lie Superalgebras</a>.
* Roček, M., Wadhwa, N. <a href="https://arxiv.org/pdf/hep-th/0408188"> On Calabi-Yau Supermanifolds</a>.
* Cremonini, C. A., Grassi, P. A. <a href="https://arxiv.org/pdf/2106.11786"> Cohomology of Lie Superalgebras: Forms, Pseudoforms, and Integral Forms</a>.
* Davis, S. <a href="https://polipapers.upv.es/index.php/AGT/article/view/1623/1735"> Supersymmetry and the Hopf Fibration</a>.
* Aguilar, M. A., Lopez-Romero, J. M., Socolovsky, M. <a href="https://inspirehep.net/files/72a57b4474bdb1f83e6963d1586050d0">Cohomology and Spectral Sequences in Gauge Theory</a>.
* Hisham Sati, Urs Schreiber. <a href="https://arxiv.org/pdf/2209.08331">Topological Quantum Programming in TED-K</a>.

## Author

* Namdak Tonpa

