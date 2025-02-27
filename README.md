# Urs: Equivariant Super HoTT

## Abstract

We present a layered type theory that integrates three foundational frameworks:
Homotopy Type System (HTS), de Cohesive Modal Type Theory (CMTT), and Equivariant Super Type Theory (ESTT).
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

* Homotopy Type System (HTS): The base layer, providing a foundation for higher categorical structures via types as ∞-groupoids.
* Cohesive Modal Type Theory: The middle layer, adding modal operators for geometric cohesion and differential structure.
* Equivariant Super Type Theory (ESTT): The top layer, introducing graded universes, graded tensors, group actions, and a super modality for supergeometry.

Each layer builds on the previous, culminating in a system tailored to
formalize superpoints (𝑅ᵖᴵ𐞥), supersymmetry, and equivariant structures,
as exemplified in Schreiber’s "Equivariant Super Homotopy Theory" (2012).

## Syntax

## Semantics

### Formation

* Graded Universes: ⊢ `Uᵢ^|0|` : `Uᵢ₊₁^|0|`, ⊢ `Uᵢ^|1|` : `Uᵢ₊₁^|0|`.
* Graded Tensor: Γ ⊢ A : Uᵢ^g₁, Γ ⊢ B : Uᵢ^g₂ → Γ ⊢ A ⊗ B : Uᵢ^(g₁ + g₂) Γ ⊢ a : A, Γ ⊢ b : B → Γ ⊢ a ⊗ b : A ⊗ B Γ ⊢ a : A^g₁, Γ ⊢ b : B^g₂ → Γ ⊢ a ⊗ b = (−1)^(g₁ g₂) b ⊗ a : A ⊗ B.
* Group Action: Γ, g : 𝔾 ⊢ A : Uᵢ^g → Γ ⊢ 𝔾 → A : Uᵢ^g.
* Cohesive Type Theory: ... `∣`ʃA `∣` ♭A `∣` ♯A `∣` ℑA `|` &A `|` ....
* Super Type Theory: Uᵍᵢ`|` 𝖘 A `|` 𝔾 → A.
* Super Modality: Γ ⊢ A : Uᵢ^g → Γ ⊢ s A : Uᵢ^g.

### Introduction

* Graded Tensor: Γ ⊢ a : A, Γ ⊢ b : B → Γ ⊢ a ⊗ b : A ⊗ B.
* Group Action: Γ, g : 𝔾 ⊢ a : A → Γ ⊢ λg.a : 𝔾 → A.
* Super Modality: Γ ⊢ a : A → Γ ⊢ 𝖘-intro(a) : 𝖘 A.

### Elimation

* Graded Tensor: Γ ⊢ t : A ⊗ B, Γ, x : A, y : B ⊢ C : Uᵢ^g → Γ ⊢ ⊗-elim(t, x.y.C) : C[fst(t)/x, snd(t)/y].
* Group Action: Γ ⊢ t : 𝔾 → A, Γ ⊢ g : 𝔾 → Γ ⊢ t g : A.
* Super Modality: Γ ⊢ t : 𝖘 A, Γ, x : A ⊢ B : Uᵢ^g, Γ, x : A ⊢ f : B → Γ ⊢ 𝖘-elim(t, x.B, f) : B[𝖘-intro(t)/x].

### Computation

* Graded Tensor: Γ ⊢ a : A, Γ ⊢ b : B, Γ, x : A, y : B ⊢ C : Uᵢ^g → Γ ⊢ ⊗-elim(a ⊗ b, x.y.C) = C[a/x, b/y] : C[a/x, b/y].
* Graded Commutativity: Γ ⊢ a : A^g₁, Γ ⊢ b : B^g₂ → Γ ⊢ a ⊗ b = (−1)^(g₁ g₂) b ⊗ a : A ⊗ B.
* Group Action: Γ, g : 𝔾 ⊢ a : A, Γ ⊢ h : 𝔾 → Γ ⊢ (λg.a) h = a[h/g] : A.
* Super Modality: Γ ⊢ a : A, Γ, x : A ⊢ B : Uᵢ^g, Γ, x : A ⊢ f : B → Γ ⊢ 𝖘-elim(𝖘-intro(a), x.B, f) = f[a/x] : B[a/x].

### Uniqueness

* Graded Tensor: Γ ⊢ t : A ⊗ B, Γ ⊢ u : A ⊗ B, Γ ⊢ fst(t) = fst(u) : A, snd(t) = snd(u) : B → Γ ⊢ t = u : A ⊗ B.
* Group Action Γ ⊢ t, u : 𝔾 → A, Γ, g : 𝔾 ⊢ t g = u g : A → Γ ⊢ t = u : 𝔾 → A.
* Super Modality:  Γ ⊢ t,u : 𝖘 A, Γ ⊢ s-elim(t, x.A, x) = 𝖘-elim(u, x.A, x) : A → Γ ⊢ t = u : 𝖘 A.

## Examples

```
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
Γ, g : G ⊢ a : ℝ^|0| ⊗ ℝ^|1| ⊗ ℝ^|1| → Γ ⊢ λg.a : G → ℝ^|0| ⊗ ℝ^|1| ⊗ ℝ^|1| Γ ⊢ t : G → ℝ^|0| ⊗ ℝ^|1| ⊗ ℝ^|1|,
Γ ⊢ g : G → Γ ⊢ t g : ℝ^|0| ⊗ ℝ^|1| ⊗ ℝ^|1|
```

## Bibliography

* Felix Cherubini. Formalizing Cartan Geometry in Modal Homotopy Type Theory. PhD
* Daniel R. Licata, Michael Shulman, Mitchell Riley. <a href="https://github.com/mikeshulman/cohesivett">A Fibrational Framework for Substructural and Modal Logics</a>
* Branislav Jurco, Christian Sämann, Urs Schreiber, Martin Wolf. <a href="https://arxiv.org/pdf/1903.02807">Higher Structures in M-Theory</a>
* Namdak Tonpa, <a href="https://tonpa.guru/stream/2020/2020-03-24 Modal Homotopy Type Theory.htm">2020-03-24 Modal Homotopy Type Theory</a>
* Namdak Tonpa, <a href="https://tonpa.guru/stream/2018/2018-06-09 Cohesive Type Theory.htm">2018-06-09 Cohesive Type Theory</a>
* Namdak Tonpa, <a href="https://tonpa.guru/stream/2019/2019-03-16 Geometry in Modal HoTT.htm">2019-03-16 Geometry in Modal HoTT</a>
* Namdak Tonpa, <a href="https://urs.groupoid.space">Urs: Equivariant Super Type Theory</a>

## Author

* Namdak Tonpa

