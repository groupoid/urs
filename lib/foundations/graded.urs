module graded where

-- Graded Universes
def Grade : Set := {0, 1}  -- 0 for bosonic, 1 for fermionic
def U (i : Nat) (g : Grade) : Type := Uᵢ^g
def U₀^g (g : Grade) : U 1 g := U 0 g

-- Graded Tensor Product
def tensor (i : Nat) (g₁ g₂ : Grade) (A : U i g₁) (B : U i g₂) : U i (g₁ + g₂ mod 2)
 := A ⊗ B
def pair-tensor (i : Nat) (g₁ g₂ : Grade) (A : U i g₁) (B : U i g₂) (a : A) (b : B)
  : tensor i g₁ g₂ A B := a ⊗ b

-- Eliminators
def proj-tensor₁ (i : Nat) (g₁ g₂ : Grade) (A : U i g₁) (B : U i g₂) (p : A ⊗ B) : A := p.1
def proj-tensor₂ (i : Nat) (g₁ g₂ : Grade) (A : U i g₁) (B : U i g₂) (p : A ⊗ B) : B := p.2

-- Computation Rules
def tensor-comm (i : Nat) (g₁ g₂ : Grade) (A : U i g₁) (B : U i g₂) (a : A) (b : B)
  : Path (A ⊗ B) (a ⊗ b) ((-1)^(g₁ * g₂) * (b ⊗ a))
 := idp (A ⊗ B) (a ⊗ b)  -- Graded commutativity
def tensor-β₁ (i : Nat) (g₁ g₂ : Grade) (A : U i g₁) (B : U i g₂) (a : A) (b : B)
  : Path A (proj-tensor₁ i g₁ g₂ A B (a ⊗ b)) a := idp A a

-- Test Terms and Lemmas

-- Test 1: Bosonic tensor
def test-bosonic-tensor (A B : U 0 0) (a : A) (b : B)
  : tensor 0 0 0 A B := pair-tensor 0 0 0 A B a b
def test-bosonic-comm (A B : U 0 0) (a : A) (b : B)
  : Path (A ⊗ B) (a ⊗ b) (b ⊗ a) := tensor-comm 0 0 0 A B a b  -- 0 * 0 = 0, so 1

-- Test 2: Fermionic tensor
def test-fermionic-tensor (A B : U 0 1) (a : A) (b : B)
  : tensor 0 1 1 A B := pair-tensor 0 1 1 A B a b
def test-fermionic-comm (A B : U 0 1) (a : A) (b : B)
  : Path (A ⊗ B) (a ⊗ b) (- (b ⊗ a)) := tensor-comm 0 1 1 A B a b  -- 1 * 1 = 1, so -1

-- Lemma: Tensor associativity (inspired by supergeometry, Page 6)
def tensor-assoc (i : Nat) (g₁ g₂ g₃ : Grade) (A : U i g₁) (B : U i g₂) (C : U i g₃)
  : Path (U i (g₁ + (g₂ + g₃) mod 2)) ((A ⊗ B) ⊗ C) (A ⊗ (B ⊗ C))
 := idp _ _  -- Placeholder for associativity proof

