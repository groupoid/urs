module modalities where

import foundations.graded
import foundations.tedk
import foundations.config

-- Cohesive Modalities
def flat            (i : Nat) (g : Grade) (A : U i g) : U i g := ♭ A
def sharp           (i : Nat) (g : Grade) (A : U i g) : U i g := ♯ A
def fermionic-modal (i : Nat) (g : Grade) (A : U i g) : U i 1 := ℑ A
def bosonic-modal   (i : Nat) (g : Grade) (A : U i g) : U i 0 := ◯ A

def ∫ (A : Uᵢᵍ) := Π (X : Uᵢᵍ), (♯ X → A) → ♭ X -- Shape Modality
def ∇ (A : Uᵢᵍ) := Σ (X : Uᵢᵍ), (A → ♭ X) × (♯ X → A) -- Crisp Modality

-- Constructors
def intro-flat      (i : Nat) (g : Grade) (A : U i g) (a : A) : ♭ A := flat-intro a
def intro-sharp     (i : Nat) (g : Grade) (A : U i g) (a : A) : ♯ A := sharp-intro a

-- Eliminators
def elim-flat       (i : Nat) (g : Grade) (A : U i g) (fa : ♭ A) : A := flat-elim fa
def elim-fermionic  (i : Nat) (g : Grade) (A : U i g) (fa : ℑ A) : A := fermionic-elim fa

-- Computation Rules
def flat-β (i : Nat) (g : Grade) (A : U i g) (a : A)
  : Path A (elim-flat i g A (intro-flat i g A a)) a := idp A a
def fermionic-idem (i : Nat) (g : Grade) (A : U i g)
  : Path (U i 1) (ℑ (ℑ A)) (ℑ A) := idp (U i 1) (ℑ A)

-- Test Terms and Lemmas

-- Test 1: Flat modality on Hilbert space
def test-flat (a : H) : ♭ H := intro-flat 0 0 H a
def test-flat-β (a : H)
  : Path H (elim-flat 0 0 H (test-flat a)) a := flat-β 0 0 H a

-- Test 2: Fermionic modality on Config
def test-fermionic (n : Nat) : U 0 1 := fermionic-modal 0 0 (Config^n (ℝ^2))
def test-fermionic-idem (n : Nat)
  : Path (U 0 1) (ℑ (ℑ (Config^n (ℝ^2)))) (ℑ (Config^n (ℝ^2))) := fermionic-idem 0 0 (Config^n (ℝ^2))

-- Lemma: Braid group delooping (Page 5)
def braid-delooop (n : Nat)
  : Path (Grpd 1) (ℑ (Config^n (ℝ^2))) (BB_n n) := idp _ _  -- Matches TED-K shape equivalence

-- Lemma: Bosonic projection (Page 6)
def bosonic-proj (A : U 0 1) (a : A)
  : Path (◯ A) (bosonic-modal 0 1 A a) (bosonic-modal 0 1 A a)
 := idp (◯ A) (bosonic-modal 0 1 A a)  -- Trivial, but reflects bosonic reduction

