module modalities where

import foundations.graded

-- Cohesive Modalities
def flat (i : Nat) (g : Grade) (A : U i g) : U i g := ♭ A
def sharp (i : Nat) (g : Grade) (A : U i g) : U i g := ♯ A
def fermionic-modal (i : Nat) (g : Grade) (A : U i g) : U i 1 := ℑ A
def bosonic-modal (i : Nat) (g : Grade) (A : U i g) : U i 0 := ◯ A

-- Constructors
def intro-flat (i : Nat) (g : Grade) (A : U i g) (a : A) : ♭ A := flat-intro a
def intro-sharp (i : Nat) (g : Grade) (A : U i g) (a : A) : ♯ A := sharp-intro a

-- Eliminators
def elim-flat (i : Nat) (g : Grade) (A : U i g) (fa : ♭ A) : A := flat-elim fa
def elim-fermionic (i : Nat) (g : Grade) (A : U i g) (fa : ℑ A) : A := fermionic-elim fa

-- Computation Rules
def flat-β (i : Nat) (g : Grade) (A : U i g) (a : A)
  : Path A (elim-flat i g A (intro-flat i g A a)) a := idp A a
def fermionic-idem (i : Nat) (g : Grade) (A : U i g)
  : Path (U i 1) (ℑ (ℑ A)) (ℑ A) := idp (U i 1) (ℑ A)  -- Idempotence

-- Test Terms and Lemmas

-- Test 1: Flat modality
def test-flat (A : U 0 0) (a : A) : ♭ A := intro-flat 0 0 A a
def test-flat-β (A : U 0 0) (a : A)
  : Path A (elim-flat 0 0 A (test-flat A a)) a := flat-β 0 0 A a

-- Test 2: Fermionic modality
def test-fermionic (A : U 0 1) : U 0 1 := fermionic-modal 0 1 A
def test-fermionic-idem (A : U 0 1)
  : Path (U 0 1) (ℑ (ℑ A)) (ℑ A) := fermionic-idem 0 1 A

-- Lemma: Bosonic projection (Page 6)
def bosonic-proj (A : U 0 1) (a : A)
  : Path (◯ A) (bosonic-modal 0 1 A a) (bosonic-modal 0 1 A a)
 := idp (◯ A) (bosonic-modal 0 1 A a)  -- Trivial, but reflects bosonic reduction

