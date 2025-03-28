module config where

import foundations.smooth
import foundations.modalities

-- Configuration Space
def Config (n : Nat) (X : SmthSet) : SmthSet := Config^n(X)  -- n points in X
def plt-config (n m : Nat) (X : SmthSet) : Set := plt m (Config^n(X))

-- Braid Group Delooping
def BB_n (n : Nat) : Grpd 1 := ℑ (Config^n (ℝ^2))

-- Constructors
def intro-config (n : Nat) (X : SmthSet) (ps : Π (i : Fin n), plt 0 X) : Config^n(X) := config-intro ps
def braid (n : Nat) (b : plt-grpd 1 (BB_n n)) : BB_n n := b

-- Eliminators
def elim-config (n : Nat) (X : SmthSet) (c : Config^n(X)) (i : Fin n) : plt 0 X := config-elim c i
def elim-braid (n : Nat) (b : BB_n n) : plt-grpd 1 (BB_n n) := b

-- Computation Rules
def config-β (n : Nat) (X : SmthSet) (ps : Π (i : Fin n), plt 0 X) (i : Fin n)
  : Path (plt 0 X) (elim-config n X (intro-config n X ps) i) (ps i) := idp _ (ps i)
def braid-idem (n : Nat)
  : Path (Grpd 1) (ℑ (BB_n n)) (BB_n n) := fermionic-idem 0 1 (Config^n (ℝ^2))

-- Test Terms and Lemmas

-- Test 1: Configuration of points
def test-config (n : Nat) (X : SmthSet) (ps : Π (i : Fin n), plt 0 X)
  : Config^n(X) := intro-config n X ps
def test-config-β (n : Nat) (X : SmthSet) (ps : Π (i : Fin n), plt 0 X) (i : Fin n)
  : Path (plt 0 X) (elim-config n X (test-config n X ps) i) (ps i) := config-β n X ps i

-- Test 2: Braid group element
def test-braid (n : Nat) (b : plt-grpd 1 (BB_n n)) : BB_n n := braid n b
def test-braid-idem (n : Nat)
  : Path (Grpd 1) (ℑ (BB_n n)) (BB_n n) := braid-idem n

-- Lemma: Braid group shape (Page 5)
def braid-shape (n : Nat)
  : Path (Grpd 1) (ℑ (Config^n (ℝ^2))) (BB_n n) := idp _ _  -- Reflects shape equivalence
